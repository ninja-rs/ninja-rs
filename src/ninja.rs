// Copyright 2011 Google Inc. All Rights Reserved.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

use std;

use std::path::{Path, PathBuf};

use clap::{App, AppSettings, SubCommand, Arg, ArgMatches};

use super::debug_flags::*;
use super::build::{BuildConfig, BuildConfigVerbosity, Builder};
use super::build_log::{BuildLog, BuildLogUser};
use super::deps_log::DepsLog;
use super::utils::*;
use super::state::State;
use super::graph::NodeIndex;
use super::disk_interface::{DiskInterface, RealDiskInterface};
use super::eval_env::Env;
use super::manifest_parser::{ManifestParser, ManifestParserOptions, DupeEdgeAction, PhonyCycleAction};
use super::version::NINJA_VERSION;

/// Command-line options.
#[derive(Default)]
struct Options<'a> {
  /// Build file to load.
  input_file: PathBuf,

  /// Directory to change into before running.
  working_dir: Option<PathBuf>,

  /// Tool to run rather than building.
  tool: Option<Tool<'a>>,

  /// Whether duplicate rules for one target should warn or print an error.
  dupe_edges_should_err: bool,

  /// Whether phony cycles should warn or print an error.
  phony_cycle_should_err: bool,
}

impl<'a> Options<'a> {
    pub fn new() -> Self {
        Self::default()
    }
}

#[derive(PartialEq, Clone, Copy)]
enum ToolRunAfter {
    /// Run after parsing the command-line flags and potentially changing
    /// the current working directory (as early as possible).
    RunAfterFlags,

    /// Run after loading build.ninja.
    RunAfterLoad,

    /// Run after loading the build/deps logs.
    RunAfterLogs,
}

/// Subtools, accessible via "-t foo".
struct Tool<'a> {
  /// Short name of the tool.
  name: &'a str,

  /// Description (shown in "-t list").
  desc: &'a str,

  /// When to run the tool.
  when: ToolRunAfter,

  /// Implementation of the tool.
  func: NinjaMainToolFunc,
}

type NinjaMainToolFunc = fn (&NinjaMain, &Options) -> Result<(), isize>;

struct NinjaMain<'a> {
    /// Command line used to run Ninja.
    ninja_command: &'a Path,
    /// Build configuration set from flags (e.g. parallelism).
    config: &'a BuildConfig,
    /// Loaded state (rules, nodes).
    state: State,
    /// Functions for accesssing the disk.
    disk_interface: RealDiskInterface,
    /// The build directory, used for storing the build log etc.
    build_dir: Vec<u8>,
    build_log: BuildLog<'a>,
    deps_log: DepsLog,
}

impl<'a> NinjaMain<'a> {
    pub fn new(ninja_command: &'a Path, config: &'a BuildConfig) -> Self {
        NinjaMain{
            ninja_command,
            config,
            state: State::new(),
            disk_interface: RealDiskInterface{},
            build_dir: Vec::new(),
            build_log: BuildLog::new(),
            deps_log: DepsLog::new(),
        }
    }

    /// Open the build log.
    /// @return false on error.
    pub fn open_build_log(&mut self, recompact_only: bool) -> Result<(), ()> {
        let mut log_path = self.build_dir.clone();
        if log_path.is_empty() {
            log_path.extend_from_slice(b"/");
            log_path.extend_from_slice(b".ninja_log");
        }

        let log_path = pathbuf_from_bytes(log_path).map_err(|e| {
            error!("invalid utf-8 filename {}", String::from_utf8_lossy(&e));
        })?;

        if let Some(warn) = self.build_log.load(&log_path).map_err(|e| {
            error!("loading build log {}: {}", log_path.display(), e);
        })? {
            warning!("{}", warn);
        }

        if recompact_only {
            self.build_log.recompact(&log_path, self).map_err(|e| {
                error!("failed recompaction: {}", e);
            })?;
            return Ok(());
        }
        
        if !self.config.dry_run {
            self.build_log.open_for_write(&log_path, self).map_err(|e| {
                error!("opening build log: {}", e);
            })?;
        }

        Ok(())
    }

    /// Open the deps log: load it, then open for writing.
    /// @return false on error.
    pub fn open_deps_log(&mut self, recompact_only: bool) -> Result<(), ()> {
        let mut log_path = self.build_dir.clone();
        if log_path.is_empty() {
            log_path.extend_from_slice(b"/");
            log_path.extend_from_slice(b".ninja_deps");
        }

        let log_path = pathbuf_from_bytes(log_path).map_err(|e| {
            error!("invalid utf-8 filename {}", String::from_utf8_lossy(&e));
        })?;

        if let Some(warn) = self.deps_log.load(&log_path, &mut self.state).map_err(|e| {
            error!("loading deps log {}: {}", log_path.display(), e);
        })? {
            warning!("{}", warn);
        }

        if recompact_only {
            self.deps_log.recompact(&log_path).map_err(|e| {
                error!("failed recompaction: {}", e);
            })?;
            return Ok(());
        }
        
        if !self.config.dry_run {
            self.deps_log.open_for_write(&log_path).map_err(|e| {
                error!("opening deps log: {}", e);
            })?;
        }

        Ok(())
    }

    /// Ensure the build directory exists, creating it if necessary.
    /// @return false on error.
    pub fn ensure_build_dir_exists(&mut self) -> Result<(), ()> {
        use std::io::ErrorKind;

        let bindings = self.state.bindings.borrow();
        self.build_dir = bindings.lookup_variable(b"builddir").into_owned();
        if !self.build_dir.is_empty() && !self.config.dry_run {
            let mut make_dir_bytes = self.build_dir.clone();
            make_dir_bytes.extend_from_slice(b"/.");
            let make_dir = pathbuf_from_bytes(make_dir_bytes).map_err(|e| {
              error!("invalid utf8 pathname {}", String::from_utf8_lossy(&e));
            })?;
            self.disk_interface.make_dirs(&make_dir).or_else(|e| {
              if e.kind() == ErrorKind::AlreadyExists {
                Ok(())
              } else {
                Err(e)
              }
            }).map_err(|e| {
              error!("creating build directory {}: {}", String::from_utf8_lossy(&self.build_dir), e);
            })?;
        }
        Ok(())
    }

    /// Rebuild the manifest, if necessary.
    /// Fills in \a err on error.
    /// @return true if the manifest was rebuilt.
    pub fn rebuild_manifest(&mut self, input_file: &std::path::Path) -> Result<bool, String> {
        let mut path = input_file.to_string_lossy().into_owned().into_bytes();
        let _ = canonicalize_path(&mut path)?;

        let node_idx = self.state.node_state.lookup_node(&path);
        if node_idx.is_none() {
            return Ok(false);
        }
        let node_idx = node_idx.unwrap();

        {
            let mut builder = Builder::new(&self.state, &self.config, 
                &self.build_log, &self.deps_log, &self.disk_interface);

            builder.add_target(node_idx)?;

            if builder.is_already_up_to_date() {
                return Ok(false); // Not an error, but we didn't rebuild.
            }

            builder.build()?;
        }

        // The manifest was only rebuilt if it is now dirty (it may have been cleaned
        // by a restat).
        if !self.state.node_state.get_node(node_idx).is_dirty() {
          // Reset the state to prevent problems like
          // https://github.com/ninja-build/ninja/issues/874
          self.state.reset();
          return Ok(false);
        }

        return Ok(true);
    }

    /// Get the Node for a given command-line path, handling features like
    /// spell correction.
    fn collect_target(&self, cpath: &[u8]) -> Result<NodeIndex, String> {
        let mut path = cpath.to_owned();
        let slash_bits = canonicalize_path(&mut path)?;
        
        // Special syntax: "foo.cc^" means "the first output of foo.cc".
        let mut first_dependent = false;
        if path.last() == Some(&b'^') {
            path.pop();
            first_dependent = true;
        }

        match self.state.node_state.lookup_node(&path) {
          None => {
              let mut err = format!("unknown target '{}'", 
                  String::from_utf8_lossy(&decanonicalize_path(&path, slash_bits)));
              if &path == b"clean" {
                  err += ", did you mean 'ninja -t clean'?";
              } else if &path == b"help" {
                  err += ", did you mean 'ninja -h'?";
              } else if let Some(suggestion) = self.state.spellcheck_node(&path) {
                  err += &format!(", did you mean '{}'?", String::from_utf8_lossy(suggestion));
              };
              return Err(err);
          },
          Some(node_idx) => {
              if first_dependent {
                  let out_edge_idx = self.state.node_state.get_node(node_idx)
                        .out_edges().first().cloned().ok_or_else(|| {
                          format!("'{}' has no out edge", String::from_utf8_lossy(&path))})?;
                  let output_node_idx = self.state.edge_state.get_edge(out_edge_idx)
                        .outputs.first().cloned();
                  let output_node_idx = output_node_idx.ok_or_else(|| {
                      self.state.edge_state.get_edge(out_edge_idx).dump();
                      format!("edge has no outputs")
                  })?;
                  return Ok(output_node_idx);
              }
              return Ok(node_idx);
          }
        }
    }

    /// CollectTarget for all command-line arguments, filling in \a targets.
    fn collect_targets_from_args(&self, args: ArgMatches<'static>) 
            -> Result<Vec<NodeIndex>, String> {
        if let Some(inputs_value) = args.values_of_lossy("TARGET") {
            let mut result = Vec::new();
            for input_value in inputs_value.into_iter().map(String::into_bytes) {
                let node_idx = self.collect_target(&input_value)?;
                result.push(node_idx);
            }
            Ok(result)
        } else {
            self.state.default_nodes()
        }
    }

    /// Build the targets listed on the command line.
    /// @return an exit code.
    pub fn run_build(&mut self, args: ArgMatches<'static>) -> Result<(), isize> {
        let targets = self.collect_targets_from_args(args).map_err(|e| {
            error!("{}", e);
            return 1isize;
        })?;

        self.disk_interface.allow_stat_cache(EXPERIMENTAL_STATCACHE);

        let mut builder = Builder::new(&self.state, &self.config, 
            &self.build_log, &self.deps_log, &self.disk_interface);

        for target in targets.into_iter() {
            let _ = builder.add_target(target).map_err(|e| {
              error!("{}", e);
              return 1isize;
            })?;
            // If _ is false, it's adding a target that is already up-to-date; not really
            // an error.
        }

        self.disk_interface.allow_stat_cache(false);

        if builder.is_already_up_to_date() {
            print!("ninja: no work to do.\n");
            return Ok(());
        }

        builder.build().map_err(|e| {
            print!("ninja: build stopped: {}.\n", e);
            if e.find("interrupted by user").is_some() {
                return 2isize;
            }
            return 1isize;
        })?;

        Ok(())
    }

    /// Dump the output requested by '-d stats'.
    pub fn dump_metrics(&mut self) {
        unimplemented!()
    }
}

impl<'a> BuildLogUser for NinjaMain<'a> {
    fn is_path_dead(&self, s: &str) -> bool {
        unimplemented!{}
    }
}

/*

/// The Ninja main() loads up a series of data structures; various tools need
/// to poke into these, so store them as fields on an object.
struct NinjaMain : public BuildLogUser {
  NinjaMain(const char* ninja_command, const BuildConfig& config) :
      ninja_command_(ninja_command), config_(config) {}



  /// The type of functions that are the entry points to tools (subcommands).
  typedef int (NinjaMain::*ToolFunc)(const Options*, int, char**);

  /// Get the Node for a given command-line path, handling features like
  /// spell correction.
  Node* CollectTarget(const char* cpath, string* err);

  /// CollectTarget for all command-line arguments, filling in \a targets.
  bool CollectTargetsFromArgs(int argc, char* argv[],
                              vector<Node*>* targets, string* err);

  // The various subcommands, run via "-t XXX".
  int ToolGraph(const Options* options, int argc, char* argv[]);
  int ToolQuery(const Options* options, int argc, char* argv[]);
  int ToolDeps(const Options* options, int argc, char* argv[]);
  int ToolBrowse(const Options* options, int argc, char* argv[]);
  int ToolMSVC(const Options* options, int argc, char* argv[]);
  int ToolTargets(const Options* options, int argc, char* argv[]);
  int ToolCommands(const Options* options, int argc, char* argv[]);
  int ToolClean(const Options* options, int argc, char* argv[]);
  int ToolCompilationDatabase(const Options* options, int argc, char* argv[]);
  int ToolRecompact(const Options* options, int argc, char* argv[]);
  int ToolUrtle(const Options* options, int argc, char** argv);



  virtual bool IsPathDead(StringPiece s) const {
    Node* n = state_.LookupNode(s);
    if (!n || !n->in_edge())
      return false;
    // Just checking n isn't enough: If an old output is both in the build log
    // and in the deps log, it will have a Node object in state_.  (It will also
    // have an in edge if one of its inputs is another output that's in the deps
    // log, but having a deps edge product an output thats input to another deps
    // edge is rare, and the first recompaction will delete all old outputs from
    // the deps log, and then a second recompaction will clear the build log,
    // which seems good enough for this corner case.)
    // Do keep entries around for files which still exist on disk, for
    // generators that want to use this information.
    string err;
    TimeStamp mtime = disk_interface_.Stat(s.AsString(), &err);
    if (mtime == -1)
      Error("%s", err.c_str());  // Log and ignore Stat() errors.
    return mtime == 0;
  }
};
*/

fn debug_enable(name: &str) -> Result<(), isize> {
    unimplemented!()
}

fn warning_enable(name: &str) -> Result<(), isize> {
    unimplemented!()
}

fn choose_tool(subcommand: &[&str]) -> Result<Tool<'static>, isize> {
    unimplemented!()
}

/*
/// Enable a debugging mode.  Returns false if Ninja should exit instead
/// of continuing.
bool DebugEnable(const string& name) {
  if (name == "list") {
    printf("debugging modes:\n"
"  stats        print operation counts/timing info\n"
"  explain      explain what caused a command to execute\n"
"  keepdepfile  don't delete depfiles after they're read by ninja\n"
"  keeprsp      don't delete @response files on success\n"
#ifdef _WIN32
"  nostatcache  don't batch stat() calls per directory and cache them\n"
#endif
"multiple modes can be enabled via -d FOO -d BAR\n");
    return false;
  } else if (name == "stats") {
    g_metrics = new Metrics;
    return true;
  } else if (name == "explain") {
    g_explaining = true;
    return true;
  } else if (name == "keepdepfile") {
    g_keep_depfile = true;
    return true;
  } else if (name == "keeprsp") {
    g_keep_rsp = true;
    return true;
  } else if (name == "nostatcache") {
    g_experimental_statcache = false;
    return true;
  } else {
    const char* suggestion =
        SpellcheckString(name.c_str(),
                         "stats", "explain", "keepdepfile", "keeprsp",
                         "nostatcache", NULL);
    if (suggestion) {
      Error("unknown debug setting '%s', did you mean '%s'?",
            name.c_str(), suggestion);
    } else {
      Error("unknown debug setting '%s'", name.c_str());
    }
    return false;
  }
}

/// Set a warning flag.  Returns false if Ninja should exit instead  of
/// continuing.
bool WarningEnable(const string& name, Options* options) {
  if (name == "list") {
    printf("warning flags:\n"
"  dupbuild={err,warn}  multiple build lines for one target\n"
"  phonycycle={err,warn}  phony build statement references itself\n");
    return false;
  } else if (name == "dupbuild=err") {
    options->dupe_edges_should_err = true;
    return true;
  } else if (name == "dupbuild=warn") {
    options->dupe_edges_should_err = false;
    return true;
  } else if (name == "phonycycle=err") {
    options->phony_cycle_should_err = true;
    return true;
  } else if (name == "phonycycle=warn") {
    options->phony_cycle_should_err = false;
    return true;
  } else {
    const char* suggestion =
        SpellcheckString(name.c_str(), "dupbuild=err", "dupbuild=warn",
                         "phonycycle=err", "phonycycle=warn", NULL);
    if (suggestion) {
      Error("unknown warning flag '%s', did you mean '%s'?",
            name.c_str(), suggestion);
    } else {
      Error("unknown warning flag '%s'", name.c_str());
    }
    return false;
  }
}
*/

/// Choose a default value for the -j (parallelism) flag.
fn guess_parallelism() -> usize {
    match get_processor_count() {
        0 | 1 => 2,
        2 => 3,
        p => p + 2
    }
}

/// Parse argv for command-line options.
/// Returns an exit code, or -1 if Ninja should continue.
fn read_flags(options: &mut Options, config: &mut BuildConfig) -> Result<ArgMatches<'static>, isize> {
    // let helpstring_version = format!("print ninja version (\"{}\")", NINJA_VERSION);
    lazy_static! {
        static ref GUESSED_PARALLELISM : usize = guess_parallelism();
        static ref DEFAULT_PARALLELISM : String = GUESSED_PARALLELISM.to_string();
    }
    let helpstring_parallelism = format!("run N jobs in parallel [default={}, derived from CPUs available]", &GUESSED_PARALLELISM as &usize);
    let app = App::new("ninja")
        .version(NINJA_VERSION)
        .setting(AppSettings::DisableHelpSubcommand)
        .setting(AppSettings::DeriveDisplayOrder)
        .setting(AppSettings::UnifiedHelpMessage)
        .arg(Arg::with_name("cwd").short("C").takes_value(true).value_name("DIR")
            .help("change to DIR before doing anything else"))
        .arg(Arg::with_name("input_file").short("f").takes_value(true).value_name("FILE")
            .default_value("build.ninja").help("specify input build file"))
        .arg(Arg::with_name("parallelism").short("j").takes_value(true).value_name("N")
            .default_value(&DEFAULT_PARALLELISM).help(&helpstring_parallelism).hide_default_value(true))
        .arg(Arg::with_name("failures_allowed").short("k").takes_value(true).value_name("N")
            .default_value("1").help("keep going until N jobs fail"))
        .arg(Arg::with_name("load_average_limit").short("l").takes_value(true).value_name("N")
            .help("do not start new jobs if the load average is greater than N"))        
        .arg(Arg::with_name("dry_run").short("n")
            .help("dry run (don't run commands but act like they succeeded)"))        
        .arg(Arg::with_name("verbose").short("v")
            .help("show all command lines while building"))
        .arg(Arg::with_name("debug_mode").short("d").takes_value(true).value_name("MODE")
            .help("enable debugging (use -d list to list modes)"))
        .arg(Arg::with_name("warning").short("w").takes_value(true).value_name("FLAG")
            .help("adjust warnings (use -w list to list warnings)"))
        .arg(Arg::with_name("targets").multiple(true).value_name("TARGETS")
            .help("if targets are unspecified, builds the 'default' target (see manual)."))
        .subcommand(SubCommand::with_name("-t")
            .setting(AppSettings::TrailingVarArg)
            .help("run a subtool (use -t list to list subtools)\nterminates toplevel options; further flags are passed to the tool")
            .arg(Arg::with_name("tool").multiple(true).value_name("TOOL").required(true)
                .help("tool and its arguments.")))
        ;
    let matches = app.get_matches();
    if let Some(debug_mode) = matches.value_of("debug_mode") {
        debug_enable(debug_mode)?;
    }

    if let Some(input_file) = matches.value_of_os("input_file") {
        options.input_file = input_file.into();
    }

    if let Some(parallelism) = matches.value_of("parallelism") {
        let parallelism = parallelism.parse::<isize>()
            .map_err(|_| 1isize)
            .and_then(|p| if p > 0 {Ok(p)} else {Err(1isize)})
            .unwrap_or_else(|e| {
                fatal!("invalid -j parameter");
            });
        config.parallelism = parallelism as _;
    }

    if let Some(failures_allowed) = matches.value_of("failures_allowed") {
        // We want to go until N jobs fail, which means we should allow
        // N failures and then stop.  For N <= 0, INT_MAX is close enough
        // to infinite for most sane builds.        
        let failures_allowed = failures_allowed.parse::<isize>()
            .map(|v| if v > 0 { v } else { std::isize::MAX })
            .unwrap_or_else(|e| {
                fatal!("-k parameter not numeric; did you mean -k 0?");
            });
        config.failures_allowed = failures_allowed;
    }

    if let Some(load_average_limit) = matches.value_of("load_average_limit") {
        // We want to go until N jobs fail, which means we should allow
        // N failures and then stop.  For N <= 0, INT_MAX is close enough
        // to infinite for most sane builds.        
        let load_average_limit = load_average_limit.parse::<f64>()
            .unwrap_or_else(|e| {
                fatal!("-l parameter not numeric: did you mean -l 0.0?");
            });
        config.max_load_average = load_average_limit;
    }

    if matches.is_present("dry_run") {
        config.dry_run = true;
    }

    if matches.is_present("verbose") {
        config.verbosity = BuildConfigVerbosity::VERBOSE;
    }

    if let Some(warning) = matches.value_of("warning") {
        warning_enable(warning)?;
    }

    if let Some(cwd) = matches.value_of_os("cwd") {
        options.working_dir = Some(cwd.into());
    }

    if let Some(sub_matches) = matches.subcommand_matches("-t") {
        let mut subcommand : Vec<&str> = Vec::new();
        if let Some(args) = sub_matches.values_of("tool") {
            subcommand = args.collect();
        }
        options.tool = Some(choose_tool(&subcommand).map_err(|_| 0isize)?);
        return Ok(sub_matches.clone())
    }
    return Ok(matches);
}

pub fn ninja_entry() -> Result<(), isize> {
    let mut config = BuildConfig::new();
    let mut options = Options::new();
    options.input_file = "build.ninja".into();

    set_stdout_linebuffered();
    let ninja_command: PathBuf = 
        std::env::args_os().next().map(Into::into).unwrap_or_default();

    let args = read_flags(&mut options, &mut config)?;
    if let Some(working_dir) = options.working_dir.as_ref() {
        // The formatting of this string, complete with funny quotes, is
        // so Emacs can properly identify that the cwd has changed for
        // subsequent commands.
        // Don't print this if a tool is being used, so that tool output
        // can be piped into a file without this string showing up.
        if options.tool.is_none() {
            print!("ninja: Entering directory `{:?}'\n", working_dir);
        }

        std::env::set_current_dir(working_dir).unwrap_or_else(|e| {
            fatal!("chdir to '{:?}' - {}", working_dir, e);
        });
    }

    if Some(ToolRunAfter::RunAfterFlags) == (options.tool.as_ref().map(|tool| tool.when)) {
        let ninja = NinjaMain::new(&ninja_command, &config);
        let tool_func = options.tool.as_ref().unwrap().func.clone();
        return tool_func(&ninja, &options);
    }
    const CYCLE_LIMIT: isize = 100;
    for cycle in 1..(CYCLE_LIMIT + 1) {
        let mut ninja = NinjaMain::new(&ninja_command, &config);

        let mut parser_opts = ManifestParserOptions::new();
        if options.dupe_edges_should_err {
            parser_opts.dupe_edge_action = DupeEdgeAction::ERROR;
        }
        if options.phony_cycle_should_err {
            parser_opts.phony_cycle_action = PhonyCycleAction::ERROR;
        }

        {
          let mut parser = ManifestParser::new(&mut ninja.state, &ninja.disk_interface, parser_opts);
          parser.load(&options.input_file)
              .map_err(|err| {
                  error!("{}", &err);
                  return 1isize;
              })?;
        }
        
        if Some(ToolRunAfter::RunAfterLoad) == (options.tool.as_ref().map(|tool| tool.when)) {
            let tool_func = options.tool.as_ref().unwrap().func.clone();
            return tool_func(&ninja, &options);
        }

        ninja.ensure_build_dir_exists().map_err(|_| 1isize)?;
        ninja.open_build_log(false).map_err(|_| 1isize)?;
        ninja.open_deps_log(false).map_err(|_| 1isize)?;

        if Some(ToolRunAfter::RunAfterLogs) == (options.tool.as_ref().map(|tool| tool.when)) {
            let tool_func = options.tool.as_ref().unwrap().func.clone();
            return tool_func(&ninja, &options);
        }

        // Attempt to rebuild the manifest before building anything else
        match ninja.rebuild_manifest(&options.input_file) {
            Ok(false) => (),
            Ok(true) => {
                // In dry_run mode the regeneration will succeed without changing the
                // manifest forever. Better to return immediately.
                if config.dry_run {
                    return Ok(());
                }
                // Start the build over with the new manifest.
                continue;
            }
            Err(err) => {
                error!("rebuilding '{:?}': {}", options.input_file, &err);
                return Err(1);
            }
        }
        let result = ninja.run_build(args);
        if METRICS.is_some() {
            ninja.dump_metrics(); 
        }

        return result;
    }

    error!("manifest '{:?}' still dirty after {} tries\n",
      options.input_file, CYCLE_LIMIT);
    return Err(1);
}

/*

#include <errno.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#ifdef _WIN32
#include "getopt.h"
#include <direct.h>
#include <windows.h>
#elif defined(_AIX)
#include "getopt.h"
#include <unistd.h>
#else
#include <getopt.h>
#include <unistd.h>
#endif

#include "browse.h"
#include "build.h"
#include "build_log.h"
#include "deps_log.h"
#include "clean.h"
#include "debug_flags.h"
#include "disk_interface.h"
#include "graph.h"
#include "graphviz.h"
#include "manifest_parser.h"
#include "metrics.h"
#include "state.h"
#include "util.h"
#include "version.h"

#ifdef _MSC_VER
// Defined in msvc_helper_main-win32.cc.
int MSVCHelperMain(int argc, char** argv);

// Defined in minidump-win32.cc.
void CreateWin32MiniDump(_EXCEPTION_POINTERS* pep);
#endif

namespace {

Node* NinjaMain::CollectTarget(const char* cpath, string* err) {
  string path = cpath;
  uint64_t slash_bits;
  if (!CanonicalizePath(&path, &slash_bits, err))
    return NULL;

  // Special syntax: "foo.cc^" means "the first output of foo.cc".
  bool first_dependent = false;
  if (!path.empty() && path[path.size() - 1] == '^') {
    path.resize(path.size() - 1);
    first_dependent = true;
  }

  Node* node = state_.LookupNode(path);
  if (node) {
    if (first_dependent) {
      if (node->out_edges().empty()) {
        *err = "'" + path + "' has no out edge";
        return NULL;
      }
      Edge* edge = node->out_edges()[0];
      if (edge->outputs_.empty()) {
        edge->Dump();
        Fatal("edge has no outputs");
      }
      node = edge->outputs_[0];
    }
    return node;
  } else {
    *err =
        "unknown target '" + Node::PathDecanonicalized(path, slash_bits) + "'";
    if (path == "clean") {
      *err += ", did you mean 'ninja -t clean'?";
    } else if (path == "help") {
      *err += ", did you mean 'ninja -h'?";
    } else {
      Node* suggestion = state_.SpellcheckNode(path);
      if (suggestion) {
        *err += ", did you mean '" + suggestion->path() + "'?";
      }
    }
    return NULL;
  }
}



int NinjaMain::ToolGraph(const Options* options, int argc, char* argv[]) {
  vector<Node*> nodes;
  string err;
  if (!CollectTargetsFromArgs(argc, argv, &nodes, &err)) {
    Error("%s", err.c_str());
    return 1;
  }

  GraphViz graph;
  graph.Start();
  for (vector<Node*>::const_iterator n = nodes.begin(); n != nodes.end(); ++n)
    graph.AddTarget(*n);
  graph.Finish();

  return 0;
}

int NinjaMain::ToolQuery(const Options* options, int argc, char* argv[]) {
  if (argc == 0) {
    Error("expected a target to query");
    return 1;
  }

  for (int i = 0; i < argc; ++i) {
    string err;
    Node* node = CollectTarget(argv[i], &err);
    if (!node) {
      Error("%s", err.c_str());
      return 1;
    }

    printf("%s:\n", node->path().c_str());
    if (Edge* edge = node->in_edge()) {
      printf("  input: %s\n", edge->rule_->name().c_str());
      for (int in = 0; in < (int)edge->inputs_.size(); in++) {
        const char* label = "";
        if (edge->is_implicit(in))
          label = "| ";
        else if (edge->is_order_only(in))
          label = "|| ";
        printf("    %s%s\n", label, edge->inputs_[in]->path().c_str());
      }
    }
    printf("  outputs:\n");
    for (vector<Edge*>::const_iterator edge = node->out_edges().begin();
         edge != node->out_edges().end(); ++edge) {
      for (vector<Node*>::iterator out = (*edge)->outputs_.begin();
           out != (*edge)->outputs_.end(); ++out) {
        printf("    %s\n", (*out)->path().c_str());
      }
    }
  }
  return 0;
}

#if defined(NINJA_HAVE_BROWSE)
int NinjaMain::ToolBrowse(const Options* options, int argc, char* argv[]) {
  RunBrowsePython(&state_, ninja_command_, options->input_file, argc, argv);
  // If we get here, the browse failed.
  return 1;
}
#endif  // _WIN32

#if defined(_MSC_VER)
int NinjaMain::ToolMSVC(const Options* options, int argc, char* argv[]) {
  // Reset getopt: push one argument onto the front of argv, reset optind.
  argc++;
  argv--;
  optind = 0;
  return MSVCHelperMain(argc, argv);
}
#endif

int ToolTargetsList(const vector<Node*>& nodes, int depth, int indent) {
  for (vector<Node*>::const_iterator n = nodes.begin();
       n != nodes.end();
       ++n) {
    for (int i = 0; i < indent; ++i)
      printf("  ");
    const char* target = (*n)->path().c_str();
    if ((*n)->in_edge()) {
      printf("%s: %s\n", target, (*n)->in_edge()->rule_->name().c_str());
      if (depth > 1 || depth <= 0)
        ToolTargetsList((*n)->in_edge()->inputs_, depth - 1, indent + 1);
    } else {
      printf("%s\n", target);
    }
  }
  return 0;
}

int ToolTargetsSourceList(State* state) {
  for (vector<Edge*>::iterator e = state->edges_.begin();
       e != state->edges_.end(); ++e) {
    for (vector<Node*>::iterator inps = (*e)->inputs_.begin();
         inps != (*e)->inputs_.end(); ++inps) {
      if (!(*inps)->in_edge())
        printf("%s\n", (*inps)->path().c_str());
    }
  }
  return 0;
}

int ToolTargetsList(State* state, const string& rule_name) {
  set<string> rules;

  // Gather the outputs.
  for (vector<Edge*>::iterator e = state->edges_.begin();
       e != state->edges_.end(); ++e) {
    if ((*e)->rule_->name() == rule_name) {
      for (vector<Node*>::iterator out_node = (*e)->outputs_.begin();
           out_node != (*e)->outputs_.end(); ++out_node) {
        rules.insert((*out_node)->path());
      }
    }
  }

  // Print them.
  for (set<string>::const_iterator i = rules.begin();
       i != rules.end(); ++i) {
    printf("%s\n", (*i).c_str());
  }

  return 0;
}

int ToolTargetsList(State* state) {
  for (vector<Edge*>::iterator e = state->edges_.begin();
       e != state->edges_.end(); ++e) {
    for (vector<Node*>::iterator out_node = (*e)->outputs_.begin();
         out_node != (*e)->outputs_.end(); ++out_node) {
      printf("%s: %s\n",
             (*out_node)->path().c_str(),
             (*e)->rule_->name().c_str());
    }
  }
  return 0;
}

int NinjaMain::ToolDeps(const Options* options, int argc, char** argv) {
  vector<Node*> nodes;
  if (argc == 0) {
    for (vector<Node*>::const_iterator ni = deps_log_.nodes().begin();
         ni != deps_log_.nodes().end(); ++ni) {
      if (deps_log_.IsDepsEntryLiveFor(*ni))
        nodes.push_back(*ni);
    }
  } else {
    string err;
    if (!CollectTargetsFromArgs(argc, argv, &nodes, &err)) {
      Error("%s", err.c_str());
      return 1;
    }
  }

  RealDiskInterface disk_interface;
  for (vector<Node*>::iterator it = nodes.begin(), end = nodes.end();
       it != end; ++it) {
    DepsLog::Deps* deps = deps_log_.GetDeps(*it);
    if (!deps) {
      printf("%s: deps not found\n", (*it)->path().c_str());
      continue;
    }

    string err;
    TimeStamp mtime = disk_interface.Stat((*it)->path(), &err);
    if (mtime == -1)
      Error("%s", err.c_str());  // Log and ignore Stat() errors;
    printf("%s: #deps %d, deps mtime %d (%s)\n",
           (*it)->path().c_str(), deps->node_count, deps->mtime,
           (!mtime || mtime > deps->mtime ? "STALE":"VALID"));
    for (int i = 0; i < deps->node_count; ++i)
      printf("    %s\n", deps->nodes[i]->path().c_str());
    printf("\n");
  }

  return 0;
}

int NinjaMain::ToolTargets(const Options* options, int argc, char* argv[]) {
  int depth = 1;
  if (argc >= 1) {
    string mode = argv[0];
    if (mode == "rule") {
      string rule;
      if (argc > 1)
        rule = argv[1];
      if (rule.empty())
        return ToolTargetsSourceList(&state_);
      else
        return ToolTargetsList(&state_, rule);
    } else if (mode == "depth") {
      if (argc > 1)
        depth = atoi(argv[1]);
    } else if (mode == "all") {
      return ToolTargetsList(&state_);
    } else {
      const char* suggestion =
          SpellcheckString(mode.c_str(), "rule", "depth", "all", NULL);
      if (suggestion) {
        Error("unknown target tool mode '%s', did you mean '%s'?",
              mode.c_str(), suggestion);
      } else {
        Error("unknown target tool mode '%s'", mode.c_str());
      }
      return 1;
    }
  }

  string err;
  vector<Node*> root_nodes = state_.RootNodes(&err);
  if (err.empty()) {
    return ToolTargetsList(root_nodes, depth, 0);
  } else {
    Error("%s", err.c_str());
    return 1;
  }
}

enum PrintCommandMode { PCM_Single, PCM_All };
void PrintCommands(Edge* edge, set<Edge*>* seen, PrintCommandMode mode) {
  if (!edge)
    return;
  if (!seen->insert(edge).second)
    return;

  if (mode == PCM_All) {
    for (vector<Node*>::iterator in = edge->inputs_.begin();
         in != edge->inputs_.end(); ++in)
      PrintCommands((*in)->in_edge(), seen, mode);
  }

  if (!edge->is_phony())
    puts(edge->EvaluateCommand().c_str());
}

int NinjaMain::ToolCommands(const Options* options, int argc, char* argv[]) {
  // The clean tool uses getopt, and expects argv[0] to contain the name of
  // the tool, i.e. "commands".
  ++argc;
  --argv;

  PrintCommandMode mode = PCM_All;

  optind = 1;
  int opt;
  while ((opt = getopt(argc, argv, const_cast<char*>("hs"))) != -1) {
    switch (opt) {
    case 's':
      mode = PCM_Single;
      break;
    case 'h':
    default:
      printf("usage: ninja -t commands [options] [targets]\n"
"\n"
"options:\n"
"  -s     only print the final command to build [target], not the whole chain\n"
             );
    return 1;
    }
  }
  argv += optind;
  argc -= optind;

  vector<Node*> nodes;
  string err;
  if (!CollectTargetsFromArgs(argc, argv, &nodes, &err)) {
    Error("%s", err.c_str());
    return 1;
  }

  set<Edge*> seen;
  for (vector<Node*>::iterator in = nodes.begin(); in != nodes.end(); ++in)
    PrintCommands((*in)->in_edge(), &seen, mode);

  return 0;
}

int NinjaMain::ToolClean(const Options* options, int argc, char* argv[]) {
  // The clean tool uses getopt, and expects argv[0] to contain the name of
  // the tool, i.e. "clean".
  argc++;
  argv--;

  bool generator = false;
  bool clean_rules = false;

  optind = 1;
  int opt;
  while ((opt = getopt(argc, argv, const_cast<char*>("hgr"))) != -1) {
    switch (opt) {
    case 'g':
      generator = true;
      break;
    case 'r':
      clean_rules = true;
      break;
    case 'h':
    default:
      printf("usage: ninja -t clean [options] [targets]\n"
"\n"
"options:\n"
"  -g     also clean files marked as ninja generator output\n"
"  -r     interpret targets as a list of rules to clean instead\n"
             );
    return 1;
    }
  }
  argv += optind;
  argc -= optind;

  if (clean_rules && argc == 0) {
    Error("expected a rule to clean");
    return 1;
  }

  Cleaner cleaner(&state_, config_);
  if (argc >= 1) {
    if (clean_rules)
      return cleaner.CleanRules(argc, argv);
    else
      return cleaner.CleanTargets(argc, argv);
  } else {
    return cleaner.CleanAll(generator);
  }
}

void EncodeJSONString(const char *str) {
  while (*str) {
    if (*str == '"' || *str == '\\')
      putchar('\\');
    putchar(*str);
    str++;
  }
}

int NinjaMain::ToolCompilationDatabase(const Options* options, int argc, char* argv[]) {
  bool first = true;
  vector<char> cwd;

  do {
    cwd.resize(cwd.size() + 1024);
    errno = 0;
  } while (!getcwd(&cwd[0], cwd.size()) && errno == ERANGE);
  if (errno != 0 && errno != ERANGE) {
    Error("cannot determine working directory: %s", strerror(errno));
    return 1;
  }

  putchar('[');
  for (vector<Edge*>::iterator e = state_.edges_.begin();
       e != state_.edges_.end(); ++e) {
    if ((*e)->inputs_.empty())
      continue;
    for (int i = 0; i != argc; ++i) {
      if ((*e)->rule_->name() == argv[i]) {
        if (!first)
          putchar(',');

        printf("\n  {\n    \"directory\": \"");
        EncodeJSONString(&cwd[0]);
        printf("\",\n    \"command\": \"");
        EncodeJSONString((*e)->EvaluateCommand().c_str());
        printf("\",\n    \"file\": \"");
        EncodeJSONString((*e)->inputs_[0]->path().c_str());
        printf("\"\n  }");

        first = false;
      }
    }
  }

  puts("\n]");
  return 0;
}

int NinjaMain::ToolRecompact(const Options* options, int argc, char* argv[]) {
  if (!EnsureBuildDirExists())
    return 1;

  if (!OpenBuildLog(/*recompact_only=*/true) ||
      !OpenDepsLog(/*recompact_only=*/true))
    return 1;

  return 0;
}

int NinjaMain::ToolUrtle(const Options* options, int argc, char** argv) {
  // RLE encoded.
  const char* urtle =
" 13 ,3;2!2;\n8 ,;<11!;\n5 `'<10!(2`'2!\n11 ,6;, `\\. `\\9 .,c13$ec,.\n6 "
",2;11!>; `. ,;!2> .e8$2\".2 \"?7$e.\n <:<8!'` 2.3,.2` ,3!' ;,(?7\";2!2'<"
"; `?6$PF ,;,\n2 `'4!8;<!3'`2 3! ;,`'2`2'3!;4!`2.`!;2 3,2 .<!2'`).\n5 3`5"
"'2`9 `!2 `4!><3;5! J2$b,`!>;2!:2!`,d?b`!>\n26 `'-;,(<9!> $F3 )3.:!.2 d\""
"2 ) !>\n30 7`2'<3!- \"=-='5 .2 `2-=\",!>\n25 .ze9$er2 .,cd16$bc.'\n22 .e"
"14$,26$.\n21 z45$c .\n20 J50$c\n20 14$P\"`?34$b\n20 14$ dbc `2\"?22$?7$c"
"\n20 ?18$c.6 4\"8?4\" c8$P\n9 .2,.8 \"20$c.3 ._14 J9$\n .2,2c9$bec,.2 `?"
"21$c.3`4%,3%,3 c8$P\"\n22$c2 2\"?21$bc2,.2` .2,c7$P2\",cb\n23$b bc,.2\"2"
"?14$2F2\"5?2\",J5$P\" ,zd3$\n24$ ?$3?%3 `2\"2?12$bcucd3$P3\"2 2=7$\n23$P"
"\" ,3;<5!>2;,. `4\"6?2\"2 ,9;, `\"?2$\n";
  int count = 0;
  for (const char* p = urtle; *p; p++) {
    if ('0' <= *p && *p <= '9') {
      count = count*10 + *p - '0';
    } else {
      for (int i = 0; i < max(count, 1); ++i)
        printf("%c", *p);
      count = 0;
    }
  }
  return 0;
}

/// Find the function to execute for \a tool_name and return it via \a func.
/// Returns a Tool, or NULL if Ninja should exit.
const Tool* ChooseTool(const string& tool_name) {
  static const Tool kTools[] = {
#if defined(NINJA_HAVE_BROWSE)
    { "browse", "browse dependency graph in a web browser",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolBrowse },
#endif
#if defined(_MSC_VER)
    { "msvc", "build helper for MSVC cl.exe (EXPERIMENTAL)",
      Tool::RUN_AFTER_FLAGS, &NinjaMain::ToolMSVC },
#endif
    { "clean", "clean built files",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolClean },
    { "commands", "list all commands required to rebuild given targets",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolCommands },
    { "deps", "show dependencies stored in the deps log",
      Tool::RUN_AFTER_LOGS, &NinjaMain::ToolDeps },
    { "graph", "output graphviz dot file for targets",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolGraph },
    { "query", "show inputs/outputs for a path",
      Tool::RUN_AFTER_LOGS, &NinjaMain::ToolQuery },
    { "targets",  "list targets by their rule or depth in the DAG",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolTargets },
    { "compdb",  "dump JSON compilation database to stdout",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolCompilationDatabase },
    { "recompact",  "recompacts ninja-internal data structures",
      Tool::RUN_AFTER_LOAD, &NinjaMain::ToolRecompact },
    { "urtle", NULL,
      Tool::RUN_AFTER_FLAGS, &NinjaMain::ToolUrtle },
    { NULL, NULL, Tool::RUN_AFTER_FLAGS, NULL }
  };

  if (tool_name == "list") {
    printf("ninja subtools:\n");
    for (const Tool* tool = &kTools[0]; tool->name; ++tool) {
      if (tool->desc)
        printf("%10s  %s\n", tool->name, tool->desc);
    }
    return NULL;
  }

  for (const Tool* tool = &kTools[0]; tool->name; ++tool) {
    if (tool->name == tool_name)
      return tool;
  }

  vector<const char*> words;
  for (const Tool* tool = &kTools[0]; tool->name; ++tool)
    words.push_back(tool->name);
  const char* suggestion = SpellcheckStringV(tool_name, words);
  if (suggestion) {
    Fatal("unknown tool '%s', did you mean '%s'?",
          tool_name.c_str(), suggestion);
  } else {
    Fatal("unknown tool '%s'", tool_name.c_str());
  }
  return NULL;  // Not reached.
}

void NinjaMain::DumpMetrics() {
  g_metrics->Report();

  printf("\n");
  int count = (int)state_.paths_.size();
  int buckets = (int)state_.paths_.bucket_count();
  printf("path->node hash load %.2f (%d entries / %d buckets)\n",
         count / (double) buckets, count, buckets);
}

bool NinjaMain::EnsureBuildDirExists() {
  build_dir_ = state_.bindings_.LookupVariable("builddir");
  if (!build_dir_.empty() && !config_.dry_run) {
    if (!disk_interface_.MakeDirs(build_dir_ + "/.") && errno != EEXIST) {
      Error("creating build directory %s: %s",
            build_dir_.c_str(), strerror(errno));
      return false;
    }
  }
  return true;
}

int NinjaMain::RunBuild(int argc, char** argv) {
  string err;
  vector<Node*> targets;
  if (!CollectTargetsFromArgs(argc, argv, &targets, &err)) {
    Error("%s", err.c_str());
    return 1;
  }

  disk_interface_.AllowStatCache(g_experimental_statcache);

  Builder builder(&state_, config_, &build_log_, &deps_log_, &disk_interface_);
  for (size_t i = 0; i < targets.size(); ++i) {
    if (!builder.AddTarget(targets[i], &err)) {
      if (!err.empty()) {
        Error("%s", err.c_str());
        return 1;
      } else {
        // Added a target that is already up-to-date; not really
        // an error.
      }
    }
  }

  // Make sure restat rules do not see stale timestamps.
  disk_interface_.AllowStatCache(false);

  if (builder.AlreadyUpToDate()) {
    printf("ninja: no work to do.\n");
    return 0;
  }

  if (!builder.Build(&err)) {
    printf("ninja: build stopped: %s.\n", err.c_str());
    if (err.find("interrupted by user") != string::npos) {
      return 2;
    }
    return 1;
  }

  return 0;
}

#ifdef _MSC_VER

/// This handler processes fatal crashes that you can't catch
/// Test example: C++ exception in a stack-unwind-block
/// Real-world example: ninja launched a compiler to process a tricky
/// C++ input file. The compiler got itself into a state where it
/// generated 3 GB of output and caused ninja to crash.
void TerminateHandler() {
  CreateWin32MiniDump(NULL);
  Fatal("terminate handler called");
}

/// On Windows, we want to prevent error dialogs in case of exceptions.
/// This function handles the exception, and writes a minidump.
int ExceptionFilter(unsigned int code, struct _EXCEPTION_POINTERS *ep) {
  Error("exception: 0x%X", code);  // e.g. EXCEPTION_ACCESS_VIOLATION
  fflush(stderr);
  CreateWin32MiniDump(ep);
  return EXCEPTION_EXECUTE_HANDLER;
}

#endif  // _MSC_VER

}  // anonymous namespace

extern "C" int exported_main(int argc, char** argv) {
#if defined(_MSC_VER)
  // Set a handler to catch crashes not caught by the __try..__except
  // block (e.g. an exception in a stack-unwind-block).
  std::set_terminate(TerminateHandler);
  __try {
    // Running inside __try ... __except suppresses any Windows error
    // dialogs for errors such as bad_alloc.
    return real_main(argc, argv);
  }
  __except(ExceptionFilter(GetExceptionCode(), GetExceptionInformation())) {
    // Common error situations return exitCode=1. 2 was chosen to
    // indicate a more serious problem.
    return 2;
  }
#else
  return real_main(argc, argv);
#endif
}

*/