// Copyright 2011 Google Inc. All Rights Reserved.
// Copyright 2017 Ninja-rs Authors. All Rights Reserved.
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

use std::cell::{Cell, RefCell};
use std::collections::{BTreeMap, BTreeSet, btree_map};

use super::state::State;
use super::deps_log::DepsLog;
use super::build_log::BuildLog;
use super::disk_interface::DiskInterface;
use super::graph::{NodeIndex, EdgeIndex, DependencyScan};
use super::exit_status::ExitStatus;
use super::metrics::Stopwatch;
use super::metrics::get_time_millis;
use super::debug_flags::KEEP_RSP;
use super::timestamp::TimeStamp;
use super::subprocess::SubprocessSet;
use super::utils::{get_load_average, pathbuf_from_bytes};
use super::line_printer::{LinePrinter, LinePrinterLineType};

pub enum EdgeResult {
    EdgeFailed,
    EdgeSucceeded,
}

/// Plan stores the state of a build plan: what we intend to build,
/// which steps we're ready to execute.
pub struct Plan {
    wanted_edges: usize,
    command_edges: usize,

    /// Keep track of which edges we want to build in this plan.  If this map does
    /// not contain an entry for an edge, we do not want to build the entry or its
    /// dependents.  If an entry maps to false, we do not want to build it, but we
    /// might want to build one of its dependents.  If the entry maps to true, we
    /// want to build it.
    want: BTreeMap<EdgeIndex, bool>,
    ready: BTreeSet<EdgeIndex>,
}

trait IsVacant {
    fn is_vacant(&self) -> bool;
}

impl<'a, K, V> IsVacant for btree_map::Entry<'a, K, V> {
    fn is_vacant(&self) -> bool {
        match self {
            &btree_map::Entry::Vacant(_) => true,
            _ => false,
        }
    }
}


impl Plan {
    pub fn new() -> Self {
        Plan {
            wanted_edges: 0usize,
            command_edges: 0usize,
            want: BTreeMap::new(),
            ready: BTreeSet::new(),
        }
    }

    /// Add a target to our plan (including all its dependencies).
    /// Returns false if we don't need to build this target; may
    /// fill in |err| with an error message if there's a problem.
    pub fn add_target(&mut self, state: &State, node: NodeIndex) -> Result<bool, String> {
        self.add_sub_target(state, node, None)
    }

    pub fn add_sub_target(
        &mut self,
        state: &State,
        node_idx: NodeIndex,
        dependent: Option<NodeIndex>,
    ) -> Result<bool, String> {
        let node = state.node_state.get_node(node_idx);
        let edge_idx = node.in_edge();
        if edge_idx.is_none() {
            if node.is_dirty() {
                let mut err = format!("'{}'", String::from_utf8_lossy(node.path()));
                if let Some(dependent) = dependent {
                    err += &format!(
                        ", needed by '{}',",
                        String::from_utf8_lossy(state.node_state.get_node(dependent).path())
                    );
                }
                err += " missing and no known rule to make it";
                return Err(err);
            }
            return Ok(false);
        }
        let edge_idx = edge_idx.unwrap();
        let edge = state.edge_state.get_edge(edge_idx);
        if edge.outputs_ready() {
            return Ok(false); // Don't need to do anything.
        }

        // If an entry in want_ does not already exist for edge, create an entry which
        // maps to false, indicating that we do not want to build this entry itself.
        let want = self.want.get(&edge_idx).cloned();
        let vacant = want.is_none();

        if node.is_dirty() && want.unwrap_or(false) == false {
            self.want.insert(edge_idx, true);
            self.wanted_edges += 1;
            if edge.all_inputs_ready(state) {
                self.schedule_work(state, edge_idx);
            }
            if !edge.is_phony() {
                self.command_edges += 1;
            }
        }

        if vacant {
            for input_node_idx in edge.inputs.iter() {
                self.add_sub_target(state, *input_node_idx, Some(node_idx))?;
            }
        }

        return Ok(true);
    }

    /// Number of edges with commands to run.
    fn command_edge_count(&self) -> usize {
        return self.command_edges;
    }

    /// Reset state.  Clears want and ready sets.
    fn reset(&mut self) {
        self.command_edges = 0;
        self.wanted_edges = 0;
        self.ready.clear();
        self.want.clear();
    }

    /// Returns true if there's more work to be done.
    pub fn more_to_do(&self) -> bool {
        self.wanted_edges > 0 && self.command_edges > 0
    }

    /// Submits a ready edge as a candidate for execution.
    /// The edge may be delayed from running, for example if it's a member of a
    /// currently-full pool.
    pub fn schedule_work(&mut self, state: &State, edge_idx: EdgeIndex) {
        if self.ready.get(&edge_idx).is_some() {
            // This edge has already been scheduled.  We can get here again if an edge
            // and one of its dependencies share an order-only input, or if a node
            // duplicates an out edge (see https://github.com/ninja-build/ninja/pull/519).
            // Avoid scheduling the work again.
            return;
        }

        let edge = state.edge_state.get_edge(edge_idx);
        let mut pool = edge.pool.borrow_mut();
        if pool.should_delay_edge() {
            pool.delay_edge(state, edge_idx);
            pool.retrieve_ready_edges(state, &mut self.ready);
        } else {
            pool.edge_scheduled(state, edge_idx);
            self.ready.insert(edge_idx);
        }
    }

    // Pop a ready edge off the queue of edges to build.
    // Returns NULL if there's no work to do.
    pub fn find_work(&mut self) -> Option<EdgeIndex> {
        match self.ready.iter().next().cloned() {
            Some(idx) => {
                self.ready.remove(&idx);
                Some(idx)
            }
            None => None,
        }
    }

    /// Mark an edge as done building (whether it succeeded or failed).
    pub fn edge_finished(&mut self, state: &mut State, edge_idx: EdgeIndex, result: EdgeResult) {
        let directly_wanted = self.want.get(&edge_idx).unwrap().clone();

        {
            let edge = state.edge_state.get_edge(edge_idx);

            // See if this job frees up any delayed jobs.
            if directly_wanted {
                edge.pool.borrow_mut().edge_finished(state, edge_idx);
            }

            edge.pool.borrow_mut().retrieve_ready_edges(
                state,
                &mut self.ready,
            );
        }


        match result {
            EdgeResult::EdgeSucceeded => {
                if directly_wanted {
                    self.wanted_edges -= 1;
                }
                self.want.remove(&edge_idx);

                state.edge_state.get_edge_mut(edge_idx).outputs_ready = true;

                // Check off any nodes we were waiting for with this edge.
                for output_node_idx in state
                    .edge_state
                    .get_edge_mut(edge_idx)
                    .outputs
                    .clone()
                    .into_iter()
                {
                    self.node_finished(state, output_node_idx);
                }
            }
            _ => {}
        };
    }

    pub fn node_finished(&mut self, state: &mut State, node_idx: NodeIndex) {
        // See if we we want any edges from this node.
        for out_edge_idx in state
            .node_state
            .get_node(node_idx)
            .out_edges()
            .to_owned()
            .into_iter()
        {
            let want_e = self.want.get(&out_edge_idx).cloned();
            if want_e.is_none() {
                continue;
            }

            {
                let oe = state.edge_state.get_edge(out_edge_idx);
                if !oe.all_inputs_ready(state) {
                    continue;
                }
            }

            if want_e.unwrap() {
                self.schedule_work(state, out_edge_idx);
            } else {
                // We do not need to build this edge, but we might need to build one of
                // its dependents.
                self.edge_finished(state, out_edge_idx, EdgeResult::EdgeSucceeded);
            }
        }
    }

    /// Clean the given node during the build.
    /// Return false on error.
    pub fn clean_node(
        &mut self,
        scan: &DependencyScan,
        State: &State,
        node_idx: NodeIndex,
    ) -> Result<(), String> {
        unimplemented!()
    }
}

/*

struct Plan {
  Plan();

  /// Dumps the current state of the plan.
  void Dump();

  enum EdgeResult {
    kEdgeFailed,
    kEdgeSucceeded
  };


  /// Clean the given node during the build.
  /// Return false on error.
  bool CleanNode(DependencyScan* scan, Node* node, string* err);


  /// Reset state.  Clears want and ready sets.
  void Reset();

private:
  bool AddSubTarget(Node* node, Node* dependent, string* err);
  void NodeFinished(Node* node);

  set<Edge*> ready_;

  /// Total number of edges that have commands (not phony).
  int command_edges_;

  /// Total remaining number of wanted edges.
  int wanted_edges_;
};
*/

/// CommandRunner is an interface that wraps running the build
/// subcommands.  This allows tests to abstract out running commands.
/// RealCommandRunner is an implementation that actually runs commands.

/// The result of waiting for a command.
pub struct CommandRunnerResult {
    pub edge: EdgeIndex,
    pub status: ExitStatus,
    pub output: Vec<u8>,
}

impl CommandRunnerResult {
    fn is_success(&self) -> bool {
        match self.status {
            ExitStatus::ExitSuccess => true,
            _ => false,
        }
    }
}

pub trait CommandRunner {
    fn can_run_more(&self) -> bool;
    fn start_command(&mut self, state: &State, edge: EdgeIndex) -> bool;
    /// Wait for a command to complete, or return false if interrupted.
    fn wait_for_command(&mut self) -> Option<CommandRunnerResult>;
    fn get_active_edges(&self) -> Vec<EdgeIndex>;
    fn abort(&mut self);
}

pub enum BuildConfigVerbosity {
    NORMAL,
    QUIET, // No output -- used when testing.
    VERBOSE,
}

/// Options (e.g. verbosity, parallelism) passed to a build.
pub struct BuildConfig {
    pub verbosity: BuildConfigVerbosity,
    pub dry_run: bool,
    pub parallelism: usize,
    pub failures_allowed: usize,
    pub max_load_average: f64,
}

impl BuildConfig {
    pub fn new() -> Self {
        BuildConfig {
            verbosity: BuildConfigVerbosity::NORMAL,
            dry_run: false,
            parallelism: 1,
            failures_allowed: 1,
            max_load_average: -0.0f64,
        }
    }
}

/*
struct BuildConfig {
  BuildConfig() : verbosity(NORMAL), dry_run(false), parallelism(1),
                  failures_allowed(1), max_load_average(-0.0f) {}

  enum Verbosity {
    NORMAL,
    QUIET,  // No output -- used when testing.
    VERBOSE
  };
  Verbosity verbosity;
  bool dry_run;
  int parallelism;
  int failures_allowed;
  /// The maximum load average we must not exceed. A negative value
  /// means that we do not have any limit.
  double max_load_average;
};
*/

/// Builder wraps the build process: starting commands, updating status.
pub struct Builder<'s, 'p, 'a, 'b, 'c>
where
    's: 'a,
{
    state: &'s mut State,
    config: &'p BuildConfig,
    plan: Plan,
    command_runner: Option<Box<CommandRunner + 'p>>,
    disk_interface: &'c DiskInterface,
    scan: DependencyScan<'s, 'a, 'b, 'c>,
    status: BuildStatus<'p>,
}

impl<'s, 'p, 'a, 'b, 'c> Builder<'s, 'p, 'a, 'b, 'c>
where
    's: 'a,
{
    pub fn new(
        state: &'s mut State,
        config: &'p BuildConfig,
        build_log: &'a BuildLog<'s>,
        deps_log: &'b DepsLog,
        disk_interface: &'c DiskInterface,
    ) -> Self {
        Builder {
            state,
            config,
            plan: Plan::new(),
            command_runner: None,
            disk_interface,
            scan: DependencyScan::new(build_log, deps_log, disk_interface),
            status: BuildStatus::new(config),
        }
    }

    /// Add a target to the build, scanning dependencies.
    /// @return false on error.
    pub fn add_target(&mut self, node_idx: NodeIndex) -> Result<(), String> {
        self.scan.recompute_dirty(self.state, node_idx)?;

        if let Some(in_edge) = self.state.node_state.get_node(node_idx).in_edge() {
            if self.state.edge_state.get_edge(in_edge).outputs_ready() {
                return Ok(()); // Nothing to do.
            }
        }

        self.plan.add_target(self.state, node_idx)?;

        Ok(())
    }

    /// Returns true if the build targets are already up to date.
    pub fn is_already_up_to_date(&mut self) -> bool {
        !self.plan.more_to_do()
    }

    /// Run the build.  Returns false on error.
    /// It is an error to call this function when AlreadyUpToDate() is true.
    pub fn build(&mut self) -> Result<(), String> {
        assert!(!self.is_already_up_to_date());

        self.status.plan_has_total_edges(
            self.plan.command_edge_count(),
        );

        let mut pending_commands = 0;
        let mut failures_allowed = self.config.failures_allowed;

        // Set up the command runner if we haven't done so already.
        let config = self.config;
        if self.command_runner.is_none() {
            self.command_runner = Some(if config.dry_run {
                Box::new(DryRunCommandRunner::new())
            } else {
                Box::new(RealCommandRunner::new(config))
            });
        }

        // We are about to start the build process.
        self.status.build_started();

        // This main loop runs the entire build process.
        // It is structured like this:
        // First, we attempt to start as many commands as allowed by the
        // command runner.
        // Second, we attempt to wait for / reap the next finished command.

        while self.plan.more_to_do() {
            // See if we can start any more commands.
            if failures_allowed > 0 && self.command_runner.as_ref().unwrap().can_run_more() {
                if let Some(edge_idx) = self.plan.find_work() {
                    if let Err(e) = self.start_edge(edge_idx) {
                        self.cleanup();
                        self.status.build_finished();
                        return Err(e);
                    };

                    if self.state.edge_state.get_edge(edge_idx).is_phony() {
                        self.plan.edge_finished(
                            self.state,
                            edge_idx,
                            EdgeResult::EdgeSucceeded,
                        );
                    } else {
                        pending_commands += 1;
                    }

                    // We made some progress; go back to the main loop.
                    continue;
                }
            }

            // See if we can reap any finished commands.
            if pending_commands > 0 {
                let result = self.command_runner.as_mut().unwrap().wait_for_command();

                if result.is_none() ||
                    result.as_ref().unwrap().status == ExitStatus::ExitInterrupted
                {
                    self.cleanup();
                    self.status.build_finished();
                    return Err("interrupted by user".to_owned());
                }

                pending_commands -= 1;
                let result = self.finish_command(result.unwrap());
                if let Err(e) = result {
                    self.cleanup();
                    self.status.build_finished();
                    return Err(e);
                }

                let result = result.unwrap();
                if !result.is_success() {
                    if failures_allowed > 0 {
                        failures_allowed -= 1;
                    }
                }

                // We made some progress; start the main loop over.
                continue;
            }

            // If we get here, we cannot make any more progress.
            self.status.build_finished();
            return match failures_allowed {
                0 if config.failures_allowed > 1 => Err("subcommands failed".to_owned()),
                0 => Err("subcommand failed".to_owned()),
                _ if failures_allowed < self.config.failures_allowed => Err(
                    "cannot make progress due to previous errors"
                        .to_owned(),
                ),
                _ => Err("stuck [this is a bug]".to_owned()),
            };
        }

        self.status.build_finished();
        return Ok(());
    }

    fn start_edge(&mut self, edge_idx: EdgeIndex) -> Result<(), String> {
        metric_record!("StartEdge");
        let edge = self.state.edge_state.get_edge(edge_idx);
        if edge.is_phony() {
            return Ok(());
        }

        self.status.build_edge_started(self.state, edge_idx);

        // Create directories necessary for outputs.
        // XXX: this will block; do we care?
        for out_idx in edge.outputs.iter() {
            let path = pathbuf_from_bytes(
                self.state.node_state.get_node(*out_idx).path().to_owned(),
            ).map_err(|e| {
                format!("invalid utf-8 filename: {}", String::from_utf8_lossy(&e))
            })?;
            if let Some(parent) = path.parent() {
                self.disk_interface.make_dirs(parent).map_err(
                    |e| format!("{}", e),
                )?;
            }
        }

        // Create response file, if needed
        // XXX: this may also block; do we care?
        let rspfile = edge.get_unescaped_rspfile(&self.state.node_state);
        if !rspfile.as_ref().is_empty() {
            let content = edge.get_binding(&self.state.node_state, b"rspfile_content");
            let rspfile_path = pathbuf_from_bytes(rspfile.into_owned()).map_err(|e| {
                format!("invalid utf-8 filename: {}", String::from_utf8_lossy(&e))
            })?;
            self.disk_interface
                .write_file(&rspfile_path, content.as_ref())
                .map_err(|_| String::new())?;
        }

        // start command computing and run it
        if !self.command_runner.as_mut().unwrap().start_command(
            self.state,
            edge_idx,
        )
        {
            return Err(format!(
                "command '{}' failed.",
                String::from_utf8_lossy(
                    &edge.evaluate_command(&self.state.node_state),
                )
            ));
        }

        Ok(())
    }

    /// Update status ninja logs following a command termination.
    /// @return false if the build can not proceed further due to a fatal error.
    fn finish_command(
        &mut self,
        mut result: CommandRunnerResult,
    ) -> Result<CommandRunnerResult, String> {
        use errno;

        metric_record!("FinishCommand");

        let edge_idx = result.edge;

        // First try to extract dependencies from the result, if any.
        // This must happen first as it filters the command output (we want
        // to filter /showIncludes output, even on compile failure) and
        // extraction itself can fail, which makes the command fail from a
        // build perspective.
        let mut deps_nodes = Vec::new();

        let (deps_type, deps_prefix) = {
            let edge = self.state.edge_state.get_edge(edge_idx);
            let deps_type = edge.get_binding(&self.state.node_state, b"deps");
            let deps_prefix = edge.get_binding(&self.state.node_state, b"msvc_deps_prefix");
            (deps_type.into_owned(), deps_prefix.into_owned())
        };
        if !deps_type.is_empty() {
            match self.extract_deps(&mut result, deps_type.as_ref(), deps_prefix.as_ref()) {
                Ok(n) => {
                    deps_nodes = n;
                }
                Err(e) => {
                    if result.is_success() {
                        if !result.output.is_empty() {
                            result.output.extend_from_slice(b"\n".as_ref());
                        }
                        result.output.extend_from_slice(e.as_bytes());
                        result.status = ExitStatus::ExitFailure;
                    }
                }
            }
        }

        let (start_time, end_time) = self.status.build_edge_finished(
            self.state,
            edge_idx,
            result.is_success(),
            &result.output,
        );

        if !result.is_success() {
            self.plan.edge_finished(
                self.state,
                edge_idx,
                EdgeResult::EdgeFailed,
            );
            return Ok(result);
        }

        // The rest of this function only applies to successful commands.

        // Restat the edge outputs
        let mut output_mtime = TimeStamp(0);
        let restat = self.state.edge_state.get_edge(edge_idx).get_binding_bool(
            &self.state
                .node_state,
            b"restat",
        );
        if !self.config.dry_run {
            let edge = self.state.edge_state.get_edge(edge_idx);
            let mut node_cleaned = false;
            for o_node_idx in edge.outputs.iter() {
                let o_node = self.state.node_state.get_node(*o_node_idx);
                let path = pathbuf_from_bytes(o_node.path().to_owned()).map_err(|e| {
                    format!("Invalid utf-8 pathname {}", String::from_utf8_lossy(&e))
                })?;
                let new_mtime = self.disk_interface.stat(&path)?;
                if new_mtime > output_mtime {
                    output_mtime = new_mtime;
                }
                if o_node.mtime() == new_mtime && restat {
                    // The rule command did not change the output.  Propagate the clean
                    // state through the build graph.
                    // Note that this also applies to nonexistent outputs (mtime == 0).
                    self.plan.clean_node(&self.scan, self.state, *o_node_idx)?;
                    node_cleaned = true;
                }
            }

            if node_cleaned {
                let mut restat_mtime = TimeStamp(0);
                // If any output was cleaned, find the most recent mtime of any
                // (existing) non-order-only input or the depfile.
                for i_idx in edge.inputs[edge.non_order_only_deps_range()].iter() {
                    let path = pathbuf_from_bytes(
                        self.state.node_state.get_node(*i_idx).path().to_owned(),
                    ).map_err(|e| {
                        format!("invalid utf-8 filename: {}", String::from_utf8_lossy(&e))
                    })?;
                    let input_mtime = self.disk_interface.stat(&path)?;
                    if input_mtime > restat_mtime {
                        restat_mtime = input_mtime;
                    }
                }

                let depfile = edge.get_unescaped_depfile(&self.state.node_state);
                if restat_mtime.0 != 0 && deps_type.is_empty() && !depfile.is_empty() {
                    let path = pathbuf_from_bytes(depfile.into_owned()).map_err(|e| {
                        format!("invalid utf-8 filename: {}", String::from_utf8_lossy(&e))
                    })?;
                    let depfile_mtime = self.disk_interface.stat(&path)?;
                    if depfile_mtime > restat_mtime {
                        restat_mtime = depfile_mtime;
                    }
                }

                // The total number of edges in the plan may have changed as a result
                // of a restat.
                self.status.plan_has_total_edges(
                    self.plan.command_edge_count(),
                );
                output_mtime = restat_mtime;
            }
        }

        self.plan.edge_finished(
            self.state,
            edge_idx,
            EdgeResult::EdgeSucceeded,
        );

        let edge = self.state.edge_state.get_edge(edge_idx);
        let rspfile = edge.get_unescaped_rspfile(&self.state.node_state);
        if !rspfile.is_empty() && !KEEP_RSP {
            if let Ok(path) = pathbuf_from_bytes(rspfile.into_owned()) {
                let _ = self.disk_interface.remove_file(&path);
            };
        }

        if let Some(build_log) = self.scan.build_log() {
            build_log
                .record_command(self.state, edge_idx, start_time, end_time, output_mtime)
                .map_err(|e| {
                    format!("Error writing to build log: {}", errno::errno())
                })?;
        }

        if !deps_type.is_empty() && !self.config.dry_run {
            assert!(edge.outputs.len() == 1);
            //or it should have been rejected by parser.
            let out_idx = edge.outputs[0];
            let out = self.state.node_state.get_node(out_idx);
            let path = pathbuf_from_bytes(out.path().to_owned()).map_err(|e| {
                format!("Invalid utf-8 pathname {}", String::from_utf8_lossy(&e))
            })?;

            let deps_mtime = self.disk_interface.stat(&path)?;

            self.scan
                .deps_log()
                .record_deps(self.state, out_idx, deps_mtime, &deps_nodes)
                .map_err(|e| format!("Error writing to deps log: {}", errno::errno()))?;
        }

        Ok(result)
    }

    /// Clean up after interrupted commands by deleting output files.
    pub fn cleanup(&mut self) {
        if self.command_runner.is_none() {
            return;
        }
        let command_runner = self.command_runner.as_mut().unwrap();

        let active_edges = command_runner.get_active_edges();
        command_runner.abort();
        for edge_idx in active_edges.into_iter() {
            let edge = self.state.edge_state.get_edge(edge_idx);
            let depfile = edge.get_unescaped_depfile(&self.state.node_state)
                .into_owned();
            for out_idx in edge.outputs.iter() {
                // Only delete this output if it was actually modified.  This is
                // important for things like the generator where we don't want to
                // delete the manifest file if we can avoid it.  But if the rule
                // uses a depfile, always delete.  (Consider the case where we
                // need to rebuild an output because of a modified header file
                // mentioned in a depfile, and the command touches its depfile
                // but is interrupted before it touches its output file.)
                let out_node = self.state.node_state.get_node(*out_idx);
                match pathbuf_from_bytes(out_node.path().to_owned()) {
                    Err(e) => {
                        error!("invalid utf-8 filename: {}", String::from_utf8_lossy(&e));
                    }
                    Ok(path) => {
                        match self.disk_interface.stat(&path) {
                            Err(e) => {
                                error!("{}", e);
                            }
                            Ok(new_mtime) => {
                                if !depfile.is_empty() || out_node.mtime() != new_mtime {
                                    let _ = self.disk_interface.remove_file(&path);
                                }
                            }
                        }
                    }
                }
            }
            if !depfile.is_empty() {
                match pathbuf_from_bytes(depfile) {
                    Err(e) => {
                        error!("invalid utf-8 filename: {}", String::from_utf8_lossy(&e));
                    }
                    Ok(path) => {
                        let _ = self.disk_interface.remove_file(&path);
                    }
                };
            }
        }
    }

    fn extract_deps(
        &self,
        result: &mut CommandRunnerResult,
        deps_type: &[u8],
        deps_prefix: &[u8],
    ) -> Result<Vec<NodeIndex>, String> {
        if deps_type == b"msvc" {
            /*
    CLParser parser;
    string output;
    if (!parser.Parse(result->output, deps_prefix, &output, err))
      return false;
    result->output = output;
    for (set<string>::iterator i = parser.includes_.begin();
         i != parser.includes_.end(); ++i) {
      // ~0 is assuming that with MSVC-parsed headers, it's ok to always make
      // all backslashes (as some of the slashes will certainly be backslashes
      // anyway). This could be fixed if necessary with some additional
      // complexity in IncludesNormalize::Relativize.
      deps_nodes->push_back(state_->GetNode(*i, ~0u));
    }
*/
            return Ok(Vec::new());
            unimplemented!{}
        } else if deps_type == b"gcc" {
            /*
    string depfile = result->edge->GetUnescapedDepfile();
    if (depfile.empty()) {
      *err = string("edge with deps=gcc but no depfile makes no sense");
      return false;
    }

    // Read depfile content.  Treat a missing depfile as empty.
    string content;
    switch (disk_interface_->ReadFile(depfile, &content, err)) {
    case DiskInterface::Okay:
      break;
    case DiskInterface::NotFound:
      err->clear();
      break;
    case DiskInterface::OtherError:
      return false;
    }
    if (content.empty())
      return true;

    DepfileParser deps;
    if (!deps.Parse(&content, err))
      return false;

    // XXX check depfile matches expected output.
    deps_nodes->reserve(deps.ins_.size());
    for (vector<StringPiece>::iterator i = deps.ins_.begin();
         i != deps.ins_.end(); ++i) {
      uint64_t slash_bits;
      if (!CanonicalizePath(const_cast<char*>(i->str_), &i->len_, &slash_bits,
                            err))
        return false;
      deps_nodes->push_back(state_->GetNode(*i, slash_bits));
    }

    if (!g_keep_depfile) {
      if (disk_interface_->RemoveFile(depfile) < 0) {
        *err = string("deleting depfile: ") + strerror(errno) + string("\n");
        return false;
      }
    }
*/
            unimplemented!{}
        } else {
            fatal!("unknown deps type '{}'", String::from_utf8_lossy(deps_type));
            unreachable!();
        }
    }
}

impl<'s, 'p, 'a, 'b, 'c> Drop for Builder<'s, 'p, 'a, 'b, 'c> {
    fn drop(&mut self) {
        self.cleanup();
    }
}

/*
struct Builder {
  Builder(State* state, const BuildConfig& config,
          BuildLog* build_log, DepsLog* deps_log,
          DiskInterface* disk_interface);
  ~Builder();

  /// Clean up after interrupted commands by deleting output files.
  void Cleanup();

  Node* AddTarget(const string& name, string* err);




  /// Used for tests.
  void SetBuildLog(BuildLog* log) {
    scan_.set_build_log(log);
  }

  State* state_;
  const BuildConfig& config_;
  Plan plan_;
  auto_ptr<CommandRunner> command_runner_;
  BuildStatus* status_;

 private:
   bool ExtractDeps(CommandRunner::Result* result, const string& deps_type,
                    const string& deps_prefix, vector<Node*>* deps_nodes,
                    string* err);

  DiskInterface* disk_interface_;
  DependencyScan scan_;

  // Unimplemented copy ctor and operator= ensure we don't copy the auto_ptr.
  Builder(const Builder &other);        // DO NOT IMPLEMENT
  void operator=(const Builder &other); // DO NOT IMPLEMENT
};
*/

enum BuildStatusEdgeStatus {
    EdgeStarted,
    EdgeFinished,
}

/// Tracks the status of a build: completion fraction, printing updates.
struct BuildStatus<'a> {
    config: &'a BuildConfig,

    /// Time the build started.
    start_time_millis: u64,

    started_edges: usize,
    running_edges: BTreeMap<EdgeIndex, u64>,
    /// Map of running edge to time the edge started running.
    finished_edges: usize,
    total_edges: usize,

    /// The custom progress status format to use.
    progress_status_format: Vec<u8>,

    /// Prints progress output.
    printer: LinePrinter,

    overall_rate: RefCell<RateInfo>,
    current_rate: RefCell<SlidingRateInfo>,
}

impl<'a> BuildStatus<'a> {
    pub fn new(config: &'a BuildConfig) -> Self {
        let v = BuildStatus {
            config,

            start_time_millis: get_time_millis(),

            started_edges: 0,
            running_edges: BTreeMap::new(),
            finished_edges: 0,
            total_edges: 0,

            progress_status_format: Vec::new(), // TODO
            printer: LinePrinter::new(),

            overall_rate: RefCell::new(RateInfo::new()),
            current_rate: RefCell::new(SlidingRateInfo::new(config.parallelism)),
        };
        return v;
        unimplemented!{}
    }

    pub fn plan_has_total_edges(&mut self, total: usize) {
        self.total_edges = total;
    }

    pub fn build_started(&mut self) {
        self.overall_rate.borrow_mut().restart();
        self.current_rate.borrow_mut().restart();
    }

    pub fn build_finished(&mut self) {
        self.printer.set_console_locked(false);
        self.printer.print_on_new_line(b"");
    }

    pub fn build_edge_started(&mut self, state: &State, edge_idx: EdgeIndex) {
        let start_time = get_time_millis() - self.start_time_millis;
        self.running_edges.insert(edge_idx, start_time);
        self.started_edges += 1;

        let edge_use_console = state.edge_state.get_edge(edge_idx).use_console();
        if edge_use_console || self.printer.is_smart_terminal() {
            self.print_status(state, edge_idx, BuildStatusEdgeStatus::EdgeStarted);
        }

        if edge_use_console {
            self.printer.set_console_locked(true);
        }
    }

    pub fn build_edge_finished(
        &mut self,
        state: &State,
        edge_idx: EdgeIndex,
        success: bool,
        output: &[u8],
    ) -> (u64, u64) {
        let now = get_time_millis();
        self.finished_edges += 1;

        let start_time = self.running_edges.remove(&edge_idx).unwrap();
        let end_time = now - self.start_time_millis;

        if state.edge_state.get_edge(edge_idx).use_console() {
            self.printer.set_console_locked(false);
        }

        match self.config.verbosity {
            BuildConfigVerbosity::QUIET => {
                return (start_time, end_time);
            }
            _ => {}
        };

        /*
  if (!edge->use_console())
    PrintStatus(edge, kEdgeFinished);

  // Print the command that is spewing before printing its output.
  if (!success) {
    string outputs;
    for (vector<Node*>::const_iterator o = edge->outputs_.begin();
         o != edge->outputs_.end(); ++o)
      outputs += (*o)->path() + " ";

    printer_.PrintOnNewLine("FAILED: " + outputs + "\n");
    printer_.PrintOnNewLine(edge->EvaluateCommand() + "\n");
  }

  if (!output.empty()) {
    // ninja sets stdout and stderr of subprocesses to a pipe, to be able to
    // check if the output is empty. Some compilers, e.g. clang, check
    // isatty(stderr) to decide if they should print colored output.
    // To make it possible to use colored output with ninja, subprocesses should
    // be run with a flag that forces them to always print color escape codes.
    // To make sure these escape codes don't show up in a file if ninja's output
    // is piped to a file, ninja strips ansi escape codes again if it's not
    // writing to a |smart_terminal_|.
    // (Launching subprocesses in pseudo ttys doesn't work because there are
    // only a few hundred available on some systems, and ninja can launch
    // thousands of parallel compile commands.)
    // TODO: There should be a flag to disable escape code stripping.
    string final_output;
    if (!printer_.is_smart_terminal())
      final_output = StripAnsiEscapeCodes(output);
    else
      final_output = output;

#ifdef _WIN32
    // Fix extra CR being added on Windows, writing out CR CR LF (#773)
    _setmode(_fileno(stdout), _O_BINARY);  // Begin Windows extra CR fix
#endif

    printer_.PrintOnNewLine(final_output);

#ifdef _WIN32
    _setmode(_fileno(stdout), _O_TEXT);  // End Windows extra CR fix
#endif
  }
*/
        return (start_time, end_time);
        unimplemented!();
    }

    /// Format the progress status string by replacing the placeholders.
    /// See the user manual for more information about the available
    /// placeholders.
    /// @param progress_status_format The format of the progress status.
    /// @param status The status of the edge.
    pub fn format_progress_status(
        progress_status_format: &[u8],
        status: BuildStatusEdgeStatus,
    ) -> Vec<u8> {
        return Vec::new();
        unimplemented!()
    }

    fn print_status(&self, state: &State, edge_idx: EdgeIndex, status: BuildStatusEdgeStatus) {
        let force_full_command = match self.config.verbosity {
            BuildConfigVerbosity::QUIET => {
                return;
            }
            BuildConfigVerbosity::VERBOSE => true,
            BuildConfigVerbosity::NORMAL => false,
        };

        let edge = state.edge_state.get_edge(edge_idx);
        let mut desc_or_cmd = edge.get_binding(&state.node_state, b"description");
        if desc_or_cmd.is_empty() || force_full_command {
            desc_or_cmd = edge.get_binding(&state.node_state, b"command");
        }

        let mut to_print = Self::format_progress_status(&self.progress_status_format, status);
        to_print.extend_from_slice(&desc_or_cmd);
        let ty = if force_full_command {
            LinePrinterLineType::Full
        } else {
            LinePrinterLineType::Elide
        };
        self.printer.print(&to_print, ty);
    }
}
/*
struct BuildStatus {
  explicit BuildStatus(const BuildConfig& config);
  void PlanHasTotalEdges(int total);
  void BuildEdgeStarted(Edge* edge);
  void BuildEdgeFinished(Edge* edge, bool success, const string& output,
                         int* start_time, int* end_time);
  void BuildStarted();
  void BuildFinished();



 private:
  void PrintStatus(Edge* edge, EdgeStatus status);



  template<size_t S>
  void SnprintfRate(double rate, char(&buf)[S], const char* format) const {
    if (rate == -1)
      snprintf(buf, S, "?");
    else
      snprintf(buf, S, format, rate);
  }
*/

struct RateInfo {
    rate: f64,
    stopwatch: Stopwatch,
}

impl RateInfo {
    pub fn new() -> Self {
        RateInfo {
            rate: -1f64,
            stopwatch: Stopwatch::new(),
        }
    }

    pub fn restart(&mut self) {
        self.stopwatch.restart()
    }
}

/*
  struct RateInfo {
    RateInfo() : rate_(-1) {}

    void Restart() { stopwatch_.Restart(); }
    double Elapsed() const { return stopwatch_.Elapsed(); }
    double rate() { return rate_; }

    void UpdateRate(int edges) {
      if (edges && stopwatch_.Elapsed())
        rate_ = edges / stopwatch_.Elapsed();
    }

  private:
    double rate_;
    Stopwatch stopwatch_;
  };

  */

struct SlidingRateInfo {
    rate: f64,
    stopwatch: Stopwatch,
    max_len: usize,
    times: VecDeque<f64>,
    last_update: isize,
}

impl SlidingRateInfo {
    pub fn new(n: usize) -> Self {
        SlidingRateInfo {
            rate: -1.0f64,
            stopwatch: Stopwatch::new(),
            max_len: n,
            times: VecDeque::new(),
            last_update: -1,
        }
    }

    pub fn restart(&mut self) {
        self.stopwatch.restart();
    }
}

/*
  struct SlidingRateInfo {
    SlidingRateInfo(int n) : rate_(-1), N(n), last_update_(-1) {}

    void Restart() { stopwatch_.Restart(); }
    double rate() { return rate_; }

    void UpdateRate(int update_hint) {
      if (update_hint == last_update_)
        return;
      last_update_ = update_hint;

      if (times_.size() == N)
        times_.pop();
      times_.push(stopwatch_.Elapsed());
      if (times_.back() != times_.front())
        rate_ = times_.size() / (times_.back() - times_.front());
    }

  private:
    double rate_;
    Stopwatch stopwatch_;
    const size_t N;
    queue<double> times_;
    int last_update_;
  };

  mutable RateInfo overall_rate_;
  mutable SlidingRateInfo current_rate_;
};

#endif  // NINJA_BUILD_H_
*/

/*

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

#include "build.h"

#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <functional>

#ifdef _WIN32
#include <fcntl.h>
#include <io.h>
#endif

#if defined(__SVR4) && defined(__sun)
#include <sys/termios.h>
#endif

#include "build_log.h"
#include "clparser.h"
#include "debug_flags.h"
#include "depfile_parser.h"
#include "deps_log.h"
#include "disk_interface.h"
#include "graph.h"
#include "state.h"
#include "subprocess.h"
#include "util.h"
*/

use std::collections::VecDeque;

struct DryRunCommandRunner {
    finished: VecDeque<EdgeIndex>,
}

impl DryRunCommandRunner {
    pub fn new() -> Self {
        DryRunCommandRunner { finished: VecDeque::new() }
    }
}

impl CommandRunner for DryRunCommandRunner {
    fn can_run_more(&self) -> bool {
        true
    }

    fn start_command(&mut self, _: &State, edge: EdgeIndex) -> bool {
        self.finished.push_back(edge);
        true
    }

    fn wait_for_command(&mut self) -> Option<CommandRunnerResult> {
        match self.finished.pop_front() {
            None => None,
            Some(e) => Some(CommandRunnerResult {
                edge: e,
                status: ExitStatus::ExitSuccess,
                output: Vec::new(),
            }),
        }
    }

    fn get_active_edges(&self) -> Vec<EdgeIndex> {
        Vec::new()
    }

    fn abort(&mut self) {
        //do nothing
    }
}
/*

BuildStatus::BuildStatus(const BuildConfig& config)
    : config_(config),
      start_time_millis_(GetTimeMillis()),
      started_edges_(0), finished_edges_(0), total_edges_(0),
      progress_status_format_(NULL),
      overall_rate_(), current_rate_(config.parallelism) {

  // Don't do anything fancy in verbose mode.
  if (config_.verbosity != BuildConfig::NORMAL)
    printer_.set_smart_terminal(false);

  progress_status_format_ = getenv("NINJA_STATUS");
  if (!progress_status_format_)
    progress_status_format_ = "[%f/%t] ";
}

void BuildStatus::PlanHasTotalEdges(int total) {
  total_edges_ = total;
}

void BuildStatus::BuildEdgeStarted(Edge* edge) {
  int start_time = (int)(GetTimeMillis() - start_time_millis_);
  running_edges_.insert(make_pair(edge, start_time));
  ++started_edges_;

  if (edge->use_console() || printer_.is_smart_terminal())
    PrintStatus(edge, kEdgeStarted);

  if (edge->use_console())
    printer_.SetConsoleLocked(true);
}

void BuildStatus::BuildEdgeFinished(Edge* edge,
                                    bool success,
                                    const string& output,
                                    int* start_time,
                                    int* end_time) {
  int64_t now = GetTimeMillis();

  ++finished_edges_;

  RunningEdgeMap::iterator i = running_edges_.find(edge);
  *start_time = i->second;
  *end_time = (int)(now - start_time_millis_);
  running_edges_.erase(i);

  if (edge->use_console())
    printer_.SetConsoleLocked(false);

  if (config_.verbosity == BuildConfig::QUIET)
    return;

  if (!edge->use_console())
    PrintStatus(edge, kEdgeFinished);

  // Print the command that is spewing before printing its output.
  if (!success) {
    string outputs;
    for (vector<Node*>::const_iterator o = edge->outputs_.begin();
         o != edge->outputs_.end(); ++o)
      outputs += (*o)->path() + " ";

    printer_.PrintOnNewLine("FAILED: " + outputs + "\n");
    printer_.PrintOnNewLine(edge->EvaluateCommand() + "\n");
  }

  if (!output.empty()) {
    // ninja sets stdout and stderr of subprocesses to a pipe, to be able to
    // check if the output is empty. Some compilers, e.g. clang, check
    // isatty(stderr) to decide if they should print colored output.
    // To make it possible to use colored output with ninja, subprocesses should
    // be run with a flag that forces them to always print color escape codes.
    // To make sure these escape codes don't show up in a file if ninja's output
    // is piped to a file, ninja strips ansi escape codes again if it's not
    // writing to a |smart_terminal_|.
    // (Launching subprocesses in pseudo ttys doesn't work because there are
    // only a few hundred available on some systems, and ninja can launch
    // thousands of parallel compile commands.)
    // TODO: There should be a flag to disable escape code stripping.
    string final_output;
    if (!printer_.is_smart_terminal())
      final_output = StripAnsiEscapeCodes(output);
    else
      final_output = output;

#ifdef _WIN32
    // Fix extra CR being added on Windows, writing out CR CR LF (#773)
    _setmode(_fileno(stdout), _O_BINARY);  // Begin Windows extra CR fix
#endif

    printer_.PrintOnNewLine(final_output);

#ifdef _WIN32
    _setmode(_fileno(stdout), _O_TEXT);  // End Windows extra CR fix
#endif
  }
}

void BuildStatus::BuildStarted() {
  overall_rate_.Restart();
  current_rate_.Restart();
}

void BuildStatus::BuildFinished() {
  printer_.SetConsoleLocked(false);
  printer_.PrintOnNewLine("");
}

string BuildStatus::FormatProgressStatus(
    const char* progress_status_format, EdgeStatus status) const {
  string out;
  char buf[32];
  int percent;
  for (const char* s = progress_status_format; *s != '\0'; ++s) {
    if (*s == '%') {
      ++s;
      switch (*s) {
      case '%':
        out.push_back('%');
        break;

        // Started edges.
      case 's':
        snprintf(buf, sizeof(buf), "%d", started_edges_);
        out += buf;
        break;

        // Total edges.
      case 't':
        snprintf(buf, sizeof(buf), "%d", total_edges_);
        out += buf;
        break;

        // Running edges.
      case 'r': {
        int running_edges = started_edges_ - finished_edges_;
        // count the edge that just finished as a running edge
        if (status == kEdgeFinished)
          running_edges++;
        snprintf(buf, sizeof(buf), "%d", running_edges);
        out += buf;
        break;
      }

        // Unstarted edges.
      case 'u':
        snprintf(buf, sizeof(buf), "%d", total_edges_ - started_edges_);
        out += buf;
        break;

        // Finished edges.
      case 'f':
        snprintf(buf, sizeof(buf), "%d", finished_edges_);
        out += buf;
        break;

        // Overall finished edges per second.
      case 'o':
        overall_rate_.UpdateRate(finished_edges_);
        SnprintfRate(overall_rate_.rate(), buf, "%.1f");
        out += buf;
        break;

        // Current rate, average over the last '-j' jobs.
      case 'c':
        current_rate_.UpdateRate(finished_edges_);
        SnprintfRate(current_rate_.rate(), buf, "%.1f");
        out += buf;
        break;

        // Percentage
      case 'p':
        percent = (100 * finished_edges_) / total_edges_;
        snprintf(buf, sizeof(buf), "%3i%%", percent);
        out += buf;
        break;

      case 'e': {
        double elapsed = overall_rate_.Elapsed();
        snprintf(buf, sizeof(buf), "%.3f", elapsed);
        out += buf;
        break;
      }

      default:
        Fatal("unknown placeholder '%%%c' in $NINJA_STATUS", *s);
        return "";
      }
    } else {
      out.push_back(*s);
    }
  }

  return out;
}

void BuildStatus::PrintStatus(Edge* edge, EdgeStatus status) {
  if (config_.verbosity == BuildConfig::QUIET)
    return;

  bool force_full_command = config_.verbosity == BuildConfig::VERBOSE;

  string to_print = edge->GetBinding("description");
  if (to_print.empty() || force_full_command)
    to_print = edge->GetBinding("command");

  to_print = FormatProgressStatus(progress_status_format_, status) + to_print;

  printer_.Print(to_print,
                 force_full_command ? LinePrinter::FULL : LinePrinter::ELIDE);
}

Plan::Plan() : command_edges_(0), wanted_edges_(0) {}

bool Plan::CleanNode(DependencyScan* scan, Node* node, string* err) {
  node->set_dirty(false);

  for (vector<Edge*>::const_iterator oe = node->out_edges().begin();
       oe != node->out_edges().end(); ++oe) {
    // Don't process edges that we don't actually want.
    map<Edge*, bool>::iterator want_e = want_.find(*oe);
    if (want_e == want_.end() || !want_e->second)
      continue;

    // Don't attempt to clean an edge if it failed to load deps.
    if ((*oe)->deps_missing_)
      continue;

    // If all non-order-only inputs for this edge are now clean,
    // we might have changed the dirty state of the outputs.
    vector<Node*>::iterator
        begin = (*oe)->inputs_.begin(),
        end = (*oe)->inputs_.end() - (*oe)->order_only_deps_;
    if (find_if(begin, end, mem_fun(&Node::dirty)) == end) {
      // Recompute most_recent_input.
      Node* most_recent_input = NULL;
      for (vector<Node*>::iterator i = begin; i != end; ++i) {
        if (!most_recent_input || (*i)->mtime() > most_recent_input->mtime())
          most_recent_input = *i;
      }

      // Now, this edge is dirty if any of the outputs are dirty.
      // If the edge isn't dirty, clean the outputs and mark the edge as not
      // wanted.
      bool outputs_dirty = false;
      if (!scan->RecomputeOutputsDirty(*oe, most_recent_input,
                                       &outputs_dirty, err)) {
        return false;
      }
      if (!outputs_dirty) {
        for (vector<Node*>::iterator o = (*oe)->outputs_.begin();
             o != (*oe)->outputs_.end(); ++o) {
          if (!CleanNode(scan, *o, err))
            return false;
        }

        want_e->second = false;
        --wanted_edges_;
        if (!(*oe)->is_phony())
          --command_edges_;
      }
    }
  }
  return true;
}

void Plan::Dump() {
  printf("pending: %d\n", (int)want_.size());
  for (map<Edge*, bool>::iterator e = want_.begin(); e != want_.end(); ++e) {
    if (e->second)
      printf("want ");
    e->first->Dump();
  }
  printf("ready: %d\n", (int)ready_.size());
}
*/

struct RealCommandRunner<'a> {
    config: &'a BuildConfig,
    subprocs: SubprocessSet<EdgeIndex>,
}

impl<'a> RealCommandRunner<'a> {
    pub fn new(config: &'a BuildConfig) -> Self {
        RealCommandRunner {
            config,
            subprocs: SubprocessSet::new(),
        }
    }
}

impl<'a> CommandRunner for RealCommandRunner<'a> {
    fn can_run_more(&self) -> bool {
        let subproc_number = self.subprocs.running().len() + self.subprocs.finished().len();
        if subproc_number >= self.config.parallelism {
            return false;
        }
        if self.subprocs.running().is_empty() {
            return true;
        }
        if self.config.max_load_average <= 0.0f64 {
            return true;
        }
        if get_load_average().unwrap_or(-0.0f64) < self.config.max_load_average {
            return true;
        }
        return false;
    }

    fn start_command(&mut self, state: &State, edge_idx: EdgeIndex) -> bool {
        let edge = state.edge_state.get_edge(edge_idx);
        let command = edge.evaluate_command(&state.node_state);

        return self.subprocs
            .add(&command, edge.use_console(), edge_idx)
            .is_some();
    }

    fn wait_for_command(&mut self) -> Option<CommandRunnerResult> {
        let (mut subproc, edge_idx) = loop {
            if let Some(next_finished) = self.subprocs.next_finished() {
                break next_finished;
            }
            if self.subprocs.do_work().is_err() {
                //interrupted
                return None;
            }
        };

        let status = subproc.finish();
        let output = subproc.output().to_owned();
        Some(CommandRunnerResult {
            status,
            output,
            edge: edge_idx,
        })
    }

    fn get_active_edges(&self) -> Vec<EdgeIndex> {
        self.subprocs.iter().map(|x| x.1).collect()
    }

    fn abort(&mut self) {
        self.subprocs.clear();
    }
}

/*
struct RealCommandRunner : public CommandRunner {
  explicit RealCommandRunner(const BuildConfig& config) : config_(config) {}
  virtual ~RealCommandRunner() {}
  virtual bool CanRunMore();
  virtual bool StartCommand(Edge* edge);
  virtual bool WaitForCommand(Result* result);
  virtual vector<Edge*> GetActiveEdges();
  virtual void Abort();

  const BuildConfig& config_;
  SubprocessSet subprocs_;
  map<Subprocess*, Edge*> subproc_to_edge_;
};

bool RealCommandRunner::CanRunMore() {
  size_t subproc_number =
      subprocs_.running_.size() + subprocs_.finished_.size();
  return (int)subproc_number < config_.parallelism
    && ((subprocs_.running_.empty() || config_.max_load_average <= 0.0f)
        || GetLoadAverage() < config_.max_load_average);
}

bool RealCommandRunner::StartCommand(Edge* edge) {
  string command = edge->EvaluateCommand();
  Subprocess* subproc = subprocs_.Add(command, edge->use_console());
  if (!subproc)
    return false;
  subproc_to_edge_.insert(make_pair(subproc, edge));

  return true;
}

bool RealCommandRunner::WaitForCommand(Result* result) {
  Subprocess* subproc;
  while ((subproc = subprocs_.NextFinished()) == NULL) {
    bool interrupted = subprocs_.DoWork();
    if (interrupted)
      return false;
  }

  result->status = subproc->Finish();
  result->output = subproc->GetOutput();

  map<Subprocess*, Edge*>::iterator e = subproc_to_edge_.find(subproc);
  result->edge = e->second;
  subproc_to_edge_.erase(e);

  delete subproc;
  return true;
}

Builder::Builder(State* state, const BuildConfig& config,
                 BuildLog* build_log, DepsLog* deps_log,
                 DiskInterface* disk_interface)
    : state_(state), config_(config), disk_interface_(disk_interface),
      scan_(state, build_log, deps_log, disk_interface) {
  status_ = new BuildStatus(config);
}

Node* Builder::AddTarget(const string& name, string* err) {
  Node* node = state_->LookupNode(name);
  if (!node) {
    *err = "unknown target: '" + name + "'";
    return NULL;
  }
  if (!AddTarget(node, err))
    return NULL;
  return node;
}

bool Builder::AddTarget(Node* node, string* err) {
  if (!scan_.RecomputeDirty(node, err))
    return false;

  if (Edge* in_edge = node->in_edge()) {
    if (in_edge->outputs_ready())
      return true;  // Nothing to do.
  }

  if (!plan_.AddTarget(node, err))
    return false;

  return true;
}



bool Builder::ExtractDeps(CommandRunner::Result* result,
                          const string& deps_type,
                          const string& deps_prefix,
                          vector<Node*>* deps_nodes,
                          string* err) {
  if (deps_type == "msvc") {
    CLParser parser;
    string output;
    if (!parser.Parse(result->output, deps_prefix, &output, err))
      return false;
    result->output = output;
    for (set<string>::iterator i = parser.includes_.begin();
         i != parser.includes_.end(); ++i) {
      // ~0 is assuming that with MSVC-parsed headers, it's ok to always make
      // all backslashes (as some of the slashes will certainly be backslashes
      // anyway). This could be fixed if necessary with some additional
      // complexity in IncludesNormalize::Relativize.
      deps_nodes->push_back(state_->GetNode(*i, ~0u));
    }
  } else
  if (deps_type == "gcc") {
    string depfile = result->edge->GetUnescapedDepfile();
    if (depfile.empty()) {
      *err = string("edge with deps=gcc but no depfile makes no sense");
      return false;
    }

    // Read depfile content.  Treat a missing depfile as empty.
    string content;
    switch (disk_interface_->ReadFile(depfile, &content, err)) {
    case DiskInterface::Okay:
      break;
    case DiskInterface::NotFound:
      err->clear();
      break;
    case DiskInterface::OtherError:
      return false;
    }
    if (content.empty())
      return true;

    DepfileParser deps;
    if (!deps.Parse(&content, err))
      return false;

    // XXX check depfile matches expected output.
    deps_nodes->reserve(deps.ins_.size());
    for (vector<StringPiece>::iterator i = deps.ins_.begin();
         i != deps.ins_.end(); ++i) {
      uint64_t slash_bits;
      if (!CanonicalizePath(const_cast<char*>(i->str_), &i->len_, &slash_bits,
                            err))
        return false;
      deps_nodes->push_back(state_->GetNode(*i, slash_bits));
    }

    if (!g_keep_depfile) {
      if (disk_interface_->RemoveFile(depfile) < 0) {
        *err = string("deleting depfile: ") + strerror(errno) + string("\n");
        return false;
      }
    }
  } else {
    Fatal("unknown deps type '%s'", deps_type.c_str());
  }

  return true;
}


*/

#[cfg(test)]
mod tests {
    use super::*;
    use super::super::test::TestWithStateAndVFS;
    use super::super::graph::Node;

    /// Fixture for tests involving Plan.
    // Though Plan doesn't use State, it's useful to have one around
    // to create Nodes and Edges.
    struct PlanTestData {
        plan: Plan,
    }

    impl Default for PlanTestData {
        fn default() -> Self {
            PlanTestData { plan: Plan::new() }
        }
    }

    type PlanTest = TestWithStateAndVFS<PlanTestData>;

    impl PlanTest {
        pub fn new() -> Self {
            Self::new_with_builtin_rule()
        }
    }

    /*

/// Fixture for tests involving Plan.
// Though Plan doesn't use State, it's useful to have one around
// to create Nodes and Edges.
struct PlanTest : public StateTestWithBuiltinRules {
  Plan plan_;

  /// Because FindWork does not return Edges in any sort of predictable order,
  // provide a means to get available Edges in order and in a format which is
  // easy to write tests around.
  void FindWorkSorted(deque<Edge*>* ret, int count) {
    struct CompareEdgesByOutput {
      static bool cmp(const Edge* a, const Edge* b) {
        return a->outputs_[0]->path() < b->outputs_[0]->path();
      }
    };

    for (int i = 0; i < count; ++i) {
      ASSERT_TRUE(plan_.more_to_do());
      Edge* edge = plan_.FindWork();
      ASSERT_TRUE(edge);
      ret->push_back(edge);
    }
    ASSERT_FALSE(plan_.FindWork());
    sort(ret->begin(), ret->end(), CompareEdgesByOutput::cmp);
  }

  void TestPoolWithDepthOne(const char *test_case);
};
*/
    #[test]
    fn plantest_basic() {
        let mut plantest = PlanTest::new();
        plantest.assert_parse(
            concat!("build out: cat mid\n", "build mid: cat in\n").as_bytes(),
        );
        plantest.assert_with_node_mut(b"mid", Node::mark_dirty);
        plantest.assert_with_node_mut(b"out", Node::mark_dirty);
        let out_node_idx = plantest.assert_node_idx(b"out");

        let mut state = plantest.state.borrow_mut();
        let state = &mut *state;
        let plan = &mut plantest.other.plan;
        assert_eq!(Ok(true), plan.add_target(state, out_node_idx));
        assert_eq!(true, plan.more_to_do());

        let edge_idx = plan.find_work().unwrap();
        {
            let edge = state.edge_state.get_edge(edge_idx);
            let input0 = edge.inputs[0];
            assert_eq!(b"in", state.node_state.get_node(input0).path());
            let output0 = edge.outputs[0];
            assert_eq!(b"mid", state.node_state.get_node(output0).path());
        }
        assert_eq!(None, plan.find_work());
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);
        let edge_idx = plan.find_work().unwrap();
        {
            let edge = state.edge_state.get_edge(edge_idx);
            let input0 = edge.inputs[0];
            assert_eq!(b"mid", state.node_state.get_node(input0).path());
            let output0 = edge.outputs[0];
            assert_eq!(b"out", state.node_state.get_node(output0).path());
        }
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        assert_eq!(false, plan.more_to_do());
        assert_eq!(None, plan.find_work());
    }

    // Test that two outputs from one rule can be handled as inputs to the next.
    #[test]
    fn plantest_double_output_direct() {
        let mut plantest = PlanTest::new();
        plantest.assert_parse(
            concat!("build out: cat mid1 mid2\n", "build mid1 mid2: cat in\n").as_bytes(),
        );
        plantest.assert_with_node_mut(b"mid1", Node::mark_dirty);
        plantest.assert_with_node_mut(b"mid2", Node::mark_dirty);
        plantest.assert_with_node_mut(b"out", Node::mark_dirty);

        let out_node_idx = plantest.assert_node_idx(b"out");
        let mut state = plantest.state.borrow_mut();
        let state = &mut *state;
        let plan = &mut plantest.other.plan;
        assert_eq!(Ok(true), plan.add_target(state, out_node_idx));
        assert_eq!(true, plan.more_to_do());

        let edge_idx = plan.find_work().unwrap(); // cat in
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat mid1 mid2
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        assert_eq!(None, plan.find_work()); // done
    }

    // Test that two outputs from one rule can eventually be routed to another.
    #[test]
    fn plantest_double_output_indirect() {
        let mut plantest = PlanTest::new();
        plantest.assert_parse(
            concat!(
                "build out: cat b1 b2\n",
                "build b1: cat a1\n",
                "build b2: cat a2\n",
                "build a1 a2: cat in\n"
            ).as_bytes(),
        );
        plantest.assert_with_node_mut(b"a1", Node::mark_dirty);
        plantest.assert_with_node_mut(b"a2", Node::mark_dirty);
        plantest.assert_with_node_mut(b"b1", Node::mark_dirty);
        plantest.assert_with_node_mut(b"b2", Node::mark_dirty);
        plantest.assert_with_node_mut(b"out", Node::mark_dirty);

        let out_node_idx = plantest.assert_node_idx(b"out");
        let mut state = plantest.state.borrow_mut();
        let state = &mut *state;
        let plan = &mut plantest.other.plan;
        assert_eq!(Ok(true), plan.add_target(state, out_node_idx));
        assert_eq!(true, plan.more_to_do());

        let edge_idx = plan.find_work().unwrap(); // cat in
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat a1
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat a2
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat b1 b2
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        assert_eq!(None, plan.find_work()); // done
    }

    // Test that two edges from one output can both execute.
    #[test]
    fn plantest_double_dependent() {
        let mut plantest = PlanTest::new();
        plantest.assert_parse(
            concat!(
                "build out: cat a1 a2\n",
                "build a1: cat mid\n",
                "build a2: cat mid\n",
                "build mid: cat in\n"
            ).as_bytes(),
        );
        plantest.assert_with_node_mut(b"mid", Node::mark_dirty);
        plantest.assert_with_node_mut(b"a1", Node::mark_dirty);
        plantest.assert_with_node_mut(b"a2", Node::mark_dirty);
        plantest.assert_with_node_mut(b"out", Node::mark_dirty);

        let out_node_idx = plantest.assert_node_idx(b"out");
        let mut state = plantest.state.borrow_mut();
        let state = &mut *state;
        let plan = &mut plantest.other.plan;
        assert_eq!(Ok(true), plan.add_target(state, out_node_idx));
        assert_eq!(true, plan.more_to_do());

        let edge_idx = plan.find_work().unwrap(); // cat in
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat mid
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat mid
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap(); // cat a1 a2
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        assert_eq!(None, plan.find_work()); // done
    }

    fn test_pool_with_depth_one_helper(plantest: &mut PlanTest, test_case: &[u8]) {
        plantest.assert_parse(test_case);
        plantest.assert_with_node_mut(b"out1", Node::mark_dirty);
        plantest.assert_with_node_mut(b"out2", Node::mark_dirty);

        let out1_node_idx = plantest.assert_node_idx(b"out1");
        let out2_node_idx = plantest.assert_node_idx(b"out2");

        let mut state = plantest.state.borrow_mut();
        let state = &mut *state;
        let plan = &mut plantest.other.plan;
        assert_eq!(Ok(true), plan.add_target(state, out1_node_idx));
        assert_eq!(Ok(true), plan.add_target(state, out2_node_idx));

        assert_eq!(true, plan.more_to_do());

        let edge_idx = plan.find_work().unwrap();
        {
            let edge = state.edge_state.get_edge(edge_idx);
            let edge_in0_idx = edge.inputs.get(0).cloned().unwrap();
            let edge_in0_node = state.node_state.get_node(edge_in0_idx);
            assert_eq!(b"in".as_ref(), edge_in0_node.path());
            let edge_out0_idx = edge.outputs.get(0).cloned().unwrap();
            let edge_out0_node = state.node_state.get_node(edge_out0_idx);
            assert_eq!(b"out1".as_ref(), edge_out0_node.path());
        }

        // This will be false since poolcat is serialized
        assert!(plan.find_work().is_none());
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        let edge_idx = plan.find_work().unwrap();
        {
            let edge = state.edge_state.get_edge(edge_idx);
            let edge_in0_idx = edge.inputs.get(0).cloned().unwrap();
            let edge_in0_node = state.node_state.get_node(edge_in0_idx);
            assert_eq!(b"in".as_ref(), edge_in0_node.path());
            let edge_out0_idx = edge.outputs.get(0).cloned().unwrap();
            let edge_out0_node = state.node_state.get_node(edge_out0_idx);
            assert_eq!(b"out2".as_ref(), edge_out0_node.path());
        }

        // This will be false since poolcat is serialized
        assert!(plan.find_work().is_none());
        plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);

        assert_eq!(false, plan.more_to_do());
        assert_eq!(None, plan.find_work()); // done
    }

    #[test]
    fn plantest_pool_with_depth_one() {
        let mut plantest = PlanTest::new();
        test_pool_with_depth_one_helper(
            &mut plantest,
            concat!(
                "pool foobar\n",
                "  depth = 1\n",
                "rule poolcat\n",
                "  command = cat $in > $out\n",
                "  pool = foobar\n",
                "build out1: poolcat in\n",
                "build out2: poolcat in\n"
            ).as_bytes(),
        );
    }

    #[test]
    fn plantest_console_pool() {
        let mut plantest = PlanTest::new();
        test_pool_with_depth_one_helper(
            &mut plantest,
            concat!(
          "rule poolcat\n",
          "  command = cat $in > $out\n",
          "  pool = console\n",
          "build out1: poolcat in\n",
          "build out2: poolcat in\n",
        ).as_bytes(),
        );
    }

    /// Because FindWork does not return Edges in any sort of predictable order,
    // provide a means to get available Edges in order and in a format which is
    // easy to write tests around.
    fn find_work_sorted_helper(
        plan: &mut Plan,
        state: &State,
        count: usize,
    ) -> VecDeque<EdgeIndex> {
        let mut result = (0..count)
            .map(|i| {
                assert!(plan.more_to_do());
                plan.find_work().unwrap()
            })
            .collect::<Vec<_>>();

        assert!(plan.find_work().is_none());
        result.sort_by_key(|e| {
            state
                .node_state
                .get_node(state.edge_state.get_edge(*e).outputs[0])
                .path()
        });
        result.into_iter().collect()
    }

    #[test]
    fn plantest_pools_with_depth_two() {
        let mut plantest = PlanTest::new();
        plantest.assert_parse(
            concat!(
                "pool foobar\n",
                "  depth = 2\n",
                "pool bazbin\n",
                "  depth = 2\n",
                "rule foocat\n",
                "  command = cat $in > $out\n",
                "  pool = foobar\n",
                "rule bazcat\n",
                "  command = cat $in > $out\n",
                "  pool = bazbin\n",
                "build out1: foocat in\n",
                "build out2: foocat in\n",
                "build out3: foocat in\n",
                "build outb1: bazcat in\n",
                "build outb2: bazcat in\n",
                "build outb3: bazcat in\n",
                "  pool =\n",
                "build allTheThings: cat out1 out2 out3 outb1 outb2 outb3\n"
            ).as_bytes(),
        );
        [
            b"out1".as_ref(),
            b"out2".as_ref(),
            b"out3".as_ref(),
            b"outb1".as_ref(),
            b"outb2".as_ref(),
            b"outb3".as_ref(),
            b"allTheThings".as_ref(),
        ].as_ref()
            .iter()
            .for_each(|path| {
                plantest.assert_with_node_mut(path, Node::mark_dirty);
            });

        let mut state = plantest.state.borrow_mut();
        let state = &mut *state;
        let plan = &mut plantest.other.plan;
        let all_the_things_node = state.node_state.lookup_node(b"allTheThings").unwrap();
        assert_eq!(Ok(true), plan.add_target(state, all_the_things_node));

        let mut edges = find_work_sorted_helper(plan, state, 5);
        {
            let edge_idx = edges[0];
            let edge = state.edge_state.get_edge(edge_idx);
            assert_eq!(
                b"in".as_ref(),
                state.node_state.get_node(edge.inputs[0]).path()
            );
            assert_eq!(
                b"out1".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        {
            let edge_idx = edges[1];
            let edge = state.edge_state.get_edge(edge_idx);
            assert_eq!(
                b"in".as_ref(),
                state.node_state.get_node(edge.inputs[0]).path()
            );
            assert_eq!(
                b"out2".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        {
            let edge_idx = edges[2];
            let edge = state.edge_state.get_edge(edge_idx);
            assert_eq!(
                b"in".as_ref(),
                state.node_state.get_node(edge.inputs[0]).path()
            );
            assert_eq!(
                b"outb1".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        {
            let edge_idx = edges[3];
            let edge = state.edge_state.get_edge(edge_idx);
            assert_eq!(
                b"in".as_ref(),
                state.node_state.get_node(edge.inputs[0]).path()
            );
            assert_eq!(
                b"outb2".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        {
            let edge_idx = edges[4];
            let edge = state.edge_state.get_edge(edge_idx);
            assert_eq!(
                b"in".as_ref(),
                state.node_state.get_node(edge.inputs[0]).path()
            );
            assert_eq!(
                b"outb3".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        // finish out1
        plan.edge_finished(state, edges.pop_front().unwrap(), EdgeResult::EdgeSucceeded);

        let out3_idx = plan.find_work().unwrap();
        {
            let edge = state.edge_state.get_edge(out3_idx);
            assert_eq!(
                b"in".as_ref(),
                state.node_state.get_node(edge.inputs[0]).path()
            );
            assert_eq!(
                b"out3".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        assert!(plan.find_work().is_none());
        plan.edge_finished(state, out3_idx, EdgeResult::EdgeSucceeded);
        assert!(plan.find_work().is_none());

        edges.into_iter().for_each(|edge_idx| {
            plan.edge_finished(state, edge_idx, EdgeResult::EdgeSucceeded);
        });

        let last_idx = plan.find_work().unwrap();
        {
            let edge = state.edge_state.get_edge(last_idx);
            assert_eq!(
                b"allTheThings".as_ref(),
                state.node_state.get_node(edge.outputs[0]).path()
            )
        }
        plan.edge_finished(state, last_idx, EdgeResult::EdgeSucceeded);

        assert_eq!(false, plan.more_to_do());
        assert_eq!(None, plan.find_work()); // done
    }
    /*
TEST_F(PlanTest, PoolWithRedundantEdges) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "pool compile\n"
    "  depth = 1\n"
    "rule gen_foo\n"
    "  command = touch foo.cpp\n"
    "rule gen_bar\n"
    "  command = touch bar.cpp\n"
    "rule echo\n"
    "  command = echo $out > $out\n"
    "build foo.cpp.obj: echo foo.cpp || foo.cpp\n"
    "  pool = compile\n"
    "build bar.cpp.obj: echo bar.cpp || bar.cpp\n"
    "  pool = compile\n"
    "build libfoo.a: echo foo.cpp.obj bar.cpp.obj\n"
    "build foo.cpp: gen_foo\n"
    "build bar.cpp: gen_bar\n"
    "build all: phony libfoo.a\n"));
  GetNode("foo.cpp")->MarkDirty();
  GetNode("foo.cpp.obj")->MarkDirty();
  GetNode("bar.cpp")->MarkDirty();
  GetNode("bar.cpp.obj")->MarkDirty();
  GetNode("libfoo.a")->MarkDirty();
  GetNode("all")->MarkDirty();
  string err;
  EXPECT_TRUE(plan_.AddTarget(GetNode("all"), &err));
  ASSERT_EQ("", err);
  ASSERT_TRUE(plan_.more_to_do());

  Edge* edge = NULL;

  deque<Edge*> initial_edges;
  FindWorkSorted(&initial_edges, 2);

  edge = initial_edges[1];  // Foo first
  ASSERT_EQ("foo.cpp", edge->outputs_[0]->path());
  plan_.EdgeFinished(edge, Plan::kEdgeSucceeded);

  edge = plan_.FindWork();
  ASSERT_TRUE(edge);
  ASSERT_FALSE(plan_.FindWork());
  ASSERT_EQ("foo.cpp", edge->inputs_[0]->path());
  ASSERT_EQ("foo.cpp", edge->inputs_[1]->path());
  ASSERT_EQ("foo.cpp.obj", edge->outputs_[0]->path());
  plan_.EdgeFinished(edge, Plan::kEdgeSucceeded);

  edge = initial_edges[0];  // Now for bar
  ASSERT_EQ("bar.cpp", edge->outputs_[0]->path());
  plan_.EdgeFinished(edge, Plan::kEdgeSucceeded);

  edge = plan_.FindWork();
  ASSERT_TRUE(edge);
  ASSERT_FALSE(plan_.FindWork());
  ASSERT_EQ("bar.cpp", edge->inputs_[0]->path());
  ASSERT_EQ("bar.cpp", edge->inputs_[1]->path());
  ASSERT_EQ("bar.cpp.obj", edge->outputs_[0]->path());
  plan_.EdgeFinished(edge, Plan::kEdgeSucceeded);

  edge = plan_.FindWork();
  ASSERT_TRUE(edge);
  ASSERT_FALSE(plan_.FindWork());
  ASSERT_EQ("foo.cpp.obj", edge->inputs_[0]->path());
  ASSERT_EQ("bar.cpp.obj", edge->inputs_[1]->path());
  ASSERT_EQ("libfoo.a", edge->outputs_[0]->path());
  plan_.EdgeFinished(edge, Plan::kEdgeSucceeded);

  edge = plan_.FindWork();
  ASSERT_TRUE(edge);
  ASSERT_FALSE(plan_.FindWork());
  ASSERT_EQ("libfoo.a", edge->inputs_[0]->path());
  ASSERT_EQ("all", edge->outputs_[0]->path());
  plan_.EdgeFinished(edge, Plan::kEdgeSucceeded);

  edge = plan_.FindWork();
  ASSERT_FALSE(edge);
  ASSERT_FALSE(plan_.more_to_do());
}

TEST_F(PlanTest, PoolWithFailingEdge) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "pool foobar\n"
    "  depth = 1\n"
    "rule poolcat\n"
    "  command = cat $in > $out\n"
    "  pool = foobar\n"
    "build out1: poolcat in\n"
    "build out2: poolcat in\n"));
  GetNode("out1")->MarkDirty();
  GetNode("out2")->MarkDirty();
  string err;
  EXPECT_TRUE(plan_.AddTarget(GetNode("out1"), &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(plan_.AddTarget(GetNode("out2"), &err));
  ASSERT_EQ("", err);
  ASSERT_TRUE(plan_.more_to_do());

  Edge* edge = plan_.FindWork();
  ASSERT_TRUE(edge);
  ASSERT_EQ("in",  edge->inputs_[0]->path());
  ASSERT_EQ("out1", edge->outputs_[0]->path());

  // This will be false since poolcat is serialized
  ASSERT_FALSE(plan_.FindWork());

  plan_.EdgeFinished(edge, Plan::kEdgeFailed);

  edge = plan_.FindWork();
  ASSERT_TRUE(edge);
  ASSERT_EQ("in", edge->inputs_[0]->path());
  ASSERT_EQ("out2", edge->outputs_[0]->path());

  ASSERT_FALSE(plan_.FindWork());

  plan_.EdgeFinished(edge, Plan::kEdgeFailed);

  ASSERT_TRUE(plan_.more_to_do()); // Jobs have failed
  edge = plan_.FindWork();
  ASSERT_EQ(0, edge);
}

/// Fake implementation of CommandRunner, useful for tests.
struct FakeCommandRunner : public CommandRunner {
  explicit FakeCommandRunner(VirtualFileSystem* fs) :
      last_command_(NULL), fs_(fs) {}

  // CommandRunner impl
  virtual bool CanRunMore();
  virtual bool StartCommand(Edge* edge);
  virtual bool WaitForCommand(Result* result);
  virtual vector<Edge*> GetActiveEdges();
  virtual void Abort();

  vector<string> commands_ran_;
  Edge* last_command_;
  VirtualFileSystem* fs_;
};
*/

    /*
struct BuildTest : public StateTestWithBuiltinRules, public BuildLogUser {
  BuildTest() : config_(MakeConfig()), command_runner_(&fs_),
                builder_(&state_, config_, NULL, NULL, &fs_),
                status_(config_) {
  }

  virtual void SetUp() {
    StateTestWithBuiltinRules::SetUp();

    builder_.command_runner_.reset(&command_runner_);
    AssertParse(&state_,
"build cat1: cat in1\n"
"build cat2: cat in1 in2\n"
"build cat12: cat cat1 cat2\n");

    fs_.Create("in1", "");
    fs_.Create("in2", "");
  }

  ~BuildTest() {
    builder_.command_runner_.release();
  }

  virtual bool IsPathDead(StringPiece s) const { return false; }

  /// Rebuild target in the 'working tree' (fs_).
  /// State of command_runner_ and logs contents (if specified) ARE MODIFIED.
  /// Handy to check for NOOP builds, and higher-level rebuild tests.
  void RebuildTarget(const string& target, const char* manifest,
                     const char* log_path = NULL, const char* deps_path = NULL,
                     State* state = NULL);

  // Mark a path dirty.
  void Dirty(const string& path);

  BuildConfig MakeConfig() {
    BuildConfig config;
    config.verbosity = BuildConfig::QUIET;
    return config;
  }

  BuildConfig config_;
  FakeCommandRunner command_runner_;
  VirtualFileSystem fs_;
  Builder builder_;

  BuildStatus status_;
};

void BuildTest::RebuildTarget(const string& target, const char* manifest,
                              const char* log_path, const char* deps_path,
                              State* state) {
  State local_state, *pstate = &local_state;
  if (state)
    pstate = state;
  ASSERT_NO_FATAL_FAILURE(AddCatRule(pstate));
  AssertParse(pstate, manifest);

  string err;
  BuildLog build_log, *pbuild_log = NULL;
  if (log_path) {
    ASSERT_TRUE(build_log.Load(log_path, &err));
    ASSERT_TRUE(build_log.OpenForWrite(log_path, *this, &err));
    ASSERT_EQ("", err);
    pbuild_log = &build_log;
  }

  DepsLog deps_log, *pdeps_log = NULL;
  if (deps_path) {
    ASSERT_TRUE(deps_log.Load(deps_path, pstate, &err));
    ASSERT_TRUE(deps_log.OpenForWrite(deps_path, &err));
    ASSERT_EQ("", err);
    pdeps_log = &deps_log;
  }

  Builder builder(pstate, config_, pbuild_log, pdeps_log, &fs_);
  EXPECT_TRUE(builder.AddTarget(target, &err));

  command_runner_.commands_ran_.clear();
  builder.command_runner_.reset(&command_runner_);
  if (!builder.AlreadyUpToDate()) {
    bool build_res = builder.Build(&err);
    EXPECT_TRUE(build_res);
  }
  builder.command_runner_.release();
}

bool FakeCommandRunner::CanRunMore() {
  // Only run one at a time.
  return last_command_ == NULL;
}

bool FakeCommandRunner::StartCommand(Edge* edge) {
  assert(!last_command_);
  commands_ran_.push_back(edge->EvaluateCommand());
  if (edge->rule().name() == "cat"  ||
      edge->rule().name() == "cat_rsp" ||
      edge->rule().name() == "cat_rsp_out" ||
      edge->rule().name() == "cc" ||
      edge->rule().name() == "touch" ||
      edge->rule().name() == "touch-interrupt" ||
      edge->rule().name() == "touch-fail-tick2") {
    for (vector<Node*>::iterator out = edge->outputs_.begin();
         out != edge->outputs_.end(); ++out) {
      fs_->Create((*out)->path(), "");
    }
  } else if (edge->rule().name() == "true" ||
             edge->rule().name() == "fail" ||
             edge->rule().name() == "interrupt" ||
             edge->rule().name() == "console") {
    // Don't do anything.
  } else {
    printf("unknown command\n");
    return false;
  }

  last_command_ = edge;
  return true;
}

bool FakeCommandRunner::WaitForCommand(Result* result) {
  if (!last_command_)
    return false;

  Edge* edge = last_command_;
  result->edge = edge;

  if (edge->rule().name() == "interrupt" ||
      edge->rule().name() == "touch-interrupt") {
    result->status = ExitInterrupted;
    return true;
  }

  if (edge->rule().name() == "console") {
    if (edge->use_console())
      result->status = ExitSuccess;
    else
      result->status = ExitFailure;
    last_command_ = NULL;
    return true;
  }

  if (edge->rule().name() == "fail" ||
      (edge->rule().name() == "touch-fail-tick2" && fs_->now_ == 2))
    result->status = ExitFailure;
  else
    result->status = ExitSuccess;
  last_command_ = NULL;
  return true;
}

vector<Edge*> FakeCommandRunner::GetActiveEdges() {
  vector<Edge*> edges;
  if (last_command_)
    edges.push_back(last_command_);
  return edges;
}

void FakeCommandRunner::Abort() {
  last_command_ = NULL;
}

void BuildTest::Dirty(const string& path) {
  Node* node = GetNode(path);
  node->MarkDirty();

  // If it's an input file, mark that we've already stat()ed it and
  // it's missing.
  if (!node->in_edge())
    node->MarkMissing();
}

TEST_F(BuildTest, NoWork) {
  string err;
  EXPECT_TRUE(builder_.AlreadyUpToDate());
}

TEST_F(BuildTest, OneStep) {
  // Given a dirty target with one ready input,
  // we should rebuild the target.
  Dirty("cat1");
  string err;
  EXPECT_TRUE(builder_.AddTarget("cat1", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);

  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  EXPECT_EQ("cat in1 > cat1", command_runner_.commands_ran_[0]);
}

TEST_F(BuildTest, OneStep2) {
  // Given a target with one dirty input,
  // we should rebuild the target.
  Dirty("cat1");
  string err;
  EXPECT_TRUE(builder_.AddTarget("cat1", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);

  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  EXPECT_EQ("cat in1 > cat1", command_runner_.commands_ran_[0]);
}

TEST_F(BuildTest, TwoStep) {
  string err;
  EXPECT_TRUE(builder_.AddTarget("cat12", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());
  // Depending on how the pointers work out, we could've ran
  // the first two commands in either order.
  EXPECT_TRUE((command_runner_.commands_ran_[0] == "cat in1 > cat1" &&
               command_runner_.commands_ran_[1] == "cat in1 in2 > cat2") ||
              (command_runner_.commands_ran_[1] == "cat in1 > cat1" &&
               command_runner_.commands_ran_[0] == "cat in1 in2 > cat2"));

  EXPECT_EQ("cat cat1 cat2 > cat12", command_runner_.commands_ran_[2]);

  fs_.Tick();

  // Modifying in2 requires rebuilding one intermediate file
  // and the final file.
  fs_.Create("in2", "");
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("cat12", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(5u, command_runner_.commands_ran_.size());
  EXPECT_EQ("cat in1 in2 > cat2", command_runner_.commands_ran_[3]);
  EXPECT_EQ("cat cat1 cat2 > cat12", command_runner_.commands_ran_[4]);
}

TEST_F(BuildTest, TwoOutputs) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule touch\n"
"  command = touch $out\n"
"build out1 out2: touch in.txt\n"));

  fs_.Create("in.txt", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  EXPECT_EQ("touch out1 out2", command_runner_.commands_ran_[0]);
}

TEST_F(BuildTest, ImplicitOutput) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule touch\n"
"  command = touch $out $out.imp\n"
"build out | out.imp: touch in.txt\n"));
  fs_.Create("in.txt", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out.imp", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  EXPECT_EQ("touch out out.imp", command_runner_.commands_ran_[0]);
}

// Test case from
//   https://github.com/ninja-build/ninja/issues/148
TEST_F(BuildTest, MultiOutIn) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule touch\n"
"  command = touch $out\n"
"build in1 otherfile: touch in\n"
"build out: touch in | in1\n"));

  fs_.Create("in", "");
  fs_.Tick();
  fs_.Create("in1", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
}

TEST_F(BuildTest, Chain) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build c2: cat c1\n"
"build c3: cat c2\n"
"build c4: cat c3\n"
"build c5: cat c4\n"));

  fs_.Create("c1", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("c5", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  ASSERT_EQ(4u, command_runner_.commands_ran_.size());

  err.clear();
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("c5", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());

  fs_.Tick();

  fs_.Create("c3", "");
  err.clear();
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("c5", &err));
  ASSERT_EQ("", err);
  EXPECT_FALSE(builder_.AlreadyUpToDate());
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());  // 3->4, 4->5
}

TEST_F(BuildTest, MissingInput) {
  // Input is referenced by build file, but no rule for it.
  string err;
  Dirty("in1");
  EXPECT_FALSE(builder_.AddTarget("cat1", &err));
  EXPECT_EQ("'in1', needed by 'cat1', missing and no known rule to make it",
            err);
}

TEST_F(BuildTest, MissingTarget) {
  // Target is not referenced by build file.
  string err;
  EXPECT_FALSE(builder_.AddTarget("meow", &err));
  EXPECT_EQ("unknown target: 'meow'", err);
}

TEST_F(BuildTest, MakeDirs) {
  string err;

#ifdef _WIN32
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
                                      "build subdir\\dir2\\file: cat in1\n"));
#else
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
                                      "build subdir/dir2/file: cat in1\n"));
#endif
  EXPECT_TRUE(builder_.AddTarget("subdir/dir2/file", &err));

  EXPECT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(2u, fs_.directories_made_.size());
  EXPECT_EQ("subdir", fs_.directories_made_[0]);
  EXPECT_EQ("subdir/dir2", fs_.directories_made_[1]);
}

TEST_F(BuildTest, DepFileMissing) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n  command = cc $in\n  depfile = $out.d\n"
"build fo$ o.o: cc foo.c\n"));
  fs_.Create("foo.c", "");

  EXPECT_TRUE(builder_.AddTarget("fo o.o", &err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, fs_.files_read_.size());
  EXPECT_EQ("fo o.o.d", fs_.files_read_[0]);
}

TEST_F(BuildTest, DepFileOK) {
  string err;
  int orig_edges = state_.edges_.size();
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n  command = cc $in\n  depfile = $out.d\n"
"build foo.o: cc foo.c\n"));
  Edge* edge = state_.edges_.back();

  fs_.Create("foo.c", "");
  GetNode("bar.h")->MarkDirty();  // Mark bar.h as missing.
  fs_.Create("foo.o.d", "foo.o: blah.h bar.h\n");
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, fs_.files_read_.size());
  EXPECT_EQ("foo.o.d", fs_.files_read_[0]);

  // Expect three new edges: one generating foo.o, and two more from
  // loading the depfile.
  ASSERT_EQ(orig_edges + 3, (int)state_.edges_.size());
  // Expect our edge to now have three inputs: foo.c and two headers.
  ASSERT_EQ(3u, edge->inputs_.size());

  // Expect the command line we generate to only use the original input.
  ASSERT_EQ("cc foo.c", edge->EvaluateCommand());
}

TEST_F(BuildTest, DepFileParseError) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n  command = cc $in\n  depfile = $out.d\n"
"build foo.o: cc foo.c\n"));
  fs_.Create("foo.c", "");
  fs_.Create("foo.o.d", "randomtext\n");
  EXPECT_FALSE(builder_.AddTarget("foo.o", &err));
  EXPECT_EQ("foo.o.d: expected ':' in depfile", err);
}

TEST_F(BuildTest, EncounterReadyTwice) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule touch\n"
"  command = touch $out\n"
"build c: touch\n"
"build b: touch || c\n"
"build a: touch | b || c\n"));

  vector<Edge*> c_out = GetNode("c")->out_edges();
  ASSERT_EQ(2u, c_out.size());
  EXPECT_EQ("b", c_out[0]->outputs_[0]->path());
  EXPECT_EQ("a", c_out[1]->outputs_[0]->path());

  fs_.Create("b", "");
  EXPECT_TRUE(builder_.AddTarget("a", &err));
  ASSERT_EQ("", err);

  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, OrderOnlyDeps) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n  command = cc $in\n  depfile = $out.d\n"
"build foo.o: cc foo.c || otherfile\n"));
  Edge* edge = state_.edges_.back();

  fs_.Create("foo.c", "");
  fs_.Create("otherfile", "");
  fs_.Create("foo.o.d", "foo.o: blah.h bar.h\n");
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  ASSERT_EQ("", err);

  // One explicit, two implicit, one order only.
  ASSERT_EQ(4u, edge->inputs_.size());
  EXPECT_EQ(2, edge->implicit_deps_);
  EXPECT_EQ(1, edge->order_only_deps_);
  // Verify the inputs are in the order we expect
  // (explicit then implicit then orderonly).
  EXPECT_EQ("foo.c", edge->inputs_[0]->path());
  EXPECT_EQ("blah.h", edge->inputs_[1]->path());
  EXPECT_EQ("bar.h", edge->inputs_[2]->path());
  EXPECT_EQ("otherfile", edge->inputs_[3]->path());

  // Expect the command line we generate to only use the original input.
  ASSERT_EQ("cc foo.c", edge->EvaluateCommand());

  // explicit dep dirty, expect a rebuild.
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());

  fs_.Tick();

  // Recreate the depfile, as it should have been deleted by the build.
  fs_.Create("foo.o.d", "foo.o: blah.h bar.h\n");

  // implicit dep dirty, expect a rebuild.
  fs_.Create("blah.h", "");
  fs_.Create("bar.h", "");
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());

  fs_.Tick();

  // Recreate the depfile, as it should have been deleted by the build.
  fs_.Create("foo.o.d", "foo.o: blah.h bar.h\n");

  // order only dep dirty, no rebuild.
  fs_.Create("otherfile", "");
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());

  // implicit dep missing, expect rebuild.
  fs_.RemoveFile("bar.h");
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, RebuildOrderOnlyDeps) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n  command = cc $in\n"
"rule true\n  command = true\n"
"build oo.h: cc oo.h.in\n"
"build foo.o: cc foo.c || oo.h\n"));

  fs_.Create("foo.c", "");
  fs_.Create("oo.h.in", "");

  // foo.o and order-only dep dirty, build both.
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());

  // all clean, no rebuild.
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());

  // order-only dep missing, build it only.
  fs_.RemoveFile("oo.h");
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  ASSERT_EQ("cc oo.h.in", command_runner_.commands_ran_[0]);

  fs_.Tick();

  // order-only dep dirty, build it only.
  fs_.Create("oo.h.in", "");
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("foo.o", &err));
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  ASSERT_EQ("cc oo.h.in", command_runner_.commands_ran_[0]);
}

#ifdef _WIN32
TEST_F(BuildTest, DepFileCanonicalize) {
  string err;
  int orig_edges = state_.edges_.size();
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n  command = cc $in\n  depfile = $out.d\n"
"build gen/stuff\\things/foo.o: cc x\\y/z\\foo.c\n"));
  Edge* edge = state_.edges_.back();

  fs_.Create("x/y/z/foo.c", "");
  GetNode("bar.h")->MarkDirty();  // Mark bar.h as missing.
  // Note, different slashes from manifest.
  fs_.Create("gen/stuff\\things/foo.o.d",
             "gen\\stuff\\things\\foo.o: blah.h bar.h\n");
  EXPECT_TRUE(builder_.AddTarget("gen/stuff/things/foo.o", &err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, fs_.files_read_.size());
  // The depfile path does not get Canonicalize as it seems unnecessary.
  EXPECT_EQ("gen/stuff\\things/foo.o.d", fs_.files_read_[0]);

  // Expect three new edges: one generating foo.o, and two more from
  // loading the depfile.
  ASSERT_EQ(orig_edges + 3, (int)state_.edges_.size());
  // Expect our edge to now have three inputs: foo.c and two headers.
  ASSERT_EQ(3u, edge->inputs_.size());

  // Expect the command line we generate to only use the original input, and
  // using the slashes from the manifest.
  ASSERT_EQ("cc x\\y/z\\foo.c", edge->EvaluateCommand());
}
#endif

TEST_F(BuildTest, Phony) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out: cat bar.cc\n"
"build all: phony out\n"));
  fs_.Create("bar.cc", "");

  EXPECT_TRUE(builder_.AddTarget("all", &err));
  ASSERT_EQ("", err);

  // Only one command to run, because phony runs no command.
  EXPECT_FALSE(builder_.AlreadyUpToDate());
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, PhonyNoWork) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out: cat bar.cc\n"
"build all: phony out\n"));
  fs_.Create("bar.cc", "");
  fs_.Create("out", "");

  EXPECT_TRUE(builder_.AddTarget("all", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());
}

// Test a self-referencing phony.  Ideally this should not work, but
// ninja 1.7 and below tolerated and CMake 2.8.12.x and 3.0.x both
// incorrectly produce it.  We tolerate it for compatibility.
TEST_F(BuildTest, PhonySelfReference) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build a: phony a\n"));

  EXPECT_TRUE(builder_.AddTarget("a", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());
}

TEST_F(BuildTest, Fail) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule fail\n"
"  command = fail\n"
"build out1: fail\n"));

  string err;
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  ASSERT_EQ("", err);

  EXPECT_FALSE(builder_.Build(&err));
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
  ASSERT_EQ("subcommand failed", err);
}

TEST_F(BuildTest, SwallowFailures) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule fail\n"
"  command = fail\n"
"build out1: fail\n"
"build out2: fail\n"
"build out3: fail\n"
"build all: phony out1 out2 out3\n"));

  // Swallow two failures, die on the third.
  config_.failures_allowed = 3;

  string err;
  EXPECT_TRUE(builder_.AddTarget("all", &err));
  ASSERT_EQ("", err);

  EXPECT_FALSE(builder_.Build(&err));
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());
  ASSERT_EQ("subcommands failed", err);
}

TEST_F(BuildTest, SwallowFailuresLimit) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule fail\n"
"  command = fail\n"
"build out1: fail\n"
"build out2: fail\n"
"build out3: fail\n"
"build final: cat out1 out2 out3\n"));

  // Swallow ten failures; we should stop before building final.
  config_.failures_allowed = 11;

  string err;
  EXPECT_TRUE(builder_.AddTarget("final", &err));
  ASSERT_EQ("", err);

  EXPECT_FALSE(builder_.Build(&err));
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());
  ASSERT_EQ("cannot make progress due to previous errors", err);
}

TEST_F(BuildTest, SwallowFailuresPool) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"pool failpool\n"
"  depth = 1\n"
"rule fail\n"
"  command = fail\n"
"  pool = failpool\n"
"build out1: fail\n"
"build out2: fail\n"
"build out3: fail\n"
"build final: cat out1 out2 out3\n"));

  // Swallow ten failures; we should stop before building final.
  config_.failures_allowed = 11;

  string err;
  EXPECT_TRUE(builder_.AddTarget("final", &err));
  ASSERT_EQ("", err);

  EXPECT_FALSE(builder_.Build(&err));
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());
  ASSERT_EQ("cannot make progress due to previous errors", err);
}

TEST_F(BuildTest, PoolEdgesReadyButNotWanted) {
  fs_.Create("x", "");

  const char* manifest =
    "pool some_pool\n"
    "  depth = 4\n"
    "rule touch\n"
    "  command = touch $out\n"
    "  pool = some_pool\n"
    "rule cc\n"
    "  command = touch grit\n"
    "\n"
    "build B.d.stamp: cc | x\n"
    "build C.stamp: touch B.d.stamp\n"
    "build final.stamp: touch || C.stamp\n";

  RebuildTarget("final.stamp", manifest);

  fs_.RemoveFile("B.d.stamp");

  State save_state;
  RebuildTarget("final.stamp", manifest, NULL, NULL, &save_state);
  EXPECT_GE(save_state.LookupPool("some_pool")->current_use(), 0);
}

struct BuildWithLogTest : public BuildTest {
  BuildWithLogTest() {
    builder_.SetBuildLog(&build_log_);
  }

  BuildLog build_log_;
};

TEST_F(BuildWithLogTest, NotInLogButOnDisk) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n"
"  command = cc\n"
"build out1: cc in\n"));

  // Create input/output that would be considered up to date when
  // not considering the command line hash.
  fs_.Create("in", "");
  fs_.Create("out1", "");
  string err;

  // Because it's not in the log, it should not be up-to-date until
  // we build again.
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_FALSE(builder_.AlreadyUpToDate());

  command_runner_.commands_ran_.clear();
  state_.Reset();

  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_TRUE(builder_.AlreadyUpToDate());
}

TEST_F(BuildWithLogTest, RebuildAfterFailure) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule touch-fail-tick2\n"
"  command = touch-fail-tick2\n"
"build out1: touch-fail-tick2 in\n"));

  string err;

  fs_.Create("in", "");

  // Run once successfully to get out1 in the log
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  EXPECT_EQ(1u, command_runner_.commands_ran_.size());

  command_runner_.commands_ran_.clear();
  state_.Reset();
  builder_.Cleanup();
  builder_.plan_.Reset();

  fs_.Tick();
  fs_.Create("in", "");

  // Run again with a failure that updates the output file timestamp
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_FALSE(builder_.Build(&err));
  EXPECT_EQ("subcommand failed", err);
  EXPECT_EQ(1u, command_runner_.commands_ran_.size());

  command_runner_.commands_ran_.clear();
  state_.Reset();
  builder_.Cleanup();
  builder_.plan_.Reset();

  fs_.Tick();

  // Run again, should rerun even though the output file is up to date on disk
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_FALSE(builder_.AlreadyUpToDate());
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ(1u, command_runner_.commands_ran_.size());
  EXPECT_EQ("", err);
}

TEST_F(BuildWithLogTest, RebuildWithNoInputs) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule touch\n"
"  command = touch\n"
"build out1: touch\n"
"build out2: touch in\n"));

  string err;

  fs_.Create("in", "");

  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  EXPECT_EQ(2u, command_runner_.commands_ran_.size());

  command_runner_.commands_ran_.clear();
  state_.Reset();

  fs_.Tick();

  fs_.Create("in", "");

  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  EXPECT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildWithLogTest, RestatTest) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule true\n"
"  command = true\n"
"  restat = 1\n"
"rule cc\n"
"  command = cc\n"
"  restat = 1\n"
"build out1: cc in\n"
"build out2: true out1\n"
"build out3: cat out2\n"));

  fs_.Create("out1", "");
  fs_.Create("out2", "");
  fs_.Create("out3", "");

  fs_.Tick();

  fs_.Create("in", "");

  // Do a pre-build so that there's commands in the log for the outputs,
  // otherwise, the lack of an entry in the build log will cause out3 to rebuild
  // regardless of restat.
  string err;
  EXPECT_TRUE(builder_.AddTarget("out3", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  EXPECT_EQ("[3/3]", builder_.status_->FormatProgressStatus("[%s/%t]",
      BuildStatus::kEdgeStarted));
  command_runner_.commands_ran_.clear();
  state_.Reset();

  fs_.Tick();

  fs_.Create("in", "");
  // "cc" touches out1, so we should build out2.  But because "true" does not
  // touch out2, we should cancel the build of out3.
  EXPECT_TRUE(builder_.AddTarget("out3", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());

  // If we run again, it should be a no-op, because the build log has recorded
  // that we've already built out2 with an input timestamp of 2 (from out1).
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out3", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());

  fs_.Tick();

  fs_.Create("in", "");

  // The build log entry should not, however, prevent us from rebuilding out2
  // if out1 changes.
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out3", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());
}

TEST_F(BuildWithLogTest, RestatMissingFile) {
  // If a restat rule doesn't create its output, and the output didn't
  // exist before the rule was run, consider that behavior equivalent
  // to a rule that doesn't modify its existent output file.

  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule true\n"
"  command = true\n"
"  restat = 1\n"
"rule cc\n"
"  command = cc\n"
"build out1: true in\n"
"build out2: cc out1\n"));

  fs_.Create("in", "");
  fs_.Create("out2", "");

  // Do a pre-build so that there's commands in the log for the outputs,
  // otherwise, the lack of an entry in the build log will cause out2 to rebuild
  // regardless of restat.
  string err;
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  command_runner_.commands_ran_.clear();
  state_.Reset();

  fs_.Tick();
  fs_.Create("in", "");
  fs_.Create("out2", "");

  // Run a build, expect only the first command to run.
  // It doesn't touch its output (due to being the "true" command), so
  // we shouldn't run the dependent build.
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildWithLogTest, RestatSingleDependentOutputDirty) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "rule true\n"
    "  command = true\n"
    "  restat = 1\n"
    "rule touch\n"
    "  command = touch\n"
    "build out1: true in\n"
    "build out2 out3: touch out1\n"
    "build out4: touch out2\n"
    ));

  // Create the necessary files
  fs_.Create("in", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out4", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());

  fs_.Tick();
  fs_.Create("in", "");
  fs_.RemoveFile("out3");

  // Since "in" is missing, out1 will be built. Since "out3" is missing,
  // out2 and out3 will be built even though "in" is not touched when built.
  // Then, since out2 is rebuilt, out4 should be rebuilt -- the restat on the
  // "true" rule should not lead to the "touch" edge writing out2 and out3 being
  // cleard.
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out4", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ("", err);
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());
}

// Test scenario, in which an input file is removed, but output isn't changed
// https://github.com/ninja-build/ninja/issues/295
TEST_F(BuildWithLogTest, RestatMissingInput) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "rule true\n"
    "  command = true\n"
    "  depfile = $out.d\n"
    "  restat = 1\n"
    "rule cc\n"
    "  command = cc\n"
    "build out1: true in\n"
    "build out2: cc out1\n"));

  // Create all necessary files
  fs_.Create("in", "");

  // The implicit dependencies and the depfile itself
  // are newer than the output
  TimeStamp restat_mtime = fs_.Tick();
  fs_.Create("out1.d", "out1: will.be.deleted restat.file\n");
  fs_.Create("will.be.deleted", "");
  fs_.Create("restat.file", "");

  // Run the build, out1 and out2 get built
  string err;
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());

  // See that an entry in the logfile is created, capturing
  // the right mtime
  BuildLog::LogEntry* log_entry = build_log_.LookupByOutput("out1");
  ASSERT_TRUE(NULL != log_entry);
  ASSERT_EQ(restat_mtime, log_entry->mtime);

  // Now remove a file, referenced from depfile, so that target becomes
  // dirty, but the output does not change
  fs_.RemoveFile("will.be.deleted");

  // Trigger the build again - only out1 gets built
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());

  // Check that the logfile entry remains correctly set
  log_entry = build_log_.LookupByOutput("out1");
  ASSERT_TRUE(NULL != log_entry);
  ASSERT_EQ(restat_mtime, log_entry->mtime);
}

struct BuildDryRun : public BuildWithLogTest {
  BuildDryRun() {
    config_.dry_run = true;
  }
};

TEST_F(BuildDryRun, AllCommandsShown) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule true\n"
"  command = true\n"
"  restat = 1\n"
"rule cc\n"
"  command = cc\n"
"  restat = 1\n"
"build out1: cc in\n"
"build out2: true out1\n"
"build out3: cat out2\n"));

  fs_.Create("out1", "");
  fs_.Create("out2", "");
  fs_.Create("out3", "");

  fs_.Tick();

  fs_.Create("in", "");

  // "cc" touches out1, so we should build out2.  But because "true" does not
  // touch out2, we should cancel the build of out3.
  string err;
  EXPECT_TRUE(builder_.AddTarget("out3", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());
}

// Test that RSP files are created when & where appropriate and deleted after
// successful execution.
TEST_F(BuildTest, RspFileSuccess)
{
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "rule cat_rsp\n"
    "  command = cat $rspfile > $out\n"
    "  rspfile = $rspfile\n"
    "  rspfile_content = $long_command\n"
    "rule cat_rsp_out\n"
    "  command = cat $rspfile > $out\n"
    "  rspfile = $out.rsp\n"
    "  rspfile_content = $long_command\n"
    "build out1: cat in\n"
    "build out2: cat_rsp in\n"
    "  rspfile = out 2.rsp\n"
    "  long_command = Some very long command\n"
    "build out$ 3: cat_rsp_out in\n"
    "  long_command = Some very long command\n"));

  fs_.Create("out1", "");
  fs_.Create("out2", "");
  fs_.Create("out 3", "");

  fs_.Tick();

  fs_.Create("in", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AddTarget("out 3", &err));
  ASSERT_EQ("", err);

  size_t files_created = fs_.files_created_.size();
  size_t files_removed = fs_.files_removed_.size();

  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(3u, command_runner_.commands_ran_.size());

  // The RSP files were created
  ASSERT_EQ(files_created + 2, fs_.files_created_.size());
  ASSERT_EQ(1u, fs_.files_created_.count("out 2.rsp"));
  ASSERT_EQ(1u, fs_.files_created_.count("out 3.rsp"));

  // The RSP files were removed
  ASSERT_EQ(files_removed + 2, fs_.files_removed_.size());
  ASSERT_EQ(1u, fs_.files_removed_.count("out 2.rsp"));
  ASSERT_EQ(1u, fs_.files_removed_.count("out 3.rsp"));
}

// Test that RSP file is created but not removed for commands, which fail
TEST_F(BuildTest, RspFileFailure) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "rule fail\n"
    "  command = fail\n"
    "  rspfile = $rspfile\n"
    "  rspfile_content = $long_command\n"
    "build out: fail in\n"
    "  rspfile = out.rsp\n"
    "  long_command = Another very long command\n"));

  fs_.Create("out", "");
  fs_.Tick();
  fs_.Create("in", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  ASSERT_EQ("", err);

  size_t files_created = fs_.files_created_.size();
  size_t files_removed = fs_.files_removed_.size();

  EXPECT_FALSE(builder_.Build(&err));
  ASSERT_EQ("subcommand failed", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());

  // The RSP file was created
  ASSERT_EQ(files_created + 1, fs_.files_created_.size());
  ASSERT_EQ(1u, fs_.files_created_.count("out.rsp"));

  // The RSP file was NOT removed
  ASSERT_EQ(files_removed, fs_.files_removed_.size());
  ASSERT_EQ(0u, fs_.files_removed_.count("out.rsp"));

  // The RSP file contains what it should
  ASSERT_EQ("Another very long command", fs_.files_["out.rsp"].contents);
}

// Test that contents of the RSP file behaves like a regular part of
// command line, i.e. triggers a rebuild if changed
TEST_F(BuildWithLogTest, RspFileCmdLineChange) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
    "rule cat_rsp\n"
    "  command = cat $rspfile > $out\n"
    "  rspfile = $rspfile\n"
    "  rspfile_content = $long_command\n"
    "build out: cat_rsp in\n"
    "  rspfile = out.rsp\n"
    "  long_command = Original very long command\n"));

  fs_.Create("out", "");
  fs_.Tick();
  fs_.Create("in", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  ASSERT_EQ("", err);

  // 1. Build for the 1st time (-> populate log)
  EXPECT_TRUE(builder_.Build(&err));
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());

  // 2. Build again (no change)
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  EXPECT_EQ("", err);
  ASSERT_TRUE(builder_.AlreadyUpToDate());

  // 3. Alter the entry in the logfile
  // (to simulate a change in the command line between 2 builds)
  BuildLog::LogEntry* log_entry = build_log_.LookupByOutput("out");
  ASSERT_TRUE(NULL != log_entry);
  ASSERT_NO_FATAL_FAILURE(AssertHash(
        "cat out.rsp > out;rspfile=Original very long command",
        log_entry->command_hash));
  log_entry->command_hash++;  // Change the command hash to something else.
  // Now expect the target to be rebuilt
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  EXPECT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, InterruptCleanup) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule interrupt\n"
"  command = interrupt\n"
"rule touch-interrupt\n"
"  command = touch-interrupt\n"
"build out1: interrupt in1\n"
"build out2: touch-interrupt in2\n"));

  fs_.Create("out1", "");
  fs_.Create("out2", "");
  fs_.Tick();
  fs_.Create("in1", "");
  fs_.Create("in2", "");

  // An untouched output of an interrupted command should be retained.
  string err;
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  EXPECT_EQ("", err);
  EXPECT_FALSE(builder_.Build(&err));
  EXPECT_EQ("interrupted by user", err);
  builder_.Cleanup();
  EXPECT_GT(fs_.Stat("out1", &err), 0);
  err = "";

  // A touched output of an interrupted command should be deleted.
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  EXPECT_EQ("", err);
  EXPECT_FALSE(builder_.Build(&err));
  EXPECT_EQ("interrupted by user", err);
  builder_.Cleanup();
  EXPECT_EQ(0, fs_.Stat("out2", &err));
}

TEST_F(BuildTest, StatFailureAbortsBuild) {
  const string kTooLongToStat(400, 'i');
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
("build " + kTooLongToStat + ": cat in\n").c_str()));
  fs_.Create("in", "");

  // This simulates a stat failure:
  fs_.files_[kTooLongToStat].mtime = -1;
  fs_.files_[kTooLongToStat].stat_error = "stat failed";

  string err;
  EXPECT_FALSE(builder_.AddTarget(kTooLongToStat, &err));
  EXPECT_EQ("stat failed", err);
}

TEST_F(BuildTest, PhonyWithNoInputs) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build nonexistent: phony\n"
"build out1: cat || nonexistent\n"
"build out2: cat nonexistent\n"));
  fs_.Create("out1", "");
  fs_.Create("out2", "");

  // out1 should be up to date even though its input is dirty, because its
  // order-only dependency has nothing to do.
  string err;
  EXPECT_TRUE(builder_.AddTarget("out1", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.AlreadyUpToDate());

  // out2 should still be out of date though, because its input is dirty.
  err.clear();
  command_runner_.commands_ran_.clear();
  state_.Reset();
  EXPECT_TRUE(builder_.AddTarget("out2", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, DepsGccWithEmptyDepfileErrorsOut) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule cc\n"
"  command = cc\n"
"  deps = gcc\n"
"build out: cc\n"));
  Dirty("out");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  ASSERT_EQ("", err);
  EXPECT_FALSE(builder_.AlreadyUpToDate());

  EXPECT_FALSE(builder_.Build(&err));
  ASSERT_EQ("subcommand failed", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, StatusFormatElapsed) {
  status_.BuildStarted();
  // Before any task is done, the elapsed time must be zero.
  EXPECT_EQ("[%/e0.000]",
            status_.FormatProgressStatus("[%%/e%e]",
                BuildStatus::kEdgeStarted));
}

TEST_F(BuildTest, StatusFormatReplacePlaceholder) {
  EXPECT_EQ("[%/s0/t0/r0/u0/f0]",
            status_.FormatProgressStatus("[%%/s%s/t%t/r%r/u%u/f%f]",
                BuildStatus::kEdgeStarted));
}

TEST_F(BuildTest, FailedDepsParse) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build bad_deps.o: cat in1\n"
"  deps = gcc\n"
"  depfile = in1.d\n"));

  string err;
  EXPECT_TRUE(builder_.AddTarget("bad_deps.o", &err));
  ASSERT_EQ("", err);

  // These deps will fail to parse, as they should only have one
  // path to the left of the colon.
  fs_.Create("in1.d", "AAA BBB");

  EXPECT_FALSE(builder_.Build(&err));
  EXPECT_EQ("subcommand failed", err);
}

/// Tests of builds involving deps logs necessarily must span
/// multiple builds.  We reuse methods on BuildTest but not the
/// builder_ it sets up, because we want pristine objects for
/// each build.
struct BuildWithDepsLogTest : public BuildTest {
  BuildWithDepsLogTest() {}

  virtual void SetUp() {
    BuildTest::SetUp();

    temp_dir_.CreateAndEnter("BuildWithDepsLogTest");
  }

  virtual void TearDown() {
    temp_dir_.Cleanup();
  }

  ScopedTempDir temp_dir_;

  /// Shadow parent class builder_ so we don't accidentally use it.
  void* builder_;
};

/// Run a straightforwad build where the deps log is used.
TEST_F(BuildWithDepsLogTest, Straightforward) {
  string err;
  // Note: in1 was created by the superclass SetUp().
  const char* manifest =
      "build out: cat in1\n"
      "  deps = gcc\n"
      "  depfile = in1.d\n";
  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Run the build once, everything should be ok.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    EXPECT_TRUE(builder.AddTarget("out", &err));
    ASSERT_EQ("", err);
    fs_.Create("in1.d", "out: in2");
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    // The deps file should have been removed.
    EXPECT_EQ(0, fs_.Stat("in1.d", &err));
    // Recreate it for the next step.
    fs_.Create("in1.d", "out: in2");
    deps_log.Close();
    builder.command_runner_.release();
  }

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Touch the file only mentioned in the deps.
    fs_.Tick();
    fs_.Create("in2", "");

    // Run the build again.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.Load("ninja_deps", &state, &err));
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    command_runner_.commands_ran_.clear();
    EXPECT_TRUE(builder.AddTarget("out", &err));
    ASSERT_EQ("", err);
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    // We should have rebuilt the output due to in2 being
    // out of date.
    EXPECT_EQ(1u, command_runner_.commands_ran_.size());

    builder.command_runner_.release();
  }
}

/// Verify that obsolete dependency info causes a rebuild.
/// 1) Run a successful build where everything has time t, record deps.
/// 2) Move input/output to time t+1 -- despite files in alignment,
///    should still need to rebuild due to deps at older time.
TEST_F(BuildWithDepsLogTest, ObsoleteDeps) {
  string err;
  // Note: in1 was created by the superclass SetUp().
  const char* manifest =
      "build out: cat in1\n"
      "  deps = gcc\n"
      "  depfile = in1.d\n";
  {
    // Run an ordinary build that gathers dependencies.
    fs_.Create("in1", "");
    fs_.Create("in1.d", "out: ");

    State state;
    ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Run the build once, everything should be ok.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    EXPECT_TRUE(builder.AddTarget("out", &err));
    ASSERT_EQ("", err);
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    deps_log.Close();
    builder.command_runner_.release();
  }

  // Push all files one tick forward so that only the deps are out
  // of date.
  fs_.Tick();
  fs_.Create("in1", "");
  fs_.Create("out", "");

  // The deps file should have been removed, so no need to timestamp it.
  EXPECT_EQ(0, fs_.Stat("in1.d", &err));

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    DepsLog deps_log;
    ASSERT_TRUE(deps_log.Load("ninja_deps", &state, &err));
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    command_runner_.commands_ran_.clear();
    EXPECT_TRUE(builder.AddTarget("out", &err));
    ASSERT_EQ("", err);

    // Recreate the deps file here because the build expects them to exist.
    fs_.Create("in1.d", "out: ");

    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    // We should have rebuilt the output due to the deps being
    // out of date.
    EXPECT_EQ(1u, command_runner_.commands_ran_.size());

    builder.command_runner_.release();
  }
}

TEST_F(BuildWithDepsLogTest, DepsIgnoredInDryRun) {
  const char* manifest =
      "build out: cat in1\n"
      "  deps = gcc\n"
      "  depfile = in1.d\n";

  fs_.Create("out", "");
  fs_.Tick();
  fs_.Create("in1", "");

  State state;
  ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

  // The deps log is NULL in dry runs.
  config_.dry_run = true;
  Builder builder(&state, config_, NULL, NULL, &fs_);
  builder.command_runner_.reset(&command_runner_);
  command_runner_.commands_ran_.clear();

  string err;
  EXPECT_TRUE(builder.AddTarget("out", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder.Build(&err));
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());

  builder.command_runner_.release();
}

/// Check that a restat rule generating a header cancels compilations correctly.
TEST_F(BuildTest, RestatDepfileDependency) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule true\n"
"  command = true\n"  // Would be "write if out-of-date" in reality.
"  restat = 1\n"
"build header.h: true header.in\n"
"build out: cat in1\n"
"  depfile = in1.d\n"));

  fs_.Create("header.h", "");
  fs_.Create("in1.d", "out: header.h");
  fs_.Tick();
  fs_.Create("header.in", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("out", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
}

/// Check that a restat rule generating a header cancels compilations correctly,
/// depslog case.
TEST_F(BuildWithDepsLogTest, RestatDepfileDependencyDepsLog) {
  string err;
  // Note: in1 was created by the superclass SetUp().
  const char* manifest =
      "rule true\n"
      "  command = true\n"  // Would be "write if out-of-date" in reality.
      "  restat = 1\n"
      "build header.h: true header.in\n"
      "build out: cat in1\n"
      "  deps = gcc\n"
      "  depfile = in1.d\n";
  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Run the build once, everything should be ok.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    EXPECT_TRUE(builder.AddTarget("out", &err));
    ASSERT_EQ("", err);
    fs_.Create("in1.d", "out: header.h");
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    deps_log.Close();
    builder.command_runner_.release();
  }

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AddCatRule(&state));
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Touch the input of the restat rule.
    fs_.Tick();
    fs_.Create("header.in", "");

    // Run the build again.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.Load("ninja_deps", &state, &err));
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    command_runner_.commands_ran_.clear();
    EXPECT_TRUE(builder.AddTarget("out", &err));
    ASSERT_EQ("", err);
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    // Rule "true" should have run again, but the build of "out" should have
    // been cancelled due to restat propagating through the depfile header.
    EXPECT_EQ(1u, command_runner_.commands_ran_.size());

    builder.command_runner_.release();
  }
}

TEST_F(BuildWithDepsLogTest, DepFileOKDepsLog) {
  string err;
  const char* manifest =
      "rule cc\n  command = cc $in\n  depfile = $out.d\n  deps = gcc\n"
      "build fo$ o.o: cc foo.c\n";

  fs_.Create("foo.c", "");

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Run the build once, everything should be ok.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    EXPECT_TRUE(builder.AddTarget("fo o.o", &err));
    ASSERT_EQ("", err);
    fs_.Create("fo o.o.d", "fo\\ o.o: blah.h bar.h\n");
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    deps_log.Close();
    builder.command_runner_.release();
  }

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    DepsLog deps_log;
    ASSERT_TRUE(deps_log.Load("ninja_deps", &state, &err));
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);

    Edge* edge = state.edges_.back();

    state.GetNode("bar.h", 0)->MarkDirty();  // Mark bar.h as missing.
    EXPECT_TRUE(builder.AddTarget("fo o.o", &err));
    ASSERT_EQ("", err);

    // Expect three new edges: one generating fo o.o, and two more from
    // loading the depfile.
    ASSERT_EQ(3u, state.edges_.size());
    // Expect our edge to now have three inputs: foo.c and two headers.
    ASSERT_EQ(3u, edge->inputs_.size());

    // Expect the command line we generate to only use the original input.
    ASSERT_EQ("cc foo.c", edge->EvaluateCommand());

    deps_log.Close();
    builder.command_runner_.release();
  }
}

#ifdef _WIN32
TEST_F(BuildWithDepsLogTest, DepFileDepsLogCanonicalize) {
  string err;
  const char* manifest =
      "rule cc\n  command = cc $in\n  depfile = $out.d\n  deps = gcc\n"
      "build a/b\\c\\d/e/fo$ o.o: cc x\\y/z\\foo.c\n";

  fs_.Create("x/y/z/foo.c", "");

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    // Run the build once, everything should be ok.
    DepsLog deps_log;
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);
    EXPECT_TRUE(builder.AddTarget("a/b/c/d/e/fo o.o", &err));
    ASSERT_EQ("", err);
    // Note, different slashes from manifest.
    fs_.Create("a/b\\c\\d/e/fo o.o.d",
               "a\\b\\c\\d\\e\\fo\\ o.o: blah.h bar.h\n");
    EXPECT_TRUE(builder.Build(&err));
    EXPECT_EQ("", err);

    deps_log.Close();
    builder.command_runner_.release();
  }

  {
    State state;
    ASSERT_NO_FATAL_FAILURE(AssertParse(&state, manifest));

    DepsLog deps_log;
    ASSERT_TRUE(deps_log.Load("ninja_deps", &state, &err));
    ASSERT_TRUE(deps_log.OpenForWrite("ninja_deps", &err));
    ASSERT_EQ("", err);

    Builder builder(&state, config_, NULL, &deps_log, &fs_);
    builder.command_runner_.reset(&command_runner_);

    Edge* edge = state.edges_.back();

    state.GetNode("bar.h", 0)->MarkDirty();  // Mark bar.h as missing.
    EXPECT_TRUE(builder.AddTarget("a/b/c/d/e/fo o.o", &err));
    ASSERT_EQ("", err);

    // Expect three new edges: one generating fo o.o, and two more from
    // loading the depfile.
    ASSERT_EQ(3u, state.edges_.size());
    // Expect our edge to now have three inputs: foo.c and two headers.
    ASSERT_EQ(3u, edge->inputs_.size());

    // Expect the command line we generate to only use the original input.
    // Note, slashes from manifest, not .d.
    ASSERT_EQ("cc x\\y/z\\foo.c", edge->EvaluateCommand());

    deps_log.Close();
    builder.command_runner_.release();
  }
}
#endif

/// Check that a restat rule doesn't clear an edge if the depfile is missing.
/// Follows from: https://github.com/ninja-build/ninja/issues/603
TEST_F(BuildTest, RestatMissingDepfile) {
const char* manifest =
"rule true\n"
"  command = true\n"  // Would be "write if out-of-date" in reality.
"  restat = 1\n"
"build header.h: true header.in\n"
"build out: cat header.h\n"
"  depfile = out.d\n";

  fs_.Create("header.h", "");
  fs_.Tick();
  fs_.Create("out", "");
  fs_.Create("header.in", "");

  // Normally, only 'header.h' would be rebuilt, as
  // its rule doesn't touch the output and has 'restat=1' set.
  // But we are also missing the depfile for 'out',
  // which should force its command to run anyway!
  RebuildTarget("out", manifest);
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());
}

/// Check that a restat rule doesn't clear an edge if the deps are missing.
/// https://github.com/ninja-build/ninja/issues/603
TEST_F(BuildWithDepsLogTest, RestatMissingDepfileDepslog) {
  string err;
  const char* manifest =
"rule true\n"
"  command = true\n"  // Would be "write if out-of-date" in reality.
"  restat = 1\n"
"build header.h: true header.in\n"
"build out: cat header.h\n"
"  deps = gcc\n"
"  depfile = out.d\n";

  // Build once to populate ninja deps logs from out.d
  fs_.Create("header.in", "");
  fs_.Create("out.d", "out: header.h");
  fs_.Create("header.h", "");

  RebuildTarget("out", manifest, "build_log", "ninja_deps");
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());

  // Sanity: this rebuild should be NOOP
  RebuildTarget("out", manifest, "build_log", "ninja_deps");
  ASSERT_EQ(0u, command_runner_.commands_ran_.size());

  // Touch 'header.in', blank dependencies log (create a different one).
  // Building header.h triggers 'restat' outputs cleanup.
  // Validate that out is rebuilt netherless, as deps are missing.
  fs_.Tick();
  fs_.Create("header.in", "");

  // (switch to a new blank deps_log "ninja_deps2")
  RebuildTarget("out", manifest, "build_log", "ninja_deps2");
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());

  // Sanity: this build should be NOOP
  RebuildTarget("out", manifest, "build_log", "ninja_deps2");
  ASSERT_EQ(0u, command_runner_.commands_ran_.size());

  // Check that invalidating deps by target timestamp also works here
  // Repeat the test but touch target instead of blanking the log.
  fs_.Tick();
  fs_.Create("header.in", "");
  fs_.Create("out", "");
  RebuildTarget("out", manifest, "build_log", "ninja_deps2");
  ASSERT_EQ(2u, command_runner_.commands_ran_.size());

  // And this build should be NOOP again
  RebuildTarget("out", manifest, "build_log", "ninja_deps2");
  ASSERT_EQ(0u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, WrongOutputInDepfileCausesRebuild) {
  string err;
  const char* manifest =
"rule cc\n"
"  command = cc $in\n"
"  depfile = $out.d\n"
"build foo.o: cc foo.c\n";

  fs_.Create("foo.c", "");
  fs_.Create("foo.o", "");
  fs_.Create("header.h", "");
  fs_.Create("foo.o.d", "bar.o.d: header.h\n");

  RebuildTarget("foo.o", manifest, "build_log", "ninja_deps");
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

TEST_F(BuildTest, Console) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule console\n"
"  command = console\n"
"  pool = console\n"
"build cons: console in.txt\n"));

  fs_.Create("in.txt", "");

  string err;
  EXPECT_TRUE(builder_.AddTarget("cons", &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(builder_.Build(&err));
  EXPECT_EQ("", err);
  ASSERT_EQ(1u, command_runner_.commands_ran_.size());
}

*/


}
