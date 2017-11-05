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


use std::rc::Rc;
use std::cell::{Cell, RefCell};
use std::borrow::Cow;
use std::ops::Range;

use super::state::{Pool, State, NodeState};
use super::build_log::BuildLog;
use super::deps_log::DepsLog;
use super::disk_interface::DiskInterface;
use super::state::{PHONY_RULE, CONSOLE_POOL};
use super::eval_env::{Env, Rule, BindingEnv};
use super::timestamp::TimeStamp;
use super::utils::WINDOWS_PATH;
use super::utils::{decanonicalize_path, pathbuf_from_bytes};
use super::utils::{ExtendFromEscapedSlice, RangeContains};

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct NodeIndex(pub(crate) usize);

#[derive(Clone, Copy, PartialOrd, Ord, PartialEq, Eq, Debug)]
pub struct EdgeIndex(pub(crate) usize);

/// Information about a node in the dependency graph: the file, whether
/// it's dirty, mtime, etc.
pub struct Node {
    path: Vec<u8>,

    /// Set bits starting from lowest for backslashes that were normalized to
    /// forward slashes by CanonicalizePath. See |PathDecanonicalized|.
    slash_bits: u64,

    /// The Edge that produces this Node, or NULL when there is no
    /// known edge to produce it.
    in_edge: Option<EdgeIndex>,

    /// All Edges that use this Node as an input.
    out_edges: Vec<EdgeIndex>,

    /// A dense integer id for the node, assigned and used by DepsLog.
    id: isize,

    /// Possible values of mtime_:
    ///   -1: file hasn't been examined
    ///   0:  we looked, and file doesn't exist
    ///   >0: actual file's mtime
    mtime: TimeStamp,

    /// Dirty is true when the underlying file is out-of-date.
    /// But note that Edge::outputs_ready_ is also used in judging which
    /// edges to build.
    dirty: bool,
}

impl Node {
    pub fn new(path: &[u8], slash_bits: u64) -> Self {
        Node {
            path: path.to_owned(),
            slash_bits,
            in_edge: None,
            out_edges: Vec::new(),
            id: -1,
            mtime: TimeStamp(-1),
            dirty: false,
        }
    }

    pub fn id(&self) -> isize {
        self.id
    }

    pub fn set_id(&mut self, id: isize) {
        self.id = id;
    }

    pub fn path(&self) -> &[u8] {
        &self.path
    }

    pub fn slash_bits(&self) -> u64 {
        self.slash_bits
    }

    pub fn mtime(&self) -> TimeStamp {
        self.mtime
    }

    pub fn is_dirty(&self) -> bool {
        self.dirty
    }

    pub fn set_dirty(&mut self, dirty: bool) {
        self.dirty = dirty;
    }

    pub fn mark_dirty(&mut self) {
        self.dirty = true;
    }

    /// Mark as not-yet-stat()ed and not dirty.
    pub fn reset_state(&mut self) {
        self.mtime = TimeStamp(-1);
        self.dirty = false;
    }

    /// Mark the Node as already-stat()ed and missing.
    pub fn mark_missing(&mut self) {
        self.mtime = TimeStamp(0);
    }

    pub fn exists(&self) -> bool {
        self.mtime.0 != 0
    }

    pub fn status_known(&self) -> bool {
        self.mtime.0 != -1
    }

    pub fn in_edge(&self) -> Option<EdgeIndex> {
        self.in_edge
    }

    pub fn set_in_edge(&mut self, edge: Option<EdgeIndex>) {
        self.in_edge = edge;
    }
    
    pub fn out_edges(&self) -> &[EdgeIndex] {
        &self.out_edges
    }

    pub fn add_out_edge(&mut self, edge: EdgeIndex) {
        self.out_edges.push(edge);
    }

    /// Get |path()| but use slash_bits to convert back to original slash styles.
    pub fn path_decanonicalized(&self) -> Vec<u8> {
        decanonicalize_path(&self.path, self.slash_bits)
    }

    /// Return false on error.
    pub fn stat(&mut self, disk_interface: &DiskInterface) -> Result<(), String> {
        self.mtime = TimeStamp(-1);

        let pathbuf = pathbuf_from_bytes(self.path.clone()).map_err(|e| {
            format!("invalid utf-8 pathname: {}", String::from_utf8_lossy(&e))
        })?;

        self.mtime = disk_interface.stat(&pathbuf)?;
        Ok(())
    }

    /// Return false on error.
    pub fn stat_if_necessary(&mut self, disk_interface: &DiskInterface) -> Result<(), String> {
        if self.status_known() {
            return Ok(());
        }

        self.stat(disk_interface)
    }
}

/*

struct Node {

  void Dump(const char* prefix="") const;

private:
};
*/

#[derive(Clone, Copy)]
pub enum EdgeVisitMark {
  VisitNone,
  VisitInStack,
  VisitDone
}

/// An edge in the dependency graph; links between Nodes using Rules.
pub struct Edge {
    rule: Rc<Rule>,
    pub pool: Rc<RefCell<Pool>>,
    pub inputs: Vec<NodeIndex>,
    pub outputs: Vec<NodeIndex>,
    pub env: Rc<RefCell<BindingEnv>>,
    pub mark: EdgeVisitMark,
    pub outputs_ready: bool,
    pub deps_missing: bool,
    pub implicit_deps: usize,
    pub order_only_deps: usize,
    pub implicit_outs: usize,
}

impl Edge {
    pub fn new(rule: Rc<Rule>, pool: Rc<RefCell<Pool>>, env: Rc<RefCell<BindingEnv>>) -> Self {
        Edge {
          rule,
          pool,
          inputs: Vec::new(),
          outputs: Vec::new(),
          env,
          mark: EdgeVisitMark::VisitNone,
          outputs_ready: false,
          deps_missing: false,
          implicit_deps: 0,
          order_only_deps: 0,
          implicit_outs: 0
        }
    }

    pub fn rule(&self) -> &Rc<Rule> {
        &self.rule
    }

    pub fn pool(&self) -> &Rc<RefCell<Pool>> {
        &self.pool
    }

    pub fn weight(&self) -> usize { 
        1 
    }

    pub fn outputs_ready(&self) -> bool { 
        self.outputs_ready
    }
    
    // There are three types of inputs.
    // 1) explicit deps, which show up as $in on the command line;
    // 2) implicit deps, which the target depends on implicitly (e.g. C headers),
    //                   and changes in them cause the target to rebuild;
    // 3) order-only deps, which are needed before the target builds but which
    //                     don't cause the target to rebuild.
    // These are stored in inputs_ in that order, and we keep counts of
    // #2 and #3 when we need to access the various subsets.
    pub fn explicit_deps_range(&self) -> Range<usize> {
        0..(self.inputs.len() - self.implicit_deps - self.order_only_deps)
    }

    pub fn implicit_deps_range(&self) -> Range<usize> {
        (self.inputs.len() - self.implicit_deps - self.order_only_deps)..
        (self.inputs.len() - self.order_only_deps)
    }

    pub fn non_order_only_deps_range(&self) -> Range<usize> {
        0..(self.inputs.len() - self.order_only_deps)
    }

    pub fn order_only_deps_range(&self) -> Range<usize> {
        (self.inputs.len() - self.order_only_deps)..(self.inputs.len())
    }

    // There are two types of outputs.
    // 1) explicit outs, which show up as $out on the command line;
    // 2) implicit outs, which the target generates but are not part of $out.
    // These are stored in outputs_ in that order, and we keep a count of
    // #2 to use when we need to access the various subsets.
    pub fn explicit_outs_range(&self) -> Range<usize> {
        0..(self.outputs.len() - self.implicit_outs)
    }

    pub fn implicit_outs_range(&self) -> Range<usize> {
        (self.outputs.len() - self.implicit_outs)..(self.outputs.len())
    }

    /// Returns the shell-escaped value of |key|.
    pub fn get_binding(&self, node_state: &NodeState, key: &[u8]) -> Cow<[u8]> {
        let env = EdgeEnv::new(self, node_state, EdgeEnvEscapeKind::ShellEscape);
        env.lookup_variable(key).into_owned().into()
    }

    pub fn get_binding_bool(&self, node_state: &NodeState, key: &[u8]) -> bool {
        !self.get_binding(node_state, key).is_empty()
    }

    /// Like GetBinding("depfile"), but without shell escaping.
    pub fn get_unescaped_depfile(&self, node_state: &NodeState) -> Cow<[u8]> {
        let env = EdgeEnv::new(self, node_state, EdgeEnvEscapeKind::DoNotEscape);
        env.lookup_variable(b"depfile").into_owned().into()
    }

    /// Like GetBinding("rspfile"), but without shell escaping.
    pub fn get_unescaped_rspfile(&self, node_state: &NodeState) -> Cow<[u8]> {
        let env = EdgeEnv::new(self, node_state, EdgeEnvEscapeKind::DoNotEscape);
        env.lookup_variable(b"rspfile").into_owned().into()
    }

    pub fn is_phony(&self) -> bool {
        self.rule.as_ref() as * const Rule == 
          PHONY_RULE.with(|x| x.as_ref() as * const Rule)
    }

    pub fn use_console(&self) -> bool {
        &*self.pool().borrow() as * const Pool ==
          CONSOLE_POOL.with(|x| &*x.borrow() as * const Pool)
    }

    /// Expand all variables in a command and return it as a string.
    /// If incl_rsp_file is enabled, the string will also contain the
    /// full contents of a response file (if applicable)
    pub fn evaluate_command(&self, node_state: &NodeState) -> Vec<u8> {
        self.evaluate_command_with_rsp_file(node_state, false)
    }

    pub fn evaluate_command_with_rsp_file(&self, node_state: &NodeState, incl_rsp_file: bool) -> Vec<u8> {
        let mut command = self.get_binding(node_state, b"command").into_owned();
        if incl_rsp_file {
            let rspfile_content = self.get_binding(node_state, b"rspfile_content");
            if !rspfile_content.is_empty() {
                command.extend_from_slice(b";rspfile=");
                command.extend_from_slice(rspfile_content.as_ref());
            }
        }
        command
    }

    pub fn maybe_phonycycle_diagnostic(&self) -> bool {
        // CMake 2.8.12.x and 3.0.x produced self-referencing phony rules
        // of the form "build a: phony ... a ...".   Restrict our
        // "phonycycle" diagnostic option to the form it used.
        self.is_phony() && self.outputs.len() == 1 && 
          self.implicit_outs == 0 && self.implicit_deps == 0
    }

    /// Return true if all inputs' in-edges are ready.
    pub fn all_inputs_ready(&self, state: &State) -> bool {
        for input_idx in self.inputs.iter() {
            let input = state.node_state.get_node(*input_idx);
            if let Some(in_edge) = input.in_edge() {
                if !state.edge_state.get_edge(in_edge).outputs_ready() {
                    return false;
                }
            }
        }
        return true;
    }

    pub fn dump(&self) {
        unimplemented!();
    }
}


/*

struct Edge {

  void Dump(const char* prefix="") const;
};

*/
/// ImplicitDepLoader loads implicit dependencies, as referenced via the
/// "depfile" attribute in build files.
struct ImplicitDepLoader<'b, 'c> {
    disk_interface: &'c DiskInterface,
    deps_log: &'b DepsLog,
}

impl<'b, 'c> ImplicitDepLoader<'b, 'c> {
    pub fn new(deps_log: &'b DepsLog, disk_interface: &'c DiskInterface) -> Self {
        ImplicitDepLoader {
            deps_log,
            disk_interface,
        }
    }

    pub fn deps_log(&self) -> &'b DepsLog {
        self.deps_log
    }

    /// Load implicit dependencies for \a edge.
    /// @return false on error (without filling \a err if info is just missing
    //                          or out of date).
    pub fn load_deps(&self, state: &State, edge_idx: EdgeIndex) -> Result<bool, String> {
        let edge = state.edge_state.get_edge(edge_idx);
        let deps_type = edge.get_binding(&state.node_state, b"deps");
        if !deps_type.is_empty() {
            return self.load_deps_from_log(state, edge_idx);
        }

        let depfile = edge.get_unescaped_depfile(&state.node_state);
        if !depfile.is_empty() {
            return self.load_dep_file(state, edge_idx, &depfile);
        }

        // No deps to load.
        return Ok(true);
    }

    /// Load implicit dependencies for \a edge from a depfile attribute.
    /// @return false on error (without filling \a err if info is just missing).
    pub fn load_dep_file(&self, state: &State, edge_idx: EdgeIndex, path: &[u8]) -> Result<bool, String> {
        unimplemented!{}
    }

    /// Load implicit dependencies for \a edge from the DepsLog.
    /// @return false on error (without filling \a err if info is just missing).
    pub fn load_deps_from_log(&self, state: &State, edge_idx: EdgeIndex) -> Result<bool, String> {
        return Ok(false);
        unimplemented!{}
    }

}

/*
struct ImplicitDepLoader {
  ImplicitDepLoader(State* state, DepsLog* deps_log,
                    DiskInterface* disk_interface)
      : state_(state), disk_interface_(disk_interface), deps_log_(deps_log) {}

  /// Load implicit dependencies for \a edge.
  /// @return false on error (without filling \a err if info is just missing
  //                          or out of date).
  bool LoadDeps(Edge* edge, string* err);

  DepsLog* deps_log() const {
    return deps_log_;
  }

 private:

  /// Preallocate \a count spaces in the input array on \a edge, returning
  /// an iterator pointing at the first new space.
  vector<Node*>::iterator PreallocateSpace(Edge* edge, int count);

  /// If we don't have a edge that generates this input already,
  /// create one; this makes us not abort if the input is missing,
  /// but instead will rebuild in that circumstance.
  void CreatePhonyInEdge(Node* node);

  State* state_;
  DiskInterface* disk_interface_;
  DepsLog* deps_log_;
};

*/

/// DependencyScan manages the process of scanning the files in a graph
/// and updating the dirty/outputs_ready state of all the nodes and edges.
pub struct DependencyScan<'s, 'a, 'b, 'c> where 's : 'a {
    build_log: Option<&'a BuildLog<'s>>,
    deps_log: &'b DepsLog,
    disk_interface: &'c DiskInterface,
    dep_loader: ImplicitDepLoader<'b, 'c>
}

impl<'s, 'a, 'b, 'c> DependencyScan<'s, 'a, 'b, 'c> where 's : 'a {
    pub fn new(build_log: &'a BuildLog<'s>, deps_log: &'b DepsLog, disk_interface: &'c DiskInterface) -> Self {
        DependencyScan {
            build_log: Some(build_log),
            deps_log,
            disk_interface,
            dep_loader: ImplicitDepLoader::new(deps_log, disk_interface)
        }
    }

    pub fn build_log(&self) -> Option<&'a BuildLog<'s>> {
        self.build_log.clone()
    }

    pub fn deps_log(&self) -> &'b DepsLog {
        self.dep_loader.deps_log()
    }

    /// Update the |dirty_| state of the given node by inspecting its input edge.
    /// Examine inputs, outputs, and command lines to judge whether an edge
    /// needs to be re-run, and update outputs_ready_ and each outputs' |dirty_|
    /// state accordingly.
    /// Returns false on failure.
    pub fn recompute_dirty(&self, state: &mut State, node_idx: NodeIndex) -> Result<(), String> {
        let mut stack = Vec::new();
        return self.recompute_dirty_inner(state, node_idx, &mut stack);
    }

    fn recompute_dirty_inner(&self, state: &mut State, node_idx: NodeIndex, stack: &mut Vec<NodeIndex>) -> Result<(), String> {        
        match state.node_state.get_node(node_idx).in_edge.as_ref() {
          None => {
              let node = state.node_state.get_node_mut(node_idx);
              // If we already visited this leaf node then we are done.
              if node.status_known() {
                  return Ok(());
              };
              // This node has no in-edge; it is dirty if it is missing.
              node.stat_if_necessary(self.disk_interface)?;
              if !node.exists() {
                  explain!("{} has no in-edge and is missing", String::from_utf8_lossy(node.path()));
              }
              let dirty = !node.exists();
              node.set_dirty(dirty);
              Ok(())
          },
          Some(&edge_idx) => {
              // If we already finished this edge then we are done.
              match state.edge_state.get_edge(edge_idx).mark {
                  EdgeVisitMark::VisitDone => {return Ok(());},
                  _ => {},
              };

              // If we encountered this edge earlier in the call stack we have a cycle.
              self.verify_dag(state, node_idx, stack)?;

              let mut dirty = false;
              let mut outputs_ready = true;
              let mut deps_missing = false;
              
              // Mark the edge temporarily while in the call stack.
              state.edge_state.get_edge_mut(edge_idx).mark = EdgeVisitMark::VisitInStack;

              stack.push(node_idx);
              // Load output mtimes so we can compare them to the most recent input below.
              for o_idx in state.edge_state.get_edge(edge_idx).outputs.iter().cloned() {
                  state.node_state.get_node_mut(o_idx).stat_if_necessary(self.disk_interface)?;
              };

              if !self.dep_loader.load_deps(state, edge_idx)? {
                  // Failed to load dependency info: rebuild to regenerate it.
                  // LoadDeps() did EXPLAIN() already, no need to do it here.
                  dirty = true;
                  deps_missing = true;
              }

              let mut most_recent_input = None;
              {
                  let (order_only_range, inputs) = {
                      let edge = state.edge_state.get_edge(edge_idx);
                      (edge.order_only_deps_range(), edge.inputs.clone())
                  };
                  
                  for (i, i_idx) in inputs.into_iter().enumerate() {
                      // Visit this input.
                      self.recompute_dirty_inner(state, i_idx, stack)?;

                      // If an input is not ready, neither are our outputs.
                      if let Some(in_edge) = state.node_state.get_node(i_idx).in_edge() {
                          if !state.edge_state.get_edge(in_edge).outputs_ready {
                              outputs_ready = false;
                          }
                      }

                      if !order_only_range.contains_stable(i) {
                          // If a regular input is dirty (or missing), we're dirty.
                          // Otherwise consider mtime.
                          let i_node = state.node_state.get_node(i_idx);
                          if i_node.is_dirty() {
                              explain!("{} is dirty", String::from_utf8_lossy(i_node.path()));
                              dirty = true;
                          } else {
                              if most_recent_input.as_ref().map(|&prev_idx| {
                                 let prev_node = state.node_state.get_node(prev_idx);
                                 i_node.mtime() > prev_node.mtime()
                              }).unwrap_or(true) {
                                 most_recent_input = Some(i_idx);
                              }
                          }
                      }
                  }
              }
              // We may also be dirty due to output state: missing outputs, out of
              // date outputs, etc.  Visit all outputs and determine whether they're dirty.
              if !dirty {
                  dirty = self.recompute_outputs_dirty(state, edge_idx, most_recent_input)?;
              }

              if dirty {
                  let edge = state.edge_state.get_edge(edge_idx);

                  // Finally, visit each output and update their dirty state if necessary.
                  for o_idx in edge.outputs.iter().cloned() {
                      state.node_state.get_node_mut(o_idx).mark_dirty();
                  }

                  // If an edge is dirty, its outputs are normally not ready.  (It's
                  // possible to be clean but still not be ready in the presence of
                  // order-only inputs.)
                  // But phony edges with no inputs have nothing to do, so are always
                  // ready.

                  if !(edge.is_phony() && edge.inputs.is_empty()) {
                      outputs_ready = false;
                  }
              }

              let edge = state.edge_state.get_edge_mut(edge_idx);
              edge.deps_missing = deps_missing;
              edge.outputs_ready = outputs_ready;

              // Mark the edge as finished during this walk now that it will no longer
              // be in the call stack.
              edge.mark = EdgeVisitMark::VisitDone;
              debug_assert!(stack.last() == Some(&node_idx));
              stack.pop();
              Ok(())
          },
        }
    }

    fn verify_dag(&self, state: &State, node_idx: NodeIndex, stack: &mut Vec<NodeIndex>) -> Result<(), String> {
        let edge_idx = state.node_state.get_node(node_idx).in_edge().unwrap();

        // If we have no temporary mark on the edge then we do not yet have a cycle.
        match state.edge_state.get_edge(edge_idx).mark {
          EdgeVisitMark::VisitInStack => {},
          _ => {return Ok(());}
        };

        // We have this edge earlier in the call stack.  Find it.
        let mut start = 0;
        while start < stack.len() {
            let item = stack[start];
            if state.node_state.get_node(item).in_edge() == Some(edge_idx) {
                break;
            }
            start += 1;
        }
        assert!(start < stack.len());

        // Make the cycle clear by reporting its start as the node at its end
        // instead of some other output of the starting edge.  For example,
        // running 'ninja b' on
        //   build a b: cat c
        //   build c: cat a
        // should report a -> c -> a instead of b -> c -> a.
        stack[start] = node_idx;

        // Construct the error message rejecting the cycle.
        let mut err = "dependency cycle: ".to_owned();
        for iter_idx in stack[start..].iter() {
            err += String::from_utf8_lossy(state.node_state.get_node(*iter_idx).path()).as_ref();
            err += " -> ";
        }

        err += String::from_utf8_lossy(state.node_state.get_node(node_idx).path()).as_ref();

        if start + 1 == stack.len() && state.edge_state.get_edge(edge_idx).maybe_phonycycle_diagnostic() {
            // The manifest parser would have filtered out the self-referencing
            // input if it were not configured to allow the error.
            err += " [-w phonycycle=err]";
        }

        return Err(err);
    }

    /// Recompute whether any output of the edge is dirty, if so sets |*dirty|.
    /// Returns false on failure.
    fn recompute_outputs_dirty(&self, state: &State, edge_idx: EdgeIndex, most_recent_input: Option<NodeIndex>) -> Result<bool, String> {
        let edge = state.edge_state.get_edge(edge_idx);
        let command = edge.evaluate_command_with_rsp_file(&state.node_state, true);
        for output in edge.outputs.iter() {
            if self.recompute_output_dirty(state, edge_idx, most_recent_input, &command, *output) {
                return Ok(true);
            }
        }
        return Ok(false);
    }

    /// Recompute whether a given single output should be marked dirty.
    /// Returns true if so.
    fn recompute_output_dirty(&self, state: &State, edge_idx: EdgeIndex, most_recent_input: Option<NodeIndex>,
        command: &[u8], output_node_idx: NodeIndex) -> bool {
    
        let edge = state.edge_state.get_edge(edge_idx);
        let output = state.node_state.get_node(output_node_idx);
        let mut entry = None;

        if edge.is_phony() {
            // Phony edges don't write any output.  Outputs are only dirty if
            // there are no inputs and we're missing the output.
            if edge.inputs.is_empty() && !output.exists() {
                explain!("output {} of phony edge with no inputs doesn't exist",
                    String::from_utf8_lossy(output.path()));
                
                return true;
            }
            return false;   
        }

        // Dirty if we're missing the output.
        if !output.exists() {
            explain!("output {} doesn't exist", String::from_utf8_lossy(output.path()));
            return true;
        }

        // Dirty if the output is older than the input.
        if let Some(ref most_recent_input_idx) = most_recent_input {
            let most_recent_input = state.node_state.get_node(*most_recent_input_idx);
            if output.mtime() < most_recent_input.mtime() {
                let mut output_mtime = output.mtime();

                // If this is a restat rule, we may have cleaned the output with a restat
                // rule in a previous run and stored the most recent input mtime in the
                // build log.  Use that mtime instead, so that the file will only be
                // considered dirty if an input was modified since the previous run.
                let mut used_restat = false;

                if edge.get_binding_bool(&state.node_state, b"restat") {
                    if let Some(build_log) = self.build_log() {
                        if entry.is_none() {
                            entry = build_log.lookup_by_output(output.path());
                        }
                        if let Some(found_entry) = entry {
                            output_mtime = found_entry.mtime;
                            used_restat = true;
                        }
                    }
                }


                if output_mtime < most_recent_input.mtime() {
                    explain!("{}output {} older than most recent input {} ({} vs {})",
                        if used_restat { "restat of " } else { "" },
                        String::from_utf8_lossy(output.path()),
                        String::from_utf8_lossy(most_recent_input.path()),
                        output_mtime,
                        most_recent_input.mtime);
                    return true;
                }
            }
        }

        if let Some(build_log) = self.build_log() {
            let generator = edge.get_binding_bool(&state.node_state, b"generator");
            if entry.is_none() {
                entry = build_log.lookup_by_output(output.path());
            }
            if let Some(found_entry) = entry {
                unimplemented!()
/*
      if (!generator &&
          BuildLog::LogEntry::HashCommand(command) != entry->command_hash) {
        // May also be dirty due to the command changing since the last build.
        // But if this is a generator rule, the command changing does not make us
        // dirty.
        EXPLAIN("command line changed for %s", output->path().c_str());
        return true;
      }
      if (most_recent_input && entry->mtime < most_recent_input->mtime()) {
        // May also be dirty due to the mtime in the log being older than the
        // mtime of the most recent input.  This can occur even when the mtime
        // on disk is newer if a previous run wrote to the output file but
        // exited with an error or was interrupted.
        EXPLAIN("recorded mtime of %s older than most recent input %s (%d vs %d)",
                output->path().c_str(), most_recent_input->path().c_str(),
                entry->mtime, most_recent_input->mtime());
        return true;
      }
*/
            }

            if entry.is_none() && !generator {
                explain!("command line not found in log for {}", String::from_utf8_lossy(output.path()));
                return true;
            }
        }

        return false;
    }
}

/*

struct DependencyScan {
  DependencyScan(State* state, BuildLog* build_log, DepsLog* deps_log,
                 DiskInterface* disk_interface)
      : build_log_(build_log),
        disk_interface_(disk_interface),
        dep_loader_(state, deps_log, disk_interface) {}

  BuildLog* build_log() const {
    return build_log_;
  }
  void set_build_log(BuildLog* log) {
    build_log_ = log;
  }

  DepsLog* deps_log() const {
    return dep_loader_.deps_log();
  }

 private:
  bool RecomputeDirty(Node* node, vector<Node*>* stack, string* err);
  bool VerifyDAG(Node* node, vector<Node*>* stack, string* err);



  BuildLog* build_log_;
  DiskInterface* disk_interface_;
  ImplicitDepLoader dep_loader_;
};

#endif  // NINJA_GRAPH_H_

*/



/*

bool DependencyScan::RecomputeOutputDirty(Edge* edge,
                                          Node* most_recent_input,
                                          const string& command,
                                          Node* output) {
}

*/

#[derive(Clone, Copy)]
enum EdgeEnvEscapeKind {
    ShellEscape,
    DoNotEscape,
}

/// An Env for an Edge, providing $in and $out.
struct EdgeEnv<'a, 'b> {
    lookups: RefCell<Vec<Vec<u8>>>,
    edge: &'a Edge,
    node_state: &'b NodeState,
    escape_in_out: EdgeEnvEscapeKind,
    recursive: Cell<bool>,
}

impl<'a, 'b> EdgeEnv<'a, 'b> {
    pub fn new(edge: &'a Edge, node_state: &'b NodeState, escape: EdgeEnvEscapeKind) -> Self {
        EdgeEnv {
          lookups: RefCell::new(Vec::new()),
          edge,
          node_state,
          escape_in_out: escape,
          recursive: Cell::new(false)
        }
    }

    /// Given a span of Nodes, construct a list of paths suitable for a command
    /// line.
    pub fn make_path_list(node_state: &NodeState,
        nodes: &[NodeIndex], sep: u8, escape_in_out: EdgeEnvEscapeKind) -> Vec<u8> {

        let mut result = Vec::new();
        for node_idx in nodes {
            if !result.is_empty() {
                result.push(sep);
            };
            let node = node_state.get_node(*node_idx);
            let path = node.path_decanonicalized();
            match escape_in_out {
              EdgeEnvEscapeKind::ShellEscape => {
                  if WINDOWS_PATH {
                      result.extend_from_win32_escaped_slice(&path);
                  } else {
                      result.extend_from_shell_escaped_slice(&path);
                  }
              },
              EdgeEnvEscapeKind::DoNotEscape => {
                  result.extend_from_slice(&path);
              }
            }
        }
        result
    }
}

impl<'a, 'b> Env for EdgeEnv<'a, 'b> {
    fn lookup_variable(&self, var: &[u8]) -> Cow<[u8]> {
        if var == b"in".as_ref() || var == b"in_newline".as_ref() {
            let sep = if var == b"in".as_ref() { b' ' } else { b'\n' };
            let explicit_deps_range = self.edge.explicit_deps_range();
            return Cow::Owned(EdgeEnv::make_path_list(
                self.node_state, 
                &self.edge.inputs[explicit_deps_range], sep,
                self.escape_in_out));
        } else if var == b"out".as_ref() {
            let explicit_outs_range = self.edge.explicit_outs_range();
            return Cow::Owned(EdgeEnv::make_path_list(
                self.node_state, 
                &self.edge.outputs[explicit_outs_range], b' ',
                self.escape_in_out));
        }

        if self.recursive.get() {
            let lookups = self.lookups.borrow();
            let mut lookups_iter = lookups.iter().skip_while(|v| var != v as &[u8]).peekable();
            if lookups_iter.peek().is_some() {
                let mut cycle = Vec::new();
                for it in lookups_iter {
                    cycle.extend_from_slice(&it);
                    cycle.extend_from_slice(b" -> ");
                }
                cycle.extend_from_slice(var);
                fatal!("cycle in rule variables: {}", String::from_utf8_lossy(&cycle))
            }
        }

        // See notes on BindingEnv::LookupWithFallback.
        let eval = self.edge.rule.get_binding(var);
        if self.recursive.get() && eval.is_some() {
            self.lookups.borrow_mut().push(var.to_owned());
        }

        // In practice, variables defined on rules never use another rule variable.
        // For performance, only start checking for cycles after the first lookup.
        self.recursive.set(true);
        return Cow::Owned(self.edge.env.borrow().lookup_with_fallback(var, eval, self).into_owned());
    }
}
/*

void Edge::Dump(const char* prefix) const {
  printf("%s[ ", prefix);
  for (vector<Node*>::const_iterator i = inputs_.begin();
       i != inputs_.end() && *i != NULL; ++i) {
    printf("%s ", (*i)->path().c_str());
  }
  printf("--%s-> ", rule_->name().c_str());
  for (vector<Node*>::const_iterator i = outputs_.begin();
       i != outputs_.end() && *i != NULL; ++i) {
    printf("%s ", (*i)->path().c_str());
  }
  if (pool_) {
    if (!pool_->name().empty()) {
      printf("(in pool '%s')", pool_->name().c_str());
    }
  } else {
    printf("(null pool?)");
  }
  printf("] 0x%p\n", this);
}


void Node::Dump(const char* prefix) const {
  printf("%s <%s 0x%p> mtime: %d%s, (:%s), ",
         prefix, path().c_str(), this,
         mtime(), mtime() ? "" : " (:missing)",
         dirty() ? " dirty" : " clean");
  if (in_edge()) {
    in_edge()->Dump("in-edge: ");
  } else {
    printf("no in-edge\n");
  }
  printf(" out edges:\n");
  for (vector<Edge*>::const_iterator e = out_edges().begin();
       e != out_edges().end() && *e != NULL; ++e) {
    (*e)->Dump(" +- ");
  }
}

bool ImplicitDepLoader::LoadDeps(Edge* edge, string* err) {
  string deps_type = edge->GetBinding("deps");
  if (!deps_type.empty())
    return LoadDepsFromLog(edge, err);

  string depfile = edge->GetUnescapedDepfile();
  if (!depfile.empty())
    return LoadDepFile(edge, depfile, err);

  // No deps to load.
  return true;
}

bool ImplicitDepLoader::LoadDepFile(Edge* edge, const string& path,
                                    string* err) {
  METRIC_RECORD("depfile load");
  // Read depfile content.  Treat a missing depfile as empty.
  string content;
  switch (disk_interface_->ReadFile(path, &content, err)) {
  case DiskInterface::Okay:
    break;
  case DiskInterface::NotFound:
    err->clear();
    break;
  case DiskInterface::OtherError:
    *err = "loading '" + path + "': " + *err;
    return false;
  }
  // On a missing depfile: return false and empty *err.
  if (content.empty()) {
    EXPLAIN("depfile '%s' is missing", path.c_str());
    return false;
  }

  DepfileParser depfile;
  string depfile_err;
  if (!depfile.Parse(&content, &depfile_err)) {
    *err = path + ": " + depfile_err;
    return false;
  }

  uint64_t unused;
  if (!CanonicalizePath(const_cast<char*>(depfile.out_.str_),
                        &depfile.out_.len_, &unused, err)) {
    *err = path + ": " + *err;
    return false;
  }

  // Check that this depfile matches the edge's output, if not return false to
  // mark the edge as dirty.
  Node* first_output = edge->outputs_[0];
  StringPiece opath = StringPiece(first_output->path());
  if (opath != depfile.out_) {
    EXPLAIN("expected depfile '%s' to mention '%s', got '%s'", path.c_str(),
            first_output->path().c_str(), depfile.out_.AsString().c_str());
    return false;
  }

  // Preallocate space in edge->inputs_ to be filled in below.
  vector<Node*>::iterator implicit_dep =
      PreallocateSpace(edge, depfile.ins_.size());

  // Add all its in-edges.
  for (vector<StringPiece>::iterator i = depfile.ins_.begin();
       i != depfile.ins_.end(); ++i, ++implicit_dep) {
    uint64_t slash_bits;
    if (!CanonicalizePath(const_cast<char*>(i->str_), &i->len_, &slash_bits,
                          err))
      return false;

    Node* node = state_->GetNode(*i, slash_bits);
    *implicit_dep = node;
    node->AddOutEdge(edge);
    CreatePhonyInEdge(node);
  }

  return true;
}

bool ImplicitDepLoader::LoadDepsFromLog(Edge* edge, string* err) {
  // NOTE: deps are only supported for single-target edges.
  Node* output = edge->outputs_[0];
  DepsLog::Deps* deps = deps_log_->GetDeps(output);
  if (!deps) {
    EXPLAIN("deps for '%s' are missing", output->path().c_str());
    return false;
  }

  // Deps are invalid if the output is newer than the deps.
  if (output->mtime() > deps->mtime) {
    EXPLAIN("stored deps info out of date for '%s' (%d vs %d)",
            output->path().c_str(), deps->mtime, output->mtime());
    return false;
  }

  vector<Node*>::iterator implicit_dep =
      PreallocateSpace(edge, deps->node_count);
  for (int i = 0; i < deps->node_count; ++i, ++implicit_dep) {
    Node* node = deps->nodes[i];
    *implicit_dep = node;
    node->AddOutEdge(edge);
    CreatePhonyInEdge(node);
  }
  return true;
}

vector<Node*>::iterator ImplicitDepLoader::PreallocateSpace(Edge* edge,
                                                            int count) {
  edge->inputs_.insert(edge->inputs_.end() - edge->order_only_deps_,
                       (size_t)count, 0);
  edge->implicit_deps_ += count;
  return edge->inputs_.end() - edge->order_only_deps_ - count;
}

void ImplicitDepLoader::CreatePhonyInEdge(Node* node) {
  if (node->in_edge())
    return;

  Edge* phony_edge = state_->AddEdge(&State::kPhonyRule);
  node->set_in_edge(phony_edge);
  phony_edge->outputs_.push_back(node);

  // RecomputeDirty might not be called for phony_edge if a previous call
  // to RecomputeDirty had caused the file to be stat'ed.  Because previous
  // invocations of RecomputeDirty would have seen this node without an
  // input edge (and therefore ready), we have to set outputs_ready_ to true
  // to avoid a potential stuck build.  If we do call RecomputeDirty for
  // this node, it will simply set outputs_ready_ to the correct value.
  phony_edge->outputs_ready_ = true;
}

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

#include "graph.h"
#include "build.h"

#include "test.h"

struct GraphTest : public StateTestWithBuiltinRules {
  GraphTest() : scan_(&state_, NULL, NULL, &fs_) {}

  VirtualFileSystem fs_;
  DependencyScan scan_;
};

TEST_F(GraphTest, MissingImplicit) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out: cat in | implicit\n"));
  fs_.Create("in", "");
  fs_.Create("out", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out"), &err));
  ASSERT_EQ("", err);

  // A missing implicit dep *should* make the output dirty.
  // (In fact, a build will fail.)
  // This is a change from prior semantics of ninja.
  EXPECT_TRUE(GetNode("out")->dirty());
}

TEST_F(GraphTest, ModifiedImplicit) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out: cat in | implicit\n"));
  fs_.Create("in", "");
  fs_.Create("out", "");
  fs_.Tick();
  fs_.Create("implicit", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out"), &err));
  ASSERT_EQ("", err);

  // A modified implicit dep should make the output dirty.
  EXPECT_TRUE(GetNode("out")->dirty());
}

TEST_F(GraphTest, FunkyMakefilePath) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule catdep\n"
"  depfile = $out.d\n"
"  command = cat $in > $out\n"
"build out.o: catdep foo.cc\n"));
  fs_.Create("foo.cc",  "");
  fs_.Create("out.o.d", "out.o: ./foo/../implicit.h\n");
  fs_.Create("out.o", "");
  fs_.Tick();
  fs_.Create("implicit.h", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.o"), &err));
  ASSERT_EQ("", err);

  // implicit.h has changed, though our depfile refers to it with a
  // non-canonical path; we should still find it.
  EXPECT_TRUE(GetNode("out.o")->dirty());
}

TEST_F(GraphTest, ExplicitImplicit) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule catdep\n"
"  depfile = $out.d\n"
"  command = cat $in > $out\n"
"build implicit.h: cat data\n"
"build out.o: catdep foo.cc || implicit.h\n"));
  fs_.Create("implicit.h", "");
  fs_.Create("foo.cc", "");
  fs_.Create("out.o.d", "out.o: implicit.h\n");
  fs_.Create("out.o", "");
  fs_.Tick();
  fs_.Create("data", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.o"), &err));
  ASSERT_EQ("", err);

  // We have both an implicit and an explicit dep on implicit.h.
  // The implicit dep should "win" (in the sense that it should cause
  // the output to be dirty).
  EXPECT_TRUE(GetNode("out.o")->dirty());
}

TEST_F(GraphTest, ImplicitOutputParse) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out | out.imp: cat in\n"));

  Edge* edge = GetNode("out")->in_edge();
  EXPECT_EQ(2, edge->outputs_.size());
  EXPECT_EQ("out", edge->outputs_[0]->path());
  EXPECT_EQ("out.imp", edge->outputs_[1]->path());
  EXPECT_EQ(1, edge->implicit_outs_);
  EXPECT_EQ(edge, GetNode("out.imp")->in_edge());
}

TEST_F(GraphTest, ImplicitOutputMissing) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out | out.imp: cat in\n"));
  fs_.Create("in", "");
  fs_.Create("out", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out"), &err));
  ASSERT_EQ("", err);

  EXPECT_TRUE(GetNode("out")->dirty());
  EXPECT_TRUE(GetNode("out.imp")->dirty());
}

TEST_F(GraphTest, ImplicitOutputOutOfDate) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out | out.imp: cat in\n"));
  fs_.Create("out.imp", "");
  fs_.Tick();
  fs_.Create("in", "");
  fs_.Create("out", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out"), &err));
  ASSERT_EQ("", err);

  EXPECT_TRUE(GetNode("out")->dirty());
  EXPECT_TRUE(GetNode("out.imp")->dirty());
}

TEST_F(GraphTest, ImplicitOutputOnlyParse) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build | out.imp: cat in\n"));

  Edge* edge = GetNode("out.imp")->in_edge();
  EXPECT_EQ(1, edge->outputs_.size());
  EXPECT_EQ("out.imp", edge->outputs_[0]->path());
  EXPECT_EQ(1, edge->implicit_outs_);
  EXPECT_EQ(edge, GetNode("out.imp")->in_edge());
}

TEST_F(GraphTest, ImplicitOutputOnlyMissing) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build | out.imp: cat in\n"));
  fs_.Create("in", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.imp"), &err));
  ASSERT_EQ("", err);

  EXPECT_TRUE(GetNode("out.imp")->dirty());
}

TEST_F(GraphTest, ImplicitOutputOnlyOutOfDate) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build | out.imp: cat in\n"));
  fs_.Create("out.imp", "");
  fs_.Tick();
  fs_.Create("in", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.imp"), &err));
  ASSERT_EQ("", err);

  EXPECT_TRUE(GetNode("out.imp")->dirty());
}

TEST_F(GraphTest, PathWithCurrentDirectory) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule catdep\n"
"  depfile = $out.d\n"
"  command = cat $in > $out\n"
"build ./out.o: catdep ./foo.cc\n"));
  fs_.Create("foo.cc", "");
  fs_.Create("out.o.d", "out.o: foo.cc\n");
  fs_.Create("out.o", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.o"), &err));
  ASSERT_EQ("", err);

  EXPECT_FALSE(GetNode("out.o")->dirty());
}

TEST_F(GraphTest, RootNodes) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out1: cat in1\n"
"build mid1: cat in1\n"
"build out2: cat mid1\n"
"build out3 out4: cat mid1\n"));

  string err;
  vector<Node*> root_nodes = state_.RootNodes(&err);
  EXPECT_EQ(4u, root_nodes.size());
  for (size_t i = 0; i < root_nodes.size(); ++i) {
    string name = root_nodes[i]->path();
    EXPECT_EQ("out", name.substr(0, 3));
  }
}

TEST_F(GraphTest, VarInOutPathEscaping) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build a$ b: cat no'space with$ space$$ no\"space2\n"));

  Edge* edge = GetNode("a b")->in_edge();
#if _WIN32
  EXPECT_EQ("cat no'space \"with space$\" \"no\\\"space2\" > \"a b\"",
      edge->EvaluateCommand());
#else
  EXPECT_EQ("cat 'no'\\''space' 'with space$' 'no\"space2' > 'a b'",
      edge->EvaluateCommand());
#endif
}

// Regression test for https://github.com/ninja-build/ninja/issues/380
TEST_F(GraphTest, DepfileWithCanonicalizablePath) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule catdep\n"
"  depfile = $out.d\n"
"  command = cat $in > $out\n"
"build ./out.o: catdep ./foo.cc\n"));
  fs_.Create("foo.cc", "");
  fs_.Create("out.o.d", "out.o: bar/../foo.cc\n");
  fs_.Create("out.o", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.o"), &err));
  ASSERT_EQ("", err);

  EXPECT_FALSE(GetNode("out.o")->dirty());
}

// Regression test for https://github.com/ninja-build/ninja/issues/404
TEST_F(GraphTest, DepfileRemoved) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule catdep\n"
"  depfile = $out.d\n"
"  command = cat $in > $out\n"
"build ./out.o: catdep ./foo.cc\n"));
  fs_.Create("foo.h", "");
  fs_.Create("foo.cc", "");
  fs_.Tick();
  fs_.Create("out.o.d", "out.o: foo.h\n");
  fs_.Create("out.o", "");

  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.o"), &err));
  ASSERT_EQ("", err);
  EXPECT_FALSE(GetNode("out.o")->dirty());

  state_.Reset();
  fs_.RemoveFile("out.o.d");
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("out.o"), &err));
  ASSERT_EQ("", err);
  EXPECT_TRUE(GetNode("out.o")->dirty());
}

// Check that rule-level variables are in scope for eval.
TEST_F(GraphTest, RuleVariablesInScope) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule r\n"
"  depfile = x\n"
"  command = depfile is $depfile\n"
"build out: r in\n"));
  Edge* edge = GetNode("out")->in_edge();
  EXPECT_EQ("depfile is x", edge->EvaluateCommand());
}

// Check that build statements can override rule builtins like depfile.
TEST_F(GraphTest, DepfileOverride) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule r\n"
"  depfile = x\n"
"  command = unused\n"
"build out: r in\n"
"  depfile = y\n"));
  Edge* edge = GetNode("out")->in_edge();
  EXPECT_EQ("y", edge->GetBinding("depfile"));
}

// Check that overridden values show up in expansion of rule-level bindings.
TEST_F(GraphTest, DepfileOverrideParent) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"rule r\n"
"  depfile = x\n"
"  command = depfile is $depfile\n"
"build out: r in\n"
"  depfile = y\n"));
  Edge* edge = GetNode("out")->in_edge();
  EXPECT_EQ("depfile is y", edge->GetBinding("command"));
}

// Verify that building a nested phony rule prints "no work to do"
TEST_F(GraphTest, NestedPhonyPrintsDone) {
  AssertParse(&state_,
"build n1: phony \n"
"build n2: phony n1\n"
  );
  string err;
  EXPECT_TRUE(scan_.RecomputeDirty(GetNode("n2"), &err));
  ASSERT_EQ("", err);

  Plan plan_;
  EXPECT_TRUE(plan_.AddTarget(GetNode("n2"), &err));
  ASSERT_EQ("", err);

  EXPECT_EQ(0, plan_.command_edge_count());
  ASSERT_FALSE(plan_.more_to_do());
}

TEST_F(GraphTest, PhonySelfReferenceError) {
  ManifestParserOptions parser_opts;
  parser_opts.phony_cycle_action_ = kPhonyCycleActionError;
  AssertParse(&state_,
"build a: phony a\n",
  parser_opts);

  string err;
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("a"), &err));
  ASSERT_EQ("dependency cycle: a -> a [-w phonycycle=err]", err);
}

TEST_F(GraphTest, DependencyCycle) {
  AssertParse(&state_,
"build out: cat mid\n"
"build mid: cat in\n"
"build in: cat pre\n"
"build pre: cat out\n");

  string err;
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("out"), &err));
  ASSERT_EQ("dependency cycle: out -> mid -> in -> pre -> out", err);
}

TEST_F(GraphTest, CycleInEdgesButNotInNodes1) {
  string err;
  AssertParse(&state_,
"build a b: cat a\n");
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("b"), &err));
  ASSERT_EQ("dependency cycle: a -> a", err);
}

TEST_F(GraphTest, CycleInEdgesButNotInNodes2) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build b a: cat a\n"));
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("b"), &err));
  ASSERT_EQ("dependency cycle: a -> a", err);
}

TEST_F(GraphTest, CycleInEdgesButNotInNodes3) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build a b: cat c\n"
"build c: cat a\n"));
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("b"), &err));
  ASSERT_EQ("dependency cycle: a -> c -> a", err);
}

TEST_F(GraphTest, CycleInEdgesButNotInNodes4) {
  string err;
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build d: cat c\n"
"build c: cat b\n"
"build b: cat a\n"
"build a e: cat d\n"
"build f: cat e\n"));
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("f"), &err));
  ASSERT_EQ("dependency cycle: a -> d -> c -> b -> a", err);
}

// Verify that cycles in graphs with multiple outputs are handled correctly
// in RecomputeDirty() and don't cause deps to be loaded multiple times.
TEST_F(GraphTest, CycleWithLengthZeroFromDepfile) {
  AssertParse(&state_,
"rule deprule\n"
"   depfile = dep.d\n"
"   command = unused\n"
"build a b: deprule\n"
  );
  fs_.Create("dep.d", "a: b\n");

  string err;
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("a"), &err));
  ASSERT_EQ("dependency cycle: b -> b", err);

  // Despite the depfile causing edge to be a cycle (it has outputs a and b,
  // but the depfile also adds b as an input), the deps should have been loaded
  // only once:
  Edge* edge = GetNode("a")->in_edge();
  EXPECT_EQ(1, edge->inputs_.size());
  EXPECT_EQ("b", edge->inputs_[0]->path());
}

// Like CycleWithLengthZeroFromDepfile but with a higher cycle length.
TEST_F(GraphTest, CycleWithLengthOneFromDepfile) {
  AssertParse(&state_,
"rule deprule\n"
"   depfile = dep.d\n"
"   command = unused\n"
"rule r\n"
"   command = unused\n"
"build a b: deprule\n"
"build c: r b\n"
  );
  fs_.Create("dep.d", "a: c\n");

  string err;
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("a"), &err));
  ASSERT_EQ("dependency cycle: b -> c -> b", err);

  // Despite the depfile causing edge to be a cycle (|edge| has outputs a and b,
  // but c's in_edge has b as input but the depfile also adds |edge| as
  // output)), the deps should have been loaded only once:
  Edge* edge = GetNode("a")->in_edge();
  EXPECT_EQ(1, edge->inputs_.size());
  EXPECT_EQ("c", edge->inputs_[0]->path());
}

// Like CycleWithLengthOneFromDepfile but building a node one hop away from
// the cycle.
TEST_F(GraphTest, CycleWithLengthOneFromDepfileOneHopAway) {
  AssertParse(&state_,
"rule deprule\n"
"   depfile = dep.d\n"
"   command = unused\n"
"rule r\n"
"   command = unused\n"
"build a b: deprule\n"
"build c: r b\n"
"build d: r a\n"
  );
  fs_.Create("dep.d", "a: c\n");

  string err;
  EXPECT_FALSE(scan_.RecomputeDirty(GetNode("d"), &err));
  ASSERT_EQ("dependency cycle: b -> c -> b", err);

  // Despite the depfile causing edge to be a cycle (|edge| has outputs a and b,
  // but c's in_edge has b as input but the depfile also adds |edge| as
  // output)), the deps should have been loaded only once:
  Edge* edge = GetNode("a")->in_edge();
  EXPECT_EQ(1, edge->inputs_.size());
  EXPECT_EQ("c", edge->inputs_[0]->path());
}

#ifdef _WIN32
TEST_F(GraphTest, Decanonicalize) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(&state_,
"build out\\out1: cat src\\in1\n"
"build out\\out2/out3\\out4: cat mid1\n"
"build out3 out4\\foo: cat mid1\n"));

  string err;
  vector<Node*> root_nodes = state_.RootNodes(&err);
  EXPECT_EQ(4u, root_nodes.size());
  EXPECT_EQ(root_nodes[0]->path(), "out/out1");
  EXPECT_EQ(root_nodes[1]->path(), "out/out2/out3/out4");
  EXPECT_EQ(root_nodes[2]->path(), "out3");
  EXPECT_EQ(root_nodes[3]->path(), "out4/foo");
  EXPECT_EQ(root_nodes[0]->PathDecanonicalized(), "out\\out1");
  EXPECT_EQ(root_nodes[1]->PathDecanonicalized(), "out\\out2/out3\\out4");
  EXPECT_EQ(root_nodes[2]->PathDecanonicalized(), "out3");
  EXPECT_EQ(root_nodes[3]->PathDecanonicalized(), "out4\\foo");
}
#endif

*/