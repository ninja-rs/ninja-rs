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
use super::utils::decanonicalize_path;
use super::utils::ExtendFromEscapedSlice;

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

    /// Possible values of mtime_:
    ///   -1: file hasn't been examined
    ///   0:  we looked, and file doesn't exist
    ///   >0: actual file's mtime
    mtime: TimeStamp,

    /// Dirty is true when the underlying file is out-of-date.
    /// But note that Edge::outputs_ready_ is also used in judging which
    /// edges to build.
    dirty: bool,

    /// The Edge that produces this Node, or NULL when there is no
    /// known edge to produce it.
    in_edge: Option<EdgeIndex>,

    /// All Edges that use this Node as an input.
    out_edges: Vec<EdgeIndex>,

    /// A dense integer id for the node, assigned and used by DepsLog.
    id: isize,
}

impl Node {
    pub fn new(path: &[u8], slash_bits: u64) -> Self {
        Node {
        path: path.to_owned(),
        slash_bits,
        mtime: TimeStamp(-1),
        dirty: false,
        in_edge: None,
        out_edges: Vec::new(),
        id: -1
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

    pub fn stat(&self, disk_interface: &DiskInterface) -> Result<(), String> {
        unimplemented!()
    }

    pub fn stat_if_necessary(&self, disk_interface: &DiskInterface) -> Result<(), String> {
        if self.status_known() {
            return Ok(());
        }

        self.stat(disk_interface)
    }
}

/*

struct Node {

  /// Return false on error.
  bool Stat(DiskInterface* disk_interface, string* err);

  /// Return false on error.
  bool StatIfNecessary(DiskInterface* disk_interface, string* err) {
    if (status_known())
      return true;
    return Stat(disk_interface, err);
  }


  void Dump(const char* prefix="") const;

private:
};
*/


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
    deps_missing: bool,
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

    pub fn weight(&self) -> isize { 
        1 
    }

    pub fn outputs_ready(&self) -> bool { 
        self.outputs_ready
    }
    
    pub fn explicit_deps_range(&self) -> Range<usize> {
        0..(self.inputs.len() - self.implicit_deps - self.order_only_deps)
    }

    pub fn implicit_deps_range(&self) -> Range<usize> {
        (self.inputs.len() - self.implicit_deps - self.order_only_deps)..
        (self.inputs.len() - self.order_only_deps)
    }

    pub fn order_only_deps_range(&self) -> Range<usize> {
        (self.inputs.len() - self.order_only_deps)..(self.inputs.len())
    }

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
    pub fn all_inputs_ready(&self) -> bool {
        unimplemented!();
    }

    pub fn dump(&self) {
        unimplemented!();
    }
}


/*

struct Edge {


  Edge() : rule_(NULL), pool_(NULL), env_(NULL), mark_(VisitNone),
           outputs_ready_(false), deps_missing_(false),
           implicit_deps_(0), order_only_deps_(0), implicit_outs_(0) {}




  void Dump(const char* prefix="") const;



  bool outputs_ready_;
  bool deps_missing_;


  // There are three types of inputs.
  // 1) explicit deps, which show up as $in on the command line;
  // 2) implicit deps, which the target depends on implicitly (e.g. C headers),
  //                   and changes in them cause the target to rebuild;
  // 3) order-only deps, which are needed before the target builds but which
  //                     don't cause the target to rebuild.
  // These are stored in inputs_ in that order, and we keep counts of
  // #2 and #3 when we need to access the various subsets.
  int implicit_deps_;
  int order_only_deps_;
  bool is_implicit(size_t index) {
    return index >= inputs_.size() - order_only_deps_ - implicit_deps_ &&
        !is_order_only(index);
  }
  bool is_order_only(size_t index) {
    return index >= inputs_.size() - order_only_deps_;
  }

  // There are two types of outputs.
  // 1) explicit outs, which show up as $out on the command line;
  // 2) implicit outs, which the target generates but are not part of $out.
  // These are stored in outputs_ in that order, and we keep a count of
  // #2 to use when we need to access the various subsets.
  int implicit_outs_;
  bool is_implicit_out(size_t index) const {
    return index >= outputs_.size() - implicit_outs_;
  }

};


/// ImplicitDepLoader loads implicit dependencies, as referenced via the
/// "depfile" attribute in build files.
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
  /// Load implicit dependencies for \a edge from a depfile attribute.
  /// @return false on error (without filling \a err if info is just missing).
  bool LoadDepFile(Edge* edge, const string& path, string* err);

  /// Load implicit dependencies for \a edge from the DepsLog.
  /// @return false on error (without filling \a err if info is just missing).
  bool LoadDepsFromLog(Edge* edge, string* err);

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
pub struct DependencyScan {

}

impl DependencyScan {
    pub fn new(state: &State, build_log: &BuildLog, deps_log: &DepsLog, disk_interface: &DiskInterface) -> Self {
        DependencyScan {

        }
    }

    /// Update the |dirty_| state of the given node by inspecting its input edge.
    /// Examine inputs, outputs, and command lines to judge whether an edge
    /// needs to be re-run, and update outputs_ready_ and each outputs' |dirty_|
    /// state accordingly.
    /// Returns false on failure.
    pub fn recompute_dirty(&self, node: NodeIndex) -> Result<(), String> {
        let mut stack = Vec::new();
        return self.recompute_dirty_inner(node, &mut stack);
    }

    fn recompute_dirty_inner(&self, node: NodeIndex, stack: &mut Vec<NodeIndex>) -> Result<(), String> {
        return Ok(());
        unimplemented!()
    }


}

/*

struct DependencyScan {
  DependencyScan(State* state, BuildLog* build_log, DepsLog* deps_log,
                 DiskInterface* disk_interface)
      : build_log_(build_log),
        disk_interface_(disk_interface),
        dep_loader_(state, deps_log, disk_interface) {}

  /// Update the |dirty_| state of the given node by inspecting its input edge.
  /// Examine inputs, outputs, and command lines to judge whether an edge
  /// needs to be re-run, and update outputs_ready_ and each outputs' |dirty_|
  /// state accordingly.
  /// Returns false on failure.
  bool RecomputeDirty(Node* node, string* err);

  /// Recompute whether any output of the edge is dirty, if so sets |*dirty|.
  /// Returns false on failure.
  bool RecomputeOutputsDirty(Edge* edge, Node* most_recent_input,
                             bool* dirty, string* err);

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

  /// Recompute whether a given single output should be marked dirty.
  /// Returns true if so.
  bool RecomputeOutputDirty(Edge* edge, Node* most_recent_input,
                            const string& command, Node* output);

  BuildLog* build_log_;
  DiskInterface* disk_interface_;
  ImplicitDepLoader dep_loader_;
};

#endif  // NINJA_GRAPH_H_

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

#include <assert.h>
#include <stdio.h>

#include "build_log.h"
#include "debug_flags.h"
#include "depfile_parser.h"
#include "deps_log.h"
#include "disk_interface.h"
#include "manifest_parser.h"
#include "metrics.h"
#include "state.h"
#include "util.h"

bool Node::Stat(DiskInterface* disk_interface, string* err) {
  return (mtime_ = disk_interface->Stat(path_, err)) != -1;
}

bool DependencyScan::RecomputeDirty(Node* node, string* err) {
  vector<Node*> stack;
  return RecomputeDirty(node, &stack, err);
}

bool DependencyScan::RecomputeDirty(Node* node, vector<Node*>* stack,
                                    string* err) {
  Edge* edge = node->in_edge();
  if (!edge) {
    // If we already visited this leaf node then we are done.
    if (node->status_known())
      return true;
    // This node has no in-edge; it is dirty if it is missing.
    if (!node->StatIfNecessary(disk_interface_, err))
      return false;
    if (!node->exists())
      EXPLAIN("%s has no in-edge and is missing", node->path().c_str());
    node->set_dirty(!node->exists());
    return true;
  }

  // If we already finished this edge then we are done.
  if (edge->mark_ == Edge::VisitDone)
    return true;

  // If we encountered this edge earlier in the call stack we have a cycle.
  if (!VerifyDAG(node, stack, err))
    return false;

  // Mark the edge temporarily while in the call stack.
  edge->mark_ = Edge::VisitInStack;
  stack->push_back(node);

  bool dirty = false;
  edge->outputs_ready_ = true;
  edge->deps_missing_ = false;

  // Load output mtimes so we can compare them to the most recent input below.
  for (vector<Node*>::iterator o = edge->outputs_.begin();
       o != edge->outputs_.end(); ++o) {
    if (!(*o)->StatIfNecessary(disk_interface_, err))
      return false;
  }

  if (!dep_loader_.LoadDeps(edge, err)) {
    if (!err->empty())
      return false;
    // Failed to load dependency info: rebuild to regenerate it.
    // LoadDeps() did EXPLAIN() already, no need to do it here.
    dirty = edge->deps_missing_ = true;
  }

  // Visit all inputs; we're dirty if any of the inputs are dirty.
  Node* most_recent_input = NULL;
  for (vector<Node*>::iterator i = edge->inputs_.begin();
       i != edge->inputs_.end(); ++i) {
    // Visit this input.
    if (!RecomputeDirty(*i, stack, err))
      return false;

    // If an input is not ready, neither are our outputs.
    if (Edge* in_edge = (*i)->in_edge()) {
      if (!in_edge->outputs_ready_)
        edge->outputs_ready_ = false;
    }

    if (!edge->is_order_only(i - edge->inputs_.begin())) {
      // If a regular input is dirty (or missing), we're dirty.
      // Otherwise consider mtime.
      if ((*i)->dirty()) {
        EXPLAIN("%s is dirty", (*i)->path().c_str());
        dirty = true;
      } else {
        if (!most_recent_input || (*i)->mtime() > most_recent_input->mtime()) {
          most_recent_input = *i;
        }
      }
    }
  }

  // We may also be dirty due to output state: missing outputs, out of
  // date outputs, etc.  Visit all outputs and determine whether they're dirty.
  if (!dirty)
    if (!RecomputeOutputsDirty(edge, most_recent_input, &dirty, err))
      return false;

  // Finally, visit each output and update their dirty state if necessary.
  for (vector<Node*>::iterator o = edge->outputs_.begin();
       o != edge->outputs_.end(); ++o) {
    if (dirty)
      (*o)->MarkDirty();
  }

  // If an edge is dirty, its outputs are normally not ready.  (It's
  // possible to be clean but still not be ready in the presence of
  // order-only inputs.)
  // But phony edges with no inputs have nothing to do, so are always
  // ready.
  if (dirty && !(edge->is_phony() && edge->inputs_.empty()))
    edge->outputs_ready_ = false;

  // Mark the edge as finished during this walk now that it will no longer
  // be in the call stack.
  edge->mark_ = Edge::VisitDone;
  assert(stack->back() == node);
  stack->pop_back();

  return true;
}

bool DependencyScan::VerifyDAG(Node* node, vector<Node*>* stack, string* err) {
  Edge* edge = node->in_edge();
  assert(edge != NULL);

  // If we have no temporary mark on the edge then we do not yet have a cycle.
  if (edge->mark_ != Edge::VisitInStack)
    return true;

  // We have this edge earlier in the call stack.  Find it.
  vector<Node*>::iterator start = stack->begin();
  while (start != stack->end() && (*start)->in_edge() != edge)
    ++start;
  assert(start != stack->end());

  // Make the cycle clear by reporting its start as the node at its end
  // instead of some other output of the starting edge.  For example,
  // running 'ninja b' on
  //   build a b: cat c
  //   build c: cat a
  // should report a -> c -> a instead of b -> c -> a.
  *start = node;

  // Construct the error message rejecting the cycle.
  *err = "dependency cycle: ";
  for (vector<Node*>::const_iterator i = start; i != stack->end(); ++i) {
    err->append((*i)->path());
    err->append(" -> ");
  }
  err->append((*start)->path());

  if ((start + 1) == stack->end() && edge->maybe_phonycycle_diagnostic()) {
    // The manifest parser would have filtered out the self-referencing
    // input if it were not configured to allow the error.
    err->append(" [-w phonycycle=err]");
  }

  return false;
}

bool DependencyScan::RecomputeOutputsDirty(Edge* edge, Node* most_recent_input,
                                           bool* outputs_dirty, string* err) {
  string command = edge->EvaluateCommand(/*incl_rsp_file=*/true);
  for (vector<Node*>::iterator o = edge->outputs_.begin();
       o != edge->outputs_.end(); ++o) {
    if (RecomputeOutputDirty(edge, most_recent_input, command, *o)) {
      *outputs_dirty = true;
      return true;
    }
  }
  return true;
}

bool DependencyScan::RecomputeOutputDirty(Edge* edge,
                                          Node* most_recent_input,
                                          const string& command,
                                          Node* output) {
  if (edge->is_phony()) {
    // Phony edges don't write any output.  Outputs are only dirty if
    // there are no inputs and we're missing the output.
    if (edge->inputs_.empty() && !output->exists()) {
      EXPLAIN("output %s of phony edge with no inputs doesn't exist",
              output->path().c_str());
      return true;
    }
    return false;
  }

  BuildLog::LogEntry* entry = 0;

  // Dirty if we're missing the output.
  if (!output->exists()) {
    EXPLAIN("output %s doesn't exist", output->path().c_str());
    return true;
  }

  // Dirty if the output is older than the input.
  if (most_recent_input && output->mtime() < most_recent_input->mtime()) {
    TimeStamp output_mtime = output->mtime();

    // If this is a restat rule, we may have cleaned the output with a restat
    // rule in a previous run and stored the most recent input mtime in the
    // build log.  Use that mtime instead, so that the file will only be
    // considered dirty if an input was modified since the previous run.
    bool used_restat = false;
    if (edge->GetBindingBool("restat") && build_log() &&
        (entry = build_log()->LookupByOutput(output->path()))) {
      output_mtime = entry->mtime;
      used_restat = true;
    }

    if (output_mtime < most_recent_input->mtime()) {
      EXPLAIN("%soutput %s older than most recent input %s "
              "(%d vs %d)",
              used_restat ? "restat of " : "", output->path().c_str(),
              most_recent_input->path().c_str(),
              output_mtime, most_recent_input->mtime());
      return true;
    }
  }

  if (build_log()) {
    bool generator = edge->GetBindingBool("generator");
    if (entry || (entry = build_log()->LookupByOutput(output->path()))) {
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
    }
    if (!entry && !generator) {
      EXPLAIN("command line not found in log for %s", output->path().c_str());
      return true;
    }
  }

  return false;
}

bool Edge::AllInputsReady() const {
  for (vector<Node*>::const_iterator i = inputs_.begin();
       i != inputs_.end(); ++i) {
    if ((*i)->in_edge() && !(*i)->in_edge()->outputs_ready())
      return false;
  }
  return true;
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