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
use std::cell::RefCell;
use std::collections::{HashMap, HashSet, BTreeSet};
use std::cmp::{PartialOrd, Ordering};

use super::eval_env::{BindingEnv, Rule};
use super::graph::{Edge, Node, EdgeIndex, NodeIndex};

struct DelayedEdge<'a>(pub &'a Edge);

impl<'a> PartialEq for DelayedEdge<'a> {
    fn eq(&self, other: &Self) -> bool {
        self.0 as * const _ as usize == 
            other.0 as * const _ as usize
    }
}

impl<'a> PartialOrd for DelayedEdge<'a> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl<'a> Eq for DelayedEdge<'a> {}
impl<'a> Ord for DelayedEdge<'a> {
    fn cmp(&self, other: &Self) -> Ordering {
        // if (!a) return b;
        // if (!b) return false;
        let weight1 = self.0.weight();
        let weight2 = other.0.weight();
        if weight1 != weight2 {
            weight1.cmp(&weight2)
        } else {
            (self.0 as * const _ as usize)
                .cmp(&(other.0 as * const _ as usize))
        }
    }
}

/// A pool for delayed edges.
/// Pools are scoped to a State. Edges within a State will share Pools. A Pool
/// will keep a count of the total 'weight' of the currently scheduled edges. If
/// a Plan attempts to schedule an Edge which would cause the total weight to
/// exceed the depth of the Pool, the Pool will enque the Edge instead of
/// allowing the Plan to schedule it. The Pool will relinquish queued Edges when
/// the total scheduled weight diminishes enough (i.e. when a scheduled edge
/// completes).
pub struct Pool {
    name: Vec<u8>,
    /// |current_use_| is the total of the weights of the edges which are
    /// currently scheduled in the Plan (i.e. the edges in Plan::ready_).
    current_use: isize,
    depth: isize,
    
    delayed: BTreeSet<DelayedEdge<'static>>,
}

impl Pool {
    pub fn new(name: Vec<u8>, depth: isize) -> Self {
        Pool {
            name,
            current_use: 0,
            depth,
            delayed: BTreeSet::new(),
        }
    }

    pub fn is_valid(&self) -> bool {
        // A depth of 0 is infinite
        self.depth >= 0
    }

    pub fn depth(&self) -> isize {
        self.depth
    }

    pub fn name(&self) -> &[u8] {
        &self.name
    }

    pub fn current_use(&self) -> isize {
        self.current_use
    }

}

/*

struct Pool {

  /// true if the Pool might delay this edge
  bool ShouldDelayEdge() const { return depth_ != 0; }

  /// informs this Pool that the given edge is committed to be run.
  /// Pool will count this edge as using resources from this pool.
  void EdgeScheduled(const Edge& edge);

  /// informs this Pool that the given edge is no longer runnable, and should
  /// relinquish its resources back to the pool
  void EdgeFinished(const Edge& edge);

  /// adds the given edge to this Pool to be delayed.
  void DelayEdge(Edge* edge);

  /// Pool will add zero or more edges to the ready_queue
  void RetrieveReadyEdges(set<Edge*>* ready_queue);

  /// Dump the Pool and its edges (useful for debugging).
  void Dump() const;

 private:
  string name_;

  /// |current_use_| is the total of the weights of the edges which are
  /// currently scheduled in the Plan (i.e. the edges in Plan::ready_).
  int current_use_;
  int depth_;

  static bool WeightedEdgeCmp(const Edge* a, const Edge* b);

  typedef set<Edge*,bool(*)(const Edge*, const Edge*)> DelayedEdges;
  DelayedEdges delayed_;
};

/// Global state (file status) for a single run.
struct State {
  static Pool kDefaultPool;
  static Pool kConsolePool;
  static const Rule kPhonyRule;

  State();

  void AddPool(Pool* pool);
  Pool* LookupPool(const string& pool_name);

  Edge* AddEdge(const Rule* rule);

  Node* GetNode(StringPiece path, uint64_t slash_bits);
  Node* LookupNode(StringPiece path) const;
  Node* SpellcheckNode(const string& path);

  void AddIn(Edge* edge, StringPiece path, uint64_t slash_bits);
  bool AddOut(Edge* edge, StringPiece path, uint64_t slash_bits);
  bool AddDefault(StringPiece path, string* error);

  /// Reset state.  Keeps all nodes and edges, but restores them to the
  /// state where we haven't yet examined the disk for dirty state.
  void Reset();

  /// Dump the nodes and Pools (useful for debugging).
  void Dump();

  /// @return the root node(s) of the graph. (Root nodes have no output edges).
  /// @param error where to write the error message if somethings went wrong.
  vector<Node*> RootNodes(string* error) const;
  vector<Node*> DefaultNodes(string* error) const;

  /// Mapping of path -> Node.
  typedef ExternalStringHashMap<Node*>::Type Paths;
  Paths paths_;

  /// All the pools used in the graph.
  map<string, Pool*> pools_;

  /// All the edges of the graph.
  vector<Edge*> edges_;

  BindingEnv bindings_;
  vector<Node*> defaults_;
};

#endif  // NINJA_STATE_H_
*/

thread_local!{ 
    pub static DEFAULT_POOL: Rc<RefCell<Pool>> = Rc::new(RefCell::new(Pool::new(b"".as_ref().to_owned(), 0)));
    pub static CONSOLE_POOL: Rc<RefCell<Pool>> = Rc::new(RefCell::new(Pool::new(b"console".as_ref().to_owned(), 1)));

    pub static PHONY_RULE: Rc<Rule> = Rc::new(Rule::new(b"phony".as_ref().to_owned()));
}

pub struct NodeState {
    /// All the nodes of the graph.
    nodes: Vec<Node>,

    /// Mapping of path -> Node.
    paths: HashMap<Vec<u8>, NodeIndex>,
}

impl NodeState {
    pub fn new() -> Self {
        NodeState {
            nodes: Vec::new(),
            paths: HashMap::new(),
        }
    }

    pub fn prepare_node(&mut self, path: &[u8], slash_bits: u64) -> NodeIndex {
        let node_idx = self.lookup_node(path);
        if node_idx.is_some() {
            return node_idx.unwrap();
        }

        let node = Node::new(path, slash_bits);
        let node_idx = NodeIndex(self.nodes.len());
        self.nodes.push(node);
        self.paths.insert(path.to_owned(), node_idx);
        node_idx
    }

    pub fn lookup_node(&self, path: &[u8]) -> Option<NodeIndex> {
        metric_record!("lookup node");
        self.paths.get(path).cloned()
    }

    pub fn get_node(&self, idx: NodeIndex) -> &Node {
        self.nodes.get(idx.0).expect("index out of range")
    }

    pub fn get_node_mut(&mut self, idx: NodeIndex) -> &mut Node {
        self.nodes.get_mut(idx.0).expect("index out of range")
    }
}

pub struct EdgeState {
    /// All the edges of the graph.
    edges: Vec<Edge>,
}

impl EdgeState {
    pub fn new() -> Self {
        EdgeState {
            edges: Vec::new()
        }
    }

    pub fn get_edge(&self, idx: EdgeIndex) -> &Edge {
        self.edges.get(idx.0).expect("index out of range")
    }

    pub fn get_edge_mut(&mut self, idx: EdgeIndex) -> &mut Edge {
        self.edges.get_mut(idx.0).expect("index out of range")
    }

    pub fn make_edge(&mut self, rule: Rc<Rule>, bindings: Rc<RefCell<BindingEnv>>) -> EdgeIndex {
        let edge = Edge::new(rule, DEFAULT_POOL.with(Clone::clone), bindings);
        let idx = EdgeIndex(self.edges.len());
        self.edges.push(edge);
        idx
    }

    pub fn revoke_latest_edge(&mut self, idx: EdgeIndex) {
        if self.edges.len() != idx.0 + 1 {
            panic!("trying to revoke an edge that is not the latest one.")
        }
        self.edges.pop();
    }
}

pub struct PoolState {
    /// All the pools used in the graph.
    pools: HashMap<Vec<u8>, Rc<RefCell<Pool>>>,
}

impl PoolState {
    pub fn new() -> Self {
        PoolState {
            pools: HashMap::new()
        }
    }

    pub fn add_pool(&mut self, pool: Rc<RefCell<Pool>>) {
        assert!(self.lookup_pool(pool.borrow().name()).is_none());
        let name = pool.borrow().name().to_owned();
        self.pools.insert(name, pool);
    }

    pub fn lookup_pool(&self, pool_name: &[u8]) -> Option<&Rc<RefCell<Pool>>> {
        self.pools.get(pool_name)
    }
}

/// Global state (file status) for a single run.
pub struct State {
    pub node_state: NodeState,
    pub edge_state: EdgeState,
    pub pool_state: PoolState,

    pub bindings: Rc<RefCell<BindingEnv>>,
    defaults: Vec<NodeIndex>,
}

impl State {
    pub fn new() -> Self {
        let mut state = State {
            node_state: NodeState::new(),
            edge_state: EdgeState::new(),
            pool_state: PoolState::new(),
            bindings: Rc::new(RefCell::new(BindingEnv::new())),
            defaults: Vec::new()
        };

        state.bindings.borrow_mut().add_rule(PHONY_RULE.with(Rc::clone));
        state.pool_state.add_pool(DEFAULT_POOL.with(Rc::clone));
        state.pool_state.add_pool(CONSOLE_POOL.with(Rc::clone));
        state
    }

    pub fn connect_edge_to_in_node(edge: &mut Edge, edge_idx: EdgeIndex, node: &mut Node, node_idx: NodeIndex) {
        edge.inputs.push(node_idx);
        node.add_out_edge(edge_idx);
    }
    
    pub fn connect_edge_to_out_node(edge: &mut Edge, edge_idx: EdgeIndex, node: &mut Node, node_idx: NodeIndex) -> bool {
        if node.in_edge().is_some() {
            return false;
        }
        edge.outputs.push(node_idx);
        node.set_in_edge(Some(edge_idx));
        return true;
    }

    pub fn get_env(&self) -> Rc<RefCell<BindingEnv>> {
        self.bindings.clone()
    }

    pub fn add_default(&mut self, path: &[u8]) -> Result<(), String> {
        let node = self.node_state.lookup_node(path);
        if let Some(node_idx) = node {
            self.defaults.push(node_idx);
            Ok(())
        } else {
            Err(format!("unknown target '{}'", String::from_utf8_lossy(path)))
        }
    }
}

#[cfg(test)]
impl State {
    pub fn verify_graph(&self) {
        for (i, e) in self.edge_state.edges.iter().enumerate() {
            // All edges need at least one output.
            assert_eq!(false, e.outputs.is_empty());

            // Check that the edge's inputs have the edge as out-edge.
            for in_node_idx in e.inputs.iter() {
                let in_node = self.node_state.get_node(*in_node_idx);
                assert!(in_node.out_edges().contains(&EdgeIndex(i)));
            }

            // Check that the edge's outputs have the edge as in-edge.
            for out_node_idx in e.outputs.iter() {
                let out_node = self.node_state.get_node(*out_node_idx);
                assert_eq!(out_node.in_edge(), Some(EdgeIndex(i)));
            }
        }

        // The union of all in- and out-edges of each nodes should be exactly edges_.
        assert_eq!(self.node_state.paths.len(), self.node_state.nodes.len());
        let mut node_edge_set = HashSet::new();
        for n in self.node_state.nodes.iter() {
            if let Some(in_edge) = n.in_edge() {
                node_edge_set.insert(self.edge_state.get_edge(in_edge) as * const _);
            }
            node_edge_set.extend(n.out_edges().iter().map(|&r| self.edge_state.get_edge(r) as * const _));
        }
        let edge_set = self.edge_state.edges.iter().map(|r| r as * const _).collect::<HashSet<_>>();
        assert_eq!(node_edge_set, edge_set);
    }
}


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

#include "state.h"

#include <assert.h>
#include <stdio.h>

#include "edit_distance.h"
#include "graph.h"
#include "metrics.h"
#include "util.h"


void Pool::EdgeScheduled(const Edge& edge) {
  if (depth_ != 0)
    current_use_ += edge.weight();
}

void Pool::EdgeFinished(const Edge& edge) {
  if (depth_ != 0)
    current_use_ -= edge.weight();
}

void Pool::DelayEdge(Edge* edge) {
  assert(depth_ != 0);
  delayed_.insert(edge);
}

void Pool::RetrieveReadyEdges(set<Edge*>* ready_queue) {
  DelayedEdges::iterator it = delayed_.begin();
  while (it != delayed_.end()) {
    Edge* edge = *it;
    if (current_use_ + edge->weight() > depth_)
      break;
    ready_queue->insert(edge);
    EdgeScheduled(*edge);
    ++it;
  }
  delayed_.erase(delayed_.begin(), it);
}

void Pool::Dump() const {
  printf("%s (%d/%d) ->\n", name_.c_str(), current_use_, depth_);
  for (DelayedEdges::const_iterator it = delayed_.begin();
       it != delayed_.end(); ++it)
  {
    printf("\t");
    (*it)->Dump();
  }
}

// static
bool Pool::WeightedEdgeCmp(const Edge* a, const Edge* b) {
  if (!a) return b;
  if (!b) return false;
  int weight_diff = a->weight() - b->weight();
  return ((weight_diff < 0) || (weight_diff == 0 && a < b));
}

Edge* State::AddEdge(const Rule* rule) {
  Edge* edge = new Edge();
  edge->rule_ = rule;
  edge->pool_ = &State::kDefaultPool;
  edge->env_ = &bindings_;
  edges_.push_back(edge);
  return edge;
}

Node* State::SpellcheckNode(const string& path) {
  const bool kAllowReplacements = true;
  const int kMaxValidEditDistance = 3;

  int min_distance = kMaxValidEditDistance + 1;
  Node* result = NULL;
  for (Paths::iterator i = paths_.begin(); i != paths_.end(); ++i) {
    int distance = EditDistance(
        i->first, path, kAllowReplacements, kMaxValidEditDistance);
    if (distance < min_distance && i->second) {
      min_distance = distance;
      result = i->second;
    }
  }
  return result;
}

void State::AddIn(Edge* edge, StringPiece path, uint64_t slash_bits) {
  Node* node = GetNode(path, slash_bits);
  edge->inputs_.push_back(node);
  node->AddOutEdge(edge);
}

bool State::AddOut(Edge* edge, StringPiece path, uint64_t slash_bits) {
  Node* node = GetNode(path, slash_bits);
  if (node->in_edge())
    return false;
  edge->outputs_.push_back(node);
  node->set_in_edge(edge);
  return true;
}

vector<Node*> State::RootNodes(string* err) const {
  vector<Node*> root_nodes;
  // Search for nodes with no output.
  for (vector<Edge*>::const_iterator e = edges_.begin();
       e != edges_.end(); ++e) {
    for (vector<Node*>::const_iterator out = (*e)->outputs_.begin();
         out != (*e)->outputs_.end(); ++out) {
      if ((*out)->out_edges().empty())
        root_nodes.push_back(*out);
    }
  }

  if (!edges_.empty() && root_nodes.empty())
    *err = "could not determine root nodes of build graph";

  return root_nodes;
}

vector<Node*> State::DefaultNodes(string* err) const {
  return defaults_.empty() ? RootNodes(err) : defaults_;
}

void State::Reset() {
  for (Paths::iterator i = paths_.begin(); i != paths_.end(); ++i)
    i->second->ResetState();
  for (vector<Edge*>::iterator e = edges_.begin(); e != edges_.end(); ++e) {
    (*e)->outputs_ready_ = false;
    (*e)->mark_ = Edge::VisitNone;
  }
}

void State::Dump() {
  for (Paths::iterator i = paths_.begin(); i != paths_.end(); ++i) {
    Node* node = i->second;
    printf("%s %s [id:%d]\n",
           node->path().c_str(),
           node->status_known() ? (node->dirty() ? "dirty" : "clean")
                                : "unknown",
           node->id());
  }
  if (!pools_.empty()) {
    printf("resource_pools:\n");
    for (map<string, Pool*>::const_iterator it = pools_.begin();
         it != pools_.end(); ++it)
    {
      if (!it->second->name().empty()) {
        it->second->Dump();
      }
    }
  }
}

*/