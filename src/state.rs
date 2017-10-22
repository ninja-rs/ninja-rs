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
use super::graph::{Edge, Node};

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

/// Global state (file status) for a single run.
pub struct State<'a> {
    /// Mapping of path -> Node.
    paths: HashMap<String, &'a Node<'a>>,
    
    /// All the pools used in the graph.
    pools: HashMap<Vec<u8>, Pool>,

    /// All the edges of the graph.
    edges: Vec<&'a Edge>,

    pub bindings: Rc<RefCell<BindingEnv<'a>>>,
    defaults: Vec<&'a Node<'a>>,
}

impl<'a> State<'a> {
    pub fn new() -> Self {
        State {
            paths: HashMap::new(),
            pools: HashMap::new(),
            edges: Vec::new(),
            bindings: Rc::new(RefCell::new(BindingEnv::new())),
            defaults: Vec::new()
        }
    }

    pub fn add_pool(&mut self, pool: Pool) {
        assert!(self.lookup_pool(pool.name()).is_none());
        self.pools.insert(pool.name().to_owned(), pool);
    }

    pub fn lookup_pool(&self, pool_name: &[u8]) -> Option<&Pool> {
        self.pools.get(pool_name)
    }

    pub fn clone_bindings(&self) -> Rc<RefCell<BindingEnv<'a>>> {
        self.bindings.clone()
    }
}

#[cfg(test)]
impl<'a> State<'a> {
    pub fn verify_graph(&self) {
        for e in self.edges.iter() {
            /*
            // All edges need at least one output.
            EXPECT_FALSE((*e)->outputs_.empty());
            // Check that the edge's inputs have the edge as out-edge.
            for (vector<Node*>::const_iterator in_node = (*e)->inputs_.begin();
                in_node != (*e)->inputs_.end(); ++in_node) {
            const vector<Edge*>& out_edges = (*in_node)->out_edges();
            EXPECT_NE(find(out_edges.begin(), out_edges.end(), *e),
                        out_edges.end());
            }
            // Check that the edge's outputs have the edge as in-edge.
            for (vector<Node*>::const_iterator out_node = (*e)->outputs_.begin();
                out_node != (*e)->outputs_.end(); ++out_node) {
            EXPECT_EQ((*out_node)->in_edge(), *e);
            }
            */
            unimplemented!()
        }

        // The union of all in- and out-edges of each nodes should be exactly edges_.
        let mut node_edge_set = HashSet::new();
        for p in self.paths.iter() {
            let n = p.1;
            if let Some(in_edge) = n.in_edge() {
                node_edge_set.insert(in_edge as * const _);
            }
            node_edge_set.extend(n.out_edges().iter().map(|&r| r as * const _));
        }
        let edge_set = self.edges.iter().map(|&r| r as * const _).collect::<HashSet<_>>();
        assert_eq!(node_edge_set, edge_set);
    }
}

/*
void VerifyGraph(const State& state) {
  for (vector<Edge*>::const_iterator e = state.edges_.begin();
       e != state.edges_.end(); ++e) {
    
  }

  // The union of all in- and out-edges of each nodes should be exactly edges_.
  set<const Edge*> node_edge_set;
  for (State::Paths::const_iterator p = state.paths_.begin();
       p != state.paths_.end(); ++p) {
    const Node* n = p->second;
    if (n->in_edge())
      node_edge_set.insert(n->in_edge());
    node_edge_set.insert(n->out_edges().begin(), n->out_edges().end());
  }
  set<const Edge*> edge_set(state.edges_.begin(), state.edges_.end());
  EXPECT_EQ(node_edge_set, edge_set);
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

Pool State::kDefaultPool("", 0);
Pool State::kConsolePool("console", 1);
const Rule State::kPhonyRule("phony");

State::State() {
  bindings_.AddRule(&kPhonyRule);
  AddPool(&kDefaultPool);
  AddPool(&kConsolePool);
}

void State::AddPool(Pool* pool) {
  assert(LookupPool(pool->name()) == NULL);
  pools_[pool->name()] = pool;
}

Pool* State::LookupPool(const string& pool_name) {
  map<string, Pool*>::iterator i = pools_.find(pool_name);
  if (i == pools_.end())
    return NULL;
  return i->second;
}

Edge* State::AddEdge(const Rule* rule) {
  Edge* edge = new Edge();
  edge->rule_ = rule;
  edge->pool_ = &State::kDefaultPool;
  edge->env_ = &bindings_;
  edges_.push_back(edge);
  return edge;
}

Node* State::GetNode(StringPiece path, uint64_t slash_bits) {
  Node* node = LookupNode(path);
  if (node)
    return node;
  node = new Node(path.AsString(), slash_bits);
  paths_[node->path()] = node;
  return node;
}

Node* State::LookupNode(StringPiece path) const {
  METRIC_RECORD("lookup node");
  Paths::const_iterator i = paths_.find(path);
  if (i != paths_.end())
    return i->second;
  return NULL;
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

bool State::AddDefault(StringPiece path, string* err) {
  Node* node = LookupNode(path);
  if (!node) {
    *err = "unknown target '" + path.AsString() + "'";
    return false;
  }
  defaults_.push_back(node);
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