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

/// An interface for a scope for variable (e.g. "$foo") lookups.
pub trait Env {
    fn lookup_variable(&self, var: &[u8]) -> Vec<u8>;
}

enum TokenType {
    Raw,
    Special
}

type TokenList = Vec<(Vec<u8>, TokenType)>;

/// A tokenized string that contains variable references.
/// Can be evaluated relative to an Env.
pub struct EvalString {
    parsed: TokenList,
}

impl EvalString {
    pub fn new() -> Self {
        EvalString {
        parsed: Vec::new(),
        }
    }
    pub fn evaluate(&self, env: &Env) -> Vec<u8> {
        unimplemented!()
    }

    pub fn clear(&mut self) {
        self.parsed.clear()
    }

    pub fn is_empty(&self) -> bool {
        self.parsed.is_empty()
    }

    pub fn add_text(&mut self, text: &[u8]) {
        unimplemented!()
    }

    pub fn add_special(&mut self, text: &[u8]) {
        unimplemented!()
    }

    /// Construct a human-readable representation of the parsed state,
    /// for use in tests.
    pub(crate) fn serialize(&self) -> Vec<u8> {
        unimplemented!()
    }
}


/*

/// An invokable build command and associated metadata (description, etc.).
struct Rule {
  explicit Rule(const string& name) : name_(name) {}

  const string& name() const { return name_; }

  void AddBinding(const string& key, const EvalString& val);

  static bool IsReservedBinding(const string& var);

  const EvalString* GetBinding(const string& key) const;

 private:
  // Allow the parsers to reach into this object and fill out its fields.
  friend struct ManifestParser;

  string name_;
  typedef map<string, EvalString> Bindings;
  Bindings bindings_;
};

/// An Env which contains a mapping of variables to values
/// as well as a pointer to a parent scope.
struct BindingEnv : public Env {
  BindingEnv() : parent_(NULL) {}
  explicit BindingEnv(BindingEnv* parent) : parent_(parent) {}

  virtual ~BindingEnv() {}
  virtual string LookupVariable(const string& var);

  void AddRule(const Rule* rule);
  const Rule* LookupRule(const string& rule_name);
  const Rule* LookupRuleCurrentScope(const string& rule_name);
  const map<string, const Rule*>& GetRules() const;

  void AddBinding(const string& key, const string& val);

  /// This is tricky.  Edges want lookup scope to go in this order:
  /// 1) value set on edge itself (edge_->env_)
  /// 2) value set on rule, with expansion in the edge's scope
  /// 3) value set on enclosing scope of edge (edge_->env_->parent_)
  /// This function takes as parameters the necessary info to do (2).
  string LookupWithFallback(const string& var, const EvalString* eval,
                            Env* env);

private:
  map<string, string> bindings_;
  map<string, const Rule*> rules_;
  BindingEnv* parent_;
};

#endif  // NINJA_EVAL_ENV_H_

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

#include <assert.h>

#include "eval_env.h"

string BindingEnv::LookupVariable(const string& var) {
  map<string, string>::iterator i = bindings_.find(var);
  if (i != bindings_.end())
    return i->second;
  if (parent_)
    return parent_->LookupVariable(var);
  return "";
}

void BindingEnv::AddBinding(const string& key, const string& val) {
  bindings_[key] = val;
}

void BindingEnv::AddRule(const Rule* rule) {
  assert(LookupRuleCurrentScope(rule->name()) == NULL);
  rules_[rule->name()] = rule;
}

const Rule* BindingEnv::LookupRuleCurrentScope(const string& rule_name) {
  map<string, const Rule*>::iterator i = rules_.find(rule_name);
  if (i == rules_.end())
    return NULL;
  return i->second;
}

const Rule* BindingEnv::LookupRule(const string& rule_name) {
  map<string, const Rule*>::iterator i = rules_.find(rule_name);
  if (i != rules_.end())
    return i->second;
  if (parent_)
    return parent_->LookupRule(rule_name);
  return NULL;
}

void Rule::AddBinding(const string& key, const EvalString& val) {
  bindings_[key] = val;
}

const EvalString* Rule::GetBinding(const string& key) const {
  Bindings::const_iterator i = bindings_.find(key);
  if (i == bindings_.end())
    return NULL;
  return &i->second;
}

// static
bool Rule::IsReservedBinding(const string& var) {
  return var == "command" ||
      var == "depfile" ||
      var == "description" ||
      var == "deps" ||
      var == "generator" ||
      var == "pool" ||
      var == "restat" ||
      var == "rspfile" ||
      var == "rspfile_content" ||
      var == "msvc_deps_prefix";
}

const map<string, const Rule*>& BindingEnv::GetRules() const {
  return rules_;
}

string BindingEnv::LookupWithFallback(const string& var,
                                      const EvalString* eval,
                                      Env* env) {
  map<string, string>::iterator i = bindings_.find(var);
  if (i != bindings_.end())
    return i->second;

  if (eval)
    return eval->Evaluate(env);

  if (parent_)
    return parent_->LookupVariable(var);

  return "";
}

string EvalString::Evaluate(Env* env) const {
  string result;
  for (TokenList::const_iterator i = parsed_.begin(); i != parsed_.end(); ++i) {
    if (i->second == RAW)
      result.append(i->first);
    else
      result.append(env->LookupVariable(i->first));
  }
  return result;
}

void EvalString::AddText(StringPiece text) {
  // Add it to the end of an existing RAW token if possible.
  if (!parsed_.empty() && parsed_.back().second == RAW) {
    parsed_.back().first.append(text.str_, text.len_);
  } else {
    parsed_.push_back(make_pair(text.AsString(), RAW));
  }
}
void EvalString::AddSpecial(StringPiece text) {
  parsed_.push_back(make_pair(text.AsString(), SPECIAL));
}

string EvalString::Serialize() const {
  string result;
  for (TokenList::const_iterator i = parsed_.begin();
       i != parsed_.end(); ++i) {
    result.append("[");
    if (i->second == SPECIAL)
      result.append("$");
    result.append(i->first);
    result.append("]");
  }
  return result;
}
*/