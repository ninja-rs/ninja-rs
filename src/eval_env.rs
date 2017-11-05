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

use std::borrow::Cow;
use std::cell::RefCell;
use std::rc::Rc;
use std::collections::{BTreeMap, HashMap};
use std::fmt;
use std::io::Write;

/// An interface for a scope for variable (e.g. "$foo") lookups.
pub trait Env {
    fn lookup_variable(&self, var: &[u8]) -> Cow<[u8]>;
}

#[derive(PartialEq, Clone)]
enum TokenType {
    Raw,
    Special
}

type TokenList = Vec<(Vec<u8>, TokenType)>;

/// A tokenized string that contains variable references.
/// Can be evaluated relative to an Env.
#[derive(Clone)]
pub struct EvalString {
    parsed: TokenList,
}

impl EvalString {
    pub fn new() -> Self {
        EvalString {
        parsed: TokenList::new(),
        }
    }

    pub fn evaluate<E: Env + ?Sized>(&self, env: &E) -> Vec<u8> {
        let mut result = Vec::new();
        for &(ref txt, ref ty) in self.parsed.iter() {
            if ty == &TokenType::Raw {
                result.extend_from_slice(txt);
            } else {
                result.extend_from_slice(&env.lookup_variable(txt))
            }
        }
        result
    }

    pub fn clear(&mut self) {
        self.parsed.clear()
    }

    pub fn is_empty(&self) -> bool {
        self.parsed.is_empty()
    }

    pub fn add_text(&mut self, text: &[u8]) {
        if let Some(last) = self.parsed.last_mut() {
            if last.1 == TokenType::Raw {
                last.0.extend(text.iter());
                return;
            }
        }
        self.parsed.push((text.to_owned(), TokenType::Raw));
    }

    pub fn add_special(&mut self, text: &[u8]) {
        self.parsed.push((text.to_owned(), TokenType::Special));
    }

    /// Construct a human-readable representation of the parsed state,
    /// for use in tests.
    pub(crate) fn serialize(&self) -> Vec<u8> {
        let mut result = Vec::new();
        for &(ref txt, ref ty) in self.parsed.iter() {
            result.extend_from_slice(b"[");
            if ty == &TokenType::Special {
                result.extend_from_slice(b"$");
            }
            result.extend_from_slice(txt);
            result.extend_from_slice(b"]");
        }
        result
    }
}

impl fmt::Debug for EvalString {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(formatter, "EvalString {{ {} }}", String::from_utf8_lossy(&self.serialize()))
    }
}


type RuleBindings = HashMap<Vec<u8>, EvalString>;

/// An invokable build command and associated metadata (description, etc.).
pub struct Rule {
    name: Vec<u8>,
    pub(crate) bindings: RuleBindings,
}

impl Rule {
    pub fn new(name: Vec<u8>) -> Self {
        Rule {
            name,
            bindings: RuleBindings::new(),
        }
    }

    pub fn name(&self) -> &[u8] {
        &self.name
    }

    pub fn add_binding(&mut self, key: &[u8], val: &EvalString) {
        self.bindings.insert(key.to_owned(), val.clone());
    }

    pub fn is_reserved_binding(var: &[u8]) -> bool {
        var == b"command" ||
        var == b"depfile" ||
        var == b"description" ||
        var == b"deps" ||
        var == b"generator" ||
        var == b"pool" ||
        var == b"restat" ||
        var == b"rspfile" ||
        var == b"rspfile_content" ||
        var == b"msvc_deps_prefix"
    }

    pub fn get_binding(&self, key: &[u8]) -> Option<&EvalString> {
        self.bindings.get(key)
    }
}

/// An Env which contains a mapping of variables to values
/// as well as a pointer to a parent scope.
pub struct BindingEnv {
    bindings: BTreeMap<Vec<u8>, Vec<u8>>,
    rules: BTreeMap<Vec<u8>, Rc<Rule>>,
    parent: Option<Rc<RefCell<BindingEnv>>>
}

impl BindingEnv {
    pub fn new() -> Self {
        BindingEnv {
            bindings: BTreeMap::new(),
            rules: BTreeMap::new(),
            parent: None,
        }
    }

    pub fn new_with_parent(parent: Option<Rc<RefCell<BindingEnv>>>) -> Self {
        BindingEnv {
            bindings: BTreeMap::new(),
            rules: BTreeMap::new(),
            parent: parent,
        }
    }
    
    pub fn add_binding(&mut self, key: &[u8], val: &[u8]) {
        self.bindings.insert(key.to_owned(), val.to_owned());
    }

    pub fn lookup_rule_current_scope(&self, rule_name: &[u8]) -> Option<&Rc<Rule>> {
        if let Some(rule) = self.rules.get(rule_name) {
            return Some(rule);
        }

        return None;
    }

    pub fn lookup_rule(&self, rule_name: &[u8]) -> Option<Cow<Rc<Rule>>> {
        if let Some(rule) = self.rules.get(rule_name) {
            return Some(Cow::Borrowed(rule));
        }

        if let Some(ref parent) = self.parent {
            return parent.borrow().lookup_rule(rule_name).map(|c| Cow::Owned(c.into_owned()));
        }

        return None;
    }

    pub fn add_rule(&mut self, rule: Rc<Rule>) {
        debug_assert!(self.lookup_rule_current_scope(rule.name()).is_none());
        self.rules.insert(rule.name().to_owned(), rule);
    }

    pub fn get_rules(&self) -> &BTreeMap<Vec<u8>, Rc<Rule>> {
        return &self.rules;
    }

    /// This is tricky.  Edges want lookup scope to go in this order:
    /// 1) value set on edge itself (edge_->env_)
    /// 2) value set on rule, with expansion in the edge's scope
    /// 3) value set on enclosing scope of edge (edge_->env_->parent_)
    /// This function takes as parameters the necessary info to do (2).
    pub fn lookup_with_fallback(&self, var: &[u8], eval: Option<&EvalString>, env: &Env) -> Cow<[u8]> {
        if let Some(self_binding) = self.bindings.get(var) {
            return Cow::Borrowed(self_binding.as_ref());
        }
        if let Some(eval) = eval {
            return eval.evaluate(env).into();
        }

        if let Some(ref parent) = self.parent {
            return Cow::Owned(parent.borrow().lookup_variable(var).into_owned());
        }
        return b"".as_ref().into();
    }
}

impl Env for BindingEnv {
    fn lookup_variable(&self, var: &[u8]) -> Cow<[u8]> {
        if let Some(self_binding) = self.bindings.get(var) {
            return Cow::Borrowed(self_binding);
        }
        if let Some(ref parent) = self.parent {
            return Cow::Owned(parent.borrow().lookup_variable(var).into_owned());
        }
        return Cow::Borrowed(b"");
    }
}
