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
use std::borrow::Cow;
use std::cell::RefCell;
use std::path::Path;
use std::ffi::{OsString, OsStr};

use super::lexer::Lexer;
use super::lexer::Token as LexerToken;
use super::state::{State, Pool};
use super::eval_env::{BindingEnv, EvalString, Rule};
use super::disk_interface::FileReader;
use super::version::check_ninja_version;
use super::utils::canonicalize_path;

#[derive(PartialEq)]
pub enum DupeEdgeAction {
    WARN,
    ERROR,
}

#[derive(PartialEq)]
pub enum PhonyCycleAction {
    WARN,
    ERROR,
}

pub struct ManifestParserOptions {
    pub dupe_edge_action: DupeEdgeAction,
    pub phony_cycle_action: PhonyCycleAction,
}

impl ManifestParserOptions {
    pub fn new() -> Self {
        Default::default()
    }
}

impl Default for ManifestParserOptions {
    fn default() -> Self {
        ManifestParserOptions {
            dupe_edge_action: DupeEdgeAction::ERROR,
            phony_cycle_action: PhonyCycleAction::ERROR,
        }
    }
}

/// Parses .ninja files.
pub struct ManifestParser<'a, 'c : 'a> {
    state: &'a mut State,
    env: Rc<RefCell<BindingEnv>>,
    file_reader: &'a FileReader,
    lexer: Lexer<'a, 'c>,
    options: ManifestParserOptions,
    quiet: bool
}

impl<'a, 'c> ManifestParser<'a, 'c> where 'c : 'a {
    pub fn new(state: &'a mut State, file_reader: &'a FileReader, options: ManifestParserOptions) -> Self {
        let env = state.get_env();
        ManifestParser {
            state,
            env: env,
            file_reader,
            options,
            lexer: Lexer::new(),
            quiet: false
        }
    }

    /// Load and parse a file.
    pub fn load(&mut self, filename: &Path) -> Result<(), String> {
        self.load_with_parent(filename, None)
    }

    pub fn load_with_parent(&mut self, filename: &Path, parent: Option<&Lexer>) -> Result<(), String> {
/*
  METRIC_RECORD(".ninja parse");
  string contents;
  string read_err;
  if (file_reader_->ReadFile(filename, &contents, &read_err) != FileReader::Okay) {
    *err = "loading '" + filename + "': " + read_err;
    if (parent)
      parent->Error(string(*err), err);
    return false;
  }

  // The lexer needs a nul byte at the end of its input, to know when it's done.
  // It takes a StringPiece, and StringPiece's string constructor uses
  // string::data().  data()'s return value isn't guaranteed to be
  // null-terminated (although in practice - libc++, libstdc++, msvc's stl --
  // it is, and C++11 demands that too), so add an explicit nul byte.
  contents.resize(contents.size() + 1);

  return Parse(filename, contents, err);
*/
        unimplemented!{}
    }

    /// Parse a text string of input.  Used by tests.
    #[cfg(test)]
    pub(crate) fn parse_test(&mut self, input: &'c [u8]) -> Result<(), String> {
        lazy_static! {
            static ref FAKE_FILENAME : OsString = OsString::from("input");
        }
        self.quiet = true;
        self.parse(&FAKE_FILENAME, input)
    }

    /// Parse a file, given its contents as a string.
    pub fn parse(&mut self, filename: &'a OsStr, input: &'c [u8]) -> Result<(), String> {
        self.lexer.start(filename, input);
        loop {
            let token = self.lexer.read_token();
            match token {
              LexerToken::POOL => {
                  self.parse_pool()?;
              },
              LexerToken::BUILD => {
                  self.parse_edge()?;
              },
              LexerToken::RULE => {
                  self.parse_rule()?;
              },
              LexerToken::DEFAULT => {
                  self.parse_default()?;
              },
              LexerToken::IDENT => {
                  self.lexer.unread_token();
                  let (name, let_value) = self.parse_let()?;
                  let value = let_value.evaluate(&self.env.borrow() as &BindingEnv);
                  // Check ninja_required_version immediately so we can exit
                  // before encountering any syntactic surprises.
                  if &name == b"ninja_required_version" {
                      check_ninja_version(String::from_utf8_lossy(&value).as_ref());
                  }
                  self.env.borrow_mut().add_binding(&name, &value);
              },
              LexerToken::INCLUDE => {
                  self.parse_file_include(false)?;
              },
              LexerToken::SUBNINJA => {
                  self.parse_file_include(true)?;
              },
              LexerToken::ERROR => {
                  return Err(self.lexer.error(self.lexer.describe_last_error()));
              },
              LexerToken::TEOF => {
                  return Ok(());
              },
              LexerToken::NEWLINE => {
                  ()
              },
              _ => {
                  return Err(self.lexer.error(&format!("unexpected {}", token.name())));
              }
            }
        }
    }

    /// Parse various statement types.
    fn parse_pool(&mut self) -> Result<(), String> {
        let name = self.lexer.read_ident("expected pool name")?.to_owned();
        self.expect_token(LexerToken::NEWLINE)?;
        if self.state.pool_state.lookup_pool(&name).is_some() {
            return Err(self.lexer.error(&format!("duplicate pool '{}'", String::from_utf8_lossy(&name))));
        }

        let mut depth = None;
        while self.lexer.peek_token(LexerToken::INDENT) {
            let (key, value) = self.parse_let()?;

            if key != b"depth" {
                return Err(self.lexer.error(&format!("unexpected variable '{}'", String::from_utf8_lossy(&key))))
            }

            let depth_string = value.evaluate(&self.env.borrow() as &BindingEnv);
            let depth_value = String::from_utf8_lossy(&depth_string).parse::<isize>().ok()
                        .and_then(|v| if v >= 0 { Some(v) } else { None });
            if depth_value.is_none() {
                return Err(self.lexer.error("invalid pool depth"));
            }
            depth = depth_value;
        }

        let depth = depth.ok_or_else(|| { self.lexer.error("expected 'depth =' line") })?;

        self.state.pool_state.add_pool(Rc::new(RefCell::new(Pool::new(name, depth))));
        Ok(())
    }

    fn parse_rule(&mut self) -> Result<(), String> {
        let name = self.lexer.read_ident("expected rule name")?.to_owned();

        self.expect_token(LexerToken::NEWLINE)?;

        if self.env.borrow().lookup_rule_current_scope(&name).is_some() {
            return Err(self.lexer.error(&format!("duplicate rule '{}'", String::from_utf8_lossy(&name))))
        }
        let mut rule = Rule::new(name);
        while self.lexer.peek_token(LexerToken::INDENT) {
            let (key, value) = self.parse_let()?;
            if Rule::is_reserved_binding(&key) {
                rule.add_binding(&key, &value);
            } else {
                // Die on other keyvals for now; revisit if we want to add a
                // scope here.
                return Err(self.lexer.error(&format!("unexpected variable '{}'", String::from_utf8_lossy(&key))));
            }
        }
        if rule.bindings.get(b"rspfile".as_ref()).is_none() !=
            rule.bindings.get(b"rspfile_content".as_ref()).is_none() {
            return Err(self.lexer.error("rspfile and rspfile_content need to be both specified")); 
        }

        if rule.bindings.get(b"command".as_ref()).is_none() {
            return Err(self.lexer.error("expected 'command =' line"));
        }

        self.env.borrow_mut().add_rule(Rc::new(rule));
        return Ok(());
    }

    fn parse_let(&mut self) -> Result<(Vec<u8>, EvalString), String> {
        let key = self.lexer.read_ident("expected variable name")?.to_owned();
        self.expect_token(LexerToken::EQUALS)?;
        let mut value = EvalString::new();
        self.lexer.read_var_value(&mut value)?;
        Ok((key, value))
    }

    fn parse_edge(&mut self) -> Result<(), String> {
        let mut ins = Vec::new();
        let mut outs = Vec::new();

        loop {
            let mut out = EvalString::new();
            self.lexer.read_path(&mut out)?;

            if out.is_empty() {
                break;
            }
            outs.push(out);
        }

        // Add all implicit outs, counting how many as we go.
        let mut implicit_outs = 0usize;
        if self.lexer.peek_token(LexerToken::PIPE) {
            loop {
                let mut out = EvalString::new();
                self.lexer.read_path(&mut out)?;

                if out.is_empty() {
                    break;
                }
                outs.push(out);
                implicit_outs += 1;
            }
        }

        if outs.is_empty() {
            return Err(self.lexer.error("expected path"));
        }

        self.expect_token(LexerToken::COLON)?;

        let rule = {
            let rule_name = self.lexer.read_ident("expected build command name")?.to_owned();
            let rule = self.env.borrow().lookup_rule(&rule_name).map(Cow::into_owned);
            rule.ok_or_else(|| {
                self.lexer.error(&format!("unknown build rule '{}'", String::from_utf8_lossy(&rule_name)))
            })?
        };

        loop {
            // XXX should we require one path here?
            let mut in_ = EvalString::new();
            self.lexer.read_path(&mut in_)?;

            if in_.is_empty() {
                break;
            }
            ins.push(in_);
        }

        // Add all implicit deps, counting how many as we go.
        let mut implicit = 0usize;
        if self.lexer.peek_token(LexerToken::PIPE) {
            loop {
                let mut in_ = EvalString::new();
                self.lexer.read_path(&mut in_)?;

                if in_.is_empty() {
                    break;
                }
                ins.push(in_);
                implicit += 1;
            }
        }

        // Add all order-only deps, counting how many as we go.
        let mut order_only = 0usize;
        if self.lexer.peek_token(LexerToken::PIPE2) {
            loop {
                let mut in_ = EvalString::new();
                self.lexer.read_path(&mut in_)?;

                if in_.is_empty() {
                    break;
                }
                ins.push(in_);
                order_only += 1;
            }
        }
        self.expect_token(LexerToken::NEWLINE)?;
        // Bindings on edges are rare, so allocate per-edge envs only when needed.
        let mut edge_env = None;
        if self.lexer.peek_token(LexerToken::INDENT) {
            let mut env = BindingEnv::new_with_parent(Some(self.env.clone()));
            while {
                let (key, value) = self.parse_let()?;
                let evaluated_value = value.evaluate(&env);
                env.add_binding(&key, &evaluated_value);
                self.lexer.peek_token(LexerToken::INDENT)
            } {}
            edge_env = Some(Rc::new(RefCell::new(env)));
        }
        
        let env = edge_env.as_ref().unwrap_or(&self.env).clone();

        let mut edge_idx = self.state.edge_state.make_edge(rule, self.state.bindings.clone());
        let mut edge_revoked = false;
        {
            let mut edge = self.state.edge_state.get_edge_mut(edge_idx);
            edge.env = env.clone();

            let pool_name = edge.get_binding(b"pool").into_owned();
            if !pool_name.is_empty() {
                let lexer = &self.lexer;
                let pool = self.state.pool_state.lookup_pool(&pool_name).ok_or_else(|| {
                    lexer.error(&format!("unknown pool name '{}'", String::from_utf8_lossy(&pool_name)))
                })?;
                edge.pool = pool.clone();
            }

            let e = outs.len();
            edge.outputs.reserve(e);
            for (i, o) in outs.iter().enumerate() {
                let mut path = o.evaluate(&*env.borrow());
                let lexer = &self.lexer;

                let slash_bits = canonicalize_path(&mut path).map_err(|path_err| {
                  lexer.error(&path_err)
                })?;

                let out_node_idx = self.state.node_state.prepare_node(&path, slash_bits);
                let mut out_node = self.state.node_state.get_node_mut(out_node_idx);

                if !State::connect_edge_to_out_node(edge, edge_idx, out_node, out_node_idx) {
                  match self.options.dupe_edge_action {
                    DupeEdgeAction::ERROR => {
                      return Err(self.lexer.error(
                        &format!("multiple rules generate {} [-w dupbuild=err]", 
                        String::from_utf8_lossy(&path))));
                    },
                    DupeEdgeAction::WARN => {
                      if !self.quiet {
                        warning!(concat!(
                          "multiple rules generate {}. ",
                          "builds involving this target will not be correct; ",
                          "continuing anyway [-w dupbuild=warn]"
                        ), String::from_utf8_lossy(&path));
                      }
                    }
                  }
                  if implicit_outs + i >= e {
                    implicit_outs -= 1;
                  }

                }
            }
            if edge.outputs.is_empty() {
                // All outputs of the edge are already created by other edges. Don't add
                // this edge.  Do this check before input nodes are connected to the edge.
                edge_revoked = true;
            }
        }
        if edge_revoked {
            self.state.edge_state.revoke_latest_edge(edge_idx);
            return Ok(());
        }

        let mut edge = self.state.edge_state.get_edge_mut(edge_idx);
        
        edge.implicit_outs = implicit_outs;

        edge.inputs.reserve(ins.len());
        for i in ins.iter() {
            let mut path = i.evaluate(&*env.borrow());
            let lexer = &self.lexer;
            let slash_bits = canonicalize_path(&mut path).map_err(|path_err| {
              lexer.error(&path_err)
            })?;

            let in_node_idx = self.state.node_state.prepare_node(&path, slash_bits);
            let mut in_node = self.state.node_state.get_node_mut(in_node_idx);
            State::connect_edge_to_in_node(edge, edge_idx, in_node, in_node_idx);
        }
        edge.implicit_deps = implicit;
        edge.order_only_deps = order_only;

        if self.options.phony_cycle_action == PhonyCycleAction::WARN && edge.maybe_phonycycle_diagnostic() {
            // CMake 2.8.12.x and 3.0.x incorrectly write phony build statements
            // that reference themselves.  Ninja used to tolerate these in the
            // build graph but that has since been fixed.  Filter them out to
            // support users of those old CMake versions.
            let out_node_idx = edge.outputs[0];
            // XXX use drain_filter instead.
            let mut i = 0;
            let mut modified = false;
            while i != edge.inputs.len() {
              if edge.inputs[i] == out_node_idx {
                edge.inputs.remove(i);
                i -= 1;
                modified = true;
              }
              i += 1;
            }
            if modified && !self.quiet {
              let out_node = self.state.node_state.get_node(out_node_idx);
              warning!("phony target '{}' names itself as an input; ignoring [-w phonycycle=warn]",
                String::from_utf8_lossy(out_node.path()));
            }
        }

        // Multiple outputs aren't (yet?) supported with depslog.
        let deps_type = edge.get_binding(b"deps");
        if !deps_type.is_empty() && edge.outputs.len() > 1 {
            return Err(self.lexer.error(
                concat!(
                  "multiple outputs aren't (yet?) supported by depslog; ",
                  "bring this up on the mailing list if it affects you")));
        }
        Ok(())
    }

    fn parse_default(&mut self) -> Result<(), String> {
        unimplemented!()
    }

    /// Parse either a 'subninja' or 'include' line.
    fn parse_file_include(&mut self, new_scope: bool) -> Result<(), String> {
        unimplemented!()
    }

    /// If the next token is not \a expected, produce an error string
    /// saying "expectd foo, got bar".
    fn expect_token(&mut self, expected: LexerToken) -> Result<(), String> {
        let token = self.lexer.read_token();
        if token == expected {
            Ok(())
        } else {
            let message = format!("expected {}, got {}{}", expected.name(), token.name(), expected.error_hint());
            Err(self.lexer.error(&message))
        }
    }

}

/*






bool ManifestParser::ParseDefault(string* err) {
  EvalString eval;
  if (!lexer_.ReadPath(&eval, err))
    return false;
  if (eval.empty())
    return lexer_.Error("expected target name", err);

  do {
    string path = eval.Evaluate(env_);
    string path_err;
    uint64_t slash_bits;  // Unused because this only does lookup.
    if (!CanonicalizePath(&path, &slash_bits, &path_err))
      return lexer_.Error(path_err, err);
    if (!state_->AddDefault(path, &path_err))
      return lexer_.Error(path_err, err);

    eval.Clear();
    if (!lexer_.ReadPath(&eval, err))
      return false;
  } while (!eval.empty());

  if (!ExpectToken(Lexer::NEWLINE, err))
    return false;

  return true;
}

bool ManifestParser::ParseEdge(string* err) {
}

bool ManifestParser::ParseFileInclude(bool new_scope, string* err) {
  EvalString eval;
  if (!lexer_.ReadPath(&eval, err))
    return false;
  string path = eval.Evaluate(env_);

  ManifestParser subparser(state_, file_reader_, options_);
  if (new_scope) {
    subparser.env_ = new BindingEnv(env_);
  } else {
    subparser.env_ = env_;
  }

  if (!subparser.Load(path, err, &lexer_))
    return false;

  if (!ExpectToken(Lexer::NEWLINE, err))
    return false;

  return true;
}

*/

#[cfg(test)]
mod parser_test {
    use super::*;
    use super::super::state::State;
    use super::super::test::VirtualFileSystem;

    struct ParserTest {
        pub state: RefCell<State>,
        pub fs: VirtualFileSystem,
    }

    impl ParserTest {
        pub fn new() -> Self {
            ParserTest {
                state: RefCell::new(State::new()),
                fs: VirtualFileSystem::new(),
            }
        }

        pub fn assert_parse(&mut self, input: &[u8]) -> () {
            {
              let mut state = self.state.borrow_mut();
              let mut parser = ManifestParser::new(&mut state, 
                &self.fs, Default::default());
              assert_eq!(Ok(()), parser.parse_test(input));
            }
            assert_eq!((), self.state.borrow().verify_graph());
        }
    }

    #[test]
    fn parsertest_empty() {
        let mut parsertest = ParserTest::new();
        parsertest.assert_parse(b"");
    }

    #[test]
    fn parsertest_rules() {
        let mut parsertest = ParserTest::new();
        parsertest.assert_parse(concat!(
          "rule cat\n",
          "  command = cat $in > $out\n",
          "\n",
          "rule date\n",
          "  command = date > $out\n",
          "\n",
          "build result: cat in_1.cc in-2.O\n"
          ).as_bytes());
        let state = parsertest.state.borrow();
        let bindings = state.bindings.borrow();
        assert_eq!(3usize, bindings.get_rules().len());
        let rule = bindings.get_rules().iter().next().unwrap().1;
        assert_eq!(b"cat", rule.name());
        assert_eq!(b"[cat ][$in][ > ][$out]".as_ref().to_owned(), 
            rule.get_binding(b"command").unwrap().serialize());
    }

    #[test]
    fn parsertest_ruleattributes() {
        let mut parsertest = ParserTest::new();
        // Check that all of the allowed rule attributes are parsed ok.
        parsertest.assert_parse(concat!(
          "rule cat\n",
          "  command = a\n",
          "  depfile = a\n",
          "  deps = a\n",
          "  description = a\n",
          "  generator = a\n",
          "  restat = a\n",
          "  rspfile = a\n",
          "  rspfile_content = a\n"
          ).as_bytes());
    }

    #[test]
    fn parsertest_ignore_indented_comments() {
        let mut parsertest = ParserTest::new();
        parsertest.assert_parse(concat!(
          "  #indented comment\n",
          "rule cat\n",
          "  command = cat $in > $out\n",
          "  #generator = 1\n",
          "  restat = 1 # comment\n",
          "  #comment\n",
          "build result: cat in_1.cc in-2.O\n",
          "  #comment\n"
          ).as_bytes());
        let state = parsertest.state.borrow();
        let bindings = state.bindings.borrow();
        assert_eq!(2usize, bindings.get_rules().len());
        let rule = bindings.get_rules().iter().next().unwrap().1;
        assert_eq!(b"cat", rule.name());

        let node_idx = state.node_state.lookup_node(b"result").unwrap();
        let edge_idx = state.node_state.get_node(node_idx).in_edge().unwrap();
        let edge = state.edge_state.get_edge(edge_idx);
        assert_eq!(true, edge.get_binding_bool(b"restat"));
        assert_eq!(false, edge.get_binding_bool(b"generator"));
    }


/*

TEST_F(ParserTest, IgnoreIndentedBlankLines) {
  // the indented blanks used to cause parse errors
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"  \n"
"rule cat\n"
"  command = cat $in > $out\n"
"  \n"
"build result: cat in_1.cc in-2.O\n"
"  \n"
"variable=1\n"));

  // the variable must be in the top level environment
  EXPECT_EQ("1", state.bindings_.LookupVariable("variable"));
}

TEST_F(ParserTest, ResponseFiles) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat_rsp\n"
"  command = cat $rspfile > $out\n"
"  rspfile = $rspfile\n"
"  rspfile_content = $in\n"
"\n"
"build out: cat_rsp in\n"
"  rspfile=out.rsp\n"));

  ASSERT_EQ(2u, state.bindings_.GetRules().size());
  const Rule* rule = state.bindings_.GetRules().begin()->second;
  EXPECT_EQ("cat_rsp", rule->name());
  EXPECT_EQ("[cat ][$rspfile][ > ][$out]",
            rule->GetBinding("command")->Serialize());
  EXPECT_EQ("[$rspfile]", rule->GetBinding("rspfile")->Serialize());
  EXPECT_EQ("[$in]", rule->GetBinding("rspfile_content")->Serialize());
}

TEST_F(ParserTest, InNewline) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat_rsp\n"
"  command = cat $in_newline > $out\n"
"\n"
"build out: cat_rsp in in2\n"
"  rspfile=out.rsp\n"));

  ASSERT_EQ(2u, state.bindings_.GetRules().size());
  const Rule* rule = state.bindings_.GetRules().begin()->second;
  EXPECT_EQ("cat_rsp", rule->name());
  EXPECT_EQ("[cat ][$in_newline][ > ][$out]",
            rule->GetBinding("command")->Serialize());

  Edge* edge = state.edges_[0];
  EXPECT_EQ("cat in\nin2 > out", edge->EvaluateCommand());
}

TEST_F(ParserTest, Variables) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"l = one-letter-test\n"
"rule link\n"
"  command = ld $l $extra $with_under -o $out $in\n"
"\n"
"extra = -pthread\n"
"with_under = -under\n"
"build a: link b c\n"
"nested1 = 1\n"
"nested2 = $nested1/2\n"
"build supernested: link x\n"
"  extra = $nested2/3\n"));

  ASSERT_EQ(2u, state.edges_.size());
  Edge* edge = state.edges_[0];
  EXPECT_EQ("ld one-letter-test -pthread -under -o a b c",
            edge->EvaluateCommand());
  EXPECT_EQ("1/2", state.bindings_.LookupVariable("nested2"));

  edge = state.edges_[1];
  EXPECT_EQ("ld one-letter-test 1/2/3 -under -o supernested x",
            edge->EvaluateCommand());
}

TEST_F(ParserTest, VariableScope) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"foo = bar\n"
"rule cmd\n"
"  command = cmd $foo $in $out\n"
"\n"
"build inner: cmd a\n"
"  foo = baz\n"
"build outer: cmd b\n"
"\n"  // Extra newline after build line tickles a regression.
));

  ASSERT_EQ(2u, state.edges_.size());
  EXPECT_EQ("cmd baz a inner", state.edges_[0]->EvaluateCommand());
  EXPECT_EQ("cmd bar b outer", state.edges_[1]->EvaluateCommand());
}

TEST_F(ParserTest, Continuation) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule link\n"
"  command = foo bar $\n"
"    baz\n"
"\n"
"build a: link c $\n"
" d e f\n"));

  ASSERT_EQ(2u, state.bindings_.GetRules().size());
  const Rule* rule = state.bindings_.GetRules().begin()->second;
  EXPECT_EQ("link", rule->name());
  EXPECT_EQ("[foo bar baz]", rule->GetBinding("command")->Serialize());
}

TEST_F(ParserTest, Backslash) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"foo = bar\\baz\n"
"foo2 = bar\\ baz\n"
));
  EXPECT_EQ("bar\\baz", state.bindings_.LookupVariable("foo"));
  EXPECT_EQ("bar\\ baz", state.bindings_.LookupVariable("foo2"));
}

TEST_F(ParserTest, Comment) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"# this is a comment\n"
"foo = not # a comment\n"));
  EXPECT_EQ("not # a comment", state.bindings_.LookupVariable("foo"));
}

TEST_F(ParserTest, Dollars) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule foo\n"
"  command = ${out}bar$$baz$$$\n"
"blah\n"
"x = $$dollar\n"
"build $x: foo y\n"
));
  EXPECT_EQ("$dollar", state.bindings_.LookupVariable("x"));
#ifdef _WIN32
  EXPECT_EQ("$dollarbar$baz$blah", state.edges_[0]->EvaluateCommand());
#else
  EXPECT_EQ("'$dollar'bar$baz$blah", state.edges_[0]->EvaluateCommand());
#endif
}

TEST_F(ParserTest, EscapeSpaces) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule spaces\n"
"  command = something\n"
"build foo$ bar: spaces $$one two$$$ three\n"
));
  EXPECT_TRUE(state.LookupNode("foo bar"));
  EXPECT_EQ(state.edges_[0]->outputs_[0]->path(), "foo bar");
  EXPECT_EQ(state.edges_[0]->inputs_[0]->path(), "$one");
  EXPECT_EQ(state.edges_[0]->inputs_[1]->path(), "two$ three");
  EXPECT_EQ(state.edges_[0]->EvaluateCommand(), "something");
}

TEST_F(ParserTest, CanonicalizeFile) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build out: cat in/1 in//2\n"
"build in/1: cat\n"
"build in/2: cat\n"));

  EXPECT_TRUE(state.LookupNode("in/1"));
  EXPECT_TRUE(state.LookupNode("in/2"));
  EXPECT_FALSE(state.LookupNode("in//1"));
  EXPECT_FALSE(state.LookupNode("in//2"));
}

#ifdef _WIN32
TEST_F(ParserTest, CanonicalizeFileBackslashes) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build out: cat in\\1 in\\\\2\n"
"build in\\1: cat\n"
"build in\\2: cat\n"));

  Node* node = state.LookupNode("in/1");;
  EXPECT_TRUE(node);
  EXPECT_EQ(1, node->slash_bits());
  node = state.LookupNode("in/2");
  EXPECT_TRUE(node);
  EXPECT_EQ(1, node->slash_bits());
  EXPECT_FALSE(state.LookupNode("in//1"));
  EXPECT_FALSE(state.LookupNode("in//2"));
}
#endif

TEST_F(ParserTest, PathVariables) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"dir = out\n"
"build $dir/exe: cat src\n"));

  EXPECT_FALSE(state.LookupNode("$dir/exe"));
  EXPECT_TRUE(state.LookupNode("out/exe"));
}

TEST_F(ParserTest, CanonicalizePaths) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build ./out.o: cat ./bar/baz/../foo.cc\n"));

  EXPECT_FALSE(state.LookupNode("./out.o"));
  EXPECT_TRUE(state.LookupNode("out.o"));
  EXPECT_FALSE(state.LookupNode("./bar/baz/../foo.cc"));
  EXPECT_TRUE(state.LookupNode("bar/foo.cc"));
}

#ifdef _WIN32
TEST_F(ParserTest, CanonicalizePathsBackslashes) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build ./out.o: cat ./bar/baz/../foo.cc\n"
"build .\\out2.o: cat .\\bar/baz\\..\\foo.cc\n"
"build .\\out3.o: cat .\\bar\\baz\\..\\foo3.cc\n"
));

  EXPECT_FALSE(state.LookupNode("./out.o"));
  EXPECT_FALSE(state.LookupNode(".\\out2.o"));
  EXPECT_FALSE(state.LookupNode(".\\out3.o"));
  EXPECT_TRUE(state.LookupNode("out.o"));
  EXPECT_TRUE(state.LookupNode("out2.o"));
  EXPECT_TRUE(state.LookupNode("out3.o"));
  EXPECT_FALSE(state.LookupNode("./bar/baz/../foo.cc"));
  EXPECT_FALSE(state.LookupNode(".\\bar/baz\\..\\foo.cc"));
  EXPECT_FALSE(state.LookupNode(".\\bar/baz\\..\\foo3.cc"));
  Node* node = state.LookupNode("bar/foo.cc");
  EXPECT_TRUE(node);
  EXPECT_EQ(0, node->slash_bits());
  node = state.LookupNode("bar/foo3.cc");
  EXPECT_TRUE(node);
  EXPECT_EQ(1, node->slash_bits());
}
#endif

TEST_F(ParserTest, DuplicateEdgeWithMultipleOutputs) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build out1 out2: cat in1\n"
"build out1: cat in2\n"
"build final: cat out1\n"
));
  // AssertParse() checks that the generated build graph is self-consistent.
  // That's all the checking that this test needs.
}

TEST_F(ParserTest, NoDeadPointerFromDuplicateEdge) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build out: cat in\n"
"build out: cat in\n"
));
  // AssertParse() checks that the generated build graph is self-consistent.
  // That's all the checking that this test needs.
}

TEST_F(ParserTest, DuplicateEdgeWithMultipleOutputsError) {
  const char kInput[] =
"rule cat\n"
"  command = cat $in > $out\n"
"build out1 out2: cat in1\n"
"build out1: cat in2\n"
"build final: cat out1\n";
  ManifestParserOptions parser_opts;
  parser_opts.dupe_edge_action_ = kDupeEdgeActionError;
  ManifestParser parser(&state, &fs_, parser_opts);
  string err;
  EXPECT_FALSE(parser.ParseTest(kInput, &err));
  EXPECT_EQ("input:5: multiple rules generate out1 [-w dupbuild=err]\n", err);
}

TEST_F(ParserTest, DuplicateEdgeInIncludedFile) {
  fs_.Create("sub.ninja",
    "rule cat\n"
    "  command = cat $in > $out\n"
    "build out1 out2: cat in1\n"
    "build out1: cat in2\n"
    "build final: cat out1\n");
  const char kInput[] =
    "subninja sub.ninja\n";
  ManifestParserOptions parser_opts;
  parser_opts.dupe_edge_action_ = kDupeEdgeActionError;
  ManifestParser parser(&state, &fs_, parser_opts);
  string err;
  EXPECT_FALSE(parser.ParseTest(kInput, &err));
  EXPECT_EQ("sub.ninja:5: multiple rules generate out1 [-w dupbuild=err]\n",
            err);
}

TEST_F(ParserTest, PhonySelfReferenceIgnored) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"build a: phony a\n"
));

  Node* node = state.LookupNode("a");
  Edge* edge = node->in_edge();
  ASSERT_TRUE(edge->inputs_.empty());
}

TEST_F(ParserTest, PhonySelfReferenceKept) {
  const char kInput[] =
"build a: phony a\n";
  ManifestParserOptions parser_opts;
  parser_opts.phony_cycle_action_ = kPhonyCycleActionError;
  ManifestParser parser(&state, &fs_, parser_opts);
  string err;
  EXPECT_TRUE(parser.ParseTest(kInput, &err));
  EXPECT_EQ("", err);

  Node* node = state.LookupNode("a");
  Edge* edge = node->in_edge();
  ASSERT_EQ(edge->inputs_.size(), 1);
  ASSERT_EQ(edge->inputs_[0], node);
}

TEST_F(ParserTest, ReservedWords) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule build\n"
"  command = rule run $out\n"
"build subninja: build include default foo.cc\n"
"default subninja\n"));
}

TEST_F(ParserTest, Errors) {
  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest(string("subn", 4), &err));
    EXPECT_EQ("input:1: expected '=', got eof\n"
              "subn\n"
              "    ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("foobar", &err));
    EXPECT_EQ("input:1: expected '=', got eof\n"
              "foobar\n"
              "      ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("x 3", &err));
    EXPECT_EQ("input:1: expected '=', got identifier\n"
              "x 3\n"
              "  ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("x = 3", &err));
    EXPECT_EQ("input:1: unexpected EOF\n"
              "x = 3\n"
              "     ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("x = 3\ny 2", &err));
    EXPECT_EQ("input:2: expected '=', got identifier\n"
              "y 2\n"
              "  ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("x = $", &err));
    EXPECT_EQ("input:1: bad $-escape (literal $ must be written as $$)\n"
              "x = $\n"
              "    ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("x = $\n $[\n", &err));
    EXPECT_EQ("input:2: bad $-escape (literal $ must be written as $$)\n"
              " $[\n"
              " ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("x = a$\n b$\n $\n", &err));
    EXPECT_EQ("input:4: unexpected EOF\n"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("build\n", &err));
    EXPECT_EQ("input:1: expected path\n"
              "build\n"
              "     ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("build x: y z\n", &err));
    EXPECT_EQ("input:1: unknown build rule 'y'\n"
              "build x: y z\n"
              "       ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("build x:: y z\n", &err));
    EXPECT_EQ("input:1: expected build command name\n"
              "build x:: y z\n"
              "       ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n  command = cat ok\n"
                                  "build x: cat $\n :\n",
                                  &err));
    EXPECT_EQ("input:4: expected newline, got ':'\n"
              " :\n"
              " ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n",
                                  &err));
    EXPECT_EQ("input:2: expected 'command =' line\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n"
                                  "  command = echo\n"
                                  "rule cat\n"
                                  "  command = echo\n", &err));
    EXPECT_EQ("input:3: duplicate rule 'cat'\n"
              "rule cat\n"
              "        ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n"
                                  "  command = echo\n"
                                  "  rspfile = cat.rsp\n", &err));
    EXPECT_EQ(
        "input:4: rspfile and rspfile_content need to be both specified\n",
        err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n"
                                  "  command = ${fafsd\n"
                                  "foo = bar\n",
                                  &err));
    EXPECT_EQ("input:2: bad $-escape (literal $ must be written as $$)\n"
              "  command = ${fafsd\n"
              "            ^ near here"
              , err);
  }


  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n"
                                  "  command = cat\n"
                                  "build $.: cat foo\n",
                                  &err));
    EXPECT_EQ("input:3: bad $-escape (literal $ must be written as $$)\n"
              "build $.: cat foo\n"
              "      ^ near here"
              , err);
  }


  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cat\n"
                                  "  command = cat\n"
                                  "build $: cat foo\n",
                                  &err));
    EXPECT_EQ("input:3: expected ':', got newline ($ also escapes ':')\n"
              "build $: cat foo\n"
              "                ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule %foo\n",
                                  &err));
    EXPECT_EQ("input:1: expected rule name\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cc\n"
                                  "  command = foo\n"
                                  "  othervar = bar\n",
                                  &err));
    EXPECT_EQ("input:3: unexpected variable 'othervar'\n"
              "  othervar = bar\n"
              "                ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cc\n  command = foo\n"
                                  "build $.: cc bar.cc\n",
                                  &err));
    EXPECT_EQ("input:3: bad $-escape (literal $ must be written as $$)\n"
              "build $.: cc bar.cc\n"
              "      ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cc\n  command = foo\n  && bar",
                                  &err));
    EXPECT_EQ("input:3: expected variable name\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule cc\n  command = foo\n"
                                  "build $: cc bar.cc\n",
                                  &err));
    EXPECT_EQ("input:3: expected ':', got newline ($ also escapes ':')\n"
              "build $: cc bar.cc\n"
              "                  ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("default\n",
                                  &err));
    EXPECT_EQ("input:1: expected target name\n"
              "default\n"
              "       ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("default nonexistent\n",
                                  &err));
    EXPECT_EQ("input:1: unknown target 'nonexistent'\n"
              "default nonexistent\n"
              "                   ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule r\n  command = r\n"
                                  "build b: r\n"
                                  "default b:\n",
                                  &err));
    EXPECT_EQ("input:4: expected newline, got ':'\n"
              "default b:\n"
              "         ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("default $a\n", &err));
    EXPECT_EQ("input:1: empty path\n"
              "default $a\n"
              "          ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("rule r\n"
                                  "  command = r\n"
                                  "build $a: r $c\n", &err));
    // XXX the line number is wrong; we should evaluate paths in ParseEdge
    // as we see them, not after we've read them all!
    EXPECT_EQ("input:4: empty path\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    // the indented blank line must terminate the rule
    // this also verifies that "unexpected (token)" errors are correct
    EXPECT_FALSE(parser.ParseTest("rule r\n"
                                  "  command = r\n"
                                  "  \n"
                                  "  generator = 1\n", &err));
    EXPECT_EQ("input:4: unexpected indent\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("pool\n", &err));
    EXPECT_EQ("input:1: expected pool name\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("pool foo\n", &err));
    EXPECT_EQ("input:2: expected 'depth =' line\n", err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("pool foo\n"
                                  "  depth = 4\n"
                                  "pool foo\n", &err));
    EXPECT_EQ("input:3: duplicate pool 'foo'\n"
              "pool foo\n"
              "        ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("pool foo\n"
                                  "  depth = -1\n", &err));
    EXPECT_EQ("input:2: invalid pool depth\n"
              "  depth = -1\n"
              "            ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    EXPECT_FALSE(parser.ParseTest("pool foo\n"
                                  "  bar = 1\n", &err));
    EXPECT_EQ("input:2: unexpected variable 'bar'\n"
              "  bar = 1\n"
              "         ^ near here"
              , err);
  }

  {
    State local_state;
    ManifestParser parser(&local_state, NULL);
    string err;
    // Pool names are dereferenced at edge parsing time.
    EXPECT_FALSE(parser.ParseTest("rule run\n"
                                  "  command = echo\n"
                                  "  pool = unnamed_pool\n"
                                  "build out: run in\n", &err));
    EXPECT_EQ("input:5: unknown pool name 'unnamed_pool'\n", err);
  }
}

TEST_F(ParserTest, MissingInput) {
  State local_state;
  ManifestParser parser(&local_state, &fs_);
  string err;
  EXPECT_FALSE(parser.Load("build.ninja", &err));
  EXPECT_EQ("loading 'build.ninja': No such file or directory", err);
}

TEST_F(ParserTest, MultipleOutputs) {
  State local_state;
  ManifestParser parser(&local_state, NULL);
  string err;
  EXPECT_TRUE(parser.ParseTest("rule cc\n  command = foo\n  depfile = bar\n"
                               "build a.o b.o: cc c.cc\n",
                               &err));
  EXPECT_EQ("", err);
}

TEST_F(ParserTest, MultipleOutputsWithDeps) {
  State local_state;
  ManifestParser parser(&local_state, NULL);
  string err;
  EXPECT_FALSE(parser.ParseTest("rule cc\n  command = foo\n  deps = gcc\n"
                               "build a.o b.o: cc c.cc\n",
                               &err));
  EXPECT_EQ("input:5: multiple outputs aren't (yet?) supported by depslog; "
            "bring this up on the mailing list if it affects you\n", err);
}

TEST_F(ParserTest, SubNinja) {
  fs_.Create("test.ninja",
    "var = inner\n"
    "build $builddir/inner: varref\n");
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"builddir = some_dir/\n"
"rule varref\n"
"  command = varref $var\n"
"var = outer\n"
"build $builddir/outer: varref\n"
"subninja test.ninja\n"
"build $builddir/outer2: varref\n"));
  ASSERT_EQ(1u, fs_.files_read_.size());

  EXPECT_EQ("test.ninja", fs_.files_read_[0]);
  EXPECT_TRUE(state.LookupNode("some_dir/outer"));
  // Verify our builddir setting is inherited.
  EXPECT_TRUE(state.LookupNode("some_dir/inner"));

  ASSERT_EQ(3u, state.edges_.size());
  EXPECT_EQ("varref outer", state.edges_[0]->EvaluateCommand());
  EXPECT_EQ("varref inner", state.edges_[1]->EvaluateCommand());
  EXPECT_EQ("varref outer", state.edges_[2]->EvaluateCommand());
}

TEST_F(ParserTest, MissingSubNinja) {
  ManifestParser parser(&state, &fs_);
  string err;
  EXPECT_FALSE(parser.ParseTest("subninja foo.ninja\n", &err));
  EXPECT_EQ("input:1: loading 'foo.ninja': No such file or directory\n"
            "subninja foo.ninja\n"
            "                  ^ near here"
            , err);
}

TEST_F(ParserTest, DuplicateRuleInDifferentSubninjas) {
  // Test that rules are scoped to subninjas.
  fs_.Create("test.ninja", "rule cat\n"
                         "  command = cat\n");
  ManifestParser parser(&state, &fs_);
  string err;
  EXPECT_TRUE(parser.ParseTest("rule cat\n"
                                "  command = cat\n"
                                "subninja test.ninja\n", &err));
}

TEST_F(ParserTest, DuplicateRuleInDifferentSubninjasWithInclude) {
  // Test that rules are scoped to subninjas even with includes.
  fs_.Create("rules.ninja", "rule cat\n"
                         "  command = cat\n");
  fs_.Create("test.ninja", "include rules.ninja\n"
                         "build x : cat\n");
  ManifestParser parser(&state, &fs_);
  string err;
  EXPECT_TRUE(parser.ParseTest("include rules.ninja\n"
                                "subninja test.ninja\n"
                                "build y : cat\n", &err));
}

TEST_F(ParserTest, Include) {
  fs_.Create("include.ninja", "var = inner\n");
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"var = outer\n"
"include include.ninja\n"));

  ASSERT_EQ(1u, fs_.files_read_.size());
  EXPECT_EQ("include.ninja", fs_.files_read_[0]);
  EXPECT_EQ("inner", state.bindings_.LookupVariable("var"));
}

TEST_F(ParserTest, BrokenInclude) {
  fs_.Create("include.ninja", "build\n");
  ManifestParser parser(&state, &fs_);
  string err;
  EXPECT_FALSE(parser.ParseTest("include include.ninja\n", &err));
  EXPECT_EQ("include.ninja:1: expected path\n"
            "build\n"
            "     ^ near here"
            , err);
}

TEST_F(ParserTest, Implicit) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build foo: cat bar | baz\n"));

  Edge* edge = state.LookupNode("foo")->in_edge();
  ASSERT_TRUE(edge->is_implicit(1));
}

TEST_F(ParserTest, OrderOnly) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n  command = cat $in > $out\n"
"build foo: cat bar || baz\n"));

  Edge* edge = state.LookupNode("foo")->in_edge();
  ASSERT_TRUE(edge->is_order_only(1));
}

TEST_F(ParserTest, ImplicitOutput) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build foo | imp: cat bar\n"));

  Edge* edge = state.LookupNode("imp")->in_edge();
  ASSERT_EQ(edge->outputs_.size(), 2);
  EXPECT_TRUE(edge->is_implicit_out(1));
}

TEST_F(ParserTest, ImplicitOutputEmpty) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build foo | : cat bar\n"));

  Edge* edge = state.LookupNode("foo")->in_edge();
  ASSERT_EQ(edge->outputs_.size(), 1);
  EXPECT_FALSE(edge->is_implicit_out(0));
}

TEST_F(ParserTest, ImplicitOutputDupe) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build foo baz | foo baq foo: cat bar\n"));

  Edge* edge = state.LookupNode("foo")->in_edge();
  ASSERT_EQ(edge->outputs_.size(), 3);
  EXPECT_FALSE(edge->is_implicit_out(0));
  EXPECT_FALSE(edge->is_implicit_out(1));
  EXPECT_TRUE(edge->is_implicit_out(2));
}

TEST_F(ParserTest, ImplicitOutputDupes) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = cat $in > $out\n"
"build foo foo foo | foo foo foo foo: cat bar\n"));

  Edge* edge = state.LookupNode("foo")->in_edge();
  ASSERT_EQ(edge->outputs_.size(), 1);
  EXPECT_FALSE(edge->is_implicit_out(0));
}

TEST_F(ParserTest, NoExplicitOutput) {
  ManifestParser parser(&state, NULL);
  string err;
  EXPECT_TRUE(parser.ParseTest(
"rule cat\n"
"  command = cat $in > $out\n"
"build | imp : cat bar\n", &err));
}

TEST_F(ParserTest, DefaultDefault) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n  command = cat $in > $out\n"
"build a: cat foo\n"
"build b: cat foo\n"
"build c: cat foo\n"
"build d: cat foo\n"));

  string err;
  EXPECT_EQ(4u, state.DefaultNodes(&err).size());
  EXPECT_EQ("", err);
}

TEST_F(ParserTest, DefaultDefaultCycle) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n  command = cat $in > $out\n"
"build a: cat a\n"));

  string err;
  EXPECT_EQ(0u, state.DefaultNodes(&err).size());
  EXPECT_EQ("could not determine root nodes of build graph", err);
}

TEST_F(ParserTest, DefaultStatements) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n  command = cat $in > $out\n"
"build a: cat foo\n"
"build b: cat foo\n"
"build c: cat foo\n"
"build d: cat foo\n"
"third = c\n"
"default a b\n"
"default $third\n"));

  string err;
  vector<Node*> nodes = state.DefaultNodes(&err);
  EXPECT_EQ("", err);
  ASSERT_EQ(3u, nodes.size());
  EXPECT_EQ("a", nodes[0]->path());
  EXPECT_EQ("b", nodes[1]->path());
  EXPECT_EQ("c", nodes[2]->path());
}
*/

    #[test]
    fn parsertest_utf8() {
        let mut parsertest = ParserTest::new();
        parsertest.assert_parse(concat!("rule utf8\n",
          "  command = true\n",
          "  description = compilaci\u{F3}\n").as_bytes());
    }

    #[test]
    fn parsertest_crlf() {
        let inputs = [
            "# comment with crlf\r\n",
            "foo = foo\nbar = bar\r\n",
            concat!(
              "pool link_pool\r\n",
              "  depth = 15\r\n\r\n",
              "rule xyz\r\n",
              "  command = something$expand \r\n",
              "  description = YAY!\r\n",
            )
        ];
        for input in inputs.into_iter() {
            let mut parsertest = ParserTest::new();
            parsertest.assert_parse(input.as_bytes());
        }
    }

}
