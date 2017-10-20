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
use std::path::Path;
use std::ffi::{OsString, OsStr};

use super::lexer::Lexer;
use super::lexer::Token as LexerToken;
use super::state::State;
use super::eval_env::{BindingEnv, EvalString};
use super::disk_interface::FileReader;
use super::version::check_ninja_version;

pub enum DupeEdgeAction {
    WARN,
    ERROR,
}

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
pub struct ManifestParser<'a, 'b : 'a, 'c : 'a> {
    state: &'a State<'b>,
    env:   Rc<RefCell<BindingEnv<'b>>>,
    file_reader: &'a FileReader,
    lexer: Lexer<'a, 'c>,
    options: ManifestParserOptions,
    quiet: bool
}

impl<'a, 'b, 'c> ManifestParser<'a, 'b, 'c> where 'b : 'a, 'c : 'a {
    pub fn new(state: &'a State<'b>, file_reader: &'a FileReader, options: ManifestParserOptions) -> Self {
        ManifestParser {
            state,
            env: state.bindings.clone(),
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
        unreachable!()
    }

    /// Parse various statement types.
    fn parse_pool(&mut self) -> Result<(), String> {
        unimplemented!()
    }

    fn parse_rule(&mut self) -> Result<(), String> {
        unimplemented!()
    }

    fn parse_let(&mut self) -> Result<(Vec<u8>, EvalString), String> {
        unimplemented!()
    }

    fn parse_edge(&mut self) -> Result<(), String> {
        unimplemented!()
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
        unimplemented!()
    }

}

/*

bool ManifestParser::Load(const string& filename, string* err, Lexer* parent) {
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
}


bool ManifestParser::ParsePool(string* err) {
  string name;
  if (!lexer_.ReadIdent(&name))
    return lexer_.Error("expected pool name", err);

  if (!ExpectToken(Lexer::NEWLINE, err))
    return false;

  if (state_->LookupPool(name) != NULL)
    return lexer_.Error("duplicate pool '" + name + "'", err);

  int depth = -1;

  while (lexer_.PeekToken(Lexer::INDENT)) {
    string key;
    EvalString value;
    if (!ParseLet(&key, &value, err))
      return false;

    if (key == "depth") {
      string depth_string = value.Evaluate(env_);
      depth = atol(depth_string.c_str());
      if (depth < 0)
        return lexer_.Error("invalid pool depth", err);
    } else {
      return lexer_.Error("unexpected variable '" + key + "'", err);
    }
  }

  if (depth < 0)
    return lexer_.Error("expected 'depth =' line", err);

  state_->AddPool(new Pool(name, depth));
  return true;
}


bool ManifestParser::ParseRule(string* err) {
  string name;
  if (!lexer_.ReadIdent(&name))
    return lexer_.Error("expected rule name", err);

  if (!ExpectToken(Lexer::NEWLINE, err))
    return false;

  if (env_->LookupRuleCurrentScope(name) != NULL)
    return lexer_.Error("duplicate rule '" + name + "'", err);

  Rule* rule = new Rule(name);  // XXX scoped_ptr

  while (lexer_.PeekToken(Lexer::INDENT)) {
    string key;
    EvalString value;
    if (!ParseLet(&key, &value, err))
      return false;

    if (Rule::IsReservedBinding(key)) {
      rule->AddBinding(key, value);
    } else {
      // Die on other keyvals for now; revisit if we want to add a
      // scope here.
      return lexer_.Error("unexpected variable '" + key + "'", err);
    }
  }

  if (rule->bindings_["rspfile"].empty() !=
      rule->bindings_["rspfile_content"].empty()) {
    return lexer_.Error("rspfile and rspfile_content need to be "
                        "both specified", err);
  }

  if (rule->bindings_["command"].empty())
    return lexer_.Error("expected 'command =' line", err);

  env_->AddRule(rule);
  return true;
}

bool ManifestParser::ParseLet(string* key, EvalString* value, string* err) {
  if (!lexer_.ReadIdent(key))
    return lexer_.Error("expected variable name", err);
  if (!ExpectToken(Lexer::EQUALS, err))
    return false;
  if (!lexer_.ReadVarValue(value, err))
    return false;
  return true;
}

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
  vector<EvalString> ins, outs;

  {
    EvalString out;
    if (!lexer_.ReadPath(&out, err))
      return false;
    while (!out.empty()) {
      outs.push_back(out);

      out.Clear();
      if (!lexer_.ReadPath(&out, err))
        return false;
    }
  }

  // Add all implicit outs, counting how many as we go.
  int implicit_outs = 0;
  if (lexer_.PeekToken(Lexer::PIPE)) {
    for (;;) {
      EvalString out;
      if (!lexer_.ReadPath(&out, err))
        return err;
      if (out.empty())
        break;
      outs.push_back(out);
      ++implicit_outs;
    }
  }

  if (outs.empty())
    return lexer_.Error("expected path", err);

  if (!ExpectToken(Lexer::COLON, err))
    return false;

  string rule_name;
  if (!lexer_.ReadIdent(&rule_name))
    return lexer_.Error("expected build command name", err);

  const Rule* rule = env_->LookupRule(rule_name);
  if (!rule)
    return lexer_.Error("unknown build rule '" + rule_name + "'", err);

  for (;;) {
    // XXX should we require one path here?
    EvalString in;
    if (!lexer_.ReadPath(&in, err))
      return false;
    if (in.empty())
      break;
    ins.push_back(in);
  }

  // Add all implicit deps, counting how many as we go.
  int implicit = 0;
  if (lexer_.PeekToken(Lexer::PIPE)) {
    for (;;) {
      EvalString in;
      if (!lexer_.ReadPath(&in, err))
        return err;
      if (in.empty())
        break;
      ins.push_back(in);
      ++implicit;
    }
  }

  // Add all order-only deps, counting how many as we go.
  int order_only = 0;
  if (lexer_.PeekToken(Lexer::PIPE2)) {
    for (;;) {
      EvalString in;
      if (!lexer_.ReadPath(&in, err))
        return false;
      if (in.empty())
        break;
      ins.push_back(in);
      ++order_only;
    }
  }

  if (!ExpectToken(Lexer::NEWLINE, err))
    return false;

  // Bindings on edges are rare, so allocate per-edge envs only when needed.
  bool has_indent_token = lexer_.PeekToken(Lexer::INDENT);
  BindingEnv* env = has_indent_token ? new BindingEnv(env_) : env_;
  while (has_indent_token) {
    string key;
    EvalString val;
    if (!ParseLet(&key, &val, err))
      return false;

    env->AddBinding(key, val.Evaluate(env_));
    has_indent_token = lexer_.PeekToken(Lexer::INDENT);
  }

  Edge* edge = state_->AddEdge(rule);
  edge->env_ = env;

  string pool_name = edge->GetBinding("pool");
  if (!pool_name.empty()) {
    Pool* pool = state_->LookupPool(pool_name);
    if (pool == NULL)
      return lexer_.Error("unknown pool name '" + pool_name + "'", err);
    edge->pool_ = pool;
  }

  edge->outputs_.reserve(outs.size());
  for (size_t i = 0, e = outs.size(); i != e; ++i) {
    string path = outs[i].Evaluate(env);
    string path_err;
    uint64_t slash_bits;
    if (!CanonicalizePath(&path, &slash_bits, &path_err))
      return lexer_.Error(path_err, err);
    if (!state_->AddOut(edge, path, slash_bits)) {
      if (options_.dupe_edge_action_ == kDupeEdgeActionError) {
        lexer_.Error("multiple rules generate " + path + " [-w dupbuild=err]",
                     err);
        return false;
      } else {
        if (!quiet_) {
          Warning("multiple rules generate %s. "
                  "builds involving this target will not be correct; "
                  "continuing anyway [-w dupbuild=warn]",
                  path.c_str());
        }
        if (e - i <= static_cast<size_t>(implicit_outs))
          --implicit_outs;
      }
    }
  }
  if (edge->outputs_.empty()) {
    // All outputs of the edge are already created by other edges. Don't add
    // this edge.  Do this check before input nodes are connected to the edge.
    state_->edges_.pop_back();
    delete edge;
    return true;
  }
  edge->implicit_outs_ = implicit_outs;

  edge->inputs_.reserve(ins.size());
  for (vector<EvalString>::iterator i = ins.begin(); i != ins.end(); ++i) {
    string path = i->Evaluate(env);
    string path_err;
    uint64_t slash_bits;
    if (!CanonicalizePath(&path, &slash_bits, &path_err))
      return lexer_.Error(path_err, err);
    state_->AddIn(edge, path, slash_bits);
  }
  edge->implicit_deps_ = implicit;
  edge->order_only_deps_ = order_only;

  if (options_.phony_cycle_action_ == kPhonyCycleActionWarn &&
      edge->maybe_phonycycle_diagnostic()) {
    // CMake 2.8.12.x and 3.0.x incorrectly write phony build statements
    // that reference themselves.  Ninja used to tolerate these in the
    // build graph but that has since been fixed.  Filter them out to
    // support users of those old CMake versions.
    Node* out = edge->outputs_[0];
    vector<Node*>::iterator new_end =
        remove(edge->inputs_.begin(), edge->inputs_.end(), out);
    if (new_end != edge->inputs_.end()) {
      edge->inputs_.erase(new_end, edge->inputs_.end());
      if (!quiet_) {
        Warning("phony target '%s' names itself as an input; "
                "ignoring [-w phonycycle=warn]",
                out->path().c_str());
      }
    }
  }

  // Multiple outputs aren't (yet?) supported with depslog.
  string deps_type = edge->GetBinding("deps");
  if (!deps_type.empty() && edge->outputs_.size() > 1) {
    return lexer_.Error("multiple outputs aren't (yet?) supported by depslog; "
                        "bring this up on the mailing list if it affects you",
                        err);
  }

  return true;
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

bool ManifestParser::ExpectToken(Lexer::Token expected, string* err) {
  Lexer::Token token = lexer_.ReadToken();
  if (token != expected) {
    string message = string("expected ") + Lexer::TokenName(expected);
    message += string(", got ") + Lexer::TokenName(token);
    message += Lexer::TokenErrorHint(expected);
    return lexer_.Error(message, err);
  }
  return true;
}


*/

#[cfg(test)]
mod parser_test {
    use super::*;
    use super::super::state::State;
    use super::super::test::VirtualFileSystem;

    struct ParserTest<'a> {
        pub state: State<'a>,
        pub fs: VirtualFileSystem,
    }

    impl<'a> ParserTest<'a> {
        pub fn new() -> Self {
            ParserTest {
                state: State::new(),
                fs: VirtualFileSystem::new(),
            }
        }

        pub fn assert_parse(&'a self, input: &[u8]) -> () {
            {
              let mut parser = ManifestParser::new(&self.state, &self.fs, Default::default());
              assert_eq!(Ok(()), parser.parse_test(input));
            }
            assert_eq!((), self.state.verify_graph());
        }
    }

    #[test]
    fn parsertest_empty() {
        let parsertest = ParserTest::new();
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
        assert_eq!(3usize, parsertest.state.bindings.borrow().get_rules().len());
        let bindings = parsertest.state.bindings.borrow();
        let rule = bindings.get_rules().iter().next().unwrap().1;
        assert_eq!(b"cat", rule.name());
        assert_eq!(b"[cat ][$in][ > ][$out]".as_ref().to_owned(), 
            rule.get_binding(b"command").unwrap().serialize());
    }

}


/*

TEST_F(ParserTest, RuleAttributes) {
  // Check that all of the allowed rule attributes are parsed ok.
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule cat\n"
"  command = a\n"
"  depfile = a\n"
"  deps = a\n"
"  description = a\n"
"  generator = a\n"
"  restat = a\n"
"  rspfile = a\n"
"  rspfile_content = a\n"
));
}

TEST_F(ParserTest, IgnoreIndentedComments) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"  #indented comment\n"
"rule cat\n"
"  command = cat $in > $out\n"
"  #generator = 1\n"
"  restat = 1 # comment\n"
"  #comment\n"
"build result: cat in_1.cc in-2.O\n"
"  #comment\n"));

  ASSERT_EQ(2u, state.bindings_.GetRules().size());
  const Rule* rule = state.bindings_.GetRules().begin()->second;
  EXPECT_EQ("cat", rule->name());
  Edge* edge = state.GetNode("result", 0)->in_edge();
  EXPECT_TRUE(edge->GetBindingBool("restat"));
  EXPECT_FALSE(edge->GetBindingBool("generator"));
}

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

TEST_F(ParserTest, UTF8) {
  ASSERT_NO_FATAL_FAILURE(AssertParse(
"rule utf8\n"
"  command = true\n"
"  description = compilaci\xC3\xB3\n"));
}

TEST_F(ParserTest, CRLF) {
  State local_state;
  ManifestParser parser(&local_state, NULL);
  string err;

  EXPECT_TRUE(parser.ParseTest("# comment with crlf\r\n", &err));
  EXPECT_TRUE(parser.ParseTest("foo = foo\nbar = bar\r\n", &err));
  EXPECT_TRUE(parser.ParseTest(
      "pool link_pool\r\n"
      "  depth = 15\r\n\r\n"
      "rule xyz\r\n"
      "  command = something$expand \r\n"
      "  description = YAY!\r\n",
      &err));
}
*/