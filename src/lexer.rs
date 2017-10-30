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

use std::ffi::{OsString, OsStr};
use nom::{self, IResult, Offset};

use super::eval_env::EvalString;

#[derive(PartialEq, Clone, Copy, Debug)]
pub enum LexerToken {
    ERROR,
    BUILD,
    COLON,
    DEFAULT,
    EQUALS,
    IDENT,
    INCLUDE,
    INDENT,
    NEWLINE,
    PIPE,
    PIPE2,
    POOL,
    RULE,
    SUBNINJA,
    TEOF,
}

impl LexerToken {

    /// Return a human-readable form of a token, used in error messages.
    pub fn name(&self) -> &'static str {
        match *self {
            LexerToken::ERROR     => "lexing error",
            LexerToken::BUILD     => "'build'",
            LexerToken::COLON     => "':'",
            LexerToken::DEFAULT   => "'default'",
            LexerToken::EQUALS    => "'='",
            LexerToken::IDENT     => "identifier",
            LexerToken::INCLUDE   => "'include'",
            LexerToken::INDENT    => "indent",
            LexerToken::NEWLINE   => "newline",
            LexerToken::PIPE2     => "'||'",
            LexerToken::PIPE      => "'|'",
            LexerToken::POOL      => "'pool'",
            LexerToken::RULE      => "'rule'",
            LexerToken::SUBNINJA  => "'subninja'",
            LexerToken::TEOF      => "eof",
        }
    }

    /// Return a human-readable token hint, used in error messages.
    pub fn error_hint(&self) -> &'static str {
        match *self {
            LexerToken::COLON => " ($ also escapes ':')",
            _ => "",
        }
    }

}

pub struct Lexer<'a, 'b> {
    filename: &'a OsStr,
    input: &'b [u8],
    last_token_offset: usize,
    offset: usize,
}

fn is_simple_varname_char(c: u8) -> bool {
    match c {
    b'a'...b'z' |
    b'A'...b'Z' |
    b'0'...b'9' |
    b'_' | b'-' => true,
    _ => false,
    }
}

fn is_varname_char(c: u8) -> bool {
    match c {
    b'a'...b'z' |
    b'A'...b'Z' |
    b'0'...b'9' |
    b'.' |
    b'_' | b'-' => true,
    _ => false,
    }
}


fn is_comment_char(c: u8) -> bool {
    match c {
    0 | b'\n' => false,
    _ => true,
    }
}

fn is_text_char(ch: u8) -> bool {
    match ch {
    b'$' | b' ' | b':' | b'\r' | b'\n' | b'|' | 0 => false,
    _ => true
    }
}

fn is_sp_char(c: u8) -> bool {
    c == b' '
}

impl<'a, 'b> Lexer<'a, 'b> {
    pub fn new(filename: &'a OsStr, input: &'b [u8]) -> Self {
        Lexer {
            filename: filename,
            input: input,
            last_token_offset: 0,
            offset: 0,
        }
    }

    /// Helper ctor useful for tests.
    #[cfg(test)]
    pub(crate) fn new_with_input(input: &'b [u8]) -> Self {
        lazy_static! {
            static ref FAKE_FILENAME: OsString = "input".into();
        }
        Lexer::new(&FAKE_FILENAME, input)
    }

    /// If the last token read was an ERROR token, provide more info
    /// or the empty string.
    pub fn describe_last_error(&self) -> &'static str {
        match self.input.get(self.last_token_offset) {
            Some(&b'\t') => 
                "tabs are not allowed, use spaces",
            _ => "lexing error"
        }
    }

    /// Read a LexerToken from the LexerToken enum.
    pub fn read_token(&mut self) -> LexerToken {
        let mut rest_input = &self.input[self.offset..];

        named!(skip_comment<&[u8], ()>,
            fold_many0!(
                complete!(
                    preceded!(take_while!(is_sp_char), 
                        terminated!(preceded!(char!('#'), take_while!(is_comment_char)),
                            char!('\n')))),
                (),
                |_, _| ()));

        named!(ident_or_keyword<&[u8], LexerToken>,
            alt_complete!(
                value!(LexerToken::BUILD, terminated!(tag!("build"), eof!())) |
                value!(LexerToken::POOL, terminated!(tag!("pool"), eof!())) |
                value!(LexerToken::RULE, terminated!(tag!("rule"), eof!())) |
                value!(LexerToken::DEFAULT, terminated!(tag!("default"), eof!())) |
                value!(LexerToken::INCLUDE, terminated!(tag!("include"), eof!())) |
                value!(LexerToken::SUBNINJA, terminated!(tag!("subninja"), eof!())) |
                value!(LexerToken::IDENT, nom::non_empty)
            ));

        named!(read_one_token<&[u8], LexerToken>,
            alt_complete!(
                value!(LexerToken::NEWLINE, 
                    preceded!(take_while!(is_sp_char),
                        preceded!(opt!(char!('\r')), char!('\n')))) |
                value!(LexerToken::INDENT, take_while1!(is_sp_char)) |
                value!(LexerToken::EQUALS, tag!("=")) |
                value!(LexerToken::COLON, tag!(":")) |
                value!(LexerToken::PIPE2, tag!("||")) |
                value!(LexerToken::PIPE, tag!("|")) |
                flat_map!(take_while1!(is_varname_char), ident_or_keyword) |
                value!(LexerToken::TEOF, char!('\0')) |
                value!(LexerToken::ERROR, take!(1)) |
                value!(LexerToken::TEOF, eof!())
                ));

        let token : LexerToken;

        match skip_comment(rest_input) {
            IResult::Done(i, _) => {
                rest_input = i;
            },
            _ => {},
        }

        self.last_token_offset = self.input.offset(rest_input);

        match read_one_token(rest_input) {
            IResult::Done(i, v) => {
                rest_input = i;
                token = v;
            },
            _ => {
                panic!("unreachable");
            }            
        }

        self.offset = self.input.offset(rest_input);

        match token {
            LexerToken::NEWLINE | LexerToken::TEOF => {},
            _ => { self.eat_whitespace(); },
        }

        return token;
    }

    /// Rewind to the last read LexerToken.
    pub fn unread_token(&mut self) {
        self.offset = self.last_token_offset;
    }

    /// If the next token is \a token, read it and return true.
    pub fn peek_token(&mut self, token: LexerToken) -> bool {
        let t = self.read_token();
        if t == token {
            return true;
        }
        self.unread_token();
        return false;
    }

    /// Read a simple identifier (a rule or variable name).
    /// Returns false if a name can't be read.
    pub fn read_ident(&mut self, message: &str) -> Result<&[u8], String> {
        let rest_input = &self.input[self.offset..];
        named!(read_ident_token,
            take_while1!(is_varname_char));
        let (i, v) = match read_ident_token(rest_input) {
            IResult::Done(i, v) => {
                (i, v)
            },
            _ => {
                return Err(self.error(message));
            }
        };
        self.offset = self.input.offset(i);
        self.eat_whitespace();
        return Ok(v);
    }

    /// Read a path (complete with $escapes).
    /// Returns false only on error, returned path may be empty if a delimiter
    /// (space, newline) is hit.
    pub fn read_path(&mut self, path: &mut EvalString) -> Result<(), String> {
        self.read_evalstring(path, true)
    }
    

    /// Read the value side of a var = value line (complete with $escapes).
    /// Returns false only on error.
    pub fn read_var_value(&mut self, value: &mut EvalString) -> Result<(), String> {
        self.read_evalstring(value, false)
    }

    /// Construct an error message with context.
    pub fn error(&self, message: &str) -> String {
        // Compute line/column.
        let context = &self.input[0..self.last_token_offset];
        let (last_line_idx, last_line_cnt) = context.split(|ch| ch == &b'\n').enumerate().last().unwrap();

        let line = last_line_idx + 1;
        let col = last_line_cnt.len();

        let mut err = format!("{}:{}: {}\n", self.filename.to_string_lossy(), line, message);

        const TRUNCATE_COLUMN: usize = 72;
        if col > 0 && col < TRUNCATE_COLUMN {
            let last_line_start = self.input.offset(last_line_cnt);
            let last_line_fulltext = self.input[last_line_start..].split(|ch| ch == &b'\n' || ch == &0).next().unwrap();
            let mut last_line_context_len = last_line_fulltext.len();
            let truncated = last_line_context_len >= TRUNCATE_COLUMN;
            if truncated {
                last_line_context_len = TRUNCATE_COLUMN;
            }

            err += &format!("{}{}\n{}^ near here",
                String::from_utf8_lossy(&self.input[last_line_start..last_line_start + last_line_context_len]),
                if truncated { "..." } else { "" },
                (0..col).map(|_| ' ').collect::<String>()
            );
        }
        return err;
    }

    /// Skip past whitespace (called after each read token/ident/etc.).
    fn eat_whitespace(&mut self) {
        let mut rest_input = &self.input[self.offset..];
        named!(skip_whitespace<&[u8], ()>,
            fold_many0!(
                alt_complete!(
                    take_while1!(is_sp_char) |
                    tag!("$\r\n") |
                    tag!("$\n")),
                (),
                |_, _| ()));

        match skip_whitespace(rest_input) {
            IResult::Done(i, _) => {
                rest_input = i;
            },
            _ => {}
        }

        self.offset = self.input.offset(rest_input);
    }
    
    /// Read a $-escaped string.
    pub fn read_evalstring(&mut self, eval: &mut EvalString, path: bool) -> Result<(), String> {
        let mut rest_input = &self.input[self.offset..];

        enum TokenResult<'a> {
            Text(&'a[u8]),
            Special(&'a[u8]),
            Ignored,
            StopHere,
            Error(&'static str),
            ErrorLastError,
        }

        named_args!(read_evalstring_token(path: bool)<TokenResult>,
            alt_complete!(
                map!(take_while1!(is_text_char), TokenResult::Text) |
                value!(TokenResult::StopHere, cond_reduce!(path, peek!(tag!("\r\n")))) |
                value!(TokenResult::StopHere, tag!("\r\n")) |
                value!(TokenResult::StopHere, cond_reduce!(path, peek!(one_of!(" :|\n")))) |
                value!(TokenResult::StopHere, tag!("\n")) |
                map!(alt!(tag!(" ")|tag!(":")|tag!("|")), TokenResult::Text) |
                map!(preceded!(tag!("$"), tag!("$")), TokenResult::Text) |
                map!(preceded!(tag!("$"), tag!(" ")), TokenResult::Text) |
                value!(TokenResult::Ignored, preceded!(tag!("$\r\n"),take_while!(is_sp_char))) |
                value!(TokenResult::Ignored, preceded!(tag!("$\n"),take_while!(is_sp_char))) |
                map!(delimited!(tag!("${"), take_while1!(is_varname_char), tag!("}")), TokenResult::Special) |
                map!(preceded!(tag!("$"), take_while1!(is_simple_varname_char)), TokenResult::Special) |
                map!(preceded!(tag!("$"), tag!(":")), TokenResult::Text) |
                value!(TokenResult::Error("bad $-escape (literal $ must be written as $$)"),
                    peek!(preceded!(tag!("$"), alt_complete!(take!(1)|eof!())))) |
                value!(TokenResult::Error("unexpected EOF"),
                    alt_complete!(peek!(tag!("\0"))|eof!())) |
                value!(TokenResult::ErrorLastError, peek!(take!(1)))));
        
        loop {
            match read_evalstring_token(rest_input, path) {
                IResult::Done(i, v) => {
                    match v {
                        TokenResult::Text(p) => {
                            eval.add_text(p);
                            rest_input = i;
                        },
                        TokenResult::Special(p) => {
                            eval.add_special(p);
                            rest_input = i;
                        },
                        TokenResult::Ignored => {
                            rest_input = i;
                        },
                        TokenResult::StopHere => {
                            self.last_token_offset = self.input.offset(rest_input);
                            rest_input = i;
                            self.offset = self.input.offset(rest_input);
                            break;
                        },
                        TokenResult::Error(p) => {
                            self.last_token_offset = self.input.offset(rest_input);
                            return Err(self.error(p));
                        }
                        TokenResult::ErrorLastError => {
                            self.last_token_offset = self.input.offset(rest_input);
                            return Err(self.error(self.describe_last_error()));
                        }
                    }
                },
                _ => {
                    unreachable!()
                }
            }
        };

        if path {
            self.eat_whitespace();
        }
        Ok(())
    }

}

#[test]
fn test_lexer_read_var_value() {
    let mut lexer = Lexer::new_with_input(b"plain text $var $VaR ${x}\n");
    let mut eval = EvalString::new();
    assert_eq!(Ok(()), lexer.read_var_value(&mut eval));
    assert_eq!(b"[plain text ][$var][ ][$VaR][ ][$x]".as_ref().to_owned(),
            eval.serialize());
}

#[test]
fn test_lexer_read_evalstring_escapes() {
    let mut lexer = Lexer::new_with_input(b"$ $$ab c$: $\ncde\n");
    let mut eval = EvalString::new();
    assert_eq!(Ok(()), lexer.read_var_value(&mut eval));
    assert_eq!(b"[ $ab c: cde]".as_ref().to_owned(),
            eval.serialize());
}

#[test]
fn test_lexer_read_ident() {
    let mut lexer = Lexer::new_with_input(b"foo baR baz_123 foo-bar");

    assert_eq!(Ok(b"foo".as_ref()), lexer.read_ident("read_ident"));
    assert_eq!(Ok(b"baR".as_ref()), lexer.read_ident("read_ident"));
    assert_eq!(Ok(b"baz_123".as_ref()), lexer.read_ident("read_ident"));
    assert_eq!(Ok(b"foo-bar".as_ref()), lexer.read_ident("read_ident"));
}

#[test]
fn test_lexer_read_ident_curlies() {
    // Verify that ReadIdent includes dots in the name,
    // but in an expansion $bar.dots stops at the dot.
    let mut lexer = Lexer::new_with_input(b"foo.dots $bar.dots ${bar.dots}\n");
    assert_eq!(Ok(b"foo.dots".as_ref()), lexer.read_ident("read_ident"));

    let mut eval = EvalString::new();
    assert_eq!(Ok(()), lexer.read_var_value(&mut eval));
    assert_eq!(b"[$bar][.dots ][$bar.dots]".as_ref().to_owned(),
            eval.serialize());
}

#[test]
fn test_lexer_error() {
    let mut lexer = Lexer::new_with_input(b"foo$\nbad $");
    let mut eval = EvalString::new();
    assert_eq!(Err(
        concat!(
            "input:2: bad $-escape (literal $ must be written as $$)\n",
            "bad $\n",
            "    ^ near here",
        ).to_owned()), lexer.read_var_value(&mut eval));
}

#[test]
fn test_lexer_comment_eof() {
    // Verify we don't run off the end of the string when the EOF is
    // mid-comment.
    let mut lexer = Lexer::new_with_input(b"# foo");
    let token = lexer.read_token();
    assert_eq!(LexerToken::ERROR, token);
}


#[test]
fn test_lexer_tabs() {
    // Verify we print a useful error on a disallowed character.
    let mut lexer = Lexer::new_with_input(b"   \tfoobar");
    let mut token;
    token = lexer.read_token();
    assert_eq!(LexerToken::INDENT, token);
    token = lexer.read_token();
    assert_eq!(LexerToken::ERROR, token);
    assert_eq!("tabs are not allowed, use spaces", lexer.describe_last_error());
}
