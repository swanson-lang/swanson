// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2020, swanson authors.
//
// Licensed under the Apache License, Version 2.0 (the "License"); you may not use this file except
// in compliance with the License.  You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software distributed under the
// License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
// express or implied.  See the License for the specific language governing permissions and
// limitations under the License.
// ------------------------------------------------------------------------------------------------

use std::fmt::Debug;
use std::iter::Peekable;

use crate::s0;
use crate::s0::Name;
use crate::s1;

/// Indicates that an error occurred while trying to parse the content of an S₀ program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    /// The parser encountered a character that wasn't valid at the current position in the
    /// program.
    UnexpectedCharacter,
    /// The parser encountered the end of the program when it wasn't expecting to.
    UnexpectedEnd,
}

pub(crate) struct Parser<I>
where
    I: Iterator<Item = char>,
{
    it: Peekable<I>,
}

impl Parser<std::str::Chars<'_>> {
    pub(crate) fn for_str(input: &str) -> Parser<std::str::Chars<'_>> {
        Parser {
            it: input.chars().peekable(),
        }
    }
}

//-------------------------------------------------------------------------------------------------
// Common stuff

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn require_next(&mut self) -> Result<char, ParseError> {
        self.it.next().ok_or(ParseError::UnexpectedEnd)
    }

    fn require_peek(&mut self) -> Result<char, ParseError> {
        self.it.peek().copied().ok_or(ParseError::UnexpectedEnd)
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn skip_whitespace(&mut self) {
        while let Some(ch) = self.it.peek() {
            if !ch.is_ascii_whitespace() {
                return;
            }
            self.it.next();
        }
    }
}

#[cfg(test)]
mod skip_whitespace_test {
    use super::*;

    fn remaining(input: &str) -> String {
        let mut parser = Parser::for_str(input);
        parser.skip_whitespace();
        parser.it.collect()
    }

    #[test]
    fn can_parse() {
        assert_eq!(remaining(""), "");
        assert_eq!(remaining(" "), "");
        assert_eq!(remaining("\x0c"), ""); // \f
        assert_eq!(remaining("\n"), "");
        assert_eq!(remaining("\r"), "");
        assert_eq!(remaining("\t"), "");
        assert_eq!(remaining("   "), "");
        assert_eq!(remaining("   foo"), "foo");
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn require_character(&mut self, expected: char) -> Result<(), ParseError> {
        let ch = self.require_next()?;
        if ch != expected {
            return Err(ParseError::UnexpectedCharacter);
        }
        Ok(())
    }
}

#[cfg(test)]
mod require_character_tests {
    use super::*;

    #[test]
    fn can_parse() {
        assert_eq!(Parser::for_str("a").require_character('a'), Ok(()));
        assert_eq!(Parser::for_str("ab").require_character('a'), Ok(()));
        assert_eq!(
            Parser::for_str("b").require_character('a'),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("").require_character('a'),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn require_keyword(&mut self, expected: &str) -> Result<(), ParseError> {
        for expected in expected.chars() {
            self.require_character(expected)?;
        }
        if let Some(ch) = self.it.peek() {
            if ch.is_ascii_alphabetic() {
                return Err(ParseError::UnexpectedCharacter);
            }
        }
        Ok(())
    }
}

#[cfg(test)]
mod require_keyword_tests {
    use super::*;

    #[test]
    fn can_parse() {
        assert_eq!(Parser::for_str("foo").require_keyword("foo"), Ok(()));
        assert_eq!(Parser::for_str("foo ").require_keyword("foo"), Ok(()));
        assert_eq!(Parser::for_str("foo,").require_keyword("foo"), Ok(()));
        assert_eq!(Parser::for_str("foo;").require_keyword("foo"), Ok(()));
        assert_eq!(Parser::for_str("foo=").require_keyword("foo"), Ok(()));
        assert_eq!(
            Parser::for_str("foobar").require_keyword("foo"),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("bar").require_keyword("foo"),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("fo").require_keyword("foo"),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            Parser::for_str("").require_keyword("foo"),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn require_operator(&mut self, expected: &str) -> Result<(), ParseError> {
        for expected in expected.chars() {
            self.require_character(expected)?;
        }
        Ok(())
    }
}

#[cfg(test)]
mod require_operator_tests {
    use super::*;

    #[test]
    fn can_parse() {
        assert_eq!(Parser::for_str(".").require_operator("."), Ok(()));
        assert_eq!(Parser::for_str(". ").require_operator("."), Ok(()));
        assert_eq!(Parser::for_str(".,").require_operator("."), Ok(()));
        assert_eq!(Parser::for_str(".;").require_operator("."), Ok(()));
        assert_eq!(Parser::for_str(".=").require_operator("."), Ok(()));
        assert_eq!(Parser::for_str(".bar").require_operator("."), Ok(()));
        assert_eq!(
            Parser::for_str(",").require_operator("."),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str(":.").require_operator(":="),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str(":").require_operator(":="),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            Parser::for_str("").require_operator("."),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_hex_char(&mut self) -> Result<u32, ParseError> {
        self.require_next()?
            .to_digit(16)
            .ok_or(ParseError::UnexpectedCharacter)
    }

    fn parse_hex_byte(&mut self) -> Result<u8, ParseError> {
        let upper_nybble = self.parse_hex_char()? as u8;
        let lower_nybble = self.parse_hex_char()? as u8;
        Ok(upper_nybble << 4 | lower_nybble)
    }

    fn parse_binary_literal(&mut self) -> Result<Vec<u8>, ParseError> {
        let mut result = Vec::new();
        self.require_operator("\"")?;
        loop {
            let ch = self.require_next()?;
            match ch {
                '"' => return Ok(result),
                '\\' => {
                    let escape = self.require_next()?;
                    match escape {
                        '\\' => result.push(b'\\'),
                        '"' => result.push(b'"'),
                        'f' => result.push(b'\x0c'),
                        'n' => result.push(b'\n'),
                        'r' => result.push(b'\r'),
                        't' => result.push(b'\t'),
                        'v' => result.push(b'\x0b'),
                        'x' => result.push(self.parse_hex_byte()?),
                        _ => return Err(ParseError::UnexpectedCharacter),
                    }
                }
                _ if ch.is_ascii() => result.push(ch as u8),
                _ => return Err(ParseError::UnexpectedCharacter),
            }
        }
    }
}

#[cfg(test)]
mod parse_binary_literal_tests {
    use super::*;

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str(r#""foo""#).parse_binary_literal(),
            Ok(b"foo".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""foo123""#).parse_binary_literal(),
            Ok(b"foo123".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""@foo""#).parse_binary_literal(),
            Ok(b"@foo".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""foo"("#).parse_binary_literal(),
            Ok(b"foo".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\"""#).parse_binary_literal(),
            Ok(b"\"".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\\""#).parse_binary_literal(),
            Ok(b"\\".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\f""#).parse_binary_literal(),
            Ok(b"\x0c".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\n""#).parse_binary_literal(),
            Ok(b"\n".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\r""#).parse_binary_literal(),
            Ok(b"\r".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\t""#).parse_binary_literal(),
            Ok(b"\t".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\v""#).parse_binary_literal(),
            Ok(b"\x0b".to_vec())
        );
        assert_eq!(
            Parser::for_str(r#""\x57""#).parse_binary_literal(),
            Ok(b"\x57".to_vec())
        );
        assert_eq!(
            Parser::for_str(",").parse_binary_literal(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("").parse_binary_literal(),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            Parser::for_str(r#""foo"#).parse_binary_literal(),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

fn is_bare_name_character(ch: char) -> bool {
    match ch {
        'A'..='Z' | 'a'..='z' | '0'..='9' | '@' | '$' | '_' | '.' => true,
        _ => false,
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_bare_name(&mut self) -> Result<Name, ParseError> {
        let ch = self.require_next()?;
        if !is_bare_name_character(ch) {
            return Err(ParseError::UnexpectedCharacter);
        }
        let mut name = ch.to_string();

        while let Some(ch) = self.it.peek() {
            if !is_bare_name_character(*ch) {
                break;
            }
            name.push(*ch);
            self.it.next();
        }

        Ok(Name::new(name))
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_name(&mut self) -> Result<Name, ParseError> {
        if let Some(ch) = self.it.peek() {
            match ch {
                '"' => self.parse_binary_literal().map(Name::new),
                _ => self.parse_bare_name(),
            }
        } else {
            Err(ParseError::UnexpectedEnd)
        }
    }
}

#[cfg(test)]
mod parse_name_tests {
    use super::*;

    #[test]
    fn can_parse_bare_names() {
        assert_eq!(Parser::for_str("foo").parse_name(), Ok(Name::new("foo")));
        assert_eq!(
            Parser::for_str("foo123").parse_name(),
            Ok(Name::new("foo123"))
        );
        assert_eq!(Parser::for_str("@foo").parse_name(), Ok(Name::new("@foo")));
        assert_eq!(Parser::for_str("foo(").parse_name(), Ok(Name::new("foo")));
        assert_eq!(
            Parser::for_str(",").parse_name(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("").parse_name(),
            Err(ParseError::UnexpectedEnd)
        );
    }

    #[test]
    fn can_parse_binary_names() {
        assert_eq!(
            Parser::for_str(r#""foo""#).parse_name(),
            Ok(Name::new("foo"))
        );
        assert_eq!(
            Parser::for_str(r#""foo123""#).parse_name(),
            Ok(Name::new("foo123"))
        );
        assert_eq!(
            Parser::for_str(r#""@foo""#).parse_name(),
            Ok(Name::new("@foo"))
        );
        assert_eq!(
            Parser::for_str(r#""foo"("#).parse_name(),
            Ok(Name::new("foo"))
        );
        assert_eq!(Parser::for_str(r#""\"""#).parse_name(), Ok(Name::new("\"")));
        assert_eq!(Parser::for_str(r#""\\""#).parse_name(), Ok(Name::new("\\")));
        assert_eq!(
            Parser::for_str(r#""\f""#).parse_name(),
            Ok(Name::new("\x0c"))
        );
        assert_eq!(Parser::for_str(r#""\n""#).parse_name(), Ok(Name::new("\n")));
        assert_eq!(Parser::for_str(r#""\r""#).parse_name(), Ok(Name::new("\r")));
        assert_eq!(Parser::for_str(r#""\t""#).parse_name(), Ok(Name::new("\t")));
        assert_eq!(
            Parser::for_str(r#""\v""#).parse_name(),
            Ok(Name::new("\x0b"))
        );
        assert_eq!(
            Parser::for_str(r#""\x57""#).parse_name(),
            Ok(Name::new("\x57"))
        );
        assert_eq!(
            Parser::for_str(",").parse_name(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("").parse_name(),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            Parser::for_str(r#""foo"#).parse_name(),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_name_list(&mut self) -> Result<Vec<Name>, ParseError> {
        let mut result = Vec::new();

        self.require_operator("(")?;
        self.skip_whitespace();
        let ch = self.require_peek()?;
        if ch == ')' {
            self.it.next();
            return Ok(result);
        }
        result.push(self.parse_name()?);

        loop {
            self.skip_whitespace();
            let ch = self.require_peek()?;
            if ch == ')' {
                self.it.next();
                return Ok(result);
            }
            self.require_operator(",")?;
            self.skip_whitespace();
            result.push(self.parse_name()?);
        }
    }
}

#[cfg(test)]
fn check_all_prefixes<'r, F, T>(f: F, input: &'r str)
where
    F: Fn(&mut Parser<std::str::Chars<'r>>) -> Result<T, ParseError>,
    T: Debug,
{
    for len in 0..input.len() {
        assert_eq!(
            f(&mut Parser::for_str(&input[0..len])).err(),
            Some(ParseError::UnexpectedEnd)
        );
    }
}

#[cfg(test)]
mod parse_name_list_tests {
    use super::*;

    fn name_array(names: Vec<&str>) -> Vec<Name> {
        names.into_iter().map(Name::from).collect()
    }

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str("()").parse_name_list(),
            Ok(name_array(vec![]))
        );
        assert_eq!(
            Parser::for_str("(foo)").parse_name_list(),
            Ok(name_array(vec!["foo"]))
        );
        assert_eq!(
            Parser::for_str("(foo,bar)").parse_name_list(),
            Ok(name_array(vec!["foo", "bar"]))
        );
        assert_eq!(
            Parser::for_str("( foo , bar ) ").parse_name_list(),
            Ok(name_array(vec!["foo", "bar"]))
        );
        assert_eq!(
            Parser::for_str("(foo bar)").parse_name_list(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("(foo,,bar)").parse_name_list(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("(,foo)").parse_name_list(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("(foo,)").parse_name_list(),
            Err(ParseError::UnexpectedCharacter)
        );
        check_all_prefixes(Parser::parse_name_list, "(foo,bar)");
        check_all_prefixes(Parser::parse_name_list, "( foo , bar )");
    }
}

//-------------------------------------------------------------------------------------------------
// S₀

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_s0_statement(&mut self) -> Result<s0::Statement, ParseError> {
        let dest = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator("=")?;
        self.skip_whitespace();
        self.parse_s0_statement_inner(dest)
    }

    fn parse_s0_statement_inner(&mut self, dest: Name) -> Result<s0::Statement, ParseError> {
        let ch = self.require_peek()?;
        match ch {
            'a' => self.parse_create_atom(dest),
            'c' => self.parse_create_closure(dest),
            'l' => self.parse_create_literal(dest),
            'r' => self.parse_rename(dest),
            _ => Err(ParseError::UnexpectedCharacter),
        }
    }

    /// ``` s0
    /// [dest] = atom;
    /// ```
    fn parse_create_atom(&mut self, dest: Name) -> Result<s0::Statement, ParseError> {
        self.require_keyword("atom")?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s0::CreateAtom { dest }.into())
    }

    /// ``` s0
    /// [dest] = closure containing ([names],...)
    ///   branch [name] = [name],
    ///   ...
    ///   branch [name] = [name];
    /// ```
    fn parse_create_closure(&mut self, dest: Name) -> Result<s0::Statement, ParseError> {
        self.require_keyword("closure")?;
        self.skip_whitespace();
        self.require_keyword("containing")?;
        self.skip_whitespace();
        let containing = self.parse_name_list()?;
        let mut branches = Vec::new();
        {
            self.skip_whitespace();
            self.require_keyword("branch")?;
            self.skip_whitespace();
            let branch_name = self.parse_name()?;
            self.skip_whitespace();
            self.require_operator("=")?;
            self.skip_whitespace();
            let branch_target = self.parse_name()?;
            branches.push(s0::BranchRef {
                branch_name,
                block_name: branch_target,
                resolved: 0,
            });
        }
        loop {
            self.skip_whitespace();
            let ch = self.require_peek()?;
            if ch == ';' {
                self.it.next();
                return Ok(s0::CreateClosure {
                    dest,
                    close_over: containing,
                    branches,
                }
                .into());
            }

            self.require_operator(",")?;
            self.skip_whitespace();
            self.require_keyword("branch")?;
            self.skip_whitespace();
            let branch_name = self.parse_name()?;
            self.skip_whitespace();
            self.require_operator("=")?;
            self.skip_whitespace();
            let branch_target = self.parse_name()?;
            branches.push(s0::BranchRef {
                branch_name,
                block_name: branch_target,
                resolved: 0,
            });
        }
    }

    /// ``` s0
    /// [dest] = literal [content];
    /// ```
    fn parse_create_literal(&mut self, dest: Name) -> Result<s0::Statement, ParseError> {
        self.require_keyword("literal")?;
        self.skip_whitespace();
        let value = self.parse_binary_literal()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s0::CreateLiteral { dest, value }.into())
    }

    /// ``` s0
    /// [dest] = rename [source];
    /// ```
    fn parse_rename(&mut self, dest: Name) -> Result<s0::Statement, ParseError> {
        self.require_keyword("rename")?;
        self.skip_whitespace();
        let source = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s0::Rename { dest, source }.into())
    }
}

#[cfg(test)]
fn remove_whitespace(source: &str) -> String {
    use regex::Regex;
    let before_re = Regex::new(r"(\W)\s+").unwrap();
    let after_re = Regex::new(r"\s+(\W)").unwrap();
    after_re
        .replace_all(&before_re.replace_all(source, "$1"), "$1")
        .into_owned()
}

#[cfg(test)]
fn create_atom(dest: &str) -> s0::CreateAtom {
    s0::CreateAtom { dest: dest.into() }
}

#[cfg(test)]
fn create_closure(
    dest: &str,
    close_over: Vec<&str>,
    branches: Vec<(&str, &str)>,
) -> s0::CreateClosure {
    s0::CreateClosure {
        dest: dest.into(),
        close_over: close_over.into_iter().map(Name::from).collect(),
        branches: branches
            .into_iter()
            .map(|(branch_name, block_name)| s0::BranchRef {
                branch_name: branch_name.into(),
                block_name: block_name.into(),
                resolved: 0,
            })
            .collect(),
    }
}

#[cfg(test)]
fn create_literal(dest: &str, value: &[u8]) -> s0::CreateLiteral {
    s0::CreateLiteral {
        dest: dest.into(),
        value: value.to_vec(),
    }
}

#[cfg(test)]
fn rename(dest: &str, source: &str) -> s0::Rename {
    s0::Rename {
        dest: dest.into(),
        source: source.into(),
    }
}

#[cfg(test)]
mod parse_s0_statement_tests {
    use super::*;

    fn check_statement<S>(input: &str, expected: S)
    where
        S: Into<s0::Statement>,
    {
        let input = input.trim();
        let expected = expected.into();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_s0_statement()
            .expect("Expected a valid S₀ statement");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s0_statement, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_s0_statement()
            .expect("Expected a valid S₀ statement");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s0_statement, &without_whitespace);
    }

    #[test]
    fn can_parse_create_atom() {
        check_statement(r#" dest = atom ; "#, create_atom("dest"));
        check_statement(r#" "dest" = atom ; "#, create_atom("dest"));
    }

    #[test]
    fn can_parse_create_closure() {
        check_statement(
            r#"
                dest = closure containing ( foo , bar )
                    branch true = @true ,
                    branch false = @false ;
            "#,
            create_closure(
                "dest",
                vec!["foo", "bar"],
                vec![("true", "@true"), ("false", "@false")],
            ),
        );
        check_statement(
            r#"
                "dest" = closure containing ( "foo\n" , bar )
                    branch true = @true ,
                    branch false = @false ;
            "#,
            create_closure(
                "dest",
                vec!["foo\n", "bar"],
                vec![("true", "@true"), ("false", "@false")],
            ),
        );
    }

    #[test]
    fn can_parse_create_literal() {
        check_statement(r#" dest = literal "bar" ;"#, create_literal("dest", b"bar"));
        check_statement(
            r#" "dest" = literal "bar" ;"#,
            create_literal("dest", b"bar"),
        );
    }

    #[test]
    fn can_parse_rename() {
        check_statement(r#" dest = rename source ;"#, rename("dest", "source"));
        check_statement(r#" dest = rename "source" ;"#, rename("dest", "source"));
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    /// ``` s0
    /// -> [name] [name];
    /// ```
    fn parse_invocation(&mut self) -> Result<s0::Invocation, ParseError> {
        self.require_operator("->")?;
        self.skip_whitespace();
        let target = self.parse_name()?;
        self.skip_whitespace();
        let branch = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s0::Invocation { target, branch })
    }
}

#[cfg(test)]
fn invocation(target: &str, branch: &str) -> s0::Invocation {
    s0::Invocation {
        target: target.into(),
        branch: branch.into(),
    }
}

#[cfg(test)]
mod parse_invocation_tests {
    use super::*;

    fn check_invocation(input: &str, expected: s0::Invocation) {
        let input = input.trim();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_invocation()
            .expect("Expected a valid S₀ invocation");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_invocation, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_invocation()
            .expect("Expected a valid S₀ invocation");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_invocation, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_invocation(r#"-> target branch ;"#, invocation("target", "branch"));
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    /// ``` s0
    /// [name]:
    /// containing ([names],...)
    /// receiving ([name],...)
    /// {
    ///   [statements]
    ///   [invocation]
    /// }
    /// ```
    fn parse_s0_block(&mut self) -> Result<s0::Block, ParseError> {
        let name = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(":")?;
        self.skip_whitespace();
        self.require_keyword("containing")?;
        self.skip_whitespace();
        let containing = self.parse_name_list()?;
        self.skip_whitespace();
        self.require_keyword("receiving")?;
        self.skip_whitespace();
        let receiving = self.parse_name_list()?;
        self.skip_whitespace();
        self.require_operator("{")?;
        self.skip_whitespace();
        let mut statements = Vec::new();
        while self.require_peek()? != '-' {
            statements.push(self.parse_s0_statement()?);
            self.skip_whitespace();
        }
        let invocation = self.parse_invocation()?;
        self.skip_whitespace();
        self.require_operator("}")?;
        Ok(s0::Block {
            name,
            containing,
            receiving,
            statements,
            invocation,
        })
    }
}

#[cfg(test)]
fn s0_block(
    name: &str,
    containing: Vec<&str>,
    receiving: Vec<&str>,
    statements: Vec<s0::Statement>,
    invocation: s0::Invocation,
) -> s0::Block {
    s0::Block {
        name: name.into(),
        containing: containing.into_iter().map(Name::from).collect(),
        receiving: receiving.into_iter().map(Name::from).collect(),
        statements,
        invocation,
    }
}

#[cfg(test)]
mod parse_s0_block_tests {
    use super::*;

    fn check_block(input: &str, expected: s0::Block) {
        let input = input.trim();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser.parse_s0_block().expect("Expected a valid S₀ block");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s0_block, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser.parse_s0_block().expect("Expected a valid S₀ block");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s0_block, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_block(
            r#"
                block_name:
                  containing (closed_over)
                  receiving (input)
                {
                    @lit = literal "foo";
                    @atom = atom;
                    -> closed_over branch;
                }
            "#,
            s0_block(
                "block_name",
                vec!["closed_over"],
                vec!["input"],
                vec![
                    create_literal("@lit", b"foo").into(),
                    create_atom("@atom").into(),
                ],
                invocation("closed_over", "branch"),
            ),
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    /// ``` s0
    /// module [name] {
    ///   [block]
    ///   ...
    /// }
    /// ```
    pub(crate) fn parse_s0_module(&mut self) -> Result<s0::ParsedModule, ParseError> {
        self.skip_whitespace();
        self.require_keyword("module")?;
        self.skip_whitespace();
        let name = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator("{")?;
        let mut blocks = Vec::new();
        loop {
            self.skip_whitespace();
            if self.require_peek()? == '}' {
                self.it.next();
                return Ok(s0::ParsedModule::new(name, blocks));
            }
            let block = self.parse_s0_block()?;
            blocks.push(block);
        }
    }
}

#[cfg(test)]
fn s0_module(name: &str, blocks: Vec<s0::Block>) -> s0::ParsedModule {
    s0::ParsedModule::new(name.into(), blocks)
}

#[cfg(test)]
mod parse_s0_module_tests {
    use super::*;

    fn check_module(input: &str, expected: s0::ParsedModule) {
        let input = input.trim();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_s0_module()
            .expect("Expected a valid S₀ module");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s0_module, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_s0_module()
            .expect("Expected a valid S₀ module");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s0_module, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_module(
            r#"
                module @mod {
                  @block:
                    containing (closed_over)
                    receiving (input)
                    {
                      @lit = literal "foo";
                      @atom = atom;
                      -> closed_over branch;
                    }
                }
            "#,
            s0_module(
                "@mod",
                vec![s0_block(
                    "@block",
                    vec!["closed_over"],
                    vec!["input"],
                    vec![
                        create_literal("@lit", b"foo").into(),
                        create_atom("@atom").into(),
                    ],
                    invocation("closed_over", "branch"),
                )],
            ),
        );
    }
}

//-------------------------------------------------------------------------------------------------
// S₁

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_named_parameter(&mut self) -> Result<s1::NamedParameter, ParseError> {
        let param_name = self.parse_name()?;
        self.skip_whitespace();
        let source = match self.it.peek() {
            Some(ch) if *ch == '<' => {
                self.require_operator("<-")?;
                self.skip_whitespace();
                Some(self.parse_name()?)
            }
            _ => None,
        };
        Ok(s1::NamedParameter { param_name, source })
    }
}

#[cfg(test)]
mod parse_named_parameter_tests {
    use super::*;

    #[test]
    fn can_parse() {
        let foo = s1::NamedParameter {
            param_name: Name::new("foo"),
            source: None,
        };
        let foo_from_bar = s1::NamedParameter {
            param_name: Name::new("foo"),
            source: Some(Name::new("bar")),
        };
        assert_eq!(
            Parser::for_str("foo").parse_named_parameter(),
            Ok(foo.clone())
        );
        assert_eq!(
            Parser::for_str("foo <- bar").parse_named_parameter(),
            Ok(foo_from_bar.clone())
        );
        assert_eq!(
            Parser::for_str("foo<-bar").parse_named_parameter(),
            Ok(foo_from_bar.clone())
        );
        assert_eq!(
            Parser::for_str("foo <=").parse_named_parameter(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("foo <-").parse_named_parameter(),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_named_parameters(&mut self) -> Result<Vec<s1::NamedParameter>, ParseError> {
        let mut result = Vec::new();

        self.require_operator("(")?;
        self.skip_whitespace();
        let ch = self.require_peek()?;
        if ch == ')' {
            self.it.next();
            return Ok(result);
        }
        result.push(self.parse_named_parameter()?);

        loop {
            self.skip_whitespace();
            let ch = self.require_peek()?;
            if ch == ')' {
                self.it.next();
                return Ok(result);
            }
            self.require_operator(",")?;
            self.skip_whitespace();
            result.push(self.parse_named_parameter()?);
        }
    }
}

#[cfg(test)]
mod parse_named_parameters_tests {
    use super::*;

    #[test]
    fn can_parse() {
        let foo = s1::NamedParameter {
            param_name: Name::new("foo"),
            source: None,
        };
        let bar = s1::NamedParameter {
            param_name: Name::new("bar"),
            source: None,
        };
        let foo_from_bar = s1::NamedParameter {
            param_name: Name::new("foo"),
            source: Some(Name::new("bar")),
        };
        assert_eq!(Parser::for_str("()").parse_named_parameters(), Ok(vec![]));
        assert_eq!(
            Parser::for_str("(foo)").parse_named_parameters(),
            Ok(vec![foo.clone()])
        );
        assert_eq!(
            Parser::for_str("(foo<-bar)").parse_named_parameters(),
            Ok(vec![foo_from_bar.clone()])
        );
        assert_eq!(
            Parser::for_str("(foo,bar)").parse_named_parameters(),
            Ok(vec![foo.clone(), bar.clone()])
        );
        assert_eq!(
            Parser::for_str("(foo<-bar,bar)").parse_named_parameters(),
            Ok(vec![foo_from_bar.clone(), bar.clone()])
        );
        assert_eq!(
            Parser::for_str("( foo , bar ) ").parse_named_parameters(),
            Ok(vec![foo.clone(), bar.clone()])
        );
        assert_eq!(
            Parser::for_str("( foo <- bar , bar ) ").parse_named_parameters(),
            Ok(vec![foo_from_bar.clone(), bar.clone()])
        );
        assert_eq!(
            Parser::for_str("(foo bar)").parse_named_parameters(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("(foo,,bar)").parse_named_parameters(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("(,foo)").parse_named_parameters(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("(foo,)").parse_named_parameters(),
            Err(ParseError::UnexpectedCharacter)
        );
        check_all_prefixes(Parser::parse_named_parameters, "(foo,bar)");
        check_all_prefixes(Parser::parse_named_parameters, "(foo<-bar,baz)");
        check_all_prefixes(Parser::parse_named_parameters, "(baz,foo<-bar)");
        check_all_prefixes(Parser::parse_named_parameters, "( foo , bar )");
        check_all_prefixes(Parser::parse_named_parameters, "( foo <- bar , baz )");
        check_all_prefixes(Parser::parse_named_parameters, "( baz , foo <- bar )");
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_closure_parameter(&mut self) -> Result<s1::ClosureParameter, ParseError> {
        let param_name = self.parse_name()?;
        self.skip_whitespace();
        let close_over = self.parse_name_list()?;
        self.skip_whitespace();
        let mut branches = Vec::new();
        branches.push(self.parse_closure_parameter_branch()?);
        self.skip_whitespace();
        while self.require_peek()? == ':' {
            branches.push(self.parse_closure_parameter_branch()?);
            self.skip_whitespace();
        }
        Ok(s1::ClosureParameter {
            param_name,
            close_over,
            branches,
        })
    }

    fn parse_closure_parameter_branch(&mut self) -> Result<s1::ClosureParameterBranch, ParseError> {
        self.require_operator("::")?;
        let branch_name = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator("->")?;
        self.skip_whitespace();
        let receiving = self.parse_name_list()?;
        self.skip_whitespace();
        let statements = self.parse_s1_statement_list()?;
        Ok(s1::ClosureParameterBranch {
            branch_name,
            receiving,
            statements,
        })
    }
}

#[cfg(test)]
fn closure_parameter(
    param_name: &str,
    close_over: Vec<&str>,
    branches: Vec<(&str, Vec<&str>, Vec<s1::Statement>)>,
) -> s1::ClosureParameter {
    s1::ClosureParameter {
        param_name: param_name.into(),
        close_over: close_over.into_iter().map(Name::from).collect(),
        branches: branches
            .into_iter()
            .map(
                |(branch_name, receiving, statements)| s1::ClosureParameterBranch {
                    branch_name: branch_name.into(),
                    receiving: receiving.into_iter().map(Name::from).collect(),
                    statements,
                },
            )
            .collect(),
    }
}

#[cfg(test)]
mod parse_closure_parameter_tests {
    use super::*;

    fn check_closure_parameter(input: &str, expected: s1::ClosureParameter) {
        let input = input.trim();

        // First try parsing the input as-is.  The trailing "~" is just the start of any clause
        // that can terminate the list of block parameters.
        let mut parser_input = input.to_string();
        parser_input.push('~');
        let mut parser = Parser::for_str(&parser_input);
        let actual = parser
            .parse_closure_parameter()
            .expect("Expected a valid S₁ closure parameter");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_closure_parameter, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let mut without_whitespace = remove_whitespace(input);
        without_whitespace.push('~');
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_closure_parameter()
            .expect("Expected a valid S₁ closure parameter");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_closure_parameter, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_closure_parameter(
            r#"foo ( ) ::bar -> ( ) { } "#,
            closure_parameter("foo", vec![], vec![("bar", vec![], vec![])]),
        );
    }
}

fn is_result_or_continuation_char(ch: char) -> bool {
    match ch {
        '-' | '~' | '=' | ';' => true,
        _ => false,
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_closure_parameters(&mut self) -> Result<Vec<s1::ClosureParameter>, ParseError> {
        let mut result = Vec::new();
        while !is_result_or_continuation_char(self.require_peek()?) {
            result.push(self.parse_closure_parameter()?);
            self.skip_whitespace();
        }
        Ok(result)
    }
}

#[cfg(test)]
mod parse_closure_parameters_tests {
    use super::*;

    fn check_closure_parameters(input: &str, expected: Vec<s1::ClosureParameter>) {
        let input = input.trim();

        // First try parsing the input as-is.  The trailing "~" is just the start of any clause
        // that can terminate the list of block parameters.
        let mut parser_input = input.to_string();
        parser_input.push('~');
        let mut parser = Parser::for_str(&parser_input);
        let actual = parser
            .parse_closure_parameters()
            .expect("Expected a valid S₁ closure parameter list");
        assert_eq!(expected, actual);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let mut without_whitespace = remove_whitespace(input);
        without_whitespace.push('~');
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_closure_parameters()
            .expect("Expected a valid S₁ closure parameter list");
        assert_eq!(expected, actual);
    }

    #[test]
    fn can_parse() {
        check_closure_parameters(
            r#"foo ( ) ::bar -> ( ) { } "#,
            vec![closure_parameter(
                "foo",
                vec![],
                vec![("bar", vec![], vec![])],
            )],
        );
        check_closure_parameters(
            r#"
                foo ( ) ::bar -> ( ) { }
                foo ( ) ::bar -> ( ) { }
            "#,
            vec![
                closure_parameter("foo", vec![], vec![("bar", vec![], vec![])]),
                closure_parameter("foo", vec![], vec![("bar", vec![], vec![])]),
            ],
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_call_results(&mut self) -> Result<Vec<Name>, ParseError> {
        let mut result = Vec::new();
        self.require_operator("->")?;
        self.skip_whitespace();
        self.require_operator("(")?;
        self.skip_whitespace();
        result.push(self.parse_name()?);
        self.skip_whitespace();
        while self.require_peek()? == ',' {
            self.it.next();
            self.skip_whitespace();
            result.push(self.parse_name()?);
            self.skip_whitespace();
        }
        self.require_operator(")")?;
        Ok(result)
    }
}

#[cfg(test)]
mod parse_call_results_tests {
    use super::*;

    fn check_call_results(input: &str, expected: Vec<&str>) {
        let input = input.trim();
        let expected = expected.into_iter().map(Name::from).collect::<Vec<_>>();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_call_results()
            .expect("Expected a valid S₁ call result list");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_call_results, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_call_results()
            .expect("Expected a valid S₁ call result list");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_call_results, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_call_results(r#"-> ( foo ) "#, vec!["foo"]);
        check_call_results(r#"-> ( foo , bar ) "#, vec!["foo", "bar"]);
        // The result list can't be empty; if there are no results, just leave it out.
        assert_eq!(
            Parser::for_str("->()").parse_call_results(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("-> ( )").parse_call_results(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("-> (foo bar)").parse_call_results(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("-> (foo,,bar)").parse_call_results(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("-> (,foo)").parse_call_results(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("-> (foo,)").parse_call_results(),
            Err(ParseError::UnexpectedCharacter)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_call_continuation(&mut self) -> Result<s1::Continuation, ParseError> {
        match self.require_peek()? {
            ';' => {
                self.it.next();
                Ok(s1::Continuation::UseDefault)
            }
            '~' => self.parse_inside_parameter_continuation(),
            '=' => self.parse_as_parameter_continuation(),
            _ => Err(ParseError::UnexpectedCharacter),
        }
    }

    fn parse_inside_parameter_continuation(&mut self) -> Result<s1::Continuation, ParseError> {
        self.require_operator("~>")?;
        self.skip_whitespace();
        let param_name = self.parse_name()?;
        self.skip_whitespace();
        let mut name = None;
        let mut branch_name = None;
        if self.require_peek()? == '(' {
            self.it.next();
            self.skip_whitespace();
            name = Some(self.parse_name()?);
            if self.require_peek()? == ':' {
                self.require_operator("::")?;
                branch_name = Some(self.parse_name()?);
            }
            self.skip_whitespace();
            self.require_operator(")")?;
            self.skip_whitespace();
        }
        self.require_operator(";")?;
        Ok(s1::Continuation::InsideParameter {
            param_name,
            name,
            branch_name,
        })
    }

    fn parse_as_parameter_continuation(&mut self) -> Result<s1::Continuation, ParseError> {
        self.require_operator("=>")?;
        self.skip_whitespace();
        let param_name = self.parse_name()?;
        self.require_operator("::")?;
        let branch_name = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s1::Continuation::AsParameter {
            param_name,
            branch_name,
        })
    }
}

#[cfg(test)]
fn inside_parameter(
    param_name: &str,
    name: Option<&str>,
    branch_name: Option<&str>,
) -> s1::Continuation {
    s1::Continuation::InsideParameter {
        param_name: param_name.into(),
        name: name.map(Name::from),
        branch_name: branch_name.map(Name::from),
    }
}

#[cfg(test)]
fn as_parameter(param_name: &str, branch_name: &str) -> s1::Continuation {
    s1::Continuation::AsParameter {
        param_name: param_name.into(),
        branch_name: branch_name.into(),
    }
}

#[cfg(test)]
mod parse_call_continuation_tests {
    use super::*;

    fn check_call_continuation(input: &str, expected: s1::Continuation) {
        let input = input.trim();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_call_continuation()
            .expect("Expected a valid S₁ call continuation");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_call_continuation, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_call_continuation()
            .expect("Expected a valid S₁ call continuation");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_call_continuation, &without_whitespace);
    }

    #[test]
    fn can_parse_default() {
        check_call_continuation(r#" ; "#, s1::Continuation::UseDefault);
    }

    #[test]
    fn can_parse_inside_parameter() {
        check_call_continuation(r#" ~> foo ; "#, inside_parameter("foo", None, None));
        check_call_continuation(
            r#" ~> foo ( bar ) ; "#,
            inside_parameter("foo", Some("bar"), None),
        );
        check_call_continuation(
            r#" ~> foo ( bar::baz ) ; "#,
            inside_parameter("foo", Some("bar"), Some("baz")),
        );
    }

    #[test]
    fn can_parse_as_parameter() {
        check_call_continuation(r#" => foo::bar ;"#, as_parameter("foo", "bar"));
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_s1_call(&mut self, target: Name) -> Result<s1::Statement, ParseError> {
        self.require_operator("::")?;
        let branch = self.parse_name()?;
        self.skip_whitespace();
        let named_parameters = self.parse_named_parameters()?;
        self.skip_whitespace();
        let closure_parameters = self.parse_closure_parameters()?;
        self.skip_whitespace();
        let results = if self.require_peek()? == '-' {
            self.parse_call_results()?
        } else {
            Vec::new()
        };
        self.skip_whitespace();
        let continuation = self.parse_call_continuation()?;
        Ok(s1::Call {
            target,
            branch,
            named_parameters,
            closure_parameters,
            results,
            continuation,
        }
        .into())
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_s1_statement(&mut self) -> Result<s1::Statement, ParseError> {
        let dest = self.parse_name()?;
        if self.require_peek()? == ':' {
            self.parse_s1_call(dest)
        } else {
            self.skip_whitespace();
            self.require_operator("=")?;
            self.skip_whitespace();
            Ok(self.parse_s0_statement_inner(dest)?.into())
        }
    }
}

#[cfg(test)]
fn call(
    target: &str,
    branch: &str,
    named_parameters: Vec<(&str, Option<&str>)>,
    closure_parameters: Vec<s1::ClosureParameter>,
    results: Vec<&str>,
    continuation: s1::Continuation,
) -> s1::Call {
    s1::Call {
        target: target.into(),
        branch: branch.into(),
        named_parameters: named_parameters
            .into_iter()
            .map(|(param_name, source)| s1::NamedParameter {
                param_name: param_name.into(),
                source: source.map(Name::from),
            })
            .collect(),
        closure_parameters,
        results: results.into_iter().map(Name::from).collect(),
        continuation,
    }
}

#[cfg(test)]
mod parse_s1_statement_tests {
    use super::*;

    fn check_statement<S>(input: &str, expected: S)
    where
        S: Into<s1::Statement>,
    {
        let input = input.trim();
        let expected = expected.into();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_s1_statement()
            .expect("Expected a valid S₁ statement");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s1_statement, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_s1_statement()
            .expect("Expected a valid S₁ statement");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s1_statement, &without_whitespace);
    }

    #[test]
    fn can_parse_create_atom() {
        check_statement(r#" dest = atom ; "#, create_atom("dest"));
        check_statement(r#" "dest" = atom ; "#, create_atom("dest"));
    }

    #[test]
    fn can_parse_create_closure() {
        check_statement(
            r#"
                dest = closure containing ( foo , bar )
                    branch true = @true ,
                    branch false = @false ;
            "#,
            create_closure(
                "dest",
                vec!["foo", "bar"],
                vec![("true", "@true"), ("false", "@false")],
            ),
        );
        check_statement(
            r#"
                "dest" = closure containing ( "foo\n" , bar )
                    branch true = @true ,
                    branch false = @false ;
            "#,
            create_closure(
                "dest",
                vec!["foo\n", "bar"],
                vec![("true", "@true"), ("false", "@false")],
            ),
        );
    }

    #[test]
    fn can_parse_create_literal() {
        check_statement(r#" dest = literal "bar" ;"#, create_literal("dest", b"bar"));
        check_statement(
            r#" "dest" = literal "bar" ;"#,
            create_literal("dest", b"bar"),
        );
    }

    #[test]
    fn can_parse_rename() {
        check_statement(r#" dest = rename source ;"#, rename("dest", "source"));
        check_statement(r#" dest = rename "source" ;"#, rename("dest", "source"));
    }

    #[test]
    fn can_parse_call() {
        check_statement(
            r#" foo::bar ( ) ;"#,
            call(
                "foo",
                "bar",
                vec![],
                vec![],
                vec![],
                s1::Continuation::UseDefault,
            ),
        );

        check_statement(
            r#" foo::bar ( param1 , param2 <- var ) ; "#,
            call(
                "foo",
                "bar",
                vec![("param1", None), ("param2", Some("var"))],
                vec![],
                vec![],
                s1::Continuation::UseDefault,
            ),
        );

        check_statement(
            r#" foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ; "#,
            call(
                "foo",
                "bar",
                vec![("param1", None), ("param2", Some("var"))],
                vec![closure_parameter(
                    "block",
                    vec!["close1"],
                    vec![("branch", vec![], vec![])],
                )],
                vec![],
                s1::Continuation::UseDefault,
            ),
        );

        check_statement(
            r#"
                foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { }
                  -> ( result1 , result2 ) ;
            "#,
            call(
                "foo",
                "bar",
                vec![("param1", None), ("param2", Some("var"))],
                vec![closure_parameter(
                    "block",
                    vec!["close1"],
                    vec![("branch", vec![], vec![])],
                )],
                vec!["result1", "result2"],
                s1::Continuation::UseDefault,
            ),
        );

        check_statement(
            r#"
                foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { }
                  -> ( result1 , result2 ) ~> foo ;
            "#,
            call(
                "foo",
                "bar",
                vec![("param1", None), ("param2", Some("var"))],
                vec![closure_parameter(
                    "block",
                    vec!["close1"],
                    vec![("branch", vec![], vec![])],
                )],
                vec!["result1", "result2"],
                inside_parameter("foo", None, None),
            ),
        );

        check_statement(
            r#"
                foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { }
                  -> ( result1 , result2 ) ~> foo ( bar::baz ) ;
            "#,
            call(
                "foo",
                "bar",
                vec![("param1", None), ("param2", Some("var"))],
                vec![closure_parameter(
                    "block",
                    vec!["close1"],
                    vec![("branch", vec![], vec![])],
                )],
                vec!["result1", "result2"],
                inside_parameter("foo", Some("bar"), Some("baz")),
            ),
        );

        check_statement(
            r#"
                foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { }
                  -> ( result1 , result2 ) => foo::bar ;
            "#,
            call(
                "foo",
                "bar",
                vec![("param1", None), ("param2", Some("var"))],
                vec![closure_parameter(
                    "block",
                    vec!["close1"],
                    vec![("branch", vec![], vec![])],
                )],
                vec!["result1", "result2"],
                as_parameter("foo", "bar"),
            ),
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_s1_statement_list(&mut self) -> Result<Vec<s1::Statement>, ParseError> {
        let mut result = Vec::new();
        self.require_operator("{")?;
        self.skip_whitespace();
        while self.require_peek()? != '}' {
            result.push(self.parse_s1_statement()?);
            self.skip_whitespace();
        }
        self.it.next();
        Ok(result)
    }
}

#[cfg(test)]
mod parse_s1_statement_list_tests {
    use super::*;

    #[test]
    fn can_parse_s1_statement_list() {
        assert_eq!(
            Parser::for_str(concat!(
                "{",
                "  @lit = literal \"foo\"; ",
                "  @atom = atom; ",
                "}",
            ))
            .parse_s1_statement_list(),
            Ok(vec![
                create_literal("@lit", b"foo").into(),
                create_atom("@atom").into(),
            ])
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    /// ``` s0
    /// [name]:
    /// containing ([names],...)
    /// receiving ([name],...)
    /// {
    ///   [statements]
    ///   [invocation]
    /// }
    /// ```
    fn parse_s1_block(&mut self) -> Result<s1::Block, ParseError> {
        let name = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(":")?;
        self.skip_whitespace();
        self.require_keyword("containing")?;
        self.skip_whitespace();
        let containing = self.parse_name_list()?;
        self.skip_whitespace();
        self.require_keyword("receiving")?;
        self.skip_whitespace();
        let receiving = self.parse_name_list()?;
        self.skip_whitespace();
        let statements = self.parse_s1_statement_list()?;
        Ok(s1::Block {
            name,
            containing,
            receiving,
            statements,
        })
    }
}

#[cfg(test)]
fn s1_block(
    name: &str,
    containing: Vec<&str>,
    receiving: Vec<&str>,
    statements: Vec<s1::Statement>,
) -> s1::Block {
    s1::Block {
        name: name.into(),
        containing: containing.into_iter().map(Name::from).collect(),
        receiving: receiving.into_iter().map(Name::from).collect(),
        statements,
    }
}

#[cfg(test)]
mod parse_s1_block_tests {
    use super::*;

    fn check_block(input: &str, expected: s1::Block) {
        let input = input.trim();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser.parse_s1_block().expect("Expected a valid S₁ block");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s1_block, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser.parse_s1_block().expect("Expected a valid S₁ block");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s1_block, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_block(
            r#"
                block_name:
                  containing ( closed_over )
                  receiving ( input )
                {
                    @lit = literal "foo" ;
                    @atom = atom ;
                    foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ;
                }
            "#,
            s1_block(
                "block_name",
                vec!["closed_over"],
                vec!["input"],
                vec![
                    create_literal("@lit", b"foo").into(),
                    create_atom("@atom").into(),
                    call(
                        "foo",
                        "bar",
                        vec![("param1", None), ("param2", Some("var"))],
                        vec![closure_parameter(
                            "block",
                            vec!["close1"],
                            vec![("branch", vec![], vec![])],
                        )],
                        vec![],
                        s1::Continuation::UseDefault,
                    )
                    .into(),
                ],
            ),
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    pub(crate) fn parse_s1_module(&mut self) -> Result<s1::ParsedModule, ParseError> {
        self.skip_whitespace();
        self.require_keyword("module")?;
        self.skip_whitespace();
        let name = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator("{")?;
        let mut blocks = Vec::new();
        loop {
            self.skip_whitespace();
            if self.require_peek()? == '}' {
                self.it.next();
                return Ok(s1::ParsedModule::new(name, blocks));
            }
            let block = self.parse_s1_block()?;
            blocks.push(block);
        }
    }
}

#[cfg(test)]
fn s1_module(name: &str, blocks: Vec<s1::Block>) -> s1::ParsedModule {
    s1::ParsedModule::new(name.into(), blocks)
}

#[cfg(test)]
mod parse_s1_module_tests {
    use super::*;

    fn check_module(input: &str, expected: s1::ParsedModule) {
        let input = input.trim();

        // First try parsing the input as-is.
        let mut parser = Parser::for_str(input);
        let actual = parser
            .parse_s1_module()
            .expect("Expected a valid S₁ module");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s1_module, input);

        // Then parse it again with as much whitespace removed as possible.  (We can't remove
        // whitespace that occurs in between two words.)
        let without_whitespace = remove_whitespace(input);
        let mut parser = Parser::for_str(&without_whitespace);
        let actual = parser
            .parse_s1_module()
            .expect("Expected a valid S₁ module");
        assert_eq!(expected, actual);
        check_all_prefixes(Parser::parse_s1_module, &without_whitespace);
    }

    #[test]
    fn can_parse() {
        check_module(
            r#"
                module @module {
                    block_name:
                      containing ( closed_over )
                      receiving ( input )
                    {
                        @lit = literal "foo" ;
                        @atom = atom ;
                        foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ;
                    }
                }
            "#,
            s1_module(
                "@module",
                vec![s1_block(
                    "block_name",
                    vec!["closed_over"],
                    vec!["input"],
                    vec![
                        create_literal("@lit", b"foo").into(),
                        create_atom("@atom").into(),
                        call(
                            "foo",
                            "bar",
                            vec![("param1", None), ("param2", Some("var"))],
                            vec![closure_parameter(
                                "block",
                                vec!["close1"],
                                vec![("branch", vec![], vec![])],
                            )],
                            vec![],
                            s1::Continuation::UseDefault,
                        )
                        .into(),
                    ],
                )],
            ),
        );
    }
}
