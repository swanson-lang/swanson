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

use std::iter::Peekable;

use crate::s0;
use crate::s0::Name;

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
            Parser::for_str(":").require_operator(":="),
            Err(ParseError::UnexpectedEnd)
        );
        assert_eq!(
            Parser::for_str("").require_operator("."),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

fn is_bare_name_character(ch: char) -> bool {
    match ch {
        'A'..='Z' | 'a'..='z' | '0'..='9' | '@' | '$' | '_' | '-' | '.' => true,
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

#[cfg(test)]
mod parse_bare_name_tests {
    use super::*;

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str("foo").parse_bare_name(),
            Ok(Name::new("foo"))
        );
        assert_eq!(
            Parser::for_str("foo123").parse_bare_name(),
            Ok(Name::new("foo123"))
        );
        assert_eq!(
            Parser::for_str("@foo").parse_bare_name(),
            Ok(Name::new("@foo"))
        );
        assert_eq!(
            Parser::for_str("foo(").parse_bare_name(),
            Ok(Name::new("foo"))
        );
        assert_eq!(
            Parser::for_str(",").parse_bare_name(),
            Err(ParseError::UnexpectedCharacter)
        );
        assert_eq!(
            Parser::for_str("").parse_bare_name(),
            Err(ParseError::UnexpectedEnd)
        );
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_name(&mut self) -> Result<Name, ParseError> {
        self.parse_bare_name()
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
mod parse_name_list_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_name_list(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse() {
        assert_eq!(Parser::for_str("()").parse_name_list(), Ok(vec![]));
        assert_eq!(
            Parser::for_str("(foo)").parse_name_list(),
            Ok(vec![Name::new("foo")])
        );
        assert_eq!(
            Parser::for_str("(foo,bar)").parse_name_list(),
            Ok(vec![Name::new("foo"), Name::new("bar")])
        );
        assert_eq!(
            Parser::for_str("( foo , bar ) ").parse_name_list(),
            Ok(vec![Name::new("foo"), Name::new("bar")])
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
        check_all_prefixes("(foo,bar)");
        check_all_prefixes("( foo , bar )");
    }
}

impl<I> Parser<I>
where
    I: Iterator<Item = char>,
{
    fn parse_statement(&mut self) -> Result<s0::Statement, ParseError> {
        let dest = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator("=")?;
        self.skip_whitespace();

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
        Ok(s0::Statement::create_atom(dest))
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
            branches.push(s0::BranchRef::new(branch_name, branch_target));
        }
        loop {
            self.skip_whitespace();
            let ch = self.require_peek()?;
            if ch == ';' {
                self.it.next();
                return Ok(s0::Statement::create_closure(dest, containing, branches));
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
            branches.push(s0::BranchRef::new(branch_name, branch_target));
        }
    }

    /// ``` s0
    /// [dest] = literal [content];
    /// ```
    fn parse_create_literal(&mut self, dest: Name) -> Result<s0::Statement, ParseError> {
        self.require_keyword("literal")?;
        self.skip_whitespace();
        let content = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s0::Statement::create_literal(
            dest,
            content.as_ref().to_vec(),
        ))
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
        Ok(s0::Statement::rename(dest, source))
    }
}

#[cfg(test)]
mod parse_statement_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_statement(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse_create_atom() {
        assert_eq!(
            Parser::for_str("foo = atom ; ").parse_statement(),
            Ok(s0::Statement::create_atom(Name::new("foo")))
        );
        assert_eq!(
            Parser::for_str("foo=atom;").parse_statement(),
            Ok(s0::Statement::create_atom(Name::new("foo")))
        );
        check_all_prefixes("foo=atom;");
    }

    #[test]
    fn can_parse_create_closure() {
        assert_eq!(
            Parser::for_str(concat!(
                "foo = closure containing ( foo , bar ) ",
                "branch true = @true , ",
                "branch false = @false ; "
            ))
            .parse_statement(),
            Ok(s0::Statement::create_closure(
                Name::new("foo"),
                vec![Name::new("foo"), Name::new("bar")],
                vec![
                    s0::BranchRef::new(Name::new("true"), Name::new("@true")),
                    s0::BranchRef::new(Name::new("false"), Name::new("@false")),
                ]
            ))
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo=closure containing(foo,bar)",
                "branch true=@true,",
                "branch false=@false;"
            ))
            .parse_statement(),
            Ok(s0::Statement::create_closure(
                Name::new("foo"),
                vec![Name::new("foo"), Name::new("bar")],
                vec![
                    s0::BranchRef::new(Name::new("true"), Name::new("@true")),
                    s0::BranchRef::new(Name::new("false"), Name::new("@false")),
                ]
            ))
        );
        check_all_prefixes("foo=closure containing(foo,bar)branch true=@true,branch false=@false;");
    }

    #[test]
    fn can_parse_create_literal() {
        assert_eq!(
            Parser::for_str("foo = literal bar ; ").parse_statement(),
            Ok(s0::Statement::create_literal(
                Name::new("foo"),
                "bar".as_bytes().to_vec()
            ))
        );
        assert_eq!(
            Parser::for_str("foo=literal bar;").parse_statement(),
            Ok(s0::Statement::create_literal(
                Name::new("foo"),
                "bar".as_bytes().to_vec()
            ))
        );
        check_all_prefixes("foo=literal bar;");
    }

    #[test]
    fn can_parse_rename() {
        assert_eq!(
            Parser::for_str("foo = rename bar ; ").parse_statement(),
            Ok(s0::Statement::rename(Name::new("foo"), Name::new("bar")))
        );
        assert_eq!(
            Parser::for_str("foo=rename bar;").parse_statement(),
            Ok(s0::Statement::rename(Name::new("foo"), Name::new("bar")))
        );
        check_all_prefixes("foo=rename bar;");
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
        Ok(s0::Invocation::new(target, branch))
    }
}

#[cfg(test)]
mod parse_invocation_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_invocation(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str("-> target branch ; ").parse_invocation(),
            Ok(s0::Invocation::new(
                Name::new("target"),
                Name::new("branch")
            ))
        );
        assert_eq!(
            Parser::for_str("->target branch;").parse_invocation(),
            Ok(s0::Invocation::new(
                Name::new("target"),
                Name::new("branch")
            ))
        );
        check_all_prefixes("->target branch;");
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
    fn parse_block(&mut self) -> Result<s0::Block, ParseError> {
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
            statements.push(self.parse_statement()?);
            self.skip_whitespace();
        }
        let invocation = self.parse_invocation()?;
        self.skip_whitespace();
        self.require_operator("}")?;
        Ok(s0::Block::new(
            name, containing, receiving, statements, invocation,
        ))
    }
}

#[cfg(test)]
mod parse_block_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_block(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str(concat!(
                "block_name: ",
                "containing (closed_over) ",
                "receiving (input) ",
                "{",
                "  @lit = literal foo; ",
                "  @atom = atom; ",
                "  -> closed_over branch; ",
                "}",
            ))
            .parse_block(),
            Ok(s0::Block::new(
                Name::new("block_name"),
                vec![Name::new("closed_over")],
                vec![Name::new("input")],
                vec![
                    s0::Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                    s0::Statement::create_atom(Name::new("@atom")),
                ],
                s0::Invocation::new(Name::new("closed_over"), Name::new("branch"))
            ))
        );
        assert_eq!(
            Parser::for_str(concat!(
                "block_name:",
                "containing(closed_over)",
                "receiving(input)",
                "{",
                "@lit=literal foo;",
                "@atom=atom;",
                "->closed_over branch;",
                "}",
            ))
            .parse_block(),
            Ok(s0::Block::new(
                Name::new("block_name"),
                vec![Name::new("closed_over")],
                vec![Name::new("input")],
                vec![
                    s0::Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                    s0::Statement::create_atom(Name::new("@atom")),
                ],
                s0::Invocation::new(Name::new("closed_over"), Name::new("branch"))
            ))
        );
        check_all_prefixes(concat!(
            "block_name: ",
            "containing (closed_over) ",
            "receiving (input) ",
            "{",
            "  @lit = literal foo; ",
            "  @atom = atom; ",
            "  -> closed_over branch; ",
            "}",
        ));
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
    pub(crate) fn parse_module(&mut self) -> Result<s0::ParsedModule, ParseError> {
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
            let block = self.parse_block()?;
            blocks.push(block);
        }
    }
}

#[cfg(test)]
mod parse_module_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_module(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str(concat!(
                "module @mod {",
                "  @block: ",
                "    containing (closed_over) ",
                "    receiving (input) ",
                "    {",
                "      @lit = literal foo; ",
                "      @atom = atom; ",
                "      -> closed_over branch; ",
                "    }",
                "}",
            ))
            .parse_module(),
            Ok(s0::ParsedModule::new(
                Name::new("@mod"),
                vec![s0::Block::new(
                    Name::new("@block"),
                    vec![Name::new("closed_over")],
                    vec![Name::new("input")],
                    vec![
                        s0::Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                        s0::Statement::create_atom(Name::new("@atom")),
                    ],
                    s0::Invocation::new(Name::new("closed_over"), Name::new("branch"))
                )]
            ))
        );
        assert_eq!(
            Parser::for_str(concat!(
                "module @mod{",
                "@block:",
                "containing(closed_over)",
                "receiving(input)",
                "{",
                "@lit=literal foo;",
                "@atom=atom;",
                "->closed_over branch;",
                "}",
                "}",
            ))
            .parse_module(),
            Ok(s0::ParsedModule::new(
                Name::new("@mod"),
                vec![s0::Block::new(
                    Name::new("@block"),
                    vec![Name::new("closed_over")],
                    vec![Name::new("input")],
                    vec![
                        s0::Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                        s0::Statement::create_atom(Name::new("@atom")),
                    ],
                    s0::Invocation::new(Name::new("closed_over"), Name::new("branch"))
                )]
            ))
        );
        check_all_prefixes(concat!(
            "module @mod {",
            "  @block: ",
            "    containing (closed_over) ",
            "    receiving (input) ",
            "    {",
            "      @lit = literal foo; ",
            "      @atom = atom; ",
            "      -> closed_over branch; ",
            "    }",
            "}",
        ));
    }
}
