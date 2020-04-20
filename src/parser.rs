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
        let content = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(s0::CreateLiteral {
            dest,
            value: content.as_ref().to_vec(),
        }
        .into())
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
mod parse_s0_statement_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_s0_statement(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse_create_atom() {
        assert_eq!(
            Parser::for_str("foo = atom ; ").parse_s0_statement(),
            Ok(s0::CreateAtom {
                dest: Name::new("foo"),
            }
            .into())
        );
        assert_eq!(
            Parser::for_str("foo=atom;").parse_s0_statement(),
            Ok(s0::CreateAtom {
                dest: Name::new("foo"),
            }
            .into())
        );
        check_all_prefixes("foo=atom;");
    }

    #[test]
    fn can_parse_create_closure() {
        assert_eq!(
            Parser::for_str(concat!(
                "foo = closure containing ( foo , bar ) ",
                "branch true = @true , ",
                "branch false = @false ; ",
            ))
            .parse_s0_statement(),
            Ok(s0::CreateClosure {
                dest: Name::new("foo"),
                close_over: vec![Name::new("foo"), Name::new("bar")],
                branches: vec![
                    s0::BranchRef {
                        branch_name: Name::new("true"),
                        block_name: Name::new("@true"),
                        resolved: 0,
                    },
                    s0::BranchRef {
                        branch_name: Name::new("false"),
                        block_name: Name::new("@false"),
                        resolved: 0,
                    },
                ],
            }
            .into())
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo=closure containing(foo,bar)",
                "branch true=@true,",
                "branch false=@false;",
            ))
            .parse_s0_statement(),
            Ok(s0::CreateClosure {
                dest: Name::new("foo"),
                close_over: vec![Name::new("foo"), Name::new("bar")],
                branches: vec![
                    s0::BranchRef {
                        branch_name: Name::new("true"),
                        block_name: Name::new("@true"),
                        resolved: 0,
                    },
                    s0::BranchRef {
                        branch_name: Name::new("false"),
                        block_name: Name::new("@false"),
                        resolved: 0,
                    },
                ],
            }
            .into())
        );
        check_all_prefixes("foo=closure containing(foo,bar)branch true=@true,branch false=@false;");
    }

    #[test]
    fn can_parse_create_literal() {
        assert_eq!(
            Parser::for_str("foo = literal bar ; ").parse_s0_statement(),
            Ok(s0::CreateLiteral {
                dest: Name::new("foo"),
                value: "bar".as_bytes().to_vec(),
            }
            .into())
        );
        assert_eq!(
            Parser::for_str("foo=literal bar;").parse_s0_statement(),
            Ok(s0::CreateLiteral {
                dest: Name::new("foo"),
                value: "bar".as_bytes().to_vec(),
            }
            .into())
        );
        check_all_prefixes("foo=literal bar;");
    }

    #[test]
    fn can_parse_rename() {
        assert_eq!(
            Parser::for_str("foo = rename bar ; ").parse_s0_statement(),
            Ok(s0::Rename {
                dest: Name::new("foo"),
                source: Name::new("bar"),
            }
            .into())
        );
        assert_eq!(
            Parser::for_str("foo=rename bar;").parse_s0_statement(),
            Ok(s0::Rename {
                dest: Name::new("foo"),
                source: Name::new("bar"),
            }
            .into())
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
        Ok(s0::Invocation { target, branch })
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
            Ok(s0::Invocation {
                target: Name::new("target"),
                branch: Name::new("branch"),
            })
        );
        assert_eq!(
            Parser::for_str("->target branch;").parse_invocation(),
            Ok(s0::Invocation {
                target: Name::new("target"),
                branch: Name::new("branch"),
            })
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
mod parse_s0_block_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_s0_block(),
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
            .parse_s0_block(),
            Ok(s0::Block {
                name: Name::new("block_name"),
                containing: vec![Name::new("closed_over")],
                receiving: vec![Name::new("input")],
                statements: vec![
                    s0::CreateLiteral {
                        dest: Name::new("@lit"),
                        value: "foo".as_bytes().to_vec(),
                    }
                    .into(),
                    s0::CreateAtom {
                        dest: Name::new("@atom"),
                    }
                    .into(),
                ],
                invocation: s0::Invocation {
                    target: Name::new("closed_over"),
                    branch: Name::new("branch"),
                },
            })
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
            .parse_s0_block(),
            Ok(s0::Block {
                name: Name::new("block_name"),
                containing: vec![Name::new("closed_over")],
                receiving: vec![Name::new("input")],
                statements: vec![
                    s0::CreateLiteral {
                        dest: Name::new("@lit"),
                        value: "foo".as_bytes().to_vec(),
                    }
                    .into(),
                    s0::CreateAtom {
                        dest: Name::new("@atom"),
                    }
                    .into(),
                ],
                invocation: s0::Invocation {
                    target: Name::new("closed_over"),
                    branch: Name::new("branch"),
                },
            })
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
mod parse_s0_module_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_s0_module(),
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
            .parse_s0_module(),
            Ok(s0::ParsedModule::new(
                Name::new("@mod"),
                vec![s0::Block {
                    name: Name::new("@block"),
                    containing: vec![Name::new("closed_over")],
                    receiving: vec![Name::new("input")],
                    statements: vec![
                        s0::CreateLiteral {
                            dest: Name::new("@lit"),
                            value: "foo".as_bytes().to_vec(),
                        }
                        .into(),
                        s0::CreateAtom {
                            dest: Name::new("@atom"),
                        }
                        .into(),
                    ],
                    invocation: s0::Invocation {
                        target: Name::new("closed_over"),
                        branch: Name::new("branch"),
                    },
                }]
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
            .parse_s0_module(),
            Ok(s0::ParsedModule::new(
                Name::new("@mod"),
                vec![s0::Block {
                    name: Name::new("@block"),
                    containing: vec![Name::new("closed_over")],
                    receiving: vec![Name::new("input")],
                    statements: vec![
                        s0::CreateLiteral {
                            dest: Name::new("@lit"),
                            value: "foo".as_bytes().to_vec(),
                        }
                        .into(),
                        s0::CreateAtom {
                            dest: Name::new("@atom"),
                        }
                        .into(),
                    ],
                    invocation: s0::Invocation {
                        target: Name::new("closed_over"),
                        branch: Name::new("branch"),
                    },
                }]
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

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_named_parameters(),
                Err(ParseError::UnexpectedEnd),
            );
        }
    }

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
        check_all_prefixes("(foo,bar)");
        check_all_prefixes("(foo<-bar,baz)");
        check_all_prefixes("(baz,foo<-bar)");
        check_all_prefixes("( foo , bar )");
        check_all_prefixes("( foo <- bar , baz )");
        check_all_prefixes("( baz , foo <- bar )");
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
mod parse_closure_parameter_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_closure_parameter(),
                Err(ParseError::UnexpectedEnd),
            );
        }
    }

    #[test]
    fn can_parse() {
        // The trailing "~" is just the start of any clause that can terminate the list of block
        // parameters.
        assert_eq!(
            Parser::for_str("foo()::bar->(){}~").parse_closure_parameter(),
            Ok(s1::ClosureParameter {
                param_name: Name::new("foo"),
                close_over: vec![],
                branches: vec![s1::ClosureParameterBranch {
                    branch_name: Name::new("bar"),
                    receiving: vec![],
                    statements: vec![],
                }],
            })
        );
        assert_eq!(
            Parser::for_str("foo ( ) ::bar -> ( ) { } ~").parse_closure_parameter(),
            Ok(s1::ClosureParameter {
                param_name: Name::new("foo"),
                close_over: vec![],
                branches: vec![s1::ClosureParameterBranch {
                    branch_name: Name::new("bar"),
                    receiving: vec![],
                    statements: vec![],
                }],
            })
        );
        check_all_prefixes("foo()::bar->(){}");
        check_all_prefixes("foo ( ) ::bar -> ( ) { }");
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

    #[test]
    fn can_parse() {
        // The trailing "~" is just the start of any clause that can terminate the list of block
        // parameters.
        assert_eq!(
            Parser::for_str("foo()::bar->(){}~").parse_closure_parameters(),
            Ok(vec![s1::ClosureParameter {
                param_name: Name::new("foo"),
                close_over: vec![],
                branches: vec![s1::ClosureParameterBranch {
                    branch_name: Name::new("bar"),
                    receiving: vec![],
                    statements: vec![],
                }],
            }])
        );
        assert_eq!(
            Parser::for_str("foo ( ) ::bar -> ( ) { } ~").parse_closure_parameters(),
            Ok(vec![s1::ClosureParameter {
                param_name: Name::new("foo"),
                close_over: vec![],
                branches: vec![s1::ClosureParameterBranch {
                    branch_name: Name::new("bar"),
                    receiving: vec![],
                    statements: vec![],
                }],
            }])
        );
        assert_eq!(
            Parser::for_str("foo()::bar->(){}foo()::bar->(){}~").parse_closure_parameters(),
            Ok(vec![
                s1::ClosureParameter {
                    param_name: Name::new("foo"),
                    close_over: vec![],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("bar"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                },
                s1::ClosureParameter {
                    param_name: Name::new("foo"),
                    close_over: vec![],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("bar"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                },
            ])
        );
        assert_eq!(
            Parser::for_str("foo ( ) ::bar -> ( ) { } foo ( ) ::bar -> ( ) { } ~")
                .parse_closure_parameters(),
            Ok(vec![
                s1::ClosureParameter {
                    param_name: Name::new("foo"),
                    close_over: vec![],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("bar"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                },
                s1::ClosureParameter {
                    param_name: Name::new("foo"),
                    close_over: vec![],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("bar"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                },
            ])
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

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_call_results(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse() {
        assert_eq!(
            Parser::for_str("->(foo)").parse_call_results(),
            Ok(vec![Name::new("foo")])
        );
        assert_eq!(
            Parser::for_str("->(foo,bar)").parse_call_results(),
            Ok(vec![Name::new("foo"), Name::new("bar")])
        );
        assert_eq!(
            Parser::for_str("-> ( foo , bar ) ").parse_call_results(),
            Ok(vec![Name::new("foo"), Name::new("bar")])
        );
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
        check_all_prefixes("->(foo,bar)");
        check_all_prefixes("-> ( foo , bar )");
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
mod parse_call_continuation_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_call_continuation(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse_default() {
        assert_eq!(
            Parser::for_str(";").parse_call_continuation(),
            Ok(s1::Continuation::UseDefault),
        );
        check_all_prefixes(";");
    }

    #[test]
    fn can_parse_inside_parameter() {
        assert_eq!(
            Parser::for_str("~>foo;").parse_call_continuation(),
            Ok(s1::Continuation::InsideParameter {
                param_name: Name::new("foo"),
                name: None,
                branch_name: None,
            }),
        );
        assert_eq!(
            Parser::for_str("~> foo ;").parse_call_continuation(),
            Ok(s1::Continuation::InsideParameter {
                param_name: Name::new("foo"),
                name: None,
                branch_name: None,
            }),
        );
        assert_eq!(
            Parser::for_str("~>foo(bar);").parse_call_continuation(),
            Ok(s1::Continuation::InsideParameter {
                param_name: Name::new("foo"),
                name: Some(Name::new("bar")),
                branch_name: None,
            }),
        );
        assert_eq!(
            Parser::for_str("~> foo ( bar ) ;").parse_call_continuation(),
            Ok(s1::Continuation::InsideParameter {
                param_name: Name::new("foo"),
                name: Some(Name::new("bar")),
                branch_name: None,
            }),
        );
        assert_eq!(
            Parser::for_str("~>foo(bar::baz);").parse_call_continuation(),
            Ok(s1::Continuation::InsideParameter {
                param_name: Name::new("foo"),
                name: Some(Name::new("bar")),
                branch_name: Some(Name::new("baz")),
            }),
        );
        assert_eq!(
            Parser::for_str("~> foo ( bar::baz ) ;").parse_call_continuation(),
            Ok(s1::Continuation::InsideParameter {
                param_name: Name::new("foo"),
                name: Some(Name::new("bar")),
                branch_name: Some(Name::new("baz")),
            }),
        );
        check_all_prefixes("~>foo;");
        check_all_prefixes("~>foo(bar);");
        check_all_prefixes("~>foo(bar::baz);");
        check_all_prefixes("~> foo ;");
        check_all_prefixes("~> foo ( bar ) ;");
        check_all_prefixes("~> foo ( bar::baz ) ;");
    }

    #[test]
    fn can_parse_as_parameter() {
        assert_eq!(
            Parser::for_str("=>foo::bar;").parse_call_continuation(),
            Ok(s1::Continuation::AsParameter {
                param_name: Name::new("foo"),
                branch_name: Name::new("bar"),
            }),
        );
        assert_eq!(
            Parser::for_str("=> foo::bar ;").parse_call_continuation(),
            Ok(s1::Continuation::AsParameter {
                param_name: Name::new("foo"),
                branch_name: Name::new("bar"),
            }),
        );
        check_all_prefixes("=>foo::bar;");
        check_all_prefixes("=> foo::bar ;");
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
mod parse_s1_statement_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_s1_statement(),
                Err(ParseError::UnexpectedEnd)
            );
        }
    }

    #[test]
    fn can_parse_create_atom() {
        assert_eq!(
            Parser::for_str("foo=atom;").parse_s1_statement(),
            Ok(s0::CreateAtom {
                dest: Name::new("foo"),
            }
            .into())
        );
    }

    #[test]
    fn can_parse_create_closure() {
        assert_eq!(
            Parser::for_str(concat!(
                "foo = closure containing (foo, bar) ",
                "branch true = @true, ",
                "branch false = @false;",
            ))
            .parse_s1_statement(),
            Ok(s0::CreateClosure {
                dest: Name::new("foo"),
                close_over: vec![Name::new("foo"), Name::new("bar")],
                branches: vec![
                    s0::BranchRef {
                        branch_name: Name::new("true"),
                        block_name: Name::new("@true"),
                        resolved: 0
                    },
                    s0::BranchRef {
                        branch_name: Name::new("false"),
                        block_name: Name::new("@false"),
                        resolved: 0
                    },
                ],
            }
            .into())
        );
    }

    #[test]
    fn can_parse_create_literal() {
        assert_eq!(
            Parser::for_str("foo = literal bar;").parse_s1_statement(),
            Ok(s0::CreateLiteral {
                dest: Name::new("foo"),
                value: "bar".as_bytes().to_vec(),
            }
            .into())
        );
    }

    #[test]
    fn can_parse_rename() {
        assert_eq!(
            Parser::for_str("foo = rename bar;").parse_s1_statement(),
            Ok(s0::Rename {
                dest: Name::new("foo"),
                source: Name::new("bar"),
            }
            .into())
        );
    }

    #[test]
    fn can_parse_call() {
        assert_eq!(
            Parser::for_str("foo::bar();").parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![],
                closure_parameters: vec![],
                results: vec![],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );
        assert_eq!(
            Parser::for_str("foo::bar ( ) ;").parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![],
                closure_parameters: vec![],
                results: vec![],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );

        assert_eq!(
            Parser::for_str("foo::bar(param1,param2<-var);").parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![],
                results: vec![],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );
        assert_eq!(
            Parser::for_str("foo::bar ( param1 , param2 <- var ) ;").parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![],
                results: vec![],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );

        assert_eq!(
            Parser::for_str("foo::bar(param1,param2<-var)block(close1)::branch->(){};")
                .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar ( param1 , param2 <- var ) ",
                "block ( close1 ) ::branch -> ( ) { } ;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );

        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
                "->(result1,result2);",
            ),)
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
                "-> ( result1 , result2 ) ;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::UseDefault,
            }
            .into())
        );

        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
                "->(result1,result2)~>foo;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::InsideParameter {
                    param_name: Name::new("foo"),
                    name: None,
                    branch_name: None,
                },
            }
            .into())
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
                "-> ( result1 , result2 ) ~> foo ;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::InsideParameter {
                    param_name: Name::new("foo"),
                    name: None,
                    branch_name: None,
                },
            }
            .into())
        );

        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
                "->(result1,result2)~>foo(bar::baz);",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::InsideParameter {
                    param_name: Name::new("foo"),
                    name: Some(Name::new("bar")),
                    branch_name: Some(Name::new("baz")),
                },
            }
            .into())
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
                "-> ( result1 , result2 ) ~> foo ( bar::baz ) ;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::InsideParameter {
                    param_name: Name::new("foo"),
                    name: Some(Name::new("bar")),
                    branch_name: Some(Name::new("baz")),
                },
            }
            .into())
        );

        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
                "->(result1,result2)=>foo::bar;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::AsParameter {
                    param_name: Name::new("foo"),
                    branch_name: Name::new("bar"),
                },
            }
            .into())
        );
        assert_eq!(
            Parser::for_str(concat!(
                "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
                "-> ( result1 , result2 ) => foo::bar ;",
            ))
            .parse_s1_statement(),
            Ok(s1::Call {
                target: Name::new("foo"),
                branch: Name::new("bar"),
                named_parameters: vec![
                    s1::NamedParameter {
                        param_name: Name::new("param1"),
                        source: None
                    },
                    s1::NamedParameter {
                        param_name: Name::new("param2"),
                        source: Some(Name::new("var")),
                    },
                ],
                closure_parameters: vec![s1::ClosureParameter {
                    param_name: Name::new("block"),
                    close_over: vec![Name::new("close1")],
                    branches: vec![s1::ClosureParameterBranch {
                        branch_name: Name::new("branch"),
                        receiving: vec![],
                        statements: vec![],
                    }],
                }],
                results: vec![Name::new("result1"), Name::new("result2")],
                continuation: s1::Continuation::AsParameter {
                    param_name: Name::new("foo"),
                    branch_name: Name::new("bar"),
                },
            }
            .into())
        );

        check_all_prefixes("foo::bar();");
        check_all_prefixes("foo::bar(param1,param2<-var);");
        check_all_prefixes("foo::bar(param1,param2<-var)block(close1)::branch->(){};");
        check_all_prefixes(concat!(
            "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
            "->(result1,result2);",
        ));
        check_all_prefixes(concat!(
            "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
            "->(result1,result2)~>foo;",
        ));
        check_all_prefixes(concat!(
            "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
            "->(result1,result2)~>foo(bar::baz);",
        ));
        check_all_prefixes(concat!(
            "foo::bar(param1,param2<-var)block(close1)::branch->(){}",
            "->(result1,result2)=>foo::bar;",
        ));

        check_all_prefixes("foo::bar ( ) ;");
        check_all_prefixes("foo::bar ( param1 , param2 <- var ) ;");
        check_all_prefixes(concat!(
            "foo::bar ( param1 , param2 <- var ) ",
            "block ( close1 ) ::branch -> ( ) { } ;",
        ));
        check_all_prefixes(concat!(
            "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
            "-> ( result1, result2 ) ;",
        ));
        check_all_prefixes(concat!(
            "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
            "-> ( result1, result2 ) ~> foo ;",
        ));
        check_all_prefixes(concat!(
            "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
            "-> ( result1, result2 ) ~> foo ( bar::baz ) ;",
        ));
        check_all_prefixes(concat!(
            "foo::bar ( param1 , param2 <- var ) block ( close1 ) ::branch -> ( ) { } ",
            "-> ( result1, result2 ) => foo::bar ;",
        ));
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
                "  @lit = literal foo; ",
                "  @atom = atom; ",
                "}",
            ))
            .parse_s1_statement_list(),
            Ok(vec![
                s0::CreateLiteral {
                    dest: Name::new("@lit"),
                    value: "foo".as_bytes().to_vec()
                }
                .into(),
                s0::CreateAtom {
                    dest: Name::new("@atom")
                }
                .into(),
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
mod parse_s1_block_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_s1_block(),
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
                "  foo::bar(param1, param2 <- var) block (close1) ::branch ->() {};",
                "}",
            ))
            .parse_s1_block(),
            Ok(s1::Block {
                name: Name::new("block_name"),
                containing: vec![Name::new("closed_over")],
                receiving: vec![Name::new("input")],
                statements: vec![
                    s0::CreateLiteral {
                        dest: Name::new("@lit"),
                        value: "foo".as_bytes().to_vec(),
                    }
                    .into(),
                    s0::CreateAtom {
                        dest: Name::new("@atom"),
                    }
                    .into(),
                    s1::Call {
                        target: Name::new("foo"),
                        branch: Name::new("bar"),
                        named_parameters: vec![
                            s1::NamedParameter {
                                param_name: Name::new("param1"),
                                source: None
                            },
                            s1::NamedParameter {
                                param_name: Name::new("param2"),
                                source: Some(Name::new("var")),
                            },
                        ],
                        closure_parameters: vec![s1::ClosureParameter {
                            param_name: Name::new("block"),
                            close_over: vec![Name::new("close1")],
                            branches: vec![s1::ClosureParameterBranch {
                                branch_name: Name::new("branch"),
                                receiving: vec![],
                                statements: vec![],
                            }],
                        }],
                        results: vec![],
                        continuation: s1::Continuation::UseDefault,
                    }
                    .into(),
                ],
            })
        );
        assert_eq!(
            Parser::for_str(concat!(
                "block_name:",
                "containing(closed_over)",
                "receiving(input)",
                "{",
                "@lit=literal foo;",
                "@atom=atom;",
                "foo::bar(param1,param2<-var)block(close1)::branch->(){};",
                "}",
            ))
            .parse_s1_block(),
            Ok(s1::Block {
                name: Name::new("block_name"),
                containing: vec![Name::new("closed_over")],
                receiving: vec![Name::new("input")],
                statements: vec![
                    s0::CreateLiteral {
                        dest: Name::new("@lit"),
                        value: "foo".as_bytes().to_vec(),
                    }
                    .into(),
                    s0::CreateAtom {
                        dest: Name::new("@atom"),
                    }
                    .into(),
                    s1::Call {
                        target: Name::new("foo"),
                        branch: Name::new("bar"),
                        named_parameters: vec![
                            s1::NamedParameter {
                                param_name: Name::new("param1"),
                                source: None
                            },
                            s1::NamedParameter {
                                param_name: Name::new("param2"),
                                source: Some(Name::new("var")),
                            },
                        ],
                        closure_parameters: vec![s1::ClosureParameter {
                            param_name: Name::new("block"),
                            close_over: vec![Name::new("close1")],
                            branches: vec![s1::ClosureParameterBranch {
                                branch_name: Name::new("branch"),
                                receiving: vec![],
                                statements: vec![],
                            }],
                        }],
                        results: vec![],
                        continuation: s1::Continuation::UseDefault,
                    }
                    .into(),
                ],
            })
        );
        check_all_prefixes(concat!(
            "block_name: ",
            "containing (closed_over) ",
            "receiving (input) ",
            "{",
            "  @lit = literal foo; ",
            "  @atom = atom; ",
            "  foo::bar(param1, param2 <- var) block (close1) ::branch ->() {};",
            "}",
        ));
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
mod parse_s1_module_tests {
    use super::*;

    fn check_all_prefixes(input: &str) {
        for len in 0..input.len() {
            assert_eq!(
                Parser::for_str(&input[0..len]).parse_s1_module(),
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
                "      foo::bar(param1, param2 <- var) block (close1) ::branch ->() {};",
                "    }",
                "}",
            ))
            .parse_s1_module(),
            Ok(s1::ParsedModule::new(
                Name::new("@mod"),
                vec![s1::Block {
                    name: Name::new("@block"),
                    containing: vec![Name::new("closed_over")],
                    receiving: vec![Name::new("input")],
                    statements: vec![
                        s0::CreateLiteral {
                            dest: Name::new("@lit"),
                            value: "foo".as_bytes().to_vec(),
                        }
                        .into(),
                        s0::CreateAtom {
                            dest: Name::new("@atom"),
                        }
                        .into(),
                        s1::Call {
                            target: Name::new("foo"),
                            branch: Name::new("bar"),
                            named_parameters: vec![
                                s1::NamedParameter {
                                    param_name: Name::new("param1"),
                                    source: None
                                },
                                s1::NamedParameter {
                                    param_name: Name::new("param2"),
                                    source: Some(Name::new("var")),
                                },
                            ],
                            closure_parameters: vec![s1::ClosureParameter {
                                param_name: Name::new("block"),
                                close_over: vec![Name::new("close1")],
                                branches: vec![s1::ClosureParameterBranch {
                                    branch_name: Name::new("branch"),
                                    receiving: vec![],
                                    statements: vec![],
                                }],
                            }],
                            results: vec![],
                            continuation: s1::Continuation::UseDefault,
                        }
                        .into(),
                    ],
                }]
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
                "foo::bar(param1,param2<-var)block(close1)::branch->(){};",
                "}",
                "}",
            ))
            .parse_s1_module(),
            Ok(s1::ParsedModule::new(
                Name::new("@mod"),
                vec![s1::Block {
                    name: Name::new("@block"),
                    containing: vec![Name::new("closed_over")],
                    receiving: vec![Name::new("input")],
                    statements: vec![
                        s0::CreateLiteral {
                            dest: Name::new("@lit"),
                            value: "foo".as_bytes().to_vec(),
                        }
                        .into(),
                        s0::CreateAtom {
                            dest: Name::new("@atom"),
                        }
                        .into(),
                        s1::Call {
                            target: Name::new("foo"),
                            branch: Name::new("bar"),
                            named_parameters: vec![
                                s1::NamedParameter {
                                    param_name: Name::new("param1"),
                                    source: None
                                },
                                s1::NamedParameter {
                                    param_name: Name::new("param2"),
                                    source: Some(Name::new("var")),
                                },
                            ],
                            closure_parameters: vec![s1::ClosureParameter {
                                param_name: Name::new("block"),
                                close_over: vec![Name::new("close1")],
                                branches: vec![s1::ClosureParameterBranch {
                                    branch_name: Name::new("branch"),
                                    receiving: vec![],
                                    statements: vec![],
                                }],
                            }],
                            results: vec![],
                            continuation: s1::Continuation::UseDefault,
                        }
                        .into(),
                    ],
                }]
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
            "      foo::bar(param1, param2 <- var) block (close1) ::branch ->() {};",
            "    }",
            "}",
        ));
    }
}
