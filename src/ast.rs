// -*- coding: utf-8 -*-
// ------------------------------------------------------------------------------------------------
// Copyright © 2019, swanson authors.
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

//! Types and constructors for working with the syntax AST of an S₀ program.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Display;
use std::iter::Peekable;
use std::sync::Arc;

//-------------------------------------------------------------------------------------------------
// Names

/// The name of an S₀ entity.
///
/// Note that names in S₀ can be arbitrary binary content — no restriction that they're strings
/// with any particular encoding.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Name(Vec<u8>);

impl Name {
    pub fn new<C: AsRef<[u8]>>(content: C) -> Name {
        Name(content.as_ref().to_vec())
    }
}

impl AsRef<[u8]> for Name {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8]> for Name {
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        String::from_utf8(self.0.clone())
            .expect("Invalid UTF-8 name")
            .fmt(f)
    }
}

impl From<&str> for Name {
    fn from(value: &str) -> Name {
        Name::new(value)
    }
}

impl PartialEq<&str> for Name {
    fn eq(&self, other: &&str) -> bool {
        self.0 == other.as_bytes()
    }
}

#[cfg(test)]
mod name_tests {
    use super::*;

    #[test]
    pub fn names_are_comparable() {
        let foo1 = Name::new("foo");
        let foo2 = Name::new("foo");
        let bar = Name::new("bar");
        assert_eq!(foo1, foo2);
        assert_eq!(foo1, "foo");
        assert_ne!(foo1, bar);
        assert_ne!(foo1, "bar");
        assert_ne!(foo2, bar);
        assert_ne!(foo2, "bar");
    }
}

//-------------------------------------------------------------------------------------------------
// Modules

#[derive(Clone, Debug, Eq, PartialEq)]
struct ModuleInner {
    name: Name,
    blocks: Vec<Block>,
}

//-------------------------------------------------------------------------------------------------
// Blocks

/// A sequence of S₀ instructions (zero or more statements followed by exactly one invocation),
/// defining one of the branches of a closure.
///
/// The block also specifies which entities must be passed in as inputs (the `receiving` clause),
/// and which entities will be closed over (the `containing` clause).
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub name: Name,
    pub containing: Vec<Name>,
    pub receiving: Vec<Name>,
    pub statements: Vec<Statement>,
    pub invocation: Invocation,
}

impl Block {
    pub fn new(
        name: Name,
        containing: Vec<Name>,
        receiving: Vec<Name>,
        statements: Vec<Statement>,
        invocation: Invocation,
    ) -> Block {
        Block {
            name,
            containing,
            receiving,
            statements,
            invocation,
        }
    }
}

//-------------------------------------------------------------------------------------------------
// Statements

/// A single statement in an S₀ block.  Statements create new entities (or rename existing ones) in
/// the environment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    CreateAtom(CreateAtom),
    CreateClosure(CreateClosure),
    CreateLiteral(CreateLiteral),
    Rename(Rename),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CreateAtom {
    pub dest: Name,
}

impl Statement {
    /// A statement that creates a new atom.
    pub fn create_atom(dest: Name) -> Statement {
        Statement::CreateAtom(CreateAtom { dest })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BranchRef {
    pub branch_name: Name,
    pub block_name: Name,
    pub resolved: usize,
}

impl BranchRef {
    pub fn new(branch_name: Name, block_name: Name) -> BranchRef {
        BranchRef {
            branch_name,
            block_name,
            resolved: 0,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CreateClosure {
    pub dest: Name,
    pub close_over: Vec<Name>,
    pub branches: Vec<BranchRef>,
}

impl Statement {
    /// A statement that creates a new closure.  The closure consists of one or more _branches_.
    /// Each branch has a name, and is definition is provided by one of the blocks in the module.
    /// The closure also _closes over_ some entities in the environment, moving them into the
    /// closure.  (They are removed from the environment as part of making the closure, and are no
    /// longer available for the remainder of the current block.)
    pub fn create_closure(
        dest: Name,
        close_over: Vec<Name>,
        branches: Vec<BranchRef>,
    ) -> Statement {
        Statement::CreateClosure(CreateClosure {
            dest,
            close_over,
            branches,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CreateLiteral {
    pub dest: Name,
    pub value: Vec<u8>,
}

impl Statement {
    /// A statement that creates a new literal.
    pub fn create_literal(dest: Name, value: Vec<u8>) -> Statement {
        Statement::CreateLiteral(CreateLiteral { dest, value })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rename {
    pub dest: Name,
    pub source: Name,
}

impl Statement {
    /// A statement that renames an existing entity in the environment.
    pub fn rename(dest: Name, source: Name) -> Statement {
        Statement::Rename(Rename { dest, source })
    }
}

/// The final instruction in an S₀ block, which passes control to some other closure.
///
/// Invokes a closure that already exists in the current environment, passing control to one of
/// its branches.  The closure is first removed from the environment; it is not available in
/// the body of the selected branch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Invocation {
    pub target: Name,
    pub branch: Name,
}

impl Invocation {
    pub fn new(target: Name, branch: Name) -> Invocation {
        Invocation { target, branch }
    }
}

//-------------------------------------------------------------------------------------------------
// Resolving and validation modules

/// Indicates that an error occurred while trying to resolve an S₀ module.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ResolutionError {
    /// There are two blocks in a module with the same name.
    DuplicateBlock,
    /// There are two branches in a closure with the same name.
    DuplicateBranch,
    /// There is a reference to branch that doesn't exist in the module.
    MissingBranch,
}

/// Parse and resolve S₀ source code into its internal AST representation.
pub fn s0(content: &str) -> Arc<Module> {
    let module = parse_module(content).expect("Invalid S₀ program");
    Arc::new(module.resolve().expect("Ill-formed S₀ program"))
}

/// A collection of S₀ definitions that make up a single logical unit.  An instance of this type
/// has been _resolved_, meaning that we've validated that it doesn't contain any basic syntax
/// errors.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module(ModuleInner);

impl Module {
    pub fn name(&self) -> &Name {
        &self.0.name
    }

    pub fn block(&self, index: usize) -> &Block {
        &self.0.blocks[index]
    }
}

impl ParsedModule {
    /// Resolve a parsed module, ensuring that it doesn't contain any basic syntax errors.
    pub fn resolve(mut self) -> Result<Module, ResolutionError> {
        // First build up a mapping from block names to their index within the module.
        let mut block_indices = HashMap::new();
        for (idx, block) in self.0.blocks.iter().enumerate() {
            use std::collections::hash_map::Entry;
            match block_indices.entry(block.name.clone()) {
                Entry::Occupied(_) => return Err(ResolutionError::DuplicateBlock),
                Entry::Vacant(entry) => entry.insert(idx),
            };
        }

        // Then update each closure in the module so that their branches refer to their blocks by
        // index as well as by name.
        let mut branch_names = HashSet::new();
        for block in &mut self.0.blocks {
            for stmt in &mut block.statements {
                match stmt {
                    Statement::CreateClosure(stmt) => {
                        branch_names.clear();
                        for branch in &mut stmt.branches {
                            if !branch_names.insert(branch.block_name.clone()) {
                                return Err(ResolutionError::DuplicateBranch);
                            }
                            let idx = match block_indices.get(&branch.block_name) {
                                Some(idx) => idx,
                                None => return Err(ResolutionError::MissingBranch),
                            };
                            branch.resolved = *idx;
                        }
                    }
                    _ => {}
                }
            }
        }

        Ok(Module(self.0))
    }
}

#[cfg(test)]
mod resolution_tests {
    use super::*;

    #[test]
    fn cannot_have_duplicate_block_names() {
        let module = parse_module(
            "module mod {
                block: containing () receiving (input) {
                    -> input branch;
                }
                block: containing () receiving (input) {
                    -> input branch;
                }
            }",
        )
        .unwrap();
        assert_eq!(module.resolve(), Err(ResolutionError::DuplicateBlock));
    }

    #[test]
    fn cannot_have_duplicate_branch_names() {
        let module = parse_module(
            "module mod {
                block: containing () receiving (input) {
                    foo = closure containing ()
                        branch false = target,
                        branch false = target;
                    -> input branch;
                }
                target: containing () receiving (input) {
                    -> input branch;
                }
            }",
        )
        .unwrap();
        assert_eq!(module.resolve(), Err(ResolutionError::DuplicateBranch));
    }

    #[test]
    fn cannot_have_missing_branches() {
        let module = parse_module(
            "module mod {
                block: containing () receiving (input) {
                    foo = closure containing ()
                        branch false = missing;
                    -> input branch;
                }
            }",
        )
        .unwrap();
        assert_eq!(module.resolve(), Err(ResolutionError::MissingBranch));
    }

    #[test]
    fn can_resolve_modules() {
        let _ = s0("
            module mod {
                block: containing () receiving (input) {
                    foo = closure containing ()
                        branch false = target;
                    -> input branch;
                }
                target: containing () receiving (input) {
                    -> input branch;
                }
            }");
    }
}

//-------------------------------------------------------------------------------------------------
// Parsing modules

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ParsedModule(ModuleInner);

impl ParsedModule {
    fn new(name: Name, blocks: Vec<Block>) -> ParsedModule {
        ParsedModule(ModuleInner { name, blocks })
    }
}

/// Indicates that an error occurred while trying to parse the content of an S₀ program.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ParseError {
    /// The parser encountered a character that wasn't valid at the current position in the
    /// program.
    UnexpectedCharacter,
    /// The parser encountered the end of the program when it wasn't expecting to.
    UnexpectedEnd,
}

/// Parse S₀ source code into its internal AST representation.
pub fn parse_module(input: &str) -> Result<ParsedModule, ParseError> {
    let mut parser = Parser::for_str(input);
    let result = parser.parse_module();
    dbg!(parser.it.collect::<String>());
    result
}

#[cfg(test)]
mod macro_tests {
    use super::*;

    #[test]
    fn can_parse() {
        assert_eq!(
            parse_module(
                "module mod {
                    block: containing (closed_over) receiving (input) {
                        lit = literal foo;
                        atom = atom;
                        -> closed_over branch;
                    }

                    @b1: containing () receiving (result) {
                        -> result return;
                    }
                }"
            )
            .unwrap(),
            ParsedModule::new(
                Name::new("mod"),
                vec![
                    Block::new(
                        Name::new("block"),
                        vec![Name::new("closed_over")],
                        vec![Name::new("input")],
                        vec![
                            Statement::create_literal(Name::new("lit"), "foo".as_bytes().to_vec()),
                            Statement::create_atom(Name::new("atom")),
                        ],
                        Invocation::new(Name::new("closed_over"), Name::new("branch"))
                    ),
                    Block::new(
                        Name::new("@b1"),
                        vec![],
                        vec![Name::new("result")],
                        vec![],
                        Invocation::new(Name::new("result"), Name::new("return"))
                    ),
                ]
            )
        );
    }
}

struct Parser<I>
where
    I: Iterator<Item = char>,
{
    it: Peekable<I>,
}

impl Parser<std::str::Chars<'_>> {
    fn for_str(input: &str) -> Parser<std::str::Chars<'_>> {
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
    fn parse_statement(&mut self) -> Result<Statement, ParseError> {
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
    fn parse_create_atom(&mut self, dest: Name) -> Result<Statement, ParseError> {
        self.require_keyword("atom")?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(Statement::create_atom(dest))
    }

    /// ``` s0
    /// [dest] = closure containing ([names],...)
    ///   branch [name] = [name],
    ///   ...
    ///   branch [name] = [name];
    /// ```
    fn parse_create_closure(&mut self, dest: Name) -> Result<Statement, ParseError> {
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
            branches.push(BranchRef::new(branch_name, branch_target));
        }
        loop {
            self.skip_whitespace();
            let ch = self.require_peek()?;
            if ch == ';' {
                self.it.next();
                return Ok(Statement::create_closure(dest, containing, branches));
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
            branches.push(BranchRef::new(branch_name, branch_target));
        }
    }

    /// ``` s0
    /// [dest] = literal [content];
    /// ```
    fn parse_create_literal(&mut self, dest: Name) -> Result<Statement, ParseError> {
        self.require_keyword("literal")?;
        self.skip_whitespace();
        let content = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(Statement::create_literal(dest, content.as_ref().to_vec()))
    }

    /// ``` s0
    /// [dest] = rename [source];
    /// ```
    fn parse_rename(&mut self, dest: Name) -> Result<Statement, ParseError> {
        self.require_keyword("rename")?;
        self.skip_whitespace();
        let source = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(Statement::rename(dest, source))
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
            Ok(Statement::create_atom(Name::new("foo")))
        );
        assert_eq!(
            Parser::for_str("foo=atom;").parse_statement(),
            Ok(Statement::create_atom(Name::new("foo")))
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
            Ok(Statement::create_closure(
                Name::new("foo"),
                vec![Name::new("foo"), Name::new("bar")],
                vec![
                    BranchRef::new(Name::new("true"), Name::new("@true")),
                    BranchRef::new(Name::new("false"), Name::new("@false")),
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
            Ok(Statement::create_closure(
                Name::new("foo"),
                vec![Name::new("foo"), Name::new("bar")],
                vec![
                    BranchRef::new(Name::new("true"), Name::new("@true")),
                    BranchRef::new(Name::new("false"), Name::new("@false")),
                ]
            ))
        );
        check_all_prefixes("foo=closure containing(foo,bar)branch true=@true,branch false=@false;");
    }

    #[test]
    fn can_parse_create_literal() {
        assert_eq!(
            Parser::for_str("foo = literal bar ; ").parse_statement(),
            Ok(Statement::create_literal(
                Name::new("foo"),
                "bar".as_bytes().to_vec()
            ))
        );
        assert_eq!(
            Parser::for_str("foo=literal bar;").parse_statement(),
            Ok(Statement::create_literal(
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
            Ok(Statement::rename(Name::new("foo"), Name::new("bar")))
        );
        assert_eq!(
            Parser::for_str("foo=rename bar;").parse_statement(),
            Ok(Statement::rename(Name::new("foo"), Name::new("bar")))
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
    fn parse_invocation(&mut self) -> Result<Invocation, ParseError> {
        self.require_operator("->")?;
        self.skip_whitespace();
        let target = self.parse_name()?;
        self.skip_whitespace();
        let branch = self.parse_name()?;
        self.skip_whitespace();
        self.require_operator(";")?;
        Ok(Invocation::new(target, branch))
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
            Ok(Invocation::new(Name::new("target"), Name::new("branch")))
        );
        assert_eq!(
            Parser::for_str("->target branch;").parse_invocation(),
            Ok(Invocation::new(Name::new("target"), Name::new("branch")))
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
    fn parse_block(&mut self) -> Result<Block, ParseError> {
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
        Ok(Block::new(
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
            Ok(Block::new(
                Name::new("block_name"),
                vec![Name::new("closed_over")],
                vec![Name::new("input")],
                vec![
                    Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                    Statement::create_atom(Name::new("@atom")),
                ],
                Invocation::new(Name::new("closed_over"), Name::new("branch"))
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
            Ok(Block::new(
                Name::new("block_name"),
                vec![Name::new("closed_over")],
                vec![Name::new("input")],
                vec![
                    Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                    Statement::create_atom(Name::new("@atom")),
                ],
                Invocation::new(Name::new("closed_over"), Name::new("branch"))
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
    fn parse_module(&mut self) -> Result<ParsedModule, ParseError> {
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
                return Ok(ParsedModule::new(name, blocks));
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
            Ok(ParsedModule::new(
                Name::new("@mod"),
                vec![Block::new(
                    Name::new("@block"),
                    vec![Name::new("closed_over")],
                    vec![Name::new("input")],
                    vec![
                        Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                        Statement::create_atom(Name::new("@atom")),
                    ],
                    Invocation::new(Name::new("closed_over"), Name::new("branch"))
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
            Ok(ParsedModule::new(
                Name::new("@mod"),
                vec![Block::new(
                    Name::new("@block"),
                    vec![Name::new("closed_over")],
                    vec![Name::new("input")],
                    vec![
                        Statement::create_literal(Name::new("@lit"), "foo".as_bytes().to_vec()),
                        Statement::create_atom(Name::new("@atom")),
                    ],
                    Invocation::new(Name::new("closed_over"), Name::new("branch"))
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
