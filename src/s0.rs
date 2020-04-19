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

//! Types and constructors for working with the AST of an S₀ program.

use std::borrow::Borrow;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt::Debug;
use std::fmt::Display;
use std::sync::Arc;

use crate::parser::ParseError;
use crate::parser::Parser;

//-------------------------------------------------------------------------------------------------
// Names

/// The name of an S₀ entity.
///
/// Note that names in S₀ can be arbitrary binary content — no restriction that they're strings
/// with any particular encoding.
#[derive(Clone, Eq, Hash, Ord, PartialEq, PartialOrd)]
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

impl Debug for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let string = String::from_utf8(self.0.clone()).expect("Invalid UTF-8 name");
        write!(f, "{:?}", string)
    }
}

impl Display for Name {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        let string = String::from_utf8(self.0.clone()).expect("Invalid UTF-8 name");
        write!(f, "{}", string)
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

//-------------------------------------------------------------------------------------------------
// Statements

/// A single statement in an S₀ block.  Statements create new entities (or rename existing ones) in
/// the environment.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    /// A statement that creates a new atom.
    CreateAtom(CreateAtom),
    /// A statement that creates a new closure.  The closure consists of one or more _branches_.
    /// Each branch has a name, and is definition is provided by one of the blocks in the module.
    /// The closure also _closes over_ some entities in the environment, moving them into the
    /// closure.  (They are removed from the environment as part of making the closure, and are no
    /// longer available for the remainder of the current block.)
    CreateClosure(CreateClosure),
    /// A statement that creates a new literal.
    CreateLiteral(CreateLiteral),
    /// A statement that renames an existing entity in the environment.
    Rename(Rename),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CreateAtom {
    pub dest: Name,
}

impl From<CreateAtom> for Statement {
    fn from(stmt: CreateAtom) -> Statement {
        Statement::CreateAtom(stmt)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct BranchRef {
    pub branch_name: Name,
    pub block_name: Name,
    pub resolved: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CreateClosure {
    pub dest: Name,
    pub close_over: Vec<Name>,
    pub branches: Vec<BranchRef>,
}

impl From<CreateClosure> for Statement {
    fn from(stmt: CreateClosure) -> Statement {
        Statement::CreateClosure(stmt)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CreateLiteral {
    pub dest: Name,
    pub value: Vec<u8>,
}

impl From<CreateLiteral> for Statement {
    fn from(stmt: CreateLiteral) -> Statement {
        Statement::CreateLiteral(stmt)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Rename {
    pub dest: Name,
    pub source: Name,
}

impl From<Rename> for Statement {
    fn from(stmt: Rename) -> Statement {
        Statement::Rename(stmt)
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
    pub(crate) fn new(name: Name, blocks: Vec<Block>) -> ParsedModule {
        ParsedModule(ModuleInner { name, blocks })
    }
}

/// Parse S₀ source code into its internal AST representation.
pub fn parse_module(input: &str) -> Result<ParsedModule, ParseError> {
    let mut parser = Parser::for_str(input);
    parser.parse_s0_module()
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
                    Block {
                        name: Name::new("block"),
                        containing: vec![Name::new("closed_over")],
                        receiving: vec![Name::new("input")],
                        statements: vec![
                            CreateLiteral {
                                dest: Name::new("lit"),
                                value: "foo".as_bytes().to_vec(),
                            }
                            .into(),
                            CreateAtom {
                                dest: Name::new("atom"),
                            }
                            .into(),
                        ],
                        invocation: Invocation {
                            target: Name::new("closed_over"),
                            branch: Name::new("branch"),
                        },
                    },
                    Block {
                        name: Name::new("@b1"),
                        containing: vec![],
                        receiving: vec![Name::new("result")],
                        statements: vec![],
                        invocation: Invocation {
                            target: Name::new("result"),
                            branch: Name::new("return"),
                        },
                    },
                ]
            )
        );
    }
}
