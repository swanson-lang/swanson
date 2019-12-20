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

use std::collections::HashMap;

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

/// A collection of S₀ definitions that make up a single logical unit.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Module {
    name: Name,
    blocks: HashMap<Name, Block>,
}

impl Module {
    pub fn new(name: Name, blocks: HashMap<Name, Block>) -> Module {
        Module { name, blocks }
    }
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
    containing: Vec<Name>,
    receiving: Vec<Name>,
    statements: Vec<Statement>,
    invocation: Invocation,
}

impl Block {
    pub fn new(
        containing: Vec<Name>,
        receiving: Vec<Name>,
        statements: Vec<Statement>,
        invocation: Invocation,
    ) -> Block {
        Block {
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
pub struct Statement(StatementInner);

#[derive(Clone, Debug, Eq, PartialEq)]
enum StatementInner {
    CreateAtom(CreateAtom),
    CreateClosure(CreateClosure),
    CreateLiteral(CreateLiteral),
    Rename(Rename),
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CreateAtom {
    dest: Name,
}

impl Statement {
    /// A statement that creates a new atom.
    pub fn create_atom(dest: Name) -> Statement {
        Statement(StatementInner::CreateAtom(CreateAtom { dest }))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CreateClosure {
    dest: Name,
    close_over: Vec<Name>,
    branches: HashMap<Name, Name>,
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
        branches: HashMap<Name, Name>,
    ) -> Statement {
        Statement(StatementInner::CreateClosure(CreateClosure {
            dest,
            close_over,
            branches,
        }))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct CreateLiteral {
    dest: Name,
    value: Vec<u8>,
}

impl Statement {
    /// A statement that creates a new literal.
    pub fn create_literal(dest: Name, value: Vec<u8>) -> Statement {
        Statement(StatementInner::CreateLiteral(CreateLiteral { dest, value }))
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Rename {
    dest: Name,
    source: Name,
}

impl Statement {
    /// A statement that renames an existing entity in the environment.
    pub fn rename(dest: Name, source: Name) -> Statement {
        Statement(StatementInner::Rename(Rename { dest, source }))
    }
}

/// The final instruction in an S₀ block, which passes control to some other closure.
///
/// Invokes a closure that already exists in the current environment, passing control to one of
/// its branches.  The closure is first removed from the environment; it is not available in
/// the body of the selected branch.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Invocation {
    target: Name,
    branch: Name,
}

impl Invocation {
    pub fn new(target: Name, branch: Name) -> Invocation {
        Invocation { target, branch }
    }
}
