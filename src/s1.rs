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

//! Types and constructors for working with the AST of an S₁ program.

use crate::parser::ParseError;
use crate::parser::Parser;
use crate::s0;
use crate::s0::Name;

//-------------------------------------------------------------------------------------------------
// Modules

#[derive(Clone, Debug, Eq, PartialEq)]
struct ModuleInner {
    name: Name,
    blocks: Vec<Block>,
}

//-------------------------------------------------------------------------------------------------
// Blocks

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Block {
    pub name: Name,
    pub containing: Vec<Name>,
    pub receiving: Vec<Name>,
    pub statements: Vec<Statement>,
}

//-------------------------------------------------------------------------------------------------
// Statements

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Statement {
    S0Statement(s0::Statement),
    Call(Call),
}

impl From<s0::Statement> for Statement {
    fn from(stmt: s0::Statement) -> Statement {
        Statement::S0Statement(stmt)
    }
}

impl From<s0::CreateAtom> for Statement {
    fn from(stmt: s0::CreateAtom) -> Statement {
        Statement::S0Statement(stmt.into())
    }
}

impl From<s0::CreateClosure> for Statement {
    fn from(stmt: s0::CreateClosure) -> Statement {
        Statement::S0Statement(stmt.into())
    }
}

impl From<s0::CreateLiteral> for Statement {
    fn from(stmt: s0::CreateLiteral) -> Statement {
        Statement::S0Statement(stmt.into())
    }
}

impl From<s0::Rename> for Statement {
    fn from(stmt: s0::Rename) -> Statement {
        Statement::S0Statement(stmt.into())
    }
}

impl From<Call> for Statement {
    fn from(stmt: Call) -> Statement {
        Statement::Call(stmt)
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Call {
    pub target: Name,
    pub branch: Name,
    pub named_parameters: Vec<NamedParameter>,
    pub closure_parameters: Vec<ClosureParameter>,
    pub results: Vec<Name>,
    pub continuation: Continuation,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamedParameter {
    pub param_name: Name,
    pub source: Option<Name>,
}

/// Create a new closure named `param_name` in the environment before making call.  All block
/// parameters will the same `param_name` will be "merged" into a single closure with multiple
/// branches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureParameter {
    pub param_name: Name,
    pub close_over: Vec<Name>,
    pub branches: Vec<ClosureParameterBranch>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ClosureParameterBranch {
    pub branch_name: Name,
    pub receiving: Vec<Name>,
    pub statements: Vec<Statement>,
}

/// Determines how the automatically constructed "continuation block" is passed in to the target of
/// a call.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Continuation {
    /// If there are no statements after the call, then there's no continuation block to worry
    /// about.  If there are, then this is the same as `AsParameter { "return", "return" }`.
    UseDefault,
    /// Include the continuation block in the closed-over set of the closure named `closure_name`.
    /// `~>`
    InsideParameter {
        /// The name of the closure to add the continuation block to.  (There must already be a
        /// closure in the environment named `param_name`, **_or_** you must have at least one
        /// block parameter with the same `param_name`.)
        param_name: Name,
        /// The name to use for the continuation in the closure's environmet.  Defaults to
        /// `return`.
        name: Option<Name>,
        /// The branch name to use for the continuation block in the new closure parameter.
        /// Defaults to `return`.
        branch_name: Option<Name>,
    },
    /// Add the continuation block as an additional closure parameter to the call.
    /// `=>`
    AsParameter {
        /// The name to use for the new parameter.  There must not already be any value in the
        /// environment with this name, nor any parameter in the call with this name.
        param_name: Name,
        /// The branch name to use for the continuation block in the new closure parameter.
        branch_name: Name,
    },
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

/// Parse S₁ source code into its internal AST representation.
pub fn parse_module(input: &str) -> Result<ParsedModule, ParseError> {
    let mut parser = Parser::for_str(input);
    parser.parse_s1_module()
}
