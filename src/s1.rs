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

use std::collections::HashSet;
use std::collections::VecDeque;

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

impl Continuation {
    /// Returns the name that the continuation will have in the environment once it's been created.
    pub fn closure_name(&self) -> Name {
        match self {
            Continuation::InsideParameter {
                name: Some(name), ..
            } => name.clone(),
            Continuation::AsParameter { param_name, .. } => param_name.clone(),
            _ => Name::new("return"),
        }
    }

    /// Returns the name of the continuation's single branch.
    pub fn branch_name(&self) -> Name {
        match self {
            Continuation::InsideParameter {
                branch_name: Some(name),
                ..
            } => name.clone(),
            Continuation::AsParameter { branch_name, .. } => branch_name.clone(),
            _ => Name::new("return"),
        }
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

/// Parse S₁ source code into its internal AST representation.
pub fn parse_module(input: &str) -> Result<ParsedModule, ParseError> {
    let mut parser = Parser::for_str(input);
    parser.parse_s1_module()
}

//-------------------------------------------------------------------------------------------------
// Translating S₁ into S₀

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum TranslationError {
    DuplicateOutput,
    InvalidContinuation,
    MissingFinalCall,
    MissingValue,
}

struct TranslationState {
    block_names: HashSet<Name>,
    remaining_blocks: VecDeque<BlockState>,
    translated_blocks: Vec<s0::Block>,
}

impl TranslationState {
    fn new(blocks: Vec<Block>) -> TranslationState {
        let mut state = TranslationState {
            block_names: HashSet::new(),
            remaining_blocks: VecDeque::new(),
            translated_blocks: Vec::new(),
        };
        for block in blocks {
            state.block_names.insert(block.name.clone());
            state
                .remaining_blocks
                .push_back(BlockState::from_block(block));
        }
        state
    }
}

struct BlockState {
    name: Name,
    containing: Vec<Name>,
    receiving: Vec<Name>,
    env_contents: HashSet<Name>,
    remaining_statements: VecDeque<Statement>,
    translated_statements: Vec<s0::Statement>,
    name_generator: NameGenerator,
}

impl BlockState {
    fn new(
        name: Name,
        containing: Vec<Name>,
        receiving: Vec<Name>,
        statements: VecDeque<Statement>,
        name_generator: NameGenerator,
    ) -> BlockState {
        let mut env_contents = HashSet::new();
        env_contents.extend(containing.iter().cloned());
        env_contents.extend(receiving.iter().cloned());
        BlockState {
            name: name,
            containing: containing,
            receiving: receiving,
            env_contents,
            remaining_statements: statements,
            translated_statements: Vec::new(),
            name_generator,
        }
    }

    fn from_block(block: Block) -> BlockState {
        let name_generator = NameGenerator::new(block.name.to_string());
        BlockState::new(
            block.name,
            block.containing,
            block.receiving,
            block.statements.into(),
            name_generator,
        )
    }

    fn add_value(&mut self, name: &Name) -> Result<(), TranslationError> {
        if self.env_contents.insert(name.clone()) {
            Ok(())
        } else {
            Err(TranslationError::DuplicateOutput)
        }
    }

    fn remove_value(&mut self, name: &Name) -> Result<(), TranslationError> {
        if self.env_contents.remove(name) {
            Ok(())
        } else {
            Err(TranslationError::MissingValue)
        }
    }

    fn translate(mut self, state: &mut TranslationState) -> Result<(), TranslationError> {
        while let Some(stmt) = self.remaining_statements.pop_front() {
            match stmt {
                Statement::S0Statement(s0::Statement::CreateAtom(stmt)) => {
                    self.translate_create_atom(stmt)?;
                }
                Statement::S0Statement(s0::Statement::CreateClosure(stmt)) => {
                    self.translate_create_closure(stmt)?;
                }
                Statement::S0Statement(s0::Statement::CreateLiteral(stmt)) => {
                    self.translate_create_literal(stmt)?;
                }
                Statement::S0Statement(s0::Statement::Rename(stmt)) => {
                    self.translate_rename(stmt)?;
                }
                Statement::Call(stmt) => {
                    return self.translate_call(stmt, state);
                }
            }
        }

        Err(TranslationError::MissingFinalCall)
    }

    fn translate_create_atom(&mut self, stmt: s0::CreateAtom) -> Result<(), TranslationError> {
        self.add_value(&stmt.dest)?;
        self.translated_statements.push(stmt.into());
        Ok(())
    }

    fn translate_create_closure(
        &mut self,
        stmt: s0::CreateClosure,
    ) -> Result<(), TranslationError> {
        for name in &stmt.close_over {
            self.remove_value(name)?;
        }
        self.add_value(&stmt.dest)?;
        self.translated_statements.push(stmt.into());
        Ok(())
    }

    fn translate_create_literal(
        &mut self,
        stmt: s0::CreateLiteral,
    ) -> Result<(), TranslationError> {
        self.add_value(&stmt.dest)?;
        self.translated_statements.push(stmt.into());
        Ok(())
    }

    fn translate_rename(&mut self, stmt: s0::Rename) -> Result<(), TranslationError> {
        self.remove_value(&stmt.source)?;
        self.add_value(&stmt.dest)?;
        self.translated_statements.push(stmt.into());
        Ok(())
    }

    fn translate_call(
        mut self,
        stmt: Call,
        state: &mut TranslationState,
    ) -> Result<(), TranslationError> {
        // As we process the call, the final contents of `self.env_contents` will be the
        // closed-over set for the continuation that we have to create.  That means we have to
        // remove any of the values that are "consumed" by each parameter, and we _don't_ add in
        // the values that we _create_ for those parameters (since they're about to be consumed
        // too).

        // The final invocation will consume the call's target.
        self.remove_value(&stmt.target)?;

        // Let's take care of the named parameters first.
        for param in stmt.named_parameters {
            if let Some(source) = param.source {
                // If the parameter is renamed, then we consume the source, and add a Rename
                // statement so that the parameter has the right name going into the call.
                self.remove_value(&source)?;
                self.translated_statements.push(
                    s0::Rename {
                        dest: param.param_name,
                        source,
                    }
                    .into(),
                );
            } else {
                // If the parameter is _not_ renamed, then it already has the correct name; we just
                // have to consume it.
                self.remove_value(&param.param_name)?;
            }
        }

        // Now we have to create a bunch of new closures: one for each closure parameter, and one
        // for the continuation.  We want to create the continuation first, since we might need to
        // add it to one of the closure parameters.  But before we can do that, we have to
        // _partially_ process the closure parameters, so that we know what the final closure set
        // for the continuation looks like.
        for param in &stmt.closure_parameters {
            // Remove the closed-over set from our view of the environment's contents so that we
            // don't close over them again when creating the continuation block later.
            for name in &param.close_over {
                self.remove_value(name)?;
            }
        }

        // Our continuation closed-over set should be correct now, so we can go ahead and add a
        // create closure statement for the continuation closure.  (If there is one — if there
        // aren't any more statements in this S₁ block, then there's no continuation.)
        if self.remaining_statements.is_empty() {
            if stmt.continuation != Continuation::UseDefault {
                return Err(TranslationError::InvalidContinuation);
            }
        } else {
            let continuation_block_name = self.name_generator.generate_name(state);
            let mut close_over = self.env_contents.drain().collect::<Vec<_>>();
            close_over.sort_unstable();

            self.translated_statements.push(
                s0::CreateClosure {
                    dest: stmt.continuation.closure_name(),
                    close_over: close_over.clone(),
                    branches: vec![s0::BranchRef {
                        branch_name: stmt.continuation.branch_name(),
                        block_name: continuation_block_name.clone(),
                        resolved: 0,
                    }],
                }
                .into(),
            );

            state.remaining_blocks.push_front(BlockState::new(
                continuation_block_name.clone(),
                close_over,
                stmt.results,
                std::mem::take(&mut self.remaining_statements),
                self.name_generator,
            ));
        }

        // Create a closure for each closure parameter.  Queue up each of the closure's branches so
        // that we translate their contents in later passes.  (We create the name of the blocks for
        // each branch now, which lets us finish up _this_ block before we've translated the blocks
        // that it refers to.)
        let mut new_s1_blocks = Vec::new();
        for param in stmt.closure_parameters {
            // Is this the closure parameter that we should add the continuation to?
            let mut close_over = param.close_over;
            if let Continuation::InsideParameter { param_name, .. } = &stmt.continuation {
                if *param_name == param.param_name {
                    close_over.push(stmt.continuation.closure_name());
                }
            }

            // Queue up a block for each of the closure's branches.
            let mut branches = Vec::new();
            for branch in param.branches {
                let mut name_generator = NameGenerator::new(format!(
                    "{}${}${}",
                    &self.name, &param.param_name, &branch.branch_name
                ));
                let block_name = name_generator.generate_name(state);
                branches.push(s0::BranchRef {
                    branch_name: branch.branch_name,
                    block_name: block_name.clone(),
                    resolved: 0,
                });
                new_s1_blocks.push(BlockState::new(
                    block_name,
                    close_over.clone(),
                    branch.receiving,
                    branch.statements.into(),
                    name_generator,
                ));
            }

            // Add a create closure statement whose branches refer to all of the blocks that we
            // just queued up.
            self.translated_statements.push(
                s0::CreateClosure {
                    dest: param.param_name,
                    close_over,
                    branches,
                }
                .into(),
            );
        }

        // We want all of the new closure blocks to be at the beginning of our queue, so that
        // they show up "near" the blocks that refer to them, which means we want to push them onto
        // the front.  But we also want them to appear in the same order as they appeared in the S₀
        // source, when means we have to push them in reverse order.
        for block in new_s1_blocks.into_iter().rev() {
            state.remaining_blocks.push_front(block);
        }

        // Lastly, create an invocation for the call, and add a new S₀ block to the final result.
        state.translated_blocks.push(s0::Block {
            name: self.name,
            containing: self.containing,
            receiving: self.receiving,
            statements: self.translated_statements,
            invocation: s0::Invocation {
                target: stmt.target,
                branch: stmt.branch,
            },
        });

        Ok(())
    }
}

struct NameGenerator {
    prefix: String,
    next_suffix: usize,
}

impl NameGenerator {
    fn new(prefix: String) -> NameGenerator {
        NameGenerator {
            prefix,
            next_suffix: 0,
        }
    }

    fn generate_name(&mut self, state: &mut TranslationState) -> Name {
        loop {
            let attempt = if self.next_suffix == 0 {
                Name::new(&self.prefix)
            } else {
                Name::new(format!("{}@{}", self.prefix, self.next_suffix))
            };
            self.next_suffix += 1;
            if state.block_names.insert(attempt.clone()) {
                return attempt;
            }
        }
    }
}

impl ParsedModule {
    pub fn translate(self) -> Result<s0::ParsedModule, TranslationError> {
        let mut state = TranslationState::new(self.0.blocks);
        while let Some(block) = state.remaining_blocks.pop_front() {
            block.translate(&mut state)?;
        }
        Ok(s0::ParsedModule::new(self.0.name, state.translated_blocks))
    }
}

#[cfg(test)]
mod translation_tests {
    use super::*;

    #[test]
    fn can_translate_simple() -> Result<(), TranslationError> {
        let s1 = parse_module(
            "module mod {
                entry: containing () receiving (Finish) {
                    Finish::succeed();
                }
            }",
        )
        .expect("Invalid S₁ program");

        let expected_s0 = s0::parse_module(
            "module mod {
                entry: containing () receiving (Finish) {
                    -> Finish succeed;
                }
            }",
        )
        .expect("Invalid S₀ program");

        let actual_s0 = s1.translate()?;
        assert_eq!(actual_s0, expected_s0);
        Ok(())
    }

    #[test]
    fn can_translate_continuation() -> Result<(), TranslationError> {
        let s1 = parse_module(
            "module mod {
                entry: containing () receiving (String, Finish) {
                    content = literal hello;
                    String::from_literal(content) -> ($_, $0);
                    $_::drop();
                    Finish::succeed(result <- $0);
                }
            }",
        )
        .expect("Invalid S₁ program");

        let expected_s0 = s0::parse_module(
            "module mod {
                entry: containing () receiving (String, Finish) {
                    content = literal hello;
                    return = closure containing (Finish) branch return = entry@1;
                    -> String from_literal;
                }

                entry@1: containing (Finish) receiving ($_, $0) {
                    return = closure containing ($0, Finish) branch return = entry@2;
                    -> $_ drop;
                }

                entry@2: containing ($0, Finish) receiving () {
                    result = rename $0;
                    -> Finish succeed;
                }
            }",
        )
        .expect("Invalid S₀ program");

        let actual_s0 = s1.translate()?;
        assert_eq!(actual_s0, expected_s0);
        Ok(())
    }

    #[test]
    fn can_translate_named_continuation() -> Result<(), TranslationError> {
        let s1 = parse_module(
            "module mod {
                entry: containing () receiving (String, Finish) {
                    content = literal hello;
                    String::from_literal(content) -> ($_, $0) => continue::continue;
                    $_::drop();
                    Finish::succeed(result <- $0);
                }
            }",
        )
        .expect("Invalid S₁ program");

        let expected_s0 = s0::parse_module(
            "module mod {
                entry: containing () receiving (String, Finish) {
                    content = literal hello;
                    continue = closure containing (Finish) branch continue = entry@1;
                    -> String from_literal;
                }

                entry@1: containing (Finish) receiving ($_, $0) {
                    return = closure containing ($0, Finish) branch return = entry@2;
                    -> $_ drop;
                }

                entry@2: containing ($0, Finish) receiving () {
                    result = rename $0;
                    -> Finish succeed;
                }
            }",
        )
        .expect("Invalid S₀ program");

        let actual_s0 = s1.translate()?;
        assert_eq!(actual_s0, expected_s0);
        Ok(())
    }

    #[test]
    fn can_translate_closure_parameter() -> Result<(), TranslationError> {
        let s1 = parse_module(
            "module mod {
                entry: containing () receiving (Boolean, continue) {
                    content = literal true;
                    Boolean::eval(content)
                        eval (continue)
                          ::true ->() { continue::return(); }
                          ::false ->() { continue::return(); };
                }
            }",
        )
        .expect("Invalid S₁ program");

        let expected_s0 = s0::parse_module(
            "module mod {
                entry: containing () receiving (Boolean, continue) {
                    content = literal true;
                    eval = closure containing (continue)
                      branch true = entry$eval$true,
                      branch false = entry$eval$false;
                    -> Boolean eval;
                }

                entry$eval$true: containing (continue) receiving () {
                    -> continue return;
                }

                entry$eval$false: containing (continue) receiving () {
                    -> continue return;
                }
            }",
        )
        .expect("Invalid S₀ program");

        let actual_s0 = s1.translate()?;
        assert_eq!(actual_s0, expected_s0);
        Ok(())
    }

    #[test]
    fn can_add_continuation_to_closure_parameter() -> Result<(), TranslationError> {
        let s1 = parse_module(
            "module mod {
                entry: containing () receiving (Boolean, Finish) {
                    content = literal true;
                    Boolean::eval(content)
                        eval ()
                          ::true ->() { continue::return(); }
                          ::false ->() { continue::return(); }
                        ~> eval(continue);
                    Finish::succeed();
                }
            }",
        )
        .expect("Invalid S₁ program");

        let expected_s0 = s0::parse_module(
            "module mod {
                entry: containing () receiving (Boolean, Finish) {
                    content = literal true;
                    continue = closure containing (Finish) branch return = entry@1;
                    eval = closure containing (continue)
                      branch true = entry$eval$true,
                      branch false = entry$eval$false;
                    -> Boolean eval;
                }

                entry$eval$true: containing (continue) receiving () {
                    -> continue return;
                }

                entry$eval$false: containing (continue) receiving () {
                    -> continue return;
                }

                entry@1: containing (Finish) receiving () {
                    -> Finish succeed;
                }
            }",
        )
        .expect("Invalid S₀ program");

        let actual_s0 = s1.translate()?;
        assert_eq!(actual_s0, expected_s0);
        Ok(())
    }
}
