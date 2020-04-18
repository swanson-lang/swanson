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

//! An interpreter for S₀ code.
//!
//! ## Values and environments
//!
//! S₀ code operates on an _environment_, which is a collection of _values_, each with a separate
//! name.  (A good intuition is that it's the set of local parameters and variables that are in
//! scope at the current point of execution.)
//!
//! There are only four kinds of values:
//!
//!   - atoms
//!   - closures
//!   - literals
//!   - primitives
//!
//! Atoms, closures, and literals can be created by S₀ code.  Primitives can only be provided by
//! the host environment.  Closures and primitives are both _invokable_.
//!
//! A _block_ of S₀ code is a list of zero or more _statements_ followed by exactly one
//! _invocation_.  The invocation consumes an invokable value (the _target_) from the environment
//! and passes control to it.  The statements allow you to set up the environment in the way that
//! the invocation target expects.
//!
//! An invokable value consists of a set of _branches_, each with a distinct name.  For closures
//! (which are created in S₀), each branch is a block of S₀ code.  For primitives, each branch is
//! some arbitrary code provided by the host environment.
//!
//! Environments and values are _linear_, which means that they must be used _exactly once_.  That
//! means two things:  First, you cannot use a value more than once.  Invoking a closure or
//! primitive, or using an atom or literal, consumes the value.  Second, you must use every value.
//! When an S₀ program finishes, the environment must be empty.
//!
//! (Primitives are "magical" in the sense that they let you side-step some of those rules.  It's
//! perfectly fine for a primitive to duplicate a value, so that you can use it more than once.
//! The host environment will provide primitives for duplicating values that are safe to duplicate
//! or alias, and won't provide them for other values.  Since there's no way to duplicate values
//! purely in S₀, we can be sure that all S₀ code follows the rules provided by the host
//! environment.)
//!
//! S₀ doesn't really give you anything else!  All of the interesting things that a program might
//! do are handled by the set of primitives your host environment gives you.
//!
//! ## Implementing primitives
//!
//! This S₀ interpreter is implemented in Rust, and so you also implement your primitives in Rust.
//!
//! You have two options: _boxed primitives_ and _inline primitives_.  (These two options are
//! implementation details of this particular interpreter.  Boxed and inline primitives appear
//! exactly the same to the S₀ code that you execute with the interpreter.)
//!
//! A primitive consists of some _associated data_ (which is a Rust value) and Rust code that
//! implements each of the primitive's branches.  The two kinds of primitive give you two different
//! ways of storing the primitive's associated data.
//!
//! For an inline primitive, you only get a single `usize` for the primitive's associated data.
//! This is limiting, but means that the data is stored directly in our environment implementation,
//! and doesn't require any additional heap allocation.  Boxed primitives, on the other hand, let
//! you store arbitrary associated data, but requires you to store that data on the heap (in a
//! `Box`).
//!
//! In both cases, we also provide a helper type (`BoxedBranches` and `InlineBranches`
//! respectively) that makes it easier to define the Rust code for the primitive's branches.  In
//! each case, you define a single function or method for each branch, and the helper type collects
//! them together for you into something easy to call in your `invoke` implementation.

use std::any::Any;
use std::collections::HashMap;
use std::sync::Arc;

use crate::s0::Block;
use crate::s0::CreateAtom;
use crate::s0::CreateClosure;
use crate::s0::CreateLiteral;
use crate::s0::Invocation;
use crate::s0::Module;
use crate::s0::Name;
use crate::s0::Rename;
use crate::s0::Statement;

//-------------------------------------------------------------------------------------------------
// Atoms

#[derive(Clone, Copy, Eq, Ord, PartialEq, PartialOrd)]
struct AtomId;

/// Atoms are basic entities that exist and can be compared for equality.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Atom(uid::Id<AtomId>);

impl Atom {
    /// Creates a new atom that is distinct from all other atoms.
    pub fn new() -> Atom {
        Atom(uid::Id::default())
    }
}

impl Default for Atom {
    fn default() -> Atom {
        Atom::new()
    }
}

#[cfg(test)]
mod atom_tests {
    use super::*;

    #[test]
    pub fn atoms_are_not_equal() {
        let atom1 = Atom::new();
        let atom2 = Atom::new();
        assert_ne!(atom1, atom2);
    }
}

//-------------------------------------------------------------------------------------------------
// Literals

/// Literals represent immutable binary content.  These are the only constants available to an S₀
/// program.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Literal(Vec<u8>);

impl Literal {
    pub fn new<C: AsRef<[u8]>>(content: C) -> Literal {
        Literal(content.as_ref().to_vec())
    }

    pub fn into_content(self) -> Vec<u8> {
        self.0
    }
}

#[cfg(test)]
mod literal_tests {
    use super::*;

    #[test]
    pub fn literals_are_comparable() {
        let foo1 = Literal::new("foo");
        let foo2 = Literal::new("foo");
        let bar = Literal::new("bar");
        assert_eq!(foo1, foo2);
        assert_ne!(foo1, bar);
        assert_ne!(foo2, bar);
    }
}

//-------------------------------------------------------------------------------------------------
// Values and environments

/// A value that can live in an environment.
pub enum Value {
    Atom(Atom),
    Closure(Closure),
    Literal(Literal),
    BoxedPrimitive(Box<dyn BoxedPrimitive>),
    InlinePrimitive(usize, &'static dyn InlinePrimitive),
}

impl Value {
    pub fn as_atom(self) -> Result<Atom, ExecutionError> {
        match self {
            Value::Atom(atom) => Ok(atom),
            _ => Err(ExecutionError::IncorrectValueKind),
        }
    }

    pub fn as_literal(self) -> Result<Literal, ExecutionError> {
        match self {
            Value::Literal(literal) => Ok(literal),
            _ => Err(ExecutionError::IncorrectValueKind),
        }
    }
}

/// A collection of values, each with a distinct name.
pub struct Environment(HashMap<Name, Value>);

impl Environment {
    /// Creates a new, empty environment.
    pub fn new() -> Environment {
        Environment(HashMap::new())
    }

    /// Returns whether the environment is empty.
    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }

    /// Adds a new value to the environment.  Returns a `DuplicateOutput` error if there's already
    /// a value with the same name.
    pub fn add<N>(&mut self, name: N, value: Value) -> Result<(), ExecutionError>
    where
        N: Into<Name>,
    {
        use std::collections::hash_map::Entry;
        match self.0.entry(name.into()) {
            Entry::Occupied(_) => Err(ExecutionError::DuplicateOutput),
            Entry::Vacant(v) => {
                v.insert(value);
                Ok(())
            }
        }
    }

    /// Returns whether the environment contains exactly the given set of names, and no others.
    pub fn contains_exactly(&self, expected: &[Name]) -> bool {
        if self.0.len() != expected.len() {
            return false;
        }

        for name in expected {
            if !self.0.contains_key(name) {
                return false;
            }
        }

        return true;
    }

    /// Merges the contents of `other` into this environment.  Returns a `DuplicateOutput` error if
    /// there are any pair of values in the two environments that have the same name.
    pub fn merge<E>(&mut self, other: E) -> Result<(), ExecutionError>
    where
        E: IntoIterator<Item = (Name, Value)>,
    {
        for (key, value) in other {
            self.add(key, value)?;
        }
        Ok(())
    }

    /// Removes and returns the value from the environment with a particular name.  Returns a
    /// `MissingValue` error if there is no value with that name.
    pub fn remove<N>(&mut self, name: &N) -> Result<Value, ExecutionError>
    where
        N: AsRef<[u8]>,
    {
        self.0
            .remove(name.as_ref())
            .ok_or(ExecutionError::MissingValue)
    }
}

impl IntoIterator for Environment {
    type Item = (Name, Value);
    type IntoIter = std::collections::hash_map::IntoIter<Name, Value>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

//-------------------------------------------------------------------------------------------------
// Execution

/// The set of possible errors that can occur when executing S₀ code.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ExecutionError {
    DuplicateOutput,
    IncorrectValueKind,
    MismatchedContaining,
    MismatchedPrimitive,
    MismatchedReceiving,
    MissingValue,
    TargetNotInvokable,
    UnknownBranch,
}

impl Module {
    /// Executes the module in a given environment (starting at its entry point, which is the first
    /// block defined in the module).
    pub fn execute(self: Arc<Self>, env: &mut Environment) -> Result<(), ExecutionError> {
        let entry_point = self.block(0);
        if !env.contains_exactly(&entry_point.receiving) {
            return Err(ExecutionError::MismatchedReceiving);
        }
        if !entry_point.containing.is_empty() {
            return Err(ExecutionError::MismatchedContaining);
        }
        entry_point.execute(&self, env)
    }
}

#[cfg(test)]
mod module_tests {
    use super::*;

    use crate::s0::s0;

    #[test]
    fn entry_point_must_have_empty_containing_set() -> Result<(), ExecutionError> {
        let module = s0("
            module test {
                entry: containing (something) receiving (unused) {
                    -> unused unused;
                }
            }");

        let mut env = Environment::new();
        env.add("unused", Value::Atom(Atom::new()))?;
        let result = module.execute(&mut env);
        assert_eq!(result, Err(ExecutionError::MismatchedContaining));
        Ok(())
    }

    #[test]
    fn entry_point_must_have_matching_receiving_set() -> Result<(), ExecutionError> {
        let module = s0("
            module test {
                entry: containing () receiving (unused) {
                    -> unused unused;
                }
            }");

        let mut env = Environment::new();
        let result = module.execute(&mut env);
        assert_eq!(result, Err(ExecutionError::MismatchedReceiving));
        Ok(())
    }
}

impl Block {
    fn execute(&self, module: &Arc<Module>, env: &mut Environment) -> Result<(), ExecutionError> {
        for stmt in &self.statements {
            stmt.execute(module, env)?;
        }
        self.invocation.invoke(env)
    }
}

impl Statement {
    fn execute(&self, module: &Arc<Module>, env: &mut Environment) -> Result<(), ExecutionError> {
        match self {
            Statement::CreateAtom(stmt) => stmt.execute(env),
            Statement::CreateClosure(stmt) => stmt.execute(module, env),
            Statement::CreateLiteral(stmt) => stmt.execute(env),
            Statement::Rename(stmt) => stmt.execute(env),
        }
    }
}

impl CreateAtom {
    fn execute(&self, env: &mut Environment) -> Result<(), ExecutionError> {
        let atom = Atom::new();
        env.add(self.dest.clone(), Value::Atom(atom))?;
        Ok(())
    }
}

impl CreateClosure {
    fn execute(&self, module: &Arc<Module>, env: &mut Environment) -> Result<(), ExecutionError> {
        let mut closed_over = Environment::new();
        for name in &self.close_over {
            let value = env.remove(name)?;
            closed_over.add(name.clone(), value)?;
        }

        let mut branches = HashMap::new();
        for branch_ref in &self.branches {
            let closure_branch = ClosureBranch {
                module: module.clone(),
                index: branch_ref.resolved,
            };
            branches.insert(branch_ref.branch_name.clone(), closure_branch);
        }

        let closure = Closure {
            closed_over,
            branches,
        };
        env.add(self.dest.clone(), Value::Closure(closure))?;
        Ok(())
    }
}

impl CreateLiteral {
    fn execute(&self, env: &mut Environment) -> Result<(), ExecutionError> {
        let literal = Literal::new(&self.value);
        env.add(self.dest.clone(), Value::Literal(literal))?;
        Ok(())
    }
}

impl Rename {
    fn execute(&self, env: &mut Environment) -> Result<(), ExecutionError> {
        let value = env.remove(&self.source)?;
        env.add(self.dest.clone(), value)?;
        Ok(())
    }
}

impl Value {
    /// Invokes one of the branches of a value in the given environment.  Returns a
    /// `TargetNotInvokable` error if the value isn't invokable (i.e., a closure or a primitive).
    pub fn invoke(self, branch: &Name, env: &mut Environment) -> Result<(), ExecutionError> {
        match self {
            Value::Closure(target) => target.invoke(branch, env),
            Value::BoxedPrimitive(target) => target.invoke(branch, env),
            Value::InlinePrimitive(value, target) => target.invoke(value, branch, env),
            _ => Err(ExecutionError::TargetNotInvokable),
        }
    }
}

impl Invocation {
    fn invoke(&self, env: &mut Environment) -> Result<(), ExecutionError> {
        let target = env.remove(&self.target)?;
        target.invoke(&self.branch, env)
    }
}

//-------------------------------------------------------------------------------------------------
// Closures

/// An invokable value that can be created in S₀.  It consists of a set of blocks, each with a
/// separate branch name.  The blocks themselves are defined elsewhere in the same S₀ module.
pub struct Closure {
    closed_over: Environment,
    branches: HashMap<Name, ClosureBranch>,
}

struct ClosureBranch {
    module: Arc<Module>,
    index: usize,
}

impl Closure {
    fn invoke(self, branch: &Name, env: &mut Environment) -> Result<(), ExecutionError> {
        let branch = self
            .branches
            .get(branch)
            .ok_or(ExecutionError::UnknownBranch)?;
        let block = branch.module.block(branch.index);
        if !env.contains_exactly(&block.receiving) {
            return Err(ExecutionError::MismatchedReceiving);
        }
        if !self.closed_over.contains_exactly(&block.containing) {
            return Err(ExecutionError::MismatchedContaining);
        }
        env.merge(self.closed_over)?;
        block.execute(&branch.module, env)
    }
}

#[cfg(test)]
mod closure_tests {
    use super::*;

    use crate::s0::s0;

    #[test]
    fn closure_must_have_matching_containing_set() -> Result<(), ExecutionError> {
        let module = s0("
            module test {
                entry: containing () receiving () {
                    closure = closure containing ()
                        branch return = entry@1;
                    -> closure return;
                }

                entry@1: containing (incorrect) receiving () {
                    -> incorrect unused;
                }
            }");

        let mut env = Environment::new();
        let result = module.execute(&mut env);
        assert_eq!(result, Err(ExecutionError::MismatchedContaining));
        Ok(())
    }

    #[test]
    fn closure_must_have_matching_receiving_set() -> Result<(), ExecutionError> {
        let module = s0("
            module test {
                entry: containing () receiving () {
                    closure = closure containing ()
                        branch return = entry@1;
                    -> closure return;
                }

                entry@1: containing () receiving (incorrect) {
                    -> incorrect unused;
                }
            }");

        let mut env = Environment::new();
        let result = module.execute(&mut env);
        assert_eq!(result, Err(ExecutionError::MismatchedReceiving));
        Ok(())
    }
}

//-------------------------------------------------------------------------------------------------
// Boxed primitives

/// A primitive that's associated with boxed data on the heap.  If your primitive doesn't need any
/// data, or only needs a single `usize`, you can use `InlinePrimitive`, which doesn't require heap
/// allocations.
pub trait BoxedPrimitive: 'static {
    /// Invokes one of the primitive's branches in the given environment.
    fn invoke(self: Box<Self>, branch: &Name, env: &mut Environment) -> Result<(), ExecutionError>;

    fn as_any(self: Box<Self>) -> Box<dyn Any>;

    fn into_value(self) -> Value
    where
        Self: Sized,
    {
        Value::BoxedPrimitive(Box::new(self))
    }
}

impl Value {
    pub fn into_boxed<V>(self) -> Result<Box<V>, ExecutionError>
    where
        V: BoxedPrimitive,
    {
        match self {
            Value::BoxedPrimitive(boxed) => boxed
                .as_any()
                .downcast()
                .or(Err(ExecutionError::MismatchedPrimitive)),
            _ => Err(ExecutionError::IncorrectValueKind),
        }
    }
}

/// A helper type for implementing the branches for a boxed primitive.
///
/// The primitive's data can be any Rust type, and each branch is anything that implements
/// `BoxedPrimitiveBranch`.  Typically this will be a function or method with the following
/// signature:
///
/// ``` ignore
/// fn invoke(value: Box<V>, env: &mut Environment) -> Result<(), ExecutionError>;
/// ```
pub struct BoxedBranches<V>(HashMap<Name, Box<dyn BoxedPrimitiveBranch<V> + Send + Sync>>);

pub trait BoxedPrimitiveBranch<V> {
    fn invoke(&self, value: Box<V>, env: &mut Environment) -> Result<(), ExecutionError>;
}

impl<V, F> BoxedPrimitiveBranch<V> for F
where
    F: Fn(Box<V>, &mut Environment) -> Result<(), ExecutionError>,
{
    fn invoke(&self, value: Box<V>, env: &mut Environment) -> Result<(), ExecutionError> {
        (*self)(value, env)
    }
}

impl<V> BoxedBranches<V> {
    pub fn new() -> BoxedBranches<V> {
        BoxedBranches(HashMap::new())
    }

    pub fn add<N, B>(mut self, name: N, branch: B) -> Self
    where
        N: Into<Name>,
        B: BoxedPrimitiveBranch<V> + Send + Sync + 'static,
    {
        self.0.insert(name.into(), Box::new(branch));
        self
    }

    pub fn invoke(
        &self,
        value: Box<V>,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branch = self.0.get(branch).ok_or(ExecutionError::UnknownBranch)?;
        branch.invoke(value, env)
    }
}

//-------------------------------------------------------------------------------------------------
// Inline primitives

/// A primitive whose associated data is a single `usize`.  This data is stored directly in the
/// environment, and doesn't require any additional heap allocation.
pub trait InlinePrimitive {
    /// Invokes one of the primitive's branches in the given environment.
    fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError>;
}

pub trait InlinePrimitiveMetadata {
    fn as_static() -> &'static dyn InlinePrimitive;

    fn into_value(value: usize) -> Value {
        Value::InlinePrimitive(value, Self::as_static())
    }
}

impl Value {
    pub fn from_inline<V>(&self) -> Result<usize, ExecutionError>
    where
        V: InlinePrimitiveMetadata,
    {
        match self {
            Value::InlinePrimitive(value, primitive) => {
                if *primitive as *const _ == V::as_static() {
                    Ok(*value)
                } else {
                    Err(ExecutionError::MismatchedPrimitive)
                }
            }
            _ => Err(ExecutionError::IncorrectValueKind),
        }
    }
}

pub trait InlinePrimitiveBranch {
    fn invoke(&self, value: usize, env: &mut Environment) -> Result<(), ExecutionError>;
}

impl<F> InlinePrimitiveBranch for F
where
    F: Fn(usize, &mut Environment) -> Result<(), ExecutionError>,
{
    fn invoke(&self, value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        (*self)(value, env)
    }
}

pub struct InlineBranches(HashMap<Name, Box<dyn InlinePrimitiveBranch + Send + Sync>>);

impl InlineBranches {
    pub fn new() -> InlineBranches {
        InlineBranches(HashMap::new())
    }

    pub fn add<N, B>(mut self, name: N, branch: B) -> Self
    where
        N: Into<Name>,
        B: InlinePrimitiveBranch + Send + Sync + 'static,
    {
        self.0.insert(name.into(), Box::new(branch));
        self
    }

    pub fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branch = self.0.get(branch).ok_or(ExecutionError::UnknownBranch)?;
        branch.invoke(value, env)
    }
}
