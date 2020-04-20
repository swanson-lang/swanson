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

//! Some useful primitives for the S₀ interpreter.
//!
//! ## Best practices
//!
//! - The values that are closed over in a closure should have `snake_case` names.
//! - The branches of an invocable should have `snake_case` names.
//! - Any continuation passed into an invocable (i.e., a closure passed in that will be invoked
//!   when its done) should have a `$dollar_prefixed_snake_case` name.
//! - Any other inputs to an invocable should have `snake_case` names.
//! - The outputs from an invocable (i.e., the inputs passed into a continution) should have names
//!   that start with `$`.
//! - If a primitive returns a copy of itself as an output (so that it can be reused again), that
//!   output's name should be `$_`.
//! - If there is a single output from an invocable, it should be called `$0`.
//! - If the invocable has multiple outputs, they should either all have `$[digit]` names (in which
//!   case it should be "obvious" why a particular output is output #0 vs #1); or they should all
//!   have `$dollar_snake_case` names (if you need the names to describe the meaning of each
//!   output).

use std::any::Any;
use std::sync::Arc;

use once_cell::sync::Lazy;

use crate::interpreter::BoxedBranches;
use crate::interpreter::BoxedPrimitive;
use crate::interpreter::Environment;
use crate::interpreter::ExecutionError;
use crate::interpreter::InlineBranches;
use crate::interpreter::InlinePrimitive;
use crate::interpreter::InlinePrimitiveMetadata;
use crate::interpreter::Value;
use crate::s0::Module;
use crate::s0::Name;

impl Module {
    pub fn execute_and_get_result(
        self: Arc<Self>,
        env: &mut Environment,
    ) -> Result<Value, ExecutionError> {
        env.add("Finish", Finish::as_value())?;
        self.execute(env)?;
        let result = env.remove(&"result")?;
        assert!(env.is_empty());
        Ok(result)
    }
}

//-------------------------------------------------------------------------------------------------
// Common operations for boxed primitives

fn copy_boxed<V>(value: Box<V>, env: &mut Environment) -> Result<(), ExecutionError>
where
    V: Clone + BoxedPrimitive,
{
    let ret = env.remove(&"return")?;
    env.add("$0", Value::BoxedPrimitive(value.clone()))?;
    env.add("$1", Value::BoxedPrimitive(value))?;
    ret.invoke(&"return".into(), env)
}

fn drop_boxed<V>(_value: Box<V>, env: &mut Environment) -> Result<(), ExecutionError>
where
    V: 'static,
{
    let ret = env.remove(&"return")?;
    ret.invoke(&"return".into(), env)
}

//-------------------------------------------------------------------------------------------------
// Common operations for inline primitives

fn drop_inline(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
    let ret = env.remove(&"return")?;
    ret.invoke(&"return".into(), env)
}

//-------------------------------------------------------------------------------------------------
// Finishing execution

#[derive(Debug)]
pub struct Finish;

impl Finish {
    fn as_value() -> Value {
        Self::into_value(0)
    }

    fn succeed(_value: usize, _env: &mut Environment) -> Result<(), ExecutionError> {
        Ok(())
    }

    fn unreachable(_value: usize, _env: &mut Environment) -> Result<(), ExecutionError> {
        unreachable!();
    }
}

impl InlinePrimitiveMetadata for Finish {
    fn as_static() -> &'static dyn InlinePrimitive {
        static PRIMITIVE: Finish = Finish;
        &PRIMITIVE
    }
}

impl InlinePrimitive for Finish {
    fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branches = Lazy::new(|| {
            InlineBranches::new()
                .add("succeed", Finish::succeed)
                .add("unreachable", Finish::unreachable)
        });
        branches.invoke(value, branch, env)
    }
}

//-------------------------------------------------------------------------------------------------
// Strings

#[derive(Debug)]
struct StringNamespace;

impl StringNamespace {
    fn as_value() -> Value {
        Self::into_value(0)
    }

    fn from_literal(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"return")?;
        let content = env.remove(&"content")?.as_literal()?;
        let content = String::from_utf8(content.into_content()).expect("Invalid UTF-8 content");
        env.add("$_", StringNamespace::as_value())?;
        env.add("$0", Value::from_string(content))?;
        ret.invoke(&"return".into(), env)
    }
}

impl InlinePrimitiveMetadata for StringNamespace {
    fn as_static() -> &'static dyn InlinePrimitive {
        static PRIMITIVE: StringNamespace = StringNamespace;
        &PRIMITIVE
    }
}

impl InlinePrimitive for StringNamespace {
    fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branches = Lazy::new(|| {
            InlineBranches::new()
                .add("drop", drop_inline)
                .add("from_literal", StringNamespace::from_literal)
        });
        branches.invoke(value, branch, env)
    }
}

pub trait StringValue {
    fn from_string(value: String) -> Value;
    fn into_string(self) -> Result<String, ExecutionError>;
}

impl StringValue for Value {
    fn from_string(value: String) -> Value {
        StringPrimitive(value).into_value()
    }

    fn into_string(self) -> Result<String, ExecutionError> {
        Ok(self.into_boxed::<StringPrimitive>()?.0)
    }
}

#[derive(Clone, Debug)]
struct StringPrimitive(String);

impl StringPrimitive {
    fn append_string(mut self: Box<Self>, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"return")?;
        let rhs = env.remove(&"rhs")?.into_string()?;
        self.0.push_str(&rhs);
        env.add("$0", self.into_value())?;
        ret.invoke(&"return".into(), env)
    }
}

impl BoxedPrimitive for StringPrimitive {
    fn invoke(self: Box<Self>, branch: &Name, env: &mut Environment) -> Result<(), ExecutionError> {
        let branches = Lazy::new(|| {
            BoxedBranches::new()
                .add("append", StringPrimitive::append_string)
                .add("copy", copy_boxed)
                .add("drop", drop_boxed)
        });
        branches.invoke(self, branch, env)
    }

    fn as_any(self: Box<Self>) -> Box<dyn Any> {
        self
    }
}

#[cfg(test)]
mod string_tests {
    use super::*;

    use crate::s1::s1;

    #[test]
    fn can_produce_string() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (String, Finish) {
                    content = literal hello;
                    String::from_literal(content) -> ($_, $0);
                    $_::drop();
                    Finish::succeed(result <- $0);
                }
            }");
        let mut env = Environment::new();
        env.add("String", StringNamespace::as_value())?;
        let result = module.execute_and_get_result(&mut env)?.into_string()?;
        assert_eq!(result, "hello");
        Ok(())
    }

    #[test]
    fn can_duplicate_string() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (String, Finish) {
                    content = literal hello;
                    String::from_literal(content) -> ($_, $0);
                    $_::drop();
                    $0::copy() -> ($0, $1);
                    $0::append(rhs <- $1) -> ($0);
                    Finish::succeed(result <- $0);
                }
            }");
        let mut env = Environment::new();
        env.add("String", StringNamespace::as_value())?;
        let result = module.execute_and_get_result(&mut env)?.into_string()?;
        assert_eq!(result, "hellohello");
        Ok(())
    }
}

//-------------------------------------------------------------------------------------------------
// Booleans

#[derive(Debug)]
struct BooleanNamespace;

impl BooleanNamespace {
    fn as_value() -> Value {
        Self::into_value(0)
    }

    fn r#false(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"return")?;
        env.add("$_", BooleanNamespace::as_value())?;
        env.add("$0", Value::from_boolean(false))?;
        ret.invoke(&"return".into(), env)
    }

    fn r#true(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"return")?;
        env.add("$_", BooleanNamespace::as_value())?;
        env.add("$0", Value::from_boolean(true))?;
        ret.invoke(&"return".into(), env)
    }
}

impl InlinePrimitiveMetadata for BooleanNamespace {
    fn as_static() -> &'static dyn InlinePrimitive {
        static PRIMITIVE: BooleanNamespace = BooleanNamespace;
        &PRIMITIVE
    }
}

impl InlinePrimitive for BooleanNamespace {
    fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branches = Lazy::new(|| {
            InlineBranches::new()
                .add("drop", drop_inline)
                .add("false", BooleanNamespace::r#false)
                .add("true", BooleanNamespace::r#true)
        });
        branches.invoke(value, branch, env)
    }
}

pub trait BooleanValue {
    fn from_boolean(value: bool) -> Value;
    fn is_boolean(&self, expected: bool) -> bool;
}

impl BooleanValue for Value {
    fn from_boolean(value: bool) -> Value {
        if value {
            TruePrimitive::into_value(0)
        } else {
            FalsePrimitive::into_value(0)
        }
    }

    fn is_boolean(&self, expected: bool) -> bool {
        if expected {
            self.from_inline::<TruePrimitive>().is_ok()
        } else {
            self.from_inline::<FalsePrimitive>().is_ok()
        }
    }
}

#[derive(Debug)]
struct FalsePrimitive;

impl FalsePrimitive {
    fn eval(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"eval")?;
        ret.invoke(&"false".into(), env)
    }

    fn not(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"return")?;
        env.add("$0", Value::from_boolean(true))?;
        ret.invoke(&"return".into(), env)
    }
}

impl InlinePrimitiveMetadata for FalsePrimitive {
    fn as_static() -> &'static dyn InlinePrimitive {
        static PRIMITIVE: FalsePrimitive = FalsePrimitive;
        &PRIMITIVE
    }
}

impl InlinePrimitive for FalsePrimitive {
    fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branches = Lazy::new(|| {
            InlineBranches::new()
                .add("eval", FalsePrimitive::eval)
                .add("not", FalsePrimitive::not)
        });
        branches.invoke(value, branch, env)
    }
}

#[derive(Debug)]
struct TruePrimitive;

impl TruePrimitive {
    fn eval(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"eval")?;
        ret.invoke(&"true".into(), env)
    }

    fn not(_value: usize, env: &mut Environment) -> Result<(), ExecutionError> {
        let ret = env.remove(&"return")?;
        env.add("$0", Value::from_boolean(false))?;
        ret.invoke(&"return".into(), env)
    }
}

impl InlinePrimitiveMetadata for TruePrimitive {
    fn as_static() -> &'static dyn InlinePrimitive {
        static PRIMITIVE: TruePrimitive = TruePrimitive;
        &PRIMITIVE
    }
}

impl InlinePrimitive for TruePrimitive {
    fn invoke(
        &self,
        value: usize,
        branch: &Name,
        env: &mut Environment,
    ) -> Result<(), ExecutionError> {
        let branches = Lazy::new(|| {
            InlineBranches::new()
                .add("eval", TruePrimitive::eval)
                .add("not", TruePrimitive::not)
        });
        branches.invoke(value, branch, env)
    }
}

#[cfg(test)]
mod boolean_tests {
    use super::*;

    use crate::s1::s1;

    #[test]
    fn can_produce_false() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (Boolean, Finish) {
                    Boolean::false() -> ($_, $0);
                    $_::drop();
                    Finish::succeed(result <- $0);
                }
            }");
        let mut env = Environment::new();
        env.add("Boolean", BooleanNamespace::as_value())?;
        let result = module.execute_and_get_result(&mut env)?;
        assert!(result.is_boolean(false));
        Ok(())
    }

    #[test]
    fn can_negate_false() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (Boolean, Finish) {
                    Boolean::false() -> ($_, $0);
                    $_::drop();
                    $0::not() -> ($0);
                    Finish::succeed(result <- $0);
                }
            }");
        let mut env = Environment::new();
        env.add("Boolean", BooleanNamespace::as_value())?;
        let result = module.execute_and_get_result(&mut env)?;
        assert!(result.is_boolean(true));
        Ok(())
    }

    #[test]
    fn can_eval_false() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (Boolean, Finish) {
                    Boolean::false() -> ($_, $0);
                    $_::drop();
                    $0::eval()
                      eval (Finish)
                        ::true ->() {
                            Finish::unreachable();
                        }
                        ::false ->() {
                            Finish::succeed();
                        };
                }
            }");
        let mut env = Environment::new();
        env.add("Boolean", BooleanNamespace::as_value())?;
        env.add("Finish", Finish::as_value())?;
        module.execute(&mut env)?;
        Ok(())
    }

    #[test]
    fn can_produce_true() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (Boolean, Finish) {
                    Boolean::true() -> ($_, $0);
                    $_::drop();
                    Finish::succeed(result <- $0);
                }
            }");
        let mut env = Environment::new();
        env.add("Boolean", BooleanNamespace::as_value())?;
        let result = module.execute_and_get_result(&mut env)?;
        assert!(result.is_boolean(true));
        Ok(())
    }

    #[test]
    fn can_negate_true() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (Boolean, Finish) {
                    Boolean::true() -> ($_, $0);
                    $_::drop();
                    $0::not() -> ($0);
                    Finish::succeed(result <- $0);
                }
            }");
        let mut env = Environment::new();
        env.add("Boolean", BooleanNamespace::as_value())?;
        let result = module.execute_and_get_result(&mut env)?;
        assert!(result.is_boolean(false));
        Ok(())
    }

    #[test]
    fn can_eval_true() -> Result<(), ExecutionError> {
        let module = s1("
            module test {
                entry: containing () receiving (Boolean, Finish) {
                    Boolean::true() -> ($_, $0);
                    $_::drop();
                    $0::eval()
                      eval (Finish)
                        ::true ->() {
                            Finish::succeed();
                        }
                        ::false ->() {
                            Finish::unreachable();
                        };
                }
            }");
        let mut env = Environment::new();
        env.add("Boolean", BooleanNamespace::as_value())?;
        env.add("Finish", Finish::as_value())?;
        module.execute(&mut env)?;
        Ok(())
    }
}
