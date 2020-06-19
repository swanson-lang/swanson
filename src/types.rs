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

//! Types for S₀ code.

use std::collections::HashMap;
use std::num::NonZeroUsize;

use crate::s0::Name;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum TypeParameter {
    Unspecified,
    Id(NonZeroUsize),
}

pub struct TypeParameterFamily {
    next_id: NonZeroUsize,
}

impl TypeParameterFamily {
    pub fn new_id(&mut self) -> TypeParameter {
        let result = TypeParameter::Id(self.next_id);
        self.next_id = unsafe { NonZeroUsize::new_unchecked(usize::from(self.next_id) + 1) };
        result
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ValueType {
    Any,
    Atom(TypeParameter),
    Literal,
}

impl ValueType {
    pub fn unify(&self, other: &ValueType) -> Option<ValueType> {
        match self {
            ValueType::Any => ValueType::unify_any(other),
            ValueType::Atom(param) => ValueType::unify_atom(param, other),
            ValueType::Literal => ValueType::unify_literal(other),
        }
    }

    fn unify_any(other: &ValueType) -> Option<ValueType> {
        Some(other.clone())
    }

    fn unify_atom(param: &TypeParameter, other: &ValueType) -> Option<ValueType> {
        match other {
            ValueType::Any => Some(ValueType::Atom(*param)),
            ValueType::Atom(other_param) if param == other_param => Some(ValueType::Atom(*param)),
            _ => None,
        }
    }

    fn unify_literal(other: &ValueType) -> Option<ValueType> {
        match other {
            ValueType::Any => Some(ValueType::Literal),
            ValueType::Literal => Some(ValueType::Literal),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum EnvironmentGlob {
    /// The rest of the environment must be empty — that is, the environment type specifies
    /// _exactly_ which values must exist.
    Empty,
    /// The environment can contain additional values besides what the type specifies.
    Any(TypeParameter),
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EnvironmentType {
    pub values: HashMap<Name, ValueType>,
    pub glob: EnvironmentGlob,
}
