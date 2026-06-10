//! Compiler2's callee-owned type-definition facts.
//!
//! A [`TypeDef`] is what a `@type` declaration names once resolved: a hard
//! compiler2 [`Ty`], plus the type-variable ids standing for its formal
//! parameters. A monomorphic `@type t :: integer` has no parameters and a
//! concrete `ty`; a parametric `@type box(a) :: list(a)` stores a template over
//! its parameter vars, which a use site instantiates by substitution.
//!
//! The store mirrors [`super::contract::FunctionContractMap`]: a callee owns
//! its resolved surface, and `DeriveTypeDef` publishes it under the type's
//! [`TypeName`] identity for referencing consumers to read.

use std::collections::HashMap;

use super::identity::TypeName;
use super::types::{Sigma, Ty, TypeVarId, Types};

/// A `@type` declaration resolved to a hard type. For a parametric type the
/// `ty` is a template over `params` — the formal parameters in declaration
/// order, mapped to `TypeVarId(0..params.len())`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeDef {
    pub ty: Ty,
    pub params: Vec<TypeVarId>,
}

impl TypeDef {
    /// Instantiates this definition at a use site by substituting `args` for the
    /// formal parameters. A monomorphic definition (or a use that supplies no
    /// arguments) returns `ty` unchanged.
    pub fn instantiate(&self, types: &mut Types, args: &[Ty]) -> Ty {
        if self.params.is_empty() || args.is_empty() {
            return self.ty;
        }
        let sigma: Sigma<Ty> = self.params.iter().copied().zip(args.iter().copied()).collect();
        types.instantiate(&self.ty, &sigma)
    }
}

#[derive(Debug, Clone)]
struct TypeDefSlot {
    def: TypeDef,
}

/// Type-name → resolved definition, keyed by the full [`TypeName`] identity so
/// `t` and `t(a)` (distinct arities) never conflate.
#[derive(Debug, Default)]
pub struct TypeDefMap {
    slots: HashMap<TypeName, TypeDefSlot>,
}

impl TypeDefMap {
    pub fn new() -> Self {
        Self::default()
    }

    /// Publishes `def` under `name`. An unchanged definition keeps its
    /// revision; a changed one bumps it, so the `TypeDefined` fact only wakes
    /// consumers when the resolved type actually moved.
    pub fn define(&mut self, name: TypeName, def: TypeDef, current_revision: u64) -> u64 {
        let changed = self.slots.get(&name).map(|s| s.def != def).unwrap_or(true);
        self.slots.insert(name, TypeDefSlot { def });
        if changed {
            current_revision + 1
        } else {
            current_revision
        }
    }

    pub fn get(&self, name: &TypeName) -> Option<&TypeDef> {
        self.slots.get(name).map(|slot| &slot.def)
    }
}
