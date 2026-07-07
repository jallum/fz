//! Compiler2's callee-owned `defstruct` facts.
//!
//! A [`StructDef`] is what a `defstruct` declaration names once its owning
//! module body settles: the ordered field names a struct literal/pattern must
//! agree with, plus the declaration's span for diagnostics. The store mirrors
//! [`super::typedef::TypeDefMap`] and [`super::protocol::ProtocolDispatchMap`]:
//! a module owns its `defstruct`, and the module-defining job publishes it
//! under the module's [`ModuleId`] identity for referencing consumers to
//! read.
//!
//! This store is additive: `World::module_struct_fields`/`struct_schemas`
//! still scan `ModuleState` source forms and remain the sole reader of struct
//! schema today. Nothing here is wired to a consumer yet.

use std::collections::HashMap;

use crate::source::Span;

use super::identity::ModuleId;

/// A `defstruct` declaration resolved for its owning module: the field names
/// in declaration order (the only shape `defstruct` itself carries — field
/// *types* live in the module's conventional `@type t`, read separately) plus
/// the declaration's span for provenance.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructDef {
    pub(crate) fields: Vec<String>,
    pub(crate) span: Span,
}

/// Module → resolved `defstruct`, keyed by [`ModuleId`] so each struct-owning
/// module has exactly one definition.
#[derive(Debug, Default)]
pub(crate) struct StructDefMap {
    slots: HashMap<ModuleId, StructDef>,
}

impl StructDefMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Publishes `def` under `module`. An unchanged definition keeps its
    /// revision; a changed one bumps it, so the `StructDefined` fact only
    /// wakes consumers when the recorded fields actually moved.
    pub(crate) fn define(&mut self, module: ModuleId, def: StructDef) -> bool {
        let changed = self.slots.get(&module) != Some(&def);
        self.slots.insert(module, def);
        changed
    }

    pub(crate) fn get(&self, module: ModuleId) -> Option<&StructDef> {
        self.slots.get(&module)
    }
}
