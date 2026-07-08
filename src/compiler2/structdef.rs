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
//! This store is the single source of truth for struct schemas: every
//! consumer (type resolution, struct-literal/pattern lowering,
//! protocol-impl-target classification, and the backend's whole-program
//! schema inventory) reads it, directly or through
//! [`super::world::World::struct_def_fields`]. There is no source-form scan
//! left to fall back to — a struct defined through a macro-emitted
//! `defstruct` is visible here exactly like a source-written one.
//!
//! [`StructFieldExpectation`] and [`StructExpectationMap`] are this store's
//! obligation half, mirroring [`super::module_interface::InterfaceExpectation`]/
//! `ModuleInterface`'s expectation list: a reference to `A.field` is
//! recordable before `A`'s `defstruct` publishes, and is checked against
//! whichever side settles second (see `World::note_struct_field_expectation`
//! and `World::validate_struct_field_expectations`).

use std::collections::HashMap;

use crate::source::Span;

use super::identity::ModuleId;
use super::module_interface::InterfaceRequester;

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

    /// Every `defstruct` published so far, for the backend's whole-program
    /// schema inventory — the fact-backed sibling of the deleted
    /// `ModuleStore::named_struct_schemas` source scan.
    pub(crate) fn iter(&self) -> impl Iterator<Item = (ModuleId, &StructDef)> {
        self.slots.iter().map(|(module, def)| (*module, def))
    }
}

/// One `A.field` obligation: a struct-record use recorded field `field` on
/// the struct's owning module, from `requester`. Mirrors
/// [`super::module_interface::InterfaceExpectation`]'s requester-carrying
/// shape one-for-one, reusing [`InterfaceRequester`] itself since "who
/// referenced this and from where" is the same question for a callable
/// import and a struct field.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructFieldExpectation {
    pub(crate) field: String,
    pub(crate) requester: InterfaceRequester,
}

/// Module → outstanding field obligations, keyed by the struct's own
/// [`ModuleId`] exactly like [`StructDefMap`] — so an obligation recorded
/// before `A` is processed lives at the same identity `A`'s `defstruct`
/// later publishes under.
#[derive(Debug, Default)]
pub(crate) struct StructExpectationMap {
    slots: HashMap<ModuleId, Vec<StructFieldExpectation>>,
}

impl StructExpectationMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Records one obligation, deduplicating identical (field, requester)
    /// pairs so re-scoping the same reference site stays idempotent.
    pub(crate) fn record(&mut self, module: ModuleId, expectation: StructFieldExpectation) {
        let list = self.slots.entry(module).or_default();
        if !list.contains(&expectation) {
            list.push(expectation);
        }
    }

    pub(crate) fn expectations(&self, module: ModuleId) -> &[StructFieldExpectation] {
        self.slots.get(&module).map(Vec::as_slice).unwrap_or(&[])
    }
}
