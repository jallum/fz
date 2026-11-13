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
//! protocol-impl-target classification, and root-local backend packaging)
//! reads it, directly or through
//! [`super::world::World::struct_def_fields`]. There is no source-form scan
//! left to fall back to — a struct defined through a macro-emitted
//! `defstruct` is visible here exactly like a source-written one.
//!
//! [`StructReferenceExpectation`], [`StructFieldExpectation`], and
//! [`StructExpectationMap`] are this store's obligation half, mirroring
//! [`super::module_interface::InterfaceExpectation`]/`ModuleInterface`'s
//! expectation list: a reference to `%A{...}` is recordable before `A`'s
//! `defstruct` publishes, and any referenced `A.field` is checked against
//! whichever side settles second (see
//! `World::note_struct_reference_expectation`,
//! `World::note_struct_field_expectation`, and
//! `World::validate_struct_field_expectations`).

use crate::fast_hash::HashMap;

use crate::ast::{Expr, Spanned};
use crate::ground_value::GroundValue;
use crate::source::Span;

use super::identity::ModuleId;
use super::module_interface::InterfaceRequester;

/// A `defstruct` declaration resolved for its owning module: the field names
/// in declaration order, the default of each field that declares one, and
/// the declaration's span for provenance. Field *types* live in the module's
/// conventional `@type t`, read separately.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructDef {
    pub(crate) fields: Vec<String>,
    pub(crate) defaults: HashMap<String, LiteralTerm>,
    pub(crate) span: Span,
}

/// A value written out in full: a scalar, or a list, tuple or map of such
/// values. It names nothing, so it means the same wherever it is read. A
/// field default is one, which is why a struct literal in any module can
/// start from it.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LiteralTerm {
    Ground(GroundValue),
    List(Vec<LiteralTerm>),
    Tuple(Vec<LiteralTerm>),
    Map(Vec<(LiteralTerm, LiteralTerm)>),
}

impl LiteralTerm {
    /// `expr` as a literal term, or `None` when it computes or names anything.
    pub(crate) fn of(expr: &Expr) -> Option<Self> {
        let all = |items: &[Spanned<Expr>]| {
            items
                .iter()
                .map(|item| Self::of(&item.node))
                .collect::<Option<Vec<_>>>()
        };
        Some(match expr {
            Expr::Int(value) => Self::Ground(GroundValue::Int(*value)),
            Expr::Float(value) => Self::Ground(GroundValue::from_f64(*value)),
            Expr::Binary(bytes) => Self::Ground(GroundValue::Binary(bytes.clone())),
            Expr::Atom(name) => Self::Ground(GroundValue::Atom(name.clone())),
            Expr::Bool(value) => Self::Ground(GroundValue::Bool(*value)),
            Expr::Nil => Self::Ground(GroundValue::Nil),
            Expr::List(items, None) => Self::List(all(items)?),
            Expr::Tuple(items) => Self::Tuple(all(items)?),
            Expr::Map(entries) => Self::Map(
                entries
                    .iter()
                    .map(|(key, value)| Some((Self::of(&key.node)?, Self::of(&value.node)?)))
                    .collect::<Option<_>>()?,
            ),
            _ => return None,
        })
    }

    /// The expression that writes this term, placed at `span`.
    pub(crate) fn expr(&self, span: Span) -> Spanned<Expr> {
        let all = |items: &[LiteralTerm]| items.iter().map(|item| item.expr(span)).collect();
        let node = match self {
            Self::Ground(GroundValue::Int(value)) => Expr::Int(*value),
            Self::Ground(GroundValue::Float(bits)) => Expr::Float(f64::from_bits(*bits)),
            Self::Ground(GroundValue::Binary(bytes) | GroundValue::Utf8Binary(bytes)) => Expr::Binary(bytes.clone()),
            Self::Ground(GroundValue::Atom(name)) => Expr::Atom(name.clone()),
            Self::Ground(GroundValue::Bool(value)) => Expr::Bool(*value),
            Self::Ground(GroundValue::Nil) => Expr::Nil,
            Self::List(items) => Expr::List(all(items), None),
            Self::Tuple(items) => Expr::Tuple(all(items)),
            Self::Map(entries) => Expr::Map(
                entries
                    .iter()
                    .map(|(key, value)| (key.expr(span), value.expr(span)))
                    .collect(),
            ),
        };
        Spanned::new(node, span)
    }
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

/// One `%A{...}` obligation: a struct-record use recorded the struct's owning
/// module, from `requester`, even if it named no fields.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct StructReferenceExpectation {
    pub(crate) requester: InterfaceRequester,
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
    references: HashMap<ModuleId, Vec<StructReferenceExpectation>>,
    fields: HashMap<ModuleId, Vec<StructFieldExpectation>>,
}

impl StructExpectationMap {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Records one module-level obligation, deduplicating identical requesters
    /// so re-scoping the same reference site stays idempotent.
    pub(crate) fn record_reference(&mut self, module: ModuleId, expectation: StructReferenceExpectation) {
        let list = self.references.entry(module).or_default();
        if !list.contains(&expectation) {
            list.push(expectation);
        }
    }

    /// Records one field obligation, deduplicating identical (field,
    /// requester) pairs so re-scoping the same reference site stays
    /// idempotent.
    pub(crate) fn record_field(&mut self, module: ModuleId, expectation: StructFieldExpectation) {
        let list = self.fields.entry(module).or_default();
        if !list.contains(&expectation) {
            list.push(expectation);
        }
    }

    pub(crate) fn reference_expectations(&self, module: ModuleId) -> &[StructReferenceExpectation] {
        self.references.get(&module).map(Vec::as_slice).unwrap_or(&[])
    }

    pub(crate) fn field_expectations(&self, module: ModuleId) -> &[StructFieldExpectation] {
        self.fields.get(&module).map(Vec::as_slice).unwrap_or(&[])
    }
}

#[cfg(test)]
#[path = "structdef_test.rs"]
mod structdef_test;
