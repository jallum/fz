//! What a dispatch question asks of a value, shaped like the value it asks
//! about.
//!
//! `DispatchDemand` is a lattice. `Ignore` is the bottom -- nothing is asked --
//! and `Whole` is the top -- the value itself is the answer. `Class` sits just
//! above the bottom: the value is read, but nothing that reads it can tell one
//! literal from another, so a key may name its kind and drop which literal it
//! was. `TupleFields` and `ListShape` say the question descends into one
//! structural position and asks nothing of the rest. A slot can be asked about
//! from more than one place, so `join_assign` raises a demand to the least
//! upper bound of what it already held and what the new question asks:
//! `Ignore < Class < {TupleFields, ListShape} < Whole`.
//!
//! A `DemandPathStep` is one step into a value's structure in the detail the
//! lattice carries. Only a tuple field and a list head descend; a struct field,
//! a list tail, a map value and a bitstring field are positions the lattice
//! cannot name, so a question reached through one of them collapses to `Whole`.
//! `demand_at_step` turns one step and the demand beyond it into the demand on
//! the value the step was taken from, and `demand_at_path` folds a whole path
//! that way, from its end back to the value it started from.

use std::collections::BTreeMap;

use super::ProjectionKind;

#[derive(Debug, Clone, PartialEq, Eq, Hash, Default)]
pub(crate) enum DispatchDemand {
    #[default]
    Ignore,
    /// Read, but literal-blind: no reader tells one atom from another.
    Class,
    Whole,
    TupleFields(BTreeMap<u32, DispatchDemand>),
    ListShape(Box<DispatchDemand>),
    /// The question descends into the values a map or struct holds, and asks
    /// the same of each. It is never `Whole` (that is `Whole`) and never
    /// nothing (that is `Ignore`).
    MapValues(Box<DispatchDemand>),
}

impl DispatchDemand {
    /// Whether anything at all is asked of the value.
    pub(crate) fn asks_anything(&self) -> bool {
        *self != Self::Ignore
    }

    pub(crate) fn join_assign(&mut self, other: DispatchDemand) {
        match (self, other) {
            (Self::Whole, _) | (_, Self::Ignore) => {}
            (slot @ (Self::Ignore | Self::Class), next) => *slot = next,
            (_, Self::Class) => {}
            (slot, Self::Whole) => *slot = Self::Whole,
            (Self::ListShape(current), Self::ListShape(next)) => current.join_assign(*next),
            (Self::MapValues(current), Self::MapValues(next)) => current.join_assign(*next),
            (Self::TupleFields(current), Self::TupleFields(next)) => {
                for (field, demand) in next {
                    current.entry(field).or_default().join_assign(demand);
                }
            }
            (slot, _) => *slot = Self::Whole,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum DemandPathStep {
    StructField,
    TupleField(u32),
    ListHead,
    ListTail,
    MapValue,
    BitstringField,
}

impl From<&ProjectionKind> for DemandPathStep {
    fn from(kind: &ProjectionKind) -> Self {
        match kind {
            ProjectionKind::TupleField(index) => DemandPathStep::TupleField(*index),
            ProjectionKind::StructField(_) => DemandPathStep::StructField,
            ProjectionKind::ListHead => DemandPathStep::ListHead,
            ProjectionKind::ListTail => DemandPathStep::ListTail,
            ProjectionKind::MapValue { .. } => DemandPathStep::MapValue,
            ProjectionKind::BitstringField(_) => DemandPathStep::BitstringField,
        }
    }
}

/// What a demand beyond one step asks of the value the step was taken from.
pub(crate) fn demand_at_step(step: &DemandPathStep, demand: DispatchDemand) -> DispatchDemand {
    match step {
        DemandPathStep::TupleField(field) => DispatchDemand::TupleFields(BTreeMap::from([(*field, demand)])),
        DemandPathStep::ListHead => DispatchDemand::ListShape(Box::new(demand)),
        // A tail, a bitstring field and a struct or map value are positions the
        // lattice names only as far as the question goes: a map's values are
        // asked about together, and the rest are the whole value to anyone who
        // asks. Nothing asked, or nothing that could tell one literal from
        // another, holds of the value however deep the position sits.
        DemandPathStep::MapValue | DemandPathStep::StructField => match demand {
            DispatchDemand::Ignore | DispatchDemand::Class | DispatchDemand::Whole => demand,
            DispatchDemand::TupleFields(_) | DispatchDemand::ListShape(_) | DispatchDemand::MapValues(_) => {
                DispatchDemand::MapValues(Box::new(demand))
            }
        },
        DemandPathStep::ListTail | DemandPathStep::BitstringField => match demand {
            DispatchDemand::Ignore | DispatchDemand::Class => demand,
            DispatchDemand::Whole
            | DispatchDemand::TupleFields(_)
            | DispatchDemand::ListShape(_)
            | DispatchDemand::MapValues(_) => DispatchDemand::Whole,
        },
    }
}

/// The same, for a whole path: the demand at the path's end travels back
/// through each step to the value the path started from.
///
/// The one step this reads more finely than [`demand_at_step`] is a list's
/// tail: the tail is a list of the same shape, so a question about its
/// elements is a question about the elements of the list it is the tail of.
/// That is what lets `count(t)` in `count([_ | t])` ask of `t` what the
/// recursion asks of the whole.
pub(crate) fn demand_at_path(path: &[DemandPathStep], demand: DispatchDemand) -> DispatchDemand {
    path.iter().rev().fold(demand, |demand, step| match (step, demand) {
        (DemandPathStep::ListTail, shape @ DispatchDemand::ListShape(_)) => shape,
        (step, demand) => demand_at_step(step, demand),
    })
}

/// What a demand on a value asks of the position one step INSIDE it: the
/// inverse of [`demand_at_step`]. A demand that asks nothing, or nothing that
/// tells one literal from another, asks the same of every position inside; a
/// demand that names the value's structure asks of a position what the
/// structure says, and of a position it cannot name, everything.
pub(crate) fn demand_within_step(demand: &DispatchDemand, step: &DemandPathStep) -> DispatchDemand {
    use DispatchDemand::{Class, Ignore, ListShape, MapValues, TupleFields, Whole};
    match (demand, step) {
        (Ignore, _) => Ignore,
        (Class, _) => Class,
        (TupleFields(fields), DemandPathStep::TupleField(field)) => fields.get(field).cloned().unwrap_or(Ignore),
        (ListShape(element), DemandPathStep::ListHead) => (**element).clone(),
        (ListShape(_), DemandPathStep::ListTail) => demand.clone(),
        (MapValues(values), DemandPathStep::MapValue | DemandPathStep::StructField) => (**values).clone(),
        _ => Whole,
    }
}

/// [`demand_within_step`] along a whole path, outermost step first.
pub(crate) fn demand_within_path(demand: &DispatchDemand, path: &[DemandPathStep]) -> DispatchDemand {
    path.iter()
        .fold(demand.clone(), |demand, step| demand_within_step(&demand, step))
}

impl DispatchDemand {
    /// How many structural steps the demand descends before it asks about a
    /// value outright.
    pub(crate) fn depth(&self) -> usize {
        match self {
            Self::Ignore | Self::Class | Self::Whole => 0,
            Self::ListShape(element) | Self::MapValues(element) => 1 + element.depth(),
            Self::TupleFields(fields) => 1 + fields.values().map(Self::depth).max().unwrap_or(0),
        }
    }
}

#[cfg(test)]
#[path = "demand_test.rs"]
mod demand_test;
