//! What a dispatch question asks of a value, shaped like the value it asks
//! about.
//!
//! `DispatchDemand` is a lattice. `Ignore` is the bottom -- nothing is asked --
//! and `Whole` is the top -- the value itself is the answer. Between them,
//! `TupleFields` and `ListShape` say the question descends into one structural
//! position and asks nothing of the rest. A slot can be asked about from more
//! than one place, so `join_assign` raises a demand to the least upper bound of
//! what it already held and what the new question asks.
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

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum DispatchDemand {
    #[default]
    Ignore,
    Whole,
    TupleFields(BTreeMap<u32, DispatchDemand>),
    ListShape(Box<DispatchDemand>),
}

impl DispatchDemand {
    /// Whether anything at all is asked of the value.
    pub(crate) fn asks_anything(&self) -> bool {
        *self != Self::Ignore
    }

    pub(crate) fn join_assign(&mut self, other: DispatchDemand) {
        match (self, other) {
            (Self::Whole, _) | (_, Self::Ignore) => {}
            (slot @ Self::Ignore, next) => *slot = next,
            (slot, Self::Whole) => *slot = Self::Whole,
            (Self::ListShape(current), Self::ListShape(next)) => current.join_assign(*next),
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
        DemandPathStep::ListTail
        | DemandPathStep::MapValue
        | DemandPathStep::StructField
        | DemandPathStep::BitstringField => DispatchDemand::Whole,
    }
}

/// The same, for a whole path: the demand at the path's end travels back
/// through each step to the value the path started from.
pub(crate) fn demand_at_path(path: &[DemandPathStep], demand: DispatchDemand) -> DispatchDemand {
    path.iter()
        .rev()
        .fold(demand, |demand, step| demand_at_step(step, demand))
}

#[cfg(test)]
#[path = "demand_test.rs"]
mod demand_test;
