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
//! `demand_at_path` turns a path and the demand at its end into the demand on
//! the value the path started from.

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

pub(crate) fn demand_at_path(path: &[DemandPathStep], demand: DispatchDemand) -> DispatchDemand {
    let Some((head, tail)) = path.split_first() else {
        return demand;
    };
    match head {
        DemandPathStep::TupleField(field) => {
            let mut fields = BTreeMap::new();
            fields.insert(*field, demand_at_path(tail, demand));
            DispatchDemand::TupleFields(fields)
        }
        DemandPathStep::ListHead => DispatchDemand::ListShape(Box::new(demand_at_path(tail, demand))),
        DemandPathStep::ListTail
        | DemandPathStep::MapValue
        | DemandPathStep::StructField
        | DemandPathStep::BitstringField => DispatchDemand::Whole,
    }
}

#[cfg(test)]
#[path = "demand_test.rs"]
mod demand_test;
