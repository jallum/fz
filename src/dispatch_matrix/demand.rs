//! What a dispatch question asks of a value.
//!
//! `DispatchDemand` is a lattice. `Ignore` is the bottom -- nothing is asked --
//! and `Whole` is the top -- the value itself is the answer. Between them,
//! `TupleFields` and `ListShape` say the question descends into a structural
//! position of that kind and asks nothing of the rest. Which position, and what
//! is asked beyond it, is not carried: no reader of a demand distinguishes one
//! tuple field from another. A slot can be asked about from more than one
//! place, so `join_assign` raises a demand to the least upper bound of what it
//! already held and what the new question asks, and two questions that descend
//! through different kinds meet at `Whole`.
//!
//! A projection is one step into a value's structure, and
//! `demand_at_projection` reads it in the detail the lattice carries and no
//! finer -- which tuple field, which struct name, which map key all fall away.
//! Only a tuple field and a list head descend; a struct field, a list tail, a
//! map value and a bitstring field are positions the lattice cannot name, so a
//! question reached through one of them collapses to `Whole`.

use super::ProjectionKind;

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum DispatchDemand {
    #[default]
    Ignore,
    Whole,
    TupleFields,
    ListShape,
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
            (Self::ListShape, Self::ListShape) | (Self::TupleFields, Self::TupleFields) => {}
            (slot, _) => *slot = Self::Whole,
        }
    }
}

/// What a question reached through one projection asks of the value the
/// projection reads from.
pub(crate) fn demand_at_projection(kind: &ProjectionKind) -> DispatchDemand {
    match kind {
        ProjectionKind::TupleField(_) => DispatchDemand::TupleFields,
        ProjectionKind::ListHead => DispatchDemand::ListShape,
        ProjectionKind::StructField(_)
        | ProjectionKind::ListTail
        | ProjectionKind::MapValue { .. }
        | ProjectionKind::BitstringField(_) => DispatchDemand::Whole,
    }
}

#[cfg(test)]
#[path = "demand_test.rs"]
mod demand_test;
