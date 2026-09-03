//! Stable facts used to canonicalize activation keys.
//!
//! `DispatchDemand` is the lattice both halves of [`InputDemand`] live in: what
//! a body asks about one input, shaped like the type it asks about. `Ignore` is
//! the bottom (nothing is asked), `Whole` the top (the value itself is the
//! answer), and `ListShape`/`TupleFields` say the question descends into one
//! structural position. It is a lattice because a slot can be asked about from
//! more than one place -- two clauses of one body, and, since fz-kdt.183, every
//! callee this body hands the slot on to -- and `join_assign` is its least
//! upper bound.

use std::collections::BTreeMap;

use super::identity::FunctionId;

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

#[derive(Debug, Clone)]
pub(crate) struct FunctionFactMap<T> {
    slots: Vec<Option<T>>,
}

/// The body-shape keying fact `Job::DeriveCallGraphComponent` publishes under
/// `FactKey::Recursive`: both answers live in one value so a consumer can
/// never observe one without the other.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BodyKeying {
    /// Reaches itself through the static call graph: its activation keys
    /// convergence-collapse so the ascent settles (fz-y6w).
    pub(crate) recursive: bool,
    /// Calls through a callable, constructs a lambda, or is a capture-holding
    /// lambda: closure brands are meaning to this body, so its keys stay
    /// precise. A body with neither treats brands as freight (fz-6gb).
    pub(crate) consumes_callable_identity: bool,
}

/// What one function's inputs are DEMANDED for, as `Job::DeriveInputDemand`
/// publishes it under `FactKey::InputDemand`: both halves live in one value so
/// a consumer can never observe one without the other, exactly as
/// [`BodyKeying`] carries two answers behind `FactKey::Recursive`.
///
/// The two halves answer two different questions and neither stands in for the
/// other. `local_dispatch` is "does a clause of THIS body ask about this slot"
/// -- the question closure-brand erasure has always asked (fz-6gb): a body that
/// never tests a slot cannot tell two same-shape lambdas apart there.
/// `forwarded_dispatch` is "does this activation's published RETURN depend on
/// this slot" -- which includes everything the callees this body hands the slot
/// to depend on, because the value that arrives decides which callee activation
/// is reached and therefore what comes back (fz-kdt.183).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct InputDemand {
    /// This body's own entry dispatch, one demand per semantic input.
    pub(crate) local_dispatch: Vec<DispatchDemand>,
    /// `local_dispatch` joined with the demand of every callee this body
    /// forwards each input to, transitively (fz-kdt.183). Always at least as
    /// high as `local_dispatch` slot for slot.
    pub(crate) forwarded_dispatch: Vec<DispatchDemand>,
}

pub(crate) type BodyKeyingMap = FunctionFactMap<BodyKeying>;
pub(crate) type InputDemandMap = FunctionFactMap<InputDemand>;

/// The call graph's edge store: the static callees `FactKey::StaticCallees`
/// publishes for each function, ascending by function id.
pub(crate) type StaticCalleeMap = FunctionFactMap<Vec<FunctionId>>;

/// The call graph's component store: the canonical id `FactKey::CallGraphComponent`
/// publishes for each function -- the SMALLEST `FunctionId` in that function's
/// strong component of the static call graph.
///
/// The canonical member is what makes membership a comparison rather than a
/// traversal: two functions are mutually reachable exactly when their stored
/// ids are equal, because a strong component is a set and its minimum is a
/// function of that set alone.
pub(crate) type CallGraphComponentMap = FunctionFactMap<FunctionId>;

impl<T> FunctionFactMap<T>
where
    T: Clone + PartialEq,
{
    pub(crate) fn new() -> Self {
        Self { slots: Vec::new() }
    }

    pub(crate) fn define(&mut self, function: FunctionId, value: T) -> bool {
        self.ensure(function);
        let slot = &mut self.slots[function.as_u32() as usize];
        let changed = slot.as_ref() != Some(&value);
        *slot = Some(value);
        changed
    }

    pub(crate) fn get(&self, function: FunctionId) -> Option<&T> {
        self.slots.get(function.as_u32() as usize)?.as_ref()
    }

    fn ensure(&mut self, function: FunctionId) {
        let needed = function.as_u32() as usize + 1;
        if self.slots.len() < needed {
            self.slots.resize_with(needed, || None);
        }
    }
}

impl<T> Default for FunctionFactMap<T> {
    fn default() -> Self {
        Self { slots: Vec::new() }
    }
}
