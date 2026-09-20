//! Stable facts used to canonicalize activation keys.
//!
//! Every vector in [`InputDemand`] holds [`DispatchDemand`]: what a body asks
//! about one input, shaped like the type it asks about. A slot is asked about
//! from more than one place -- two clauses of one body, and every callee this
//! body hands the slot on to -- so what is published here is the join of all
//! of them over that lattice.

use crate::dispatch_matrix::demand::DispatchDemand;

use super::identity::FunctionId;

#[derive(Debug, Clone)]
pub(crate) struct FunctionFactMap<T> {
    slots: Vec<Option<T>>,
}

/// The body-shape keying fact `Job::DeriveCallGraphComponent` publishes under
/// `FactKey::Recursive`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct BodyKeying {
    /// Reaches itself through the static call graph.
    pub(crate) recursive: bool,
}

/// What one function's inputs are DEMANDED for, as `Job::DeriveInputDemand`
/// publishes it under `FactKey::InputDemand`.
///
/// There is ONE dispatch question per slot: "does any activation this slot can
/// reach ask about it". It includes every callee this body hands the slot on
/// to, because the value that arrives decides which callee activation is
/// reached, and it includes a closure call -- which asks about the callable and
/// about everything handed to it, because the body being entered is not known
/// here. What a body asks by itself is a step in deriving that answer, never a
/// published one: every consumer -- the coordinate a call site names, the call
/// surface an activation key keeps -- is deciding whether something somewhere
/// can read the slot, and a body that only transports a callable to a callee
/// that calls it has no say in that.
///
/// Dispatch is one of the two ways a value at a slot can be observed from
/// outside the activation. The other is return flow -- the return IS, CONTAINS,
/// or is a PROJECTION OF what arrived -- and that answer is published on
/// `FunctionUnknowns::returned_inputs`, derived from the same position graph
/// that decides which positions are still climbing. `World::observable_inputs`
/// is the single place the two are read together.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct InputDemand {
    /// One demand per semantic input: this body's own entry dispatch, raised to
    /// `Whole` wherever a closure call touches a slot or a lambda captures one,
    /// joined with the demand of every callee this body forwards the input to,
    /// transitively.
    pub(crate) forwarded_dispatch: Vec<DispatchDemand>,
}

pub(crate) type BodyKeyingMap = FunctionFactMap<BodyKeying>;

/// One function's static shape, as `Job::DeriveReturnSkeleton` publishes it
/// under `FactKey::ReturnSkeleton`.
pub(crate) type ReturnSkeletonMap = FunctionFactMap<std::rc::Rc<super::return_skeleton::FunctionSkeleton>>;

/// Which of one function's positions the fixpoint is still solving, as
/// `Job::DeriveReturnUnknowns` publishes it under `FactKey::ReturnUnknowns`.
pub(crate) type ReturnUnknownsMap = FunctionFactMap<std::rc::Rc<super::return_unknowns::FunctionUnknowns>>;
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
