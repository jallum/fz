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
/// is reached and therefore what comes back (fz-kdt.183). `returned` is the
/// other way a return depends on an input: not "which activation is reached"
/// but "the returned value IS this input position" (fz-kdt.199).
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct InputDemand {
    /// This body's own entry dispatch, one demand per semantic input.
    pub(crate) local_dispatch: Vec<DispatchDemand>,
    /// `local_dispatch` joined with the demand of every callee this body
    /// forwards each input to, transitively (fz-kdt.183). Always at least as
    /// high as `local_dispatch` slot for slot.
    pub(crate) forwarded_dispatch: Vec<DispatchDemand>,
    /// Where this activation's published RETURN is BUILT FROM: the input
    /// positions the returned value is, contains, or is a projection of --
    /// this body's own returns joined with the returns of every callee it
    /// forwards an input to, transitively (fz-kdt.199), MINUS the positions
    /// the recursion itself supplies (`recursion_supplied_positions`).
    ///
    /// It is the DUAL of `forwarded_dispatch` and it lives on its own axis
    /// because the two ask for different collapses. A dispatched position is
    /// a QUESTION, and `Whole` there means "the value itself is the answer",
    /// so the key keeps it verbatim. A returned position is an ANSWER, and
    /// `Whole` here means "this value is the return", so the key keeps its
    /// ground CLASS: list families normalise to `list(elem)` with the element
    /// kept at every depth, and callable brands still erase.
    /// `Types::convergence_class_at` caps depth at `ADDRESS_COLLAPSE_DEPTH`
    /// for LIST families only -- the cap is checked inside its
    /// `is_pure_list_family` branch, so a tuple, map or resource nest at a
    /// returned position recurses uncapped and is bounded only by the type
    /// that arrives. Every program built to exercise that (a self-nesting or
    /// mutually nesting accumulator) already fails to terminate at base for
    /// fz-kdt.177's reason, so the uncapped case is a reading of the code, not
    /// a measured divergence. Joining the two axes into one mask would have to
    /// raise a returned position to `Whole`, which has no collapse at all
    /// (fz-kdt.200) -- so they stay two.
    pub(crate) returned: Vec<DispatchDemand>,
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
