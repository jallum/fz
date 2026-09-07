//! Stable facts used to canonicalize activation keys.
//!
//! `DispatchDemand` is the lattice for each of [`InputDemand`]'s local,
//! forwarded, and returned projections: what a body asks about one input,
//! shaped like the type it asks about. `Ignore` is
//! the bottom (nothing is asked), `Whole` the top (the value itself is the
//! answer), and `ListShape`/`TupleFields` say the question descends into one
//! structural position. It is a lattice because a slot can be asked about from
//! more than one place -- two clauses of one body, and, since fz-kdt.183, every
//! callee this body hands the slot on to -- and `join_assign` is its least
//! upper bound.

use std::collections::BTreeMap;

use super::body::CallSiteId;
use super::identity::FunctionId;
use crate::ground_value::GroundValue;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)]
pub(crate) enum DispatchDemand {
    #[default]
    Ignore,
    Whole,
    TupleFields(BTreeMap<u32, DispatchDemand>),
    ListShape(Box<DispatchDemand>),
}

/// One structural step from a semantic input root.
///
/// These are semantic positions, not rendered type fragments. A path is
/// therefore stable across type-arena allocation order and can be compared,
/// deduplicated, and retained without asking a `Ty` for display text.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum InputPathStep {
    TupleField(u32),
    ListHead,
    ListTail,
    MapValue(MapSelector),
    MapKey(MapSelector),
    /// The base of a map update after the named fields have been replaced.
    MapRemainder(Box<[InputMapKey]>),
    BitstringField(BitstringSelector),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum MapSelector {
    Known(InputMapKey),
    Dynamic,
    DynamicExcept(Box<[InputMapKey]>),
}

/// One literal runtime map key in the local flow relation.
///
/// Raw and UTF-8-branded binaries denote the same runtime key here; the brand
/// is dispatch evidence, not map-key identity.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum InputMapKey {
    Int(i64),
    Float(u64),
    Atom(String),
    Binary(Box<[u8]>),
}

impl InputMapKey {
    pub(crate) fn from_ground(value: &GroundValue) -> Self {
        match value {
            GroundValue::Int(value) => Self::Int(*value),
            GroundValue::Float(bits) => Self::Float(*bits),
            GroundValue::Atom(value) => Self::Atom(value.clone()),
            GroundValue::Bool(value) => Self::Atom(value.to_string()),
            GroundValue::Nil => Self::Atom("nil".to_string()),
            GroundValue::Binary(bytes) | GroundValue::Utf8Binary(bytes) => {
                Self::Binary(bytes.clone().into_boxed_slice())
            }
        }
    }
}

impl MapSelector {
    pub(crate) fn dynamic_excluding(mut excluded: Vec<InputMapKey>) -> Self {
        excluded.sort_unstable();
        excluded.dedup();
        if excluded.is_empty() {
            Self::Dynamic
        } else {
            Self::DynamicExcept(excluded.into_boxed_slice())
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum BitstringSelector {
    Known(u32),
    Dynamic,
}

/// An exact position below one function input.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InputPosition {
    pub(crate) input: usize,
    pub(crate) path: Box<[InputPathStep]>,
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum InputFlowOrigin {
    Input(InputPosition),
    CallResult {
        callsite: CallSiteId,
        path: Box<[InputPathStep]>,
    },
}

impl InputPosition {
    pub(crate) fn root(input: usize) -> Self {
        Self {
            input,
            path: Box::default(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum CallableInputUse {
    ClosureCall(CallSiteId),
    LambdaCapture { function: FunctionId, capture: usize },
}

/// The normalized semantic destination of one value origin.
///
/// Projection and reconstruction are expressed only by the origin and sink
/// paths. How many local SSA hops happened between them is deliberately not
/// identity: direct and project/rebuild routes with the same endpoints are
/// the same fact.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum InputFlowSink {
    FunctionReturn(Box<[InputPathStep]>),
    ProtocolInput {
        callee: FunctionId,
        input: InputPosition,
    },
    CallableUse {
        site: CallableInputUse,
        path: Box<[InputPathStep]>,
    },
}

/// How demand at a sink is pulled back through one retained provenance edge.
///
/// Most values transport structure, so a demanded sink path maps to the same
/// subtree of the origin. Some values merely decide the result (for example a
/// dynamic map key): any use of the selected result needs that entire origin,
/// independently of which result subtree is later inspected.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum InputPullback {
    Structural,
    WholeOrigin,
}

/// One normalized terminal, protocol, or callable-use path transfer.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InputFlow {
    pub(crate) origin: InputFlowOrigin,
    pub(crate) sink: InputFlowSink,
    pub(crate) pullback: InputPullback,
}

/// One semantic origin bound into a direct-call input path.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct InputBinding {
    pub(crate) origin: InputFlowOrigin,
    pub(crate) path: Box<[InputPathStep]>,
    pub(crate) pullback: InputPullback,
}

/// The complete input binding owned by one direct callsite.
///
/// The slice index is the callee input. An empty set means that input is
/// supplied entirely locally; an empty slice is a zero-argument call.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct DirectCallFlow {
    pub(crate) callee: FunctionId,
    pub(crate) inputs: Box<[std::collections::BTreeSet<InputBinding>]>,
}

/// The immutable, deterministic input-flow extraction for one function.
///
/// `local_dispatch` is the body's own typed question. `direct_calls` owns every
/// direct call and its complete input bindings; `flows` owns function returns,
/// protocol inputs, and callable-use sites. Together they are the one
/// extraction authority used by every InputDemand dimension; the fixpoint over
/// functions remains a separate concern.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct InputFlowRelation {
    pub(crate) local_dispatch: Box<[DispatchDemand]>,
    pub(crate) direct_calls: BTreeMap<CallSiteId, DirectCallFlow>,
    pub(crate) flows: std::collections::BTreeSet<InputFlow>,
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

/// The three current activation-key projections of one retained
/// [`InputFlowRelation`]. They are published together so consumers cannot see
/// dimensions derived from different relation generations.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) struct InputDemand {
    /// This body's own entry dispatch, one demand per semantic input.
    pub(crate) local_dispatch: Vec<DispatchDemand>,
    /// Entry questions pulled back through exact local paths and exact
    /// callsites, transitively. Callee-local questions apply at every site;
    /// result-induced questions return only through the site whose result was
    /// used.
    pub(crate) forwarded_dispatch: Vec<DispatchDemand>,
    /// Return demand pulled backward through reconstruction, projection,
    /// delivery, protocol forwarding, and exact callsite result/input pairs.
    ///
    /// It remains separate from dispatch because an input used as an answer
    /// and one used as a question require different key collapses. Local and
    /// acyclic composition are exact; recursive SCC demand alone is widened
    /// soundly below a fixed structural frontier in the current finite demand
    /// lattice. fz-kdt.200 replaces that lattice and deletes the normalizer.
    pub(crate) returned: Vec<DispatchDemand>,
}

pub(crate) type BodyKeyingMap = FunctionFactMap<BodyKeying>;
pub(crate) type InputDemandMap = FunctionFactMap<InputDemand>;
pub(crate) type InputFlowRelationMap = FunctionFactMap<InputFlowRelation>;

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
    T: PartialEq,
{
    pub(crate) fn new() -> Self {
        Self { slots: Vec::new() }
    }

    pub(crate) fn define(&mut self, function: FunctionId, value: T) -> bool {
        self.ensure(function);
        let slot = &mut self.slots[function.as_u32() as usize];
        if slot.as_ref() == Some(&value) {
            return false;
        }
        *slot = Some(value);
        true
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
