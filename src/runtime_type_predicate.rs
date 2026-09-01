//! First-class runtime-observable membership predicates.
//!
//! Semantic types remain richer than what the runtime can inspect directly.
//! Backends and the interpreter therefore answer runtime-membership questions
//! by projecting semantic types into this explicit predicate layer.

use crate::finite_set::FiniteSet;
use crate::fz_ir::Module;
use crate::types::ClosureTarget;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind, closure_fn_ptr, struct_schema_id};
use std::collections::{BTreeSet, HashMap};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ListShape {
    Empty,
    NonEmpty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeTypePredicate {
    pub(crate) ints: FiniteSet<i64>,
    pub(crate) floats: FiniteSet<u64>,
    pub(crate) atoms: FiniteSet<String>,
    pub(crate) lists: FiniteSet<ListShape>,
    pub(crate) tuple_arities: FiniteSet<usize>,
    pub(crate) named_structs: FiniteSet<String>,
    pub(crate) allow_other_structs: bool,
    pub(crate) maps: bool,
    pub(crate) binaries: bool,
    /// WHICH callable, not merely "a callable". A closure value's heap word at
    /// `+8` is the code it was minted from, so the callable a value is IS
    /// runtime-observable and belongs on the same finite-or-cofinite footing as
    /// an atom or a tuple arity (fz-kdt.125).
    pub(crate) callables: FiniteSet<ClosureTarget>,
    pub(crate) resources: bool,
}

impl RuntimeTypePredicate {
    pub(crate) fn none() -> Self {
        Self {
            ints: FiniteSet::none(),
            floats: FiniteSet::none(),
            atoms: FiniteSet::none(),
            lists: FiniteSet::none(),
            tuple_arities: FiniteSet::none(),
            named_structs: FiniteSet::none(),
            allow_other_structs: false,
            maps: false,
            binaries: false,
            callables: FiniteSet::none(),
            resources: false,
        }
    }

    pub(crate) fn any() -> Self {
        Self {
            ints: FiniteSet::any(),
            floats: FiniteSet::any(),
            atoms: FiniteSet::any(),
            lists: FiniteSet::any(),
            tuple_arities: FiniteSet::any(),
            named_structs: FiniteSet::any(),
            allow_other_structs: true,
            maps: true,
            binaries: true,
            callables: FiniteSet::any(),
            resources: true,
        }
    }

    pub(crate) fn tuple_arity(arity: usize) -> Self {
        let mut predicate = Self::none();
        predicate.tuple_arities = FiniteSet::lit(arity);
        predicate
    }

    pub(crate) fn named_struct(name: impl Into<String>) -> Self {
        let mut predicate = Self::none();
        predicate.named_structs = FiniteSet::lit(name.into());
        predicate
    }

    pub(crate) fn map_kind() -> Self {
        let mut predicate = Self::none();
        predicate.maps = true;
        predicate
    }

    pub(crate) fn has_structs(&self) -> bool {
        !self.tuple_arities.is_none() || !self.named_structs.is_none() || self.allow_other_structs
    }

    /// Whether every value this predicate's test admits, `other`'s admits too.
    ///
    /// Axis by axis, because the axes are independent: a value reaches exactly
    /// one of them, so a test that admits more on every axis admits more,
    /// full stop. This is CONTAINMENT OF TESTS, not of the semantic types the
    /// tests were projected from -- `{:halt, :false}` and
    /// `{:cont, :true} | {:halt, :false}` are two types and one test.
    ///
    /// It is what the runtime ASKS, and that is exactly why it does not settle
    /// a dispatch's arm order on its own. A test is a projection and it drops
    /// what the body reads: list shape erases the elements, tuple arity erases
    /// the payloads. So a value can satisfy every question an arm asks and
    /// still lie outside the surface that arm's body was compiled for, and
    /// seating on this relation alone hands it to a body that never named it
    /// (fz-kdt.131). `callsite_dispatch::covers` is the conjunct that makes a
    /// seat sound; this is one half of it.
    pub(crate) fn contained_in(&self, other: &Self) -> bool {
        other.ints.contains_all(&self.ints)
            && other.floats.contains_all(&self.floats)
            && other.atoms.contains_all(&self.atoms)
            && other.lists.contains_all(&self.lists)
            && other.tuple_arities.contains_all(&self.tuple_arities)
            && other.named_structs.contains_all(&self.named_structs)
            && (other.allow_other_structs || !self.allow_other_structs)
            && (other.maps || !self.maps)
            && (other.binaries || !self.binaries)
            && other.callables.contains_all(&self.callables)
            && (other.resources || !self.resources)
    }

    /// Whether the two tests can both admit a value on an axis whose
    /// projection ERASES something a body reads: list elements, tuple
    /// payloads, struct fields, map fields, binary contents, resource
    /// payloads. On those axes "the tests differ" is not separation --
    /// tuple arities {2} and {2,3} both admit a 2-tuple, list shapes
    /// {NonEmpty} and {Empty, NonEmpty} both admit a cons cell -- so a
    /// dispatch seat may not skip the surface-coverage check there. The
    /// exact axes (ints, floats, atoms, callables) are deliberately
    /// absent: a value passes those tests only by being in the tested
    /// set, which the arm's surface names.
    pub(crate) fn overlaps_on_an_erasing_axis(&self, other: &Self) -> bool {
        self.lists.overlaps(&other.lists)
            || self.tuple_arities.overlaps(&other.tuple_arities)
            || self.named_structs.overlaps(&other.named_structs)
            || (self.allow_other_structs && other.allow_other_structs)
            || (self.maps && other.maps)
            || (self.binaries && other.binaries)
            || (self.resources && other.resources)
    }

    pub(crate) fn overlaps(&self, other: &Self) -> bool {
        self.ints.overlaps(&other.ints)
            || self.floats.overlaps(&other.floats)
            || self.atoms.overlaps(&other.atoms)
            || self.lists.overlaps(&other.lists)
            || self.tuple_arities.overlaps(&other.tuple_arities)
            || self.named_structs.overlaps(&other.named_structs)
            || (self.allow_other_structs && other.allow_other_structs)
            || (self.maps && other.maps)
            || (self.binaries && other.binaries)
            || self.callables.overlaps(&other.callables)
            || (self.resources && other.resources)
    }
}

impl Default for RuntimeTypePredicate {
    fn default() -> Self {
        Self::none()
    }
}

impl fmt::Display for RuntimeTypePredicate {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

/// Which callable a runtime code word denotes.
///
/// The word a closure carries at `+8` is the backend's, not the type lattice's:
/// one callable can be minted through several code paths, and a backend is free
/// to name them however it likes. The backend that minted them is therefore the
/// authority on reading them back, and it answers here. `None` is a code word
/// the program never described, which no finite callable set can name.
pub(crate) type CallableIdentities<'a> = dyn Fn(u64) -> Option<ClosureTarget> + 'a;

pub(crate) fn matches_runtime_type_predicate(
    predicate: &RuntimeTypePredicate,
    module: &Module,
    value: RuntimeAnyValue,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
    callables: &CallableIdentities<'_>,
) -> bool {
    match value {
        RuntimeAnyValue::Null => false,
        RuntimeAnyValue::EmptyList => predicate.lists.contains(&ListShape::Empty),
        RuntimeAnyValue::Int(value) => predicate.ints.contains(&value),
        RuntimeAnyValue::Float(bits) => predicate.floats.contains(&bits),
        RuntimeAnyValue::Atom(atom_id) => mapped_membership(&predicate.atoms, atom_id, |name| {
            module
                .atom_names
                .iter()
                .position(|candidate| candidate == name)
                .map(|idx| idx as u32)
        }),
        RuntimeAnyValue::HeapRef(value_ref) => match value_ref.tag() {
            ValueKind::LIST => predicate.lists.contains(&ListShape::NonEmpty),
            ValueKind::MAP => predicate.maps,
            ValueKind::BITSTRING => predicate.binaries,
            ValueKind::CLOSURE => matches_runtime_callable(predicate, value, callables),
            ValueKind::RESOURCE => predicate.resources,
            ValueKind::STRUCT => matches_runtime_struct(predicate, module, value, tuple_schema_ids, named_schema_ids),
            ValueKind::NULL | ValueKind::INT | ValueKind::FLOAT | ValueKind::ATOM => false,
            _ => false,
        },
    }
}

/// Read a closure value's identity and ask the predicate about it.
///
/// A cofinite callable set names every callable but the ones it lists, so a
/// code word the backend cannot place is in it: the value is a callable, and
/// none of the excluded ones.
fn matches_runtime_callable(
    predicate: &RuntimeTypePredicate,
    value: RuntimeAnyValue,
    callables: &CallableIdentities<'_>,
) -> bool {
    if predicate.callables.is_none() {
        return false;
    }
    if predicate.callables.is_any() {
        return true;
    }
    let Some(addr) = value.heap_addr() else {
        return false;
    };
    match callables(unsafe { closure_fn_ptr(addr.cast_const()) }) {
        Some(target) => predicate.callables.contains(&target),
        None => predicate.callables.cofinite,
    }
}

fn mapped_membership<T, U>(set: &FiniteSet<T>, actual: U, mut map: impl FnMut(&T) -> Option<U>) -> bool
where
    T: Ord,
    U: Ord,
{
    set.values
        .iter()
        .filter_map(&mut map)
        .collect::<BTreeSet<_>>()
        .contains(&actual)
        != set.cofinite
}

fn matches_runtime_struct(
    predicate: &RuntimeTypePredicate,
    module: &Module,
    value: RuntimeAnyValue,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
) -> bool {
    if !predicate.has_structs() {
        return false;
    }
    if predicate.allow_other_structs && predicate.tuple_arities.is_any() && predicate.named_structs.is_any() {
        return true;
    }
    let Some(ptr) = value.heap_addr() else {
        return false;
    };
    let actual_schema = unsafe { struct_schema_id(ptr.cast_const()) };
    let known_named = module
        .struct_schemas
        .keys()
        .filter_map(|name| named_schema_ids.get(name).copied())
        .collect::<BTreeSet<_>>();
    let tuple_match = if predicate.tuple_arities.is_none() {
        false
    } else if predicate.tuple_arities.is_any() {
        !known_named.contains(&actual_schema)
    } else {
        let tuple_ids = predicate
            .tuple_arities
            .values
            .iter()
            .filter_map(|arity| tuple_schema_ids.get(arity).copied())
            .collect::<BTreeSet<_>>();
        if predicate.tuple_arities.cofinite {
            !known_named.contains(&actual_schema) && !tuple_ids.contains(&actual_schema)
        } else {
            tuple_ids.contains(&actual_schema)
        }
    };
    let named_match = if predicate.named_structs.is_none() {
        false
    } else if predicate.named_structs.is_any() {
        known_named.contains(&actual_schema)
    } else {
        let relevant = predicate
            .named_structs
            .values
            .iter()
            .filter_map(|name| named_schema_ids.get(name).copied())
            .collect::<BTreeSet<_>>();
        if predicate.named_structs.cofinite {
            known_named.contains(&actual_schema) && !relevant.contains(&actual_schema)
        } else {
            relevant.contains(&actual_schema)
        }
    };
    let known_tuple = predicate
        .tuple_arities
        .values
        .iter()
        .filter_map(|arity| tuple_schema_ids.get(arity).copied())
        .collect::<BTreeSet<_>>();
    let other_match =
        predicate.allow_other_structs && !known_named.contains(&actual_schema) && !known_tuple.contains(&actual_schema);
    tuple_match || named_match || other_match
}
