//! First-class runtime-observable membership predicates.
//!
//! Semantic types remain richer than what the runtime can inspect directly.
//! Backends and the interpreter therefore answer runtime-membership questions
//! by projecting semantic types into this explicit predicate layer.

use crate::finite_set::FiniteSet;
use crate::fz_ir::Module;
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind, struct_schema_id};
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
    pub(crate) closures: bool,
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
            closures: false,
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
            closures: true,
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
            || (self.closures && other.closures)
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

pub(crate) fn matches_runtime_type_predicate(
    predicate: &RuntimeTypePredicate,
    module: &Module,
    value: RuntimeAnyValue,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
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
            ValueKind::CLOSURE => predicate.closures,
            ValueKind::RESOURCE => predicate.resources,
            ValueKind::STRUCT => matches_runtime_struct(predicate, module, value, tuple_schema_ids, named_schema_ids),
            ValueKind::NULL | ValueKind::INT | ValueKind::FLOAT | ValueKind::ATOM => false,
            _ => false,
        },
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
