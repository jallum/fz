use crate::fz_ir::Module;
use crate::types::{Ty as LegacyTy, ty_descr};
use fz_runtime::any_value::{AnyValue as RuntimeAnyValue, ValueKind, struct_schema_id};
use std::collections::{BTreeSet, HashMap};
use std::fmt;

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ListShape {
    Empty,
    NonEmpty,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ObservedSet<T> {
    pub(crate) cofinite: bool,
    pub(crate) values: BTreeSet<T>,
}

impl<T> Default for ObservedSet<T> {
    fn default() -> Self {
        Self {
            cofinite: false,
            values: BTreeSet::new(),
        }
    }
}

impl<T: Ord> ObservedSet<T> {
    pub(crate) fn none() -> Self {
        Self::default()
    }

    pub(crate) fn any() -> Self {
        Self {
            cofinite: true,
            values: BTreeSet::new(),
        }
    }

    pub(crate) fn lit(value: T) -> Self {
        Self::finite([value])
    }

    pub(crate) fn finite(values: impl IntoIterator<Item = T>) -> Self {
        Self {
            cofinite: false,
            values: values.into_iter().collect(),
        }
    }

    pub(crate) fn cofinite(values: impl IntoIterator<Item = T>) -> Self {
        Self {
            cofinite: true,
            values: values.into_iter().collect(),
        }
    }

    pub(crate) fn is_none(&self) -> bool {
        !self.cofinite && self.values.is_empty()
    }

    pub(crate) fn is_any(&self) -> bool {
        self.cofinite && self.values.is_empty()
    }

    pub(crate) fn contains(&self, value: &T) -> bool {
        self.values.contains(value) != self.cofinite
    }
}

impl<T: Ord + Clone> ObservedSet<T> {
    pub(crate) fn union(&self, other: &Self) -> Self {
        match (self.cofinite, other.cofinite) {
            (false, false) => Self::finite(self.values.union(&other.values).cloned()),
            (true, false) => Self::cofinite(self.values.difference(&other.values).cloned()),
            (false, true) => Self::cofinite(other.values.difference(&self.values).cloned()),
            (true, true) => Self::cofinite(self.values.intersection(&other.values).cloned()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct RuntimeTypeTestShim {
    pub(crate) ints: ObservedSet<i64>,
    pub(crate) floats: ObservedSet<u64>,
    pub(crate) atoms: ObservedSet<String>,
    pub(crate) lists: ObservedSet<ListShape>,
    pub(crate) tuple_arities: ObservedSet<usize>,
    pub(crate) named_structs: ObservedSet<String>,
    pub(crate) allow_other_structs: bool,
    pub(crate) maps: bool,
    pub(crate) binaries: bool,
    pub(crate) closures: bool,
    pub(crate) resources: bool,
}

impl RuntimeTypeTestShim {
    pub(crate) fn none() -> Self {
        Self {
            ints: ObservedSet::none(),
            floats: ObservedSet::none(),
            atoms: ObservedSet::none(),
            lists: ObservedSet::none(),
            tuple_arities: ObservedSet::none(),
            named_structs: ObservedSet::none(),
            allow_other_structs: false,
            maps: false,
            binaries: false,
            closures: false,
            resources: false,
        }
    }

    pub(crate) fn any() -> Self {
        Self {
            ints: ObservedSet::any(),
            floats: ObservedSet::any(),
            atoms: ObservedSet::any(),
            lists: ObservedSet::any(),
            tuple_arities: ObservedSet::any(),
            named_structs: ObservedSet::any(),
            allow_other_structs: true,
            maps: true,
            binaries: true,
            closures: true,
            resources: true,
        }
    }

    pub(crate) fn tuple_arity(arity: usize) -> Self {
        let mut shim = Self::none();
        shim.tuple_arities = ObservedSet::lit(arity);
        shim
    }

    pub(crate) fn named_struct(name: impl Into<String>) -> Self {
        let mut shim = Self::none();
        shim.named_structs = ObservedSet::lit(name.into());
        shim
    }

    pub(crate) fn map_kind() -> Self {
        let mut shim = Self::none();
        shim.maps = true;
        shim
    }

    pub(crate) fn has_structs(&self) -> bool {
        !self.tuple_arities.is_none() || !self.named_structs.is_none() || self.allow_other_structs
    }
}

impl Default for RuntimeTypeTestShim {
    fn default() -> Self {
        Self::none()
    }
}

impl fmt::Display for RuntimeTypeTestShim {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{self:?}")
    }
}

pub(crate) fn matches_runtime_any_value(
    shim: &RuntimeTypeTestShim,
    module: &Module,
    value: RuntimeAnyValue,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
) -> bool {
    match value {
        RuntimeAnyValue::Null => false,
        RuntimeAnyValue::EmptyList => shim.lists.contains(&ListShape::Empty),
        RuntimeAnyValue::Int(value) => shim.ints.contains(&value),
        RuntimeAnyValue::Float(bits) => shim.floats.contains(&bits),
        RuntimeAnyValue::Atom(atom_id) => mapped_membership(&shim.atoms, atom_id, |name| {
            module
                .atom_names
                .iter()
                .position(|candidate| candidate == name)
                .map(|idx| idx as u32)
        }),
        RuntimeAnyValue::HeapRef(value_ref) => match value_ref.tag() {
            ValueKind::LIST => shim.lists.contains(&ListShape::NonEmpty),
            ValueKind::MAP => shim.maps,
            ValueKind::BITSTRING => shim.binaries,
            ValueKind::CLOSURE => shim.closures,
            ValueKind::RESOURCE => shim.resources,
            ValueKind::STRUCT => matches_runtime_struct(shim, module, value, tuple_schema_ids, named_schema_ids),
            ValueKind::NULL | ValueKind::INT | ValueKind::FLOAT | ValueKind::ATOM => false,
            _ => false,
        },
    }
}

pub(crate) fn from_legacy_ty(ty: &LegacyTy) -> RuntimeTypeTestShim {
    let descr = ty_descr(ty);
    RuntimeTypeTestShim {
        ints: ObservedSet {
            cofinite: descr.ints.cofinite,
            values: descr.ints.set.iter().copied().collect(),
        },
        floats: ObservedSet {
            cofinite: descr.floats.cofinite,
            values: descr.floats.set.iter().map(|bits| bits.get().to_bits()).collect(),
        },
        atoms: ObservedSet {
            cofinite: descr.atoms.cofinite,
            values: descr.atoms.set.iter().cloned().collect(),
        },
        lists: legacy_list_shapes(descr),
        tuple_arities: legacy_tuple_arities(descr),
        named_structs: legacy_named_structs(descr),
        allow_other_structs: false,
        maps: !descr.maps.is_empty(),
        binaries: !descr.basic.is_empty(),
        closures: !descr.funcs.is_empty(),
        resources: !descr.resources.is_empty(),
    }
}

fn legacy_list_shapes(descr: &crate::types::Descr) -> ObservedSet<ListShape> {
    let mut out = ObservedSet::none();
    for clause in &descr.lists {
        let mut allowed = ObservedSet::finite([ListShape::Empty, ListShape::NonEmpty]);
        for sig in &clause.pos {
            let sig_allowed = if sig.empty && sig.elem.is_none() {
                ObservedSet::lit(ListShape::Empty)
            } else if !sig.empty && sig.elem.is_some() {
                ObservedSet::lit(ListShape::NonEmpty)
            } else {
                ObservedSet::finite([ListShape::Empty, ListShape::NonEmpty])
            };
            allowed = intersect_observed_sets(&allowed, &sig_allowed);
        }
        for sig in &clause.neg {
            if sig.empty && sig.elem.is_none() {
                allowed = remove_observed_value(&allowed, &ListShape::Empty);
            } else if !sig.empty && sig.elem.is_some() {
                allowed = remove_observed_value(&allowed, &ListShape::NonEmpty);
            }
        }
        out = out.union(&allowed);
    }
    out
}

fn legacy_tuple_arities(descr: &crate::types::Descr) -> ObservedSet<usize> {
    let mut out = ObservedSet::none();
    for clause in &descr.tuples {
        let mut allowed = if clause.pos.is_empty() {
            ObservedSet::any()
        } else {
            let mut arities = clause.pos.iter().map(|sig| sig.elems.len()).collect::<BTreeSet<_>>();
            if arities.len() != 1 {
                continue;
            }
            ObservedSet::lit(arities.pop_first().expect("one arity"))
        };
        for sig in &clause.neg {
            allowed = remove_observed_value(&allowed, &sig.elems.len());
        }
        out = out.union(&allowed);
    }
    out
}

fn legacy_named_structs(descr: &crate::types::Descr) -> ObservedSet<String> {
    const PREFIX: &str = "impl-target::";
    ObservedSet {
        cofinite: descr.opaques.cofinite,
        values: descr
            .opaques
            .set
            .iter()
            .filter_map(|name| name.strip_prefix(PREFIX).map(str::to_string))
            .collect(),
    }
}

fn intersect_observed_sets<T>(left: &ObservedSet<T>, right: &ObservedSet<T>) -> ObservedSet<T>
where
    T: Ord + Clone,
{
    match (left.cofinite, right.cofinite) {
        (false, false) => ObservedSet::finite(left.values.intersection(&right.values).cloned()),
        (true, false) => ObservedSet::finite(right.values.difference(&left.values).cloned()),
        (false, true) => ObservedSet::finite(left.values.difference(&right.values).cloned()),
        (true, true) => ObservedSet::cofinite(left.values.union(&right.values).cloned()),
    }
}

fn remove_observed_value<T>(set: &ObservedSet<T>, value: &T) -> ObservedSet<T>
where
    T: Ord + Clone,
{
    if set.cofinite {
        let mut excluded = set.values.clone();
        excluded.insert(value.clone());
        ObservedSet::cofinite(excluded)
    } else {
        ObservedSet::finite(set.values.iter().filter(|candidate| *candidate != value).cloned())
    }
}

fn mapped_membership<T, U>(set: &ObservedSet<T>, actual: U, mut map: impl FnMut(&T) -> Option<U>) -> bool
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
    shim: &RuntimeTypeTestShim,
    module: &Module,
    value: RuntimeAnyValue,
    tuple_schema_ids: &HashMap<usize, u32>,
    named_schema_ids: &HashMap<String, u32>,
) -> bool {
    if !shim.has_structs() {
        return false;
    }
    if shim.allow_other_structs && shim.tuple_arities.is_any() && shim.named_structs.is_any() {
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
    let tuple_match = if shim.tuple_arities.is_none() {
        false
    } else if shim.tuple_arities.is_any() {
        !known_named.contains(&actual_schema)
    } else {
        let tuple_ids = shim
            .tuple_arities
            .values
            .iter()
            .filter_map(|arity| tuple_schema_ids.get(arity).copied())
            .collect::<BTreeSet<_>>();
        if shim.tuple_arities.cofinite {
            !known_named.contains(&actual_schema) && !tuple_ids.contains(&actual_schema)
        } else {
            tuple_ids.contains(&actual_schema)
        }
    };
    let named_match = if shim.named_structs.is_none() {
        false
    } else if shim.named_structs.is_any() {
        known_named.contains(&actual_schema)
    } else {
        let relevant = shim
            .named_structs
            .values
            .iter()
            .filter_map(|name| named_schema_ids.get(name).copied())
            .collect::<BTreeSet<_>>();
        if shim.named_structs.cofinite {
            known_named.contains(&actual_schema) && !relevant.contains(&actual_schema)
        } else {
            relevant.contains(&actual_schema)
        }
    };
    let known_tuple = shim
        .tuple_arities
        .values
        .iter()
        .filter_map(|arity| tuple_schema_ids.get(arity).copied())
        .collect::<BTreeSet<_>>();
    let other_match =
        shim.allow_other_structs && !known_named.contains(&actual_schema) && !known_tuple.contains(&actual_schema);
    tuple_match || named_match || other_match
}
