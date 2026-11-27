//! Borrowed comparison of published, finite immutable runtime terms.
//!
//! Map keys always use strict numeric identity, including keys nested in maps
//! whose values are compared with the widening language operators.

use crate::any_value::{
    AnyValue, ListCons, ListTail, MAP_DESTINATION_FLAG, Stored, ValueKind, closure_capture_value,
    closure_captured_count, closure_denotation, map_count, map_entries, map_entry, map_header_is_collision,
    map_header_is_trie, map_key, map_node_child, map_node_child_count, map_node_entry_count, map_slot,
    struct_schema_id,
};
use crate::bits::Bin;
use crate::heap::{Schema, SchemaIdentity, SchemaRegistry, StructKey};
use crate::module_name::STRUCT_MODULE_FIELD;
use crate::process::Node;
use crate::resource::ResourceStub;
use std::cmp::Ordering;
use std::ptr::read;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NumericMode {
    Strict,
    Widening,
}

/// The raw address of a heap value: what dereferencing and identity
/// comparison use, never its payload word. The empty list has no object; its
/// word is the null address the list comparator expects.
pub(crate) fn address(value: AnyValue) -> *mut u8 {
    value.heap_addr().unwrap_or(value.raw() as *mut u8)
}

fn assert_language_value(value: AnyValue) {
    assert_ne!(value.kind(), ValueKind::NULL, "absent carrier is not a language value");
    if value.kind() == ValueKind::MAP {
        assert_eq!(
            unsafe { read(value.heap_addr().expect("map address") as *const u64) } & MAP_DESTINATION_FLAG,
            0,
            "unpublished map is not a language value"
        );
    }
    if let AnyValue::Float(bits) = value {
        assert!(
            f64::from_bits(bits).is_finite(),
            "nonfinite float is not a language value"
        );
    }
}

/// The order of two scalars of one kind from their stored words alone:
/// integers as integers, atoms by name. Any other pair is `None`: a float,
/// whose order the numeric mode decides, a heap value, or two kinds. The mode
/// never matters for the pairs this answers, so no decode, registry or mode is
/// needed to ask.
#[inline(always)]
pub(crate) fn stored_scalar_order(node: &Node, a: Stored, b: Stored) -> Option<Ordering> {
    if a.kind != b.kind {
        return None;
    }
    if a.kind == u64::from(ValueKind::INT.tag()) {
        return Some((a.word as i64).cmp(&(b.word as i64)));
    }
    if a.kind == u64::from(ValueKind::ATOM.tag()) {
        return Some(node.cmp_atom_ids(a.word as u32, b.word as u32));
    }
    None
}

/// Whether two scalars of one kind are equal, from their stored words alone:
/// integers and atoms by word. `None` for any other pair, as
/// [`stored_scalar_order`].
#[inline(always)]
pub(crate) fn stored_scalar_equal(a: Stored, b: Stored) -> Option<bool> {
    let scalar = |kind: ValueKind| a.kind == u64::from(kind.tag()) && b.kind == a.kind;
    (scalar(ValueKind::INT) || scalar(ValueKind::ATOM)).then_some(a.word == b.word)
}

pub struct TermComparator<'a> {
    node: &'a Node,
    schemas: &'a SchemaRegistry,
}

impl<'a> TermComparator<'a> {
    pub fn new(node: &'a Node, schemas: &'a SchemaRegistry) -> Self {
        Self { node, schemas }
    }

    /// The order of two language values. Each is checked to be one here,
    /// once; the values inside them are published with them.
    pub fn compare(&self, a: AnyValue, b: AnyValue, mode: NumericMode) -> Ordering {
        #[cfg(test)]
        tests::COMPARISON_CALLS.with(|count| count.set(count.get() + 1));
        assert_language_value(a);
        assert_language_value(b);
        self.order(a, b, mode)
    }

    /// The strict term order of two map keys, each given as the word and
    /// kind a map stores. An identical word is the same key, integers order
    /// as integers, atoms by name and binaries by their bits, all without a
    /// value being rebuilt; any other pair is ordered as the terms they are.
    #[inline(always)]
    pub fn key_order(&self, a: u64, a_kind: ValueKind, b: u64, b_kind: ValueKind) -> Ordering {
        #[cfg(test)]
        tests::COMPARISON_CALLS.with(|count| count.set(count.get() + 1));
        self.stored_key_order(a, a_kind, b, b_kind)
    }

    #[inline(always)]
    fn stored_key_order(&self, a: u64, a_kind: ValueKind, b: u64, b_kind: ValueKind) -> Ordering {
        // A float and a map are told apart from what is not a language
        // value before they are called equal.
        if a_kind == b_kind && a == b && !matches!(a_kind, ValueKind::FLOAT | ValueKind::MAP | ValueKind::NULL) {
            return Ordering::Equal;
        }
        if let Some(order) = stored_scalar_order(self.node, Stored::of_parts(a, a_kind), Stored::of_parts(b, b_kind)) {
            return order;
        }
        if a_kind.is_binary_repr() && b_kind.is_binary_repr() {
            return unsafe { Bin::of_stored(a, a_kind).cmp(&Bin::of_stored(b, b_kind)) };
        }
        self.decoded_key_order(a, a_kind, b, b_kind)
    }

    /// The order of two stored keys the words and kinds do not settle by
    /// themselves: by class when the classes differ, else from the decoded values.
    #[inline(never)]
    fn decoded_key_order(&self, a: u64, a_kind: ValueKind, b: u64, b_kind: ValueKind) -> Ordering {
        // Two kinds of different class order by class, with nothing decoded.
        if let (Some(a_class), Some(b_class)) = (kind_category(a_kind), kind_category(b_kind))
            && a_class != b_class
        {
            return a_class.cmp(&b_class);
        }
        let a = AnyValue::decode_parts(a, a_kind.tag()).expect("stored map key");
        let b = AnyValue::decode_parts(b, b_kind.tag()).expect("stored map key");
        assert_language_value(a);
        assert_language_value(b);
        self.order_decoded(a, b, NumericMode::Strict)
    }

    /// `key_order` of two keys held as values.
    pub(crate) fn key_order_of(&self, a: AnyValue, b: AnyValue) -> Ordering {
        self.key_order(a.raw(), a.kind(), b.raw(), b.kind())
    }

    fn keys_order(&self, a: AnyValue, b: AnyValue) -> Ordering {
        self.stored_key_order(a.raw(), a.kind(), b.raw(), b.kind())
    }

    fn order(&self, a: AnyValue, b: AnyValue, mode: NumericMode) -> Ordering {
        if let Some(order) = same_simple_kind_cmp(self.node, a, b) {
            return order;
        }
        self.order_decoded(a, b, mode)
    }

    /// `order` for a pair the scalar question has already been asked of.
    fn order_decoded(&self, a: AnyValue, b: AnyValue, mode: NumericMode) -> Ordering {
        let category = self.category(a);
        let order = category.cmp(&self.category(b));
        if order != Ordering::Equal {
            return order;
        }
        match category {
            Category::Number => number_cmp(a, b, mode),
            Category::Reference | Category::Pid => a.raw().cmp(&b.raw()),
            Category::Atom => self.node.cmp_atom_names(a.raw() as u32, b.raw() as u32),
            Category::Tuple => self.tuple_cmp(address(a), address(b), mode),
            Category::Closure => self.closure_cmp(address(a), address(b)),
            _ if a == b => Ordering::Equal,
            Category::Bitstring => bin_of(a).cmp(&bin_of(b)),
            Category::Map => self.map_cmp(self.map_term(a), self.map_term(b), mode),
            Category::List => self.list_cmp(address(a), address(b), mode),
            Category::Resource => {
                let a = unsafe { ResourceStub::from_raw(address(a)) };
                let b = unsafe { ResourceStub::from_raw(address(b)) };
                a.id().cmp(&b.id())
            }
        }
    }

    /// Whether `a` and `b` are equal under `mode`: exactly `compare(..) ==
    /// Equal`, settled without an ordering wherever the kinds allow.
    pub fn equal(&self, a: AnyValue, b: AnyValue, mode: NumericMode) -> bool {
        if let Some(answer) = same_simple_kind_equal(a, b) {
            return answer;
        }
        if a.kind() != ValueKind::NULL && b.kind() != ValueKind::NULL && self.category(a) != self.category(b) {
            return false;
        }
        self.compare(a, b, mode) == Ordering::Equal
    }

    /// Where a value stands among the kinds of term. A struct stands with the
    /// maps, whichever layout holds it.
    pub(crate) fn category(&self, value: AnyValue) -> Category {
        match kind_category(value.kind()) {
            Some(category) => category,
            None if self.struct_map_keys(address(value)).is_some() => Category::Map,
            None => Category::Tuple,
        }
    }

    fn struct_map_keys(&self, object: *const u8) -> Option<&'a [StructKey]> {
        self.schemas.map_keys(unsafe { struct_schema_id(object) })
    }

    pub(crate) fn map_term(&self, value: AnyValue) -> MapTerm<'a> {
        let addr = address(value) as *const u8;
        match value.kind() {
            ValueKind::MAP => MapTerm::Entries(addr),
            _ => MapTerm::Struct {
                object: addr,
                schema: self.schemas.get(unsafe { struct_schema_id(addr) }),
                keys: self.struct_map_keys(addr).expect("a struct in the map category"),
            },
        }
    }

    fn tuple_cmp(&self, a: *const u8, b: *const u8, mode: NumericMode) -> Ordering {
        let schema = self.schemas.get(unsafe { struct_schema_id(a) });
        let other = self.schemas.get(unsafe { struct_schema_id(b) });
        let (SchemaIdentity::Tuple(arity), SchemaIdentity::Tuple(other_arity)) = (&schema.identity, &other.identity)
        else {
            panic!("internal storage schema is not a language value");
        };
        let size = arity.cmp(other_arity);
        if size != Ordering::Equal || a == b {
            return size;
        }
        for index in 0..*arity {
            let order = self.order(field_value(schema, a, index), field_value(schema, b, index), mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    /// Maps order by size, then by their keys, then by their values in key
    /// order. Two structs of one schema have the same size, keys and module,
    /// so only their fields are read. Two tries that hold the same keys have
    /// the same shape, so a walk of both settles equality without ordering
    /// either; any other pair is read in key order, sorting a trie first.
    fn map_cmp(&self, a: MapTerm<'a>, b: MapTerm<'a>, mode: NumericMode) -> Ordering {
        if let (
            MapTerm::Struct { object, schema, keys },
            MapTerm::Struct {
                object: other,
                schema: other_schema,
                ..
            },
        ) = (a, b)
            && std::ptr::eq(schema, other_schema)
        {
            return self.fields_cmp(schema, keys, object, other, mode);
        }
        let size = self.map_count(a).cmp(&self.map_count(b));
        if size != Ordering::Equal {
            return size;
        }
        if let (MapTerm::Entries(left), MapTerm::Entries(right)) = (a, b)
            && unsafe { map_header_is_trie(left) && map_header_is_trie(right) }
            && self.tries_equal(left, right, mode)
        {
            return Ordering::Equal;
        }
        let (a, b) = (self.in_key_order(a), self.in_key_order(b));
        for i in 0..self.map_count(a.map) {
            let order = self.keys_order(self.ordered_key(&a, i), self.ordered_key(&b, i));
            if order != Ordering::Equal {
                return order;
            }
        }
        for i in 0..self.map_count(a.map) {
            let order = self.order(self.ordered_value(&a, i), self.ordered_value(&b, i), mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    /// Whether two trie nodes hold the same keys with equal values. Equal keys
    /// hash alike, so a canonical trie of a key set has one shape: bitmaps that
    /// differ mean different keys, and equal ones put the keys in one order.
    /// Only a collision node, whose entries are unordered, is matched by key.
    fn tries_equal(&self, a: *const u8, b: *const u8, mode: NumericMode) -> bool {
        if a == b {
            return true;
        }
        if unsafe { read(a as *const u64) != read(b as *const u64) } {
            return false;
        }
        let entries = unsafe { map_node_entry_count(a) };
        let own_equal = if unsafe { map_header_is_collision(a) } {
            (0..entries).all(|i| self.collision_entry_matches(a, i, b, mode))
        } else {
            (0..entries).all(|i| self.entries_equal(unsafe { map_slot(a, i) }, unsafe { map_slot(b, i) }, mode))
        };
        own_equal
            && (0..unsafe { map_node_child_count(a) })
                .all(|i| self.tries_equal(unsafe { map_node_child(a, i) }, unsafe { map_node_child(b, i) }, mode))
    }

    fn collision_entry_matches(&self, a: *const u8, slot: usize, b: *const u8, mode: NumericMode) -> bool {
        let entry = unsafe { map_slot(a, slot) };
        (0..unsafe { map_node_entry_count(b) }).any(|j| self.entries_equal(entry, unsafe { map_slot(b, j) }, mode))
    }

    fn entries_equal(&self, a: (AnyValue, AnyValue), b: (AnyValue, AnyValue), mode: NumericMode) -> bool {
        self.keys_order(a.0, b.0).is_eq() && self.order(a.1, b.1, mode).is_eq()
    }

    /// The map's entries as they are read in key order.
    fn in_key_order(&self, map: MapTerm<'a>) -> KeyOrder<'a> {
        match map {
            MapTerm::Entries(addr) if unsafe { map_header_is_trie(addr) } => {
                let mut entries = unsafe { map_entries(addr) };
                entries.sort_by(|a, b| self.keys_order(a.0, b.0));
                KeyOrder {
                    map,
                    sorted: Some(entries),
                }
            }
            _ => KeyOrder { map, sorted: None },
        }
    }

    fn ordered_key(&self, order: &KeyOrder<'a>, index: usize) -> AnyValue {
        match &order.sorted {
            Some(entries) => entries[index].0,
            None => self.map_key(order.map, index),
        }
    }

    fn ordered_value(&self, order: &KeyOrder<'a>, index: usize) -> AnyValue {
        match &order.sorted {
            Some(entries) => entries[index].1,
            None => self.map_value(order.map, index),
        }
    }

    fn fields_cmp(
        &self,
        schema: &Schema,
        keys: &[StructKey],
        a: *const u8,
        b: *const u8,
        mode: NumericMode,
    ) -> Ordering {
        for key in keys {
            let StructKey::Field(index) = *key else {
                continue;
            };
            let order = self.order(field_value(schema, a, index), field_value(schema, b, index), mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    pub(crate) fn map_count(&self, map: MapTerm<'a>) -> usize {
        match map {
            MapTerm::Entries(addr) => unsafe { map_count(addr) },
            MapTerm::Struct { keys, .. } => keys.len(),
        }
    }

    pub(crate) fn map_key(&self, map: MapTerm<'a>, index: usize) -> AnyValue {
        match map {
            MapTerm::Entries(addr) => unsafe { map_key(addr, index) },
            MapTerm::Struct { schema, keys, .. } => match keys[index] {
                StructKey::Module => self.atom(STRUCT_MODULE_FIELD),
                StructKey::Field(field) => self.atom(
                    schema.fields[field]
                        .name
                        .as_deref()
                        .expect("a named struct's field has a name"),
                ),
            },
        }
    }

    pub(crate) fn map_value(&self, map: MapTerm<'a>, index: usize) -> AnyValue {
        match map {
            MapTerm::Entries(addr) => unsafe { map_entry(addr, index).1 },
            MapTerm::Struct { object, schema, keys } => match keys[index] {
                StructKey::Module => match &schema.identity {
                    SchemaIdentity::Named(module) => self.atom(&module.atom_name()),
                    other => panic!("schema {} has no module", other.display_name()),
                },
                StructKey::Field(field) => field_value(schema, object, field),
            },
        }
    }

    fn atom(&self, name: &str) -> AnyValue {
        AnyValue::atom(self.node.intern_atom(name))
    }

    fn list_cmp(&self, mut a: *const u8, mut b: *const u8, mode: NumericMode) -> Ordering {
        while !a.is_null() && !b.is_null() {
            let ac = unsafe { &*a.cast::<ListCons>() };
            let bc = unsafe { &*b.cast::<ListCons>() };
            let order = self.order(ac.head_value(), bc.head_value(), mode);
            if order != Ordering::Equal {
                return order;
            }
            match (ac.tail(), bc.tail()) {
                (ListTail::Proper(next_a), ListTail::Proper(next_b)) => {
                    a = next_a as *const u8;
                    b = next_b as *const u8;
                }
                // A tail that is not the rest of a list is compared as a term:
                // after equal heads, `[1 | 2]` sorts before `[1, 2]` as `2`
                // sorts before `[2]`.
                (tail_a, tail_b) => return self.order(unsafe { tail_a.value() }, unsafe { tail_b.value() }, mode),
            }
        }
        b.is_null().cmp(&a.is_null())
    }

    fn closure_cmp(&self, a: *const u8, b: *const u8) -> Ordering {
        let identity = self
            .node
            .compare_closure_denotations(unsafe { closure_denotation(a) }, unsafe { closure_denotation(b) });
        if identity != Ordering::Equal || a == b {
            return identity;
        }
        let count = unsafe { closure_captured_count(a) };
        let shape = count.cmp(&unsafe { closure_captured_count(b) });
        if shape != Ordering::Equal {
            return shape;
        }
        for i in 0..count {
            let order = self.order(
                unsafe { closure_capture_value(a, i) },
                unsafe { closure_capture_value(b, i) },
                NumericMode::Strict,
            );
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }
}

/// The kinds of term, in term order.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum Category {
    Number,
    Atom,
    Reference,
    Resource,
    Closure,
    Pid,
    Tuple,
    Map,
    List,
    Bitstring,
}

/// A map in either layout, read in map key order.
#[derive(Clone, Copy)]
pub(crate) enum MapTerm<'a> {
    Entries(*const u8),
    Struct {
        object: *const u8,
        schema: &'a Schema,
        keys: &'a [StructKey],
    },
}

/// A map read in key order: in place where the layout is stored sorted, and
/// from a sorted copy of its entries where it is not.
struct KeyOrder<'a> {
    map: MapTerm<'a>,
    sorted: Option<Vec<(AnyValue, AnyValue)>>,
}

/// The value in field `index` of a tuple or struct whose fields are all
/// language values.
pub(crate) fn field_value(schema: &Schema, object: *const u8, index: usize) -> AnyValue {
    let offset = schema.fields[index].offset as usize;
    unsafe {
        AnyValue::decode_parts(
            read(object.add(8 + offset).cast()),
            read(object.add(8 + schema.size as usize + index)),
        )
    }
    .expect("published field")
}

/// Two numbers in `mode`. `Widening` orders an integer and a float by value.
/// `Strict` is the order of map keys, which tells `1` from `1.0`: every
/// integer sorts before every float.
fn number_cmp(a: AnyValue, b: AnyValue, mode: NumericMode) -> Ordering {
    match (a, b) {
        (AnyValue::Int(a), AnyValue::Int(b)) => a.cmp(&b),
        (AnyValue::Float(a), AnyValue::Float(b)) => float_cmp(f64::from_bits(a), f64::from_bits(b), mode),
        (AnyValue::Int(_), AnyValue::Float(_)) if mode == NumericMode::Strict => Ordering::Less,
        (AnyValue::Float(_), AnyValue::Int(_)) if mode == NumericMode::Strict => Ordering::Greater,
        (AnyValue::Int(a), AnyValue::Float(b)) => compare_int_float(a, f64::from_bits(b)),
        (AnyValue::Float(a), AnyValue::Int(b)) => compare_int_float(b, f64::from_bits(a)).reverse(),
        _ => unreachable!("a number is an integer or a float"),
    }
}

fn float_cmp(a: f64, b: f64, mode: NumericMode) -> Ordering {
    assert!(
        a.is_finite() && b.is_finite(),
        "nonfinite float is not a language value"
    );
    match mode {
        NumericMode::Strict => a.total_cmp(&b),
        NumericMode::Widening => a.partial_cmp(&b).expect("finite floats have a total order"),
    }
}

/// Exact mathematical comparison without rounding the integer to a float.
/// Shared by structural terms and unboxed interpreter/native numeric lanes.
pub fn compare_int_float(integer: i64, float: f64) -> Ordering {
    assert!(float.is_finite(), "nonfinite float is not a language value");
    if float >= -(i64::MIN as f64) {
        return Ordering::Less;
    }
    if float < i64::MIN as f64 {
        return Ordering::Greater;
    }
    integer
        .cmp(&(float as i64))
        .then_with(|| float_cmp(integer as f64, float, NumericMode::Widening))
}

fn is_bitstring(value: AnyValue) -> bool {
    matches!(value.kind(), ValueKind::BITSTRING | ValueKind::BINVIEW)
}

/// The order of two values of one simple kind, which needs neither the
/// category lookup nor the mode: two scalars by their words, two bitstrings by
/// their bits. A float is excluded because the mode decides how it orders.
#[inline(always)]
fn same_simple_kind_cmp(node: &Node, a: AnyValue, b: AnyValue) -> Option<Ordering> {
    stored_scalar_order(node, Stored::of(a), Stored::of(b)).or_else(|| match (a, b) {
        (AnyValue::HeapRef(_), AnyValue::HeapRef(_)) if is_bitstring(a) && is_bitstring(b) => {
            Some(bin_of(a).cmp(&bin_of(b)))
        }
        _ => None,
    })
}

/// Whether two values of one simple kind are equal, when their kinds settle
/// it: scalars by word, bitstrings by bits, identical float bits, pids and
/// references by kind and word.
fn same_simple_kind_equal(a: AnyValue, b: AnyValue) -> Option<bool> {
    stored_scalar_equal(Stored::of(a), Stored::of(b)).or_else(|| match (a, b) {
        (AnyValue::Float(x), AnyValue::Float(y)) if x == y => Some(true),
        (AnyValue::Opaque(x_kind, x), AnyValue::Opaque(y_kind, y)) => Some(x_kind == y_kind && x == y),
        (AnyValue::HeapRef(_), AnyValue::HeapRef(_)) if is_bitstring(a) && is_bitstring(b) => {
            Some(bin_of(a) == bin_of(b))
        }
        _ => None,
    })
}

/// The class a kind of value stands in, or `None` for a struct, whose schema
/// decides between tuple and map.
fn kind_category(kind: ValueKind) -> Option<Category> {
    Some(match kind {
        ValueKind::INT | ValueKind::FLOAT => Category::Number,
        ValueKind::ATOM => Category::Atom,
        ValueKind::REF => Category::Reference,
        ValueKind::PID => Category::Pid,
        ValueKind::RESOURCE => Category::Resource,
        ValueKind::CLOSURE => Category::Closure,
        ValueKind::MAP => Category::Map,
        ValueKind::LIST => Category::List,
        ValueKind::BITSTRING | ValueKind::BINVIEW => Category::Bitstring,
        ValueKind::STRUCT => return None,
        _ => unreachable!("runtime value kind"),
    })
}

fn bin_of(value: AnyValue) -> Bin {
    unsafe { Bin::of_stored(value.raw(), value.kind()) }
}

#[cfg(test)]
#[path = "term_test.rs"]
pub(crate) mod tests;
