//! Borrowed comparison of published, finite immutable runtime terms.
//!
//! Map keys always use strict numeric identity, including keys nested in maps
//! whose values are compared with the widening language operators.

use crate::any_value::{
    AnyValue, ListCons, MAP_DESTINATION_FLAG, ValueKind, closure_capture_value, closure_captured_count,
    closure_denotation, map_count, map_entry, struct_schema_id,
};
use crate::heap::{Schema, SchemaIdentity, SchemaRegistry, StructKey};
use crate::module_name::STRUCT_MODULE_FIELD;
use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
use crate::process::Node;
use crate::resource::ResourceStub;
use std::cmp::Ordering;
use std::ptr::read;
use std::slice::from_raw_parts;

#[derive(Clone, Copy, PartialEq, Eq)]
pub enum NumericMode {
    Strict,
    Widening,
}

/// The raw address of a heap value: what dereferencing and identity
/// comparison use, never its payload word. The empty list has no object; its
/// word is the null address the list comparator expects.
fn address(value: AnyValue) -> *mut u8 {
    value.heap_addr().unwrap_or(value.raw() as *mut u8)
}

pub struct TermComparator<'a> {
    node: &'a Node,
    schemas: &'a SchemaRegistry,
}

impl<'a> TermComparator<'a> {
    pub fn new(node: &'a Node, schemas: &'a SchemaRegistry) -> Self {
        Self { node, schemas }
    }

    pub fn compare(&self, a: AnyValue, b: AnyValue, mode: NumericMode) -> Ordering {
        #[cfg(test)]
        tests::COMPARISON_CALLS.with(|count| count.set(count.get() + 1));
        for value in [a, b] {
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
        let category = self.category(a);
        let order = category.cmp(&self.category(b));
        if order != Ordering::Equal {
            return order;
        }
        match category {
            Category::Number => number_cmp(a, b, mode),
            Category::Atom => self.node.cmp_atom_names(a.raw() as u32, b.raw() as u32),
            Category::Tuple => self.tuple_cmp(address(a), address(b), mode),
            Category::Closure => self.closure_cmp(address(a), address(b)),
            _ if a == b => Ordering::Equal,
            Category::Bitstring => bitstring_cmp(
                a.heap_object_word().expect("bitstring"),
                b.heap_object_word().expect("bitstring"),
            ),
            Category::Map => self.map_cmp(self.map_term(a), self.map_term(b), mode),
            Category::List => self.list_cmp(address(a), address(b), mode),
            Category::Resource => {
                let a = unsafe { ResourceStub::from_raw(address(a)) };
                let b = unsafe { ResourceStub::from_raw(address(b)) };
                a.id().cmp(&b.id())
            }
        }
    }

    /// Where a value stands among the kinds of term. A struct stands with the
    /// maps, whichever layout holds it.
    fn category(&self, value: AnyValue) -> Category {
        match value.kind() {
            ValueKind::INT | ValueKind::FLOAT => Category::Number,
            ValueKind::ATOM => Category::Atom,
            ValueKind::RESOURCE => Category::Resource,
            ValueKind::CLOSURE => Category::Closure,
            ValueKind::STRUCT if self.struct_map_keys(address(value)).is_some() => Category::Map,
            ValueKind::STRUCT => Category::Tuple,
            ValueKind::MAP => Category::Map,
            ValueKind::LIST => Category::List,
            ValueKind::BITSTRING | ValueKind::PROCBIN => Category::Bitstring,
            _ => unreachable!("runtime value kind"),
        }
    }

    fn struct_map_keys(&self, object: *const u8) -> Option<&'a [StructKey]> {
        self.schemas.map_keys(unsafe { struct_schema_id(object) })
    }

    fn map_term(&self, value: AnyValue) -> MapTerm<'a> {
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
            let order = self.compare(field_value(schema, a, index), field_value(schema, b, index), mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    /// Maps order by size, then by their keys, then by their values in key
    /// order. Two structs of one schema have the same size, keys and module,
    /// so only their fields are read.
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
        let count = self.map_count(a);
        let size = count.cmp(&self.map_count(b));
        if size != Ordering::Equal {
            return size;
        }
        for i in 0..count {
            let order = self.compare(self.map_key(a, i), self.map_key(b, i), NumericMode::Strict);
            if order != Ordering::Equal {
                return order;
            }
        }
        for i in 0..count {
            let order = self.compare(self.map_value(a, i), self.map_value(b, i), mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
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
            let order = self.compare(field_value(schema, a, index), field_value(schema, b, index), mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    fn map_count(&self, map: MapTerm<'a>) -> usize {
        match map {
            MapTerm::Entries(addr) => unsafe { map_count(addr) },
            MapTerm::Struct { keys, .. } => keys.len(),
        }
    }

    fn map_key(&self, map: MapTerm<'a>, index: usize) -> AnyValue {
        match map {
            MapTerm::Entries(addr) => unsafe { map_entry(addr, index).0 },
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

    fn map_value(&self, map: MapTerm<'a>, index: usize) -> AnyValue {
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
            let order = self.compare(ac.head_value(), bc.head_value(), mode);
            if order != Ordering::Equal {
                return order;
            }
            a = ac.tail_addr() as *const u8;
            b = bc.tail_addr() as *const u8;
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
            let order = self.compare(
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
enum Category {
    Number,
    Atom,
    Resource,
    Closure,
    Tuple,
    Map,
    List,
    Bitstring,
}

/// A map in either layout, read in map key order.
#[derive(Clone, Copy)]
enum MapTerm<'a> {
    Entries(*const u8),
    Struct {
        object: *const u8,
        schema: &'a Schema,
        keys: &'a [StructKey],
    },
}

/// The value in field `index` of a tuple or struct whose fields are all
/// language values.
fn field_value(schema: &Schema, object: *const u8, index: usize) -> AnyValue {
    let offset = schema.fields[index].offset as usize;
    unsafe {
        AnyValue::decode_parts(
            read(object.add(8 + offset).cast()),
            read(object.add(8 + schema.size as usize + index)),
        )
    }
    .expect("published field")
}

fn number_cmp(a: AnyValue, b: AnyValue, mode: NumericMode) -> Ordering {
    match (a, b) {
        (AnyValue::Int(a), AnyValue::Int(b)) => a.cmp(&b),
        (AnyValue::Float(a), AnyValue::Float(b)) => float_cmp(f64::from_bits(a), f64::from_bits(b), mode),
        (AnyValue::Int(a), AnyValue::Float(b)) => match mode {
            NumericMode::Strict => compare_int_float(a, f64::from_bits(b)).then(Ordering::Less),
            NumericMode::Widening => compare_int_float(a, f64::from_bits(b)),
        },
        (AnyValue::Float(a), AnyValue::Int(b)) => match mode {
            NumericMode::Strict => compare_int_float(b, f64::from_bits(a))
                .reverse()
                .then(Ordering::Greater),
            NumericMode::Widening => compare_int_float(b, f64::from_bits(a)).reverse(),
        },
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

fn bitstring_cmp(a: u64, b: u64) -> Ordering {
    let a_bits = unsafe { bitstring_bit_len(a) } as usize;
    let b_bits = unsafe { bitstring_bit_len(b) } as usize;
    let a_bytes = unsafe { from_raw_parts(bitstring_byte_ptr(a), a_bits.div_ceil(8)) };
    let b_bytes = unsafe { from_raw_parts(bitstring_byte_ptr(b), b_bits.div_ceil(8)) };
    let common_bits = a_bits.min(b_bits);
    let common_bytes = common_bits / 8;
    let bytes = a_bytes[..common_bytes].cmp(&b_bytes[..common_bytes]);
    if bytes != Ordering::Equal {
        return bytes;
    }
    if !common_bits.is_multiple_of(8) {
        let mask = u8::MAX << (8 - common_bits % 8);
        let partial = (a_bytes[common_bytes] & mask).cmp(&(b_bytes[common_bytes] & mask));
        if partial != Ordering::Equal {
            return partial;
        }
    }
    a_bits.cmp(&b_bits)
}

#[cfg(test)]
#[path = "term_test.rs"]
mod tests;
