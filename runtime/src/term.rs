//! Borrowed comparison of published, finite immutable runtime terms.
//!
//! Map keys always use strict numeric identity, including keys nested in maps
//! whose values are compared with the widening language operators.

use crate::any_value::{
    AnyValue, ListCons, MAP_DESTINATION_FLAG, ValueKind, closure_capture_value, closure_captured_count,
    closure_denotation, map_count, map_entry, struct_schema_id,
};
use crate::heap::{FieldKind, SchemaRegistry};
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
                    unsafe { read(value.raw() as *const u64) } & MAP_DESTINATION_FLAG,
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
        let category = rank(a.kind()).cmp(&rank(b.kind()));
        if category != Ordering::Equal {
            return category;
        }
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
            (AnyValue::Atom(a), AnyValue::Atom(b)) => self.node.cmp_atom_names(a, b),
            _ if a.kind() == ValueKind::STRUCT => self.struct_cmp(a.raw() as *const u8, b.raw() as *const u8, mode),
            _ if a.kind() == ValueKind::CLOSURE => self.closure_cmp(a.raw() as *const u8, b.raw() as *const u8),
            _ if a == b => Ordering::Equal,
            _ if a.kind().is_binary_repr() => bitstring_cmp(
                a.heap_object_word().expect("bitstring") as *const u8,
                b.heap_object_word().expect("bitstring") as *const u8,
            ),
            _ if a.kind() == ValueKind::MAP => self.map_cmp(a.raw() as *const u8, b.raw() as *const u8, mode),
            _ if a.kind() == ValueKind::LIST => self.list_cmp(a.raw() as *const u8, b.raw() as *const u8, mode),
            _ if a.kind() == ValueKind::RESOURCE => {
                let a = unsafe { ResourceStub::from_raw(a.raw() as *mut u8) };
                let b = unsafe { ResourceStub::from_raw(b.raw() as *mut u8) };
                a.id().cmp(&b.id())
            }
            _ => unreachable!("unpublished runtime value"),
        }
    }

    fn struct_cmp(&self, a: *const u8, b: *const u8, mode: NumericMode) -> Ordering {
        let a_id = unsafe { struct_schema_id(a) };
        let b_id = unsafe { struct_schema_id(b) };
        let schema = self.schemas.get(a_id);
        let identity = schema.identity.semantic_cmp(&self.schemas.get(b_id).identity);
        if identity != Ordering::Equal || a == b {
            return identity;
        }
        let mut value_index = 0;
        for field in &schema.fields {
            let ap = unsafe { a.add(8 + field.offset as usize) };
            let bp = unsafe { b.add(8 + field.offset as usize) };
            let order = match field.kind {
                FieldKind::AnyValue => {
                    let kind_offset = 8 + schema.size as usize + value_index;
                    value_index += 1;
                    let av = unsafe { AnyValue::decode_parts(read(ap.cast()), read(a.add(kind_offset))) }
                        .expect("published struct field");
                    let bv = unsafe { AnyValue::decode_parts(read(bp.cast()), read(b.add(kind_offset))) }
                        .expect("published struct field");
                    self.compare(av, bv, mode)
                }
                FieldKind::RawI64 => unsafe { read(ap.cast::<i64>()).cmp(&read(bp.cast::<i64>())) },
                FieldKind::RawF64 => unsafe { float_cmp(read(ap.cast()), read(bp.cast()), mode) },
                FieldKind::RawBytes(n) => unsafe { from_raw_parts(ap, n as usize).cmp(from_raw_parts(bp, n as usize)) },
            };
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
    }

    fn map_cmp(&self, a: *const u8, b: *const u8, mode: NumericMode) -> Ordering {
        let count = unsafe { map_count(a) };
        let size = count.cmp(&unsafe { map_count(b) });
        if size != Ordering::Equal {
            return size;
        }
        for i in 0..count {
            let order = self.compare(
                unsafe { map_entry(a, i).0 },
                unsafe { map_entry(b, i).0 },
                NumericMode::Strict,
            );
            if order != Ordering::Equal {
                return order;
            }
        }
        for i in 0..count {
            let order = self.compare(unsafe { map_entry(a, i).1 }, unsafe { map_entry(b, i).1 }, mode);
            if order != Ordering::Equal {
                return order;
            }
        }
        Ordering::Equal
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

fn rank(kind: ValueKind) -> u8 {
    match kind {
        ValueKind::INT | ValueKind::FLOAT => 0,
        ValueKind::ATOM => 1,
        ValueKind::RESOURCE => 2,
        ValueKind::CLOSURE => 3,
        ValueKind::STRUCT => 4,
        ValueKind::MAP => 5,
        ValueKind::LIST => 6,
        ValueKind::BITSTRING | ValueKind::PROCBIN => 7,
        _ => unreachable!("runtime value kind"),
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

fn bitstring_cmp(a: *const u8, b: *const u8) -> Ordering {
    let a_bits = unsafe { bitstring_bit_len(a as *mut u8) } as usize;
    let b_bits = unsafe { bitstring_bit_len(b as *mut u8) } as usize;
    let a_bytes = unsafe { from_raw_parts(bitstring_byte_ptr(a as *mut u8), a_bits.div_ceil(8)) };
    let b_bytes = unsafe { from_raw_parts(bitstring_byte_ptr(b as *mut u8), b_bits.div_ceil(8)) };
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
