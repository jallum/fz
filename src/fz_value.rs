//! Tagged FzValue and heap object header.
//!
//! Low-bit tag scheme (3 bits):
//!   0b000 = ptr to heap object (HeapHeader is 16-byte aligned, so low 4 bits are 0)
//!   0b001 = small int (61-bit signed; payload = (n << 3) | 0b001)
//!   0b010 = atom (32-bit interned id; payload = (id << 3) | 0b010)
//!   0b011 = special (nil/true/false/sentinels)
//!   1xx   = reserved (future: boxed float, etc.)

#![allow(dead_code)]

use std::alloc::{alloc, Layout};
use std::ptr;

const TAG_BITS: u64 = 3;
const TAG_MASK: u64 = 0b111;

const TAG_PTR: u64 = 0b000;
const TAG_INT: u64 = 0b001;
const TAG_ATOM: u64 = 0b010;
const TAG_SPECIAL: u64 = 0b011;

const SPECIAL_NIL: u64 = (0 << TAG_BITS) | TAG_SPECIAL;
const SPECIAL_TRUE: u64 = (1 << TAG_BITS) | TAG_SPECIAL;
const SPECIAL_FALSE: u64 = (2 << TAG_BITS) | TAG_SPECIAL;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Tag {
    Ptr,
    Int,
    Atom,
    Special,
    Reserved,
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct FzValue(pub u64);

impl FzValue {
    pub const NIL: FzValue = FzValue(SPECIAL_NIL);
    pub const TRUE: FzValue = FzValue(SPECIAL_TRUE);
    pub const FALSE: FzValue = FzValue(SPECIAL_FALSE);

    pub const fn from_int(n: i64) -> FzValue {
        // Sign-preserving shift left by 3, OR in tag.
        // Caller is responsible for range; debug builds check.
        let bits = ((n as u64) << TAG_BITS) | TAG_INT;
        FzValue(bits)
    }

    pub const fn from_atom_id(id: u32) -> FzValue {
        FzValue(((id as u64) << TAG_BITS) | TAG_ATOM)
    }

    pub fn from_ptr(p: *mut HeapHeader) -> FzValue {
        let bits = p as u64;
        debug_assert!(bits & TAG_MASK == 0, "heap pointer not 8-byte aligned");
        FzValue(bits)
    }

    pub fn tag(self) -> Tag {
        match self.0 & TAG_MASK {
            TAG_PTR => Tag::Ptr,
            TAG_INT => Tag::Int,
            TAG_ATOM => Tag::Atom,
            TAG_SPECIAL => Tag::Special,
            _ => Tag::Reserved,
        }
    }

    pub fn unbox_int(self) -> Option<i64> {
        if self.0 & TAG_MASK == TAG_INT {
            // Arithmetic shift right preserves sign.
            Some((self.0 as i64) >> TAG_BITS)
        } else {
            None
        }
    }

    pub fn unbox_atom(self) -> Option<u32> {
        if self.0 & TAG_MASK == TAG_ATOM {
            Some((self.0 >> TAG_BITS) as u32)
        } else {
            None
        }
    }

    pub fn unbox_ptr(self) -> Option<*mut HeapHeader> {
        if self.0 == SPECIAL_NIL || self.0 == SPECIAL_TRUE || self.0 == SPECIAL_FALSE {
            return None;
        }
        if self.0 & TAG_MASK == TAG_PTR {
            Some(self.0 as *mut HeapHeader)
        } else {
            None
        }
    }

    pub fn is_nil(self) -> bool {
        self.0 == SPECIAL_NIL
    }
    pub fn is_true(self) -> bool {
        self.0 == SPECIAL_TRUE
    }
    pub fn is_false(self) -> bool {
        self.0 == SPECIAL_FALSE
    }

    /// Range of valid 61-bit signed ints.
    pub const INT_MIN: i64 = -(1 << 60);
    pub const INT_MAX: i64 = (1 << 60) - 1;
}

impl std::fmt::Debug for FzValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag() {
            Tag::Int => write!(f, "FzValue::Int({})", self.unbox_int().unwrap()),
            Tag::Atom => write!(f, "FzValue::Atom({})", self.unbox_atom().unwrap()),
            Tag::Special if self.is_nil() => write!(f, "FzValue::Nil"),
            Tag::Special if self.is_true() => write!(f, "FzValue::True"),
            Tag::Special if self.is_false() => write!(f, "FzValue::False"),
            Tag::Special => write!(f, "FzValue::Special({:#x})", self.0),
            Tag::Ptr => write!(f, "FzValue::Ptr({:#x})", self.0),
            Tag::Reserved => write!(f, "FzValue::Reserved({:#x})", self.0),
        }
    }
}

#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapKind {
    Struct = 0,
    List = 1,
    Bitstring = 2,
    VecI64 = 3,
    VecF64 = 4,
    VecU8 = 5,
    VecBit = 6,
    Map = 7,
}

impl HeapKind {
    pub fn from_u16(v: u16) -> Option<HeapKind> {
        match v {
            0 => Some(HeapKind::Struct),
            1 => Some(HeapKind::List),
            2 => Some(HeapKind::Bitstring),
            3 => Some(HeapKind::VecI64),
            4 => Some(HeapKind::VecF64),
            5 => Some(HeapKind::VecU8),
            6 => Some(HeapKind::VecBit),
            7 => Some(HeapKind::Map),
            _ => None,
        }
    }
}

/// Heap object header — exactly 16 bytes, 16-byte aligned.
///
/// Every heap object starts with this header; payload follows immediately.
/// `flags` holds GC mark bit, region tag, etc. (defined in .11.2).
#[repr(C, align(16))]
#[derive(Debug, Clone, Copy)]
pub struct HeapHeader {
    pub kind: u16,
    pub flags: u16,
    pub size_bytes: u32,
    pub schema_id: u32,
    pub _reserved: u32,
}

const _: () = {
    assert!(std::mem::size_of::<HeapHeader>() == 16);
    assert!(std::mem::align_of::<HeapHeader>() == 16);
};

/// Allocator stubs for v1. These leak — real GC-managed allocator lands in .11.2.
///
/// All allocations are 16-byte aligned (matches HeapHeader alignment).
unsafe fn raw_alloc(total_size: usize) -> *mut HeapHeader {
    let layout = Layout::from_size_align(total_size, 16).expect("bad layout");
    let p = unsafe { alloc(layout) } as *mut HeapHeader;
    assert!(!p.is_null(), "allocation failed");
    p
}

pub fn alloc_struct(schema_id: u32, payload_size: u32) -> *mut HeapHeader {
    let total = 16 + payload_size as usize;
    // Round up to 16 for alignment of subsequent objects.
    let total = (total + 15) & !15;
    unsafe {
        let p = raw_alloc(total);
        ptr::write(
            p,
            HeapHeader {
                kind: HeapKind::Struct as u16,
                flags: 0,
                size_bytes: total as u32,
                schema_id,
                _reserved: 0,
            },
        );
        // Zero payload.
        let payload = (p as *mut u8).add(16);
        ptr::write_bytes(payload, 0, total - 16);
        p
    }
}

/// List cons cell: header (16) + head (8) + tail (8) = 32 bytes.
#[repr(C)]
pub struct ListCons {
    pub header: HeapHeader,
    pub head: FzValue,
    pub tail: FzValue,
}

pub fn alloc_list_cons(head: FzValue, tail: FzValue) -> *mut HeapHeader {
    unsafe {
        let p = raw_alloc(32) as *mut ListCons;
        ptr::write(
            p,
            ListCons {
                header: HeapHeader {
                    kind: HeapKind::List as u16,
                    flags: 0,
                    size_bytes: 32,
                    schema_id: 0,
                    _reserved: 0,
                },
                head,
                tail,
            },
        );
        p as *mut HeapHeader
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_is_16_bytes() {
        assert_eq!(std::mem::size_of::<HeapHeader>(), 16);
        assert_eq!(std::mem::align_of::<HeapHeader>(), 16);
    }

    #[test]
    fn int_round_trip_zero() {
        assert_eq!(FzValue::from_int(0).unbox_int(), Some(0));
    }

    #[test]
    fn int_round_trip_positive() {
        assert_eq!(FzValue::from_int(42).unbox_int(), Some(42));
        assert_eq!(FzValue::from_int(1_000_000).unbox_int(), Some(1_000_000));
    }

    #[test]
    fn int_round_trip_negative() {
        assert_eq!(FzValue::from_int(-1).unbox_int(), Some(-1));
        assert_eq!(FzValue::from_int(-42).unbox_int(), Some(-42));
        assert_eq!(FzValue::from_int(-1_000_000).unbox_int(), Some(-1_000_000));
    }

    #[test]
    fn int_round_trip_extremes() {
        assert_eq!(
            FzValue::from_int(FzValue::INT_MAX).unbox_int(),
            Some(FzValue::INT_MAX)
        );
        assert_eq!(
            FzValue::from_int(FzValue::INT_MIN).unbox_int(),
            Some(FzValue::INT_MIN)
        );
    }

    #[test]
    fn int_tag() {
        assert_eq!(FzValue::from_int(7).tag(), Tag::Int);
        assert_eq!(FzValue::from_int(-7).tag(), Tag::Int);
    }

    #[test]
    fn atom_round_trip() {
        for id in [0u32, 1, 42, 1234, u32::MAX] {
            let v = FzValue::from_atom_id(id);
            assert_eq!(v.tag(), Tag::Atom);
            assert_eq!(v.unbox_atom(), Some(id));
        }
    }

    #[test]
    fn nil_true_false_distinct() {
        let n = FzValue::NIL;
        let t = FzValue::TRUE;
        let f = FzValue::FALSE;
        assert!(n.is_nil() && !n.is_true() && !n.is_false());
        assert!(!t.is_nil() && t.is_true() && !t.is_false());
        assert!(!f.is_nil() && !f.is_true() && f.is_false());
        assert_eq!(n.tag(), Tag::Special);
        assert_eq!(t.tag(), Tag::Special);
        assert_eq!(f.tag(), Tag::Special);
        assert_ne!(n.0, t.0);
        assert_ne!(n.0, f.0);
        assert_ne!(t.0, f.0);
    }

    #[test]
    fn int_does_not_unbox_as_atom_or_ptr() {
        let v = FzValue::from_int(42);
        assert_eq!(v.unbox_atom(), None);
        assert_eq!(v.unbox_ptr(), None);
    }

    #[test]
    fn nil_does_not_unbox_as_ptr() {
        assert_eq!(FzValue::NIL.unbox_ptr(), None);
        assert_eq!(FzValue::TRUE.unbox_ptr(), None);
        assert_eq!(FzValue::FALSE.unbox_ptr(), None);
    }

    #[test]
    fn ptr_round_trip() {
        let p = alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        let v = FzValue::from_ptr(p);
        assert_eq!(v.tag(), Tag::Ptr);
        assert_eq!(v.unbox_ptr(), Some(p));
        assert_eq!(v.unbox_int(), None);
        assert_eq!(v.unbox_atom(), None);
    }

    #[test]
    fn list_cons_header() {
        let p = alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        unsafe {
            let h = &*p;
            assert_eq!(h.kind, HeapKind::List as u16);
            assert_eq!(h.size_bytes, 32);
            assert_eq!(h.schema_id, 0);
            let cons = &*(p as *mut ListCons);
            assert_eq!(cons.head.unbox_int(), Some(7));
            assert!(cons.tail.is_nil());
        }
    }

    #[test]
    fn list_cons_chain() {
        // [1, 2, 3]
        let l3 = alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let l2 = alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(l3));
        let l1 = alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(l2));
        unsafe {
            let c1 = &*(l1 as *mut ListCons);
            assert_eq!(c1.head.unbox_int(), Some(1));
            let c2 = &*(c1.tail.unbox_ptr().unwrap() as *mut ListCons);
            assert_eq!(c2.head.unbox_int(), Some(2));
            let c3 = &*(c2.tail.unbox_ptr().unwrap() as *mut ListCons);
            assert_eq!(c3.head.unbox_int(), Some(3));
            assert!(c3.tail.is_nil());
        }
    }

    #[test]
    fn alloc_struct_zeros_payload_and_sets_header() {
        let p = alloc_struct(7, 24);
        unsafe {
            let h = &*p;
            assert_eq!(h.kind, HeapKind::Struct as u16);
            assert_eq!(h.schema_id, 7);
            // 16 header + 24 payload, rounded up to 16 → 48.
            assert_eq!(h.size_bytes, 48);
            let payload = (p as *mut u8).add(16);
            for i in 0..24 {
                assert_eq!(*payload.add(i), 0);
            }
        }
    }

    #[test]
    fn heap_kind_round_trip() {
        for k in [
            HeapKind::Struct,
            HeapKind::List,
            HeapKind::Bitstring,
            HeapKind::VecI64,
            HeapKind::VecF64,
            HeapKind::VecU8,
            HeapKind::VecBit,
            HeapKind::Map,
        ] {
            assert_eq!(HeapKind::from_u16(k as u16), Some(k));
        }
        assert_eq!(HeapKind::from_u16(99), None);
    }

    #[test]
    fn pointer_alignment_satisfies_tag_zero_low_bits() {
        let p = alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert_eq!((p as u64) & TAG_MASK, 0);
    }
}
