//! Tagged FzValue and heap object header.
//!
//! The active runtime still uses the legacy 3-bit FzValue encoding. The
//! `TAG_*` constants below pin the next 4-bit value-representation table used
//! by pointer-kind tags and side-band container tags; vrx.A.* migrates active
//! call sites to that table one heap kind at a time.

#![allow(dead_code)]

use std::alloc::{Layout, alloc};
use std::ptr;

pub const TAG_BITS: u64 = 4;
pub const TAG_MASK: u64 = 0b1111;
/// Zero-init memory and typed-List end-of-list sentinel.
pub const TAG_NULL: u64 = 0x0;
/// Heap cons cell; side-band list layout is pinned in vrx.0.2.
pub const TAG_LIST: u64 = 0x1;
/// Heap flat map; one tag byte per key/value entry, pinned in vrx.0.2.
pub const TAG_MAP: u64 = 0x2;
/// Heap tuple/struct; schema-driven typed fields, pinned in vrx.0.2.
pub const TAG_STRUCT: u64 = 0x3;
/// Heap closure; schema-driven typed captures, pinned in vrx.0.2.
pub const TAG_CLOSURE: u64 = 0x4;
/// Heap inline bitstring; bit length prefix plus padded bytes.
pub const TAG_BITSTRING: u64 = 0x5;
/// Heap ProcBin stub; shared binary pointer plus MSO next link.
pub const TAG_PROCBIN: u64 = 0x6;
/// Heap monotyped i64 vector; count prefix plus raw i64 payload.
pub const TAG_VEC_I64: u64 = 0x7;
/// Heap monotyped f64 vector; count prefix plus raw f64 payload.
pub const TAG_VEC_F64: u64 = 0x8;
/// Heap monotyped byte vector; count prefix plus raw u8 payload.
pub const TAG_VEC_U8: u64 = 0x9;
/// Heap monotyped bit vector; bit-count prefix plus bit-packed payload.
pub const TAG_VEC_BIT: u64 = 0xA;
/// Heap resource stub; resource pointer plus MSO next link.
pub const TAG_RESOURCE: u64 = 0xB;
/// Cheney forwarding marker stored in the first word of a copied from-space object.
pub const TAG_FWD: u64 = 0xC;
/// Side-band immediate tag for raw i64 slots.
pub const TAG_INT_IMM: u64 = 0xD;
/// Side-band immediate tag for raw f64::to_bits slots.
pub const TAG_FLOAT_IMM: u64 = 0xE;
/// Side-band immediate tag for raw atom-id slots.
pub const TAG_ATOM_IMM: u64 = 0xF;

const FZVALUE_TAG_BITS: u64 = 3;
const FZVALUE_TAG_MASK: u64 = 0b111;

const FZVALUE_TAG_PTR: u64 = 0b000;
const FZVALUE_TAG_INT: u64 = 0b001;
const FZVALUE_TAG_ATOM: u64 = 0b010;
// fz-yan.1 — TAG_SPECIAL (0b011) is not a user value. The former occupants
// (nil/true/false) are now regular atoms with reserved compile-time IDs; see
// NIL_ATOM_ID etc. below. Matchers use one reserved bit pattern internally as
// a non-value sentinel.
pub const MATCHER_MAP_MISS_BITS: u64 = 0b011;

/// fz-yan.1 — reserved atom IDs. `AtomTable::new()` pre-interns
/// "nil"/"true"/"false" in this order at module construction time,
/// so every module has these well-known IDs available. The
/// `*_BITS` constants below are atom-tagged FzValue encodings of
/// these IDs; consumers reference the named constants and don't
/// need to know about the reservation.
pub const NIL_ATOM_ID: u32 = 0;
pub const TRUE_ATOM_ID: u32 = 1;
pub const FALSE_ATOM_ID: u32 = 2;

/// fz-yan.1 — public bit patterns. Atom-tagged FzValue encodings
/// of the three reserved IDs. Kept as named constants so call sites
/// throughout codegen / runtime are unchanged from the pre-fz-yan
/// world; only the definitions move.
pub const NIL_BITS: u64 = (NIL_ATOM_ID as u64) << FZVALUE_TAG_BITS | FZVALUE_TAG_ATOM;
pub const TRUE_BITS: u64 = (TRUE_ATOM_ID as u64) << FZVALUE_TAG_BITS | FZVALUE_TAG_ATOM;
pub const FALSE_BITS: u64 = (FALSE_ATOM_ID as u64) << FZVALUE_TAG_BITS | FZVALUE_TAG_ATOM;

/// fz-s9y.2 — the empty-list sentinel. TAG_PTR tag (0b000) with payload
/// value 1 (so the full bit pattern is `0x8`). Address 0x8 sits inside
/// page 0, which the OS reserves as unmapped — no allocator ever returns
/// it, so the sentinel can't collide with a real heap pointer.
/// Distinct from `NIL_BITS`: `[]` and `nil` are different values.
pub(crate) const EMPTY_LIST: u64 = 1 << FZVALUE_TAG_BITS;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Tag {
    Ptr,
    Int,
    Atom,
    Reserved,
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct FzValue(pub u64);

impl FzValue {
    pub const NIL: FzValue = FzValue(NIL_BITS);
    pub const TRUE: FzValue = FzValue(TRUE_BITS);
    pub const FALSE: FzValue = FzValue(FALSE_BITS);
    /// fz-s9y.2 — the empty list `[]`. Distinct from `NIL`.
    pub const EMPTY_LIST: FzValue = FzValue(EMPTY_LIST);

    pub const fn from_int(n: i64) -> FzValue {
        // Sign-preserving shift left by 3, OR in tag.
        // Caller is responsible for range; debug builds check.
        let bits = ((n as u64) << FZVALUE_TAG_BITS) | FZVALUE_TAG_INT;
        FzValue(bits)
    }

    pub const fn from_atom_id(id: u32) -> FzValue {
        FzValue(((id as u64) << FZVALUE_TAG_BITS) | FZVALUE_TAG_ATOM)
    }

    pub fn from_ptr(p: *mut HeapHeader) -> FzValue {
        let bits = p as u64;
        debug_assert!(bits & TAG_MASK == 0, "heap pointer not 16-byte aligned");
        FzValue(bits)
    }

    pub fn tag(self) -> Tag {
        match self.0 & FZVALUE_TAG_MASK {
            FZVALUE_TAG_PTR => Tag::Ptr,
            FZVALUE_TAG_INT => Tag::Int,
            FZVALUE_TAG_ATOM => Tag::Atom,
            _ => Tag::Reserved,
        }
    }

    pub fn unbox_int(self) -> Option<i64> {
        if self.0 & FZVALUE_TAG_MASK == FZVALUE_TAG_INT {
            // Arithmetic shift right preserves sign.
            Some((self.0 as i64) >> FZVALUE_TAG_BITS)
        } else {
            None
        }
    }

    pub fn unbox_atom(self) -> Option<u32> {
        if self.0 & FZVALUE_TAG_MASK == FZVALUE_TAG_ATOM {
            Some((self.0 >> FZVALUE_TAG_BITS) as u32)
        } else {
            None
        }
    }

    pub fn unbox_ptr(self) -> Option<*mut HeapHeader> {
        if self.0 == EMPTY_LIST {
            // fz-s9y.2 — the empty list is TAG_PTR-tagged but its "pointer"
            // is a sentinel into unmapped memory. Do not dereference.
            return None;
        }
        if self.0 & FZVALUE_TAG_MASK == FZVALUE_TAG_PTR {
            Some(self.0 as *mut HeapHeader)
        } else {
            None
        }
    }

    // fz-yan.1 — nil/true/false are atoms with reserved IDs. The
    // predicates are now atom-id checks; their public signatures are
    // preserved so consumers don't notice the representation move.
    pub fn is_nil(self) -> bool {
        self.unbox_atom() == Some(NIL_ATOM_ID)
    }
    pub fn is_empty_list(self) -> bool {
        self.0 == EMPTY_LIST
    }
    pub fn is_true(self) -> bool {
        self.unbox_atom() == Some(TRUE_ATOM_ID)
    }
    pub fn is_false(self) -> bool {
        self.unbox_atom() == Some(FALSE_ATOM_ID)
    }

    /// Range of valid 61-bit signed ints.
    pub const INT_MIN: i64 = -(1 << 60);
    pub const INT_MAX: i64 = (1 << 60) - 1;
}

impl std::fmt::Debug for FzValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag() {
            Tag::Int => write!(f, "FzValue::Int({})", self.unbox_int().unwrap()),
            // fz-yan.1 — the reserved-ID atoms get their conventional
            // names in debug output; other atoms render as their id.
            Tag::Atom if self.is_nil() => write!(f, "FzValue::Nil"),
            Tag::Atom if self.is_true() => write!(f, "FzValue::True"),
            Tag::Atom if self.is_false() => write!(f, "FzValue::False"),
            Tag::Atom => write!(f, "FzValue::Atom({})", self.unbox_atom().unwrap()),
            Tag::Ptr if self.is_empty_list() => write!(f, "FzValue::EmptyList"),
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
    Closure = 8,
    Float = 9,
    /// fz-cty.3 — 32-byte stub on a per-process heap that references an
    /// off-heap `SharedBin`. Cheney trace is a no-op; the per-heap MSO
    /// list governs retain/release across GC.
    ProcBin = 10,
    /// fz-swt.7 — 32-byte stub on a per-process heap that references an
    /// off-heap refcounted `Resource` (user-supplied destructor). Same
    /// 32-byte layout as ProcBin (HeapHeader + shared_ptr + mso_next),
    /// threaded onto the same MSO chain. Cheney trace is a no-op; the
    /// MSO sweep dispatches on kind to invoke `fz_resource_release`.
    Resource = 11,
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
            8 => Some(HeapKind::Closure),
            9 => Some(HeapKind::Float),
            10 => Some(HeapKind::ProcBin),
            11 => Some(HeapKind::Resource),
            _ => None,
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct ValueKind(u8);

impl ValueKind {
    pub const NULL: Self = Self(TAG_NULL as u8);
    pub const LIST: Self = Self(TAG_LIST as u8);
    pub const MAP: Self = Self(TAG_MAP as u8);
    pub const STRUCT: Self = Self(TAG_STRUCT as u8);
    pub const CLOSURE: Self = Self(TAG_CLOSURE as u8);
    pub const BITSTRING: Self = Self(TAG_BITSTRING as u8);
    pub const PROCBIN: Self = Self(TAG_PROCBIN as u8);
    pub const VEC_I64: Self = Self(TAG_VEC_I64 as u8);
    pub const VEC_F64: Self = Self(TAG_VEC_F64 as u8);
    pub const VEC_U8: Self = Self(TAG_VEC_U8 as u8);
    pub const VEC_BIT: Self = Self(TAG_VEC_BIT as u8);
    pub const RESOURCE: Self = Self(TAG_RESOURCE as u8);
    pub const INT: Self = Self(TAG_INT_IMM as u8);
    pub const FLOAT: Self = Self(TAG_FLOAT_IMM as u8);
    pub const ATOM: Self = Self(TAG_ATOM_IMM as u8);

    pub const fn new(tag: u8) -> Option<Self> {
        if tag <= TAG_MASK as u8 && tag != TAG_FWD as u8 {
            Some(Self(tag))
        } else {
            None
        }
    }

    pub const fn tag(self) -> u8 {
        self.0
    }

    pub const fn is_heap(self) -> bool {
        self.0 >= TAG_LIST as u8 && self.0 <= TAG_RESOURCE as u8
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TypedValue {
    pub raw: u64,
    pub kind: ValueKind,
}

impl TypedValue {
    pub const fn new(raw: u64, kind: ValueKind) -> Self {
        Self { raw, kind }
    }

    pub fn heap_ptr(addr: *mut HeapHeader, kind: ValueKind) -> Self {
        assert!(kind.is_heap(), "heap_ptr requires a heap ValueKind");
        let raw = addr as u64;
        assert_eq!(raw & TAG_MASK, 0, "heap address must be 16-byte aligned");
        Self { raw, kind }
    }

    pub fn tagged_heap_bits(self) -> Option<u64> {
        if self.kind.is_heap() {
            Some((self.raw & !TAG_MASK) | self.kind.tag() as u64)
        } else {
            None
        }
    }

    pub fn heap_addr(self) -> Option<*mut HeapHeader> {
        if self.kind.is_heap() {
            Some((self.raw & !TAG_MASK) as *mut HeapHeader)
        } else {
            None
        }
    }

    /// Convert a legacy free-standing FzValue into an explicit raw+kind slot.
    ///
    /// This is intentionally legacy-aware: scalar tags are decoded before any
    /// 4-bit heap-kind interpretation, so a tagged integer like 2
    /// (`0x11`, low nibble `TAG_LIST`) remains an int, not a list pointer.
    pub fn from_legacy_fz_value(bits: u64) -> Self {
        let v = FzValue(bits);
        if v.is_empty_list() {
            return Self::new(0, ValueKind::LIST);
        }
        match v.tag() {
            Tag::Int => Self::new(v.unbox_int().expect("int-tagged") as u64, ValueKind::INT),
            Tag::Atom => Self::new(v.unbox_atom().expect("atom-tagged") as u64, ValueKind::ATOM),
            Tag::Ptr => {
                let Some(ptr) = v.unbox_ptr() else {
                    return Self::new(0, ValueKind::NULL);
                };
                if ptr.is_null() {
                    return Self::new(0, ValueKind::NULL);
                }
                let kind = unsafe { (*ptr).kind };
                match HeapKind::from_u16(kind) {
                    Some(HeapKind::Float) => Self::new(
                        crate::heap::Heap::read_float(ptr).to_bits(),
                        ValueKind::FLOAT,
                    ),
                    Some(heap_kind) => Self::heap_ptr(ptr, ValueKind::from_heap_kind(heap_kind)),
                    None => panic!("legacy FzValue points at invalid HeapKind {kind:#x}"),
                }
            }
            Tag::Reserved => panic!("cannot convert reserved FzValue {bits:#x} to TypedValue"),
        }
    }
}

impl ValueKind {
    pub const fn from_heap_kind(kind: HeapKind) -> Self {
        match kind {
            HeapKind::List => Self::LIST,
            HeapKind::Map => Self::MAP,
            HeapKind::Struct => Self::STRUCT,
            HeapKind::Closure => Self::CLOSURE,
            HeapKind::Bitstring => Self::BITSTRING,
            HeapKind::ProcBin => Self::PROCBIN,
            HeapKind::VecI64 => Self::VEC_I64,
            HeapKind::VecF64 => Self::VEC_F64,
            HeapKind::VecU8 => Self::VEC_U8,
            HeapKind::VecBit => Self::VEC_BIT,
            HeapKind::Resource => Self::RESOURCE,
            HeapKind::Float => Self::FLOAT,
        }
    }
}

// Bitstring storage dispatchers moved to `crate::procbin` in fz-q8d.1.
// `fz_value.rs` does not own bitstring layout; render uses the procbin
// helpers like every other read site.

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

/// vrx.0.2 — raw mailbox payload plus side-band kind byte. The low nibble
/// of `kind` is one of the canonical 4-bit `TAG_*` values; the high nibble is
/// reserved and must remain zero when vrx.B.1 starts using this layout.
#[repr(C)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MailboxSlot {
    pub value: u64,
    pub kind: u8,
}

const _: () = {
    assert!(std::mem::size_of::<MailboxSlot>() == 16);
    assert!(std::mem::align_of::<MailboxSlot>() == 8);
};

// fz-ul4.27.22.6 — closure `flags` packing. Low 14 bits hold captured_count;
// high 2 bits hold halt_kind (0=Tagged, 1=RawInt, 2=RawF64). The split keeps
// the field in the GC-safe region of the header (offset 2; forwarding
// pointers clobber offsets 8..16). 14 bits = 16K captures, far above any
// realistic program.
pub const CLOSURE_FLAGS_CAPTURED_MASK: u16 = 0x3FFF;
pub const CLOSURE_FLAGS_HALT_KIND_SHIFT: u16 = 14;

#[inline]
pub fn closure_flags_pack(captured_count: u16, halt_kind: u16) -> u16 {
    debug_assert!(
        captured_count <= CLOSURE_FLAGS_CAPTURED_MASK,
        "closure captured count {} exceeds 14-bit capacity",
        captured_count
    );
    debug_assert!(
        halt_kind <= 0b11,
        "closure halt_kind {} out of range",
        halt_kind
    );
    (captured_count & CLOSURE_FLAGS_CAPTURED_MASK) | (halt_kind << CLOSURE_FLAGS_HALT_KIND_SHIFT)
}

#[inline]
pub fn closure_flags_captured(flags: u16) -> u16 {
    flags & CLOSURE_FLAGS_CAPTURED_MASK
}

#[inline]
pub fn closure_flags_halt_kind(flags: u16) -> u16 {
    flags >> CLOSURE_FLAGS_HALT_KIND_SHIFT
}

#[inline]
pub fn is_heap_kind(tag: u64) -> bool {
    (TAG_LIST..=TAG_RESOURCE).contains(&tag)
}

/// Returns the to-space address encoded in a vrx forwarding marker.
///
/// `addr` must point at the first byte of a valid from-space object. The
/// active Cheney collector still uses the legacy `FORWARDED_KIND` header
/// marker; this helper is the scaffold consumed by vrx.A.* migrations.
#[inline]
pub fn is_forwarded(addr: *const u8) -> Option<*const u8> {
    let marker = unsafe { std::ptr::read(addr as *const u64) };
    if marker & TAG_MASK == TAG_FWD {
        Some((marker & !TAG_MASK) as *const u8)
    } else {
        None
    }
}

pub fn object_size(ptr_with_tag: u64) -> usize {
    let kind = ptr_with_tag & TAG_MASK;
    let addr = (ptr_with_tag & !TAG_MASK) as *const u8;
    unsafe {
        match kind {
            TAG_LIST => size_of_list(addr),
            TAG_MAP => size_of_map(addr),
            TAG_STRUCT => size_of_struct(addr),
            TAG_CLOSURE => size_of_closure(addr),
            TAG_BITSTRING => size_of_bitstring(addr),
            TAG_PROCBIN => size_of_procbin(addr),
            TAG_VEC_I64 => size_of_vec_i64(addr),
            TAG_VEC_F64 => size_of_vec_f64(addr),
            TAG_VEC_U8 => size_of_vec_u8(addr),
            TAG_VEC_BIT => size_of_vecbit(addr),
            TAG_RESOURCE => size_of_resource(addr),
            TAG_FWD => unreachable!("forwarded; caller must check first"),
            _ => unreachable!("non-pointer tag passed to object_size"),
        }
    }
}

unsafe fn size_of_list(_addr: *const u8) -> usize {
    panic!("vrx.A.1 has not migrated List layout yet")
}

unsafe fn size_of_map(_addr: *const u8) -> usize {
    panic!("vrx.A.2 has not migrated Map layout yet")
}

unsafe fn size_of_struct(_addr: *const u8) -> usize {
    panic!("vrx.A.3 has not migrated Struct layout yet")
}

unsafe fn size_of_closure(_addr: *const u8) -> usize {
    panic!("vrx.A.4 has not migrated Closure layout yet")
}

unsafe fn size_of_bitstring(_addr: *const u8) -> usize {
    panic!("vrx.A.5 has not migrated Bitstring layout yet")
}

unsafe fn size_of_procbin(_addr: *const u8) -> usize {
    panic!("vrx.A.6 has not migrated ProcBin layout yet")
}

unsafe fn size_of_vec_i64(_addr: *const u8) -> usize {
    panic!("vrx.A.7 has not migrated VecI64 layout yet")
}

unsafe fn size_of_vec_f64(_addr: *const u8) -> usize {
    panic!("vrx.A.7 has not migrated VecF64 layout yet")
}

unsafe fn size_of_vec_u8(_addr: *const u8) -> usize {
    panic!("vrx.A.7 has not migrated VecU8 layout yet")
}

unsafe fn size_of_vecbit(_addr: *const u8) -> usize {
    panic!("vrx.A.7 has not migrated VecBit layout yet")
}

unsafe fn size_of_resource(_addr: *const u8) -> usize {
    panic!("vrx.A.8 has not migrated Resource layout yet")
}

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
        // fz-yan.1 — nil/true/false are atoms with reserved IDs.
        assert_eq!(n.tag(), Tag::Atom);
        assert_eq!(t.tag(), Tag::Atom);
        assert_eq!(f.tag(), Tag::Atom);
        assert_eq!(n.unbox_atom(), Some(NIL_ATOM_ID));
        assert_eq!(t.unbox_atom(), Some(TRUE_ATOM_ID));
        assert_eq!(f.unbox_atom(), Some(FALSE_ATOM_ID));
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
            HeapKind::Closure,
            HeapKind::Float,
            HeapKind::ProcBin,
            HeapKind::Resource,
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

    #[test]
    fn tag_constants_all_distinct() {
        let tags = [
            TAG_NULL,
            TAG_LIST,
            TAG_MAP,
            TAG_STRUCT,
            TAG_CLOSURE,
            TAG_BITSTRING,
            TAG_PROCBIN,
            TAG_VEC_I64,
            TAG_VEC_F64,
            TAG_VEC_U8,
            TAG_VEC_BIT,
            TAG_RESOURCE,
            TAG_FWD,
            TAG_INT_IMM,
            TAG_FLOAT_IMM,
            TAG_ATOM_IMM,
        ];
        for (i, a) in tags.iter().enumerate() {
            for b in tags.iter().skip(i + 1) {
                assert_ne!(a, b);
            }
        }
    }

    #[test]
    fn tag_constants_fit_in_4_bits() {
        for tag in [
            TAG_NULL,
            TAG_LIST,
            TAG_MAP,
            TAG_STRUCT,
            TAG_CLOSURE,
            TAG_BITSTRING,
            TAG_PROCBIN,
            TAG_VEC_I64,
            TAG_VEC_F64,
            TAG_VEC_U8,
            TAG_VEC_BIT,
            TAG_RESOURCE,
            TAG_FWD,
            TAG_INT_IMM,
            TAG_FLOAT_IMM,
            TAG_ATOM_IMM,
        ] {
            assert!(tag <= TAG_MASK);
        }
    }

    #[test]
    fn kind_round_trip() {
        let addr = 0x1000_u64;
        for tag in [
            TAG_LIST,
            TAG_MAP,
            TAG_STRUCT,
            TAG_CLOSURE,
            TAG_BITSTRING,
            TAG_PROCBIN,
            TAG_VEC_I64,
            TAG_VEC_F64,
            TAG_VEC_U8,
            TAG_VEC_BIT,
            TAG_RESOURCE,
        ] {
            let tagged = addr | tag;
            assert_eq!(tagged & TAG_MASK, tag);
            assert_eq!(tagged & !TAG_MASK, addr);
        }
    }

    #[test]
    fn forwarding_marker_distinguishable() {
        for heap_tag in [
            TAG_LIST,
            TAG_MAP,
            TAG_STRUCT,
            TAG_CLOSURE,
            TAG_BITSTRING,
            TAG_PROCBIN,
            TAG_VEC_I64,
            TAG_VEC_F64,
            TAG_VEC_U8,
            TAG_VEC_BIT,
            TAG_RESOURCE,
        ] {
            assert_ne!(TAG_FWD, heap_tag);
        }
    }

    #[test]
    fn forward_marker_distinguishable_from_pointers() {
        let addr = 0x1000_u64;
        let marker = addr | TAG_FWD;
        for heap_tag in [
            TAG_LIST,
            TAG_MAP,
            TAG_STRUCT,
            TAG_CLOSURE,
            TAG_BITSTRING,
            TAG_PROCBIN,
            TAG_VEC_I64,
            TAG_VEC_F64,
            TAG_VEC_U8,
            TAG_VEC_BIT,
            TAG_RESOURCE,
        ] {
            assert_ne!(marker, addr | heap_tag);
        }
    }

    #[test]
    fn is_forwarded_detects_marker() {
        let mut words = [0_u64; 2];
        let to_space = 0x2000_u64;
        words[0] = (to_space & !TAG_MASK) | TAG_FWD;

        let found = is_forwarded(words.as_ptr() as *const u8);

        assert_eq!(found, Some(to_space as *const u8));
    }

    #[test]
    #[should_panic(expected = "vrx.A.1 has not migrated List layout yet")]
    fn object_size_panics_on_unmigrated_kind() {
        let ptr_with_tag = 0x1000_u64 | TAG_LIST;
        let _ = object_size(ptr_with_tag);
    }

    #[test]
    fn immediate_tags_not_used_for_pointers() {
        let p = alloc_list_cons(FzValue::NIL, FzValue::NIL) as u64;
        assert_eq!(p & TAG_MASK, TAG_NULL);
        assert_ne!(p & TAG_MASK, TAG_INT_IMM);
        assert_ne!(p & TAG_MASK, TAG_FLOAT_IMM);
        assert_ne!(p & TAG_MASK, TAG_ATOM_IMM);
    }

    #[test]
    fn typed_value_keeps_even_int_distinct_from_list_tag() {
        let int_bits = FzValue::from_int(2).0;
        assert_eq!(int_bits & TAG_MASK, TAG_LIST);

        let tv = TypedValue::from_legacy_fz_value(int_bits);

        assert_eq!(tv.kind, ValueKind::INT);
        assert_eq!(tv.raw as i64, 2);
        assert_eq!(tv.tagged_heap_bits(), None);
    }

    #[test]
    fn typed_value_recognizes_explicit_list_typed_pointer() {
        let addr = 0x1000 as *mut HeapHeader;
        let tv = TypedValue::heap_ptr(addr, ValueKind::LIST);

        assert_eq!(tv.kind, ValueKind::LIST);
        assert_eq!(tv.heap_addr(), Some(addr));
        assert_eq!(tv.tagged_heap_bits(), Some(0x1000 | TAG_LIST));
    }

    #[test]
    fn typed_value_decodes_legacy_empty_list_as_typed_null_list() {
        let tv = TypedValue::from_legacy_fz_value(FzValue::EMPTY_LIST.0);

        assert_eq!(tv, TypedValue::new(0, ValueKind::LIST));
    }

    #[test]
    fn typed_value_decodes_legacy_boxed_float_to_raw_bits() {
        let p = alloc_struct(0, 16);
        unsafe {
            (*p).kind = HeapKind::Float as u16;
            (*p).size_bytes = 32;
            std::ptr::write((p as *mut u8).add(16) as *mut f64, 1.5);
        }

        let tv = TypedValue::from_legacy_fz_value(FzValue::from_ptr(p).0);

        assert_eq!(tv.kind, ValueKind::FLOAT);
        assert_eq!(f64::from_bits(tv.raw), 1.5);
    }
}

/// Debug rendering of FzValues. Lifted out of ir_codegen.rs by
/// fz-ul4.23.4.3 so that any execution path (JIT, future interp/AOT) can
/// use the same rendering — values are uniformly tagged, regardless of
/// what produced them. The single runtime dependency is the heap's
/// schema registry on the current Process, accessed via
/// `crate::process::current_process()`.
pub mod debug {
    use super::{FzValue, HeapKind, ListCons, Tag};
    use crate::process::{CURRENT_PROCESS, current_process};

    /// Render an atom id as `:name` if the current Process has a name
    /// for it; fall back to `:atom_N` otherwise. The fallback fires when
    /// render is called without a Process installed (e.g. unit tests
    /// poking the renderer directly) or when an id is outside the
    /// module's table (defensive — shouldn't happen in practice).
    fn render_atom(id: u32) -> String {
        let proc_ptr = CURRENT_PROCESS.with(|c| c.get());
        if proc_ptr.is_null() {
            return format!(":atom_{}", id);
        }
        let names = unsafe { &(*proc_ptr).atom_names };
        match names.get(id as usize) {
            Some(name) if !name.is_empty() => format!(":{}", name),
            _ => format!(":atom_{}", id),
        }
    }

    pub fn render(bits: u64) -> String {
        let v = FzValue(bits);
        match v.tag() {
            Tag::Int => v.unbox_int().unwrap().to_string(),
            // fz-yan.1 — the reserved-ID atoms (nil/true/false) render
            // bareword, matching their source-level keyword spelling.
            // Other atoms get the leading colon via `render_atom`.
            Tag::Atom if v.is_nil() => "nil".into(),
            Tag::Atom if v.is_true() => "true".into(),
            Tag::Atom if v.is_false() => "false".into(),
            Tag::Atom => render_atom(v.unbox_atom().unwrap()),
            Tag::Ptr => {
                // fz-s9y.2 — the empty list `[]` is TAG_PTR-tagged but its
                // "pointer" is the EMPTY_LIST sentinel pointing into unmapped
                // memory. Detect before any dereference.
                if v.is_empty_list() {
                    return "[]".into();
                }
                let p = v.unbox_ptr().unwrap();
                let kind = unsafe { (*p).kind };
                match HeapKind::from_u16(kind) {
                    Some(HeapKind::List) => render_list(bits),
                    Some(HeapKind::Struct) => render_struct(bits),
                    Some(HeapKind::Bitstring) | Some(HeapKind::ProcBin) => render_bitstring(bits),
                    Some(HeapKind::Map) => render_map(bits),
                    Some(HeapKind::Closure) => render_closure(bits),
                    Some(HeapKind::Float) => render_float(bits),
                    Some(HeapKind::VecI64) => render_vec_i64(bits),
                    Some(HeapKind::VecU8) => render_vec_u8(bits),
                    Some(HeapKind::VecBit) => render_vec_bit(bits),
                    _ => format!("#ptr<{:#x}>", bits),
                }
            }
            Tag::Reserved => format!("#reserved<{:#x}>", bits),
        }
    }

    /// Render a heap-typed Struct (currently only emitted for tuples). Reads
    /// the schema from the current Process's SchemaRegistry to determine
    /// field count. Each FzValue field renders inline; non-FzValue fields
    /// are elided (no callers emit them yet).
    fn render_struct(bits: u64) -> String {
        let v = FzValue(bits);
        let p = v.unbox_ptr().unwrap();
        let schema_id = unsafe { (*p).schema_id };
        let parts: Vec<String> = {
            let reg = current_process().heap.schemas_registry();
            let registry = reg.borrow();
            let schema = registry.get(schema_id);
            schema
                .fields
                .iter()
                .filter(|f| matches!(f.kind, crate::heap::FieldKind::FzValue))
                .map(|f| {
                    let field_bits = unsafe {
                        std::ptr::read((p as *const u8).add(16 + f.offset as usize) as *const u64)
                    };
                    render(field_bits)
                })
                .collect()
        };
        format!("{{{}}}", parts.join(", "))
    }

    /// Render a heap Map as `%{k => v, ...}` in canonical sorted order.
    fn render_map(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let count = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
        let cursor = unsafe { (p as *const u8).add(24) as *const u64 };
        let mut parts: Vec<String> = Vec::with_capacity(count);
        for i in 0..count {
            let k = unsafe { std::ptr::read(cursor.add(i * 2)) };
            let v = unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
            parts.push(format!("{} => {}", render(k), render(v)));
        }
        format!("%{{{}}}", parts.join(", "))
    }

    fn render_bitstring(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as usize;
        let total_bytes = bit_len.div_ceil(8);
        let byte_ptr = unsafe { crate::procbin::bitstring_byte_ptr(p) };
        let bytes = unsafe { std::slice::from_raw_parts(byte_ptr, total_bytes) };
        let full_bytes = bit_len / 8;
        let trailing_bits = bit_len % 8;

        // fz-axu.15 (R2) — UTF-8-aware rendering: byte-aligned + valid
        // UTF-8 + Elixir-style String.printable?/1 heuristic renders as
        // a quoted string. Anything else falls back to the `<<...>>`
        // byte-list form. Print intentionally doesn't read the type
        // system's brand axis — the rendering decision is purely
        // payload-driven so AOT and JIT agree without sharing type
        // info at runtime.
        if trailing_bits == 0
            && let Ok(s) = std::str::from_utf8(&bytes[..full_bytes])
            && is_printable_utf8(s)
        {
            return format!("\"{}\"", escape_for_display(s));
        }

        let mut parts: Vec<String> = bytes[..full_bytes].iter().map(|b| b.to_string()).collect();
        if trailing_bits > 0 {
            let last = bytes[full_bytes] >> (8 - trailing_bits);
            parts.push(format!("{}::{}", last, trailing_bits));
        }
        format!("<<{}>>", parts.join(", "))
    }

    /// fz-axu.15 (R2) — matches Elixir's `String.printable?/1`: any
    /// codepoint outside the C0/C1 control ranges is fine, plus the
    /// whitelisted control set `\n \r \t \v \b \f \e \a`. Anything else
    /// (lone NUL, DEL, other C0/C1) disqualifies the slice.
    #[cfg(test)]
    mod r2_tests {
        use super::*;

        #[test]
        fn ascii_printable_passes() {
            assert!(is_printable_utf8("hello world"));
            assert!(is_printable_utf8(""));
            assert!(is_printable_utf8("/tmp/fz-x5m"));
        }

        #[test]
        fn utf8_non_ascii_passes() {
            assert!(is_printable_utf8("héllo"));
            assert!(is_printable_utf8("日本語"));
        }

        #[test]
        fn whitelisted_controls_pass() {
            assert!(is_printable_utf8("line\nbreak"));
            assert!(is_printable_utf8("tab\tseparated"));
            assert!(is_printable_utf8("\r\n"));
        }

        #[test]
        fn other_controls_fail() {
            assert!(!is_printable_utf8("\x01"));
            assert!(!is_printable_utf8("\x00"));
            assert!(!is_printable_utf8("\x7f"));
            // Any prefix-rejection works elsewhere too.
            assert!(!is_printable_utf8("hello\x01world"));
        }

        #[test]
        fn escape_round_trips_through_display() {
            assert_eq!(escape_for_display("a\nb"), "a\\nb");
            assert_eq!(escape_for_display("\"quoted\""), "\\\"quoted\\\"");
            assert_eq!(escape_for_display("plain"), "plain");
            // tab + carriage return escape too.
            assert_eq!(escape_for_display("a\tb\rc"), "a\\tb\\rc");
        }
    }

    fn is_printable_utf8(s: &str) -> bool {
        for c in s.chars() {
            let cp = c as u32;
            // Whitelisted control codepoints (Elixir-compatible).
            if matches!(cp, 0x07 | 0x08 | 0x09 | 0x0A | 0x0B | 0x0C | 0x0D | 0x1B) {
                continue;
            }
            if cp < 0x20 || (0x7F..=0x9F).contains(&cp) {
                return false;
            }
        }
        true
    }

    /// Escape the bytes that would corrupt the surrounding `"…"` form.
    /// Inverse of the lexer's canonical escapes (`\n \t \r \\ \"`).
    fn escape_for_display(s: &str) -> String {
        let mut out = String::with_capacity(s.len());
        for c in s.chars() {
            match c {
                '\n' => out.push_str("\\n"),
                '\r' => out.push_str("\\r"),
                '\t' => out.push_str("\\t"),
                '\\' => out.push_str("\\\\"),
                '"' => out.push_str("\\\""),
                other => out.push(other),
            }
        }
        out
    }

    fn render_float(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let f = crate::heap::Heap::read_float(p);
        if f.is_finite() && f.fract() == 0.0 {
            format!("{:.1}", f)
        } else {
            format!("{}", f)
        }
    }

    fn render_vec_i64(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let len = crate::heap::Heap::vec_len(p) as usize;
        let payload = unsafe { (p as *const u8).add(24) as *const i64 };
        let parts: Vec<String> = (0..len)
            .map(|i| unsafe { std::ptr::read(payload.add(i)) }.to_string())
            .collect();
        format!("~v[{}]", parts.join(", "))
    }

    fn render_vec_u8(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let len = crate::heap::Heap::vec_len(p) as usize;
        let payload = unsafe { (p as *const u8).add(24) };
        let parts: Vec<String> = (0..len)
            .map(|i| unsafe { *payload.add(i) }.to_string())
            .collect();
        format!("~b[{}]", parts.join(", "))
    }

    fn render_vec_bit(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let len = crate::heap::Heap::vec_len(p) as usize;
        let payload = unsafe { (p as *const u8).add(24) };
        let parts: Vec<String> = (0..len)
            .map(|i| {
                let byte_idx = i / 8;
                let bit_idx = 7 - (i % 8);
                let byte = unsafe { *payload.add(byte_idx) };
                ((byte >> bit_idx) & 1).to_string()
            })
            .collect();
        format!("~bits[{}]", parts.join(", "))
    }

    fn render_closure(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let header = unsafe { &*p };
        format!("#fn<{}/{}>", header.schema_id, header.flags)
    }

    fn render_list(bits: u64) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut cur_bits = bits;
        let mut tail_render: Option<String> = None;
        loop {
            let cv = FzValue(cur_bits);
            // fz-s9y.2 — terminate on the empty-list sentinel, not on nil.
            // A list ending in `nil` (atom-like value) is an improper list;
            // it renders as `[a, b | nil]` via the tail_render path below.
            if cv.is_empty_list() {
                break;
            }
            let cp = match cv.unbox_ptr() {
                Some(p) => p,
                None => {
                    tail_render = Some(render(cur_bits));
                    break;
                }
            };
            let ch = unsafe { &*cp };
            if HeapKind::from_u16(ch.kind) != Some(HeapKind::List) {
                tail_render = Some(render(cur_bits));
                break;
            }
            let cons = unsafe { &*(cp as *const ListCons) };
            parts.push(render(cons.head.0));
            cur_bits = cons.tail.0;
        }
        match tail_render {
            Some(t) => format!("[{} | {}]", parts.join(", "), t),
            None => format!("[{}]", parts.join(", ")),
        }
    }
}
