//! Storage-local value slots and strict heap object metadata.
//!
//! `ValueSlot` is not the runtime value ABI. It exists only where persistent
//! heap/root storage still needs side-band kind metadata while the hard cut
//! moves public runtime boundaries to opaque tagged value words.

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
/// Heap resource stub; resource pointer plus MSO next link.
pub const TAG_RESOURCE: u64 = 0x7;
/// Cheney forwarding marker stored in the first word of a copied from-space object.
pub const TAG_FWD: u64 = 0x8;
/// Side-band immediate tag for raw i64 slots.
pub const TAG_KIND_INT: u64 = 0xD;
/// Side-band immediate tag for raw f64::to_bits slots.
pub const TAG_KIND_FLOAT: u64 = 0xE;
/// Side-band immediate tag for raw atom-id slots.
pub const TAG_KIND_ATOM: u64 = 0xF;

// fz-yan.1 — TAG_SPECIAL (0b011) is not a user value. The former occupants
// (nil/true/false) are now regular atoms with reserved compile-time IDs; see
// NIL_ATOM_ID etc. below. Matchers use one reserved bit pattern internally as
// a non-value sentinel.
pub const MATCHER_MAP_MISS_BITS: u64 = 0b011;

/// fz-yan.1 — reserved atom IDs. `AtomTable::new()` pre-interns
/// "nil"/"true"/"false" in this order at module construction time,
/// so every module has these well-known IDs available. The `*_BITS`
/// constants below are raw atom payloads; side-band `ValueKind::ATOM`
/// carries the kind when needed.
pub const NIL_ATOM_ID: u32 = 0;
pub const TRUE_ATOM_ID: u32 = 1;
pub const FALSE_ATOM_ID: u32 = 2;

/// Reserved atom raw payloads.
pub const NIL_BITS: u64 = NIL_ATOM_ID as u64;
pub const TRUE_BITS: u64 = TRUE_ATOM_ID as u64;
pub const FALSE_BITS: u64 = FALSE_ATOM_ID as u64;

/// fz-s9y.2 — the empty-list sentinel. TAG_PTR tag (0b000) with payload
/// value 1 (so the full bit pattern is `0x8`). Address 0x8 sits inside
/// page 0, which the OS reserves as unmapped — no allocator ever returns
/// it, so the sentinel can't collide with a real heap pointer.
/// Distinct from `NIL_BITS`: `[]` and `nil` are different values.
pub const EMPTY_LIST_BITS: u64 = 0x8;
pub(crate) const EMPTY_LIST: u64 = EMPTY_LIST_BITS;

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
    pub const RESOURCE: Self = Self(TAG_RESOURCE as u8);
    pub const INT: Self = Self(TAG_KIND_INT as u8);
    pub const FLOAT: Self = Self(TAG_KIND_FLOAT as u8);
    pub const ATOM: Self = Self(TAG_KIND_ATOM as u8);

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

    pub const fn from_heap_tag(tag: u64) -> Option<Self> {
        if tag >= TAG_LIST && tag <= TAG_RESOURCE {
            Some(Self(tag as u8))
        } else {
            None
        }
    }
}

/// Persistent heap/root storage slot only. Do not use this as a runtime ABI,
/// generated-code value, mailbox-specific carrier, or interpreter value view.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ValueSlot {
    pub raw: u64,
    pub kind: ValueKind,
}

impl ValueSlot {
    pub const fn new(raw: u64, kind: ValueKind) -> Self {
        Self { raw, kind }
    }

    pub fn heap_ptr(addr: *mut u8, kind: ValueKind) -> Self {
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

    pub fn heap_addr(self) -> Option<*mut u8> {
        if self.kind.is_heap() {
            Some((self.raw & !TAG_MASK) as *mut u8)
        } else {
            None
        }
    }

    pub const fn null() -> Self {
        Self {
            raw: 0,
            kind: ValueKind::NULL,
        }
    }

    pub const fn empty_list() -> Self {
        Self {
            raw: 0,
            kind: ValueKind::LIST,
        }
    }

    pub const fn int(value: i64) -> Self {
        Self {
            raw: value as u64,
            kind: ValueKind::INT,
        }
    }

    pub const fn atom(atom_id: u32) -> Self {
        Self {
            raw: atom_id as u64,
            kind: ValueKind::ATOM,
        }
    }

    pub const fn nil_atom() -> Self {
        Self::atom(NIL_ATOM_ID)
    }

    pub const fn bool_atom(value: bool) -> Self {
        if value {
            Self::atom(TRUE_ATOM_ID)
        } else {
            Self::atom(FALSE_ATOM_ID)
        }
    }

    pub const fn float(value: f64) -> Self {
        Self {
            raw: value.to_bits(),
            kind: ValueKind::FLOAT,
        }
    }

    pub const fn from_parts(raw: u64, kind: ValueKind) -> Self {
        Self { raw, kind }
    }

    pub fn decode_parts(raw: u64, kind_tag: u8) -> Option<Self> {
        let kind = ValueKind::new(kind_tag & TAG_MASK as u8)?;
        Some(Self { raw, kind })
    }

    pub fn decode_tagged_heap_bits(bits: u64) -> Option<Self> {
        let kind = heap_kind_from_tagged(bits)?;
        let addr = (bits & !TAG_MASK) as *mut u8;
        Some(Self::heap_ptr(addr, kind))
    }

    pub const fn raw(self) -> u64 {
        self.raw
    }

    pub const fn kind(self) -> ValueKind {
        self.kind
    }
}

// Bitstring storage dispatchers moved to `crate::procbin` in fz-q8d.1.
// `fz_value.rs` does not own bitstring layout; render uses the procbin
// helpers like every other read site.

// fz-ul4.27.22.6 — closure `flags` packing. Low 14 bits hold captured_count;
// high 2 bits hold halt_kind (0=ValueRef, 1=RawInt, 2=RawF64). The split keeps
// the field in object-local metadata that forwarding does not clobber.
// 14 bits = 16K captures, far above any realistic program.
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
pub fn closure_size_for_count(captured_count: usize) -> usize {
    let raw_bytes = captured_count * 8;
    let kind_bytes = (captured_count + 7) & !7;
    (16 + raw_bytes + kind_bytes + 15) & !15
}

#[inline]
pub fn tagged_closure_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_CLOSURE
}

#[inline]
pub fn closure_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_CLOSURE {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object.
#[inline]
pub unsafe fn closure_schema_id(addr: *const u8) -> u32 {
    unsafe { std::ptr::read(addr as *const u32) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object.
#[inline]
pub unsafe fn closure_flags(addr: *const u8) -> u16 {
    unsafe { std::ptr::read(addr.add(4) as *const u32) as u16 }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object.
#[inline]
pub unsafe fn closure_captured_count(addr: *const u8) -> usize {
    closure_flags_captured(unsafe { closure_flags(addr) }) as usize
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object.
#[inline]
pub unsafe fn closure_halt_kind(addr: *const u8) -> u16 {
    closure_flags_halt_kind(unsafe { closure_flags(addr) })
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object.
#[inline]
pub unsafe fn closure_fn_ptr(addr: *const u8) -> u64 {
    unsafe { std::ptr::read(addr.add(8) as *const u64) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_raw_slot(addr: *const u8, idx: usize) -> *mut u64 {
    unsafe { addr.add(16 + idx * 8) as *mut u64 }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_kind_slot(addr: *const u8, idx: usize) -> *mut u8 {
    let count = unsafe { closure_captured_count(addr) };
    unsafe { addr.add(16 + count * 8 + idx) as *mut u8 }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_value(addr: *const u8, idx: usize) -> ValueSlot {
    let raw = unsafe { std::ptr::read(closure_capture_raw_slot(addr, idx)) };
    let kind_tag = unsafe { std::ptr::read(closure_capture_kind_slot(addr, idx)) };
    ValueSlot::decode_parts(raw, kind_tag).expect("closure capture kind")
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_set(addr: *const u8, idx: usize, value: ValueSlot) {
    let raw = if value.kind().is_heap() {
        value.raw() & !TAG_MASK
    } else {
        value.raw()
    };
    unsafe {
        std::ptr::write(closure_capture_raw_slot(addr, idx), raw);
        std::ptr::write(closure_capture_kind_slot(addr, idx), value.kind().tag());
    }
}

#[inline]
pub fn is_heap_kind(tag: u64) -> bool {
    (TAG_LIST..=TAG_RESOURCE).contains(&tag)
}

#[inline]
pub fn heap_kind_from_tagged(bits: u64) -> Option<ValueKind> {
    ValueKind::from_heap_tag(bits & TAG_MASK)
}

#[inline]
pub fn heap_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    heap_kind_from_tagged(bits).map(|_| (bits & !TAG_MASK) as *mut u8)
}

#[inline]
pub fn tagged_heap_bits(addr: *const u8, kind: ValueKind) -> u64 {
    assert!(kind.is_heap(), "tagged_heap_bits requires a heap kind");
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | kind.tag() as u64
}

/// Returns the to-space address encoded in a vrx forwarding marker.
///
/// `addr` must point at the first byte of a valid from-space object. The
/// active Cheney collector writes a `TAG_FWD` marker into object-local
/// metadata while moving reachable from-space objects.
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
    object_size_with_struct_payload(ptr_with_tag, |_| {
        panic!("Struct size requires the owning SchemaRegistry")
    })
}

pub fn object_size_with_struct_payload(
    ptr_with_tag: u64,
    mut struct_payload_size: impl FnMut(u32) -> usize,
) -> usize {
    let kind = ptr_with_tag & TAG_MASK;
    let addr = (ptr_with_tag & !TAG_MASK) as *const u8;
    unsafe {
        match kind {
            TAG_LIST => size_of_list(addr),
            TAG_MAP => size_of_map(addr),
            TAG_STRUCT => size_of_struct(addr, &mut struct_payload_size),
            TAG_CLOSURE => size_of_closure(addr),
            TAG_BITSTRING => size_of_bitstring(addr),
            TAG_PROCBIN => size_of_procbin(addr),
            TAG_RESOURCE => size_of_resource(addr),
            TAG_FWD => unreachable!("forwarded; caller must check first"),
            _ => unreachable!("non-pointer tag passed to object_size"),
        }
    }
}

unsafe fn size_of_list(_addr: *const u8) -> usize {
    16
}

unsafe fn size_of_map(addr: *const u8) -> usize {
    let count = unsafe { std::ptr::read(addr as *const u64) as usize };
    map_size_for_count(count)
}

unsafe fn size_of_struct(
    addr: *const u8,
    struct_payload_size: &mut impl FnMut(u32) -> usize,
) -> usize {
    let schema_id = unsafe { struct_schema_id(addr) };
    struct_size_for_payload(struct_payload_size(schema_id))
}

unsafe fn size_of_closure(_addr: *const u8) -> usize {
    closure_size_for_count(unsafe { closure_captured_count(_addr) })
}

unsafe fn size_of_bitstring(_addr: *const u8) -> usize {
    bitstring_size_for_bit_len(unsafe { bitstring_bit_len(_addr) })
}

unsafe fn size_of_procbin(_addr: *const u8) -> usize {
    16
}

unsafe fn size_of_resource(_addr: *const u8) -> usize {
    48
}

/// Allocator stubs for v1. These leak — real GC-managed allocator lands in .11.2.
///
/// All allocations are 16-byte aligned so low-bit pointer tags are available.
unsafe fn raw_alloc(total_size: usize) -> *mut u8 {
    let layout = Layout::from_size_align(total_size, 16).expect("bad layout");
    let p = unsafe { alloc(layout) };
    assert!(!p.is_null(), "allocation failed");
    p
}

pub fn alloc_struct(schema_id: u32, payload_size: u32) -> *mut u8 {
    let total = struct_size_for_payload(payload_size as usize);
    unsafe {
        let p = raw_alloc(total);
        ptr::write(p as *mut u32, schema_id);
        ptr::write(p.add(4) as *mut u32, 0);
        // Zero payload.
        let payload = p.add(8);
        ptr::write_bytes(payload, 0, total - 8);
        p
    }
}

/// vrx.A.1 — List cons cell: head (8) + link/head-kind (8) = 16 bytes.
///
/// `head` is raw payload. `link` stores the next cons address in the high 60
/// bits and the head's canonical kind tag in the low 4 bits.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct ListCons {
    pub head: u64,
    pub link: u64,
}

const _: () = {
    assert!(std::mem::size_of::<ListCons>() == 16);
    assert!(std::mem::align_of::<ListCons>() == 8);
};

impl ListCons {
    pub fn new(head: ValueSlot, tail_bits: u64) -> Self {
        Self::from_value_head(head, tail_bits)
    }

    pub fn from_value_head(head: ValueSlot, tail_bits: u64) -> Self {
        Self {
            head: head.raw(),
            link: list_tail_addr_from_bits(tail_bits) | head.kind().tag() as u64,
        }
    }

    pub fn head_kind(&self) -> ValueKind {
        ValueKind::new((self.link & TAG_MASK) as u8).expect("list head kind tag")
    }

    pub fn tail_addr(&self) -> u64 {
        self.link & !TAG_MASK
    }

    pub fn tail_bits(&self) -> u64 {
        let addr = self.tail_addr();
        if addr == 0 {
            EMPTY_LIST
        } else {
            addr | TAG_LIST
        }
    }

    pub fn head_value(&self) -> ValueSlot {
        ValueSlot::new(self.head, self.head_kind())
    }
}

#[inline]
pub fn tagged_list_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_LIST
}

#[inline]
pub fn list_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_LIST {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

#[inline]
pub fn list_tail_addr_from_bits(bits: u64) -> u64 {
    if bits == EMPTY_LIST || bits == NIL_BITS || bits == 0 {
        0
    } else if bits & TAG_MASK == TAG_LIST {
        bits & !TAG_MASK
    } else {
        panic!("list tail must be [] or a list pointer, got {bits:#x}")
    }
}

#[inline]
pub fn map_tag_bytes_len(count: usize) -> usize {
    count.div_ceil(8) * 8
}

#[inline]
pub fn map_size_for_count(count: usize) -> usize {
    (8 + map_tag_bytes_len(count) + count * 16 + 15) & !15
}

#[inline]
pub fn map_keys_offset(count: usize) -> usize {
    8 + map_tag_bytes_len(count)
}

#[inline]
pub fn map_values_offset(count: usize) -> usize {
    map_keys_offset(count) + count * 8
}

#[inline]
pub fn tagged_map_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_MAP
}

#[inline]
pub fn map_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_MAP {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

#[inline]
pub fn struct_size_for_payload(payload_size: usize) -> usize {
    (8 + payload_size + 15) & !15
}

#[inline]
pub fn tagged_struct_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_STRUCT
}

#[inline]
pub fn struct_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_STRUCT {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Struct object.
#[inline]
pub unsafe fn struct_schema_id(addr: *const u8) -> u32 {
    unsafe { std::ptr::read(addr as *const u32) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Struct object.
#[inline]
pub unsafe fn struct_flags(addr: *const u8) -> u32 {
    unsafe { std::ptr::read(addr.add(4) as *const u32) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Struct object.
#[inline]
pub unsafe fn struct_field_raw_slot(addr: *const u8, field_offset: u32) -> *mut u64 {
    unsafe { addr.add(8 + field_offset as usize) as *mut u64 }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Struct object and
/// `kind_offset` must be the schema-derived offset of that field's kind byte.
#[inline]
pub unsafe fn struct_field_kind_slot(addr: *const u8, kind_offset: u32) -> *mut u8 {
    unsafe { addr.add(8 + kind_offset as usize) as *mut u8 }
}

#[inline]
pub fn bitstring_size_for_bit_len(bit_len: u64) -> usize {
    let bytes_len = (bit_len as usize).div_ceil(8);
    (8 + bytes_len + 1 + 15) & !15
}

#[inline]
pub fn tagged_bitstring_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_BITSTRING
}

#[inline]
pub fn bitstring_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_BITSTRING {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict inline Bitstring.
#[inline]
pub unsafe fn bitstring_bit_len(addr: *const u8) -> u64 {
    unsafe { std::ptr::read(addr as *const u64) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict inline Bitstring.
#[inline]
pub unsafe fn bitstring_bytes_ptr(addr: *const u8) -> *const u8 {
    unsafe { addr.add(8) }
}

#[inline]
pub fn tagged_procbin_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_PROCBIN
}

#[inline]
pub fn procbin_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_PROCBIN {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

#[inline]
pub fn tagged_resource_bits(addr: *const u8) -> u64 {
    let raw = addr as u64;
    debug_assert_eq!(raw & TAG_MASK, 0);
    raw | TAG_RESOURCE
}

#[inline]
pub fn resource_addr_from_tagged(bits: u64) -> Option<*mut u8> {
    if bits & TAG_MASK == TAG_RESOURCE {
        Some((bits & !TAG_MASK) as *mut u8)
    } else {
        None
    }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
pub unsafe fn map_count(addr: *const u8) -> usize {
    unsafe { std::ptr::read(addr as *const u64) as usize }
}

#[inline]
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
pub unsafe fn map_tag_ptr(addr: *const u8) -> *mut u8 {
    unsafe { addr.add(8) as *mut u8 }
}

#[inline]
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object with
/// exactly `count` entries.
pub unsafe fn map_keys_ptr(addr: *const u8, count: usize) -> *mut u64 {
    unsafe { addr.add(map_keys_offset(count)) as *mut u64 }
}

#[inline]
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object with
/// exactly `count` entries.
pub unsafe fn map_values_ptr(addr: *const u8, count: usize) -> *mut u64 {
    unsafe { addr.add(map_values_offset(count)) as *mut u64 }
}

#[inline]
pub fn map_pack_tag(key: ValueKind, value: ValueKind) -> u8 {
    (key.tag() << 4) | value.tag()
}

#[inline]
pub fn map_key_kind(tag_byte: u8) -> ValueKind {
    ValueKind::new(tag_byte >> 4).expect("map key kind tag")
}

#[inline]
pub fn map_value_kind(tag_byte: u8) -> ValueKind {
    ValueKind::new(tag_byte & TAG_MASK as u8).expect("map value kind tag")
}

#[inline]
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object, and
/// `index` must be in bounds for that map's entry count.
pub unsafe fn map_entry(addr: *const u8, index: usize) -> (ValueSlot, ValueSlot) {
    let count = unsafe { map_count(addr) };
    assert!(index < count, "map entry index out of bounds");
    let tag = unsafe { std::ptr::read(map_tag_ptr(addr).add(index)) };
    let keys = unsafe { map_keys_ptr(addr, count) };
    let values = unsafe { map_values_ptr(addr, count) };
    (
        ValueSlot::new(
            unsafe { std::ptr::read(keys.add(index)) },
            map_key_kind(tag),
        ),
        ValueSlot::new(
            unsafe { std::ptr::read(values.add(index)) },
            map_value_kind(tag),
        ),
    )
}

pub fn alloc_list_cons_slot(head: ValueSlot, tail_bits: u64) -> u64 {
    unsafe {
        let p = raw_alloc(16) as *mut ListCons;
        ptr::write(p, ListCons::new(head, tail_bits));
        tagged_list_bits(p as *const u8)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn list_cons_size_is_16() {
        assert_eq!(std::mem::size_of::<ListCons>(), 16);
    }

    #[test]
    fn list_cons_layout() {
        let bits = alloc_list_cons_slot(ValueSlot::int(7), EMPTY_LIST);
        let p = list_addr_from_tagged(bits).expect("tagged list ptr");
        unsafe {
            let cons = &*(p as *mut ListCons);
            assert_eq!(cons.head_kind(), ValueKind::INT);
            assert_eq!(cons.head as i64, 7);
            assert_eq!(cons.tail_bits(), EMPTY_LIST);
        }
    }

    #[test]
    fn list_cons_chain() {
        // [1, 2, 3]
        let l3 = alloc_list_cons_slot(ValueSlot::int(3), EMPTY_LIST);
        let l2 = alloc_list_cons_slot(ValueSlot::int(2), l3);
        let l1 = alloc_list_cons_slot(ValueSlot::int(1), l2);
        unsafe {
            let c1 = &*(list_addr_from_tagged(l1).unwrap() as *mut ListCons);
            assert_eq!(c1.head_value(), ValueSlot::new(1, ValueKind::INT));
            let c2 = &*(list_addr_from_tagged(c1.tail_bits()).unwrap() as *mut ListCons);
            assert_eq!(c2.head_value(), ValueSlot::new(2, ValueKind::INT));
            let c3 = &*(list_addr_from_tagged(c2.tail_bits()).unwrap() as *mut ListCons);
            assert_eq!(c3.head_value(), ValueSlot::new(3, ValueKind::INT));
            assert_eq!(c3.tail_bits(), EMPTY_LIST);
        }
    }

    #[test]
    fn alloc_struct_zeros_payload_and_sets_prefix() {
        let p = alloc_struct(7, 24);
        unsafe {
            assert_eq!(struct_schema_id(p), 7);
            assert_eq!(struct_flags(p), 0);
            assert_eq!(struct_size_for_payload(24), 32);
            let payload = p.add(8);
            for i in 0..24 {
                assert_eq!(*payload.add(i), 0);
            }
        }
    }

    #[test]
    fn pointer_alignment_satisfies_tag_zero_low_bits() {
        let p = alloc_struct(0, 0);
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
            TAG_RESOURCE,
            TAG_FWD,
            TAG_KIND_INT,
            TAG_KIND_FLOAT,
            TAG_KIND_ATOM,
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
            TAG_RESOURCE,
            TAG_FWD,
            TAG_KIND_INT,
            TAG_KIND_FLOAT,
            TAG_KIND_ATOM,
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
            TAG_RESOURCE,
        ] {
            let tagged = addr | tag;
            assert_eq!(tagged & TAG_MASK, tag);
            assert_eq!(tagged & !TAG_MASK, addr);
        }
    }

    #[test]
    fn strict_heap_kind_comes_from_pointer_low_bits() {
        let addr = 0x1000 as *const u8;
        for (kind, tag) in [
            (ValueKind::LIST, TAG_LIST),
            (ValueKind::MAP, TAG_MAP),
            (ValueKind::STRUCT, TAG_STRUCT),
            (ValueKind::CLOSURE, TAG_CLOSURE),
            (ValueKind::BITSTRING, TAG_BITSTRING),
            (ValueKind::PROCBIN, TAG_PROCBIN),
            (ValueKind::RESOURCE, TAG_RESOURCE),
        ] {
            let bits = tagged_heap_bits(addr, kind);

            assert_eq!(bits, 0x1000 | tag);
            assert_eq!(heap_kind_from_tagged(bits), Some(kind));
            assert_eq!(heap_addr_from_tagged(bits), Some(0x1000 as *mut u8));
        }
    }

    #[test]
    fn fz_value_constructors_use_canonical_value_kind_tags() {
        let null = ValueSlot::null();
        assert_eq!(null.raw(), 0);
        assert_eq!(null.kind(), ValueKind::NULL);

        let int = ValueSlot::int(-12);
        assert_eq!(int.raw() as i64, -12);
        assert_eq!(int.kind(), ValueKind::INT);

        let atom = ValueSlot::atom(42);
        assert_eq!(atom.raw(), 42);
        assert_eq!(atom.kind(), ValueKind::ATOM);

        let float = ValueSlot::float(3.5);
        assert_eq!(f64::from_bits(float.raw()), 3.5);
        assert_eq!(float.kind(), ValueKind::FLOAT);

        let heap = ValueSlot::heap_ptr(0x1000 as *mut u8, ValueKind::MAP);
        assert_eq!(heap.raw(), 0x1000);
        assert_eq!(heap.kind(), ValueKind::MAP);
        assert_eq!(heap.tagged_heap_bits(), Some(0x1000 | TAG_MAP));
    }

    #[test]
    fn value_slot_round_trip_without_packed_scalar_tags() {
        let values = [
            ValueSlot::int(-12),
            ValueSlot::atom(42),
            ValueSlot::null(),
            ValueSlot::bool_atom(true),
            ValueSlot::bool_atom(false),
            ValueSlot::empty_list(),
        ];

        for value in values {
            let decoded =
                ValueSlot::decode_parts(value.raw(), value.kind().tag()).expect("value slot parts");
            assert_eq!(decoded, value);
        }

        assert_eq!(ValueSlot::int(7).raw(), 7);
        assert_eq!(ValueSlot::atom(TRUE_ATOM_ID).raw(), TRUE_ATOM_ID as u64);
        assert_eq!(ValueSlot::nil_atom().raw(), NIL_ATOM_ID as u64);
        assert_eq!(ValueSlot::bool_atom(true).raw(), TRUE_ATOM_ID as u64);
        assert_eq!(ValueSlot::bool_atom(false).raw(), FALSE_ATOM_ID as u64);
        assert_eq!(ValueSlot::empty_list().raw(), 0);
    }

    #[test]
    fn value_slot_decode_parts_uses_low_kind_nibble() {
        let decoded = ValueSlot::decode_parts(0, TAG_MASK as u8 + 1).expect("masked kind byte");
        assert_eq!(decoded, ValueSlot::null());
    }

    #[test]
    fn fz_value_decodes_side_band_parts_without_packed_tags() {
        let looks_like_packed_int = 0x11;
        let decoded = ValueSlot::decode_parts(looks_like_packed_int, ValueKind::LIST.tag())
            .expect("strict side-band decode");

        assert_eq!(decoded.raw(), looks_like_packed_int);
        assert_eq!(decoded.kind(), ValueKind::LIST);
    }

    #[test]
    fn fz_value_decodes_tagged_heap_bits_from_low_four_bits() {
        let decoded = ValueSlot::decode_tagged_heap_bits(0x2000 | TAG_RESOURCE).expect("heap bits");

        assert_eq!(decoded.raw(), 0x2000);
        assert_eq!(decoded.kind(), ValueKind::RESOURCE);
        assert_eq!(decoded.heap_addr(), Some(0x2000 as *mut u8));
    }

    #[test]
    fn list_cons_stores_canonical_head_kind_in_link_low_bits() {
        let cons = ListCons::from_value_head(ValueSlot::float(2.5), EMPTY_LIST);

        assert_eq!(cons.head, 2.5f64.to_bits());
        assert_eq!(cons.head_kind(), ValueKind::FLOAT);
        assert_eq!(cons.head_value(), ValueSlot::float(2.5));
        assert_eq!(cons.tail_bits(), EMPTY_LIST);
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
    fn object_size_returns_list_size() {
        let ptr_with_tag = 0x1000_u64 | TAG_LIST;
        assert_eq!(object_size(ptr_with_tag), 16);
    }

    #[test]
    fn object_size_dispatches_from_pointer_tag_and_object_local_metadata() {
        #[repr(align(16))]
        struct AlignedWords([u64; 8]);

        let mut words = AlignedWords([0; 8]);
        let addr = words.0.as_mut_ptr() as *mut u8;
        let write_word0 = |value| unsafe {
            std::ptr::write(addr as *mut u64, value);
        };

        write_word0(3);
        assert_eq!(
            object_size(tagged_heap_bits(addr, ValueKind::MAP)),
            map_size_for_count(3)
        );

        write_word0(7);
        assert_eq!(
            object_size_with_struct_payload(tagged_heap_bits(addr, ValueKind::STRUCT), |schema| {
                assert_eq!(schema, 7);
                24
            }),
            struct_size_for_payload(24)
        );

        write_word0((closure_flags_pack(2, 0) as u64) << 32);
        assert_eq!(
            object_size(tagged_heap_bits(addr, ValueKind::CLOSURE)),
            closure_size_for_count(2)
        );

        write_word0(17);
        assert_eq!(
            object_size(tagged_heap_bits(addr, ValueKind::BITSTRING)),
            bitstring_size_for_bit_len(17)
        );
        assert_eq!(object_size(tagged_heap_bits(addr, ValueKind::PROCBIN)), 16);
        assert_eq!(object_size(tagged_heap_bits(addr, ValueKind::RESOURCE)), 48);
    }

    #[test]
    fn immediate_tags_not_used_for_pointers() {
        let p = alloc_struct(0, 0) as u64;
        assert_eq!(p & TAG_MASK, TAG_NULL);
        assert_ne!(p & TAG_MASK, TAG_KIND_INT);
        assert_ne!(p & TAG_MASK, TAG_KIND_FLOAT);
        assert_ne!(p & TAG_MASK, TAG_KIND_ATOM);
    }

    #[test]
    fn fz_value_recognizes_explicit_list_typed_pointer() {
        let addr = 0x1000 as *mut u8;
        let tv = ValueSlot::heap_ptr(addr, ValueKind::LIST);

        assert_eq!(tv.kind, ValueKind::LIST);
        assert_eq!(tv.heap_addr(), Some(addr));
        assert_eq!(tv.tagged_heap_bits(), Some(0x1000 | TAG_LIST));
    }

}

/// Debug rendering of FzValues. Lifted out of ir_codegen.rs by
/// fz-ul4.23.4.3 so that any execution path (JIT, future interp/AOT) can
/// use the same rendering — values are uniformly tagged, regardless of
/// what produced them. The single runtime dependency is the heap's
/// schema registry on the current Process, accessed via
/// `crate::process::current_process()`.
pub mod debug {
    use super::{ListCons, ValueKind};
    use crate::process::{CURRENT_PROCESS, current_process};

    /// Render an atom id as `:name` if the current Process has a name
    /// for it; fall back to `:atom_N` otherwise. The fallback fires when
    /// render is called without a Process installed (e.g. unit tests
    /// poking the renderer directly) or when an id is outside the
    /// module's table (defensive — shouldn't happen in practice).
    fn render_atom(id: u32) -> String {
        match id {
            super::NIL_ATOM_ID => return "nil".to_string(),
            super::TRUE_ATOM_ID => return "true".to_string(),
            super::FALSE_ATOM_ID => return "false".to_string(),
            _ => {}
        }
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

    fn is_current_heap_list(bits: u64) -> bool {
        let Some(p) = super::list_addr_from_tagged(bits) else {
            return false;
        };
        if p.is_null() {
            return false;
        }
        let proc_ptr = CURRENT_PROCESS.with(|c| c.get());
        !proc_ptr.is_null() && unsafe { (*proc_ptr).heap.contains_heap_addr(p) }
    }

    fn is_current_heap_map(bits: u64) -> bool {
        let Some(p) = super::map_addr_from_tagged(bits) else {
            return false;
        };
        if p.is_null() {
            return false;
        }
        let proc_ptr = CURRENT_PROCESS.with(|c| c.get());
        !proc_ptr.is_null() && unsafe { (*proc_ptr).heap.contains_heap_addr(p) }
    }

    pub fn render(bits: u64) -> String {
        if is_current_heap_list(bits) {
            return render_list(bits);
        }
        if is_current_heap_map(bits) {
            return render_map(bits);
        }
        if super::closure_addr_from_tagged(bits).is_some() {
            return render_closure(bits);
        }
        if super::struct_addr_from_tagged(bits).is_some() {
            return render_struct(bits);
        }
        if super::bitstring_addr_from_tagged(bits).is_some() {
            return render_bitstring(bits);
        }
        if super::procbin_addr_from_tagged(bits).is_some() {
            return render_bitstring(bits);
        }
        if bits == super::EMPTY_LIST {
            "[]".into()
        } else {
            format!("#ptr<{:#x}>", bits)
        }
    }

    /// Render a heap-typed Struct (currently only emitted for tuples). Reads
    /// the schema from the current Process's SchemaRegistry to determine
    /// field count. Each value field renders inline; non-value fields
    /// are elided (no callers emit them yet).
    fn render_struct(bits: u64) -> String {
        let p = super::struct_addr_from_tagged(bits).expect("struct bits");
        let schema_id = unsafe { super::struct_schema_id(p) };
        let field_offsets: Vec<u32> = {
            let reg = current_process().heap.schemas_registry();
            let registry = reg.borrow();
            let schema = registry.get(schema_id);
            schema
                .fields
                .iter()
                .filter(|f| matches!(f.kind, crate::heap::FieldKind::ValueSlot))
                .map(|f| f.offset)
                .collect()
        };
        let parts: Vec<String> = field_offsets
            .into_iter()
            .map(|offset| render_value(current_process().heap.read_field_slot(p, offset)))
            .collect();
        format!("{{{}}}", parts.join(", "))
    }

    /// Render a heap Map as `%{k => v, ...}` in canonical sorted order.
    fn render_map(bits: u64) -> String {
        let p = super::map_addr_from_tagged(bits).unwrap();
        let count = unsafe { super::map_count(p) };
        let mut parts: Vec<String> = Vec::with_capacity(count);
        for i in 0..count {
            let (k, v) = unsafe { super::map_entry(p, i) };
            parts.push(format!("{} => {}", render_value(k), render_value(v)));
        }
        format!("%{{{}}}", parts.join(", "))
    }

    pub fn render_value(value: super::ValueSlot) -> String {
        match value.kind {
            ValueKind::INT => (value.raw as i64).to_string(),
            ValueKind::FLOAT => f64::from_bits(value.raw).to_string(),
            ValueKind::ATOM => render_atom(value.raw as u32),
            ValueKind::LIST if value.raw == 0 => "[]".to_string(),
            kind if kind.is_heap() => render(value.raw | kind.tag() as u64),
            ValueKind::NULL => "null".to_string(),
            _ => format!("#slot<{:#x}:{}>", value.raw, value.kind.tag()),
        }
    }

    fn render_bitstring(bits: u64) -> String {
        let p = if super::procbin_addr_from_tagged(bits).is_some() {
            bits as *mut u8
        } else {
            super::bitstring_addr_from_tagged(bits).unwrap()
        };
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

    fn render_closure(bits: u64) -> String {
        let p = super::closure_addr_from_tagged(bits).unwrap();
        let schema_id = unsafe { super::closure_schema_id(p) };
        let flags = unsafe { super::closure_flags(p) };
        format!("#fn<{}/{}>", schema_id, flags)
    }

    fn render_list(bits: u64) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut cur_bits = bits;
        let mut tail_render: Option<String> = None;
        loop {
            if cur_bits == super::EMPTY_LIST {
                break;
            }
            let cp = match super::list_addr_from_tagged(cur_bits) {
                Some(p) => p,
                None => {
                    tail_render = Some(render(cur_bits));
                    break;
                }
            };
            let cons = unsafe { &*(cp as *const ListCons) };
            parts.push(render_typed_list_head(cons));
            cur_bits = cons.tail_bits();
        }
        match tail_render {
            Some(t) => format!("[{} | {}]", parts.join(", "), t),
            None => format!("[{}]", parts.join(", ")),
        }
    }

    fn render_typed_list_head(cons: &ListCons) -> String {
        match cons.head_kind() {
            ValueKind::INT => (cons.head as i64).to_string(),
            ValueKind::FLOAT => f64::from_bits(cons.head).to_string(),
            ValueKind::ATOM => render_atom(cons.head as u32),
            kind if kind.is_heap() => {
                let bits = cons.head | kind.tag() as u64;
                render(bits)
            }
            _ => format!("#slot<{:#x}:{}>", cons.head, cons.head_kind().tag()),
        }
    }

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
            assert!(!is_printable_utf8("hello\x01world"));
        }

        #[test]
        fn escape_round_trips_through_display() {
            assert_eq!(escape_for_display("a\nb"), "a\\nb");
            assert_eq!(escape_for_display("\"quoted\""), "\\\"quoted\\\"");
            assert_eq!(escape_for_display("plain"), "plain");
            assert_eq!(escape_for_display("a\tb\rc"), "a\\tb\\rc");
        }
    }
}
