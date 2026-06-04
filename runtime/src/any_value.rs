//! Strict heap object metadata.
//!
//! Program values are opaque `AnyValueRef` words at runtime boundaries.
//! Containers may store payload words plus object-local kind bytes, but this
//! module does not expose a reusable `{value, kind}` carrier.

use std::alloc::{Layout, alloc};
use std::mem;
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

/// fz-s9y.2 — object-storage empty-list sentinel. This is not the public
/// `AnyValueRef` representation of `[]`; public refs use a null-address
/// List tag. Address 0x8 sits inside page 0, which the OS reserves as
/// unmapped, so the sentinel can't collide with a real heap pointer.
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
        match tag as u64 {
            TAG_NULL | TAG_LIST | TAG_MAP | TAG_STRUCT | TAG_CLOSURE | TAG_BITSTRING | TAG_PROCBIN | TAG_RESOURCE
            | TAG_KIND_INT | TAG_KIND_FLOAT | TAG_KIND_ATOM => Some(Self(tag)),
            _ => None,
        }
    }

    pub const fn tag(self) -> u8 {
        self.0
    }

    pub const fn is_heap(self) -> bool {
        self.0 >= TAG_LIST as u8 && self.0 <= TAG_RESOURCE as u8
    }

    pub const fn is_scalar(self) -> bool {
        matches!(self, Self::INT | Self::FLOAT | Self::ATOM)
    }

    pub const fn from_heap_tag(tag: u64) -> Option<Self> {
        if tag >= TAG_LIST && tag <= TAG_RESOURCE {
            Some(Self(tag as u8))
        } else {
            None
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnyValueRefError {
    UnknownTag(u8),
    ExpectedTag { expected: ValueKind, found: ValueKind },
    ExpectedScalarTag(ValueKind),
    ExpectedHeapObjectTag(ValueKind),
    NullAddress(ValueKind),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaggedRefArch {
    Arm64Tbi,
    X86_64Canonical57,
}

impl TaggedRefArch {
    pub const fn current() -> Self {
        #[cfg(target_arch = "aarch64")]
        {
            Self::Arm64Tbi
        }
        #[cfg(target_arch = "x86_64")]
        {
            Self::X86_64Canonical57
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct AnyValueRefPacking {
    tag_shift: u8,
    address_mask: u64,
}

impl AnyValueRefPacking {
    pub const fn for_arch(arch: TaggedRefArch) -> Self {
        match arch {
            TaggedRefArch::Arm64Tbi => Self::new(56),
            TaggedRefArch::X86_64Canonical57 => Self::new(57),
        }
    }

    pub const fn current() -> Self {
        Self::for_arch(TaggedRefArch::current())
    }

    const fn new(tag_shift: u8) -> Self {
        Self {
            tag_shift,
            address_mask: (1u64 << tag_shift) - 1,
        }
    }

    pub const fn tag_shift(self) -> u8 {
        self.tag_shift
    }

    pub const fn address_mask(self) -> u64 {
        self.address_mask
    }

    fn pack(self, tag: ValueKind, address: usize) -> AnyValueRef {
        AnyValueRef {
            word: ((tag.tag() as u64) << self.tag_shift) | ((address as u64) & self.address_mask),
        }
    }

    pub fn tag(self, value: AnyValueRef) -> Result<ValueKind, AnyValueRefError> {
        let raw = (value.word >> self.tag_shift) as u8;
        ValueKind::new(raw).ok_or(AnyValueRefError::UnknownTag(raw))
    }

    fn address(self, value: AnyValueRef) -> usize {
        (value.word & self.address_mask) as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct AnyValueRef {
    word: u64,
}

impl AnyValueRef {
    pub fn from_raw_word(word: u64) -> Result<Self, AnyValueRefError> {
        let value = Self { word };
        AnyValueRefPacking::current().tag(value)?;
        Ok(value)
    }

    pub const fn raw_word(self) -> u64 {
        self.word
    }

    pub fn null() -> Self {
        AnyValueRefPacking::current().pack(ValueKind::NULL, 0)
    }

    pub fn empty_list() -> Self {
        AnyValueRefPacking::current().pack(ValueKind::LIST, 0)
    }

    pub fn from_scalar_slot(tag: ValueKind, slot: *const u64) -> Result<Self, AnyValueRefError> {
        if !tag.is_scalar() {
            return Err(AnyValueRefError::ExpectedScalarTag(tag));
        }
        if slot.is_null() {
            return Err(AnyValueRefError::NullAddress(tag));
        }
        Ok(AnyValueRefPacking::current().pack(tag, slot as usize))
    }

    pub fn from_heap_object(tag: ValueKind, addr: *const u8) -> Result<Self, AnyValueRefError> {
        if !tag.is_heap() {
            return Err(AnyValueRefError::ExpectedHeapObjectTag(tag));
        }
        if addr.is_null() && tag != ValueKind::LIST {
            return Err(AnyValueRefError::NullAddress(tag));
        }
        Ok(AnyValueRefPacking::current().pack(tag, addr as usize))
    }

    pub fn tag(self) -> ValueKind {
        AnyValueRefPacking::current()
            .tag(self)
            .expect("AnyValueRef contains a valid tag")
    }

    fn cleared_addr(self) -> *mut u8 {
        AnyValueRefPacking::current().address(self) as *mut u8
    }

    pub fn storage_addr(self) -> *mut u8 {
        self.cleared_addr()
    }

    pub fn storage_raw(self) -> Result<u64, AnyValueRefError> {
        if self.is_empty_list() {
            return Ok(0);
        }
        Ok(match self.tag() {
            ValueKind::NULL => 0,
            ValueKind::INT => self.load_int()? as u64,
            ValueKind::FLOAT => self.load_float()?.to_bits(),
            ValueKind::ATOM => self.load_atom()?,
            tag if tag.is_heap() => self.cleared_addr() as u64,
            _ => unreachable!("AnyValueRef tag set is exhaustive"),
        })
    }

    pub fn heap_object_word(self) -> Result<u64, AnyValueRefError> {
        let tag = self.tag();
        if !tag.is_heap() {
            return Err(AnyValueRefError::ExpectedHeapObjectTag(tag));
        }
        Ok(heap_object_word(self.cleared_addr(), tag))
    }

    pub fn is_heap_root(self) -> bool {
        self.tag().is_heap() && !self.is_empty_list()
    }

    pub fn is_empty_list(self) -> bool {
        self.tag() == ValueKind::LIST && self.cleared_addr().is_null()
    }

    pub fn load_int(self) -> Result<i64, AnyValueRefError> {
        self.expect_tag(ValueKind::INT)?;
        Ok(unsafe { ptr::read(self.cleared_addr() as *const i64) })
    }

    pub fn load_float(self) -> Result<f64, AnyValueRefError> {
        self.expect_tag(ValueKind::FLOAT)?;
        Ok(f64::from_bits(unsafe { ptr::read(self.cleared_addr() as *const u64) }))
    }

    pub fn load_atom(self) -> Result<u64, AnyValueRefError> {
        self.expect_tag(ValueKind::ATOM)?;
        Ok(unsafe { ptr::read(self.cleared_addr() as *const u64) })
    }

    pub fn heap_addr(self, expected: ValueKind) -> Result<*mut u8, AnyValueRefError> {
        if !expected.is_heap() {
            return Err(AnyValueRefError::ExpectedHeapObjectTag(expected));
        }
        self.expect_tag(expected)?;
        Ok(self.cleared_addr())
    }

    pub fn list_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::LIST)
    }

    pub fn map_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::MAP)
    }

    pub fn struct_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::STRUCT)
    }

    pub fn closure_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::CLOSURE)
    }

    pub fn bitstring_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::BITSTRING)
    }

    pub fn procbin_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::PROCBIN)
    }

    pub fn resource_addr(self) -> Result<*mut u8, AnyValueRefError> {
        self.heap_addr(ValueKind::RESOURCE)
    }

    fn expect_tag(self, expected: ValueKind) -> Result<(), AnyValueRefError> {
        let found = self.tag();
        if found == expected {
            Ok(())
        } else {
            Err(AnyValueRefError::ExpectedTag { expected, found })
        }
    }
}

#[cfg(test)]
mod any_value_ref_tests {
    use super::*;
    use super::{AnyValue, ValueKind, heap_object_word};
    use crate::heap::{Heap, Schema, SchemaRegistry};
    use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn packing_strategy_uses_platform_specific_tag_shift() {
        assert_eq!(AnyValueRefPacking::for_arch(TaggedRefArch::Arm64Tbi).tag_shift(), 56);
        assert_eq!(
            AnyValueRefPacking::for_arch(TaggedRefArch::X86_64Canonical57).tag_shift(),
            57
        );
        assert_eq!(
            AnyValueRefPacking::for_arch(TaggedRefArch::Arm64Tbi).address_mask(),
            (1u64 << 56) - 1
        );
        assert_eq!(
            AnyValueRefPacking::for_arch(TaggedRefArch::X86_64Canonical57).address_mask(),
            (1u64 << 57) - 1
        );
    }

    #[test]
    fn packing_extracts_same_semantic_tag_on_supported_arches() {
        let address = 0x1234_5678usize;
        for packing in [
            AnyValueRefPacking::for_arch(TaggedRefArch::Arm64Tbi),
            AnyValueRefPacking::for_arch(TaggedRefArch::X86_64Canonical57),
        ] {
            let value = packing.pack(ValueKind::MAP, address);
            assert_eq!(packing.tag(value), Ok(ValueKind::MAP));
            assert_eq!(packing.address(value), address);
        }
    }

    #[test]
    fn any_value_refs_use_value_kind_tags_directly() {
        let packing = AnyValueRefPacking::current();
        let value = packing.pack(ValueKind::ATOM, 0x1000);

        assert_eq!(packing.tag(value), Ok(ValueKind::ATOM));
        assert_eq!(value.raw_word() >> packing.tag_shift(), ValueKind::ATOM.tag() as u64);
        assert_eq!(
            AnyValueRef::from_raw_word(8_u64 << packing.tag_shift()),
            Err(AnyValueRefError::UnknownTag(8))
        );
    }

    #[test]
    fn empty_list_is_null_address_list_ref() {
        let empty = AnyValueRef::empty_list();

        assert_eq!(empty.tag(), ValueKind::LIST);
        assert!(empty.is_empty_list());
        assert!(!empty.is_heap_root());
        assert_eq!(empty.list_addr(), Ok(ptr::null_mut()));
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::LIST, ptr::null()).expect("empty list ref"),
            empty
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::MAP, ptr::null()),
            Err(AnyValueRefError::NullAddress(ValueKind::MAP))
        );
    }

    #[test]
    fn x86_packing_preserves_wide_canonical_user_addresses() {
        let packing = AnyValueRefPacking::for_arch(TaggedRefArch::X86_64Canonical57);
        let address = 0x00ab_cdef_1234_5000usize;
        let value = packing.pack(ValueKind::INT, address);

        assert_eq!(packing.tag(value), Ok(ValueKind::INT));
        assert_eq!(packing.address(value), address);
    }

    #[test]
    fn scalar_refs_load_full_width_payloads() {
        let int_slot = (-42i64) as u64;
        let float_slot = 3.5f64.to_bits();
        let atom_slot = 99u64;

        let int_ref = AnyValueRef::from_scalar_slot(ValueKind::INT, &int_slot).expect("int ref");
        let float_ref = AnyValueRef::from_scalar_slot(ValueKind::FLOAT, &float_slot).expect("float ref");
        let atom_ref = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &atom_slot).expect("atom ref");

        assert_eq!(int_ref.load_int(), Ok(-42));
        assert_eq!(float_ref.load_float(), Ok(3.5));
        assert_eq!(atom_ref.load_atom(), Ok(99));
        assert!(!int_ref.is_heap_root());
    }

    #[test]
    fn bad_scalar_projection_reports_expected_and_found_tags() {
        let slot = 7u64;
        let value = AnyValueRef::from_scalar_slot(ValueKind::INT, &slot).expect("int ref");

        assert_eq!(
            value.load_float(),
            Err(AnyValueRefError::ExpectedTag {
                expected: ValueKind::FLOAT,
                found: ValueKind::INT
            })
        );
        assert_eq!(
            AnyValueRef::from_scalar_slot(ValueKind::MAP, &slot),
            Err(AnyValueRefError::ExpectedScalarTag(ValueKind::MAP))
        );
    }

    #[test]
    fn heap_object_refs_clear_addresses_before_projection() {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut heap = Heap::new(4096, schemas.clone());
        let schema_id = heap.register_schema(Schema::tuple_of_arity(1));

        let list_bits = heap.alloc_list_cons_slot(AnyValue::int(1), EMPTY_LIST_BITS);
        let list_addr = list_addr_from_tagged(list_bits).expect("list addr");
        let map_bits = heap.alloc_map_slots(&[(AnyValue::atom(3), AnyValue::int(4))]);
        let map_addr = map_addr_from_tagged(map_bits).expect("map addr");
        let struct_addr = heap.alloc_struct(schema_id);
        let bitstring_addr = heap.alloc_bitstring(&[0xAA], 8);
        let closure_bits = heap.alloc_closure(schema_id, 0, 0, 0xfeed, &[]);
        let closure_addr = closure_addr_from_tagged(closure_bits).expect("closure addr");
        let procbin_addr = heap.alloc_bitstring(&[0u8; 65], 65 * 8);
        let resource_addr = alloc_resource(
            &mut heap,
            ResourceHandle::new(77, fz_resource_destructor_noop),
            AnyValue::nil_atom(),
        )
        .as_raw();

        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::LIST, list_addr)
                .expect("list ref")
                .list_addr(),
            Ok(list_addr)
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::MAP, map_addr)
                .expect("map ref")
                .map_addr(),
            Ok(map_addr)
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::STRUCT, struct_addr)
                .expect("struct ref")
                .struct_addr(),
            Ok(struct_addr)
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr)
                .expect("closure ref")
                .closure_addr(),
            Ok(closure_addr)
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::BITSTRING, bitstring_addr)
                .expect("bitstring ref")
                .bitstring_addr(),
            Ok(bitstring_addr)
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::PROCBIN, procbin_addr)
                .expect("procbin ref")
                .procbin_addr(),
            Ok(procbin_addr)
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::RESOURCE, resource_addr)
                .expect("resource ref")
                .resource_addr(),
            Ok(resource_addr)
        );

        let packed = AnyValueRef::from_heap_object(ValueKind::BITSTRING, bitstring_addr).expect("bitstring ref");
        assert_eq!(
            heap_object_word(packed.bitstring_addr().expect("bitstring addr"), ValueKind::BITSTRING),
            heap_object_word(bitstring_addr, ValueKind::BITSTRING)
        );
        let packed = AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr).expect("closure ref");
        assert_eq!(
            heap_object_word(packed.closure_addr().expect("closure addr"), ValueKind::CLOSURE),
            heap_object_word(closure_addr, ValueKind::CLOSURE)
        );
    }

    #[test]
    fn bad_heap_projection_reports_expected_and_found_tags() {
        let mut bytes = [0u8; 16];
        let map_ref = AnyValueRef::from_heap_object(ValueKind::MAP, bytes.as_mut_ptr()).expect("map ref");

        assert!(map_ref.is_heap_root());
        assert_eq!(
            map_ref.list_addr(),
            Err(AnyValueRefError::ExpectedTag {
                expected: ValueKind::LIST,
                found: ValueKind::MAP
            })
        );
        assert_eq!(
            AnyValueRef::from_heap_object(ValueKind::INT, bytes.as_mut_ptr()),
            Err(AnyValueRefError::ExpectedHeapObjectTag(ValueKind::INT))
        );
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AnyValue {
    Null,
    EmptyList,
    Int(i64),
    Float(u64),
    Atom(u32),
    HeapRef(AnyValueRef),
}

impl AnyValue {
    pub const fn null() -> Self {
        Self::Null
    }

    pub const fn empty_list() -> Self {
        Self::EmptyList
    }

    pub const fn int(value: i64) -> Self {
        Self::Int(value)
    }

    pub const fn float(value: f64) -> Self {
        Self::Float(value.to_bits())
    }

    pub const fn atom(atom_id: u32) -> Self {
        Self::Atom(atom_id)
    }

    pub const fn nil_atom() -> Self {
        Self::Atom(NIL_ATOM_ID)
    }

    pub const fn bool_atom(value: bool) -> Self {
        if value {
            Self::Atom(TRUE_ATOM_ID)
        } else {
            Self::Atom(FALSE_ATOM_ID)
        }
    }

    pub fn heap_ptr(addr: *mut u8, kind: ValueKind) -> Self {
        if !kind.is_heap() {
            panic!("heap_ptr requires a heap ValueKind");
        }
        Self::HeapRef(AnyValueRef::from_heap_object(kind, addr).expect("heap value ref"))
    }

    pub fn from_ref(value: AnyValueRef) -> Result<Self, AnyValueRefError> {
        if value.is_empty_list() {
            return Ok(Self::EmptyList);
        }
        Ok(match value.tag() {
            ValueKind::NULL => Self::Null,
            ValueKind::INT => Self::Int(value.load_int()?),
            ValueKind::FLOAT => Self::Float(value.load_float()?.to_bits()),
            ValueKind::ATOM => Self::Atom(value.load_atom()? as u32),
            tag if tag.is_heap() => Self::HeapRef(value),
            _ => unreachable!("AnyValueRef tag set is exhaustive"),
        })
    }

    pub fn decode_parts(raw: u64, kind_tag: u8) -> Option<Self> {
        let kind = ValueKind::new(kind_tag & TAG_MASK as u8)?;
        Some(match kind {
            ValueKind::NULL => Self::Null,
            ValueKind::INT => Self::Int(raw as i64),
            ValueKind::FLOAT => Self::Float(raw),
            ValueKind::ATOM => Self::Atom(raw as u32),
            ValueKind::LIST if raw == 0 => Self::EmptyList,
            kind if kind.is_heap() => Self::heap_ptr(raw as *mut u8, kind),
            _ => return None,
        })
    }

    pub fn decode_tagged_heap_bits(bits: u64) -> Option<Self> {
        let kind = heap_kind_from_tagged(bits)?;
        if kind == ValueKind::LIST && (bits & !TAG_MASK) == 0 {
            return Some(Self::EmptyList);
        }
        Some(Self::heap_ptr((bits & !TAG_MASK) as *mut u8, kind))
    }

    pub fn raw(self) -> u64 {
        match self {
            Self::Null | Self::EmptyList => 0,
            Self::Int(value) => value as u64,
            Self::Float(bits) => bits,
            Self::Atom(atom_id) => atom_id as u64,
            Self::HeapRef(value) => value.storage_raw().expect("heap ref raw"),
        }
    }

    pub fn kind(self) -> ValueKind {
        match self {
            Self::Null => ValueKind::NULL,
            Self::EmptyList => ValueKind::LIST,
            Self::Int(_) => ValueKind::INT,
            Self::Float(_) => ValueKind::FLOAT,
            Self::Atom(_) => ValueKind::ATOM,
            Self::HeapRef(value) => value.tag(),
        }
    }

    pub fn heap_addr(self) -> Option<*mut u8> {
        match self {
            Self::HeapRef(_) => Some(self.raw() as *mut u8),
            _ => None,
        }
    }

    pub fn heap_object_word(self) -> Option<u64> {
        self.kind()
            .is_heap()
            .then(|| heap_object_word(self.raw() as *const u8, self.kind()))
    }

    pub fn ref_word(self) -> AnyValueRef {
        match self {
            Self::Null => AnyValueRef::null(),
            Self::EmptyList => AnyValueRef::empty_list(),
            Self::HeapRef(value) => value,
            Self::Int(_) | Self::Float(_) | Self::Atom(_) => {
                panic!("scalar AnyValue needs object-local storage before it can become a ref")
            }
        }
    }
}

// Bitstring storage dispatchers moved to `crate::procbin` in fz-q8d.1.
// `any_value.rs` does not own bitstring layout; render uses the procbin
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
    debug_assert!(halt_kind <= 0b11, "closure halt_kind {} out of range", halt_kind);
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
    let raw_bytes = (captured_count + 1) * 8;
    let kind_bytes = (captured_count + 7) & !7;
    (8 + raw_bytes + kind_bytes + 15) & !15
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
    unsafe { ptr::read(addr as *const u32) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object.
#[inline]
pub unsafe fn closure_flags(addr: *const u8) -> u16 {
    unsafe { ptr::read(addr.add(4) as *const u32) as u16 }
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
    unsafe { ptr::read(addr.add(8) as *const u64) }
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
pub unsafe fn closure_capture_raw_kind(addr: *const u8, idx: usize) -> (u64, ValueKind) {
    let kind_tag = unsafe { ptr::read(closure_capture_kind_slot(addr, idx)) };
    let raw = unsafe { ptr::read(closure_capture_raw_slot(addr, idx)) };
    let kind = ValueKind::new(kind_tag).expect("closure capture kind");
    (raw, kind)
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_set_raw_kind(addr: *const u8, idx: usize, raw: u64, kind: ValueKind) {
    let raw = if kind.is_heap() { raw & !TAG_MASK } else { raw };
    unsafe {
        ptr::write(closure_capture_raw_slot(addr, idx), raw);
        ptr::write(closure_capture_kind_slot(addr, idx), kind.tag());
    }
}

/// # Safety
///
/// `addr` must point to an initialized strict Closure object and `idx` must
/// be in bounds.
#[inline]
pub unsafe fn closure_capture_value(addr: *const u8, idx: usize) -> AnyValue {
    let (raw, kind) = unsafe { closure_capture_raw_kind(addr, idx) };
    AnyValue::decode_parts(raw, kind.tag()).expect("closure capture value")
}

/// # Safety
///
/// `addr` must point to an initialized strict Closure object and `idx` must
/// be in bounds.
#[inline]
pub unsafe fn closure_capture_set(addr: *const u8, idx: usize, value: AnyValue) {
    unsafe { closure_capture_set_raw_kind(addr, idx, value.raw(), value.kind()) };
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_ref_word(addr: *const u8, idx: usize) -> u64 {
    let raw_slot = unsafe { closure_capture_raw_slot(addr, idx) };
    let (raw, kind) = unsafe { closure_capture_raw_kind(addr, idx) };
    match kind {
        ValueKind::NULL => AnyValueRef::null().raw_word(),
        ValueKind::LIST if raw == 0 => AnyValueRef::empty_list().raw_word(),
        ValueKind::INT | ValueKind::FLOAT | ValueKind::ATOM => {
            AnyValueRef::from_scalar_slot(kind, raw_slot as *const u64)
                .expect("closure scalar capture ref")
                .raw_word()
        }
        kind if kind.is_heap() => heap_object_word(raw as *const u8, kind),
        _ => unreachable!("unknown closure capture kind"),
    }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Closure object and
/// `idx` must be in-bounds for its captured-count prefix.
#[inline]
pub unsafe fn closure_capture_set_ref_word(addr: *const u8, idx: usize, value: u64) {
    let value = AnyValueRef::from_raw_word(value).expect("closure capture ref word");
    let any = AnyValue::from_ref(value).expect("closure capture ref value");
    unsafe { closure_capture_set(addr, idx, any) };
}

/// # Safety
///
/// Both closure addresses must be initialized strict Closure objects, and both
/// capture indexes must be in-bounds.
#[inline]
pub unsafe fn closure_capture_copy(src_addr: *const u8, src_idx: usize, dst_addr: *const u8, dst_idx: usize) {
    let raw = unsafe { ptr::read(closure_capture_raw_slot(src_addr, src_idx)) };
    let kind = unsafe { ptr::read(closure_capture_kind_slot(src_addr, src_idx)) };
    unsafe {
        ptr::write(closure_capture_raw_slot(dst_addr, dst_idx), raw);
        ptr::write(closure_capture_kind_slot(dst_addr, dst_idx), kind);
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
pub(crate) fn heap_object_word(addr: *const u8, kind: ValueKind) -> u64 {
    assert!(kind.is_heap(), "object-local heap words require a heap kind");
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
    let marker = unsafe { ptr::read(addr as *const u64) };
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

pub fn object_size_with_struct_payload(ptr_with_tag: u64, mut struct_payload_size: impl FnMut(u32) -> usize) -> usize {
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
    let count = unsafe { ptr::read(addr as *const u64) as usize };
    map_size_for_count(count)
}

unsafe fn size_of_struct(addr: *const u8, struct_payload_size: &mut impl FnMut(u32) -> usize) -> usize {
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
/// `head` is raw payload. `link` stores an architecture-local tail address plus
/// a high metadata field: 4 bits of head kind followed by one alias flag bit.
/// Low pointer-alignment bits stay clear so future layout checks can keep using
/// normal aligned-address invariants.
#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub struct ListCons {
    pub head: u64,
    pub link: u64,
}

const _: () = {
    assert!(mem::size_of::<ListCons>() == 16);
    assert!(mem::align_of::<ListCons>() == 8);
};

const LIST_LINK_KIND_SHIFT: u8 = AnyValueRefPacking::current().tag_shift();
const LIST_LINK_ALIAS_SHIFT: u8 = LIST_LINK_KIND_SHIFT + TAG_BITS as u8;
const LIST_LINK_KIND_MASK: u64 = TAG_MASK << LIST_LINK_KIND_SHIFT;
pub const LIST_LINK_ALIAS_MASK: u64 = 1u64 << LIST_LINK_ALIAS_SHIFT;
const LIST_LINK_ADDR_MASK: u64 = AnyValueRefPacking::current().address_mask() & !TAG_MASK;
const LIST_LINK_METADATA_MASK: u64 = LIST_LINK_KIND_MASK | LIST_LINK_ALIAS_MASK;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ListLink(u64);

impl ListLink {
    pub fn new(tail_bits: u64, head_kind: ValueKind) -> Self {
        Self(list_tail_addr_from_bits(tail_bits) | ((head_kind.tag() as u64) << LIST_LINK_KIND_SHIFT))
    }

    pub fn from_raw(raw: u64) -> Self {
        Self(raw)
    }

    pub fn raw(self) -> u64 {
        self.0
    }

    pub fn head_kind(self) -> ValueKind {
        let tag = ((self.0 & LIST_LINK_KIND_MASK) >> LIST_LINK_KIND_SHIFT) as u8;
        ValueKind::new(tag).expect("list head kind tag")
    }

    pub fn tail_addr(self) -> u64 {
        self.0 & LIST_LINK_ADDR_MASK
    }

    pub fn tail_bits(self) -> u64 {
        let addr = self.tail_addr();
        if addr == 0 { EMPTY_LIST } else { addr | TAG_LIST }
    }

    pub fn aliased(self) -> bool {
        self.0 & LIST_LINK_ALIAS_MASK != 0
    }

    pub fn mark_aliased(&mut self) {
        self.0 |= LIST_LINK_ALIAS_MASK;
    }

    pub fn with_tail(self, tail_bits: u64) -> Self {
        let metadata = self.0 & LIST_LINK_METADATA_MASK;
        Self(metadata | list_tail_addr_from_bits(tail_bits))
    }
}

impl ListCons {
    pub fn new(head_raw: u64, head_kind: ValueKind, tail_bits: u64) -> Self {
        Self {
            head: head_raw,
            link: ListLink::new(tail_bits, head_kind).raw(),
        }
    }

    pub fn head_kind(&self) -> ValueKind {
        self.link().head_kind()
    }

    pub fn tail_addr(&self) -> u64 {
        self.link().tail_addr()
    }

    pub fn tail_bits(&self) -> u64 {
        self.link().tail_bits()
    }

    pub fn head_raw_kind(&self) -> (u64, ValueKind) {
        (self.head, self.head_kind())
    }

    pub fn head_value(&self) -> AnyValue {
        AnyValue::decode_parts(self.head, self.head_kind().tag()).expect("list head value")
    }

    pub fn aliased(&self) -> bool {
        self.link().aliased()
    }

    pub fn mark_aliased(&mut self) {
        let mut link = self.link();
        link.mark_aliased();
        self.link = link.raw();
    }

    pub fn set_tail_bits(&mut self, tail_bits: u64) {
        self.link = self.link().with_tail(tail_bits).raw();
    }

    pub fn relink_tail_if_unaliased(&mut self, tail_bits: u64) -> bool {
        if self.aliased() {
            return false;
        }
        self.set_tail_bits(tail_bits);
        true
    }

    pub fn link(&self) -> ListLink {
        ListLink::from_raw(self.link)
    }
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
    unsafe { ptr::read(addr as *const u32) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Struct object.
#[inline]
pub unsafe fn struct_flags(addr: *const u8) -> u32 {
    unsafe { ptr::read(addr.add(4) as *const u32) }
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
    unsafe { ptr::read(addr as *const u64) }
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict inline Bitstring.
#[inline]
pub unsafe fn bitstring_bytes_ptr(addr: *const u8) -> *const u8 {
    unsafe { addr.add(8) }
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
    unsafe { ptr::read(addr as *const u64) as usize }
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
pub unsafe fn map_entry_raw_kinds(addr: *const u8, index: usize) -> (u64, ValueKind, u64, ValueKind) {
    let count = unsafe { map_count(addr) };
    assert!(index < count, "map entry index out of bounds");
    let tag = unsafe { ptr::read(map_tag_ptr(addr).add(index)) };
    let keys = unsafe { map_keys_ptr(addr, count) };
    let values = unsafe { map_values_ptr(addr, count) };
    (
        unsafe { ptr::read(keys.add(index)) },
        map_key_kind(tag),
        unsafe { ptr::read(values.add(index)) },
        map_value_kind(tag),
    )
}

/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object, and
/// `index` must be in bounds for that map's entry count.
pub unsafe fn map_entry(addr: *const u8, index: usize) -> (AnyValue, AnyValue) {
    let (kr, kk, vr, vk) = unsafe { map_entry_raw_kinds(addr, index) };
    (
        AnyValue::decode_parts(kr, kk.tag()).expect("map key value"),
        AnyValue::decode_parts(vr, vk.tag()).expect("map entry value"),
    )
}

pub fn alloc_list_cons_raw_kind(head_raw: u64, head_kind: ValueKind, tail_bits: u64) -> u64 {
    unsafe {
        let p = raw_alloc(16) as *mut ListCons;
        ptr::write(p, ListCons::new(head_raw, head_kind, tail_bits));
        heap_object_word(p as *const u8, ValueKind::LIST)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::mem;

    #[test]
    fn list_cons_size_is_16() {
        assert_eq!(mem::size_of::<ListCons>(), 16);
    }

    #[test]
    fn list_cons_layout() {
        let bits = alloc_list_cons_raw_kind(7, ValueKind::INT, EMPTY_LIST);
        let p = list_addr_from_tagged(bits).expect("tagged list ptr");
        unsafe {
            let cons = &*(p as *mut ListCons);
            assert_eq!(cons.head_kind(), ValueKind::INT);
            assert_eq!(cons.head as i64, 7);
            assert_eq!(cons.tail_bits(), EMPTY_LIST);
            assert_eq!(cons.link & TAG_MASK, 0);
            assert_eq!((cons.link & LIST_LINK_KIND_MASK) >> LIST_LINK_KIND_SHIFT, TAG_KIND_INT);
            assert!(!cons.aliased());
        }
    }

    #[test]
    fn list_cons_chain() {
        // [1, 2, 3]
        let l3 = alloc_list_cons_raw_kind(3, ValueKind::INT, EMPTY_LIST);
        let l2 = alloc_list_cons_raw_kind(2, ValueKind::INT, l3);
        let l1 = alloc_list_cons_raw_kind(1, ValueKind::INT, l2);
        unsafe {
            let c1 = &*(list_addr_from_tagged(l1).unwrap() as *mut ListCons);
            assert_eq!(c1.head_value(), AnyValue::int(1));
            let c2 = &*(list_addr_from_tagged(c1.tail_bits()).unwrap() as *mut ListCons);
            assert_eq!(c2.head_value(), AnyValue::int(2));
            let c3 = &*(list_addr_from_tagged(c2.tail_bits()).unwrap() as *mut ListCons);
            assert_eq!(c3.head_value(), AnyValue::int(3));
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
            let bits = heap_object_word(addr, kind);

            assert_eq!(bits, 0x1000 | tag);
            assert_eq!(heap_kind_from_tagged(bits), Some(kind));
            assert_eq!(heap_addr_from_tagged(bits), Some(0x1000 as *mut u8));
        }
    }

    #[test]
    fn value_kind_rejects_non_value_tags() {
        assert_eq!(ValueKind::new(TAG_FWD as u8), None);
        assert_eq!(ValueKind::new(9), None);
        assert_eq!(ValueKind::new(10), None);
        assert_eq!(ValueKind::new(11), None);
        assert_eq!(ValueKind::new(12), None);
    }

    #[test]
    fn any_value_constructors_use_canonical_value_kind_tags() {
        let null = AnyValue::null();
        assert_eq!(null.raw(), 0);
        assert_eq!(null.kind(), ValueKind::NULL);

        let int = AnyValue::int(-12);
        assert_eq!(int.raw() as i64, -12);
        assert_eq!(int.kind(), ValueKind::INT);

        let atom = AnyValue::atom(42);
        assert_eq!(atom.raw(), 42);
        assert_eq!(atom.kind(), ValueKind::ATOM);

        let float = AnyValue::float(3.5);
        assert_eq!(f64::from_bits(float.raw()), 3.5);
        assert_eq!(float.kind(), ValueKind::FLOAT);

        let heap = AnyValue::heap_ptr(0x1000 as *mut u8, ValueKind::MAP);
        assert_eq!(heap.raw(), 0x1000);
        assert_eq!(heap.kind(), ValueKind::MAP);
        assert_eq!(heap.heap_object_word(), Some(0x1000 | TAG_MAP));
    }

    #[test]
    fn any_value_round_trip_without_packed_scalar_tags() {
        let values = [
            AnyValue::int(-12),
            AnyValue::atom(42),
            AnyValue::null(),
            AnyValue::bool_atom(true),
            AnyValue::bool_atom(false),
            AnyValue::empty_list(),
        ];

        for value in values {
            let decoded = AnyValue::decode_parts(value.raw(), value.kind().tag()).expect("value slot parts");
            assert_eq!(decoded, value);
        }

        assert_eq!(AnyValue::int(7).raw(), 7);
        assert_eq!(AnyValue::atom(TRUE_ATOM_ID).raw(), TRUE_ATOM_ID as u64);
        assert_eq!(AnyValue::nil_atom().raw(), NIL_ATOM_ID as u64);
        assert_eq!(AnyValue::bool_atom(true).raw(), TRUE_ATOM_ID as u64);
        assert_eq!(AnyValue::bool_atom(false).raw(), FALSE_ATOM_ID as u64);
        assert_eq!(AnyValue::empty_list().raw(), 0);
    }

    #[test]
    fn any_value_decode_parts_uses_low_kind_nibble() {
        let decoded = AnyValue::decode_parts(0, TAG_MASK as u8 + 1).expect("masked kind byte");
        assert_eq!(decoded, AnyValue::null());
    }

    #[test]
    fn any_value_decodes_side_band_parts_without_packed_tags() {
        let looks_like_packed_int = 0x11;
        let decoded =
            AnyValue::decode_parts(looks_like_packed_int, ValueKind::LIST.tag()).expect("strict side-band decode");

        assert_eq!(decoded.raw(), looks_like_packed_int);
        assert_eq!(decoded.kind(), ValueKind::LIST);
    }

    #[test]
    fn any_value_decodes_tagged_heap_bits_from_low_four_bits() {
        let decoded = AnyValue::decode_tagged_heap_bits(0x2000 | TAG_RESOURCE).expect("heap bits");

        assert_eq!(decoded.raw(), 0x2000);
        assert_eq!(decoded.kind(), ValueKind::RESOURCE);
        assert_eq!(decoded.heap_addr(), Some(0x2000 as *mut u8));
    }

    #[test]
    fn list_cons_stores_canonical_head_kind_in_link_high_bits() {
        let cons = ListCons::new(2.5f64.to_bits(), ValueKind::FLOAT, EMPTY_LIST);

        assert_eq!(cons.head, 2.5f64.to_bits());
        assert_eq!(cons.head_kind(), ValueKind::FLOAT);
        assert_eq!(cons.head_value(), AnyValue::float(2.5));
        assert_eq!(cons.tail_bits(), EMPTY_LIST);
        assert_eq!(cons.link & TAG_MASK, 0);
        assert_eq!(
            (cons.link & LIST_LINK_KIND_MASK) >> LIST_LINK_KIND_SHIFT,
            TAG_KIND_FLOAT
        );
    }

    #[test]
    fn list_link_keeps_alias_bit_in_high_metadata() {
        let tail = alloc_list_cons_raw_kind(3, ValueKind::INT, EMPTY_LIST);
        let mut cons = ListCons::new(7, ValueKind::INT, tail);

        assert_eq!(cons.tail_bits(), tail);
        assert!(!cons.aliased());

        cons.mark_aliased();

        assert!(cons.aliased());
        assert_eq!(cons.head_kind(), ValueKind::INT);
        assert_eq!(cons.tail_bits(), tail);
        assert_ne!(cons.link & LIST_LINK_ALIAS_MASK, 0);
        assert_eq!(cons.link & TAG_MASK, 0);
    }

    #[test]
    fn list_link_tail_rewrite_preserves_high_metadata() {
        let old_tail = alloc_list_cons_raw_kind(1, ValueKind::INT, EMPTY_LIST);
        let new_tail = alloc_list_cons_raw_kind(2, ValueKind::INT, EMPTY_LIST);
        let mut cons = ListCons::new(7, ValueKind::ATOM, old_tail);
        cons.mark_aliased();

        cons.set_tail_bits(new_tail);

        assert_eq!(cons.head_kind(), ValueKind::ATOM);
        assert!(cons.aliased());
        assert_eq!(cons.tail_bits(), new_tail);
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
            ptr::write(addr as *mut u64, value);
        };

        write_word0(3);
        assert_eq!(
            object_size(heap_object_word(addr, ValueKind::MAP)),
            map_size_for_count(3)
        );

        write_word0(7);
        assert_eq!(
            object_size_with_struct_payload(heap_object_word(addr, ValueKind::STRUCT), |schema| {
                assert_eq!(schema, 7);
                24
            }),
            struct_size_for_payload(24)
        );

        write_word0((closure_flags_pack(2, 0) as u64) << 32);
        assert_eq!(
            object_size(heap_object_word(addr, ValueKind::CLOSURE)),
            closure_size_for_count(2)
        );

        write_word0(17);
        assert_eq!(
            object_size(heap_object_word(addr, ValueKind::BITSTRING)),
            bitstring_size_for_bit_len(17)
        );
        assert_eq!(object_size(heap_object_word(addr, ValueKind::PROCBIN)), 16);
        assert_eq!(object_size(heap_object_word(addr, ValueKind::RESOURCE)), 48);
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
    fn any_value_recognizes_explicit_list_typed_pointer() {
        let addr = 0x1000 as *mut u8;
        let tv = AnyValue::heap_ptr(addr, ValueKind::LIST);

        assert_eq!(tv.kind(), ValueKind::LIST);
        assert_eq!(tv.heap_addr(), Some(addr));
        assert_eq!(tv.heap_object_word(), Some(0x1000 | TAG_LIST));
    }
}

/// Debug rendering of AnyValues. Lifted out of ir_codegen.rs by
/// fz-ul4.23.4.3 so that any execution path (JIT, future interp/AOT) can
/// use the same rendering — values are uniformly tagged, regardless of
/// what produced them. The single runtime dependency is the heap's schema
/// registry + atom-name table on a `Process`, threaded in explicitly (a
/// nullable `*mut Process`) so two schedulers can render concurrently
/// without an ambient thread-local.
pub mod debug {
    use super::{
        AnyValue, AnyValueRef, EMPTY_LIST, FALSE_ATOM_ID, ListCons, NIL_ATOM_ID, TRUE_ATOM_ID, ValueKind,
        bitstring_addr_from_tagged, closure_addr_from_tagged, closure_flags, closure_schema_id, list_addr_from_tagged,
        map_addr_from_tagged, map_count, map_entry_raw_kinds, procbin_addr_from_tagged, struct_addr_from_tagged,
        struct_schema_id,
    };
    use crate::heap::{FieldKind, Schema};
    use crate::procbin::{bitstring_bit_len, bitstring_byte_ptr};
    use crate::process::Process;
    use std::slice;
    use std::str;

    /// Render an atom id as `:name` if `proc` has a name for it; fall back
    /// to `:atom_N` otherwise. `proc` is nullable — render may be called
    /// without a process (unit tests poking the renderer directly, or the
    /// panic path) — in which case the fallback fires. Threading the process
    /// explicitly is what lets two schedulers render concurrently without an
    /// ambient `CURRENT_PROCESS`.
    fn render_atom(proc: *mut Process, id: u32) -> String {
        match id {
            NIL_ATOM_ID => return "nil".to_string(),
            TRUE_ATOM_ID => return "true".to_string(),
            FALSE_ATOM_ID => return "false".to_string(),
            _ => {}
        }
        if proc.is_null() {
            return format!(":atom_{}", id);
        }
        let proc_ref = unsafe { &*proc };
        match proc_ref.node.atom_name(id) {
            Some(name) if !name.is_empty() => format!(":{}", name),
            _ => format!(":atom_{}", id),
        }
    }

    fn is_proc_heap_list(proc: *mut Process, bits: u64) -> bool {
        let Some(p) = list_addr_from_tagged(bits) else {
            return false;
        };
        if p.is_null() {
            return false;
        }
        !proc.is_null() && unsafe { (*proc).heap.contains_heap_addr(p) }
    }

    fn is_proc_heap_map(proc: *mut Process, bits: u64) -> bool {
        let Some(p) = map_addr_from_tagged(bits) else {
            return false;
        };
        if p.is_null() {
            return false;
        }
        !proc.is_null() && unsafe { (*proc).heap.contains_heap_addr(p) }
    }

    pub fn render(proc: *mut Process, bits: u64) -> String {
        if is_proc_heap_list(proc, bits) {
            return render_list(proc, bits);
        }
        if is_proc_heap_map(proc, bits) {
            return render_map(proc, bits);
        }
        if closure_addr_from_tagged(bits).is_some() {
            return render_closure(bits);
        }
        if struct_addr_from_tagged(bits).is_some() {
            return render_struct(proc, bits);
        }
        if bitstring_addr_from_tagged(bits).is_some() {
            return render_bitstring(bits);
        }
        if procbin_addr_from_tagged(bits).is_some() {
            return render_bitstring(bits);
        }
        if bits == EMPTY_LIST {
            "[]".into()
        } else {
            format!("#ptr<{:#x}>", bits)
        }
    }

    /// Render a heap-typed Struct (currently only emitted for tuples). Reads
    /// the schema from the current Process's SchemaRegistry to determine
    /// field count. Each value field renders inline; non-value fields
    /// are elided (no callers emit them yet).
    fn render_struct(proc: *mut Process, bits: u64) -> String {
        let p = struct_addr_from_tagged(bits).expect("struct bits");
        let schema_id = unsafe { struct_schema_id(p) };
        let heap = &unsafe { &*proc }.heap;
        {
            let reg = heap.schemas_registry();
            let registry = reg.borrow();
            if registry.get(schema_id).name.as_str() == Schema::RANGE_NAME {
                return render_range(proc, bits);
            }
        }
        let field_offsets: Vec<u32> = {
            let reg = heap.schemas_registry();
            let registry = reg.borrow();
            let schema = registry.get(schema_id);
            schema
                .fields
                .iter()
                .filter(|f| matches!(f.kind, FieldKind::AnyValue))
                .map(|f| f.offset)
                .collect()
        };
        let parts: Vec<String> = field_offsets
            .into_iter()
            .map(|offset| render_value(proc, heap.read_field_slot(p, offset)))
            .collect();
        format!("{{{}}}", parts.join(", "))
    }

    fn render_range(proc: *mut Process, bits: u64) -> String {
        let range_ref = AnyValueRef::from_heap_object(
            ValueKind::STRUCT,
            struct_addr_from_tagged(bits).expect("range struct bits"),
        )
        .expect("range ref");
        let (first, last, step) = unsafe { &*proc }.heap.range_fields(range_ref).expect("range fields");
        if step == 1 {
            format!("{}..{}", first, last)
        } else {
            format!("{}..{}//{}", first, last, step)
        }
    }

    /// Render a heap Map as `%{k => v, ...}` in canonical sorted order.
    fn render_map(proc: *mut Process, bits: u64) -> String {
        let p = map_addr_from_tagged(bits).unwrap();
        let count = unsafe { map_count(p) };
        let mut parts: Vec<String> = Vec::with_capacity(count);
        for i in 0..count {
            let (kr, kk, vr, vk) = unsafe { map_entry_raw_kinds(p, i) };
            let k = AnyValue::decode_parts(kr, kk.tag()).expect("map key");
            let v = AnyValue::decode_parts(vr, vk.tag()).expect("map value");
            parts.push(format!("{} => {}", render_value(proc, k), render_value(proc, v)));
        }
        format!("%{{{}}}", parts.join(", "))
    }

    pub fn render_value(proc: *mut Process, value: AnyValue) -> String {
        match value.kind() {
            ValueKind::INT => (value.raw() as i64).to_string(),
            ValueKind::FLOAT => render_float(f64::from_bits(value.raw())),
            ValueKind::ATOM => render_atom(proc, value.raw() as u32),
            ValueKind::LIST if value.raw() == 0 => "[]".to_string(),
            kind if kind.is_heap() => render(proc, value.heap_object_word().expect("heap object")),
            ValueKind::NULL => "null".to_string(),
            _ => format!("#value<{:#x}:{}>", value.raw(), value.kind().tag()),
        }
    }

    pub fn render_float(x: f64) -> String {
        if x.is_finite() && x.fract() == 0.0 {
            format!("{:.1}", x)
        } else {
            format!("{}", x)
        }
    }

    fn render_bitstring(bits: u64) -> String {
        let p = if procbin_addr_from_tagged(bits).is_some() {
            bits as *mut u8
        } else {
            bitstring_addr_from_tagged(bits).unwrap()
        };
        let bit_len = unsafe { bitstring_bit_len(p) } as usize;
        let total_bytes = bit_len.div_ceil(8);
        let byte_ptr = unsafe { bitstring_byte_ptr(p) };
        let bytes = unsafe { slice::from_raw_parts(byte_ptr, total_bytes) };
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
            && let Ok(s) = str::from_utf8(&bytes[..full_bytes])
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
        let p = closure_addr_from_tagged(bits).unwrap();
        let schema_id = unsafe { closure_schema_id(p) };
        let flags = unsafe { closure_flags(p) };
        format!("#fn<{}/{}>", schema_id, flags)
    }

    fn render_list(proc: *mut Process, bits: u64) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut cur_bits = bits;
        let mut tail_render: Option<String> = None;
        loop {
            if cur_bits == EMPTY_LIST {
                break;
            }
            let cp = match list_addr_from_tagged(cur_bits) {
                Some(p) => p,
                None => {
                    tail_render = Some(render(proc, cur_bits));
                    break;
                }
            };
            let cons = unsafe { &*(cp as *const ListCons) };
            parts.push(render_typed_list_head(proc, cons));
            cur_bits = cons.tail_bits();
        }
        match tail_render {
            Some(t) => format!("[{} | {}]", parts.join(", "), t),
            None => format!("[{}]", parts.join(", ")),
        }
    }

    fn render_typed_list_head(proc: *mut Process, cons: &ListCons) -> String {
        match cons.head_kind() {
            ValueKind::INT => (cons.head as i64).to_string(),
            ValueKind::FLOAT => f64::from_bits(cons.head).to_string(),
            ValueKind::ATOM => render_atom(proc, cons.head as u32),
            kind if kind.is_heap() => {
                let bits = cons.head | kind.tag() as u64;
                render(proc, bits)
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
