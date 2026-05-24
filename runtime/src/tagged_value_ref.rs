//! Opaque tagged references to scalar slots and heap objects.
//!
//! This module owns the platform-specific packing format. Callers may ask for
//! a tag, clear an address through the API, or project a typed payload, but
//! they do not inspect the packed word or dereference it directly.

use std::convert::TryFrom;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum TaggedValueTag {
    Null = 0,
    Int = 1,
    Float = 2,
    Atom = 3,
    EmptyList = 4,
    List = 5,
    Map = 6,
    Struct = 7,
    Closure = 8,
    Bitstring = 9,
    ProcBin = 10,
    Resource = 11,
}

impl TaggedValueTag {
    pub const fn is_scalar(self) -> bool {
        matches!(self, Self::Int | Self::Float | Self::Atom)
    }

    pub const fn is_heap_object(self) -> bool {
        matches!(
            self,
            Self::List
                | Self::Map
                | Self::Struct
                | Self::Closure
                | Self::Bitstring
                | Self::ProcBin
                | Self::Resource
        )
    }
}

impl TryFrom<u8> for TaggedValueTag {
    type Error = TaggedValueRefError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(Self::Null),
            1 => Ok(Self::Int),
            2 => Ok(Self::Float),
            3 => Ok(Self::Atom),
            4 => Ok(Self::EmptyList),
            5 => Ok(Self::List),
            6 => Ok(Self::Map),
            7 => Ok(Self::Struct),
            8 => Ok(Self::Closure),
            9 => Ok(Self::Bitstring),
            10 => Ok(Self::ProcBin),
            11 => Ok(Self::Resource),
            _ => Err(TaggedValueRefError::UnknownTag(value)),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaggedValueRefError {
    UnknownTag(u8),
    ExpectedTag {
        expected: TaggedValueTag,
        found: TaggedValueTag,
    },
    ExpectedScalarTag(TaggedValueTag),
    ExpectedHeapObjectTag(TaggedValueTag),
    NullAddress(TaggedValueTag),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum TaggedRefArch {
    Arm64Tbi,
    X86_64Canonical57,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct TaggedRefPacking {
    tag_shift: u8,
    address_mask: u64,
}

impl TaggedRefPacking {
    pub const fn for_arch(arch: TaggedRefArch) -> Self {
        match arch {
            TaggedRefArch::Arm64Tbi => Self::new(56),
            TaggedRefArch::X86_64Canonical57 => Self::new(57),
        }
    }

    pub const fn current() -> Self {
        #[cfg(target_arch = "aarch64")]
        {
            Self::for_arch(TaggedRefArch::Arm64Tbi)
        }
        #[cfg(not(target_arch = "aarch64"))]
        {
            Self::for_arch(TaggedRefArch::X86_64Canonical57)
        }
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

    fn pack(self, tag: TaggedValueTag, address: usize) -> TaggedValueRef {
        TaggedValueRef {
            word: ((tag as u64) << self.tag_shift) | ((address as u64) & self.address_mask),
        }
    }

    pub fn tag(self, value: TaggedValueRef) -> Result<TaggedValueTag, TaggedValueRefError> {
        TaggedValueTag::try_from((value.word >> self.tag_shift) as u8)
    }

    fn address(self, value: TaggedValueRef) -> usize {
        (value.word & self.address_mask) as usize
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(transparent)]
pub struct TaggedValueRef {
    word: u64,
}

impl TaggedValueRef {
    pub fn from_raw_word(word: u64) -> Result<Self, TaggedValueRefError> {
        let value = Self { word };
        TaggedRefPacking::current().tag(value)?;
        Ok(value)
    }

    pub const fn raw_word(self) -> u64 {
        self.word
    }

    pub fn null() -> Self {
        TaggedRefPacking::current().pack(TaggedValueTag::Null, 0)
    }

    pub fn empty_list() -> Self {
        TaggedRefPacking::current().pack(TaggedValueTag::EmptyList, 0)
    }

    pub fn from_scalar_slot(
        tag: TaggedValueTag,
        slot: *const u64,
    ) -> Result<Self, TaggedValueRefError> {
        if !tag.is_scalar() {
            return Err(TaggedValueRefError::ExpectedScalarTag(tag));
        }
        if slot.is_null() {
            return Err(TaggedValueRefError::NullAddress(tag));
        }
        Ok(TaggedRefPacking::current().pack(tag, slot as usize))
    }

    pub fn from_heap_object(
        tag: TaggedValueTag,
        addr: *const u8,
    ) -> Result<Self, TaggedValueRefError> {
        if !tag.is_heap_object() {
            return Err(TaggedValueRefError::ExpectedHeapObjectTag(tag));
        }
        if addr.is_null() {
            return Err(TaggedValueRefError::NullAddress(tag));
        }
        Ok(TaggedRefPacking::current().pack(tag, addr as usize))
    }

    pub fn tag(self) -> TaggedValueTag {
        TaggedRefPacking::current()
            .tag(self)
            .expect("TaggedValueRef contains a valid tag")
    }

    fn cleared_addr(self) -> *mut u8 {
        TaggedRefPacking::current().address(self) as *mut u8
    }

    pub fn is_heap_root(self) -> bool {
        self.tag().is_heap_object()
    }

    pub fn load_int(self) -> Result<i64, TaggedValueRefError> {
        self.expect_tag(TaggedValueTag::Int)?;
        Ok(unsafe { std::ptr::read(self.cleared_addr() as *const i64) })
    }

    pub fn load_float(self) -> Result<f64, TaggedValueRefError> {
        self.expect_tag(TaggedValueTag::Float)?;
        Ok(f64::from_bits(unsafe {
            std::ptr::read(self.cleared_addr() as *const u64)
        }))
    }

    pub fn load_atom(self) -> Result<u64, TaggedValueRefError> {
        self.expect_tag(TaggedValueTag::Atom)?;
        Ok(unsafe { std::ptr::read(self.cleared_addr() as *const u64) })
    }

    pub fn heap_addr(self, expected: TaggedValueTag) -> Result<*mut u8, TaggedValueRefError> {
        if !expected.is_heap_object() {
            return Err(TaggedValueRefError::ExpectedHeapObjectTag(expected));
        }
        self.expect_tag(expected)?;
        Ok(self.cleared_addr())
    }

    pub fn list_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::List)
    }

    pub fn map_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::Map)
    }

    pub fn struct_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::Struct)
    }

    pub fn closure_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::Closure)
    }

    pub fn bitstring_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::Bitstring)
    }

    pub fn procbin_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::ProcBin)
    }

    pub fn resource_addr(self) -> Result<*mut u8, TaggedValueRefError> {
        self.heap_addr(TaggedValueTag::Resource)
    }

    fn expect_tag(self, expected: TaggedValueTag) -> Result<(), TaggedValueRefError> {
        let found = self.tag();
        if found == expected {
            Ok(())
        } else {
            Err(TaggedValueRefError::ExpectedTag { expected, found })
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::{ValueKind, ValueSlot, tagged_bitstring_bits, tagged_closure_bits};
    use crate::heap::{Heap, Schema, SchemaRegistry};
    use crate::resource::{ResourceHandle, alloc_resource, fz_resource_destructor_noop};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn packing_strategy_uses_platform_specific_tag_shift() {
        assert_eq!(
            TaggedRefPacking::for_arch(TaggedRefArch::Arm64Tbi).tag_shift(),
            56
        );
        assert_eq!(
            TaggedRefPacking::for_arch(TaggedRefArch::X86_64Canonical57).tag_shift(),
            57
        );
        assert_eq!(
            TaggedRefPacking::for_arch(TaggedRefArch::Arm64Tbi).address_mask(),
            (1u64 << 56) - 1
        );
        assert_eq!(
            TaggedRefPacking::for_arch(TaggedRefArch::X86_64Canonical57).address_mask(),
            (1u64 << 57) - 1
        );
    }

    #[test]
    fn packing_extracts_same_semantic_tag_on_supported_arches() {
        let address = 0x1234_5678usize;
        for packing in [
            TaggedRefPacking::for_arch(TaggedRefArch::Arm64Tbi),
            TaggedRefPacking::for_arch(TaggedRefArch::X86_64Canonical57),
        ] {
            let value = packing.pack(TaggedValueTag::Map, address);
            assert_eq!(packing.tag(value), Ok(TaggedValueTag::Map));
            assert_eq!(packing.address(value), address);
        }
    }

    #[test]
    fn x86_packing_preserves_wide_canonical_user_addresses() {
        let packing = TaggedRefPacking::for_arch(TaggedRefArch::X86_64Canonical57);
        let address = 0x00ab_cdef_1234_5000usize;
        let value = packing.pack(TaggedValueTag::Int, address);

        assert_eq!(packing.tag(value), Ok(TaggedValueTag::Int));
        assert_eq!(packing.address(value), address);
    }

    #[test]
    fn scalar_refs_load_full_width_payloads() {
        let int_slot = (-42i64) as u64;
        let float_slot = 3.5f64.to_bits();
        let atom_slot = 99u64;

        let int_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &int_slot).expect("int ref");
        let float_ref = TaggedValueRef::from_scalar_slot(TaggedValueTag::Float, &float_slot)
            .expect("float ref");
        let atom_ref =
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_slot).expect("atom ref");

        assert_eq!(int_ref.load_int(), Ok(-42));
        assert_eq!(float_ref.load_float(), Ok(3.5));
        assert_eq!(atom_ref.load_atom(), Ok(99));
        assert!(!int_ref.is_heap_root());
    }

    #[test]
    fn bad_scalar_projection_reports_expected_and_found_tags() {
        let slot = 7u64;
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &slot).expect("int ref");

        assert_eq!(
            value.load_float(),
            Err(TaggedValueRefError::ExpectedTag {
                expected: TaggedValueTag::Float,
                found: TaggedValueTag::Int
            })
        );
        assert_eq!(
            TaggedValueRef::from_scalar_slot(TaggedValueTag::Map, &slot),
            Err(TaggedValueRefError::ExpectedScalarTag(TaggedValueTag::Map))
        );
    }

    #[test]
    fn heap_object_refs_clear_addresses_before_projection() {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut heap = Heap::new(4096, schemas.clone());
        let schema_id = heap.register_schema(Schema::tuple_of_arity(1));

        let list_bits =
            heap.alloc_list_cons_slot(ValueSlot::int(1), crate::fz_value::EMPTY_LIST_BITS);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("list addr");
        let map_bits = heap.alloc_map_slots(&[(ValueSlot::atom(3), ValueSlot::int(4))]);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("map addr");
        let struct_addr = heap.alloc_struct(schema_id);
        let bitstring_addr = heap.alloc_bitstring(&[0xAA], 8);
        let closure_bits = heap.alloc_closure(schema_id, 0, 0, 0xfeed, &[]);
        let closure_addr =
            crate::fz_value::closure_addr_from_tagged(closure_bits).expect("closure addr");
        let procbin_addr = heap.alloc_bitstring(&[0u8; 65], 65 * 8);
        let resource_addr = alloc_resource(
            &mut heap,
            ResourceHandle::new(77, ValueKind::INT.tag(), fz_resource_destructor_noop),
            ValueSlot::nil_atom(),
        )
        .as_raw();

        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
                .expect("list ref")
                .list_addr(),
            Ok(list_addr)
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr)
                .expect("map ref")
                .map_addr(),
            Ok(map_addr)
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::Struct, struct_addr)
                .expect("struct ref")
                .struct_addr(),
            Ok(struct_addr)
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
                .expect("closure ref")
                .closure_addr(),
            Ok(closure_addr)
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::Bitstring, bitstring_addr)
                .expect("bitstring ref")
                .bitstring_addr(),
            Ok(bitstring_addr)
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::ProcBin, procbin_addr)
                .expect("procbin ref")
                .procbin_addr(),
            Ok(procbin_addr)
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::Resource, resource_addr)
                .expect("resource ref")
                .resource_addr(),
            Ok(resource_addr)
        );

        let packed = TaggedValueRef::from_heap_object(TaggedValueTag::Bitstring, bitstring_addr)
            .expect("bitstring ref");
        assert_eq!(
            tagged_bitstring_bits(packed.bitstring_addr().expect("bitstring addr")),
            tagged_bitstring_bits(bitstring_addr)
        );
        let packed = TaggedValueRef::from_heap_object(TaggedValueTag::Closure, closure_addr)
            .expect("closure ref");
        assert_eq!(
            tagged_closure_bits(packed.closure_addr().expect("closure addr")),
            tagged_closure_bits(closure_addr)
        );
    }

    #[test]
    fn bad_heap_projection_reports_expected_and_found_tags() {
        let mut bytes = [0u8; 16];
        let map_ref = TaggedValueRef::from_heap_object(TaggedValueTag::Map, bytes.as_mut_ptr())
            .expect("map ref");

        assert!(map_ref.is_heap_root());
        assert_eq!(
            map_ref.list_addr(),
            Err(TaggedValueRefError::ExpectedTag {
                expected: TaggedValueTag::List,
                found: TaggedValueTag::Map
            })
        );
        assert_eq!(
            TaggedValueRef::from_heap_object(TaggedValueTag::Int, bytes.as_mut_ptr()),
            Err(TaggedValueRefError::ExpectedHeapObjectTag(
                TaggedValueTag::Int
            ))
        );
    }
}
