//! impl Heap — the giant impl block + Drop.

use super::block_pool::{SIZE_TABLE, pick_size_class, pool_alloc, pool_free};
use super::fragment::{CopiedObject, FRAGMENT_THRESHOLD, Fragment, classify_fragment};
use super::gc::{
    cheney_forward_strict_bits, cheney_trace_closure, cheney_trace_list, cheney_trace_map,
    cheney_trace_resource, cheney_trace_struct, forward_tagged_ref_root,
};
use super::key_cmp::{map_key_cmp_any, map_key_cmp_refs, same_any_value, same_value_ref};
use super::ref_io::{
    any_value_from_ref, list_tail_bits_from_ref, map_entry_refs, reject_scalar_ref_write,
    tagged_ref_from_storage, watermark_for, write_any_value_to_storage, write_ref_to_storage,
};
use super::schema::{Schema, SchemaRegistry};
use super::stats::GcStats;
use super::{Heap, SHARED_BIN_THRESHOLD_BYTES};
use crate::fz_value::{AnyValue, ListCons, ValueKind};
use crate::procbin::{SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep};
use crate::tagged_value_ref::{TaggedValueRef, TaggedValueRefError, TaggedValueTag};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::rc::Rc;

impl Heap {
    pub fn new(capacity: usize, schemas: Rc<RefCell<SchemaRegistry>>) -> Self {
        assert!(
            capacity > 0 && capacity.is_multiple_of(16),
            "capacity must be 16-aligned"
        );
        let size_class = pick_size_class(capacity);
        let block_size = SIZE_TABLE[size_class as usize];
        let block_start = pool_alloc(size_class);
        let block_end = unsafe { block_start.add(block_size) };
        Self {
            block_start,
            bump_top: block_start,
            block_end,
            block_size,
            size_class,
            gc_watermark: watermark_for(block_start, block_size),
            last_gc_live_bytes: 0,
            last_gc_stats: GcStats::default(),
            abandoned_blocks: Vec::new(),
            schemas,
            pressure: std::sync::atomic::AtomicBool::new(false),
            // Default: half the block. Tunable per-Process for tests that
            // want to force the park-time GC hook to fire.
            gc_threshold_bytes: block_size / 2,
            gc_run_count: 0,
            alloc_count: 0,
            mso_head: 0,
            pending_dtors: std::collections::VecDeque::new(),
            fragments: Vec::new(),
        }
    }

    pub fn should_gc(&self) -> bool {
        self.pressure.load(std::sync::atomic::Ordering::Relaxed)
    }

    pub fn clear_should_gc_flag(&self) {
        self.pressure
            .store(false, std::sync::atomic::Ordering::Relaxed);
    }

    fn note_alloc_pressure(&self) {
        if self.bytes_used() >= self.gc_threshold_bytes {
            self.pressure
                .store(true, std::sync::atomic::Ordering::Relaxed);
        }
    }

    /// Bump-only allocator. Rounds `size` up to 16 and advances `bump_top`.
    /// On overflow, abandons the current block and allocates a fresh
    /// pool-backed block at the next size_class. The next park-time
    /// Cheney recycles the whole abandoned chain.
    ///
    /// fz-q8d.4 — objects larger than `FRAGMENT_THRESHOLD` (the last
    /// `SIZE_TABLE` entry, ~6 MiB) are allocated as system-allocator
    /// backed singletons attached to `self.fragments`. They don't move
    /// during Cheney; the collector marks them in place and frees
    /// survivors / unmarked fragments at sweep time.
    pub fn alloc(&mut self, size: usize) -> *mut u8 {
        let size = (size + 15) & !15;
        assert!(
            size >= 16,
            "alloc must reserve at least one 16-byte object slot"
        );
        // Oversize allocations route through the fragment path.
        if size > FRAGMENT_THRESHOLD {
            let layout = Layout::from_size_align(size, 16).expect("fragment layout");
            let ptr = unsafe { alloc_zeroed(layout) };
            assert!(!ptr.is_null(), "fragment allocation failed");
            self.fragments.push(Fragment {
                ptr,
                size,
                layout,
                mark: false,
            });
            self.alloc_count += 1;
            self.note_alloc_pressure();
            return ptr;
        }
        let new_top = unsafe { self.bump_top.add(size) };
        if new_top > self.block_end {
            // Grow: pick the smallest size_class > current that also fits
            // `size`. Allocate via the pool; abandon the current block
            // for Cheney/Drop to return.
            let want_for_alloc = pick_size_class(size);
            let bumped = self
                .size_class
                .saturating_add(1)
                .min((SIZE_TABLE.len() - 1) as u8);
            let new_class = want_for_alloc.max(bumped);
            let new_size = SIZE_TABLE[new_class as usize];
            self.abandoned_blocks
                .push((self.block_start, self.size_class));
            let new_block = pool_alloc(new_class);
            self.block_start = new_block;
            self.bump_top = new_block;
            self.block_end = unsafe { new_block.add(new_size) };
            self.block_size = new_size;
            self.size_class = new_class;
            self.gc_watermark = watermark_for(new_block, new_size);
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        self.note_alloc_pressure();
        if self.bump_top >= self.gc_watermark {
            crate::yield_flag::request();
        }
        p
    }

    pub fn alloc_struct(&mut self, schema_id: u32) -> *mut u8 {
        let payload_size = self
            .schemas
            .borrow()
            .get(schema_id)
            .allocation_payload_size();
        let total = crate::fz_value::struct_size_for_payload(payload_size);
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u32, schema_id);
            std::ptr::write(p.add(4) as *mut u32, 0);
            // Zero payload.
            std::ptr::write_bytes(p.add(8), 0, total - 8);
        }
        p
    }

    pub(crate) fn closure_schema_id(&mut self, captured_count: usize) -> u32 {
        self.schemas.borrow_mut().closure_env(captured_count)
    }

    fn alloc_list_cons_value(&mut self, head: TaggedValueRef, tail_bits: u64) -> u64 {
        let p = self.alloc(16);
        unsafe {
            let cons = &mut *(p as *mut ListCons);
            write_ref_to_storage(&mut cons.head, None, head);
            cons.link = crate::fz_value::list_tail_addr_from_bits(tail_bits)
                | crate::fz_value::value_kind_from_ref_tag(head.tag())
                    .expect("list head kind")
                    .tag() as u64;
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::LIST)
    }

    pub fn alloc_list_cons_slot(&mut self, head: AnyValue, tail_bits: u64) -> u64 {
        let p = self.alloc(16);
        unsafe {
            let cons = &mut *(p as *mut ListCons);
            write_any_value_to_storage(&mut cons.head, None, head);
            cons.link =
                crate::fz_value::list_tail_addr_from_bits(tail_bits) | head.kind().tag() as u64;
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::LIST)
    }

    pub fn box_any_value_ref(&mut self, value: AnyValue) -> TaggedValueRef {
        match value {
            AnyValue::Null => TaggedValueRef::null(),
            AnyValue::EmptyList => TaggedValueRef::empty_list(),
            AnyValue::HeapRef(value) => value,
            AnyValue::Int(value) => {
                let slot = self.alloc(std::mem::size_of::<u64>()) as *mut u64;
                unsafe {
                    std::ptr::write(slot, value as u64);
                }
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, slot as *const u64)
                    .expect("int ref")
            }
            AnyValue::Float(bits) => {
                let slot = self.alloc(std::mem::size_of::<u64>()) as *mut u64;
                unsafe {
                    std::ptr::write(slot, bits);
                }
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Float, slot as *const u64)
                    .expect("float ref")
            }
            AnyValue::Atom(atom_id) => {
                let slot = self.alloc(std::mem::size_of::<u64>()) as *mut u64;
                unsafe {
                    std::ptr::write(slot, atom_id as u64);
                }
                TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, slot as *const u64)
                    .expect("atom ref")
            }
        }
    }

    pub fn alloc_list_cons_ref(
        &mut self,
        head: TaggedValueRef,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        reject_scalar_ref_write("alloc_list_cons_ref head", head);
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_value(head, tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn alloc_list_cons_int(
        &mut self,
        head: i64,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::int(head), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn alloc_list_cons_float(
        &mut self,
        head: f64,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::float(head), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn alloc_list_cons_atom(
        &mut self,
        atom_id: u32,
        tail: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::atom(atom_id), tail_bits);
        let list_addr = crate::fz_value::list_addr_from_tagged(list_bits).expect("new list addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::List, list_addr)
    }

    pub fn current_heap_tagged_addr(&self, bits: u64) -> Option<(ValueKind, *mut u8)> {
        let kind = crate::fz_value::heap_kind_from_tagged(bits)?;
        let p = (bits & !crate::fz_value::TAG_MASK) as *mut u8;
        (!p.is_null() && self.contains_heap_addr(p)).then_some((kind, p))
    }

    pub fn current_heap_addr_for_kind(&self, bits: u64, kind: ValueKind) -> Option<*mut u8> {
        self.current_heap_tagged_addr(bits)
            .and_then(|(actual, p)| (actual == kind).then_some(p))
    }

    pub fn contains_heap_addr(&self, p: *mut u8) -> bool {
        (p >= self.block_start && p < self.block_end)
            || self
                .abandoned_blocks
                .iter()
                .any(|&(start, sc)| p >= start && p < unsafe { start.add(SIZE_TABLE[sc as usize]) })
            || classify_fragment(p, &self.fragments).is_some()
    }

    /// Map layout: count, padded tag bytes, raw keys, raw values. Caller
    /// supplies canonically-sorted typed entries; this performs the heap copy.
    pub fn alloc_map_refs_bits(&mut self, entries: &[(TaggedValueRef, TaggedValueRef)]) -> u64 {
        let total = crate::fz_value::map_size_for_count(entries.len());
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, entries.len() as u64);
            let tag_p = crate::fz_value::map_tag_ptr(p);
            std::ptr::write_bytes(tag_p, 0, crate::fz_value::map_tag_bytes_len(entries.len()));
            let keys = crate::fz_value::map_keys_ptr(p, entries.len());
            let values = crate::fz_value::map_values_ptr(p, entries.len());
            for (i, (key, value)) in entries.iter().copied().enumerate() {
                let key_kind =
                    crate::fz_value::value_kind_from_ref_tag(key.tag()).expect("key kind");
                let value_kind =
                    crate::fz_value::value_kind_from_ref_tag(value.tag()).expect("value kind");
                std::ptr::write(
                    tag_p.add(i),
                    crate::fz_value::map_pack_tag(key_kind, value_kind),
                );
                write_ref_to_storage(keys.add(i), None, key);
                write_ref_to_storage(values.add(i), None, value);
            }
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::MAP)
    }

    pub fn alloc_map_slots(&mut self, entries: &[(AnyValue, AnyValue)]) -> u64 {
        let total = crate::fz_value::map_size_for_count(entries.len());
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u64, entries.len() as u64);
            let tag_p = crate::fz_value::map_tag_ptr(p);
            std::ptr::write_bytes(tag_p, 0, crate::fz_value::map_tag_bytes_len(entries.len()));
            let keys = crate::fz_value::map_keys_ptr(p, entries.len());
            let values = crate::fz_value::map_values_ptr(p, entries.len());
            for (i, (key, value)) in entries.iter().copied().enumerate() {
                std::ptr::write(
                    tag_p.add(i),
                    crate::fz_value::map_pack_tag(key.kind(), value.kind()),
                );
                write_any_value_to_storage(keys.add(i), None, key);
                write_any_value_to_storage(values.add(i), None, value);
            }
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::MAP)
    }

    pub fn alloc_map_refs(
        &mut self,
        entries: &[(TaggedValueRef, TaggedValueRef)],
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let map_bits = self.alloc_map_refs_bits(entries);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("new map addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr)
    }

    pub fn map_put_ref(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        reject_scalar_ref_write("map_put_ref value", value);
        self.map_put_value(map, key, value)
    }

    pub fn map_put_int(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: i64,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let value = value as u64;
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Int, &value)?;
        self.map_put_value(map, key, value)
    }

    pub fn map_put_float(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: f64,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let value = value.to_bits();
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Float, &value)?;
        self.map_put_value(map, key, value)
    }

    pub fn map_put_atom(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        atom_id: u32,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let atom_id = atom_id as u64;
        let value = TaggedValueRef::from_scalar_slot(TaggedValueTag::Atom, &atom_id)?;
        self.map_put_value(map, key, value)
    }

    fn map_put_value(
        &mut self,
        map: TaggedValueRef,
        key: TaggedValueRef,
        value: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let map_addr = map.map_addr()?;
        let map_bits = self.map_put_value_bits(map_addr, key, value);
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits).expect("new map addr");
        TaggedValueRef::from_heap_object(TaggedValueTag::Map, map_addr)
    }

    fn map_put_value_bits(
        &mut self,
        map_addr: *mut u8,
        key: TaggedValueRef,
        value: TaggedValueRef,
    ) -> u64 {
        let count = unsafe { crate::fz_value::map_count(map_addr) };
        let mut entries = Vec::with_capacity(count + 1);
        let mut replaced = false;

        for i in 0..count {
            let (entry_key, entry_value) = unsafe { map_entry_refs(map_addr, i) };
            if !replaced && same_value_ref(entry_key, key) {
                entries.push((key, value));
                replaced = true;
            } else {
                entries.push((entry_key, entry_value));
            }
        }
        if !replaced {
            entries.push((key, value));
        }

        entries.sort_by(|a, b| map_key_cmp_refs(a.0, b.0));
        self.alloc_map_refs_bits(&entries)
    }

    pub fn map_put_slot_bits(&mut self, map_bits: u64, key: AnyValue, value: AnyValue) -> u64 {
        let map_addr = crate::fz_value::map_addr_from_tagged(map_bits);
        let count = map_addr.map_or(0, |addr| unsafe { crate::fz_value::map_count(addr) });
        let mut entries = Vec::with_capacity(count + 1);
        let mut replaced = false;
        if let Some(map_addr) = map_addr {
            for i in 0..count {
                let (entry_key, entry_value) = unsafe { crate::fz_value::map_entry(map_addr, i) };
                if !replaced && same_any_value(entry_key, key) {
                    entries.push((key, value));
                    replaced = true;
                } else {
                    entries.push((entry_key, entry_value));
                }
            }
        }
        if !replaced {
            entries.push((key, value));
        }
        entries.sort_by(|a, b| map_key_cmp_any(a.0, b.0));
        self.alloc_map_slots(&entries)
    }

    /// Strict inline Bitstring layout: bit_len: u64 + bytes (padded to 16).
    /// Caller supplies a fully-built byte buffer + bit_len; this performs the
    /// heap copy.
    ///
    /// fz-cty.5 — payloads larger than `SHARED_BIN_THRESHOLD_BYTES` route
    /// through the shared zone: a SharedBin is allocated off-heap and the
    /// per-process heap gets a 16-byte tagged ProcBin stub referencing
    /// it. Render and bit-match dispatch via
    /// `bitstring_bit_len` / `bitstring_byte_ptr`.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> *mut u8 {
        if bytes.len() > SHARED_BIN_THRESHOLD_BYTES {
            let handle = SharedBinHandle::from_bytes(bytes, bit_len);
            return alloc_procbin(self, handle).as_raw();
        }
        // fz-wu9 — reserve at least 1 byte past the payload for the
        // invisible trailing NUL. The pad-zeroing below guarantees it reads
        // as 0; bytes_len / bit_len are unchanged.
        let total = crate::fz_value::bitstring_size_for_bit_len(bit_len);
        let p = self.alloc(total);
        unsafe {
            let bit_len_p = p as *mut u64;
            std::ptr::write(bit_len_p, bit_len);
            let bytes_p = p.add(8);
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), bytes_p, bytes.len());
            // Zero the trailing padding so renders / debug aren't garbage.
            let pad_start = 8 + bytes.len();
            if pad_start < total {
                std::ptr::write_bytes(p.add(pad_start), 0, total - pad_start);
            }
        }
        p
    }

    /// Closure layout: `schema_id`, `flags`, raw code pointer, then
    /// schema-backed capture fields.
    pub fn alloc_closure_slots(
        &mut self,
        _target_id: u32,
        captured_count: usize,
        halt_kind: u16,
    ) -> u64 {
        assert!(
            captured_count <= crate::fz_value::CLOSURE_FLAGS_CAPTURED_MASK as usize,
            "closure captured count overflow"
        );
        let schema_id = self.closure_schema_id(captured_count);
        let total = crate::fz_value::closure_size_for_count(captured_count);
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(p as *mut u32, schema_id);
            std::ptr::write(
                p.add(4) as *mut u32,
                crate::fz_value::closure_flags_pack(captured_count as u16, halt_kind) as u32,
            );
            std::ptr::write(p.add(8) as *mut u64, 0);
            if total > 16 {
                std::ptr::write_bytes(p.add(16), 0, total - 16);
            }
        }
        crate::fz_value::heap_object_word(p, crate::fz_value::ValueKind::CLOSURE)
    }

    pub fn alloc_closure(
        &mut self,
        schema_id: u32,
        captured_count: usize,
        halt_kind: u16,
        fn_ptr: u64,
        captures: &[AnyValue],
    ) -> u64 {
        assert!(
            captures.len() <= captured_count,
            "too many closure captures"
        );
        let bits = self.alloc_closure_slots(schema_id, captured_count, halt_kind);
        let p = crate::fz_value::closure_addr_from_tagged(bits).expect("new closure ptr");
        unsafe {
            std::ptr::write(p.add(8) as *mut u64, fn_ptr);
            for (i, capture) in captures.iter().enumerate() {
                crate::fz_value::closure_capture_set(p, i, *capture);
            }
        }
        bits
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn write_closure_capture_value(
        &mut self,
        closure_addr: *mut u8,
        idx: usize,
        value: AnyValue,
    ) {
        unsafe { crate::fz_value::closure_capture_set(closure_addr, idx, value) };
    }

    pub fn write_closure_capture_ref(
        &mut self,
        closure: TaggedValueRef,
        idx: usize,
        value: TaggedValueRef,
    ) -> Result<(), TaggedValueRefError> {
        let closure = closure.closure_addr()?;
        unsafe { crate::fz_value::closure_capture_set(closure, idx, any_value_from_ref(value)?) };
        Ok(())
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn read_closure_capture_value(
        &self,
        closure_addr: *const u8,
        idx: usize,
    ) -> AnyValue {
        unsafe { crate::fz_value::closure_capture_value(closure_addr, idx) }
    }

    /// Write a canonical value into a Struct's generic payload slot.
    pub fn write_field_slot(&mut self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        self.write_struct_field_value(obj, field_offset, value);
    }

    pub fn write_struct_field_ref(
        &mut self,
        obj: TaggedValueRef,
        field_offset: u32,
        value: TaggedValueRef,
    ) -> Result<(), TaggedValueRefError> {
        let obj = obj.struct_addr()?;
        self.write_struct_field_value(obj, field_offset, any_value_from_ref(value)?);
        Ok(())
    }

    fn write_struct_field_value(&self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        let schema_id = unsafe { crate::fz_value::struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw = value.raw();
        unsafe {
            std::ptr::write(
                crate::fz_value::struct_field_raw_slot(obj as *const u8, field_offset),
                raw,
            );
            std::ptr::write(
                crate::fz_value::struct_field_kind_slot(obj as *const u8, kind_offset),
                value.kind().tag(),
            );
        }
    }

    /// Read a canonical value from a Struct's generic payload slot.
    pub fn read_field_slot(&self, obj: *mut u8, field_offset: u32) -> AnyValue {
        let schema_id = unsafe { crate::fz_value::struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        unsafe {
            let raw = std::ptr::read(crate::fz_value::struct_field_raw_slot(
                obj as *const u8,
                field_offset,
            ));
            let kind = std::ptr::read(crate::fz_value::struct_field_kind_slot(
                obj as *const u8,
                kind_offset,
            ));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        }
    }

    pub fn read_list_head_ref(
        &self,
        list: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = list.list_addr()?;
        let cons = unsafe { &*(addr as *const ListCons) };
        tagged_ref_from_storage(&cons.head as *const u64, cons.head_kind())
    }

    pub fn read_list_tail_ref(
        &self,
        list: TaggedValueRef,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = list.list_addr()?;
        let cons = unsafe { &*(addr as *const ListCons) };
        let tail_addr = cons.tail_addr();
        if tail_addr == 0 {
            Ok(TaggedValueRef::empty_list())
        } else {
            TaggedValueRef::from_heap_object(TaggedValueTag::List, tail_addr as *const u8)
        }
    }

    pub fn read_map_value_ref(
        &self,
        map: TaggedValueRef,
        key: TaggedValueRef,
    ) -> Result<Option<TaggedValueRef>, TaggedValueRefError> {
        let addr = map.map_addr()?;
        self.read_map_addr_value_ref(addr, key)
    }

    fn read_map_addr_value_ref(
        &self,
        addr: *mut u8,
        key: TaggedValueRef,
    ) -> Result<Option<TaggedValueRef>, TaggedValueRefError> {
        let count = unsafe { crate::fz_value::map_count(addr) };

        for i in 0..count {
            let (entry_key, entry_value) = unsafe { map_entry_refs(addr, i) };
            if !same_value_ref(entry_key, key) {
                continue;
            }
            return Ok(Some(entry_value));
        }
        Ok(None)
    }

    pub fn read_map_value_for_any_key(
        &self,
        map: TaggedValueRef,
        key: AnyValue,
    ) -> Result<Option<TaggedValueRef>, TaggedValueRefError> {
        let addr = map.map_addr()?;
        let count = unsafe { crate::fz_value::map_count(addr) };
        for i in 0..count {
            let (entry_key, _) = unsafe { crate::fz_value::map_entry(addr, i) };
            if !same_any_value(entry_key, key) {
                continue;
            }
            let (_, entry_value) = unsafe { map_entry_refs(addr, i) };
            return Ok(Some(entry_value));
        }
        Ok(None)
    }

    pub fn read_struct_field_ref(
        &self,
        obj: TaggedValueRef,
        field_offset: u32,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = obj.struct_addr()?;
        let schema_id = unsafe { crate::fz_value::struct_schema_id(addr as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw_slot =
            unsafe { crate::fz_value::struct_field_raw_slot(addr as *const u8, field_offset) };
        let kind = unsafe {
            std::ptr::read(crate::fz_value::struct_field_kind_slot(
                addr as *const u8,
                kind_offset,
            ))
        };
        tagged_ref_from_storage(
            raw_slot as *const u64,
            ValueKind::new(kind).expect("struct field kind"),
        )
    }

    pub fn read_closure_capture_ref(
        &self,
        closure: TaggedValueRef,
        idx: usize,
    ) -> Result<TaggedValueRef, TaggedValueRefError> {
        let addr = closure.closure_addr()?;
        let raw_slot = unsafe { crate::fz_value::closure_capture_raw_slot(addr as *const u8, idx) };
        let kind_slot =
            unsafe { crate::fz_value::closure_capture_kind_slot(addr as *const u8, idx) };
        let kind = unsafe { std::ptr::read(kind_slot) };
        tagged_ref_from_storage(
            raw_slot as *const u64,
            ValueKind::new(kind).expect("closure capture kind"),
        )
    }

    /// Register a schema in this heap's registry, returning its id. Codegen
    /// uses this to register tuple-arity / closure / record schemas at JIT
    /// compile time so the tracer can walk their typed fields.
    pub fn register_schema(&self, schema: Schema) -> u32 {
        self.schemas.borrow_mut().register(schema)
    }

    /// Borrow the SchemaRegistry handle. Used by render paths that need to
    /// know a struct's arity / field layout from its schema_id.
    pub fn schemas_registry(&self) -> Rc<RefCell<SchemaRegistry>> {
        self.schemas.clone()
    }

    /// Total allocations made on this heap (since last GC). Under the
    /// fz-siu.7 stub GC, all allocations remain "live" because nothing is
    /// reclaimed. .8's Cheney pass resets this to the surviving-object
    /// count after each copy.
    pub fn live_count(&self) -> usize {
        self.alloc_count as usize
    }

    /// Always zero under bump-only. Retained for tests asserting freelist
    /// invariants; .8 / .9 may remove entirely.
    pub fn freelist_len(&self) -> usize {
        0
    }

    /// Bytes consumed across the current block + every abandoned block.
    /// Tracks total memory footprint, not "logically live" data.
    pub fn bytes_used(&self) -> usize {
        let current = unsafe { self.bump_top.offset_from(self.block_start) } as usize;
        let abandoned: usize = self
            .abandoned_blocks
            .iter()
            .map(|(_, sc)| SIZE_TABLE[*sc as usize])
            .sum();
        // fz-q8d.4 — include fragment sizes so allocation pressure
        // accounting reflects the full per-heap footprint.
        let fragments: usize = self.fragments.iter().map(|f| f.size).sum();
        current + abandoned + fragments
    }

    /// Park-time Cheney GC (§6.4). The caller passes a primary closure root
    /// by mutable pointer; on return it is updated to the to-space copy (or
    /// left null on entry — nothing to trace, just recycle blocks).
    ///
    /// Algorithm: standard Cheney two-finger BFS. Allocate a to-space block
    /// at the chosen size_class (§6.3 / §6.5 picker), copy the root, then
    /// scan to-space objects breadth-first, forwarding each from-space
    /// child pointer to its newly-copied address. Off-heap pointers
    /// (static-closure / halt-cont singletons) are detected by an
    /// in-from-space range check and left untouched.
    pub fn gc(&mut self, root_slot: &mut *mut u8) -> GcStats {
        self.gc_with_extra_root_slots(root_slot, &mut [])
    }

    /// Cheney GC with an optional slice of extra typed roots. Each element is
    /// forwarded in-place.
    pub fn gc_with_extra_root_slots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, extra_roots, &mut [])
    }

    pub fn gc_with_tagged_ref_roots(
        &mut self,
        root_slot: &mut *mut u8,
        ref_roots: &mut [TaggedValueRef],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, &mut [], ref_roots)
    }

    pub fn gc_with_value_and_tagged_ref_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
        ref_roots: &mut [TaggedValueRef],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, extra_roots, ref_roots)
    }

    fn gc_with_extra_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
        ref_roots: &mut [TaggedValueRef],
    ) -> GcStats {
        // Snapshot from-space block ranges before we allocate to-space.
        let mut from_ranges: Vec<(*mut u8, *mut u8)> =
            Vec::with_capacity(1 + self.abandoned_blocks.len());
        from_ranges.push((self.block_start, self.block_end));
        for &(p, sc) in &self.abandoned_blocks {
            from_ranges.push((p, unsafe { p.add(SIZE_TABLE[sc as usize]) }));
        }
        let from_space_capacity_bytes: usize = from_ranges
            .iter()
            .map(|(start, end)| unsafe { end.offset_from(*start) as usize })
            .sum();

        // fz-q8d.4 — reset fragment marks at the start of each GC.
        for f in &mut self.fragments {
            f.mark = false;
        }

        // Pick to-space size: first GC uses bytes_used() as upper bound;
        // subsequent GCs use last_gc_live_bytes * 2 (50% post-GC target).
        // Fragment bytes are excluded from the bump-arena sizing because
        // fragments don't get copied into to-space.
        let bump_live_for_sizing = if self.last_gc_live_bytes > 0 {
            self.last_gc_live_bytes.saturating_mul(2)
        } else {
            self.bytes_used()
                .saturating_sub(self.fragments.iter().map(|f| f.size).sum())
        };
        let size_class = pick_size_class(bump_live_for_sizing.max(SIZE_TABLE[0]));
        let to_size = SIZE_TABLE[size_class as usize];
        let to_start = pool_alloc(size_class);
        let to_end = unsafe { to_start.add(to_size) };
        let mut free = to_start;
        let mut frag_queue: Vec<CopiedObject> = Vec::new();
        let mut copied_objects: Vec<CopiedObject> = Vec::new();
        let mut stats = GcStats {
            from_space_capacity_bytes: from_space_capacity_bytes as u64,
            to_space_capacity_bytes: to_size as u64,
            size_class,
            ..GcStats::default()
        };

        if !root_slot.is_null() {
            stats.root_heap_edges += 1;
            let root_bits = *root_slot as u64;
            if let Some(new_root) = cheney_forward_strict_bits(
                root_bits,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
                &mut stats,
            ) {
                *root_slot = new_root as *mut u8;
            }
        }

        // Forward extra roots (mid-flight args, mailbox items).
        for value in extra_roots.iter_mut() {
            if !value.kind().is_heap() || value.raw() == 0 {
                stats.root_scalar_slots += 1;
                continue;
            }
            stats.root_heap_edges += 1;
            let bits = value
                .heap_object_word()
                .expect("heap root should encode as tagged bits");
            if let Some(new_bits) = cheney_forward_strict_bits(
                bits,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
                &mut stats,
            ) {
                *value = AnyValue::heap_ptr(
                    (new_bits & !crate::fz_value::TAG_MASK) as *mut u8,
                    value.kind(),
                );
            }
        }

        for value in ref_roots.iter_mut() {
            forward_tagged_ref_root(
                value,
                &from_ranges,
                &mut self.fragments,
                &mut frag_queue,
                &mut free,
                to_end,
                &self.schemas.borrow(),
                &mut copied_objects,
                &mut stats,
            );
        }

        // Mixed-mode BFS: alternately drain to-space scan and frag_queue
        // until both are empty. Fragments traced in frag_queue may push
        // new to-space objects (their children); newly-traced to-space
        // objects may push new fragments. Loop until no work left.
        let schemas = self.schemas.borrow();
        let mut scan_idx = 0usize;
        loop {
            // Drain to-space BFS frontier.
            while scan_idx < copied_objects.len() {
                let copied = copied_objects[scan_idx];
                scan_idx += 1;
                match copied.tag {
                    crate::fz_value::TAG_LIST => cheney_trace_list(
                        copied.ptr as *mut ListCons,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_MAP => cheney_trace_map(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_CLOSURE => cheney_trace_closure(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_STRUCT => cheney_trace_struct(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_BITSTRING | crate::fz_value::TAG_PROCBIN => {}
                    crate::fz_value::TAG_RESOURCE => cheney_trace_resource(
                        copied.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    tag => panic!("Cheney scan: invalid copied object tag {tag:#x}"),
                }
            }
            // Drain fragment queue. Each fragment's children may forward
            // either into to-space (which extends `free`, picked up by
            // the loop above on the next iteration) or into another
            // fragment (re-pushes to frag_queue).
            if let Some(frag) = frag_queue.pop() {
                match frag.tag {
                    crate::fz_value::TAG_LIST => cheney_trace_list(
                        frag.ptr as *mut ListCons,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_MAP => cheney_trace_map(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_CLOSURE => cheney_trace_closure(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_STRUCT => cheney_trace_struct(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    crate::fz_value::TAG_BITSTRING | crate::fz_value::TAG_PROCBIN => {}
                    crate::fz_value::TAG_RESOURCE => cheney_trace_resource(
                        frag.ptr,
                        &from_ranges,
                        &mut self.fragments,
                        &mut frag_queue,
                        &mut free,
                        to_end,
                        &schemas,
                        &mut copied_objects,
                        &mut stats,
                    ),
                    tag => panic!("Cheney scan: invalid fragment object tag {tag:#x}"),
                }
                continue;
            }
            break;
        }
        drop(schemas);

        // fz-q8d.1 — MSO sweep walks the intrusive chain. Survivors get
        // rewritten to their to-space copies; dead entries release their
        // SharedBin reference. Must run before `pool_free` below because
        // it dereferences from-space ProcBins (specifically their
        // mso_next link, which Cheney never overwrites).
        mso_sweep(self);

        // fz-q8d.4 — fragment sweep: free unmarked fragments, count
        // survivors into live_count, and reset marks on those that
        // remain. `swap_remove` is safe because order doesn't matter.
        let mut live_count = copied_objects.len() as u64;
        let mut fragment_live_bytes = 0usize;
        let mut i = 0;
        while i < self.fragments.len() {
            if self.fragments[i].mark {
                self.fragments[i].mark = false;
                fragment_live_bytes += self.fragments[i].size;
                live_count += 1;
                i += 1;
            } else {
                let f = self.fragments.swap_remove(i);
                unsafe { dealloc(f.ptr, f.layout) };
            }
        }

        // Return old from-space (current + abandoned) to the pool (§6.6).
        pool_free(self.block_start, self.size_class);
        for (p, sc) in self.abandoned_blocks.drain(..) {
            pool_free(p, sc);
        }

        // Install to-space as the new current block.
        self.block_start = to_start;
        self.bump_top = free;
        self.block_end = to_end;
        self.block_size = to_size;
        self.size_class = size_class;
        self.alloc_count = live_count;
        self.gc_run_count += 1;
        self.gc_threshold_bytes = to_size / 2;
        self.gc_watermark = watermark_for(to_start, to_size);
        self.last_gc_live_bytes = unsafe { free.offset_from(to_start) } as usize;
        stats.fragment_survivors = live_count.saturating_sub(copied_objects.len() as u64);
        stats.fragment_live_bytes = fragment_live_bytes as u64;
        stats.live_objects = live_count;
        stats.live_bytes = self.last_gc_live_bytes as u64 + stats.fragment_live_bytes;
        self.last_gc_stats = stats;
        stats
    }

    /// Cheney with a scheduler-owned primary closure root plus persistent
    /// process roots. This is the closure-shaped mid-flight path: the
    /// continuation closure captures the live loop state, while mailbox
    /// entries remain process-owned roots until consumed.
    pub fn gc_process_roots(
        &mut self,
        primary_root: &mut *mut u8,
        mailbox: &mut std::collections::VecDeque<TaggedValueRef>,
    ) -> GcStats {
        let mut primary_root_bits = if primary_root.is_null() {
            std::ptr::null_mut()
        } else {
            crate::fz_value::heap_object_word(
                *primary_root as *const u8,
                crate::fz_value::ValueKind::CLOSURE,
            ) as *mut u8
        };
        let mut mb_roots: Vec<TaggedValueRef> = mailbox.drain(..).collect();
        let stats = self.gc_with_extra_roots(&mut primary_root_bits, &mut [], &mut mb_roots);

        *primary_root = if primary_root_bits.is_null() {
            std::ptr::null_mut()
        } else {
            crate::fz_value::closure_addr_from_tagged(primary_root_bits as u64)
                .expect("forwarded process closure root")
        };
        for v in mb_roots {
            mailbox.push_back(v);
        }
        stats
    }

    /// Cheney with interpreter-owned typed roots plus persistent process roots.
    /// The interpreter has no parked continuation closure while it is
    /// synchronously executing a tail-recursive loop, so its current argument
    /// vector is the root set.
    pub fn gc_any_value_roots_with_process_roots(
        &mut self,
        roots: &mut [AnyValue],
        mailbox: &mut std::collections::VecDeque<TaggedValueRef>,
    ) -> GcStats {
        let mut null_root: *mut u8 = std::ptr::null_mut();
        let mut mb_roots: Vec<TaggedValueRef> = mailbox.drain(..).collect();
        let mut all_extras: Vec<AnyValue> = roots.to_vec();

        let stats = self.gc_with_extra_roots(&mut null_root, &mut all_extras, &mut mb_roots);

        let roots_end = roots.len();
        roots.copy_from_slice(&all_extras[..roots_end]);
        for v in mb_roots {
            mailbox.push_back(v);
        }
        stats
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        // fz-q8d.1 — release every SharedBin held via the intrusive MSO
        // chain. Order matters: must run before pool_free below, since
        // mso_drop_all walks ProcBin payloads in the from-space blocks.
        mso_drop_all(self);
        // fz-q8d.4 — free every fragment outright. Fragments are
        // system-allocator backed; no pool involvement.
        for f in self.fragments.drain(..) {
            unsafe { dealloc(f.ptr, f.layout) };
        }
        // Return blocks to the pool (§6.6) instead of free'ing. Next
        // spawn pulls from the same class — no per-spawn malloc.
        pool_free(self.block_start, self.size_class);
        for (p, sc) in self.abandoned_blocks.drain(..) {
            pool_free(p, sc);
        }
    }
}
