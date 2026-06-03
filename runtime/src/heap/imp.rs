//! impl Heap — the giant impl block + Drop.

use super::block_pool::{SIZE_TABLE, pick_size_class, pool_alloc, pool_free};
use super::fragment::{CopiedObject, FRAGMENT_THRESHOLD, Fragment, classify_fragment};
use super::gc::{
    cheney_forward_strict_bits, cheney_trace_closure, cheney_trace_list, cheney_trace_map, cheney_trace_resource,
    cheney_trace_struct, forward_any_value_ref_root,
};
use super::key_cmp::{map_key_cmp_any, map_key_cmp_refs, same_any_value, same_value_ref};
use super::ref_io::{
    allocation_watermark_for, any_value_ref_from_storage, list_tail_bits_from_ref, map_entry_refs,
    reject_scalar_ref_write, write_any_value_to_storage, write_ref_to_storage,
};
use super::schema::{Schema, SchemaRegistry};
use super::stats::GcStats;
use super::{Heap, HeapAllocKind, HeapAllocStats, SHARED_BIN_THRESHOLD_BYTES};
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, CLOSURE_FLAGS_CAPTURED_MASK, ListCons, TAG_BITSTRING, TAG_CLOSURE,
    TAG_LIST, TAG_MAP, TAG_MASK, TAG_PROCBIN, TAG_RESOURCE, TAG_STRUCT, ValueKind, bitstring_size_for_bit_len,
    closure_addr_from_tagged, closure_capture_kind_slot, closure_capture_raw_slot, closure_capture_set,
    closure_capture_value, closure_flags_pack, closure_size_for_count, heap_kind_from_tagged, heap_object_word,
    list_addr_from_tagged, map_addr_from_tagged, map_count, map_entry, map_entry_raw_kinds, map_key_kind, map_keys_ptr,
    map_pack_tag, map_size_for_count, map_tag_bytes_len, map_tag_ptr, map_values_ptr, struct_field_kind_slot,
    struct_field_raw_slot, struct_schema_id, struct_size_for_payload,
};
use crate::procbin::{SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep};
use crate::process::{Process, YIELD_REASON_ALLOCATION_PRESSURE};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::mem::size_of;
use std::ptr::{copy_nonoverlapping, null_mut, read, write, write_bytes};
use std::rc::Rc;
use std::sync::atomic::{AtomicBool, Ordering};

// fz-vdt.16 — pure reads that need no heap state. Reading a list head/tail or a
// closure capture is a dereference of the self-describing value pointer, so these
// are free functions (the `Heap::read_*` methods below delegate). BIFs call them
// directly, with no `current_process()` and no process argument — which is also
// why the receive matcher can project list/closure shapes without a process.

pub fn list_head_ref(list: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
    let addr = list.list_addr()?;
    let cons = unsafe { &*(addr as *const ListCons) };
    any_value_ref_from_storage(&cons.head as *const u64, cons.head_kind())
}

pub fn list_tail_ref(list: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
    let addr = list.list_addr()?;
    let cons = unsafe { &*(addr as *const ListCons) };
    let tail_addr = cons.tail_addr();
    if tail_addr == 0 {
        Ok(AnyValueRef::empty_list())
    } else {
        AnyValueRef::from_heap_object(ValueKind::LIST, tail_addr as *const u8)
    }
}

pub fn closure_capture_ref(closure: AnyValueRef, idx: usize) -> Result<AnyValueRef, AnyValueRefError> {
    let addr = closure.closure_addr()?;
    let raw_slot = unsafe { closure_capture_raw_slot(addr as *const u8, idx) };
    let kind_slot = unsafe { closure_capture_kind_slot(addr as *const u8, idx) };
    let kind = unsafe { read(kind_slot) };
    any_value_ref_from_storage(
        raw_slot as *const u64,
        ValueKind::new(kind).expect("closure capture kind"),
    )
}

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
            allocation_watermark: allocation_watermark_for(block_start, block_size),
            last_gc_live_bytes: 0,
            last_gc_stats: GcStats::default(),
            abandoned_blocks: Vec::new(),
            schemas,
            pressure: AtomicBool::new(false),
            // Default: half the block. Tunable per-Process for tests that
            // want to force the park-time GC hook to fire.
            gc_threshold_bytes: block_size / 2,
            gc_run_count: 0,
            alloc_count: 0,
            alloc_stats: HeapAllocStats::default(),
            mso_head: 0,
            pending_dtors: VecDeque::new(),
            fragments: Vec::new(),
            owner: null_mut(),
        }
    }

    /// Install the owning process for allocation-pressure budget expiry.
    /// Called per quantum at scheduler entry (alongside `Process.ctx`).
    pub fn set_owner(&mut self, owner: *mut Process) {
        self.owner = owner;
    }

    pub fn should_gc(&self) -> bool {
        self.pressure.load(Ordering::Relaxed)
    }

    pub fn clear_should_gc_flag(&self) {
        self.pressure.store(false, Ordering::Relaxed);
    }

    fn note_alloc_pressure(&self) {
        if self.bytes_used() >= self.gc_threshold_bytes {
            self.pressure.store(true, Ordering::Relaxed);
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
        self.alloc_kind(HeapAllocKind::Other, size)
    }

    pub fn alloc_kind(&mut self, kind: HeapAllocKind, size: usize) -> *mut u8 {
        let size = (size + 15) & !15;
        assert!(size >= 16, "alloc must reserve at least one 16-byte object slot");
        self.alloc_stats.record(kind, size as u64);
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
            let bumped = self.size_class.saturating_add(1).min((SIZE_TABLE.len() - 1) as u8);
            let new_class = want_for_alloc.max(bumped);
            let new_size = SIZE_TABLE[new_class as usize];
            self.abandoned_blocks.push((self.block_start, self.size_class));
            let new_block = pool_alloc(new_class);
            self.block_start = new_block;
            self.bump_top = new_block;
            self.block_end = unsafe { new_block.add(new_size) };
            self.block_size = new_size;
            self.size_class = new_class;
            self.allocation_watermark = allocation_watermark_for(new_block, new_size);
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        self.note_alloc_pressure();
        if self.bump_top >= self.allocation_watermark && !self.owner.is_null() {
            // Expire the owning process's reduction budget so the next back-edge
            // yields through the normal scheduler path. Reached via the per-quantum
            // owner back-pointer — no ambient current-process. Routes through
            // `expire_budget` (not a hand-rolled zero) so the reductions burned
            // before the watermark cross are banked into `reductions_executed`
            // exactly once; `finish_yield_report` depends on this invariant.
            let owner = unsafe { &mut *self.owner };
            owner.expire_budget(YIELD_REASON_ALLOCATION_PRESSURE);
        }
        p
    }

    pub fn alloc_stats_snapshot(&self) -> HeapAllocStats {
        self.alloc_stats
    }

    pub fn reset_alloc_stats(&mut self) {
        self.alloc_stats = HeapAllocStats::default();
    }

    pub fn record_external_alloc(&mut self, kind: HeapAllocKind, bytes: usize) {
        let bytes = ((bytes + 15) & !15) as u64;
        self.alloc_stats.record(kind, bytes);
    }

    pub fn alloc_struct(&mut self, schema_id: u32) -> *mut u8 {
        let payload_size = self.schemas.borrow().get(schema_id).allocation_payload_size();
        let total = struct_size_for_payload(payload_size);
        let p = self.alloc_kind(HeapAllocKind::Struct, total);
        unsafe {
            write(p as *mut u32, schema_id);
            write(p.add(4) as *mut u32, 0);
            // Zero payload.
            write_bytes(p.add(8), 0, total - 8);
        }
        p
    }

    pub(crate) fn closure_schema_id(&mut self, captured_count: usize) -> u32 {
        self.schemas.borrow_mut().closure_env(captured_count)
    }

    pub fn range_fields(&self, range: AnyValueRef) -> Result<(i64, i64, i64), AnyValueRefError> {
        let p = range.struct_addr()?;
        let schema_id = unsafe { struct_schema_id(p.cast_const()) };
        let reg = self.schemas.borrow();
        assert_eq!(
            reg.get(schema_id).name.as_str(),
            Schema::RANGE_NAME,
            "expected Range schema"
        );
        drop(reg);
        let first = self.read_struct_named_field_ref(range, "first")?.load_int()?;
        let last = self.read_struct_named_field_ref(range, "last")?.load_int()?;
        let step = self.read_struct_named_field_ref(range, "step")?.load_int()?;
        Ok((first, last, step))
    }

    fn alloc_list_cons_value(&mut self, head: AnyValueRef, tail_bits: u64) -> u64 {
        let p = self.alloc_kind(HeapAllocKind::ListCons, 16);
        unsafe {
            write(
                p as *mut ListCons,
                ListCons::new(
                    head.storage_raw().expect("list head storage raw"),
                    head.tag(),
                    tail_bits,
                ),
            );
        }
        heap_object_word(p, ValueKind::LIST)
    }

    pub fn alloc_list_cons_slot(&mut self, head: AnyValue, tail_bits: u64) -> u64 {
        self.alloc_list_cons_raw_kind(head.raw(), head.kind(), tail_bits)
    }

    fn alloc_list_cons_raw_kind(&mut self, head_raw: u64, head_kind: ValueKind, tail_bits: u64) -> u64 {
        let p = self.alloc_kind(HeapAllocKind::ListCons, 16);
        unsafe {
            write(p as *mut ListCons, ListCons::new(head_raw, head_kind, tail_bits));
        }
        heap_object_word(p, ValueKind::LIST)
    }

    pub fn alloc_list_cons_any(&mut self, head: AnyValue, tail: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(head, tail_bits);
        let list_addr = list_addr_from_tagged(list_bits).expect("new list addr");
        AnyValueRef::from_heap_object(ValueKind::LIST, list_addr)
    }

    pub fn box_any_value_ref(&mut self, value: AnyValue) -> AnyValueRef {
        match value {
            AnyValue::Null => AnyValueRef::null(),
            AnyValue::EmptyList => AnyValueRef::empty_list(),
            AnyValue::HeapRef(value) => value,
            AnyValue::Int(value) => {
                let slot = self.alloc_kind(HeapAllocKind::ScalarBox, size_of::<u64>()) as *mut u64;
                unsafe {
                    write(slot, value as u64);
                }
                AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("int ref")
            }
            AnyValue::Float(bits) => {
                let slot = self.alloc_kind(HeapAllocKind::ScalarBox, size_of::<u64>()) as *mut u64;
                unsafe {
                    write(slot, bits);
                }
                AnyValueRef::from_scalar_slot(ValueKind::FLOAT, slot as *const u64).expect("float ref")
            }
            AnyValue::Atom(atom_id) => {
                let slot = self.alloc_kind(HeapAllocKind::ScalarBox, size_of::<u64>()) as *mut u64;
                unsafe {
                    write(slot, atom_id as u64);
                }
                AnyValueRef::from_scalar_slot(ValueKind::ATOM, slot as *const u64).expect("atom ref")
            }
        }
    }

    pub fn alloc_list_cons_ref(
        &mut self,
        head: AnyValueRef,
        tail: AnyValueRef,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        reject_scalar_ref_write("alloc_list_cons_ref head", head);
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_value(head, tail_bits);
        let list_addr = list_addr_from_tagged(list_bits).expect("new list addr");
        AnyValueRef::from_heap_object(ValueKind::LIST, list_addr)
    }

    pub fn alloc_list_cons_int(&mut self, head: i64, tail: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::int(head), tail_bits);
        let list_addr = list_addr_from_tagged(list_bits).expect("new list addr");
        AnyValueRef::from_heap_object(ValueKind::LIST, list_addr)
    }

    pub fn alloc_list_cons_float(&mut self, head: f64, tail: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::float(head), tail_bits);
        let list_addr = list_addr_from_tagged(list_bits).expect("new list addr");
        AnyValueRef::from_heap_object(ValueKind::LIST, list_addr)
    }

    pub fn alloc_list_cons_atom(&mut self, atom_id: u32, tail: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let list_bits = self.alloc_list_cons_slot(AnyValue::atom(atom_id), tail_bits);
        let list_addr = list_addr_from_tagged(list_bits).expect("new list addr");
        AnyValueRef::from_heap_object(ValueKind::LIST, list_addr)
    }

    pub fn current_heap_tagged_addr(&self, bits: u64) -> Option<(ValueKind, *mut u8)> {
        let kind = heap_kind_from_tagged(bits)?;
        let p = (bits & !TAG_MASK) as *mut u8;
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
    pub fn alloc_map_refs_bits(&mut self, entries: &[(AnyValueRef, AnyValueRef)]) -> u64 {
        let total = map_size_for_count(entries.len());
        let p = self.alloc_kind(HeapAllocKind::Map, total);
        unsafe {
            write(p as *mut u64, entries.len() as u64);
            let tag_p = map_tag_ptr(p);
            write_bytes(tag_p, 0, map_tag_bytes_len(entries.len()));
            let keys = map_keys_ptr(p, entries.len());
            let values = map_values_ptr(p, entries.len());
            for (i, (key, value)) in entries.iter().copied().enumerate() {
                let key_kind = key.tag();
                let value_kind = value.tag();
                write(tag_p.add(i), map_pack_tag(key_kind, value_kind));
                write_ref_to_storage(keys.add(i), None, key);
                write_ref_to_storage(values.add(i), None, value);
            }
        }
        heap_object_word(p, ValueKind::MAP)
    }

    pub fn alloc_map_slots(&mut self, entries: &[(AnyValue, AnyValue)]) -> u64 {
        let total = map_size_for_count(entries.len());
        let p = self.alloc_kind(HeapAllocKind::Map, total);
        unsafe {
            write(p as *mut u64, entries.len() as u64);
            let tag_p = map_tag_ptr(p);
            write_bytes(tag_p, 0, map_tag_bytes_len(entries.len()));
            let keys = map_keys_ptr(p, entries.len());
            let values = map_values_ptr(p, entries.len());
            for (i, (key, value)) in entries.iter().copied().enumerate() {
                write(tag_p.add(i), map_pack_tag(key.kind(), value.kind()));
                write_any_value_to_storage(keys.add(i), None, key);
                write_any_value_to_storage(values.add(i), None, value);
            }
        }
        heap_object_word(p, ValueKind::MAP)
    }

    pub fn alloc_map_destination(&mut self, base: Option<AnyValueRef>, extra: usize) -> u64 {
        let base_addr = base.and_then(|value| {
            if value.tag() == ValueKind::MAP {
                value.heap_addr(ValueKind::MAP).ok()
            } else {
                None
            }
        });
        let base_count = base_addr.map_or(0, |addr| unsafe { map_count(addr as *const u8) });
        let count = base_count + extra;
        let total = map_size_for_count(count);
        let p = self.alloc(total);
        unsafe {
            write(p as *mut u64, count as u64);
            let tag_p = map_tag_ptr(p);
            write_bytes(tag_p, 0, map_tag_bytes_len(count));
            let keys = map_keys_ptr(p, count);
            let values = map_values_ptr(p, count);
            if let Some(base_addr) = base_addr {
                let base_tags = map_tag_ptr(base_addr);
                let base_keys = map_keys_ptr(base_addr, base_count);
                let base_values = map_values_ptr(base_addr, base_count);
                for i in 0..base_count {
                    write(tag_p.add(i), read(base_tags.add(i)));
                    write(keys.add(i), read(base_keys.add(i)));
                    write(values.add(i), read(base_values.add(i)));
                }
            }
        }
        heap_object_word(p, ValueKind::MAP)
    }

    pub fn map_destination_put(&mut self, dest_bits: u64, key: AnyValue, value: AnyValue) {
        let dest = map_addr_from_tagged(dest_bits).expect("map_destination_put dest");
        let count = unsafe { map_count(dest as *const u8) };
        unsafe {
            let tag_p = map_tag_ptr(dest);
            let keys = map_keys_ptr(dest, count);
            let values = map_values_ptr(dest, count);
            for i in 0..count {
                if map_key_kind(read(tag_p.add(i))) == ValueKind::NULL {
                    write(tag_p.add(i), map_pack_tag(key.kind(), value.kind()));
                    write_any_value_to_storage(keys.add(i), None, key);
                    write_any_value_to_storage(values.add(i), None, value);
                    return;
                }
            }
        }
        panic!("map destination has no free entry slot");
    }

    pub fn map_destination_freeze(&mut self, dest_bits: u64) -> u64 {
        let dest = map_addr_from_tagged(dest_bits).expect("map_destination_freeze dest");
        let count = unsafe { map_count(dest as *const u8) };
        let mut entries = Vec::with_capacity(count);
        for i in 0..count {
            let (key_raw, key_kind, value_raw, value_kind) = unsafe { map_entry_raw_kinds(dest as *const u8, i) };
            if key_kind == ValueKind::NULL {
                continue;
            }
            entries.push((
                AnyValue::decode_parts(key_raw, key_kind.tag()).expect("map destination key"),
                AnyValue::decode_parts(value_raw, value_kind.tag()).expect("map destination value"),
            ));
        }
        entries.sort_by(|a, b| map_key_cmp_any(a.0, b.0));
        let mut deduped: Vec<(AnyValue, AnyValue)> = Vec::with_capacity(entries.len());
        for (key, value) in entries {
            if let Some((last_key, last_value)) = deduped.last_mut()
                && same_any_value(*last_key, key)
            {
                *last_value = value;
                continue;
            }
            deduped.push((key, value));
        }
        if deduped.len() == count {
            unsafe {
                let tag_p = map_tag_ptr(dest);
                let keys = map_keys_ptr(dest, count);
                let values = map_values_ptr(dest, count);
                for (i, (key, value)) in deduped.iter().copied().enumerate() {
                    write(tag_p.add(i), map_pack_tag(key.kind(), value.kind()));
                    write_any_value_to_storage(keys.add(i), None, key);
                    write_any_value_to_storage(values.add(i), None, value);
                }
            }
            return dest_bits;
        }
        self.alloc_map_slots(&deduped)
    }

    pub fn alloc_map_refs(&mut self, entries: &[(AnyValueRef, AnyValueRef)]) -> Result<AnyValueRef, AnyValueRefError> {
        let map_bits = self.alloc_map_refs_bits(entries);
        let map_addr = map_addr_from_tagged(map_bits).expect("new map addr");
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr)
    }

    pub fn map_put_ref(
        &mut self,
        map: AnyValueRef,
        key: AnyValueRef,
        value: AnyValueRef,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        reject_scalar_ref_write("map_put_ref value", value);
        self.map_put_value(map, key, value)
    }

    pub fn map_put_int(
        &mut self,
        map: AnyValueRef,
        key: AnyValueRef,
        value: i64,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let value = value as u64;
        let value = AnyValueRef::from_scalar_slot(ValueKind::INT, &value)?;
        self.map_put_value(map, key, value)
    }

    pub fn map_put_float(
        &mut self,
        map: AnyValueRef,
        key: AnyValueRef,
        value: f64,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let value = value.to_bits();
        let value = AnyValueRef::from_scalar_slot(ValueKind::FLOAT, &value)?;
        self.map_put_value(map, key, value)
    }

    pub fn map_put_atom(
        &mut self,
        map: AnyValueRef,
        key: AnyValueRef,
        atom_id: u32,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let atom_id = atom_id as u64;
        let value = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &atom_id)?;
        self.map_put_value(map, key, value)
    }

    fn map_put_value(
        &mut self,
        map: AnyValueRef,
        key: AnyValueRef,
        value: AnyValueRef,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let map_addr = map.map_addr()?;
        let map_bits = self.map_put_value_bits(map_addr, key, value);
        let map_addr = map_addr_from_tagged(map_bits).expect("new map addr");
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr)
    }

    fn map_put_value_bits(&mut self, map_addr: *mut u8, key: AnyValueRef, value: AnyValueRef) -> u64 {
        let count = unsafe { map_count(map_addr) };
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
        let map_addr = map_addr_from_tagged(map_bits);
        let count = map_addr.map_or(0, |addr| unsafe { map_count(addr) });
        let mut entries = Vec::with_capacity(count + 1);
        let mut replaced = false;
        if let Some(map_addr) = map_addr {
            for i in 0..count {
                let (entry_key, entry_value) = unsafe { map_entry(map_addr, i) };
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
        let total = bitstring_size_for_bit_len(bit_len);
        let p = self.alloc_kind(HeapAllocKind::Bitstring, total);
        unsafe {
            let bit_len_p = p as *mut u64;
            write(bit_len_p, bit_len);
            let bytes_p = p.add(8);
            copy_nonoverlapping(bytes.as_ptr(), bytes_p, bytes.len());
            // Zero the trailing padding so renders / debug aren't garbage.
            let pad_start = 8 + bytes.len();
            if pad_start < total {
                write_bytes(p.add(pad_start), 0, total - pad_start);
            }
        }
        p
    }

    /// Closure layout: `schema_id`, `flags`, raw code pointer, then
    /// schema-backed capture fields.
    pub fn alloc_closure_slots(&mut self, _target_id: u32, captured_count: usize, halt_kind: u16) -> u64 {
        let schema_id = self.closure_schema_id(captured_count);
        self.alloc_closure_slots_with_schema(schema_id, captured_count, halt_kind)
    }

    /// Allocate a closure's slots writing `schema_id` verbatim instead of
    /// registering a `ClosureEnv{n}` schema. For scheduler scaffolding
    /// closures (entry thunks, synthetic main inners) whose `schema_id` is
    /// never consulted: captures are accessed by offset, GC sizes and traces
    /// them by `captured_count` (the closure `flags`), and they are never
    /// rendered. Registering a `ClosureEnv` schema for them would only perturb
    /// the schema-id space the AOT runtime must keep identical to compile time
    /// (and the schema ids interpreter and codegen render). Scaffolding mints
    /// pass a placeholder `schema_id`.
    pub fn alloc_closure_slots_with_schema(&mut self, schema_id: u32, captured_count: usize, halt_kind: u16) -> u64 {
        assert!(
            captured_count <= CLOSURE_FLAGS_CAPTURED_MASK as usize,
            "closure captured count overflow"
        );
        let total = closure_size_for_count(captured_count);
        let p = self.alloc_kind(HeapAllocKind::Closure, total);
        unsafe {
            write(p as *mut u32, schema_id);
            write(
                p.add(4) as *mut u32,
                closure_flags_pack(captured_count as u16, halt_kind) as u32,
            );
            write(p.add(8) as *mut u64, 0);
            if total > 16 {
                write_bytes(p.add(16), 0, total - 16);
            }
        }
        heap_object_word(p, ValueKind::CLOSURE)
    }

    pub fn alloc_closure(
        &mut self,
        schema_id: u32,
        captured_count: usize,
        halt_kind: u16,
        fn_ptr: u64,
        captures: &[AnyValue],
    ) -> u64 {
        assert!(captures.len() <= captured_count, "too many closure captures");
        let bits = self.alloc_closure_slots(schema_id, captured_count, halt_kind);
        let p = closure_addr_from_tagged(bits).expect("new closure ptr");
        unsafe {
            write(p.add(8) as *mut u64, fn_ptr);
            for (i, capture) in captures.iter().enumerate() {
                closure_capture_set(p, i, *capture);
            }
        }
        bits
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn write_closure_capture_value(&mut self, closure_addr: *mut u8, idx: usize, value: AnyValue) {
        unsafe { closure_capture_set(closure_addr, idx, value) };
    }

    pub fn write_closure_capture_ref(
        &mut self,
        closure: AnyValueRef,
        idx: usize,
        value: AnyValueRef,
    ) -> Result<(), AnyValueRefError> {
        let closure = closure.closure_addr()?;
        unsafe { closure_capture_set(closure, idx, AnyValue::from_ref(value)?) };
        Ok(())
    }

    /// # Safety
    ///
    /// `closure_addr` must point to a live closure allocation with a capture
    /// slot at `idx`.
    pub unsafe fn read_closure_capture_value(&self, closure_addr: *const u8, idx: usize) -> AnyValue {
        unsafe { closure_capture_value(closure_addr, idx) }
    }

    /// Write a canonical value into a Struct's generic payload slot.
    pub fn write_field_slot(&mut self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        self.write_struct_field_value(obj, field_offset, value);
    }

    pub fn write_struct_field_ref(
        &mut self,
        obj: AnyValueRef,
        field_offset: u32,
        value: AnyValueRef,
    ) -> Result<(), AnyValueRefError> {
        let obj = obj.struct_addr()?;
        self.write_struct_field_value(obj, field_offset, AnyValue::from_ref(value)?);
        Ok(())
    }

    fn write_struct_field_value(&self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        let schema_id = unsafe { struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw = value.raw();
        unsafe {
            write(struct_field_raw_slot(obj as *const u8, field_offset), raw);
            write(
                struct_field_kind_slot(obj as *const u8, kind_offset),
                value.kind().tag(),
            );
        }
    }

    /// Read a canonical value from a Struct's generic payload slot.
    pub fn read_field_slot(&self, obj: *mut u8, field_offset: u32) -> AnyValue {
        let schema_id = unsafe { struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        unsafe {
            let raw = read(struct_field_raw_slot(obj as *const u8, field_offset));
            let kind = read(struct_field_kind_slot(obj as *const u8, kind_offset));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        }
    }

    pub fn read_list_head_ref(&self, list: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        list_head_ref(list)
    }

    pub fn read_list_tail_ref(&self, list: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        list_tail_ref(list)
    }

    pub fn mark_list_cons_aliased(&mut self, list: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = nonempty_list_addr(list)?;
        let cons = unsafe { &mut *(addr as *mut ListCons) };
        cons.mark_aliased();
        Ok(list)
    }

    pub fn mark_published_ref_aliased(&mut self, value: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        if value.tag() != ValueKind::LIST || value.is_empty_list() {
            return Ok(value);
        }

        let mut addr = value.list_addr()?;
        while !addr.is_null() {
            let cons = unsafe { &mut *(addr as *mut ListCons) };
            cons.mark_aliased();
            addr = cons.tail_addr() as *mut u8;
        }
        Ok(value)
    }

    pub fn relink_unaliased_list_cons_tail(
        &mut self,
        list: AnyValueRef,
        tail: AnyValueRef,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = nonempty_list_addr(list)?;
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let cons = unsafe { &mut *(addr as *mut ListCons) };
        assert!(
            cons.relink_tail_if_unaliased(tail_bits),
            "cannot destructively relink aliased list cons"
        );
        Ok(list)
    }

    pub fn reuse_or_alloc_list_cons_tail(
        &mut self,
        list: AnyValueRef,
        tail: AnyValueRef,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = nonempty_list_addr(list)?;
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let cons = unsafe { &mut *(addr as *mut ListCons) };
        if cons.relink_tail_if_unaliased(tail_bits) {
            return Ok(list);
        }
        let (head_raw, head_kind) = cons.head_raw_kind();
        let fresh = self.alloc_list_cons_raw_kind(head_raw, head_kind, tail_bits);
        let addr = list_addr_from_tagged(fresh).expect("fresh list cons");
        AnyValueRef::from_heap_object(ValueKind::LIST, addr)
    }

    pub fn read_map_value_ref(
        &self,
        map: AnyValueRef,
        key: AnyValueRef,
    ) -> Result<Option<AnyValueRef>, AnyValueRefError> {
        let addr = map.map_addr()?;
        self.read_map_addr_value_ref(addr, key)
    }

    fn read_map_addr_value_ref(
        &self,
        addr: *mut u8,
        key: AnyValueRef,
    ) -> Result<Option<AnyValueRef>, AnyValueRefError> {
        let count = unsafe { map_count(addr) };

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
        map: AnyValueRef,
        key: AnyValue,
    ) -> Result<Option<AnyValueRef>, AnyValueRefError> {
        let addr = map.map_addr()?;
        let count = unsafe { map_count(addr) };
        for i in 0..count {
            let (entry_key, _) = unsafe { map_entry(addr, i) };
            if !same_any_value(entry_key, key) {
                continue;
            }
            let (_, entry_value) = unsafe { map_entry_refs(addr, i) };
            return Ok(Some(entry_value));
        }
        Ok(None)
    }

    pub fn read_struct_field_ref(&self, obj: AnyValueRef, field_offset: u32) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = obj.struct_addr()?;
        let schema_id = unsafe { struct_schema_id(addr as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw_slot = unsafe { struct_field_raw_slot(addr as *const u8, field_offset) };
        let kind = unsafe { read(struct_field_kind_slot(addr as *const u8, kind_offset)) };
        any_value_ref_from_storage(raw_slot as *const u64, ValueKind::new(kind).expect("struct field kind"))
    }

    pub fn read_struct_named_field_ref(
        &self,
        obj: AnyValueRef,
        field_name: &str,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = obj.struct_addr()?;
        let schema_id = unsafe { struct_schema_id(addr as *const u8) };
        let field_offset = {
            let schemas = self.schemas.borrow();
            let schema = schemas.get(schema_id);
            schema
                .fields
                .iter()
                .find(|field| field.name.as_deref() == Some(field_name))
                .unwrap_or_else(|| panic!("schema {} has no field named {}", schema.name, field_name))
                .offset
        };
        self.read_struct_field_ref(obj, field_offset)
    }

    pub fn read_closure_capture_ref(&self, closure: AnyValueRef, idx: usize) -> Result<AnyValueRef, AnyValueRefError> {
        closure_capture_ref(closure, idx)
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

    pub fn bytes_remaining_in_block(&self) -> usize {
        unsafe { self.block_end.offset_from(self.bump_top) as usize }
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
    pub fn gc_with_extra_root_slots(&mut self, root_slot: &mut *mut u8, extra_roots: &mut [AnyValue]) -> GcStats {
        self.gc_with_extra_roots(root_slot, extra_roots, &mut [])
    }

    pub fn gc_with_any_value_ref_roots(&mut self, root_slot: &mut *mut u8, ref_roots: &mut [AnyValueRef]) -> GcStats {
        self.gc_with_extra_roots(root_slot, &mut [], ref_roots)
    }

    pub fn gc_with_value_and_any_value_ref_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
        ref_roots: &mut [AnyValueRef],
    ) -> GcStats {
        self.gc_with_extra_roots(root_slot, extra_roots, ref_roots)
    }

    fn gc_with_extra_roots(
        &mut self,
        root_slot: &mut *mut u8,
        extra_roots: &mut [AnyValue],
        ref_roots: &mut [AnyValueRef],
    ) -> GcStats {
        // Snapshot from-space block ranges before we allocate to-space.
        let mut from_ranges: Vec<(*mut u8, *mut u8)> = Vec::with_capacity(1 + self.abandoned_blocks.len());
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

        // Pick to-space size with BEAM-style grow/shrink bands
        // (erlang.org/doc/apps/erts/garbagecollection). Fragment bytes are
        // excluded — fragments are never copied into to-space.
        //
        // The steady-state target is ~2x live (a 50% post-GC fill).
        // `prev_live` is the last GC's survivor bytes (0 before the first GC).
        let fragment_bytes: usize = self.fragments.iter().map(|f| f.size).sum();
        let prev_live = self.last_gc_live_bytes;
        let fit_to_live = if prev_live > 0 {
            prev_live.saturating_mul(2)
        } else {
            self.bytes_used().saturating_sub(fragment_bytes)
        };

        // Three bands, biased toward holding size — unlike a BEAM minor
        // collection, a copy GC here costs a scheduler yield, so frequent
        // collection is expensive and oscillation is worth avoiding:
        //
        //   GROW   — this GC fired under allocation pressure (the from-space
        //            reached the watermark, or we abandoned a block and grew
        //            mid-quantum). The heap can't hold the allocation rate;
        //            refitting to 2x *live* would just thrash. Size to hold
        //            this cycle's realized footprint (live + garbage since the
        //            last GC), doubled for headroom, jumping as many classes
        //            as needed and never less than one class up. Self-bounding:
        //            once a quantum of allocation fits below the watermark, GCs
        //            go back to reduction-driven and the pressure clears.
        //   SHRINK — live has fallen to <=25% of the heap; refit to ~50%.
        //   KEEP   — live sits in the 25%–75% dead zone; hold the current size.
        let was_pressured = !self.abandoned_blocks.is_empty() || self.bump_top >= self.allocation_watermark;
        let target_bytes = if was_pressured {
            let footprint = self.bytes_used().saturating_sub(fragment_bytes);
            fit_to_live.max(footprint.saturating_mul(2))
        } else if prev_live == 0 || prev_live.saturating_mul(4) <= self.block_size {
            fit_to_live
        } else {
            self.block_size
        };
        let mut size_class = pick_size_class(target_bytes.max(SIZE_TABLE[0]));
        if was_pressured {
            let grown = self.size_class.saturating_add(1).min((SIZE_TABLE.len() - 1) as u8);
            size_class = size_class.max(grown);
        }
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
                *value = AnyValue::heap_ptr((new_bits & !TAG_MASK) as *mut u8, value.kind());
            }
        }

        for value in ref_roots.iter_mut() {
            forward_any_value_ref_root(
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
                    TAG_LIST => cheney_trace_list(
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
                    TAG_MAP => cheney_trace_map(
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
                    TAG_CLOSURE => cheney_trace_closure(
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
                    TAG_STRUCT => cheney_trace_struct(
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
                    TAG_BITSTRING | TAG_PROCBIN => {}
                    TAG_RESOURCE => cheney_trace_resource(
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
                    TAG_LIST => cheney_trace_list(
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
                    TAG_MAP => cheney_trace_map(
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
                    TAG_CLOSURE => cheney_trace_closure(
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
                    TAG_STRUCT => cheney_trace_struct(
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
                    TAG_BITSTRING | TAG_PROCBIN => {}
                    TAG_RESOURCE => cheney_trace_resource(
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
        self.allocation_watermark = allocation_watermark_for(to_start, to_size);
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
    pub fn gc_process_roots(&mut self, primary_root: &mut *mut u8, mailbox: &mut VecDeque<AnyValueRef>) -> GcStats {
        let mut primary_root_bits = if primary_root.is_null() {
            null_mut()
        } else {
            heap_object_word(*primary_root as *const u8, ValueKind::CLOSURE) as *mut u8
        };
        let mut mb_roots: Vec<AnyValueRef> = mailbox.drain(..).collect();
        let stats = self.gc_with_extra_roots(&mut primary_root_bits, &mut [], &mut mb_roots);

        *primary_root = if primary_root_bits.is_null() {
            null_mut()
        } else {
            closure_addr_from_tagged(primary_root_bits as u64).expect("forwarded process closure root")
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
        mailbox: &mut VecDeque<AnyValueRef>,
    ) -> GcStats {
        let mut null_root: *mut u8 = null_mut();
        let mut mb_roots: Vec<AnyValueRef> = mailbox.drain(..).collect();
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

fn nonempty_list_addr(list: AnyValueRef) -> Result<*mut u8, AnyValueRefError> {
    let addr = list.list_addr()?;
    if addr.is_null() {
        return Err(AnyValueRefError::NullAddress(ValueKind::LIST));
    }
    Ok(addr)
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
