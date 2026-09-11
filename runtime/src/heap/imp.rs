//! impl Heap — the giant impl block + Drop.

use super::block_pool::{SIZE_TABLE, pick_size_class, pool_alloc, pool_free};
use super::fragment::{CopiedObject, FRAGMENT_THRESHOLD, Fragment, classify_fragment};
use super::gc::{
    cheney_forward_strict_bits, cheney_trace_closure, cheney_trace_list, cheney_trace_map, cheney_trace_resource,
    cheney_trace_struct, forward_any_value_ref_root,
};
use super::ref_io::{
    any_value_ref_from_storage, list_tail_bits_from_ref, map_entry_refs, reject_scalar_ref_write,
    write_any_value_to_storage,
};
use super::schema::{Schema, SchemaRegistry};
use super::stats::GcStats;
use super::{Heap, HeapAllocKind, HeapAllocStats, SHARED_BIN_THRESHOLD_BYTES};
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, CLOSURE_FLAGS_CAPTURED_MASK, ListCons, MAP_DESTINATION_FLAG,
    TAG_BITSTRING, TAG_CLOSURE, TAG_LIST, TAG_MAP, TAG_MASK, TAG_PROCBIN, TAG_RESOURCE, TAG_STRUCT, ValueKind,
    bitstring_size_for_bit_len, closure_addr_from_tagged, closure_capture_kind_slot, closure_capture_raw_slot,
    closure_capture_set, closure_capture_value, closure_header_word, closure_size_for_count, heap_kind_from_tagged,
    heap_object_word, list_addr_from_tagged, map_addr_from_tagged, map_count, map_entry, map_keys_ptr, map_pack_tag,
    map_size_for_count, map_tag_bytes_len, map_tag_ptr, map_values_ptr, struct_field_kind_slot, struct_field_raw_slot,
    struct_schema_id, struct_size_for_payload,
};
use crate::procbin::{SharedBin, SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep};
use crate::process::Node;
use crate::term::{NumericMode, TermComparator};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::mem::size_of;
use std::ptr::{copy_nonoverlapping, null_mut, read, write, write_bytes};
use std::rc::Rc;
use std::slice::from_raw_parts;
use std::sync::atomic::{AtomicBool, Ordering};

// fz-vdt.16 — pure reads that need no heap state. Reading a list head/tail or a
// closure capture is a dereference of the self-describing value pointer, so these
// are free functions (the `Heap::read_*` methods below delegate). BIFs call them
// directly, with no `current_process()` and no process argument — which is also
// why the receive matcher can project list/closure shapes without a process.

fn map_destination_header(capacity: usize, filled: usize) -> u64 {
    assert!(capacity < (1 << 31) && filled <= capacity, "map destination capacity");
    MAP_DESTINATION_FLAG | ((filled as u64) << 32) | capacity as u64
}

fn map_destination_state(addr: *const u8) -> (usize, usize) {
    let header = unsafe { read(addr.cast::<u64>()) };
    assert_ne!(header & MAP_DESTINATION_FLAG, 0, "map is already published");
    (
        header as u32 as usize,
        ((header & !MAP_DESTINATION_FLAG) >> 32) as usize,
    )
}

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
        Self::with_node(capacity, schemas, Rc::new(Node::empty()))
    }

    pub fn with_node(capacity: usize, schemas: Rc<RefCell<SchemaRegistry>>, node: Rc<Node>) -> Self {
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
            last_gc_live_bytes: 0,
            last_gc_stats: GcStats::default(),
            abandoned_blocks: Vec::new(),
            node,
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
        }
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
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        self.note_alloc_pressure();
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

    pub fn range_fields(&self, range: AnyValueRef) -> Result<(i64, i64, i64), AnyValueRefError> {
        let p = range.struct_addr()?;
        let schema_id = unsafe { struct_schema_id(p.cast_const()) };
        let reg = self.schemas.borrow();
        assert!(reg.get(schema_id).is_range(), "expected Range schema");
        drop(reg);
        let first = self.read_struct_named_field_ref(range, "first")?.load_int()?;
        let last = self.read_struct_named_field_ref(range, "last")?.load_int()?;
        let step = self.read_struct_named_field_ref(range, "step")?.load_int()?;
        Ok((first, last, step))
    }

    fn alloc_list_cons_value(&mut self, head: AnyValueRef, tail_bits: u64) -> u64 {
        self.mark_published_ref_aliased(head).expect("published list head");
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
        self.publish_contained_parts(head_raw, head_kind);
        self.alloc_list_cons_storage(head_raw, head_kind, tail_bits)
    }

    fn alloc_list_cons_storage(&mut self, head_raw: u64, head_kind: ValueKind, tail_bits: u64) -> u64 {
        let p = self.alloc_kind(HeapAllocKind::ListCons, 16);
        unsafe {
            write(p as *mut ListCons, ListCons::new(head_raw, head_kind, tail_bits));
        }
        heap_object_word(p, ValueKind::LIST)
    }

    pub(super) fn publish_contained_parts(&mut self, raw: u64, kind: ValueKind) {
        if kind == ValueKind::LIST && raw != 0 {
            let value = AnyValueRef::from_heap_object(kind, raw as *const u8).expect("contained list");
            self.mark_published_ref_aliased(value)
                .expect("published contained list");
        }
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
                let bits = AnyValue::float(f64::from_bits(bits)).raw();
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

    /// Publish a map, normalizing its strict structural keys exactly once.
    pub fn alloc_map_refs_bits(&mut self, entries: &[(AnyValueRef, AnyValueRef)]) -> u64 {
        let entries = entries
            .iter()
            .map(|&(key, value)| {
                (
                    AnyValue::from_ref(key).expect("map key"),
                    AnyValue::from_ref(value).expect("map value"),
                )
            })
            .collect();
        self.publish_map_entries(entries)
    }

    pub fn alloc_map_slots(&mut self, entries: &[(AnyValue, AnyValue)]) -> u64 {
        self.publish_map_entries(entries.to_vec())
    }

    fn publish_map_entries(&mut self, mut entries: Vec<(AnyValue, AnyValue)>) -> u64 {
        self.normalize_map_entries(&mut entries);
        self.alloc_ordered_map_entries(entries.into_iter())
    }

    fn normalize_map_entries(&self, entries: &mut Vec<(AnyValue, AnyValue)>) {
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        entries.sort_by(|a, b| comparator.compare(a.0, b.0, NumericMode::Strict));
        entries.dedup_by(|later, earlier| {
            if comparator.compare(later.0, earlier.0, NumericMode::Strict).is_eq() {
                earlier.1 = later.1;
                true
            } else {
                false
            }
        });
    }

    /// Copy entries whose ordering is preserved by an immutable map operation.
    pub(super) fn alloc_ordered_map_entries(
        &mut self,
        entries: impl ExactSizeIterator<Item = (AnyValue, AnyValue)>,
    ) -> u64 {
        let count = entries.len();
        let p = self.alloc_kind(HeapAllocKind::Map, map_size_for_count(count));
        self.write_ordered_map_entries(p, count, entries);
        heap_object_word(p, ValueKind::MAP)
    }

    fn write_ordered_map_entries(
        &mut self,
        p: *mut u8,
        count: usize,
        entries: impl Iterator<Item = (AnyValue, AnyValue)>,
    ) {
        unsafe {
            write(p as *mut u64, count as u64);
            let tag_p = map_tag_ptr(p);
            write_bytes(tag_p, 0, map_tag_bytes_len(count));
            let keys = map_keys_ptr(p, count);
            let values = map_values_ptr(p, count);
            for (i, (key, value)) in entries.enumerate() {
                assert_ne!(key.kind(), ValueKind::NULL, "unpublished map key");
                self.publish_contained_parts(key.raw(), key.kind());
                self.publish_contained_parts(value.raw(), value.kind());
                write(tag_p.add(i), map_pack_tag(key.kind(), value.kind()));
                write_any_value_to_storage(keys.add(i), None, key);
                write_any_value_to_storage(values.add(i), None, value);
            }
        }
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
        let p = self.alloc_kind(HeapAllocKind::Map, total);
        unsafe {
            write(p as *mut u64, map_destination_header(count, base_count));
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

    /// Append to an exclusively owned, unpublished map destination.
    ///
    /// # Safety
    /// `key` and `value` must be finite immutable terms. Neither may reach this
    /// or any other unfinished destination. Freezing publishes the stored fields.
    pub unsafe fn map_destination_put(&mut self, dest_bits: u64, key: AnyValue, value: AnyValue) {
        let dest = map_addr_from_tagged(dest_bits).expect("map_destination_put dest");
        let (count, filled) = map_destination_state(dest);
        assert!(filled < count, "map destination has no free entry slot");
        assert_ne!(key.kind(), ValueKind::NULL, "unpublished map key");
        unsafe {
            let tag_p = map_tag_ptr(dest);
            let keys = map_keys_ptr(dest, count);
            let values = map_values_ptr(dest, count);
            write(tag_p.add(filled), map_pack_tag(key.kind(), value.kind()));
            write_any_value_to_storage(keys.add(filled), None, key);
            write_any_value_to_storage(values.add(filled), None, value);
            write(dest as *mut u64, map_destination_header(count, filled + 1));
        }
    }

    pub fn map_destination_freeze(&mut self, dest_bits: u64) -> u64 {
        let dest = map_addr_from_tagged(dest_bits).expect("map destination");
        let (_, filled) = map_destination_state(dest);
        let mut entries: Vec<_> = (0..filled).map(|i| unsafe { map_entry(dest, i) }).collect();
        self.normalize_map_entries(&mut entries);
        self.write_ordered_map_entries(dest, entries.len(), entries.into_iter());
        dest_bits
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
        self.map_put_entry(
            map_addr,
            AnyValue::from_ref(key).expect("map key"),
            AnyValue::from_ref(value).expect("map value"),
        )
    }

    /// An absent deletion borrows the original map without allocating.
    pub fn map_delete_ref(&mut self, map: AnyValueRef, key: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = map.map_addr()?;
        let Ok(index) = self.map_key_position(addr, AnyValue::from_ref(key)?) else {
            return Ok(map);
        };
        let count = unsafe { map_count(addr) };
        let bits = self.alloc_ordered_map_entries(
            (0..count - 1).map(|i| unsafe { map_entry(addr, if i < index { i } else { i + 1 }) }),
        );
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(bits).expect("new map"))
    }

    pub fn map_put_slot_bits(&mut self, map_bits: u64, key: AnyValue, value: AnyValue) -> u64 {
        match map_addr_from_tagged(map_bits) {
            Some(addr) => self.map_put_entry(addr, key, value),
            None => self.alloc_ordered_map_entries(std::iter::once((key, value))),
        }
    }

    fn map_put_entry(&mut self, addr: *mut u8, key: AnyValue, value: AnyValue) -> u64 {
        let count = unsafe { map_count(addr) };
        let position = self.map_key_position(addr, key);
        let (index, inserted) = match position {
            Ok(index) => (index, 0),
            Err(index) => (index, 1),
        };
        self.alloc_ordered_map_entries((0..count + inserted).map(|i| {
            if i == index {
                (key, value)
            } else {
                unsafe { map_entry(addr, if i < index { i } else { i - inserted }) }
            }
        }))
    }

    fn map_key_position(&self, addr: *mut u8, key: AnyValue) -> Result<usize, usize> {
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        let (mut low, mut high) = (0, unsafe { map_count(addr) });
        while low < high {
            let middle = low + (high - low) / 2;
            let entry_key = unsafe { map_entry(addr, middle).0 };
            match comparator.compare(entry_key, key, NumericMode::Strict) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Ok(middle),
            }
        }
        Err(low)
    }

    /// Strict inline Bitstring layout: bit_len: u64 + bytes (padded to 16).
    /// Caller supplies a fully-built byte buffer + bit_len; this performs the
    /// heap copy.
    ///
    /// fz-cty.5 — payloads larger than `SHARED_BIN_THRESHOLD_BYTES` route
    /// through the shared zone: a SharedBin is allocated off-heap and the
    /// per-process heap gets a tagged ProcBin stub referencing
    /// it. Render and bit-match dispatch via
    /// `bitstring_bit_len` / `bitstring_byte_ptr`.
    ///
    /// This always COPIES `bytes`. To view an existing shared buffer
    /// without copying it, use `alloc_bitstring_suffix`.
    ///
    /// fz-5xp.45 — returns the VALUE, kind included. The storage choice is
    /// made here and only here; four callers used to re-derive it from
    /// `bytes.len()` against the same threshold, which meant the threshold was
    /// a constant five places had to agree about and a caller could disagree
    /// with what was actually allocated.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> AnyValue {
        if bytes.len() > SHARED_BIN_THRESHOLD_BYTES {
            let handle = SharedBinHandle::from_bytes(bytes, bit_len);
            self.alloc_stats.record_shared_bin(bytes.len() as u64);
            return AnyValue::heap_ptr(alloc_procbin(self, handle, 0).as_raw(), ValueKind::PROCBIN);
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
        AnyValue::heap_ptr(p, ValueKind::BITSTRING)
    }

    /// Allocate the byte-aligned SUFFIX `[byte_offset ..]` of an existing
    /// `SharedBin`, returning it as a value.
    ///
    /// fz-5xp.55 — above `SHARED_BIN_THRESHOLD_BYTES` the suffix SHARES the
    /// parent's bytes: a new stub retains the same SharedBin at its own
    /// offset, and nothing is copied. That is what stops a byte scanner
    /// being quadratic, because every `<<_c, rest :: binary>>` step is a
    /// suffix.
    ///
    /// At or below the threshold the bytes are copied into an inline
    /// bitstring. Copying is cheaper than a stub at that size, and it keeps
    /// a small tail from pinning a large buffer alive.
    ///
    /// This is the one place the inline/shared choice is made for a suffix,
    /// so it returns the value rather than a bare pointer the caller has to
    /// re-classify.
    ///
    /// # Safety
    ///
    /// `shared` must point at a live `SharedBin` the caller holds a
    /// reference edge to for the duration of the call.
    pub unsafe fn alloc_bitstring_suffix(&mut self, shared: *mut SharedBin, byte_offset: u64) -> AnyValue {
        let (buf_ptr, buf_bytes, buf_bits) = unsafe { ((*shared).bytes_ptr, (*shared).bytes_len, (*shared).bit_len) };
        assert!(
            byte_offset as usize <= buf_bytes,
            "bitstring suffix offset {byte_offset} past the shared buffer"
        );
        let suffix_bytes = buf_bytes - byte_offset as usize;
        if suffix_bytes > SHARED_BIN_THRESHOLD_BYTES {
            let handle = unsafe { SharedBinHandle::retain_from_raw(shared) };
            let p = alloc_procbin(self, handle, byte_offset).as_raw();
            return AnyValue::heap_ptr(p, ValueKind::PROCBIN);
        }
        // Owned because `alloc_bitstring` takes `&mut self`; the buffer is
        // off-heap and immovable, so the read itself is safe.
        let owned = unsafe { from_raw_parts(buf_ptr.add(byte_offset as usize), suffix_bytes) }.to_vec();
        self.alloc_bitstring(&owned, buf_bits - byte_offset * 8)
    }

    /// Denotation, layout header, code pointer, then captures and their kind bytes.
    pub fn alloc_closure_slots(
        &mut self,
        denotation: crate::any_value::ClosureDenotationId,
        arity: u16,
        captured_count: usize,
        halt_kind: u16,
    ) -> u64 {
        assert!(
            captured_count <= CLOSURE_FLAGS_CAPTURED_MASK as usize,
            "closure captured count overflow"
        );
        let total = closure_size_for_count(captured_count);
        let p = self.alloc_kind(HeapAllocKind::Closure, total);
        unsafe {
            write(p as *mut u32, denotation.as_u32());
            write(
                p.add(4) as *mut u32,
                closure_header_word(captured_count as u16, halt_kind, arity),
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
        denotation: crate::any_value::ClosureDenotationId,
        arity: u16,
        captured_count: usize,
        halt_kind: u16,
        fn_ptr: u64,
        captures: &[AnyValue],
    ) -> u64 {
        assert!(captures.len() <= captured_count, "too many closure captures");
        let bits = self.alloc_closure_slots(denotation, arity, captured_count, halt_kind);
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
    /// The caller exclusively owns the live, unpublished closure allocation at
    /// `closure_addr`, and `idx` is an allocated capture slot. `value` must be a
    /// published immutable finite acyclic term with no path to this closure.
    pub unsafe fn write_closure_capture_value(&mut self, closure_addr: *mut u8, idx: usize, value: AnyValue) {
        unsafe { closure_capture_set(closure_addr, idx, value) };
    }

    /// # Safety
    /// The caller exclusively owns this live, unpublished closure, and `idx` is
    /// an allocated capture slot. Captures must be published immutable finite
    /// acyclic terms and cannot reach the closure being built.
    pub unsafe fn write_closure_capture_ref(
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

    /// Initialize an unpublished Struct's generic payload slot.
    ///
    /// # Safety
    /// The caller exclusively owns the unpublished object. The written value
    /// must be a published finite immutable term, with no path back to this object.
    /// Collector tests may construct non-language graphs only while keeping them
    /// outside all runtime term operations.
    pub unsafe fn write_field_slot(&mut self, obj: *mut u8, field_offset: u32, value: AnyValue) {
        self.write_struct_field_value(obj, field_offset, value);
    }

    /// # Safety
    /// The same unpublished finite-term contract as `write_field_slot` applies.
    pub unsafe fn write_struct_field_ref(
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

    pub fn mark_published_ref_aliased(&mut self, value: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        self.share_list_spine(value)?;
        Ok(value)
    }

    /// An aliased cell certifies an entirely shared tail. Publication marks a
    /// closed spine atomically, and shared cells cannot subsequently relink.
    /// The count measures newly protected cells without retaining heap state.
    pub(super) fn share_list_spine(&mut self, value: AnyValueRef) -> Result<usize, AnyValueRefError> {
        if value.tag() != ValueKind::LIST || value.is_empty_list() {
            return Ok(0);
        }

        Ok(unsafe { ListCons::share_spine(value.list_addr()?) })
    }

    /// Retain identical immutable contents without allocation. Changed contents
    /// require construction-owned rewrite permission and an unaliased source;
    /// otherwise allocate a fresh cell.
    ///
    /// Return contract: in-place reuse returns the original `list` ref;
    /// fallback allocation returns a distinct freshly-allocated cons ref.
    /// Callers that need to count reuse vs fallback should interpret the
    /// result through that identity contract rather than through a parallel
    /// outcome channel.
    pub fn reuse_or_alloc_list_cons_raw_kind(
        &mut self,
        list: AnyValueRef,
        head_raw: u64,
        head_kind: ValueKind,
        tail: AnyValueRef,
        may_rewrite: bool,
    ) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = nonempty_list_addr(list)?;
        let tail_bits = list_tail_bits_from_ref(tail)?;
        let cons = unsafe { &mut *(addr as *mut ListCons) };
        if cons.head_raw_kind() == (head_raw, head_kind) && cons.tail_bits() == tail_bits {
            return Ok(list);
        }
        self.publish_contained_parts(head_raw, head_kind);
        let cons = unsafe { &mut *(addr as *mut ListCons) };
        if may_rewrite && cons.rewrite_if_unaliased(head_raw, head_kind, tail_bits) {
            return Ok(list);
        }
        let fresh = self.alloc_list_cons_storage(head_raw, head_kind, tail_bits);
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
        Ok(self
            .map_key_position(addr, AnyValue::from_ref(key)?)
            .ok()
            .map(|index| unsafe { map_entry_refs(addr, index).1 }))
    }

    pub fn read_map_value_for_any_key(
        &self,
        map: AnyValueRef,
        key: AnyValue,
    ) -> Result<Option<AnyValueRef>, AnyValueRefError> {
        let addr = map.map_addr()?;
        Ok(self
            .map_key_position(addr, key)
            .ok()
            .map(|index| unsafe { map_entry_refs(addr, index).1 }))
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
                .unwrap_or_else(|| {
                    panic!(
                        "schema {} has no field named {}",
                        schema.identity.display_name(),
                        field_name
                    )
                })
                .offset
        };
        self.read_struct_field_ref(obj, field_offset)
    }

    pub fn read_closure_capture_ref(&self, closure: AnyValueRef, idx: usize) -> Result<AnyValueRef, AnyValueRefError> {
        closure_capture_ref(closure, idx)
    }

    /// Register a schema in this heap's registry, returning its id. Codegen
    /// uses this to register tuple-arity / record schemas at JIT
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
        //   GROW   — this GC fired after the heap crossed its pressure
        //            threshold, or after allocation abandoned a block and grew
        //            mid-quantum. The heap can't hold the allocation rate;
        //            refitting to 2x *live* would just thrash. Size to hold
        //            this cycle's realized footprint (live + garbage since the
        //            last GC), doubled for headroom, jumping as many classes
        //            as needed and never less than one class up.
        //   SHRINK — live has fallen to <=25% of the heap; refit to ~50%.
        //   KEEP   — live sits in the 25%–75% dead zone; hold the current size.
        let occupied_before_gc = self.bytes_used().saturating_sub(fragment_bytes);
        let was_pressured = !self.abandoned_blocks.is_empty() || occupied_before_gc >= self.gc_threshold_bytes;
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
