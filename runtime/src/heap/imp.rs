//! impl Heap — the giant impl block + Drop.

use super::block_pool::{Block, SIZE_TABLE, next_block_capacity, pick_block_capacity, pool_alloc, round_up_16};
use super::gc::{
    CopiedObject, FromSpace, cheney_trace_closure, cheney_trace_list, cheney_trace_map, cheney_trace_resource,
    cheney_trace_struct, forward_any_value_ref_root, forward_heap_value,
};
use super::ref_io::{
    any_value_ref_from_storage, list_tail_bits_from_ref, ptr_in_ranges, reject_scalar_ref_write,
    write_any_value_to_storage,
};
use super::schema::{Schema, SchemaRegistry};
use super::stats::GcStats;
use super::{Heap, HeapAllocKind, HeapAllocStats, MapLayout, SHARED_BIN_THRESHOLD_BYTES};
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, CLOSURE_FLAGS_CAPTURED_MASK, ListCons, MapDestinationKind,
    STRUCT_PAYLOAD_OFFSET, ValueKind, bitstring_header_word, bitstring_size_for_bit_len, closure_addr_from_tagged,
    closure_capture_kind_slot, closure_capture_raw_slot, closure_capture_set, closure_capture_value,
    closure_header_word, closure_header_write, closure_size_for_count, heap_object_word, list_addr_from_tagged,
    map_addr_from_tagged, map_count, map_destination_header_word, map_destination_state, map_entry, map_header_word,
    map_keys_ptr, map_pack_tag, map_size_for_count, map_tag_bytes_len, map_tag_ptr, map_values_ptr,
    struct_field_kind_slot, struct_field_raw_slot, struct_header_word, struct_schema_id, struct_size_for_payload,
};
use crate::procbin::{
    DeadResource, SharedBin, SharedBinHandle, alloc_procbin, mso_drop_all, mso_sweep, mso_unreached_closures,
};
use crate::process::Node;
use crate::term::{NumericMode, TermComparator};
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::mem::size_of;
use std::ptr::{copy_nonoverlapping, read, write, write_bytes};
use std::rc::Rc;
use std::slice::from_raw_parts;

// Pure reads that need no heap state. Reading a list head/tail or a
// closure capture is a dereference of the self-describing value pointer, so these
// are free functions (the `Heap::read_*` methods below delegate). BIFs call them
// directly, with no `current_process()` and no process argument — which is also
// why the receive matcher can project list/closure shapes without a process.

/// Copy `count` published entries from the map at `from` into the
/// unpublished allocation at `to`, which has room for exactly that many.
unsafe fn copy_map_slots(from: *mut u8, to: *mut u8, count: usize) {
    unsafe {
        std::ptr::copy_nonoverlapping(map_tag_ptr(from), map_tag_ptr(to), map_tag_bytes_len(count));
        std::ptr::copy_nonoverlapping(map_keys_ptr(from, count), map_keys_ptr(to, count), count);
        std::ptr::copy_nonoverlapping(map_values_ptr(from, count), map_values_ptr(to, count), count);
    }
}

fn entries_map_ref(addr: *mut u8) -> AnyValueRef {
    AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("published map")
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
        let block_size = pick_block_capacity(capacity.max(SIZE_TABLE[0]));
        let block_start = pool_alloc(block_size);
        let block_end = unsafe { block_start.add(block_size) };
        Self {
            block_start,
            bump_top: block_start,
            block_end,
            block_size,
            live_baseline: 0,
            blocks: Vec::new(),
            gift: None,
            node,
            schemas,
            struct_maps: Default::default(),
            gc_run_count: 0,
            alloc_count: 0,
            alloc_stats: HeapAllocStats::default(),
            mso_head: 0,
            pending_dtors: VecDeque::new(),
        }
    }

    /// Whether a collection is due: the bytes allocated since the heap was
    /// last known to be all live have reached the larger of that live
    /// baseline and half the smallest tip. A collection sets the baseline to
    /// its survivors and a graft raises it by the gift's fill, so only the
    /// heap's own allocation counts, and a heap that holds N live bytes
    /// collects after allocating N more. A pure function of the heap's
    /// state, so a collection that reclaims the bytes answers the question by
    /// itself.
    pub fn should_gc(&self) -> bool {
        let allocated_since = self.bytes_used().saturating_sub(self.live_baseline);
        allocated_since >= self.live_baseline.max(SIZE_TABLE[0] / 2)
    }

    /// Bump-only allocator. Rounds `size` up to 16 and advances `bump_top`.
    /// On overflow, an object larger than the capacity one step above the tip
    /// is placed alone in a block sized for it, parked on `blocks` with the tip
    /// unchanged; any other object abandons the tip for a fresh tip one capacity
    /// step up. The next park-time Cheney copies what is live out of the
    /// parked blocks and releases them.
    pub fn alloc(&mut self, size: usize) -> *mut u8 {
        self.alloc_kind(HeapAllocKind::Other, size)
    }

    pub fn alloc_kind(&mut self, kind: HeapAllocKind, size: usize) -> *mut u8 {
        let size = round_up_16(size);
        assert!(size >= 16, "alloc must reserve at least one 16-byte object slot");
        self.alloc_stats.record(kind, size as u64);
        self.bump(size)
    }

    /// Place `size` bytes (already a multiple of 16) in the tip, or beyond it
    /// when the tip is full. Allocation and the collector's copies both
    /// place through here, so a copy overflows exactly as an allocation does.
    pub(super) fn bump(&mut self, size: usize) -> *mut u8 {
        debug_assert!(
            size >= 16 && size.is_multiple_of(16),
            "placements are whole 16-byte slots"
        );
        let new_top = unsafe { self.bump_top.add(size) };
        if new_top > self.block_end {
            if self.parks_alone(size) {
                return self.alloc_parked(size);
            }
            self.climb_tip();
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        p
    }

    /// Whether an object of `size` bytes is huge: larger than the capacity one
    /// step above the tip. Such an object gets a block of its own beside the
    /// tip; anything smaller moves the tip up a step and lands in it.
    fn parks_alone(&self, size: usize) -> bool {
        size > next_block_capacity(self.block_size)
    }

    /// Place a huge object at the start of a block sized for it and park the
    /// block on `blocks`, full. The tip is untouched, so the allocations after
    /// it keep filling the block they were filling.
    ///
    /// A gift window never reaches this: its copy allocates exactly the
    /// measured bytes into a block of that size, and the object is part of them.
    fn alloc_parked(&mut self, size: usize) -> *mut u8 {
        assert!(
            self.gift.is_none(),
            "a huge object was allocated inside a gift window: the measure and the copy disagree"
        );
        let capacity = pick_block_capacity(size);
        let start = pool_alloc(capacity);
        self.blocks.push(Block {
            start,
            top: unsafe { start.add(size) },
            capacity,
        });
        self.alloc_count += 1;
        start
    }

    /// Park the tip and install a fresh tip one capacity step above it.
    fn climb_tip(&mut self) {
        let capacity = next_block_capacity(self.block_size);
        self.blocks.push(self.current_block());
        let start = pool_alloc(capacity);
        self.install_block(Block {
            start,
            top: start,
            capacity,
        });
    }

    /// The block being bumped into, with its fill so far.
    pub(super) fn current_block(&self) -> Block {
        Block {
            start: self.block_start,
            top: self.bump_top,
            capacity: self.block_size,
        }
    }

    pub(super) fn install_block(&mut self, block: Block) {
        self.block_start = block.start;
        self.bump_top = block.top;
        self.block_end = block.end();
        self.block_size = block.capacity;
    }

    pub fn alloc_stats_snapshot(&self) -> HeapAllocStats {
        self.alloc_stats
    }

    pub fn reset_alloc_stats(&mut self) {
        self.alloc_stats = HeapAllocStats::default();
    }

    pub fn record_external_alloc(&mut self, kind: HeapAllocKind, bytes: usize) {
        let bytes = round_up_16(bytes) as u64;
        self.alloc_stats.record(kind, bytes);
    }

    pub fn alloc_struct(&mut self, schema_id: u32) -> *mut u8 {
        let payload_size = self.schemas.borrow().get(schema_id).allocation_payload_size();
        let size = struct_size_for_payload(payload_size);
        let p = self.alloc_struct_unwritten(schema_id, size);
        unsafe { write_bytes(p.add(STRUCT_PAYLOAD_OFFSET), 0, size - STRUCT_PAYLOAD_OFFSET) };
        p
    }

    /// A struct of `size` bytes whose header names `schema_id` and whose
    /// payload is not yet written. The caller stores every slot and kind byte
    /// before the object can be read. A collection only runs between quanta,
    /// so one cannot see the object in between.
    pub fn alloc_struct_unwritten(&mut self, schema_id: u32, size: usize) -> *mut u8 {
        debug_assert_eq!(
            size,
            struct_size_for_payload(self.schemas.borrow().get(schema_id).allocation_payload_size()),
            "the size is the schema's"
        );
        let p = self.alloc_kind(HeapAllocKind::Struct, size);
        unsafe { write(p as *mut u64, struct_header_word(schema_id)) };
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

    pub fn contains_heap_addr(&self, p: *mut u8) -> bool {
        ptr_in_ranges(p, self.block_ranges())
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
            write(p as *mut u64, map_header_word(count));
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

    /// An unpublished destination with room for `extra` entries, which freezes
    /// into a new map.
    pub fn alloc_map_destination(&mut self, extra: usize) -> u64 {
        let p = self.alloc_kind(HeapAllocKind::Map, map_size_for_count(extra));
        unsafe {
            write(
                p as *mut u64,
                map_destination_header_word(extra, 0, MapDestinationKind::Build),
            );
            write_bytes(map_tag_ptr(p), 0, map_tag_bytes_len(extra));
        }
        heap_object_word(p, ValueKind::MAP)
    }

    /// An unpublished destination holding `base`'s entries, in either of its
    /// layouts, whose puts may only replace them.
    pub fn alloc_map_update(&mut self, base: AnyValueRef) -> u64 {
        let layout = self.expect_map_layout(base, "map update base");
        let count = self.map_view_count(layout);
        let p = self.alloc_kind(HeapAllocKind::Map, map_size_for_count(count));
        let struct_base = match layout {
            MapLayout::Entries(base) => {
                unsafe { copy_map_slots(base, p, count) };
                false
            }
            MapLayout::Struct { .. } => {
                let entries = self.map_view_entries(layout);
                self.write_ordered_map_entries(p, count, entries.into_iter());
                true
            }
        };
        let kind = MapDestinationKind::Update {
            missed: false,
            struct_base,
        };
        unsafe { write(p as *mut u64, map_destination_header_word(count, count, kind)) };
        heap_object_word(p, ValueKind::MAP)
    }

    /// Store `key` and `value` in an exclusively owned, unpublished map
    /// destination. A build destination appends; an update destination
    /// replaces the value under `key`, and when it has no such key it stores
    /// nothing and remembers the miss for its freeze.
    ///
    /// # Safety
    /// `key` and `value` must be finite immutable terms. Neither may reach this
    /// or any other unfinished destination. Freezing publishes the stored fields.
    pub unsafe fn map_destination_put(&mut self, dest_bits: u64, key: AnyValue, value: AnyValue) {
        let dest = map_addr_from_tagged(dest_bits).expect("map_destination_put dest");
        let (count, filled, kind) = unsafe { map_destination_state(dest) };
        assert_ne!(key.kind(), ValueKind::NULL, "unpublished map key");
        let slot = match kind {
            MapDestinationKind::Build => {
                assert!(filled < count, "map destination has no free entry slot");
                filled
            }
            MapDestinationKind::Update { struct_base, .. } => match self.map_key_position(dest, key) {
                Ok(index) => index,
                Err(_) => {
                    let missed = MapDestinationKind::Update {
                        missed: true,
                        struct_base,
                    };
                    unsafe { write(dest as *mut u64, map_destination_header_word(count, filled, missed)) };
                    return;
                }
            },
        };
        unsafe {
            let tag_p = map_tag_ptr(dest);
            let keys = map_keys_ptr(dest, count);
            let values = map_values_ptr(dest, count);
            write(tag_p.add(slot), map_pack_tag(key.kind(), value.kind()));
            write_any_value_to_storage(keys.add(slot), None, key);
            write_any_value_to_storage(values.add(slot), None, value);
            if kind == MapDestinationKind::Build {
                write(dest as *mut u64, map_destination_header_word(count, filled + 1, kind));
            }
        }
    }

    /// Publish a destination. An update that missed a key answers `None`:
    /// `%{map | k: v}` with no `k` in `map` makes no map, and its caller
    /// raises `KeyError`. An update's puts only replace, so its entries are
    /// already in order and it publishes in place; one whose base was a struct
    /// comes out as the struct its keys name, so updating a struct keeps it
    /// one.
    pub fn map_destination_freeze(&mut self, dest_bits: u64) -> Option<AnyValueRef> {
        let dest = map_addr_from_tagged(dest_bits).expect("map destination");
        let (_, filled, kind) = unsafe { map_destination_state(dest) };
        match kind {
            MapDestinationKind::Build => {
                let mut entries: Vec<_> = (0..filled).map(|i| unsafe { map_entry(dest, i) }).collect();
                self.normalize_map_entries(&mut entries);
                self.write_ordered_map_entries(dest, entries.len(), entries.into_iter());
            }
            MapDestinationKind::Update { .. } => {
                for i in 0..filled {
                    let (key, value) = unsafe { map_entry(dest, i) };
                    self.publish_contained_parts(key.raw(), key.kind());
                    self.publish_contained_parts(value.raw(), value.kind());
                }
                unsafe { write(dest as *mut u64, map_header_word(filled)) };
            }
        }
        match kind {
            MapDestinationKind::Update { missed: true, .. } => None,
            MapDestinationKind::Update { struct_base: true, .. } => {
                Some(self.struct_of_entries(dest).unwrap_or_else(|| entries_map_ref(dest)))
            }
            _ => Some(entries_map_ref(dest)),
        }
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
        let layout = self.map_layout(map).ok_or(AnyValueRefError::ExpectedTag {
            expected: ValueKind::MAP,
            found: map.tag(),
        })?;
        Ok(self.map_view_put(layout, AnyValue::from_ref(key)?, AnyValue::from_ref(value)?))
    }

    /// An absent deletion borrows the original map without allocating.
    pub fn map_delete_ref(&mut self, map: AnyValueRef, key: AnyValueRef) -> Result<AnyValueRef, AnyValueRefError> {
        Ok(self.map_view_delete(map, AnyValue::from_ref(key)?))
    }

    /// `map` with `key` bound to `value`; a map of that one entry when `map`
    /// is the null ref a fresh literal starts from.
    pub fn map_put_slot(&mut self, map: AnyValueRef, key: AnyValue, value: AnyValue) -> AnyValueRef {
        if map.tag() == ValueKind::NULL {
            let bits = self.alloc_ordered_map_entries(std::iter::once((key, value)));
            return AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(bits).expect("new map"))
                .expect("map ref");
        }
        let layout = self.expect_map_layout(map, "map put");
        self.map_view_put(layout, key, value)
    }

    pub(super) fn map_put_entry(&mut self, addr: *mut u8, key: AnyValue, value: AnyValue) -> u64 {
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

    pub(super) fn map_key_position(&self, addr: *mut u8, key: AnyValue) -> Result<usize, usize> {
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
    /// Payloads larger than `SHARED_BIN_THRESHOLD_BYTES` route
    /// through the shared zone: a SharedBin is allocated off-heap and the
    /// per-process heap gets a tagged ProcBin stub referencing
    /// it. Render and bit-match dispatch via
    /// `bitstring_bit_len` / `bitstring_byte_ptr`.
    ///
    /// This always COPIES `bytes`. To view an existing shared buffer
    /// without copying it, use `alloc_bitstring_suffix`.
    ///
    /// Returns the VALUE, kind included. The storage choice is
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
        // Reserve at least 1 byte past the payload for the
        // invisible trailing NUL. The pad-zeroing below guarantees it reads
        // as 0; bytes_len / bit_len are unchanged.
        let total = bitstring_size_for_bit_len(bit_len);
        let p = self.alloc_kind(HeapAllocKind::Bitstring, total);
        unsafe {
            write(p as *mut u64, bitstring_header_word(bit_len));
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
    /// Above `SHARED_BIN_THRESHOLD_BYTES` the suffix SHARES the
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
        let suffix = unsafe { from_raw_parts(buf_ptr.add(byte_offset as usize), suffix_bytes) };
        self.alloc_bitstring(suffix, buf_bits - byte_offset * 8)
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
            closure_header_write(
                p,
                closure_header_word(denotation, captured_count as u16, halt_kind, arity),
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

    /// Store `value` as the field of `object` whose raw word is at
    /// `slot_offset` and whose kind byte is at `kind_offset`, both from the
    /// start of the object. A list becomes shared, since the struct now holds
    /// it too.
    ///
    /// # Safety
    /// `object` is a struct under construction and the offsets are one
    /// field's, by its `SlotLayout`.
    pub unsafe fn store_struct_field_ref(
        &mut self,
        object: *mut u8,
        slot_offset: usize,
        kind_offset: usize,
        value: AnyValueRef,
    ) -> Result<(), AnyValueRefError> {
        let raw = value.storage_raw()?;
        self.share_list_spine(value)?;
        unsafe {
            write(object.add(slot_offset).cast::<u64>(), raw);
            write(object.add(kind_offset), value.tag().tag());
        }
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
        &mut self,
        map: AnyValueRef,
        key: AnyValueRef,
    ) -> Result<Option<AnyValueRef>, AnyValueRefError> {
        self.read_map_value_for_any_key(map, AnyValue::from_ref(key)?)
    }

    pub fn read_map_value_for_any_key(
        &mut self,
        map: AnyValueRef,
        key: AnyValue,
    ) -> Result<Option<AnyValueRef>, AnyValueRefError> {
        let layout = self.map_layout(map).ok_or(AnyValueRefError::ExpectedTag {
            expected: ValueKind::MAP,
            found: map.tag(),
        })?;
        Ok(self.map_view_get(layout, key))
    }

    pub fn read_struct_field_ref(&self, obj: AnyValueRef, field_offset: u32) -> Result<AnyValueRef, AnyValueRefError> {
        let addr = obj.struct_addr()?;
        let schema_id = unsafe { struct_schema_id(addr as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        let raw_slot = unsafe { struct_field_raw_slot(addr as *const u8, field_offset) };
        let kind = unsafe { read(struct_field_kind_slot(addr as *const u8, kind_offset)) };
        let field =
            any_value_ref_from_storage(raw_slot as *const u64, ValueKind::new(kind).expect("struct field kind"))?;
        // A scalar field's ref points into the struct's own payload, so it is
        // read-only data exactly when the struct is. A heap field's ref is its
        // stored address and already says what it names.
        Ok(if obj.is_literal() && field.tag().is_scalar() {
            field.literal()
        } else {
            field
        })
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

    /// Total allocations made on this heap (since last GC). Each Cheney
    /// pass resets this to the surviving-object count after the copy.
    pub fn live_count(&self) -> usize {
        self.alloc_count as usize
    }

    /// Bytes written into the heap since the last collection, which is also
    /// the most a collection can copy: the tip's fill plus every parked
    /// block's fill. Blocks count by fill, never by capacity: a gift's block
    /// is mostly empty, and an abandoned block's tail was never written.
    pub fn bytes_used(&self) -> usize {
        self.current_block().fill() + self.blocks.iter().map(Block::fill).sum::<usize>()
    }

    /// The address range of the tip, of the tip set aside by an open gift
    /// window, and of every parked block.
    pub(super) fn block_ranges(&self) -> impl Iterator<Item = (*mut u8, *mut u8)> + '_ {
        let saved_tip = self.gift.as_ref().map(|window| window.saved_tip);
        std::iter::once((self.block_start, self.block_end))
            .chain(saved_tip.map(|block| (block.start, block.end())))
            .chain(self.blocks.iter().map(|block| (block.start, block.end())))
    }

    pub fn bytes_remaining_in_block(&self) -> usize {
        unsafe { self.block_end.offset_from(self.bump_top) as usize }
    }

    /// The one collection entry: a Cheney copy of everything `roots` reaches
    /// into a fresh tip, after which the old blocks are released.
    ///
    /// The fresh tip's capacity is a guess, the live baseline (the smallest
    /// tip on an empty baseline). Every copy is placed by the ordinary bump
    /// path, so a copy that outgrows the guess parks the tip and climbs the
    /// table, and a huge object parks alone; a wrong guess costs a block,
    /// never correctness. The scan reads a worklist of copied objects, not an
    /// address, so to-space needs no contiguity.
    ///
    /// Every slot of `roots` holds its forwarded value on return. A slot
    /// that is not a pointer into this heap's from-space (a scalar immediate,
    /// the empty list, a static closure or halt continuation) is
    /// left as it was; a scalar box in from-space is copied without tracing
    /// its payload.
    ///
    /// The caller passes every reference it holds into this heap. For a
    /// `Process` that is `Process::collect`, which assembles the runnable
    /// closure, the park record, the mailbox and the caller's transient
    /// values into one slice. Gifts still waiting in a delivery in-queue are
    /// not roots: their blocks join the from-space only when grafted, and
    /// every reference inside a gift points into its own segment.
    ///
    /// The heap must not have a gift window open.
    pub fn collect(&mut self, roots: &mut [AnyValueRef]) -> GcStats {
        assert!(
            self.gift.is_none(),
            "a gift window is open; the heap collects only between end_gift and the next begin_gift"
        );
        // From-space is every block the heap owns before to-space is installed.
        let from_space = FromSpace::of(self);
        let from_block_count = self.block_ranges().count();
        let from_space_capacity_bytes: usize = self
            .block_ranges()
            .map(|(start, end)| unsafe { end.offset_from(start) as usize })
            .sum();

        let from_tip = self.current_block();
        let from_blocks = std::mem::take(&mut self.blocks);
        let to_capacity = pick_block_capacity(self.live_baseline.max(SIZE_TABLE[0]));
        let to_start = pool_alloc(to_capacity);
        self.install_block(Block {
            start: to_start,
            top: to_start,
            capacity: to_capacity,
        });
        self.alloc_count = 0;
        let mut copied_objects: Vec<CopiedObject> = Vec::new();
        let mut stats = GcStats {
            from_space_capacity_bytes: from_space_capacity_bytes as u64,
            blocks_released: from_block_count as u64,
            ..GcStats::default()
        };
        let schemas_handle = self.schemas.clone();

        for value in roots.iter_mut() {
            forward_any_value_ref_root(
                value,
                &from_space,
                self,
                &schemas_handle.borrow(),
                &mut copied_objects,
                &mut stats,
            );
        }

        let schemas = schemas_handle.borrow();
        let mut scan_idx = 0usize;
        cheney_scan(
            &mut scan_idx,
            &from_space,
            self,
            &schemas,
            &mut copied_objects,
            &mut stats,
        );

        // A resource stub nothing reached is dead, but its destructor closure
        // still has to run. Forward each such closure, with everything it
        // captures, so it outlives the from-space. A stub a closure captures
        // is reached by this and survives until a later collection.
        let unreached = mso_unreached_closures(self);
        let mut dead_closures: HashMap<usize, AnyValue> = HashMap::with_capacity(unreached.len());
        for (stub, closure) in unreached {
            let forwarded = forward_heap_value(closure, &from_space, self, &schemas, &mut copied_objects, &mut stats);
            dead_closures.insert(stub, forwarded);
        }
        cheney_scan(
            &mut scan_idx,
            &from_space,
            self,
            &schemas,
            &mut copied_objects,
            &mut stats,
        );
        drop(schemas);

        // The MSO sweep walks the intrusive chain: survivors are rewritten to
        // their to-space copies and dead entries drop their off-heap
        // reference. It must run before the from-space is released because
        // it reads from-space stubs (their `mso_next` link, which Cheney never
        // overwrites).
        let dead = mso_sweep(self, |stub| {
            *dead_closures
                .get(&(stub.as_raw() as usize))
                .expect("a dead unclaimed resource stub had its closure forwarded")
        });

        // Release old from-space (current + parked blocks): pooled capacities
        // return to the pool (§6.6), exact blocks to the system allocator.
        from_tip.release();
        for block in from_blocks {
            block.release();
        }

        let live_count = copied_objects.len() as u64;
        self.alloc_count = live_count;
        self.gc_run_count += 1;
        self.live_baseline = stats.copied_bytes as usize;
        stats.live_objects = live_count;
        stats.live_bytes = self.live_baseline as u64;
        stats.blocks_after = 1 + self.blocks.len() as u64;
        self.queue_dead_resources(dead);
        stats
    }

    /// Release every stub on the MSO chain as a process exit does: nothing is
    /// live, so every resource whose last reference this heap held queues its
    /// destructor on `pending_dtors`. Allocates no to-space.
    pub fn release_resources_at_exit(&mut self) {
        let dead = mso_sweep(self, |stub| stub.closure_value());
        self.queue_dead_resources(dead);
    }

    /// Queue each dead resource's closure and a boxed payload for the
    /// scheduler to dispatch.
    fn queue_dead_resources(&mut self, dead: Vec<DeadResource>) {
        for DeadResource { closure, payload } in dead {
            let payload_ref = self.box_any_value_ref(AnyValue::int(payload as i64)).raw_word();
            self.pending_dtors.push_back((closure, payload_ref));
        }
    }
}

/// Scan the to-space objects copied since `scan_idx`, forwarding what each
/// one references, until the scan catches up with the copy frontier.
fn cheney_scan(
    scan_idx: &mut usize,
    from_space: &FromSpace,
    heap: &mut Heap,
    schemas: &SchemaRegistry,
    copied_objects: &mut Vec<CopiedObject>,
    stats: &mut GcStats,
) {
    while *scan_idx < copied_objects.len() {
        let copied = copied_objects[*scan_idx];
        *scan_idx += 1;
        match copied.kind {
            ValueKind::LIST => cheney_trace_list(
                copied.ptr as *mut ListCons,
                from_space,
                heap,
                schemas,
                copied_objects,
                stats,
            ),
            ValueKind::MAP => cheney_trace_map(copied.ptr, from_space, heap, schemas, copied_objects, stats),
            ValueKind::CLOSURE => cheney_trace_closure(copied.ptr, from_space, heap, schemas, copied_objects, stats),
            ValueKind::STRUCT => cheney_trace_struct(copied.ptr, from_space, heap, schemas, copied_objects, stats),
            ValueKind::BITSTRING | ValueKind::PROCBIN => {}
            ValueKind::RESOURCE => cheney_trace_resource(copied.ptr, from_space, heap, schemas, copied_objects, stats),
            kind => panic!("Cheney scan: invalid copied object kind {kind:?}"),
        }
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
        // release every SharedBin held via the intrusive MSO
        // chain. Order matters: must run before pool_free below, since
        // mso_drop_all walks ProcBin payloads in the from-space blocks.
        mso_drop_all(self);
        // Release blocks: pooled capacities go back to the pool (§6.6) so the
        // next spawn pulls from it with no per-spawn malloc; exact blocks go
        // to the system allocator. A tip set aside by an unfinished gift
        // window goes back too.
        self.current_block().release();
        if let Some(window) = self.gift.take() {
            window.saved_tip.release();
        }
        for block in self.blocks.drain(..) {
            block.release();
        }
    }
}
