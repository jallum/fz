//! impl Heap — the giant impl block + Drop.

use super::block_pool::{Block, SIZE_TABLE, next_block_capacity, pick_block_capacity, pool_alloc, round_up_16};
use super::gc::{
    CopiedObject, FromSpace, cheney_trace_binview, cheney_trace_closure, cheney_trace_list, cheney_trace_map,
    cheney_trace_struct, forward_any_value_ref_root,
};
use super::map_view::destination_layout;
use super::ref_io::{
    any_value_ref_from_storage, list_tail_bits_from_ref, ptr_in_ranges, reject_scalar_ref_write,
    write_any_value_to_storage,
};
use super::schema::{Schema, SchemaRegistry};
use super::stats::{GcStats, Generation, StubCounts, StubSite};
use super::{BinaryBudget, Heap, HeapAllocKind, HeapAllocStats, MapLayout, SHARED_BIN_THRESHOLD_BYTES};
use crate::alloc_site::RuntimeAllocSite;
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefError, CLOSURE_FLAGS_CAPTURED_MASK, ListCons, MAP_FLAT_MAX, MapDestinationKind,
    STRUCT_PAYLOAD_OFFSET, SlotLayout, ValueKind, bitstring_header_word, bitstring_size_for_bit_len,
    closure_addr_from_tagged, closure_capture_kind_slot, closure_capture_raw_slot, closure_capture_set,
    closure_capture_value, closure_header_word, closure_header_write, closure_size_for_count, heap_object_word,
    list_addr_from_tagged, map_addr_from_tagged, map_count, map_destination_header_word, map_destination_state,
    map_entry, map_header_word, map_key, map_key_in_arrays, map_key_kind, map_keys_ptr, map_pack_tag,
    map_size_for_count, map_tag_bytes_len, map_tag_ptr, map_value_kind, map_values_ptr, share_struct,
    struct_field_kind_slot, struct_field_raw_slot, struct_header_word, struct_schema_id, struct_size_for_payload,
};
use crate::bits::{BinView, SharedBinHandle, alloc_buffer_view, alloc_view, shared_bin_append};
use crate::off_heap;
use crate::process::Node;
use crate::term::TermComparator;
use std::cell::RefCell;
use std::collections::VecDeque;
use std::mem::{MaybeUninit, size_of};
use std::ptr::{copy, copy_nonoverlapping, read, write, write_bytes};
use std::rc::Rc;
use std::slice::{from_raw_parts, from_raw_parts_mut};

/// A major collection runs once the old bytes exceed this multiple of what the
/// last major collection left. A larger multiple copies the old generation less
/// often and lets more dead old data stay in memory: up to this multiple minus
/// one times the live old bytes. Two holds at most as much dead data as live.
pub(super) const MAJOR_GROWTH_FACTOR: usize = 2;

/// Map entry lists up to this length are normalized without a heap vector.
/// It is the longest the standard stable sort orders without allocating.
pub(super) const MAP_STACK_ENTRIES: usize = 20;

// Pure reads that need no heap state. Reading a list head/tail or a
// closure capture is a dereference of the self-describing value pointer, so these
// are free functions (the `Heap::read_*` methods below delegate). BIFs call them
// directly, with no `current_process()` and no process argument — which is also
// why the receive matcher can project list/closure shapes without a process.

fn entries_map_ref(addr: *mut u8) -> AnyValueRef {
    AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("published map")
}

fn map_bits_ref(bits: u64) -> AnyValueRef {
    entries_map_ref(map_addr_from_tagged(bits).expect("published map"))
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
            old_after_last_major: 0,
            last_minor_copied_bytes: 0,
            overflow_step: SIZE_TABLE[0],
            young_blocks: Vec::new(),
            old_blocks: Vec::new(),
            gift: None,
            node,
            schemas,
            struct_maps: Default::default(),
            gc_run_count: 0,
            alloc_count: 0,
            old_objects: 0,
            alloc_stats: HeapAllocStats::default(),
            off_heap_head: 0,
            off_heap_old_head: 0,
            binary_budget: BinaryBudget::new(),
            stubs_made: StubCounts::default(),
            binrefs_made: StubCounts::default(),
            pending_dtors: VecDeque::new(),
        }
    }

    /// Whether a collection is due: the young bytes, those allocated since
    /// the last collection, have reached the larger of the old bytes and half
    /// the smallest tip. A collection sets the old bytes to what it keeps and a
    /// graft raises them by the gift's fill, so only the heap's own allocation
    /// counts, and a heap that holds N live bytes collects after allocating N
    /// more. A pure function of the heap's state, so a collection that
    /// reclaims the bytes answers the question by itself.
    pub fn should_gc(&self) -> bool {
        self.young_bytes() >= self.collection_budget() || self.binary_budget.is_due()
    }

    /// The young bytes at which a collection is due: the young budget, and at
    /// least half the smallest tip.
    fn collection_budget(&self) -> usize {
        self.young_budget().max(SIZE_TABLE[0] / 2)
    }

    /// The young bytes the heap allocates before a collection is due: as many
    /// as it holds old, and never more than the largest pooled block. A larger
    /// young generation would be a block the system allocator makes and frees
    /// at every collection, and it keeps nothing more from being copied: what
    /// dies young is already dead well inside that many bytes.
    fn young_budget(&self) -> usize {
        self.live_baseline.min(SIZE_TABLE[SIZE_TABLE.len() - 1])
    }

    /// Bump-only allocator. Rounds `size` up to 16 and advances `bump_top`.
    /// On overflow, an object larger than the capacity one step above the tip
    /// is placed alone in a block sized for it, parked on `young_blocks` with the tip
    /// unchanged; any other object abandons the tip for a fresh tip one capacity
    /// step up. The next collection copies what is live out of the
    /// parked blocks and releases them.
    pub fn alloc(&mut self, size: usize) -> *mut u8 {
        self.alloc_at(RuntimeAllocSite::Other, size)
    }

    /// Place `size` bytes for the runtime function `site`.
    pub fn alloc_at(&mut self, site: RuntimeAllocSite, size: usize) -> *mut u8 {
        let size = round_up_16(size);
        assert!(size >= 16, "alloc must reserve at least one 16-byte object slot");
        self.alloc_stats.record(site.kind(), size as u64);
        self.node.runtime_allocs.record(site, size as u64);
        self.bump(size)
    }

    /// Place `size` bytes (already a multiple of 16) in the tip, or beyond it
    /// when the tip is full. The collector's copies place through
    /// `bump_to_space` instead.
    #[inline]
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
    /// block on `young_blocks`, full. The tip is untouched, so the allocations after
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
        self.young_blocks.push(Block {
            start,
            top: unsafe { start.add(size) },
            capacity,
        });
        self.alloc_count += 1;
        start
    }

    /// Park the tip and install a fresh tip one capacity step above it.
    fn climb_tip(&mut self) {
        self.park_tip_and_install(next_block_capacity(self.block_size));
    }

    /// Place `size` bytes (already a multiple of 16) for the collector's copy.
    /// A copy that outgrows its to-space block takes an overflow block sized
    /// for the overflow: the first is the smallest class, each later one the
    /// class above the last (`overflow_step`), and an object above the step
    /// parks alone. The to-space block's own size, which is a guess and may be
    /// huge, never sets the next block's size. Allocation outside a collection
    /// never comes here: it climbs from the tip it holds (`bump`).
    #[inline]
    pub(super) fn bump_to_space(&mut self, size: usize) -> *mut u8 {
        debug_assert!(
            size >= 16 && size.is_multiple_of(16),
            "placements are whole 16-byte slots"
        );
        let new_top = unsafe { self.bump_top.add(size) };
        if new_top > self.block_end {
            if size > self.overflow_step {
                return self.alloc_parked(size);
            }
            self.park_tip_and_install(self.overflow_step);
            self.overflow_step = next_block_capacity(self.overflow_step);
        }
        let p = self.bump_top;
        self.bump_top = unsafe { self.bump_top.add(size) };
        self.alloc_count += 1;
        p
    }

    /// Park the tip and install an empty tip of `capacity`.
    fn park_tip_and_install(&mut self, capacity: usize) {
        self.young_blocks.push(self.current_block());
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
        let p = self.alloc_at(RuntimeAllocSite::Struct, size);
        unsafe { write(p as *mut u64, struct_header_word(schema_id)) };
        p
    }

    /// An unpublished copy of the struct at `object`, whose fields `layout`
    /// places. A list the struct holds becomes shared, since the copy holds
    /// it too.
    ///
    /// # Safety
    /// `object` must be a published struct of `layout`'s field count.
    pub unsafe fn copy_struct(&mut self, object: *const u8, layout: SlotLayout) -> *mut u8 {
        let copy = self.alloc_struct_unwritten(unsafe { struct_schema_id(object) }, layout.size());
        unsafe {
            copy_nonoverlapping(
                object.add(STRUCT_PAYLOAD_OFFSET),
                copy.add(STRUCT_PAYLOAD_OFFSET),
                layout.payload_size(),
            );
        }
        for index in 0..layout.fields() {
            let raw = unsafe { read(object.add(SlotLayout::slot_offset(index)).cast::<u64>()) };
            let kind = unsafe { read(object.add(layout.kind_offset(index))) };
            self.publish_contained_parts(raw, ValueKind::new(kind).expect("struct field kind"));
        }
        copy
    }

    fn alloc_list_cons_value(&mut self, head: AnyValueRef, tail_bits: u64) -> u64 {
        self.mark_published_ref_aliased(head).expect("published list head");
        let p = self.alloc_at(RuntimeAllocSite::ListConsValue, 16);
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
        let p = self.alloc_at(RuntimeAllocSite::ListConsStorage, 16);
        unsafe {
            write(p as *mut ListCons, ListCons::new(head_raw, head_kind, tail_bits));
        }
        heap_object_word(p, ValueKind::LIST)
    }

    pub(super) fn publish_contained_parts(&mut self, raw: u64, kind: ValueKind) {
        if matches!(kind, ValueKind::LIST | ValueKind::STRUCT) && raw != 0 {
            let value = AnyValueRef::from_heap_object(kind, raw as *const u8).expect("contained value");
            self.mark_published_ref_aliased(value)
                .expect("published contained value");
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
                let slot = self.alloc_at(RuntimeAllocSite::ScalarBox, size_of::<u64>()) as *mut u64;
                unsafe {
                    write(slot, value as u64);
                }
                AnyValueRef::from_scalar_slot(ValueKind::INT, slot as *const u64).expect("int ref")
            }
            AnyValue::Opaque(ValueKind::PID, word) => AnyValueRef::pid(word).expect("a pid fits its ref"),
            AnyValue::Opaque(kind, word) => {
                let slot = self.alloc_at(RuntimeAllocSite::ScalarBox, size_of::<u64>()) as *mut u64;
                unsafe {
                    write(slot, word);
                }
                AnyValueRef::from_scalar_slot(kind, slot as *const u64).expect("opaque word ref")
            }
            AnyValue::Float(bits) => {
                let bits = AnyValue::float(f64::from_bits(bits)).raw();
                let slot = self.alloc_at(RuntimeAllocSite::ScalarBox, size_of::<u64>()) as *mut u64;
                unsafe {
                    write(slot, bits);
                }
                AnyValueRef::from_scalar_slot(ValueKind::FLOAT, slot as *const u64).expect("float ref")
            }
            AnyValue::Atom(atom_id) => AnyValueRef::atom(atom_id),
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
        self.publish_map_entries(entries.iter().map(|&(key, value)| {
            (
                AnyValue::from_ref(key).expect("map key"),
                AnyValue::from_ref(value).expect("map value"),
            )
        }))
    }

    pub fn alloc_map_slots(&mut self, entries: &[(AnyValue, AnyValue)]) -> u64 {
        self.publish_map_entries(entries.iter().copied())
    }

    /// Entries up to `MAP_STACK_ENTRIES` are normalized in a stack buffer; a
    /// larger list is collected once. The buffer stays within the length the
    /// standard stable sort handles without allocating.
    fn publish_map_entries(&mut self, entries: impl ExactSizeIterator<Item = (AnyValue, AnyValue)>) -> u64 {
        let len = entries.len();
        if len <= MAP_STACK_ENTRIES {
            let mut buffer = [(AnyValue::int(0), AnyValue::int(0)); MAP_STACK_ENTRIES];
            for (slot, entry) in buffer.iter_mut().zip(entries) {
                *slot = entry;
            }
            self.publish_normalized_map_entries(&mut buffer[..len])
        } else {
            let mut collected: Vec<_> = entries.collect();
            self.publish_normalized_map_entries(&mut collected)
        }
    }

    fn publish_normalized_map_entries(&mut self, entries: &mut [(AnyValue, AnyValue)]) -> u64 {
        let count = self.normalize_map_entries(entries);
        self.alloc_bulk_map_entries(&entries[..count])
    }

    /// Publish entries in key order with no key repeated, as a trie when there
    /// are more than `MAP_FLAT_MAX` of them and as a flat array otherwise.
    pub(super) fn alloc_bulk_map_entries(&mut self, entries: &[(AnyValue, AnyValue)]) -> u64 {
        if entries.len() > MAP_FLAT_MAX {
            self.alloc_trie(entries)
        } else {
            self.alloc_ordered_map_entries(entries.iter().copied())
        }
    }

    /// Sort the entries by strict structural key and merge equal keys, the
    /// last value winning. Answers how many leading entries remain.
    fn normalize_map_entries(&self, entries: &mut [(AnyValue, AnyValue)]) -> usize {
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        entries.sort_by(|a, b| comparator.key_order_of(a.0, b.0));
        let mut kept = 0;
        for index in 1..entries.len() {
            if comparator.key_order_of(entries[index].0, entries[kept].0).is_eq() {
                entries[kept].1 = entries[index].1;
            } else {
                kept += 1;
                entries[kept] = entries[index];
            }
        }
        if entries.is_empty() { 0 } else { kept + 1 }
    }

    /// Copy entries whose ordering is preserved by an immutable map operation.
    pub(super) fn alloc_ordered_map_entries(
        &mut self,
        entries: impl ExactSizeIterator<Item = (AnyValue, AnyValue)>,
    ) -> u64 {
        let count = entries.len();
        debug_assert!(count <= MAP_FLAT_MAX, "a flat map holds at most {MAP_FLAT_MAX} entries");
        let p = self.alloc_at(RuntimeAllocSite::OrderedMapEntries, map_size_for_count(count));
        unsafe { write(p as *mut u64, map_header_word(count)) };
        self.write_map_entries(p, count, entries);
        heap_object_word(p, ValueKind::MAP)
    }

    /// Write `count` entries, as the kind bytes, keys and values of the node at
    /// `p`, which has room for them and whose header is written already.
    pub(super) fn write_map_entries(
        &mut self,
        p: *mut u8,
        count: usize,
        entries: impl Iterator<Item = (AnyValue, AnyValue)>,
    ) {
        unsafe {
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
        let p = self.alloc_at(RuntimeAllocSite::MapDestination, map_size_for_count(extra));
        unsafe {
            write(
                p as *mut u64,
                map_destination_header_word(extra, 0, MapDestinationKind::Build),
            );
            write_bytes(map_tag_ptr(p), 0, map_tag_bytes_len(extra));
        }
        heap_object_word(p, ValueKind::MAP)
    }

    /// A destination holding `base`'s entries, whose puts may only replace
    /// them. A struct's destination is a copy of the struct, so replacing its
    /// fields keeps it that struct. A trie is its own destination: each put
    /// copies one path of it and leaves the map it was given as it was.
    pub fn alloc_map_update(&mut self, base: AnyValueRef) -> u64 {
        match self.expect_map_layout(base, "map update base") {
            MapLayout::Struct { object, schema_id } => self.alloc_struct_update(object, schema_id),
            MapLayout::Trie(root) => heap_object_word(root, ValueKind::MAP),
            entries @ MapLayout::Entries(_) => self.alloc_entries_update(entries),
        }
    }

    /// An unpublished entries destination holding the entries of `base`, in
    /// key order: a flat map is copied as it is, a struct is read in key order.
    pub(super) fn alloc_entries_update(&mut self, base: MapLayout) -> u64 {
        let count = self.map_view_count(base);
        let p = match base {
            MapLayout::Entries(base) => self.write_flat_map(base, Edit::NONE),
            MapLayout::Struct { .. } => {
                let entries = self.map_view_entries(base);
                map_addr_from_tagged(self.alloc_ordered_map_entries(entries.into_iter())).expect("new map")
            }
            MapLayout::Trie(_) => unreachable!("a trie is its own update destination"),
        };
        let header = map_destination_header_word(count, count, MapDestinationKind::Update);
        unsafe { write(p as *mut u64, header) };
        heap_object_word(p, ValueKind::MAP)
    }

    /// Store `key` and `value` in an exclusively owned, unpublished map
    /// destination, and answer the destination the next put or the freeze
    /// continues with. A build destination appends. An update destination
    /// replaces the value under `key`; when it has no such key the update has
    /// missed and there is no destination to continue with, which is `0`.
    ///
    /// # Safety
    /// `key` and `value` must be finite immutable terms. Neither may reach this
    /// or any other unfinished destination. Freezing publishes the stored fields.
    pub unsafe fn map_destination_put(&mut self, dest_bits: u64, key: AnyValue, value: AnyValue) -> u64 {
        assert_ne!(key.kind(), ValueKind::NULL, "unpublished map key");
        match destination_layout(dest_bits) {
            None => 0,
            Some(MapLayout::Struct { object, schema_id }) => self.struct_update_put(object, schema_id, key, value),
            Some(MapLayout::Entries(dest)) if unsafe { self.entries_destination_put(dest, key, value) } => dest_bits,
            Some(MapLayout::Entries(_)) => 0,
            Some(MapLayout::Trie(root)) => match self.find(root, key) {
                Some(_) => self.trie_put(root, key, value),
                None => 0,
            },
        }
    }

    /// Store one entry in the entries destination at `dest`: a build takes
    /// its next free slot, an update the slot already holding `key`. False
    /// when an update has no such key, and nothing is stored.
    unsafe fn entries_destination_put(&mut self, dest: *mut u8, key: AnyValue, value: AnyValue) -> bool {
        self.assert_written_object_is_young(dest);
        let (count, filled, kind) = unsafe { map_destination_state(dest) };
        let slot = match kind {
            MapDestinationKind::Build => {
                assert!(filled < count, "map destination has no free entry slot");
                filled
            }
            MapDestinationKind::Update => match self.find_or_place(dest, key) {
                Ok(index) => index,
                Err(_) => return false,
            },
        };
        unsafe {
            write(map_tag_ptr(dest).add(slot), map_pack_tag(key.kind(), value.kind()));
            write_any_value_to_storage(map_keys_ptr(dest, count).add(slot), None, key);
            write_any_value_to_storage(map_values_ptr(dest, count).add(slot), None, value);
            if kind == MapDestinationKind::Build {
                write(dest as *mut u64, map_destination_header_word(count, filled + 1, kind));
            }
        }
        true
    }

    /// Publish a destination. An update that missed a key has no destination
    /// left and answers `None`: `%{map | k: v}` with no `k` in `map` makes no
    /// map, and its caller raises `KeyError`. An update's puts only replace,
    /// so its entries are already in key order and it publishes in place; a
    /// struct's destination is the finished struct and a trie's is the trie the
    /// puts made. A destination that holds more than `MAP_FLAT_MAX` entries
    /// once published becomes a trie.
    pub fn map_destination_freeze(&mut self, dest_bits: u64) -> Option<AnyValueRef> {
        let dest = match destination_layout(dest_bits)? {
            MapLayout::Struct { object, .. } => return Some(object),
            MapLayout::Entries(dest) => dest,
            MapLayout::Trie(root) => return Some(map_bits_ref(heap_object_word(root, ValueKind::MAP))),
        };
        let (capacity, filled, kind) = unsafe { map_destination_state(dest) };
        match kind {
            MapDestinationKind::Build if filled > MAP_FLAT_MAX => {
                let mut entries: Vec<_> = (0..filled).map(|i| unsafe { map_entry(dest, i) }).collect();
                return Some(map_bits_ref(self.publish_normalized_map_entries(&mut entries)));
            }
            MapDestinationKind::Build => {
                let count = self.normalize_destination_entries(dest, capacity, filled);
                self.compact_destination_entries(dest, capacity, count);
                self.publish_entries_in_place(dest, count);
            }
            MapDestinationKind::Update if filled > MAP_FLAT_MAX => {
                let entries: Vec<_> = (0..filled).map(|i| unsafe { map_entry(dest, i) }).collect();
                return Some(map_bits_ref(self.alloc_bulk_map_entries(&entries)));
            }
            MapDestinationKind::Update => self.publish_entries_in_place(dest, filled),
        }
        Some(entries_map_ref(dest))
    }

    /// Publish a build destination whose entries were put in key order with
    /// no key repeated, which is how the compiler writes a map literal whose
    /// keys are all literal atoms. Nothing is sorted or moved.
    pub fn map_destination_publish(&mut self, dest_bits: u64) -> AnyValueRef {
        let dest = map_addr_from_tagged(dest_bits).expect("a map destination");
        let (_, filled, _) = unsafe { map_destination_state(dest) };
        debug_assert!(
            self.entries_are_in_key_order(dest, filled),
            "a map published in place must already be in key order"
        );
        if filled > MAP_FLAT_MAX {
            let entries: Vec<_> = (0..filled).map(|i| unsafe { map_entry(dest, i) }).collect();
            return map_bits_ref(self.alloc_bulk_map_entries(&entries));
        }
        self.publish_entries_in_place(dest, filled);
        entries_map_ref(dest)
    }

    /// Sort the first `filled` entries of the build destination at `dest`,
    /// laid out for `capacity`, by strict structural key where they stand,
    /// and merge equal keys, the last value winning. Answers how many leading
    /// entries remain. Entries move as the words and kind tags they are
    /// stored as; only keys are decoded, to be compared. The sort is stable,
    /// so of equal keys the last put is the last one met.
    fn normalize_destination_entries(&self, dest: *mut u8, capacity: usize, filled: usize) -> usize {
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        let entries = unsafe { StoredEntries::of(dest, capacity) };
        let key = |i| unsafe { entries.key(i) };
        for i in 1..filled {
            let moving = unsafe { entries.read(i) };
            let moving_key = key(i);
            let mut j = i;
            while j > 0 && comparator.key_order_of(key(j - 1), moving_key).is_gt() {
                unsafe { entries.write(j, entries.read(j - 1)) };
                j -= 1;
            }
            unsafe { entries.write(j, moving) };
        }
        let mut kept = 0;
        for i in 1..filled {
            if comparator.key_order_of(key(i), key(kept)).is_eq() {
                unsafe { entries.take_value(i, kept) };
            } else {
                kept += 1;
                unsafe { entries.write(kept, entries.read(i)) };
            }
        }
        if filled == 0 { 0 } else { kept + 1 }
    }

    /// Move the first `count` entries of the build destination at `dest`
    /// from its `capacity` layout to a `count`-entry layout, where they
    /// stand. Every array starts no later than it did, so each moves down.
    fn compact_destination_entries(&mut self, dest: *mut u8, capacity: usize, count: usize) {
        if count == capacity {
            return;
        }
        unsafe {
            write_bytes(map_tag_ptr(dest).add(count), 0, map_tag_bytes_len(count) - count);
            copy(map_keys_ptr(dest, capacity), map_keys_ptr(dest, count), count);
            copy(map_values_ptr(dest, capacity), map_values_ptr(dest, count), count);
            write(
                dest as *mut u64,
                map_destination_header_word(count, count, MapDestinationKind::Build),
            );
        }
    }

    /// Make the first `filled` entries of the destination at `dest` the
    /// published map, where they stand.
    fn publish_entries_in_place(&mut self, dest: *mut u8, filled: usize) {
        for i in 0..filled {
            let (key, value) = unsafe { map_entry(dest, i) };
            self.publish_contained_parts(key.raw(), key.kind());
            self.publish_contained_parts(value.raw(), value.kind());
        }
        debug_assert!(
            filled <= MAP_FLAT_MAX,
            "a flat map holds at most {MAP_FLAT_MAX} entries"
        );
        unsafe { write(dest as *mut u64, map_header_word(filled)) };
    }

    fn entries_are_in_key_order(&self, dest: *mut u8, filled: usize) -> bool {
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        (1..filled).all(|i| {
            let (earlier, later) = unsafe { (map_key(dest, i - 1), map_key(dest, i)) };
            comparator.key_order_of(earlier, later).is_lt()
        })
    }

    pub fn alloc_map_refs(&mut self, entries: &[(AnyValueRef, AnyValueRef)]) -> Result<AnyValueRef, AnyValueRefError> {
        let map_bits = self.alloc_map_refs_bits(entries);
        let map_addr = map_addr_from_tagged(map_bits).expect("new map addr");
        AnyValueRef::from_heap_object(ValueKind::MAP, map_addr)
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

    /// The flat map at `addr` with `key` bound to `value`: a trie when the
    /// key is new and the map held `MAP_FLAT_MAX` entries.
    pub(super) fn map_put_entry(&mut self, addr: *mut u8, key: AnyValue, value: AnyValue) -> u64 {
        let count = unsafe { map_count(addr) };
        match self.find_or_place(addr, key) {
            Err(index) if count == MAP_FLAT_MAX => {
                let mut entries: Vec<_> = (0..count).map(|i| unsafe { map_entry(addr, i) }).collect();
                entries.insert(index, (key, value));
                self.alloc_trie(&entries)
            }
            Err(slot) => self.flat_map_bits(addr, Edit::insert(slot, key, value)),
            Ok(slot) => self.flat_map_bits(addr, Edit::replace(slot, key, value)),
        }
    }

    /// The flat map at `addr` without the entry at `slot`.
    pub(super) fn flat_map_without_slot(&mut self, addr: *const u8, slot: usize) -> u64 {
        self.flat_map_bits(addr, Edit::skip(slot))
    }

    #[inline(always)]
    fn flat_map_bits(&mut self, source: *const u8, edit: Edit) -> u64 {
        heap_object_word(self.write_flat_map(source, edit), ValueKind::MAP)
    }

    /// A flat map of the entries of the flat map at `source`, changed by
    /// `edit`. An edit that keeps the count copies the map whole; one that
    /// changes it copies each array around the slot. The entries kept were
    /// shared when they were first stored, so only a new entry is published.
    #[inline(always)]
    fn write_flat_map(&mut self, source: *const u8, edit: Edit) -> *mut u8 {
        let count = unsafe { map_count(source) };
        let puts = usize::from(edit.puts.is_some());
        let new_count = count - edit.drops + puts;
        debug_assert!(
            new_count <= MAP_FLAT_MAX,
            "a flat map holds at most {MAP_FLAT_MAX} entries"
        );
        let put = edit.puts.map(|(key, value)| self.publish_entry(key, value));
        let size = map_size_for_count(new_count);
        let p = self.alloc_at(RuntimeAllocSite::FlatMap, size);
        unsafe {
            let to = StoredEntries::of(p, new_count);
            if new_count == count {
                copy_nonoverlapping(source, p, size);
            } else {
                let from = StoredEntries::of(source as *mut u8, count);
                let kept = Kept {
                    before: edit.at,
                    from: edit.at + edit.drops,
                    to: edit.at + puts,
                    after: count - edit.at - edit.drops,
                };
                write(p as *mut u64, map_header_word(new_count));
                to.clear_kind_padding(new_count);
                kept.copy(from.tags, to.tags);
                kept.copy(from.keys, to.keys);
                kept.copy(from.values, to.values);
            }
            if let Some(entry) = put {
                to.write(edit.at, entry);
            }
        }
        p
    }

    /// Publish what a new entry holds, and answer the entry as it is stored.
    #[inline(always)]
    fn publish_entry(&mut self, key: AnyValue, value: AnyValue) -> StoredEntry {
        assert_ne!(key.kind(), ValueKind::NULL, "unpublished map key");
        self.publish_contained_parts(key.raw(), key.kind());
        self.publish_contained_parts(value.raw(), value.kind());
        StoredEntry {
            tag: map_pack_tag(key.kind(), value.kind()),
            key: key.raw(),
            value: value.raw(),
        }
    }

    /// Where `key` is in the flat map at `addr`, or where a new entry for it
    /// goes: one ordered search, which a put needs either way.
    pub(super) fn find_or_place(&self, addr: *const u8, key: AnyValue) -> Result<usize, usize> {
        let count = unsafe { map_count(addr) };
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        let (keys, kinds) = unsafe { (map_keys_ptr(addr, count), map_tag_ptr(addr)) };
        let (word, kind) = (key.raw(), key.kind());
        let (mut low, mut high) = (0, count);
        while low < high {
            let middle = low + (high - low) / 2;
            let (entry_word, entry_kind) = unsafe { (read(keys.add(middle)), map_key_kind(read(kinds.add(middle)))) };
            match comparator.key_order(entry_word, entry_kind, word, kind) {
                std::cmp::Ordering::Less => low = middle + 1,
                std::cmp::Ordering::Greater => high = middle,
                std::cmp::Ordering::Equal => return Ok(middle),
            }
        }
        Err(low)
    }

    /// The slot of the flat map at `addr` that holds `key`. A key that is its
    /// stored word is found by that word, with no key ordered; any other is
    /// found by the ordered search.
    #[inline]
    pub(super) fn flat_find(&self, addr: *const u8, key: AnyValue) -> Option<usize> {
        match word_key(key) {
            Some((word, kind)) => unsafe { slot_of_word_key(addr, map_count(addr), word, kind) },
            None => self.find_or_place(addr, key).ok(),
        }
    }

    /// Whether entry `slot` of the node at `node` holds `key`.
    pub(super) fn slot_holds(&self, node: *const u8, slot: usize, key: AnyValue) -> bool {
        let count = unsafe { crate::any_value::map_node_entry_count(node) };
        let (stored, stored_kind) = unsafe {
            (
                read(map_keys_ptr(node, count).add(slot)),
                map_key_kind(read(map_tag_ptr(node).add(slot))),
            )
        };
        if let Some((word, kind)) = word_key(key) {
            return stored == word && stored_kind == kind;
        }
        let schemas = self.schemas.borrow();
        TermComparator::new(&self.node, &schemas)
            .key_order(stored, stored_kind, key.raw(), key.kind())
            .is_eq()
    }

    /// Strict inline Bitstring layout: bit_len: u64 + bytes (padded to 16).
    /// Caller supplies a fully-built byte buffer + bit_len; this performs the
    /// heap copy.
    ///
    /// This always COPIES `bytes`. To view an existing shared buffer
    /// without copying it, use `alloc_bitstring_slice`.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> AnyValue {
        self.alloc_bitstring_with(bytes.len(), bit_len, |dest| {
            dest.write_copy_of_slice(bytes);
        })
    }

    /// Allocate a bitstring of `byte_len` bytes and let `fill` write them in
    /// place, so a caller that computes its payload never builds it twice.
    /// The bytes `fill` receives are unwritten heap memory, so it writes every
    /// one of them.
    ///
    /// Payloads larger than `SHARED_BIN_THRESHOLD_BYTES` route
    /// through the shared zone: a SharedBin is allocated off-heap and the
    /// per-process heap gets a BinRef holding it and a tagged
    /// view of it. Render and bit-match dispatch via
    /// `bitstring_bit_len` / `bitstring_byte_ptr`.
    ///
    /// Returns the VALUE, kind included. The storage choice is
    /// made here and only here: a caller that re-derived it from the length
    /// could disagree with what was actually allocated.
    pub fn alloc_bitstring_with(
        &mut self,
        byte_len: usize,
        bit_len: u64,
        fill: impl FnOnce(&mut [MaybeUninit<u8>]),
    ) -> AnyValue {
        if byte_len > SHARED_BIN_THRESHOLD_BYTES {
            let handle = SharedBinHandle::from_filled(byte_len, fill);
            self.alloc_stats.record_shared_bin(byte_len as u64);
            self.binary_budget.record_made(byte_len);
            return AnyValue::heap_ptr(
                alloc_buffer_view(self, handle, bit_len, StubSite::FilledBuffer).as_raw(),
                ValueKind::BINVIEW,
            );
        }
        self.alloc_inline_bitstring(byte_len, bit_len, fill)
    }

    /// An inline bitstring of `byte_len` bytes that `fill` writes in place.
    /// Reserves at least 1 byte past the payload for the invisible
    /// trailing NUL; the pad-zeroing guarantees it reads as 0, and
    /// bytes_len / bit_len are unchanged by it.
    fn alloc_inline_bitstring(
        &mut self,
        byte_len: usize,
        bit_len: u64,
        fill: impl FnOnce(&mut [MaybeUninit<u8>]),
    ) -> AnyValue {
        let total = bitstring_size_for_bit_len(bit_len);
        let p = self.alloc_at(RuntimeAllocSite::InlineBitstring, total);
        unsafe {
            write(p as *mut u64, bitstring_header_word(bit_len));
            fill(from_raw_parts_mut(p.add(8) as *mut MaybeUninit<u8>, byte_len));
            // Zero the trailing padding so renders / debug aren't garbage.
            let pad_start = 8 + byte_len;
            if pad_start < total {
                write_bytes(p.add(pad_start), 0, total - pad_start);
            }
        }
        AnyValue::heap_ptr(p, ValueKind::BITSTRING)
    }

    /// The binary `left <> right`, where `left` is the whole-byte value
    /// `left_bytes`, viewed through `left_view` when it is a BinView.
    ///
    /// When `left` ends where its buffer's written bytes end and the buffer has
    /// room for `right` (only a buffer a concatenation allocated, and not yet
    /// frozen, has any), `right` is written into that room and the result is a
    /// longer view of the same buffer: `left` is not copied, and keeps its own
    /// length. Otherwise a result of at most `SHARED_BIN_THRESHOLD_BYTES` is
    /// built inline, and a larger one gets a new buffer with as much room as
    /// it holds bytes, so a run of appends allocates a buffer per doubling.
    /// Each side is written once.
    ///
    /// # Safety
    /// `left_bytes` and `right` must be live byte slices that stay valid for
    /// the call, and `left_view`, if present, the BinView `left_bytes` views.
    pub unsafe fn alloc_concatenation(
        &mut self,
        left_bytes: &[u8],
        left_view: Option<BinView>,
        right: &[u8],
    ) -> AnyValue {
        if let Some(view) = left_view.filter(BinView::ends_at_buffer_end) {
            let shared = view.shared_raw();
            if right.len() <= unsafe { &*shared }.spare() {
                unsafe { shared_bin_append(shared, right) };
                let bit_len = (left_bytes.len() + right.len()) as u64 * 8;
                let longer = alloc_view(
                    self,
                    view.binref(),
                    view.bytes_ptr(),
                    bit_len,
                    StubSite::AppendedInPlace,
                );
                return AnyValue::heap_ptr(longer.as_raw(), ValueKind::BINVIEW);
            }
        }
        let total = left_bytes.len() + right.len();
        if total <= SHARED_BIN_THRESHOLD_BYTES {
            return self.alloc_inline_bitstring(total, total as u64 * 8, |dest| {
                dest[..left_bytes.len()].write_copy_of_slice(left_bytes);
                dest[left_bytes.len()..].write_copy_of_slice(right);
            });
        }
        let handle = SharedBinHandle::from_bytes_with_room(&[], total * 2);
        let shared = handle.as_raw();
        unsafe {
            shared_bin_append(shared, left_bytes);
            shared_bin_append(shared, right);
        }
        self.alloc_stats.record_shared_bin((total * 2) as u64);
        self.binary_budget.record_made(total * 2);
        AnyValue::heap_ptr(
            alloc_buffer_view(self, handle, total as u64 * 8, StubSite::GrownBuffer).as_raw(),
            ValueKind::BINVIEW,
        )
    }

    /// Allocate the whole-byte slice `[byte_offset, byte_offset + byte_len)` of
    /// the window `parent` views, returning it as a value. `byte_offset` counts from
    /// the window's first byte.
    ///
    /// Above `SHARED_BIN_THRESHOLD_BYTES` the slice SHARES the parent's
    /// bytes: a new view names the parent's BinRef at its own first byte and
    /// length, and nothing is copied or retained. That is what stops a byte
    /// scanner being quadratic, and what makes taking a field out of a large
    /// binary cost a view rather than the field.
    ///
    /// At or below the threshold the bytes are copied into an inline
    /// bitstring. Copying is cheaper than a view at that size, and it keeps
    /// a small slice from pinning a large buffer alive.
    ///
    /// This is the one place the inline/shared choice is made for a slice,
    /// so it returns the value rather than a bare pointer the caller has to
    /// re-classify.
    ///
    /// # Safety
    ///
    /// `parent` must be a live view on this heap.
    pub unsafe fn alloc_bitstring_slice(&mut self, parent: BinView, byte_offset: u64, byte_len: u64) -> AnyValue {
        assert!(
            (byte_offset + byte_len) as usize <= parent.bytes_len(),
            "bitstring slice [{byte_offset}, +{byte_len}) runs past the window it slices"
        );
        let first = unsafe { parent.bytes_ptr().add(byte_offset as usize) };
        if byte_len as usize > SHARED_BIN_THRESHOLD_BYTES {
            let window = alloc_view(self, parent.binref(), first, byte_len * 8, StubSite::WindowOfBuffer);
            return AnyValue::heap_ptr(window.as_raw(), ValueKind::BINVIEW);
        }
        let slice = unsafe { from_raw_parts(first, byte_len as usize) };
        self.alloc_bitstring(slice, byte_len * 8)
    }

    /// Denotation, layout header, code pointer, then captures and their kind bytes.
    pub fn alloc_closure_slots(
        &mut self,
        denotation: crate::any_value::ClosureDenotationId,
        arity: u16,
        captured_count: usize,
        halt_kind: u16,
    ) -> u64 {
        self.alloc_closure_slots_of(RuntimeAllocSite::Closure, denotation, arity, captured_count, halt_kind)
    }

    /// A continuation frame: an internal closure the compiler builds to
    /// resume a call's caller. The statistics count it apart from the
    /// closures a program makes.
    pub fn alloc_continuation_slots(&mut self, arity: u16, captured_count: usize) -> u64 {
        self.alloc_closure_slots_of(
            RuntimeAllocSite::Continuation,
            crate::any_value::ClosureDenotationId::INTERNAL,
            arity,
            captured_count,
            0,
        )
    }

    fn alloc_closure_slots_of(
        &mut self,
        site: RuntimeAllocSite,
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
        let p = self.alloc_at(site, total);
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
        self.assert_written_object_is_young(closure_addr);
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
        self.assert_written_object_is_young(closure);
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
        self.assert_written_object_is_young(object);
        let raw = value.storage_raw()?;
        self.share(value)?;
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
        self.share(value)?;
        Ok(value)
    }

    /// Mark `value` shared: from now on it may have a second holder and is
    /// never written again. A list marks its spine up to the first cell
    /// already marked, so an aliased cell certifies an entirely shared tail. A
    /// struct or tuple marks its header; everything it holds was shared when
    /// it was stored. Other kinds are never written in place and carry no
    /// mark. The count is the objects this call newly protected.
    pub(super) fn share(&mut self, value: AnyValueRef) -> Result<usize, AnyValueRefError> {
        match value.tag() {
            ValueKind::LIST if !value.is_empty_list() => Ok(unsafe { ListCons::share_spine(value.list_addr()?) }),
            ValueKind::STRUCT => Ok(usize::from(unsafe { share_struct(value.struct_addr()?) })),
            _ => Ok(0),
        }
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
            self.assert_written_object_is_young(addr);
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
        // An integer, float or reference field's ref points into the struct's own payload,
        // so it is read-only data exactly when the struct is. A heap field's ref
        // is its stored address and an atom or pid field's ref is its value; each already
        // says what it names.
        Ok(
            if obj.is_literal() && matches!(field.tag(), ValueKind::INT | ValueKind::FLOAT | ValueKind::REF) {
                field.literal()
            } else {
                field
            },
        )
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

    /// Objects on this heap: those a collection kept or a gift brought, and
    /// those allocated since. A collection counts what it copied.
    pub fn live_count(&self) -> usize {
        (self.old_objects + self.alloc_count) as usize
    }

    /// Bytes written into the heap, old and young. Blocks count by fill, never
    /// by capacity: a gift's block is mostly empty, and an abandoned block's
    /// tail was never written.
    pub fn bytes_used(&self) -> usize {
        self.live_baseline + self.young_bytes()
    }

    /// Whether `object` lies in a young block: the tip, the tip a gift window
    /// set aside, or a parked block. A minor collection looks inside every
    /// young object and inside no old one.
    pub fn is_young(&self, object: *mut u8) -> bool {
        super::ref_io::ptr_in_ranges(object, self.young_ranges())
    }

    /// A write into an object that already exists is sound only while the
    /// object is young. A minor collection does not look inside old objects, so
    /// an old object must never come to hold a pointer to a young one. Checked
    /// in debug builds.
    #[inline]
    pub(crate) fn assert_written_object_is_young(&self, object: *mut u8) {
        debug_assert!(
            self.is_young(object),
            "a write into an object a collection has already kept"
        );
    }

    /// Bytes written since the last collection, which is also the most a minor
    /// collection can copy: the tip's fill plus every young parked block's fill.
    pub fn young_bytes(&self) -> usize {
        self.current_block().fill() + self.young_blocks.iter().map(Block::fill).sum::<usize>()
    }

    /// The address range of the tip, of the tip set aside by an open gift
    /// window, and of every young parked block.
    pub(super) fn young_ranges(&self) -> impl Iterator<Item = (*mut u8, *mut u8)> + '_ {
        let saved_tip = self.gift.as_ref().map(|window| window.saved_tip);
        std::iter::once((self.block_start, self.block_end))
            .chain(saved_tip.map(|block| (block.start, block.end())))
            .chain(self.young_blocks.iter().map(|block| (block.start, block.end())))
    }

    /// The address range of every old block.
    pub(super) fn old_ranges(&self) -> impl Iterator<Item = (*mut u8, *mut u8)> + '_ {
        self.old_blocks.iter().map(|block| (block.start, block.end()))
    }

    /// The address range of every block the heap owns.
    pub(super) fn block_ranges(&self) -> impl Iterator<Item = (*mut u8, *mut u8)> + '_ {
        self.young_ranges().chain(self.old_ranges())
    }

    pub fn bytes_remaining_in_block(&self) -> usize {
        unsafe { self.block_end.offset_from(self.bump_top) as usize }
    }

    /// The generation the next collection takes: major once the old bytes have
    /// outgrown what the last major collection left by `MAJOR_GROWTH_FACTOR`,
    /// minor otherwise. A heap with no major collection yet is measured against
    /// half the smallest tip, so a heap with nothing old is always minor.
    pub(super) fn next_generation(&self) -> Generation {
        let reference = self.old_after_last_major.max(SIZE_TABLE[0] / 2);
        if self.live_baseline > MAJOR_GROWTH_FACTOR * reference {
            Generation::Major
        } else {
            Generation::Minor
        }
    }

    /// The one collection entry: a Cheney copy of everything `roots` reaches
    /// in the from-space into fresh blocks, which become old, after which the
    /// from-space is released. A minor collection's from-space is the young
    /// blocks; a major collection's is every block (`next_generation`).
    ///
    /// The to-space block's capacity is a guess, at least the smallest tip: the
    /// old bytes for a major collection, the bytes the last minor collection
    /// copied for a minor one (a major's much larger copy says nothing about
    /// what the young generation keeps). A copy that outgrows the guess takes
    /// overflow blocks sized for the overflow (`bump_to_space`), so the room a
    /// wrong guess leaves unused is bounded by the overflow, not by the guess;
    /// a huge object parks alone. A wrong guess costs a block, never
    /// correctness. The scan reads a worklist of copied objects, not an
    /// address, so to-space needs no contiguity.
    ///
    /// Every slot of `roots` holds its forwarded value on return. A slot
    /// that is not a pointer into the from-space (a scalar immediate, the empty
    /// list, a static closure or halt continuation, a pointer into an old block
    /// a minor collection leaves) is left as it was; a scalar box in the
    /// from-space is copied without tracing its payload.
    ///
    /// The caller passes every reference it holds into this heap. For a
    /// `Process` that is `Process::collect`, which assembles the runnable
    /// closure, the park record, the mailbox and the caller's transient
    /// values into one slice. Gifts still waiting in a delivery in-queue are
    /// not roots: their blocks join the heap, old, only when grafted, and
    /// every reference inside a gift points into its own segment.
    ///
    /// The heap must not have a gift window open.
    pub fn collect(&mut self, roots: &mut [AnyValueRef]) -> GcStats {
        assert!(
            self.gift.is_none(),
            "a gift window is open; the heap collects only between end_gift and the next begin_gift"
        );
        debug_assert_eq!(
            self.live_baseline,
            self.old_blocks.iter().map(Block::fill).sum::<usize>(),
            "the old bytes are the fill of the old blocks"
        );
        let generation = self.next_generation();
        let (young_bytes, young_budget) = (self.young_bytes() as u64, self.collection_budget() as u64);
        let (young_binary_bytes, binary_budget) = (
            self.binary_budget.young_binary_bytes() as u64,
            self.binary_budget.budget() as u64,
        );
        let from_space = FromSpace::of(self, generation);
        let to_capacity_guess = match generation {
            Generation::Major => self.live_baseline,
            Generation::Minor => self.last_minor_copied_bytes,
        };
        let from_blocks = self.take_from_space(generation);
        let to_capacity = pick_block_capacity(to_capacity_guess.max(SIZE_TABLE[0]));
        self.overflow_step = SIZE_TABLE[0];
        let to_start = pool_alloc(to_capacity);
        self.install_block(Block {
            start: to_start,
            top: to_start,
            capacity: to_capacity,
        });
        let mut copied_objects: Vec<CopiedObject> = Vec::new();
        let mut stats = GcStats {
            generation,
            young_bytes,
            young_budget,
            young_binary_bytes,
            binary_budget,
            from_space_capacity_bytes: from_blocks.iter().map(|block| block.capacity as u64).sum(),
            blocks_released: from_blocks.len() as u64,
            to_space_guess_bytes: to_capacity as u64,
            stubs_made: std::mem::take(&mut self.stubs_made),
            binrefs_made: std::mem::take(&mut self.binrefs_made),
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

        drop(schemas);

        // The off-heap sweep walks the intrusive chain of the from-space: survivors
        // are rewritten to their to-space copies and move to the old chain, and
        // dead entries drop their off-heap reference. It must run before the
        // from-space is released because it reads from-space stubs (their
        // `off_heap_next` link, which Cheney never overwrites).
        let survivor_binary_bytes =
            off_heap::sweep(self, generation, &mut stats.stub_visits, &mut stats.stubs_survived);
        self.binary_budget.after_collection(generation, survivor_binary_bytes);

        stats.to_space_capacity_bytes = self.retire_to_space_as_old() as u64;
        let kept_objects = copied_objects.len() as u64;
        match generation {
            Generation::Major => {
                self.live_baseline = stats.copied_bytes as usize;
                self.old_objects = kept_objects;
                self.old_after_last_major = self.live_baseline;
            }
            Generation::Minor => {
                self.live_baseline += stats.copied_bytes as usize;
                self.old_objects += kept_objects;
                self.last_minor_copied_bytes = stats.copied_bytes as usize;
            }
        }
        self.install_fresh_tip();
        self.gc_run_count += 1;
        stats.live_objects = self.old_objects;
        stats.live_bytes = self.live_baseline as u64;
        stats.blocks_after = self.old_blocks.len() as u64;

        // Release the from-space: pooled capacities return to the pool (§6.6),
        // exact blocks to the system allocator. The fresh tip is installed
        // first, so it never lands on an address the from-space is about to
        // give up.
        for block in from_blocks {
            block.release();
        }
        stats
    }

    /// Detach the blocks a collection of `generation` copies out of: the tip and
    /// the young parked blocks, and for a major collection the old blocks too.
    fn take_from_space(&mut self, generation: Generation) -> Vec<Block> {
        let mut blocks = std::mem::take(&mut self.young_blocks);
        blocks.push(self.current_block());
        if generation == Generation::Major {
            blocks.append(&mut self.old_blocks);
        }
        blocks
    }

    /// Make the blocks a collection copied into old: its tip, unless it holds
    /// nothing, and the blocks the copy parked. Returns their capacity.
    fn retire_to_space_as_old(&mut self) -> usize {
        let tip = self.current_block();
        let mut capacity = self.young_blocks.iter().map(|block| block.capacity).sum::<usize>();
        if tip.fill() == 0 {
            tip.release();
        } else {
            capacity += tip.capacity;
            self.old_blocks.push(tip);
        }
        self.old_blocks.append(&mut self.young_blocks);
        capacity
    }

    /// Install the empty tip allocation continues in after a collection,
    /// sized to the old bytes: the heap collects again after allocating as many.
    fn install_fresh_tip(&mut self) {
        let capacity = pick_block_capacity(self.young_budget().max(SIZE_TABLE[0]));
        let start = pool_alloc(capacity);
        self.install_block(Block {
            start,
            top: start,
            capacity,
        });
        self.alloc_count = 0;
    }

    /// Release every object on the off-heap chain as a process exit does: nothing is
    /// live, so every resource whose last reference this heap held queues its
    /// destructor on `pending_dtors`. Allocates no to-space.
    pub fn release_resources_at_exit(&mut self) {
        off_heap::sweep(self, Generation::Major, &mut 0, &mut StubCounts::default());
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
            // These hold no heap edge for the scan to forward.
            ValueKind::BITSTRING | ValueKind::BINREF | ValueKind::RESOURCE => {}
            ValueKind::BINVIEW => cheney_trace_binview(copied.ptr, from_space, heap, schemas, copied_objects, stats),
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
        // release every SharedBin held via the intrusive off-heap
        // chain. Order matters: must run before pool_free below, since
        // off_heap_drop_all walks BinRef payloads in the heap's blocks.
        off_heap::drop_all(self);
        // Release blocks: pooled capacities go back to the pool (§6.6) so the
        // next spawn pulls from it with no per-spawn malloc; exact blocks go
        // to the system allocator. A tip set aside by an unfinished gift
        // window goes back too.
        self.current_block().release();
        if let Some(window) = self.gift.take() {
            window.saved_tip.release();
        }
        for block in self.young_blocks.drain(..).chain(self.old_blocks.drain(..)) {
            block.release();
        }
    }
}

/// One entry as it is stored: its kind tag, key word and value word.
#[derive(Clone, Copy)]
struct StoredEntry {
    tag: u8,
    key: u64,
    value: u64,
}

/// The word and kind of a key that is the same key exactly when its stored
/// word is the same: an integer, an atom, a pid, a reference. A float is
/// left out, since its word must first be checked to be a number.
#[inline]
fn word_key(key: AnyValue) -> Option<(u64, ValueKind)> {
    match key {
        AnyValue::Int(value) => Some((value as u64, ValueKind::INT)),
        AnyValue::Atom(id) => Some((id as u64, ValueKind::ATOM)),
        AnyValue::Opaque(kind, word) => Some((word, kind)),
        _ => None,
    }
}

/// The first of the `count` words at `words` that is `word`.
///
/// # Safety
/// `words` must point at `count` readable words.
#[inline]
pub(super) unsafe fn position_of_word(words: *const u64, count: usize, word: u64) -> Option<usize> {
    (0..count).find(|&i| unsafe { read(words.add(i)) } == word)
}

/// The slot among the `count` entries of the node at `addr` whose stored key
/// is `word` with kind `kind`.
///
/// # Safety
/// `addr` must be a map node laid out for `count` entries, all written.
#[inline]
unsafe fn slot_of_word_key(addr: *const u8, count: usize, word: u64, kind: ValueKind) -> Option<usize> {
    let (keys, kinds) = unsafe { (map_keys_ptr(addr, count), map_tag_ptr(addr)) };
    let mut from = 0;
    loop {
        let slot = from + unsafe { position_of_word(keys.add(from), count - from, word) }?;
        if map_key_kind(unsafe { read(kinds.add(slot)) }) == kind {
            return Some(slot);
        }
        from = slot + 1;
    }
}

/// The kind tags, keys and values of a flat map's entries, read and written
/// as stored.
struct StoredEntries {
    tags: *mut u8,
    keys: *mut u64,
    values: *mut u64,
}

impl StoredEntries {
    /// # Safety
    ///
    /// `node` must be a map or a map destination laid out for `capacity`
    /// entries.
    unsafe fn of(node: *mut u8, capacity: usize) -> Self {
        unsafe {
            Self {
                tags: map_tag_ptr(node),
                keys: map_keys_ptr(node, capacity),
                values: map_values_ptr(node, capacity),
            }
        }
    }

    /// Zero the kind bytes past the last of `count` entries. They share the
    /// last word of kind bytes, which is cleared whole before any is written.
    ///
    /// # Safety
    ///
    /// The arrays must be laid out for `count` entries, none written yet.
    unsafe fn clear_kind_padding(&self, count: usize) {
        if count > 0 {
            unsafe { write(self.keys.sub(1), 0) };
        }
    }

    /// # Safety
    ///
    /// Entry `i` must be written.
    unsafe fn key(&self, i: usize) -> AnyValue {
        unsafe { map_key_in_arrays(self.keys, self.tags, i) }
    }

    /// # Safety
    ///
    /// Entry `i` must be in bounds.
    unsafe fn read(&self, i: usize) -> StoredEntry {
        unsafe {
            StoredEntry {
                tag: read(self.tags.add(i)),
                key: read(self.keys.add(i)),
                value: read(self.values.add(i)),
            }
        }
    }

    /// # Safety
    ///
    /// Entry `i` must be in bounds.
    unsafe fn write(&self, i: usize, entry: StoredEntry) {
        unsafe {
            write(self.tags.add(i), entry.tag);
            write(self.keys.add(i), entry.key);
            write(self.values.add(i), entry.value);
        }
    }

    /// Give entry `to` the value of entry `from`, keeping its key.
    ///
    /// # Safety
    ///
    /// Both entries must be in bounds.
    unsafe fn take_value(&self, from: usize, to: usize) {
        unsafe {
            let from = self.read(from);
            let tag = self.tags.add(to);
            write(tag, map_pack_tag(map_key_kind(read(tag)), map_value_kind(from.tag)));
            write(self.values.add(to), from.value);
        }
    }
}

/// The entries an edit keeps: `before` of them from the front of the source,
/// and `after` of them from slot `from` of the source to slot `to`.
struct Kept {
    before: usize,
    from: usize,
    to: usize,
    after: usize,
}

impl Kept {
    /// Copy the kept items of one of a flat map's arrays.
    ///
    /// # Safety
    ///
    /// `source` must hold `from + after` items and `dest` have room for
    /// `to + after`, and the two must not overlap.
    unsafe fn copy<T: Copy>(&self, source: *const T, dest: *mut T) {
        unsafe {
            copy_nonoverlapping(source, dest, self.before);
            copy_nonoverlapping(source.add(self.from), dest.add(self.to), self.after);
        }
    }
}

/// What a flat map's writer changes as it copies: at slot `at` of the
/// source it leaves out `drops` entries (none or one) and writes `puts`.
struct Edit {
    at: usize,
    drops: usize,
    puts: Option<(AnyValue, AnyValue)>,
}

impl Edit {
    /// Every entry is copied.
    const NONE: Self = Self {
        at: 0,
        drops: 0,
        puts: None,
    };

    /// A new entry goes in ahead of the entry at `at`.
    fn insert(at: usize, key: AnyValue, value: AnyValue) -> Self {
        Self {
            at,
            drops: 0,
            puts: Some((key, value)),
        }
    }

    /// The entry at `at` gives way to a new one.
    fn replace(at: usize, key: AnyValue, value: AnyValue) -> Self {
        Self {
            at,
            drops: 1,
            puts: Some((key, value)),
        }
    }

    /// The entry at `at` is left out.
    fn skip(at: usize) -> Self {
        Self {
            at,
            drops: 1,
            puts: None,
        }
    }
}
