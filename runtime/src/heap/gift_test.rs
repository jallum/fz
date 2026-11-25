//! A heap opens a gift window, cuts the segment, and another heap grafts it.
//! Each test states the property it holds the gift window to.

use super::imp::BUDGET_FLOOR;
use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, EMPTY_LIST, ValueKind, binview_addr_from_tagged, heap_kind_from_tagged, heap_object_word,
    heap_word_addr, list_addr_from_tagged, struct_addr_from_tagged, struct_size_for_payload,
};
use crate::bits::{
    BINREF_BYTES, BINVIEW_BYTES, BinRef, BinView, SharedBinHandle, alloc_binref, alloc_buffer_view, alloc_view,
};
use crate::heap::StubSite;
use crate::resource::{RESOURCE_STUB_SIZE, ResourceHandle, ResourceStub, alloc_resource};
use crate::sync::Ordering;
use std::cell::RefCell;
use std::ptr::null_mut;
use std::rc::Rc;

/// A destructor word the test never dispatches: the resource only carries it.
const TEST_DESTRUCTOR: u64 = 0xD7;

/// A view of `bit_len` bits that starts `byte_offset` bytes into a buffer that
/// enters the heap with it, as a buffer does when a message copy brings it.
fn window_of_new_buffer(
    heap: &mut Heap,
    handle: SharedBinHandle,
    byte_offset: usize,
    bit_len: u64,
    site: StubSite,
) -> BinView {
    let first = unsafe { handle.bytes_ptr().add(byte_offset) };
    let binref = alloc_binref(heap, handle, site);
    alloc_view(heap, binref, first, bit_len, site)
}

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

/// A fresh buffer's two objects: its BinRef and its view.
const NEW_BUFFER_BYTES: usize = BINREF_BYTES + BINVIEW_BYTES;

fn shared_refs(handle: &SharedBinHandle) -> usize {
    unsafe { (*handle.as_raw()).refcount.load(Ordering::Relaxed) }
}

fn alloc_int_list_cons(heap: &mut Heap, head: i64, tail_bits: u64) -> u64 {
    heap.alloc_list_cons_slot(AnyValue::int(head), tail_bits)
}

fn list_ref_from_bits(bits: u64) -> AnyValueRef {
    let addr = list_addr_from_tagged(bits).expect("list addr");
    AnyValueRef::from_heap_object(ValueKind::LIST, addr).expect("list ref")
}

fn heap_ref(bits: u64) -> AnyValueRef {
    let kind = heap_kind_from_tagged(bits).expect("tagged heap root");
    AnyValueRef::from_raw_word(bits)
        .inspect(|root| assert_eq!(root.tag(), kind))
        .expect("heap root ref")
}

/// The chain word of the BinRef a view names: the one binary object on a chain.
fn binref_word(pb: &BinView) -> u64 {
    pb.binref().word()
}

/// The off-heap chain from `head` as tagged words, head first.
fn chain_from(head: u64) -> Vec<u64> {
    let mut out = Vec::new();
    let mut cur_bits = head;
    while cur_bits != 0 {
        let addr = heap_word_addr(cur_bits);
        let next = match heap_kind_from_tagged(cur_bits) {
            Some(ValueKind::BINREF) => unsafe { BinRef::from_raw(addr).off_heap_next() },
            Some(ValueKind::RESOURCE) => unsafe { ResourceStub::from_raw(addr).off_heap_next() },
            kind => panic!("unexpected off-heap kind {kind:?}"),
        };
        out.push(cur_bits);
        cur_bits = next;
    }
    out
}

/// The heap's young off-heap chain: the stubs allocated since its last collection.
fn off_heap_chain(h: &Heap) -> Vec<u64> {
    chain_from(h.off_heap_head)
}

/// The heap's old off-heap chain: the stubs a collection kept.
fn off_heap_old_chain(h: &Heap) -> Vec<u64> {
    chain_from(h.off_heap_old_head)
}

/// The last table entry: anything larger is outside the pool.
const TABLE_CEILING: usize = SIZE_TABLE[SIZE_TABLE.len() - 1];

/// A struct schema whose object is larger than every table entry, so
/// `alloc_struct` gives it an exact block.
fn oversize_schema(reg: &Rc<RefCell<SchemaRegistry>>) -> u32 {
    let n_fields = (TABLE_CEILING + 256) / 8;
    let fields = (0..n_fields)
        .map(|i| FieldDescriptor {
            offset: (i * 8) as u32,
            kind: FieldKind::AnyValue,
            name: None,
        })
        .collect();
    reg.borrow_mut().register(Schema {
        identity: SchemaIdentity::Internal("Oversize".into()),
        size: (n_fields * 8) as u32,
        fields,
    })
}

/// One cons cell copied through a gift window, as a sender would copy a
/// matched message part.
fn gift_one_cons(sender: &mut Heap, value: i64) -> (GiftSegment, u64) {
    sender.begin_gift(16);
    let bits = alloc_int_list_cons(sender, value, EMPTY_LIST);
    (sender.end_gift(), bits)
}

#[test]
fn a_gift_below_the_table_occupies_a_pooled_block_of_its_measured_size() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pooled_before = pool_outstanding_blocks();
    for (measured, block) in [(16, 16), (64, 64), (1008, 1008)] {
        sender.begin_gift(measured);
        assert_eq!(sender.block_size, block, "{measured} measured bytes");
        let _ = sender.alloc(measured);
        let segment = sender.end_gift();
        assert_eq!(segment.fill_bytes(), measured);
        assert_eq!(
            pool_outstanding_blocks(),
            pooled_before + 1,
            "the gift block is a pooled block of the measured size"
        );
        drop(segment);
        assert_eq!(pool_outstanding_blocks(), pooled_before);
    }
    assert_eq!(sender.block_size, SIZE_TABLE[0], "the tip is untouched by the gifts");
}

#[test]
fn end_gift_restores_the_senders_tip_and_leaves_its_earlier_allocations_untouched() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let kept = alloc_int_list_cons(&mut sender, 42, EMPTY_LIST);
    let (start, top, capacity) = (sender.block_start, sender.bump_top, sender.block_size);
    let bytes_used = sender.bytes_used();

    sender.begin_gift(1008 + 64);
    assert_eq!(
        sender.block_size,
        pick_block_capacity(1008 + 64),
        "a gift opens the smallest block that holds the measured bytes"
    );
    assert_ne!(sender.block_start, start, "the gift allocates into its own block");
    let _ = sender.alloc(1008);
    let _ = sender.alloc(64);
    assert!(
        sender.young_blocks.is_empty(),
        "the measured bytes fit; the window never overflows"
    );
    let segment = sender.end_gift();

    assert_eq!(segment.block_count(), 1, "the segment is the one gift block");
    assert_eq!(segment.fill_bytes(), 1008 + 64);
    assert_eq!(
        (sender.block_start, sender.bump_top, sender.block_size),
        (start, top, capacity)
    );
    assert!(sender.young_blocks.is_empty(), "the sender's own chain is as it was");
    assert_eq!(sender.bytes_used(), bytes_used);
    let head = sender.read_list_head_ref(list_ref_from_bits(kept)).expect("head");
    assert_eq!(head.load_int().expect("int"), 42);
    assert_eq!(
        sender.node.alloc_stats().other.allocs,
        2,
        "the program's figure counts what the copy allocated"
    );
}

#[test]
fn a_gift_with_a_shared_bin_stub_survives_the_receivers_gc_on_its_off_heap_chain() {
    pool_drain_for_test();
    let witness = SharedBinHandle::from_bytes(&[0xaa; 8]);
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);

    sender.begin_gift(NEW_BUFFER_BYTES);
    let pb = alloc_buffer_view(
        &mut sender,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let gifted = binref_word(&pb);
    let segment = sender.end_gift();
    assert_eq!(sender.off_heap_head, 0, "the stub left the sender's chain");
    assert_eq!(segment.off_heap_head(), gifted);
    assert_eq!(shared_refs(&witness), 2, "the segment holds the heap-owned reference");

    receiver.graft(segment);
    assert_eq!(off_heap_chain(&receiver), vec![gifted]);
    assert_eq!(off_heap_old_chain(&receiver), Vec::<u64>::new());
    let mut root = heap_object_word(pb.as_raw() as *const u8, ValueKind::BINVIEW) as *mut u8;
    assert_eq!(pool_total_cached_blocks(), 0);
    let stats = receiver.collect_tagged(&mut root);

    assert_eq!(stats.generation, Generation::Minor);
    let kept = binview_addr_from_tagged(root as u64).expect("binview root");
    assert_ne!(
        kept,
        pb.as_raw(),
        "a gift is young: the minor collection copied the live view out of it"
    );
    let kept_view = unsafe { BinView::from_raw(kept) };
    assert_eq!(
        off_heap_old_chain(&receiver),
        vec![binref_word(&kept_view)],
        "the surviving stub moved from the young chain to the old chain"
    );
    assert_eq!(off_heap_chain(&receiver), Vec::<u64>::new());
    assert_eq!(kept_view.shared_raw(), witness.as_raw());
    assert_eq!(shared_refs(&witness), 2, "the refcount is unchanged by the collection");
    assert_eq!(
        pool_total_cached_blocks(),
        2,
        "the receiver's old tip and the gift block are back in the pool"
    );
    drop(receiver);
    assert_eq!(
        shared_refs(&witness),
        1,
        "the receiver released the reference it adopted"
    );
    drop(sender);
    pool_drain_for_test();
}

#[test]
fn graft_splices_each_gifts_off_heap_prefix_ahead_of_the_receivers_young_chain() {
    let witness = SharedBinHandle::from_bytes(&[1, 2, 3, 4]);
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let sender_own = binref_word(&alloc_buffer_view(
        &mut sender,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    ));
    let receiver_own = binref_word(&alloc_buffer_view(
        &mut receiver,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    ));

    sender.begin_gift(2 * NEW_BUFFER_BYTES);
    let older = binref_word(&window_of_new_buffer(
        &mut sender,
        witness.clone(),
        1,
        witness.bytes_len() as u64 * 8 - 8,
        StubSite::FilledBuffer,
    ));
    let newer = binref_word(&window_of_new_buffer(
        &mut sender,
        witness.clone(),
        2,
        witness.bytes_len() as u64 * 8 - 2 * 8,
        StubSite::FilledBuffer,
    ));
    let segment = sender.end_gift();
    sender.begin_gift(NEW_BUFFER_BYTES);
    let latest = binref_word(&window_of_new_buffer(
        &mut sender,
        witness.clone(),
        3,
        witness.bytes_len() as u64 * 8 - 3 * 8,
        StubSite::FilledBuffer,
    ));
    let later_segment = sender.end_gift();

    assert_eq!(
        off_heap_chain(&sender),
        vec![sender_own],
        "the sender keeps only its own stub"
    );
    receiver.graft(segment);
    receiver.graft(later_segment);
    assert_eq!(
        off_heap_chain(&receiver),
        vec![latest, newer, older, receiver_own],
        "each gift's stubs join the young chain ahead of the receiver's own, newest to oldest"
    );
    assert_eq!(off_heap_old_chain(&receiver), Vec::<u64>::new());
    assert_eq!(shared_refs(&witness), 6);
    drop(receiver);
    assert_eq!(
        shared_refs(&witness),
        2,
        "the receiver released its own stub and every adopted one"
    );
    drop(sender);
    assert_eq!(shared_refs(&witness), 1);
}

#[test]
fn a_gift_with_an_object_above_the_table_grafts_and_is_copied_by_the_receivers_collection() {
    let reg = fresh_registry();
    let schema = oversize_schema(&reg);
    let size = struct_size_for_payload(reg.borrow().get(schema).allocation_payload_size());
    assert!(size > TABLE_CEILING);
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let pooled_before = pool_outstanding_blocks();

    sender.begin_gift(size);
    let big = sender.alloc_struct(schema);
    let segment = sender.end_gift();
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before,
        "the gift block is exact, above the table, and not pooled"
    );
    assert_eq!(segment.block_count(), 1, "the object is the segment's one exact block");
    assert!(segment.fill_bytes() >= size, "the object is written into the segment");
    assert!(!sender.contains_heap_addr(big), "the object left the sender");

    receiver.graft(segment);
    assert!(
        receiver.contains_heap_addr(big),
        "the receiver now owns the object's address"
    );
    let mut root = heap_object_word(big as *const u8, ValueKind::STRUCT) as *mut u8;
    let stats = receiver.collect_tagged(&mut root);

    let moved = struct_addr_from_tagged(root as u64).expect("struct root");
    assert_ne!(moved, big, "the object was copied");
    assert!(receiver.contains_heap_addr(moved));
    assert!(!receiver.contains_heap_addr(big));
    assert_eq!(stats.copied_objects, 1);
    assert!(receiver.bytes_used() >= size, "the heap's blocks hold the object");
    assert_eq!(stats.live_bytes, receiver.live_baseline as u64);
    drop(receiver);
    drop(sender);
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before - 2,
        "every pooled block came back"
    );
}

#[test]
fn thousands_of_small_unread_gifts_do_not_grow_the_receivers_tip_after_gc() {
    pool_drain_for_test();
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[11], reg);
    let capacity_before = receiver.block_size;

    // The receiver's own live data: a 2000-cell list it keeps.
    let mut list = EMPTY_LIST;
    for i in 0..2000 {
        list = alloc_int_list_cons(&mut receiver, i, list);
    }
    let own_live = 2000 * 16;
    assert_eq!(receiver.bytes_used(), own_live);
    assert!(
        receiver.should_gc(),
        "a heap never collected is due at the budget floor"
    );

    let gifts: u64 = 6000;
    for i in 0..gifts as i64 {
        let (segment, _) = gift_one_cons(&mut sender, i);
        receiver.graft(segment);
    }
    let adopted_fill = gifts as usize * 16;
    assert!(own_live + adopted_fill < receiver.block_size);
    assert_eq!(
        receiver.bytes_used(),
        own_live + adopted_fill,
        "adopted bytes count by fill"
    );
    assert_eq!(receiver.live_baseline, 0, "adopted fill is young, not old");
    assert!(
        receiver.should_gc(),
        "the 128000 young bytes are far past the budget floor"
    );
    let mut roots = [heap_ref(list)];
    let stats = receiver.collect_stats(&mut roots);

    assert_eq!(stats.generation, Generation::Minor, "the gifts raised no old bytes");
    assert_eq!(stats.received_bytes, adopted_fill as u64);
    assert_eq!(
        receiver.block_size,
        pick_block_capacity(own_live),
        "the fresh tip is fitted to the bytes the collection kept"
    );
    assert!(
        receiver.block_size <= capacity_before,
        "dead gifts do not grow the heap"
    );
    assert_eq!(
        receiver.bytes_used(),
        own_live,
        "only the 32000 own live bytes remain of the 128000 in use; the gifts are dead"
    );
    assert_eq!(stats.live_bytes, own_live as u64, "none of the gifts was reachable");
    assert!(receiver.young_blocks.is_empty());
    assert_eq!(
        pool_total_cached_blocks(),
        1 + gifts as usize,
        "the old tip and every gift block went back to the pool"
    );
    drop(receiver);
    drop(sender);
    pool_drain_for_test();
}

#[test]
fn end_gift_leaves_the_senders_should_gc_answering_for_the_restored_heap_alone() {
    // Under the threshold before the window: the gift block's bytes left with
    // the segment.
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _ = sender.alloc(BUDGET_FLOOR / 2);
    assert!(!sender.should_gc());
    sender.begin_gift(BUDGET_FLOOR);
    let _ = sender.alloc(BUDGET_FLOOR);
    assert!(sender.should_gc(), "the gift block alone crossed the threshold");
    let _segment = sender.end_gift();
    assert_eq!(sender.bytes_used(), BUDGET_FLOOR / 2);
    assert!(!sender.should_gc(), "the restored heap is under its threshold");

    // Over the threshold before the window: the window does not change that.
    let mut pressured = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _ = pressured.alloc(BUDGET_FLOOR);
    assert!(pressured.should_gc());
    pressured.begin_gift(16);
    let _ = pressured.alloc(16);
    let _segment = pressured.end_gift();
    assert_eq!(pressured.bytes_used(), BUDGET_FLOOR);
    assert!(pressured.should_gc(), "the restored heap is still over its threshold");
}

#[test]
fn an_empty_segment_grafts_as_a_no_op_and_never_touches_the_pool() {
    pool_drain_for_test();
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _ = alloc_int_list_cons(&mut receiver, 1, EMPTY_LIST);
    let bytes_before = receiver.bytes_used();
    let adopted_before = receiver.young_blocks.len();
    let cached_before = pool_total_cached_blocks();

    let segment = GiftSegment::empty();
    assert_eq!((segment.block_count(), segment.fill_bytes()), (0, 0));
    assert_eq!(segment.off_heap_head(), 0);
    receiver.graft(segment);

    assert_eq!(receiver.bytes_used(), bytes_before, "nothing was adopted");
    assert_eq!(receiver.young_blocks.len(), adopted_before);
    assert_eq!(
        pool_total_cached_blocks(),
        cached_before,
        "no block was taken or returned"
    );
    assert_eq!(off_heap_chain(&receiver), Vec::<u64>::new());
    drop(receiver);
    pool_drain_for_test();
}

#[test]
fn dropping_an_ungrafted_segment_returns_its_blocks_and_releases_its_stubs() {
    pool_drain_for_test();
    let witness = SharedBinHandle::from_bytes(&[0x55; 16]);
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pooled_before = pool_outstanding_blocks();

    sender.begin_gift(NEW_BUFFER_BYTES + 32);
    let _ = alloc_buffer_view(
        &mut sender,
        witness.clone(),
        witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let _ = sender.alloc(32);
    let segment = sender.end_gift();
    assert_eq!(segment.block_count(), 1);
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before + 1,
        "the gift block is below the table and pooled at its exact size"
    );
    assert_eq!(shared_refs(&witness), 2);
    assert_eq!(pool_total_cached_blocks(), 0);

    drop(segment);

    assert_eq!(pool_total_cached_blocks(), 1, "the gift block goes back to the pool");
    assert_eq!(pool_outstanding_blocks(), pooled_before);
    assert_eq!(shared_refs(&witness), 1, "the orphaned stub released its reference");
    drop(sender);
    pool_drain_for_test();
}

#[test]
fn a_grafted_list_is_readable_and_survives_the_receivers_gc() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let (segment, bits) = gift_one_cons(&mut sender, 7);
    receiver.graft(segment);
    assert!(receiver.contains_heap_addr(list_addr_from_tagged(bits).expect("addr")));
    let mut roots = [heap_ref(bits)];
    let stats = receiver.collect_stats(&mut roots);
    let kept = roots[0].heap_object_word().expect("kept list");
    assert_eq!(stats.generation, Generation::Minor);
    assert_ne!(kept, bits, "a gift is young: the minor collection copied the live cell");
    assert!(receiver.contains_heap_addr(list_addr_from_tagged(kept).expect("addr")));
    let head = receiver.read_list_head_ref(list_ref_from_bits(kept)).expect("head");
    assert_eq!(head.load_int().expect("int"), 7);
}

#[test]
#[should_panic(expected = "begin_gift while a gift window is already open")]
fn a_second_begin_gift_inside_a_window_is_refused() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    sender.begin_gift(16);
    sender.begin_gift(16);
}

#[test]
#[should_panic(expected = "a gift window is open")]
fn a_collection_inside_a_window_is_refused() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    sender.begin_gift(16);
    let mut root = null_mut();
    sender.collect_tagged(&mut root);
}

/// A receiver whose last collection kept 2000 bytes in a block of 192768, then it allocated 80000 bytes that all stay reachable.
fn receiver_with_live_allocation_since_a_small_collection(reg: &Rc<RefCell<SchemaRegistry>>) -> (Heap, u64) {
    let mut receiver = Heap::new(SIZE_TABLE[9], reg.clone());
    for _ in 0..60 {
        let _ = receiver.alloc(1000);
    }
    let mut live = EMPTY_LIST;
    for i in 0..125 {
        live = alloc_int_list_cons(&mut receiver, i, live);
    }
    let mut roots = [heap_ref(live)];
    receiver.collect_stats(&mut roots);
    let mut live = roots[0].heap_object_word().expect("live list");
    for i in 0..5000 {
        live = alloc_int_list_cons(&mut receiver, i, live);
    }
    (receiver, live)
}

fn gift_of_cons_cells(sender: &mut Heap, cells: i64) -> GiftSegment {
    sender.begin_gift(cells as usize * 16);
    let mut list = EMPTY_LIST;
    for i in 0..cells {
        list = alloc_int_list_cons(sender, i, list);
    }
    sender.end_gift()
}

#[test]
fn gifts_leave_the_baseline_alone_and_the_heaps_blocks_hold_every_live_byte() {
    let reg = fresh_registry();
    let (mut receiver, live) = receiver_with_live_allocation_since_a_small_collection(&reg);
    assert_eq!(receiver.live_baseline, 2000);
    assert!(
        receiver.should_gc(),
        "80000 allocated bytes are past the 2000-byte baseline"
    );
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    for _ in 0..16 {
        receiver.graft(gift_of_cons_cells(&mut sender, 60));
    }
    assert_eq!(receiver.live_baseline, 2000, "the gifts are young, not old");
    assert!(
        receiver.should_gc(),
        "the gifts' 15360 bytes join the 80000 allocated bytes past the baseline"
    );
    let mut roots = [heap_ref(live)];
    let stats = receiver.collect_stats(&mut roots);

    assert_eq!(
        receiver.bytes_used() as u64,
        stats.copied_bytes,
        "the heap's blocks hold the {} bytes copied",
        stats.copied_bytes
    );
    assert_eq!(stats.live_bytes, 2000 + 5000 * 16, "every own live byte survived");
}

#[test]
fn a_direct_collection_after_a_small_one_holds_every_live_byte_without_gifts() {
    let reg = fresh_registry();
    let (mut receiver, live) = receiver_with_live_allocation_since_a_small_collection(&reg);
    let mut roots = [heap_ref(live)];
    let stats = receiver.collect_stats(&mut roots);

    assert_eq!(receiver.bytes_used() as u64, stats.copied_bytes);
    assert_eq!(stats.live_bytes, 2000 + 5000 * 16, "every own live byte survived");
}

#[test]
#[should_panic(expected = "gift copy allocated a different number of bytes than it was measured at")]
fn end_gift_refuses_a_copy_that_allocated_less_than_its_measure() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    sender.begin_gift(32);
    let _ = sender.alloc(16);
    let _ = sender.end_gift();
}

#[test]
#[should_panic(expected = "gift copy overflowed its measured block")]
fn end_gift_refuses_a_copy_that_allocated_past_its_measured_block() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    sender.begin_gift(16);
    let _ = sender.alloc(16);
    let _ = sender.alloc(SIZE_TABLE[0]);
    let _ = sender.end_gift();
}

#[test]
fn a_gift_of_the_exact_measured_bytes_fills_its_block_without_overflow() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    for bytes in [16, SIZE_TABLE[0], SIZE_TABLE[0] + 16, SIZE_TABLE[3], TABLE_CEILING + 16] {
        sender.begin_gift(bytes);
        let _ = sender.alloc(bytes);
        let segment = sender.end_gift();
        assert_eq!(segment.block_count(), 1, "{bytes} bytes");
        assert_eq!(segment.fill_bytes(), bytes);
    }
}

/// A gift's bytes count toward the next collection exactly as the receiver's
/// own allocation does, and raise nothing old: received and allocated bytes
/// add up to the young bytes, and the baseline stays where it was.
#[test]
fn a_grafted_gift_counts_as_young_bytes_alongside_allocation() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);

    receiver.graft(gift_of_cons_cells(&mut sender, 100));
    assert_eq!(receiver.young_bytes(), 1600);
    assert_eq!(receiver.bytes_used(), 1600);
    assert_eq!(receiver.live_baseline, 0, "the gift is not old data");
    assert!(!receiver.should_gc(), "1600 young bytes are under the 4096-byte floor");

    for _ in 0..100 {
        let _ = receiver.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    }
    assert_eq!(receiver.young_bytes(), 3200, "allocation adds to the received bytes");
    assert!(!receiver.should_gc());

    receiver.graft(gift_of_cons_cells(&mut sender, 56));
    assert_eq!(receiver.young_bytes(), 3200 + 896);
    assert!(receiver.should_gc(), "4096 young bytes reach the floor");
    assert_eq!(receiver.live_baseline, 0);
    assert!(receiver.old_blocks.is_empty(), "no gift block is old");
}

/// A gift nobody keeps is garbage like any young allocation: a minor collection
/// reclaims its block, and the old generation never held it.
#[test]
fn a_dead_gift_is_reclaimed_by_a_minor_collection() {
    pool_drain_for_test();
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let (segment, bits) = gift_one_cons(&mut sender, 7);
    receiver.graft(segment);
    let gift_addr = list_addr_from_tagged(bits).expect("addr");
    assert!(receiver.contains_heap_addr(gift_addr));

    let stats = receiver.collect_stats(&mut []);

    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(stats.received_bytes, 16);
    assert_eq!(stats.copied_bytes, 0, "nothing reached the gift");
    assert_eq!(stats.live_bytes, 0);
    assert_eq!(receiver.bytes_used(), 0);
    assert!(!receiver.contains_heap_addr(gift_addr), "the gift's block was released");
    assert!(receiver.young_blocks.is_empty());
    assert!(receiver.old_blocks.is_empty());
    drop(receiver);
    drop(sender);
    pool_drain_for_test();
}

/// A gift a root reaches is copied once, by the first minor collection, and is
/// old after it: the second minor collection leaves it where it is.
#[test]
fn a_live_gift_is_copied_once_and_then_stays_in_place() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let (segment, bits) = gift_one_cons(&mut sender, 7);
    receiver.graft(segment);
    let mut roots = [heap_ref(bits)];

    let first = receiver.collect_stats(&mut roots);
    let after_first = roots[0].heap_object_word().expect("kept list");

    assert_eq!(first.generation, Generation::Minor);
    assert_eq!(first.copied_bytes, 16, "the cell was copied once");
    assert_ne!(after_first, bits);

    let second = receiver.collect_stats(&mut roots);

    assert_eq!(second.generation, Generation::Minor);
    assert_eq!(second.copied_bytes, 0, "an old cell is not copied again");
    assert_eq!(roots[0].heap_object_word().expect("kept list"), after_first);
}

/// The collection event separates the bytes a receive brought from the bytes
/// the process allocated, and counts each gift once.
#[test]
fn a_collection_reports_the_bytes_grafted_since_the_previous_one() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    receiver.graft(gift_of_cons_cells(&mut sender, 10));
    receiver.graft(gift_of_cons_cells(&mut sender, 5));
    let _ = alloc_int_list_cons(&mut receiver, 1, EMPTY_LIST);

    let first = receiver.collect_stats(&mut []);
    assert_eq!(first.received_bytes, 15 * 16);
    assert_eq!(first.young_bytes, 15 * 16 + 16);

    let second = receiver.collect_stats(&mut []);
    assert_eq!(second.received_bytes, 0);
}

/// A gift that holds both kinds of off-heap object carries them on one chain,
/// newest first, and graft splices that chain onto the receiver's young chain.
#[test]
fn a_gift_carries_binary_and_resource_stubs_on_one_chain() {
    let witness = SharedBinHandle::from_bytes(&[1, 2, 3, 4]);
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);

    sender.begin_gift(NEW_BUFFER_BYTES + RESOURCE_STUB_SIZE);
    let witness_bits = witness.bytes_len() as u64 * 8;
    let binary = binref_word(&alloc_buffer_view(
        &mut sender,
        witness,
        witness_bits,
        StubSite::FilledBuffer,
    ));
    let resource = heap_object_word(
        alloc_resource(&mut sender, ResourceHandle::new(1, TEST_DESTRUCTOR)).as_raw(),
        ValueKind::RESOURCE,
    );
    let segment = sender.end_gift();
    assert_eq!(sender.off_heap_head, 0);
    assert_eq!(segment.off_heap_head(), resource);
    assert_eq!(chain_from(segment.off_heap_head()), vec![resource, binary]);

    receiver.graft(segment);
    assert_eq!(chain_from(receiver.off_heap_head), vec![resource, binary]);
    assert_eq!(receiver.off_heap_old_head, 0);
}

/// The collection budget as the formula states it, from the heap's facts.
fn due_by_the_budget_formula(heap: &Heap) -> bool {
    let budget = heap
        .live_baseline
        .min(SIZE_TABLE[SIZE_TABLE.len() - 1])
        .max(BUDGET_FLOOR);
    heap.young_bytes() >= budget || heap.binary_budget.is_due()
}

/// The one compare at a park answers what the budget formula answers, after
/// each thing that changes its inputs: allocation that climbs to a new tip, a
/// graft, a shared binary that makes the binary budget due, and a collection.
#[test]
fn the_park_check_is_one_compare_that_agrees_with_the_budget_across_a_park_a_graft_and_a_binary() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut checked = 0;
    let mut check = |heap: &Heap, what: &str| {
        assert_eq!(heap.should_gc(), due_by_the_budget_formula(heap), "{what}");
        checked += 1;
    };
    check(&heap, "a new heap");

    while heap.young_blocks.is_empty() {
        let _ = heap.alloc(16);
        check(&heap, "allocation that has not climbed");
    }
    check(&heap, "after the tip climbed and parked a block");
    assert!(!heap.should_gc(), "a parked block under the floor is not due");

    for i in 0..300 {
        let (segment, _) = gift_one_cons(&mut sender, i);
        heap.graft(segment);
        check(&heap, "after a graft");
    }
    assert!(heap.should_gc(), "the grafts took the young bytes past the floor");

    let mut roots: [AnyValueRef; 0] = [];
    heap.collect_stats(&mut roots);
    check(&heap, "after a collection");
    assert!(!heap.should_gc(), "nothing was live, so nothing is due");
    assert!(heap.collect_room > 0, "a collection gives the tip its budget back");

    for _ in 0..3 {
        let _ = heap.alloc_bitstring_with(100_000, 800_000, |dest| dest.fill(std::mem::MaybeUninit::new(7)));
        check(&heap, "after a shared binary");
    }
    assert!(heap.binary_budget.is_due());
    assert_eq!(
        heap.collect_room, 0,
        "a due binary budget leaves the tip no room, so the next check collects"
    );
    assert!(heap.should_gc());

    let _ = heap.alloc(16);
    check(&heap, "an allocation while the binary budget is due");
    heap.collect_stats(&mut roots);
    check(&heap, "after the collection the binary budget asked for");
    assert!(!heap.should_gc());
    assert!(checked > 300);
}
