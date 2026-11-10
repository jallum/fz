//! A heap opens a gift window, cuts the segment, and another heap grafts it.
//! Each test states the property it holds the gift window to.

use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, EMPTY_LIST, ValueKind, heap_kind_from_tagged, heap_object_word, heap_word_addr,
    list_addr_from_tagged, procbin_addr_from_tagged, struct_addr_from_tagged, struct_size_for_payload,
};
use crate::procbin::{PROCBIN_BYTES, ProcBin, SharedBinHandle, alloc_procbin};
use crate::resource::ResourceStub;
use crate::sync::Ordering;
use std::cell::RefCell;
use std::ptr::null_mut;
use std::rc::Rc;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

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

fn procbin_word(pb: &ProcBin) -> u64 {
    heap_object_word(pb.as_raw() as *const u8, ValueKind::PROCBIN)
}

/// The heap's mso chain as tagged words, head first.
fn mso_chain(h: &Heap) -> Vec<u64> {
    let mut out = Vec::new();
    let mut cur_bits = h.mso_head;
    while cur_bits != 0 {
        let addr = heap_word_addr(cur_bits);
        let next = match heap_kind_from_tagged(cur_bits) {
            Some(ValueKind::PROCBIN) => unsafe { ProcBin::from_raw(addr).mso_next() },
            Some(ValueKind::RESOURCE) => unsafe { ResourceStub::from_raw(addr).mso_next() },
            kind => panic!("unexpected MSO kind {kind:?}"),
        };
        out.push(cur_bits);
        cur_bits = next;
    }
    out
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
fn a_gift_below_the_table_occupies_an_exact_block_of_its_measured_size() {
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
            pooled_before,
            "an exact block is not a pooled block"
        );
    }
    assert_eq!(sender.block_size, SIZE_TABLE[0], "the tip is untouched by the gifts");
}

#[test]
fn end_gift_restores_the_senders_tip_and_leaves_its_earlier_allocations_untouched() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let kept = alloc_int_list_cons(&mut sender, 42, EMPTY_LIST);
    let (start, top, capacity) = (sender.block_start, sender.bump_top, sender.block_size);
    let (bytes_used, live_count) = (sender.bytes_used(), sender.live_count());

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
        sender.blocks.is_empty(),
        "the measured bytes fit; the window never overflows"
    );
    let segment = sender.end_gift();

    assert_eq!(segment.block_count(), 1, "the segment is the one gift block");
    assert_eq!(segment.fill_bytes(), 1008 + 64);
    assert_eq!(
        (sender.block_start, sender.bump_top, sender.block_size),
        (start, top, capacity)
    );
    assert!(sender.blocks.is_empty(), "the sender's own chain is as it was");
    assert_eq!(sender.bytes_used(), bytes_used);
    assert_eq!(
        sender.live_count(),
        live_count,
        "gift objects are not the sender's live objects"
    );
    let head = sender.read_list_head_ref(list_ref_from_bits(kept)).expect("head");
    assert_eq!(head.load_int().expect("int"), 42);
    assert_eq!(
        sender.alloc_stats_snapshot().other.allocs,
        2,
        "allocation statistics stay with the heap that did the copying"
    );
}

#[test]
fn a_gift_with_a_shared_bin_stub_survives_the_receivers_gc_on_its_mso_chain() {
    pool_drain_for_test();
    let witness = SharedBinHandle::from_bytes(&[0xaa; 8], 64);
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);

    sender.begin_gift(PROCBIN_BYTES);
    let pb = alloc_procbin(&mut sender, witness.clone(), 0);
    let gifted = procbin_word(&pb);
    let segment = sender.end_gift();
    assert_eq!(sender.mso_head, 0, "the stub left the sender's chain");
    assert_eq!(segment.mso_head(), gifted);
    assert_eq!(shared_refs(&witness), 2, "the segment holds the heap-owned reference");

    receiver.graft(segment);
    assert_eq!(mso_chain(&receiver), vec![gifted]);
    let mut root = gifted as *mut u8;
    assert_eq!(pool_total_cached_blocks(), 0);
    receiver.collect_tagged(&mut root);

    let moved = procbin_addr_from_tagged(root as u64).expect("procbin root");
    assert_ne!(moved, pb.as_raw(), "the stub was copied out of the adopted block");
    assert_eq!(
        mso_chain(&receiver),
        vec![heap_object_word(moved as *const u8, ValueKind::PROCBIN)],
        "the chain now names the to-space copy"
    );
    assert_eq!(unsafe { ProcBin::from_raw(moved) }.shared_raw(), witness.as_raw());
    assert_eq!(shared_refs(&witness), 2, "the refcount is unchanged by the move");
    assert_eq!(
        pool_total_cached_blocks(),
        1,
        "the receiver's old tip is back in the pool; the exact gift block went to the system allocator"
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
fn graft_splices_the_gifts_mso_prefix_ahead_of_the_receivers_chain() {
    let witness = SharedBinHandle::from_bytes(&[1, 2, 3, 4], 32);
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let sender_own = procbin_word(&alloc_procbin(&mut sender, witness.clone(), 0));
    let receiver_own = procbin_word(&alloc_procbin(&mut receiver, witness.clone(), 0));

    sender.begin_gift(2 * PROCBIN_BYTES);
    let older = procbin_word(&alloc_procbin(&mut sender, witness.clone(), 1));
    let newer = procbin_word(&alloc_procbin(&mut sender, witness.clone(), 2));
    let segment = sender.end_gift();

    assert_eq!(
        mso_chain(&sender),
        vec![sender_own],
        "the sender keeps only its own stub"
    );
    receiver.graft(segment);
    assert_eq!(
        mso_chain(&receiver),
        vec![newer, older, receiver_own],
        "the gift's stubs come first, newest to oldest, then the receiver's own"
    );
    assert_eq!(shared_refs(&witness), 5);
    drop(receiver);
    assert_eq!(
        shared_refs(&witness),
        2,
        "the receiver released its own stub and both adopted ones"
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
    assert!(stats.to_space_capacity_bytes as usize >= size);
    assert_eq!(stats.live_bytes, receiver.last_gc_live_bytes as u64);
    drop(receiver);
    drop(sender);
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before - 2,
        "every pooled block came back"
    );
}

#[test]
fn thousands_of_small_unread_gifts_leave_the_receivers_capacity_unchanged_after_gc() {
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
    assert!(!receiver.should_gc());

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
    assert!(receiver.should_gc(), "adopted fill counts toward should_gc");
    let mut roots = [heap_ref(list)];
    let stats = receiver.collect(&mut roots);

    assert_eq!(receiver.block_size, capacity_before, "dead gifts do not grow the heap");
    assert_eq!(
        stats.to_space_capacity_bytes, SIZE_TABLE[11] as u64,
        "to-space is sized from the 128000 bytes in use (32000 own, 96000 adopted) and the gifts are dead"
    );
    assert_eq!(stats.live_bytes, own_live as u64, "none of the gifts was reachable");
    assert!(receiver.blocks.is_empty());
    assert_eq!(
        pool_total_cached_blocks(),
        1,
        "the old tip went back to the pool; each exact gift block went to the system allocator"
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
    let _ = sender.alloc(256);
    assert!(!sender.should_gc());
    sender.begin_gift(608);
    let _ = sender.alloc(608);
    assert!(sender.should_gc(), "the gift block alone crossed the threshold");
    let _segment = sender.end_gift();
    assert_eq!(sender.bytes_used(), 256);
    assert!(!sender.should_gc(), "the restored heap is under its threshold");

    // Over the threshold before the window: the window does not change that.
    let mut pressured = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _ = pressured.alloc(608);
    assert!(pressured.should_gc());
    pressured.begin_gift(16);
    let _ = pressured.alloc(16);
    let _segment = pressured.end_gift();
    assert_eq!(pressured.bytes_used(), 608);
    assert!(pressured.should_gc(), "the restored heap is still over its threshold");
}

#[test]
fn an_empty_segment_grafts_as_a_no_op_and_never_touches_the_pool() {
    pool_drain_for_test();
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let _ = alloc_int_list_cons(&mut receiver, 1, EMPTY_LIST);
    let bytes_before = receiver.bytes_used();
    let adopted_before = receiver.blocks.len();
    let cached_before = pool_total_cached_blocks();

    let segment = GiftSegment::empty();
    assert_eq!((segment.block_count(), segment.fill_bytes()), (0, 0));
    assert_eq!(segment.mso_head(), 0);
    receiver.graft(segment);

    assert_eq!(receiver.bytes_used(), bytes_before, "nothing was adopted");
    assert_eq!(receiver.blocks.len(), adopted_before);
    assert_eq!(
        pool_total_cached_blocks(),
        cached_before,
        "no block was taken or returned"
    );
    assert_eq!(mso_chain(&receiver), Vec::<u64>::new());
    drop(receiver);
    pool_drain_for_test();
}

#[test]
fn dropping_an_ungrafted_segment_returns_its_blocks_and_releases_its_stubs() {
    pool_drain_for_test();
    let witness = SharedBinHandle::from_bytes(&[0x55; 16], 128);
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pooled_before = pool_outstanding_blocks();

    sender.begin_gift(PROCBIN_BYTES + 32);
    let _ = alloc_procbin(&mut sender, witness.clone(), 0);
    let _ = sender.alloc(32);
    let segment = sender.end_gift();
    assert_eq!(segment.block_count(), 1);
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before,
        "the gift block is exact, below the table, and not pooled"
    );
    assert_eq!(shared_refs(&witness), 2);
    assert_eq!(pool_total_cached_blocks(), 0);

    drop(segment);

    assert_eq!(
        pool_total_cached_blocks(),
        0,
        "an exact gift block goes back to the system allocator, not the pool"
    );
    assert_eq!(
        pool_outstanding_blocks(),
        pooled_before,
        "the exact blocks never counted"
    );
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
    receiver.collect(&mut roots);
    let moved = roots[0].heap_object_word().expect("moved list");
    assert_ne!(moved, bits, "the cell moved into the receiver's to-space");
    let head = receiver.read_list_head_ref(list_ref_from_bits(moved)).expect("head");
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

/// A receiver in the SHRINK band: its last collection kept 2000 bytes in a
/// block of 192768, then it allocated 80000 bytes that all stay reachable.
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
    receiver.collect(&mut roots);
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
fn gifts_alone_make_should_gc_true_and_to_space_holds_every_live_byte() {
    let reg = fresh_registry();
    let (mut receiver, live) = receiver_with_live_allocation_since_a_small_collection(&reg);
    assert!(
        !receiver.should_gc(),
        "80000 live bytes in a 192768-byte block are under half"
    );
    let mut sender = Heap::new(SIZE_TABLE[0], reg);
    for _ in 0..16 {
        receiver.graft(gift_of_cons_cells(&mut sender, 60));
    }
    assert!(
        receiver.should_gc(),
        "the gifts' fill carried the heap over half its block"
    );
    let mut roots = [heap_ref(live)];
    let stats = receiver.collect(&mut roots);

    assert!(
        stats.to_space_capacity_bytes >= stats.copied_bytes,
        "to-space of {} cannot hold the {} bytes copied",
        stats.to_space_capacity_bytes,
        stats.copied_bytes
    );
    assert_eq!(stats.live_bytes, 2000 + 5000 * 16, "every own live byte survived");
}

#[test]
fn a_direct_collection_in_the_shrink_band_holds_every_live_byte_without_gifts() {
    let reg = fresh_registry();
    let (mut receiver, live) = receiver_with_live_allocation_since_a_small_collection(&reg);
    let mut roots = [heap_ref(live)];
    let stats = receiver.collect(&mut roots);

    assert!(stats.to_space_capacity_bytes >= stats.copied_bytes);
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
