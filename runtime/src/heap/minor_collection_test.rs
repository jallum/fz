//! A collection copies what was allocated since the last one; what an earlier
//! collection kept stays where it is until a major collection.

use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, EMPTY_LIST, ListCons, ValueKind, heap_kind_from_tagged, heap_object_word,
    list_addr_from_tagged,
};
use crate::procbin::{SharedBinHandle, alloc_procbin};
use crate::sync::Ordering;
use std::cell::RefCell;
use std::rc::Rc;

fn fresh_registry() -> Rc<RefCell<SchemaRegistry>> {
    Rc::new(RefCell::new(SchemaRegistry::new()))
}

fn cons(heap: &mut Heap, head: i64, tail_bits: u64) -> u64 {
    heap.alloc_list_cons_slot(AnyValue::int(head), tail_bits)
}

fn root_of(bits: u64) -> AnyValueRef {
    let kind = heap_kind_from_tagged(bits).expect("tagged heap root");
    AnyValueRef::from_raw_word(bits)
        .inspect(|root| assert_eq!(root.tag(), kind))
        .expect("heap root ref")
}

/// Collect with `bits` as the only root and return the forwarded bits.
fn collect_list(heap: &mut Heap, bits: u64) -> (u64, GcStats) {
    let mut roots = [root_of(bits)];
    let stats = heap.collect(&mut roots);
    (roots[0].heap_object_word().expect("forwarded list"), stats)
}

#[test]
fn a_heap_that_retains_a_thin_slice_of_what_it_allocates_copies_each_retained_byte_a_bounded_number_of_times() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut retained = EMPTY_LIST;
    let (mut collections, mut copied, mut live) = (0u64, 0u64, 0u64);
    for step in 0..1_000_000i64 {
        if step % 32 == 0 {
            retained = cons(&mut heap, step, retained);
        } else {
            cons(&mut heap, step, EMPTY_LIST);
        }
        if heap.should_gc() {
            let (bits, stats) = collect_list(&mut heap, retained);
            retained = bits;
            collections += 1;
            copied += stats.copied_bytes;
            live = stats.live_bytes;
        }
    }
    assert!(collections >= 100, "the run collects often: {collections}");
    assert!(
        copied <= 4 * live,
        "{collections} collections copied {copied} bytes for {live} live bytes"
    );
}

/// A list of `len` cells, heads counting up from `first`, ending in `tail_bits`.
fn list_of(heap: &mut Heap, first: i64, len: i64, tail_bits: u64) -> u64 {
    (first..first + len).fold(tail_bits, |tail, head| cons(heap, head, tail))
}

/// A list of `len` cells sent from `sender`, as the scheduler sends one: copied
/// through a gift window into a segment, with the bits of the copy's head.
fn gift_of_list(sender: &mut Heap, first: i64, len: i64) -> (GiftSegment, u64) {
    let source = list_of(sender, first, len, EMPTY_LIST);
    let (segment, copied) = crate::sched::gift_copy(sender, &[root_of(source)]);
    (segment, copied[0].heap_object_word().expect("copied list"))
}

fn tail_addr(bits: u64) -> u64 {
    let cell = list_addr_from_tagged(bits).expect("list cell") as *const ListCons;
    unsafe { (*cell).tail_addr() }
}

fn shared_refs(handle: &SharedBinHandle) -> usize {
    unsafe { (*handle.as_raw()).refcount.load(Ordering::Relaxed) }
}

#[test]
fn a_minor_collection_leaves_an_old_object_where_it_is_and_a_major_one_moves_it() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let list = list_of(&mut heap, 0, 8, EMPTY_LIST);
    let (old, stats) = collect_list(&mut heap, list);
    assert_eq!(stats.generation, Generation::Minor, "nothing is old yet");
    assert_ne!(old, list, "the young list was copied into an old block");

    let young = cons(&mut heap, 99, old);
    let (young, stats) = collect_list(&mut heap, young);
    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(stats.copied_bytes, 16, "only the young cell was copied");
    assert_eq!(
        tail_addr(young),
        list_addr_from_tagged(old).unwrap() as u64,
        "the old list did not move"
    );

    let more = list_of(&mut heap, 100, 200, young);
    let (more, stats) = collect_list(&mut heap, more);
    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(stats.live_bytes, (8 + 1 + 200) * 16);

    let (_, stats) = collect_list(&mut heap, more);
    assert_eq!(
        stats.generation,
        Generation::Major,
        "the old bytes outgrew what the last major kept"
    );
    assert_eq!(
        stats.copied_bytes,
        (8 + 1 + 200) * 16,
        "a major collection copies every live object"
    );
}

#[test]
fn old_data_that_died_is_reclaimed_by_the_next_major_collection_and_not_before() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let doomed = list_of(&mut heap, 0, 400, EMPTY_LIST);
    let (doomed, stats) = collect_list(&mut heap, doomed);
    assert_eq!(stats.generation, Generation::Minor);
    let (_, stats) = collect_list(&mut heap, doomed);
    assert_eq!(
        stats.generation,
        Generation::Major,
        "6400 old bytes against a floor of 512"
    );
    assert_eq!(heap.old_after_last_major, 400 * 16);

    let kept = list_of(&mut heap, 0, 100, EMPTY_LIST);
    let (kept, stats) = collect_list(&mut heap, kept);
    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(stats.live_bytes, (400 + 100) * 16, "the dead old list is still held");

    let kept = list_of(&mut heap, 100, 400, kept);
    let (kept, stats) = collect_list(&mut heap, kept);
    assert_eq!(
        stats.generation,
        Generation::Minor,
        "800 of 1,600 live bytes is not past twice 6,400"
    );
    assert_eq!(stats.live_bytes, (400 + 100 + 400) * 16);

    let (_, stats) = collect_list(&mut heap, kept);
    assert_eq!(
        stats.generation,
        Generation::Major,
        "old bytes passed twice what the last major kept"
    );
    assert_eq!(stats.live_bytes, (100 + 400) * 16, "the dead old list was reclaimed");
    assert_eq!(heap.live_baseline, 500 * 16);
    assert_eq!(heap.old_after_last_major, 500 * 16);
}

/// A binary stub is found dead by the collection that examines its chain: a
/// young one by the minor collection, an old one only by a major collection.
#[test]
fn an_old_procbin_that_died_is_released_by_a_major_collection_and_a_young_one_by_a_minor() {
    let old_witness = SharedBinHandle::from_bytes(&[1; 8], 64);
    let young_witness = SharedBinHandle::from_bytes(&[2; 8], 64);
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let old = alloc_procbin(&mut heap, old_witness.clone(), 0);
    let mut roots = [root_of(heap_object_word(old.as_raw(), ValueKind::PROCBIN))];
    assert_eq!(heap.collect(&mut roots).generation, Generation::Minor);
    assert_ne!(heap.mso_old_head, 0, "the survivor is on the old chain");
    assert_eq!(heap.mso_head, 0);

    alloc_procbin(&mut heap, young_witness.clone(), 0);
    assert_eq!(shared_refs(&young_witness), 2);
    let stats = heap.collect(&mut []);
    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(
        shared_refs(&young_witness),
        1,
        "the minor sweep released the young stub"
    );
    assert_eq!(
        shared_refs(&old_witness),
        2,
        "the old stub is not examined by a minor sweep"
    );

    let retained = list_of(&mut heap, 0, 100, EMPTY_LIST);
    let (retained, stats) = collect_list(&mut heap, retained);
    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(shared_refs(&old_witness), 2);

    let (_, stats) = collect_list(&mut heap, retained);
    assert_eq!(stats.generation, Generation::Major);
    assert_eq!(shared_refs(&old_witness), 1, "the major sweep released the old stub");
    assert_eq!((heap.mso_head, heap.mso_old_head), (0, 0));
}

/// Dropping the heap releases the stubs of both chains.
#[test]
fn dropping_a_heap_releases_its_young_and_its_old_stubs() {
    let witnesses = [
        SharedBinHandle::from_bytes(&[1], 8),
        SharedBinHandle::from_bytes(&[2], 8),
    ];
    {
        let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
        let old = alloc_procbin(&mut heap, witnesses[0].clone(), 0);
        let mut roots = [root_of(heap_object_word(old.as_raw(), ValueKind::PROCBIN))];
        heap.collect(&mut roots);
        alloc_procbin(&mut heap, witnesses[1].clone(), 0);
        assert_eq!(witnesses.each_ref().map(shared_refs), [2, 2]);
    }
    assert_eq!(witnesses.each_ref().map(shared_refs), [1, 1]);
}

#[test]
fn a_grafted_gift_is_old_so_a_minor_collection_leaves_it_and_what_points_at_it_stays_valid() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let (segment, gift) = gift_of_list(&mut sender, 1, 3);
    receiver.graft(segment);
    assert_eq!(receiver.live_baseline, 3 * 16, "the gift is old bytes, not allocation");

    let above = cons(&mut receiver, 0, gift);
    let (above, stats) = collect_list(&mut receiver, above);

    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(stats.copied_bytes, 16, "only the receiver's own cell was copied");
    assert_eq!(stats.live_bytes, 4 * 16);
    assert_eq!(
        tail_addr(above),
        list_addr_from_tagged(gift).unwrap() as u64,
        "the gift stayed in place"
    );
    let mut sum = 0;
    let mut cursor = root_of(above);
    while !cursor.is_empty_list() {
        sum += receiver
            .read_list_head_ref(cursor)
            .expect("head")
            .load_int()
            .expect("int");
        cursor = receiver.read_list_tail_ref(cursor).expect("tail");
    }
    assert_eq!(sum, 1 + 2 + 3);
}

/// An old cell must never come to point at a value made after it, and a
/// grafted gift is old: its cells refuse an in-place rewrite as a kept cell does.
#[test]
fn a_grafted_list_cell_is_not_rewritten_in_place() {
    let reg = fresh_registry();
    let mut sender = Heap::new(SIZE_TABLE[0], reg.clone());
    let mut receiver = Heap::new(SIZE_TABLE[0], reg);
    let (segment, gift) = gift_of_list(&mut sender, 1, 2);
    receiver.graft(segment);
    let young = cons(&mut receiver, 7, EMPTY_LIST);

    let rebuilt = receiver
        .reuse_or_alloc_list_cons_raw_kind(root_of(gift), 5, ValueKind::INT, root_of(young), true)
        .expect("rebuild");

    assert_ne!(rebuilt, root_of(gift), "a fresh cell was allocated");
    assert_ne!(tail_addr(gift), list_addr_from_tagged(young).unwrap() as u64);
}
