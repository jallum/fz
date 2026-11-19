//! A collection copies what was allocated since the last one; what an earlier
//! collection kept stays where it is until a major collection.

use super::*;
use crate::any_value::{
    AnyValue, AnyValueRef, EMPTY_LIST, ListCons, ValueKind, heap_kind_from_tagged, heap_object_word,
    list_addr_from_tagged,
};
use crate::bits::{BinView, SharedBinHandle, alloc_buffer_view};
use crate::heap::{StubCounts, StubSite};
use crate::off_heap;
use crate::resource::{ResourceHandle, alloc_resource};
use crate::sync::Ordering;
use std::cell::RefCell;
use std::rc::Rc;

/// A destructor word the test never dispatches: the resource only carries it.
const TEST_DESTRUCTOR: u64 = 0xD7;

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

/// A BinRef is found dead by the collection that examines its chain: a
/// young one by the minor collection, an old one only by a major collection.
#[test]
fn an_old_binref_that_died_is_released_by_a_major_collection_and_a_young_one_by_a_minor() {
    let old_witness = SharedBinHandle::from_bytes(&[1; 8]);
    let young_witness = SharedBinHandle::from_bytes(&[2; 8]);
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let old = alloc_buffer_view(
        &mut heap,
        old_witness.clone(),
        old_witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
    let mut roots = [root_of(heap_object_word(old.as_raw(), ValueKind::BINVIEW))];
    assert_eq!(heap.collect(&mut roots).generation, Generation::Minor);
    assert_ne!(heap.off_heap_old_head, 0, "the survivor is on the old chain");
    assert_eq!(heap.off_heap_head, 0);

    alloc_buffer_view(
        &mut heap,
        young_witness.clone(),
        young_witness.bytes_len() as u64 * 8,
        StubSite::FilledBuffer,
    );
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
    assert_eq!((heap.off_heap_head, heap.off_heap_old_head), (0, 0));
}

/// Dropping the heap releases the stubs of both chains.
#[test]
fn dropping_a_heap_releases_its_young_and_its_old_stubs() {
    let witnesses = [SharedBinHandle::from_bytes(&[1]), SharedBinHandle::from_bytes(&[2])];
    {
        let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
        let old = alloc_buffer_view(
            &mut heap,
            witnesses[0].clone(),
            witnesses[0].bytes_len() as u64 * 8,
            StubSite::FilledBuffer,
        );
        let mut roots = [root_of(heap_object_word(old.as_raw(), ValueKind::BINVIEW))];
        heap.collect(&mut roots);
        alloc_buffer_view(
            &mut heap,
            witnesses[1].clone(),
            witnesses[1].bytes_len() as u64 * 8,
            StubSite::FilledBuffer,
        );
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

fn alloc_unrooted_stubs(heap: &mut Heap, binaries: usize, resources: usize) {
    for _ in 0..binaries {
        alloc_buffer_view(heap, SharedBinHandle::from_bytes(&[7; 8]), 64, StubSite::FilledBuffer);
    }
    for _ in 0..resources {
        let handle = ResourceHandle::new(1, TEST_DESTRUCTOR);
        alloc_resource(heap, handle);
    }
}

/// A collection decides each binary stub in one walk: a heap of binary stubs
/// and no resources follows one chain link per stub, whether the stubs die or
/// survive.
#[test]
fn a_collection_follows_one_link_per_binary_stub() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    alloc_unrooted_stubs(&mut heap, 5, 0);
    assert_eq!(heap.collect(&mut []).stub_visits, 5, "dead stubs");

    let survivors: Vec<AnyValueRef> = (0..5)
        .map(|_| {
            let pb = alloc_buffer_view(
                &mut heap,
                SharedBinHandle::from_bytes(&[7; 8]),
                64,
                StubSite::FilledBuffer,
            );
            root_of(heap_object_word(pb.as_raw(), ValueKind::BINVIEW))
        })
        .collect();
    let mut roots = survivors;
    assert_eq!(heap.collect(&mut roots).stub_visits, 5, "surviving stubs");
}

/// A collection decides every stub, binary or resource, in one walk, so a
/// heap of N binary stubs and R resource stubs follows N + R chain links: no
/// separate search precedes the sweep.
#[test]
fn a_collection_walks_the_binary_and_resource_stubs_once_each() {
    let (binaries, resources) = (4, 3);
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    alloc_unrooted_stubs(&mut heap, binaries, resources);

    let mut sweep_visits = 0;
    off_heap::sweep(
        &mut heap,
        Generation::Minor,
        &mut sweep_visits,
        &mut StubCounts::default(),
    );
    assert_eq!(sweep_visits, (binaries + resources) as u64);
    assert_eq!(
        heap.pending_dtors.len(),
        resources,
        "every dead unclaimed resource queued its destructor"
    );

    alloc_unrooted_stubs(&mut heap, binaries, resources);
    assert_eq!(heap.collect(&mut []).stub_visits, (binaries + resources) as u64);
}

/// One chain holds both kinds, interleaved as they were allocated, and one
/// sweep decides each: a dead BinRef releases its buffer, a dead unclaimed
/// resource queues (destructor, payload) newest first, and each survivor is
/// relinked onto the old chain in its own kind.
#[test]
fn one_sweep_decides_interleaved_binrefs_and_resources() {
    let buffers = [
        SharedBinHandle::from_bytes(&[1; 8]),
        SharedBinHandle::from_bytes(&[2; 8]),
        SharedBinHandle::from_bytes(&[3; 8]),
    ];
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut views = Vec::new();
    let mut resources = Vec::new();
    for (payload, buffer) in (1u64..).zip(&buffers) {
        views.push(alloc_buffer_view(&mut heap, buffer.clone(), 64, StubSite::FilledBuffer));
        resources.push(alloc_resource(&mut heap, ResourceHandle::new(payload, TEST_DESTRUCTOR)));
    }
    let mut roots = [
        root_of(heap_object_word(views[1].as_raw(), ValueKind::BINVIEW)),
        root_of(heap_object_word(resources[1].as_raw(), ValueKind::RESOURCE)),
    ];

    let stats = heap.collect(&mut roots);

    assert_eq!(stats.generation, Generation::Minor);
    assert_eq!(stats.stub_visits, 6, "one visit per off-heap object");
    let released = |buffer: &SharedBinHandle| unsafe { (*buffer.as_raw()).refcount.load(Ordering::Relaxed) };
    assert_eq!(
        [&buffers[0], &buffers[1], &buffers[2]].map(released),
        [1, 2, 1],
        "only the live buffer keeps the heap's reference"
    );
    assert_eq!(
        heap.pending_dtors,
        [(TEST_DESTRUCTOR, 3), (TEST_DESTRUCTOR, 1)],
        "the dead resources queued, newest first; the live one did not"
    );
    let old = heap.off_heap_old_head;
    assert_eq!(heap_kind_from_tagged(old), Some(ValueKind::BINREF));
    let binref = unsafe { crate::bits::BinRef::from_raw(crate::any_value::heap_word_addr(old)) };
    assert_eq!(heap_kind_from_tagged(binref.off_heap_next()), Some(ValueKind::RESOURCE));
    assert_eq!(
        unsafe { crate::resource::ResourceStub::from_raw(crate::any_value::heap_word_addr(binref.off_heap_next())) }
            .off_heap_next(),
        0,
        "the survivors are the whole old chain"
    );
    assert_eq!(heap.off_heap_head, 0);
}

/// A minor collection follows only the young chain; a major collection also
/// follows the old chain, where both kinds of survivor sit.
#[test]
fn a_major_collection_follows_the_old_chain_and_a_minor_does_not() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let pb = alloc_buffer_view(
        &mut heap,
        SharedBinHandle::from_bytes(&[7; 8]),
        64,
        StubSite::FilledBuffer,
    );
    let rs = alloc_resource(&mut heap, ResourceHandle::new(1, TEST_DESTRUCTOR));
    let ballast = list_of(&mut heap, 0, 400, EMPTY_LIST);
    let mut roots = [
        root_of(heap_object_word(pb.as_raw(), ValueKind::BINVIEW)),
        root_of(heap_object_word(rs.as_raw(), ValueKind::RESOURCE)),
        root_of(ballast),
    ];
    let first = heap.collect(&mut roots);
    assert_eq!(first.generation, Generation::Minor);
    assert_eq!(first.stub_visits, 2, "one sweep link per stub");
    assert_ne!(heap.off_heap_old_head, 0, "both survivors are on the one old chain");
    assert_eq!(heap.off_heap_head, 0);

    let second = heap.collect(&mut roots);
    assert_eq!(second.generation, Generation::Major);
    assert_eq!(second.stub_visits, 2, "the major collection follows the old chain");
    assert_ne!(heap.off_heap_old_head, 0);
}

/// A minor collection looks inside every young object, so a write into one is
/// safe wherever it sits: in the tip, or in the block a huge object is parked
/// alone in. Only the tip is the range `[block_start, bump_top)` that compiled
/// code can test inline.
#[test]
fn a_huge_object_parked_alone_is_young_though_it_lies_outside_the_tip() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let small = heap.alloc(16);
    let huge = heap.alloc(1 << 20);

    assert!(heap.is_young(small));
    assert!(heap.is_young(huge), "a parked block is young");
    let in_tip = |p: *mut u8| heap.block_start <= p && p < heap.bump_top;
    assert!(in_tip(small));
    assert!(!in_tip(huge), "the huge object does not move the tip");
}

fn counts(pairs: &[(StubSite, u64)]) -> StubCounts {
    let mut counts = StubCounts::default();
    for &(site, n) in pairs {
        for _ in 0..n {
            counts.record(site);
        }
    }
    counts
}

fn bytes_of(value: AnyValue) -> (BinView, Vec<u8>) {
    let stub = unsafe { BinView::from_raw(value.heap_addr().expect("a stub")) };
    let bytes = unsafe { std::slice::from_raw_parts(stub.bytes_ptr(), stub.bytes_len()) }.to_vec();
    (stub, bytes)
}

/// Every place that makes a binary view is counted under its own site by the
/// heap that made it, and so is every BinRef; a minor collection reports which
/// BinRefs it kept. Each site is driven once through the call that production
/// code uses. A window and an in-place append make a view and no BinRef.
#[test]
fn a_minor_collection_counts_the_views_and_binrefs_each_site_made_and_the_binrefs_it_kept() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let big = vec![1u8; SHARED_BIN_THRESHOLD_BYTES + 1];

    let filled = heap.alloc_bitstring(&big, big.len() as u64 * 8);
    let grown = unsafe { heap.alloc_concatenation(&big, None, &[2]) };
    let (grown_stub, grown_bytes) = bytes_of(grown);
    let appended = unsafe { heap.alloc_concatenation(&grown_bytes, Some(grown_stub), &[3]) };
    let window = unsafe { heap.alloc_bitstring_slice(grown_stub, 1, big.len() as u64) };

    let mut roots = [filled, appended, window].map(AnyValue::ref_word);
    let stats = heap.collect(&mut roots);

    assert_eq!(
        stats.stubs_made,
        counts(&[
            (StubSite::FilledBuffer, 1),
            (StubSite::GrownBuffer, 1),
            (StubSite::AppendedInPlace, 1),
            (StubSite::WindowOfBuffer, 1),
        ]),
        "each call made one view under its own site"
    );
    assert_eq!(
        stats.binrefs_made,
        counts(&[(StubSite::FilledBuffer, 1), (StubSite::GrownBuffer, 1)]),
        "only the calls that brought a buffer into the heap made a BinRef"
    );
    assert_eq!(
        stats.stubs_survived,
        counts(&[(StubSite::FilledBuffer, 1), (StubSite::GrownBuffer, 1)]),
        "the grown buffer's own view died, but the appended view and the window kept its BinRef"
    );
    assert_eq!(stats.stub_visits, 2, "one visit per BinRef, however many views name it");

    let again = heap.collect(&mut roots);
    assert_eq!(
        (again.stubs_made, again.binrefs_made),
        (StubCounts::default(), StubCounts::default()),
        "made counts restart at each collection"
    );
    assert_eq!(
        again.stubs_survived,
        StubCounts::default(),
        "a minor collection does not examine old BinRefs"
    );
}

/// A major collection examines the old BinRefs too, so it counts the survivors
/// among BinRefs earlier collections kept, under the site that made them.
#[test]
fn a_major_collection_counts_old_survivors_under_their_original_site() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let big = vec![1u8; SHARED_BIN_THRESHOLD_BYTES + 1];
    let filled = heap.alloc_bitstring(&big, big.len() as u64 * 8);
    let ballast = list_of(&mut heap, 0, 400, EMPTY_LIST);
    let mut roots = [filled.ref_word(), root_of(ballast)];
    assert_eq!(heap.collect(&mut roots).generation, Generation::Minor);

    let major = heap.collect(&mut roots);
    assert_eq!(major.generation, Generation::Major);
    assert_eq!(major.stubs_made, StubCounts::default());
    assert_eq!(major.stubs_survived, counts(&[(StubSite::FilledBuffer, 1)]));
}

/// A message copy makes the receiver's view and BinRef under its own site.
#[test]
fn a_message_copy_counts_as_its_own_site_on_the_receiving_heap() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let big = vec![1u8; SHARED_BIN_THRESHOLD_BYTES + 1];
    let filled = sender.alloc_bitstring(&big, big.len() as u64 * 8);
    let copy = deep_copy_slot(filled, &sender.view(), &mut receiver);

    let stats = receiver.collect(&mut [copy.ref_word()]);
    assert_eq!(stats.stubs_made, counts(&[(StubSite::MessageCopy, 1)]));
    assert_eq!(stats.binrefs_made, counts(&[(StubSite::MessageCopy, 1)]));
    assert_eq!(stats.stubs_survived, counts(&[(StubSite::MessageCopy, 1)]));
}

/// A buffer of `len` bytes in `heap` and a witness holding a reference to it, so
/// a test can read how many references the buffer has.
fn witnessed_buffer(heap: &mut Heap, bytes: &[u8]) -> (AnyValue, SharedBinHandle) {
    let value = heap.alloc_bitstring(bytes, bytes.len() as u64 * 8);
    let witness = unsafe { SharedBinHandle::retain_from_raw(view_of(value).shared_raw()) };
    (value, witness)
}

fn view_of(value: AnyValue) -> BinView {
    unsafe { BinView::from_raw(value.heap_addr().expect("a view")) }
}

/// The view a collection left in `root`.
fn view_in(root: AnyValueRef) -> BinView {
    view_of(AnyValue::from_ref(root).expect("a heap root"))
}

fn view_bytes(view: BinView) -> Vec<u8> {
    unsafe { std::slice::from_raw_parts(view.bytes_ptr(), view.bytes_len()) }.to_vec()
}

/// Windows of a buffer take no reference of their own: the heap holds one
/// reference through the buffer's BinRef, and it stays while any view of the
/// buffer lives, whichever view that is. When the last view dies the sweep that
/// finds the BinRef unreached releases the reference.
#[test]
fn a_binref_outlives_its_buffers_own_view_and_dies_with_its_last_window() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let (whole, witness) = witnessed_buffer(&mut heap, &[9u8; 200]);
    let window = unsafe { heap.alloc_bitstring_slice(view_of(whole), 10, 100) };
    assert_eq!(window.kind(), ValueKind::BINVIEW);
    assert_eq!(
        shared_refs(&witness),
        2,
        "a window retains nothing: the witness and the BinRef"
    );
    let retained = list_of(&mut heap, 0, 100, EMPTY_LIST);

    let mut roots = [window.ref_word(), root_of(retained)];
    let first = heap.collect(&mut roots);
    assert_eq!(first.generation, Generation::Minor);
    assert_eq!(first.stub_visits, 1, "one BinRef visited for two views");
    assert_eq!(first.stubs_survived, counts(&[(StubSite::FilledBuffer, 1)]));
    assert_eq!(
        shared_refs(&witness),
        2,
        "the window kept the BinRef after the whole view died"
    );

    roots[0] = AnyValueRef::empty_list();
    let second = heap.collect(&mut roots);
    assert_eq!(second.generation, Generation::Major);
    assert_eq!(second.stub_visits, 1);
    assert_eq!(second.stubs_survived, StubCounts::default());
    assert_eq!(
        shared_refs(&witness),
        1,
        "no view names the BinRef, so the major released it"
    );
    assert_eq!(heap.off_heap_old_head, 0);
}

/// A view made after a collection can name a BinRef that collection kept. A
/// minor collection leaves that BinRef where it is, does not visit it, and the
/// young view still reads the buffer; a major collection then copies it and
/// keeps it because the view names it.
#[test]
fn a_young_view_of_an_old_binref_survives_a_minor_and_a_major_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..200u8).collect();
    let (whole, witness) = witnessed_buffer(&mut heap, &bytes);
    let mut roots = [whole.ref_word()];
    assert_eq!(heap.collect(&mut roots).generation, Generation::Minor);
    let old_whole = view_in(roots[0]);
    let old_binref = old_whole.binref().as_raw();
    assert!(!heap.is_young(old_binref), "the buffer's BinRef is old");

    let window = unsafe { heap.alloc_bitstring_slice(old_whole, 70, 100) };
    assert!(heap.is_young(view_of(window).as_raw()));
    assert_eq!(
        view_of(window).binref().as_raw(),
        old_binref,
        "the window names the old BinRef"
    );
    roots = [window.ref_word()];
    let minor = heap.collect(&mut roots);
    assert_eq!(minor.generation, Generation::Minor);
    assert_eq!(minor.stub_visits, 0, "a minor collection does not visit an old BinRef");
    let kept = view_in(roots[0]);
    assert_eq!(kept.binref().as_raw(), old_binref, "the BinRef stayed where it was");
    assert_eq!(view_bytes(kept), &bytes[70..170]);
    assert_eq!(shared_refs(&witness), 2);

    let retained = list_of(&mut heap, 0, 100, EMPTY_LIST);
    let mut roots = [roots[0], root_of(retained)];
    assert_eq!(heap.collect(&mut roots).generation, Generation::Minor);
    let major = heap.collect(&mut roots);
    assert_eq!(major.generation, Generation::Major);
    assert_eq!(major.stub_visits, 1);
    assert_eq!(major.stubs_survived, counts(&[(StubSite::FilledBuffer, 1)]));
    let moved = view_in(roots[0]);
    assert_ne!(
        moved.binref().as_raw(),
        old_binref,
        "the major collection moved the BinRef"
    );
    assert_eq!(view_bytes(moved), &bytes[70..170]);
    assert_eq!(
        shared_refs(&witness),
        2,
        "the window kept the one BinRef through the major"
    );
    drop(heap);
    assert_eq!(shared_refs(&witness), 1);
}

/// A send gives the receiver its own BinRef over the one buffer: the buffer's
/// reference count rises by one, the two heaps name different BinRefs, and each
/// heap releases exactly its own reference when it goes.
#[test]
fn a_send_gives_the_receiver_its_own_binref_and_both_heaps_release() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..200u8).collect();
    let (whole, witness) = witnessed_buffer(&mut sender, &bytes);
    assert_eq!(shared_refs(&witness), 2);

    let copy = deep_copy_slot(whole, &sender.view(), &mut receiver);
    assert_eq!(
        shared_refs(&witness),
        3,
        "the receiver's BinRef holds its own reference"
    );
    let (sent, received) = (view_of(whole), view_of(copy));
    assert_ne!(sent.binref().as_raw(), received.binref().as_raw());
    assert_eq!(sent.shared_raw(), received.shared_raw());
    assert_eq!(view_bytes(received), bytes);
    assert_eq!(receiver.off_heap_head, received.binref().word());
    assert_eq!(sender.off_heap_head, sent.binref().word());

    drop(sender);
    assert_eq!(shared_refs(&witness), 2, "the sender released its BinRef");
    assert_eq!(view_bytes(received), bytes);
    drop(receiver);
    assert_eq!(shared_refs(&witness), 1);
}

/// Collect `root` with a minor collection, then with a major one: the minor
/// promotes a retained list beside it, and the next collection is major.
fn collect_through_a_major(heap: &mut Heap, root: &mut AnyValueRef) {
    assert_eq!(heap.collect(std::slice::from_mut(root)).generation, Generation::Minor);
    let retained = list_of(heap, 0, 100, EMPTY_LIST);
    let mut roots = [*root, root_of(retained)];
    assert_eq!(heap.collect(&mut roots).generation, Generation::Minor);
    assert_eq!(heap.collect(&mut roots).generation, Generation::Major);
    *root = roots[0];
}

fn small_bitstring_is_shared(root: AnyValueRef) -> bool {
    unsafe { crate::any_value::bitstring_is_shared(root.bitstring_addr().expect("a small bitstring")) }
}

fn small_bitstring_bytes(root: AnyValueRef) -> Vec<u8> {
    let addr = root.bitstring_addr().expect("a small bitstring");
    let len = (unsafe { crate::any_value::bitstring_bit_len(addr) } as usize).div_ceil(8);
    unsafe { std::slice::from_raw_parts(crate::any_value::bitstring_bytes_ptr(addr), len) }.to_vec()
}

/// A small bitstring is born unshared. Sharing it sets the mark in its first
/// word, above the length, so the length still reads as before, and the
/// collector carries the mark through a minor and a major collection.
#[test]
fn a_small_bitstrings_shared_mark_leaves_its_length_and_survives_collection() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let small = heap.alloc_bitstring(b"abc", 24);
    let mut roots = [small.ref_word()];
    assert!(!small_bitstring_is_shared(roots[0]), "a new bitstring has one holder");

    heap.mark_published_ref_aliased(roots[0]).expect("share");
    heap.mark_published_ref_aliased(roots[0]).expect("share again");
    assert!(small_bitstring_is_shared(roots[0]));
    assert_eq!(
        heap.binaries_shared(),
        1,
        "a binary is counted once, when its mark is set"
    );
    assert_eq!(
        small_bitstring_bytes(roots[0]),
        b"abc",
        "the mark is not part of the length"
    );

    collect_through_a_major(&mut heap, &mut roots[0]);
    assert!(small_bitstring_is_shared(roots[0]), "collection keeps the mark");
    assert_eq!(small_bitstring_bytes(roots[0]), b"abc");
}

/// A view's mark sits in the word that points at its BinRef. The collector
/// rewrites that pointer when it moves the BinRef, and keeps the mark; the
/// BinRef still reads without it.
#[test]
fn a_views_shared_mark_survives_the_collectors_rewrite_of_its_binref_word() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..200u8).collect();
    let (whole, _witness) = witnessed_buffer(&mut heap, &bytes);
    assert!(!view_of(whole).is_shared(), "a filled buffer's view has one holder");
    let mut roots = [whole.ref_word()];
    heap.mark_published_ref_aliased(roots[0]).expect("share");
    assert!(view_in(roots[0]).is_shared());
    let before = view_in(roots[0]).binref().as_raw();

    collect_through_a_major(&mut heap, &mut roots[0]);
    let moved = view_in(roots[0]);
    assert_ne!(
        moved.binref().as_raw(),
        before,
        "the major moved the BinRef and rewrote the view"
    );
    assert!(moved.is_shared(), "the rewrite keeps the mark");
    assert_eq!(view_bytes(moved), bytes);
}

/// A slice does not own the room after its buffer's bytes, so it is born
/// shared, and it marks its source: two views now reach the same bytes.
#[test]
fn a_slice_is_born_shared_and_marks_its_source() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..200u8).collect();
    let (whole, _witness) = witnessed_buffer(&mut heap, &bytes);
    let window = unsafe { heap.alloc_bitstring_slice(view_of(whole), 70, 100) };
    assert!(view_of(window).is_shared());
    assert!(view_of(whole).is_shared());
    assert_eq!(
        heap.binaries_shared(),
        1,
        "the source is marked; the slice is born marked"
    );
}

/// An append that writes into its left view's buffer leaves that view short
/// of the buffer's end, so the view is marked; the longer view it makes is
/// the one view that reaches the end, and is born clear.
#[test]
fn an_append_in_place_marks_the_view_it_grew_from_and_not_the_new_one() {
    let mut heap = Heap::new(SIZE_TABLE[0], fresh_registry());
    let left: Vec<u8> = (0..100u8).collect();
    let grown = unsafe { heap.alloc_concatenation(&left, None, &[1; 100]) };
    let grown_bytes = view_bytes(view_of(grown));
    let longer = unsafe { heap.alloc_concatenation(&grown_bytes, Some(view_of(grown)), b"x") };
    assert_eq!(
        view_of(longer).shared_raw(),
        view_of(grown).shared_raw(),
        "the append wrote into the left's buffer"
    );
    assert!(view_of(grown).is_shared());
    assert!(!view_of(longer).is_shared());
}

/// A copy into another process: a view's copy names a frozen buffer the
/// sender also reaches, so it is born shared; a small bitstring's copy is a
/// new object only the receiver holds, so it is born clear.
#[test]
fn a_copied_view_is_shared_and_a_copied_small_bitstring_is_not() {
    let mut sender = Heap::new(SIZE_TABLE[0], fresh_registry());
    let mut receiver = Heap::new(SIZE_TABLE[0], fresh_registry());
    let bytes: Vec<u8> = (0..200u8).collect();
    let (whole, _witness) = witnessed_buffer(&mut sender, &bytes);
    let small = sender.alloc_bitstring(b"abc", 24);
    sender.mark_published_ref_aliased(small.ref_word()).expect("share");

    let view_copy = deep_copy_slot(whole, &sender.view(), &mut receiver);
    let small_copy = deep_copy_slot(small, &sender.view(), &mut receiver);
    assert!(view_of(view_copy).is_shared());
    assert!(!small_bitstring_is_shared(small_copy.ref_word()));
    assert_eq!(small_bitstring_bytes(small_copy.ref_word()), b"abc");
}
