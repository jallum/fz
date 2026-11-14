//! A trie is held to a plain model of its entries and to the invariants that
//! make one key set have one trie, in the heap that allocates, collects and
//! copies it.

use super::*;
use crate::any_value::{
    AnyValueRef, EMPTY_LIST, ValueKind, heap_word_addr, map_addr_from_tagged, map_count, map_entry, map_header_is_trie,
    map_node_child_count, map_object_size, map_slot_raw_kinds,
};
use crate::heap::{Generation, MapLayout, SchemaRegistry, measure_deep_copy};
use crate::sched::gift_copy;
use crate::term::{NumericMode, TermComparator};
use std::cell::RefCell;
use std::cmp::Ordering;
use std::collections::{BTreeMap, HashSet};
use std::rc::Rc;

fn heap() -> Heap {
    Heap::new(4096, Rc::new(RefCell::new(SchemaRegistry::new())))
}

fn int_of(value: AnyValue) -> i64 {
    match value {
        AnyValue::Int(i) => i,
        other => panic!("expected an integer, found {other:?}"),
    }
}

/// Keys `0..count` in an order that is not their numeric order, each bound to
/// ten times itself.
fn shuffled_entries(count: i64) -> Vec<(AnyValue, AnyValue)> {
    (0..count)
        .map(|i| (i * 7919) % count)
        .map(|i| (AnyValue::int(i), AnyValue::int(i * 10)))
        .collect()
}

fn model_of(entries: &[(AnyValue, AnyValue)]) -> BTreeMap<i64, i64> {
    entries.iter().map(|&(k, v)| (int_of(k), int_of(v))).collect()
}

fn map_ref(bits: u64) -> AnyValueRef {
    AnyValueRef::from_heap_object(ValueKind::MAP, map_addr_from_tagged(bits).expect("map addr")).expect("map ref")
}

fn root_addr(map: AnyValueRef) -> *const u8 {
    map.heap_object_word()
        .map(|word| heap_word_addr(word) as *const u8)
        .expect("map root")
}

fn layout_of(heap: &Heap, map: AnyValueRef) -> MapLayout {
    heap.expect_map_layout(map, "trie test")
}

fn contents(heap: &Heap, map: AnyValueRef) -> BTreeMap<i64, i64> {
    let entries = heap.map_view_entries(layout_of(heap, map));
    let model = model_of(&entries);
    assert_eq!(model.len(), entries.len(), "no key is enumerated twice");
    model
}

fn compare(heap: &Heap, a: AnyValue, b: AnyValue) -> Ordering {
    let schemas = heap.schemas.borrow();
    TermComparator::new(&heap.node, &schemas).compare(a, b, NumericMode::Strict)
}

fn map_value(map: AnyValueRef) -> AnyValue {
    AnyValue::from_ref(map).expect("map value")
}

/// Check the invariants of the trie at `node`, whose entries' hashes must
/// begin with `prefix`, the `level` nibbles of the path to it. Answers the
/// entries at and beneath it.
fn check_node(hash_of: &dyn Fn(AnyValue) -> u64, node: *const u8, level: u32, prefix: u64) -> usize {
    let on_path = |key: AnyValue| level == 0 || hash_of(key) >> (64 - 4 * level) == prefix;
    let own = unsafe { map_node_entry_count(node) };
    for slot in 0..own {
        assert!(
            on_path(unsafe { map_slot(node, slot) }.0),
            "an entry lies on the path to its node"
        );
    }
    if unsafe { map_header_is_collision(node) } {
        assert_eq!(level, LEVELS, "a collision node is where the hash bits run out");
        assert!(own >= 2, "a collision node holds at least two keys");
        let first = hash_of(unsafe { map_slot(node, 0) }.0);
        for slot in 0..own {
            assert_eq!(
                hash_of(unsafe { map_slot(node, slot) }.0),
                first,
                "keys in a collision node hash alike"
            );
        }
        assert_eq!(unsafe { map_count(node) }, own);
        return own;
    }
    assert!(level < LEVELS, "a trie node is above the last level");
    let (data, children) = unsafe { map_trie_bitmaps(node) };
    assert_eq!(data & children, 0, "a slot holds an entry or a child, not both");
    let mut slots = (0..16u16).filter(|bit| data & (1 << bit) != 0);
    for slot in 0..own {
        let bit = slots.next().expect("a data bit for each entry");
        let key = unsafe { map_slot(node, slot) }.0;
        assert_eq!(
            slot_at(hash_of(key), level),
            bit,
            "an entry sits in the slot its hash names"
        );
    }
    let mut total = own;
    for (index, bit) in (0..16u16).filter(|bit| children & (1 << bit) != 0).enumerate() {
        let child = unsafe { map_node_child(node, index) };
        let below = check_node(hash_of, child, level + 1, (prefix << 4) | u64::from(bit));
        assert!(below >= 2, "a child exists only where two keys share its path");
        total += below;
    }
    assert_eq!(
        unsafe { map_count(node) },
        total,
        "a node's total is what lies at and beneath it"
    );
    total
}

fn check_trie(heap: &Heap, map: AnyValueRef) -> usize {
    let hash_of = |key| heap.key_hash(key);
    check_node(&hash_of, root_addr(map), 0, 0)
}

/// The bytes of every node of the trie at `node`.
fn trie_bytes(node: *const u8) -> usize {
    let own = unsafe { map_object_size(node) };
    (0..unsafe { map_node_child_count(node) })
        .map(|child| trie_bytes(unsafe { map_node_child(node, child) }))
        .sum::<usize>()
        + own
}

fn assert_holds_model(heap: &mut Heap, map: AnyValueRef, model: &BTreeMap<i64, i64>) {
    assert_eq!(
        contents(heap, map),
        *model,
        "the trie enumerates exactly the model's entries"
    );
    assert_eq!(check_trie(heap, map), model.len());
    let layout = layout_of(heap, map);
    assert_eq!(heap.map_view_count(layout), model.len());
    for (&key, &value) in model {
        let found = heap
            .map_view_get(layout, AnyValue::int(key))
            .expect("a present key is found");
        assert_eq!(int_of(AnyValue::from_ref(found).unwrap()), value);
    }
    let missing = AnyValue::int(model.keys().next_back().copied().unwrap_or(0) + 1);
    assert!(!heap.map_view_has_key(layout, missing), "an absent key is not found");
}

#[test]
fn a_bulk_built_map_past_the_flat_limit_is_a_trie_that_holds_exactly_its_entries() {
    for count in [33, 1000, 1025, 40_000] {
        let mut heap = heap();
        let entries = shuffled_entries(count);
        let map = map_ref(heap.alloc_map_slots(&entries));
        assert!(
            unsafe { map_header_is_trie(root_addr(map)) },
            "{count} entries make a trie"
        );
        assert_holds_model(&mut heap, map, &model_of(&entries));
    }
}

#[test]
fn a_bulk_built_map_of_the_flat_limit_stays_a_flat_array() {
    let mut heap = heap();
    let map = map_ref(heap.alloc_map_slots(&shuffled_entries(MAP_FLAT_MAX as i64)));
    assert!(!unsafe { map_header_is_trie(root_addr(map)) });
}

#[test]
fn the_trie_of_a_key_set_does_not_depend_on_the_order_the_keys_arrived_in() {
    let mut heap = heap();
    let mut entries = shuffled_entries(500);
    let first = map_ref(heap.alloc_map_slots(&entries));
    entries.reverse();
    let second = map_ref(heap.alloc_map_slots(&entries));
    assert_eq!(
        heap.map_view_entries(layout_of(&heap, first)),
        heap.map_view_entries(layout_of(&heap, second))
    );
    assert_eq!(compare(&heap, map_value(first), map_value(second)), Ordering::Equal);
}

#[test]
fn keys_with_equal_hashes_meet_in_a_collision_node_and_are_told_apart_by_equality() {
    let mut heap = heap();
    let mut hashed: Vec<(u64, (AnyValue, AnyValue))> = (0..200i64)
        .map(|i| {
            (
                ((i % 4) as u64) << 62 | (i % 20) as u64,
                (AnyValue::int(i), AnyValue::int(i * 10)),
            )
        })
        .collect();
    let root = map_ref(heap.alloc_trie_hashed(&mut hashed));
    let hash_of: &dyn Fn(AnyValue) -> u64 = &|key| hashed.iter().find(|(_, e)| e.0.raw() == key.raw()).unwrap().0;
    assert_eq!(check_node(hash_of, root_addr(root), 0, 0), 200);
    for &(hash, (key, value)) in &hashed {
        let (node, slot) = find(root_addr(root), hash, |k| k.raw() == key.raw()).expect("a colliding key is found");
        assert_eq!(unsafe { map_slot(node, slot) }.1.raw(), value.raw());
    }
    let absent = AnyValue::int(1000);
    assert!(find(root_addr(root), hashed[0].0, |k| k.raw() == absent.raw()).is_none());
    assert!(
        hashed
            .iter()
            .any(|&(hash, _)| unsafe { map_header_is_collision(find(root_addr(root), hash, |_| true).unwrap().0) }),
        "some keys share every bit of their hash"
    );
}

#[test]
fn a_young_trie_collects_with_its_entries_under_minor_and_major_collections() {
    let mut heap = heap();
    let entries: Vec<_> = (0..300i64)
        .map(|i| {
            (
                AnyValue::int(i),
                heap_value(heap.alloc_list_cons_slot(AnyValue::int(i), EMPTY_LIST)),
            )
        })
        .collect();
    let map = map_ref(heap.alloc_map_slots(&entries));
    let mut roots = [map];
    let minor = heap.collect(&mut roots);
    assert_eq!(minor.generation, Generation::Minor);
    let map = roots[0];
    assert_eq!(check_trie(&heap, map), 300);
    let layout = layout_of(&heap, map);
    for i in 0..300i64 {
        let value = heap.map_view_get(layout, AnyValue::int(i)).expect("key survives");
        let head = unsafe { list_head(value) };
        assert_eq!(head, i, "the list under key {i} survives with its contents");
    }
    let mut roots = [map];
    collect_until_major(&mut heap, &mut roots);
    assert_eq!(check_trie(&heap, roots[0]), 300);
    let layout = layout_of(&heap, roots[0]);
    for i in 0..300i64 {
        let value = heap
            .map_view_get(layout, AnyValue::int(i))
            .expect("key survives a major collection");
        assert_eq!(unsafe { list_head(value) }, i);
    }
}

/// Collect `roots` until a major collection has run, allocating garbage between.
fn collect_until_major(heap: &mut Heap, roots: &mut [AnyValueRef]) {
    loop {
        if heap.collect(roots).generation == Generation::Major {
            return;
        }
        for i in 0..4096 {
            heap.alloc_list_cons_slot(AnyValue::int(i), EMPTY_LIST);
        }
    }
}

unsafe fn list_head(list: AnyValueRef) -> i64 {
    let addr = list.heap_object_word().map(heap_word_addr).expect("list");
    int_of(unsafe { &*(addr as *const crate::any_value::ListCons) }.head_value())
}

fn heap_value(bits: u64) -> AnyValue {
    AnyValue::decode_tagged_heap_bits(bits).expect("heap value")
}

#[test]
fn a_young_node_over_old_children_collects_without_moving_the_old_ones() {
    let mut heap = heap();
    let old_map = map_ref(heap.alloc_map_slots(&shuffled_entries(100)));
    let mut roots = [old_map];
    collect_until_major(&mut heap, &mut roots);
    let old = roots[0];
    let old_addr = root_addr(old);
    let header = map_trie_header_word(0, 1, 100);
    let young = heap.alloc_map_node(header, &[], &[old_addr as *mut u8]);
    let mut roots = [map_ref(heap_object_word(young, ValueKind::MAP))];
    let stats = heap.collect(&mut roots);
    assert_eq!(stats.generation, Generation::Minor);
    let moved = root_addr(roots[0]);
    assert_ne!(moved, young as *const u8, "the young node was copied");
    assert_eq!(
        unsafe { map_node_child(moved, 0) } as *const u8,
        old_addr,
        "the old child stayed where it was"
    );
    assert_eq!(unsafe { map_count(moved) }, 100);
}

#[test]
fn deep_copy_and_a_gift_copy_each_node_once_and_measure_what_they_write() {
    let mut heap = heap();
    let entries = shuffled_entries(2000);
    let map = map_ref(heap.alloc_map_slots(&entries));
    let nodes_bytes = trie_bytes(root_addr(map));
    let measured = measure_deep_copy(&[map], &heap.view());
    assert_eq!(measured, nodes_bytes, "the copy is one object per node");
    let (segment, copied) = gift_copy(&mut heap, &[map]);
    assert_eq!(segment.fill_bytes(), measured);
    assert_holds_model(&mut heap, copied[0], &model_of(&entries));
    assert_ne!(root_addr(copied[0]), root_addr(map));
}

#[test]
fn a_shared_subtrie_is_copied_once() {
    let mut heap = heap();
    let inner = map_ref(heap.alloc_map_slots(&shuffled_entries(100)));
    let header = map_trie_header_word(0, 0b11, 200);
    let shared = root_addr(inner) as *mut u8;
    let outer = heap.alloc_map_node(header, &[], &[shared, shared]);
    let outer = map_ref(heap_object_word(outer, ValueKind::MAP));
    let measured = measure_deep_copy(&[outer], &heap.view());
    assert_eq!(measured, map_node_size(0, 2) + trie_bytes(root_addr(inner)));
}

#[test]
fn a_trie_and_the_flat_map_of_the_same_entries_are_equal_and_order_alike() {
    let mut heap = heap();
    let entries = shuffled_entries(40);
    let trie = map_ref(heap.alloc_map_slots(&entries));
    let mut flat = map_ref(heap.alloc_map_slots(&entries[..30]));
    for &(key, value) in &entries[30..] {
        flat = heap.map_view_put(layout_of(&heap, flat), key, value);
    }
    assert!(unsafe { map_header_is_trie(root_addr(trie)) });
    assert!(
        unsafe { map_header_is_trie(root_addr(flat)) },
        "a put past the flat limit makes a trie"
    );
    assert_eq!(shape(root_addr(flat)), shape(root_addr(trie)));
    let (trie_value, flat_value) = (map_value(trie), map_value(flat));
    assert_eq!(compare(&heap, trie_value, flat_value), Ordering::Equal);
    assert_eq!(compare(&heap, flat_value, trie_value), Ordering::Equal);

    let mut changed = entries.clone();
    changed[7].1 = AnyValue::int(-1);
    let other = map_value(map_ref(heap.alloc_map_slots(&changed)));
    for pair in [(trie_value, other), (other, trie_value)] {
        let against_flat = compare(
            &heap,
            if pair.0.raw() == trie_value.raw() {
                flat_value
            } else {
                pair.0
            },
            if pair.1.raw() == trie_value.raw() {
                flat_value
            } else {
                pair.1
            },
        );
        assert_eq!(
            compare(&heap, pair.0, pair.1),
            against_flat,
            "a trie orders as the flat map of its entries"
        );
        assert_ne!(against_flat, Ordering::Equal);
    }
    assert_eq!(
        compare(&heap, trie_value, other),
        compare(&heap, other, trie_value).reverse()
    );
}

#[test]
fn put_replaces_or_adds_and_delete_removes_in_a_trie() {
    let mut heap = heap();
    let entries = shuffled_entries(100);
    let mut model = model_of(&entries);
    let mut map = map_ref(heap.alloc_map_slots(&entries));

    map = heap.map_view_put(layout_of(&heap, map), AnyValue::int(5), AnyValue::int(-5));
    model.insert(5, -5);
    assert_holds_model(&mut heap, map, &model);
    map = heap.map_view_put(layout_of(&heap, map), AnyValue::int(500), AnyValue::int(1));
    model.insert(500, 1);
    assert_holds_model(&mut heap, map, &model);

    let same = heap.map_view_delete(map, AnyValue::int(9999));
    assert_eq!(
        root_addr(same),
        root_addr(map),
        "deleting an absent key is the same map"
    );

    for key in (0..101).filter(|k| *k != 500) {
        map = heap.map_view_delete(map, AnyValue::int(key));
        model.remove(&key);
        if model.len() > MAP_FLAT_MAX {
            assert_holds_model(&mut heap, map, &model);
        } else {
            assert!(
                !unsafe { map_header_is_trie(root_addr(map)) },
                "{} entries are a flat array",
                model.len()
            );
            assert_eq!(contents(&heap, map), model);
        }
    }
}

#[test]
fn a_destination_of_more_than_the_flat_limit_publishes_as_a_trie() {
    let mut heap = heap();
    let entries = shuffled_entries(60);
    let mut dest = heap.alloc_map_destination(entries.len());
    for &(key, value) in &entries {
        dest = unsafe { heap.map_destination_put(dest, key, value) };
    }
    let map = heap.map_destination_freeze(dest).expect("a build freezes");
    assert!(unsafe { map_header_is_trie(root_addr(map)) });
    assert_holds_model(&mut heap, map, &model_of(&entries));
}

#[test]
fn the_entry_by_index_of_a_trie_is_the_entry_the_walk_visits_at_that_position() {
    let mut heap = heap();
    let map = map_ref(heap.alloc_map_slots(&shuffled_entries(1000)));
    let layout = layout_of(&heap, map);
    let walked = heap.map_view_entries(layout);
    for (index, &(key, value)) in walked.iter().enumerate() {
        let (by_index_key, by_index_value) = heap.map_view_entry(layout, index);
        assert_eq!((by_index_key.raw(), by_index_value.raw()), (key.raw(), value.raw()));
    }
    let MapLayout::Trie(root) = layout else {
        panic!("a trie layout")
    };
    let (key, value) = unsafe { map_entry(root, 999) };
    assert_eq!(key.raw(), walked[999].0.raw());
    assert_eq!(value.raw(), walked[999].1.raw());
}

/// A small deterministic generator, so a failing interleaving repeats.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn below(&mut self, bound: u64) -> u64 {
        self.next() % bound
    }
}

/// The nodes of the map at `node` and everything beneath it, as text: each
/// node's header, its entries' words and kinds, and its children in order.
/// Two maps of one key set are one tree exactly when this text is equal.
fn shape(node: *const u8) -> String {
    let own = unsafe { map_node_entry_count(node) };
    let entries: Vec<_> = (0..own).map(|slot| unsafe { map_slot_raw_kinds(node, slot) }).collect();
    let children: Vec<_> = (0..unsafe { map_node_child_count(node) })
        .map(|child| shape(unsafe { map_node_child(node, child) }))
        .collect();
    format!(
        "{:x}{entries:?}({})",
        unsafe { std::ptr::read(node as *const u64) },
        children.join(",")
    )
}

/// Every node address of the map at `node`.
fn node_addresses(node: *const u8, into: &mut HashSet<usize>) {
    into.insert(node as usize);
    for child in 0..unsafe { map_node_child_count(node) } {
        node_addresses(unsafe { map_node_child(node, child) }, into);
    }
}

fn entries_of(model: &BTreeMap<i64, i64>) -> Vec<(AnyValue, AnyValue)> {
    model
        .iter()
        .map(|(&k, &v)| (AnyValue::int(k), AnyValue::int(v)))
        .collect()
}

fn is_trie(map: AnyValueRef) -> bool {
    unsafe { map_header_is_trie(root_addr(map)) }
}

fn map_bytes_allocated(heap: &Heap) -> u64 {
    heap.alloc_stats_snapshot().map.bytes
}

fn map_allocs(heap: &Heap) -> u64 {
    heap.alloc_stats_snapshot().map.allocs
}

#[test]
fn puts_and_deletes_in_any_order_leave_the_trie_a_bulk_build_of_the_same_entries_would_make() {
    let mut heap = heap();
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let mut model = BTreeMap::new();
    let mut map = map_ref(heap.alloc_map_slots(&[]));
    let (mut grew, mut shrank) = (0, 0);
    for step in 0..6000 {
        let was_trie = is_trie(map);
        let key = rng.below(80) as i64;
        let (old_map, old_shape, old_contents) = (map, shape(root_addr(map)), contents(&heap, map));
        if rng.below(100) < 52 {
            let value = step as i64;
            map = heap.map_view_put(layout_of(&heap, map), AnyValue::int(key), AnyValue::int(value));
            model.insert(key, value);
        } else {
            map = heap.map_view_delete(map, AnyValue::int(key));
            model.remove(&key);
        }
        grew += usize::from(!was_trie && is_trie(map));
        shrank += usize::from(was_trie && !is_trie(map));
        assert_eq!(
            is_trie(map),
            model.len() > MAP_FLAT_MAX,
            "step {step}: {} entries",
            model.len()
        );
        if is_trie(map) {
            assert_holds_model(&mut heap, map, &model);
        } else {
            assert_eq!(contents(&heap, map), model);
        }
        let bulk = map_ref(heap.alloc_map_slots(&entries_of(&model)));
        assert_eq!(
            shape(root_addr(map)),
            shape(root_addr(bulk)),
            "step {step}: one key set, one tree"
        );
        assert_eq!(
            shape(root_addr(old_map)),
            old_shape,
            "step {step}: the map operated on is as it was"
        );
        assert_eq!(contents(&heap, old_map), old_contents);
    }
    assert!(
        grew > 8 && shrank > 8,
        "the run crossed the limit both ways ({grew}, {shrank})"
    );
}

#[test]
fn an_operation_leaves_the_map_it_was_given_as_it_was() {
    let mut heap = heap();
    let entries = shuffled_entries(300);
    let original = map_ref(heap.alloc_map_slots(&entries));
    let (original_shape, original_contents) = (shape(root_addr(original)), contents(&heap, original));
    let layout = layout_of(&heap, original);
    let _ = heap.map_view_put(layout, AnyValue::int(7), AnyValue::int(-1));
    let _ = heap.map_view_put(layout, AnyValue::int(7000), AnyValue::int(-1));
    let _ = heap.map_view_delete(original, AnyValue::int(8));
    assert_eq!(shape(root_addr(original)), original_shape);
    assert_eq!(contents(&heap, original), original_contents);
}

/// A hash that gives forty-odd keys in two hundred the same sixty-four bits,
/// and keeps the rest of the key set on shared long paths.
fn colliding_hash(key: AnyValue) -> u64 {
    let i = int_of(key);
    ((i % 4) as u64) << 62 | (i % 20) as u64
}

fn colliding_ops() -> KeyOps<'static> {
    KeyOps {
        hash: &colliding_hash,
        order: &|a, b| int_of(a).cmp(&int_of(b)),
    }
}

fn colliding_bulk(heap: &mut Heap, model: &BTreeMap<i64, i64>) -> AnyValueRef {
    let mut hashed: Vec<_> = entries_of(model)
        .into_iter()
        .map(|e| (colliding_hash(e.0), e))
        .collect();
    map_ref(heap.alloc_trie_hashed(&mut hashed))
}

#[test]
fn keys_that_share_a_whole_hash_are_put_and_deleted_through_collision_nodes_and_long_paths() {
    let mut heap = heap();
    let mut rng = Rng(0x2545_f491_4f6c_dd1d);
    let ops = colliding_ops();
    let mut model: BTreeMap<i64, i64> = (0..100).map(|i| (i, i * 10)).collect();
    let mut map = colliding_bulk(&mut heap, &model);
    let mut saw_collision_shrink = false;
    for step in 0..4000 {
        let key = rng.below(200) as i64;
        let put = model.len() < 40 || (model.len() < 190 && rng.below(2) == 0);
        if put {
            let bits = heap.trie_put_with(root_addr(map), AnyValue::int(key), AnyValue::int(step), &ops);
            map = map_ref(bits);
            model.insert(key, step);
        } else if let Some(bits) = heap.trie_delete_with(root_addr(map), AnyValue::int(key), &ops) {
            map = map_ref(bits);
            model.remove(&key);
            saw_collision_shrink |= model.len() < 100;
        } else {
            assert!(!model.contains_key(&key), "only an absent key is a missing delete");
        }
        assert_eq!(check_node(&|k| colliding_hash(k), root_addr(map), 0, 0), model.len());
        assert_eq!(contents(&heap, map), model);
        let bulk = colliding_bulk(&mut heap, &model);
        assert_eq!(shape(root_addr(map)), shape(root_addr(bulk)), "step {step}");
    }
    assert!(saw_collision_shrink);
}

#[test]
fn a_put_into_a_flat_map_of_the_limit_makes_a_trie_and_a_replacement_does_not() {
    let mut heap = heap();
    let flat = map_ref(heap.alloc_map_slots(&shuffled_entries(MAP_FLAT_MAX as i64)));
    let replaced = heap.map_view_put(layout_of(&heap, flat), AnyValue::int(3), AnyValue::int(-3));
    assert!(
        !is_trie(replaced),
        "replacing a value keeps {MAP_FLAT_MAX} entries flat"
    );
    let grown = heap.map_view_put(layout_of(&heap, flat), AnyValue::int(1000), AnyValue::int(1));
    assert!(is_trie(grown));
    assert_eq!(check_trie(&heap, grown), MAP_FLAT_MAX + 1);
}

#[test]
fn a_delete_that_leaves_the_limit_makes_the_flat_array_and_an_absent_key_is_the_same_map() {
    let mut heap = heap();
    let trie = map_ref(heap.alloc_map_slots(&shuffled_entries(MAP_FLAT_MAX as i64 + 1)));
    let allocated = map_allocs(&heap);
    assert_eq!(
        root_addr(heap.map_view_delete(trie, AnyValue::int(5000))),
        root_addr(trie)
    );
    assert_eq!(map_allocs(&heap), allocated, "an absent key allocates nothing");
    let shrunk = heap.map_view_delete(trie, AnyValue::int(5));
    assert!(!is_trie(shrunk));
    let keys: Vec<i64> = contents(&heap, shrunk).keys().copied().collect();
    let flat_keys: Vec<i64> = heap
        .map_view_entries(layout_of(&heap, shrunk))
        .iter()
        .map(|e| int_of(e.0))
        .collect();
    assert_eq!(keys, flat_keys, "the flat array is in key order");
    let flat = map_ref(heap.alloc_map_slots(&[]));
    assert_eq!(root_addr(heap.map_view_delete(flat, AnyValue::int(1))), root_addr(flat));
}

#[test]
fn a_put_into_a_large_trie_allocates_the_nodes_of_one_path_whatever_its_size() {
    for size in [1000i64, 100_000] {
        let mut heap = heap();
        let entries = shuffled_entries(size);
        let map = map_ref(heap.alloc_map_slots(&entries));
        let layout = layout_of(&heap, map);
        let mut before = HashSet::new();
        node_addresses(root_addr(map), &mut before);
        let (bytes, allocs) = (map_bytes_allocated(&heap), map_allocs(&heap));
        let replaced = heap.map_view_put(layout, AnyValue::int(size / 2), AnyValue::int(-1));
        let added = heap.map_view_put(layout, AnyValue::int(size + 10), AnyValue::int(-1));
        let deleted = heap.map_view_delete(map, AnyValue::int(size / 3));
        let per_operation = (map_bytes_allocated(&heap) - bytes) / 3;
        assert!(
            per_operation < 3000,
            "{size} entries: {per_operation} bytes an operation"
        );
        assert!(
            map_allocs(&heap) - allocs <= 3 * 9,
            "{size} entries: a path of nodes an operation"
        );
        for result in [replaced, added, deleted] {
            let mut after = HashSet::new();
            node_addresses(root_addr(result), &mut after);
            let fresh = after.difference(&before).count();
            assert!(fresh <= 9, "{size} entries: {fresh} nodes are new, the rest are shared");
        }
    }
}

#[test]
fn an_update_destination_over_a_trie_replaces_along_a_path_and_misses_an_absent_key() {
    let mut heap = heap();
    let entries = shuffled_entries(5000);
    let map = map_ref(heap.alloc_map_slots(&entries));
    let mut model = model_of(&entries);
    let (bytes, allocs) = (map_bytes_allocated(&heap), map_allocs(&heap));
    let mut dest = heap.alloc_map_update(map);
    dest = unsafe { heap.map_destination_put(dest, AnyValue::int(10), AnyValue::int(-10)) };
    dest = unsafe { heap.map_destination_put(dest, AnyValue::int(4000), AnyValue::int(-4000)) };
    model.insert(10, -10);
    model.insert(4000, -4000);
    let updated = heap.map_destination_freeze(dest).expect("an update that hit freezes");
    assert_holds_model(&mut heap, updated, &model);
    assert!(map_bytes_allocated(&heap) - bytes < 2 * 3000, "two paths, not the map");
    assert!(map_allocs(&heap) - allocs <= 2 * 9);
    assert_eq!(contents(&heap, map), model_of(&entries), "the base is untouched");

    let miss = heap.alloc_map_update(map);
    let miss = unsafe { heap.map_destination_put(miss, AnyValue::int(99_999), AnyValue::int(1)) };
    assert_eq!(miss, 0, "a key the base lacks is the miss");
    assert!(heap.map_destination_freeze(miss).is_none());
}
