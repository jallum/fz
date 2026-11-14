//! A map of more than `MAP_FLAT_MAX` entries is a hash array mapped trie of
//! heap objects (the layout is in `any_value::map_node`).
//!
//! The hash of a key (`TermHasher`) chooses its place: sixteen levels of four
//! bits each, the top bits first. A node has sixteen slots, each empty, an
//! entry, or a child; an entry sits in the node of the first level at which no
//! other key shares its path, so a node exists only where two or more keys
//! share the path to it. A key set therefore has exactly one trie, whichever
//! way it was built, and two maps with equal keys have nodes with equal
//! bitmaps. Keys whose 64-bit hashes are equal share all sixteen levels and
//! meet in a collision node, where they are told apart by equality.
//!
//! Entries are enumerated in node order: a node's own entries in slot order,
//! then each child's in slot order. That order is a function of the hashes, so
//! it is the same on every path and every run. Whatever needs key order sorts.
//!
//! Put and delete copy the nodes on the path from the root to the slot the
//! key's hash names and share every other node with the map they were given.
//! A node left holding one entry is pulled up into its parent, so the trie
//! stays the one trie of its key set; the entries of a collision node are in
//! key order for the same reason. A put that takes a flat map past
//! `MAP_FLAT_MAX` entries makes a trie, and a delete that takes a trie down to
//! `MAP_FLAT_MAX` entries makes the flat array, so no trie holds that few
//! entries and no flat map more.

use super::Heap;
use crate::any_value::{
    AnyValue, MAP_FLAT_MAX, ValueKind, heap_object_word, map_collision_header_word, map_count, map_entries,
    map_header_is_collision, map_node_child, map_node_entry_count, map_node_size, map_slot, map_trie_bitmaps,
    map_trie_header_word,
};
use crate::heap::HeapAllocKind;
use crate::term::{NumericMode, TermComparator};
use crate::term_hash::TermHasher;
use std::cmp::Ordering;
use std::ptr::write;

type Entry = (AnyValue, AnyValue);

/// What places keys in a trie and tells them apart: a hash, and an order
/// whose equal keys are one key.
pub(super) struct KeyOps<'a> {
    pub(super) hash: &'a dyn Fn(AnyValue) -> u64,
    pub(super) order: &'a dyn Fn(AnyValue, AnyValue) -> Ordering,
}

/// What deleting a key from a node leaves.
enum Deleted {
    Absent,
    Node(*mut u8),
    /// One entry and nothing else, which the node's parent holds inline.
    Entry(Entry),
}

/// A trie node unpacked: its entries and its children, each in slot order.
struct Parts {
    data: u16,
    kids: u16,
    total: usize,
    entries: [Entry; 16],
    children: [*mut u8; 16],
}

impl Parts {
    /// # Safety
    ///
    /// `node` must be an initialized trie node that is not a collision node.
    unsafe fn read(node: *const u8) -> Self {
        let (data, kids) = unsafe { map_trie_bitmaps(node) };
        let mut parts = Self {
            data,
            kids,
            total: unsafe { map_count(node) },
            entries: [(AnyValue::int(0), AnyValue::int(0)); 16],
            children: [std::ptr::null_mut(); 16],
        };
        for slot in 0..parts.entry_count() {
            parts.entries[slot] = unsafe { map_slot(node, slot) };
        }
        for index in 0..parts.child_count() {
            parts.children[index] = unsafe { map_node_child(node, index) };
        }
        parts
    }

    fn entry_count(&self) -> usize {
        self.data.count_ones() as usize
    }

    fn child_count(&self) -> usize {
        self.kids.count_ones() as usize
    }

    fn entry(&self, bit: u16) -> Entry {
        self.entries[rank(self.data, bit)]
    }

    fn child(&self, bit: u16) -> *mut u8 {
        self.children[rank(self.kids, bit)]
    }

    fn set_entry(&mut self, bit: u16, entry: Entry) {
        self.entries[rank(self.data, bit)] = entry;
    }

    fn set_child(&mut self, bit: u16, child: *mut u8) {
        self.children[rank(self.kids, bit)] = child;
    }

    fn insert_entry(&mut self, bit: u16, entry: Entry) {
        let (at, count) = (rank(self.data, bit), self.entry_count());
        self.entries.copy_within(at..count, at + 1);
        self.entries[at] = entry;
        self.data |= bit;
    }

    fn remove_entry(&mut self, bit: u16) {
        let (at, count) = (rank(self.data, bit), self.entry_count());
        self.entries.copy_within(at + 1..count, at);
        self.data &= !bit;
    }

    fn insert_child(&mut self, bit: u16, child: *mut u8) {
        let (at, count) = (rank(self.kids, bit), self.child_count());
        self.children.copy_within(at..count, at + 1);
        self.children[at] = child;
        self.kids |= bit;
    }

    fn remove_child(&mut self, bit: u16) {
        let (at, count) = (rank(self.kids, bit), self.child_count());
        self.children.copy_within(at + 1..count, at);
        self.kids &= !bit;
    }

    /// The one entry of a node that holds nothing else. A child holds at
    /// least two, so a node of one entry has no child.
    fn lone_entry(&self) -> Option<Entry> {
        (self.total == 1).then(|| self.entries[0])
    }
}

/// The entries of the collision node at `node`, in key order.
///
/// # Safety
///
/// `node` must be an initialized collision node.
unsafe fn collision_entries(node: *const u8) -> Vec<Entry> {
    (0..unsafe { map_node_entry_count(node) })
        .map(|slot| unsafe { map_slot(node, slot) })
        .collect()
}

/// Levels of the trie: the 64 bits of a hash, four to a level.
const LEVELS: u32 = 16;

/// Which of a node's sixteen slots a hash takes at `level`.
fn slot_at(hash: u64, level: u32) -> u16 {
    ((hash >> (60 - 4 * level)) & 15) as u16
}

/// Where in the node's entries or children the slot `bit` of `bitmap` falls.
fn rank(bitmap: u16, bit: u16) -> usize {
    (bitmap & (bit - 1)).count_ones() as usize
}

/// The node and entry slot holding the key `is_key` recognises, in the trie
/// rooted at `root`, given the key's hash.
pub(super) fn find(root: *const u8, hash: u64, is_key: impl Fn(AnyValue) -> bool) -> Option<(*const u8, usize)> {
    let mut node = root;
    for level in 0..=LEVELS {
        if unsafe { map_header_is_collision(node) } {
            let entries = unsafe { map_node_entry_count(node) };
            return (0..entries)
                .find(|&slot| is_key(unsafe { map_slot(node, slot) }.0))
                .map(|slot| (node, slot));
        }
        let (data, children) = unsafe { map_trie_bitmaps(node) };
        let bit = 1u16 << slot_at(hash, level);
        if data & bit != 0 {
            let slot = rank(data, bit);
            return is_key(unsafe { map_slot(node, slot) }.0).then_some((node, slot));
        }
        if children & bit == 0 {
            return None;
        }
        node = unsafe { map_node_child(node, rank(children, bit)) };
    }
    unreachable!("a trie is {LEVELS} levels deep at most, and the last is a collision node")
}

impl Heap {
    /// The hash of `key` that places it in a trie.
    pub(super) fn key_hash(&self, key: AnyValue) -> u64 {
        let schemas = self.schemas.borrow();
        TermHasher::new(&self.node, &schemas).hash(key)
    }

    /// The node and entry slot that hold `key` in the trie rooted at `root`.
    pub(super) fn trie_find(&self, root: *const u8, key: AnyValue) -> Option<(*const u8, usize)> {
        let hash = self.key_hash(key);
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        find(root, hash, |candidate| {
            comparator.compare(candidate, key, NumericMode::Strict).is_eq()
        })
    }

    /// A trie of `entries`, which have no key repeated, and answers its root.
    pub(super) fn alloc_trie(&mut self, entries: &[Entry]) -> u64 {
        assert!(
            entries.len() > MAP_FLAT_MAX,
            "a trie holds more than {MAP_FLAT_MAX} entries"
        );
        let mut hashed: Vec<_> = entries.iter().map(|&entry| (self.key_hash(entry.0), entry)).collect();
        self.alloc_trie_hashed(&mut hashed)
    }

    /// A trie placing each entry by the hash it is given. Entries whose hashes
    /// are equal share a collision node.
    pub(super) fn alloc_trie_hashed(&mut self, hashed: &mut [(u64, Entry)]) -> u64 {
        hashed.sort_unstable_by_key(|&(hash, _)| hash);
        heap_object_word(self.alloc_trie_level(hashed, 0), ValueKind::MAP)
    }

    /// The node for entries, sorted by hash, that agree on the hash bits above
    /// `level`.
    fn alloc_trie_level(&mut self, hashed: &[(u64, Entry)], level: u32) -> *mut u8 {
        if level == LEVELS {
            let mut entries: Vec<Entry> = hashed.iter().map(|&(_, entry)| entry).collect();
            self.sort_entries_by_key(&mut entries);
            return self.alloc_collision(&entries);
        }
        let (mut data, mut child_map) = (0u16, 0u16);
        let mut entries = Vec::with_capacity(16);
        let mut children = Vec::with_capacity(16);
        for run in hashed.chunk_by(|a, b| slot_at(a.0, level) == slot_at(b.0, level)) {
            let bit = 1u16 << slot_at(run[0].0, level);
            if let [(_, entry)] = run {
                data |= bit;
                entries.push(*entry);
            } else {
                child_map |= bit;
                children.push(self.alloc_trie_level(run, level + 1));
            }
        }
        let header = map_trie_header_word(data, child_map, hashed.len());
        self.alloc_map_node(header, &entries, &children)
    }

    /// A node whose header is `header` holding `entries` and `children`.
    pub(super) fn alloc_map_node(&mut self, header: u64, entries: &[Entry], children: &[*mut u8]) -> *mut u8 {
        let node = self.alloc_kind(HeapAllocKind::Map, map_node_size(entries.len(), children.len()));
        unsafe { write(node as *mut u64, header) };
        self.write_map_entries(node, entries.len(), entries.iter().copied());
        let child_words = unsafe { crate::any_value::map_node_children_ptr(node) };
        for (index, child) in children.iter().enumerate() {
            unsafe { write(child_words.add(index), *child as u64) };
        }
        node
    }

    /// A hash and an order on keys, as the trie places and tells them apart.
    /// A heap's own keys are hashed by `TermHasher` and ordered by
    /// `TermComparator`; a test hands in others to force keys to meet.
    fn with_key_ops<R>(&mut self, then: impl FnOnce(&mut Heap, &KeyOps) -> R) -> R {
        let (node, schemas) = (self.node.clone(), self.schemas.clone());
        let hash = |key| TermHasher::new(&node, &schemas.borrow()).hash(key);
        let order = |a, b| TermComparator::new(&node, &schemas.borrow()).compare(a, b, NumericMode::Strict);
        then(
            self,
            &KeyOps {
                hash: &hash,
                order: &order,
            },
        )
    }

    /// The trie rooted at `root` with `key` bound to `value`.
    pub(super) fn trie_put(&mut self, root: *const u8, key: AnyValue, value: AnyValue) -> u64 {
        self.with_key_ops(|heap, ops| heap.trie_put_with(root, key, value, ops))
    }

    pub(super) fn trie_put_with(&mut self, root: *const u8, key: AnyValue, value: AnyValue, ops: &KeyOps) -> u64 {
        let (node, _) = self.put_in_node(ops, root, 0, (ops.hash)(key), (key, value));
        heap_object_word(node, ValueKind::MAP)
    }

    /// The map of the entries of the trie rooted at `root` but for `key`: a
    /// trie, or a flat array once no more than `MAP_FLAT_MAX` remain. `None`
    /// when the trie lacks `key`.
    pub(super) fn trie_delete(&mut self, root: *const u8, key: AnyValue) -> Option<u64> {
        self.with_key_ops(|heap, ops| heap.trie_delete_with(root, key, ops))
    }

    pub(super) fn trie_delete_with(&mut self, root: *const u8, key: AnyValue, ops: &KeyOps) -> Option<u64> {
        if unsafe { map_count(root) } == MAP_FLAT_MAX + 1 {
            return self.flat_map_without(root, key, ops);
        }
        match self.delete_in_node(ops, root, 0, (ops.hash)(key), key) {
            Deleted::Absent => None,
            Deleted::Node(node) => Some(heap_object_word(node, ValueKind::MAP)),
            Deleted::Entry(_) => unreachable!("a trie of more than {MAP_FLAT_MAX} entries keeps more than one"),
        }
    }

    /// The flat array of the entries of the trie at `root` but for `key`.
    fn flat_map_without(&mut self, root: *const u8, key: AnyValue, ops: &KeyOps) -> Option<u64> {
        let mut entries = unsafe { map_entries(root) };
        let at = entries.iter().position(|entry| (ops.order)(entry.0, key).is_eq())?;
        entries.remove(at);
        entries.sort_by(|a, b| (ops.order)(a.0, b.0));
        Some(self.alloc_ordered_map_entries(entries.into_iter()))
    }

    /// The node at `node`, which sits at `level`, with `entry` bound, and
    /// whether its key is new to it. Only the nodes on the way to the slot the
    /// hash names are copied; the rest are shared.
    fn put_in_node(&mut self, ops: &KeyOps, node: *const u8, level: u32, hash: u64, entry: Entry) -> (*mut u8, bool) {
        if unsafe { map_header_is_collision(node) } {
            return self.put_in_collision(ops, node, entry);
        }
        let mut parts = unsafe { Parts::read(node) };
        let bit = 1u16 << slot_at(hash, level);
        let added = if parts.kids & bit != 0 {
            let (child, added) = self.put_in_node(ops, parts.child(bit), level + 1, hash, entry);
            parts.set_child(bit, child);
            added
        } else if parts.data & bit == 0 {
            parts.insert_entry(bit, entry);
            true
        } else if (ops.order)(parts.entry(bit).0, entry.0).is_eq() {
            parts.set_entry(bit, entry);
            false
        } else {
            let resident = parts.entry(bit);
            let child = self.node_of_two(ops, level + 1, ((ops.hash)(resident.0), resident), (hash, entry));
            parts.remove_entry(bit);
            parts.insert_child(bit, child);
            true
        };
        parts.total += usize::from(added);
        (self.alloc_parts(&parts), added)
    }

    fn put_in_collision(&mut self, ops: &KeyOps, node: *const u8, entry: Entry) -> (*mut u8, bool) {
        let mut entries = unsafe { collision_entries(node) };
        let added = match entries.binary_search_by(|resident| (ops.order)(resident.0, entry.0)) {
            Ok(at) => {
                entries[at] = entry;
                false
            }
            Err(at) => {
                entries.insert(at, entry);
                true
            }
        };
        (self.alloc_collision(&entries), added)
    }

    /// The node at `level` holding two entries whose hashes agree on every
    /// level above it, and the chain of single-child nodes down to where they
    /// part.
    fn node_of_two(&mut self, ops: &KeyOps, level: u32, first: (u64, Entry), second: (u64, Entry)) -> *mut u8 {
        if level == LEVELS {
            let mut pair = [first.1, second.1];
            pair.sort_by(|a, b| (ops.order)(a.0, b.0));
            return self.alloc_collision(&pair);
        }
        let (a, b) = (slot_at(first.0, level), slot_at(second.0, level));
        if a == b {
            let child = self.node_of_two(ops, level + 1, first, second);
            let header = map_trie_header_word(0, 1 << a, 2);
            return self.alloc_map_node(header, &[], &[child]);
        }
        let (low, high) = if a < b {
            (first.1, second.1)
        } else {
            (second.1, first.1)
        };
        self.alloc_map_node(map_trie_header_word(1 << a | 1 << b, 0, 2), &[low, high], &[])
    }

    /// The node at `node`, which sits at `level`, without the entry for `key`;
    /// a trie node left holding one entry is that entry, for its parent to
    /// hold in the slot it names.
    fn delete_in_node(&mut self, ops: &KeyOps, node: *const u8, level: u32, hash: u64, key: AnyValue) -> Deleted {
        if unsafe { map_header_is_collision(node) } {
            return self.delete_in_collision(ops, node, key);
        }
        let mut parts = unsafe { Parts::read(node) };
        let bit = 1u16 << slot_at(hash, level);
        if parts.kids & bit != 0 {
            match self.delete_in_node(ops, parts.child(bit), level + 1, hash, key) {
                Deleted::Absent => return Deleted::Absent,
                Deleted::Node(child) => parts.set_child(bit, child),
                Deleted::Entry(entry) => {
                    parts.remove_child(bit);
                    parts.insert_entry(bit, entry);
                }
            }
        } else if parts.data & bit != 0 && (ops.order)(parts.entry(bit).0, key).is_eq() {
            parts.remove_entry(bit);
        } else {
            return Deleted::Absent;
        }
        parts.total -= 1;
        match parts.lone_entry() {
            Some(entry) => Deleted::Entry(entry),
            None => Deleted::Node(self.alloc_parts(&parts)),
        }
    }

    fn delete_in_collision(&mut self, ops: &KeyOps, node: *const u8, key: AnyValue) -> Deleted {
        let mut entries = unsafe { collision_entries(node) };
        let Ok(at) = entries.binary_search_by(|resident| (ops.order)(resident.0, key)) else {
            return Deleted::Absent;
        };
        entries.remove(at);
        match entries[..] {
            [lone] => Deleted::Entry(lone),
            _ => Deleted::Node(self.alloc_collision(&entries)),
        }
    }

    fn alloc_parts(&mut self, parts: &Parts) -> *mut u8 {
        let header = map_trie_header_word(parts.data, parts.kids, parts.total);
        self.alloc_map_node(
            header,
            &parts.entries[..parts.entry_count()],
            &parts.children[..parts.child_count()],
        )
    }

    /// A collision node of `entries`, which are in key order.
    fn alloc_collision(&mut self, entries: &[Entry]) -> *mut u8 {
        self.alloc_map_node(map_collision_header_word(entries.len()), entries, &[])
    }

    /// Order entries that have no key repeated by their keys.
    pub(super) fn sort_entries_by_key(&self, entries: &mut [Entry]) {
        let schemas = self.schemas.borrow();
        let comparator = TermComparator::new(&self.node, &schemas);
        entries.sort_by(|a, b| comparator.compare(a.0, b.0, NumericMode::Strict));
    }
}

#[cfg(test)]
#[path = "map_trie_test.rs"]
mod map_trie_test;
