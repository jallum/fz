//! A map of more than `MAP_FLAT_MAX` entries built in one call is a hash array
//! mapped trie of heap objects (the layout is in `any_value::map_node`).
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
//! Put and delete rebuild the whole trie from its entries. They are correct,
//! and linear in the size of the map.

use super::Heap;
use crate::any_value::{
    AnyValue, MAP_FLAT_MAX, ValueKind, heap_object_word, map_collision_header_word, map_entries,
    map_header_is_collision, map_node_child, map_node_entry_count, map_node_size, map_slot, map_trie_bitmaps,
    map_trie_header_word,
};
use crate::heap::HeapAllocKind;
use crate::term::{NumericMode, TermComparator};
use crate::term_hash::TermHasher;
use std::ptr::write;

type Entry = (AnyValue, AnyValue);

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
            let entries: Vec<Entry> = hashed.iter().map(|&(_, entry)| entry).collect();
            return self.alloc_map_node(map_collision_header_word(entries.len()), &entries, &[]);
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

    /// The trie rooted at `root` with `key` bound to `value`.
    pub(super) fn trie_put(&mut self, root: *const u8, key: AnyValue, value: AnyValue) -> u64 {
        let mut hashed = self.hashed_entries(root);
        let key_hash = self.key_hash(key);
        let position = {
            let schemas = self.schemas.borrow();
            let comparator = TermComparator::new(&self.node, &schemas);
            hashed.iter().position(|&(hash, entry)| {
                hash == key_hash && comparator.compare(entry.0, key, NumericMode::Strict).is_eq()
            })
        };
        match position {
            Some(index) => hashed[index].1 = (key, value),
            None => hashed.push((key_hash, (key, value))),
        }
        self.alloc_trie_hashed(&mut hashed)
    }

    /// The map of the entries of the trie rooted at `root` but for `key`: a
    /// trie, or a flat array once no more than `MAP_FLAT_MAX` remain.
    pub(super) fn trie_delete(&mut self, root: *const u8, key: AnyValue) -> u64 {
        let key_hash = self.key_hash(key);
        let mut hashed = self.hashed_entries(root);
        {
            let schemas = self.schemas.borrow();
            let comparator = TermComparator::new(&self.node, &schemas);
            hashed.retain(|&(hash, entry)| {
                hash != key_hash || !comparator.compare(entry.0, key, NumericMode::Strict).is_eq()
            });
        }
        if hashed.len() > MAP_FLAT_MAX {
            return self.alloc_trie_hashed(&mut hashed);
        }
        let mut entries: Vec<Entry> = hashed.into_iter().map(|(_, entry)| entry).collect();
        self.sort_entries_by_key(&mut entries);
        self.alloc_ordered_map_entries(entries.into_iter())
    }

    fn hashed_entries(&self, root: *const u8) -> Vec<(u64, Entry)> {
        unsafe { map_entries(root) }
            .into_iter()
            .map(|entry| (self.key_hash(entry.0), entry))
            .collect()
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
