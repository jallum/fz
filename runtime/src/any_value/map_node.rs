//! The raw layout of a map object that is a node of a trie.
//!
//! A map of up to `MAP_FLAT_MAX` entries built in one call is one flat sorted
//! array (`map_header_word`). A larger one is a hash array mapped trie of
//! nodes, each a heap object of kind MAP whose first word says so:
//!
//! ```text
//! flat map:    count << 4
//! trie node:   TRIE(bit 62) | total << 36 | child_map << 20 | data_map << 4
//! collision:   TRIE(bit 62) | COLLISION(bit 61) | count << 36
//! destination: DESTINATION(bit 63) | ...        (see `map_destination_header_word`)
//! ```
//!
//! The low nibble stays clear in every header, so the collector's forwarding
//! marker works on a trie node as on any other map. `total` counts the entries
//! at and beneath the node, so the root answers the map's size.
//!
//! A node holds its own entries first and its children after them, in the
//! order of their bits in the two bitmaps. The entries use the flat layout, and
//! the children are the words after the last value:
//!
//! ```text
//! header | kind bytes (one per entry, padded to 8) | keys | values | children
//! ```
//!
//! Every slot of a node, a flat map included, is therefore described by the
//! header alone: `map_node_entry_count` entries and `map_node_child_count`
//! children. A collision node is the node for entries whose 64-bit hashes are
//! equal: it has entries and no bitmaps.

use super::{
    AnyValue, MAP_DESTINATION_FLAG, MAP_HEADER_FIELD_SHIFT, ValueKind, map_count, map_key_kind, map_keys_ptr,
    map_tag_bytes_len, map_tag_ptr, map_value_kind, map_values_ptr,
};
use std::ptr;

/// The most entries a map built in one call holds as a flat array.
pub const MAP_FLAT_MAX: usize = 32;

const MAP_TRIE_FLAG: u64 = 1 << 62;
const MAP_COLLISION_FLAG: u64 = 1 << 61;
const MAP_DATA_MAP_SHIFT: u32 = MAP_HEADER_FIELD_SHIFT;
const MAP_CHILD_MAP_SHIFT: u32 = MAP_DATA_MAP_SHIFT + 16;
const MAP_TOTAL_SHIFT: u32 = MAP_CHILD_MAP_SHIFT + 16;
const MAP_TOTAL_BITS: u32 = 61 - MAP_TOTAL_SHIFT;

fn assert_total_fits(total: usize) {
    assert!((total as u64) < 1 << MAP_TOTAL_BITS, "map entry count overflow");
}

/// A trie node's first word: which of the 16 slots hold an entry and which
/// hold a child, and the entries at and beneath the node.
#[inline]
pub fn map_trie_header_word(data_map: u16, child_map: u16, total: usize) -> u64 {
    assert_total_fits(total);
    MAP_TRIE_FLAG
        | ((total as u64) << MAP_TOTAL_SHIFT)
        | ((child_map as u64) << MAP_CHILD_MAP_SHIFT)
        | ((data_map as u64) << MAP_DATA_MAP_SHIFT)
}

/// A collision node's first word: it holds `count` entries and no children.
#[inline]
pub fn map_collision_header_word(count: usize) -> u64 {
    assert_total_fits(count);
    MAP_TRIE_FLAG | MAP_COLLISION_FLAG | ((count as u64) << MAP_TOTAL_SHIFT)
}

/// Whether a published map's first word names a trie node or collision node.
#[inline]
pub fn map_header_is_trie_word(header: u64) -> bool {
    header & (MAP_DESTINATION_FLAG | MAP_TRIE_FLAG) == MAP_TRIE_FLAG
}

/// Whether the map at `addr` is a node of a trie rather than a flat array.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
#[inline]
pub unsafe fn map_header_is_trie(addr: *const u8) -> bool {
    map_header_is_trie_word(unsafe { ptr::read(addr as *const u64) })
}

/// Whether the map at `addr` is a collision node.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
#[inline]
pub unsafe fn map_header_is_collision(addr: *const u8) -> bool {
    let header = unsafe { ptr::read(addr as *const u64) };
    map_header_is_trie_word(header) && header & MAP_COLLISION_FLAG != 0
}

/// The entries at and beneath a trie node.
#[inline]
pub(super) fn map_trie_total(header: u64) -> usize {
    ((header & !(MAP_TRIE_FLAG | MAP_COLLISION_FLAG)) >> MAP_TOTAL_SHIFT) as usize
}

/// The data bitmap and the child bitmap of a non-collision trie node: bit `n`
/// of the first is set where slot `n` holds an entry, of the second where it
/// holds a child.
///
/// # Safety
///
/// `addr` must point to the start of an initialized trie node.
#[inline]
pub unsafe fn map_trie_bitmaps(addr: *const u8) -> (u16, u16) {
    let header = unsafe { ptr::read(addr as *const u64) };
    debug_assert!(map_header_is_trie_word(header), "not a trie node");
    (
        (header >> MAP_DATA_MAP_SHIFT) as u16,
        (header >> MAP_CHILD_MAP_SHIFT) as u16,
    )
}

/// How many entries the node at `addr` holds itself: a flat map's entries, a
/// destination's capacity, a trie node's own entries.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
#[inline]
pub unsafe fn map_node_entry_count(addr: *const u8) -> usize {
    let header = unsafe { ptr::read(addr as *const u64) };
    if !map_header_is_trie_word(header) {
        unsafe { map_count(addr) }
    } else if header & MAP_COLLISION_FLAG != 0 {
        map_trie_total(header)
    } else {
        ((header >> MAP_DATA_MAP_SHIFT) as u16).count_ones() as usize
    }
}

/// How many children the node at `addr` has: none for a flat map or a
/// collision node.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
#[inline]
pub unsafe fn map_node_child_count(addr: *const u8) -> usize {
    let header = unsafe { ptr::read(addr as *const u64) };
    if map_header_is_trie_word(header) && header & MAP_COLLISION_FLAG == 0 {
        ((header >> MAP_CHILD_MAP_SHIFT) as u16).count_ones() as usize
    } else {
        0
    }
}

/// The bytes of a node holding `entries` entries and `children` children.
#[inline]
pub fn map_node_size(entries: usize, children: usize) -> usize {
    (8 + map_tag_bytes_len(entries) + entries * 16 + children * 8 + 15) & !15
}

/// The bytes the map object at `addr` occupies, in any of its layouts.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
pub unsafe fn map_object_size(addr: *const u8) -> usize {
    map_node_size(unsafe { map_node_entry_count(addr) }, unsafe {
        map_node_child_count(addr)
    })
}

/// Child `index` of the node at `addr`.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object and
/// `index` must be below its child count.
#[inline]
pub unsafe fn map_node_child(addr: *const u8, index: usize) -> *mut u8 {
    let entries = unsafe { map_node_entry_count(addr) };
    debug_assert!(
        index < unsafe { map_node_child_count(addr) },
        "child index out of bounds"
    );
    unsafe { ptr::read(map_values_ptr(addr, entries).add(entries + index)) as *mut u8 }
}

/// Where the words of the children of the node at `addr` begin.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object.
#[inline]
pub unsafe fn map_node_children_ptr(addr: *const u8) -> *mut u64 {
    let entries = unsafe { map_node_entry_count(addr) };
    unsafe { map_values_ptr(addr, entries).add(entries) }
}

/// The node that holds entry `index` of the map at `addr`, in node order, and
/// that entry's slot within it. A flat map is its own node. In a trie the
/// descent skips whole children by their totals, so it reads one header per
/// child passed.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict published Map
/// object, and `index` must be in bounds for its entry count.
pub unsafe fn map_locate(mut addr: *const u8, mut index: usize) -> (*const u8, usize) {
    assert!(index < unsafe { map_count(addr) }, "map entry index out of bounds");
    while unsafe { map_header_is_trie(addr) } {
        let own = unsafe { map_node_entry_count(addr) };
        if index < own {
            break;
        }
        index -= own;
        addr = unsafe { child_holding(addr, &mut index) };
    }
    (addr, index)
}

/// The child of `addr` whose entries include the one numbered `index` among
/// the children's entries, with `index` made relative to that child.
unsafe fn child_holding(addr: *const u8, index: &mut usize) -> *const u8 {
    for child in 0..unsafe { map_node_child_count(addr) } {
        let below = unsafe { map_node_child(addr, child) } as *const u8;
        let count = unsafe { map_count(below) };
        if *index < count {
            return below;
        }
        *index -= count;
    }
    unreachable!("a trie node's total is the sum of its entries and its children's totals")
}

/// The raw words and kinds of entry `slot` of the node at `addr`.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict Map object, and
/// `slot` must be below its `map_node_entry_count`.
#[inline]
pub unsafe fn map_slot_raw_kinds(addr: *const u8, slot: usize) -> (u64, ValueKind, u64, ValueKind) {
    let count = unsafe { map_node_entry_count(addr) };
    assert!(slot < count, "map entry index out of bounds");
    let tag = unsafe { ptr::read(map_tag_ptr(addr).add(slot)) };
    (
        unsafe { ptr::read(map_keys_ptr(addr, count).add(slot)) },
        map_key_kind(tag),
        unsafe { ptr::read(map_values_ptr(addr, count).add(slot)) },
        map_value_kind(tag),
    )
}

/// Entry `slot` of the node at `addr`, as values.
///
/// # Safety
///
/// As `map_slot_raw_kinds`.
pub unsafe fn map_slot(addr: *const u8, slot: usize) -> (AnyValue, AnyValue) {
    let (key, key_kind, value, value_kind) = unsafe { map_slot_raw_kinds(addr, slot) };
    (
        AnyValue::decode_parts(key, key_kind.tag()).expect("map key value"),
        AnyValue::decode_parts(value, value_kind.tag()).expect("map entry value"),
    )
}

/// Visit every entry of the map at `addr` in node order: a flat map in key
/// order, a trie node's own entries before each of its children's.
///
/// # Safety
///
/// `addr` must point to the start of an initialized strict published Map
/// object.
pub unsafe fn map_for_each_entry(addr: *const u8, visit: &mut impl FnMut(AnyValue, AnyValue)) {
    for slot in 0..unsafe { map_node_entry_count(addr) } {
        let (key, value) = unsafe { map_slot(addr, slot) };
        visit(key, value);
    }
    for child in 0..unsafe { map_node_child_count(addr) } {
        unsafe { map_for_each_entry(map_node_child(addr, child), visit) };
    }
}

/// The entries of the map at `addr` in node order.
///
/// # Safety
///
/// As `map_for_each_entry`.
pub unsafe fn map_entries(addr: *const u8) -> Vec<(AnyValue, AnyValue)> {
    let mut entries = Vec::with_capacity(unsafe { map_count(addr) });
    unsafe { map_for_each_entry(addr, &mut |key, value| entries.push((key, value))) };
    entries
}
