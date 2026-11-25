//! A map read the same way whichever layout holds it.
//!
//! A map has three physical layouts. The entries layout is a sorted array of
//! key/value pairs. The trie layout is a hash array mapped trie, for a map of
//! more than `MAP_FLAT_MAX` entries (see `map_trie`). The
//! struct layout is a schema-backed object: a named
//! struct's keys are its schema's fields plus `__struct__`, which answers the
//! module. Which layout a value has is invisible to the language, so every map
//! operation reads through `MapLayout` and never asks for one layout by name.
//!
//! Writes keep the struct layout while the struct stays the struct it is:
//! replacing a field copies the object. Adding a key, removing one, or naming
//! another module under `__struct__` leaves the schema, so the result is
//! published in the entries layout with `__struct__` a real key.

use std::cell::RefCell;
use std::collections::HashMap;
use std::rc::Rc;

use super::Heap;
use super::imp::position_of_word;
use super::schema::SchemaIdentity;
use super::schema::{NamedSchema, StructKey};
use crate::alloc_site::RuntimeAllocSite;
use crate::any_value::{
    AnyValue, AnyValueRef, ListCons, STRUCT_PAYLOAD_OFFSET, SlotLayout, ValueKind, heap_object_word,
    map_addr_from_tagged, map_count, map_entries, map_entry, map_header_is_trie, map_key_kind, map_keys_ptr,
    map_node_child, map_node_child_count, map_node_entry_count, map_slot, map_tag_ptr, map_value_kind, map_values_ptr,
    struct_addr_from_tagged, struct_field_kind_slot, struct_field_raw_slot, struct_schema_id, struct_size_for_payload,
};
use crate::heap::map_slot_refs;
use crate::module_name::{ModuleName, STRUCT_MODULE_FIELD};
use std::ptr::{read, write};

/// Which part of each entry a map's list holds: `Map.keys`, `Map.values` or
/// `Map.to_list`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapPart {
    Keys,
    Values,
    Pairs,
}

const LIST_CELL_SIZE: usize = size_of::<ListCons>();

/// Where a `{key, value}` tuple's parts go: its header word, its size in bytes, and
/// the payload offset of its kind bytes.
#[derive(Clone, Copy)]
struct PairShape {
    header: u64,
    size: usize,
    kinds: u32,
}

/// A map's list as it is built, last entry first: the address of its first
/// cell so far (0 while it is empty), the entries still to list, and the
/// records the heap has placed for them and not yet filled. A record is one
/// list cell, or a pair followed by its cell.
struct Listing {
    part: MapPart,
    pair: Option<PairShape>,
    first: u64,
    unlisted: usize,
    next: *mut u8,
    room: usize,
}

impl Listing {
    fn new(part: MapPart, pair: Option<PairShape>, entries: usize) -> Self {
        Listing {
            part,
            pair,
            first: 0,
            unlisted: entries,
            next: std::ptr::null_mut(),
            room: 0,
        }
    }

    fn record_size(&self) -> usize {
        self.pair.map_or(0, |pair| pair.size) + LIST_CELL_SIZE
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapLayout {
    /// A flat array of entries in key order.
    Entries(*mut u8),
    /// The root of a trie, whose entries are in trie order.
    Trie(*mut u8),
    Struct {
        object: AnyValueRef,
        schema_id: u32,
    },
}

/// A named struct's keys in map key order, each with its atom and, for a
/// field, its slot offset.
struct StructMap {
    keys: Vec<StructKey>,
    atoms: Vec<u64>,
    offsets: Vec<u32>,
    module: AnyValue,
}

/// The atoms a heap's named structs answer as maps, learned once per schema.
#[derive(Default)]
pub(crate) struct StructMaps {
    by_schema: RefCell<HashMap<u32, Rc<StructMap>>>,
    /// The schema each module atom was found to name. A module with no
    /// schema is asked again, since one may be registered later.
    by_module_atom: RefCell<HashMap<u32, u32>>,
}

impl Heap {
    /// The layout of `value` when it is a map, in either layout; `None` for
    /// every other value, a tuple included.
    pub fn map_layout(&self, value: AnyValueRef) -> Option<MapLayout> {
        match value.tag() {
            ValueKind::MAP => value.map_addr().ok().map(|addr| {
                if unsafe { map_header_is_trie(addr as *const u8) } {
                    MapLayout::Trie(addr)
                } else {
                    MapLayout::Entries(addr)
                }
            }),
            ValueKind::STRUCT => {
                let addr = value.struct_addr().ok()?;
                let schema_id = unsafe { struct_schema_id(addr as *const u8) };
                self.schemas.borrow().map_keys(schema_id).map(|_| MapLayout::Struct {
                    object: value,
                    schema_id,
                })
            }
            _ => None,
        }
    }

    /// Whether `value` is in the struct layout of the struct named `module`.
    pub fn has_struct_layout_of(&self, value: AnyValueRef, module: &ModuleName) -> bool {
        let Ok(addr) = value.struct_addr() else {
            return false;
        };
        let schema_id = unsafe { struct_schema_id(addr as *const u8) };
        matches!(&self.schemas.borrow().get(schema_id).identity, SchemaIdentity::Named(name) if name == module)
    }

    /// The struct schema of the module `value` names. A struct names its
    /// own; a map in the entries layout names the atom under `__struct__`.
    pub fn named_schema(&self, value: AnyValueRef) -> NamedSchema {
        match self.map_layout(value) {
            Some(MapLayout::Struct { schema_id, .. }) => NamedSchema::Schema(schema_id),
            Some(MapLayout::Entries(addr) | MapLayout::Trie(addr)) => self.entries_named_schema(addr),
            None => NamedSchema::None,
        }
    }

    fn entries_named_schema(&self, addr: *mut u8) -> NamedSchema {
        let key = AnyValue::atom(self.node.intern_atom(STRUCT_MODULE_FIELD));
        let Some((node, slot)) = self.find(addr, key) else {
            return NamedSchema::None;
        };
        let (_, module) = unsafe { map_slot(node, slot) };
        if module.kind() != ValueKind::ATOM {
            return NamedSchema::None;
        }
        let atom = module.raw() as u32;
        if let Some(schema_id) = self.struct_maps.by_module_atom.borrow().get(&atom) {
            return NamedSchema::Schema(*schema_id);
        }
        let declared = self
            .node
            .atom_name(atom)
            .and_then(|name| ModuleName::from_atom_name(name.as_str()))
            .and_then(|module| self.schemas.borrow().named(&module));
        match declared {
            Some(schema_id) => {
                self.struct_maps.by_module_atom.borrow_mut().insert(atom, schema_id);
                NamedSchema::Schema(schema_id)
            }
            None => NamedSchema::Undeclared,
        }
    }

    /// The struct a map in the entries layout spells: the module it names
    /// and that struct's fields in declaration order, when its keys are
    /// exactly the struct's.
    pub fn entries_spelling_a_struct(&self, map: AnyValueRef) -> Option<(ModuleName, Vec<(String, AnyValue)>)> {
        let addr = map.map_addr().ok()?;
        let NamedSchema::Schema(schema_id) = self.entries_named_schema(addr) else {
            return None;
        };
        let keys = self.struct_map(schema_id);
        if unsafe { map_count(addr) } != keys.atoms.len() {
            return None;
        }
        let schemas = self.schemas.borrow();
        let schema = schemas.get(schema_id);
        let SchemaIdentity::Named(module) = &schema.identity else {
            return None;
        };
        let mut fields = vec![None; schema.fields.len()];
        for (key, atom) in keys.keys.iter().zip(&keys.atoms) {
            let (node, slot) = self.find(addr, AnyValue::atom(*atom as u32))?;
            if let StructKey::Field(field) = key {
                let name = schema.fields[*field].name.clone()?;
                fields[*field] = Some((name, unsafe { map_slot(node, slot) }.1));
            }
        }
        Some((module.clone(), fields.into_iter().collect::<Option<_>>()?))
    }

    /// The layout of a value the compiled program has proven is a map: a map
    /// extern declares `map` for it, so the runtime reads the layout and does
    /// not ask again. A debug build checks the promise.
    pub fn expect_map_layout(&self, value: AnyValueRef, context: &str) -> MapLayout {
        debug_assert!(
            self.map_layout(value).is_some(),
            "{context}: expected a map, found {:?}",
            value.tag()
        );
        let addr = value.cleared_addr();
        match value.tag() {
            ValueKind::MAP if unsafe { map_header_is_trie(addr as *const u8) } => MapLayout::Trie(addr),
            ValueKind::MAP => MapLayout::Entries(addr),
            _ => MapLayout::Struct {
                object: value,
                schema_id: unsafe { struct_schema_id(addr as *const u8) },
            },
        }
    }

    /// The entries of `layout`. Constant time in every layout: a trie keeps its
    /// total in its root.
    pub fn map_view_count(&self, layout: MapLayout) -> usize {
        match layout {
            MapLayout::Entries(addr) | MapLayout::Trie(addr) => unsafe { map_count(addr) },
            MapLayout::Struct { schema_id, .. } => self.struct_map(schema_id).keys.len(),
        }
    }

    /// The entry at `index` in the map's own order: key order for an entries
    /// layout and a struct, trie order for a trie. A trie finds it by skipping
    /// whole children by their totals, so reading every entry by index costs
    /// more than `map_view_entries`.
    pub fn map_view_entry(&self, layout: MapLayout, index: usize) -> (AnyValue, AnyValue) {
        assert!(index < self.map_view_count(layout), "map entry index out of bounds");
        match layout {
            MapLayout::Entries(addr) | MapLayout::Trie(addr) => unsafe { map_entry(addr, index) },
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                (
                    map.key_atom(index),
                    self.struct_key_value(struct_addr(object), &map, index),
                )
            }
        }
    }

    /// Every entry, in the map's own order, in one pass.
    pub fn map_view_entries(&self, layout: MapLayout) -> Vec<(AnyValue, AnyValue)> {
        match layout {
            MapLayout::Entries(addr) | MapLayout::Trie(addr) => unsafe { map_entries(addr) },
            MapLayout::Struct { .. } => (0..self.map_view_count(layout))
                .map(|index| self.map_view_entry(layout, index))
                .collect(),
        }
    }

    /// The map as a list of `part` of each entry, in the map's own order, in
    /// one pass. Each element is the word and kind the map stores, placed in
    /// its cell or tuple field as it is; nothing is decoded or boxed. The list
    /// is built from its end, so a node's children are listed last to first
    /// before its own entries, last to first.
    pub fn map_list(&mut self, map: AnyValueRef, part: MapPart) -> AnyValueRef {
        let layout = self.expect_map_layout(map, "map list");
        let pair = (part == MapPart::Pairs).then(|| self.pair_shape());
        let mut listing = Listing::new(part, pair, self.map_view_count(layout));
        match layout {
            MapLayout::Entries(addr) | MapLayout::Trie(addr) => unsafe { self.list_node(addr, &mut listing) },
            MapLayout::Struct { .. } => {
                for index in (0..self.map_view_count(layout)).rev() {
                    let (key, value) = self.map_view_entry(layout, index);
                    let entry = ((key.raw(), key.kind()), (value.raw(), value.kind()));
                    self.list_part(&mut listing, part, entry);
                }
            }
        }
        debug_assert_eq!(listing.unlisted, 0, "every entry is listed");
        if listing.first == 0 {
            return AnyValueRef::empty_list();
        }
        AnyValueRef::from_heap_object(ValueKind::LIST, listing.first as *const u8).expect("a listed map is a list")
    }

    /// Lists the entries of the node at `addr` and of its children, last
    /// entry first, so the list reads them in node order.
    ///
    /// # Safety
    ///
    /// `addr` is a node of a published map.
    unsafe fn list_node(&mut self, addr: *const u8, listing: &mut Listing) {
        for child in (0..unsafe { map_node_child_count(addr) }).rev() {
            unsafe { self.list_node(map_node_child(addr, child), listing) };
        }
        let count = unsafe { map_node_entry_count(addr) };
        let (tags, keys, values) = unsafe {
            (
                map_tag_ptr(addr),
                map_keys_ptr(addr, count),
                map_values_ptr(addr, count),
            )
        };
        let entry = |slot: usize| unsafe {
            let tag = read(tags.add(slot));
            (
                (read(keys.add(slot)), map_key_kind(tag)),
                (read(values.add(slot)), map_value_kind(tag)),
            )
        };
        match listing.part {
            MapPart::Keys => (0..count)
                .rev()
                .for_each(|slot| self.list_part(listing, MapPart::Keys, entry(slot))),
            MapPart::Values => (0..count)
                .rev()
                .for_each(|slot| self.list_part(listing, MapPart::Values, entry(slot))),
            MapPart::Pairs => (0..count)
                .rev()
                .for_each(|slot| self.list_part(listing, MapPart::Pairs, entry(slot))),
        }
    }

    /// Puts `part` of one entry, given as its key's and its value's words and
    /// kinds, in front of the list. Inlined where `part` is a constant, so each
    /// part's loop carries only its own work.
    #[inline(always)]
    fn list_part(&mut self, listing: &mut Listing, part: MapPart, (key, value): ((u64, ValueKind), (u64, ValueKind))) {
        if listing.room == 0 {
            let cell = (RuntimeAllocSite::ListConsStorage, LIST_CELL_SIZE);
            (listing.next, listing.room) = match listing.pair {
                None => self.alloc_run_at(&[cell], listing.unlisted),
                Some(pair) => self.alloc_run_at(&[(RuntimeAllocSite::Struct, pair.size), cell], listing.unlisted),
            };
        }
        let record = listing.next;
        listing.next = unsafe { record.add(listing.record_size()) };
        listing.room -= 1;
        listing.unlisted -= 1;
        // A key or a value the map holds is now held by the list too, so it is
        // published; a new pair is held by its cell alone.
        let (head, cell) = match part {
            MapPart::Keys | MapPart::Values => {
                let head = if part == MapPart::Keys { key } else { value };
                self.publish_contained_parts(head.0, head.1);
                (head, record)
            }
            MapPart::Pairs => {
                let pair = listing.pair.expect("a pair's shape");
                (self.write_pair(record, pair, key, value), unsafe {
                    record.add(pair.size)
                })
            }
        };
        unsafe { write(cell as *mut ListCons, ListCons::to_addr(head.0, head.1, listing.first)) };
        listing.first = cell as u64;
    }

    /// The 2-tuple's schema and the bytes one takes.
    fn pair_shape(&mut self) -> PairShape {
        let schema = self.schemas.borrow_mut().tuple(2);
        let schemas = self.schemas.borrow();
        let tuple = schemas.get(schema);
        let size = struct_size_for_payload(tuple.allocation_payload_size());
        assert!(
            tuple.size.is_multiple_of(8) && size == STRUCT_PAYLOAD_OFFSET + tuple.size as usize + 8,
            "a pair's two kind bytes fill one word, last in the tuple"
        );
        PairShape {
            header: schemas.struct_header(schema),
            size,
            kinds: tuple.size,
        }
    }

    /// Writes the `{key, value}` tuple of `pair`'s shape at `object`: its
    /// header, its two fields, and the word that holds their kind bytes.
    #[inline(always)]
    fn write_pair(
        &mut self,
        object: *mut u8,
        pair: PairShape,
        key: (u64, ValueKind),
        value: (u64, ValueKind),
    ) -> (u64, ValueKind) {
        self.publish_contained_parts(key.0, key.1);
        self.publish_contained_parts(value.0, value.1);
        let kinds = u64::from(key.1.tag()) | u64::from(value.1.tag()) << 8;
        unsafe {
            write(object as *mut u64, pair.header);
            write(struct_field_raw_slot(object, 0), key.0);
            write(struct_field_raw_slot(object, 8), value.0);
            write(struct_field_kind_slot(object, pair.kinds) as *mut u64, kinds);
        }
        (object as u64, ValueKind::STRUCT)
    }

    /// The node and entry slot that hold `key` in the map at `addr`, a flat
    /// map or a trie.
    #[inline]
    pub(super) fn find(&self, addr: *const u8, key: AnyValue) -> Option<(*const u8, usize)> {
        if unsafe { map_header_is_trie(addr) } {
            return self.trie_find(addr, key);
        }
        self.flat_find(addr, key).map(|slot| (addr, slot))
    }

    /// The value under `key`, or `None` when the map lacks it.
    pub fn map_view_get(&mut self, layout: MapLayout, key: AnyValue) -> Option<AnyValueRef> {
        match layout {
            MapLayout::Entries(addr) | MapLayout::Trie(addr) => self
                .find(addr, key)
                .map(|(node, slot)| unsafe { map_slot_refs(node, slot).1 }),
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                let index = map.find(key)?;
                Some(self.struct_key_value_ref(object, &map, index))
            }
        }
    }

    pub fn map_view_has_key(&self, layout: MapLayout, key: AnyValue) -> bool {
        match layout {
            MapLayout::Entries(addr) | MapLayout::Trie(addr) => self.find(addr, key).is_some(),
            MapLayout::Struct { schema_id, .. } => self.struct_map(schema_id).find(key).is_some(),
        }
    }

    /// The map with `key` bound to `value`. A struct keeps its layout when
    /// `key` is one of its fields; any other key leaves the schema. A trie
    /// copies the path to the key's slot.
    pub fn map_view_put(&mut self, layout: MapLayout, key: AnyValue, value: AnyValue) -> AnyValueRef {
        match layout {
            MapLayout::Entries(addr) => entries_ref(self.map_put_entry(addr, key, value)),
            MapLayout::Trie(addr) => entries_ref(self.trie_put(addr, key, value)),
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                match map.find(key).map(|index| map.keys[index]) {
                    Some(StructKey::Field(field)) => self.struct_with_field(struct_addr(object), &map, field, value),
                    _ => {
                        let entries = self.struct_as_entries(layout);
                        self.map_put_slot(entries, key, value)
                    }
                }
            }
        }
    }

    /// The map without `key`; the same map when it lacks `key`.
    pub fn map_view_delete(&mut self, map: AnyValueRef, key: AnyValue) -> AnyValueRef {
        match self.expect_map_layout(map, "map delete") {
            MapLayout::Trie(root) => self.trie_delete(root, key).map_or(map, entries_ref),
            MapLayout::Entries(addr) => match self.flat_find(addr, key) {
                Some(slot) => entries_ref(self.flat_map_without_slot(addr, slot)),
                None => map,
            },
            layout @ MapLayout::Struct { schema_id, .. } => {
                if self.struct_map(schema_id).find(key).is_none() {
                    return map;
                }
                let entries = self.struct_as_entries(layout);
                self.map_view_delete(entries, key)
            }
        }
    }

    /// The entries of a struct that is leaving its schema, as the map of
    /// them that is not a struct: `__struct__` is a key like the rest.
    #[inline(never)]
    fn struct_as_entries(&mut self, layout: MapLayout) -> AnyValueRef {
        let entries = self.map_view_entries(layout);
        entries_ref(self.alloc_bulk_map_entries(&entries))
    }

    /// The struct `object` copied into an unpublished destination of its own
    /// layout.
    pub(super) fn alloc_struct_update(&mut self, object: AnyValueRef, schema_id: u32) -> u64 {
        let layout = self.struct_map(schema_id).layout();
        heap_object_word(
            unsafe { self.copy_struct(struct_addr(object), layout) },
            ValueKind::STRUCT,
        )
    }

    /// Replace the value under `key` in the unpublished struct `object`, and
    /// answer the destination to continue with. A field is stored in its
    /// slot. The module is not stored anywhere: naming the struct's own keeps
    /// the struct, and naming another moves the entries to an entries
    /// destination that holds it. A key the struct lacks is the miss, `0`.
    pub(super) fn struct_update_put(
        &mut self,
        object: AnyValueRef,
        schema_id: u32,
        key: AnyValue,
        value: AnyValue,
    ) -> u64 {
        let map = self.struct_map(schema_id);
        let Some(index) = map.find(key) else {
            return 0;
        };
        let addr = struct_addr(object);
        match map.keys[index] {
            StructKey::Field(field) => {
                self.store_field(addr, map.offsets[field], value);
                heap_object_word(addr, ValueKind::STRUCT)
            }
            StructKey::Module if value == map.module => heap_object_word(addr, ValueKind::STRUCT),
            StructKey::Module => {
                let entries = self.alloc_entries_update(MapLayout::Struct { object, schema_id });
                unsafe { self.map_destination_put(entries, key, value) }
            }
        }
    }

    /// Store `value` in a field of the unpublished struct at `addr`. A list
    /// becomes shared, since the struct now holds it too.
    fn store_field(&mut self, addr: *mut u8, offset: u32, value: AnyValue) {
        self.assert_written_object_is_young(addr);
        self.publish_contained_parts(value.raw(), value.kind());
        unsafe { self.write_field_slot(addr, offset, value) };
    }

    fn struct_map(&self, schema_id: u32) -> Rc<StructMap> {
        if let Some(map) = self.struct_maps.by_schema.borrow().get(&schema_id) {
            return Rc::clone(map);
        }
        let map = Rc::new(self.learn_struct_map(schema_id));
        self.struct_maps
            .by_schema
            .borrow_mut()
            .insert(schema_id, Rc::clone(&map));
        map
    }

    fn learn_struct_map(&self, schema_id: u32) -> StructMap {
        let schemas = self.schemas.borrow();
        let schema = schemas.get(schema_id);
        let keys = schemas
            .map_keys(schema_id)
            .expect("a map-layout struct has map keys")
            .to_vec();
        let atom = |name: &str| self.node.intern_atom(name) as u64;
        let atoms = keys
            .iter()
            .map(|key| match key {
                StructKey::Module => atom(STRUCT_MODULE_FIELD),
                StructKey::Field(index) => atom(
                    schema.fields[*index]
                        .name
                        .as_deref()
                        .expect("a named struct's field has a name"),
                ),
            })
            .collect();
        let module = match &schema.identity {
            super::SchemaIdentity::Named(name) => AnyValue::atom(atom(&name.atom_name()) as u32),
            other => panic!("schema {} has no module", other.display_name()),
        };
        StructMap {
            keys,
            atoms,
            offsets: schema.fields.iter().map(|field| field.offset).collect(),
            module,
        }
    }

    fn struct_key_value(&self, addr: *mut u8, map: &StructMap, index: usize) -> AnyValue {
        match map.keys[index] {
            StructKey::Module => map.module,
            StructKey::Field(field) => self.read_field_slot(addr, map.offsets[field]),
        }
    }

    fn struct_key_value_ref(&mut self, object: AnyValueRef, map: &StructMap, index: usize) -> AnyValueRef {
        match map.keys[index] {
            StructKey::Module => self.box_any_value_ref(map.module),
            StructKey::Field(field) => self
                .read_struct_field_ref(object, map.offsets[field])
                .expect("struct field ref"),
        }
    }

    /// A copy of the struct at `addr` with field `field` replaced by `value`.
    fn struct_with_field(&mut self, addr: *mut u8, map: &StructMap, field: usize, value: AnyValue) -> AnyValueRef {
        let copy = unsafe { self.copy_struct(addr, map.layout()) };
        self.store_field(copy, map.offsets[field], value);
        AnyValueRef::from_heap_object(ValueKind::STRUCT, copy).expect("struct copy ref")
    }
}

impl StructMap {
    fn layout(&self) -> SlotLayout {
        SlotLayout::of(self.offsets.len())
    }

    fn key_atom(&self, index: usize) -> AnyValue {
        AnyValue::atom(self.atoms[index] as u32)
    }

    /// Where `key` sits among the struct's keys; only an atom names one, and
    /// it is found by its word, as a map finds it.
    fn find(&self, key: AnyValue) -> Option<usize> {
        if key.kind() != ValueKind::ATOM {
            return None;
        }
        unsafe { position_of_word(self.atoms.as_ptr(), self.atoms.len(), key.raw()) }
    }
}

fn struct_addr(object: AnyValueRef) -> *mut u8 {
    object.struct_addr().expect("a struct layout holds a struct")
}

/// The layout of the destination `bits` names: an unpublished entries
/// destination, a struct's copy, or the trie an update of a trie continues
/// with. `None` for `0`, which is what an update that missed a key is left
/// with.
pub(super) fn destination_layout(bits: u64) -> Option<MapLayout> {
    if bits == 0 {
        return None;
    }
    if let Some(addr) = map_addr_from_tagged(bits) {
        return Some(if unsafe { map_header_is_trie(addr) } {
            MapLayout::Trie(addr)
        } else {
            MapLayout::Entries(addr)
        });
    }
    let addr = struct_addr_from_tagged(bits).expect("a map destination is a map or a struct");
    Some(MapLayout::Struct {
        object: AnyValueRef::from_heap_object(ValueKind::STRUCT, addr).expect("struct destination"),
        schema_id: unsafe { struct_schema_id(addr as *const u8) },
    })
}

fn entries_ref(bits: u64) -> AnyValueRef {
    let addr = map_addr_from_tagged(bits).expect("published map");
    AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")
}

#[cfg(test)]
#[path = "map_view_test.rs"]
mod map_view_test;
