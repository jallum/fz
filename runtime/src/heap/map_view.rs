//! A map read the same way whichever layout holds it.
//!
//! A map has two physical layouts. The entries layout is a sorted array of
//! key/value pairs. The struct layout is a schema-backed object: a named
//! struct's keys are its schema's fields plus `__struct__`, which answers the
//! module. Which layout a value has is invisible to the language, so every map
//! operation reads through `MapLayout` and never asks for one layout by name.
//!
//! Writes keep the struct layout while the keys stay the schema's: replacing a
//! field copies the object. Adding a key or removing one leaves the schema, so
//! the result is published in the entries layout with `__struct__` a real key.

use std::cell::{Cell, RefCell};
use std::collections::HashMap;
use std::rc::Rc;

use super::Heap;
use super::schema::StructKey;
use crate::any_value::{
    AnyValue, AnyValueRef, ValueKind, map_addr_from_tagged, map_count, map_entry, struct_schema_id,
};
use crate::heap::map_entry_refs;
use crate::module_name::STRUCT_MODULE_FIELD;
use crate::term::{NumericMode, TermComparator};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum MapLayout {
    Entries(*mut u8),
    Struct { object: AnyValueRef, schema_id: u32 },
}

/// A named struct's keys in map key order, each with its atom and, for a
/// field, its slot offset.
struct StructMap {
    keys: Vec<StructKey>,
    atoms: Vec<AnyValue>,
    offsets: Vec<u32>,
    module: AnyValue,
}

/// The atoms a heap's named structs answer as maps, learned once per schema.
#[derive(Default)]
pub(crate) struct StructMaps {
    by_schema: RefCell<HashMap<u32, Rc<StructMap>>>,
    by_module: RefCell<HashMap<u32, Option<u32>>>,
    module_key: Cell<Option<AnyValue>>,
}

impl Heap {
    /// The layout of `value` when it is a map, in either layout; `None` for
    /// every other value, a tuple included.
    pub fn map_layout(&self, value: AnyValueRef) -> Option<MapLayout> {
        match value.tag() {
            ValueKind::MAP => value.map_addr().ok().map(MapLayout::Entries),
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

    /// `map_layout`, for a caller whose value the types promise is a map.
    pub fn expect_map_layout(&self, value: AnyValueRef, context: &str) -> MapLayout {
        self.map_layout(value)
            .unwrap_or_else(|| panic!("{context}: expected a map, found {:?}", value.tag()))
    }

    pub fn map_view_count(&self, layout: MapLayout) -> usize {
        match layout {
            MapLayout::Entries(addr) => unsafe { map_count(addr) },
            MapLayout::Struct { schema_id, .. } => self.struct_map(schema_id).keys.len(),
        }
    }

    /// The entry at `index` in map key order.
    pub fn map_view_entry(&self, layout: MapLayout, index: usize) -> (AnyValue, AnyValue) {
        assert!(index < self.map_view_count(layout), "map entry index out of bounds");
        match layout {
            MapLayout::Entries(addr) => unsafe { map_entry(addr, index) },
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                (
                    map.atoms[index],
                    self.struct_key_value(struct_addr(object), &map, index),
                )
            }
        }
    }

    /// The entry at `index` as references. A struct's keys and module live in
    /// no slot of the object, so they are boxed.
    pub fn map_view_entry_refs(&mut self, layout: MapLayout, index: usize) -> (AnyValueRef, AnyValueRef) {
        match layout {
            MapLayout::Entries(addr) => {
                assert!(index < unsafe { map_count(addr) }, "map entry index out of bounds");
                unsafe { map_entry_refs(addr, index) }
            }
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                let key = self.box_any_value_ref(map.atoms[index]);
                (key, self.struct_key_value_ref(object, &map, index))
            }
        }
    }

    pub fn map_view_entries(&self, layout: MapLayout) -> Vec<(AnyValue, AnyValue)> {
        (0..self.map_view_count(layout))
            .map(|index| self.map_view_entry(layout, index))
            .collect()
    }

    /// The value under `key`, or `None` when the map lacks it.
    pub fn map_view_get(&mut self, layout: MapLayout, key: AnyValue) -> Option<AnyValueRef> {
        match layout {
            MapLayout::Entries(addr) => self
                .map_key_position(addr, key)
                .ok()
                .map(|index| unsafe { map_entry_refs(addr, index).1 }),
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                let index = map.position(key)?;
                Some(self.struct_key_value_ref(object, &map, index))
            }
        }
    }

    pub fn map_view_has_key(&self, layout: MapLayout, key: AnyValue) -> bool {
        match layout {
            MapLayout::Entries(addr) => self.map_key_position(addr, key).is_ok(),
            MapLayout::Struct { schema_id, .. } => self.struct_map(schema_id).position(key).is_some(),
        }
    }

    /// The map with `key` bound to `value`. A struct keeps its layout when
    /// `key` is one of its fields; any other key leaves the schema.
    pub fn map_view_put(&mut self, layout: MapLayout, key: AnyValue, value: AnyValue) -> AnyValueRef {
        match layout {
            MapLayout::Entries(addr) => entries_ref(self.map_put_entry(addr, key, value)),
            MapLayout::Struct { object, schema_id } => {
                let map = self.struct_map(schema_id);
                match map.position(key).map(|index| map.keys[index]) {
                    Some(StructKey::Field(field)) => self.struct_with_field(struct_addr(object), &map, field, value),
                    _ => {
                        let mut entries = self.map_view_entries(layout);
                        entries.push((key, value));
                        entries_ref(self.alloc_map_slots(&entries))
                    }
                }
            }
        }
    }

    /// The map without `key`; the same map when it lacks `key`.
    pub fn map_view_delete(&mut self, map: AnyValueRef, key: AnyValue) -> AnyValueRef {
        let layout = self.expect_map_layout(map, "map delete");
        if !self.map_view_has_key(layout, key) {
            return map;
        }
        let entries: Vec<_> = {
            let schemas = self.schemas.borrow();
            let comparator = TermComparator::new(&self.node, &schemas);
            self.map_view_entries(layout)
                .into_iter()
                .filter(|(entry_key, _)| !comparator.compare(*entry_key, key, NumericMode::Strict).is_eq())
                .collect()
        };
        entries_ref(self.alloc_ordered_map_entries(entries.into_iter()))
    }

    /// The entries layout map at `addr` as the named struct its keys are
    /// exactly, when they are: `__struct__` names a registered struct and the
    /// other keys are that struct's fields.
    pub(super) fn struct_of_entries(&mut self, addr: *mut u8) -> Option<AnyValueRef> {
        let module_key = self.struct_module_key();
        let index = self.map_key_position(addr, module_key).ok()?;
        let (_, module) = unsafe { map_entry(addr, index) };
        let schema_id = self.struct_named(module)?;
        let map = self.struct_map(schema_id);
        let count = unsafe { map_count(addr) };
        if count != map.atoms.len() || (0..count).any(|i| unsafe { map_entry(addr, i) }.0 != map.atoms[i]) {
            return None;
        }
        let object = self.alloc_struct(schema_id);
        for (index, key) in map.keys.iter().enumerate() {
            if let StructKey::Field(field) = key {
                let value = unsafe { map_entry(addr, index) }.1;
                self.publish_contained_parts(value.raw(), value.kind());
                unsafe { self.write_field_slot(object, map.offsets[*field], value) };
            }
        }
        Some(AnyValueRef::from_heap_object(ValueKind::STRUCT, object).expect("struct ref"))
    }

    /// The registered named struct whose module is the atom `module`.
    fn struct_named(&self, module: AnyValue) -> Option<u32> {
        let AnyValue::Atom(id) = module else {
            return None;
        };
        if let Some(found) = self.struct_maps.by_module.borrow().get(&id) {
            return *found;
        }
        let found = self
            .node
            .atom_name(id)
            .and_then(|name| self.schemas.borrow().named_by_atom_name(&name));
        self.struct_maps.by_module.borrow_mut().insert(id, found);
        found
    }

    fn struct_module_key(&self) -> AnyValue {
        if let Some(key) = self.struct_maps.module_key.get() {
            return key;
        }
        let key = AnyValue::atom(self.node.intern_atom(STRUCT_MODULE_FIELD));
        self.struct_maps.module_key.set(Some(key));
        key
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
        let atom = |name: &str| AnyValue::atom(self.node.intern_atom(name));
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
            super::SchemaIdentity::Named(name) => atom(&name.atom_name()),
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
        let schema_id = unsafe { struct_schema_id(addr as *const u8) };
        let copy = self.alloc_struct(schema_id);
        for (index, offset) in map.offsets.iter().enumerate() {
            let item = if index == field {
                value
            } else {
                self.read_field_slot(addr, *offset)
            };
            self.publish_contained_parts(item.raw(), item.kind());
            unsafe { self.write_field_slot(copy, *offset, item) };
        }
        AnyValueRef::from_heap_object(ValueKind::STRUCT, copy).expect("struct copy ref")
    }
}

impl StructMap {
    /// Where `key` sits among the struct's keys; only an atom names one.
    fn position(&self, key: AnyValue) -> Option<usize> {
        self.atoms.iter().position(|atom| *atom == key)
    }
}

fn struct_addr(object: AnyValueRef) -> *mut u8 {
    object.struct_addr().expect("a struct layout holds a struct")
}

fn entries_ref(bits: u64) -> AnyValueRef {
    let addr = map_addr_from_tagged(bits).expect("published map");
    AnyValueRef::from_heap_object(ValueKind::MAP, addr).expect("map ref")
}

#[cfg(test)]
#[path = "map_view_test.rs"]
mod map_view_test;
