//! A field destination: one open field of a cell, named so that the cell can
//! move and the field still be found.
//!
//! A builder that returns `[h | f(t)]` places the cell first and leaves its
//! tail open, and the call fills it. The open field is written down as a
//! `FieldDestination`, a word of the kind `ValueKind::DESTINATION`: the cell's
//! address, with a selector in the bits above the address saying which field
//! of which kind of cell. The collector forwards the cell and recomposes the
//! word, so the destination follows its cell wherever the cell goes. A word
//! never holds an address into the middle of a cell.
//!
//! Three layouts hold a field: a list cell's link word (the open tail is the
//! terminator flag with address 0, `ListLink::hole`), a struct or tuple field
//! (a word and a kind byte), and a map entry's value (a word and a kind
//! nibble). The last two are open when they hold `OPEN_FIELD`, a null
//! reference. The selector space is split by layout: 0 is the list tail, then
//! the struct fields, then the map slots of one node.
//!
//! Filling a field is not a barrier. A collection runs only at a yield or a
//! park, so between two collections nothing reads a field half written; the
//! fill stores the field's word and its kind and keeps no other record. The
//! collector keeps the record instead: each collection writes down the
//! destinations it meets with their fields still open (`Heap::open_holes`),
//! and the next minor collection reads those fields first, because a young
//! value may have been stored into an old cell since.

use super::Heap;
use super::schema::SchemaRegistry;
use crate::alloc_site::RuntimeAllocSite;
use crate::any_value::{
    AnyValue, AnyValueRef, AnyValueRefPacking, ListCons, ListLink, ListTail, MAP_DESTINATION_FLAG, MAP_FLAT_MAX,
    ValueKind, map_node_entry_count, map_tag_ptr, map_value_kind, map_values_ptr, struct_field_kind_slot,
    struct_field_raw_slot, struct_schema_id,
};
use std::ptr::{read, write};

const SELECTOR_SHIFT: u8 = AnyValueRefPacking::current().tag_shift();
const ADDRESS_MASK: u64 = AnyValueRefPacking::current().address_mask();
/// How many fields the bits above an address can name.
const SELECTOR_SPACE: usize = 1 << (64 - SELECTOR_SHIFT as usize);
/// The low nibble of the value half of a map entry's kind byte.
const VALUE_NIBBLE: u8 = 0xF;

/// Which field of a cell a destination names.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Layout {
    /// The tail of a list cell, held in its link word.
    ListTail,
    /// The value field with this ordinal of a struct or tuple.
    StructField(usize),
    /// The value of this slot of a published map node.
    MapValue(usize),
}

impl Layout {
    /// The kind of cell the field lives in.
    pub const fn cell_kind(self) -> ValueKind {
        match self {
            Self::ListTail => ValueKind::LIST,
            Self::StructField(_) => ValueKind::STRUCT,
            Self::MapValue(_) => ValueKind::MAP,
        }
    }
}

/// An open field, named by its cell and its layout. See the module comment.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FieldDestination(u64);

impl FieldDestination {
    /// The most map slots of one node a destination can name: a flat map's
    /// entries are the most a node holds.
    pub const MAP_SLOT_LIMIT: usize = MAP_FLAT_MAX;
    /// The most struct or tuple value fields a destination can name. What the
    /// selector bits leave after the list tail and the map slots.
    pub const STRUCT_FIELD_LIMIT: usize = SELECTOR_SPACE - 1 - Self::MAP_SLOT_LIMIT;

    /// Whether `layout` can be named by a destination. A field past the limit
    /// cannot be one, and whoever chooses to build into a field asks first.
    pub const fn fits(layout: Layout) -> bool {
        match layout {
            Layout::ListTail => true,
            Layout::StructField(ordinal) => ordinal < Self::STRUCT_FIELD_LIMIT,
            Layout::MapValue(slot) => slot < Self::MAP_SLOT_LIMIT,
        }
    }

    pub fn new(cell: *mut u8, layout: Layout) -> Self {
        assert!(Self::fits(layout), "{layout:?} does not fit a destination");
        debug_assert!(
            (cell as u64) & !ADDRESS_MASK == 0 && (cell as usize).is_multiple_of(16),
            "a destination names an aligned heap cell"
        );
        let selector = match layout {
            Layout::ListTail => 0,
            Layout::StructField(ordinal) => 1 + ordinal,
            Layout::MapValue(slot) => 1 + Self::STRUCT_FIELD_LIMIT + slot,
        };
        Self(cell as u64 | (selector as u64) << SELECTOR_SHIFT)
    }

    /// The destination a word of kind `ValueKind::DESTINATION` holds.
    pub fn from_word(word: u64) -> Self {
        Self(word)
    }

    /// The word a slot of kind `ValueKind::DESTINATION` holds.
    pub const fn word(self) -> u64 {
        self.0
    }

    pub fn cell_addr(self) -> *mut u8 {
        (self.0 & ADDRESS_MASK) as *mut u8
    }

    pub fn layout(self) -> Layout {
        let selector = (self.0 >> SELECTOR_SHIFT) as usize;
        let first_slot = 1 + Self::STRUCT_FIELD_LIMIT;
        match selector {
            0 => Layout::ListTail,
            1..=Self::STRUCT_FIELD_LIMIT => Layout::StructField(selector - 1),
            _ => Layout::MapValue(selector - first_slot),
        }
    }

    /// The same field of the cell at `cell`, which is where the collection
    /// moved this destination's cell to.
    pub fn rebased(self, cell: *mut u8) -> Self {
        Self::new(cell, self.layout())
    }

    /// Whether the field is still open.
    ///
    /// # Safety
    /// The destination names a live cell of its layout's kind.
    pub(super) unsafe fn is_open(self, schemas: &SchemaRegistry) -> bool {
        unsafe { Place::of(self, schemas) }.is_open()
    }
}

/// What an open struct field or map value holds: address 0 under the kind
/// `STRUCT`. No live value is a struct at address 0, so no filled field holds
/// it, and an int 0 or an `[]` is told apart by its kind. Every reader of a
/// field that decodes it as a value meets a null heap reference and panics, and
/// the collector skips a null address of a heap kind, so the placeholder is
/// traced for free and never read as a value.
pub(super) const OPEN_FIELD: (u64, ValueKind) = (0, ValueKind::STRUCT);

/// Where a destination's field is stored: the two words a fill or a trace
/// touches, resolved from the cell and its layout.
#[derive(Clone, Copy)]
pub(super) enum Place {
    Link(*mut ListCons),
    /// A word and the byte that holds its kind.
    Struct {
        word: *mut u64,
        kind: *mut u8,
    },
    /// A word and the kind byte of its entry, whose low nibble is the value's
    /// kind.
    Map {
        word: *mut u64,
        kinds: *mut u8,
    },
}

impl Place {
    /// # Safety
    /// `dest` names a live cell of its layout's kind.
    pub(super) unsafe fn of(dest: FieldDestination, schemas: &SchemaRegistry) -> Self {
        let cell = dest.cell_addr();
        match dest.layout() {
            Layout::ListTail => Self::Link(cell as *mut ListCons),
            Layout::StructField(ordinal) => {
                let schema = schemas.get(unsafe { struct_schema_id(cell) });
                let (field, kind_offset) = schema
                    .any_value_fields_with_kind_offsets()
                    .nth(ordinal)
                    .unwrap_or_else(|| panic!("a destination names value field {ordinal} of a struct that has fewer"));
                Self::Struct {
                    word: unsafe { struct_field_raw_slot(cell, field.offset) },
                    kind: unsafe { struct_field_kind_slot(cell, kind_offset) },
                }
            }
            Layout::MapValue(slot) => {
                let count = unsafe { map_node_entry_count(cell) };
                assert!(slot < count, "a destination names map slot {slot} of a node of {count}");
                Self::Map {
                    word: unsafe { map_values_ptr(cell, count).add(slot) },
                    kinds: unsafe { map_tag_ptr(cell).add(slot) },
                }
            }
        }
    }

    /// Whether the field still holds the placeholder (a list tail: the hole
    /// its link names).
    pub(super) fn is_open(self) -> bool {
        unsafe {
            match self {
                Self::Link(cons) => (&*cons).tail() == ListTail::Hole,
                Self::Struct { word, kind } => {
                    (read(word), ValueKind::new(read(kind))) == (OPEN_FIELD.0, Some(OPEN_FIELD.1))
                }
                Self::Map { word, kinds } => (read(word), map_value_kind(read(kinds))) == OPEN_FIELD,
            }
        }
    }

    /// Store `value` in the field: its word and its kind, nothing else.
    fn store(self, value: AnyValue) {
        unsafe {
            match self {
                Self::Link(_) => unreachable!("a list tail is closed with a link"),
                Self::Struct { word, kind } => {
                    write(word, value.raw());
                    write(kind, value.kind().tag());
                }
                Self::Map { word, kinds } => {
                    write(word, value.raw());
                    write(kinds, (read(kinds) & !VALUE_NIBBLE) | value.kind().tag());
                }
            }
        }
    }

    /// Leave the field open.
    fn open(self) {
        unsafe {
            match self {
                Self::Link(_) => unreachable!("a list tail opens with the cell that holds it"),
                Self::Struct { word, kind } => {
                    write(word, OPEN_FIELD.0);
                    write(kind, OPEN_FIELD.1.tag());
                }
                Self::Map { word, kinds } => {
                    write(word, OPEN_FIELD.0);
                    write(kinds, (read(kinds) & !VALUE_NIBBLE) | OPEN_FIELD.1.tag());
                }
            }
        }
    }
}

impl Heap {
    /// A list cell holding `head` whose tail is open, and the destination
    /// that closes it.
    pub fn alloc_open_list_cell(&mut self, head: AnyValue) -> (AnyValueRef, FieldDestination) {
        self.publish_contained_parts(head.raw(), head.kind());
        let bits = self.place_list_cons(
            RuntimeAllocSite::ListConsStorage,
            head.raw(),
            ListLink::hole(head.kind()),
        );
        let cell = crate::any_value::list_addr_from_tagged(bits).expect("a new list cell");
        let cell_ref = AnyValueRef::from_heap_object(ValueKind::LIST, cell).expect("a new list cell ref");
        (cell_ref, FieldDestination::new(cell, Layout::ListTail))
    }

    /// Open value field `ordinal` of the struct or tuple at `object`, which
    /// this heap has just allocated, and answer its destination.
    ///
    /// # Safety
    /// `object` is a live struct of this heap and has a value field `ordinal`.
    pub unsafe fn open_struct_field(&mut self, object: *mut u8, ordinal: usize) -> FieldDestination {
        self.assert_written_object_is_young(object);
        let dest = FieldDestination::new(object, Layout::StructField(ordinal));
        unsafe { Place::of(dest, &self.schemas.borrow()) }.open();
        dest
    }

    /// Open the value of slot `slot` of the published map node at `node`,
    /// which this heap has just allocated, and answer its destination. The
    /// node is published first, so its keys are in their final order and the
    /// slot stays where it is.
    ///
    /// # Safety
    /// `node` is a live published map node of this heap with a slot `slot`.
    pub unsafe fn open_map_value(&mut self, node: *mut u8, slot: usize) -> FieldDestination {
        self.assert_written_object_is_young(node);
        assert_eq!(
            unsafe { read(node as *const u64) } & MAP_DESTINATION_FLAG,
            0,
            "a map value is opened after its map is published"
        );
        let dest = FieldDestination::new(node, Layout::MapValue(slot));
        unsafe { Place::of(dest, &self.schemas.borrow()) }.open();
        dest
    }

    /// Whether the field `dest` names is still open.
    pub fn destination_is_open(&self, dest: FieldDestination) -> bool {
        unsafe { dest.is_open(&self.schemas.borrow()) }
    }

    /// Close the open field `dest` names with `value`.
    ///
    /// The cell may be old: a collection moved it and kept it, and the field
    /// is closed in place anyway. That is sound because the collector wrote
    /// the open field down (`open_holes`) and reads it at the next minor
    /// collection. The fill is not a write barrier and records nothing.
    pub fn fill_destination(&mut self, dest: FieldDestination, value: AnyValue) {
        let place = unsafe { Place::of(dest, &self.schemas.borrow()) };
        assert!(place.is_open(), "{dest:?} is filled once");
        match place {
            Place::Link(cons) => {
                let head_kind = unsafe { &*cons }.head_kind();
                let link = self.link_to_tail(head_kind, value);
                unsafe { &mut *cons }.close_tail(link);
            }
            Place::Struct { .. } | Place::Map { .. } => {
                if let AnyValue::HeapRef(heap_value) = value {
                    self.share(heap_value).expect("a value stored in a field is published");
                }
                place.store(value);
            }
        }
    }
}

#[cfg(test)]
#[path = "destination_test.rs"]
mod destination_test;
