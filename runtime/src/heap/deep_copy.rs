//! Deep copies between heaps and into a heap's own gift window.
//!
//! A copy reads one heap and allocates into another. The source is read
//! through a `HeapView`, an owned snapshot of the source's schema table (and,
//! in debug builds, its address ranges), so a sender that copies into a gift window on its own heap
//! holds one `&mut Heap` and no second reference to the same heap.

use smallvec::SmallVec;
use std::cell::RefCell;
use std::ptr::{copy_nonoverlapping, read, write};
use std::rc::Rc;
use std::slice::from_raw_parts;

use super::block_pool::round_up_16;
#[cfg(debug_assertions)]
use super::ref_io::ptr_in_ranges;
use super::ref_io::strict_object_size;
use super::schema::{FieldKind, SchemaRegistry};
use super::stats::StubSite;
use super::{Heap, HeapAllocKind};
use crate::any_value::AnyValueRef;
use crate::any_value::{
    AnyValue, EMPTY_LIST, ListCons, ValueKind, bitstring_bit_len, bitstring_bytes_ptr, closure_addr_from_tagged,
    closure_arity, closure_capture_set, closure_capture_value, closure_captured_count, closure_fn_ptr,
    closure_halt_kind, heap_object_word, list_addr_from_tagged, map_addr_from_tagged, map_node_child,
    map_node_child_count, map_node_entry_count, map_slot, share_struct, struct_field_kind_slot, struct_field_raw_slot,
    struct_schema_id,
};
use crate::bits::{BINREF_BYTES, BinView, SharedBinHandle, alloc_binref, alloc_view, shared_bin_freeze};
use crate::resource::{ResourceHandle, ResourceStub, alloc_resource};

/// What a deep copy needs to know about the heap it reads: how its structs are
/// laid out, and, in debug builds, which addresses belong to it. Taken by
/// value, so reading a heap and allocating into a gift window on that same
/// heap needs no second reference to it.
///
/// A copy shares an object named by a literal address and copies every other
/// object, which is the source heap's own.
pub struct HeapView {
    #[cfg(debug_assertions)]
    ranges: Vec<(*mut u8, *mut u8)>,
    schemas: Rc<RefCell<SchemaRegistry>>,
}

impl HeapView {
    /// Whether a copy passes `value` through by pointer. Debug builds check
    /// that the literal bit agrees with where the object lies.
    fn shares(&self, value: AnyValue) -> bool {
        let AnyValue::HeapRef(value_ref) = value else {
            return false;
        };
        let literal = value_ref.is_literal();
        self.assert_classified(value_ref.storage_addr(), literal);
        literal
    }

    /// Debug-only: a source object is in the source heap exactly when it is not a literal.
    fn assert_classified(&self, p: *mut u8, literal: bool) {
        #[cfg(debug_assertions)]
        assert_eq!(
            ptr_in_ranges(p, self.ranges.iter().copied()),
            !literal,
            "{p:p} is {} but lies {} the source heap",
            if literal {
                "a tagged literal"
            } else {
                "an untagged object"
            },
            if literal { "inside" } else { "outside" },
        );
        #[cfg(not(debug_assertions))]
        let _ = (p, literal);
    }

    fn read_field_slot(&self, obj: *mut u8, field_offset: u32) -> AnyValue {
        let schema_id = unsafe { struct_schema_id(obj as *const u8) };
        let schema = self.schemas.borrow();
        let kind_offset = schema.get(schema_id).value_field_kind_offset(field_offset);
        unsafe {
            let raw = read(struct_field_raw_slot(obj as *const u8, field_offset));
            let kind = read(struct_field_kind_slot(obj as *const u8, kind_offset));
            AnyValue::decode_parts(raw, kind).expect("struct field kind")
        }
    }
}

impl Heap {
    /// A snapshot of every address range this heap owns right now: the tip,
    /// the tip set aside by an open gift window, and parked blocks.
    pub fn view(&self) -> HeapView {
        HeapView {
            #[cfg(debug_assertions)]
            ranges: self.block_ranges().collect(),
            schemas: Rc::clone(&self.schemas),
        }
    }
}

/// The bytes `deep_copy_any_value_ref` allocates when it copies `values`,
/// without allocating or writing anything.
///
/// It walks what the copy walks: the same kinds, the same ownership test
/// against the source view, and, like the copy, it keeps no record of what it
/// has reached: a subterm reached twice is counted twice, as the copy makes it
/// twice. A copied object has the size of its source, which
/// `strict_object_size` states for the collector too; each scalar the copy
/// boxes takes one slot.
pub fn measure_deep_copy(values: &[AnyValueRef], src_heap: &HeapView) -> usize {
    let mut measure = CopyMeasure { src_heap, bytes: 0 };
    for value in values {
        measure.value_ref(*value);
    }
    measure.bytes
}

struct CopyMeasure<'a> {
    src_heap: &'a HeapView,
    bytes: usize,
}

impl CopyMeasure<'_> {
    fn value_ref(&mut self, value: AnyValueRef) {
        if value.is_empty_list() {
            return;
        }
        match value.tag() {
            ValueKind::NULL => {}
            tag if tag.is_immediate() => {}
            tag if tag.is_boxed_scalar() => self.bytes += round_up_16(size_of::<u64>()),
            tag if tag.is_heap() => {
                self.value(AnyValue::from_ref(value).expect("heap ref value"));
            }
            _ => unreachable!("AnyValueRef tag set is exhaustive"),
        }
    }

    /// Count `child` when it is a heap value; an inline slot costs nothing.
    fn slot(&mut self, child: AnyValue) {
        if child.kind().is_heap() {
            self.value(child);
        }
    }

    fn value(&mut self, src: AnyValue) {
        let Some(sp) = src.heap_addr() else {
            return;
        };
        if sp.is_null() || self.src_heap.shares(src) {
            return;
        }
        match src.kind() {
            ValueKind::LIST => self.list(sp),
            ValueKind::MAP
            | ValueKind::CLOSURE
            | ValueKind::STRUCT
            | ValueKind::BITSTRING
            | ValueKind::BINVIEW
            | ValueKind::RESOURCE => self.object(sp, src),
            _ => {}
        }
    }

    /// Count the object at `sp` and what it holds.
    fn object(&mut self, sp: *mut u8, src: AnyValue) {
        self.bytes += strict_object_size(src.kind(), sp, &self.src_heap.schemas.borrow());
        if src.kind() == ValueKind::BINVIEW {
            // Each copied view arrives with a BinRef of its own.
            self.bytes += BINREF_BYTES;
        }
        self.children(sp, src.kind());
    }

    fn children(&mut self, sp: *mut u8, kind: ValueKind) {
        match kind {
            ValueKind::MAP => {
                for i in 0..unsafe { map_node_entry_count(sp as *const u8) } {
                    let (key, value) = unsafe { map_slot(sp as *const u8, i) };
                    self.slot(key);
                    self.slot(value);
                }
                for i in 0..unsafe { map_node_child_count(sp as *const u8) } {
                    let child = unsafe { map_node_child(sp as *const u8, i) };
                    self.slot(AnyValue::heap_ptr(child, ValueKind::MAP));
                }
            }
            ValueKind::CLOSURE => {
                for i in 0..unsafe { closure_captured_count(sp as *const u8) } {
                    self.slot(unsafe { closure_capture_value(sp as *const u8, i) });
                }
            }
            ValueKind::STRUCT => {
                let schema_id = unsafe { struct_schema_id(sp as *const u8) };
                let registry = self.src_heap.schemas.borrow();
                for (field, _) in registry.get(schema_id).any_value_fields_with_kind_offsets() {
                    self.slot(self.src_heap.read_field_slot(sp, field.offset));
                }
            }
            _ => {}
        }
    }

    /// A list is walked along its spine, like the copy: it stops at the empty
    /// list.
    fn list(&mut self, first: *mut u8) {
        let mut cell = first;
        while !cell.is_null() {
            self.bytes += size_of::<ListCons>();
            let cons = unsafe { &*(cell as *const ListCons) };
            self.slot(cons.head_value());
            cell = cons.tail_addr() as *mut u8;
            if !cell.is_null() {
                self.src_heap.assert_classified(cell, false);
            }
        }
    }
}

pub fn deep_copy_any_value_ref(value: AnyValueRef, src_heap: &HeapView, dst_heap: &mut Heap) -> AnyValueRef {
    if value.is_empty_list() {
        return value;
    }
    match value.tag() {
        ValueKind::NULL => value,
        tag if tag.is_immediate() => value,
        tag if tag.is_boxed_scalar() => {
            let src = value.storage_addr();
            let dst = dst_heap.alloc_kind(HeapAllocKind::ScalarBox, 8);
            unsafe {
                write(dst as *mut u64, read(src as *const u64));
            }
            AnyValueRef::from_scalar_slot(tag, dst as *const u64).expect("deep-copied scalar ref")
        }
        tag if tag.is_heap() => {
            let src = AnyValue::from_ref(value).expect("heap ref value");
            deep_copy_any_value(src, src_heap, dst_heap).ref_word()
        }
        _ => unreachable!("AnyValueRef tag set is exhaustive"),
    }
}

/// A copy of the map node at `sp` in `dst_heap`, with its entries and children
/// copied. The copy has the node's header, so a trie node
/// keeps its bitmaps and a flat map its count.
fn deep_copy_map_node(sp: *mut u8, src_heap: &HeapView, dst_heap: &mut Heap) -> u64 {
    let node = sp as *const u8;
    let mut copy = |value: AnyValue| {
        if value.kind().is_heap() {
            deep_copy_any_value(value, src_heap, dst_heap)
        } else {
            value
        }
    };
    let entries: SmallVec<[(AnyValue, AnyValue); 8]> = (0..unsafe { map_node_entry_count(node) })
        .map(|slot| {
            let (key, value) = unsafe { map_slot(node, slot) };
            (copy(key), copy(value))
        })
        .collect();
    let children: SmallVec<[*mut u8; 8]> = (0..unsafe { map_node_child_count(node) })
        .map(|index| {
            let child = AnyValue::heap_ptr(unsafe { map_node_child(node, index) }, ValueKind::MAP);
            copy(child).heap_addr().expect("a copied child node")
        })
        .collect();
    let header = unsafe { std::ptr::read(node as *const u64) };
    heap_object_word(dst_heap.alloc_map_node(header, &entries, &children), ValueKind::MAP)
}

pub fn deep_copy_any_value(src: AnyValue, src_heap: &HeapView, dst_heap: &mut Heap) -> AnyValue {
    let Some(sp) = src.heap_addr() else {
        return src;
    };
    if sp.is_null() || src_heap.shares(src) {
        return src;
    }

    match src.kind() {
        ValueKind::MAP => {
            let new_bits = deep_copy_map_node(sp, src_heap, dst_heap);
            let new_p = map_addr_from_tagged(new_bits).expect("new map ptr");
            AnyValue::heap_ptr(new_p, ValueKind::MAP)
        }
        ValueKind::LIST => deep_copy_list(sp, src_heap, dst_heap),
        ValueKind::CLOSURE => deep_copy_strict_closure(sp, src_heap, dst_heap),
        ValueKind::STRUCT => deep_copy_strict_struct(sp, src_heap, dst_heap),
        ValueKind::BITSTRING => {
            let bit_len = unsafe { bitstring_bit_len(sp as *const u8) };
            let bytes_len = (bit_len as usize).div_ceil(8);
            let bytes = unsafe { from_raw_parts(bitstring_bytes_ptr(sp as *const u8), bytes_len) };
            // The copy classifies itself: an inline bitstring stays inline
            // because it is under the threshold by construction, but nothing
            // here has to know that.
            dst_heap.alloc_bitstring(bytes, bit_len)
        }
        ValueKind::BINVIEW => {
            let src_view = unsafe { BinView::from_raw(sp) };
            // The copy belongs to another heap, possibly another process: from
            // here on no one may append into the buffer both of them view.
            unsafe { shared_bin_freeze(src_view.shared_raw()) };
            // The destination heap holds its own reference to the buffer, one
            // BinRef for each view copied, and the copy views the same window
            // of the same bytes.
            let handle = unsafe { SharedBinHandle::retain_from_raw(src_view.shared_raw()) };
            let binref = alloc_binref(dst_heap, handle, StubSite::MessageCopy);
            let new_p = alloc_view(
                dst_heap,
                binref,
                src_view.bytes_ptr(),
                src_view.bit_len(),
                StubSite::MessageCopy,
            )
            .as_raw();
            AnyValue::heap_ptr(new_p, ValueKind::BINVIEW)
        }
        ValueKind::RESOURCE => {
            let src_rs = unsafe { ResourceStub::from_raw(sp) };
            let handle = unsafe { ResourceHandle::retain_from_raw(src_rs.shared_raw()) };
            let new_p = alloc_resource(dst_heap, handle).as_raw();
            AnyValue::heap_ptr(new_p, ValueKind::RESOURCE)
        }
        _ => src,
    }
}

/// Copy a list cell by cell along its spine, so a long list costs stack for
/// its deepest head, not for its length.
fn deep_copy_list(sp: *mut u8, src_heap: &HeapView, dst_heap: &mut Heap) -> AnyValue {
    let first = copy_list_cell(sp, src_heap, dst_heap);
    let mut prev = first;
    let mut cur = unsafe { &*(sp as *const ListCons) }.tail_addr() as *mut u8;
    while !cur.is_null() {
        let next = copy_list_cell(cur, src_heap, dst_heap);
        let next_bits = AnyValue::heap_ptr(next.0, ValueKind::LIST)
            .heap_object_word()
            .expect("copied list tail");
        link_list_tail(dst_heap, prev.0, prev.1, next_bits);
        prev = next;
        cur = unsafe { &*(cur as *const ListCons) }.tail_addr() as *mut u8;
    }
    link_list_tail(dst_heap, prev.0, prev.1, EMPTY_LIST);
    AnyValue::heap_ptr(first.0, ValueKind::LIST)
}

/// Allocate the copy of one cell and copy its head.
/// The tail is written by `link_list_tail` once the caller knows it.
fn copy_list_cell(sp: *mut u8, src_heap: &HeapView, dst_heap: &mut Heap) -> (*mut u8, AnyValue) {
    let bits = dst_heap.alloc_list_cons_slot(AnyValue::nil_atom(), EMPTY_LIST);
    let dp = list_addr_from_tagged(bits).expect("new list ptr");
    let cons = unsafe { &*(sp as *const ListCons) };
    let new_head = if cons.head_kind().is_heap() {
        deep_copy_any_value(cons.head_value(), src_heap, dst_heap)
    } else {
        cons.head_value()
    };
    dst_heap.publish_contained_parts(new_head.raw(), new_head.kind());
    (dp, new_head)
}

/// Write the finished cell at `dp`. A cell copied into a gift window is shared
/// from birth: the receiver grafts the gift as old data, and an old cell is
/// never rewritten in place.
fn link_list_tail(dst_heap: &Heap, dp: *mut u8, head: AnyValue, tail_bits: u64) {
    let mut cons = ListCons::new(head.raw(), head.kind(), tail_bits);
    if dst_heap.gift_window_is_open() {
        cons.keep_across_collection();
    }
    unsafe {
        write(dp as *mut ListCons, cons);
    }
}

fn deep_copy_strict_closure(sp: *mut u8, src_heap: &HeapView, dst_heap: &mut Heap) -> AnyValue {
    let captured_count = unsafe { closure_captured_count(sp as *const u8) };
    let halt_kind = unsafe { closure_halt_kind(sp as *const u8) };
    let fn_ptr = unsafe { closure_fn_ptr(sp as *const u8) };
    let arity = unsafe { closure_arity(sp as *const u8) };
    let denotation = unsafe { crate::any_value::closure_denotation(sp) };
    let new_bits = dst_heap.alloc_closure_slots(denotation, arity, captured_count, halt_kind);
    let dp = closure_addr_from_tagged(new_bits).expect("new closure ptr");
    unsafe { write(dp.add(8) as *mut u64, fn_ptr) };
    for i in 0..captured_count {
        let cv = unsafe { closure_capture_value(sp as *const u8, i) };
        let copied = if cv.kind().is_heap() {
            deep_copy_any_value(cv, src_heap, dst_heap)
        } else {
            cv
        };
        dst_heap.publish_contained_parts(copied.raw(), copied.kind());
        unsafe { closure_capture_set(dp as *const u8, i, copied) };
    }
    AnyValue::heap_ptr(dp, ValueKind::CLOSURE)
}

fn deep_copy_strict_struct(sp: *mut u8, src_heap: &HeapView, dst_heap: &mut Heap) -> AnyValue {
    let schema_id = unsafe { struct_schema_id(sp as *const u8) };
    let dp = dst_heap.alloc_struct(schema_id);
    // A struct copied into a gift window is shared from birth: the receiver
    // grafts the gift as old data, and old data is never written in place.
    if dst_heap.gift_window_is_open() {
        unsafe { share_struct(dp) };
    }
    let registry = src_heap.schemas.borrow();
    let schema = registry.get(schema_id);
    for (f, _) in schema.any_value_fields_with_kind_offsets() {
        let child = src_heap.read_field_slot(sp, f.offset);
        let copied = if child.kind().is_heap() {
            deep_copy_any_value(child, src_heap, dst_heap)
        } else {
            child
        };
        dst_heap.publish_contained_parts(copied.raw(), copied.kind());
        unsafe { dst_heap.write_field_slot(dp, f.offset, copied) };
    }
    for f in &schema.fields {
        match f.kind {
            FieldKind::AnyValue => {}
            FieldKind::RawF64 | FieldKind::RawI64 | FieldKind::RawBytes(_) => unsafe {
                let width = match f.kind {
                    FieldKind::RawBytes(n) => n as usize,
                    _ => 8,
                };
                copy_nonoverlapping(sp.add(8 + f.offset as usize), dp.add(8 + f.offset as usize), width);
            },
        }
    }
    AnyValue::heap_ptr(dp, ValueKind::STRUCT)
}

pub fn deep_copy_slot(src: AnyValue, src_heap: &HeapView, dst_heap: &mut Heap) -> AnyValue {
    deep_copy_any_value(src, src_heap, dst_heap)
}
