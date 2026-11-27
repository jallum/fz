//! Cheney tracing: scan each copied object and forward its child edges.

use super::forward::Tracer;
use crate::any_value::{
    ListCons, StructName, ValueKind, closure_capture_raw_kind, closure_capture_raw_slot, closure_captured_count,
    map_key_kind, map_keys_ptr, map_node_child_count, map_node_children_ptr, map_node_entry_count, map_tag_ptr,
    map_value_kind, map_values_ptr, struct_field_kind_slot, struct_field_raw_slot, struct_is_named, struct_schema_id,
};
use crate::bits::BinView;
use std::ptr::read;

impl Tracer<'_> {
    /// Scan every object the collection has copied, in copy order, forwarding
    /// what each one references, until the scan catches up with the copy
    /// frontier. The roots are forwarded first, so this runs once.
    pub(in super::super) fn scan(&mut self) {
        let mut scanned = 0;
        while let Some(&copied) = self.worklist.get(scanned) {
            scanned += 1;
            match copied.kind {
                ValueKind::LIST => self.trace_list(copied.ptr as *mut ListCons),
                ValueKind::MAP => self.trace_map(copied.ptr),
                ValueKind::CLOSURE => self.trace_closure(copied.ptr),
                ValueKind::STRUCT => self.trace_struct(copied.ptr),
                ValueKind::BINVIEW => self.trace_binview(copied.ptr),
                // These hold no heap edge for the scan to forward.
                ValueKind::BITSTRING | ValueKind::BINREF | ValueKind::RESOURCE => {}
                kind => panic!("Cheney scan: invalid copied object kind {kind:?}"),
            }
        }
    }

    #[inline]
    fn trace_list(&mut self, obj: *mut ListCons) {
        let cons = unsafe { &mut *obj };
        unsafe { self.forward_slot(&raw mut cons.head, cons.head_kind()) };
        self.forward_tail(cons);
    }

    #[inline]
    fn trace_struct(&mut self, obj: *mut u8) {
        let schema_id = unsafe { struct_schema_id(obj as *const u8) };
        let schemas = self.schemas;
        debug_assert_eq!(
            unsafe { struct_is_named(obj as *const u8) },
            schemas.get(schema_id).struct_name() == StructName::Named,
            "a struct's named bit is its schema's"
        );
        for (field, kind_offset) in schemas.get(schema_id).any_value_fields_with_kind_offsets() {
            let kind_slot = unsafe { struct_field_kind_slot(obj as *const u8, kind_offset) };
            let kind = ValueKind::new(unsafe { read(kind_slot) }).expect("struct field kind");
            unsafe { self.forward_slot(struct_field_raw_slot(obj as *const u8, field.offset), kind) };
        }
    }

    /// A view's one child edge is its BinRef. Forwarding it copies the BinRef
    /// the first time any view reaches it, and every later view of that buffer
    /// in the same heap finds it already forwarded, so each live BinRef is
    /// copied once. A BinRef an earlier collection kept is not in from-space
    /// and stays where it is.
    #[inline]
    fn trace_binview(&mut self, obj: *mut u8) {
        let view = unsafe { BinView::from_raw(obj) };
        view.binref_word_set(self.forward(view.binref_word(), ValueKind::BINREF));
    }

    #[inline]
    fn trace_map(&mut self, obj: *mut u8) {
        let count = unsafe { map_node_entry_count(obj as *const u8) };
        let tags = unsafe { map_tag_ptr(obj as *const u8) };
        let keys = unsafe { map_keys_ptr(obj as *const u8, count) };
        let values = unsafe { map_values_ptr(obj as *const u8, count) };
        for i in 0..count {
            let tag = unsafe { read(tags.add(i)) };
            unsafe {
                self.forward_slot(keys.add(i), map_key_kind(tag));
                self.forward_slot(values.add(i), map_value_kind(tag));
            }
        }
        let children = unsafe { map_node_children_ptr(obj as *const u8) };
        for i in 0..unsafe { map_node_child_count(obj as *const u8) } {
            unsafe { self.forward_slot(children.add(i), ValueKind::MAP) };
        }
    }

    #[inline]
    fn trace_closure(&mut self, obj: *mut u8) {
        for idx in 0..unsafe { closure_captured_count(obj as *const u8) } {
            let (_, kind) = unsafe { closure_capture_raw_kind(obj as *const u8, idx) };
            unsafe { self.forward_slot(closure_capture_raw_slot(obj as *const u8, idx), kind) };
        }
    }
}
