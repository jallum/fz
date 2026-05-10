//! Heap with mark-sweep GC and schema-driven generic tracer.
//!
//! Single contiguous 16-aligned region (raw alloc/dealloc; non-moving).
//! Live allocations tracked in `allocs` — sweep filters them and pushes freed
//! ranges to `freelist`. Free blocks have `kind = FREE_KIND` written into the
//! header for debug visibility (and to make a future linear-walk sweep easy).
//!
//! Roots come from explicit `gc(roots: &[FzValue])`. Real root sets land with
//! CPS codegen in fz-ul4.11.9.

#![allow(dead_code)]

use crate::fz_value::{FzValue, HeapHeader, HeapKind, ListCons};
use std::alloc::{Layout, alloc_zeroed, dealloc};
use std::cell::RefCell;
use std::collections::HashSet;
use std::rc::Rc;

/// Sentinel kind written into freed objects' headers. Outside HeapKind's valid
/// range (0..=7). Used for debug visibility and to support a future linear-walk
/// sweep variant.
pub const FREE_KIND: u16 = 0xFFFF;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FieldKind {
    FzValue,
    RawBytes(u32),
}

#[derive(Debug, Clone)]
pub struct FieldDescriptor {
    pub offset: u32,
    pub kind: FieldKind,
}

#[derive(Debug, Clone)]
pub struct Schema {
    pub name: String,
    pub size: u32,
    pub fields: Vec<FieldDescriptor>,
}

pub struct SchemaRegistry {
    schemas: Vec<Schema>,
}

impl SchemaRegistry {
    pub fn new() -> Self {
        Self { schemas: Vec::new() }
    }

    pub fn register(&mut self, schema: Schema) -> u32 {
        let id = self.schemas.len() as u32;
        self.schemas.push(schema);
        id
    }

    pub fn get(&self, id: u32) -> &Schema {
        &self.schemas[id as usize]
    }

    pub fn len(&self) -> usize {
        self.schemas.len()
    }
}

impl Default for SchemaRegistry {
    fn default() -> Self {
        Self::new()
    }
}

pub struct Heap {
    base: *mut u8,
    capacity: usize,
    bump: usize,
    freelist: Vec<(usize, usize)>,
    allocs: Vec<usize>,
    schemas: Rc<RefCell<SchemaRegistry>>,
}

impl Heap {
    pub fn new(capacity: usize, schemas: Rc<RefCell<SchemaRegistry>>) -> Self {
        assert!(capacity > 0 && capacity % 16 == 0, "capacity must be 16-aligned");
        let layout = Layout::from_size_align(capacity, 16).expect("bad heap layout");
        let base = unsafe { alloc_zeroed(layout) };
        assert!(!base.is_null(), "heap allocation failed");
        Self {
            base,
            capacity,
            bump: 0,
            freelist: Vec::new(),
            allocs: Vec::new(),
            schemas,
        }
    }

    /// Allocate `size` bytes, rounded up to 16. Returns a pointer suitable for
    /// writing a HeapHeader. Caller must initialize the header.
    pub fn alloc(&mut self, size: usize) -> *mut HeapHeader {
        let size = (size + 15) & !15;
        assert!(size >= 16, "alloc must include at least the 16-byte header");
        // First-fit on freelist.
        for i in 0..self.freelist.len() {
            let (off, fsz) = self.freelist[i];
            if fsz >= size {
                self.freelist.remove(i);
                if fsz > size {
                    self.freelist.push((off + size, fsz - size));
                }
                self.allocs.push(off);
                return unsafe { self.base.add(off) as *mut HeapHeader };
            }
        }
        if self.bump + size > self.capacity {
            panic!(
                "out of heap (capacity={}, bump={}, requested={})",
                self.capacity, self.bump, size
            );
        }
        let off = self.bump;
        self.bump += size;
        self.allocs.push(off);
        unsafe { self.base.add(off) as *mut HeapHeader }
    }

    pub fn alloc_struct(&mut self, schema_id: u32) -> *mut HeapHeader {
        let payload_size = self.schemas.borrow().get(schema_id).size as usize;
        let total = (16 + payload_size + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Struct as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id,
                    _reserved: 0,
                },
            );
            // Zero payload.
            std::ptr::write_bytes((p as *mut u8).add(16), 0, total - 16);
        }
        p
    }

    pub fn alloc_list_cons(&mut self, head: FzValue, tail: FzValue) -> *mut HeapHeader {
        let p = self.alloc(32);
        unsafe {
            std::ptr::write(
                p as *mut ListCons,
                ListCons {
                    header: HeapHeader {
                        kind: HeapKind::List as u16,
                        flags: 0,
                        size_bytes: 32,
                        schema_id: 0,
                        _reserved: 0,
                    },
                    head,
                    tail,
                },
            );
        }
        p
    }

    /// Map layout: HeapHeader (16) + entry_count: u64 (8) + entries
    /// [(key: FzValue (8), val: FzValue (8)); N]. Caller supplies a
    /// canonically-sorted entry slice; this performs the heap copy.
    pub fn alloc_map(&mut self, entries: &[(FzValue, FzValue)]) -> *mut HeapHeader {
        let total = (16 + 8 + entries.len() * 16 + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Map as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            let count_p = (p as *mut u8).add(16) as *mut u64;
            std::ptr::write(count_p, entries.len() as u64);
            let mut cursor = (p as *mut u8).add(24) as *mut FzValue;
            for (k, v) in entries {
                std::ptr::write(cursor, *k);
                cursor = cursor.add(1);
                std::ptr::write(cursor, *v);
                cursor = cursor.add(1);
            }
        }
        p
    }

    /// Bitstring layout: HeapHeader (16) + bit_len: u64 (8) + bytes (padded
    /// to 16). Caller supplies a fully-built byte buffer + bit_len; this
    /// performs the heap copy.
    pub fn alloc_bitstring(&mut self, bytes: &[u8], bit_len: u64) -> *mut HeapHeader {
        let total = (16 + 8 + bytes.len() + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::Bitstring as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            // bit_len at offset 16, then byte payload at offset 24.
            let bit_len_p = (p as *mut u8).add(16) as *mut u64;
            std::ptr::write(bit_len_p, bit_len);
            let bytes_p = (p as *mut u8).add(24);
            std::ptr::copy_nonoverlapping(bytes.as_ptr(), bytes_p, bytes.len());
            // Zero the trailing padding so renders / debug aren't garbage.
            let pad_start = 24 + bytes.len();
            if pad_start < total {
                std::ptr::write_bytes(
                    (p as *mut u8).add(pad_start),
                    0,
                    total - pad_start,
                );
            }
        }
        p
    }

    pub fn alloc_vec_i64(&mut self, len: usize) -> *mut HeapHeader {
        let total = (16 + len * 8 + 15) & !15;
        let p = self.alloc(total);
        unsafe {
            std::ptr::write(
                p,
                HeapHeader {
                    kind: HeapKind::VecI64 as u16,
                    flags: 0,
                    size_bytes: total as u32,
                    schema_id: 0,
                    _reserved: 0,
                },
            );
            std::ptr::write_bytes((p as *mut u8).add(16), 0, total - 16);
        }
        p
    }

    /// Write an FzValue into a Struct's payload at the given field offset.
    pub fn write_field(&self, obj: *mut HeapHeader, field_offset: u32, value: FzValue) {
        unsafe {
            let p = (obj as *mut u8).add(16).add(field_offset as usize) as *mut FzValue;
            std::ptr::write(p, value);
        }
    }

    /// Read an FzValue from a Struct's payload at the given field offset.
    pub fn read_field(&self, obj: *mut HeapHeader, field_offset: u32) -> FzValue {
        unsafe {
            let p = (obj as *mut u8).add(16).add(field_offset as usize) as *const FzValue;
            std::ptr::read(p)
        }
    }

    /// Register a schema in this heap's registry, returning its id. Codegen
    /// uses this to register tuple-arity / closure / record schemas at JIT
    /// compile time so the tracer can walk their FzValue fields.
    pub fn register_schema(&self, schema: Schema) -> u32 {
        self.schemas.borrow_mut().register(schema)
    }

    /// Borrow the SchemaRegistry handle. Used by render paths that need to
    /// know a struct's arity / field layout from its schema_id.
    pub fn schemas_registry(&self) -> Rc<RefCell<SchemaRegistry>> {
        self.schemas.clone()
    }

    pub fn live_count(&self) -> usize {
        self.allocs.len()
    }

    pub fn freelist_len(&self) -> usize {
        self.freelist.len()
    }

    pub fn bytes_used(&self) -> usize {
        self.bump - self.freelist.iter().map(|(_, s)| *s).sum::<usize>()
    }

    pub fn gc(&mut self, roots: &[FzValue]) {
        let mut marked: HashSet<*mut HeapHeader> = HashSet::new();
        {
            let registry = self.schemas.borrow();
            for r in roots {
                trace(*r, &registry, &mut marked);
            }
        }
        let mut new_allocs = Vec::with_capacity(self.allocs.len());
        for &off in &self.allocs {
            let p = unsafe { self.base.add(off) as *mut HeapHeader };
            if marked.contains(&p) {
                new_allocs.push(off);
            } else {
                let size = unsafe { (*p).size_bytes as usize };
                unsafe {
                    (*p).kind = FREE_KIND;
                }
                self.freelist.push((off, size));
            }
        }
        self.allocs = new_allocs;
    }
}

impl Drop for Heap {
    fn drop(&mut self) {
        let layout = Layout::from_size_align(self.capacity, 16).expect("bad heap layout");
        unsafe { dealloc(self.base, layout) };
    }
}

fn trace(v: FzValue, reg: &SchemaRegistry, marked: &mut HashSet<*mut HeapHeader>) {
    let p = match v.unbox_ptr() {
        Some(p) => p,
        None => return,
    };
    if !marked.insert(p) {
        return;
    }
    let h = unsafe { &*p };
    match HeapKind::from_u16(h.kind) {
        Some(HeapKind::Struct) => {
            let schema = reg.get(h.schema_id);
            for f in &schema.fields {
                if let FieldKind::FzValue = f.kind {
                    let child = unsafe {
                        std::ptr::read(
                            (p as *mut u8).add(16).add(f.offset as usize) as *const FzValue,
                        )
                    };
                    trace(child, reg, marked);
                }
            }
        }
        Some(HeapKind::List) => {
            let cons = unsafe { &*(p as *mut ListCons) };
            trace(cons.head, reg, marked);
            trace(cons.tail, reg, marked);
        }
        Some(HeapKind::Bitstring)
        | Some(HeapKind::VecI64)
        | Some(HeapKind::VecF64)
        | Some(HeapKind::VecU8)
        | Some(HeapKind::VecBit) => {
            // Raw payloads: no FzValue children to trace.
        }
        Some(HeapKind::Map) => {
            // Map payload: count: u64 at offset 16, then (key, val) pairs at
            // offset 24, 16 bytes each. Trace both key and val FzValues.
            let count = unsafe {
                std::ptr::read((p as *const u8).add(16) as *const u64) as usize
            };
            let mut cursor = unsafe { (p as *const u8).add(24) as *const FzValue };
            for _ in 0..count {
                let k = unsafe { std::ptr::read(cursor) };
                let v = unsafe { std::ptr::read(cursor.add(1)) };
                cursor = unsafe { cursor.add(2) };
                trace(k, reg, marked);
                trace(v, reg, marked);
            }
        }
        None => {
            // FREE_KIND or unknown: object is not live, must not be reachable.
            panic!(
                "tracer reached object with invalid HeapKind ({:#x}) at {:?}",
                h.kind, p
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_value::FzValue;

    fn empty_registry() -> Rc<RefCell<SchemaRegistry>> {
        Rc::new(RefCell::new(SchemaRegistry::new()))
    }

    fn pair_schema() -> Schema {
        Schema {
            name: "Pair".into(),
            size: 16,
            fields: vec![
                FieldDescriptor { offset: 0, kind: FieldKind::FzValue },
                FieldDescriptor { offset: 8, kind: FieldKind::FzValue },
            ],
        }
    }

    #[test]
    fn schema_registry_register_and_get() {
        let mut reg = SchemaRegistry::new();
        let id_a = reg.register(Schema { name: "A".into(), size: 0, fields: vec![] });
        let id_b = reg.register(pair_schema());
        assert_eq!(id_a, 0);
        assert_eq!(id_b, 1);
        assert_eq!(reg.get(id_a).name, "A");
        assert_eq!(reg.get(id_b).name, "Pair");
    }

    #[test]
    fn alloc_bumps_and_tracks() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        assert!(!p.is_null());
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.bytes_used(), 32);
    }

    #[test]
    fn gc_keeps_rooted_object() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        let v = FzValue::from_ptr(p);
        h.gc(&[v]);
        assert_eq!(h.live_count(), 1);
        assert_eq!(h.freelist_len(), 0);
    }

    #[test]
    fn gc_frees_unrooted_object() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _p = h.alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn gc_traces_through_cons_chain() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        // [1, 2, 3]
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(n3));
        let n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(n2));
        h.gc(&[FzValue::from_ptr(n1)]);
        assert_eq!(h.live_count(), 3);
        assert_eq!(h.freelist_len(), 0);
    }

    #[test]
    fn gc_frees_dropped_tail() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let n3 = h.alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let n2 = h.alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(n3));
        let _n1 = h.alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(n2));
        // Root only n2 → n1 should be freed; n2 and n3 retained.
        h.gc(&[FzValue::from_ptr(n2)]);
        assert_eq!(h.live_count(), 2);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn gc_traces_through_struct_fields() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(pair_schema());
        let mut h = Heap::new(1024, reg.clone());

        let leaf = h.alloc_list_cons(FzValue::from_int(99), FzValue::NIL);
        let parent = h.alloc_struct(pair_id);
        h.write_field(parent, 0, FzValue::from_ptr(leaf));
        h.write_field(parent, 8, FzValue::NIL);

        h.gc(&[FzValue::from_ptr(parent)]);
        assert_eq!(h.live_count(), 2);
    }

    #[test]
    fn gc_frees_struct_and_unique_child_when_root_lost() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(pair_schema());
        let mut h = Heap::new(1024, reg.clone());

        let leaf = h.alloc_list_cons(FzValue::from_int(99), FzValue::NIL);
        let parent = h.alloc_struct(pair_id);
        h.write_field(parent, 0, FzValue::from_ptr(leaf));
        h.write_field(parent, 8, FzValue::NIL);

        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 2);
    }

    #[test]
    fn gc_handles_cycle() {
        let reg = empty_registry();
        let pair_id = reg.borrow_mut().register(pair_schema());
        let mut h = Heap::new(1024, reg.clone());

        let a = h.alloc_struct(pair_id);
        let b = h.alloc_struct(pair_id);
        // a.0 = b, b.0 = a (cycle)
        h.write_field(a, 0, FzValue::from_ptr(b));
        h.write_field(a, 8, FzValue::NIL);
        h.write_field(b, 0, FzValue::from_ptr(a));
        h.write_field(b, 8, FzValue::NIL);

        // Either root keeps both alive.
        h.gc(&[FzValue::from_ptr(a)]);
        assert_eq!(h.live_count(), 2);

        h.gc(&[FzValue::from_ptr(b)]);
        assert_eq!(h.live_count(), 2);

        // No roots → both freed despite cycle.
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 2);
    }

    #[test]
    fn gc_frees_vec_i64_when_unrooted() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _v = h.alloc_vec_i64(8);
        h.gc(&[]);
        assert_eq!(h.live_count(), 0);
        assert_eq!(h.freelist_len(), 1);
    }

    #[test]
    fn alloc_reuses_freelist() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let _a = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let bump_after_first = h.bump;
        h.gc(&[]);
        assert_eq!(h.freelist_len(), 1);
        let _b = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        // Second alloc should reuse the freelist slot, not bump further.
        assert_eq!(h.bump, bump_after_first);
        assert_eq!(h.freelist_len(), 0);
    }

    #[test]
    fn freed_object_kind_is_free_sentinel() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        let p = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        h.gc(&[]);
        unsafe {
            assert_eq!((*p).kind, FREE_KIND);
        }
    }

    #[test]
    fn heap_pointers_are_16_aligned() {
        let reg = empty_registry();
        let mut h = Heap::new(1024, reg);
        for _ in 0..10 {
            let p = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
            assert_eq!((p as usize) & 15, 0);
        }
    }

    #[test]
    #[should_panic(expected = "out of heap")]
    fn alloc_panics_when_oom() {
        let reg = empty_registry();
        let mut h = Heap::new(64, reg);
        // Each cons is 32 bytes; 64 capacity → 2 fit, third should OOM.
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
        let _ = h.alloc_list_cons(FzValue::NIL, FzValue::NIL);
    }
}
