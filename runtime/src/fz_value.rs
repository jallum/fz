//! Tagged FzValue and heap object header.
//!
//! Low-bit tag scheme (3 bits):
//!   0b000 = ptr to heap object (HeapHeader is 16-byte aligned, so low 4 bits are 0)
//!   0b001 = small int (61-bit signed; payload = (n << 3) | 0b001)
//!   0b010 = atom (32-bit interned id; payload = (id << 3) | 0b010)
//!   0b011 = special (nil/true/false/sentinels)
//!   1xx   = reserved (future: boxed float, etc.)

#![allow(dead_code)]

use std::alloc::{Layout, alloc};
use std::ptr;

const TAG_BITS: u64 = 3;
const TAG_MASK: u64 = 0b111;

const TAG_PTR: u64 = 0b000;
const TAG_INT: u64 = 0b001;
const TAG_ATOM: u64 = 0b010;
const TAG_SPECIAL: u64 = 0b011;

const SPECIAL_NIL: u64 = (0 << TAG_BITS) | TAG_SPECIAL;
const SPECIAL_TRUE: u64 = (1 << TAG_BITS) | TAG_SPECIAL;
const SPECIAL_FALSE: u64 = (2 << TAG_BITS) | TAG_SPECIAL;

/// fz-s9y.2 — the empty-list sentinel. TAG_PTR tag (0b000) with payload
/// value 1 (so the full bit pattern is `0x8`). Address 0x8 sits inside
/// page 0, which the OS reserves as unmapped — no allocator ever returns
/// it, so the sentinel can't collide with a real heap pointer.
/// Distinct from `SPECIAL_NIL`: `[]` and `nil` are different values.
pub(crate) const EMPTY_LIST: u64 = 1 << TAG_BITS;

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub enum Tag {
    Ptr,
    Int,
    Atom,
    Special,
    Reserved,
}

#[repr(transparent)]
#[derive(Clone, Copy)]
pub struct FzValue(pub u64);

impl FzValue {
    pub const NIL: FzValue = FzValue(SPECIAL_NIL);
    pub const TRUE: FzValue = FzValue(SPECIAL_TRUE);
    pub const FALSE: FzValue = FzValue(SPECIAL_FALSE);
    /// fz-s9y.2 — the empty list `[]`. Distinct from `NIL`.
    pub const EMPTY_LIST: FzValue = FzValue(EMPTY_LIST);

    pub const fn from_int(n: i64) -> FzValue {
        // Sign-preserving shift left by 3, OR in tag.
        // Caller is responsible for range; debug builds check.
        let bits = ((n as u64) << TAG_BITS) | TAG_INT;
        FzValue(bits)
    }

    pub const fn from_atom_id(id: u32) -> FzValue {
        FzValue(((id as u64) << TAG_BITS) | TAG_ATOM)
    }

    pub fn from_ptr(p: *mut HeapHeader) -> FzValue {
        let bits = p as u64;
        debug_assert!(bits & TAG_MASK == 0, "heap pointer not 8-byte aligned");
        FzValue(bits)
    }

    pub fn tag(self) -> Tag {
        match self.0 & TAG_MASK {
            TAG_PTR => Tag::Ptr,
            TAG_INT => Tag::Int,
            TAG_ATOM => Tag::Atom,
            TAG_SPECIAL => Tag::Special,
            _ => Tag::Reserved,
        }
    }

    pub fn unbox_int(self) -> Option<i64> {
        if self.0 & TAG_MASK == TAG_INT {
            // Arithmetic shift right preserves sign.
            Some((self.0 as i64) >> TAG_BITS)
        } else {
            None
        }
    }

    pub fn unbox_atom(self) -> Option<u32> {
        if self.0 & TAG_MASK == TAG_ATOM {
            Some((self.0 >> TAG_BITS) as u32)
        } else {
            None
        }
    }

    pub fn unbox_ptr(self) -> Option<*mut HeapHeader> {
        if self.0 == SPECIAL_NIL || self.0 == SPECIAL_TRUE || self.0 == SPECIAL_FALSE {
            return None;
        }
        if self.0 == EMPTY_LIST {
            // fz-s9y.2 — the empty list is TAG_PTR-tagged but its "pointer"
            // is a sentinel into unmapped memory. Do not dereference.
            return None;
        }
        if self.0 & TAG_MASK == TAG_PTR {
            Some(self.0 as *mut HeapHeader)
        } else {
            None
        }
    }

    pub fn is_nil(self) -> bool {
        self.0 == SPECIAL_NIL
    }
    pub fn is_empty_list(self) -> bool {
        self.0 == EMPTY_LIST
    }
    pub fn is_true(self) -> bool {
        self.0 == SPECIAL_TRUE
    }
    pub fn is_false(self) -> bool {
        self.0 == SPECIAL_FALSE
    }

    /// Range of valid 61-bit signed ints.
    pub const INT_MIN: i64 = -(1 << 60);
    pub const INT_MAX: i64 = (1 << 60) - 1;
}

impl std::fmt::Debug for FzValue {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self.tag() {
            Tag::Int => write!(f, "FzValue::Int({})", self.unbox_int().unwrap()),
            Tag::Atom => write!(f, "FzValue::Atom({})", self.unbox_atom().unwrap()),
            Tag::Special if self.is_nil() => write!(f, "FzValue::Nil"),
            Tag::Special if self.is_true() => write!(f, "FzValue::True"),
            Tag::Special if self.is_false() => write!(f, "FzValue::False"),
            Tag::Special => write!(f, "FzValue::Special({:#x})", self.0),
            Tag::Ptr if self.is_empty_list() => write!(f, "FzValue::EmptyList"),
            Tag::Ptr => write!(f, "FzValue::Ptr({:#x})", self.0),
            Tag::Reserved => write!(f, "FzValue::Reserved({:#x})", self.0),
        }
    }
}

#[repr(u16)]
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum HeapKind {
    Struct = 0,
    List = 1,
    Bitstring = 2,
    VecI64 = 3,
    VecF64 = 4,
    VecU8 = 5,
    VecBit = 6,
    Map = 7,
    Closure = 8,
    Float = 9,
    /// fz-cty.3 — 32-byte stub on a per-process heap that references an
    /// off-heap `SharedBin`. Cheney trace is a no-op; the per-heap MSO
    /// list governs retain/release across GC.
    ProcBin = 10,
}

impl HeapKind {
    pub fn from_u16(v: u16) -> Option<HeapKind> {
        match v {
            0 => Some(HeapKind::Struct),
            1 => Some(HeapKind::List),
            2 => Some(HeapKind::Bitstring),
            3 => Some(HeapKind::VecI64),
            4 => Some(HeapKind::VecF64),
            5 => Some(HeapKind::VecU8),
            6 => Some(HeapKind::VecBit),
            7 => Some(HeapKind::Map),
            8 => Some(HeapKind::Closure),
            9 => Some(HeapKind::Float),
            10 => Some(HeapKind::ProcBin),
            _ => None,
        }
    }
}

// Bitstring storage dispatchers moved to `crate::procbin` in fz-q8d.1.
// `fz_value.rs` does not own bitstring layout; render uses the procbin
// helpers like every other read site.

/// Heap object header — exactly 16 bytes, 16-byte aligned.
///
/// Every heap object starts with this header; payload follows immediately.
/// `flags` holds GC mark bit, region tag, etc. (defined in .11.2).
#[repr(C, align(16))]
#[derive(Debug, Clone, Copy)]
pub struct HeapHeader {
    pub kind: u16,
    pub flags: u16,
    pub size_bytes: u32,
    pub schema_id: u32,
    pub _reserved: u32,
}

const _: () = {
    assert!(std::mem::size_of::<HeapHeader>() == 16);
    assert!(std::mem::align_of::<HeapHeader>() == 16);
};

// fz-ul4.27.22.6 — closure `flags` packing. Low 14 bits hold captured_count;
// high 2 bits hold halt_kind (0=Tagged, 1=RawInt, 2=RawF64). The split keeps
// the field in the GC-safe region of the header (offset 2; forwarding
// pointers clobber offsets 8..16). 14 bits = 16K captures, far above any
// realistic program.
pub const CLOSURE_FLAGS_CAPTURED_MASK: u16 = 0x3FFF;
pub const CLOSURE_FLAGS_HALT_KIND_SHIFT: u16 = 14;

#[inline]
pub fn closure_flags_pack(captured_count: u16, halt_kind: u16) -> u16 {
    debug_assert!(
        captured_count <= CLOSURE_FLAGS_CAPTURED_MASK,
        "closure captured count {} exceeds 14-bit capacity",
        captured_count
    );
    debug_assert!(
        halt_kind <= 0b11,
        "closure halt_kind {} out of range",
        halt_kind
    );
    (captured_count & CLOSURE_FLAGS_CAPTURED_MASK) | (halt_kind << CLOSURE_FLAGS_HALT_KIND_SHIFT)
}

#[inline]
pub fn closure_flags_captured(flags: u16) -> u16 {
    flags & CLOSURE_FLAGS_CAPTURED_MASK
}

#[inline]
pub fn closure_flags_halt_kind(flags: u16) -> u16 {
    flags >> CLOSURE_FLAGS_HALT_KIND_SHIFT
}

/// Allocator stubs for v1. These leak — real GC-managed allocator lands in .11.2.
///
/// All allocations are 16-byte aligned (matches HeapHeader alignment).
unsafe fn raw_alloc(total_size: usize) -> *mut HeapHeader {
    let layout = Layout::from_size_align(total_size, 16).expect("bad layout");
    let p = unsafe { alloc(layout) } as *mut HeapHeader;
    assert!(!p.is_null(), "allocation failed");
    p
}

pub fn alloc_struct(schema_id: u32, payload_size: u32) -> *mut HeapHeader {
    let total = 16 + payload_size as usize;
    // Round up to 16 for alignment of subsequent objects.
    let total = (total + 15) & !15;
    unsafe {
        let p = raw_alloc(total);
        ptr::write(
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
        let payload = (p as *mut u8).add(16);
        ptr::write_bytes(payload, 0, total - 16);
        p
    }
}

/// List cons cell: header (16) + head (8) + tail (8) = 32 bytes.
#[repr(C)]
pub struct ListCons {
    pub header: HeapHeader,
    pub head: FzValue,
    pub tail: FzValue,
}

pub fn alloc_list_cons(head: FzValue, tail: FzValue) -> *mut HeapHeader {
    unsafe {
        let p = raw_alloc(32) as *mut ListCons;
        ptr::write(
            p,
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
        p as *mut HeapHeader
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn header_is_16_bytes() {
        assert_eq!(std::mem::size_of::<HeapHeader>(), 16);
        assert_eq!(std::mem::align_of::<HeapHeader>(), 16);
    }

    #[test]
    fn int_round_trip_zero() {
        assert_eq!(FzValue::from_int(0).unbox_int(), Some(0));
    }

    #[test]
    fn int_round_trip_positive() {
        assert_eq!(FzValue::from_int(42).unbox_int(), Some(42));
        assert_eq!(FzValue::from_int(1_000_000).unbox_int(), Some(1_000_000));
    }

    #[test]
    fn int_round_trip_negative() {
        assert_eq!(FzValue::from_int(-1).unbox_int(), Some(-1));
        assert_eq!(FzValue::from_int(-42).unbox_int(), Some(-42));
        assert_eq!(FzValue::from_int(-1_000_000).unbox_int(), Some(-1_000_000));
    }

    #[test]
    fn int_round_trip_extremes() {
        assert_eq!(
            FzValue::from_int(FzValue::INT_MAX).unbox_int(),
            Some(FzValue::INT_MAX)
        );
        assert_eq!(
            FzValue::from_int(FzValue::INT_MIN).unbox_int(),
            Some(FzValue::INT_MIN)
        );
    }

    #[test]
    fn int_tag() {
        assert_eq!(FzValue::from_int(7).tag(), Tag::Int);
        assert_eq!(FzValue::from_int(-7).tag(), Tag::Int);
    }

    #[test]
    fn atom_round_trip() {
        for id in [0u32, 1, 42, 1234, u32::MAX] {
            let v = FzValue::from_atom_id(id);
            assert_eq!(v.tag(), Tag::Atom);
            assert_eq!(v.unbox_atom(), Some(id));
        }
    }

    #[test]
    fn nil_true_false_distinct() {
        let n = FzValue::NIL;
        let t = FzValue::TRUE;
        let f = FzValue::FALSE;
        assert!(n.is_nil() && !n.is_true() && !n.is_false());
        assert!(!t.is_nil() && t.is_true() && !t.is_false());
        assert!(!f.is_nil() && !f.is_true() && f.is_false());
        assert_eq!(n.tag(), Tag::Special);
        assert_eq!(t.tag(), Tag::Special);
        assert_eq!(f.tag(), Tag::Special);
        assert_ne!(n.0, t.0);
        assert_ne!(n.0, f.0);
        assert_ne!(t.0, f.0);
    }

    #[test]
    fn int_does_not_unbox_as_atom_or_ptr() {
        let v = FzValue::from_int(42);
        assert_eq!(v.unbox_atom(), None);
        assert_eq!(v.unbox_ptr(), None);
    }

    #[test]
    fn nil_does_not_unbox_as_ptr() {
        assert_eq!(FzValue::NIL.unbox_ptr(), None);
        assert_eq!(FzValue::TRUE.unbox_ptr(), None);
        assert_eq!(FzValue::FALSE.unbox_ptr(), None);
    }

    #[test]
    fn ptr_round_trip() {
        let p = alloc_list_cons(FzValue::from_int(1), FzValue::NIL);
        let v = FzValue::from_ptr(p);
        assert_eq!(v.tag(), Tag::Ptr);
        assert_eq!(v.unbox_ptr(), Some(p));
        assert_eq!(v.unbox_int(), None);
        assert_eq!(v.unbox_atom(), None);
    }

    #[test]
    fn list_cons_header() {
        let p = alloc_list_cons(FzValue::from_int(7), FzValue::NIL);
        unsafe {
            let h = &*p;
            assert_eq!(h.kind, HeapKind::List as u16);
            assert_eq!(h.size_bytes, 32);
            assert_eq!(h.schema_id, 0);
            let cons = &*(p as *mut ListCons);
            assert_eq!(cons.head.unbox_int(), Some(7));
            assert!(cons.tail.is_nil());
        }
    }

    #[test]
    fn list_cons_chain() {
        // [1, 2, 3]
        let l3 = alloc_list_cons(FzValue::from_int(3), FzValue::NIL);
        let l2 = alloc_list_cons(FzValue::from_int(2), FzValue::from_ptr(l3));
        let l1 = alloc_list_cons(FzValue::from_int(1), FzValue::from_ptr(l2));
        unsafe {
            let c1 = &*(l1 as *mut ListCons);
            assert_eq!(c1.head.unbox_int(), Some(1));
            let c2 = &*(c1.tail.unbox_ptr().unwrap() as *mut ListCons);
            assert_eq!(c2.head.unbox_int(), Some(2));
            let c3 = &*(c2.tail.unbox_ptr().unwrap() as *mut ListCons);
            assert_eq!(c3.head.unbox_int(), Some(3));
            assert!(c3.tail.is_nil());
        }
    }

    #[test]
    fn alloc_struct_zeros_payload_and_sets_header() {
        let p = alloc_struct(7, 24);
        unsafe {
            let h = &*p;
            assert_eq!(h.kind, HeapKind::Struct as u16);
            assert_eq!(h.schema_id, 7);
            // 16 header + 24 payload, rounded up to 16 → 48.
            assert_eq!(h.size_bytes, 48);
            let payload = (p as *mut u8).add(16);
            for i in 0..24 {
                assert_eq!(*payload.add(i), 0);
            }
        }
    }

    #[test]
    fn heap_kind_round_trip() {
        for k in [
            HeapKind::Struct,
            HeapKind::List,
            HeapKind::Bitstring,
            HeapKind::VecI64,
            HeapKind::VecF64,
            HeapKind::VecU8,
            HeapKind::VecBit,
            HeapKind::Map,
            HeapKind::Closure,
            HeapKind::Float,
            HeapKind::ProcBin,
        ] {
            assert_eq!(HeapKind::from_u16(k as u16), Some(k));
        }
        assert_eq!(HeapKind::from_u16(99), None);
    }

    #[test]
    fn pointer_alignment_satisfies_tag_zero_low_bits() {
        let p = alloc_list_cons(FzValue::NIL, FzValue::NIL);
        assert_eq!((p as u64) & TAG_MASK, 0);
    }
}

/// Debug rendering of FzValues. Lifted out of ir_codegen.rs by
/// fz-ul4.23.4.3 so that any execution path (JIT, future interp/AOT) can
/// use the same rendering — values are uniformly tagged, regardless of
/// what produced them. The single runtime dependency is the heap's
/// schema registry on the current Process, accessed via
/// `crate::process::current_process()`.
pub mod debug {
    use super::{FzValue, HeapKind, ListCons, Tag};
    use crate::process::{CURRENT_PROCESS, current_process};

    /// Render an atom id as `:name` if the current Process has a name
    /// for it; fall back to `:atom_N` otherwise. The fallback fires when
    /// render is called without a Process installed (e.g. unit tests
    /// poking the renderer directly) or when an id is outside the
    /// module's table (defensive — shouldn't happen in practice).
    fn render_atom(id: u32) -> String {
        let proc_ptr = CURRENT_PROCESS.with(|c| c.get());
        if proc_ptr.is_null() {
            return format!(":atom_{}", id);
        }
        let names = unsafe { &(*proc_ptr).atom_names };
        match names.get(id as usize) {
            Some(name) if !name.is_empty() => format!(":{}", name),
            _ => format!(":atom_{}", id),
        }
    }

    pub fn render(bits: u64) -> String {
        let v = FzValue(bits);
        match v.tag() {
            Tag::Int => v.unbox_int().unwrap().to_string(),
            Tag::Atom => render_atom(v.unbox_atom().unwrap()),
            Tag::Special => {
                if v.is_nil() {
                    "nil".into()
                } else if v.is_true() {
                    "true".into()
                } else if v.is_false() {
                    "false".into()
                } else {
                    format!("#special<{:#x}>", bits)
                }
            }
            Tag::Ptr => {
                // fz-s9y.2 — the empty list `[]` is TAG_PTR-tagged but its
                // "pointer" is the EMPTY_LIST sentinel pointing into unmapped
                // memory. Detect before any dereference.
                if v.is_empty_list() {
                    return "[]".into();
                }
                let p = v.unbox_ptr().unwrap();
                let kind = unsafe { (*p).kind };
                match HeapKind::from_u16(kind) {
                    Some(HeapKind::List) => render_list(bits),
                    Some(HeapKind::Struct) => render_struct(bits),
                    Some(HeapKind::Bitstring) | Some(HeapKind::ProcBin) => render_bitstring(bits),
                    Some(HeapKind::Map) => render_map(bits),
                    Some(HeapKind::Closure) => render_closure(bits),
                    Some(HeapKind::Float) => render_float(bits),
                    Some(HeapKind::VecI64) => render_vec_i64(bits),
                    Some(HeapKind::VecU8) => render_vec_u8(bits),
                    Some(HeapKind::VecBit) => render_vec_bit(bits),
                    _ => format!("#ptr<{:#x}>", bits),
                }
            }
            Tag::Reserved => format!("#reserved<{:#x}>", bits),
        }
    }

    /// Render a heap-typed Struct (currently only emitted for tuples). Reads
    /// the schema from the current Process's SchemaRegistry to determine
    /// field count. Each FzValue field renders inline; non-FzValue fields
    /// are elided (no callers emit them yet).
    fn render_struct(bits: u64) -> String {
        let v = FzValue(bits);
        let p = v.unbox_ptr().unwrap();
        let schema_id = unsafe { (*p).schema_id };
        let parts: Vec<String> = {
            let reg = current_process().heap.schemas_registry();
            let registry = reg.borrow();
            let schema = registry.get(schema_id);
            schema
                .fields
                .iter()
                .filter(|f| matches!(f.kind, crate::heap::FieldKind::FzValue))
                .map(|f| {
                    let field_bits = unsafe {
                        std::ptr::read((p as *const u8).add(16 + f.offset as usize) as *const u64)
                    };
                    render(field_bits)
                })
                .collect()
        };
        format!("{{{}}}", parts.join(", "))
    }

    /// Render a heap Map as `%{k => v, ...}` in canonical sorted order.
    fn render_map(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let count = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
        let cursor = unsafe { (p as *const u8).add(24) as *const u64 };
        let mut parts: Vec<String> = Vec::with_capacity(count);
        for i in 0..count {
            let k = unsafe { std::ptr::read(cursor.add(i * 2)) };
            let v = unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
            parts.push(format!("{} => {}", render(k), render(v)));
        }
        format!("%{{{}}}", parts.join(", "))
    }

    fn render_bitstring(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let bit_len = unsafe { crate::procbin::bitstring_bit_len(p) } as usize;
        let total_bytes = bit_len.div_ceil(8);
        let byte_ptr = unsafe { crate::procbin::bitstring_byte_ptr(p) };
        let bytes = unsafe { std::slice::from_raw_parts(byte_ptr, total_bytes) };
        let full_bytes = bit_len / 8;
        let trailing_bits = bit_len % 8;
        let mut parts: Vec<String> = bytes[..full_bytes].iter().map(|b| b.to_string()).collect();
        if trailing_bits > 0 {
            let last = bytes[full_bytes] >> (8 - trailing_bits);
            parts.push(format!("{}::{}", last, trailing_bits));
        }
        format!("<<{}>>", parts.join(", "))
    }

    fn render_float(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let f = crate::heap::Heap::read_float(p);
        if f.is_finite() && f.fract() == 0.0 {
            format!("{:.1}", f)
        } else {
            format!("{}", f)
        }
    }

    fn render_vec_i64(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let len = crate::heap::Heap::vec_len(p) as usize;
        let payload = unsafe { (p as *const u8).add(24) as *const i64 };
        let parts: Vec<String> = (0..len)
            .map(|i| unsafe { std::ptr::read(payload.add(i)) }.to_string())
            .collect();
        format!("~v[{}]", parts.join(", "))
    }

    fn render_vec_u8(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let len = crate::heap::Heap::vec_len(p) as usize;
        let payload = unsafe { (p as *const u8).add(24) };
        let parts: Vec<String> = (0..len)
            .map(|i| unsafe { *payload.add(i) }.to_string())
            .collect();
        format!("~b[{}]", parts.join(", "))
    }

    fn render_vec_bit(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let len = crate::heap::Heap::vec_len(p) as usize;
        let payload = unsafe { (p as *const u8).add(24) };
        let parts: Vec<String> = (0..len)
            .map(|i| {
                let byte_idx = i / 8;
                let bit_idx = 7 - (i % 8);
                let byte = unsafe { *payload.add(byte_idx) };
                ((byte >> bit_idx) & 1).to_string()
            })
            .collect();
        format!("~bits[{}]", parts.join(", "))
    }

    fn render_closure(bits: u64) -> String {
        let p = FzValue(bits).unbox_ptr().unwrap();
        let header = unsafe { &*p };
        format!("#fn<{}/{}>", header.schema_id, header.flags)
    }

    fn render_list(bits: u64) -> String {
        let mut parts: Vec<String> = Vec::new();
        let mut cur_bits = bits;
        let mut tail_render: Option<String> = None;
        loop {
            let cv = FzValue(cur_bits);
            // fz-s9y.2 — terminate on the empty-list sentinel, not on nil.
            // A list ending in `nil` (atom-like value) is an improper list;
            // it renders as `[a, b | nil]` via the tail_render path below.
            if cv.is_empty_list() {
                break;
            }
            let cp = match cv.unbox_ptr() {
                Some(p) => p,
                None => {
                    tail_render = Some(render(cur_bits));
                    break;
                }
            };
            let ch = unsafe { &*cp };
            if HeapKind::from_u16(ch.kind) != Some(HeapKind::List) {
                tail_render = Some(render(cur_bits));
                break;
            }
            let cons = unsafe { &*(cp as *const ListCons) };
            parts.push(render(cons.head.0));
            cur_bits = cons.tail.0;
        }
        match tail_render {
            Some(t) => format!("[{} | {}]", parts.join(", "), t),
            None => format!("[{}]", parts.join(", ")),
        }
    }
}
