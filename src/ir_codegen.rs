//! Cranelift codegen for fz-IR (CPS form).
//!
//! Per-fz-IR-fn ABI: `extern "C" fn(frame_ptr: *mut u8, host_ctx: *mut u8) -> *mut u8`
//!   * `frame_ptr` points to a heap-allocated frame: HeapHeader (16 B) + slots.
//!     Slot 0 = continuation pointer. Slots 1..N+1 = entry params for this fn.
//!   * `host_ctx` is an opaque pointer the host (trampoline) supplies. Halt
//!     writes the final value through it.
//!   * Return value: the next frame pointer to invoke (the trampoline calls
//!     it next), or null to halt.
//!
//! Frame schema is regenerated here as the source of truth for codegen + the
//! GC tracer: [cont_ptr, ...entry_params], all FzValue slots. (Replaces the
//! placeholder schema computed in .11.6.)
//!
//! .11.8 scope additions over .11.7: Term::Call (allocates continuation frame
//! + callee frame), Term::TailCall (frame reuse when callee shares schema,
//! else fresh alloc), Term::Return (writes result into continuation frame's
//! result slot or halts on null), real trampoline. Out of scope:
//! Term::CallClosure / TailCallClosure (closure invocation needs heap-typed
//! closures — lands later), and heap-typed prims (.11.10+).

#![allow(dead_code)]

use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use crate::heap::{FieldDescriptor, FieldKind, Schema};
use cranelift_codegen::ir::{
    self, condcodes::IntCC, types, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module as ClModule};
use std::collections::HashMap;
use std::sync::Arc;

const HEADER_SIZE: i32 = 16;
const SLOT_BYTES: i32 = 8;

// FzValue tag scheme (matches src/fz_value.rs).
const TAG_INT: i64 = 0b001;
const TAG_ATOM: i64 = 0b010;
const NIL_BITS: i64 = 0b011;
const TRUE_BITS: i64 = (1 << 3) | 0b011;
const FALSE_BITS: i64 = (2 << 3) | 0b011;

/// Errors from `compile()`. Backend-plumbing failures (cranelift
/// `declare_function` / `define_function` / `finalize_definitions`) carry
/// `Span::DUMMY` because they're internal — no fz source position maps to
/// "cranelift refused to declare a host function". The verify/define
/// per-fn paths populate `span` from `module.source.fn_span_of(f.id)` so
/// the diagnostic underlines the offending fn declaration.
#[derive(Debug, Clone)]
pub struct CodegenError {
    pub message: String,
    pub span: crate::diag::Span,
}
impl CodegenError {
    pub fn new(message: impl Into<String>) -> Self {
        Self { message: message.into(), span: crate::diag::Span::DUMMY }
    }
    pub fn with_span(mut self, span: crate::diag::Span) -> Self {
        self.span = span; self
    }
    pub fn to_diagnostic(&self) -> crate::diag::Diagnostic {
        crate::diag::Diagnostic::error(
            crate::diag::codes::CODEGEN_SCHEMA_MISSING,
            format!("codegen: {}", self.message),
            self.span,
        )
    }
}
impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "codegen: {}", self.message)
    }
}
impl std::error::Error for CodegenError {}
impl From<String> for CodegenError {
    fn from(s: String) -> Self { Self::new(s) }
}

/// Compiled module: persistent JITModule + per-fn ptr table + schemas. The
/// host runs a fn via `compiled.run(fn_id)` (constructs an internal default
/// Process) or `compiled.run_in(fn_id, &mut Process)` (caller-owned Process).
pub struct CompiledModule {
    module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    fn_ptrs: HashMap<u32, *const u8>,
    /// Per-fn frame schema (size, layout). Indexed by fz_fn_id (1:1 with
    /// schema_id).
    schemas: Vec<Schema>,
    /// User-data SchemaRegistry (tuple, struct, list, map, closure, bitstring,
    /// vec, float). Lifted from TLS in fz-ul4.11.32. Each Process constructed
    /// via `make_process()` shares this registry through its Heap.
    pub(crate) user_schemas: std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>,
    /// Per-fn frame size (bytes), indexed by FnId.0. Consumed by
    /// `fz_alloc_frame_dyn` to allocate frames for fns whose id is known
    /// only dynamically (closure invocation). Copied into Process at
    /// make_process() time.
    pub(crate) frame_sizes: Vec<u32>,
    /// Heap-registered schema ids for the bitstring reader/result tuples.
    /// Set when any bitstring prim is present; None means "no bitstring prim
    /// in this module". Copied into Process at make_process() time.
    pub(crate) bs_tuple_arity1_schema: Option<u32>,
    pub(crate) bs_tuple_arity3_schema: Option<u32>,
    /// Per-fn Var -> Descr maps from fz-ul4.11.24.2's flow-insensitive typer.
    /// Indexed by position in source Module.fns (not by FnId.0).
    pub(crate) types: crate::ir_typer::ModuleTypes,
    /// .11.24.6 + .20.5: diagnostics surface (unreachable arms, dead
    /// branches). Structured via the central `diag::Diagnostic` type.
    pub(crate) diagnostics: crate::diag::Diagnostics,
}

impl CompiledModule {
    pub fn warnings(&self) -> &crate::diag::Diagnostics {
        &self.diagnostics
    }
}

unsafe impl Send for CompiledModule {}

impl CompiledModule {
    pub fn fn_ptr(&self, fn_id: FnId) -> Option<*const u8> {
        self.fn_ptrs.get(&fn_id.0).copied()
    }

    pub fn schema_for(&self, fn_id: FnId) -> &Schema {
        &self.schemas[fn_id.0 as usize]
    }

    /// Construct a fresh Process bound to this module's compile-time data
    /// (SchemaRegistry, frame_sizes, bs_tuple_arity*_schema). Multiple
    /// Processes can be made from the same CompiledModule and run
    /// concurrently (one worker at a time per Process; libdispatch model).
    pub fn make_process(&self) -> Process {
        Process {
            heap: crate::heap::Heap::new(64 * 1024, std::rc::Rc::clone(&self.user_schemas)),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            closure_builder: None,
            closure_args: Vec::new(),
            frame_sizes: self.frame_sizes.clone(),
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
        }
    }

    /// Run the trampoline with `fn_id` as the entry fn, using a fresh Process
    /// stashed in DEFAULT_PROCESS for post-run inspection (test helpers
    /// `heap_live_count`, `heap_gc`, etc. read from DEFAULT_PROCESS).
    pub fn run(&self, fn_id: FnId) -> i64 {
        DEFAULT_PROCESS.with(|c| *c.borrow_mut() = Some(self.make_process()));
        let ptr = DEFAULT_PROCESS.with(|c| {
            let mut b = c.borrow_mut();
            b.as_mut().unwrap() as *mut Process
        });
        let prev = CURRENT_PROCESS.with(|c| c.replace(ptr));
        let result = self.run_internal(fn_id);
        CURRENT_PROCESS.with(|c| c.set(prev));
        result
    }

    /// Run with a caller-owned Process. Tests that need to inspect Process
    /// state after the run (or interleave runs of multiple Processes) use
    /// this form.
    pub fn run_in(&self, fn_id: FnId, process: &mut Process) -> i64 {
        let ptr = process as *mut Process;
        let prev = CURRENT_PROCESS.with(|c| c.replace(ptr));
        let result = self.run_internal(fn_id);
        CURRENT_PROCESS.with(|c| c.set(prev));
        result
    }

    fn run_internal(&self, fn_id: FnId) -> i64 {
        let entry_schema = &self.schemas[fn_id.0 as usize];
        let frame = fz_alloc_frame(fn_id.0, entry_schema.size);
        // Continuation pointer = null (entry fn).
        unsafe {
            let cont_slot = frame.add(HEADER_SIZE as usize) as *mut *mut u8;
            *cont_slot = std::ptr::null_mut();
        }
        let mut cur = frame;
        // Cap iterations to detect infinite trampolines in tests.
        let mut iters: usize = 0;
        let cap: usize = 10_000_000;
        while !cur.is_null() {
            iters += 1;
            if iters > cap {
                panic!("trampoline exceeded {} iterations", cap);
            }
            // fz-ul4.11.31 GC SAFEPOINT: check if the current Process's heap
            // wants a GC tick. If so, collect roots from the frame chain
            // (cur backward via frame[16] cont_ptr) and run mark-sweep
            // before dispatching the next fn.
            if current_process().heap.should_gc() {
                let roots = crate::heap::collect_roots_from_frame_chain(
                    cur as *mut crate::fz_value::HeapHeader,
                    &self.schemas,
                );
                current_process().heap.gc(&roots);
                current_process().heap.clear_should_gc_flag();
            }
            let header = cur as *const crate::fz_value::HeapHeader;
            let schema_id = unsafe { (*header).schema_id };
            let fn_ptr = self
                .fn_ptrs
                .get(&schema_id)
                .copied()
                .unwrap_or_else(|| panic!("no fn for schema_id {}", schema_id));
            let f: extern "C" fn(*mut u8, *mut u8) -> *mut u8 =
                unsafe { std::mem::transmute(fn_ptr) };
            // Per-fn ABI takes ctx in slot 2; we pass the same *mut Process
            // CURRENT_PROCESS points at. Runtime fns access via
            // current_process(); the JIT'd code doesn't dereference it
            // directly today, so passing it as the existing slot is
            // sufficient.
            let ctx = CURRENT_PROCESS.with(|c| c.get()) as *mut u8;
            cur = f(cur, ctx);
        }
        current_process().halt_value
    }
}

/// Per-task runtime state. One Process per fz-level task; the worker thread
/// installs `*mut Process` in `CURRENT_PROCESS` for the duration of a run,
/// and FFI fns reach the running task's state via `current_process()`.
///
/// libdispatch-style: TLS records the currently-running task's pointer per
/// worker; a task is owned by exactly one worker at a time (scheduler
/// invariant, .19.1). FFI fns do not yield, so TLS is stable within any FFI
/// call.
pub struct Process {
    pub heap: crate::heap::Heap,
    pub halt_value: i64,
    // Transient builder state — per-task so two interleaved tasks can't
    // corrupt one another's in-flight builders.
    pub map_builder: Option<Vec<(u64, u64)>>,
    pub bs_builder: Option<crate::bitstr::BitWriter>,
    pub vec_builder: Option<VecBuild>,
    pub closure_builder: Option<(u32, Vec<u64>)>,
    pub closure_args: Vec<u64>,
    // Per-CompiledModule constants copied at make_process() time. See
    // fz-ul4.19.1 follow-up to move these behind an Rc<CompiledModuleConsts>.
    pub frame_sizes: Vec<u32>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
}

impl Process {
    pub fn new(schemas: std::rc::Rc<std::cell::RefCell<crate::heap::SchemaRegistry>>) -> Self {
        Self {
            heap: crate::heap::Heap::new(64 * 1024, schemas),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            closure_builder: None,
            closure_args: Vec::new(),
            frame_sizes: Vec::new(),
            bs_tuple_arity1_schema: None,
            bs_tuple_arity3_schema: None,
        }
    }
}

thread_local! {
    /// Raw pointer to the Process currently being run by this worker (this
    /// thread). Set by `run_in` for the duration of the run; cleared
    /// afterwards. FFI fns called from JIT'd code read it via
    /// `current_process()`.
    pub(crate) static CURRENT_PROCESS: std::cell::Cell<*mut Process> =
        const { std::cell::Cell::new(std::ptr::null_mut()) };
    /// Backing storage for the convenience `compiled.run(fn_id)` path: a
    /// Process is constructed, stashed here, and CURRENT_PROCESS points at
    /// it. After the run, CURRENT_PROCESS is cleared but the Process remains
    /// here so test helpers (heap_live_count, heap_gc, ...) can inspect.
    /// Tests using the explicit `run_in(fn_id, &mut Process)` path own
    /// their Process directly and don't use this slot.
    pub(crate) static DEFAULT_PROCESS: std::cell::RefCell<Option<Process>> =
        const { std::cell::RefCell::new(None) };
}

/// Access the currently-installed Process via the raw TLS pointer. Must only
/// be called from FFI fns invoked synchronously inside `run_in`. The Process
/// is owned by either the caller (run_in path) or by DEFAULT_PROCESS (run
/// path); the pointer is valid for the duration of the run.
pub(crate) fn current_process() -> &'static mut Process {
    let p = CURRENT_PROCESS.with(|c| c.get());
    assert!(!p.is_null(), "current_process(): no Process installed (running outside run_in?)");
    unsafe { &mut *p }
}

// ----- Runtime fns called from JIT'd code -----

/// JIT-side print: receives an FzValue (u64 bits in an i64 ABI slot), renders
/// it, captures the rendering for tests.
extern "C" fn fz_print_value(fz_bits: u64) {
    let s = render_fz_value(fz_bits);
    TEST_CAPTURE.with(|c| c.borrow_mut().push(s));
}

fn render_fz_value(bits: u64) -> String {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(bits);
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap().to_string(),
        Tag::Atom => format!(":atom_{}", v.unbox_atom().unwrap()),
        Tag::Special => {
            if v.is_nil() { "[]".into() }
            else if v.is_true() { "true".into() }
            else if v.is_false() { "false".into() }
            else { format!("#special<{:#x}>", bits) }
        }
        Tag::Ptr => {
            let p = v.unbox_ptr().unwrap();
            let kind = unsafe { (*p).kind };
            match HeapKind::from_u16(kind) {
                Some(HeapKind::List) => render_list(bits),
                Some(HeapKind::Struct) => render_struct(bits),
                Some(HeapKind::Bitstring) => render_bitstring(bits),
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

/// Render a heap-typed Struct (currently only emitted for tuples). Reads the
/// schema from HEAP's SchemaRegistry to determine field count — `size_bytes`
/// is rounded up to 16 by the allocator and would over-count arity for odd
/// arities. Each FzValue field renders inline; non-FzValue fields are
/// elided for now (no callers emit them yet).
fn render_struct(bits: u64) -> String {
    use crate::fz_value::FzValue;
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
                    std::ptr::read(
                        (p as *const u8).add(16 + f.offset as usize) as *const u64,
                    )
                };
                render_fz_value(field_bits)
            })
            .collect()
    };
    format!("{{{}}}", parts.join(", "))
}

/// Render a heap Map as `%{k => v, ...}` in canonical sorted order.
fn render_map(bits: u64) -> String {
    use crate::fz_value::FzValue;
    let p = FzValue(bits).unbox_ptr().unwrap();
    let count = unsafe {
        std::ptr::read((p as *const u8).add(16) as *const u64) as usize
    };
    let cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    let mut parts: Vec<String> = Vec::with_capacity(count);
    for i in 0..count {
        let k = unsafe { std::ptr::read(cursor.add(i * 2)) };
        let v = unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
        parts.push(format!("{} => {}", render_fz_value(k), render_fz_value(v)));
    }
    format!("%{{{}}}", parts.join(", "))
}

/// Render a heap Bitstring. For byte-aligned bitstrings, render bytes as
/// `<<a, b, c>>`. For sub-byte bit_len, append `::<bits>` to the partial
/// byte's value. Mirrors the interp's display for tests.
fn render_bitstring(bits: u64) -> String {
    use crate::fz_value::FzValue;
    let p = FzValue(bits).unbox_ptr().unwrap();
    let bit_len = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) } as usize;
    let total_bytes = bit_len.div_ceil(8);
    let bytes = unsafe { std::slice::from_raw_parts((p as *const u8).add(24), total_bytes) };
    let full_bytes = bit_len / 8;
    let trailing_bits = bit_len % 8;
    let mut parts: Vec<String> = bytes[..full_bytes].iter().map(|b| b.to_string()).collect();
    if trailing_bits > 0 {
        // Show the trailing partial byte right-shifted to its high bits.
        let last = bytes[full_bytes] >> (8 - trailing_bits);
        parts.push(format!("{}::{}", last, trailing_bits));
    }
    format!("<<{}>>", parts.join(", "))
}

/// Render a boxed float: whole numbers get an explicit `.0` suffix
/// (`4.0`, not `4`); fractional values use Rust's default Display.
fn render_float(bits: u64) -> String {
    use crate::fz_value::FzValue;
    let p = FzValue(bits).unbox_ptr().unwrap();
    let f = crate::heap::Heap::read_float(p);
    if f.is_finite() && f.fract() == 0.0 { format!("{:.1}", f) } else { format!("{}", f) }
}

fn render_vec_i64(bits: u64) -> String {
    use crate::fz_value::FzValue;
    let p = FzValue(bits).unbox_ptr().unwrap();
    let len = crate::heap::Heap::vec_len(p) as usize;
    let payload = unsafe { (p as *const u8).add(24) as *const i64 };
    let parts: Vec<String> = (0..len)
        .map(|i| unsafe { std::ptr::read(payload.add(i)) }.to_string())
        .collect();
    format!("~v[{}]", parts.join(", "))
}

fn render_vec_u8(bits: u64) -> String {
    use crate::fz_value::FzValue;
    let p = FzValue(bits).unbox_ptr().unwrap();
    let len = crate::heap::Heap::vec_len(p) as usize;
    let payload = unsafe { (p as *const u8).add(24) };
    let parts: Vec<String> = (0..len)
        .map(|i| unsafe { *payload.add(i) }.to_string())
        .collect();
    format!("~b[{}]", parts.join(", "))
}

fn render_vec_bit(bits: u64) -> String {
    use crate::fz_value::FzValue;
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

/// Render a closure as `#fn<id/cap>` for debug. cap = captured count.
fn render_closure(bits: u64) -> String {
    use crate::fz_value::FzValue;
    let p = FzValue(bits).unbox_ptr().unwrap();
    let header = unsafe { &*p };
    format!("#fn<{}/{}>", header.schema_id, header.flags)
}

fn render_list(bits: u64) -> String {
    use crate::fz_value::{FzValue, HeapKind, ListCons};
    let mut parts: Vec<String> = Vec::new();
    let mut cur_bits = bits;
    let mut tail_render: Option<String> = None;
    loop {
        let cv = FzValue(cur_bits);
        if cv.is_nil() { break; }
        let cp = match cv.unbox_ptr() {
            Some(p) => p,
            None => {
                // improper tail (atom / int / etc.)
                tail_render = Some(render_fz_value(cur_bits));
                break;
            }
        };
        let ch = unsafe { &*cp };
        if HeapKind::from_u16(ch.kind) != Some(HeapKind::List) {
            tail_render = Some(render_fz_value(cur_bits));
            break;
        }
        let cons = unsafe { &*(cp as *const ListCons) };
        parts.push(render_fz_value(cons.head.0));
        cur_bits = cons.tail.0;
    }
    match tail_render {
        Some(t) => format!("[{} | {}]", parts.join(", "), t),
        None => format!("[{}]", parts.join(", ")),
    }
}

thread_local! {
    pub static TEST_CAPTURE: std::cell::RefCell<Vec<String>> = std::cell::RefCell::new(Vec::new());
    /// (.11.24.4) Per-fn Cranelift IR display text captured by compile()
    /// after compile_fn but before define_function consumes the context.
    /// Test-only; enable by calling `ir_text_record_enable()` before compile.
    pub static IR_TEXT_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = std::cell::RefCell::new(None);
}

pub fn test_capture_take() -> Vec<String> {
    TEST_CAPTURE.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

#[cfg(test)]
pub(crate) fn ir_text_record_enable() {
    IR_TEXT_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

#[cfg(test)]
pub(crate) fn ir_text_record_take() -> Vec<(String, String)> {
    IR_TEXT_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// Halt: receives an FzValue from the JIT, unboxes per-tag into a
/// debug-friendly i64 stored on the current Process's halt_value. Halt is a
/// debugging seam; this preserves byte-for-byte halt values for existing
/// scalar tests while not constraining heap-typed semantics later.
///
/// The second arg is the per-fn ABI's `ctx: *mut u8` (= *mut Process). For
/// the migration we ignore it in favor of current_process() — they point at
/// the same Process, but using current_process() keeps the access pattern
/// uniform with every other fz_* fn.
extern "C" fn fz_halt(_ctx: *mut u8, fz_bits: u64) {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(fz_bits);
    let i: i64 = match v.tag() {
        Tag::Int => v.unbox_int().unwrap(),
        Tag::Atom => v.unbox_atom().unwrap() as i64,
        Tag::Special => {
            if v.is_true() { 1 }
            else if v.is_false() { 0 }
            else { 0 } // nil
        }
        Tag::Ptr => {
            let p = v.unbox_ptr().unwrap();
            // Null Ptr-tagged value (e.g. 0): nothing to read, return raw bits.
            if p.is_null() {
                fz_bits as i64
            } else {
                let kind = unsafe { (*p).kind };
                // For boxed floats, halt returns the f64 bits so tests can
                // round-trip via f64::from_bits. Other heap kinds: raw bits.
                match HeapKind::from_u16(kind) {
                    Some(HeapKind::Float) => crate::heap::Heap::read_float(p).to_bits() as i64,
                    _ => fz_bits as i64,
                }
            }
        }
        Tag::Reserved => fz_bits as i64,
    };
    current_process().halt_value = i;
}

// ----- Heap (managed cons-cell allocator) -----
//
// The JIT-side `fz_alloc_list_cons` routes through the current Process's heap
// so the GC tracer in src/heap.rs can reclaim cons cells. Frames stay on the
// system allocator for now (frames don't yet root-trace; .11.31).

/// Reset DEFAULT_PROCESS. Call at the start of any test that needs a clean
/// heap. Tests share threads via the cargo test runner's worker pool, so
/// leftover state is otherwise sticky.
pub fn heap_reset_for_test() {
    DEFAULT_PROCESS.with(|c| *c.borrow_mut() = None);
}

pub fn heap_live_count() -> usize {
    DEFAULT_PROCESS.with(|c| {
        c.borrow().as_ref().map(|p| p.heap.live_count()).unwrap_or(0)
    })
}

pub fn heap_freelist_len() -> usize {
    DEFAULT_PROCESS.with(|c| {
        c.borrow().as_ref().map(|p| p.heap.freelist_len()).unwrap_or(0)
    })
}

pub fn heap_gc(roots: &[crate::fz_value::FzValue]) {
    DEFAULT_PROCESS.with(|c| {
        if let Some(p) = c.borrow_mut().as_mut() {
            p.heap.gc(roots);
        }
    });
}

extern "C" fn fz_alloc_list_cons(head_bits: u64, tail_bits: u64) -> u64 {
    use crate::fz_value::FzValue;
    let p = current_process()
        .heap
        .alloc_list_cons(FzValue(head_bits), FzValue(tail_bits));
    // Heap returns 16-byte-aligned pointers (low 4 bits zero), so the raw
    // pointer doubles as the FzValue ptr-tagged encoding (tag bits = 000).
    p as u64
}

/// Allocate a heap-typed Struct. `schema_id` must already be registered in
/// the current Process's heap SchemaRegistry (shared with CompiledModule).
/// Returns the FzValue ptr-bits (heap-aligned, so tag = 000). Caller is
/// responsible for writing field values into payload slots after allocation.
extern "C" fn fz_alloc_struct(schema_id: u32) -> u64 {
    let p = current_process().heap.alloc_struct(schema_id);
    p as u64
}

// ----- Map runtime fns -----
//
// Maps use a heap-backed sorted-array layout. Build-time semantics: codegen
// emits begin -> push (per pair) -> finalize. MapUpdate emits clone(base) ->
// push (per override) -> finalize. The thread-local builder accumulates
// pairs as `(key_bits, val_bits)`; finalize sorts canonically (later writes
// win on duplicate keys) and allocates one heap Map.
//
// Key total ordering for canonical layout: Int < Atom < Special < Ptr;
// within each category, by raw bits (Int compares signed). Keys compare
// equal iff their u64 bits are equal — pointer-equal heap keys for v1.

// MAP_BUILDER state moved to Process.map_builder (per fz-ul4.11.32).

fn fz_key_category(bits: u64) -> u8 {
    match bits & 0b111 {
        0b001 => 0,
        0b010 => 1,
        0b011 => 2,
        0b000 => 3,
        _ => 4,
    }
}

fn fz_key_cmp(a: u64, b: u64) -> std::cmp::Ordering {
    let ca = fz_key_category(a);
    let cb = fz_key_category(b);
    ca.cmp(&cb).then_with(|| {
        if ca == 0 {
            ((a as i64) >> 3).cmp(&((b as i64) >> 3))
        } else {
            a.cmp(&b)
        }
    })
}

extern "C" fn fz_map_begin() {
    current_process().map_builder = Some(Vec::new());
}

extern "C" fn fz_map_clone(base_bits: u64) {
    use crate::fz_value::{FzValue, HeapKind};
    let mut entries: Vec<(u64, u64)> = Vec::new();
    let p = FzValue(base_bits)
        .unbox_ptr()
        .expect("fz_map_clone base not a heap ptr");
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Map) {
        panic!("fz_map_clone base is not a Map");
    }
    let count =
        unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
    let mut cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    for _ in 0..count {
        let k = unsafe { std::ptr::read(cursor) };
        let v = unsafe { std::ptr::read(cursor.add(1)) };
        cursor = unsafe { cursor.add(2) };
        entries.push((k, v));
    }
    current_process().map_builder = Some(entries);
}

extern "C" fn fz_map_push(key_bits: u64, val_bits: u64) {
    current_process()
        .map_builder
        .as_mut()
        .expect("fz_map_push without begin/clone")
        .push((key_bits, val_bits));
}

extern "C" fn fz_map_finalize() -> u64 {
    use crate::fz_value::FzValue;
    let raw = current_process()
        .map_builder
        .take()
        .expect("fz_map_finalize without begin");
    // Last write wins on duplicate keys: walk in order, dedupe-overwriting.
    let mut by_key: Vec<(u64, u64)> = Vec::with_capacity(raw.len());
    for (k, v) in raw {
        if let Some(slot) = by_key.iter_mut().find(|(ek, _)| fz_key_cmp(*ek, k).is_eq())
        {
            slot.1 = v;
        } else {
            by_key.push((k, v));
        }
    }
    by_key.sort_by(|a, b| fz_key_cmp(a.0, b.0));
    let entries: Vec<(FzValue, FzValue)> =
        by_key.into_iter().map(|(k, v)| (FzValue(k), FzValue(v))).collect();
    let p = current_process().heap.alloc_map(&entries);
    p as u64
}

extern "C" fn fz_map_get(map_bits: u64, key_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind};
    let p = FzValue(map_bits)
        .unbox_ptr()
        .expect("fz_map_get on non-ptr");
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Map) {
        panic!("fz_map_get on non-Map");
    }
    let count =
        unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) as usize };
    let cursor = unsafe { (p as *const u8).add(24) as *const u64 };
    // v1: linear scan. Sorted layout exists primarily so equality and
    // rendering have a deterministic shape; binary search comes alongside
    // a HAMT migration for large maps (separate ticket).
    for i in 0..count {
        let k = unsafe { std::ptr::read(cursor.add(i * 2)) };
        if fz_key_cmp(k, key_bits).is_eq() {
            return unsafe { std::ptr::read(cursor.add(i * 2 + 1)) };
        }
    }
    FzValue::NIL.0
}

// ----- Bitstring runtime fns -----
//
// Construction uses a thread-local BitWriter populated across a sequence of
// `fz_bs_write_field` calls between `fz_bs_begin` and `fz_bs_finalize`. The
// codegen for a single Prim::MakeBitstring emits this whole sequence within
// one block — no CPS splits between begin and finalize, so per-thread state
// is safe.
//
// Reader prims model the reader as a 3-tuple `[bs_ptr, bit_len_int, pos_int]`
// (heap-allocated via fz_alloc_struct). Each BitReadField allocates a fresh
// 3-tuple result `[ok, extracted, new_reader]` on success or 1-tuple
// `[false]` on failure. Tuple schema_ids for arities 1 and 3 are registered
// at compile() time when any bitstring prim is present.

// BS_BUILDER + BS_TUPLE_ARITY{1,3}_SCHEMA state moved to Process fields
// (per fz-ul4.11.32). Tuple-arity schema ids are filled in at make_process()
// time from CompiledModule's compile-time tables.

extern "C" fn fz_bs_begin() {
    current_process().bs_builder = Some(crate::bitstr::BitWriter::new());
}

/// Write one field into the active builder. Field-type tags match the order
/// in `crate::ast::BitType`: Integer=0, Float=1, Binary=2, Bits=3, Utf8=4,
/// Utf16=5, Utf32=6. `size_present` distinguishes None (0) vs Some (1);
/// `size_value` is in size-units (multiplied by `unit` internally).
#[allow(clippy::too_many_arguments)]
extern "C" fn fz_bs_write_field(
    value_bits: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
) {
    use crate::ast::BitType;
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let ty = decode_bit_type(ty_tag);
    let size = if size_present != 0 { Some(size_value) } else { None };
    let endian = decode_endian(endian_tag);
    // `signed` is irrelevant on write: two's-complement truncation produces
    // the same bit pattern for signed and unsigned at fixed width. The flag
    // is consumed on read (fz_bs_read_field) for sign extension.
    let _ = signed;
    {
        let w = current_process()
            .bs_builder
            .as_mut()
            .expect("fz_bs_write_field called without fz_bs_begin");
        match ty {
            BitType::Integer => {
                let n = FzValue(value_bits)
                    .unbox_int()
                    .expect("integer bit field expects boxed int");
                let total = size.unwrap_or(8) * unit;
                assert!(total <= 64, "integer field too wide: {}", total);
                let masked = if total < 64 {
                    (n as u64) & ((1u64 << total) - 1)
                } else {
                    n as u64
                };
                let bswap = crate::bitstr::apply_endian_for_write(masked, total, endian);
                w.write_bits(bswap, total as usize);
            }
            BitType::Binary | BitType::Bits => {
                // Source must be a heap Bitstring (Vec(U8) lands in .11.14;
                // until then both Binary and Bits read from a Bitstring).
                let v = FzValue(value_bits);
                let p = match v.tag() {
                    Tag::Ptr => v.unbox_ptr().expect("binary field: bad ptr"),
                    _ => panic!("binary/bits bit field expects heap bitstring"),
                };
                let header = unsafe { &*p };
                if HeapKind::from_u16(header.kind) != Some(HeapKind::Bitstring) {
                    panic!("binary/bits bit field source is not a Bitstring");
                }
                let src_bit_len = unsafe {
                    std::ptr::read((p as *const u8).add(16) as *const u64)
                } as usize;
                let src_bytes_ptr = unsafe { (p as *const u8).add(24) };
                let needed_bits = match (ty, size) {
                    (BitType::Binary, None) => src_bit_len,
                    (BitType::Binary, Some(n)) => (n * unit) as usize,
                    (BitType::Bits, None) => src_bit_len,
                    (BitType::Bits, Some(n)) => (n * unit) as usize,
                    _ => unreachable!(),
                };
                assert!(needed_bits <= src_bit_len, "binary/bits field exceeds source");
                let src_bytes = unsafe {
                    std::slice::from_raw_parts(src_bytes_ptr, src_bit_len.div_ceil(8))
                };
                if needed_bits % 8 == 0 && w.bit_len % 8 == 0 {
                    w.bytes.extend_from_slice(&src_bytes[..needed_bits / 8]);
                    w.bit_len += needed_bits;
                } else {
                    let mut r = crate::bitstr::BitReader {
                        bytes: src_bytes,
                        bit_len: src_bit_len,
                        pos: 0,
                    };
                    for _ in 0..needed_bits {
                        w.append_bit(r.read_bit().unwrap());
                    }
                }
            }
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
                let cp = FzValue(value_bits)
                    .unbox_int()
                    .expect("utf field expects integer codepoint")
                    as u32;
                let bytes = match ty {
                    BitType::Utf8 => crate::bitstr::encode_utf8(cp),
                    BitType::Utf16 => crate::bitstr::encode_utf16(cp, endian),
                    BitType::Utf32 => crate::bitstr::encode_utf32(cp, endian),
                    _ => unreachable!(),
                };
                let bytes = bytes.expect("invalid codepoint");
                w.write_bytes(&bytes);
            }
            BitType::Float => {
                use crate::bitstr::apply_endian_for_write;
                let total = size.unwrap_or(64) * unit;
                if total != 32 && total != 64 {
                    panic!("float bit field size must be 32 or 64, got {}", total);
                }
                // Decode the FzValue: Int unboxes to i64 then casts to f64;
                // boxed Float reads payload directly. Then bit-cast and write.
                let f = fz_to_f64(value_bits);
                let raw: u64 = if total == 32 {
                    (f as f32).to_bits() as u64
                } else {
                    f.to_bits()
                };
                let raw = apply_endian_for_write(raw, total, endian);
                w.write_bits(raw, total as usize);
            }
        }
    }
}

extern "C" fn fz_bs_finalize() -> u64 {
    let w = current_process()
        .bs_builder
        .take()
        .expect("fz_bs_finalize without fz_bs_begin");
    let bit_len = w.bit_len as u64;
    let bytes = w.bytes;
    let p = current_process().heap.alloc_bitstring(&bytes, bit_len);
    p as u64
}

fn decode_bit_type(t: u32) -> crate::ast::BitType {
    use crate::ast::BitType;
    match t {
        0 => BitType::Integer,
        1 => BitType::Float,
        2 => BitType::Binary,
        3 => BitType::Bits,
        4 => BitType::Utf8,
        5 => BitType::Utf16,
        6 => BitType::Utf32,
        _ => panic!("unknown bit type tag {}", t),
    }
}

fn decode_endian(e: u32) -> crate::ast::Endian {
    use crate::ast::Endian;
    match e {
        0 => Endian::Big,
        1 => Endian::Little,
        2 => Endian::Native,
        _ => panic!("unknown endian tag {}", e),
    }
}

fn encode_bit_type(t: crate::ast::BitType) -> u32 {
    use crate::ast::BitType;
    match t {
        BitType::Integer => 0,
        BitType::Float => 1,
        BitType::Binary => 2,
        BitType::Bits => 3,
        BitType::Utf8 => 4,
        BitType::Utf16 => 5,
        BitType::Utf32 => 6,
    }
}

fn encode_endian(e: crate::ast::Endian) -> u32 {
    use crate::ast::Endian;
    match e {
        Endian::Big => 0,
        Endian::Little => 1,
        Endian::Native => 2,
    }
}

/// Default unit per type, mirroring `crate::ir_lower::resolved_unit_for`.
fn default_unit_for(ty: crate::ast::BitType) -> u32 {
    use crate::ast::BitType;
    match ty {
        BitType::Integer | BitType::Float | BitType::Bits => 1,
        BitType::Binary => 8,
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => 1,
    }
}

/// Allocate a 3-tuple reader `[bs_ptr, bit_len_int, pos_int]` for an input
/// bitstring. Schema id is set by compile() into BS_TUPLE_ARITY3_SCHEMA.
extern "C" fn fz_bs_reader_init(bs_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(bs_bits);
    let p = match v.tag() {
        Tag::Ptr => v.unbox_ptr().expect("reader_init: bad ptr"),
        _ => panic!("reader_init expects heap value"),
    };
    let header = unsafe { &*p };
    if HeapKind::from_u16(header.kind) != Some(HeapKind::Bitstring) {
        panic!("reader_init source is not a Bitstring");
    }
    let bit_len = unsafe { std::ptr::read((p as *const u8).add(16) as *const u64) } as i64;
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let tuple_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (tuple_p as *mut u8).add(16);
        // [bs_ptr, bit_len_boxed, 0_boxed]
        std::ptr::write(base as *mut u64, bs_bits);
        std::ptr::write(base.add(8) as *mut u64, ((bit_len as u64) << 3) | 0b001);
        std::ptr::write(base.add(16) as *mut u64, ((0i64 as u64) << 3) | 0b001);
    }
    tuple_p as u64
}

#[allow(clippy::too_many_arguments)]
extern "C" fn fz_bs_read_field(
    reader_bits: u64,
    ty_tag: u32,
    size_present: u32,
    size_value: u32,
    unit: u32,
    endian_tag: u32,
    signed: u32,
    is_last: u32,
) -> u64 {
    use crate::ast::BitType;
    use crate::bitstr::{apply_endian_for_read, sign_extend};
    use crate::fz_value::{FzValue, HeapKind};
    let ty = decode_bit_type(ty_tag);
    let size = if size_present != 0 { Some(size_value) } else { None };
    let endian = decode_endian(endian_tag);
    let signed_b = signed != 0;
    let is_last_b = is_last != 0;

    // Decode reader tuple.
    let v = FzValue(reader_bits);
    let rp = v.unbox_ptr().expect("read_field: reader is not a ptr");
    let bs_bits = unsafe { std::ptr::read((rp as *const u8).add(16) as *const u64) };
    let bit_len = (FzValue(unsafe {
        std::ptr::read((rp as *const u8).add(24) as *const u64)
    }))
    .unbox_int()
    .unwrap() as usize;
    let pos = (FzValue(unsafe {
        std::ptr::read((rp as *const u8).add(32) as *const u64)
    }))
    .unbox_int()
    .unwrap() as usize;

    // Bytes pointer from bs.
    let bs_v = FzValue(bs_bits);
    let bsp = bs_v.unbox_ptr().expect("read_field: reader bs not a ptr");
    let bs_header = unsafe { &*bsp };
    if HeapKind::from_u16(bs_header.kind) != Some(HeapKind::Bitstring) {
        panic!("read_field reader bs is not a Bitstring");
    }
    let bytes_ptr = unsafe { (bsp as *const u8).add(24) };
    let bytes = unsafe { std::slice::from_raw_parts(bytes_ptr, bit_len.div_ceil(8)) };

    // Failure path: alloc 1-tuple [false].
    let arity1 = current_process()
        .bs_tuple_arity1_schema
        .expect("bs_tuple_arity1_schema not set");
    let arity3 = current_process()
        .bs_tuple_arity3_schema
        .expect("bs_tuple_arity3_schema not set");
    let fail = || -> u64 {
        let p = current_process().heap.alloc_struct(arity1);
        unsafe {
            let base = (p as *mut u8).add(16);
            std::ptr::write(base as *mut u64, FzValue::FALSE.0);
        }
        p as u64
    };

    let mut r = crate::bitstr::BitReader { bytes, bit_len, pos };

    let (extracted_bits, consumed) = match ty {
        BitType::Integer => {
            let total = size.unwrap_or(8) * unit;
            if total > 64 { return fail(); }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return fail(),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let n: i64 = if signed_b { sign_extend(raw, total) } else { raw as i64 };
            (FzValue::from_int(n).0, total as usize)
        }
        BitType::Binary | BitType::Bits => {
            let needed_bits = match (ty, size, is_last_b) {
                (BitType::Binary, None, true) | (BitType::Bits, None, true) => bit_len - pos,
                (BitType::Binary, None, false) => return fail(), // size required
                (BitType::Bits, None, false) => return fail(),
                (BitType::Binary, Some(n), _) => (n * unit) as usize,
                (BitType::Bits, Some(n), _) => (n * unit) as usize,
                _ => unreachable!(),
            };
            if pos + needed_bits > bit_len { return fail(); }
            // Build a fresh Bitstring from the slice. Always copy for v1
            // (zero-copy slicing deferred — see ticket "Open").
            let mut sub_bytes = Vec::with_capacity(needed_bits.div_ceil(8));
            let mut w = crate::bitstr::BitWriter::new();
            for _ in 0..needed_bits {
                w.append_bit(r.read_bit().unwrap());
            }
            sub_bytes.extend_from_slice(&w.bytes);
            let new_bs = current_process()
                .heap
                .alloc_bitstring(&sub_bytes, needed_bits as u64);
            let new_bs_bits = new_bs as u64;
            (new_bs_bits, needed_bits)
        }
        BitType::Float => {
            let total = size.unwrap_or(64) * unit;
            if total != 32 && total != 64 {
                return fail();
            }
            let raw = match r.read_bits(total as usize) {
                Some(v) => v,
                None => return fail(),
            };
            let raw = apply_endian_for_read(raw, total, endian);
            let f = if total == 32 {
                f32::from_bits(raw as u32) as f64
            } else {
                f64::from_bits(raw)
            };
            let p = current_process().heap.alloc_float(f);
            (p as u64, total as usize)
        }
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
            // UTF: read uses crate::bitstr::decode_utf*; not exercised by
            // ticket tests, so panic to surface intent rather than partial.
            panic!(
                "BitReadField for {:?} not yet wired in JIT (lands with UTF support)",
                ty
            );
        }
    };

    // Allocate fresh reader tuple [bs_bits, bit_len_boxed, new_pos_boxed].
    let new_pos = (pos + consumed) as i64;
    let new_reader_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (new_reader_p as *mut u8).add(16);
        std::ptr::write(base as *mut u64, bs_bits);
        std::ptr::write(base.add(8) as *mut u64, ((bit_len as u64) << 3) | 0b001);
        std::ptr::write(base.add(16) as *mut u64, ((new_pos as u64) << 3) | 0b001);
    }

    // Allocate result tuple [true, extracted, new_reader].
    let result_p = current_process().heap.alloc_struct(arity3);
    unsafe {
        let base = (result_p as *mut u8).add(16);
        std::ptr::write(base as *mut u64, FzValue::TRUE.0);
        std::ptr::write(base.add(8) as *mut u64, extracted_bits);
        std::ptr::write(base.add(16) as *mut u64, new_reader_p as u64);
    }
    result_p as u64
}

// ----- Float runtime fns -----
//
// Boxed f64s. v1 representation: HeapKind::Float, layout `HeapHeader (16) +
// f64 (8) + pad (8)`. Tag::Ptr (low bits 000), so two distinct boxed floats
// with the same value are NOT bit-equal — comparison ops dispatch through
// fz_value_eq when at least one operand has Tag::Ptr.
//
// Arithmetic dispatch: codegen emits an inline both-int fast-path test
// (`((a^1) | (b^1)) & 7 == 0`) and falls back to fz_arith_* runtime helpers
// when either operand is non-Int. The slow path promotes Int→Float and
// returns a fresh boxed float; mixed-type ops promote (e.g. `1 + 2.0` ==
// `3.0`). Eq/Neq do NOT promote: `1 == 1.0` is false.

extern "C" fn fz_alloc_float(bits: u64) -> u64 {
    let f = f64::from_bits(bits);
    let p = current_process().heap.alloc_float(f);
    p as u64
}

/// Decode an FzValue (Int or boxed Float) into f64. Panics on other tags.
fn fz_to_f64(bits: u64) -> f64 {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    let v = FzValue(bits);
    match v.tag() {
        Tag::Int => v.unbox_int().unwrap() as f64,
        Tag::Ptr => {
            let p = v.unbox_ptr().unwrap();
            let kind = unsafe { (*p).kind };
            match HeapKind::from_u16(kind) {
                Some(HeapKind::Float) => crate::heap::Heap::read_float(p),
                _ => panic!("arithmetic on non-numeric heap kind {}", kind),
            }
        }
        _ => panic!("arithmetic on non-numeric tag {:?}", v.tag()),
    }
}

fn box_float(f: f64) -> u64 {
    let p = current_process().heap.alloc_float(f);
    p as u64
}

extern "C" fn fz_arith_add(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) + fz_to_f64(b)) }
extern "C" fn fz_arith_sub(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) - fz_to_f64(b)) }
extern "C" fn fz_arith_mul(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) * fz_to_f64(b)) }
extern "C" fn fz_arith_div(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) / fz_to_f64(b)) }
extern "C" fn fz_arith_mod(a: u64, b: u64) -> u64 { box_float(fz_to_f64(a) % fz_to_f64(b)) }

/// Comparison helpers return FzValue TRUE/FALSE bits. Like the arithmetic
/// helpers, these handle mixed-type operands by promoting Int→f64.
fn cmp_to_fz(b: bool) -> u64 {
    use crate::fz_value::FzValue;
    if b { FzValue::TRUE.0 } else { FzValue::FALSE.0 }
}
extern "C" fn fz_cmp_lt(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) <  fz_to_f64(b)) }
extern "C" fn fz_cmp_le(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) <= fz_to_f64(b)) }
extern "C" fn fz_cmp_gt(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) >  fz_to_f64(b)) }
extern "C" fn fz_cmp_ge(a: u64, b: u64) -> u64 { cmp_to_fz(fz_to_f64(a) >= fz_to_f64(b)) }

/// Structural Eq for two Tag::Ptr FzValues. Both args MUST be Tag::Ptr —
/// the JIT-side dispatch (`both_ptr` test) guarantees this, so the unwraps
/// are infallible. Returns FzValue TRUE/FALSE bits.
///
/// Recursion: List/Struct/Map fields are themselves FzValues that may be
/// scalars or other heap values, so the recursive call dispatches on the
/// child's tag. For scalar children we can short-circuit on raw bit
/// equality before calling back into this fn — `eq_fz` handles that.
extern "C" fn fz_value_eq(a: u64, b: u64) -> u64 {
    cmp_to_fz(eq_fz(a, b))
}

/// Internal recursive equality for FzValues of any tag. Scalars short-
/// circuit on bit-eq; heap-typed pairs of the same kind recurse per kind.
fn eq_fz(a: u64, b: u64) -> bool {
    use crate::fz_value::{FzValue, HeapKind, Tag};
    if a == b { return true; } // covers all scalar same-tag cases + ptr-identity
    let av = FzValue(a);
    let bv = FzValue(b);
    if !matches!((av.tag(), bv.tag()), (Tag::Ptr, Tag::Ptr)) {
        // At least one side is a scalar with different bits -> inequal.
        return false;
    }
    let ap = av.unbox_ptr().unwrap();
    let bp = bv.unbox_ptr().unwrap();
    if ap.is_null() || bp.is_null() {
        return ap == bp;
    }
    let ah = unsafe { &*ap };
    let bh = unsafe { &*bp };
    if ah.kind != bh.kind {
        return false;
    }
    match HeapKind::from_u16(ah.kind) {
        Some(HeapKind::Float) => {
            crate::heap::Heap::read_float(ap) == crate::heap::Heap::read_float(bp)
        }
        Some(HeapKind::List) => eq_list(ap, bp),
        Some(HeapKind::Struct) => eq_struct(ap, bp, ah.schema_id, bh.schema_id),
        Some(HeapKind::Bitstring) => eq_bitstring(ap, bp),
        Some(HeapKind::Map) => eq_map(ap, bp),
        // Closures + Vecs: ticket scope is List/Struct/Bitstring/Map only.
        // Fall back to ptr-identity (already false here, since a != b).
        _ => false,
    }
}

fn eq_list(ap: *mut crate::fz_value::HeapHeader, bp: *mut crate::fz_value::HeapHeader) -> bool {
    use crate::fz_value::{HeapKind, ListCons};
    // Walk both chains in lockstep. NIL terminates both at the same step.
    let mut a = ap as *const u8;
    let mut b = bp as *const u8;
    loop {
        let ac = unsafe { &*(a as *const ListCons) };
        let bc = unsafe { &*(b as *const ListCons) };
        if !eq_fz(ac.head.0, bc.head.0) {
            return false;
        }
        // Decide each tail: NIL => done; Ptr to List => recurse; else mismatch.
        let at = ac.tail.0;
        let bt = bc.tail.0;
        if at == bt {
            return true; // both NIL (same scalar bits) — common terminator
        }
        // If either tail is non-list, the chains diverge.
        let av = crate::fz_value::FzValue(at);
        let bv = crate::fz_value::FzValue(bt);
        let (Some(anp), Some(bnp)) = (av.unbox_ptr(), bv.unbox_ptr()) else {
            return false;
        };
        let ak = unsafe { (*anp).kind };
        let bk = unsafe { (*bnp).kind };
        if HeapKind::from_u16(ak) != Some(HeapKind::List)
            || HeapKind::from_u16(bk) != Some(HeapKind::List)
        {
            return false;
        }
        a = anp as *const u8;
        b = bnp as *const u8;
    }
}

fn eq_struct(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
    a_schema: u32,
    b_schema: u32,
) -> bool {
    if a_schema != b_schema {
        return false;
    }
    // Schema in current Process's heap registry tells us field count.
    let n_fields = {
        let reg = current_process().heap.schemas_registry();
        let registry = reg.borrow();
        registry.get(a_schema).fields.len()
    };
    for i in 0..n_fields {
        let off = (i * 8) as isize;
        let av = unsafe {
            std::ptr::read((ap as *const u8).offset(16 + off) as *const u64)
        };
        let bv = unsafe {
            std::ptr::read((bp as *const u8).offset(16 + off) as *const u64)
        };
        if !eq_fz(av, bv) {
            return false;
        }
    }
    true
}

fn eq_bitstring(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
) -> bool {
    let a_bits = unsafe { std::ptr::read((ap as *const u8).add(16) as *const u64) };
    let b_bits = unsafe { std::ptr::read((bp as *const u8).add(16) as *const u64) };
    if a_bits != b_bits {
        return false;
    }
    let bit_len = a_bits as usize;
    let full_bytes = bit_len / 8;
    let trailing = bit_len % 8;
    let a_pay = unsafe { (ap as *const u8).add(24) };
    let b_pay = unsafe { (bp as *const u8).add(24) };
    for i in 0..full_bytes {
        if unsafe { *a_pay.add(i) != *b_pay.add(i) } {
            return false;
        }
    }
    if trailing > 0 {
        let mask: u8 = 0xFFu8 << (8 - trailing);
        let a_last = unsafe { *a_pay.add(full_bytes) } & mask;
        let b_last = unsafe { *b_pay.add(full_bytes) } & mask;
        if a_last != b_last {
            return false;
        }
    }
    true
}

fn eq_map(
    ap: *mut crate::fz_value::HeapHeader,
    bp: *mut crate::fz_value::HeapHeader,
) -> bool {
    let a_count = unsafe { std::ptr::read((ap as *const u8).add(16) as *const u64) } as usize;
    let b_count = unsafe { std::ptr::read((bp as *const u8).add(16) as *const u64) } as usize;
    if a_count != b_count {
        return false;
    }
    // Both maps store entries in canonical sort order (.11.13), so a
    // pairwise walk suffices — same key-position implies same key.
    let a_cur = unsafe { (ap as *const u8).add(24) as *const u64 };
    let b_cur = unsafe { (bp as *const u8).add(24) as *const u64 };
    for i in 0..a_count {
        let ak = unsafe { std::ptr::read(a_cur.add(i * 2)) };
        let bk = unsafe { std::ptr::read(b_cur.add(i * 2)) };
        if !eq_fz(ak, bk) {
            return false;
        }
        let av = unsafe { std::ptr::read(a_cur.add(i * 2 + 1)) };
        let bv = unsafe { std::ptr::read(b_cur.add(i * 2 + 1)) };
        if !eq_fz(av, bv) {
            return false;
        }
    }
    true
}

// ----- Vec runtime fns -----
//
// Vecs are heap objects with raw element-payload (no FzValues inside).
// Construction stages elements in TLS via begin(kind) -> push(v) ×n ->
// finalize(); per-kind decoding happens at push (for U8/Bit) or finalize
// (Bit packs at the end). VecF64 is gated behind .11.20/.11.23.

#[derive(Debug)]
pub enum VecBuild {
    I64(Vec<i64>),
    U8(Vec<u8>),
    Bit(Vec<bool>),
}

// VEC_BUILDER state moved to Process.vec_builder (per fz-ul4.11.32).

/// kind tag matches `HeapKind as u16`: VecI64=3, VecU8=5, VecBit=6.
extern "C" fn fz_vec_begin(kind_tag: u32) {
    use crate::fz_value::HeapKind;
    let b = match HeapKind::from_u16(kind_tag as u16) {
        Some(HeapKind::VecI64) => VecBuild::I64(Vec::new()),
        Some(HeapKind::VecU8) => VecBuild::U8(Vec::new()),
        Some(HeapKind::VecBit) => VecBuild::Bit(Vec::new()),
        Some(HeapKind::VecF64) => panic!("VecF64 deferred to fz-ul4.11.23"),
        _ => panic!("fz_vec_begin: invalid kind tag {}", kind_tag),
    };
    current_process().vec_builder = Some(b);
}

extern "C" fn fz_vec_push(value_bits: u64) {
    use crate::fz_value::FzValue;
    let n = FzValue(value_bits)
        .unbox_int()
        .expect("fz_vec_push: vec element not Int");
    match current_process()
        .vec_builder
        .as_mut()
        .expect("fz_vec_push without begin")
    {
        VecBuild::I64(v) => v.push(n),
        VecBuild::U8(v) => v.push(n as u8),
        VecBuild::Bit(v) => v.push(n != 0),
    }
}

extern "C" fn fz_vec_finalize() -> u64 {
    let b = current_process()
        .vec_builder
        .take()
        .expect("fz_vec_finalize without begin");
    let heap = &mut current_process().heap;
    let p = match b {
        VecBuild::I64(v) => heap.alloc_vec_i64(&v),
        VecBuild::U8(v) => heap.alloc_vec_u8(&v),
        VecBuild::Bit(v) => heap.alloc_vec_bit(&v),
    };
    p as u64
}

/// vec_get(vec, index) -> element as FzValue Int (for I64/U8/Bit).
/// Out-of-bounds returns FzValue::NIL (mirrors Map's missing-key behavior).
extern "C" fn fz_vec_get(vec_bits: u64, index_bits: u64) -> u64 {
    use crate::fz_value::{FzValue, HeapKind};
    let p = FzValue(vec_bits)
        .unbox_ptr()
        .expect("fz_vec_get: vec not a heap ptr");
    let header = unsafe { &*p };
    let i = FzValue(index_bits)
        .unbox_int()
        .expect("fz_vec_get: index not Int") as usize;
    let len = crate::heap::Heap::vec_len(p) as usize;
    if i >= len {
        return FzValue::NIL.0;
    }
    let payload = unsafe { (p as *const u8).add(24) };
    let n: i64 = match HeapKind::from_u16(header.kind) {
        Some(HeapKind::VecI64) => unsafe {
            std::ptr::read((payload as *const i64).add(i))
        },
        Some(HeapKind::VecU8) => unsafe { *payload.add(i) as i64 },
        Some(HeapKind::VecBit) => {
            let byte_idx = i / 8;
            let bit_idx = 7 - (i % 8);
            let byte = unsafe { *payload.add(byte_idx) };
            ((byte >> bit_idx) & 1) as i64
        }
        Some(HeapKind::VecF64) => panic!("VecF64 deferred to fz-ul4.11.23"),
        _ => panic!("fz_vec_get on non-vec heap kind"),
    };
    FzValue::from_int(n).0
}

// ----- Closure runtime fns -----
//
// Closures are heap objects (HeapKind::Closure) holding [...captured FzValues].
// `header.schema_id` is repurposed to hold the IR fn id of the lambda body.
// `header.flags` holds the captured count (u16). The trampoline never sees
// closure headers — it dispatches off frame headers — so the schema_id reuse
// is safe and avoids registering a per-fn closure schema.
//
// Construction is staged via TLS: begin(fn_id) -> push(v) ×n -> finalize().
// Invocation is staged via TLS args: arg(v) ×n -> invoke(closure, cont_ptr)
// returns the callee frame ptr. TailCallClosure uses the same staging plus a
// frame-reuse path when the closure's fn shares the caller's schema (fn_id
// equality).

// CLOSURE_BUILDER + CLOSURE_ARGS + FRAME_SIZES state moved to Process fields
// (per fz-ul4.11.32). frame_sizes is copied into Process at make_process()
// time from CompiledModule's compile-time table.

extern "C" fn fz_closure_begin(fn_id: u32) {
    current_process().closure_builder = Some((fn_id, Vec::new()));
}

extern "C" fn fz_closure_push(v: u64) {
    current_process()
        .closure_builder
        .as_mut()
        .expect("fz_closure_push without begin")
        .1
        .push(v);
}

extern "C" fn fz_closure_finalize() -> u64 {
    use crate::fz_value::FzValue;
    let (fn_id, captured) = current_process()
        .closure_builder
        .take()
        .expect("fz_closure_finalize without begin");
    let cap_fz: Vec<FzValue> = captured.into_iter().map(FzValue).collect();
    let p = current_process().heap.alloc_closure(fn_id, &cap_fz);
    p as u64
}

extern "C" fn fz_closure_arg(v: u64) {
    current_process().closure_args.push(v);
}

/// Allocate a frame for fn `fn_id`, looking up its size in the current
/// Process's frame_sizes table populated at make_process() time.
extern "C" fn fz_alloc_frame_dyn(fn_id: u32) -> *mut u8 {
    let size = *current_process()
        .frame_sizes
        .get(fn_id as usize)
        .unwrap_or_else(|| panic!("frame_sizes has no entry for fn_id {}", fn_id));
    fz_alloc_frame(fn_id, size)
}

/// Build a callee frame for `closure` invocation:
///   frame[16] = cont_ptr
///   frame[24..24+cap*8]   = closure.captured
///   frame[24+cap*8..]     = staged args (consumed from CLOSURE_ARGS)
/// Returns the callee frame ptr for the trampoline to invoke next.
extern "C" fn fz_closure_invoke(closure_bits: u64, cont_ptr: u64) -> *mut u8 {
    use crate::fz_value::FzValue;
    let cp = FzValue(closure_bits)
        .unbox_ptr()
        .expect("fz_closure_invoke: closure not a heap ptr");
    let header = unsafe { &*cp };
    let fn_id = header.schema_id;
    let captured_count = header.flags as usize;
    let frame = fz_alloc_frame_dyn(fn_id);
    let args = std::mem::take(&mut current_process().closure_args);
    unsafe {
        std::ptr::write((frame as *mut u8).add(16) as *mut u64, cont_ptr);
        let cap_src = (cp as *const u8).add(16) as *const u64;
        let frame_slots = (frame as *mut u8).add(24) as *mut u64;
        std::ptr::copy_nonoverlapping(cap_src, frame_slots, captured_count);
        for (i, v) in args.iter().enumerate() {
            std::ptr::write(frame_slots.add(captured_count + i), *v);
        }
    }
    frame
}

/// Tail-call a closure. If the closure's fn_id matches the caller's frame
/// schema_id, overwrite the caller's frame in place (cont_ptr stays).
/// Otherwise allocate a fresh frame and copy the cont_ptr from the caller's.
extern "C" fn fz_tail_closure(closure_bits: u64, current_frame: *mut u8) -> *mut u8 {
    use crate::fz_value::{FzValue, HeapHeader};
    let cp = FzValue(closure_bits)
        .unbox_ptr()
        .expect("fz_tail_closure: closure not a heap ptr");
    let header = unsafe { &*cp };
    let fn_id = header.schema_id;
    let captured_count = header.flags as usize;
    let cur_header = unsafe { &*(current_frame as *const HeapHeader) };
    let cur_fn_id = cur_header.schema_id;
    let args = std::mem::take(&mut current_process().closure_args);
    let cap_src = unsafe { (cp as *const u8).add(16) as *const u64 };

    if cur_fn_id == fn_id {
        unsafe {
            let frame_slots = current_frame.add(24) as *mut u64;
            std::ptr::copy_nonoverlapping(cap_src, frame_slots, captured_count);
            for (i, v) in args.iter().enumerate() {
                std::ptr::write(frame_slots.add(captured_count + i), *v);
            }
        }
        current_frame
    } else {
        let frame = fz_alloc_frame_dyn(fn_id);
        unsafe {
            let old_cont = std::ptr::read(current_frame.add(16) as *const u64);
            std::ptr::write(frame.add(16) as *mut u64, old_cont);
            let frame_slots = frame.add(24) as *mut u64;
            std::ptr::copy_nonoverlapping(cap_src, frame_slots, captured_count);
            for (i, v) in args.iter().enumerate() {
                std::ptr::write(frame_slots.add(captured_count + i), *v);
            }
        }
        frame
    }
}

extern "C" fn fz_alloc_frame(schema_id: u32, total_size: u32) -> *mut u8 {
    use std::alloc::{alloc_zeroed, Layout};
    // Round size up to a multiple of 16 to keep allocator happy and ensure
    // the resulting block aligns whatever follows.
    let rounded = ((total_size as usize) + 15) & !15;
    let layout = Layout::from_size_align(rounded, 16).expect("bad frame layout");
    let p = unsafe { alloc_zeroed(layout) };
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe {
        let hp = p as *mut crate::fz_value::HeapHeader;
        (*hp) = crate::fz_value::HeapHeader {
            kind: 0, // Struct
            flags: 0,
            size_bytes: total_size,
            schema_id,
            _reserved: 0,
        };
    }
    p
}

// ---------------------------------------------------------------------------
// Compiler
// ---------------------------------------------------------------------------

fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

/// Build a [cont_ptr, ...entry_params] schema for a fn. All FzValue slots.
fn build_frame_schema(name: &str, num_entry_params: usize) -> Schema {
    let n_fields = 1 + num_entry_params;
    let mut fields = Vec::with_capacity(n_fields);
    for i in 0..n_fields {
        fields.push(FieldDescriptor {
            offset: (i * SLOT_BYTES as usize) as u32,
            kind: FieldKind::FzValue,
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: HEADER_SIZE as u32 + (n_fields as u32) * SLOT_BYTES as u32,
        fields,
    }
}

pub fn compile(module: &Module) -> Result<CompiledModule, CodegenError> {
    // Compute per-fn schemas indexed by FnId.0 (cps_split inserts continuation
    // fns out of declaration order, so module.fns[i].id.0 != i in general).
    let max_id = module.fns.iter().map(|f| f.id.0).max().unwrap_or(0);
    let placeholder = build_frame_schema("__placeholder", 0);
    let mut schemas: Vec<Schema> = vec![placeholder; (max_id + 1) as usize];
    for f in &module.fns {
        let entry_block = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        let n_params = entry_block.params.len();
        schemas[f.id.0 as usize] = build_frame_schema(&f.name, n_params);
    }

    let isa = host_isa();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    builder.symbol("fz_print_value", fz_print_value as *const u8);
    builder.symbol("fz_halt", fz_halt as *const u8);
    builder.symbol("fz_alloc_frame", fz_alloc_frame as *const u8);
    builder.symbol("fz_alloc_list_cons", fz_alloc_list_cons as *const u8);
    builder.symbol("fz_alloc_struct", fz_alloc_struct as *const u8);
    builder.symbol("fz_bs_begin", fz_bs_begin as *const u8);
    builder.symbol("fz_bs_write_field", fz_bs_write_field as *const u8);
    builder.symbol("fz_bs_finalize", fz_bs_finalize as *const u8);
    builder.symbol("fz_bs_reader_init", fz_bs_reader_init as *const u8);
    builder.symbol("fz_bs_read_field", fz_bs_read_field as *const u8);
    builder.symbol("fz_map_begin", fz_map_begin as *const u8);
    builder.symbol("fz_map_clone", fz_map_clone as *const u8);
    builder.symbol("fz_map_push", fz_map_push as *const u8);
    builder.symbol("fz_map_finalize", fz_map_finalize as *const u8);
    builder.symbol("fz_map_get", fz_map_get as *const u8);
    builder.symbol("fz_alloc_float", fz_alloc_float as *const u8);
    builder.symbol("fz_arith_add", fz_arith_add as *const u8);
    builder.symbol("fz_arith_sub", fz_arith_sub as *const u8);
    builder.symbol("fz_arith_mul", fz_arith_mul as *const u8);
    builder.symbol("fz_arith_div", fz_arith_div as *const u8);
    builder.symbol("fz_arith_mod", fz_arith_mod as *const u8);
    builder.symbol("fz_cmp_lt", fz_cmp_lt as *const u8);
    builder.symbol("fz_cmp_le", fz_cmp_le as *const u8);
    builder.symbol("fz_cmp_gt", fz_cmp_gt as *const u8);
    builder.symbol("fz_cmp_ge", fz_cmp_ge as *const u8);
    builder.symbol("fz_value_eq", fz_value_eq as *const u8);
    builder.symbol("fz_vec_begin", fz_vec_begin as *const u8);
    builder.symbol("fz_vec_push", fz_vec_push as *const u8);
    builder.symbol("fz_vec_finalize", fz_vec_finalize as *const u8);
    builder.symbol("fz_vec_get", fz_vec_get as *const u8);
    builder.symbol("fz_closure_begin", fz_closure_begin as *const u8);
    builder.symbol("fz_closure_push", fz_closure_push as *const u8);
    builder.symbol("fz_closure_finalize", fz_closure_finalize as *const u8);
    builder.symbol("fz_closure_arg", fz_closure_arg as *const u8);
    builder.symbol("fz_closure_invoke", fz_closure_invoke as *const u8);
    builder.symbol("fz_tail_closure", fz_tail_closure as *const u8);
    let mut jmod = JITModule::new(builder);

    // Declare runtime imports.
    let print_sig = sig1(&[types::I64], &[]);
    let print_id = jmod
        .declare_function("fz_print_value", Linkage::Import, &print_sig)
        .map_err(|e| CodegenError::new(format!("declare print: {}", e)))?;
    let halt_sig = sig1(&[types::I64, types::I64], &[]);
    let halt_id = jmod
        .declare_function("fz_halt", Linkage::Import, &halt_sig)
        .map_err(|e| CodegenError::new(format!("declare halt: {}", e)))?;
    let alloc_sig = sig1(&[types::I32, types::I32], &[types::I64]);
    let alloc_id = jmod
        .declare_function("fz_alloc_frame", Linkage::Import, &alloc_sig)
        .map_err(|e| CodegenError::new(format!("declare alloc: {}", e)))?;
    let alloc_cons_sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let alloc_cons_id = jmod
        .declare_function("fz_alloc_list_cons", Linkage::Import, &alloc_cons_sig)
        .map_err(|e| CodegenError::new(format!("declare alloc_cons: {}", e)))?;
    let alloc_struct_sig = sig1(&[types::I32], &[types::I64]);
    let alloc_struct_id = jmod
        .declare_function("fz_alloc_struct", Linkage::Import, &alloc_struct_sig)
        .map_err(|e| CodegenError::new(format!("declare alloc_struct: {}", e)))?;
    let bs_begin_sig = sig1(&[], &[]);
    let bs_begin_id = jmod
        .declare_function("fz_bs_begin", Linkage::Import, &bs_begin_sig)
        .map_err(|e| CodegenError::new(format!("declare bs_begin: {}", e)))?;
    let bs_write_sig = sig1(
        &[
            types::I64, // value bits
            types::I32, // ty tag
            types::I32, // size_present
            types::I32, // size_value
            types::I32, // unit
            types::I32, // endian
            types::I32, // signed
        ],
        &[],
    );
    let bs_write_id = jmod
        .declare_function("fz_bs_write_field", Linkage::Import, &bs_write_sig)
        .map_err(|e| CodegenError::new(format!("declare bs_write_field: {}", e)))?;
    let bs_finalize_sig = sig1(&[], &[types::I64]);
    let bs_finalize_id = jmod
        .declare_function("fz_bs_finalize", Linkage::Import, &bs_finalize_sig)
        .map_err(|e| CodegenError::new(format!("declare bs_finalize: {}", e)))?;
    let bs_reader_init_sig = sig1(&[types::I64], &[types::I64]);
    let bs_reader_init_id = jmod
        .declare_function("fz_bs_reader_init", Linkage::Import, &bs_reader_init_sig)
        .map_err(|e| CodegenError::new(format!("declare bs_reader_init: {}", e)))?;
    let bs_read_field_sig = sig1(
        &[
            types::I64, // reader bits
            types::I32, // ty tag
            types::I32, // size_present
            types::I32, // size_value
            types::I32, // unit
            types::I32, // endian
            types::I32, // signed
            types::I32, // is_last
        ],
        &[types::I64],
    );
    let bs_read_field_id = jmod
        .declare_function("fz_bs_read_field", Linkage::Import, &bs_read_field_sig)
        .map_err(|e| CodegenError::new(format!("declare bs_read_field: {}", e)))?;
    let map_begin_sig = sig1(&[], &[]);
    let map_begin_id = jmod
        .declare_function("fz_map_begin", Linkage::Import, &map_begin_sig)
        .map_err(|e| CodegenError::new(format!("declare map_begin: {}", e)))?;
    let map_clone_sig = sig1(&[types::I64], &[]);
    let map_clone_id = jmod
        .declare_function("fz_map_clone", Linkage::Import, &map_clone_sig)
        .map_err(|e| CodegenError::new(format!("declare map_clone: {}", e)))?;
    let map_push_sig = sig1(&[types::I64, types::I64], &[]);
    let map_push_id = jmod
        .declare_function("fz_map_push", Linkage::Import, &map_push_sig)
        .map_err(|e| CodegenError::new(format!("declare map_push: {}", e)))?;
    let map_finalize_sig = sig1(&[], &[types::I64]);
    let map_finalize_id = jmod
        .declare_function("fz_map_finalize", Linkage::Import, &map_finalize_sig)
        .map_err(|e| CodegenError::new(format!("declare map_finalize: {}", e)))?;
    let map_get_sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let map_get_id = jmod
        .declare_function("fz_map_get", Linkage::Import, &map_get_sig)
        .map_err(|e| CodegenError::new(format!("declare map_get: {}", e)))?;
    let alloc_float_sig = sig1(&[types::I64], &[types::I64]);
    let alloc_float_id = jmod
        .declare_function("fz_alloc_float", Linkage::Import, &alloc_float_sig)
        .map_err(|e| CodegenError::new(format!("declare alloc_float: {}", e)))?;
    let arith_sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let arith_add_id = jmod
        .declare_function("fz_arith_add", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare arith_add: {}", e)))?;
    let arith_sub_id = jmod
        .declare_function("fz_arith_sub", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare arith_sub: {}", e)))?;
    let arith_mul_id = jmod
        .declare_function("fz_arith_mul", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare arith_mul: {}", e)))?;
    let arith_div_id = jmod
        .declare_function("fz_arith_div", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare arith_div: {}", e)))?;
    let arith_mod_id = jmod
        .declare_function("fz_arith_mod", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare arith_mod: {}", e)))?;
    let cmp_lt_id = jmod
        .declare_function("fz_cmp_lt", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare cmp_lt: {}", e)))?;
    let cmp_le_id = jmod
        .declare_function("fz_cmp_le", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare cmp_le: {}", e)))?;
    let cmp_gt_id = jmod
        .declare_function("fz_cmp_gt", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare cmp_gt: {}", e)))?;
    let cmp_ge_id = jmod
        .declare_function("fz_cmp_ge", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare cmp_ge: {}", e)))?;
    let value_eq_id = jmod
        .declare_function("fz_value_eq", Linkage::Import, &arith_sig)
        .map_err(|e| CodegenError::new(format!("declare value_eq: {}", e)))?;
    let vec_begin_sig = sig1(&[types::I32], &[]);
    let vec_begin_id = jmod
        .declare_function("fz_vec_begin", Linkage::Import, &vec_begin_sig)
        .map_err(|e| CodegenError::new(format!("declare vec_begin: {}", e)))?;
    let vec_push_sig = sig1(&[types::I64], &[]);
    let vec_push_id = jmod
        .declare_function("fz_vec_push", Linkage::Import, &vec_push_sig)
        .map_err(|e| CodegenError::new(format!("declare vec_push: {}", e)))?;
    let vec_finalize_sig = sig1(&[], &[types::I64]);
    let vec_finalize_id = jmod
        .declare_function("fz_vec_finalize", Linkage::Import, &vec_finalize_sig)
        .map_err(|e| CodegenError::new(format!("declare vec_finalize: {}", e)))?;
    let vec_get_sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let vec_get_id = jmod
        .declare_function("fz_vec_get", Linkage::Import, &vec_get_sig)
        .map_err(|e| CodegenError::new(format!("declare vec_get: {}", e)))?;
    let closure_begin_sig = sig1(&[types::I32], &[]);
    let closure_begin_id = jmod
        .declare_function("fz_closure_begin", Linkage::Import, &closure_begin_sig)
        .map_err(|e| CodegenError::new(format!("declare closure_begin: {}", e)))?;
    let closure_push_sig = sig1(&[types::I64], &[]);
    let closure_push_id = jmod
        .declare_function("fz_closure_push", Linkage::Import, &closure_push_sig)
        .map_err(|e| CodegenError::new(format!("declare closure_push: {}", e)))?;
    let closure_finalize_sig = sig1(&[], &[types::I64]);
    let closure_finalize_id = jmod
        .declare_function("fz_closure_finalize", Linkage::Import, &closure_finalize_sig)
        .map_err(|e| CodegenError::new(format!("declare closure_finalize: {}", e)))?;
    let closure_arg_sig = sig1(&[types::I64], &[]);
    let closure_arg_id = jmod
        .declare_function("fz_closure_arg", Linkage::Import, &closure_arg_sig)
        .map_err(|e| CodegenError::new(format!("declare closure_arg: {}", e)))?;
    let closure_invoke_sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let closure_invoke_id = jmod
        .declare_function("fz_closure_invoke", Linkage::Import, &closure_invoke_sig)
        .map_err(|e| CodegenError::new(format!("declare closure_invoke: {}", e)))?;
    let tail_closure_sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let tail_closure_id = jmod
        .declare_function("fz_tail_closure", Linkage::Import, &tail_closure_sig)
        .map_err(|e| CodegenError::new(format!("declare tail_closure: {}", e)))?;

    // Per-fn signature: extern "C" fn(*mut u8, *mut u8) -> *mut u8.
    let fn_sig = sig1(&[types::I64, types::I64], &[types::I64]);

    // Declare every fn first so call sites can reference each other.
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for f in &module.fns {
        let name = format!("fz_fn_{}", f.id.0);
        let id = jmod
            .declare_function(&name, Linkage::Local, &fn_sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(f.id.0, id);
    }

    let mut fbctx = FunctionBuilderContext::new();
    let runtime = RuntimeRefs {
        print_id,
        halt_id,
        alloc_id,
        alloc_cons_id,
        alloc_struct_id,
        bs_begin_id,
        bs_write_id,
        bs_finalize_id,
        bs_reader_init_id,
        bs_read_field_id,
        map_begin_id,
        map_clone_id,
        map_push_id,
        map_finalize_id,
        map_get_id,
        closure_begin_id,
        closure_push_id,
        closure_finalize_id,
        closure_arg_id,
        closure_invoke_id,
        tail_closure_id,
        vec_begin_id,
        vec_push_id,
        vec_finalize_id,
        vec_get_id,
        alloc_float_id,
        arith_add_id,
        arith_sub_id,
        arith_mul_id,
        arith_div_id,
        arith_mod_id,
        cmp_lt_id,
        cmp_le_id,
        cmp_gt_id,
        cmp_ge_id,
        value_eq_id,
    };

    // Register a heap Schema for every tuple arity used by MakeTuple, so the
    // GC tracer can walk fields and so codegen can iconst the schema_id.
    // Also detect any bitstring prim so we can pre-register arity-1 / arity-3
    // schemas used by the reader / result tuples even if no MakeTuple uses
    // those arities directly.
    let mut tuple_arities: std::collections::HashSet<usize> =
        std::collections::HashSet::new();
    let mut has_bs_prim = false;
    for f in &module.fns {
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                match prim {
                    Prim::MakeTuple(args) => {
                        tuple_arities.insert(args.len());
                    }
                    Prim::MakeBitstring(_)
                    | Prim::BitReaderInit(_)
                    | Prim::BitReadField { .. }
                    | Prim::BitReaderDone(_) => {
                        has_bs_prim = true;
                    }
                    _ => {}
                }
            }
        }
    }
    if has_bs_prim {
        tuple_arities.insert(1);
        tuple_arities.insert(3);
    }
    // Build the per-CompiledModule SchemaRegistry. Tuple, struct, list,
    // map, closure, bitstring, vec, float schemas live here. Each Process
    // constructed via make_process() shares this registry through its Heap.
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        crate::heap::SchemaRegistry::new(),
    ));
    let mut tuple_schema_ids: HashMap<usize, u32> = HashMap::new();
    {
        let mut reg = user_schemas.borrow_mut();
        for &arity in &tuple_arities {
            let s = Schema {
                name: format!("Tuple{}", arity),
                size: (arity * 8) as u32,
                fields: (0..arity)
                    .map(|i| FieldDescriptor {
                        offset: (i * 8) as u32,
                        kind: FieldKind::FzValue,
                    })
                    .collect(),
            };
            let id = reg.register(s);
            tuple_schema_ids.insert(arity, id);
        }
    }
    let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = if has_bs_prim {
        (
            Some(*tuple_schema_ids.get(&1).expect("arity-1 schema registered")),
            Some(*tuple_schema_ids.get(&3).expect("arity-3 schema registered")),
        )
    } else {
        (None, None)
    };

    // Per-fn frame sizes for `fz_alloc_frame_dyn`. Indexed by FnId.0
    // (parallel to `schemas`). Copied into Process at make_process() time.
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.size).collect();

    // .11.24.4: run the typer ahead of codegen so per-fn Var->Descr info is
    // available during lowering (used for arithmetic dispatch elision when
    // both operands are provably Int).
    //
    // .11.24.5: clone module so the typed-schema refinement pass can rewrite
    // MakeVec(I64, ..) to MakeVec(F64, ..) when elements are typed Float.
    // Mixed Int+Float without an explicit coercion rule errors here.
    let mut working = module.clone();
    let pre_types = crate::ir_typer::type_module(&working);
    crate::ir_typer::rewrite_vec_kinds(&mut working, &pre_types)
        .map_err(CodegenError::new)?;
    // Re-run after the rewrite so MakeVec result Descrs reflect the chosen
    // kind. Element Var Descrs are unaffected by the rewrite, but downstream
    // consumers may read the MakeVec result.
    let module_types = crate::ir_typer::type_module(&working);
    let module = &working;

    for (fn_idx, f) in module.fns.iter().enumerate() {
        let func_id = *fn_ids.get(&f.id.0).unwrap();
        let mut ctx = jmod.make_context();
        ctx.func.signature = fn_sig.clone();
        compile_fn(
            &mut jmod,
            &mut ctx,
            &mut fbctx,
            &runtime,
            &schemas,
            &tuple_schema_ids,
            f,
            &module_types[fn_idx],
        )?;
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                v.push((f.name.clone(), ctx.func.display().to_string()));
            }
        });
        let fn_span = module.source.fn_span_of(f.id);
        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
            .map_err(|e| CodegenError::new(format!("verify {}:\n{}\n--- IR ---\n{}", f.name, e, ctx.func.display())).with_span(fn_span))?;
        jmod
            .define_function(func_id, &mut ctx)
            .map_err(|e| CodegenError::new(format!("define {}: {}", f.name, e)).with_span(fn_span))?;
        jmod.clear_context(&mut ctx);
    }

    jmod.finalize_definitions().map_err(|e| CodegenError::new(format!("finalize: {}", e)))?;

    let mut fn_ptrs: HashMap<u32, *const u8> = HashMap::new();
    for (fz_fn_id, func_id) in &fn_ids {
        fn_ptrs.insert(*fz_fn_id, jmod.get_finalized_function(*func_id));
    }

    let diagnostics = crate::ir_typer::collect_diagnostics(module, &module_types);
    Ok(CompiledModule {
        module: jmod,
        fn_ptrs,
        schemas,
        user_schemas,
        frame_sizes,
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
        types: module_types,
        diagnostics,
    })
}

fn sig1(params: &[ir::Type], rets: &[ir::Type]) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for p in params { s.params.push(AbiParam::new(*p)); }
    for r in rets { s.returns.push(AbiParam::new(*r)); }
    s
}

#[derive(Clone, Copy)]
struct RuntimeRefs {
    print_id: FuncId,
    halt_id: FuncId,
    alloc_id: FuncId,
    alloc_cons_id: FuncId,
    alloc_struct_id: FuncId,
    bs_begin_id: FuncId,
    bs_write_id: FuncId,
    bs_finalize_id: FuncId,
    bs_reader_init_id: FuncId,
    bs_read_field_id: FuncId,
    map_begin_id: FuncId,
    map_clone_id: FuncId,
    map_push_id: FuncId,
    map_finalize_id: FuncId,
    map_get_id: FuncId,
    closure_begin_id: FuncId,
    closure_push_id: FuncId,
    closure_finalize_id: FuncId,
    closure_arg_id: FuncId,
    closure_invoke_id: FuncId,
    tail_closure_id: FuncId,
    vec_begin_id: FuncId,
    vec_push_id: FuncId,
    vec_finalize_id: FuncId,
    vec_get_id: FuncId,
    alloc_float_id: FuncId,
    arith_add_id: FuncId,
    arith_sub_id: FuncId,
    arith_mul_id: FuncId,
    arith_div_id: FuncId,
    arith_mod_id: FuncId,
    cmp_lt_id: FuncId,
    cmp_le_id: FuncId,
    cmp_gt_id: FuncId,
    cmp_ge_id: FuncId,
    value_eq_id: FuncId,
}

fn compile_fn(
    jmod: &mut JITModule,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    tuple_schema_ids: &HashMap<usize, u32>,
    f: &crate::fz_ir::FnIr,
    fn_types: &crate::ir_typer::FnTypes,
) -> Result<(), CodegenError> {
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    let mut block_map: HashMap<u32, ir::Block> = HashMap::new();
    for blk in &f.blocks {
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    b.append_block_param(entry_cl, types::I64); // frame_ptr
    b.append_block_param(entry_cl, types::I64); // host_ctx

    for blk in &f.blocks {
        if blk.id == f.entry { continue; }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for _ in &blk.params {
            b.append_block_param(cl_blk, types::I64);
        }
    }

    b.switch_to_block(entry_cl);
    b.seal_block(entry_cl);

    let frame_ptr = b.block_params(entry_cl)[0];
    let host_ctx = b.block_params(entry_cl)[1];

    // Load entry params from frame slots [1..N+1] (offsets 24, 32, ...).
    let mut var_map: HashMap<u32, ir::Value> = HashMap::new();
    let entry_blk = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    for (i, p) in entry_blk.params.iter().enumerate() {
        let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
        let val = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, off);
        var_map.insert(p.0, val);
    }

    // Walk blocks in declared order with entry first.
    let mut order: Vec<&crate::fz_ir::Block> = Vec::with_capacity(f.blocks.len());
    if let Some(eb) = f.blocks.iter().find(|b| b.id == f.entry) {
        order.push(eb);
    }
    for blk in &f.blocks {
        if blk.id != f.entry { order.push(blk); }
    }

    for blk in &order {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.switch_to_block(cl_blk);
            let params: Vec<ir::Value> = b.block_params(cl_blk).iter().copied().collect();
            for (p, val) in blk.params.iter().zip(params.iter()) {
                var_map.insert(p.0, *val);
            }
        }

        for stmt in &blk.stmts {
            let Stmt::Let(v, prim) = stmt;
            let val = lower_prim(&mut b, jmod, runtime, tuple_schema_ids, &var_map, fn_types, prim)?;
            var_map.insert(v.0, val);
        }

        match &blk.terminator {
            Term::Goto(target, args) => {
                let tgt = *block_map.get(&target.0).unwrap();
                let arg_vals: Vec<BlockArg> = args
                    .iter()
                    .map(|v| BlockArg::Value(*var_map.get(&v.0).expect("unbound goto arg")))
                    .collect();
                b.ins().jump(tgt, &arg_vals);
            }
            Term::If(c, t, e) => {
                let cv = *var_map.get(&c.0).expect("unbound if cond");
                let t_b = *block_map.get(&t.0).unwrap();
                let e_b = *block_map.get(&e.0).unwrap();
                let no_args: Vec<BlockArg> = Vec::new();
                let truthy = is_truthy(&mut b, cv);
                b.ins().brif(truthy, t_b, &no_args, e_b, &no_args);
            }
            Term::Halt(v) => {
                let val = *var_map.get(&v.0).expect("unbound halt val");
                let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                b.ins().call(halt_fref, &[host_ctx, val]);
                let null = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[null]);
            }
            Term::Return(v) => {
                let val = *var_map.get(&v.0).expect("unbound return val");
                emit_return(&mut b, jmod, runtime, frame_ptr, host_ctx, val);
            }
            Term::Call { callee, args, continuation } => {
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound call arg"))
                    .collect();
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound captured val"))
                    .collect();
                emit_call(
                    &mut b,
                    jmod,
                    runtime,
                    schemas,
                    frame_ptr,
                    callee.0,
                    &arg_vals,
                    Some((continuation.fn_id.0, &cap_vals)),
                );
            }
            Term::TailCall { callee, args } => {
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound tailcall arg"))
                    .collect();
                emit_tail_call(
                    &mut b,
                    jmod,
                    runtime,
                    schemas,
                    f.id.0,
                    frame_ptr,
                    callee.0,
                    &arg_vals,
                );
            }
            Term::CallClosure { closure, args, continuation } => {
                let cl_val = *var_map.get(&closure.0).expect("unbound callclosure closure");
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound callclosure arg"))
                    .collect();
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound captured val"))
                    .collect();
                emit_call_closure(
                    &mut b,
                    jmod,
                    runtime,
                    schemas,
                    frame_ptr,
                    cl_val,
                    &arg_vals,
                    continuation.fn_id.0,
                    &cap_vals,
                );
            }
            Term::TailCallClosure { closure, args } => {
                let cl_val = *var_map.get(&closure.0).expect("unbound tailcallclosure closure");
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound tailcallclosure arg"))
                    .collect();
                emit_tail_call_closure(&mut b, jmod, runtime, frame_ptr, cl_val, &arg_vals);
            }
        }
    }

    for blk in &f.blocks {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry { b.seal_block(cl_blk); }
    }
    b.finalize();
    Ok(())
}

/// Term::Return: load my cont_ptr from frame[16]. If null, halt.
/// Otherwise write `val` to cont_frame[24] (continuation's "result" slot —
/// always entry param 0) and return cont_ptr.
fn emit_return(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    frame_ptr: ir::Value,
    host_ctx: ir::Value,
    val: ir::Value,
) {
    let cont_ptr = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
    let zero = b.ins().iconst(types::I64, 0);
    let is_null = b.ins().icmp(IntCC::Equal, cont_ptr, zero);

    let halt_blk = b.create_block();
    let invoke_blk = b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins().brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);

    // halt: fz_halt(host_ctx, val); return null.
    b.switch_to_block(halt_blk);
    b.seal_block(halt_blk);
    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
    b.ins().call(halt_fref, &[host_ctx, val]);
    let null = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[null]);

    // invoke: write val to cont[24], return cont_ptr.
    b.switch_to_block(invoke_blk);
    b.seal_block(invoke_blk);
    let result_off = HEADER_SIZE + SLOT_BYTES;
    b.ins().store(MemFlags::trusted(), val, cont_ptr, result_off);
    b.ins().return_(&[cont_ptr]);
}

/// Term::Call: allocate continuation frame + callee frame. Continuation
/// frame = [my_cont_ptr, result_placeholder, ...captured]. Callee frame =
/// [cont_frame_ptr, ...args]. Return callee frame ptr.
fn emit_call(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: ir::Value,
    callee_id: u32,
    args: &[ir::Value],
    cont: Option<(u32, &[ir::Value])>,
) {
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

    // Read my cont_ptr from current frame[16] — this becomes the cont frame's cont_ptr.
    let my_cont = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

    let cont_frame_val = match cont {
        Some((cont_fn_id, captured)) => {
            let cont_schema = &schemas[cont_fn_id as usize];
            let sid = b.ins().iconst(types::I32, cont_fn_id as i64);
            let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
            let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
            let cf = b.inst_results(call_inst)[0];
            // Slot 0 (offset 16): cont_ptr = my_cont (my own continuation).
            b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
            // Slot 1 (offset 24) is the continuation's "result" param —
            // left uninitialized; will be filled by callee's Term::Return.
            // Slots 2..K+2: captured vars in declaration order.
            for (i, cv) in captured.iter().enumerate() {
                let off = HEADER_SIZE + SLOT_BYTES * (2 + i as i32);
                b.ins().store(MemFlags::trusted(), *cv, cf, off);
            }
            cf
        }
        None => my_cont,
    };

    // Allocate callee frame.
    let callee_schema = &schemas[callee_id as usize];
    let sid = b.ins().iconst(types::I32, callee_id as i64);
    let sz = b.ins().iconst(types::I32, callee_schema.size as i64);
    let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
    let callee_frame = b.inst_results(call_inst)[0];
    // Slot 0: cont_ptr = cont_frame_val.
    b.ins().store(MemFlags::trusted(), cont_frame_val, callee_frame, HEADER_SIZE);
    // Slots 1..N+1: args.
    for (i, av) in args.iter().enumerate() {
        let off = HEADER_SIZE + SLOT_BYTES * (1 + i as i32);
        b.ins().store(MemFlags::trusted(), *av, callee_frame, off);
    }

    b.ins().return_(&[callee_frame]);
}

/// Term::TailCall: if callee shares schema with caller, overwrite caller's
/// frame in place. Otherwise allocate a new frame. Either way, cont_ptr is
/// preserved (the parent's continuation).
fn emit_tail_call(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    self_id: u32,
    frame_ptr: ir::Value,
    callee_id: u32,
    args: &[ir::Value],
) {
    let callee_schema = &schemas[callee_id as usize];

    if self_id == callee_id {
        // Same schema: overwrite slots 1..N+1 with new args. Slot 0 (cont) stays.
        for (i, av) in args.iter().enumerate() {
            let off = HEADER_SIZE + SLOT_BYTES * (1 + i as i32);
            b.ins().store(MemFlags::trusted(), *av, frame_ptr, off);
        }
        b.ins().return_(&[frame_ptr]);
    } else {
        // Different schema: alloc fresh, copy cont_ptr, write args.
        let my_cont = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
        let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
        let sid = b.ins().iconst(types::I32, callee_id as i64);
        let sz = b.ins().iconst(types::I32, callee_schema.size as i64);
        let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
        let nf = b.inst_results(call_inst)[0];
        b.ins().store(MemFlags::trusted(), my_cont, nf, HEADER_SIZE);
        for (i, av) in args.iter().enumerate() {
            let off = HEADER_SIZE + SLOT_BYTES * (1 + i as i32);
            b.ins().store(MemFlags::trusted(), *av, nf, off);
        }
        b.ins().return_(&[nf]);
    }
}

/// Term::CallClosure: build the continuation frame the same way as Term::Call,
/// stage args via fz_closure_arg(), then call fz_closure_invoke(closure,
/// cont_frame_ptr) which returns the callee frame ptr.
fn emit_call_closure(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: ir::Value,
    closure_val: ir::Value,
    args: &[ir::Value],
    cont_fn_id: u32,
    captured: &[ir::Value],
) {
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
    let my_cont = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

    // Build continuation frame: [my_cont, result_placeholder, ...captured].
    let cont_schema = &schemas[cont_fn_id as usize];
    let sid = b.ins().iconst(types::I32, cont_fn_id as i64);
    let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
    let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
    let cf = b.inst_results(call_inst)[0];
    b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
    for (i, cv) in captured.iter().enumerate() {
        let off = HEADER_SIZE + SLOT_BYTES * (2 + i as i32);
        b.ins().store(MemFlags::trusted(), *cv, cf, off);
    }

    // Stage args, then invoke.
    let arg_fref = jmod.declare_func_in_func(runtime.closure_arg_id, b.func);
    for av in args {
        b.ins().call(arg_fref, &[*av]);
    }
    let invoke_fref = jmod.declare_func_in_func(runtime.closure_invoke_id, b.func);
    let inv = b.ins().call(invoke_fref, &[closure_val, cf]);
    let callee_frame = b.inst_results(inv)[0];
    b.ins().return_(&[callee_frame]);
}

/// Term::TailCallClosure: stage args, then call fz_tail_closure(closure,
/// current_frame). Runtime fn handles same-fn-id frame reuse vs. fresh alloc.
fn emit_tail_call_closure(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    frame_ptr: ir::Value,
    closure_val: ir::Value,
    args: &[ir::Value],
) {
    let arg_fref = jmod.declare_func_in_func(runtime.closure_arg_id, b.func);
    for av in args {
        b.ins().call(arg_fref, &[*av]);
    }
    let tail_fref = jmod.declare_func_in_func(runtime.tail_closure_id, b.func);
    let inv = b.ins().call(tail_fref, &[closure_val, frame_ptr]);
    let callee_frame = b.inst_results(inv)[0];
    b.ins().return_(&[callee_frame]);
}

/// True when `v`'s typer-inferred Descr is a subtype of `int_top` — the
/// arithmetic dispatch elision pre-condition (.11.24.4).
fn descr_is_int(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    fn_types
        .vars
        .get(&v)
        .map(|d| d.is_subtype(&crate::types::Descr::int()))
        .unwrap_or(false)
}

fn lower_prim(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    env: &HashMap<u32, ir::Value>,
    fn_types: &crate::ir_typer::FnTypes,
    prim: &Prim,
) -> Result<ir::Value, CodegenError> {
    Ok(match prim {
        Prim::Const(c) => match c {
            Const::Int(n) => b.ins().iconst(types::I64, ((*n) << 3) | TAG_INT),
            Const::True => b.ins().iconst(types::I64, TRUE_BITS),
            Const::False => b.ins().iconst(types::I64, FALSE_BITS),
            Const::Nil => b.ins().iconst(types::I64, NIL_BITS),
            Const::Atom(id) => b.ins().iconst(types::I64, ((*id as i64) << 3) | TAG_ATOM),
            Const::Float(f) => {
                // Boxed float: emit fz_alloc_float(bits) at runtime. v1 keeps
                // const-pool dedup for a future ticket — correct first.
                let bits = f.to_bits() as i64;
                let bv = b.ins().iconst(types::I64, bits);
                let fref = jmod.declare_func_in_func(runtime.alloc_float_id, b.func);
                let inst = b.ins().call(fref, &[bv]);
                b.inst_results(inst)[0]
            }
            Const::Str(_) => {
                return Err(CodegenError::new("Str codegen lands in a later ticket"));
            }
        },
        Prim::BinOp(op, a, bv) => {
            let av = *env.get(&a.0).expect("unbound binop a");
            let bvv = *env.get(&bv.0).expect("unbound binop b");
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    let mop = *op;
                    let fast = |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                        let ai = unbox_int(b, av);
                        let bi = unbox_int(b, bv);
                        let raw = match mop {
                            BinOp::Add => b.ins().iadd(ai, bi),
                            BinOp::Sub => b.ins().isub(ai, bi),
                            BinOp::Mul => b.ins().imul(ai, bi),
                            BinOp::Div => b.ins().sdiv(ai, bi),
                            BinOp::Mod => b.ins().srem(ai, bi),
                            _ => unreachable!(),
                        };
                        box_int(b, raw)
                    };
                    // .11.24.4: when the typer proves both operands are Int,
                    // skip the dispatch test and helper call site.
                    if descr_is_int(fn_types, *a) && descr_is_int(fn_types, *bv) {
                        fast(b, av, bvv)
                    } else {
                        let helper = match op {
                            BinOp::Add => runtime.arith_add_id,
                            BinOp::Sub => runtime.arith_sub_id,
                            BinOp::Mul => runtime.arith_mul_id,
                            BinOp::Div => runtime.arith_div_id,
                            BinOp::Mod => runtime.arith_mod_id,
                            _ => unreachable!(),
                        };
                        emit_dispatch_binop(b, jmod, helper, av, bvv, fast)
                    }
                }
                BinOp::Eq | BinOp::Neq => {
                    // If both operands are Tag::Ptr, dispatch to fz_value_eq
                    // (structural / float-aware). Otherwise raw bit-eq is
                    // correct: same-tag scalars compare by bits; cross-tag
                    // pairs (e.g. Ptr vs Int) bit-differ -> always false.
                    let cond = both_ptr(b, av, bvv);
                    let fast_blk = b.create_block();
                    let slow_blk = b.create_block();
                    let join_blk = b.create_block();
                    b.append_block_param(join_blk, types::I64);
                    let no_args: Vec<BlockArg> = Vec::new();
                    // both_ptr=true => slow path
                    b.ins().brif(cond, slow_blk, &no_args, fast_blk, &no_args);

                    b.switch_to_block(fast_blk);
                    b.seal_block(fast_blk);
                    let cc = if matches!(op, BinOp::Eq) { IntCC::Equal } else { IntCC::NotEqual };
                    let cmp = b.ins().icmp(cc, av, bvv);
                    let fast_v = bool_to_fz(b, cmp);
                    b.ins().jump(join_blk, &[BlockArg::Value(fast_v)]);

                    b.switch_to_block(slow_blk);
                    b.seal_block(slow_blk);
                    let fref = jmod.declare_func_in_func(runtime.value_eq_id, b.func);
                    let inst = b.ins().call(fref, &[av, bvv]);
                    let eq = b.inst_results(inst)[0];
                    let slow_v = if matches!(op, BinOp::Eq) {
                        eq
                    } else {
                        // Negate: TRUE_BITS xor (TRUE_BITS xor FALSE_BITS) = FALSE_BITS.
                        b.ins().bxor_imm(eq, TRUE_BITS ^ FALSE_BITS)
                    };
                    b.ins().jump(join_blk, &[BlockArg::Value(slow_v)]);

                    b.switch_to_block(join_blk);
                    b.seal_block(join_blk);
                    b.block_params(join_blk)[0]
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    let cc = match op {
                        BinOp::Lt => IntCC::SignedLessThan,
                        BinOp::Le => IntCC::SignedLessThanOrEqual,
                        BinOp::Gt => IntCC::SignedGreaterThan,
                        BinOp::Ge => IntCC::SignedGreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    let fast = move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                        let ai = unbox_int(b, av);
                        let bi = unbox_int(b, bv);
                        let cmp = b.ins().icmp(cc, ai, bi);
                        bool_to_fz(b, cmp)
                    };
                    if descr_is_int(fn_types, *a) && descr_is_int(fn_types, *bv) {
                        fast(b, av, bvv)
                    } else {
                        let helper = match op {
                            BinOp::Lt => runtime.cmp_lt_id,
                            BinOp::Le => runtime.cmp_le_id,
                            BinOp::Gt => runtime.cmp_gt_id,
                            BinOp::Ge => runtime.cmp_ge_id,
                            _ => unreachable!(),
                        };
                        emit_dispatch_binop(b, jmod, helper, av, bvv, fast)
                    }
                }
                BinOp::And => {
                    let at = is_truthy(b, av);
                    let bt = is_truthy(b, bvv);
                    let conj = b.ins().band(at, bt);
                    bool_to_fz(b, conj)
                }
                BinOp::Or => {
                    let at = is_truthy(b, av);
                    let bt = is_truthy(b, bvv);
                    let disj = b.ins().bor(at, bt);
                    bool_to_fz(b, disj)
                }
            }
        }
        Prim::UnOp(op, x) => {
            let xv = *env.get(&x.0).expect("unbound unop x");
            match op {
                UnOp::Neg => {
                    let xi = unbox_int(b, xv);
                    let neg = b.ins().ineg(xi);
                    box_int(b, neg)
                }
                UnOp::Not => {
                    let truthy = is_truthy(b, xv);
                    let zero = b.ins().iconst(types::I8, 0);
                    let inv = b.ins().icmp(IntCC::Equal, truthy, zero);
                    bool_to_fz(b, inv)
                }
            }
        }
        Prim::Builtin(bid, args) => {
            use crate::fz_ir::BuiltinKind;
            let kind = BuiltinKind::from_id(*bid).ok_or_else(|| {
                CodegenError::new(format!("unknown builtin id {}", bid.0))
            })?;
            match kind {
                BuiltinKind::Print => {
                    if args.len() != 1 {
                        return Err(CodegenError::new("print/1 expected"));
                    }
                    let av = *env.get(&args[0].0).expect("unbound print arg");
                    let fref = jmod.declare_func_in_func(runtime.print_id, b.func);
                    b.ins().call(fref, &[av]);
                    // print/1 returns FzValue::NIL — never raw 0 (which would
                    // alias Tag::Ptr null and trip fz_halt's Ptr-deref path).
                    b.ins().iconst(types::I64, NIL_BITS)
                }
                BuiltinKind::VecGet => {
                    if args.len() != 2 {
                        return Err(CodegenError::new("vec_get/2 expected"));
                    }
                    let vv = *env.get(&args[0].0).expect("unbound vec_get vec");
                    let iv = *env.get(&args[1].0).expect("unbound vec_get index");
                    let fref = jmod.declare_func_in_func(runtime.vec_get_id, b.func);
                    let inst = b.ins().call(fref, &[vv, iv]);
                    b.inst_results(inst)[0]
                }
                BuiltinKind::Assert | BuiltinKind::AssertEq | BuiltinKind::AssertNeq => {
                    return Err(CodegenError::new(format!(
                        "builtin {} not yet wired through JIT",
                        kind.name()
                    )));
                }
            }
        }
        Prim::ListCons(h, t) => {
            let hv = *env.get(&h.0).expect("unbound listcons head");
            let tv = *env.get(&t.0).expect("unbound listcons tail");
            let fref = jmod.declare_func_in_func(runtime.alloc_cons_id, b.func);
            let inst = b.ins().call(fref, &[hv, tv]);
            b.inst_results(inst)[0]
        }
        Prim::ListHead(c) => {
            // `c` is FzValue ptr-tagged (tag bits = 000), so `c` is the raw
            // ListCons base address. head sits at byte offset 16 (after
            // HeapHeader); load it as i64 (raw FzValue bits).
            let cv = *env.get(&c.0).expect("unbound listhead cell");
            b.ins().load(types::I64, MemFlags::trusted(), cv, 16)
        }
        Prim::ListTail(c) => {
            let cv = *env.get(&c.0).expect("unbound listtail cell");
            b.ins().load(types::I64, MemFlags::trusted(), cv, 24)
        }
        Prim::ListIsNil(c) => {
            let cv = *env.get(&c.0).expect("unbound listisnil cell");
            let nil_v = b.ins().iconst(types::I64, NIL_BITS);
            let cmp = b.ins().icmp(IntCC::Equal, cv, nil_v);
            bool_to_fz(b, cmp)
        }
        Prim::MakeList(elems, tail) => {
            // Fold right: cons(e0, cons(e1, ..., cons(eN, tail-or-nil))).
            let mut acc = match tail {
                Some(t) => *env.get(&t.0).expect("unbound makelist tail"),
                None => b.ins().iconst(types::I64, NIL_BITS),
            };
            let fref = jmod.declare_func_in_func(runtime.alloc_cons_id, b.func);
            for e in elems.iter().rev() {
                let ev = *env.get(&e.0).expect("unbound makelist elem");
                let inst = b.ins().call(fref, &[ev, acc]);
                acc = b.inst_results(inst)[0];
            }
            acc
        }
        Prim::MakeTuple(elems) => {
            let arity = elems.len();
            let schema_id = *tuple_schema_ids.get(&arity).ok_or_else(|| {
                CodegenError::new(format!(
                    "tuple arity {} not pre-registered (compile() walk missed it?)",
                    arity
                ))
            })?;
            let fref = jmod.declare_func_in_func(runtime.alloc_struct_id, b.func);
            let sid = b.ins().iconst(types::I32, schema_id as i64);
            let inst = b.ins().call(fref, &[sid]);
            let p = b.inst_results(inst)[0];
            for (i, e) in elems.iter().enumerate() {
                let ev = *env.get(&e.0).expect("unbound maketuple elem");
                let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), ev, p, off);
            }
            p
        }
        Prim::TupleField(c, idx) => {
            let cv = *env.get(&c.0).expect("unbound tuplefield cell");
            let off = HEADER_SIZE + (*idx as i32) * SLOT_BYTES;
            b.ins().load(types::I64, MemFlags::trusted(), cv, off)
        }
        Prim::AllocStruct(schema_id, fields) => {
            // schema_id refers to a heap-registered Schema (caller's
            // responsibility). Reused later by .11.13 maps / .11.19 closures /
            // future user records. v1 has no in-tree caller — kept here so the
            // path is exercised by ir_codegen's existing Prim coverage.
            let fref = jmod.declare_func_in_func(runtime.alloc_struct_id, b.func);
            let sid = b.ins().iconst(types::I32, *schema_id as i64);
            let inst = b.ins().call(fref, &[sid]);
            let p = b.inst_results(inst)[0];
            for (i, fv) in fields.iter().enumerate() {
                let v = *env.get(&fv.0).expect("unbound allocstruct field");
                let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), v, p, off);
            }
            p
        }
        Prim::MakeBitstring(fields) => {
            let begin = jmod.declare_func_in_func(runtime.bs_begin_id, b.func);
            b.ins().call(begin, &[]);
            let write = jmod.declare_func_in_func(runtime.bs_write_id, b.func);
            for f in fields {
                let value_v = *env.get(&f.value.0).expect("unbound bs field val");
                let ty_tag = b.ins().iconst(types::I32, encode_bit_type(f.ty) as i64);
                let unit = b
                    .ins()
                    .iconst(types::I32, f.unit.unwrap_or(default_unit_for(f.ty)) as i64);
                let endian = b.ins().iconst(types::I32, encode_endian(f.endian) as i64);
                let signed = b.ins().iconst(types::I32, f.signed as i64);
                let (size_present, size_value) = match &f.size {
                    None => (
                        b.ins().iconst(types::I32, 0),
                        b.ins().iconst(types::I32, 0),
                    ),
                    Some(crate::fz_ir::BitSizeIr::Literal(n)) => (
                        b.ins().iconst(types::I32, 1),
                        b.ins().iconst(types::I32, *n as i64),
                    ),
                    Some(crate::fz_ir::BitSizeIr::Var(v)) => {
                        let raw = *env.get(&v.0).expect("unbound bs size var");
                        // Boxed int -> raw int -> truncate to i32.
                        let unb = unbox_int(b, raw);
                        let truncated = b.ins().ireduce(types::I32, unb);
                        (b.ins().iconst(types::I32, 1), truncated)
                    }
                };
                b.ins().call(
                    write,
                    &[value_v, ty_tag, size_present, size_value, unit, endian, signed],
                );
            }
            let fin = jmod.declare_func_in_func(runtime.bs_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::BitReaderInit(v) => {
            let vv = *env.get(&v.0).expect("unbound reader init src");
            let fref = jmod.declare_func_in_func(runtime.bs_reader_init_id, b.func);
            let inst = b.ins().call(fref, &[vv]);
            b.inst_results(inst)[0]
        }
        Prim::BitReadField {
            reader,
            ty,
            size,
            endian,
            signed,
            unit,
            is_last,
        } => {
            let rv = *env.get(&reader.0).expect("unbound read_field reader");
            let ty_tag = b.ins().iconst(types::I32, encode_bit_type(*ty) as i64);
            let unit_v = b
                .ins()
                .iconst(types::I32, unit.unwrap_or(default_unit_for(*ty)) as i64);
            let endian_v = b.ins().iconst(types::I32, encode_endian(*endian) as i64);
            let signed_v = b.ins().iconst(types::I32, *signed as i64);
            let is_last_v = b.ins().iconst(types::I32, *is_last as i64);
            let (size_present, size_value) = match size {
                None => (
                    b.ins().iconst(types::I32, 0),
                    b.ins().iconst(types::I32, 0),
                ),
                Some(crate::fz_ir::BitSizeIr::Literal(n)) => (
                    b.ins().iconst(types::I32, 1),
                    b.ins().iconst(types::I32, *n as i64),
                ),
                Some(crate::fz_ir::BitSizeIr::Var(v)) => {
                    let raw = *env.get(&v.0).expect("unbound read_field size var");
                    let unb = unbox_int(b, raw);
                    let truncated = b.ins().ireduce(types::I32, unb);
                    (b.ins().iconst(types::I32, 1), truncated)
                }
            };
            let fref = jmod.declare_func_in_func(runtime.bs_read_field_id, b.func);
            let inst = b.ins().call(
                fref,
                &[
                    rv,
                    ty_tag,
                    size_present,
                    size_value,
                    unit_v,
                    endian_v,
                    signed_v,
                    is_last_v,
                ],
            );
            b.inst_results(inst)[0]
        }
        Prim::BitReaderDone(r) => {
            // Reader tuple shape: [bs_ptr@16, bit_len_boxed@24, pos_boxed@32].
            // Compare bit_len == pos; return tagged bool.
            let rv = *env.get(&r.0).expect("unbound reader_done");
            let bit_len_b = b.ins().load(types::I64, MemFlags::trusted(), rv, 24);
            let pos_b = b.ins().load(types::I64, MemFlags::trusted(), rv, 32);
            let cmp = b.ins().icmp(IntCC::Equal, bit_len_b, pos_b);
            bool_to_fz(b, cmp)
        }
        Prim::MakeMap(entries) => {
            let begin = jmod.declare_func_in_func(runtime.map_begin_id, b.func);
            b.ins().call(begin, &[]);
            let push = jmod.declare_func_in_func(runtime.map_push_id, b.func);
            for (k, v) in entries {
                let kv = *env.get(&k.0).expect("unbound makemap key");
                let vv = *env.get(&v.0).expect("unbound makemap val");
                b.ins().call(push, &[kv, vv]);
            }
            let fin = jmod.declare_func_in_func(runtime.map_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MapUpdate(base, entries) => {
            let bv = *env.get(&base.0).expect("unbound mapupdate base");
            let cln = jmod.declare_func_in_func(runtime.map_clone_id, b.func);
            b.ins().call(cln, &[bv]);
            let push = jmod.declare_func_in_func(runtime.map_push_id, b.func);
            for (k, v) in entries {
                let kv = *env.get(&k.0).expect("unbound mapupdate key");
                let vv = *env.get(&v.0).expect("unbound mapupdate val");
                b.ins().call(push, &[kv, vv]);
            }
            let fin = jmod.declare_func_in_func(runtime.map_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MapGet(m, k) => {
            let mv = *env.get(&m.0).expect("unbound mapget map");
            let kv = *env.get(&k.0).expect("unbound mapget key");
            let fref = jmod.declare_func_in_func(runtime.map_get_id, b.func);
            let inst = b.ins().call(fref, &[mv, kv]);
            b.inst_results(inst)[0]
        }
        Prim::MakeClosure(fn_id, captured) => {
            let begin = jmod.declare_func_in_func(runtime.closure_begin_id, b.func);
            let id_val = b.ins().iconst(types::I32, fn_id.0 as i64);
            b.ins().call(begin, &[id_val]);
            let push = jmod.declare_func_in_func(runtime.closure_push_id, b.func);
            for cv in captured {
                let v = *env.get(&cv.0).expect("unbound makeclosure capture");
                b.ins().call(push, &[v]);
            }
            let fin = jmod.declare_func_in_func(runtime.closure_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MakeVec(kind, els) => {
            use crate::fz_ir::VecKindIr;
            use crate::fz_value::HeapKind;
            let kind_tag = match kind {
                VecKindIr::I64 => HeapKind::VecI64 as i64,
                VecKindIr::U8 => HeapKind::VecU8 as i64,
                VecKindIr::Bit => HeapKind::VecBit as i64,
                VecKindIr::F64 => {
                    return Err(CodegenError::new(
                        "MakeVec(F64) deferred to fz-ul4.11.23",
                    ));
                }
            };
            let begin = jmod.declare_func_in_func(runtime.vec_begin_id, b.func);
            let kt = b.ins().iconst(types::I32, kind_tag);
            b.ins().call(begin, &[kt]);
            let push = jmod.declare_func_in_func(runtime.vec_push_id, b.func);
            for ev in els {
                let v = *env.get(&ev.0).expect("unbound makevec element");
                b.ins().call(push, &[v]);
            }
            let fin = jmod.declare_func_in_func(runtime.vec_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
    })
}

/// Unbox an FzValue-tagged int (assumed Tag::Int — caller's responsibility) to
/// a raw i64 via arithmetic shift right.
fn unbox_int(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().sshr_imm(v, 3)
}

/// Emit `((a^1) | (b^1)) & 7 == 0` — true iff both operands are Tag::Int
/// (low 3 bits = 001). Used by arithmetic / ordered comparisons to choose
/// between the inline int fast-path and the boxed-float slow path.
fn both_int(b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value) -> ir::Value {
    let xa = b.ins().bxor_imm(av, TAG_INT);
    let xb = b.ins().bxor_imm(bv, TAG_INT);
    let or_xab = b.ins().bor(xa, xb);
    let lo = b.ins().band_imm(or_xab, 7);
    b.ins().icmp_imm(IntCC::Equal, lo, 0)
}

/// Emit a tag-dispatched binary op: if both Tag::Int, run `fast`; else call
/// `helper_id` (an extern "C" fn(u64, u64) -> u64). Returns the join-block
/// param holding the resolved value.
fn emit_dispatch_binop<F>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    helper_id: FuncId,
    av: ir::Value,
    bv: ir::Value,
    fast: F,
) -> ir::Value
where
    F: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> ir::Value,
{
    let cond = both_int(b, av, bv);
    let fast_blk = b.create_block();
    let slow_blk = b.create_block();
    let join_blk = b.create_block();
    b.append_block_param(join_blk, types::I64);
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins().brif(cond, fast_blk, &no_args, slow_blk, &no_args);

    b.switch_to_block(fast_blk);
    b.seal_block(fast_blk);
    let fast_v = fast(b, av, bv);
    b.ins().jump(join_blk, &[BlockArg::Value(fast_v)]);

    b.switch_to_block(slow_blk);
    b.seal_block(slow_blk);
    let fref = jmod.declare_func_in_func(helper_id, b.func);
    let inst = b.ins().call(fref, &[av, bv]);
    let slow_v = b.inst_results(inst)[0];
    b.ins().jump(join_blk, &[BlockArg::Value(slow_v)]);

    b.switch_to_block(join_blk);
    b.seal_block(join_blk);
    b.block_params(join_blk)[0]
}

/// True iff BOTH operands are Tag::Ptr (low 3 bits = 000). Used by Eq/Neq
/// to dispatch to fz_value_eq only when there's actually a heap value to
/// inspect; (Ptr, Int) and other cross-tag pairs are correctly handled by
/// raw bit-eq (always false: ptr bits never alias non-ptr tags).
fn both_ptr(b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value) -> ir::Value {
    let or_ab = b.ins().bor(av, bv);
    let lo = b.ins().band_imm(or_ab, 7);
    b.ins().icmp_imm(IntCC::Equal, lo, 0)
}

/// Box a raw i64 into an FzValue-tagged int: `(n << 3) | TAG_INT`.
fn box_int(b: &mut FunctionBuilder<'_>, raw: ir::Value) -> ir::Value {
    let shifted = b.ins().ishl_imm(raw, 3);
    b.ins().bor_imm(shifted, TAG_INT)
}

/// Returns an i8 (0/1) indicating whether `v` is truthy: not nil and not false.
fn is_truthy(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    let nil_v = b.ins().iconst(types::I64, NIL_BITS);
    let false_v = b.ins().iconst(types::I64, FALSE_BITS);
    let not_nil = b.ins().icmp(IntCC::NotEqual, v, nil_v);
    let not_false = b.ins().icmp(IntCC::NotEqual, v, false_v);
    b.ins().band(not_nil, not_false)
}

/// Convert an i8 cranelift bool to FzValue::TRUE / FzValue::FALSE.
fn bool_to_fz(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    let true_v = b.ins().iconst(types::I64, TRUE_BITS);
    let false_v = b.ins().iconst(types::I64, FALSE_BITS);
    b.ins().select(v, true_v, false_v)
}

#[allow(dead_code)]
fn _kp(_: &Var) {}

#[cfg(test)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir_lower::lower_program;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn lower_src(src: &str) -> Module {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        lower_program(&prog).expect("lower")
    }

    fn run_main(src: &str) -> i64 {
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        compile(&m).unwrap().run(entry)
    }

    fn run_main_after_heap_reset(src: &str) -> (i64, Module) {
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        heap_reset_for_test();
        let r = compile(&m).unwrap().run(entry);
        (r, m)
    }

    fn capture_main(src: &str) -> Vec<String> {
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        heap_reset_for_test();
        let _ = test_capture_take();
        let _ = compile(&m).unwrap().run(entry);
        test_capture_take()
    }

    // ----- fz-ul4.11.31: GC actually runs from JIT'd code -----

    /// Frame-chain root walker: given a 1-frame chain (caller is null) with
    /// a known-FzValue entry-param slot, the walker emits that slot.
    #[test]
    fn root_walker_emits_entry_param_fzvalues() {
        use crate::fz_value::{FzValue, HeapHeader};
        use crate::heap::{
            collect_roots_from_frame_chain, FieldDescriptor, FieldKind, Schema,
        };

        // Build a schema for a fn with one entry param. Schema layout:
        // [cont_ptr_slot, param_0_slot].
        let schema = Schema {
            name: "Frame_test_one_param".into(),
            size: 16, // 2 slots × 8 bytes
            fields: vec![
                FieldDescriptor { offset: 0, kind: FieldKind::FzValue },
                FieldDescriptor { offset: 8, kind: FieldKind::FzValue },
            ],
        };
        let frame_schemas = vec![schema];

        // Lay out a frame in raw memory: [header(16) | cont_ptr(8) | param(8)].
        let mut buf: [u8; 32] = [0; 32];
        unsafe {
            let hp = buf.as_mut_ptr() as *mut HeapHeader;
            *hp = HeapHeader {
                kind: 0,
                flags: 0,
                size_bytes: 16,
                schema_id: 0,
                _reserved: 0,
            };
            // cont_ptr = null (top of chain)
            std::ptr::write(buf.as_mut_ptr().add(16) as *mut *mut HeapHeader, std::ptr::null_mut());
            // param[0] = boxed int 42
            std::ptr::write(
                buf.as_mut_ptr().add(24) as *mut u64,
                FzValue::from_int(42).0,
            );
        }
        let roots = collect_roots_from_frame_chain(
            buf.as_mut_ptr() as *mut HeapHeader,
            &frame_schemas,
        );
        assert_eq!(roots.len(), 1, "one user-Var entry param emitted");
        assert_eq!(roots[0].unbox_int(), Some(42));
    }

    /// Hot-loop allocation: a tail-recursive counter that allocates one
    /// list cons cell per iteration (live only until the next iteration).
    /// Past the GC threshold, the safepoint should fire and reclaim.
    #[test]
    fn hot_loop_alloc_triggers_safepoint_gc() {
        // Each iteration allocates a fresh 2-element list. Only the latest
        // is reachable (head/tail are unused once recursion advances).
        let src = r#"
            fn loop(0, acc), do: acc
            fn loop(n, acc), do: loop(n - 1, [n, n])
            fn main(), do: loop(5000, [])
        "#;
        let m = lower_src(src);
        let entry = m.fn_by_name("main").unwrap().id;
        let compiled = compile(&m).unwrap();
        let mut p = compiled.make_process();
        // Lower the GC threshold so a small loop forces multiple ticks.
        p.heap.gc_threshold_bytes = 4 * 1024;
        let _result = compiled.run_in(entry, &mut p);
        assert!(
            p.heap.gc_run_count >= 1,
            "expected >=1 GC tick under hot alloc loop, got {}",
            p.heap.gc_run_count
        );
        // After 5000 iterations of 2-cell list allocations with only the
        // latest reachable, live_count should be far less than the raw
        // allocation count (which would otherwise have OOM'd the 64KiB
        // heap long before completing).
        assert!(
            p.heap.live_count() < 100,
            "expected GC to reclaim most allocations, live={}",
            p.heap.live_count()
        );
    }

    // ----- fz-ul4.11.32: per-Process state isolation -----

    /// Two Processes built from the same CompiledModule run independent
    /// programs that each construct a map. PRE-MIGRATION (when MAP_BUILDER
    /// was a shared TLS slot) the second `run_in` would inherit or corrupt
    /// the first's in-flight builder state. Post-migration, each Process
    /// owns its own builder fields and the two runs are fully independent.
    #[test]
    fn two_processes_run_independent_map_builds() {
        // Both programs use distinct keys + values so a corruption would
        // show up as a wrong halt value (halt reads tag bits of the map
        // pointer; we observe by reading specific entries via fz-level
        // map syntax).
        let src_a = "fn main(), do: %{1 => 10, 2 => 20}[1]";
        let src_b = "fn main(), do: %{3 => 30, 4 => 40}[3]";

        let ma = lower_src(src_a);
        let mb = lower_src(src_b);
        let ca = compile(&ma).unwrap();
        let cb = compile(&mb).unwrap();
        let entry_a = ma.fn_by_name("main").unwrap().id;
        let entry_b = mb.fn_by_name("main").unwrap().id;

        let mut pa = ca.make_process();
        let mut pb = cb.make_process();

        // Run a, then b, then a again (interleaved) — each should see only
        // its own state. If MAP_BUILDER were shared TLS, the second run
        // would either panic on stale state or compute the wrong value.
        let ra = ca.run_in(entry_a, &mut pa);
        let rb = cb.run_in(entry_b, &mut pb);
        let ra2 = ca.run_in(entry_a, &mut pa);

        assert_eq!(ra, 10, "process a's first run returns map[1] = 10");
        assert_eq!(rb, 30, "process b's run returns map[3] = 30");
        assert_eq!(ra2, 10, "process a's second run returns 10 (independent of b)");

        // Each Process accumulated its own heap allocations. The map
        // alloc lives on the Process's heap.
        assert!(pa.heap.live_count() > 0, "process a has live heap allocs");
        assert!(pb.heap.live_count() > 0, "process b has live heap allocs");
    }

    // ----- simple scalar / arithmetic tests -----

    #[test]
    fn const_int_runs_and_halts_with_value() {
        assert_eq!(run_main("fn main() do 42 end"), 42);
    }

    #[test]
    fn binop_int_addition_runs() {
        assert_eq!(run_main("fn main(), do: 40 + 2"), 42);
    }

    #[test]
    fn binop_chain_runs() {
        assert_eq!(run_main("fn main(), do: (1 + 2) * 7"), 21);
    }

    #[test]
    fn if_then_else_runs() {
        assert_eq!(run_main("fn main(), do: if 1 < 2, do: 100, else: 200"), 100);
    }

    #[test]
    fn print_builtin_routes_through_runtime() {
        assert_eq!(capture_main("fn main(), do: print(40 + 2)"), vec!["42"]);
    }

    #[test]
    fn unop_neg_runs() {
        assert_eq!(run_main("fn main(), do: -7"), -7);
    }

    #[test]
    fn atom_const_returns_atom_id() {
        assert_eq!(run_main("fn main(), do: :ok"), 1); // match_error interns first.
    }

    // ----- .11.8 frame-allocation tests -----

    #[test]
    fn add1_via_call_returns_42() {
        assert_eq!(run_main("fn add1(n), do: n + 1\nfn main(), do: add1(41)"), 42);
    }

    #[test]
    fn binop_with_inner_nontail_call() {
        assert_eq!(run_main("fn add1(n), do: n + 1\nfn main(), do: add1(40) + 2"), 43);
    }

    #[test]
    fn fact_5_smaller_repro() {
        assert_eq!(run_main(r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(5)
"#), 120);
    }

    #[test]
    fn fact_10_runs_via_recursion_and_continuation_chain() {
        assert_eq!(run_main(r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(10)
"#), 3628800);
    }

    #[test]
    fn count_100k_stays_bounded_via_tail_call_frame_reuse() {
        assert_eq!(run_main(r#"
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main(), do: count(100000, 0)
"#), 100_000);
    }

    #[test]
    fn render_fz_value_dispatches_per_tag() {
        use crate::fz_value::FzValue;
        assert_eq!(render_fz_value(FzValue::from_int(42).0), "42");
        assert_eq!(render_fz_value(FzValue::from_int(0).0), "0");
        assert_eq!(render_fz_value(FzValue::from_int(-7).0), "-7");
        assert_eq!(render_fz_value(FzValue::NIL.0), "[]");
        assert_eq!(render_fz_value(FzValue::TRUE.0), "true");
        assert_eq!(render_fz_value(FzValue::FALSE.0), "false");
        assert_eq!(render_fz_value(FzValue::from_atom_id(3).0), ":atom_3");
    }

    #[test]
    fn print_captures_atom_and_specials() {
        assert_eq!(
            capture_main("fn main() do\n  print(:ok)\n  print(true)\n  print(false)\nend"),
            vec![":atom_1", "true", "false"]
        );
    }

    // ----- .11.13 map tests -----

    #[test]
    fn print_atom_keyed_map_renders_canonically() {
        assert_eq!(
            capture_main("fn main(), do: print(%{a: 1, b: 2})"),
            vec!["%{:atom_1 => 1, :atom_2 => 2}"]
        );
    }

    #[test]
    fn map_get_returns_value_or_nil() {
        assert_eq!(run_main("fn main(), do: %{a: 10, b: 20}[:a] + %{a: 10, b: 20}[:b]"), 30);
    }

    #[test]
    fn map_update_returns_new_map_originals_unchanged() {
        assert_eq!(
            capture_main(r#"
fn main() do
  m = %{a: 1, b: 2}
  m2 = %{m | a: 99}
  print(m)
  print(m2)
end
"#),
            vec![
                "%{:atom_1 => 1, :atom_2 => 2}",
                "%{:atom_1 => 99, :atom_2 => 2}",
            ]
        );
    }

    #[test]
    fn gc_traces_map_keys_and_values() {
        let (halt_bits, _m) = run_main_after_heap_reset("fn main(), do: %{a: [1, 2, 3]}");
        let halt_bits = halt_bits as u64;
        assert_eq!(heap_live_count(), 4, "1 map + 3 cons cells");
        let root = crate::fz_value::FzValue(halt_bits);
        heap_gc(&[root]);
        assert_eq!(heap_live_count(), 4, "list survives via map's value field");
        heap_gc(&[]);
        assert_eq!(heap_live_count(), 0);
    }

    // ----- .11.12 bitstring tests -----

    #[test]
    fn print_bitstring_literal_via_jit() {
        assert_eq!(
            capture_main("fn main(), do: print(<<0xff, 0xab>>)"),
            vec!["<<255, 171>>"]
        );
    }

    #[test]
    fn match_simple_header_and_rest() {
        assert_eq!(
            capture_main(r#"
fn parse(<<n, rest::binary>>), do: {n, rest}
fn main(), do: print(parse(<<0xa5, 0x01, 0x02>>))
"#),
            vec!["{165, <<1, 2>>}"]
        );
    }

    #[test]
    fn match_variable_size_payload_via_size_var() {
        assert_eq!(
            capture_main(r#"
fn parse(<<len, payload::binary-size(len), rest::binary>>) do
  {len, payload, rest}
end
fn main(), do: print(parse(<<3, 0x01, 0x02, 0x03, 0xff>>))
"#),
            vec!["{3, <<1, 2, 3>>, <<255>>}"]
        );
    }

    #[test]
    fn gc_reclaims_bitstring_when_unrooted() {
        let _ = run_main_after_heap_reset("fn main(), do: <<0xde, 0xad>>");
        assert_eq!(heap_live_count(), 1, "single bitstring alive");
        heap_gc(&[]);
        assert_eq!(heap_live_count(), 0, "bitstring reclaimed");
    }

    // ----- .11.11 tuple tests -----

    #[test]
    fn print_tuple_pair_renders() {
        assert_eq!(capture_main("fn main(), do: print({1, 2})"), vec!["{1, 2}"]);
    }

    #[test]
    fn fst_snd_destructure_tuple() {
        assert_eq!(run_main(r#"
fn fst({a, _}), do: a
fn snd({_, b}), do: b
fn main(), do: fst({10, 20}) + snd({30, 40})
"#), 50);
    }

    #[test]
    fn print_mixed_type_tuple() {
        assert_eq!(
            capture_main("fn main(), do: print({1, :ok, true})"),
            vec!["{1, :atom_1, true}"]
        );
    }

    #[test]
    fn gc_traces_tuple_fields_freeing_pointed_objects_when_outer_dropped() {
        let src = "fn main(), do: {[1, 2, 3], 99}";
        let (_halt, _m) = run_main_after_heap_reset(src);
        assert_eq!(heap_live_count(), 4, "1 tuple + 3 cons cells");
        heap_gc(&[]);
        assert_eq!(heap_live_count(), 0);

        // Same shape with the tuple as a root: everything survives.
        let (halt_bits, _m) = run_main_after_heap_reset(src);
        let halt_bits = halt_bits as u64;
        assert_eq!(heap_live_count(), 4);
        let root = crate::fz_value::FzValue(halt_bits);
        heap_gc(&[root]);
        assert_eq!(heap_live_count(), 4);
    }

    // ----- .11.10 list tests -----

    #[test]
    fn print_list_literal_renders_via_jit() {
        assert_eq!(capture_main("fn main(), do: print([1, 2, 3])"), vec!["[1, 2, 3]"]);
    }

    #[test]
    fn sum_list_via_head_tail_recursion() {
        assert_eq!(run_main(r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: sum([1, 2, 3, 4, 5])
"#), 15);
    }

    #[test]
    fn allocate_list_drop_root_gc_reclaims() {
        let (_halt, _m) = run_main_after_heap_reset("fn main(), do: [1, 2, 3]");
        assert_eq!(heap_live_count(), 3);
        heap_gc(&[]);
        assert_eq!(heap_live_count(), 0);
        assert_eq!(heap_freelist_len(), 3);
    }

    #[test]
    fn allocate_list_keep_root_gc_preserves() {
        let (halt_bits, _m) = run_main_after_heap_reset("fn main(), do: [7, 8, 9]");
        let halt_bits = halt_bits as u64;
        assert_eq!(heap_live_count(), 3);
        let root = crate::fz_value::FzValue(halt_bits);
        heap_gc(&[root]);
        assert_eq!(heap_live_count(), 3);
    }

    #[test]
    fn box_unbox_int_roundtrip_via_neg_neg() {
        for n in &[0i64, 1, -1, 42, -42, 1_000_000_000] {
            let src = format!("fn main(), do: -(-({}))", n);
            assert_eq!(run_main(&src), *n, "round-trip failed for {}", n);
        }
    }

    #[test]
    fn mutual_recursion_even_odd_small_n() {
        assert_eq!(run_main(r#"
fn even(0), do: true
fn even(n), do: odd(n - 1)
fn odd(0), do: false
fn odd(n), do: even(n - 1)
fn main(), do: even(10)
"#), 1);
    }

    // ----- .11.19 closure tests -----

    #[test]
    fn apply_simple_closure_no_captures() {
        assert_eq!(run_main(r#"
fn double(x), do: x * 2
fn apply_f(f, n), do: f(n)
fn main(), do: apply_f(double, 21)
"#), 42);
    }

    #[test]
    fn closure_captures_local_value() {
        assert_eq!(run_main(r#"
fn make_adder(k), do: fn(x) -> x + k
fn main() do
  f = make_adder(10)
  f(5)
end
"#), 15);
    }

    #[test]
    fn map_higher_order_renders_doubled_list() {
        assert_eq!(
            capture_main(r#"
fn double(x), do: x * 2
fn map_l(_, []), do: []
fn map_l(f, [h | t]), do: [f(h) | map_l(f, t)]
fn main(), do: print(map_l(double, [1, 2, 3]))
"#),
            vec!["[2, 4, 6]"]
        );
    }

    #[test]
    fn gc_traces_closure_captured_via_jit() {
        let (halt, _m) = run_main_after_heap_reset(r#"
fn make_adder(k), do: fn(x) -> x + k
fn main(), do: make_adder(7)
"#);
        assert_eq!(heap_live_count(), 1);
        let root = crate::fz_value::FzValue(halt as u64);
        heap_gc(&[root]);
        assert_eq!(heap_live_count(), 1);
        heap_gc(&[]);
        assert_eq!(heap_live_count(), 0);
    }

    // ----- .11.21 structural equality tests -----

    #[test]
    fn list_structural_eq_same_content_distinct_allocations() {
        assert_eq!(run_main("fn main(), do: [1, 2, 3] == [1, 2, 3]"), 1);
    }

    #[test]
    fn list_structural_eq_length_mismatch_is_false() {
        assert_eq!(run_main("fn main(), do: [1, 2] == [1, 2, 3]"), 0);
    }

    #[test]
    fn tuple_structural_eq_same_arity_and_content() {
        assert_eq!(run_main("fn main(), do: {1, :ok} == {1, :ok}"), 1);
    }

    #[test]
    fn tuple_eq_different_arity_is_false() {
        assert_eq!(run_main("fn main(), do: {1, 2} == {1, 2, 3}"), 0);
    }

    #[test]
    fn bitstring_structural_eq_byte_aligned() {
        assert_eq!(run_main("fn main(), do: <<1, 2, 3>> == <<1, 2, 3>>"), 1);
    }

    #[test]
    fn map_structural_eq_ignores_construction_order() {
        assert_eq!(run_main("fn main(), do: %{a: 1, b: 2} == %{b: 2, a: 1}"), 1);
    }

    #[test]
    fn map_eq_different_value_is_false() {
        assert_eq!(run_main("fn main(), do: %{a: 1, b: 2} == %{a: 1, b: 3}"), 0);
    }

    #[test]
    fn heterogeneous_kinds_compare_unequal() {
        assert_eq!(run_main("fn main(), do: [1, 2] == {1, 2}"), 0);
    }

    #[test]
    fn nested_map_with_list_structural_eq() {
        assert_eq!(run_main("fn main(), do: %{x: [1, 2]} == %{x: [1, 2]}"), 1);
    }

    #[test]
    fn neq_inverts_structural_eq() {
        assert_eq!(run_main("fn main(), do: [1, 2] != [1, 2]"), 0);
        assert_eq!(run_main("fn main(), do: [1, 2] != [1, 3]"), 1);
    }

    // ----- .11.20 boxed-float tests -----

    #[test]
    fn float_const_halt_round_trips_via_bits() {
        let (halt, _m) = run_main_after_heap_reset("fn main(), do: 3.14");
        assert_eq!(f64::from_bits(halt as u64), 3.14);
    }

    #[test]
    fn print_float_renders_with_explicit_dot_zero() {
        assert_eq!(
            capture_main("fn main() do\n  print(4.0)\n  print(3.14)\nend"),
            vec!["4.0", "3.14"]
        );
    }

    #[test]
    fn float_arithmetic_promotes_via_runtime_helper() {
        assert_eq!(run_main("fn main(), do: 1.5 + 2.5 == 4.0"), 1);
    }

    #[test]
    fn mixed_int_float_arithmetic_promotes() {
        assert_eq!(run_main("fn main(), do: 1 + 2.0 == 3.0"), 1);
    }

    #[test]
    fn mixed_int_float_eq_does_not_promote() {
        assert_eq!(run_main("fn main(), do: 1 == 1.0"), 0);
    }

    #[test]
    fn distinct_boxed_floats_compare_equal_by_value() {
        assert_eq!(run_main("fn main(), do: 1.5 == 1.5"), 1);
    }

    #[test]
    fn float_ordered_comparison_dispatches_through_helper() {
        assert_eq!(run_main("fn main(), do: 1.5 < 2.0"), 1);
    }

    #[test]
    fn float_bit_field_round_trips_via_bitstring() {
        let (halt, _m) = run_main_after_heap_reset("fn main(), do: <<3.14::float>>");
        let halt = halt as u64;
        let p = crate::fz_value::FzValue(halt).unbox_ptr().unwrap();
        let bytes = unsafe {
            std::slice::from_raw_parts((p as *const u8).add(24), 8)
        };
        let mut buf = [0u8; 8];
        buf.copy_from_slice(bytes);
        let f = f64::from_bits(u64::from_be_bytes(buf));
        assert_eq!(f, 3.14);
    }

    #[test]
    fn allocate_float_drop_root_gc_reclaims() {
        let (_halt, _m) = run_main_after_heap_reset("fn main(), do: 2.71");
        assert_eq!(heap_live_count(), 1);
        heap_gc(&[]);
        assert_eq!(heap_live_count(), 0);
        assert_eq!(heap_freelist_len(), 1);
    }

    // ----- .11.14 vec tests -----

    #[test]
    fn print_vec_i64_renders_via_jit() {
        assert_eq!(capture_main("fn main(), do: print(~v[1, 2, 3])"), vec!["~v[1, 2, 3]"]);
    }

    #[test]
    fn print_vec_u8_renders_via_jit() {
        assert_eq!(capture_main("fn main(), do: print(~b[0xff, 0xab])"), vec!["~b[255, 171]"]);
    }

    #[test]
    fn print_vec_bit_renders_via_jit() {
        assert_eq!(
            capture_main("fn main(), do: print(~bits[1, 0, 1, 1])"),
            vec!["~bits[1, 0, 1, 1]"]
        );
    }

    #[test]
    fn vec_f64_codegen_blocks_with_pointer_to_followup_ticket() {
        // ~v[1.0, 2.0] lowers fine post-.24.5 but codegen still gates VecF64 at .11.23.
        let m = lower_src("fn main(), do: ~v[1.0, 2.0]");
        let err = match compile(&m) {
            Ok(_) => panic!("VecF64 codegen should be gated"),
            Err(e) => e,
        };
        let msg = format!("{:?}", err);
        assert!(msg.contains("11.23"), "expected ticket reference: {}", msg);
    }

    #[test]
    fn vec_get_returns_indexed_element() {
        assert_eq!(run_main("fn main(), do: vec_get(~v[10, 20, 30], 1)"), 20);
    }

    #[test]
    fn vec_get_out_of_bounds_returns_nil() {
        assert_eq!(run_main("fn main(), do: vec_get(~v[1, 2], 10)"), 0);
    }

    #[test]
    fn vec_address_stable_across_gc_via_jit() {
        let (halt_bits, _m) = run_main_after_heap_reset("fn main(), do: ~v[100, 200, 300]");
        let halt_bits = halt_bits as u64;
        assert_eq!(heap_live_count(), 1);
        let root = crate::fz_value::FzValue(halt_bits);
        let p_before = root.unbox_ptr().unwrap();
        heap_gc(&[root]);
        assert_eq!(heap_live_count(), 1);
        let p_after = crate::fz_value::FzValue(halt_bits).unbox_ptr().unwrap();
        assert_eq!(p_before, p_after);
        assert_eq!(crate::heap::Heap::vec_len(p_after), 3);
        unsafe {
            let payload = (p_after as *const u8).add(24) as *const i64;
            assert_eq!(std::ptr::read(payload.add(2)), 300);
        }
    }

    #[test]
    fn tail_call_closure_reuses_frame_via_count_loop() {
        // Self-applying closure to force TailCallClosure on every iteration.
        assert_eq!(run_main(r#"
fn loop_with(f, 0, acc), do: acc
fn loop_with(f, n, acc), do: f(f, n - 1, acc + 1)
fn main(), do: loop_with(loop_with, 100000, 0)
"#), 100_000);
    }

    // ---- fz-ul4.11.24.4: arithmetic dispatch elision ----
    //
    // These two tests synthesize IR directly via FnBuilder rather than
    // going through source: they exercise codegen with an entry-block
    // parameter at Top (impossible from a top-level fn declared in fz
    // source) so the typer is forced to retain dispatch. Keeping them
    // hand-built is the cleanest expression of the assertion.

    fn build_int_const_add_module() -> Module {
        use crate::fz_ir::{FnBuilder, ModuleBuilder};
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let two = b.let_(entry, Prim::Const(Const::Int(2)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, one, two));
        b.set_terminator(entry, Term::Halt(sum));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.build()
    }

    fn build_top_param_add_module() -> Module {
        use crate::fz_ir::{FnBuilder, ModuleBuilder};
        let mut b = FnBuilder::new(FnId(0), "main");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let sum = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
        b.set_terminator(entry, Term::Halt(sum));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.build()
    }

    fn get_main_ir(m: &Module) -> String {
        ir_text_record_enable();
        let _ = compile(m).unwrap();
        let ir = ir_text_record_take();
        ir.into_iter()
            .find(|(n, _)| n == "main")
            .map(|(_, s)| s)
            .expect("no main ir captured")
    }

    #[test]
    fn arith_int_int_elides_dispatch() {
        let m = build_int_const_add_module();
        let ir = get_main_ir(&m);
        assert!(!ir.contains("brif"),
            "elision should drop the both_int branch:\n{}", ir);
    }

    #[test]
    fn arith_top_param_keeps_dispatch() {
        let m = build_top_param_add_module();
        let ir = get_main_ir(&m);
        assert!(ir.contains("brif"),
            "dispatch should be retained for Top operands:\n{}", ir);
    }
}
