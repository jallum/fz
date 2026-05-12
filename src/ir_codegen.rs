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
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use cranelift_codegen::ir::{
    self, condcodes::{FloatCC, IntCC}, types, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) const HEADER_SIZE: i32 = 16;
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
    pub(crate) user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
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
    /// Atom names indexed by id. Copied into each Process at
    /// make_process() time so fz_value::debug::render can spell atoms
    /// out as `:name` (fz-ul4.25).
    pub(crate) atom_names: Vec<String>,
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
            heap: fz_runtime::heap::Heap::new(64 * 1024, std::rc::Rc::clone(&self.user_schemas)),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            closure_builder: None,
            closure_args: Vec::new(),
            frame_sizes: self.frame_sizes.clone(),
            atom_names: self.atom_names.clone(),
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
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

    /// Run one quantum for a Process. Resumes from `process.next_frame`
    /// (which the caller — typically the Runtime in src/runtime.rs — must
    /// have set to a fresh entry frame or the saved continuation from a
    /// prior yield). The caller is responsible for CURRENT_PROCESS
    /// install/uninstall; we just trampoline. On halt the trampoline
    /// returns null; we write that back to process.next_frame so the
    /// caller can observe completion.
    pub(crate) fn run_quantum(&self, process: &mut Process) {
        let mut cur = process.next_frame;
        let mut iters: usize = 0;
        let cap: usize = 10_000_000;
        while !cur.is_null() {
            iters += 1;
            if iters > cap {
                panic!("trampoline exceeded {} iterations", cap);
            }
            if process.heap.should_gc() {
                let roots = fz_runtime::heap::collect_roots_from_frame_chain(
                    cur as *mut fz_runtime::fz_value::HeapHeader,
                    &self.schemas,
                );
                process.heap.gc(&roots);
                process.heap.clear_should_gc_flag();
            }
            let header = cur as *const fz_runtime::fz_value::HeapHeader;
            let schema_id = unsafe { (*header).schema_id };
            let fn_ptr = self
                .fn_ptrs
                .get(&schema_id)
                .copied()
                .unwrap_or_else(|| panic!("no fn for schema_id {}", schema_id));
            let f: extern "C" fn(*mut u8, *mut u8) -> *mut u8 =
                unsafe { std::mem::transmute(fn_ptr) };
            let ctx = CURRENT_PROCESS.with(|c| c.get()) as *mut u8;
            let next = f(cur, ctx);
            // fz-ul4.19.3 yield sentinel: receive on empty mailbox sets
            // process.state = Blocked and returns YIELD_PTR. Save the
            // CURRENT frame (cur) as the resume point; the trampoline
            // will re-enter fz_receive_attempt when the task is woken.
            if next as u64 == YIELD_PTR {
                process.next_frame = cur;
                return;
            }
            cur = next;
        }
        process.next_frame = cur;
    }

    fn run_internal(&self, fn_id: FnId) -> i64 {
        let entry_schema = &self.schemas[fn_id.0 as usize];
        let frame = fz_runtime::ir_runtime::fz_alloc_frame(fn_id.0, entry_schema.size);
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
                let roots = fz_runtime::heap::collect_roots_from_frame_chain(
                    cur as *mut fz_runtime::fz_value::HeapHeader,
                    &self.schemas,
                );
                current_process().heap.gc(&roots);
                current_process().heap.clear_should_gc_flag();
            }
            let header = cur as *const fz_runtime::fz_value::HeapHeader;
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

// Process, PidId, ProcessState, CURRENT_PROCESS, DEFAULT_PROCESS, and
// current_process() moved to src/process.rs (fz-ul4.23.4.2). Re-exported
// here for back-compat with downstream users (runtime.rs, ir_runtime.rs,
// tests) while consumers migrate to `fz_runtime::process::*`.
pub use fz_runtime::process::{
    current_process, PidId, Process, ProcessState, CURRENT_PROCESS, DEFAULT_PROCESS,
};

// Runtime FFI fns called from JIT'd code now live in src/ir_runtime.rs.
// Value rendering lives in fz_runtime::fz_value::debug (fz-ul4.23.4.3).

thread_local! {
    /// (.11.24.4) Per-fn Cranelift IR display text captured by compile()
    /// after compile_fn but before define_function consumes the context.
    /// Test-only; enable by calling `ir_text_record_enable()` before compile.
    pub static IR_TEXT_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = std::cell::RefCell::new(None);
    /// (fz-ul4.23.8) Per-fn machine-code disassembly captured by compile()
    /// when set_disasm is on. Enable with `asm_record_enable()` before
    /// compile; drain with `asm_record_take()` after.
    pub static ASM_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = std::cell::RefCell::new(None);
}

pub fn asm_record_enable() {
    ASM_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

pub fn asm_record_take() -> Vec<(String, String)> {
    ASM_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// Drain the per-thread print-capture buffer. Tests in this file (and
/// the fixture_matrix integration tests) call this to read what
/// fz_print_value emitted during a compile/run. The actual storage lives
/// in the runtime crate alongside fz_print_value (fz-ul4.23.10).
pub fn test_capture_take() -> Vec<String> {
    fz_runtime::ir_runtime::test_capture_take()
}

/// Begin recording per-fn Cranelift IR display text. Subsequent `compile()`
/// calls on this thread will append `(fn_name, clif_text)` pairs to a TLS
/// buffer; `ir_text_record_take` drains and returns them.
///
/// Used by `fz dump --emit clif` (fz-ul4.23.3) and by unit tests that need
/// to assert on generated IR shape.
pub fn ir_text_record_enable() {
    IR_TEXT_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

pub fn ir_text_record_take() -> Vec<(String, String)> {
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
// fz_halt moved to ir_runtime.rs (.23.4.13).

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

pub fn heap_gc(roots: &[fz_runtime::fz_value::FzValue]) {
    DEFAULT_PROCESS.with(|c| {
        if let Some(p) = c.borrow_mut().as_mut() {
            p.heap.gc(roots);
        }
    });
}

// fz_alloc_list_cons and fz_alloc_struct moved to ir_runtime.rs (.23.4.7).

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

// Map cluster moved to ir_runtime.rs (.23.4.8). MAP_BUILDER state lives
// on Process.map_builder (per fz-ul4.11.32).

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

// Bitstring runtime cluster (fz_bs_*, decode_*) moved to ir_runtime.rs
// (.23.4.9). The codegen-time helpers below stay here.

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
// `3.0`). VR.2 (fz-ul4.27.3) added typed float-float fast paths in front
// of the dispatch: when ir_typer proves both operands Float, codegen
// inlines native fadd/fsub/fmul/fdiv and fcmp without going through the
// helper. Deleting the dispatch fallback entirely is deferred — too many
// callers (e.g. `fn add1(n) do n + 1 end`) still leave operands at `any`.
// Eq/Neq do NOT promote: `1 == 1.0` is false.

// fz_alloc_float moved to ir_runtime.rs (.23.4.7).

// ----- fz-ul4.19.2: scheduler-bound builtins (spawn / self) -----
//
// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
// Calling either outside the scheduler path panics with a clear message.

/// fz_spawn(closure_bits) -> pid_bits. Extracts fn_id from the closure
/// heap object and enqueues a new task at that fn. Returns the pid as a
/// boxed FzValue Int (Pid-as-struct deferred to a follow-up).
///
/// v1 restriction: closure must have ZERO captures. Captured values
/// would need to be copied into the new task's heap (.19.3 territory);
/// for v1 spawn takes plain fn references (closures with no captures).
// Concurrency cluster (fz_spawn/self/send/receive_attempt) moved to
// ir_runtime.rs (.23.4.12). YIELD_PTR stays here — the trampoline at
// run_internal/run_quantum (above) reads it directly.

/// fz-ul4.19.3 YIELD_PTR: the trampoline recognizes this non-null return
/// value as "task wants to suspend; resume at the same frame on next
/// scheduling". 0x1 is not 16-aligned, so it can never be a real heap
/// pointer.
pub(crate) const YIELD_PTR: u64 = 0x1;

// Arith / cmp / eq FFI cluster moved to src/ir_runtime.rs (fz-ul4.23.4.1).

// Vec cluster moved to ir_runtime.rs (.23.4.10).
// VEC_BUILDER state lives on Process.vec_builder (per fz-ul4.11.32),
// typed as Option<fz_runtime::ir_runtime::VecBuild>.

// Closure cluster moved to ir_runtime.rs (.23.4.11).

// fz_alloc_frame + fz_alloc_frame_for_test moved to ir_runtime.rs (.23.4.7).

// ---------------------------------------------------------------------------
// Compiler
// ---------------------------------------------------------------------------

fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    host_isa_with(false)
}

/// Build a host ISA. `pic = false` is right for the JIT (no relocations
/// needed inside in-memory code). `pic = true` is required for AOT on
/// macOS, where the linker rejects text relocations in regular
/// executables.
fn host_isa_with(pic: bool) -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", if pic { "true" } else { "false" }).unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

/// Build a [cont_ptr, ...entry_params] frame schema. The cont_ptr slot is
/// always `FzValue`; the param slots are described by `param_kinds`. All
/// slots are currently 8 bytes regardless of kind; VR.3.2+ flips storage to
/// raw f64 / raw i64 for the typed kinds. .5.1 (this ticket) is pure
/// FieldKind plumbing — every caller still passes `FzValue` for every
/// param, so behavior is unchanged.
fn build_frame_schema(name: &str, param_kinds: &[FieldKind]) -> Schema {
    let n_fields = 1 + param_kinds.len();
    let mut fields = Vec::with_capacity(n_fields);
    fields.push(FieldDescriptor {
        offset: 0,
        kind: FieldKind::FzValue,
    });
    for (i, k) in param_kinds.iter().enumerate() {
        fields.push(FieldDescriptor {
            offset: ((i + 1) * SLOT_BYTES as usize) as u32,
            kind: k.clone(),
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: HEADER_SIZE as u32 + (n_fields as u32) * SLOT_BYTES as u32,
        fields,
    }
}

/// Abstraction over a Cranelift module backend. <code>compile_with_backend</code>
/// drives the whole shared pipeline through this trait; JIT and AOT pick
/// what's specific to them (linkage, metadata-carrier emission, finalize).
///
/// fz-ul4.23.12 unification: where the trait used to expose only
/// `module_mut` and the surrounding pipeline was duplicated in
/// `compile()` and `compile_aot()`, the surrounding pipeline is now
/// shared and the trait owns every legitimate point of variation —
/// fn linkage, per-program metadata emission, and the finalize step
/// that materializes the backend's Output.
pub trait Backend {
    type Module: cranelift_module::Module;
    /// Whatever the backend hands the user after compilation finishes.
    /// JIT returns a `CompiledModule` (in-memory, runnable); AOT returns
    /// an `AotArtifact` (object bytes + linker metadata).
    type Output;

    fn module_mut(&mut self) -> &mut Self::Module;

    /// Linkage applied to user `fz_fn_<id>` declarations. JIT keeps them
    /// `Local` (only resolved in-process). AOT exports them so the linker
    /// can see them when assembling the final binary.
    fn fn_linkage(&self) -> Linkage;

    /// Emit per-program metadata carriers (dispatch fn, frame-size fn,
    /// atom-name blob, C `main` shim). The JIT impl is a no-op — the same
    /// data lives in `CompiledModule`'s Rust HashMaps and the runtime
    /// reads them directly. AOT emits Cranelift data + fns so the linker
    /// + `fz_aot_run` can resolve them at runtime.
    fn emit_metadata_carriers(
        &mut self,
        fbctx: &mut FunctionBuilderContext,
        meta: &CompiledMetadata,
    ) -> Result<(), CodegenError>;

    /// Finalize the backend into its Output. JIT finalizes the JITModule
    /// and resolves fn pointers. AOT emits the object-file bytes.
    fn finalize(self, meta: CompiledMetadata) -> Result<Self::Output, CodegenError>;
}

/// Everything `compile_with_backend` collects during the shared pipeline,
/// handed to the backend's `emit_metadata_carriers` and `finalize`.
///
/// The fz user `Module` (post type-rewrite) is intentionally NOT here —
/// backends only need the codegen metadata at finalize time. They've
/// already seen the module while declaring fns and compiling bodies.
pub struct CompiledMetadata {
    pub fn_ids: HashMap<u32, FuncId>,
    pub schemas: Vec<Schema>,
    pub user_schemas: std::rc::Rc<std::cell::RefCell<fz_runtime::heap::SchemaRegistry>>,
    pub frame_sizes: Vec<u32>,
    pub atom_names: Vec<String>,
    pub bs_tuple_arity1_schema: Option<u32>,
    pub bs_tuple_arity3_schema: Option<u32>,
    pub types: crate::ir_typer::ModuleTypes,
    pub diagnostics: crate::diag::Diagnostics,
    /// FnId of fz user `main`, if present. AOT needs it to wire the C
    /// `main` shim; JIT keeps it as a convenience for the run path.
    pub main_fn_id: Option<FnId>,
    /// Main fn's frame size (looked up from `schemas`). Convenience.
    pub main_frame_size: Option<u32>,
}

/// JIT backend: wraps a JITModule pre-finalize. compile() constructs one,
/// drives codegen through the Backend trait, then unpacks to call the
/// JIT-specific finalize_definitions / get_finalized_function pair.
pub struct JitBackend {
    jmod: JITModule,
}

impl JitBackend {
    fn new() -> Self {
        let isa = host_isa();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        // Bind every fz runtime FFI fn pointer. JIT-specific: the linker
        // is in-process and resolves symbols by name → Rust fn pointer.
        // AOT will skip this entire block (linker resolves against the
        // fz_runtime staticlib instead).
        builder.symbol("fz_print_value", fz_runtime::ir_runtime::fz_print_value as *const u8);
        // fz-ul4.27.7 (VR.5b): typed print helpers — JIT routes here when
        // the arg Descr is monomorphic, skipping the boxing round-trip.
        builder.symbol("fz_print_i64",  fz_runtime::fz_print_i64  as *const u8);
        builder.symbol("fz_print_f64",  fz_runtime::fz_print_f64  as *const u8);
        builder.symbol("fz_print_bool", fz_runtime::fz_print_bool as *const u8);
        builder.symbol("fz_print_atom", fz_runtime::fz_print_atom as *const u8);
        builder.symbol("fz_print_nil",  fz_runtime::fz_print_nil  as *const u8);
        builder.symbol("fz_halt", fz_runtime::ir_runtime::fz_halt as *const u8);
        builder.symbol("fz_alloc_frame", fz_runtime::ir_runtime::fz_alloc_frame as *const u8);
        builder.symbol("fz_alloc_list_cons", fz_runtime::ir_runtime::fz_alloc_list_cons as *const u8);
        builder.symbol("fz_alloc_struct", fz_runtime::ir_runtime::fz_alloc_struct as *const u8);
        builder.symbol("fz_bs_begin", fz_runtime::ir_runtime::fz_bs_begin as *const u8);
        builder.symbol("fz_bs_write_field", fz_runtime::ir_runtime::fz_bs_write_field as *const u8);
        builder.symbol("fz_bs_finalize", fz_runtime::ir_runtime::fz_bs_finalize as *const u8);
        builder.symbol("fz_bs_reader_init", fz_runtime::ir_runtime::fz_bs_reader_init as *const u8);
        builder.symbol("fz_bs_read_field", fz_runtime::ir_runtime::fz_bs_read_field as *const u8);
        builder.symbol("fz_map_begin", fz_runtime::ir_runtime::fz_map_begin as *const u8);
        builder.symbol("fz_map_clone", fz_runtime::ir_runtime::fz_map_clone as *const u8);
        builder.symbol("fz_map_push", fz_runtime::ir_runtime::fz_map_push as *const u8);
        builder.symbol("fz_map_finalize", fz_runtime::ir_runtime::fz_map_finalize as *const u8);
        builder.symbol("fz_map_get", fz_runtime::ir_runtime::fz_map_get as *const u8);
        builder.symbol("fz_alloc_float", fz_runtime::ir_runtime::fz_alloc_float as *const u8);
        builder.symbol("fz_arith_add", fz_runtime::ir_runtime::fz_arith_add as *const u8);
        builder.symbol("fz_arith_sub", fz_runtime::ir_runtime::fz_arith_sub as *const u8);
        builder.symbol("fz_arith_mul", fz_runtime::ir_runtime::fz_arith_mul as *const u8);
        builder.symbol("fz_arith_div", fz_runtime::ir_runtime::fz_arith_div as *const u8);
        builder.symbol("fz_arith_mod", fz_runtime::ir_runtime::fz_arith_mod as *const u8);
        builder.symbol("fz_cmp_lt", fz_runtime::ir_runtime::fz_cmp_lt as *const u8);
        builder.symbol("fz_cmp_le", fz_runtime::ir_runtime::fz_cmp_le as *const u8);
        builder.symbol("fz_cmp_gt", fz_runtime::ir_runtime::fz_cmp_gt as *const u8);
        builder.symbol("fz_cmp_ge", fz_runtime::ir_runtime::fz_cmp_ge as *const u8);
        builder.symbol("fz_value_eq", fz_runtime::ir_runtime::fz_value_eq as *const u8);
        builder.symbol("fz_vec_begin", fz_runtime::ir_runtime::fz_vec_begin as *const u8);
        builder.symbol("fz_vec_push", fz_runtime::ir_runtime::fz_vec_push as *const u8);
        builder.symbol("fz_vec_finalize", fz_runtime::ir_runtime::fz_vec_finalize as *const u8);
        builder.symbol("fz_vec_get", fz_runtime::ir_runtime::fz_vec_get as *const u8);
        builder.symbol("fz_closure_begin", fz_runtime::ir_runtime::fz_closure_begin as *const u8);
        builder.symbol("fz_closure_push", fz_runtime::ir_runtime::fz_closure_push as *const u8);
        builder.symbol("fz_closure_finalize", fz_runtime::ir_runtime::fz_closure_finalize as *const u8);
        builder.symbol("fz_closure_arg", fz_runtime::ir_runtime::fz_closure_arg as *const u8);
        builder.symbol("fz_closure_invoke", fz_runtime::ir_runtime::fz_closure_invoke as *const u8);
        builder.symbol("fz_tail_closure", fz_runtime::ir_runtime::fz_tail_closure as *const u8);
        builder.symbol("fz_spawn", fz_runtime::ir_runtime::fz_spawn as *const u8);
        builder.symbol("fz_self", fz_runtime::ir_runtime::fz_self as *const u8);
        builder.symbol("fz_send", fz_runtime::ir_runtime::fz_send as *const u8);
        builder.symbol("fz_receive_attempt", fz_runtime::ir_runtime::fz_receive_attempt as *const u8);
        Self {
            jmod: JITModule::new(builder),
        }
    }
}

impl Backend for JitBackend {
    type Module = JITModule;
    type Output = CompiledModule;

    fn module_mut(&mut self) -> &mut JITModule {
        &mut self.jmod
    }

    fn fn_linkage(&self) -> Linkage {
        Linkage::Local
    }

    fn emit_metadata_carriers(
        &mut self,
        _fbctx: &mut FunctionBuilderContext,
        _meta: &CompiledMetadata,
    ) -> Result<(), CodegenError> {
        // No-op: JIT carries per-program metadata (fn_ptrs, frame_sizes,
        // atom_names) in the returned CompiledModule's Rust HashMaps.
        // The runtime reads them directly. No Cranelift carriers needed.
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<CompiledModule, CodegenError> {
        let JitBackend { mut jmod } = self;
        jmod.finalize_definitions()
            .map_err(|e| CodegenError::new(format!("finalize: {}", e)))?;
        let mut fn_ptrs: HashMap<u32, *const u8> = HashMap::new();
        for (fz_fn_id, func_id) in &meta.fn_ids {
            fn_ptrs.insert(*fz_fn_id, jmod.get_finalized_function(*func_id));
        }
        Ok(CompiledModule {
            module: jmod,
            fn_ptrs,
            schemas: meta.schemas,
            user_schemas: meta.user_schemas,
            frame_sizes: meta.frame_sizes,
            atom_names: meta.atom_names,
            bs_tuple_arity1_schema: meta.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: meta.bs_tuple_arity3_schema,
            types: meta.types,
            diagnostics: meta.diagnostics,
        })
    }
}

/// AOT backend: wraps a cranelift_object ObjectModule. Drives the same
/// codegen as the JIT (through the Backend trait + declare_runtime_symbols)
/// but finalizes by emitting object-file bytes for a linker rather than
/// resolving fn pointers in memory. fz-ul4.23.6.1.
pub struct AotBackend {
    omod: cranelift_object::ObjectModule,
}

impl AotBackend {
    pub fn new(name: &str) -> Self {
        // AOT needs PIC for macOS — the linker rejects text relocations
        // in regular executables. PIC on x86_64-linux / aarch64-linux is
        // also conventional for distributable binaries.
        let isa = host_isa_with(true);
        let builder = cranelift_object::ObjectBuilder::new(
            isa,
            name.to_string(),
            cranelift_module::default_libcall_names(),
        )
        .expect("ObjectBuilder::new");
        Self {
            omod: cranelift_object::ObjectModule::new(builder),
        }
    }
}

impl Backend for AotBackend {
    type Module = cranelift_object::ObjectModule;
    type Output = AotArtifact;

    fn module_mut(&mut self) -> &mut cranelift_object::ObjectModule {
        &mut self.omod
    }

    fn fn_linkage(&self) -> Linkage {
        Linkage::Export
    }

    fn emit_metadata_carriers(
        &mut self,
        fbctx: &mut FunctionBuilderContext,
        meta: &CompiledMetadata,
    ) -> Result<(), CodegenError> {
        // No `main`/0 in the source → nothing to drive at startup, so we
        // skip the dispatch/main shim entirely. `fz build` errors gracefully
        // on this artifact via its main_symbol check.
        let Some(main_fn_id) = meta.main_fn_id else {
            return Ok(());
        };
        let main_frame_size = meta
            .main_frame_size
            .expect("main_frame_size set whenever main_fn_id is");

        let aot_run_sig = sig1(
            &[
                types::I32,
                types::I32,
                types::I64,
                types::I64,
                types::I32,
                types::I64,
            ],
            &[types::I32],
        );
        let aot_run_id = self
            .omod
            .declare_function("fz_aot_run", Linkage::Import, &aot_run_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_run: {}", e)))?;

        let dispatch_sig = sig1(&[types::I32], &[types::I64]);
        let dispatch_id = self
            .omod
            .declare_function("fz_aot_dispatch", Linkage::Local, &dispatch_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_dispatch: {}", e)))?;
        emit_aot_dispatch(
            &mut self.omod,
            fbctx,
            dispatch_id,
            &dispatch_sig,
            &meta.fn_ids,
        )?;

        let fsz_sig = sig1(&[types::I32], &[types::I32]);
        let fsz_id = self
            .omod
            .declare_function("fz_aot_frame_size", Linkage::Local, &fsz_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_frame_size: {}", e)))?;
        emit_aot_frame_size(&mut self.omod, fbctx, fsz_id, &fsz_sig, &meta.schemas)?;
        let fn_count: u32 = meta.schemas.len() as u32;

        let atom_blob_data: Option<DataId> = if meta.atom_names.is_empty() {
            None
        } else {
            let mut blob: Vec<u8> = Vec::new();
            for name in &meta.atom_names {
                blob.extend_from_slice(name.as_bytes());
                blob.push(0);
            }
            blob.push(0);
            let id = self
                .omod
                .declare_data("fz_aot_atom_blob", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare atom blob: {}", e)))?;
            let mut desc = DataDescription::new();
            desc.define(blob.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define atom blob: {}", e)))?;
            Some(id)
        };

        let mut c_main_sig = Signature::new(CallConv::SystemV);
        c_main_sig.params.push(AbiParam::new(types::I32));
        c_main_sig.params.push(AbiParam::new(types::I64));
        c_main_sig.returns.push(AbiParam::new(types::I32));
        let c_main_id = self
            .omod
            .declare_function("main", Linkage::Export, &c_main_sig)
            .map_err(|e| CodegenError::new(format!("declare C main: {}", e)))?;
        emit_aot_c_main(
            &mut self.omod,
            fbctx,
            c_main_id,
            &c_main_sig,
            main_fn_id.0,
            main_frame_size,
            dispatch_id,
            fsz_id,
            fn_count,
            atom_blob_data,
            aot_run_id,
        )?;
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<AotArtifact, CodegenError> {
        let AotBackend { omod } = self;
        let product = omod.finish();
        let object = product
            .emit()
            .map_err(|e| CodegenError::new(format!("object emit: {}", e)))?;
        // For programs with a fz `main`, the C-callable `main` shim is the
        // linker's entry point. Without a fz main, no shim was emitted and
        // we surface the underlying fz_fn_<id> name so `fz build` can
        // error cleanly.
        let main_symbol = if meta.main_fn_id.is_some() {
            Some("main".to_string())
        } else {
            None
        };
        Ok(AotArtifact {
            object,
            main_symbol,
            diagnostics: meta.diagnostics,
        })
    }
}

/// AOT artifact: per-module emitted object bytes plus enough metadata to
/// drive linking. fz-ul4.23.6.3 (`fz build`) consumes this.
pub struct AotArtifact {
    /// Object-file bytes (ELF on Linux, Mach-O on macOS, COFF on Windows)
    /// suitable for `cc` to link against fz_runtime + libc.
    pub object: Vec<u8>,
    /// `main` fn's symbol name as emitted in the object, or None if the
    /// source had no `main/0`. The AOT driver uses this when generating
    /// the startup shim's call site.
    pub main_symbol: Option<String>,
    pub diagnostics: crate::diag::Diagnostics,
}

/// Drive the shared compile pipeline through any Backend impl. JIT and
/// AOT both route through here; the backend's hooks pick the legit
/// variation points (linkage, per-program metadata carriers, finalize).
///
/// fz-ul4.23.12. Before this, `compile()` and `compile_aot()` duplicated
/// ~90% of the pipeline side by side. Now they're each ~5-line wrappers
/// constructing a backend and calling here.
pub fn compile_with_backend<B: Backend>(
    module: &Module,
    mut backend: B,
) -> Result<B::Output, CodegenError> {
    // Per-fn schemas indexed by FnId.0 (cps_split inserts continuation fns
    // out of declaration order, so module.fns[i].id.0 != i in general).
    let max_id = module.fns.iter().map(|f| f.id.0).max().unwrap_or(0);

    let placeholder = build_frame_schema("__placeholder", &[]);
    let mut schemas: Vec<Schema> = vec![placeholder; (max_id + 1) as usize];
    for f in &module.fns {
        let entry_block = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        // .5.2: schemas computed before the typer rewrite at line 1024
        // would see the un-narrowed types. Defer the kind decision: ship
        // all-FzValue here, then refine in-place after the typer pass
        // below.
        let param_kinds: Vec<FieldKind> =
            entry_block.params.iter().map(|_| FieldKind::FzValue).collect();
        schemas[f.id.0 as usize] = build_frame_schema(&f.name, &param_kinds);
    }

    let runtime = declare_runtime_symbols(backend.module_mut())?;

    // Per-fn signature: uniform `extern "C" fn(*mut u8, *mut u8) -> *mut u8`
    // until VR.4 makes it per-fn.
    let fn_sig = sig1(&[types::I64, types::I64], &[types::I64]);

    let linkage = backend.fn_linkage();
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for f in &module.fns {
        let name = format!("fz_fn_{}", f.id.0);
        let id = backend
            .module_mut()
            .declare_function(&name, linkage, &fn_sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(f.id.0, id);
    }

    let mut fbctx = FunctionBuilderContext::new();

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
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
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

    // Per-fn frame sizes for `fz_alloc_frame_dyn`. Indexed by FnId.0.
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.size).collect();

    // Run the typer ahead of codegen so per-fn Var->Descr info is
    // available during lowering. .11.24.5 clones first so the typed-schema
    // rewrite can swap MakeVec(I64) → MakeVec(F64) where elements are Float.
    let mut working = module.clone();
    let pre_types = crate::ir_typer::type_module(&working);
    crate::ir_typer::rewrite_vec_kinds(&mut working, &pre_types)
        .map_err(CodegenError::new)?;
    let module_types = crate::ir_typer::type_module(&working);
    let module = &working;

    // fz-ul4.27.5.2/3: refine entry-frame slot kinds. Float entry params
    // → RawF64; int entry params → RawI64. Both flip storage to raw bytes
    // and let codegen skip the per-op unbox/rebox round trip.
    for (i, f) in module.fns.iter().enumerate() {
        let entry_block = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        let ft = &module_types[i];
        let sch = &mut schemas[f.id.0 as usize];
        for (j, p) in entry_block.params.iter().enumerate() {
            let d = ft.vars.get(p).cloned().unwrap_or_else(crate::types::Descr::any);
            if d.is_subtype(&crate::types::Descr::float()) {
                sch.fields[j + 1].kind = FieldKind::RawF64;
            } else if d.is_subtype(&crate::types::Descr::int()) {
                sch.fields[j + 1].kind = FieldKind::RawI64;
            }
        }
    }

    for (fn_idx, f) in module.fns.iter().enumerate() {
        let func_id = *fn_ids.get(&f.id.0).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sig.clone();
        // fz-ul4.23.8: opt in to asm capture when ASM_RECORD is active.
        // Cheap to set; the TLS slot is None in normal runs.
        let want_asm = ASM_RECORD.with(|c| c.borrow().is_some());
        if want_asm {
            ctx.set_disasm(true);
        }
        compile_fn(
            backend.module_mut(),
            &mut ctx,
            &mut fbctx,
            &runtime,
            &schemas,
            &tuple_schema_ids,
            f,
            &module_types[fn_idx],
            &module.source,
        )?;
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                v.push((f.name.clone(), ctx.func.display().to_string()));
            }
        });
        let fn_span = module.source.fn_span_of(f.id);
        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verifier::verify_function(&ctx.func, &flags).map_err(|e| {
            CodegenError::new(format!(
                "verify {}:\n{}\n--- IR ---\n{}",
                f.name,
                e,
                ctx.func.display()
            ))
            .with_span(fn_span)
        })?;
        backend
            .module_mut()
            .define_function(func_id, &mut ctx)
            .map_err(|e| {
                CodegenError::new(format!("define {}: {}", f.name, e)).with_span(fn_span)
            })?;
        if want_asm {
            if let Some(cc) = ctx.compiled_code() {
                if let Some(vcode) = cc.vcode.as_ref() {
                    ASM_RECORD.with(|c| {
                        if let Some(v) = c.borrow_mut().as_mut() {
                            v.push((f.name.clone(), vcode.clone()));
                        }
                    });
                }
            }
        }
        backend.module_mut().clear_context(&mut ctx);
    }

    let main_fn_id = module.fn_by_name("main").map(|f| f.id);
    let main_frame_size = main_fn_id.map(|id| schemas[id.0 as usize].size);

    let diagnostics = crate::ir_typer::collect_diagnostics(module, &module_types);
    let metadata = CompiledMetadata {
        fn_ids,
        schemas,
        user_schemas,
        frame_sizes,
        atom_names: module.atom_names.clone(),
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
        types: module_types,
        diagnostics,
        main_fn_id,
        main_frame_size,
    };

    // Backend-specific metadata carriers (no-op for JIT; dispatch + main
    // shim + atom blob for AOT) emit before finalize so any data /
    // function declarations land in the same Module that finalize hands
    // off.
    backend.emit_metadata_carriers(&mut fbctx, &metadata)?;
    backend.finalize(metadata)
}

pub fn compile(module: &Module) -> Result<CompiledModule, CodegenError> {
    compile_with_backend(module, JitBackend::new())
}

pub fn compile_aot(module: &Module, obj_name: &str) -> Result<AotArtifact, CodegenError> {
    compile_with_backend(module, AotBackend::new(obj_name))
}


/// Emit the per-program `fz_aot_dispatch(schema_id) -> fn_ptr` fn.
/// switch-returns each fz_fn_<id>'s address via Cranelift's func_addr.
/// Returns null for unknown ids (fz_aot_run treats null as a fatal AOT
/// build error).
fn emit_aot_dispatch<M: cranelift_module::Module>(
    jmod: &mut M,
    fbctx: &mut FunctionBuilderContext,
    dispatch_id: FuncId,
    dispatch_sig: &Signature,
    fn_ids: &HashMap<u32, FuncId>,
) -> Result<(), CodegenError> {
    use cranelift_codegen::ir::condcodes::IntCC;
    use cranelift_frontend::FunctionBuilder;

    let mut ctx = jmod.make_context();
    ctx.func.signature = dispatch_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let id_param = b.block_params(entry)[0];

        // Stable id order so the emitted CLIF is reproducible.
        let mut ids_sorted: Vec<u32> = fn_ids.keys().copied().collect();
        ids_sorted.sort();

        let default_block = b.create_block();
        let return_blocks: Vec<cranelift_codegen::ir::Block> = ids_sorted
            .iter()
            .map(|_| b.create_block())
            .collect();

        // Linear if/else chain. For a small fn count (~10s) this is fine;
        // an n-arity jump table is a follow-up if AOT codegen ever does
        // huge modules.
        let mut cur_test = entry;
        for (idx, sid) in ids_sorted.iter().enumerate() {
            b.switch_to_block(cur_test);
            let cond = b.ins().icmp_imm(IntCC::Equal, id_param, *sid as i64);
            let next_test = if idx + 1 < ids_sorted.len() {
                b.create_block()
            } else {
                default_block
            };
            b.ins().brif(cond, return_blocks[idx], &[], next_test, &[]);
            cur_test = next_test;
        }

        // One-line block per fn returning its address.
        for (sid, ret_blk) in ids_sorted.iter().zip(return_blocks.iter()) {
            b.switch_to_block(*ret_blk);
            let fref = jmod.declare_func_in_func(fn_ids[sid], b.func);
            let addr = b.ins().func_addr(types::I64, fref);
            b.ins().return_(&[addr]);
        }

        // Default: null. fz_aot_run aborts on null.
        b.switch_to_block(default_block);
        let z = b.ins().iconst(types::I64, 0);
        b.ins().return_(&[z]);

        b.seal_all_blocks();
        b.finalize();
    }
    let flags = settings::Flags::new(settings::builder());
    cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
        .map_err(|e| CodegenError::new(format!("verify fz_aot_dispatch: {}", e)))?;
    jmod
        .define_function(dispatch_id, &mut ctx)
        .map_err(|e| CodegenError::new(format!("define fz_aot_dispatch: {}", e)))?;
    jmod.clear_context(&mut ctx);
    Ok(())
}

/// Emit the AOT C-callable main entry: pass the program's main schema_id,
/// main frame size, dispatch + frame-size fn addresses, and fn count to
/// fz_aot_run, return its result. Linker uses this as the binary's
/// entry point.
#[allow(clippy::too_many_arguments)]
fn emit_aot_c_main<M: cranelift_module::Module>(
    jmod: &mut M,
    fbctx: &mut FunctionBuilderContext,
    c_main_id: FuncId,
    c_main_sig: &Signature,
    main_fz_id: u32,
    main_frame_size: u32,
    dispatch_id: FuncId,
    fsz_id: FuncId,
    fn_count: u32,
    atom_blob_data: Option<DataId>,
    aot_run_id: FuncId,
) -> Result<(), CodegenError> {
    use cranelift_frontend::FunctionBuilder;

    let mut ctx = jmod.make_context();
    ctx.func.signature = c_main_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);

        let main_id_v = b.ins().iconst(types::I32, main_fz_id as i64);
        let frame_size_v = b.ins().iconst(types::I32, main_frame_size as i64);
        let dispatch_fref = jmod.declare_func_in_func(dispatch_id, b.func);
        let dispatch_addr = b.ins().func_addr(types::I64, dispatch_fref);
        let fsz_fref = jmod.declare_func_in_func(fsz_id, b.func);
        let fsz_addr = b.ins().func_addr(types::I64, fsz_fref);
        let fn_count_v = b.ins().iconst(types::I32, fn_count as i64);
        let atom_blob_addr = match atom_blob_data {
            Some(data_id) => {
                let gv = jmod.declare_data_in_func(data_id, b.func);
                b.ins().symbol_value(types::I64, gv)
            }
            None => b.ins().iconst(types::I64, 0),
        };

        let aot_fref = jmod.declare_func_in_func(aot_run_id, b.func);
        let call = b.ins().call(
            aot_fref,
            &[
                main_id_v,
                frame_size_v,
                dispatch_addr,
                fsz_addr,
                fn_count_v,
                atom_blob_addr,
            ],
        );
        let result = b.inst_results(call)[0];
        b.ins().return_(&[result]);

        b.seal_all_blocks();
        b.finalize();
    }
    let flags = settings::Flags::new(settings::builder());
    cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
        .map_err(|e| CodegenError::new(format!("verify C main: {}", e)))?;
    jmod
        .define_function(c_main_id, &mut ctx)
        .map_err(|e| CodegenError::new(format!("define C main: {}", e)))?;
    jmod.clear_context(&mut ctx);
    Ok(())
}

/// Emit the per-program `fz_aot_frame_size(schema_id) -> u32` fn. Mirrors
/// the dispatch fn's brif-chain shape; returns 0 for unknown ids (which
/// signals a sparse / out-of-range schema_id — fz_alloc_frame_dyn handles
/// the panic message).
fn emit_aot_frame_size<M: cranelift_module::Module>(
    jmod: &mut M,
    fbctx: &mut FunctionBuilderContext,
    fsz_id: FuncId,
    fsz_sig: &Signature,
    schemas: &[Schema],
) -> Result<(), CodegenError> {
    use cranelift_codegen::ir::condcodes::IntCC;
    use cranelift_frontend::FunctionBuilder;

    let mut ctx = jmod.make_context();
    ctx.func.signature = fsz_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let id_param = b.block_params(entry)[0];

        // schemas is indexed by schema_id (== FnId.0). Build one return
        // block per known schema id, plus a default-zero block. Skip
        // placeholder schemas (size 0 isn't meaningful) — they end up
        // hitting the default block anyway.
        let default_block = b.create_block();
        let known: Vec<(u32, u32)> = schemas
            .iter()
            .enumerate()
            .map(|(i, s)| (i as u32, s.size))
            .filter(|(_, sz)| *sz > 0)
            .collect();
        let return_blocks: Vec<cranelift_codegen::ir::Block> =
            known.iter().map(|_| b.create_block()).collect();

        let mut cur_test = entry;
        for (idx, (sid, _)) in known.iter().enumerate() {
            b.switch_to_block(cur_test);
            let cond = b.ins().icmp_imm(IntCC::Equal, id_param, *sid as i64);
            let next_test = if idx + 1 < known.len() {
                b.create_block()
            } else {
                default_block
            };
            b.ins().brif(cond, return_blocks[idx], &[], next_test, &[]);
            cur_test = next_test;
        }

        for ((_, size), ret_blk) in known.iter().zip(return_blocks.iter()) {
            b.switch_to_block(*ret_blk);
            let v = b.ins().iconst(types::I32, *size as i64);
            b.ins().return_(&[v]);
        }

        b.switch_to_block(default_block);
        let z = b.ins().iconst(types::I32, 0);
        b.ins().return_(&[z]);

        b.seal_all_blocks();
        b.finalize();
    }
    let flags = settings::Flags::new(settings::builder());
    cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
        .map_err(|e| CodegenError::new(format!("verify fz_aot_frame_size: {}", e)))?;
    jmod
        .define_function(fsz_id, &mut ctx)
        .map_err(|e| CodegenError::new(format!("define fz_aot_frame_size: {}", e)))?;
    jmod.clear_context(&mut ctx);
    Ok(())
}


fn sig1(params: &[ir::Type], rets: &[ir::Type]) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for p in params { s.params.push(AbiParam::new(*p)); }
    for r in rets { s.returns.push(AbiParam::new(*r)); }
    s
}

/// Declare every fz runtime FFI fn as an Import in the given Cranelift
/// Module and return the resulting FuncIds packed into a RuntimeRefs.
///
/// Generic on `M: cranelift_module::Module` so the JIT (JITModule) and a
/// future AOT driver (ObjectModule, fz-ul4.23.6) call the same fn — the
/// declarations don't care whether the underlying symbol resolves via
/// JIT-installed Rust fn pointers or via a linker-resolved staticlib.
///
/// This is the only place that knows the wire ABI of each runtime fn;
/// changing one signature requires updating both the FFI body in
/// ir_runtime.rs AND the matching entry here.
fn declare_runtime_symbols<M: cranelift_module::Module>(
    jmod: &mut M,
) -> Result<RuntimeRefs, CodegenError> {
    let mut decl = |name: &str, params: &[ir::Type], rets: &[ir::Type]| {
        let sig = sig1(params, rets);
        jmod.declare_function(name, Linkage::Import, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };

    let print_id = decl("fz_print_value", &[types::I64], &[])?;
    let print_i64_id  = decl("fz_print_i64",  &[types::I64], &[])?;
    let print_f64_id  = decl("fz_print_f64",  &[types::F64], &[])?;
    let print_bool_id = decl("fz_print_bool", &[types::I8],  &[])?;
    let print_atom_id = decl("fz_print_atom", &[types::I32], &[])?;
    let print_nil_id  = decl("fz_print_nil",  &[],           &[])?;
    let halt_id = decl("fz_halt", &[types::I64, types::I64], &[])?;
    let alloc_id = decl("fz_alloc_frame", &[types::I32, types::I32], &[types::I64])?;
    let alloc_cons_id = decl(
        "fz_alloc_list_cons",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let alloc_struct_id = decl("fz_alloc_struct", &[types::I32], &[types::I64])?;
    let bs_begin_id = decl("fz_bs_begin", &[], &[])?;
    let bs_write_id = decl(
        "fz_bs_write_field",
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
    )?;
    let bs_finalize_id = decl("fz_bs_finalize", &[], &[types::I64])?;
    let bs_reader_init_id = decl("fz_bs_reader_init", &[types::I64], &[types::I64])?;
    let bs_read_field_id = decl(
        "fz_bs_read_field",
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
    )?;
    let map_begin_id = decl("fz_map_begin", &[], &[])?;
    let map_clone_id = decl("fz_map_clone", &[types::I64], &[])?;
    let map_push_id = decl("fz_map_push", &[types::I64, types::I64], &[])?;
    let map_finalize_id = decl("fz_map_finalize", &[], &[types::I64])?;
    let map_get_id = decl("fz_map_get", &[types::I64, types::I64], &[types::I64])?;
    let alloc_float_id = decl("fz_alloc_float", &[types::I64], &[types::I64])?;

    let arith_params: &[ir::Type] = &[types::I64, types::I64];
    let arith_ret: &[ir::Type] = &[types::I64];
    let arith_add_id = decl("fz_arith_add", arith_params, arith_ret)?;
    let arith_sub_id = decl("fz_arith_sub", arith_params, arith_ret)?;
    let arith_mul_id = decl("fz_arith_mul", arith_params, arith_ret)?;
    let arith_div_id = decl("fz_arith_div", arith_params, arith_ret)?;
    let arith_mod_id = decl("fz_arith_mod", arith_params, arith_ret)?;
    let cmp_lt_id = decl("fz_cmp_lt", arith_params, arith_ret)?;
    let cmp_le_id = decl("fz_cmp_le", arith_params, arith_ret)?;
    let cmp_gt_id = decl("fz_cmp_gt", arith_params, arith_ret)?;
    let cmp_ge_id = decl("fz_cmp_ge", arith_params, arith_ret)?;
    let value_eq_id = decl("fz_value_eq", arith_params, arith_ret)?;

    let vec_begin_id = decl("fz_vec_begin", &[types::I32], &[])?;
    let vec_push_id = decl("fz_vec_push", &[types::I64], &[])?;
    let vec_finalize_id = decl("fz_vec_finalize", &[], &[types::I64])?;
    let vec_get_id = decl("fz_vec_get", &[types::I64, types::I64], &[types::I64])?;

    let closure_begin_id = decl("fz_closure_begin", &[types::I32], &[])?;
    let closure_push_id = decl("fz_closure_push", &[types::I64], &[])?;
    let closure_finalize_id = decl("fz_closure_finalize", &[], &[types::I64])?;
    let closure_arg_id = decl("fz_closure_arg", &[types::I64], &[])?;
    let closure_invoke_id = decl(
        "fz_closure_invoke",
        &[types::I64, types::I64],
        &[types::I64],
    )?;
    let tail_closure_id = decl(
        "fz_tail_closure",
        &[types::I64, types::I64],
        &[types::I64],
    )?;

    let spawn_id = decl("fz_spawn", &[types::I64], &[types::I64])?;
    let self_id = decl("fz_self", &[], &[types::I64])?;
    let send_id = decl("fz_send", &[types::I64, types::I64], &[types::I64])?;
    let receive_attempt_id = decl("fz_receive_attempt", &[types::I64], &[types::I64])?;

    Ok(RuntimeRefs {
        print_id,
        print_i64_id,
        print_f64_id,
        print_bool_id,
        print_atom_id,
        print_nil_id,
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
        vec_begin_id,
        vec_push_id,
        vec_finalize_id,
        vec_get_id,
        closure_begin_id,
        closure_push_id,
        closure_finalize_id,
        closure_arg_id,
        closure_invoke_id,
        tail_closure_id,
        spawn_id,
        self_id,
        send_id,
        receive_attempt_id,
    })
}

#[derive(Clone, Copy)]
struct RuntimeRefs {
    print_id: FuncId,
    print_i64_id: FuncId,
    print_f64_id: FuncId,
    print_bool_id: FuncId,
    print_atom_id: FuncId,
    print_nil_id: FuncId,
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
    spawn_id: FuncId,
    self_id: FuncId,
    send_id: FuncId,
    receive_attempt_id: FuncId,
}

/// Pack a Span into a Cranelift SourceLoc (u32). 8 bits file_id + 24
/// bits start offset. Dummy spans become SourceLoc::default() so they
/// don't generate noise in the dump. fz-ul4.23.7.
fn span_to_srcloc(s: crate::diag::Span) -> cranelift_codegen::ir::SourceLoc {
    if s.is_dummy() {
        return cranelift_codegen::ir::SourceLoc::default();
    }
    let file = (s.file.0 & 0xFF) << 24;
    let offset = s.start & 0x00FF_FFFF;
    cranelift_codegen::ir::SourceLoc::new(file | offset)
}

fn compile_fn<M: cranelift_module::Module>(
    jmod: &mut M,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    tuple_schema_ids: &HashMap<usize, u32>,
    f: &crate::fz_ir::FnIr,
    fn_types: &crate::ir_typer::FnTypes,
    source: &crate::fz_ir::SourceInfo,
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
    // fz-ul4.27.5.2/3: RawF64 slots load as raw f64 and join `raw_f64_vars`;
    // RawI64 slots load as raw i64 (unshifted int payload) and join
    // `raw_int_vars`. Everything else loads as a tagged FzValue i64.
    let mut var_map: HashMap<u32, ir::Value> = HashMap::new();
    let mut raw_f64_vars: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    let mut raw_int_vars: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    let entry_blk = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    let my_schema = &schemas[f.id.0 as usize];
    for (i, p) in entry_blk.params.iter().enumerate() {
        let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
        let slot_kind = &my_schema.fields[i + 1].kind;
        let val = match slot_kind {
            FieldKind::RawF64 => {
                let f = b.ins().load(types::F64, MemFlags::trusted(), frame_ptr, off);
                raw_f64_vars.insert(p.0);
                f
            }
            FieldKind::RawI64 => {
                let n = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, off);
                raw_int_vars.insert(p.0);
                n
            }
            _ => b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, off),
        };
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

        // Per-stmt source location: ir_lower records spans into
        // SourceInfo.stmt_spans; encode each as a Cranelift SourceLoc so
        // `fz dump --emit clif` can render `; @file:line:col` comments.
        // fz-ul4.23.7.
        let stmt_spans = source.stmt_spans.get(&(f.id, blk.id));
        for (idx, stmt) in blk.stmts.iter().enumerate() {
            let span = stmt_spans
                .and_then(|v| v.get(idx))
                .copied()
                .unwrap_or(crate::diag::Span::DUMMY);
            b.set_srcloc(span_to_srcloc(span));
            let Stmt::Let(v, prim) = stmt;
            let out = lower_prim(&mut b, jmod, runtime, tuple_schema_ids, &var_map, &raw_f64_vars, &raw_int_vars, fn_types, prim)?;
            let val = out.value();
            if out.is_raw_f64() {
                raw_f64_vars.insert(v.0);
            }
            if out.is_raw_i64() {
                raw_int_vars.insert(v.0);
            }
            var_map.insert(v.0, val);
        }
        // Terminator gets its own srcloc (often the same as the last
        // stmt for Return blocks; distinct for Call/Goto).
        let term_span = source
            .term_span
            .get(&(f.id, blk.id))
            .copied()
            .unwrap_or(crate::diag::Span::DUMMY);
        b.set_srcloc(span_to_srcloc(term_span));

        // fz-ul4.27.5.2: tag the raw f64 vars that the terminator is
        // about to read. Other raw f64 vars in scope are dead past this
        // point and don't need boxing. Cross-block / cross-fn flow
        // operates on tagged FzValue (block params are i64; FzValue-kind
        // entry slots are tagged), so anything the terminator reaches
        // for must be materialised tagged first.
        let mut used_by_term: std::collections::HashSet<u32> =
            std::collections::HashSet::new();
        let note = |vs: &[crate::fz_ir::Var], set: &mut std::collections::HashSet<u32>| {
            for v in vs { set.insert(v.0); }
        };
        match &blk.terminator {
            Term::Goto(_, args) => note(args, &mut used_by_term),
            Term::If(c, _, _) => { used_by_term.insert(c.0); }
            Term::Halt(v) | Term::Return(v) => { used_by_term.insert(v.0); }
            Term::Call { args, continuation, .. } => {
                note(args, &mut used_by_term);
                note(&continuation.captured, &mut used_by_term);
            }
            Term::TailCall { args, .. } => note(args, &mut used_by_term),
            Term::CallClosure { closure, args, continuation } => {
                used_by_term.insert(closure.0);
                note(args, &mut used_by_term);
                note(&continuation.captured, &mut used_by_term);
            }
            Term::TailCallClosure { closure, args } => {
                used_by_term.insert(closure.0);
                note(args, &mut used_by_term);
            }
            Term::Receive { continuation } => {
                note(&continuation.captured, &mut used_by_term);
            }
        }
        let to_tag_f: Vec<u32> = raw_f64_vars
            .iter().copied().filter(|rv| used_by_term.contains(rv)).collect();
        for rv in to_tag_f {
            let raw = *var_map.get(&rv).expect("raw f64 var dropped from env");
            let boxed = box_float_native(&mut b, jmod, &runtime, raw);
            var_map.insert(rv, boxed);
            raw_f64_vars.remove(&rv);
        }
        let to_tag_i: Vec<u32> = raw_int_vars
            .iter().copied().filter(|rv| used_by_term.contains(rv)).collect();
        for rv in to_tag_i {
            let raw = *var_map.get(&rv).expect("raw i64 var dropped from env");
            let boxed = box_int(&mut b, raw);
            var_map.insert(rv, boxed);
            raw_int_vars.remove(&rv);
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
            Term::Receive { continuation } => {
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound receive cont capture"))
                    .collect();
                emit_receive(
                    &mut b,
                    jmod,
                    runtime,
                    schemas,
                    frame_ptr,
                    continuation.fn_id.0,
                    &cap_vals,
                );
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
fn emit_return<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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
fn emit_call<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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
            // Slots 2..K+2: captured vars in declaration order. .5.4:
            // kind-aware store so a typed-int / typed-float captured slot
            // gets its raw payload, not a tagged FzValue.
            store_args_into_callee_frame(b, cont_schema, cf, captured, 2);
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
    // Slots 1..N+1: args. Each arg is tagged FzValue by the caller (the
    // pre-terminator tag pass in compile_fn made sure of it). If the
    // callee's slot is FieldKind::RawF64, unbox the tagged boxed-float
    // ptr to raw f64 here so the slot stores its declared kind — GC
    // tracer parity requires the slot's bytes match the schema.
    // fz-ul4.27.5.2.
    store_args_into_callee_frame(b, callee_schema, callee_frame, args, 1);

    b.ins().return_(&[callee_frame]);
}

/// Store `args` into the callee frame starting at slot index `slot_base`
/// (== 1 for normal calls — slot 0 is cont_ptr). Each arg is assumed
/// tagged FzValue (i64); the callee's slot kind drives whether to store
/// raw bytes or tagged FzValue. fz-ul4.27.5.2.
fn store_args_into_callee_frame(
    b: &mut FunctionBuilder<'_>,
    callee_schema: &Schema,
    callee_frame: ir::Value,
    args: &[ir::Value],
    slot_base: usize,
) {
    for (i, av) in args.iter().enumerate() {
        let slot_idx = slot_base + i;
        let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
        match callee_schema.fields[slot_idx].kind {
            FieldKind::RawF64 => {
                // av is a tagged FzValue (heap ptr to boxed float). Read
                // the f64 payload and store it raw.
                let f = unbox_float(b, *av);
                b.ins().store(MemFlags::trusted(), f, callee_frame, off);
            }
            FieldKind::RawI64 => {
                // av is a tagged FzValue int `(n << 3) | 1`. Strip the
                // tag and store the raw i64. fz-ul4.27.5.3.
                let n = unbox_int(b, *av);
                b.ins().store(MemFlags::trusted(), n, callee_frame, off);
            }
            _ => {
                b.ins().store(MemFlags::trusted(), *av, callee_frame, off);
            }
        }
    }
}

/// Term::Receive (fz-ul4.19.3). Allocate the continuation frame (just like
/// Term::Call does for its cont) and hand it to fz_receive_attempt, which
/// either pops a message and writes it into the cont's result slot
/// (returning the cont frame, which the trampoline dispatches), or sets the
/// current Process's state to Blocked and returns YIELD_PTR. The yield
/// sentinel is `0x1` — never a valid heap-aligned pointer; the trampoline
/// recognizes it and parks the task.
fn emit_receive<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: ir::Value,
    cont_fn_id: u32,
    captured: &[ir::Value],
) {
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

    // Read my cont_ptr from current frame[16] (becomes the cont frame's
    // cont_ptr — same shape as Term::Call).
    let my_cont = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

    let cont_schema = &schemas[cont_fn_id as usize];
    let sid = b.ins().iconst(types::I32, cont_fn_id as i64);
    let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
    let inst = b.ins().call(alloc_fref, &[sid, sz]);
    let cf = b.inst_results(inst)[0];
    // Slot 0 (offset 16): cont_ptr.
    b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
    // Slot 1 (offset 24) is the result slot the message will land in;
    // fz_receive_attempt writes it on a hit.
    // Slots 2..: captured vars — kind-aware (fz-ul4.27.5.4).
    store_args_into_callee_frame(b, cont_schema, cf, captured, 2);

    // Call fz_receive_attempt(cont_frame). Returns cont_frame on hit,
    // YIELD_PTR (0x1) on empty mailbox.
    let recv_fref = jmod.declare_func_in_func(runtime.receive_attempt_id, b.func);
    let recv_inst = b.ins().call(recv_fref, &[cf]);
    let result = b.inst_results(recv_inst)[0];
    // Return whatever fz_receive_attempt returned. The trampoline
    // interprets 0x1 as yield; any other non-null ptr is the next frame
    // to dispatch.
    b.ins().return_(&[result]);
}

/// Term::TailCall: if callee shares schema with caller, overwrite caller's
/// frame in place. Otherwise allocate a new frame. Either way, cont_ptr is
/// preserved (the parent's continuation).
fn emit_tail_call<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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
        store_args_into_callee_frame(b, callee_schema, frame_ptr, args, 1);
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
        store_args_into_callee_frame(b, callee_schema, nf, args, 1);
        b.ins().return_(&[nf]);
    }
}

/// Term::CallClosure: build the continuation frame the same way as Term::Call,
/// stage args via fz_closure_arg(), then call fz_closure_invoke(closure,
/// cont_frame_ptr) which returns the callee frame ptr.
fn emit_call_closure<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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
    // .5.4: kind-aware captured-slot store.
    store_args_into_callee_frame(b, cont_schema, cf, captured, 2);

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
fn emit_tail_call_closure<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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

/// True when `v`'s typer-inferred Descr is a subtype of `float` — the
/// float-arithmetic dispatch elision pre-condition (fz-ul4.27.3).
fn descr_is_float(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    fn_types
        .vars
        .get(&v)
        .map(|d| d.is_subtype(&crate::types::Descr::float()))
        .unwrap_or(false)
}

/// True when `v`'s typer-inferred Descr is a subtype of `atom_top`.
/// VR.5a: atom-monomorphic Eq/Neq lowers to a single icmp because two
/// FzValues with the same atom-id share the same bit pattern.
fn descr_is_atom(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    fn_types
        .vars
        .get(&v)
        .map(|d| d.is_subtype(&crate::types::Descr::atom_top()))
        .unwrap_or(false)
}

/// True when `v` is statically nil-or-bool. Both occupy disjoint, fixed bit
/// patterns inside the tagged FzValue, so equality on them is bit-eq.
fn descr_is_nil_or_bool(fn_types: &crate::ir_typer::FnTypes, v: crate::fz_ir::Var) -> bool {
    fn_types
        .vars
        .get(&v)
        .map(|d| {
            let nb = crate::types::Descr::nil().union(&crate::types::Descr::bool_t());
            d.is_subtype(&nb)
        })
        .unwrap_or(false)
}

/// True when the two operands' types have empty intersection — Eq folds to
/// false, Neq folds to true. VR.5a powers both the lowering shortcut and
/// the `type/dead-binop` diagnostic.
fn descrs_disjoint(fn_types: &crate::ir_typer::FnTypes, a: crate::fz_ir::Var, b: crate::fz_ir::Var) -> bool {
    match (fn_types.vars.get(&a), fn_types.vars.get(&b)) {
        (Some(da), Some(db)) => da.intersect(db).looks_empty(),
        _ => false,
    }
}

/// Output of `lower_prim`. Tagged is the common case (i64 FzValue bits);
/// RawF64 is what the typed-float fast paths return so subsequent ops on
/// the same SSA value can stay raw (fz-ul4.27.5.2). RawI64 is the same
/// idea for typed-int ops (fz-ul4.27.5.3) — the SSA value is the
/// unshifted int payload, not the `(n << 3) | TAG_INT` tagged form.
enum LowerOut {
    Tagged(ir::Value),
    RawF64(ir::Value),
    RawI64(ir::Value),
}

impl LowerOut {
    fn value(&self) -> ir::Value {
        match self {
            LowerOut::Tagged(v) | LowerOut::RawF64(v) | LowerOut::RawI64(v) => *v,
        }
    }
    fn is_raw_f64(&self) -> bool { matches!(self, LowerOut::RawF64(_)) }
    fn is_raw_i64(&self) -> bool { matches!(self, LowerOut::RawI64(_)) }
}

fn lower_prim<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    env: &HashMap<u32, ir::Value>,
    raw_f64_vars: &std::collections::HashSet<u32>,
    raw_int_vars: &std::collections::HashSet<u32>,
    fn_types: &crate::ir_typer::FnTypes,
    prim: &Prim,
) -> Result<LowerOut, CodegenError> {
    // Helper: every consumer site below that wants a tagged FzValue uses
    // this. Sites that want a raw f64 (float fast paths only) call
    // `as_raw_f64` directly.
    //
    // The match below produces a *tagged* ir::Value for almost every prim.
    // The few prims that can produce a raw f64 (currently: typed float
    // BinOp::{Add,Sub,Mul,Div,Lt,Le,Gt,Ge,Eq,Neq}) early-return
    // `LowerOut::RawF64(_)` inside their arm. Everything else falls
    // through the match and is wrapped in `LowerOut::Tagged(_)` at the
    // bottom of the function.
    let v: ir::Value = match prim {
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
            // .5.2: tagged operands are materialised lazily by `tag_a` /
            // `tag_b` below. The typed-float fast paths read raw via
            // `as_raw_f64` and never trigger the box round-trip; only the
            // tagged-path branches (int fast path, scalar Eq/Neq, dispatch
            // fallback) call `tag_a` / `tag_b` and pay the conversion.
            macro_rules! tag_a { () => { tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, a.0) } }
            macro_rules! tag_b { () => { tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, bv.0) } }
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    let mop = *op;
                    // Typed-float fast path first so we never tag the raw
                    // f64 inputs.
                    if descr_is_float(fn_types, *a) && descr_is_float(fn_types, *bv)
                        && !matches!(mop, BinOp::Mod)
                    {
                        let af = as_raw_f64(env, raw_f64_vars, b, a.0);
                        let bf = as_raw_f64(env, raw_f64_vars, b, bv.0);
                        let raw_f = match mop {
                            BinOp::Add => b.ins().fadd(af, bf),
                            BinOp::Sub => b.ins().fsub(af, bf),
                            BinOp::Mul => b.ins().fmul(af, bf),
                            BinOp::Div => b.ins().fdiv(af, bf),
                            _ => unreachable!(),
                        };
                        return Ok(LowerOut::RawF64(raw_f));
                    }
                    // Typed-int fast path: read operands as raw i64 (no
                    // sshr round trip when the var came from a RawI64 slot
                    // or a prior int fast path), do native iadd/etc., and
                    // return the result raw. fz-ul4.27.5.3.
                    if descr_is_int(fn_types, *a) && descr_is_int(fn_types, *bv) {
                        let ai = as_raw_i64(env, raw_int_vars, b, a.0);
                        let bi = as_raw_i64(env, raw_int_vars, b, bv.0);
                        let raw = match mop {
                            BinOp::Add => b.ins().iadd(ai, bi),
                            BinOp::Sub => b.ins().isub(ai, bi),
                            BinOp::Mul => b.ins().imul(ai, bi),
                            BinOp::Div => b.ins().sdiv(ai, bi),
                            BinOp::Mod => b.ins().srem(ai, bi),
                            _ => unreachable!(),
                        };
                        return Ok(LowerOut::RawI64(raw));
                    }
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let fast_int = |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
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
                    let helper = match op {
                        BinOp::Add => runtime.arith_add_id,
                        BinOp::Sub => runtime.arith_sub_id,
                        BinOp::Mul => runtime.arith_mul_id,
                        BinOp::Div => runtime.arith_div_id,
                        BinOp::Mod => runtime.arith_mod_id,
                        _ => unreachable!(),
                    };
                    emit_dispatch_binop(b, jmod, helper, av, bvv, fast_int)
                }
                BinOp::Eq | BinOp::Neq => {
                    // VR.5a + .5.2.
                    let is_eq = matches!(op, BinOp::Eq);
                    let int_cc = if is_eq { IntCC::Equal } else { IntCC::NotEqual };
                    let f_cc = if is_eq { FloatCC::Equal } else { FloatCC::NotEqual };

                    // Kind-disjoint fold doesn't need either operand.
                    if descrs_disjoint(fn_types, *a, *bv) {
                        let bits = if is_eq { FALSE_BITS } else { TRUE_BITS };
                        return Ok(LowerOut::Tagged(b.ins().iconst(types::I64, bits)));
                    }
                    // Same-kind float: native fcmp on raw f64.
                    if descr_is_float(fn_types, *a) && descr_is_float(fn_types, *bv) {
                        let af = as_raw_f64(env, raw_f64_vars, b, a.0);
                        let bf = as_raw_f64(env, raw_f64_vars, b, bv.0);
                        let cmp = b.ins().fcmp(f_cc, af, bf);
                        return Ok(LowerOut::Tagged(bool_to_fz(b, cmp)));
                    }
                    // Same-kind int: native icmp on raw i64. .5.3: must
                    // not mix raw and tagged operands — bit-eq is only
                    // correct when both are in the same encoding.
                    if descr_is_int(fn_types, *a) && descr_is_int(fn_types, *bv) {
                        let ai = as_raw_i64(env, raw_int_vars, b, a.0);
                        let bi = as_raw_i64(env, raw_int_vars, b, bv.0);
                        let cmp = b.ins().icmp(int_cc, ai, bi);
                        return Ok(LowerOut::Tagged(bool_to_fz(b, cmp)));
                    }
                    let av = tag_a!();
                    let bvv = tag_b!();
                    if (descr_is_atom(fn_types, *a)  && descr_is_atom(fn_types, *bv))
                        || (descr_is_nil_or_bool(fn_types, *a) && descr_is_nil_or_bool(fn_types, *bv))
                    {
                        let cmp = b.ins().icmp(int_cc, av, bvv);
                        bool_to_fz(b, cmp)
                    } else {
                        // Original dispatch (unchanged): both_ptr=true -> slow.
                        let cond = both_ptr(b, av, bvv);
                        let fast_blk = b.create_block();
                        let slow_blk = b.create_block();
                        let join_blk = b.create_block();
                        b.append_block_param(join_blk, types::I64);
                        let no_args: Vec<BlockArg> = Vec::new();
                        b.ins().brif(cond, slow_blk, &no_args, fast_blk, &no_args);

                        b.switch_to_block(fast_blk);
                        b.seal_block(fast_blk);
                        let cmp = b.ins().icmp(int_cc, av, bvv);
                        let fast_v = bool_to_fz(b, cmp);
                        b.ins().jump(join_blk, &[BlockArg::Value(fast_v)]);

                        b.switch_to_block(slow_blk);
                        b.seal_block(slow_blk);
                        let fref = jmod.declare_func_in_func(runtime.value_eq_id, b.func);
                        let inst = b.ins().call(fref, &[av, bvv]);
                        let eq = b.inst_results(inst)[0];
                        let slow_v = if is_eq {
                            eq
                        } else {
                            b.ins().bxor_imm(eq, TRUE_BITS ^ FALSE_BITS)
                        };
                        b.ins().jump(join_blk, &[BlockArg::Value(slow_v)]);

                        b.switch_to_block(join_blk);
                        b.seal_block(join_blk);
                        b.block_params(join_blk)[0]
                    }
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    let icc = match op {
                        BinOp::Lt => IntCC::SignedLessThan,
                        BinOp::Le => IntCC::SignedLessThanOrEqual,
                        BinOp::Gt => IntCC::SignedGreaterThan,
                        BinOp::Ge => IntCC::SignedGreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    // Typed-float fast path first.
                    if descr_is_float(fn_types, *a) && descr_is_float(fn_types, *bv) {
                        let fcc = match op {
                            BinOp::Lt => FloatCC::LessThan,
                            BinOp::Le => FloatCC::LessThanOrEqual,
                            BinOp::Gt => FloatCC::GreaterThan,
                            BinOp::Ge => FloatCC::GreaterThanOrEqual,
                            _ => unreachable!(),
                        };
                        let af = as_raw_f64(env, raw_f64_vars, b, a.0);
                        let bf = as_raw_f64(env, raw_f64_vars, b, bv.0);
                        let cmp = b.ins().fcmp(fcc, af, bf);
                        return Ok(LowerOut::Tagged(bool_to_fz(b, cmp)));
                    }
                    // Typed-int fast path: read raw i64 operands directly.
                    if descr_is_int(fn_types, *a) && descr_is_int(fn_types, *bv) {
                        let ai = as_raw_i64(env, raw_int_vars, b, a.0);
                        let bi = as_raw_i64(env, raw_int_vars, b, bv.0);
                        let cmp = b.ins().icmp(icc, ai, bi);
                        return Ok(LowerOut::Tagged(bool_to_fz(b, cmp)));
                    }
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let fast_int = move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                        let ai = unbox_int(b, av);
                        let bi = unbox_int(b, bv);
                        let cmp = b.ins().icmp(icc, ai, bi);
                        bool_to_fz(b, cmp)
                    };
                    let helper = match op {
                        BinOp::Lt => runtime.cmp_lt_id,
                        BinOp::Le => runtime.cmp_le_id,
                        BinOp::Gt => runtime.cmp_gt_id,
                        BinOp::Ge => runtime.cmp_ge_id,
                        _ => unreachable!(),
                    };
                    emit_dispatch_binop(b, jmod, helper, av, bvv, fast_int)
                }
                BinOp::And => {
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let at = is_truthy(b, av);
                    let bt = is_truthy(b, bvv);
                    let conj = b.ins().band(at, bt);
                    bool_to_fz(b, conj)
                }
                BinOp::Or => {
                    let av = tag_a!();
                    let bvv = tag_b!();
                    let at = is_truthy(b, av);
                    let bt = is_truthy(b, bvv);
                    let disj = b.ins().bor(at, bt);
                    bool_to_fz(b, disj)
                }
            }
        }
        Prim::UnOp(op, x) => {
            match op {
                UnOp::Neg => {
                    // .5.3: read raw i64, native ineg, return raw — same
                    // shape as the BinOp int fast paths.
                    let xi = as_raw_i64(env, raw_int_vars, b, x.0);
                    return Ok(LowerOut::RawI64(b.ins().ineg(xi)));
                }
                UnOp::Not => {
                    let xv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, x.0);
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
                    // VR.5b (fz-ul4.27.7): dispatch on the arg's Descr to a
                    // typed print FFI when monomorphic. Saves the boxing
                    // round-trip that the polymorphic fz_print_value needs.
                    let a = args[0];
                    if descr_is_int(fn_types, a) {
                        let n = as_raw_i64(env, raw_int_vars, b, a.0);
                        let fref = jmod.declare_func_in_func(runtime.print_i64_id, b.func);
                        b.ins().call(fref, &[n]);
                    } else if descr_is_float(fn_types, a) {
                        let f = as_raw_f64(env, raw_f64_vars, b, a.0);
                        let fref = jmod.declare_func_in_func(runtime.print_f64_id, b.func);
                        b.ins().call(fref, &[f]);
                    } else {
                        let av = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, a.0);
                        let fref = jmod.declare_func_in_func(runtime.print_id, b.func);
                        b.ins().call(fref, &[av]);
                    }
                    // print/1 returns FzValue::NIL — never raw 0 (which would
                    // alias Tag::Ptr null and trip fz_halt's Ptr-deref path).
                    b.ins().iconst(types::I64, NIL_BITS)
                }
                BuiltinKind::VecGet => {
                    if args.len() != 2 {
                        return Err(CodegenError::new("vec_get/2 expected"));
                    }
                    let vv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0);
                    let iv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[1].0);
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
                BuiltinKind::Spawn => {
                    if args.len() != 1 {
                        return Err(CodegenError::new("spawn/1 expected"));
                    }
                    let cv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0);
                    let fref = jmod.declare_func_in_func(runtime.spawn_id, b.func);
                    let inst = b.ins().call(fref, &[cv]);
                    b.inst_results(inst)[0]
                }
                BuiltinKind::SelfPid => {
                    if !args.is_empty() {
                        return Err(CodegenError::new("self/0 expected"));
                    }
                    let fref = jmod.declare_func_in_func(runtime.self_id, b.func);
                    let inst = b.ins().call(fref, &[]);
                    b.inst_results(inst)[0]
                }
                BuiltinKind::Send => {
                    if args.len() != 2 {
                        return Err(CodegenError::new("send/2 expected"));
                    }
                    let pv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0);
                    let mv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[1].0);
                    let fref = jmod.declare_func_in_func(runtime.send_id, b.func);
                    let inst = b.ins().call(fref, &[pv, mv]);
                    b.inst_results(inst)[0]
                }
            }
        }
        Prim::ListCons(h, t) => {
            let hv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, h.0);
            let tv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, t.0);
            let fref = jmod.declare_func_in_func(runtime.alloc_cons_id, b.func);
            let inst = b.ins().call(fref, &[hv, tv]);
            b.inst_results(inst)[0]
        }
        Prim::ListHead(c) => {
            // `c` is FzValue ptr-tagged (tag bits = 000), so `c` is the raw
            // ListCons base address. head sits at byte offset 16 (after
            // HeapHeader); load it as i64 (raw FzValue bits).
            let cv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, c.0);
            b.ins().load(types::I64, MemFlags::trusted(), cv, 16)
        }
        Prim::ListTail(c) => {
            let cv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, c.0);
            b.ins().load(types::I64, MemFlags::trusted(), cv, 24)
        }
        Prim::ListIsNil(c) => {
            let cv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, c.0);
            let nil_v = b.ins().iconst(types::I64, NIL_BITS);
            let cmp = b.ins().icmp(IntCC::Equal, cv, nil_v);
            bool_to_fz(b, cmp)
        }
        Prim::MakeList(elems, tail) => {
            // Fold right: cons(e0, cons(e1, ..., cons(eN, tail-or-nil))).
            let mut acc = match tail {
                Some(t) => tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, t.0),
                None => b.ins().iconst(types::I64, NIL_BITS),
            };
            let fref = jmod.declare_func_in_func(runtime.alloc_cons_id, b.func);
            for e in elems.iter().rev() {
                let ev = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, e.0);
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
                let ev = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, e.0);
                let off = HEADER_SIZE + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), ev, p, off);
            }
            p
        }
        Prim::TupleField(c, idx) => {
            let cv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, c.0);
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
                let v = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, fv.0);
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
                let value_v = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, f.value.0);
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
                        let raw = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, v.0);
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
            let vv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, v.0);
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
            let rv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, reader.0);
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
                    let raw = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, v.0);
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
            let rv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, r.0);
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
                let kv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, k.0);
                let vv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, v.0);
                b.ins().call(push, &[kv, vv]);
            }
            let fin = jmod.declare_func_in_func(runtime.map_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MapUpdate(base, entries) => {
            let bv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, base.0);
            let cln = jmod.declare_func_in_func(runtime.map_clone_id, b.func);
            b.ins().call(cln, &[bv]);
            let push = jmod.declare_func_in_func(runtime.map_push_id, b.func);
            for (k, v) in entries {
                let kv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, k.0);
                let vv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, v.0);
                b.ins().call(push, &[kv, vv]);
            }
            let fin = jmod.declare_func_in_func(runtime.map_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MapGet(m, k) => {
            let mv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, m.0);
            let kv = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, k.0);
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
                let v = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, cv.0);
                b.ins().call(push, &[v]);
            }
            let fin = jmod.declare_func_in_func(runtime.closure_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
        Prim::MakeVec(kind, els) => {
            use crate::fz_ir::VecKindIr;
            use fz_runtime::fz_value::HeapKind;
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
                let v = tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, ev.0);
                b.ins().call(push, &[v]);
            }
            let fin = jmod.declare_func_in_func(runtime.vec_finalize_id, b.func);
            let inst = b.ins().call(fin, &[]);
            b.inst_results(inst)[0]
        }
    };
    Ok(LowerOut::Tagged(v))
}

/// Unbox an FzValue-tagged int (assumed Tag::Int — caller's responsibility) to
/// a raw i64 via arithmetic shift right.
fn unbox_int(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().sshr_imm(v, 3)
}

/// Per-fn env: SSA value table for every Var in scope. For most Vars the
/// value is a tagged FzValue (i64). For Vars in `raw_f64_vars` it is a raw
/// f64; for Vars in `raw_int_vars` it is a raw i64 (the unshifted int
/// payload, not the `(n << 3) | TAG_INT` tagged form). These exist so
/// arithmetic ops can produce native results and chain across multiple
/// stmts without going through a tag/untag round trip every time.
///
/// The accessors below centralise the repr conversions so call sites
/// don't have to spell them out. `tagged_get` is what every boundary
/// site (terminator args, halt val, builtin call args) wants — it boxes
/// raw f64 / raw i64 vars lazily. `as_raw_f64` and `as_raw_i64` are what
/// the typed-float / typed-int fast paths in `lower_prim` want — they
/// produce the raw value, unboxing tagged inputs as needed.
fn tagged_get<M: cranelift_module::Module>(
    env: &HashMap<u32, ir::Value>,
    raw_f64_vars: &std::collections::HashSet<u32>,
    raw_int_vars: &std::collections::HashSet<u32>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    v: u32,
) -> ir::Value {
    let val = *env.get(&v).expect("unbound var");
    if raw_f64_vars.contains(&v) {
        box_float_native(b, jmod, runtime, val)
    } else if raw_int_vars.contains(&v) {
        box_int(b, val)
    } else {
        val
    }
}

fn as_raw_f64(
    env: &HashMap<u32, ir::Value>,
    raw_f64_vars: &std::collections::HashSet<u32>,
    b: &mut FunctionBuilder<'_>,
    v: u32,
) -> ir::Value {
    let val = *env.get(&v).expect("unbound var");
    if raw_f64_vars.contains(&v) {
        val
    } else {
        unbox_float(b, val)
    }
}

fn as_raw_i64(
    env: &HashMap<u32, ir::Value>,
    raw_int_vars: &std::collections::HashSet<u32>,
    b: &mut FunctionBuilder<'_>,
    v: u32,
) -> ir::Value {
    let val = *env.get(&v).expect("unbound var");
    if raw_int_vars.contains(&v) {
        val
    } else {
        unbox_int(b, val)
    }
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
fn emit_dispatch_binop<M: cranelift_module::Module, F>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
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

/// Load the f64 payload of a boxed-float FzValue. The boxed-float heap
/// layout is `HeapHeader (16 bytes) + f64 payload (8 bytes)`; the tagged
/// FzValue's bits are the heap ptr (Tag::Ptr has tag bits 000). Caller
/// must already have proven Tag::Ptr+HeapKind::Float via the typer
/// (descr_is_float). fz-ul4.27.3.
fn unbox_float(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().load(types::F64, MemFlags::trusted(), v, 16)
}

/// Heap-allocate a fresh boxed float from a raw f64 and return its
/// FzValue ptr-bits. Bitcasts the f64 to i64 (the wire form fz_alloc_float
/// expects) and calls fz_alloc_float. fz-ul4.27.3.
fn box_float_native<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    f: ir::Value,
) -> ir::Value {
    let bits = b.ins().bitcast(types::I64, ir::MemFlags::new(), f);
    let fref = jmod.declare_func_in_func(runtime.alloc_float_id, b.func);
    let inst = b.ins().call(fref, &[bits]);
    b.inst_results(inst)[0]
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

    #[test]
    fn aot_compile_produces_object_with_main_symbol() {
        let src = "fn add1(n) do n + 1 end\nfn main() do print(add1(41)) end";
        let m = lower_src(src);
        let artifact = compile_aot(&m, "add1_smoke").expect("compile_aot");
        assert!(
            !artifact.object.is_empty(),
            "AOT object should be non-empty"
        );
        // Post-.6.3, compile_aot emits a C-callable `main` symbol that
        // wraps fz_aot_run. The artifact's main_symbol surfaces that for
        // the linker.
        let main_sym = artifact.main_symbol.expect("main_symbol set");
        assert_eq!(main_sym, "main", "expected C-callable main symbol");
        // Sanity: object-file magic bytes for the host target. ELF starts
        // with 0x7f 'E' 'L' 'F'; Mach-O starts with 0xfeedface/0xfeedfacf
        // (or their byte-swapped 64-bit variants).
        let magic_ok = matches!(
            &artifact.object[..4],
            [0x7f, b'E', b'L', b'F']
                | [0xce, 0xfa, 0xed, 0xfe]
                | [0xcf, 0xfa, 0xed, 0xfe]
                | [0xfe, 0xed, 0xfa, 0xce]
                | [0xfe, 0xed, 0xfa, 0xcf]
        );
        assert!(magic_ok, "unexpected object magic: {:02x?}", &artifact.object[..4]);
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
        use fz_runtime::fz_value::{FzValue, HeapHeader};
        use fz_runtime::heap::{
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

    // ----- fz-ul4.19.6: atom-table policy (shared, mutex-protected) -----

    /// Two Processes built from the SAME CompiledModule observe equal
    /// atom ids for the same atom literal. Atoms are u32s baked into
    /// compiled code; they're the same bytes regardless of which Process
    /// runs the code. Confirms .19.6's "global shared singleton" policy
    /// is the actual semantics today (per ir_lower::AtomTable being
    /// CompiledModule-scoped).
    #[test]
    fn atom_identity_preserved_across_processes_from_same_module() {
        // `:ok` halts as the atom's u32 id (well, the FzValue bits which
        // encode (id << 3) | TAG_ATOM = 0b010). Run two Processes; the
        // halt value must match because the atom id was assigned once
        // at compile time.
        let src = "fn main(), do: :ok";
        let m = lower_src(src);
        let compiled = compile(&m).unwrap();
        let entry = m.fn_by_name("main").unwrap().id;

        let mut pa = compiled.make_process();
        let mut pb = compiled.make_process();
        let ra = compiled.run_in(entry, &mut pa);
        let rb = compiled.run_in(entry, &mut pb);
        assert_eq!(ra, rb, "atom id stable across processes from the same module");
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
        use fz_runtime::fz_value::FzValue;
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::from_int(42).0), "42");
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::from_int(0).0), "0");
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::from_int(-7).0), "-7");
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::NIL.0), "nil");
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::TRUE.0), "true");
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::FALSE.0), "false");
        // Atom rendering needs a populated Process.atom_names; with an
        // empty table render falls back to `:atom_N`. The full
        // source-name path is verified end-to-end by the fixture matrix
        // (hello.fz post fz-ul4.25 re-bless).
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::from_atom_id(3).0), ":atom_3");
    }

    #[test]
    fn print_captures_atom_and_specials() {
        assert_eq!(
            capture_main("fn main() do\n  print(:ok)\n  print(true)\n  print(false)\nend"),
            vec![":ok", "true", "false"]
        );
    }

    // ----- .11.13 map tests -----

    #[test]
    fn print_atom_keyed_map_renders_canonically() {
        assert_eq!(
            capture_main("fn main(), do: print(%{a: 1, b: 2})"),
            vec!["%{:a => 1, :b => 2}"]
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
                "%{:a => 1, :b => 2}",
                "%{:a => 99, :b => 2}",
            ]
        );
    }

    #[test]
    fn gc_traces_map_keys_and_values() {
        let (halt_bits, _m) = run_main_after_heap_reset("fn main(), do: %{a: [1, 2, 3]}");
        let halt_bits = halt_bits as u64;
        assert_eq!(heap_live_count(), 4, "1 map + 3 cons cells");
        let root = fz_runtime::fz_value::FzValue(halt_bits);
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
            vec!["{1, :ok, true}"]
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
        let root = fz_runtime::fz_value::FzValue(halt_bits);
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
        let root = fz_runtime::fz_value::FzValue(halt_bits);
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
        let root = fz_runtime::fz_value::FzValue(halt as u64);
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
        let p = fz_runtime::fz_value::FzValue(halt).unbox_ptr().unwrap();
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
        let root = fz_runtime::fz_value::FzValue(halt_bits);
        let p_before = root.unbox_ptr().unwrap();
        heap_gc(&[root]);
        assert_eq!(heap_live_count(), 1);
        let p_after = fz_runtime::fz_value::FzValue(halt_bits).unbox_ptr().unwrap();
        assert_eq!(p_before, p_after);
        assert_eq!(fz_runtime::heap::Heap::vec_len(p_after), 3);
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
