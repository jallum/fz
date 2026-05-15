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

use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, SpecId, Stmt, Term, UnOp, Var};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
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
        Self {
            message: message.into(),
            span: crate::diag::Span::DUMMY,
        }
    }
    pub fn with_span(mut self, span: crate::diag::Span) -> Self {
        self.span = span;
        self
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
    fn from(s: String) -> Self {
        Self::new(s)
    }
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
    /// fz-cps.1.7 — zero-capture closure-target spec singletons resolved
    /// to code addresses at JIT-finalize time. `(cl_sid, fn_id, code_ptr)`
    /// per entry. `make_process` allocates one 24-byte off-heap closure
    /// per entry and registers it at `Process.static_closures[cl_sid]`.
    /// See docs/cps-in-clif.md §8.2.
    pub(crate) static_closure_targets: Vec<(u32, u32, *const u8, u32 /* halt_kind */)>,
    /// fz-cps.1.11 — finalized address of the SystemV scheduler shim
    /// `fz_resume_park(msg, parked_cont) -> i64`. The scheduler calls
    /// this via Rust FFI when a Blocked task wakes; the shim loads
    /// `parked_cont+16` and Tail-CC indirect-calls the cont body.
    pub(crate) resume_park_addr: *const u8,
    /// fz-cps.1.11 — finalized address of the SystemV scheduler shim
    /// `fz_spawn_entry(closure) -> i64`. Allocates a halt-cont and
    /// Tail-CC indirect-calls the zero-arg closure with `(self,
    /// halt_cont)`. Used by `Runtime::spawn_closure` to launch a task.
    pub(crate) spawn_entry_addr: *const u8,
    /// fz-cps.5 — finalized address of the SystemV scheduler shim
    /// `fz_main_entry(main_fp) -> i64`. Allocates a halt-cont and
    /// Tail-CC indirect-calls main with `(halt_cont)`. Used by
    /// `Runtime::spawn(fn_id)` / `CompiledModule::run_internal`.
    pub(crate) main_entry_addr: *const u8,
    /// fz-ul4.27.22.3 — finalized addresses of the three Cranelift-emitted
    /// `fz_halt_cont_body_{tagged,i64,f64}` Tail-CC fns, indexed by repr
    /// kind (0=Tagged, 1=RawInt, 2=RawF64). `make_process` seeds matching
    /// Process singletons via `init_halt_cont_singletons`. Null slots
    /// (unused reprs for this program) are pre-populated lazily by
    /// `fz_get_halt_cont` at first use.
    pub(crate) halt_cont_body_addrs: [*const u8; 3],
    /// fz-ul4.27.22.3 — per-FnId halt-cont singleton kind. When the
    /// Rust scheduler dispatches a task via `fz_main_entry`, it picks
    /// `process.halt_cont_singletons[kind]` matching the entry fn's
    /// any-key return repr. Default kind 0 (Tagged) for fns not in
    /// the map.
    pub(crate) fn_halt_kinds: HashMap<u32, u32>,
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

    /// fz-cps.1.7 — registered zero-capture closure-target specs. Each
    /// entry corresponds to one Process-level static singleton allocated
    /// at `make_process` time. See docs/cps-in-clif.md §8.2.
    pub fn static_closure_targets(&self) -> &[(u32, u32, *const u8, u32)] {
        &self.static_closure_targets
    }

    pub fn schema_for(&self, fn_id: FnId) -> &Schema {
        &self.schemas[fn_id.0 as usize]
    }

    /// Construct a fresh Process bound to this module's compile-time data
    /// (SchemaRegistry, frame_sizes, bs_tuple_arity*_schema). Multiple
    /// Processes can be made from the same CompiledModule and run
    /// concurrently (one worker at a time per Process; libdispatch model).
    pub fn make_process(&self) -> Process {
        let mut p = Process {
            heap: fz_runtime::heap::Heap::new(64 * 1024, std::rc::Rc::clone(&self.user_schemas)),
            halt_value: 0,
            map_builder: None,
            bs_builder: None,
            vec_builder: None,
            frame_sizes: self.frame_sizes.clone(),
            atom_names: self.atom_names.clone(),
            bs_tuple_arity1_schema: self.bs_tuple_arity1_schema,
            bs_tuple_arity3_schema: self.bs_tuple_arity3_schema,
            pid: 0,
            state: ProcessState::New,
            next_frame: std::ptr::null_mut(),
            mailbox: std::collections::VecDeque::new(),
            parked_cont: std::ptr::null_mut(),
            halt_cont_singletons: [std::ptr::null_mut(); 3],
            pending_closure_entry: std::ptr::null_mut(),
            pending_main_entry: std::ptr::null_mut(),
            pending_main_entry_fn_id: 0,
            static_closures: Vec::new(),
            static_closure_bufs: Vec::new(),
        };
        // fz-cps.1.7 — allocate one static singleton per zero-cap
        // closure-target spec. See docs/cps-in-clif.md §8.2.
        p.init_static_closures(&self.static_closure_targets);
        // fz-ul4.27.22.3 — seed all three halt-cont singletons; each
        // slot's body sig matches its repr kind (Tagged / RawInt / RawF64).
        p.init_halt_cont_singletons(self.halt_cont_body_addrs);
        p
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
        /// Park-time GC trigger (cps-in-clif §7). Called at every
        /// shim-return boundary. Reads `process.heap.should_gc()`; if set,
        /// invokes Cheney with `parked_cont` as the sole root (§6.4 / §7).
        /// `gc()` may rewrite `parked_cont` to its to-space copy.
        fn park_time_gc(process: &mut Process) {
            if !process.heap.should_gc() {
                return;
            }
            process.heap.gc(&mut process.parked_cont);
            process.heap.clear_should_gc_flag();
        }

        // fz-cps.1.11 — wakeup path: if the task has a parked_cont and
        // a message waiting, dispatch via the SystemV→Tail-CC
        // fz_resume_park shim. The shim cross-CC calls the cont closure
        // (`load parked_cont+16; call_indirect Tail (msg, parked_cont)`).
        // The cont chain runs synchronously to halt; halt_value is set
        // before fz_resume_park returns.
        if !process.parked_cont.is_null() {
            if let Some(msg) = process.mailbox.pop_front() {
                let cont_ptr = process.parked_cont;
                process.parked_cont = std::ptr::null_mut();
                type ResumePark = extern "C" fn(u64, u64) -> i64;
                let f: ResumePark = unsafe { std::mem::transmute(self.resume_park_addr) };
                let _ = f(msg.0, cont_ptr as u64);
                process.next_frame = std::ptr::null_mut();
                park_time_gc(process);
                return;
            }
        }
        // fz-cps.5 — fresh main-style task entry: a fn ptr was queued
        // by `Runtime::spawn(fn_id)` or `run_internal`. Dispatch via
        // fz_main_entry (SystemV→Tail-CC). The fn body runs to halt
        // or Receive synchronously.
        if !process.pending_main_entry.is_null() {
            let fp = process.pending_main_entry;
            process.pending_main_entry = std::ptr::null_mut();
            // fz-ul4.27.22.3 — pick halt-cont singleton matching the
            // entry fn's return-repr kind. `pending_main_entry_fn_id`
            // is set alongside `pending_main_entry` by Runtime::spawn.
            let kind = self
                .fn_halt_kinds
                .get(&process.pending_main_entry_fn_id)
                .copied()
                .unwrap_or(0) as usize;
            let halt_cl = process.halt_cont_singletons[kind] as u64;
            type MainEntry = extern "C" fn(u64, u64) -> i64;
            let f: MainEntry = unsafe { std::mem::transmute(self.main_entry_addr) };
            let _ = f(fp as u64, halt_cl);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.1.11 — fresh task entry: a closure was queued by
        // `Runtime::spawn_closure`. Dispatch via fz_spawn_entry (the
        // SystemV→Tail-CC launch shim). The closure body runs to halt
        // or Receive synchronously; on Receive it sets parked_cont and
        // the next quantum's wakeup path picks it up.
        if !process.pending_closure_entry.is_null() {
            let cl_ptr = process.pending_closure_entry;
            process.pending_closure_entry = std::ptr::null_mut();
            type SpawnEntry = extern "C" fn(u64) -> i64;
            let f: SpawnEntry = unsafe { std::mem::transmute(self.spawn_entry_addr) };
            let _ = f(cl_ptr as u64);
            process.next_frame = std::ptr::null_mut();
            park_time_gc(process);
            return;
        }
        // fz-cps.5 — the trampoline loop is unreachable. All fz fns are
        // Tail-CC; dispatch flows through the three SystemV shims above
        // (parked_cont resume, pending_main_entry, pending_closure_entry).
        // No uniform fns exist, so no frame-by-frame dispatch is needed.
        process.next_frame = std::ptr::null_mut();
    }

    fn run_internal(&self, fn_id: FnId) -> i64 {
        // fz-cps.5 / fz-ul4.27.22.3 — every fz fn is Tail-CC. Dispatch
        // via fz_main_entry, passing the halt-cont singleton matching
        // the entry fn's return-repr kind.
        let fp = self
            .fn_ptrs
            .get(&fn_id.0)
            .copied()
            .unwrap_or_else(|| panic!("no fn ptr for entry {}", fn_id.0));
        let kind = self.fn_halt_kinds.get(&fn_id.0).copied().unwrap_or(0) as usize;
        let halt_cl = current_process().halt_cont_singletons[kind] as u64;
        type MainEntry = extern "C" fn(u64, u64) -> i64;
        let f: MainEntry = unsafe { std::mem::transmute(self.main_entry_addr) };
        let _ = f(fp as u64, halt_cl);
        current_process().halt_value
    }
}

// Process, PidId, ProcessState, CURRENT_PROCESS, DEFAULT_PROCESS, and
// current_process() moved to src/process.rs (fz-ul4.23.4.2). Re-exported
// here for back-compat with downstream users (runtime.rs, ir_runtime.rs,
// tests) while consumers migrate to `fz_runtime::process::*`.
pub use fz_runtime::process::{
    CURRENT_PROCESS, DEFAULT_PROCESS, PidId, Process, ProcessState, current_process,
};

// Runtime FFI fns called from JIT'd code now live in src/ir_runtime.rs.
// Value rendering lives in fz_runtime::fz_value::debug (fz-ul4.23.4.3).

thread_local! {
    /// (.11.24.4) Per-fn Cranelift IR display text captured by compile()
    /// after compile_fn but before define_function consumes the context.
    /// Test-only; enable by calling `ir_text_record_enable()` before compile.
    pub static IR_TEXT_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = const { std::cell::RefCell::new(None) };
    /// (fz-ul4.23.8) Per-fn machine-code disassembly captured by compile()
    /// when set_disasm is on. Enable with `asm_record_enable()` before
    /// compile; drain with `asm_record_take()` after.
    pub static ASM_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = const { std::cell::RefCell::new(None) };
    /// fz-ul4.32.1 — per-fn Value → IR Descr map, populated by compile_fn
    /// at end-of-body. Consumed by the IR_TEXT_RECORD assembly step to
    /// annotate each `vN` definition with its typer Descr. Only the
    /// values bound to fz Vars (block params, Prim results, etc.) are
    /// recorded; pure Cranelift intermediates (iconst, ishl_imm, ...)
    /// have no fz-level Descr and stay unannotated.
    pub static VALUE_DESCR_RECORD: std::cell::RefCell<Option<HashMap<u32, crate::types::Descr>>>
        = const { std::cell::RefCell::new(None) };
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
    // fz-ul4.32.1 — pair the value-descr recorder so the assembled
    // text gets typer Descr annotations alongside the raw CLIF.
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = Some(HashMap::new()));
}

pub fn ir_text_record_take() -> Vec<(String, String)> {
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = None);
    IR_TEXT_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// fz-ul4.32.1 — Build the per-fn header block that precedes annotated
/// CLIF. Two lines: typer's param/return Descrs and codegen's ArgReprs.
/// Disagreement between the two reveals where seam coercion lands.
fn build_typer_header(
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_typer::FnTypes,
    spec_key: &[crate::types::Descr],
    param_reprs: &[ArgRepr],
    return_repr: ArgRepr,
) -> String {
    use std::fmt::Write as _;
    let entry_params = &f.block(f.entry).params;
    let typer_params: Vec<String> = entry_params
        .iter()
        .map(|v| match ft.vars.get(v) {
            Some(d) => format!("{}", d),
            None => "?".to_string(),
        })
        .collect();
    // Join return Descrs across all Term::Return sites in this fn.
    let mut return_descrs: Vec<String> = Vec::new();
    for blk in &f.blocks {
        if let crate::fz_ir::Term::Return(v) = &blk.terminator {
            let d = ft
                .vars
                .get(v)
                .map(|d| format!("{}", d))
                .unwrap_or_else(|| "?".into());
            if !return_descrs.contains(&d) {
                return_descrs.push(d);
            }
        }
    }
    let return_str = if return_descrs.is_empty() {
        "_".to_string()
    } else {
        return_descrs.join(" | ")
    };
    let codegen_repr = |r: &ArgRepr| -> &'static str {
        match r {
            ArgRepr::Tagged => "Tagged",
            ArgRepr::RawInt => "RawInt",
            ArgRepr::RawF64 => "RawF64",
        }
    };
    let codegen_params: Vec<String> = param_reprs
        .iter()
        .map(|r| codegen_repr(r).to_string())
        .collect();
    let key_params: Vec<String> = spec_key.iter().map(|d| format!("{}", d)).collect();
    let mut out = String::new();
    let _ = writeln!(
        out,
        ";   @spec   {}({}) -> {}",
        f.name,
        typer_params.join(", "),
        return_str
    );
    let _ = writeln!(out, ";   @key    [{}]", key_params.join(", "));
    let _ = writeln!(
        out,
        ";   @abi    ({}) -> {}",
        codegen_params.join(", "),
        codegen_repr(&return_repr)
    );
    out
}

/// fz-ul4.32.1 — Annotate raw Cranelift IR text with IR-level Descrs.
///
/// Inputs:
///   - `raw`: the text from `ctx.func.display()`.
///   - `value_descrs`: Value.as_u32() → typer Descr for fz-Var-bound values.
///   - `header`: pre-built header lines (typer params/return, codegen
///     param_reprs/return_repr). Already starts with `; `.
///
/// Output: header lines + annotated CLIF. Per-`vN = ...` definitions get
/// an inline `; vN :: <Descr>` comment appended; pure intermediates with
/// no fz Var binding are left alone. The `block0(...)` line annotates
/// each block-param with its Descr inline.
fn annotate_clif_dump(
    raw: &str,
    value_descrs: &HashMap<u32, crate::types::Descr>,
    header: &str,
) -> String {
    use std::fmt::Write as _;
    let mut out = String::new();
    out.push_str(header);
    if !header.ends_with('\n') {
        out.push('\n');
    }
    for line in raw.lines() {
        let trimmed = line.trim_start();
        // Block header: `blockN(v0: ty, v1: ty, ...):`
        if trimmed.starts_with("block") && trimmed.contains('(') && trimmed.ends_with(':') {
            let _ = writeln!(out, "{}", annotate_block_header(line, value_descrs));
            continue;
        }
        // Value definition: `    vN = <op> ...`
        if let Some(rest) = trimmed.strip_prefix('v') {
            if let Some((id_str, _)) = rest.split_once(' ') {
                if let Ok(id) = id_str.parse::<u32>() {
                    // Confirm it's actually `vN =` (not `vN+16` in a load).
                    if rest
                        .split_once(' ')
                        .map(|x| x.1.starts_with('='))
                        .unwrap_or(false)
                    {
                        if let Some(d) = value_descrs.get(&id) {
                            let _ = writeln!(out, "{}    ;; v{} :: {}", line.trim_end(), id, d);
                            continue;
                        }
                    }
                }
            }
        }
        let _ = writeln!(out, "{}", line);
    }
    out
}

/// Inline-annotate the `(vN: ty, ...)` portion of a block header with the
/// IR Descr of each param. Skips params whose value-id is absent from
/// `value_descrs`.
fn annotate_block_header(line: &str, value_descrs: &HashMap<u32, crate::types::Descr>) -> String {
    // Append a trailing `; vN :: Descr  vM :: Descr` comment AFTER the
    // existing line, leaving the original CLIF text intact.
    let Some(open) = line.find('(') else {
        return line.to_string();
    };
    let Some(close) = line.rfind(')') else {
        return line.to_string();
    };
    if close <= open + 1 {
        return line.to_string();
    }
    let inner = &line[open + 1..close];
    let mut notes: Vec<String> = Vec::new();
    for p in inner.split(',') {
        let p_trim = p.trim();
        if let Some(rest) = p_trim.strip_prefix('v') {
            if let Some((id_str, _ty)) = rest.split_once(':') {
                if let Ok(id) = id_str.trim().parse::<u32>() {
                    if let Some(d) = value_descrs.get(&id) {
                        notes.push(format!("v{} :: {}", id, d));
                    }
                }
            }
        }
    }
    if notes.is_empty() {
        line.to_string()
    } else {
        format!("{}    ;; {}", line.trim_end(), notes.join(", "))
    }
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
// (`((a^1) | (b^1)) & 7 == 0`); when at least one operand is non-Int the
// slow arm promotes both to f64 via fz_promote_f64 and emits native
// fadd/fsub/fmul/fdiv (or fz_fmod for `%`, since Cranelift has no frem),
// then boxes via fz_alloc_float. fz-ul4.27.9 inlined the slow path —
// previously a call to fz_arith_*. Typed float-float fast paths
// (.27.3) and typed int-int fast paths (.27.5.3) sit in front of the
// dispatch entirely. Eq/Neq do NOT promote: `1 == 1.0` is false.

// fz_alloc_float moved to ir_runtime.rs (.23.4.7).

// ----- fz-ul4.19.2: scheduler-bound builtins (spawn / self) -----
//
// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
// Calling either outside the scheduler path panics with a clear message.

/// fz_spawn(closure_bits) -> pid_bits. Extracts fn_id from the closure
// heap object and enqueues a new task at that fn. Returns the pid as a
// boxed FzValue Int (Pid-as-struct deferred to a follow-up).
//
// v1 restriction: closure must have ZERO captures. Captured values
// would need to be copied into the new task's heap (.19.3 territory);
// for v1 spawn takes plain fn references (closures with no captures).
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
    flag_builder
        .set("is_pic", if pic { "true" } else { "false" })
        .unwrap();
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
/// fz-ul4.27.6.2.1 — Join the Descrs of every `Term::Return` operand in a
/// fn's blocks. For a fn whose only exits are TailCall / Halt / Goto / If
/// (no Return), the result is `any`. .6.2.2 consumes this to build per-fn
/// typed Signatures: an int-only return becomes `i64`, a float-only return
/// becomes `f64`, anything else stays `i64` (tagged FzValue).
fn join_return_descrs(
    f: &crate::fz_ir::FnIr,
    ft: &crate::ir_typer::FnTypes,
) -> crate::types::Descr {
    let mut joined: Option<crate::types::Descr> = None;
    for b in &f.blocks {
        if let Term::Return(v) = &b.terminator {
            let d = ft
                .vars
                .get(v)
                .cloned()
                .unwrap_or_else(crate::types::Descr::any);
            joined = Some(match joined {
                Some(prev) => prev.union(&d),
                None => d,
            });
        }
    }
    joined.unwrap_or_else(crate::types::Descr::any)
}

/// fz-ul4.27.13 — How a fz arg/return rides the Cranelift ABI for a native
/// fn. `Tagged` is the default FzValue i64 (low 3 bits = tag); `RawInt` is
/// an unshifted int payload as i64; `RawF64` is a raw f64.
///
/// Per-spec param/return reprs are derived from `ir_typer`'s Descrs:
/// float-only → `RawF64`, int-only → `RawInt`, else `Tagged`. `build_fn_
/// signature` picks the AbiParam type from the repr; `compile_fn` populates
/// `raw_*_vars` to match; call sites coerce at the seam.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ArgRepr {
    Tagged,
    RawInt,
    RawF64,
}

impl ArgRepr {
    fn from_descr(d: &crate::types::Descr) -> ArgRepr {
        if d.is_subtype(&crate::types::Descr::float()) {
            ArgRepr::RawF64
        } else if d.is_subtype(&crate::types::Descr::int()) {
            ArgRepr::RawInt
        } else {
            ArgRepr::Tagged
        }
    }
    fn cl_type(&self) -> types::Type {
        match self {
            ArgRepr::RawF64 => types::F64,
            _ => types::I64,
        }
    }
    /// fz-ul4.27.22.3 — halt-cont singleton kind. 0=Tagged, 1=RawInt, 2=RawF64.
    fn halt_kind(&self) -> u32 {
        match self {
            ArgRepr::Tagged => 0,
            ArgRepr::RawInt => 1,
            ArgRepr::RawF64 => 2,
        }
    }
}

/// fz-ul4.27.22.3 — pick the halt_cont_body FuncId matching `repr`.
fn halt_cont_body_id_for(runtime: &RuntimeRefs, repr: ArgRepr) -> FuncId {
    match repr {
        ArgRepr::Tagged => runtime.halt_cont_body_tagged_id,
        ArgRepr::RawInt => runtime.halt_cont_body_i64_id,
        ArgRepr::RawF64 => runtime.halt_cont_body_f64_id,
    }
}

/// Per-spec entry-param ArgReprs. Length matches the spec's entry block's
/// param count.
fn build_param_reprs(f: &crate::fz_ir::FnIr, ft: &crate::ir_typer::FnTypes) -> Vec<ArgRepr> {
    let entry = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    entry
        .params
        .iter()
        .map(|p| {
            let d = ft
                .vars
                .get(p)
                .cloned()
                .unwrap_or_else(crate::types::Descr::any);
            ArgRepr::from_descr(&d)
        })
        .collect()
}

/// fz-ul4.27.6.2.2 — Per-fn Cranelift Signature.
///
/// `is_native = false` → uniform `(frame_ptr: i64, host_ctx: i64) -> i64`,
/// matching the body shape produced by `compile_fn` for trampoline-driven
/// fns: frame slots for entry params, emit_return writes into the cont
/// frame and returns the cont frame ptr to the trampoline.
///
/// `is_native = true` → typed-arity signature reflecting the fn's entry
/// params + `host_ctx` + return. fz-ul4.27.13 promotes per-Descr typing:
/// each entry param's AbiParam type derives from its `ArgRepr` (RawF64 →
/// `f64`, RawInt/Tagged → `i64`); the return derives from `return_descr`
/// the same way. `host_ctx` is always `i64`.
fn build_fn_signature(
    param_reprs: &[ArgRepr],
    ret_repr: ArgRepr,
    is_native: bool,
    needs_host_ctx: bool,
    is_cont_fn: bool,
    closure_target_n_caps: Option<usize>,
) -> Signature {
    if !is_native {
        // Uniform fns always include host_ctx — the trampoline ABI is
        // fixed at `(frame_ptr, host_ctx) -> i64`; `needs_host_ctx` is
        // ignored here. (Trimming uniform sigs would require an
        // entry-harness refactor; tracked under .27.20.)
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64)); // frame_ptr
        sig.params.push(AbiParam::new(types::I64)); // host_ctx
        sig.returns.push(AbiParam::new(types::I64)); // next frame_ptr
        return sig;
    }
    // Native fns use the `Tail` calling convention so that recursive
    // tail calls can lower to `return_call` (which the SystemV ABI does
    // not permit). Without TCO, count_100k_stays_bounded blows the stack.
    // fz-ul4.27.19: append host_ctx only when this fn (or some callee
    // it forwards into) actually consumes it.
    let mut sig = Signature::new(CallConv::Tail);
    if is_cont_fn {
        // fz-ul4.27.22.3 cont fn sig per §2.1: `(result, self:i64) tail`.
        // result uses param_reprs[0]'s cl_type (RawInt=i64, RawF64=f64,
        // Tagged=i64). Producer's Term::Return sig matches via
        // return_reprs[producer_spec_id]; typer's effective_return walk
        // ensures producer and consumer agree at the seam.
        sig.params.push(AbiParam::new(param_reprs[0].cl_type())); // result
        sig.params.push(AbiParam::new(types::I64)); // self
    } else if let Some(n_caps) = closure_target_n_caps {
        // fz-cps.1.2 closure-target fn sig per §2.1:
        // `(args..., self:i64, cont:i64) tail`. Captures (param_reprs[0..n_caps])
        // are NOT Cranelift params — body loads them from self+24+8*i.
        // Args are param_reprs[n_caps..].
        for r in &param_reprs[n_caps..] {
            sig.params.push(AbiParam::new(r.cl_type()));
        }
        sig.params.push(AbiParam::new(types::I64)); // self
        sig.params.push(AbiParam::new(types::I64)); // cont
        let _ = needs_host_ctx;
    } else {
        for r in param_reprs {
            sig.params.push(AbiParam::new(r.cl_type()));
        }
        if needs_host_ctx {
            sig.params.push(AbiParam::new(types::I64)); // host_ctx
        }
        // fz-cps.1.a — trailing cont:i64 per §2.1.
        sig.params.push(AbiParam::new(types::I64)); // cont
    }
    if is_native {
        // fz-cps.1.2: native fn return canonicalized to i64. Term::Return
        // is now `return_call_indirect sig(i64, i64) -> i64 tail`; the
        // caller's return type must match the target's per Cranelift's
        // tail-call verifier. Coercion happens at the return site.
        let _ = ret_repr;
        sig.returns.push(AbiParam::new(types::I64));
    } else {
        sig.returns.push(AbiParam::new(ret_repr.cl_type()));
    }
    sig
}

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
    /// + `fz_aot_run_main` can resolve them at runtime.
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
    /// fz-ul4.27.6.2.1 — Fns that may suspend (Receive / closure ops / any
    /// fn transitively calling such). Used by .6.2.4 to decide ABI per fn.
    pub parking_reachable: std::collections::HashSet<FnId>,
    /// fz-ul4.27.6.2.1 — Fns eligible for typed native-call ABI in .6.2.
    /// See `parking::natively_callable` for qualification rules.
    pub natively_callable: std::collections::HashSet<FnId>,
    /// fz-ul4.27.6.2.1 — Per-fn join of all `Term::Return` operand Descrs.
    /// For fns with no Term::Return (only Halt / TailCall) this is `any`,
    /// which is the conservative default for .6.2.2's Signature builder.
    /// Indexed by FnId.0.
    pub return_descrs: Vec<crate::types::Descr>,
    /// fz-ul4.29.2 — (FnId, input-Descr-tuple) ↔ SpecId mapping.
    /// Resolves callsite callees to their compiled spec. fz-ul4.29.2.1
    /// makes this load-bearing for narrow-spec consumption and converts
    /// the eight FnId.0-keyed fields above to SpecId.0 in concert.
    pub spec_registry: SpecRegistry,
    /// fz-cps.1.7 — zero-capture closure-target specs.
    /// `(cl_sid, fn_id, stub_func_id)` per entry. JIT finalize resolves
    /// stub_func_id to a code address; the resulting
    /// `CompiledModule.static_closure_targets` is consumed by
    /// `make_process` to populate `Process.static_closures`. AOT carries
    /// the same list as a startup-init data table (fz-cps.1.7 AOT path is
    /// out of scope until aot rebuilds; see ticket notes).
    pub static_closure_targets: Vec<(u32, u32, FuncId, u32 /* halt_kind */)>,
    /// fz-cps.1.11 — fz_resume_park scheduler-wakeup shim FuncId.
    pub resume_park_id: FuncId,
    /// fz-cps.1.11 — fz_spawn_entry scheduler-launch shim FuncId.
    pub spawn_entry_id: FuncId,
    /// fz-cps.5 — fz_main_entry scheduler-launch shim FuncId.
    pub main_entry_id: FuncId,
    /// fz-ul4.27.22.3 — three fz_halt_cont_body fns indexed by repr
    /// kind (0=Tagged, 1=RawInt, 2=RawF64). Sigs: (Tagged|i64|f64, i64)
    /// -> i64 tail. Bodies call the matching halt_implicit_* and return 0.
    pub halt_cont_body_ids: [FuncId; 3],
    /// fz-ul4.27.22.3 — per-FnId halt-cont singleton kind (the entry
    /// fn's any-key return repr). Used by the Rust scheduler to pick
    /// the matching halt_cont_singletons slot when dispatching via
    /// fz_main_entry.
    pub fn_halt_kinds: HashMap<u32, u32>,
}

/// fz-ul4.29.2 — Two-way mapping between (FnId, input-Descr-tuple) and
/// SpecId. Each compiled body has one entry; SpecIds are dense from 0.
///
/// In .29.2 every FnIr has exactly one SpecId (its any-key spec), so
/// `SpecId.0 == FnId.0` is an invariant — preserves bit-identical CLIF
/// vs. the pre-atom baseline. fz-ul4.29.2.1 admits multiple SpecIds per
/// FnId for narrow specs, at which point the invariant relaxes.
#[derive(Clone, Default)]
pub struct SpecRegistry {
    /// keys[spec_id.0 as usize] = (callee, input_descrs).
    keys: Vec<(FnId, Vec<crate::types::Descr>)>,
    /// (callee, input_descrs) → SpecId. Exact-match fast path for `resolve`.
    lookup: HashMap<(FnId, Vec<crate::types::Descr>), SpecId>,
    /// fz-ul4.29.11 — per-FnId list of registered SpecIds, used by the
    /// subsumption fallback in `resolve`. Excludes sentinel slots inserted
    /// by `register_any_key_at`'s padding (those have no real registration).
    by_fn: HashMap<FnId, Vec<SpecId>>,
}

impl SpecRegistry {
    pub fn new() -> Self {
        Self::default()
    }

    /// Register a `(fn_id, input_descrs)` pair; return its SpecId. If
    /// already registered, returns the existing SpecId without
    /// duplicating.
    pub fn register(&mut self, fn_id: FnId, input_descrs: Vec<crate::types::Descr>) -> SpecId {
        let key = (fn_id, input_descrs);
        if let Some(&id) = self.lookup.get(&key) {
            return id;
        }
        let id = SpecId(self.keys.len() as u32);
        self.keys.push(key.clone());
        self.lookup.insert(key, id);
        self.by_fn.entry(fn_id).or_default().push(id);
        id
    }

    /// Register an any-key spec so that its SpecId.0 equals `fn_id.0`.
    /// Pads with dead sentinel slots for any intervening missing FnIds
    /// (cps_split may have produced sparse FnId.0 values when fns get
    /// dropped or reordered). Sentinel slots are filled with the same
    /// (fn_id, key) so `iter()` is well-shaped — they're never reached
    /// because their fn_id doesn't appear in the module. Callers must
    /// register any-keys in FnId.0 order.
    pub fn register_any_key_at(
        &mut self,
        fn_id: FnId,
        input_descrs: Vec<crate::types::Descr>,
    ) -> SpecId {
        let target = fn_id.0 as usize;
        while self.keys.len() < target {
            // Sentinel: tag with the slot's FnId so iter() reports a
            // self-consistent (SpecId, FnId, key) tuple; this slot's
            // FnId doesn't exist in the module, so the slot is dead.
            let sentinel_fn = FnId(self.keys.len() as u32);
            let sentinel_key = (sentinel_fn, Vec::new());
            self.keys.push(sentinel_key);
            // No `lookup` entry — the slot is unreachable from resolve().
        }
        let id = SpecId(self.keys.len() as u32);
        debug_assert_eq!(id.0, fn_id.0);
        let key = (fn_id, input_descrs);
        self.keys.push(key.clone());
        self.lookup.insert(key, id);
        self.by_fn.entry(fn_id).or_default().push(id);
        id
    }

    /// Look up the SpecId for `(fn_id, input_descrs)`, or `None` if no
    /// covering spec is registered.
    ///
    /// fz-ul4.29.11 — two-tier dispatch:
    ///   1. **Fast path**: exact-match HashMap lookup. Typer and codegen
    ///      often produce identical Descrs for the same callsite; this
    ///      path covers that common case in O(1).
    ///   2. **Slow path**: subsumption search over per-FnId specs. A
    ///      registered spec covers a query iff `query[i] ⊆ key[i]` for
    ///      every element (the spec's body was compiled assuming inputs
    ///      of type `key`, so a narrower query is safe to dispatch to it).
    ///      Among covering candidates, picks the subtype-minimal one —
    ///      the most-specialized safe dispatch. Deterministic SpecId
    ///      tiebreak when candidates are subtype-incomparable.
    ///
    /// Best-match specialization quality (typer registering tight-enough
    /// specs at every callsite) is a separate concern — different ticket.
    pub fn resolve(&self, fn_id: FnId, input_descrs: &[crate::types::Descr]) -> Option<SpecId> {
        // Fast path.
        if let Some(&id) = self.lookup.get(&(fn_id, input_descrs.to_vec())) {
            return Some(id);
        }
        // Slow path: subsumption search.
        let sids = self.by_fn.get(&fn_id)?;
        let arity = input_descrs.len();
        let mut covers: Vec<SpecId> = sids
            .iter()
            .copied()
            .filter(|sid| {
                let key = &self.keys[sid.0 as usize].1;
                key.len() == arity
                    && input_descrs
                        .iter()
                        .zip(key.iter())
                        .all(|(q, k)| q.is_subtype(k))
            })
            .collect();
        if covers.is_empty() {
            return None;
        }
        // Pick subtype-minimal: a candidate is "minimal" if no other
        // candidate is a strict subtype of it on every axis. Tiebreak by
        // lowest SpecId so the choice is deterministic across runs.
        let key_of = |sid: SpecId| -> &Vec<crate::types::Descr> { &self.keys[sid.0 as usize].1 };
        let strictly_subsumed_by_other = |sid: SpecId, others: &[SpecId]| -> bool {
            let k = key_of(sid);
            others.iter().any(|&other| {
                if other == sid {
                    return false;
                }
                let ok = key_of(other);
                if ok.len() != k.len() {
                    return false;
                }
                let all_le = ok.iter().zip(k.iter()).all(|(o, kk)| o.is_subtype(kk));
                let any_strict = ok.iter().zip(k.iter()).any(|(o, kk)| !kk.is_subtype(o));
                all_le && any_strict
            })
        };
        covers.sort_by_key(|s| s.0);
        for sid in &covers {
            if !strictly_subsumed_by_other(*sid, &covers) {
                return Some(*sid);
            }
        }
        // Mutually subtype-equivalent set — pick lowest SpecId.
        covers.into_iter().min_by_key(|s| s.0)
    }

    /// Look up a fn's any-key SpecId (the conservative fallback used by
    /// closure / Spawn / Receive paths, and by every callsite under
    /// .29.2 until .29.2.1 enables narrow consumption).
    pub fn any_key(&self, fn_id: FnId, n_params: usize) -> SpecId {
        let key = vec![crate::types::Descr::any(); n_params];
        *self
            .lookup
            .get(&(fn_id, key))
            .expect("any-key spec must always be registered for every fn")
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }

    /// Iterate all `(SpecId, &FnId, &input_descrs)` entries in SpecId
    /// order. Used by the codegen pipeline to walk every compiled body.
    pub fn iter(&self) -> impl Iterator<Item = (SpecId, FnId, &[crate::types::Descr])> {
        self.keys
            .iter()
            .enumerate()
            .map(|(i, (f, d))| (SpecId(i as u32), *f, d.as_slice()))
    }
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
        builder.symbol(
            "fz_print_value",
            fz_runtime::ir_runtime::fz_print_value as *const u8,
        );
        // fz-ul4.27.7 (VR.5b): typed print helpers — JIT routes here when
        // the arg Descr is monomorphic, skipping the boxing round-trip.
        builder.symbol("fz_print_i64", fz_runtime::fz_print_i64 as *const u8);
        builder.symbol("fz_print_f64", fz_runtime::fz_print_f64 as *const u8);
        builder.symbol("fz_halt", fz_runtime::ir_runtime::fz_halt as *const u8);
        builder.symbol(
            "fz_halt_implicit",
            fz_runtime::ir_runtime::fz_halt_implicit as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_i64",
            fz_runtime::ir_runtime::fz_halt_implicit_i64 as *const u8,
        );
        builder.symbol(
            "fz_halt_implicit_f64",
            fz_runtime::ir_runtime::fz_halt_implicit_f64 as *const u8,
        );
        builder.symbol(
            "fz_alloc_frame",
            fz_runtime::ir_runtime::fz_alloc_frame as *const u8,
        );
        builder.symbol(
            "fz_alloc_list_cons",
            fz_runtime::ir_runtime::fz_alloc_list_cons as *const u8,
        );
        builder.symbol(
            "fz_alloc_struct",
            fz_runtime::ir_runtime::fz_alloc_struct as *const u8,
        );
        builder.symbol(
            "fz_bs_begin",
            fz_runtime::ir_runtime::fz_bs_begin as *const u8,
        );
        builder.symbol(
            "fz_bs_write_field",
            fz_runtime::ir_runtime::fz_bs_write_field as *const u8,
        );
        builder.symbol(
            "fz_bs_finalize",
            fz_runtime::ir_runtime::fz_bs_finalize as *const u8,
        );
        builder.symbol(
            "fz_bs_reader_init",
            fz_runtime::ir_runtime::fz_bs_reader_init as *const u8,
        );
        builder.symbol(
            "fz_bs_read_field",
            fz_runtime::ir_runtime::fz_bs_read_field as *const u8,
        );
        builder.symbol(
            "fz_map_begin",
            fz_runtime::ir_runtime::fz_map_begin as *const u8,
        );
        builder.symbol(
            "fz_map_clone",
            fz_runtime::ir_runtime::fz_map_clone as *const u8,
        );
        builder.symbol(
            "fz_map_push",
            fz_runtime::ir_runtime::fz_map_push as *const u8,
        );
        builder.symbol(
            "fz_map_finalize",
            fz_runtime::ir_runtime::fz_map_finalize as *const u8,
        );
        builder.symbol(
            "fz_map_get",
            fz_runtime::ir_runtime::fz_map_get as *const u8,
        );
        builder.symbol(
            "fz_alloc_float",
            fz_runtime::ir_runtime::fz_alloc_float as *const u8,
        );
        builder.symbol(
            "fz_promote_f64",
            fz_runtime::ir_runtime::fz_promote_f64 as *const u8,
        );
        builder.symbol("fz_fmod", fz_runtime::ir_runtime::fz_fmod as *const u8);
        builder.symbol(
            "fz_value_eq",
            fz_runtime::ir_runtime::fz_value_eq as *const u8,
        );
        builder.symbol(
            "fz_vec_begin",
            fz_runtime::ir_runtime::fz_vec_begin as *const u8,
        );
        builder.symbol(
            "fz_vec_push",
            fz_runtime::ir_runtime::fz_vec_push as *const u8,
        );
        builder.symbol(
            "fz_vec_finalize",
            fz_runtime::ir_runtime::fz_vec_finalize as *const u8,
        );
        builder.symbol(
            "fz_vec_get",
            fz_runtime::ir_runtime::fz_vec_get as *const u8,
        );
        builder.symbol(
            "fz_alloc_closure",
            fz_runtime::ir_runtime::fz_alloc_closure as *const u8,
        );
        builder.symbol("fz_spawn", fz_runtime::ir_runtime::fz_spawn as *const u8);
        builder.symbol(
            "fz_spawn_opt",
            fz_runtime::ir_runtime::fz_spawn_opt as *const u8,
        );
        builder.symbol("fz_self", fz_runtime::ir_runtime::fz_self as *const u8);
        builder.symbol("fz_send", fz_runtime::ir_runtime::fz_send as *const u8);
        builder.symbol(
            "fz_receive_attempt",
            fz_runtime::ir_runtime::fz_receive_attempt as *const u8,
        );
        builder.symbol(
            "fz_receive_park",
            fz_runtime::ir_runtime::fz_receive_park as *const u8,
        );
        builder.symbol(
            "fz_get_static_closure",
            fz_runtime::ir_runtime::fz_get_static_closure as *const u8,
        );
        builder.symbol(
            "fz_get_halt_cont",
            fz_runtime::ir_runtime::fz_get_halt_cont as *const u8,
        );
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
        // fz-cps.1.7 — resolve each zero-cap closure-target stub_func_id
        // to its finalized code address. `make_process` writes these into
        // the off-heap singleton's `code_ptr` slot at +16.
        let static_closure_targets: Vec<(u32, u32, *const u8, u32)> = meta
            .static_closure_targets
            .iter()
            .map(|(cl_sid, fn_id, stub_fid, halt_kind)| {
                let ptr = jmod.get_finalized_function(*stub_fid);
                (*cl_sid, *fn_id, ptr, *halt_kind)
            })
            .collect();
        let resume_park_addr = jmod.get_finalized_function(meta.resume_park_id);
        let spawn_entry_addr = jmod.get_finalized_function(meta.spawn_entry_id);
        let main_entry_addr = jmod.get_finalized_function(meta.main_entry_id);
        let halt_cont_body_addrs = [
            jmod.get_finalized_function(meta.halt_cont_body_ids[0]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[1]),
            jmod.get_finalized_function(meta.halt_cont_body_ids[2]),
        ];
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
            static_closure_targets,
            resume_park_addr,
            spawn_entry_addr,
            main_entry_addr,
            halt_cont_body_addrs,
            fn_halt_kinds: meta.fn_halt_kinds,
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
        // No `main`/0 in the source → nothing to drive at startup. `fz build`
        // errors gracefully on this artifact via its main_symbol check.
        let Some(main_fn_id) = meta.main_fn_id else {
            return Ok(());
        };

        // fz-siu.6.1: AOT C-main is a thin driver around the cps-in-clif
        // SystemV→Tail-CC shims (fz_main_entry / fz_halt_cont_body) emitted
        // in compile_with_backend. Three FFI fns from fz-runtime do the
        // Process setup, static-closure registration, and run-main+teardown.
        // fz-ul4.27.22.3 — setup takes 3 halt_cont_body addrs (Tagged,
        // RawInt, RawF64) in slots 2-4.
        let setup_sig = sig1(
            &[
                types::I64,
                types::I32,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
                types::I64,
            ],
            &[types::I64],
        );
        let setup_id = self
            .omod
            .declare_function("fz_aot_setup", Linkage::Import, &setup_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_setup: {}", e)))?;

        // fz-ul4.27.22.6: trailing i32 carries halt_kind.
        let reg_sig = sig1(
            &[types::I64, types::I32, types::I32, types::I64, types::I32],
            &[],
        );
        let reg_id = self
            .omod
            .declare_function("fz_aot_register_static_closure", Linkage::Import, &reg_sig)
            .map_err(|e| {
                CodegenError::new(format!("declare fz_aot_register_static_closure: {}", e))
            })?;

        let run_sig = sig1(&[types::I64, types::I64, types::I64], &[types::I32]);
        let run_id = self
            .omod
            .declare_function("fz_aot_run_main", Linkage::Import, &run_sig)
            .map_err(|e| CodegenError::new(format!("declare fz_aot_run_main: {}", e)))?;

        let (atom_blob_data, atom_blob_len): (Option<DataId>, u32) = if meta.atom_names.is_empty() {
            (None, 0)
        } else {
            let mut blob: Vec<u8> = Vec::new();
            for name in &meta.atom_names {
                blob.extend_from_slice(name.as_bytes());
                blob.push(0);
            }
            blob.push(0);
            let len = blob.len() as u32;
            let id = self
                .omod
                .declare_data("fz_aot_atom_blob", Linkage::Local, false, false)
                .map_err(|e| CodegenError::new(format!("declare atom blob: {}", e)))?;
            let mut desc = DataDescription::new();
            desc.define(blob.into_boxed_slice());
            self.omod
                .define_data(id, &desc)
                .map_err(|e| CodegenError::new(format!("define atom blob: {}", e)))?;
            (Some(id), len)
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
            meta.fn_ids[&main_fn_id.0],
            meta.main_entry_id,
            meta.halt_cont_body_ids,
            meta.spawn_entry_id,
            meta.resume_park_id,
            &meta.static_closure_targets,
            atom_blob_data,
            atom_blob_len,
            setup_id,
            reg_id,
            run_id,
        )?;
        Ok(())
    }

    fn finalize(self, meta: CompiledMetadata) -> Result<AotArtifact, CodegenError> {
        let AotBackend { omod } = self;
        let mut product = omod.finish();
        // Emit the macOS platform load command (LC_BUILD_VERSION) so ld
        // doesn't warn "no platform load command found". Cranelift's
        // ObjectBuilder doesn't inject this automatically (fz-ul4.33).
        #[cfg(target_os = "macos")]
        {
            let mut ver = object::write::MachOBuildVersion::default();
            ver.platform = object::macho::PLATFORM_MACOS;
            ver.minos = 11 << 16; // 11.0.0 — first macOS on Apple Silicon
            ver.sdk = 11 << 16;
            product.object.set_macho_build_version(ver);
        }
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
    let runtime = declare_runtime_symbols(backend.module_mut())?;

    let mut fbctx = FunctionBuilderContext::new();

    // fz-ul4.27.22.3 — emit fz_main_entry. Generic shim: takes the
    // entry fn ptr + a halt-cont singleton ptr supplied by the Rust
    // caller (caller picks the singleton matching the entry fn's
    // return_repr kind). Body just `call_indirect Tail main_fp(halt_cl)`.
    {
        let mut ctx = backend.module_mut().make_context();
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        ctx.func.signature = sig;
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let main_fp = b.block_params(entry)[0];
            let halt_cl = b.block_params(entry)[1];
            let mut main_sig = Signature::new(CallConv::Tail);
            main_sig.params.push(AbiParam::new(types::I64));
            main_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(main_sig);
            let inst = b.ins().call_indirect(sig_ref, main_fp, &[halt_cl]);
            let r = b.inst_results(inst)[0];
            b.ins().return_(&[r]);
            b.finalize();
        }
        backend
            .module_mut()
            .define_function(runtime.main_entry_id, &mut ctx)
            .map_err(|e| CodegenError::new(format!("define fz_main_entry: {}", e)))?;
        backend.module_mut().clear_context(&mut ctx);
    }

    // fz-cps.1.11 — emit fz_spawn_entry. SystemV scheduler-callable shim
    // that invokes a zero-arg closure with a fresh halt-cont. Used by
    // `Runtime::spawn_closure` to launch the new task's first fn via
    // the closure-target sig `(self, cont) tail`. The closure body
    // tail-chains into a halt-cont; halt sets process.halt_value.
    // Sig: `(closure:i64) -> i64 system_v`.
    {
        let mut ctx = backend.module_mut().make_context();
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        ctx.func.signature = sig;
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let closure = b.block_params(entry)[0];
            // fz-ul4.27.22.6 — pick the matching halt-cont based on the
            // spawned closure's halt_kind (packed into the high 2 bits of
            // the heap header's `flags` at MakeClosure time). For
            // RawInt-returning bodies, this routes the i64 raw bits into
            // halt_cont_body_i64 instead of sshr-ing them as if they were
            // tagged FzValue. Pre-22.6 this was hardcoded Tagged.
            //
            // Closure HeapHeader layout:
            //   off 0  : kind (u16)         off 4  : size_bytes (u32)
            //   off 2  : flags (u16)        off 8  : schema_id (u32)
            //                               off 12 : _reserved (u32)
            // flags low 14 bits = captured_count; high 2 bits = halt_kind.
            let flags_u16 = b.ins().load(types::I16, MemFlags::trusted(), closure, 2);
            // Right-shift 14 to extract halt_kind (0..2), then widen to i32.
            let hk16 = b.ins().ushr_imm(flags_u16, 14);
            let kind = b.ins().uextend(types::I32, hk16);
            // Select halt_cont_body_addr by kind. Branchless via three
            // func_addrs + a tiny dispatch — keeps the spawn shim a leaf.
            let hcb_tagged = backend
                .module_mut()
                .declare_func_in_func(runtime.halt_cont_body_tagged_id, b.func);
            let hcb_i64 = backend
                .module_mut()
                .declare_func_in_func(runtime.halt_cont_body_i64_id, b.func);
            let hcb_f64 = backend
                .module_mut()
                .declare_func_in_func(runtime.halt_cont_body_f64_id, b.func);
            let a_tagged = b.ins().func_addr(types::I64, hcb_tagged);
            let a_i64 = b.ins().func_addr(types::I64, hcb_i64);
            let a_f64 = b.ins().func_addr(types::I64, hcb_f64);
            let one = b.ins().iconst(types::I32, 1);
            let two = b.ins().iconst(types::I32, 2);
            let is_i64 = b.ins().icmp(IntCC::Equal, kind, one);
            let is_f64 = b.ins().icmp(IntCC::Equal, kind, two);
            let pick_i64_or_tagged = b.ins().select(is_i64, a_i64, a_tagged);
            let hcb_addr = b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
            let ghc_fref = backend
                .module_mut()
                .declare_func_in_func(runtime.get_halt_cont_id, b.func);
            let halt_inst = b.ins().call(ghc_fref, &[hcb_addr, kind]);
            let halt_cl = b.inst_results(halt_inst)[0];
            // Load closure body addr at +16 and invoke as
            // closure-target sig `(self, cont) tail` (zero user args).
            let code = b
                .ins()
                .load(types::I64, MemFlags::trusted(), closure, HEADER_SIZE);
            let mut closure_sig = Signature::new(CallConv::Tail);
            closure_sig.params.push(AbiParam::new(types::I64)); // self
            closure_sig.params.push(AbiParam::new(types::I64)); // cont
            closure_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(closure_sig);
            let inst = b.ins().call_indirect(sig_ref, code, &[closure, halt_cl]);
            let r = b.inst_results(inst)[0];
            b.ins().return_(&[r]);
            b.finalize();
        }
        backend
            .module_mut()
            .define_function(runtime.spawn_entry_id, &mut ctx)
            .map_err(|e| CodegenError::new(format!("define fz_spawn_entry: {}", e)))?;
        backend.module_mut().clear_context(&mut ctx);
    }

    // fz-cps.1.11 — emit fz_resume_park. SystemV scheduler-callable shim
    // that wakes a parked task: `load parked_cont+16; call_indirect Tail
    // sig_cont (msg, parked_cont); return result`. The runtime invokes
    // this when a Blocked task transitions to Ready (a message has
    // arrived). Sig: `(msg:i64, parked_cont:i64) -> i64 system_v`.
    {
        let mut ctx = backend.module_mut().make_context();
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        ctx.func.signature = sig;
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let msg = b.block_params(entry)[0];
            let cont = b.block_params(entry)[1];
            let code = b
                .ins()
                .load(types::I64, MemFlags::trusted(), cont, HEADER_SIZE);
            let mut cont_sig = Signature::new(CallConv::Tail);
            cont_sig.params.push(AbiParam::new(types::I64));
            cont_sig.params.push(AbiParam::new(types::I64));
            cont_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(cont_sig);
            let inst = b.ins().call_indirect(sig_ref, code, &[msg, cont]);
            let r = b.inst_results(inst)[0];
            b.ins().return_(&[r]);
            b.finalize();
        }
        backend
            .module_mut()
            .define_function(runtime.resume_park_id, &mut ctx)
            .map_err(|e| CodegenError::new(format!("define fz_resume_park: {}", e)))?;
        backend.module_mut().clear_context(&mut ctx);
    }

    // fz-ul4.27.22.3 — emit three fz_halt_cont_body fns, one per repr.
    // The producer's Term::Return uses sig (return_repr, i64); the
    // closure pointer at the chain end points at the matching body so
    // sigs agree. Tagged variant unboxes (existing semantics); RawInt
    // / RawF64 variants store the value directly.
    for (body_id, val_ty, halt_impl_id) in [
        (
            runtime.halt_cont_body_tagged_id,
            types::I64,
            runtime.halt_implicit_id,
        ),
        (
            runtime.halt_cont_body_i64_id,
            types::I64,
            runtime.halt_implicit_i64_id,
        ),
        (
            runtime.halt_cont_body_f64_id,
            types::F64,
            runtime.halt_implicit_f64_id,
        ),
    ] {
        let mut ctx = backend.module_mut().make_context();
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        ctx.func.signature = sig;
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let val = b.block_params(entry)[0];
            let hi_fref = backend
                .module_mut()
                .declare_func_in_func(halt_impl_id, b.func);
            b.ins().call(hi_fref, &[val]);
            let zero = b.ins().iconst(types::I64, 0);
            b.ins().return_(&[zero]);
            b.finalize();
        }
        backend
            .module_mut()
            .define_function(body_id, &mut ctx)
            .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
        backend.module_mut().clear_context(&mut ctx);
    }

    // Register a heap Schema for every tuple arity used by MakeTuple, so the
    // GC tracer can walk fields and so codegen can iconst the schema_id.
    // Also detect any bitstring prim so we can pre-register arity-1 / arity-3
    // schemas used by the reader / result tuples even if no MakeTuple uses
    // those arities directly.
    let mut tuple_arities: std::collections::HashSet<usize> = std::collections::HashSet::new();
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

    // frame_sizes is computed after `schemas` is built (post-spec_registry).

    // Run the typer ahead of codegen so per-fn Var->Descr info is
    // available during lowering. .11.24.5 clones first so the typed-schema
    // rewrite can swap MakeVec(I64) → MakeVec(F64) where elements are Float.
    let mut working = module.clone();
    let pre_types = crate::ir_typer::type_module(&working);
    crate::ir_typer::rewrite_vec_kinds(&mut working, &pre_types).map_err(CodegenError::new)?;
    // fz-ul4.29.10.3 — lower known-target CallClosure / TailCallClosure
    // to direct Call / TailCall. After this, the final type_module sees
    // direct dispatch where the closure-stub used to live, and
    // .29.12.6's any-key drop logic can remove the now-dead any-key.
    let mid_types = crate::ir_typer::type_module(&working);
    crate::ir_typer::rewrite_known_target_closures(&mut working, &mid_types);
    let module_types = crate::ir_typer::type_module(&working);
    let module = &working;

    // fz-ul4.29.2.1 — Build the SpecRegistry.
    //
    // Register any-keys first, in FnId.0 order — this preserves the
    // invariant `any-key SpecId.0 == FnId.0` so closure / Spawn / Receive
    // paths (and any other "use any-key" path) can keep using fn_id.0
    // directly as a schema_id / Cranelift func key. Narrow specs from
    // `module_types.specs` get SpecIds ≥ n_fns appended afterwards.
    let mut spec_registry = SpecRegistry::new();
    let mut fns_by_fnid: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns_by_fnid.sort_by_key(|f| f.id.0);
    for f in &fns_by_fnid {
        let n_params = f.block(f.entry).params.len();
        let any_key = vec![crate::types::Descr::any(); n_params];
        // fz-ul4.29.12.6 — skip registering F's any-key when the typer
        // dropped it (every callsite of F has typed coverage). The next
        // registration via `register_any_key_at` pads slot F.0 with a
        // sentinel automatically, preserving the `SpecId.0 == FnId.0`
        // invariant for the surviving any-keys.
        if !module_types.specs.contains_key(&(f.id, any_key.clone())) {
            continue;
        }
        let sid = spec_registry.register_any_key_at(f.id, any_key);
        debug_assert_eq!(sid.0, f.id.0);
    }
    // Append narrow specs in a deterministic order (FnId.0, then descr-tuple
    // bytes) so CLIF emission is reproducible across runs.
    let mut narrow_keys: Vec<(FnId, Vec<crate::types::Descr>)> = module_types
        .specs
        .keys()
        .filter(|(fid, key)| {
            let n_params = module
                .fns
                .iter()
                .find(|f| f.id == *fid)
                .map(|f| f.block(f.entry).params.len())
                .unwrap_or(0);
            // Filter the any-keys (already registered).
            !(key.len() == n_params && key.iter().all(|d| d.is_equiv(&crate::types::Descr::any())))
        })
        .cloned()
        .collect();
    narrow_keys.sort_by(|a, b| {
        a.0.0
            .cmp(&b.0.0)
            .then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1)))
    });
    for (fid, key) in narrow_keys {
        spec_registry.register(fid, key);
    }

    let spec_count = spec_registry.len();
    let spec_keys: Vec<(FnId, Vec<crate::types::Descr>)> = spec_registry
        .iter()
        .map(|(_, fid, key)| (fid, key.to_vec()))
        .collect();
    // SpecId.0 -> module.fns index (None when the SpecId is a sentinel
    // slot for a missing FnId.0 — cps_split sparsity).
    let mut idx_of: HashMap<FnId, usize> = HashMap::new();
    for (i, f) in module.fns.iter().enumerate() {
        idx_of.insert(f.id, i);
    }
    // fz-ul4.29.12.6 — treat slots whose typer FnTypes is absent as
    // sentinels too. Three cases collapse here:
    //   * cps_split sparsity: FnId not in module → `idx_of.get` = None.
    //   * Pre-existing sentinel slot (empty-key padding) for a missing
    //     FnId.0 → no entry in `module_types.specs` either.
    //   * Dropped any-key (.29.12.6): FnId exists in module but its
    //     any-key body was pruned by the typer → no entry in
    //     `module_types.specs`. Codegen must skip compilation for the
    //     slot; no consumer can index into it because `resolve` only
    //     returns SpecIds with a real registration.
    let spec_fnidx: Vec<Option<usize>> = spec_keys
        .iter()
        .map(|(fid, key)| {
            if !module_types.specs.contains_key(&(*fid, key.clone())) {
                return None;
            }
            idx_of.get(fid).copied()
        })
        .collect();
    let spec_fn_types: Vec<Option<&crate::ir_typer::FnTypes>> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, (fid, key))| {
            spec_fnidx[sid]?;
            module_types.specs.get(&(*fid, key.clone()))
        })
        .collect();

    // fz-ul4.29.12.2 — collect typed closure shapes keyed by the
    // lambda's resolved narrow SpecId. Each `Prim::MakeClosure` site
    // is inspected per *caller* spec (so closures built in different
    // caller specializations with different capture Descrs produce
    // distinct lambda SpecIds → distinct stubs). The key fed to
    // `spec_registry.resolve` is `[capture_descrs..., any, ...]` —
    // padded to the lambda's full arity. The .29.12.2 typer change
    // (in `ir_typer::type_module`'s fixed-point loop) registers a
    // narrow spec for every MakeClosure's capture-Descr tuple, so
    // exact-match resolve succeeds; the any-key remains a subsumption
    // backstop. Value = capture count (== `captured.len()`); needed
    // to split entry params into `[captures..., args...]` at stub
    // declaration / invocation.
    let mut closure_shapes: std::collections::BTreeMap<u32, usize> =
        std::collections::BTreeMap::new();
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            continue;
        };
        let f = &module.fns[idx];
        let Some(ft) = spec_fn_types[sid] else {
            continue;
        };
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(lam_fn_id, captured) = prim {
                    let lam = module.fn_by_id(*lam_fn_id);
                    let n_params = lam.block(lam.entry).params.len();
                    let mut key: Vec<crate::types::Descr> =
                        vec![crate::types::Descr::any(); n_params];
                    for (k, cv) in captured.iter().enumerate() {
                        if let Some(slot) = key.get_mut(k) {
                            *slot = ft
                                .vars
                                .get(cv)
                                .cloned()
                                .unwrap_or_else(crate::types::Descr::any);
                        }
                    }
                    // fz-ul4.29.10.3 — when the lambda's any-key was
                    // dropped (closure-var is fully resolved via
                    // fn_constants and the IR rewrite turned every
                    // invocation into a direct Call), no covering spec
                    // exists for `[any; n_params]`. The closure header
                    // still needs `stub_fp`, but the stub is unreachable
                    // — falling back to any registered narrow SpecId is
                    // safe because nothing dispatches through it.
                    let cl_sid = spec_registry
                        .resolve(*lam_fn_id, &key)
                        .map(|s| s.0)
                        .or_else(|| {
                            spec_registry
                                .iter()
                                .find(|(s, fid, _)| {
                                    *fid == *lam_fn_id && spec_fnidx[s.0 as usize].is_some()
                                })
                                .map(|(s, _, _)| s.0)
                        })
                        .unwrap_or_else(|| {
                            panic!(
                                ".29.12.2: no live spec for closure target \
                             FnId({}); registered keys: {:?}",
                                lam_fn_id.0,
                                spec_registry
                                    .iter()
                                    .map(|(s, fid, k)| (s.0, fid.0, k.to_vec()))
                                    .collect::<Vec<_>>()
                            )
                        });
                    closure_shapes.insert(cl_sid, captured.len());
                }
            }
        }
    }

    // fz-ul4.27.6.2.1 — Parking + native-callability analyses. Stored in
    // metadata; consumed at declare-time below (.6.2.2) for per-fn sigs
    // and at compile_fn / emit_call (.6.2.3-4) for ABI bifurcation.
    // fz-ul4.27.14.1: this block moved up to feed the new
    // `uniform_cont_reachable_specs` analysis that gates the schema /
    // ABI slot-0 force-Tagged decision below.
    let parking_reachable = crate::parking::parking_reachable(module);
    let mut natively_callable = crate::parking::natively_callable(module, &parking_reachable);

    // fz-cps.1.2 (fz-siu.1.2): the set of fns used as continuations.
    // A cont fn has sig `(result:i64, self:i64) tail` per
    // docs/cps-in-clif.md §2.1 — no host_ctx, no trailing cont param.
    // Its body reads captures from `self+24, +32, ...` rather than
    // from typed entry params, and its "next k" is one of its captures.
    let cont_fns: std::collections::HashSet<crate::fz_ir::FnId> = {
        use crate::fz_ir::Term;
        let mut s = std::collections::HashSet::new();
        for f in &module.fns {
            for b in &f.blocks {
                match &b.terminator {
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive { continuation } => {
                        s.insert(continuation.fn_id);
                    }
                    _ => {}
                }
            }
        }
        s
    };
    let _ = &cont_fns; // fz-cps.1.2: consumed by sig builder + entry harness in next step.

    // fz-cps.1.2 — set of fns appearing as a MakeClosure target. Per
    // docs/cps-in-clif.md §2.1 these get sig `(args..., self:i64, cont:i64)
    // tail` and their body loads captures from `self+24+8*i`. Disjoint
    // from cont_fns by construction (conts are anonymous continuations
    // synthesized by the lowerer; MakeClosure targets are user lambdas
    // or top-level fns passed as values). If overlap occurs in some
    // future fz-IR, cont-fn shape wins (Receive parking would otherwise
    // misread the result slot).
    let (closure_target_fns, closure_n_captures): (
        std::collections::HashSet<crate::fz_ir::FnId>,
        std::collections::HashMap<crate::fz_ir::FnId, usize>,
    ) = {
        use crate::fz_ir::{Prim, Stmt, Term};
        let mut targets = std::collections::HashSet::new();
        let mut counts: std::collections::HashMap<crate::fz_ir::FnId, usize> =
            std::collections::HashMap::new();
        let mut direct_called = std::collections::HashSet::new();
        for f in &module.fns {
            for b in &f.blocks {
                match &b.terminator {
                    Term::Call { callee, .. } | Term::TailCall { callee, .. } => {
                        direct_called.insert(*callee);
                    }
                    _ => {}
                }
                for stmt in &b.stmts {
                    let Stmt::Let(_, prim) = stmt;
                    if let Prim::MakeClosure(fid, captured) = prim {
                        targets.insert(*fid);
                        let n = captured.len();
                        if let Some(prev) = counts.get(fid) {
                            debug_assert_eq!(
                                *prev, n,
                                "MakeClosure n_captures mismatch for fn {}: \
                                 {} vs {}",
                                fid.0, prev, n
                            );
                        }
                        counts.insert(*fid, n);
                    }
                }
            }
        }
        // fz-cps.1.8: closure-target sig is universal. Every MakeClosure
        // target gets `(args..., self, cont) tail` regardless of whether
        // it is also direct-called. Direct callers load the
        // per-Process static singleton (registered in fz-siu.1.7) and
        // pass it as `self`. See docs/cps-in-clif.md §8.2 acceptance:
        // both indirect calls lower to `return_call_indirect` against
        // this sig.
        //
        // Invariant: a closure-target fn that is ALSO direct-called must
        // have zero captures — direct callers have no captures to bind.
        // Asserted below.
        for fid in &targets {
            if direct_called.contains(fid) {
                debug_assert_eq!(
                    counts[fid], 0,
                    "fz-siu.1.8: fn {} is both direct-called and a non-zero-cap \
                     closure target — direct callers can't supply captures",
                    fid.0,
                );
            }
        }
        let _ = direct_called;
        (targets, counts)
    };
    let _ = (&closure_target_fns, &closure_n_captures);
    // fz-ul4.27.6.4 follow-up: heap-safe captures.
    //
    // A native cont chain routes the caller's captured vars through
    // Cranelift virtual stack slots / registers as it crosses the
    // synchronous call to the (native) callee. Those slots are
    // invisible to the GC's heap-frame tracer — safe for non-heap
    // payloads (tagged int / atom / nil / bool, which are just bits),
    // unsafe for heap pointers (boxed float, list cons, struct,
    // closure, etc.) because a GC firing inside the callee would
    // reclaim the unreachable objects.
    //
    // Stack-map emission + a stack-walking tracer would lift this
    // restriction (filed as a follow-up). Until then we shrink
    // `natively_callable` so it only admits conts whose every use
    // site has heap-safe captures. A cont removed by this pass cascades
    // through the fixed point — its callers may no longer satisfy the
    // chain's "every Term::Call cont is native" invariant.
    // fz-cps.1.2: `non_heap` / `is_non_heap_descr` removed with the
    // type-aware shrink — see (a) below. The descriptor types stay in
    // crate::types for other callers.
    // Single combined fixed point. Each iter re-enforces every invariant
    // so cascading removals don't leave an inconsistent set:
    //   (a) Term::Call's callee + cont both native, captures non-heap.
    //   (b) Term::TailCall's callee native, args non-heap.
    //   (c) Cont validity: if f is used as cont in some Term::Call, the
    //       caller's callee at that site must be native (so the site
    //       picks the native-chain branch) and captures non-heap.
    loop {
        let mut to_remove: Vec<crate::fz_ir::FnId> = Vec::new();
        // (a) and (b): body invariants.
        for f in module.fns.iter() {
            if !natively_callable.contains(&f.id) {
                continue;
            }
            let body_ok = f.blocks.iter().all(|b| match &b.terminator {
                Term::Return(_) | Term::Halt(_) | Term::Goto(_, _) | Term::If(_, _, _) => true,
                Term::Call {
                    callee,
                    continuation,
                    ..
                } => {
                    // fz-cps.1.2: non-heap-args restriction lifted. The
                    // cont chain no longer routes args through Cranelift
                    // register slots invisible to the GC tracer — every
                    // cont is now a heap-allocated closure (§2.2), and
                    // the GC roots come from `process.parked_cont` (§7)
                    // not from a stack walk.
                    natively_callable.contains(callee)
                        && natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCall { callee, .. } => natively_callable.contains(callee),
                // fz-cps.1.8 — closure-call terminators admitted; bodies
                // are Tail-CC at cl+16 with closure-target sig. Cont (if
                // any) must also be native so the cont-return chain is
                // unbroken.
                Term::CallClosure { continuation, .. } => {
                    natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCallClosure { .. } => true,
                Term::Receive { continuation } => natively_callable.contains(&continuation.fn_id),
            });
            if !body_ok {
                to_remove.push(f.id);
            }
        }
        // (c) Cont validity: cont must reach via a native Term::Call site.
        // fz-cps.1.2: capture heap-safety is no longer required (see
        // explanation in (a) above). The structural check remains: the
        // caller's callee at every cont reach site must still be native.
        for f in &module.fns {
            if !natively_callable.contains(&f.id) {
                continue;
            }
            if to_remove.contains(&f.id) {
                continue;
            }
            let mut cont_unsafe = false;
            'outer: for caller in module.fns.iter() {
                for b in &caller.blocks {
                    let Term::Call {
                        callee,
                        continuation,
                        ..
                    } = &b.terminator
                    else {
                        continue;
                    };
                    if continuation.fn_id != f.id {
                        continue;
                    }
                    if !natively_callable.contains(callee) {
                        cont_unsafe = true;
                        break 'outer;
                    }
                }
            }
            if cont_unsafe {
                to_remove.push(f.id);
            }
        }
        if to_remove.is_empty() {
            break;
        }
        for id in to_remove {
            natively_callable.remove(&id);
        }
    }

    // fz-ul4.27.22.16 — `uniform_cont_reachable_specs` deleted. The
    // analysis flagged conts reachable from uniform callees / Tagged-
    // unconditional writers so their entry slot 0 + schema kind would
    // be forced to Tagged/FzValue. Post-22.12, every callsite that
    // would have flagged a cont either:
    //   - resolves via closure_lit to a narrow body spec whose ABI
    //     already matches the cont's narrow slot 0 (direct dispatch);
    //   - flows through the unresolved indirect Tagged seam, which
    //     `tagged_slot0_cont_specs` (CallClosure / Receive branches)
    //     already covers.
    // Disabling the force changed only line numbers in
    // closure_typed_captures.clif (verified by experiment) — no
    // codegen content shifted. The analysis is dead.

    // fz-cps.1.13 — fns_needing_host_ctx analysis deleted. Native fns
    // all use fz_halt_implicit (TLS-based) for Term::Halt, dropping the
    // host_ctx parameter. The set was always empty post-1.12; threading
    // remained as a no-op placeholder. Now constructed inline as empty
    // wherever still consumed.
    let fns_needing_host_ctx: std::collections::HashSet<crate::fz_ir::FnId> =
        std::collections::HashSet::new();

    // fz-ul4.27.18 — per-FnId set: fns invoked from any fz IR site
    // (as a direct callee, a continuation, or a closure target).
    // A fn NOT in this set has no fz IR caller and can only enter via
    // the trampoline entry (which writes null into the frame's slot 0).
    // For such a fn, cont_ptr is statically null at runtime; emit_return
    // can specialize to a halt-only path, skipping the runtime
    // `load v0+16; icmp eq 0; brif` dispatch entirely.
    let mut ir_referenced_fns: std::collections::HashSet<crate::fz_ir::FnId> =
        std::collections::HashSet::new();
    for f in &module.fns {
        for blk in &f.blocks {
            match &blk.terminator {
                Term::Call {
                    callee,
                    continuation,
                    ..
                } => {
                    ir_referenced_fns.insert(*callee);
                    ir_referenced_fns.insert(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => {
                    ir_referenced_fns.insert(*callee);
                }
                Term::CallClosure { continuation, .. } | Term::Receive { continuation } => {
                    ir_referenced_fns.insert(continuation.fn_id);
                }
                _ => {}
            }
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(fid, _) = prim {
                    ir_referenced_fns.insert(*fid);
                }
            }
        }
    }
    // Rebind for the existing parameter name threading. The contained
    // fns are exactly the "never specializable as halt-only" set.
    let cont_target_fns = ir_referenced_fns;

    // Rebuild schemas: one entry per SpecId, refined entry-param kinds
    // from THAT spec's FnTypes. The any-key SpecId for FnId K lands at
    // index K (invariant) so any code path that uses fn_id.0 as a
    // schema_id continues to hit the right schema. Sentinel SpecIds
    // (missing-FnId slots) get a zero-field placeholder schema; they're
    // never reached at runtime.
    let mut schemas: Vec<Schema> = Vec::with_capacity(spec_count);
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = &module.fns[idx];
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
        let entry_block = f.block(f.entry);
        let mut kinds: Vec<FieldKind> = entry_block
            .params
            .iter()
            .map(|_| FieldKind::FzValue)
            .collect();
        for (j, p) in entry_block.params.iter().enumerate() {
            let d = ft
                .vars
                .get(p)
                .cloned()
                .unwrap_or_else(crate::types::Descr::any);
            if d.is_subtype(&crate::types::Descr::float()) {
                kinds[j] = FieldKind::RawF64;
            } else if d.is_subtype(&crate::types::Descr::int()) {
                kinds[j] = FieldKind::RawI64;
            }
        }
        // fz-ul4.27.22.16 — uniform_cont_reachable slot-0 FzValue force
        // retired; tagged_slot0_cont_specs covers every case post-22.12.
        schemas.push(build_frame_schema(&f.name, &kinds));
    }

    // Per-spec frame sizes (consumed by `fz_alloc_frame_dyn` and the AOT
    // frame-size dispatch fn). Indexed by SpecId.0.
    let frame_sizes: Vec<u32> = schemas.iter().map(|s| s.size).collect();

    // Per-spec return Descrs (each spec's `Term::Return` join under its
    // own typed view) — extended in fz-ul4.27.13 to propagate through
    // `Term::TailCall` so a fn whose only exit is a tail call inherits
    // the callee's return Descr instead of defaulting to `any`. Without
    // this, a chain like `fn run(n), do twice(n)` (which lowers to a
    // single tail call to `double`) would report `any` and force a
    // tagged-FzValue boundary at the caller, undoing the .27.13 unbox
    // win at every macro-style hop.
    //
    // Iterate to fixpoint: each pass folds in TailCall callees' current
    // return Descrs through `spec_registry` resolution. Indexed by
    // SpecId.0; sentinel slots get `any`.
    // Seed: per-spec join of Term::Return val Descrs (None == no
    // Term::Return yet). Sentinel slots seed to `any` (never reached).
    let mut return_descrs: Vec<Option<crate::types::Descr>> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
                let mut joined: Option<crate::types::Descr> = None;
                for blk in &f.blocks {
                    if let Term::Return(v) = &blk.terminator {
                        let d = ft
                            .vars
                            .get(v)
                            .cloned()
                            .unwrap_or_else(crate::types::Descr::any);
                        joined = Some(match joined {
                            Some(p) => p.union(&d),
                            None => d,
                        });
                    }
                }
                joined
            }
            None => Some(crate::types::Descr::any()),
        })
        .collect();
    // Use semantic mutual-subtype check for fixpoint termination: the
    // DNF Descr representation isn't canonical, so `prev.union(callee_d)`
    // can produce a structurally-different but semantically-equal value
    // (e.g. for recursive fns where callee_sid == sid and the value is
    // already its own fixpoint). Cap iterations as a belt-and-braces
    // bound — spec_count is small and the lattice has bounded height
    // for fz's first-order Descrs.
    let max_iters = spec_count.saturating_mul(spec_count).saturating_add(8);
    for _ in 0..max_iters {
        let mut changed = false;
        for sid in 0..spec_count {
            let Some(idx) = spec_fnidx[sid] else {
                continue;
            };
            let f = &module.fns[idx];
            let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
            for blk in &f.blocks {
                // Both Term::TailCall and a resolved-via-closure_lit
                // Term::TailCallClosure feed the callee's return Descr
                // into this spec's return Descr. Unresolved
                // TailCallClosure stays opaque (any) — same as today.
                let callee_sid_for_tc: Option<u32> = match &blk.terminator {
                    Term::TailCall { callee, args } => {
                        let arg_descrs: Vec<crate::types::Descr> = args
                            .iter()
                            .map(|av| {
                                ft.vars
                                    .get(av)
                                    .cloned()
                                    .unwrap_or_else(crate::types::Descr::any)
                            })
                            .collect();
                        spec_registry.resolve(*callee, &arg_descrs).map(|s| s.0)
                    }
                    Term::TailCallClosure { closure, args } => {
                        // fz-ul4.27.22.12 — closure_lit-driven return
                        // propagation. Mirrors the codegen direct-dispatch
                        // resolution in TailCallClosure compile.
                        ft.vars
                            .get(closure)
                            .and_then(|d| d.as_closure_lit())
                            .and_then(|lit| {
                                let body_fn = module.fn_by_id(lit.fn_id);
                                let np = body_fn.block(body_fn.entry).params.len();
                                let mut full_key: Vec<crate::types::Descr> = lit.captures.clone();
                                for av in args.iter() {
                                    full_key.push(
                                        ft.vars
                                            .get(av)
                                            .cloned()
                                            .unwrap_or_else(crate::types::Descr::any),
                                    );
                                }
                                while full_key.len() < np {
                                    full_key.push(crate::types::Descr::any());
                                }
                                full_key.truncate(np);
                                spec_registry.resolve(lit.fn_id, &full_key).map(|s| s.0)
                            })
                    }
                    _ => None,
                };
                let Some(callee_sid_v) = callee_sid_for_tc else {
                    continue;
                };
                let callee_sid = callee_sid_v as usize;
                let Some(callee_d) = return_descrs[callee_sid].clone() else {
                    continue;
                };
                let new_d = match &return_descrs[sid] {
                    Some(prev) => prev.union(&callee_d),
                    None => callee_d,
                };
                let prev_eq_new = match &return_descrs[sid] {
                    Some(prev) => prev.is_subtype(&new_d) && new_d.is_subtype(prev),
                    None => false,
                };
                if !prev_eq_new {
                    return_descrs[sid] = Some(new_d);
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    let return_descrs: Vec<crate::types::Descr> = return_descrs
        .into_iter()
        .map(|opt| opt.unwrap_or_else(crate::types::Descr::any))
        .collect();

    // fz-ul4.27.13 — Per-spec entry-param ArgReprs + return ArgRepr.
    // Drives both `build_fn_signature` (AbiParam types) and call-site
    // coerce (raw int / raw f64 vs tagged FzValue). Sentinel slots get
    // empty params + Tagged return; they're never declared.
    let param_reprs: Vec<Vec<ArgRepr>> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let reprs = build_param_reprs(
                    f,
                    spec_fn_types[sid].expect("non-sentinel spec must have FnTypes"),
                );
                // fz-ul4.27.22.16 — uniform_cont_reachable slot-0 Tagged
                // force retired; tagged_slot0_cont_specs is sufficient.
                // fz-ul4.27.22.12 — arg-slot force at closure body retired.
                // The 22.5 capture-slot wins are preserved (CAPTURE slots
                // [0..n_caps) keep their per-spec narrow reprs). ARG slots
                // now also honor build_param_reprs' typed output: with
                // 22.10's closure_lit-typed MakeClosure and 22.11's direct
                // return_call dispatch, every closure-call site resolves
                // to a single body spec whose ABI the caller targets
                // exactly — no need to flatten arg slots to Tagged for
                // indirect-sig matching.
                //
                // The indirect fallback path in TailCallClosure still
                // assumes all-Tagged at the seam, so closures used
                // polymorphically (union of closure_lits, opaque arrow)
                // still go through the Tagged path correctly: the body's
                // narrow ABI on the direct path is compatible because
                // each direct callsite coerces explicitly.
                let _ = closure_n_captures;
                reprs
            }
            None => Vec::new(),
        })
        .collect();
    // fz-ntz (fz-3zx.2) — transitive closure of fns whose return is
    // Tagged-by-construction. Seeded with closure-target fns (forced
    // all-Tagged sig by fz-cps.1.8) and fns whose terminator on any
    // block is Term::TailCallClosure (return_call_indirect against the
    // closure-target sig forwards Tagged bits). Propagated through
    // Term::TailCall: if F tail-calls into a Tagged-returning callee,
    // F itself returns Tagged. The result drives BOTH the return_reprs
    // force (below) AND the tagged_slot0_cont_specs check (next block):
    // producer-side ABI and consumer-side schema stay aligned.
    // fz-ul4.27.22.12 — per-spec tagged-return tracking. Pre-22.12 the
    // set was keyed by FnId, conflating all specs of the same fn. With
    // closure_lit-driven per-spec resolution (22.10-22.11), one spec of
    // a fn can have a fully-resolved TailCallClosure (returning the
    // body's narrow repr) while a sibling spec's TailCallClosure stays
    // opaque (returning Tagged through the indirect seam). Per-spec is
    // the precise grain.
    //
    // Seed: spec has an UNRESOLVED TailCallClosure (or returns through
    // the all-Tagged indirect ABI). Resolved-via-closure_lit
    // TailCallClosure does not seed — it's structurally a typed
    // tail-call to the resolved body, equivalent to Term::TailCall.
    //
    // Propagation: spec's terminator chains into another spec that's
    // already tagged. Per-spec analysis uses each block's terminator
    // under this spec's env (spec_fn_types[sid]).
    let tagged_return_specs: std::collections::HashSet<u32> = {
        let mut set: std::collections::HashSet<u32> = std::collections::HashSet::new();
        // Per-spec resolution of TailCallClosure: returns the resolved
        // body sid (Some) or None when unresolved (indirect Tagged seam).
        let resolve_tcc_body_sid =
            |sid: usize, closure: &crate::fz_ir::Var, args: &[crate::fz_ir::Var]| -> Option<u32> {
                let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                let cv_descr = ft.vars.get(closure)?;
                let lit = cv_descr.as_closure_lit()?;
                let body_fn = module.fn_by_id(lit.fn_id);
                let body_n_params = body_fn.block(body_fn.entry).params.len();
                let mut full_key: Vec<crate::types::Descr> = lit.captures.clone();
                for av in args.iter() {
                    full_key.push(
                        ft.vars
                            .get(av)
                            .cloned()
                            .unwrap_or_else(crate::types::Descr::any),
                    );
                }
                while full_key.len() < body_n_params {
                    full_key.push(crate::types::Descr::any());
                }
                full_key.truncate(body_n_params);
                spec_registry.resolve(lit.fn_id, &full_key).map(|s| s.0)
            };
        // Seed: spec has an unresolved TailCallClosure.
        for sid in 0..spec_count {
            let Some(idx) = spec_fnidx[sid] else {
                continue;
            };
            let f = &module.fns[idx];
            for b in &f.blocks {
                if let Term::TailCallClosure { closure, args } = &b.terminator {
                    if resolve_tcc_body_sid(sid, closure, args).is_none() {
                        set.insert(sid as u32);
                        break;
                    }
                }
            }
        }
        // Propagation: spec's terminator chains into a tagged spec.
        loop {
            let mut changed = false;
            for sid in 0..spec_count {
                if set.contains(&(sid as u32)) {
                    continue;
                }
                let Some(idx) = spec_fnidx[sid] else {
                    continue;
                };
                let f = &module.fns[idx];
                let propagates = f.blocks.iter().any(|b| match &b.terminator {
                    Term::TailCall { callee, args } => {
                        // Resolve callee's spec sid under this spec's env.
                        let csid = (|| {
                            let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                            let arg_descrs: Vec<crate::types::Descr> = args
                                .iter()
                                .map(|av| {
                                    ft.vars
                                        .get(av)
                                        .cloned()
                                        .unwrap_or_else(crate::types::Descr::any)
                                })
                                .collect();
                            spec_registry.resolve(*callee, &arg_descrs).map(|s| s.0)
                        })()
                        .unwrap_or(callee.0);
                        set.contains(&csid)
                    }
                    Term::TailCallClosure { closure, args } => {
                        match resolve_tcc_body_sid(sid, closure, args) {
                            Some(body_sid) => set.contains(&body_sid),
                            None => true, // unresolved is tagged by definition
                        }
                    }
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive { continuation } => {
                        // Cont's any-key spec id == continuation.fn_id.0.
                        set.contains(&continuation.fn_id.0)
                    }
                    _ => false,
                });
                if propagates {
                    set.insert(sid as u32);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        set
    };
    // Fn-id-level coarse view for legacy consumers (tagged_slot0_cont_specs
    // below queries by FnId). True iff ANY spec of the fn is tagged.
    let tagged_return_fns: std::collections::HashSet<crate::fz_ir::FnId> = {
        let mut s = std::collections::HashSet::new();
        for &sid in &tagged_return_specs {
            if let Some(idx) = spec_fnidx[sid as usize] {
                s.insert(module.fns[idx].id);
            }
        }
        s
    };

    // fz-ul4.27.22.3 — cont specs whose producer is a closure-target
    // (or whose producer is a Receive / CallClosure with unknown
    // target) must accept Tagged at slot 0. The producer returns
    // Tagged (forced for closure-target; opaque for unknown closure /
    // mailbox), and the cont's wire sig at the seam must agree.
    // fz-ntz extends "closure-target" to "Tagged-returning"
    // (`tagged_return_fns`) so direct-Calls into a Tagged-returning
    // fn also force the cont's slot 0 to FzValue.
    let mut tagged_slot0_cont_specs: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    for sid_caller in 0..spec_count {
        let Some(caller_idx) = spec_fnidx[sid_caller] else {
            continue;
        };
        let caller = &module.fns[caller_idx];
        let caller_ft = spec_fn_types[sid_caller].expect("non-sentinel spec must have FnTypes");
        for blk in &caller.blocks {
            let cont = match &blk.terminator {
                Term::Call {
                    callee,
                    continuation,
                    ..
                } => {
                    if tagged_return_fns.contains(callee) {
                        Some(continuation)
                    } else {
                        None
                    }
                }
                Term::CallClosure { continuation, .. } | Term::Receive { continuation } => {
                    Some(continuation)
                }
                _ => None,
            };
            if let Some(cont) = cont {
                let key =
                    crate::ir_typer::cont_input_key(blk, cont, caller_ft, module, &module_types);
                if let Some(sid) = spec_registry.resolve(cont.fn_id, &key) {
                    tagged_slot0_cont_specs.insert(sid.0);
                }
            }
        }
    }
    let param_reprs: Vec<Vec<ArgRepr>> = param_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, mut reprs)| {
            if !reprs.is_empty() && tagged_slot0_cont_specs.contains(&(sid as u32)) {
                reprs[0] = ArgRepr::Tagged;
            }
            reprs
        })
        .collect();
    let return_reprs: Vec<ArgRepr> = return_descrs.iter().map(ArgRepr::from_descr).collect();
    // fz-cps.1.8 — closure-target spec bodies return Tagged i64, matching
    // the closure-target sig in §8.2's target clif. fz-ntz extends this
    // to every fn in `tagged_return_fns`: a fn whose only exit is
    // Term::TailCallClosure (or which TailCalls into one) forwards the
    // closure-target's Tagged return bits through its own outer sig.
    // Declaring that outer return as RawInt/RawF64 would let the
    // caller read tag-shifted bits as a raw number (e.g. 42 → 337).
    let return_reprs: Vec<ArgRepr> = return_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, r)| {
            // fz-ul4.27.22.12 — per-spec override (was per-fn pre-22.12).
            // tagged_return_specs is the precise grain; specs whose
            // TailCallClosure resolves via closure_lit keep their narrow
            // return repr.
            if tagged_return_specs.contains(&(sid as u32)) {
                ArgRepr::Tagged
            } else {
                r
            }
        })
        .collect();

    // fz-ul4.27.6.2.2/.3 — Per-spec Cranelift Signature. Native fns get
    // typed-arity i64s + host_ctx; uniform fns get (i64, i64) -> i64.
    // Sentinel slots get the uniform sig — they're never declared.
    let fn_sigs: Vec<Signature> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let is_native = natively_callable.contains(&f.id);
                let needs_host_ctx = fns_needing_host_ctx.contains(&f.id);
                build_fn_signature(
                    &param_reprs[sid],
                    return_reprs[sid],
                    is_native,
                    needs_host_ctx,
                    cont_fns.contains(&f.id),
                    // fz-cps.1.2: closure-target fn shape gated on
                    // native (uniform closure targets still go through
                    // the existing stub adapter).
                    if is_native {
                        closure_n_captures.get(&f.id).copied()
                    } else {
                        None
                    },
                )
            }
            None => {
                let mut sig = Signature::new(CallConv::SystemV);
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                sig
            }
        })
        .collect();

    // Declare one Cranelift function per real SpecId, named
    // `fz_fn_{spec_id.0}`. Sentinel slots are skipped — no module
    // declaration is made. Any-key SpecId.0 == FnId.0 so the existing
    // closure / Spawn / Receive paths (which iconst fn_id.0 as the
    // schema_id) keep landing on the right entry.
    let linkage = backend.fn_linkage();
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for sid in 0..spec_count {
        if spec_fnidx[sid].is_none() {
            continue;
        }
        let name = format!("fz_fn_{}", sid);
        let id = backend
            .module_mut()
            .declare_function(&name, linkage, &fn_sigs[sid])
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(sid as u32, id);
    }

    // fz-cps.1.8 — closure stubs deleted. Closure invocation is now a
    // direct Tail-CC return_call_indirect through cl+16 against the
    // body's closure-target sig `(args..., self, cont) tail` (§8.2).
    // MakeClosure stores body_func_addr at +16; the body's entry harness
    // loads its captures from self+24+8*i. fz_stub_fn_ids is retained as
    // an empty BTreeMap so compile_fn's signature stays unchanged for
    // this commit; fz-siu.1.13 will drop the parameter.
    let stub_fn_ids: std::collections::BTreeMap<u32, FuncId> = std::collections::BTreeMap::new();

    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            continue;
        };
        let f = &module.fns[idx];
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
        let func_id = *fn_ids.get(&(sid as u32)).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sigs[sid].clone();
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
            &stub_fn_ids,
            f,
            ft,
            sid as u32,
            &spec_registry,
            &module.source,
            &natively_callable,
            &cont_target_fns,
            &cont_fns,
            &closure_n_captures,
            &fns_needing_host_ctx,
            &fn_ids,
            &param_reprs,
            &return_reprs,
            &working,
            &module_types,
        )?;
        // Any-key SpecId.0 == FnId.0 (invariant); use the bare fn name so
        // tests / `fz dump --emit clif` can refer to functions by source
        // name. Narrow specs append `_s{sid}` to keep names distinct.
        let display_name = if (sid as u32) == f.id.0 {
            f.name.clone()
        } else {
            format!("{}_s{}", f.name, sid)
        };
        // fz-ul4.32.1 — annotate raw CLIF with IR Descrs + ArgReprs so
        // golden_clif / `fz dump --emit clif` show what the typer
        // decided, not just what was lowered.
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                let raw = ctx.func.display().to_string();
                let header = build_typer_header(
                    f,
                    ft,
                    &spec_keys[sid].1,
                    &param_reprs[sid],
                    return_reprs[sid],
                );
                let annotated = VALUE_DESCR_RECORD.with(|vd| {
                    let b = vd.borrow();
                    match b.as_ref() {
                        Some(map) => annotate_clif_dump(&raw, map, &header),
                        None => {
                            let empty = HashMap::new();
                            annotate_clif_dump(&raw, &empty, &header)
                        }
                    }
                });
                v.push((display_name.clone(), annotated));
            }
        });
        let fn_span = module.source.fn_span_of(f.id);
        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verifier::verify_function(&ctx.func, &flags).map_err(|e| {
            CodegenError::new(format!(
                "verify {}:\n{}\n--- IR ---\n{}",
                display_name,
                e,
                ctx.func.display()
            ))
            .with_span(fn_span)
        })?;
        backend
            .module_mut()
            .define_function(func_id, &mut ctx)
            .map_err(|e| {
                CodegenError::new(format!("define {}: {}", display_name, e)).with_span(fn_span)
            })?;
        if want_asm {
            if let Some(cc) = ctx.compiled_code() {
                if let Some(vcode) = cc.vcode.as_ref() {
                    ASM_RECORD.with(|c| {
                        if let Some(v) = c.borrow_mut().as_mut() {
                            v.push((display_name.clone(), vcode.clone()));
                        }
                    });
                }
            }
        }
        backend.module_mut().clear_context(&mut ctx);
    }

    // fz-cps.1.8 — stub compilation loop deleted alongside stub
    // registration. compile_closure_stub itself is dead code until
    // fz-siu.1.13 cleanup; left in place to avoid a noisy delete in this
    // commit.

    let main_fn_id = module.fn_by_name("main").map(|f| f.id);
    let main_frame_size = main_fn_id.map(|id| schemas[id.0 as usize].size);

    // fz-cps.1.7 — collect zero-capture closure-target specs for static
    // singletons. fz-cps.1.8 — code_ptr is the body's func_addr directly
    // (closure-target sig `(args, self, cont) tail`), not a SystemV stub.
    // The singleton acts both as `self` for direct callers (zero-cap
    // bodies ignore self) and as the closure handed to MakeClosure(fid,
    // []) sites. See docs/cps-in-clif.md §8.2.
    let static_closure_targets: Vec<(u32, u32, FuncId, u32)> = closure_shapes
        .iter()
        .filter(|(_, n_caps)| **n_caps == 0)
        .map(|(cl_sid, _)| {
            let fn_id = spec_keys[*cl_sid as usize].0;
            let body_fid = *fn_ids
                .get(cl_sid)
                .expect("zero-cap closure spec must have a body FuncId");
            // fz-ul4.27.22.6: pack halt_kind so fz_spawn_entry can pick
            // the matching halt-cont singleton at task launch.
            let halt_kind = return_reprs[*cl_sid as usize].halt_kind();
            (*cl_sid, fn_id.0, body_fid, halt_kind)
        })
        .collect();

    let diagnostics = crate::ir_typer::collect_diagnostics(module, &module_types);
    // fz-ul4.27.22.3 — per-spec chain analysis: for each registered
    // spec, walk its exit terminators and follow callee resolutions
    // transitively. The chain's halt-seam kind = JOIN of every Return
    // contributing along reachable paths.
    let chain_repr: Vec<ArgRepr> = {
        let join = |a: ArgRepr, b: ArgRepr| -> ArgRepr { if a == b { a } else { ArgRepr::Tagged } };
        let mut chain: Vec<Option<ArgRepr>> = vec![None; spec_count];
        let resolve_sid_under =
            |callee_id: FnId, caller_sid: u32, args: &[crate::fz_ir::Var]| -> Option<u32> {
                let any_sid = caller_sid as usize;
                let ft = spec_fn_types.get(any_sid).and_then(|o| *o)?;
                let arg_descrs: Vec<crate::types::Descr> = args
                    .iter()
                    .map(|av| {
                        ft.vars
                            .get(av)
                            .cloned()
                            .unwrap_or_else(crate::types::Descr::any)
                    })
                    .collect();
                spec_registry.resolve(callee_id, &arg_descrs).map(|s| s.0)
            };
        for _ in 0..(spec_count * 4 + 16) {
            let mut changed = false;
            for sid in 0..spec_count {
                let Some(idx) = spec_fnidx[sid] else {
                    continue;
                };
                let f = &module.fns[idx];
                let mut contributions: Vec<ArgRepr> = Vec::new();
                for blk in &f.blocks {
                    match &blk.terminator {
                        Term::Return(_) => {
                            contributions.push(return_reprs[sid]);
                        }
                        Term::TailCall { callee, args } => {
                            let csid =
                                resolve_sid_under(*callee, sid as u32, args).unwrap_or(callee.0);
                            if let Some(c) = chain.get(csid as usize).and_then(|o| *o) {
                                contributions.push(c);
                            }
                        }
                        Term::Call { continuation, .. }
                        | Term::CallClosure { continuation, .. }
                        | Term::Receive { continuation } => {
                            // Cont's chain: under the caller's per-spec
                            // env, the cont's resolved sid via the typer's
                            // cont_input_key (already done elsewhere) —
                            // here we use the cont's any-key as a sound
                            // over-approximation. JOIN refines later.
                            let cont_sid = continuation.fn_id.0;
                            if let Some(c) = chain.get(cont_sid as usize).and_then(|o| *o) {
                                contributions.push(c);
                            }
                        }
                        Term::TailCallClosure { closure, args } => {
                            // fz-ul4.27.22.12 — closure_lit-driven chain
                            // resolution. When this spec's env types the
                            // closure as `closure_lit(F, K)`, the resolved
                            // body's chain feeds ours. Mirrors 22.11's
                            // direct-dispatch resolution but at the
                            // pre-codegen analysis stage so halt_kind
                            // selection (fz_spawn_entry, halt-cont
                            // singletons) picks the right kind.
                            let resolved_body = (|| {
                                let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                                let cv_descr = ft.vars.get(closure)?;
                                let lit = cv_descr.as_closure_lit()?;
                                let body_fn = module.fn_by_id(lit.fn_id);
                                let body_n_params = body_fn.block(body_fn.entry).params.len();
                                let mut full_key: Vec<crate::types::Descr> = lit.captures.clone();
                                for av in args.iter() {
                                    full_key.push(
                                        ft.vars
                                            .get(av)
                                            .cloned()
                                            .unwrap_or_else(crate::types::Descr::any),
                                    );
                                }
                                while full_key.len() < body_n_params {
                                    full_key.push(crate::types::Descr::any());
                                }
                                full_key.truncate(body_n_params);
                                spec_registry.resolve(lit.fn_id, &full_key).map(|s| s.0)
                            })();
                            match resolved_body {
                                Some(body_sid) => {
                                    if let Some(c) = chain.get(body_sid as usize).and_then(|o| *o) {
                                        contributions.push(c);
                                    }
                                }
                                None => {
                                    // Indirect dispatch via cl+16 uses the
                                    // all-Tagged seam ABI, so anything
                                    // returning through it is Tagged.
                                    contributions.push(ArgRepr::Tagged);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if contributions.is_empty() {
                    continue;
                }
                let joined = contributions.into_iter().reduce(join).unwrap();
                if chain[sid] != Some(joined) {
                    chain[sid] = Some(joined);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        chain
            .into_iter()
            .map(|o| o.unwrap_or(ArgRepr::Tagged))
            .collect()
    };
    let fn_halt_kinds: HashMap<u32, u32> = {
        let mut m: HashMap<u32, u32> = HashMap::new();
        for f in &module.fns {
            // Use the fn's any-key spec sid for the entry-time chain.
            let sid = f.id.0 as usize;
            if let Some(r) = chain_repr.get(sid).copied() {
                m.insert(f.id.0, r.halt_kind());
            }
        }
        m
    };
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
        parking_reachable,
        natively_callable,
        return_descrs,
        main_fn_id,
        main_frame_size,
        spec_registry,
        static_closure_targets,
        resume_park_id: runtime.resume_park_id,
        spawn_entry_id: runtime.spawn_entry_id,
        main_entry_id: runtime.main_entry_id,
        halt_cont_body_ids: [
            runtime.halt_cont_body_tagged_id,
            runtime.halt_cont_body_i64_id,
            runtime.halt_cont_body_f64_id,
        ],
        fn_halt_kinds,
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

/// Emit the AOT C-callable main entry (fz-siu.6.1). Drives the cps-in-clif
/// startup: `fz_aot_setup` → per-closure `fz_aot_register_static_closure`
/// → `fz_aot_run_main`. The shim addresses (fz_main_entry,
/// fz_halt_cont_body) are taken via Cranelift `func_addr` against the
/// Local symbols emitted by compile_with_backend.
#[allow(clippy::too_many_arguments)]
fn emit_aot_c_main<M: cranelift_module::Module>(
    jmod: &mut M,
    fbctx: &mut FunctionBuilderContext,
    c_main_id: FuncId,
    c_main_sig: &Signature,
    main_fz_func_id: FuncId,
    main_entry_id: FuncId,
    halt_cont_body_ids: [FuncId; 3],
    spawn_entry_id: FuncId,
    resume_park_id: FuncId,
    static_closure_targets: &[(u32, u32, FuncId, u32 /* halt_kind */)],
    atom_blob_data: Option<DataId>,
    atom_blob_len: u32,
    setup_id: FuncId,
    reg_id: FuncId,
    run_id: FuncId,
) -> Result<(), CodegenError> {
    use cranelift_frontend::FunctionBuilder;

    let mut ctx = jmod.make_context();
    ctx.func.signature = c_main_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);

        // Atom blob: symbol address + byte length.
        let atom_blob_addr = match atom_blob_data {
            Some(data_id) => {
                let gv = jmod.declare_data_in_func(data_id, b.func);
                b.ins().symbol_value(types::I64, gv)
            }
            None => b.ins().iconst(types::I64, 0),
        };
        let atom_blob_len_v = b.ins().iconst(types::I32, atom_blob_len as i64);

        // Shim addresses (Local symbols in this object).
        let hcb_tagged_fref = jmod.declare_func_in_func(halt_cont_body_ids[0], b.func);
        let hcb_tagged_addr = b.ins().func_addr(types::I64, hcb_tagged_fref);
        let hcb_i64_fref = jmod.declare_func_in_func(halt_cont_body_ids[1], b.func);
        let hcb_i64_addr = b.ins().func_addr(types::I64, hcb_i64_fref);
        let hcb_f64_fref = jmod.declare_func_in_func(halt_cont_body_ids[2], b.func);
        let hcb_f64_addr = b.ins().func_addr(types::I64, hcb_f64_fref);
        let me_fref = jmod.declare_func_in_func(main_entry_id, b.func);
        let me_addr = b.ins().func_addr(types::I64, me_fref);
        let se_fref = jmod.declare_func_in_func(spawn_entry_id, b.func);
        let se_addr = b.ins().func_addr(types::I64, se_fref);
        let rp_fref = jmod.declare_func_in_func(resume_park_id, b.func);
        let rp_addr = b.ins().func_addr(types::I64, rp_fref);
        let main_fref = jmod.declare_func_in_func(main_fz_func_id, b.func);
        let main_fp = b.ins().func_addr(types::I64, main_fref);

        // proc = fz_aot_setup(atom_blob, atom_blob_len,
        //                     hcb_tagged, hcb_i64, hcb_f64,
        //                     se_addr, rp_addr)
        let setup_fref = jmod.declare_func_in_func(setup_id, b.func);
        let setup_call = b.ins().call(
            setup_fref,
            &[
                atom_blob_addr,
                atom_blob_len_v,
                hcb_tagged_addr,
                hcb_i64_addr,
                hcb_f64_addr,
                se_addr,
                rp_addr,
            ],
        );
        let proc_v = b.inst_results(setup_call)[0];

        // Register each static closure target.
        for (cl_sid, fn_id, body_func_id, halt_kind) in static_closure_targets {
            let cl_sid_v = b.ins().iconst(types::I32, *cl_sid as i64);
            let fn_id_v = b.ins().iconst(types::I32, *fn_id as i64);
            let body_fref = jmod.declare_func_in_func(*body_func_id, b.func);
            let body_addr = b.ins().func_addr(types::I64, body_fref);
            let hk_v = b.ins().iconst(types::I32, *halt_kind as i64);
            let reg_fref = jmod.declare_func_in_func(reg_id, b.func);
            b.ins()
                .call(reg_fref, &[proc_v, cl_sid_v, fn_id_v, body_addr, hk_v]);
        }

        // exit = fz_aot_run_main(proc, main_fp, main_entry_addr)
        let run_fref = jmod.declare_func_in_func(run_id, b.func);
        let run_call = b.ins().call(run_fref, &[proc_v, main_fp, me_addr]);
        let result = b.inst_results(run_call)[0];
        b.ins().return_(&[result]);

        b.seal_all_blocks();
        b.finalize();
    }
    let flags = settings::Flags::new(settings::builder());
    cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
        .map_err(|e| CodegenError::new(format!("verify C main: {}", e)))?;
    jmod.define_function(c_main_id, &mut ctx)
        .map_err(|e| CodegenError::new(format!("define C main: {}", e)))?;
    jmod.clear_context(&mut ctx);
    Ok(())
}

fn sig1(params: &[ir::Type], rets: &[ir::Type]) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for p in params {
        s.params.push(AbiParam::new(*p));
    }
    for r in rets {
        s.returns.push(AbiParam::new(*r));
    }
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
    let print_i64_id = decl("fz_print_i64", &[types::I64], &[])?;
    let print_f64_id = decl("fz_print_f64", &[types::F64], &[])?;
    let halt_id = decl("fz_halt", &[types::I64, types::I64], &[])?;
    let halt_implicit_id = decl("fz_halt_implicit", &[types::I64], &[])?;
    // fz-ul4.27.22.3 — typed halt-implicit variants.
    let halt_implicit_i64_id = decl("fz_halt_implicit_i64", &[types::I64], &[])?;
    let halt_implicit_f64_id = decl("fz_halt_implicit_f64", &[types::F64], &[])?;
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
    // fz-ul4.27.9: mixed-type arith/cmp slow paths are now inlined in JIT.
    // `fz_promote_f64` does the tag-aware Int|Float→f64 conversion (with the
    // same panic-on-non-numeric semantics the old fz_arith_* helpers had);
    // `fz_fmod` covers float remainder (Cranelift has no frem opcode).
    let promote_f64_id = decl("fz_promote_f64", &[types::I64], &[types::F64])?;
    let fmod_id = decl("fz_fmod", &[types::F64, types::F64], &[types::F64])?;
    let value_eq_id = decl("fz_value_eq", arith_params, arith_ret)?;

    let vec_begin_id = decl("fz_vec_begin", &[types::I32], &[])?;
    let vec_push_id = decl("fz_vec_push", &[types::I64], &[])?;
    let vec_finalize_id = decl("fz_vec_finalize", &[], &[types::I64])?;
    let vec_get_id = decl("fz_vec_get", &[types::I64, types::I64], &[types::I64])?;

    let alloc_closure_id = decl(
        "fz_alloc_closure",
        &[types::I32, types::I32, types::I32],
        &[types::I64],
    )?;
    let spawn_id = decl("fz_spawn", &[types::I64], &[types::I64])?;
    let spawn_opt_id = decl("fz_spawn_opt", &[types::I64, types::I64], &[types::I64])?;
    let self_id = decl("fz_self", &[], &[types::I64])?;
    let send_id = decl("fz_send", &[types::I64, types::I64], &[types::I64])?;
    let receive_attempt_id = decl("fz_receive_attempt", &[types::I64], &[types::I64])?;
    // fz-cps.1.2 — receive cutover. Takes a cont closure ptr (i64),
    // stashes in Process::parked_cont, returns YIELD sentinel.
    let receive_park_id = decl("fz_receive_park", &[types::I64], &[types::I64])?;
    // fz-cps.1.7 — static zero-capture closure singleton lookup.
    // Returns the per-Process singleton pointer for the given cl_sid.
    let get_static_closure_id = decl("fz_get_static_closure", &[types::I32], &[types::I64])?;
    // fz-cps.1.11 — halt-cont singleton lookup. Returns the per-Process
    // halt-cont closure ptr; lazily initialized using the supplied
    // halt_cont_body addr (JIT pre-populates at make_process time;
    // AOT path relies on lazy init at first call).
    // fz-ul4.27.22.3 — `(addr, kind)` sig: kind selects among 3 Process
    // singletons (0=Tagged, 1=RawInt, 2=RawF64).
    let get_halt_cont_id = decl("fz_get_halt_cont", &[types::I64, types::I32], &[types::I64])?;
    // fz-ul4.27.22.3 — three fz_halt_cont_body variants, declared LOCAL
    // (bodies emitted below). Tagged: `(i64 Tagged, i64) -> i64 tail`;
    // RawInt: `(i64, i64) -> i64 tail`; RawF64: `(f64, i64) -> i64 tail`.
    let mut declare_hcb = |name: &str, val_ty: ir::Type| -> Result<FuncId, CodegenError> {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function(name, Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
    };
    let halt_cont_body_tagged_id = declare_hcb("fz_halt_cont_body_tagged", types::I64)?;
    let halt_cont_body_i64_id = declare_hcb("fz_halt_cont_body_i64", types::I64)?;
    let halt_cont_body_f64_id = declare_hcb("fz_halt_cont_body_f64", types::F64)?;
    // fz-cps.1.11 — fz_resume_park: SystemV entry the scheduler calls on
    // wakeup. Body emitted in compile_with_backend; signature `(msg:i64,
    // cont:i64) -> i64 system_v` matches Rust's extern "C" shape for FFI.
    let mut rp_sig = Signature::new(CallConv::SystemV);
    rp_sig.params.push(AbiParam::new(types::I64));
    rp_sig.params.push(AbiParam::new(types::I64));
    rp_sig.returns.push(AbiParam::new(types::I64));
    let resume_park_id = jmod
        .declare_function("fz_resume_park", Linkage::Local, &rp_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_resume_park: {}", e)))?;
    // fz-cps.1.11 — fz_spawn_entry: SystemV entry the scheduler calls to
    // launch a new task's zero-arg closure. Sig: `(closure:i64) -> i64`.
    let mut se_sig = Signature::new(CallConv::SystemV);
    se_sig.params.push(AbiParam::new(types::I64));
    se_sig.returns.push(AbiParam::new(types::I64));
    let spawn_entry_id = jmod
        .declare_function("fz_spawn_entry", Linkage::Local, &se_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_spawn_entry: {}", e)))?;
    // fz-ul4.27.22.3 — fz_main_entry: SystemV entry the scheduler calls
    // to launch at a known main fn. Sig: `(main_fp:i64, halt_cl:i64)
    // -> i64`. Rust caller picks halt_cl from process.halt_cont_singletons
    // by the entry fn's return_repr kind.
    let mut me_sig = Signature::new(CallConv::SystemV);
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.params.push(AbiParam::new(types::I64));
    me_sig.returns.push(AbiParam::new(types::I64));
    let main_entry_id = jmod
        .declare_function("fz_main_entry", Linkage::Local, &me_sig)
        .map_err(|e| CodegenError::new(format!("declare fz_main_entry: {}", e)))?;

    Ok(RuntimeRefs {
        print_id,
        print_i64_id,
        print_f64_id,
        halt_id,
        halt_implicit_id,
        halt_implicit_i64_id,
        halt_implicit_f64_id,
        halt_cont_body_tagged_id,
        halt_cont_body_i64_id,
        halt_cont_body_f64_id,
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
        promote_f64_id,
        fmod_id,
        value_eq_id,
        vec_begin_id,
        vec_push_id,
        vec_finalize_id,
        vec_get_id,
        alloc_closure_id,
        spawn_id,
        spawn_opt_id,
        self_id,
        send_id,
        receive_attempt_id,
        receive_park_id,
        get_static_closure_id,
        get_halt_cont_id,
        resume_park_id,
        spawn_entry_id,
        main_entry_id,
    })
}

#[derive(Clone, Copy)]
struct RuntimeRefs {
    print_id: FuncId,
    print_i64_id: FuncId,
    print_f64_id: FuncId,
    halt_id: FuncId,
    halt_implicit_id: FuncId,
    halt_implicit_i64_id: FuncId,
    halt_implicit_f64_id: FuncId,
    halt_cont_body_tagged_id: FuncId,
    halt_cont_body_i64_id: FuncId,
    halt_cont_body_f64_id: FuncId,
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
    vec_begin_id: FuncId,
    vec_push_id: FuncId,
    vec_finalize_id: FuncId,
    vec_get_id: FuncId,
    alloc_float_id: FuncId,
    promote_f64_id: FuncId,
    fmod_id: FuncId,
    value_eq_id: FuncId,
    alloc_closure_id: FuncId,
    spawn_id: FuncId,
    spawn_opt_id: FuncId,
    self_id: FuncId,
    send_id: FuncId,
    receive_attempt_id: FuncId,
    receive_park_id: FuncId,
    get_static_closure_id: FuncId,
    get_halt_cont_id: FuncId,
    resume_park_id: FuncId,
    spawn_entry_id: FuncId,
    main_entry_id: FuncId,
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
    stub_fn_ids: &std::collections::BTreeMap<u32, FuncId>,
    f: &crate::fz_ir::FnIr,
    fn_types: &crate::ir_typer::FnTypes,
    this_spec_id: u32,
    spec_registry: &SpecRegistry,
    source: &crate::fz_ir::SourceInfo,
    natively_callable: &std::collections::HashSet<crate::fz_ir::FnId>,
    cont_target_fns: &std::collections::HashSet<crate::fz_ir::FnId>,
    cont_fns: &std::collections::HashSet<crate::fz_ir::FnId>,
    closure_n_captures: &std::collections::HashMap<crate::fz_ir::FnId, usize>,
    fns_needing_host_ctx: &std::collections::HashSet<crate::fz_ir::FnId>,
    fn_ids: &HashMap<u32, FuncId>,
    param_reprs: &[Vec<ArgRepr>],
    return_reprs: &[ArgRepr],
    module: &crate::fz_ir::Module,
    module_types: &crate::ir_typer::ModuleTypes,
) -> Result<(), CodegenError> {
    let is_native = natively_callable.contains(&f.id);
    let is_cont_fn = cont_fns.contains(&f.id);
    // fz-cps.1.2 — closure-target fn shape per §2.1: `(args..., self,
    // cont) tail`. Only takes effect for native fns; uniform fns still
    // go through the closure-stub adapter for now.
    let closure_target_n_caps: Option<usize> = if is_native && !is_cont_fn {
        closure_n_captures.get(&f.id).copied()
    } else {
        None
    };
    // fz-ul4.27.18: when this fn is never invoked from any fz IR site
    // (not a direct callee, not a continuation, not a closure target),
    // it can only enter via the trampoline entry, which writes null
    // into the frame's slot 0. cont_ptr is therefore statically null at
    // runtime; emit_return can elide the load/icmp/brif dispatch and
    // emit a halt-only path. The `cont_target_fns` parameter is the
    // upstream set of "ever referenced from fz IR" FnIds.
    let cont_ptr_known_null = !cont_target_fns.contains(&f.id);
    let callee_is_native = |id: u32| natively_callable.contains(&crate::fz_ir::FnId(id));
    // Resolve a direct callsite to its narrow SpecId.0 if a matching spec
    // exists; otherwise fall back to the callee's any-key SpecId.0 (== the
    // callee's FnId.0 by invariant). Caller's `fn_types` carries the arg
    // Descrs at this callsite.
    // fz-ul4.29.12.1: resolve a Cont at this caller-block to its
    // narrow SpecId.0 via the typer's input-Descr key. The typer
    // registers a spec for every reachable Cont site (see
    // `ir_typer.rs:184-242` / `cont_input_key`); subsumption resolve
    // in SpecRegistry falls back to a covering super-spec (any-key
    // at minimum) when no exact match exists. Panic on miss for the
    // same .29.11 discipline as `resolve_callee_sid` below.
    let resolve_cont_sid = |blk: &crate::fz_ir::Block, continuation: &crate::fz_ir::Cont| -> u32 {
        let key =
            crate::ir_typer::cont_input_key(blk, continuation, fn_types, module, module_types);
        spec_registry
            .resolve(continuation.fn_id, &key)
            .map(|s| s.0)
            .unwrap_or_else(|| {
                panic!(
                    ".29.12.1: no covering spec for Cont FnId({}) with key {:?}; \
                 registered keys for this cont: {:?}",
                    continuation.fn_id.0,
                    key,
                    spec_registry
                        .iter()
                        .filter(|(_, fid, _)| *fid == continuation.fn_id)
                        .map(|(s, _, k)| (s.0, k.to_vec()))
                        .collect::<Vec<_>>()
                )
            })
    };
    let resolve_callee_sid = |callee: crate::fz_ir::FnId, args: &[crate::fz_ir::Var]| -> u32 {
        let descrs: Vec<crate::types::Descr> = args
            .iter()
            .map(|av| {
                fn_types
                    .vars
                    .get(av)
                    .cloned()
                    .unwrap_or_else(crate::types::Descr::any)
            })
            .collect();
        // fz-ul4.29.11: subsumption-based lookup. If nothing covers, this
        // is a real consistency error — the typer should have registered
        // a covering spec (any-key at minimum). Panic loudly so the gap
        // surfaces during development instead of crashing later with a
        // sentinel schema lookup.
        spec_registry
            .resolve(callee, &descrs)
            .map(|s| s.0)
            .unwrap_or_else(|| {
                panic!(
                    ".29.11: no covering spec for FnId({}) with arg Descrs {:?}; \
                 registered specs for this fn: {:?}",
                    callee.0,
                    descrs,
                    spec_registry
                        .iter()
                        .filter(|(_, fid, _)| *fid == callee)
                        .map(|(s, _, k)| (s.0, k.to_vec()))
                        .collect::<Vec<_>>()
                )
            })
    };
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    // fz-ul4.30 — reachability filter. `ir_lower` emits an unconditional
    // `fail_block` per fn (Halt with :function_clause atom) for clauses
    // whose patterns fail at runtime, and similar match-fail blocks for
    // `cond` / lambda bodies. Single-clause fns with bare-var params
    // never Goto their fail_block, leaving it as dead CLIF. Worse, the
    // dead Halt's `return` was previously typed `i64` regardless of the
    // fn's sig — under .27.13's per-Descr return type this trips the
    // Cranelift verifier (f64 sig vs i64 return). Skip emitting those
    // blocks entirely.
    let reachable_fz_blocks: std::collections::HashSet<u32> = {
        let mut reach: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack: Vec<u32> = vec![f.entry.0];
        while let Some(bid) = stack.pop() {
            if !reach.insert(bid) {
                continue;
            }
            let blk = match f.blocks.iter().find(|b| b.id.0 == bid) {
                Some(b) => b,
                None => continue,
            };
            match &blk.terminator {
                Term::Goto(t, _) => stack.push(t.0),
                Term::If(_, t, e) => {
                    stack.push(t.0);
                    stack.push(e.0);
                }
                // Return / TailCall / Halt / Call / CallClosure /
                // TailCallClosure / Receive don't pass control to other
                // fz_ir blocks within this fn; codegen lowers them into
                // Cranelift sub-blocks owned by the lowering site itself.
                _ => {}
            }
        }
        reach
    };

    let mut block_map: HashMap<u32, ir::Block> = HashMap::new();
    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    let entry_blk = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    if is_native {
        // fz-ul4.27.6.2.3 / .27.13 — native fn entry: one block_param per
        // fz arg whose type matches my param_reprs[i] (F64 for raw float,
        // I64 for raw int or tagged), plus a trailing host_ctx i64. No
        // frame_ptr; native fns run synchronously inside their caller and
        // never visit the trampoline.
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // fz-ul4.27.22.3 cont fn entry per §2.1: result's Cranelift
            // type matches my_param_reprs[0].cl_type() (RawInt=i64,
            // RawF64=f64, Tagged=i64). Body sees the value in its native
            // shape — no coerce at entry.
            b.append_block_param(entry_cl, my_param_reprs[0].cl_type()); // result
            b.append_block_param(entry_cl, types::I64); // self
        } else if let Some(n_caps) = closure_target_n_caps {
            // fz-cps.1.2 closure-target fn entry per §2.1:
            // `(args..., self:i64, cont:i64) tail`. n_args = total - n_caps.
            let n_args = my_param_reprs.len().saturating_sub(n_caps);
            for r in &my_param_reprs[..n_args] {
                b.append_block_param(entry_cl, r.cl_type());
            }
            b.append_block_param(entry_cl, types::I64); // self
            b.append_block_param(entry_cl, types::I64); // cont
        } else {
            for r in my_param_reprs {
                b.append_block_param(entry_cl, r.cl_type());
            }
            if fns_needing_host_ctx.contains(&f.id) {
                b.append_block_param(entry_cl, types::I64); // host_ctx
            }
            b.append_block_param(entry_cl, types::I64); // cont
        }
    } else {
        b.append_block_param(entry_cl, types::I64); // frame_ptr
        b.append_block_param(entry_cl, types::I64); // host_ctx
    }

    for blk in &f.blocks {
        if blk.id == f.entry {
            continue;
        }
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for _ in &blk.params {
            b.append_block_param(cl_blk, types::I64);
        }
    }

    b.switch_to_block(entry_cl);
    b.seal_block(entry_cl);

    let mut var_map: HashMap<u32, ir::Value> = HashMap::new();
    let mut raw_f64_vars: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let mut raw_int_vars: std::collections::HashSet<u32> = std::collections::HashSet::new();
    let my_schema = &schemas[this_spec_id as usize];

    // (frame_ptr, host_ctx) — uniform fns get both from entry block_params;
    // native fns have no frame and no frame_ptr (None). fz-ul4.27.16: the
    // 9 downstream consumer sites are each gated on `is_native` or on a
    // terminator type that natively_callable excludes from native fns,
    // so unwrapping the Option below is invariant-safe. Any future code
    // path that violates this surfaces immediately as a panic at codegen.
    // fz-ul4.27.19: host_ctx is `Option<ir::Value>` — None for native fns
    // whose sig dropped it (per `fns_needing_host_ctx`). Use sites that
    // forward or call fz_halt unwrap with `.expect(...)`; the analysis
    // guarantees those paths only fire when host_ctx was kept.
    // fz-cps.1.a (fz-siu.1.1): `cont_param` is the trailing i64 in the
    // native-tier signature. Threaded but unused in .1.1; .1.2+ consume it.
    let (frame_ptr, host_ctx, cont_param): (
        Option<ir::Value>,
        Option<ir::Value>,
        Option<ir::Value>,
    ) = if is_native {
        let params: Vec<ir::Value> = b.block_params(entry_cl).to_vec();
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // fz-cps.1.2 cont fn entry harness per §2.1:
            //   params[0] = result        → fz_param[0]
            //   params[1] = self          → closure ptr
            //   params[2] = host_ctx?     → conditional
            // Closure layout (§2.2 + cps cutover):
            //   self+16 : code_ptr
            //   self+24 : outer_cont       (synthetic; not in fz_param)
            //   self+32 : user_cap[0]      → fz_param[1]
            //   self+40 : user_cap[1]      → fz_param[2]
            //   ...
            // The cont's "next k" is the synthetic outer_cont at +24.
            let result_param = &entry_blk.params[0];
            // fz-ul4.27.22.3: cont sig matches my_param_reprs[0]'s
            // Cranelift type directly. Producer's Term::Return uses the
            // same sig (return_reprs[producer_sid] = my_param_reprs[0]
            // via the typer's cont_input_key seam agreement). No coerce
            // at entry — value already in body's expected repr.
            match my_param_reprs[0] {
                ArgRepr::RawInt => {
                    raw_int_vars.insert(result_param.0);
                }
                ArgRepr::RawF64 => {
                    raw_f64_vars.insert(result_param.0);
                }
                ArgRepr::Tagged => {}
            }
            var_map.insert(result_param.0, params[0]);
            let self_val = params[1];
            for (i, p) in entry_blk.params.iter().enumerate().skip(1) {
                // fz_param[i] = user_cap[i-1] at offset 32 + 8*(i-1) (= +24 + 8*i).
                // fz-ul4.27.21.2 — captures are stored in their per-capture
                // repr at the builder (param_reprs[cont_sid][i]); load with
                // the matching Cranelift type. No tag/untag round-trip when
                // the capture is narrow.
                let off = HEADER_SIZE + SLOT_BYTES * 2 + ((i - 1) as i32) * SLOT_BYTES;
                let cl_ty = my_param_reprs[i].cl_type();
                let v = b.ins().load(cl_ty, MemFlags::trusted(), self_val, off);
                match my_param_reprs[i] {
                    ArgRepr::RawInt => {
                        raw_int_vars.insert(p.0);
                    }
                    ArgRepr::RawF64 => {
                        raw_f64_vars.insert(p.0);
                    }
                    ArgRepr::Tagged => {}
                }
                var_map.insert(p.0, v);
            }
            let host_ctx = if fns_needing_host_ctx.contains(&f.id) {
                Some(params[2])
            } else {
                None
            };
            (None, host_ctx, Some(self_val))
        } else if let Some(n_caps) = closure_target_n_caps {
            // fz-cps.1.2 closure-target fn entry harness per §2.1.
            // fz_params order (set by ir_lower / closure stub convention):
            //   fz_params[0..n_caps]            = captures      → load self+24+8*k
            //   fz_params[n_caps..n_caps+n_args] = args         → Cranelift params[0..n_args]
            // Cranelift sig: `(args..., self, cont) tail`.
            //   params[0..n_args]  = args
            //   params[n_args]     = self  (closure ptr)
            //   params[n_args+1]   = cont  (cont SSA)
            let n_args = entry_blk.params.len().saturating_sub(n_caps);
            let self_val = params[n_args];
            let cont_val = params[n_args + 1];
            // Captures: fz_params[0..n_caps] ← load from self+24+8*k.
            for (k, p) in entry_blk.params.iter().enumerate().take(n_caps) {
                let off = HEADER_SIZE + SLOT_BYTES + (k as i32) * SLOT_BYTES;
                let cl_ty = my_param_reprs[k].cl_type();
                let v = b.ins().load(cl_ty, MemFlags::trusted(), self_val, off);
                match my_param_reprs[k] {
                    ArgRepr::RawInt => {
                        raw_int_vars.insert(p.0);
                    }
                    ArgRepr::RawF64 => {
                        raw_f64_vars.insert(p.0);
                    }
                    ArgRepr::Tagged => {}
                }
                var_map.insert(p.0, v);
            }
            // Args: fz_params[n_caps..] ← Cranelift params[0..n_args].
            for (j, p) in entry_blk.params.iter().enumerate().skip(n_caps) {
                let cl_idx = j - n_caps;
                let repr = my_param_reprs[j];
                match repr {
                    ArgRepr::RawInt => {
                        raw_int_vars.insert(p.0);
                    }
                    ArgRepr::RawF64 => {
                        raw_f64_vars.insert(p.0);
                    }
                    ArgRepr::Tagged => {}
                }
                var_map.insert(p.0, params[cl_idx]);
            }
            let _ = self_val;
            (None, None, Some(cont_val))
        } else {
            for (i, p) in entry_blk.params.iter().enumerate() {
                match my_param_reprs[i] {
                    ArgRepr::RawInt => {
                        raw_int_vars.insert(p.0);
                    }
                    ArgRepr::RawF64 => {
                        raw_f64_vars.insert(p.0);
                    }
                    ArgRepr::Tagged => {}
                }
                var_map.insert(p.0, params[i]);
            }
            let host_ctx_idx = entry_blk.params.len();
            let (host_ctx, cont_idx) = if fns_needing_host_ctx.contains(&f.id) {
                (Some(params[host_ctx_idx]), host_ctx_idx + 1)
            } else {
                (None, host_ctx_idx)
            };
            (None, host_ctx, Some(params[cont_idx]))
        }
    } else {
        let frame_ptr = b.block_params(entry_cl)[0];
        let host_ctx = b.block_params(entry_cl)[1];

        // Load entry params from frame slots [1..N+1] (offsets 24, 32, ...).
        // fz-ul4.27.5.2/3: RawF64 slots load as raw f64 and join `raw_f64_vars`;
        // RawI64 slots load as raw i64 (unshifted int payload) and join
        // `raw_int_vars`. Everything else loads as a tagged FzValue i64.
        for (i, p) in entry_blk.params.iter().enumerate() {
            let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
            let slot_kind = &my_schema.fields[i + 1].kind;
            let val = match slot_kind {
                FieldKind::RawF64 => {
                    let f = b
                        .ins()
                        .load(types::F64, MemFlags::trusted(), frame_ptr, off);
                    raw_f64_vars.insert(p.0);
                    f
                }
                FieldKind::RawI64 => {
                    let n = b
                        .ins()
                        .load(types::I64, MemFlags::trusted(), frame_ptr, off);
                    raw_int_vars.insert(p.0);
                    n
                }
                _ => b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), frame_ptr, off),
            };
            var_map.insert(p.0, val);
        }
        // fz-cps.1.a: uniform fns do not yet have a cont SSA value; the
        // cont still lives in slot 0 of `frame_ptr` until fz-siu.1.5.
        (Some(frame_ptr), Some(host_ctx), None)
    };

    // Walk blocks in declared order with entry first. Unreachable
    // fz_ir blocks (fz-ul4.30) are filtered out — they have no
    // Cranelift counterpart.
    let mut order: Vec<&crate::fz_ir::Block> = Vec::with_capacity(f.blocks.len());
    if let Some(eb) = f.blocks.iter().find(|b| b.id == f.entry) {
        order.push(eb);
    }
    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        if blk.id != f.entry {
            order.push(blk);
        }
    }

    for blk in &order {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.switch_to_block(cl_blk);
            let params: Vec<ir::Value> = b.block_params(cl_blk).to_vec();
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
            let out = lower_prim(
                &mut b,
                jmod,
                runtime,
                tuple_schema_ids,
                stub_fn_ids,
                &var_map,
                &raw_f64_vars,
                &raw_int_vars,
                fn_types,
                spec_registry,
                module,
                fn_ids,
                param_reprs,
                return_reprs,
                prim,
                *v,
            )?;
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
        let mut used_by_term: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let note = |vs: &[crate::fz_ir::Var], set: &mut std::collections::HashSet<u32>| {
            for v in vs {
                set.insert(v.0);
            }
        };
        match &blk.terminator {
            Term::Goto(_, args) => note(args, &mut used_by_term),
            Term::If(c, _, _) => {
                used_by_term.insert(c.0);
            }
            Term::Halt(v) | Term::Return(v) => {
                used_by_term.insert(v.0);
            }
            Term::Call {
                args, continuation, ..
            } => {
                note(args, &mut used_by_term);
                note(&continuation.captured, &mut used_by_term);
            }
            Term::TailCall { args, .. } => note(args, &mut used_by_term),
            Term::CallClosure {
                closure,
                args,
                continuation,
            } => {
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
        // fz-ul4.27.13 — Pre-terminator retag pass. Terminators that expect
        // tagged FzValue inputs across the board (Goto/If/Halt/CallClosure/
        // Receive, plus uniform Call/TailCall/Return) get their
        // used-by-term raw vars promoted here. Native Call/TailCall/Return
        // handle their own per-slot coerce inline at the branch below,
        // against the callee's `param_reprs` or this fn's own
        // `return_reprs` — skip the blanket retag for those.
        //
        // fz-ul4.27.22.12 — TailCallClosure also handles its own coerce
        // inline. On the direct-dispatch path (closure_lit-resolved), arg
        // slots match the body's narrow `param_reprs` so raw vars pass
        // through untagged. The indirect path's all-Tagged coerce runs
        // inside the else branch.
        let needs_blanket_retag = match &blk.terminator {
            Term::Return(_) => !is_native,
            Term::Call { callee, .. } => !callee_is_native(callee.0),
            Term::TailCall { callee, .. } => !callee_is_native(callee.0),
            Term::TailCallClosure { .. } => false,
            _ => true,
        };
        if needs_blanket_retag {
            let to_tag_f: Vec<u32> = raw_f64_vars
                .iter()
                .copied()
                .filter(|rv| used_by_term.contains(rv))
                .collect();
            for rv in to_tag_f {
                let raw = *var_map.get(&rv).expect("raw f64 var dropped from env");
                let boxed = box_float_native(&mut b, jmod, runtime, raw);
                var_map.insert(rv, boxed);
                raw_f64_vars.remove(&rv);
            }
            let to_tag_i: Vec<u32> = raw_int_vars
                .iter()
                .copied()
                .filter(|rv| used_by_term.contains(rv))
                .collect();
            for rv in to_tag_i {
                let raw = *var_map.get(&rv).expect("raw i64 var dropped from env");
                let boxed = box_int(&mut b, raw);
                var_map.insert(rv, boxed);
                raw_int_vars.remove(&rv);
            }
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
                // fz-cps.1.2 — cont fns have no host_ctx (§2.1); their
                // Halt uses fz_halt_implicit which pulls process from TLS.
                // fz-cps.1.12 — all native fns use fz_halt_implicit too;
                // they no longer need host_ctx threading for halt.
                if is_cont_fn || is_native {
                    let hi_fref = jmod.declare_func_in_func(runtime.halt_implicit_id, b.func);
                    b.ins().call(hi_fref, &[val]);
                } else {
                    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                    let hctx = host_ctx.expect(
                        "Term::Halt needs host_ctx but fns_needing_host_ctx \
                         analysis dropped it — invariant violated",
                    );
                    b.ins().call(halt_fref, &[hctx, val]);
                }
                if is_native {
                    // fz-ul4.27.6.4 — native fn: propagate halt val back
                    // up the chain via the native return register. The
                    // outermost uniform caller's emit_return will re-call
                    // fz_halt with this val (idempotent: same value), so
                    // halt_value stays correct even when the chain halts
                    // before control returns to the trampoline.
                    //
                    // fz-ul4.27.13: dead-code halts (e.g. unreachable
                    // function_clause / match_error fail blocks) still
                    // need a typed return value — fz_halt is no-return at
                    // runtime but Cranelift's verifier doesn't model that.
                    // Emit a typed dummy when my return_repr is RawF64;
                    // for RawInt/Tagged the tagged i64 `val` is fine
                    // (caller would interpret it as the halt-propagated
                    // value if the unreachable path were ever taken).
                    // fz-cps.1.2: native return canonicalized to i64.
                    // val here is whatever repr the body produced; coerce
                    // to a tagged i64 sentinel (fz_halt already set
                    // process.halt_value, so the actual returned bits
                    // are unobservable — but the type must match the sig).
                    let _ = return_reprs[this_spec_id as usize];
                    let zero = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[zero]);
                    let _ = val;
                } else {
                    // Uniform fn: trampoline sentinel is null.
                    let null = b.ins().iconst(types::I64, 0);
                    b.ins().return_(&[null]);
                }
            }
            Term::Return(v) => {
                let val = *var_map.get(&v.0).expect("unbound return val");
                if is_native {
                    // fz-ul4.27.22.3 — native Term::Return per docs/cps-in-clif.md
                    // §2.1: `load cont+16; return_call_indirect sig(val, cont)`.
                    // Cont fns fetch outer_cont from `self+24`; non-cont fns
                    // use their cont_param SSA. Sig and val coerce match this
                    // fn's narrow return_repr — the cont's body at +16 was
                    // chosen at construction time to match (per fz-ul4.27.22.3
                    // halt-cont typing + cont-seam narrowing in
                    // build_fn_signature).
                    let my_return_repr = return_reprs[this_spec_id as usize];
                    let from = var_repr(v.0, &raw_int_vars, &raw_f64_vars);
                    let val_typed = coerce_to(&mut b, jmod, runtime, val, from, my_return_repr);
                    let cont_val = if is_cont_fn {
                        let self_val = cont_param.expect("cont fn binds self via cont_param");
                        b.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            self_val,
                            HEADER_SIZE + SLOT_BYTES,
                        )
                    } else {
                        cont_param.expect("non-cont native fn has cont_param")
                    };
                    let code = b
                        .ins()
                        .load(types::I64, MemFlags::trusted(), cont_val, HEADER_SIZE);
                    let mut sig = Signature::new(CallConv::Tail);
                    sig.params.push(AbiParam::new(my_return_repr.cl_type()));
                    sig.params.push(AbiParam::new(types::I64));
                    sig.returns.push(AbiParam::new(types::I64));
                    let sigref = b.import_signature(sig);
                    b.ins()
                        .return_call_indirect(sigref, code, &[val_typed, cont_val]);
                } else if cont_ptr_known_null {
                    // fz-ul4.27.18: this fn is never a cont target; cont_ptr
                    // is statically null. Skip the load/icmp/brif dispatch.
                    emit_halt_and_return_null(
                        &mut b,
                        jmod,
                        runtime,
                        host_ctx.expect(
                            "emit_halt_and_return_null needs host_ctx in a \
                             uniform fn (Term::Return uniform path)",
                        ),
                        val,
                    );
                } else {
                    emit_return(
                        &mut b,
                        jmod,
                        runtime,
                        frame_ptr,
                        host_ctx.expect("emit_return needs host_ctx in a uniform fn"),
                        val,
                    );
                }
            }
            Term::Call {
                callee,
                args,
                continuation,
            } => {
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound captured val"))
                    .collect();
                // fz-ul4.29.7: resolve callee → narrow SpecId.0 (falls
                // back to any-key == callee.0 via subsumption).
                // fz-ul4.29.12.1: resolve the Cont to its narrow
                // SpecId.0 too (typer registers one per Cont site;
                // any-key is the subsumption backstop).
                let callee_sid = resolve_callee_sid(*callee, args);
                let cont_sid = resolve_cont_sid(blk, continuation);
                if callee_is_native(callee.0) {
                    // fz-ul4.27.13 — coerce each arg from its current var
                    // repr to the callee's param_repr. Result rides back
                    // in the callee's return_repr; we then coerce it to
                    // Tagged for the cont (cont is the any-key spec by
                    // invariant — all-Tagged param_reprs, FzValue cont
                    // frame slot 1).
                    let callee_param_reprs = &param_reprs[callee_sid as usize];
                    let callee_ret_repr = return_reprs[callee_sid as usize];
                    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                    let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                    let mut native_args: Vec<ir::Value> = Vec::with_capacity(args.len() + 1);
                    for (i, av) in args.iter().enumerate() {
                        let raw_val = *var_map.get(&av.0).expect("unbound call arg");
                        let from = var_repr(av.0, &raw_int_vars, &raw_f64_vars);
                        let to = callee_param_reprs[i];
                        native_args.push(coerce_to(&mut b, jmod, runtime, raw_val, from, to));
                    }
                    // fz-ul4.27.19: push host_ctx only when the callee's
                    // trimmed sig still includes it.
                    if fns_needing_host_ctx.contains(callee) {
                        native_args.push(host_ctx.expect(
                            "callee needs host_ctx; this fn must also have it \
                             by the forward-transitive analysis",
                        ));
                    }
                    // fz-cps.1.8 — if the callee is a closure-target fn,
                    // its sig is `(args..., self, cont) tail`. Direct
                    // callers load the per-Process static singleton and
                    // pass it as `self`. The zero-cap invariant (asserted
                    // at closure_target_fns build) means the body ignores
                    // self at runtime, so a singleton with no captures is
                    // valid for any direct-call site.
                    if closure_n_captures.contains_key(callee) {
                        let fref = jmod.declare_func_in_func(runtime.get_static_closure_id, b.func);
                        let sid_v = b.ins().iconst(types::I32, callee.0 as i64);
                        let inst = b.ins().call(fref, &[sid_v]);
                        native_args.push(b.inst_results(inst)[0]);
                    }
                    // fz-cps.1.a: trailing cont arg per §2.1. Native
                    // caller forwards its cont SSA; uniform caller passes
                    // fz-cps.1.2 — chained-native cutover. Build the cont
                    // closure BEFORE the callee call so the callee's
                    // Term::Return can indirect-call through it (§2.1).
                    // The closure's user captures must be stored before
                    // the call too, since the cont body loads them on
                    // entry. After the callee call, the chain unwinds
                    // via halt-cont's regular return; the caller body
                    // just returns whatever propagated.
                    let cont_is_native = callee_is_native(continuation.fn_id.0);
                    let cl_ptr_opt: Option<ir::Value> = if cont_is_native {
                        let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
                        let cont_fref = jmod.declare_func_in_func(cont_fid, b.func);
                        let acl_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                        let cl_fid_v = b.ins().iconst(types::I32, cont_sid as i64);
                        let n_caps_v = b
                            .ins()
                            .iconst(types::I32, (continuation.captured.len() + 1) as i64);
                        // fz-ul4.27.22.6: halt_kind=0 (Tagged). Cont closures
                        // are never handed to fz_spawn_entry — the field is
                        // a fz_spawn_entry-only consumer.
                        let zero_hk = b.ins().iconst(types::I32, 0);
                        let cl_inst = b.ins().call(acl_fref, &[cl_fid_v, n_caps_v, zero_hk]);
                        let cl_ptr = b.inst_results(cl_inst)[0];
                        let cont_code_addr = b.ins().func_addr(types::I64, cont_fref);
                        b.ins()
                            .store(MemFlags::trusted(), cont_code_addr, cl_ptr, HEADER_SIZE);
                        // outer_cont at +24. fz-cps.1.8 — cont fns
                        // forward their own outer_cont (loaded from
                        // self+24); non-cont native fns use cont_param;
                        // uniform fns load from frame_ptr+16.
                        let my_outer_cont = if is_cont_fn {
                            let self_val = cont_param.expect("cont fn binds self via cont_param");
                            b.ins().load(
                                types::I64,
                                MemFlags::trusted(),
                                self_val,
                                HEADER_SIZE + SLOT_BYTES,
                            )
                        } else {
                            match cont_param {
                                Some(c) => c,
                                None => {
                                    let from_slot = b.ins().load(
                                        types::I64,
                                        MemFlags::trusted(),
                                        frame_ptr.expect(
                                            "uniform caller building cont closure \
                                         must have frame_ptr",
                                        ),
                                        HEADER_SIZE,
                                    );
                                    let zero = b.ins().iconst(types::I64, 0);
                                    let is_null = b.ins().icmp(IntCC::Equal, from_slot, zero);
                                    let alloc_blk = b.create_block();
                                    let join_blk = b.create_block();
                                    b.append_block_param(join_blk, types::I64);
                                    b.ins().brif(
                                        is_null,
                                        alloc_blk,
                                        &[][..],
                                        join_blk,
                                        &[BlockArg::Value(from_slot)],
                                    );
                                    b.switch_to_block(alloc_blk);
                                    b.seal_block(alloc_blk);
                                    let acl_fref2 =
                                        jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                                    let dummy_fid = b.ins().iconst(types::I32, 0);
                                    let n_caps0 = b.ins().iconst(types::I32, 0);
                                    let zero_hk = b.ins().iconst(types::I32, 0);
                                    let halt_alloc =
                                        b.ins().call(acl_fref2, &[dummy_fid, n_caps0, zero_hk]);
                                    let halt_cl = b.inst_results(halt_alloc)[0];
                                    // fz-ul4.27.22.3 — halt-cont body matches
                                    // the user-cont's return_repr (the user's
                                    // cont's Term::Return calls into this
                                    // halt-cont's body).
                                    let hc_repr = return_reprs[cont_sid as usize];
                                    let hcb_fref = jmod.declare_func_in_func(
                                        halt_cont_body_id_for(runtime, hc_repr),
                                        b.func,
                                    );
                                    let hcb_addr = b.ins().func_addr(types::I64, hcb_fref);
                                    b.ins().store(
                                        MemFlags::trusted(),
                                        hcb_addr,
                                        halt_cl,
                                        HEADER_SIZE,
                                    );
                                    b.ins().jump(join_blk, &[BlockArg::Value(halt_cl)]);
                                    b.switch_to_block(join_blk);
                                    b.seal_block(join_blk);
                                    b.block_params(join_blk)[0]
                                }
                            }
                        };
                        b.ins().store(
                            MemFlags::trusted(),
                            my_outer_cont,
                            cl_ptr,
                            HEADER_SIZE + SLOT_BYTES,
                        );
                        // User captures at +32+8i. fz-ul4.27.21.2 — stored
                        // in the cont's per-capture repr (param_reprs[cont_sid]
                        // [i+1]; [0] is the result slot). Cont entry harness
                        // loads with the matching cl_type — no tag/untag
                        // round-trip when the capture is narrow.
                        let cont_param_reprs = &param_reprs[cont_sid as usize];
                        for (i, cv) in continuation.captured.iter().enumerate() {
                            let from = var_repr(cv.0, &raw_int_vars, &raw_f64_vars);
                            let to = cont_param_reprs[i + 1];
                            let v = coerce_to(&mut b, jmod, runtime, cap_vals[i], from, to);
                            let off = HEADER_SIZE + SLOT_BYTES * 2 + (i as i32) * SLOT_BYTES;
                            b.ins().store(MemFlags::trusted(), v, cl_ptr, off);
                        }
                        let _ = cont_fref;
                        Some(cl_ptr)
                    } else {
                        None
                    };
                    // cont arg passed to the callee: cl_ptr for native cont,
                    // else cont_param fallback (uniform-cont path). fz-cps.1.11:
                    // when the cont-fn is uniform (rare; really only main's
                    // halt-style cont after the parking-reachable lift) and
                    // we have no cont_param, build a halt-cont closure inline
                    // so the callee's Term::Return doesn't load through null+16.
                    // synth_halt_cont tracks the latter: the callee chains
                    // all the way into the halt-cont body, so the caller
                    // must NOT execute its uniform-cont write-back after
                    // the call (that would double-halt with the wrong value).
                    let mut synth_halt_cont = false;
                    let cont_arg = if let Some(cl_ptr) = cl_ptr_opt {
                        cl_ptr
                    } else {
                        match cont_param {
                            Some(c) => c,
                            None => {
                                synth_halt_cont = true;
                                // fz-ul4.27.22.3 — synth halt-cont's body
                                // matches the callee's return_repr.
                                let fref =
                                    jmod.declare_func_in_func(runtime.get_halt_cont_id, b.func);
                                let hcb_fref = jmod.declare_func_in_func(
                                    halt_cont_body_id_for(runtime, callee_ret_repr),
                                    b.func,
                                );
                                let hcb_addr = b.ins().func_addr(types::I64, hcb_fref);
                                let kind_v = b
                                    .ins()
                                    .iconst(types::I32, callee_ret_repr.halt_kind() as i64);
                                let inst = b.ins().call(fref, &[hcb_addr, kind_v]);
                                b.inst_results(inst)[0]
                            }
                        }
                    };
                    native_args.push(cont_arg);

                    if (cl_ptr_opt.is_some() || synth_halt_cont) && is_native {
                        // fz-cps.1.8 — native→native chained call uses
                        // return_call (TCO via Tail-CC). The callee's
                        // Term::Return tail-chains into the cont closure
                        // we built above. Matches §8.2 target clif.
                        let _ = (return_reprs[this_spec_id as usize], callee_ret_repr);
                        b.ins().return_call(callee_fref, &native_args);
                    } else if cl_ptr_opt.is_some() || synth_halt_cont {
                        // Uniform caller → native callee (chained). Can't
                        // return_call across CC; synchronous call then
                        // return the chain-final value (halt_value already
                        // set by the time we get here).
                        let call_inst = b.ins().call(callee_fref, &native_args);
                        let result = b.inst_results(call_inst)[0];
                        let _ = (return_reprs[this_spec_id as usize], callee_ret_repr, result);
                        let zero = b.ins().iconst(types::I64, 0);
                        b.ins().return_(&[zero]);
                    } else {
                        let call_inst = b.ins().call(callee_fref, &native_args);
                        let result = b.inst_results(call_inst)[0];
                        let cont_schema = &schemas[cont_sid as usize];
                        let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
                        let sid = b.ins().iconst(types::I32, cont_sid as i64);
                        let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
                        let alloc_call = b.ins().call(alloc_fref, &[sid, sz]);
                        let cf = b.inst_results(alloc_call)[0];
                        let my_cont = b.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            frame_ptr.expect(
                                "Term::Call uniform-cont write-back reached from \
                                 native-fn body — natively_callable invariant violated",
                            ),
                            HEADER_SIZE,
                        );
                        b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
                        // fz-ul4.29.12.1: result + captures are written
                        // into the cont's typed entry slots. `store_args
                        // _into_callee_frame` reads `cont_schema` per
                        // slot kind and unboxes from Tagged as needed.
                        let result_tagged = coerce_to(
                            &mut b,
                            jmod,
                            runtime,
                            result,
                            callee_ret_repr,
                            ArgRepr::Tagged,
                        );
                        let mut payload: Vec<ir::Value> =
                            Vec::with_capacity(continuation.captured.len() + 1);
                        payload.push(result_tagged);
                        for (cv, val) in continuation.captured.iter().zip(cap_vals.iter()) {
                            let from = var_repr(cv.0, &raw_int_vars, &raw_f64_vars);
                            payload.push(coerce_to(
                                &mut b,
                                jmod,
                                runtime,
                                *val,
                                from,
                                ArgRepr::Tagged,
                            ));
                        }
                        store_args_into_callee_frame(&mut b, cont_schema, cf, &payload, 1);
                        b.ins().return_(&[cf]);
                    }
                } else {
                    let arg_vals: Vec<ir::Value> = args
                        .iter()
                        .map(|v| *var_map.get(&v.0).expect("unbound call arg"))
                        .collect();
                    emit_call(
                        &mut b,
                        jmod,
                        runtime,
                        schemas,
                        frame_ptr,
                        callee_sid,
                        &arg_vals,
                        Some((cont_sid, &cap_vals)),
                    );
                }
            }
            Term::TailCall { callee, args } => {
                let callee_sid = resolve_callee_sid(*callee, args);
                if callee_is_native(callee.0) {
                    // fz-ul4.27.6.2.3 / .27.13 — TailCall to a native callee.
                    // Coerce each arg from its current var repr to the
                    // callee's param_repr. The natively_callable fixed point
                    // guarantees callee's return_repr matches mine, so
                    // return_call is ABI-compatible without further coerce.
                    let callee_param_reprs = &param_reprs[callee_sid as usize];
                    let callee_ret_repr = return_reprs[callee_sid as usize];
                    let callee_fid = *fn_ids.get(&callee_sid).expect("callee fn_id missing");
                    let callee_fref = jmod.declare_func_in_func(callee_fid, b.func);
                    let mut native_args: Vec<ir::Value> = Vec::with_capacity(args.len() + 1);
                    for (i, av) in args.iter().enumerate() {
                        let raw_val = *var_map.get(&av.0).expect("unbound tailcall arg");
                        let from = var_repr(av.0, &raw_int_vars, &raw_f64_vars);
                        let to = callee_param_reprs[i];
                        native_args.push(coerce_to(&mut b, jmod, runtime, raw_val, from, to));
                    }
                    // fz-ul4.27.19: forward host_ctx only when the callee
                    // needs it. The transitive analysis guarantees this fn
                    // has host_ctx if its callee does.
                    if fns_needing_host_ctx.contains(callee) {
                        native_args.push(
                            host_ctx.expect(
                                "TailCall callee needs host_ctx; this fn must also have it",
                            ),
                        );
                    }
                    // fz-cps.1.8 — TailCall to a closure-target fn: insert
                    // static singleton as `self` before cont. Mirror of
                    // the Term::Call path; same zero-cap invariant lets
                    // any singleton serve as self (body ignores it).
                    if closure_n_captures.contains_key(callee) {
                        let fref = jmod.declare_func_in_func(runtime.get_static_closure_id, b.func);
                        let sid_v = b.ins().iconst(types::I32, callee.0 as i64);
                        let inst = b.ins().call(fref, &[sid_v]);
                        native_args.push(b.inst_results(inst)[0]);
                    }
                    // fz-cps.1.a: trailing cont arg per §2.1. fz-cps.1.11:
                    // build halt-cont closure inline when uniform-tier
                    // caller (cont_param=None) tail-calls native callee,
                    // so the callee's Term::Return doesn't deref null.
                    // fz-cps.1.12: cont fns forward outer_cont (loaded
                    // from self+24); cont_param for cont fns is self.
                    let mut synth_halt_cont = false;
                    let tail_cont_arg = if is_cont_fn {
                        let self_val = cont_param.expect("cont fn binds self via cont_param");
                        b.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            self_val,
                            HEADER_SIZE + SLOT_BYTES,
                        )
                    } else {
                        match cont_param {
                            Some(c) => c,
                            None => {
                                synth_halt_cont = true;
                                // fz-ul4.27.22.3 — synth halt-cont's body
                                // matches callee's return_repr.
                                let fref =
                                    jmod.declare_func_in_func(runtime.get_halt_cont_id, b.func);
                                let hcb_fref = jmod.declare_func_in_func(
                                    halt_cont_body_id_for(runtime, callee_ret_repr),
                                    b.func,
                                );
                                let hcb_addr = b.ins().func_addr(types::I64, hcb_fref);
                                let kind_v = b
                                    .ins()
                                    .iconst(types::I32, callee_ret_repr.halt_kind() as i64);
                                let inst = b.ins().call(fref, &[hcb_addr, kind_v]);
                                b.inst_results(inst)[0]
                            }
                        }
                    };
                    native_args.push(tail_cont_arg);
                    if is_native {
                        // Native-to-native TailCall: use return_call so
                        // recursive tail calls reuse the same stack frame
                        // (TCO). Without this, count_100k blows the stack.
                        b.ins().return_call(callee_fref, &native_args);
                    } else if synth_halt_cont {
                        // fz-cps.1.11 — uniform caller + native callee
                        // with synthesized halt-cont: callee's chain runs
                        // all the way through halt_cont_body. Caller must
                        // NOT do post-call uniform write-back (would
                        // double-halt with the wrong value).
                        let _ = b.ins().call(callee_fref, &native_args);
                        let zero = b.ins().iconst(types::I64, 0);
                        b.ins().return_(&[zero]);
                    } else {
                        // Uniform caller: synchronous call, then write result
                        // into MY cont's slot 1 (FzValue — cont result param
                        // stays `any` in the typer). Coerce result to Tagged.
                        let call_inst = b.ins().call(callee_fref, &native_args);
                        let result = b.inst_results(call_inst)[0];
                        let result_tagged = coerce_to(
                            &mut b,
                            jmod,
                            runtime,
                            result,
                            callee_ret_repr,
                            ArgRepr::Tagged,
                        );
                        let my_cont = b.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            frame_ptr.expect(
                                "Term::TailCall uniform-caller writeback reached from \
                                 native-fn body — natively_callable invariant violated",
                            ),
                            HEADER_SIZE,
                        );
                        // Halt path: my_cont may be null on the top frame.
                        let zero = b.ins().iconst(types::I64, 0);
                        let is_null = b.ins().icmp(IntCC::Equal, my_cont, zero);
                        let halt_blk = b.create_block();
                        let invoke_blk = b.create_block();
                        let no_args: Vec<BlockArg> = Vec::new();
                        b.ins()
                            .brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);
                        b.switch_to_block(halt_blk);
                        b.seal_block(halt_blk);
                        let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                        b.ins().call(
                            halt_fref,
                            &[
                                host_ctx.expect(
                                    "TailCall uniform-caller halt branch needs \
                                 host_ctx — uniform fns always have it",
                                ),
                                result_tagged,
                            ],
                        );
                        let null = b.ins().iconst(types::I64, 0);
                        b.ins().return_(&[null]);
                        b.switch_to_block(invoke_blk);
                        b.seal_block(invoke_blk);
                        b.ins().store(
                            MemFlags::trusted(),
                            result_tagged,
                            my_cont,
                            HEADER_SIZE + SLOT_BYTES,
                        );
                        b.ins().return_(&[my_cont]);
                    }
                } else {
                    let arg_vals: Vec<ir::Value> = args
                        .iter()
                        .map(|v| *var_map.get(&v.0).expect("unbound tailcall arg"))
                        .collect();
                    emit_tail_call(
                        &mut b,
                        jmod,
                        runtime,
                        schemas,
                        this_spec_id,
                        frame_ptr,
                        callee_sid,
                        &arg_vals,
                    );
                }
            }
            Term::CallClosure {
                closure,
                args,
                continuation,
            } => {
                // fz-ul4.29.5: load stub_fp from closure_ptr+16, build a
                // cont frame, then call_indirect through stub_fp. The stub
                // adapts the call into the callee's entry-frame layout.
                let cl_val = *var_map
                    .get(&closure.0)
                    .expect("unbound callclosure closure");
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound callclosure arg"))
                    .collect();
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound captured val"))
                    .collect();
                // fz-cps.1.2: build cont CLOSURE (not cont frame) per
                // §2.2. The closure-target callee's body indirect-calls
                // through cont+16 on Return, so the cont must be a
                // valid heap closure (code_ptr@+16, outer_cont@+24,
                // user captures from +32).
                let cont_sid = resolve_cont_sid(blk, continuation);
                let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
                let cont_fref = jmod.declare_func_in_func(cont_fid, b.func);
                let acl_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                let cl_fid_v = b.ins().iconst(types::I32, cont_sid as i64);
                let n_caps_v = b
                    .ins()
                    .iconst(types::I32, (continuation.captured.len() + 1) as i64);
                let zero_hk = b.ins().iconst(types::I32, 0);
                let cl_inst = b.ins().call(acl_fref, &[cl_fid_v, n_caps_v, zero_hk]);
                let cf = b.inst_results(cl_inst)[0];
                let cont_code_addr = b.ins().func_addr(types::I64, cont_fref);
                b.ins()
                    .store(MemFlags::trusted(), cont_code_addr, cf, HEADER_SIZE);
                // outer_cont at +24. fz-cps.1.8 — cont fns forward their
                // own outer_cont; non-cont native use cont_param; uniform
                // loads frame_ptr+16 with halt-cont fallback.
                let my_outer_cont = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        self_val,
                        HEADER_SIZE + SLOT_BYTES,
                    )
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => {
                            let from_slot = b.ins().load(
                                types::I64,
                                MemFlags::trusted(),
                                frame_ptr.expect("uniform CallClosure must have frame_ptr"),
                                HEADER_SIZE,
                            );
                            let zero = b.ins().iconst(types::I64, 0);
                            let is_null = b.ins().icmp(IntCC::Equal, from_slot, zero);
                            let alloc_blk = b.create_block();
                            let join_blk = b.create_block();
                            b.append_block_param(join_blk, types::I64);
                            b.ins().brif(
                                is_null,
                                alloc_blk,
                                &[][..],
                                join_blk,
                                &[BlockArg::Value(from_slot)],
                            );
                            b.switch_to_block(alloc_blk);
                            b.seal_block(alloc_blk);
                            let dummy_fid = b.ins().iconst(types::I32, 0);
                            let n_caps0 = b.ins().iconst(types::I32, 0);
                            let zero_hk2 = b.ins().iconst(types::I32, 0);
                            let halt_alloc =
                                b.ins().call(acl_fref, &[dummy_fid, n_caps0, zero_hk2]);
                            let halt_cl = b.inst_results(halt_alloc)[0];
                            // fz-ul4.27.22.3 — outer halt-cont body matches the
                            // user-cont's return_repr.
                            let hc_repr = return_reprs[cont_sid as usize];
                            let hcb_fref = jmod.declare_func_in_func(
                                halt_cont_body_id_for(runtime, hc_repr),
                                b.func,
                            );
                            let hcb_addr = b.ins().func_addr(types::I64, hcb_fref);
                            b.ins()
                                .store(MemFlags::trusted(), hcb_addr, halt_cl, HEADER_SIZE);
                            b.ins().jump(join_blk, &[BlockArg::Value(halt_cl)]);
                            b.switch_to_block(join_blk);
                            b.seal_block(join_blk);
                            b.block_params(join_blk)[0]
                        }
                    }
                };
                b.ins().store(
                    MemFlags::trusted(),
                    my_outer_cont,
                    cf,
                    HEADER_SIZE + SLOT_BYTES,
                );
                // User captures at +32+8*i. fz-ul4.27.21.2 — stored in
                // the cont's per-capture repr (param_reprs[cont_sid][i+1];
                // [0] is the result slot, kept Tagged by tagged_slot0_cont_
                // specs / uniform_cont_reachable_specs).
                let cont_param_reprs = &param_reprs[cont_sid as usize];
                for (i, cv) in continuation.captured.iter().enumerate() {
                    let from = var_repr(cv.0, &raw_int_vars, &raw_f64_vars);
                    let to = cont_param_reprs[i + 1];
                    let v = coerce_to(&mut b, jmod, runtime, cap_vals[i], from, to);
                    let off = HEADER_SIZE + SLOT_BYTES * 2 + (i as i32) * SLOT_BYTES;
                    b.ins().store(MemFlags::trusted(), v, cf, off);
                }
                let _ = cont_param; // captures wired into cont closure.
                let _ = continuation; // remainder of capture/cont metadata done.
                // fz-cps.1.8 — load body's func_addr from cl+16 and Tail-CC
                // indirect-call with closure-target sig `(args..., self,
                // cont) -> i64 tail`. All-Tagged params. Native callers
                // use return_call_indirect (TCO); uniform callers use
                // call_indirect Tail (cross-CC) and return result.
                let body_fp = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), cl_val, HEADER_SIZE);
                let mut sig = Signature::new(CallConv::Tail);
                for _ in &arg_vals {
                    sig.params.push(AbiParam::new(types::I64));
                }
                sig.params.push(AbiParam::new(types::I64)); // self
                sig.params.push(AbiParam::new(types::I64)); // cont
                sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(sig);
                let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                for (i, v) in arg_vals.iter().enumerate() {
                    let from = var_repr(args[i].0, &raw_int_vars, &raw_f64_vars);
                    indirect_args.push(coerce_to(&mut b, jmod, runtime, *v, from, ArgRepr::Tagged));
                }
                indirect_args.push(cl_val);
                indirect_args.push(cf);
                let _ = host_ctx; // no host_ctx in closure-target sig
                if is_native {
                    b.ins()
                        .return_call_indirect(sig_ref, body_fp, &indirect_args);
                } else {
                    let call_inst = b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                    let result = b.inst_results(call_inst)[0];
                    b.ins().return_(&[result]);
                }
            }
            Term::TailCallClosure { closure, args } => {
                // fz-cps.1.8 — Tail-CC indirect-call through cl+16 with
                // the caller's own cont (TCO via return_call_indirect).
                // Closure-target sig `(args..., self, cont) -> i64 tail`.
                // For cont fns, the forwarded cont is outer_cont from
                // self+24. For non-cont native fns, cont_param is the
                // cont SSA. Uniform callers load from frame_ptr+16.
                //
                // fz-ul4.27.22.11 — closure_lit fast path. When the closure
                // Var's per-spec Descr is a single closure_lit(F, K), resolve
                // F's narrow body spec at key [K..., arg_descrs...] and emit
                // a direct return_call. Bypasses the cl+16 indirect load and
                // uses the body's narrow ABI directly. Falls back to the
                // indirect path on union-of-lits, plain arrows, and
                // unresolved keys.
                let cl_val = *var_map
                    .get(&closure.0)
                    .expect("unbound tailcallclosure closure");
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound tailcallclosure arg"))
                    .collect();
                let my_cont = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        self_val,
                        HEADER_SIZE + SLOT_BYTES,
                    )
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => b.ins().load(
                            types::I64,
                            MemFlags::trusted(),
                            frame_ptr.expect("uniform TailCallClosure must have frame_ptr"),
                            HEADER_SIZE,
                        ),
                    }
                };

                // fz-ul4.27.22.11 — try singleton resolution.
                let lit_resolved: Option<(u32, FuncId, usize)> = (|| {
                    let cv_descr = fn_types.vars.get(closure)?;
                    let lit = cv_descr.as_closure_lit()?;
                    let body_fn_id = lit.fn_id;
                    let body_fn = module.fn_by_id(body_fn_id);
                    let body_n_params = body_fn.block(body_fn.entry).params.len();
                    // Build full body key: [captures..., arg_descrs...].
                    let mut full_key: Vec<crate::types::Descr> = lit.captures.clone();
                    for av in args.iter() {
                        let d = fn_types
                            .vars
                            .get(av)
                            .cloned()
                            .unwrap_or_else(crate::types::Descr::any);
                        full_key.push(d);
                    }
                    while full_key.len() < body_n_params {
                        full_key.push(crate::types::Descr::any());
                    }
                    full_key.truncate(body_n_params);
                    let body_sid = spec_registry.resolve(body_fn_id, &full_key)?.0;
                    let body_fid = *fn_ids.get(&body_sid)?;
                    let n_caps = closure_n_captures.get(&body_fn_id).copied().unwrap_or(0);
                    Some((body_sid, body_fid, n_caps))
                })();

                if let Some((body_sid, body_fid, n_caps)) = lit_resolved {
                    // Direct dispatch: build sig from body's narrow
                    // param_reprs; emit return_call passing cl_val as self
                    // and my_cont as cont.
                    let body_param_reprs = &param_reprs[body_sid as usize];
                    let mut sig = Signature::new(CallConv::Tail);
                    // Closure-target sig: only arg slots [n_caps..] go on
                    // the wire; capture slots live inside the closure heap
                    // object and the body's entry harness loads them.
                    for r in &body_param_reprs[n_caps..] {
                        sig.params.push(AbiParam::new(r.cl_type()));
                    }
                    sig.params.push(AbiParam::new(types::I64)); // self
                    sig.params.push(AbiParam::new(types::I64)); // cont
                    sig.returns.push(AbiParam::new(types::I64));
                    let body_fref = jmod.declare_func_in_func(body_fid, b.func);
                    let mut direct_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                    for (i, v) in arg_vals.iter().enumerate() {
                        let from = var_repr(args[i].0, &raw_int_vars, &raw_f64_vars);
                        let to = body_param_reprs
                            .get(n_caps + i)
                            .copied()
                            .unwrap_or(ArgRepr::Tagged);
                        direct_args.push(coerce_to(&mut b, jmod, runtime, *v, from, to));
                    }
                    direct_args.push(cl_val);
                    direct_args.push(my_cont);
                    let _ = host_ctx;
                    let _ = sig; // body_fref carries the signature implicitly.
                    if is_native {
                        b.ins().return_call(body_fref, &direct_args);
                    } else {
                        let call_inst = b.ins().call(body_fref, &direct_args);
                        let result = b.inst_results(call_inst)[0];
                        b.ins().return_(&[result]);
                    }
                } else {
                    // Existing indirect path (cl+16) for unresolved /
                    // union-of-lits / plain-arrow closures.
                    let body_fp =
                        b.ins()
                            .load(types::I64, MemFlags::trusted(), cl_val, HEADER_SIZE);
                    let mut sig = Signature::new(CallConv::Tail);
                    for _ in &arg_vals {
                        sig.params.push(AbiParam::new(types::I64));
                    }
                    sig.params.push(AbiParam::new(types::I64)); // self
                    sig.params.push(AbiParam::new(types::I64)); // cont
                    sig.returns.push(AbiParam::new(types::I64));
                    let sig_ref = b.func.import_signature(sig);
                    let mut indirect_args: Vec<ir::Value> = Vec::with_capacity(arg_vals.len() + 2);
                    for (i, v) in arg_vals.iter().enumerate() {
                        let from = var_repr(args[i].0, &raw_int_vars, &raw_f64_vars);
                        indirect_args.push(coerce_to(
                            &mut b,
                            jmod,
                            runtime,
                            *v,
                            from,
                            ArgRepr::Tagged,
                        ));
                    }
                    indirect_args.push(cl_val);
                    indirect_args.push(my_cont);
                    let _ = host_ctx;
                    if is_native {
                        b.ins()
                            .return_call_indirect(sig_ref, body_fp, &indirect_args);
                    } else {
                        let call_inst = b.ins().call_indirect(sig_ref, body_fp, &indirect_args);
                        let result = b.inst_results(call_inst)[0];
                        b.ins().return_(&[result]);
                    }
                }
            }
            Term::Receive { continuation } => {
                // fz-cps.1.2 Receive cutover per docs/cps-in-clif.md §4.
                // Build the cont closure (kind=Closure, code_ptr at +16,
                // synthetic outer_cont at +24, user captures from +32),
                // hand it to fz_receive_park which stashes the closure
                // in Process::parked_cont and returns YIELD sentinel.
                // On message arrival the scheduler will dispatch the
                // parked cont via a Cranelift thunk (fz-cps.1.2 follow-on).
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound receive cont capture"))
                    .collect();
                let cont_sid = resolve_cont_sid(blk, continuation);
                let cont_fid = *fn_ids.get(&cont_sid).expect("cont fn_id missing");
                let cont_fref = jmod.declare_func_in_func(cont_fid, b.func);
                let cont_param_reprs = &param_reprs[cont_sid as usize];

                let acl_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
                let cl_fid_v = b.ins().iconst(types::I32, cont_sid as i64);
                // +1 slot for synthetic outer_cont at +24; user captures
                // start at +32.
                let n_caps_v = b
                    .ins()
                    .iconst(types::I32, (continuation.captured.len() + 1) as i64);
                let zero_hk = b.ins().iconst(types::I32, 0);
                let cl_inst = b.ins().call(acl_fref, &[cl_fid_v, n_caps_v, zero_hk]);
                let cl_ptr = b.inst_results(cl_inst)[0];
                let cont_code_addr = b.ins().func_addr(types::I64, cont_fref);
                b.ins()
                    .store(MemFlags::trusted(), cont_code_addr, cl_ptr, HEADER_SIZE);
                // outer_cont at +24 (synthetic). Native caller has
                // cont_param; uniform caller loads frame_ptr+16 with
                // null-fallback to a halt-cont closure inline.
                // fz-cps.1.8 — cont fns load outer_cont from self+24.
                let my_outer_cont = if is_cont_fn {
                    let self_val = cont_param.expect("cont fn binds self via cont_param");
                    b.ins().load(
                        types::I64,
                        MemFlags::trusted(),
                        self_val,
                        HEADER_SIZE + SLOT_BYTES,
                    )
                } else {
                    match cont_param {
                        Some(c) => c,
                        None => {
                            let from_slot = b.ins().load(
                                types::I64,
                                MemFlags::trusted(),
                                frame_ptr.expect("uniform Receive caller must have frame_ptr"),
                                HEADER_SIZE,
                            );
                            let zero = b.ins().iconst(types::I64, 0);
                            let is_null = b.ins().icmp(IntCC::Equal, from_slot, zero);
                            let alloc_blk = b.create_block();
                            let join_blk = b.create_block();
                            b.append_block_param(join_blk, types::I64);
                            b.ins().brif(
                                is_null,
                                alloc_blk,
                                &[][..],
                                join_blk,
                                &[BlockArg::Value(from_slot)],
                            );
                            b.switch_to_block(alloc_blk);
                            b.seal_block(alloc_blk);
                            let dummy_fid = b.ins().iconst(types::I32, 0);
                            let n_caps0 = b.ins().iconst(types::I32, 0);
                            let zero_hk2 = b.ins().iconst(types::I32, 0);
                            let halt_alloc =
                                b.ins().call(acl_fref, &[dummy_fid, n_caps0, zero_hk2]);
                            let halt_cl = b.inst_results(halt_alloc)[0];
                            // fz-ul4.27.22.3 — outer halt-cont body matches the
                            // user-cont's return_repr.
                            let hc_repr = return_reprs[cont_sid as usize];
                            let hcb_fref = jmod.declare_func_in_func(
                                halt_cont_body_id_for(runtime, hc_repr),
                                b.func,
                            );
                            let hcb_addr = b.ins().func_addr(types::I64, hcb_fref);
                            b.ins()
                                .store(MemFlags::trusted(), hcb_addr, halt_cl, HEADER_SIZE);
                            b.ins().jump(join_blk, &[BlockArg::Value(halt_cl)]);
                            b.switch_to_block(join_blk);
                            b.seal_block(join_blk);
                            b.block_params(join_blk)[0]
                        }
                    }
                };
                b.ins().store(
                    MemFlags::trusted(),
                    my_outer_cont,
                    cl_ptr,
                    HEADER_SIZE + SLOT_BYTES,
                );
                // User captures at +32+8i. fz-ul4.27.21.2 — stored in the
                // cont's per-capture repr. Receive's cont keeps slot 0 as
                // Tagged (msg arrives Tagged from the mailbox), but captures
                // can be typed.
                for (i, cv) in continuation.captured.iter().enumerate() {
                    let from = var_repr(cv.0, &raw_int_vars, &raw_f64_vars);
                    let to = cont_param_reprs[i + 1];
                    let v = coerce_to(&mut b, jmod, runtime, cap_vals[i], from, to);
                    let off = HEADER_SIZE + SLOT_BYTES * 2 + (i as i32) * SLOT_BYTES;
                    b.ins().store(MemFlags::trusted(), v, cl_ptr, off);
                }

                // fz_receive_park(cl_ptr) — stash + yield.
                let park_fref = jmod.declare_func_in_func(runtime.receive_park_id, b.func);
                let park_inst = b.ins().call(park_fref, &[cl_ptr]);
                let yield_sentinel = b.inst_results(park_inst)[0];
                if is_native {
                    // Native body returns i64 (canonical); the yield
                    // sentinel propagates back to the scheduler.
                    b.ins().return_(&[yield_sentinel]);
                } else {
                    // Uniform body returns next_frame ptr (here, YIELD
                    // sentinel — trampoline parks the task).
                    b.ins().return_(&[yield_sentinel]);
                }
            }
        }
    }

    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.seal_block(cl_blk);
        }
    }
    b.finalize();
    // fz-ul4.32.1 — publish Value → Descr for the dump path. Only the
    // values bound to fz Vars are recorded; pure Cranelift intermediates
    // (iconst, ishl_imm, ...) stay unannotated. Pure overhead when
    // IR_TEXT_RECORD is disabled is the `with` + None-check.
    VALUE_DESCR_RECORD.with(|c| {
        if let Some(map) = c.borrow_mut().as_mut() {
            map.clear();
            for (var_id, value) in &var_map {
                if let Some(d) = fn_types.vars.get(&crate::fz_ir::Var(*var_id)) {
                    map.insert(value.as_u32(), d.clone());
                }
            }
        }
    });
    Ok(())
}

/// Term::Return: load my cont_ptr from frame[16]. If null, halt.
/// Otherwise write `val` to cont_frame[24] (continuation's "result" slot —
/// always entry param 0) and return cont_ptr.
///
/// fz-ul4.27.16: `frame_ptr` is `Option` because native fns don't have
/// a frame; the natively_callable invariant guarantees this helper is
/// never reached from a native fn body. Unwrapping with `.expect()`
/// turns any future invariant break into a loud panic at codegen time
/// rather than a silent load-from-zero.
fn emit_return<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    frame_ptr: Option<ir::Value>,
    host_ctx: ir::Value,
    val: ir::Value,
) {
    let frame_ptr = frame_ptr
        .expect("emit_return reached from native-fn body — natively_callable invariant violated");
    let cont_ptr = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
    // fz-ul4.27.17: one `iconst.i64 0` materialized in the entry block
    // serves both the null-compare and the halt-branch return sentinel.
    // SSA dominance lets the halt block reuse it; previously we emitted
    // a duplicate iconst inside the halt block.
    let zero = b.ins().iconst(types::I64, 0);
    let is_null = b.ins().icmp(IntCC::Equal, cont_ptr, zero);

    let halt_blk = b.create_block();
    let invoke_blk = b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins()
        .brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);

    // halt: fz_halt(host_ctx, val); return null (reusing `zero`).
    b.switch_to_block(halt_blk);
    b.seal_block(halt_blk);
    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
    b.ins().call(halt_fref, &[host_ctx, val]);
    b.ins().return_(&[zero]);

    // invoke: write val to cont[24], return cont_ptr.
    b.switch_to_block(invoke_blk);
    b.seal_block(invoke_blk);
    let result_off = HEADER_SIZE + SLOT_BYTES;
    b.ins()
        .store(MemFlags::trusted(), val, cont_ptr, result_off);
    b.ins().return_(&[cont_ptr]);
}

/// fz-ul4.27.18 — specialized emit_return for fns whose cont_ptr is
/// statically known to be null at runtime (i.e. fns that are never a
/// cont target anywhere in the module — they can only be invoked as
/// the trampoline entry, which writes null into slot 0). Skip the
/// `load v0+16; icmp eq 0; brif` dispatch and the dead invoke-branch
/// entirely; just `call fz_halt(host_ctx, val); return null`.
///
/// Takes no `frame_ptr` because none is read.
fn emit_halt_and_return_null<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    host_ctx: ir::Value,
    val: ir::Value,
) {
    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
    b.ins().call(halt_fref, &[host_ctx, val]);
    let null = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[null]);
}

/// Term::Call: allocate continuation frame + callee frame. Continuation
/// frame = [my_cont_ptr, result_placeholder, ...captured]. Callee frame =
/// [cont_frame_ptr, ...args]. Return callee frame ptr.
fn emit_call<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[ir::Value],
    cont: Option<(u32, &[ir::Value])>,
) {
    let frame_ptr = frame_ptr
        .expect("emit_call reached from native-fn body — natively_callable invariant violated");
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

    // Read my cont_ptr from current frame[16] — this becomes the cont frame's cont_ptr.
    let my_cont = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

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
    b.ins().store(
        MemFlags::trusted(),
        cont_frame_val,
        callee_frame,
        HEADER_SIZE,
    );
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
    frame_ptr: Option<ir::Value>,
    cont_fn_id: u32,
    captured: &[ir::Value],
) {
    let frame_ptr = frame_ptr
        .expect("emit_receive reached from native-fn body — natively_callable invariant violated");
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

    // Read my cont_ptr from current frame[16] (becomes the cont frame's
    // cont_ptr — same shape as Term::Call).
    let my_cont = b
        .ins()
        .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

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
    frame_ptr: Option<ir::Value>,
    callee_id: u32,
    args: &[ir::Value],
) {
    let frame_ptr = frame_ptr.expect(
        "emit_tail_call reached from native-fn body — natively_callable invariant violated",
    );
    let callee_schema = &schemas[callee_id as usize];

    if self_id == callee_id {
        // Same schema: overwrite slots 1..N+1 with new args. Slot 0 (cont) stays.
        store_args_into_callee_frame(b, callee_schema, frame_ptr, args, 1);
        b.ins().return_(&[frame_ptr]);
    } else {
        // Different schema: alloc fresh, copy cont_ptr, write args.
        let my_cont = b
            .ins()
            .load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
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

// fz-ul4.29.5: emit_call_closure / emit_tail_call_closure deleted.
// Term::CallClosure / TailCallClosure lower directly inline (load stub_fp
// from closure heap object, call_indirect through it). The closure cluster
// helpers (fz_closure_begin / push / finalize / arg / invoke / tail) are
// gone from the runtime; their work happens at compile time in stubs.

/// fz-ul4.29.5: compile a closure stub. The stub is the adapter that
/// the closure heap object's `stub_fp` points at. When CallClosure (or
/// fz_spawn for the initial frame) invokes it, the stub:
///   1. Allocates the callee's entry frame (sized to the narrow spec).
///   2. Writes cont_ptr into slot 0 (offset 16).
///   3. Reads each capture as tagged FzValue from `closure_ptr + 24 + 8*k`
///      and stores it kind-aware into the callee frame's capture entry slot.
///   4. Writes each call arg into its entry slot, kind-aware.
///   5. Returns the callee frame for the trampoline.
//
// Closure-target bodies stay uniform-ABI in v1 (parking.rs:113 excludes
// `used_as_closure_target` fns from `natively_callable`). The native-
// callee branch is gated on .29.8 lifting that exclusion; for now we
// always go through the uniform frame-alloc path.

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
fn descrs_disjoint(
    fn_types: &crate::ir_typer::FnTypes,
    a: crate::fz_ir::Var,
    b: crate::fz_ir::Var,
) -> bool {
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
    fn is_raw_f64(&self) -> bool {
        matches!(self, LowerOut::RawF64(_))
    }
    fn is_raw_i64(&self) -> bool {
        matches!(self, LowerOut::RawI64(_))
    }
}

fn lower_prim<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    stub_fn_ids: &std::collections::BTreeMap<u32, FuncId>,
    env: &HashMap<u32, ir::Value>,
    raw_f64_vars: &std::collections::HashSet<u32>,
    raw_int_vars: &std::collections::HashSet<u32>,
    fn_types: &crate::ir_typer::FnTypes,
    spec_registry: &SpecRegistry,
    module: &crate::fz_ir::Module,
    fn_ids: &HashMap<u32, FuncId>,
    param_reprs: &[Vec<ArgRepr>],
    return_reprs: &[ArgRepr],
    prim: &Prim,
    dest_var: crate::fz_ir::Var,
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
            // fz-ul4.27.15.1: emit the raw payload when the consumer's
            // Descr is int-monomorphic. Tagged consumers retag via
            // `tagged_get` (= `box_int`) at their use site — same op
            // count as today's per-use unbox, just inverted. The wrapper
            // at the bottom of the match would otherwise wrap a tagged
            // `iconst((n<<3)|TAG_INT)` and every int-arithmetic /
            // RawInt-slot consumer would unbox via `as_raw_i64`.
            Const::Int(n) => {
                let d = fn_types
                    .vars
                    .get(&dest_var)
                    .cloned()
                    .unwrap_or_else(crate::types::Descr::any);
                if d.is_subtype(&crate::types::Descr::int()) {
                    return Ok(LowerOut::RawI64(b.ins().iconst(types::I64, *n)));
                }
                b.ins().iconst(types::I64, ((*n) << 3) | TAG_INT)
            }
            Const::True => b.ins().iconst(types::I64, TRUE_BITS),
            Const::False => b.ins().iconst(types::I64, FALSE_BITS),
            Const::Nil => b.ins().iconst(types::I64, NIL_BITS),
            Const::Atom(id) => b.ins().iconst(types::I64, ((*id as i64) << 3) | TAG_ATOM),
            Const::Float(f) => {
                // fz-ul4.27.15.2: emit a raw `f64const` when the consumer
                // is float-monomorphic. Tagged consumers heap-alloc via
                // `tagged_get` → `box_float_native` on demand. Skipping
                // the per-literal `fz_alloc_float` call when the literal
                // is consumed raw eliminates a runtime heap allocation
                // for every float literal that flows into float-arith,
                // a RawF64 slot, or `fz_print_f64`.
                let d = fn_types
                    .vars
                    .get(&dest_var)
                    .cloned()
                    .unwrap_or_else(crate::types::Descr::any);
                if d.is_subtype(&crate::types::Descr::float()) {
                    return Ok(LowerOut::RawF64(b.ins().f64const(*f)));
                }
                // Tagged fallback: heap-alloc as before. v1 keeps const-pool
                // dedup for a future ticket — correct first.
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
            macro_rules! tag_a {
                () => {
                    tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, a.0)
                };
            }
            macro_rules! tag_b {
                () => {
                    tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, bv.0)
                };
            }
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    let mop = *op;
                    // Typed-float fast path first so we never tag the raw
                    // f64 inputs.
                    if descr_is_float(fn_types, *a)
                        && descr_is_float(fn_types, *bv)
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
                    // fz-ul4.27.9: inlined float-arith slow path. Pre-resolve
                    // the FuncRefs the slow closure may call (jmod can't be
                    // captured into the closure). Promote both operands via
                    // fz_promote_f64, run the op natively (frem → fz_fmod
                    // since Cranelift has no native opcode), box via
                    // fz_alloc_float.
                    let pfref = jmod.declare_func_in_func(runtime.promote_f64_id, b.func);
                    let aref = jmod.declare_func_in_func(runtime.alloc_float_id, b.func);
                    let fmodref = jmod.declare_func_in_func(runtime.fmod_id, b.func);
                    let slow_arith =
                        move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                            let i0 = b.ins().call(pfref, &[av]);
                            let af = b.inst_results(i0)[0];
                            let i1 = b.ins().call(pfref, &[bv]);
                            let bf = b.inst_results(i1)[0];
                            let raw_f = match mop {
                                BinOp::Add => b.ins().fadd(af, bf),
                                BinOp::Sub => b.ins().fsub(af, bf),
                                BinOp::Mul => b.ins().fmul(af, bf),
                                BinOp::Div => b.ins().fdiv(af, bf),
                                BinOp::Mod => {
                                    let inst = b.ins().call(fmodref, &[af, bf]);
                                    b.inst_results(inst)[0]
                                }
                                _ => unreachable!(),
                            };
                            let bits = b.ins().bitcast(types::I64, ir::MemFlags::new(), raw_f);
                            let inst = b.ins().call(aref, &[bits]);
                            b.inst_results(inst)[0]
                        };
                    emit_dispatch_binop(b, av, bvv, fast_int, slow_arith)
                }
                BinOp::Eq | BinOp::Neq => {
                    // VR.5a + .5.2.
                    let is_eq = matches!(op, BinOp::Eq);
                    let int_cc = if is_eq { IntCC::Equal } else { IntCC::NotEqual };
                    let f_cc = if is_eq {
                        FloatCC::Equal
                    } else {
                        FloatCC::NotEqual
                    };

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
                    if (descr_is_atom(fn_types, *a) && descr_is_atom(fn_types, *bv))
                        || (descr_is_nil_or_bool(fn_types, *a)
                            && descr_is_nil_or_bool(fn_types, *bv))
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
                    let fast_int =
                        move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                            let ai = unbox_int(b, av);
                            let bi = unbox_int(b, bv);
                            let cmp = b.ins().icmp(icc, ai, bi);
                            bool_to_fz(b, cmp)
                        };
                    // fz-ul4.27.9: inlined float-cmp slow path. Promote both
                    // operands to f64 and emit native fcmp.
                    let pfref = jmod.declare_func_in_func(runtime.promote_f64_id, b.func);
                    let fcc = match op {
                        BinOp::Lt => FloatCC::LessThan,
                        BinOp::Le => FloatCC::LessThanOrEqual,
                        BinOp::Gt => FloatCC::GreaterThan,
                        BinOp::Ge => FloatCC::GreaterThanOrEqual,
                        _ => unreachable!(),
                    };
                    let slow_cmp =
                        move |b: &mut FunctionBuilder<'_>, av: ir::Value, bv: ir::Value| {
                            let i0 = b.ins().call(pfref, &[av]);
                            let af = b.inst_results(i0)[0];
                            let i1 = b.ins().call(pfref, &[bv]);
                            let bf = b.inst_results(i1)[0];
                            let cmp = b.ins().fcmp(fcc, af, bf);
                            bool_to_fz(b, cmp)
                        };
                    emit_dispatch_binop(b, av, bvv, fast_int, slow_cmp)
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
            let kind = BuiltinKind::from_id(*bid)
                .ok_or_else(|| CodegenError::new(format!("unknown builtin id {}", bid.0)))?;
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
                    let vv =
                        tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0);
                    let iv =
                        tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[1].0);
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
                BuiltinKind::Spawn => match args.len() {
                    1 => {
                        let cv = tagged_get(
                            env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0,
                        );
                        let fref = jmod.declare_func_in_func(runtime.spawn_id, b.func);
                        let inst = b.ins().call(fref, &[cv]);
                        b.inst_results(inst)[0]
                    }
                    2 => {
                        let cv = tagged_get(
                            env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0,
                        );
                        let mv = tagged_get(
                            env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[1].0,
                        );
                        let fref = jmod.declare_func_in_func(runtime.spawn_opt_id, b.func);
                        let inst = b.ins().call(fref, &[cv, mv]);
                        b.inst_results(inst)[0]
                    }
                    n => {
                        return Err(CodegenError::new(format!(
                            "spawn/1 or spawn/2 expected, got {n} args"
                        )));
                    }
                },
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
                    let pv =
                        tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[0].0);
                    let mv =
                        tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, args[1].0);
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
                let value_v =
                    tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, f.value.0);
                let ty_tag = b.ins().iconst(types::I32, encode_bit_type(f.ty) as i64);
                let unit = b
                    .ins()
                    .iconst(types::I32, f.unit.unwrap_or(default_unit_for(f.ty)) as i64);
                let endian = b.ins().iconst(types::I32, encode_endian(f.endian) as i64);
                let signed = b.ins().iconst(types::I32, f.signed as i64);
                let (size_present, size_value) = match &f.size {
                    None => (b.ins().iconst(types::I32, 0), b.ins().iconst(types::I32, 0)),
                    Some(crate::fz_ir::BitSizeIr::Literal(n)) => (
                        b.ins().iconst(types::I32, 1),
                        b.ins().iconst(types::I32, *n as i64),
                    ),
                    Some(crate::fz_ir::BitSizeIr::Var(v)) => {
                        let raw =
                            tagged_get(env, raw_f64_vars, raw_int_vars, b, jmod, runtime, v.0);
                        // Boxed int -> raw int -> truncate to i32.
                        let unb = unbox_int(b, raw);
                        let truncated = b.ins().ireduce(types::I32, unb);
                        (b.ins().iconst(types::I32, 1), truncated)
                    }
                };
                b.ins().call(
                    write,
                    &[
                        value_v,
                        ty_tag,
                        size_present,
                        size_value,
                        unit,
                        endian,
                        signed,
                    ],
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
                None => (b.ins().iconst(types::I32, 0), b.ins().iconst(types::I32, 0)),
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
            // fz-ul4.29.5: alloc closure heap object via fz_alloc_closure;
            // store stub_fp at payload offset 16; write captures (tagged)
            // at offsets 24+i*8. Captures are always tagged FzValue in
            // the closure payload regardless of the callee's typed entry
            // slots — the stub handles tagged→raw conversion at invoke
            // time. fz-ul4.29.12.2: resolve this MakeClosure's narrow
            // SpecId via the lambda's full input-Descr key (captures
            // from caller's `fn_types`, args = `any`); pick the typed
            // stub keyed by that SpecId.
            let n_caps = captured.len();
            let lam = module.fn_by_id(*fn_id);
            let n_params = lam.block(lam.entry).params.len();
            let mut key: Vec<crate::types::Descr> = vec![crate::types::Descr::any(); n_params];
            for (k, cv) in captured.iter().enumerate() {
                if let Some(slot) = key.get_mut(k) {
                    *slot = fn_types
                        .vars
                        .get(cv)
                        .cloned()
                        .unwrap_or_else(crate::types::Descr::any);
                }
            }
            // fz-ul4.29.10.3 — fall back to any registered SpecId for
            // the lambda when the any-key was dropped (closure unreachable
            // post-rewrite). The stub field is required by the closure
            // header layout but nothing dispatches through it in the
            // unreachable case.
            let _ = stub_fn_ids;
            let cl_sid = spec_registry
                .resolve(*fn_id, &key)
                .map(|s| s.0)
                .or_else(|| {
                    spec_registry
                        .iter()
                        .find(|(s, fid, _)| *fid == *fn_id && fn_ids.contains_key(&s.0))
                        .map(|(s, _, _)| s.0)
                })
                .ok_or_else(|| {
                    CodegenError::new(format!(
                        ".29.12.2: no live spec for closure target FnId({})",
                        fn_id.0
                    ))
                })?;
            // fz-cps.1.7 — zero-capture MakeClosure: look up the
            // per-Process static singleton instead of allocating per call
            // site. fz-cps.1.8 — singleton's +16 holds the body's
            // func_addr (closure-target sig). docs/cps-in-clif.md §8.2.
            if captured.is_empty() {
                let fref = jmod.declare_func_in_func(runtime.get_static_closure_id, b.func);
                let sid_v = b.ins().iconst(types::I32, cl_sid as i64);
                let inst = b.ins().call(fref, &[sid_v]);
                return Ok(LowerOut::Tagged(b.inst_results(inst)[0]));
            }
            // fz-cps.1.8 — non-zero captures: alloc closure heap object,
            // write body's func_addr at +16 (no stub), captures at +24+i*8.
            // The body has closure-target sig `(args..., self, cont) tail`
            // and loads captures from `self+24+i*8` in its entry harness.
            let body_func_id = *fn_ids.get(&cl_sid).ok_or_else(|| {
                CodegenError::new(format!(
                    "fz-cps.1.8: no body FuncId for closure SpecId({}) \
                     (FnId({}), {} captures)",
                    cl_sid, fn_id.0, n_caps
                ))
            })?;
            let alloc_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
            let fid_v = b.ins().iconst(types::I32, fn_id.0 as i64);
            let nc_v = b.ins().iconst(types::I32, n_caps as i64);
            // fz-ul4.27.22.6: halt_kind from body's return repr so
            // fz_spawn_entry can pick the matching halt-cont singleton.
            let body_return_repr = return_reprs[cl_sid as usize];
            let hk_v = b
                .ins()
                .iconst(types::I32, body_return_repr.halt_kind() as i64);
            let inst = b.ins().call(alloc_fref, &[fid_v, nc_v, hk_v]);
            let cl_ptr = b.inst_results(inst)[0];
            let body_fref = jmod.declare_func_in_func(body_func_id, b.func);
            let body_addr = b.ins().func_addr(types::I64, body_fref);
            b.ins()
                .store(MemFlags::trusted(), body_addr, cl_ptr, HEADER_SIZE);
            // fz-ul4.27.22.5: store each capture in the body's narrow
            // param_repr (body's entry harness at line ~3406 loads via
            // my_param_reprs[k].cl_type()). Mirrors fz-ul4.27.21.2's
            // typed-capture seam for cont closures.
            let body_param_reprs = &param_reprs[cl_sid as usize];
            for (i, cv) in captured.iter().enumerate() {
                let from = var_repr(cv.0, raw_int_vars, raw_f64_vars);
                let to = body_param_reprs[i];
                let raw = *env.get(&cv.0).expect("MakeClosure: captured var unbound");
                let val = coerce_to(b, jmod, runtime, raw, from, to);
                let off = HEADER_SIZE + SLOT_BYTES + (i as i32) * SLOT_BYTES;
                b.ins().store(MemFlags::trusted(), val, cl_ptr, off);
            }
            cl_ptr
        }
        Prim::MakeVec(kind, els) => {
            use crate::fz_ir::VecKindIr;
            use fz_runtime::fz_value::HeapKind;
            let kind_tag = match kind {
                VecKindIr::I64 => HeapKind::VecI64 as i64,
                VecKindIr::U8 => HeapKind::VecU8 as i64,
                VecKindIr::Bit => HeapKind::VecBit as i64,
                VecKindIr::F64 => {
                    return Err(CodegenError::new("MakeVec(F64) deferred to fz-ul4.11.23"));
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

/// Emit a tag-dispatched binary op: if both Tag::Int, run `fast`; else run
/// `slow`. fz-ul4.27.9: the slow arm is now caller-emitted (was a runtime
/// helper call), so promote+fadd+box (or promote+fcmp) lowers inline.
fn emit_dispatch_binop<F, S>(
    b: &mut FunctionBuilder<'_>,
    av: ir::Value,
    bv: ir::Value,
    fast: F,
    slow: S,
) -> ir::Value
where
    F: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> ir::Value,
    S: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> ir::Value,
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
    let slow_v = slow(b, av, bv);
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

/// fz-ul4.27.13 — Classify a Var's current Cranelift-side repr based on the
/// `raw_*_vars` membership sets maintained by `compile_fn`.
fn var_repr(
    v: u32,
    raw_int_vars: &std::collections::HashSet<u32>,
    raw_f64_vars: &std::collections::HashSet<u32>,
) -> ArgRepr {
    if raw_f64_vars.contains(&v) {
        ArgRepr::RawF64
    } else if raw_int_vars.contains(&v) {
        ArgRepr::RawInt
    } else {
        ArgRepr::Tagged
    }
}

/// fz-ul4.27.13 — Coerce a Cranelift value between ArgReprs. `RawInt` ↔
/// `RawF64` direct conversion is intentionally unsupported (no Descr admits
/// both; if it surfaces, the typer or call-site narrowing is wrong).
fn coerce_to<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    val: ir::Value,
    from: ArgRepr,
    to: ArgRepr,
) -> ir::Value {
    if from == to {
        return val;
    }
    match (from, to) {
        (ArgRepr::Tagged, ArgRepr::RawInt) => unbox_int(b, val),
        (ArgRepr::Tagged, ArgRepr::RawF64) => unbox_float(b, val),
        (ArgRepr::RawInt, ArgRepr::Tagged) => box_int(b, val),
        (ArgRepr::RawF64, ArgRepr::Tagged) => box_float_native(b, jmod, runtime, val),
        (a, c) => panic!("coerce_to: unsupported {:?} → {:?}", a, c),
    }
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

    /// fz-cps.1.7 — every zero-capture `MakeClosure(f, [])` target gets
    /// one entry in `static_closure_targets`. Multiple `MakeClosure(f, [])`
    /// sites for the same `f` share a single entry (cl_sid keyed). At
    /// runtime `make_process` allocates one Box per entry; two
    /// `fz_get_static_closure(cl_sid)` calls in the same Process return
    /// pointer-identical results. See docs/cps-in-clif.md §8.2.
    #[test]
    fn static_closure_targets_registered_for_zero_cap_make_closure() {
        // `f` and `g` each appear as a zero-cap closure target via
        // `apply(f, 1)` / `apply(g, 2)` — partial-eval / typer wraps the
        // top-level fns in `MakeClosure(_, [])` at the call site.
        let src = "fn f(x), do: x + 1\n\
                   fn g(x), do: x * 2\n\
                   fn apply(h, x), do: h(x)\n\
                   fn main() do\n\
                     print(apply(f, 1))\n\
                     print(apply(g, 2))\n\
                   end";
        let m = lower_src(src);
        let compiled = compile(&m).expect("compile");
        let targets = compiled.static_closure_targets();
        // At minimum, `f` and `g` are registered.
        assert!(
            targets.len() >= 2,
            "expected ≥2 static closure targets (f, g); got {}: {:?}",
            targets.len(),
            targets
                .iter()
                .map(|(s, f, _, _)| (s, f))
                .collect::<Vec<_>>(),
        );
        // Distinct cl_sids and distinct code addresses.
        let mut cl_sids: Vec<u32> = targets.iter().map(|(s, _, _, _)| *s).collect();
        cl_sids.sort();
        cl_sids.dedup();
        assert_eq!(
            cl_sids.len(),
            targets.len(),
            "cl_sids must be unique across static_closure_targets entries"
        );
        for (_, _, ptr, _) in targets {
            assert!(
                !ptr.is_null(),
                "static-closure stub_fp must be a resolved address"
            );
        }
    }

    /// fz-cps.1.7 — `make_process` populates `Process.static_closures` from
    /// the compiled module's targets, and `fz_get_static_closure(cl_sid)`
    /// returns the singleton's pointer. Two lookups return the same
    /// pointer (singleton identity).
    #[test]
    fn static_closure_lookup_returns_singleton_pointer() {
        let src = "fn f(x), do: x + 1\n\
                   fn apply(h, x), do: h(x)\n\
                   fn main() do print(apply(f, 1)) end";
        let m = lower_src(src);
        let compiled = compile(&m).expect("compile");
        let targets = compiled.static_closure_targets();
        let (cl_sid, _, _, _) = *targets.first().expect("at least one static closure target");
        let mut p = compiled.make_process();
        let prev = fz_runtime::process::CURRENT_PROCESS.with(|c| c.replace(&mut p as *mut Process));
        let a = fz_runtime::ir_runtime::fz_get_static_closure(cl_sid);
        let b = fz_runtime::ir_runtime::fz_get_static_closure(cl_sid);
        fz_runtime::process::CURRENT_PROCESS.with(|c| c.set(prev));
        assert_eq!(a, b, "static-closure lookup must return the same pointer");
        assert_ne!(a, 0, "static-closure lookup must return non-null");
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
        // wraps fz_aot_run_main. The artifact's main_symbol surfaces that for
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
        assert!(
            magic_ok,
            "unexpected object magic: {:02x?}",
            &artifact.object[..4]
        );
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
        assert_eq!(
            ra, rb,
            "atom id stable across processes from the same module"
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
        assert_eq!(
            ra2, 10,
            "process a's second run returns 10 (independent of b)"
        );

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
        assert_eq!(
            run_main("fn add1(n), do: n + 1\nfn main(), do: add1(41)"),
            42
        );
    }

    #[test]
    fn binop_with_inner_nontail_call() {
        assert_eq!(
            run_main("fn add1(n), do: n + 1\nfn main(), do: add1(40) + 2"),
            43
        );
    }

    #[test]
    fn fact_5_smaller_repro() {
        assert_eq!(
            run_main(
                r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(5)
"#
            ),
            120
        );
    }

    #[test]
    fn fact_10_runs_via_recursion_and_continuation_chain() {
        assert_eq!(
            run_main(
                r#"
fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)
fn main(), do: fact(10)
"#
            ),
            3628800
        );
    }

    #[test]
    fn count_100k_stays_bounded_via_tail_call_frame_reuse() {
        assert_eq!(
            run_main(
                r#"
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main(), do: count(100000, 0)
"#
            ),
            100_000
        );
    }

    #[test]
    fn render_fz_value_dispatches_per_tag() {
        use fz_runtime::fz_value::FzValue;
        assert_eq!(
            fz_runtime::fz_value::debug::render(FzValue::from_int(42).0),
            "42"
        );
        assert_eq!(
            fz_runtime::fz_value::debug::render(FzValue::from_int(0).0),
            "0"
        );
        assert_eq!(
            fz_runtime::fz_value::debug::render(FzValue::from_int(-7).0),
            "-7"
        );
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::NIL.0), "nil");
        assert_eq!(fz_runtime::fz_value::debug::render(FzValue::TRUE.0), "true");
        assert_eq!(
            fz_runtime::fz_value::debug::render(FzValue::FALSE.0),
            "false"
        );
        // Atom rendering needs a populated Process.atom_names; with an
        // empty table render falls back to `:atom_N`. The full
        // source-name path is verified end-to-end by the fixture matrix
        // (hello.fz post fz-ul4.25 re-bless).
        assert_eq!(
            fz_runtime::fz_value::debug::render(FzValue::from_atom_id(3).0),
            ":atom_3"
        );
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
        assert_eq!(
            run_main("fn main(), do: %{a: 10, b: 20}[:a] + %{a: 10, b: 20}[:b]"),
            30
        );
    }

    #[test]
    fn map_update_returns_new_map_originals_unchanged() {
        assert_eq!(
            capture_main(
                r#"
fn main() do
  m = %{a: 1, b: 2}
  m2 = %{m | a: 99}
  print(m)
  print(m2)
end
"#
            ),
            vec!["%{:a => 1, :b => 2}", "%{:a => 99, :b => 2}",]
        );
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
            capture_main(
                r#"
fn parse(<<n, rest::binary>>), do: {n, rest}
fn main(), do: print(parse(<<0xa5, 0x01, 0x02>>))
"#
            ),
            vec!["{165, <<1, 2>>}"]
        );
    }

    #[test]
    fn match_variable_size_payload_via_size_var() {
        assert_eq!(
            capture_main(
                r#"
fn parse(<<len, payload::binary-size(len), rest::binary>>) do
  {len, payload, rest}
end
fn main(), do: print(parse(<<3, 0x01, 0x02, 0x03, 0xff>>))
"#
            ),
            vec!["{3, <<1, 2, 3>>, <<255>>}"]
        );
    }

    // ----- .11.11 tuple tests -----

    #[test]
    fn print_tuple_pair_renders() {
        assert_eq!(capture_main("fn main(), do: print({1, 2})"), vec!["{1, 2}"]);
    }

    #[test]
    fn fst_snd_destructure_tuple() {
        assert_eq!(
            run_main(
                r#"
fn fst({a, _}), do: a
fn snd({_, b}), do: b
fn main(), do: fst({10, 20}) + snd({30, 40})
"#
            ),
            50
        );
    }

    #[test]
    fn print_mixed_type_tuple() {
        assert_eq!(
            capture_main("fn main(), do: print({1, :ok, true})"),
            vec!["{1, :ok, true}"]
        );
    }

    // ----- .11.10 list tests -----

    #[test]
    fn print_list_literal_renders_via_jit() {
        assert_eq!(
            capture_main("fn main(), do: print([1, 2, 3])"),
            vec!["[1, 2, 3]"]
        );
    }

    #[test]
    fn sum_list_via_head_tail_recursion() {
        assert_eq!(
            run_main(
                r#"
fn sum([]), do: 0
fn sum([h | t]), do: h + sum(t)
fn main(), do: sum([1, 2, 3, 4, 5])
"#
            ),
            15
        );
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
        assert_eq!(
            run_main(
                r#"
fn even(0), do: true
fn even(n), do: odd(n - 1)
fn odd(0), do: false
fn odd(n), do: even(n - 1)
fn main(), do: even(10)
"#
            ),
            1
        );
    }

    // ----- .11.19 closure tests -----

    #[test]
    fn apply_simple_closure_no_captures() {
        assert_eq!(
            run_main(
                r#"
fn double(x), do: x * 2
fn apply_f(f, n), do: f(n)
fn main(), do: apply_f(double, 21)
"#
            ),
            42
        );
    }

    #[test]
    fn closure_captures_local_value() {
        assert_eq!(
            run_main(
                r#"
fn make_adder(k), do: fn(x) -> x + k
fn main() do
  f = make_adder(10)
  f(5)
end
"#
            ),
            15
        );
    }

    #[test]
    fn map_higher_order_renders_doubled_list() {
        assert_eq!(
            capture_main(
                r#"
fn double(x), do: x * 2
fn map_l(_, []), do: []
fn map_l(f, [h | t]), do: [f(h) | map_l(f, t)]
fn main(), do: print(map_l(double, [1, 2, 3]))
"#
            ),
            vec!["[2, 4, 6]"]
        );
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
        let (halt, _m) = run_main_after_heap_reset("fn main(), do: 2.5");
        assert_eq!(f64::from_bits(halt as u64), 2.5);
    }

    #[test]
    fn print_float_renders_with_explicit_dot_zero() {
        assert_eq!(
            capture_main("fn main() do\n  print(4.0)\n  print(2.5)\nend"),
            vec!["4.0", "2.5"]
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
        let (halt, _m) = run_main_after_heap_reset("fn main(), do: <<2.5::float>>");
        let halt = halt as u64;
        let p = fz_runtime::fz_value::FzValue(halt).unbox_ptr().unwrap();
        let bytes = unsafe { std::slice::from_raw_parts((p as *const u8).add(24), 8) };
        let mut buf = [0u8; 8];
        buf.copy_from_slice(bytes);
        let f = f64::from_bits(u64::from_be_bytes(buf));
        assert_eq!(f, 2.5);
    }

    // ----- .11.14 vec tests -----

    #[test]
    fn print_vec_i64_renders_via_jit() {
        assert_eq!(
            capture_main("fn main(), do: print(~v[1, 2, 3])"),
            vec!["~v[1, 2, 3]"]
        );
    }

    #[test]
    fn print_vec_u8_renders_via_jit() {
        assert_eq!(
            capture_main("fn main(), do: print(~b[0xff, 0xab])"),
            vec!["~b[255, 171]"]
        );
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
    fn tail_call_closure_reuses_frame_via_count_loop() {
        // Self-applying closure to force TailCallClosure on every iteration.
        assert_eq!(
            run_main(
                r#"
fn loop_with(f, 0, acc), do: acc
fn loop_with(f, n, acc), do: f(f, n - 1, acc + 1)
fn main(), do: loop_with(loop_with, 100000, 0)
"#
            ),
            100_000
        );
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
        assert!(
            !ir.contains("brif"),
            "elision should drop the both_int branch:\n{}",
            ir
        );
    }

    #[test]
    fn arith_top_param_keeps_dispatch() {
        let m = build_top_param_add_module();
        let ir = get_main_ir(&m);
        assert!(
            ir.contains("brif"),
            "dispatch should be retained for Top operands:\n{}",
            ir
        );
    }

    // --- fz-ul4.27.6.2.2 — build_fn_signature ---

    #[test]
    fn signature_uniform_when_not_native() {
        // `fn add(a, b) do a + b end` lowered, typed, then asked for a
        // uniform sig. Should be `(i64, i64) -> i64` regardless of param
        // Descrs.
        let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
        let mt = crate::ir_typer::type_module(&m);
        let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
        let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
        let rd = join_return_descrs(&m.fns[add_idx], ft);
        let prs = build_param_reprs(&m.fns[add_idx], ft);
        let sig = build_fn_signature(&prs, ArgRepr::from_descr(&rd), false, true, false, None);
        assert_eq!(sig.params.len(), 2);
        assert_eq!(sig.returns.len(), 1);
        assert_eq!(sig.params[0].value_type, types::I64);
        assert_eq!(sig.params[1].value_type, types::I64);
        assert_eq!(sig.returns[0].value_type, types::I64);
    }

    #[test]
    fn signature_native_uses_typed_params_and_host_ctx() {
        // Same `add` fn, this time the typer has narrowed entry params to
        // int via call-site narrowing. Native sig should be
        // `(i64, i64, host_ctx: i64, cont: i64) -> i64`.
        // fz-cps.1.a (fz-siu.1.1): trailing cont:i64 per §2.1.
        let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
        let mt = crate::ir_typer::type_module(&m);
        let add_idx = m.fns.iter().position(|f| f.name == "add").unwrap();
        let ft = mt.any_spec_for(m.fns[add_idx].id).expect("registered spec");
        let rd = join_return_descrs(&m.fns[add_idx], ft);
        let prs = build_param_reprs(&m.fns[add_idx], ft);
        let sig = build_fn_signature(&prs, ArgRepr::from_descr(&rd), true, true, false, None);
        // 2 entry params + host_ctx + cont.
        assert_eq!(sig.params.len(), 4);
        assert_eq!(sig.returns.len(), 1);
        // Trailing cont is i64.
        assert_eq!(sig.params.last().unwrap().value_type, types::I64);
        // host_ctx (second-to-last) is i64.
        assert_eq!(sig.params[sig.params.len() - 2].value_type, types::I64);
        // Return is i64 (tagged or raw-int — both ride i64 register).
        assert_eq!(sig.returns[0].value_type, types::I64);
    }

    #[test]
    fn signature_native_arity_matches_entry_params_plus_host_ctx() {
        // .27.13: native sig is per-Descr typed. For `dist(x, y)` called
        // with `dist(1.5, 2.5)`, call-site narrowing types `x` and `y` as
        // float-only → AbiParam(f64). `host_ctx` stays i64. Return joins
        // every Term::Return val Descr; here that's float-only → f64.
        // fz-cps.1.a (fz-siu.1.1): trailing cont:i64 per §2.1.
        let m =
            lower_src("fn dist(x, y) do x * x + y * y end\nfn main() do print(dist(1.5, 2.5)) end");
        let mt = crate::ir_typer::type_module(&m);
        let dist_idx = m.fns.iter().position(|f| f.name == "dist").unwrap();
        let ft = mt
            .any_spec_for(m.fns[dist_idx].id)
            .expect("registered spec");
        let rd = join_return_descrs(&m.fns[dist_idx], ft);
        let prs = build_param_reprs(&m.fns[dist_idx], ft);
        let sig = build_fn_signature(&prs, ArgRepr::from_descr(&rd), true, true, false, None);
        // 2 entry params + host_ctx + cont.
        assert_eq!(sig.params.len(), 4);
        assert_eq!(sig.params[0].value_type, types::F64);
        assert_eq!(sig.params[1].value_type, types::F64);
        assert_eq!(sig.params[2].value_type, types::I64);
        assert_eq!(sig.params[3].value_type, types::I64); // cont
        // fz-cps.1.2: native return canonicalized to i64 (cont indirect
        // sig is `(i64, i64) -> i64 tail`; caller's return type must
        // match per Cranelift's tail-call verifier).
        assert_eq!(sig.returns[0].value_type, types::I64);
    }

    // ----- fz-ul4.29.2: SpecRegistry infrastructure -----

    #[test]
    fn spec_registry_registers_any_key_per_fn_with_spec_id_eq_fn_id() {
        // Two-fn module. After compile(), spec_registry holds one any-key
        // spec per fn; the SpecId.0 == FnId.0 invariant is asserted at
        // build time (debug_assert in compile_with_backend).
        let m = lower_src("fn add(a, b) do a + b end\nfn main() do print(add(1, 2)) end");
        let compiled = compile(&m).unwrap();
        // Drive a run to ensure the pipeline ran the registry construction
        // path; the assertion lives in compile_with_backend.
        let _ = compiled.run(m.fn_by_name("main").unwrap().id);
    }

    #[test]
    fn spec_registry_any_key_lookup() {
        // Use the registry directly to verify register/resolve/any_key
        // contracts. Doesn't go through compile().
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        let any_key_2 = vec![crate::types::Descr::any(); 2];
        let sid = reg.register(fid, any_key_2.clone());
        assert_eq!(sid.0, 0, "first registration gets SpecId(0)");
        // Re-registering the same key returns the same SpecId.
        let sid2 = reg.register(fid, any_key_2.clone());
        assert_eq!(sid, sid2);
        // Resolve roundtrips.
        let resolved = reg.resolve(fid, &any_key_2);
        assert_eq!(resolved, Some(sid));
        // any_key helper.
        let via_any = reg.any_key(fid, 2);
        assert_eq!(via_any, sid);
        // A different fn gets a different SpecId.
        let other_sid = reg.register(FnId(1), vec![crate::types::Descr::any(); 0]);
        assert_eq!(other_sid.0, 1);
        assert_eq!(reg.len(), 2);
    }

    #[test]
    fn spec_registry_distinct_narrow_keys() {
        // The registry distinguishes narrow keys via the exact-match
        // fast path. Subsumption fallback is exercised below.
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        let int1 = vec![crate::types::Descr::int()];
        let float1 = vec![crate::types::Descr::float()];
        let sid_int = reg.register(fid, int1.clone());
        let sid_float = reg.register(fid, float1.clone());
        assert_ne!(
            sid_int, sid_float,
            "int-key and float-key must be distinct SpecIds"
        );
        // Exact-match fast path returns identity.
        assert_eq!(reg.resolve(fid, &int1), Some(sid_int));
        assert_eq!(reg.resolve(fid, &float1), Some(sid_float));
        // No covering spec for atom under the registered set → None.
        let atom1 = vec![crate::types::Descr::atom_top()];
        assert_eq!(reg.resolve(fid, &atom1), None);
    }

    // ----- fz-ul4.29.11: subsumption-based callsite dispatch -----

    #[test]
    fn resolve_subsumes_narrower_query_to_wider_registered_spec() {
        // Only [int] registered; query [int_lit(4)] should subsume to it.
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        let int_spec = reg.register(fid, vec![crate::types::Descr::int()]);
        let q = vec![crate::types::Descr::int_lit(4)];
        assert_eq!(reg.resolve(fid, &q), Some(int_spec));
    }

    #[test]
    fn resolve_picks_narrowest_among_multiple_supertype_matches() {
        // Both [int] and [any] cover [int_lit(4)]. [int] is narrower; pick it.
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        let any_spec = reg.register(fid, vec![crate::types::Descr::any()]);
        let int_spec = reg.register(fid, vec![crate::types::Descr::int()]);
        let q = vec![crate::types::Descr::int_lit(4)];
        let resolved = reg.resolve(fid, &q);
        assert_eq!(
            resolved,
            Some(int_spec),
            "should pick narrower [int] over wider [any]; got {:?}, any={:?}, int={:?}",
            resolved,
            any_spec,
            int_spec
        );
    }

    #[test]
    fn resolve_returns_none_when_nothing_covers() {
        // [float] registered; query [int_lit(4)] is not a subtype → None.
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        reg.register(fid, vec![crate::types::Descr::float()]);
        let q = vec![crate::types::Descr::int_lit(4)];
        assert_eq!(
            reg.resolve(fid, &q),
            None,
            "int_lit(4) is not a subtype of float; no covering spec"
        );
    }

    #[test]
    fn resolve_subtype_incomparable_picks_lowest_specid() {
        // [int, any] (sid A) and [any, atom] (sid B). Query [int_lit(4), :foo]
        // is covered by both; neither key is a subtype of the other on every
        // axis. Deterministic tiebreak picks the lowest SpecId.
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        let int = crate::types::Descr::int();
        let any = crate::types::Descr::any();
        let atom = crate::types::Descr::atom_top();
        let sid_a = reg.register(fid, vec![int.clone(), any.clone()]);
        let sid_b = reg.register(fid, vec![any.clone(), atom.clone()]);
        let q = vec![
            crate::types::Descr::int_lit(4),
            crate::types::Descr::atom_lit(":foo"),
        ];
        let resolved = reg.resolve(fid, &q).expect("a covering spec exists");
        assert_eq!(
            resolved, sid_a,
            "subtype-incomparable matches: lowest SpecId wins; got {:?}, a={:?}, b={:?}",
            resolved, sid_a, sid_b
        );
    }

    #[test]
    fn resolve_exact_match_takes_fast_path() {
        // Exact-match registration resolves to the same SpecId — verifies
        // the O(1) fast path still works alongside subsumption fallback.
        let mut reg = SpecRegistry::new();
        let fid = FnId(0);
        let key = vec![crate::types::Descr::int(), crate::types::Descr::float()];
        let sid = reg.register(fid, key.clone());
        assert_eq!(reg.resolve(fid, &key), Some(sid));
    }

    #[test]
    fn resolve_per_fn_isolation() {
        // Specs for one fn must not subsume queries for a different fn.
        let mut reg = SpecRegistry::new();
        let _sid0 = reg.register(FnId(0), vec![crate::types::Descr::any()]);
        // No spec registered for FnId(1) — even though FnId(0) has an
        // any-key, it shouldn't cover queries to FnId(1).
        let q = vec![crate::types::Descr::int()];
        assert_eq!(reg.resolve(FnId(1), &q), None);
    }
}
