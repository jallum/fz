//! Shared codegen support constants, recording controls, and small scans.

use super::*;
use crate::fz_ir::{Prim, Stmt};
use cranelift_codegen::ir;
use std::collections::HashMap;

pub(crate) const HEADER_SIZE: i32 = 16;
pub(crate) const SLOT_BYTES: i32 = 8;

#[derive(Clone, Copy)]
pub(crate) enum ListTailBits {
    Empty,
    ValueRef(ir::Value),
    NonEmptyValueRef(ir::Value),
}

pub(crate) fn list_tail_bits_for_var<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
    tail_var: crate::fz_ir::Var,
    tail_bits: ir::Value,
) -> ListTailBits {
    if ty_is_empty_list_in_context(t, fn_types, tail_var, block_env) {
        ListTailBits::Empty
    } else if ty_is_non_empty_list_in_context(t, fn_types, tail_var, block_env) {
        ListTailBits::NonEmptyValueRef(tail_bits)
    } else {
        ListTailBits::ValueRef(tail_bits)
    }
}

// fz-yan.1 — nil/true/false are atoms with reserved compile-time IDs.
// These constants are raw atom payloads used with side-band ATOM kind tags.
pub(crate) const TRUE_BITS: i64 = fz_runtime::any_value::TRUE_BITS as i64;
pub(crate) const FALSE_BITS: i64 = fz_runtime::any_value::FALSE_BITS as i64;
thread_local! {
    /// (.11.24.4) Per-fn Cranelift IR display text captured by compile()
    /// after compile_fn but before define_function consumes the context.
    /// Test-only; enable by calling `ir_text_record_enable()` before compile.
    pub static IR_TEXT_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = const { std::cell::RefCell::new(None) };
    /// (fz-ul4.23.8) Per-fn machine-code disassembly captured by compile()
    /// when set_disasm is on. Enable with `asm_record_enable()` before
    /// compile; drain with `asm_record_take()` after.
    pub static ASM_RECORD: std::cell::RefCell<Option<Vec<(String, String)>>> = const { std::cell::RefCell::new(None) };
    /// fz-ul4.32.1 — per-fn Value → IR Ty map, populated by compile_fn
    /// at end-of-body. Consumed by the IR_TEXT_RECORD assembly step to
    /// annotate each `vN` definition with its typer result. Only the
    /// values bound to fz Vars (block params, Prim results, etc.) are
    /// recorded; pure Cranelift intermediates (iconst, ishl_imm, ...)
    /// have no fz-level type and stay unannotated.
    pub static VALUE_DESCR_RECORD: std::cell::RefCell<Option<HashMap<u32, crate::types::Ty>>>
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
#[cfg(test)]
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
    // fz-ul4.32.1 — pair the value-type recorder so the assembled
    // text gets typer annotations alongside the raw CLIF.
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = Some(HashMap::new()));
}

pub fn ir_text_record_take() -> Vec<(String, String)> {
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = None);
    IR_TEXT_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// Reset DEFAULT_PROCESS. Call at the start of any test that needs a clean
/// heap. Tests share threads via the cargo test runner's worker pool, so
/// leftover state is otherwise sticky.
#[cfg(test)]
pub fn heap_reset_for_test() {
    DEFAULT_PROCESS.with(|c| *c.borrow_mut() = None);
}

// fz_alloc_struct moved to ir_runtime.rs (.23.4.7).

// ----- Map runtime fns -----
//
// Maps use a heap-backed sorted-array layout. Codegen constructs maps by
// folding immutable put operations: start with an empty map, then each put
// copies/replaces/inserts and returns the new map.
//
// Key total ordering for canonical layout: Int < Atom < Special < Ptr;
// within each category, by raw bits (Int compares signed). Keys compare
// equal iff their u64 bits are equal — pointer-equal heap keys for v1.

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

pub(crate) fn encode_bit_type(t: crate::ast::BitType) -> u32 {
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

pub(crate) fn encode_endian(e: crate::ast::Endian) -> u32 {
    use crate::ast::Endian;
    match e {
        Endian::Big => 0,
        Endian::Little => 1,
        Endian::Native => 2,
    }
}

/// Default unit per type, mirroring `crate::ir_lower::resolved_unit_for`.
pub(crate) fn default_unit_for(ty: crate::ast::BitType) -> u32 {
    use crate::ast::BitType;
    match ty {
        BitType::Integer | BitType::Float | BitType::Bits => 1,
        BitType::Binary => 8,
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => 1,
    }
}

// ----- Float runtime fns -----
//
// Codegen keeps new float values in RawF64 or side-tagged container slots.
//
// Arithmetic dispatch: codegen emits an inline both-int fast-path test
// (`((a^1) | (b^1)) & 7 == 0`); when at least one operand is non-Int the
// slow arm promotes both to f64 via fz_promote_f64 and emits native
// fadd/fsub/fmul/fdiv when the result can stay RawF64. fz-ul4.27.9 inlined
// the slow path — previously a call to fz_arith_*. Typed float-float fast paths
// (.27.3) and typed int-int fast paths (.27.5.3) sit in front of the
// dispatch entirely. Eq/Neq do NOT promote: `1 == 1.0` is false.

// ----- fz-ul4.19.2: scheduler-bound builtins (spawn / self) -----
//
// Both consume a Runtime installed in TLS by Runtime::run_until_idle.
// Calling either outside the scheduler path panics with a clear message.

// fz_spawn(closure_bits) -> pid_bits. Extracts fn_id from the closure
// heap object and enqueues a new task at that fn. Returns the pid as a
// boxed AnyValue Int (Pid-as-struct deferred to a follow-up).
//
// Arith / cmp / eq FFI cluster moved to src/ir_runtime.rs (fz-ul4.23.4.1).

// Closure cluster moved to ir_runtime.rs (.23.4.11).

// fz_alloc_frame + fz_alloc_frame_for_test moved to ir_runtime.rs (.23.4.7).

// ---------------------------------------------------------------------------
// Compiler
// ---------------------------------------------------------------------------

pub(crate) fn fn_may_allocate_heap(f: &crate::fz_ir::FnIr) -> bool {
    f.blocks.iter().any(|block| {
        block.stmts.iter().any(|stmt| {
            let Stmt::Let(_, prim) = stmt;
            matches!(
                prim,
                Prim::MakeTuple(..)
                    | Prim::DestTupleBegin { .. }
                    | Prim::DestTupleSet { .. }
                    | Prim::DestListCons { .. }
                    | Prim::MakeList(..)
                    | Prim::MakeClosure(..)
                    | Prim::MakeMap(..)
                    | Prim::MapUpdate(..)
                    | Prim::DestMapBegin { .. }
                    | Prim::DestMapFreeze { .. }
                    | Prim::MakeBitstring(..)
                    | Prim::ConstBitstring(..)
                    | Prim::BitReaderInit(..)
                    | Prim::BitReadField { .. }
            )
        })
    })
}

#[cfg(test)]
thread_local! {
    pub(crate) static INLINE_DISABLED: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
    /// fz-jg5.6 — disable the compile-time reducer for tests that
    /// exercise codegen infrastructure (static_closure_targets,
    /// indirect closure paths, etc.) whose triggering inputs the reducer would
    /// dissolve. Parallel to INLINE_DISABLED.
    pub(crate) static REDUCER_DISABLED: std::cell::Cell<bool> =
        const { std::cell::Cell::new(false) };
}

#[cfg(test)]
pub(crate) fn with_inline_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    INLINE_DISABLED.with(|d| d.set(true));
    let r = f();
    INLINE_DISABLED.with(|d| d.set(false));
    r
}

#[cfg(test)]
pub(crate) fn with_reducer_disabled<F: FnOnce() -> R, R>(f: F) -> R {
    REDUCER_DISABLED.with(|d| d.set(true));
    let r = f();
    REDUCER_DISABLED.with(|d| d.set(false));
    r
}
