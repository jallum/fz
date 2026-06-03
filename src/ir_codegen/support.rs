//! Shared codegen support constants, recording controls, and small scans.

use super::*;
use crate::ast::{BitType, Endian};
use crate::fz_ir::Var;
use crate::ir_planner::SpecPlan;
use crate::types::{Ty, Types};
use cranelift_codegen::ir::{self, InstBuilder};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;
use fz_runtime::any_value::{FALSE_BITS as FALSE_BITS_RAW, TRUE_BITS as TRUE_BITS_RAW};
use std::cell::RefCell;
use std::collections::HashMap;

pub(crate) const HEADER_SIZE: i32 = 16;
pub(crate) const SLOT_BYTES: i32 = 8;

pub(crate) fn mark_retained_call_args_as_published<M: Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
    captured: &[Var],
) {
    for arg in args {
        if !captured.contains(arg) {
            continue;
        }
        let Some(CodegenValue::AnyRef(value_ref)) = var_env.get(&arg.0).copied() else {
            continue;
        };
        let _ = body.mark_published_ref_aliased(value_ref);
    }
}

#[derive(Clone, Copy)]
pub(crate) enum ListTailBits {
    Empty,
    ValueRef(ir::Value),
    NonEmptyValueRef(ir::Value),
}

pub(crate) fn list_tail_bits_for_var<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_types: &SpecPlan,
    block_env: Option<&HashMap<Var, Ty>>,
    tail_var: Var,
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

pub(crate) fn emit_owned_cons_reuse_or_alloc<M: Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    head: Var,
    tail: ListTailBits,
) -> Option<ir::Value> {
    let source_cons = body.owned_cons_reuse_source(head)?;
    let source_ref = body.any_ref_for_var(var_env, source_cons.0);
    let tail_ref = body.list_tail_ref_word(tail);
    Some(body.list_reuse_or_cons_tail_ref(source_ref, tail_ref))
}

// Raw atom payloads used with side-band ATOM kind tags.
pub(crate) const TRUE_BITS: i64 = TRUE_BITS_RAW as i64;
pub(crate) const FALSE_BITS: i64 = FALSE_BITS_RAW as i64;
thread_local! {
    /// Per-fn Cranelift IR display text captured between compile_fn and
    /// define_function (which consumes the context). Enable via
    /// `ir_text_record_enable()`.
    pub static IR_TEXT_RECORD: RefCell<Option<Vec<(String, String)>>> = const { RefCell::new(None) };
    /// Per-fn machine-code disassembly captured when set_disasm is on.
    /// Enable with `asm_record_enable()`; drain with `asm_record_take()`.
    pub static ASM_RECORD: RefCell<Option<Vec<(String, String)>>> = const { RefCell::new(None) };
    /// Per-fn Value -> IR Ty map populated at end-of-body and consumed by
    /// the IR_TEXT_RECORD assembly step to annotate `vN` definitions. Only
    /// values bound to fz Vars are recorded; pure Cranelift intermediates
    /// (iconst, ishl_imm, ...) stay unannotated.
    pub static VALUE_DESCR_RECORD: RefCell<Option<HashMap<u32, Ty>>>
        = const { RefCell::new(None) };
}

pub fn asm_record_enable() {
    ASM_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

pub fn asm_record_take() -> Vec<(String, String)> {
    ASM_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

/// Begin recording per-fn Cranelift IR display text. Subsequent `compile()`
/// calls on this thread append `(fn_name, clif_text)` pairs to a TLS
/// buffer; `ir_text_record_take` drains and returns them.
pub fn ir_text_record_enable() {
    IR_TEXT_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
    // Pair the value-type recorder so the assembled text gets typer
    // annotations alongside the raw CLIF.
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = Some(HashMap::new()));
}

pub fn ir_text_record_take() -> Vec<(String, String)> {
    VALUE_DESCR_RECORD.with(|c| *c.borrow_mut() = None);
    IR_TEXT_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}

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

pub(crate) fn encode_bit_type(t: BitType) -> u32 {
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

pub(crate) fn encode_endian(e: Endian) -> u32 {
    match e {
        Endian::Big => 0,
        Endian::Little => 1,
        Endian::Native => 2,
    }
}

/// Default unit per type. Mirrors `crate::ir_lower::resolved_unit_for`.
pub(crate) fn default_unit_for(ty: BitType) -> u32 {
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
// fadd/fsub/fmul/fdiv when the result can stay RawF64. Typed float-float
// and typed int-int fast paths sit in front of the dispatch entirely.
// Eq/Neq do NOT promote: `1 == 1.0` is false.
