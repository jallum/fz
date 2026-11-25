//! Compiler2 native codegen support constants and small scans.

use super::recipe::{REUSE_REF_HEAD, emit_reuse};
use super::*;
use crate::ast::Endian;
use crate::fast_hash::HashMap;
use crate::fz_ir::Var;
use crate::types::Types;
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use cranelift_module::Module;
use fz_runtime::any_value::{FALSE_BITS as FALSE_BITS_RAW, TRUE_BITS as TRUE_BITS_RAW, ValueKind};
use fz_runtime::ir_runtime::fz_list_reuse_or_cons_parts;

pub(crate) const SLOT_BYTES: i32 = 8;

/// The tail of a list under construction. A tail whose type is a list, proper
/// or not, is linked by the cell itself; any other is `Checked`, and the
/// runtime links it or ends the list in it.
#[derive(Clone, Copy)]
pub(crate) enum ListTailBits {
    Empty,
    ValueRef(ir::Value),
    NonEmptyValueRef(ir::Value),
    Checked(CodegenValue),
}

impl ListTailBits {
    /// Whether the tail is known to be a list, so a cell may be written
    /// inline with no runtime check of what follows it.
    pub(crate) fn is_list(self) -> bool {
        !matches!(self, Self::Checked(_))
    }
}

pub(crate) fn list_tail_bits_for_var<T: Types<Ty = Ty>, M: Module>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    tail_var: Var,
) -> ListTailBits {
    if ty_is_non_empty_list(t, value_types, tail_var) {
        ListTailBits::NonEmptyValueRef(body.any_ref_for_var(var_env, tail_var.0))
    } else if ty_is_any_list(t, value_types, tail_var) {
        ListTailBits::ValueRef(body.any_ref_for_var(var_env, tail_var.0))
    } else {
        ListTailBits::Checked(binding_for_var(var_env, tail_var.0))
    }
}

pub(crate) fn emit_list_retention_or_alloc<M: Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    head: Var,
    tail: ListTailBits,
    retention: crate::fz_ir::ListRetention<Var>,
) -> Option<ir::Value> {
    let source_cons = retention.source;
    let source_ref = body.any_ref_for_var(var_env, source_cons.0);
    let head_value = binding_for_var(var_env, head.0);
    let [tail_word, tail_kind] = body.list_tail_words(tail);
    let rewrite = body.b.ins().iconst(
        types::I64,
        i64::from(retention.permission == crate::fz_ir::RewritePermission::Rewrite),
    );
    let process = body.process_arg();
    if tail.is_list()
        && let CodegenValue::AnyRef(head_ref) = head_value
    {
        return Some(emit_reuse(
            body,
            REUSE_REF_HEAD,
            &[process, source_ref, head_ref, tail_word, tail_kind, rewrite],
        ));
    }
    let (head_raw, head_kind) = match value_raw_kind_parts(body, head_value) {
        Some((raw, kind)) => (raw, body.b.ins().iconst(types::I64, i64::from(kind.tag()))),
        None if !tail.is_list() => {
            let head_ref = body.value_as_any_ref(head_value);
            let [raw, kind] = super::list_cell::stored_parts_of_ref(body.b, head_ref);
            (raw, kind)
        }
        None => return None,
    };
    let args = [process, source_ref, head_raw, head_kind, tail_word, tail_kind, rewrite];
    if tail.is_list() {
        return Some(emit_reuse(body, "fz_list_reuse_or_cons_parts", &args));
    }
    let reuse: unsafe extern "C" fn(_, _, _, _, _, _, _) -> _ = fz_list_reuse_or_cons_parts;
    let call = body.call_runtime("fz_list_reuse_or_cons_parts", reuse, &args);
    Some(body.sole_result(call))
}

pub(crate) fn value_raw_kind_parts<M: Module>(
    body: &mut CodegenFn<'_, '_, M>,
    value: CodegenValue,
) -> Option<(ir::Value, ValueKind)> {
    match value {
        CodegenValue::RawInt(raw)
        | CodegenValue::Known {
            payload: raw,
            kind: ValueKind::INT,
        } => Some((raw, ValueKind::INT)),
        CodegenValue::RawAtom(raw)
        | CodegenValue::Known {
            payload: raw,
            kind: ValueKind::ATOM,
        } => Some((raw, ValueKind::ATOM)),
        CodegenValue::RawF64(raw) => {
            let bits = body.b.ins().bitcast(types::I64, MemFlagsData::new(), raw);
            Some((bits, ValueKind::FLOAT))
        }
        CodegenValue::Known {
            payload,
            kind: ValueKind::FLOAT,
        } => Some((payload, ValueKind::FLOAT)),
        CodegenValue::Known { payload, kind } if kind.is_heap() || kind == ValueKind::LIST => Some((payload, kind)),
        _ => None,
    }
}

/// The word a container stores for `value` and its kind, as two `I64`s. A
/// value whose kind codegen knows gives its word and a constant kind; any
/// other is read through its reference.
pub(crate) fn stored_parts<M: Module>(body: &mut CodegenFn<'_, '_, M>, value: CodegenValue) -> [ir::Value; 2] {
    if let Some((word, kind)) = value_raw_kind_parts(body, value) {
        return [word, body.b.ins().iconst(types::I64, i64::from(kind.tag()))];
    }
    let reference = body.value_as_any_ref(value);
    super::list_cell::stored_parts_of_ref(body.b, reference)
}

pub(crate) const TRUE_BITS: i64 = TRUE_BITS_RAW as i64;
pub(crate) const FALSE_BITS: i64 = FALSE_BITS_RAW as i64;

// ----- Map runtime fns -----
//
// Maps use an immutable heap-backed sorted array. Construction fills unpublished
// slots once, then normalizes them with the runtime's strict structural order.
// Later put/delete operations preserve that order in the returned allocation.

// ----- Bitstring runtime fns -----
//
// A construction stores one `FzBsField` descriptor per segment in a stack
// slot and makes one `fz_bs_build` call, which sizes the result, allocates it
// and writes every segment.
//
// A match reads the binary it is matching at a bit position the compiled code
// carries as an integer: `BitFieldFits` and `BitFieldNext` are arithmetic on
// that position, and `BitReadField` takes the source binary and the position.
// A match allocates nothing but the binaries its fields extract.

pub(crate) fn encode_endian(e: Endian) -> u32 {
    match e {
        Endian::Big => 0,
        Endian::Little => 1,
        Endian::Native => 2,
    }
}

// ----- Float runtime fns -----
//
// Codegen keeps new float values in RawF64 or side-tagged container slots.
//
// Arithmetic dispatch: codegen emits an inline both-int fast-path test
// (`((a^1) | (b^1)) & 7 == 0`); when at least one operand is non-Int the
// slow arm promotes both to f64 and emits native fadd/fsub/fmul/fdiv when the
// result can stay RawF64. Typed float-float and typed int-int fast paths sit in
// front of the dispatch entirely.
//
// Comparison does NOT share this path: `Kernel` gives each comparison operator
// a clause per operand pair, and the dynamic remainder asks fz_value_cmp_ref.
// `==` widens numerics (`1 == 1.0` is true, and recursively so for containers);
// structural identity -- a pinned match, `Enum.member?/2`, `--`, a map key --
// stays strict and uses fz_value_eq_ref.
