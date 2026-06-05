//! Codegen value representations and coercion helpers.

use super::*;
use crate::fz_ir::{BlockId, Var};
use crate::ir_planner::SpecPlan;
use crate::types::{Ty, Types};
use cranelift_codegen::ir::{self, InstBuilder, MemFlags, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::Module;
use fz_runtime::any_value::{AnyValue, AnyValueRef, FALSE_ATOM_ID, TRUE_ATOM_ID, ValueKind};
use std::collections::HashMap;

/// Output of `lower_prim`. Generic values leave primitives as high-bit
/// `AnyValueRef` words; typed fast paths can stay raw when the typer proves
/// the lane is narrower than `any`.
pub(crate) enum LowerOut {
    ValueRef(ir::Value),
    ValueRefWord(ir::Value),
    Strict(CodegenValue),
    StrictConst(AnyValue),
    RawF64(ir::Value),
    RawI64(ir::Value),
    /// Unit-return extern whose dest var is dead — no CLIF value emitted.
    DeadUnit,
    /// Raw i1 from a boolean prim whose var is in `if_only_conds`; tagged form is
    /// never materialised unless tagged_get is called, which emits bool_to_fz lazily
    /// at the use site.
    Condition(ir::Value),
}

impl LowerOut {
    pub(crate) fn value(&self) -> ir::Value {
        match self {
            LowerOut::ValueRef(v)
            | LowerOut::ValueRefWord(v)
            | LowerOut::RawF64(v)
            | LowerOut::RawI64(v)
            | LowerOut::Condition(v) => *v,
            LowerOut::Strict(v) => v.value(),
            LowerOut::StrictConst(_) | LowerOut::DeadUnit => {
                panic!("literal-only LowerOut has no ir::Value")
            }
        }
    }
    pub(crate) fn is_raw_f64(&self) -> bool {
        matches!(self, LowerOut::RawF64(_))
    }
    pub(crate) fn is_raw_i64(&self) -> bool {
        matches!(self, LowerOut::RawI64(_))
    }
    pub(crate) fn is_condition(&self) -> bool {
        matches!(self, LowerOut::Condition(_))
    }
}

pub(crate) fn strict_const_value(b: &mut FunctionBuilder<'_>, value: AnyValue) -> CodegenValue {
    CodegenValue::known(b.ins().iconst(types::I64, value.raw() as i64), value.kind())
}

#[derive(Clone, Copy)]
pub(crate) enum ClosureCapture {
    RefWord(ir::Value),
    RawInt(ir::Value),
    RawF64(ir::Value),
    RawAtom(ir::Value),
}

pub(crate) fn closure_capture_for_var<M: Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    v: u32,
) -> ClosureCapture {
    match *var_env.get(&v).expect("unbound closure capture var") {
        CodegenValue::RawInt(value) => {
            let raw = if let Some(&n) = body.cache.raw_int_consts.get(&v) {
                cached_iconst(body.b, body.cache, n)
            } else {
                value
            };
            ClosureCapture::RawInt(raw)
        }
        CodegenValue::RawF64(value) => ClosureCapture::RawF64(value),
        CodegenValue::RawAtom(value) => ClosureCapture::RawAtom(value),
        CodegenValue::Known { payload, kind } if kind == ValueKind::INT => ClosureCapture::RawInt(payload),
        CodegenValue::Known { payload, kind } if kind == ValueKind::FLOAT => {
            let raw = body.b.ins().bitcast(types::F64, MemFlags::new(), payload);
            ClosureCapture::RawF64(raw)
        }
        CodegenValue::Known { payload, kind } if kind == ValueKind::ATOM => ClosureCapture::RawAtom(payload),
        _ => {
            let value_ref = body.tagged_var(var_env, v);
            ClosureCapture::RefWord(value_ref)
        }
    }
}

pub(crate) fn closure_capture_for_var_as<M: Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    v: u32,
    repr: ArgRepr,
) -> ClosureCapture {
    let binding = *var_env.get(&v).expect("unbound closure capture var");
    match repr {
        ArgRepr::RawInt => ClosureCapture::RawInt(body.coerce_binding_to(binding, repr)),
        ArgRepr::RawF64 => ClosureCapture::RawF64(body.coerce_binding_to(binding, repr)),
        ArgRepr::RawAtom => ClosureCapture::RawAtom(body.coerce_binding_to(binding, repr)),
        ArgRepr::ValueRef => ClosureCapture::RefWord(body.tagged_var(var_env, v)),
        ArgRepr::Condition => unreachable!("closure captures are never condition-only"),
    }
}

pub(crate) fn emit_empty_list_value_ref_word(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache) -> ir::Value {
    let word = AnyValueRef::empty_list().raw_word();
    cached_iconst(b, cache, word as i64)
}

pub(crate) fn strict_bool(b: &mut FunctionBuilder<'_>, value: ir::Value) -> CodegenValue {
    let true_raw = b.ins().iconst(types::I64, TRUE_ATOM_ID as i64);
    let false_raw = b.ins().iconst(types::I64, FALSE_ATOM_ID as i64);
    CodegenValue::known(b.ins().select(value, true_raw, false_raw), ValueKind::ATOM)
}

pub(crate) fn binding_for_var(var_env: &HashMap<u32, CodegenValue>, v: u32) -> CodegenValue {
    *var_env.get(&v).expect("unbound var")
}

pub(crate) fn expected_runtime_value_kind<T: Types<Ty = Ty>>(
    t: &mut T,
    fn_types: &SpecPlan,
    block_env: Option<&HashMap<Var, Ty>>,
    v: Var,
) -> Option<ValueKind> {
    if ty_is_int(t, fn_types, v) {
        Some(ValueKind::INT)
    } else if ty_is_float(t, fn_types, v) {
        Some(ValueKind::FLOAT)
    } else if ty_is_atom(t, fn_types, v) {
        Some(ValueKind::ATOM)
    } else if ty_is_list(t, fn_types, v)
        || ty_is_empty_list_in_context(t, fn_types, v, block_env)
        || ty_is_non_empty_list_in_context(t, fn_types, v, block_env)
    {
        Some(ValueKind::LIST)
    } else if ty_is_map(t, fn_types, v) {
        Some(ValueKind::MAP)
    } else if ty_has_tuple(t, fn_types, v) {
        Some(ValueKind::STRUCT)
    } else {
        None
    }
}

pub(crate) fn known_list_ref_for_var(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    cache: &mut CodegenCache,
    block_id: BlockId,
    v: u32,
) -> ir::Value {
    let key = (block_id, v);
    if let Some(&list_ref) = cache.known_list_refs.get(&key) {
        return list_ref;
    }
    if let Some(CodegenValue::AnyRef(value)) = var_env.get(&v).copied() {
        cache.known_list_refs.insert(key, value);
        return value;
    }
    let Some(CodegenValue::Known {
        kind: ValueKind::LIST, ..
    }) = var_env.get(&v).copied()
    else {
        panic!("known_list_ref_for_var requires a list ref");
    };
    let list_ref = emit_empty_list_value_ref_word(b, cache);
    cache.known_list_refs.insert(key, list_ref);
    list_ref
}

#[derive(Clone, Copy)]
pub(crate) enum CodegenValue {
    AnyRef(ir::Value),
    Known { payload: ir::Value, kind: ValueKind },
    RawInt(ir::Value),
    RawF64(ir::Value),
    RawAtom(ir::Value),
    Condition(ir::Value),
}

impl CodegenValue {
    pub(crate) fn from_abi_value(value: ir::Value, repr: ArgRepr) -> Self {
        match repr {
            ArgRepr::ValueRef => Self::AnyRef(value),
            ArgRepr::RawInt => Self::RawInt(value),
            ArgRepr::RawF64 => Self::RawF64(value),
            ArgRepr::RawAtom => Self::RawAtom(value),
            ArgRepr::Condition => Self::Condition(value),
        }
    }

    pub(crate) fn known(payload: ir::Value, kind: ValueKind) -> Self {
        Self::Known { payload, kind }
    }

    pub(crate) fn any_ref(value: ir::Value) -> Self {
        Self::AnyRef(value)
    }

    pub(crate) fn value(self) -> ir::Value {
        match self {
            Self::AnyRef(value)
            | Self::RawInt(value)
            | Self::RawF64(value)
            | Self::RawAtom(value)
            | Self::Condition(value)
            | Self::Known { payload: value, .. } => value,
        }
    }

    pub(crate) fn repr(self) -> ArgRepr {
        match self {
            Self::AnyRef(_) | Self::Known { .. } => ArgRepr::ValueRef,
            Self::RawInt(_) => ArgRepr::RawInt,
            Self::RawF64(_) => ArgRepr::RawF64,
            Self::RawAtom(_) => ArgRepr::RawAtom,
            Self::Condition(_) => ArgRepr::Condition,
        }
    }
}

pub(crate) fn known_kind_ref_tag(b: &mut FunctionBuilder<'_>, _payload: ir::Value, kind: ValueKind) -> ir::Value {
    b.ins().iconst(types::I8, kind.tag() as i64)
}

/// Check if both BinOp args have narrow typed types and, if so, apply
/// the matching fast-path closure. Returns Some(LowerOut) on a hit, None
/// to signal fall-through to the tagged slow path.
///
/// float_op / int_op each return Option<LowerOut> so callers can opt out
/// of a specific fast path (e.g. Mod has no float fast path → return None).
pub(crate) fn as_known_numeric_f64(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match vb.repr() {
        ArgRepr::RawF64 => vb.value(),
        ArgRepr::RawInt => b.ins().fcvt_from_sint(types::F64, vb.value()),
        ArgRepr::RawAtom => panic!("atom is not numeric"),
        ArgRepr::ValueRef => panic!("tagged numeric-to-f64 conversion has been retired"),
        ArgRepr::Condition => unreachable!("condition is not numeric"),
    }
}

pub(crate) fn fetch_static_closure<M: Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    spec_id: u32,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.get_static_closure_id, b.func);
    let process = b.ins().get_pinned_reg(types::I64);
    let sid_v = b.ins().iconst(types::I32, spec_id as i64);
    let inst = b.ins().call(fref, &[process, sid_v]);
    b.inst_results(inst)[0]
}

pub(crate) fn tagged_to_raw_f64_unsupported(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    let _ = (b, v);
    panic!("tagged float decoding has been retired")
}
