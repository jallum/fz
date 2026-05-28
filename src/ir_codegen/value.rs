//! Codegen value representations and coercion helpers.

use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use std::collections::HashMap;

/// Output of `lower_prim`. Generic values leave primitives as high-bit
/// `AnyValueRef` words; typed fast paths can stay raw when the typer proves
/// the lane is narrower than `any`.
pub(crate) enum LowerOut {
    ValueRef(ir::Value),
    ValueRefWord(ir::Value),
    Strict(CodegenValue),
    StrictConst(fz_runtime::any_value::AnyValue),
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

pub(crate) fn strict_const_value(
    b: &mut FunctionBuilder<'_>,
    value: fz_runtime::any_value::AnyValue,
) -> CodegenValue {
    CodegenValue::known(b.ins().iconst(types::I64, value.raw() as i64), value.kind())
}

#[derive(Clone, Copy)]
pub(crate) enum ClosureCapture {
    RefWord(ir::Value),
    RawInt(ir::Value),
    RawF64(ir::Value),
}

pub(crate) fn closure_capture_for_var<M: cranelift_module::Module>(
    body: &mut CodegenFnBody<'_, '_, '_, M>,
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
        CodegenValue::Known { payload, kind } if kind == fz_runtime::any_value::ValueKind::INT => {
            ClosureCapture::RawInt(payload)
        }
        CodegenValue::Known { payload, kind }
            if kind == fz_runtime::any_value::ValueKind::FLOAT =>
        {
            let raw = body.b.ins().bitcast(types::F64, MemFlags::new(), payload);
            ClosureCapture::RawF64(raw)
        }
        _ => {
            let value_ref = body.tagged_var(var_env, v);
            ClosureCapture::RefWord(value_ref)
        }
    }
}

pub(crate) fn emit_empty_list_value_ref_word(
    b: &mut FunctionBuilder<'_>,
    cache: &mut CodegenCache,
) -> ir::Value {
    let word = fz_runtime::any_value::AnyValueRef::empty_list().raw_word();
    cached_iconst(b, cache, word as i64)
}

pub(crate) fn strict_bool(b: &mut FunctionBuilder<'_>, value: ir::Value) -> CodegenValue {
    let true_raw = b
        .ins()
        .iconst(types::I64, fz_runtime::any_value::TRUE_ATOM_ID as i64);
    let false_raw = b
        .ins()
        .iconst(types::I64, fz_runtime::any_value::FALSE_ATOM_ID as i64);
    CodegenValue::known(
        b.ins().select(value, true_raw, false_raw),
        fz_runtime::any_value::ValueKind::ATOM,
    )
}

pub(crate) fn binding_for_var(var_env: &HashMap<u32, CodegenValue>, v: u32) -> CodegenValue {
    *var_env.get(&v).expect("unbound var")
}

pub(crate) fn expected_runtime_value_kind<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
    v: crate::fz_ir::Var,
) -> Option<fz_runtime::any_value::ValueKind> {
    use fz_runtime::any_value::ValueKind;
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
    block_id: crate::fz_ir::BlockId,
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
        kind: fz_runtime::any_value::ValueKind::LIST,
        ..
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
    Known {
        payload: ir::Value,
        kind: fz_runtime::any_value::ValueKind,
    },
    RawInt(ir::Value),
    RawF64(ir::Value),
    Condition(ir::Value),
}

impl CodegenValue {
    pub(crate) fn from_abi_value(value: ir::Value, repr: ArgRepr) -> Self {
        match repr {
            ArgRepr::ValueRef => Self::AnyRef(value),
            ArgRepr::RawInt => Self::RawInt(value),
            ArgRepr::RawF64 => Self::RawF64(value),
            ArgRepr::Condition => Self::Condition(value),
        }
    }

    pub(crate) fn known(payload: ir::Value, kind: fz_runtime::any_value::ValueKind) -> Self {
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
            | Self::Condition(value)
            | Self::Known { payload: value, .. } => value,
        }
    }

    pub(crate) fn repr(self) -> ArgRepr {
        match self {
            Self::AnyRef(_) | Self::Known { .. } => ArgRepr::ValueRef,
            Self::RawInt(_) => ArgRepr::RawInt,
            Self::RawF64(_) => ArgRepr::RawF64,
            Self::Condition(_) => ArgRepr::Condition,
        }
    }

    pub(crate) fn known_kind(self) -> Option<fz_runtime::any_value::ValueKind> {
        match self {
            Self::Known { kind, .. } => Some(kind),
            _ => None,
        }
    }
}

pub(crate) fn known_kind_ref_tag(
    b: &mut FunctionBuilder<'_>,
    _payload: ir::Value,
    kind: fz_runtime::any_value::ValueKind,
) -> ir::Value {
    b.ins().iconst(types::I8, kind.tag() as i64)
}

/// Check if both BinOp args have narrow typed types and, if so, apply
/// the matching fast-path closure. Returns Some(LowerOut) on a hit, None
/// to signal fall-through to the tagged slow path.
///
/// float_op / int_op each return Option<LowerOut> so callers can opt out
/// of a specific fast path (e.g. Mod has no float fast path → return None).
pub(crate) fn try_typed_binop_fast_path<T, F, I, M>(
    cx: &mut CodegenFn<'_>,
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    var_env: &HashMap<u32, CodegenValue>,
    float_op: F,
    int_op: I,
) -> Option<LowerOut>
where
    T: crate::types::Types<Ty = crate::types::Ty>,
    M: cranelift_module::Module,
    F: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> Option<LowerOut>,
    I: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> Option<LowerOut>,
{
    if ty_is_float(t, fn_types, a) && ty_is_float(t, fn_types, bv) {
        let af = as_raw_f64(cx, var_env, b, jmod, a.0);
        let bf = as_raw_f64(cx, var_env, b, jmod, bv.0);
        if let Some(out) = float_op(b, af, bf) {
            return Some(out);
        }
    }
    if ty_is_int(t, fn_types, a) && ty_is_int(t, fn_types, bv) {
        let ai = as_raw_i64(cx, var_env, b, jmod, a.0);
        let bi = as_raw_i64(cx, var_env, b, jmod, bv.0);
        if let Some(out) = int_op(b, ai, bi) {
            return Some(out);
        }
    }
    None
}

pub(crate) fn as_raw_f64(
    cx: &mut CodegenFn<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match *vb {
        CodegenValue::RawF64(value) => value,
        CodegenValue::Known { payload, .. } => {
            b.ins().bitcast(types::F64, MemFlags::new(), payload)
        }
        CodegenValue::AnyRef(value_ref) => cx.site(b, jmod).unbox_float(value_ref),
        _ => tagged_to_raw_f64_unsupported(b, vb.value()),
    }
}

pub(crate) fn as_known_numeric_f64(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match vb.repr() {
        ArgRepr::RawF64 => vb.value(),
        ArgRepr::RawInt => b.ins().fcvt_from_sint(types::F64, vb.value()),
        ArgRepr::ValueRef => panic!("tagged numeric-to-f64 conversion has been retired"),
        ArgRepr::Condition => unreachable!("condition is not numeric"),
    }
}

pub(crate) fn as_raw_i64(
    cx: &mut CodegenFn<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match *vb {
        CodegenValue::RawInt(value) => value,
        CodegenValue::Known { payload, .. } => payload,
        CodegenValue::AnyRef(value_ref) => cx.site(b, jmod).unbox_int(value_ref),
        _ => panic!("cannot read raw i64 from non-integer value"),
    }
}

pub(crate) fn fetch_static_closure<M: cranelift_module::Module>(
    jmod: &mut M,
    b: &mut FunctionBuilder<'_>,
    runtime: &RuntimeRefs,
    spec_id: u32,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.get_static_closure_id, b.func);
    let sid_v = b.ins().iconst(types::I32, spec_id as i64);
    let inst = b.ins().call(fref, &[sid_v]);
    b.inst_results(inst)[0]
}

pub(crate) fn tagged_to_raw_f64_unsupported(
    b: &mut FunctionBuilder<'_>,
    v: ir::Value,
) -> ir::Value {
    let _ = (b, v);
    panic!("tagged float decoding has been retired")
}
