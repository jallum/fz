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
    /// Unit-return extern whose dest var is dead — no CLIF value emitted (fz-2tc).
    DeadUnit,
    /// Raw i1 from a boolean prim whose var is in `if_only_conds`; tagged form is
    /// never materialised unless tagged_get is called, which emits bool_to_fz lazily
    /// at the use site (fz-h4q).
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

pub(crate) fn unit_extern_result(
    b: &mut FunctionBuilder<'_>,
    cache: &CodegenCache,
    dest_var: crate::fz_ir::Var,
) -> LowerOut {
    if cache.used_vars.contains(&dest_var.0) {
        LowerOut::Strict(strict_const_value(
            b,
            fz_runtime::any_value::AnyValue::nil_atom(),
        ))
    } else {
        LowerOut::DeadUnit
    }
}

#[derive(Clone, Copy)]
pub(crate) enum ClosureCapture {
    RefWord(ir::Value),
    RawInt(ir::Value),
    RawF64(ir::Value),
}

pub(crate) fn closure_capture_for_var<M: cranelift_module::Module>(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    v: u32,
    cache: &mut CodegenCache,
) -> ClosureCapture {
    match *var_env.get(&v).expect("unbound closure capture var") {
        CodegenValue::RawInt(value) => {
            let raw = if let Some(&n) = cache.raw_int_consts.get(&v) {
                cached_iconst(b, cache, n)
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
            let raw = b.ins().bitcast(types::F64, MemFlags::new(), payload);
            ClosureCapture::RawF64(raw)
        }
        _ => {
            let value_ref = tagged_get(var_env, b, jmod, runtime, v, cache);
            ClosureCapture::RefWord(value_ref)
        }
    }
}

pub(crate) fn box_known_non_heap_as_any_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    raw: ir::Value,
    kind: fz_runtime::any_value::ValueKind,
) -> ir::Value {
    if kind == fz_runtime::any_value::ValueKind::INT {
        return emit_raw_int_as_abi_value_ref(b, jmod, runtime, raw);
    }
    if kind == fz_runtime::any_value::ValueKind::FLOAT {
        let raw = b.ins().bitcast(types::F64, MemFlags::new(), raw);
        return emit_raw_float_as_abi_value_ref(b, jmod, runtime, raw);
    }
    if kind == fz_runtime::any_value::ValueKind::ATOM {
        return emit_raw_atom_as_abi_value_ref(b, jmod, runtime, raw);
    }
    if kind == fz_runtime::any_value::ValueKind::NULL {
        return b.ins().iconst(types::I64, 0);
    }
    if kind == fz_runtime::any_value::ValueKind::LIST {
        let _ = raw;
        let word = fz_runtime::any_value::AnyValueRef::empty_list().raw_word();
        return b.ins().iconst(types::I64, word as i64);
    }
    unreachable!("heap refs must stay as CodegenValue::AnyRef")
}

pub(crate) fn emit_raw_int_as_abi_value_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    raw: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.box_int_for_any_id, b.func);
    let inst = b.ins().call(fref, &[raw]);
    b.inst_results(inst)[0]
}

pub(crate) fn emit_raw_float_as_abi_value_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    raw: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.box_float_for_any_id, b.func);
    let inst = b.ins().call(fref, &[raw]);
    b.inst_results(inst)[0]
}

pub(crate) fn emit_raw_atom_as_abi_value_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    raw: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.box_atom_for_any_id, b.func);
    let inst = b.ins().call(fref, &[raw]);
    b.inst_results(inst)[0]
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
    fn_types: &crate::ir_typer::FnTypes,
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

pub(crate) fn known_list_ref_for_var<M: cranelift_module::Module>(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    _jmod: &mut M,
    _runtime: &RuntimeRefs,
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

/// Materialize a local value as an ABI `AnyValueRef` word.
pub(crate) fn tagged_get<M: cranelift_module::Module>(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    v: u32,
    cache: &mut CodegenCache,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match *vb {
        CodegenValue::RawF64(value) => emit_raw_float_as_abi_value_ref(b, jmod, runtime, value),
        CodegenValue::RawInt(value) => {
            let raw = if let Some(&n) = cache.raw_int_consts.get(&v) {
                cached_iconst(b, cache, n)
            } else {
                value
            };
            emit_raw_int_as_abi_value_ref(b, jmod, runtime, raw)
        }
        CodegenValue::Known { payload, kind } => {
            box_known_non_heap_as_any_ref(b, jmod, runtime, payload, kind)
        }
        CodegenValue::AnyRef(value) => value,
        CodegenValue::Condition(value) => {
            let atom = bool_to_fz(b, cache, value);
            emit_raw_atom_as_abi_value_ref(b, jmod, runtime, atom)
        }
    }
}

pub(crate) fn codegen_value_as_any_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    value: CodegenValue,
) -> ir::Value {
    match value {
        CodegenValue::AnyRef(value) => value,
        CodegenValue::RawInt(value) => emit_raw_int_as_abi_value_ref(b, jmod, runtime, value),
        CodegenValue::RawF64(value) => emit_raw_float_as_abi_value_ref(b, jmod, runtime, value),
        CodegenValue::Condition(value) => {
            let atom = bool_to_fz(b, cache, value);
            emit_raw_atom_as_abi_value_ref(b, jmod, runtime, atom)
        }
        CodegenValue::Known { payload, kind } => {
            box_known_non_heap_as_any_ref(b, jmod, runtime, payload, kind)
        }
    }
}

pub(crate) fn emit_ref_tag<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value_ref: ir::Value,
) -> ir::Value {
    let fref = jmod.declare_func_in_func(runtime.type_of_id, b.func);
    let inst = b.ins().call(fref, &[value_ref]);
    b.inst_results(inst)[0]
}

pub(crate) fn codegen_value_truthy<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: CodegenValue,
) -> ir::Value {
    match value {
        CodegenValue::Condition(value) => value,
        CodegenValue::RawInt(_) | CodegenValue::RawF64(_) => b.ins().iconst(types::I8, 1),
        CodegenValue::Known {
            kind: fz_runtime::any_value::ValueKind::NULL,
            ..
        } => b.ins().iconst(types::I8, 0),
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        } => {
            let is_false = b.ins().icmp_imm(
                IntCC::Equal,
                payload,
                fz_runtime::any_value::FALSE_ATOM_ID as i64,
            );
            let is_nil = b.ins().icmp_imm(
                IntCC::Equal,
                payload,
                fz_runtime::any_value::NIL_ATOM_ID as i64,
            );
            let falsey = b.ins().bor(is_false, is_nil);
            b.ins().bxor_imm(falsey, 1)
        }
        CodegenValue::Known { .. } => b.ins().iconst(types::I8, 1),
        CodegenValue::AnyRef(value_ref) => {
            let fref = jmod.declare_func_in_func(runtime.truthy_ref_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            b.inst_results(inst)[0]
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

pub(crate) fn codegen_value_type_tag<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: CodegenValue,
) -> ir::Value {
    use fz_runtime::any_value::ValueKind;
    match value {
        CodegenValue::AnyRef(value_ref) => emit_ref_tag(b, jmod, runtime, value_ref),
        CodegenValue::RawInt(_) => b.ins().iconst(types::I8, ValueKind::INT.tag() as i64),
        CodegenValue::RawF64(_) => b.ins().iconst(types::I8, ValueKind::FLOAT.tag() as i64),
        CodegenValue::Condition(_) => b.ins().iconst(types::I8, ValueKind::ATOM.tag() as i64),
        CodegenValue::Known { payload, kind } => known_kind_ref_tag(b, payload, kind),
    }
}

pub(crate) fn codegen_value_is_tag<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: CodegenValue,
    tag: fz_runtime::any_value::ValueKind,
) -> ir::Value {
    let actual = codegen_value_type_tag(b, jmod, runtime, value);
    b.ins().icmp_imm(IntCC::Equal, actual, tag.tag() as i64)
}

pub(crate) fn codegen_value_atom_id_is<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: CodegenValue,
    atom_id: u32,
) -> ir::Value {
    use fz_runtime::any_value::ValueKind;

    match value {
        CodegenValue::Condition(flag) => {
            if atom_id == fz_runtime::any_value::TRUE_ATOM_ID {
                return flag;
            }
            if atom_id == fz_runtime::any_value::FALSE_ATOM_ID {
                return b.ins().bxor_imm(flag, 1);
            }
            b.ins().iconst(types::I8, 0)
        }
        CodegenValue::RawInt(_) | CodegenValue::RawF64(_) => b.ins().iconst(types::I8, 0),
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        } => b.ins().icmp_imm(IntCC::Equal, payload, atom_id as i64),
        CodegenValue::Known { .. } => b.ins().iconst(types::I8, 0),
        CodegenValue::AnyRef(value_ref) => {
            let is_atom = codegen_value_is_tag(b, jmod, runtime, value, ValueKind::ATOM);
            let atom_blk = b.create_block();
            let join_blk = b.create_block();
            b.append_block_param(join_blk, types::I8);
            let false8 = b.ins().iconst(types::I8, 0);
            let no_args: Vec<BlockArg> = Vec::new();
            b.ins().brif(
                is_atom,
                atom_blk,
                &no_args,
                join_blk,
                &[BlockArg::Value(false8)],
            );

            b.switch_to_block(atom_blk);
            b.seal_block(atom_blk);
            let fref = jmod.declare_func_in_func(runtime.unbox_atom_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            let atom = b.inst_results(inst)[0];
            let found = b.ins().icmp_imm(IntCC::Equal, atom, atom_id as i64);
            b.ins().jump(join_blk, &[BlockArg::Value(found)]);

            b.switch_to_block(join_blk);
            b.seal_block(join_blk);
            b.block_params(join_blk)[0]
        }
    }
}

pub(crate) fn codegen_value_raw_int<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: CodegenValue,
) -> ir::Value {
    match value {
        CodegenValue::RawInt(value) => value,
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::INT,
        } => payload,
        CodegenValue::AnyRef(value_ref) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_int_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            b.inst_results(inst)[0]
        }
        _ => panic!("CodegenValue is not an int"),
    }
}

pub(crate) fn codegen_value_raw_float<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: CodegenValue,
) -> ir::Value {
    match value {
        CodegenValue::RawF64(value) => value,
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::FLOAT,
        } => b.ins().bitcast(types::F64, MemFlags::new(), payload),
        CodegenValue::AnyRef(value_ref) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_float_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            b.inst_results(inst)[0]
        }
        _ => panic!("CodegenValue is not a float"),
    }
}

pub(crate) fn codegen_value_raw_atom<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    value: CodegenValue,
) -> ir::Value {
    match value {
        CodegenValue::Condition(flag) => bool_to_fz(b, cache, flag),
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        } => payload,
        CodegenValue::AnyRef(value_ref) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_atom_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            b.inst_results(inst)[0]
        }
        _ => panic!("CodegenValue is not an atom"),
    }
}

pub(crate) fn any_ref_for_var<M: cranelift_module::Module>(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    v: u32,
    cache: &mut CodegenCache,
) -> ir::Value {
    let binding = *var_env.get(&v).expect("unbound var");
    codegen_value_as_any_ref(b, jmod, runtime, cache, binding)
}

/// Check if both BinOp args have narrow typed types and, if so, apply
/// the matching fast-path closure. Returns Some(LowerOut) on a hit, None
/// to signal fall-through to the tagged slow path.
///
/// float_op / int_op each return Option<LowerOut> so callers can opt out
/// of a specific fast path (e.g. Mod has no float fast path → return None).
pub(crate) fn try_typed_binop_fast_path<T, F, I, M>(
    t: &mut T,
    fn_types: &crate::ir_typer::FnTypes,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
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
        let af = as_raw_f64(var_env, b, jmod, runtime, a.0);
        let bf = as_raw_f64(var_env, b, jmod, runtime, bv.0);
        if let Some(out) = float_op(b, af, bf) {
            return Some(out);
        }
    }
    if ty_is_int(t, fn_types, a) && ty_is_int(t, fn_types, bv) {
        let ai = as_raw_i64(var_env, b, jmod, runtime, a.0);
        let bi = as_raw_i64(var_env, b, jmod, runtime, bv.0);
        if let Some(out) = int_op(b, ai, bi) {
            return Some(out);
        }
    }
    None
}

pub(crate) fn as_raw_f64(
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    runtime: &RuntimeRefs,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match *vb {
        CodegenValue::RawF64(value) => value,
        CodegenValue::Known { payload, .. } => {
            b.ins().bitcast(types::F64, MemFlags::new(), payload)
        }
        CodegenValue::AnyRef(value_ref) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_float_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            b.inst_results(inst)[0]
        }
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
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut impl cranelift_module::Module,
    runtime: &RuntimeRefs,
    v: u32,
) -> ir::Value {
    let vb = var_env.get(&v).expect("unbound var");
    match *vb {
        CodegenValue::RawInt(value) => value,
        CodegenValue::Known { payload, .. } => payload,
        CodegenValue::AnyRef(value_ref) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_int_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            b.inst_results(inst)[0]
        }
        _ => panic!("cannot read raw i64 from non-integer value"),
    }
}

/// fz-ul4.27.13 — Coerce a Cranelift value between ArgReprs. `RawInt` ↔
/// `RawF64` direct conversion is intentionally unsupported (no type admits
/// both; if it surfaces, the typer or call-site narrowing is wrong).
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

pub(crate) fn coerce_call_args<M: cranelift_module::Module>(
    args: &[crate::fz_ir::Var],
    callee_param_reprs: &[ArgRepr],
    var_env: &HashMap<u32, CodegenValue>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
) -> Vec<ir::Value> {
    let mut out: Vec<ir::Value> = Vec::with_capacity(args.len() + 1);
    for (i, av) in args.iter().enumerate() {
        let binding = *var_env.get(&av.0).expect("unbound call arg");
        let to = callee_param_reprs[i];
        push_binding_as_abi_args(&mut out, b, jmod, runtime, cache, binding, to);
    }
    out
}

pub(crate) fn push_binding_as_abi_args<M: cranelift_module::Module>(
    out: &mut Vec<ir::Value>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    binding: CodegenValue,
    to: ArgRepr,
) {
    if to == ArgRepr::ValueRef {
        out.push(match binding {
            CodegenValue::RawInt(value) => emit_raw_int_as_abi_value_ref(b, jmod, runtime, value),
            CodegenValue::RawF64(value) => emit_raw_float_as_abi_value_ref(b, jmod, runtime, value),
            CodegenValue::Condition(value) => {
                let atom = bool_to_fz(b, cache, value);
                emit_raw_atom_as_abi_value_ref(b, jmod, runtime, atom)
            }
            CodegenValue::AnyRef(value) => value,
            CodegenValue::Known { payload, kind } => {
                box_known_non_heap_as_any_ref(b, jmod, runtime, payload, kind)
            }
        });
    } else {
        out.push(coerce_binding_to(b, jmod, runtime, binding, to));
    }
}

pub(crate) fn coerce_binding_to<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    binding: CodegenValue,
    to: ArgRepr,
) -> ir::Value {
    match (binding, to) {
        (CodegenValue::Known { payload, kind }, ArgRepr::ValueRef) => {
            box_known_non_heap_as_any_ref(b, jmod, runtime, payload, kind)
        }
        (CodegenValue::Known { payload, .. }, ArgRepr::RawInt) => payload,
        (CodegenValue::Known { payload, .. }, ArgRepr::RawF64) => {
            b.ins().bitcast(types::F64, MemFlags::new(), payload)
        }
        (CodegenValue::Known { .. }, ArgRepr::Condition) => {
            unreachable!("condition is never a callee ABI target")
        }
        (CodegenValue::AnyRef(value), ArgRepr::ValueRef) => value,
        (CodegenValue::AnyRef(value), ArgRepr::RawInt) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_int_id, b.func);
            let inst = b.ins().call(fref, &[value]);
            b.inst_results(inst)[0]
        }
        (CodegenValue::AnyRef(value), ArgRepr::RawF64) => {
            let fref = jmod.declare_func_in_func(runtime.unbox_float_id, b.func);
            let inst = b.ins().call(fref, &[value]);
            b.inst_results(inst)[0]
        }
        (CodegenValue::AnyRef(_), ArgRepr::Condition) => {
            unreachable!("condition is never a callee ABI target")
        }
        (CodegenValue::RawInt(value), ArgRepr::ValueRef) => {
            emit_raw_int_as_abi_value_ref(b, jmod, runtime, value)
        }
        (CodegenValue::RawF64(value), ArgRepr::ValueRef) => {
            emit_raw_float_as_abi_value_ref(b, jmod, runtime, value)
        }
        (CodegenValue::Condition(value), ArgRepr::ValueRef) => {
            let true_v = b
                .ins()
                .iconst(types::I64, fz_runtime::any_value::TRUE_BITS as i64);
            let false_v = b
                .ins()
                .iconst(types::I64, fz_runtime::any_value::FALSE_BITS as i64);
            let atom = b.ins().select(value, true_v, false_v);
            emit_raw_atom_as_abi_value_ref(b, jmod, runtime, atom)
        }
        (binding, to) => {
            if binding.repr() == to {
                binding.value()
            } else {
                coerce_to(b, jmod, runtime, binding.value(), binding.repr(), to)
            }
        }
    }
}

pub(crate) fn push_repr_arg<M: cranelift_module::Module>(
    out: &mut Vec<ir::Value>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    value: ir::Value,
    from: ArgRepr,
    to: ArgRepr,
) {
    out.push(coerce_to(b, jmod, runtime, value, from, to));
}

pub(crate) fn coerce_to<M: cranelift_module::Module>(
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
        (ArgRepr::ValueRef, ArgRepr::RawInt) => val,
        (ArgRepr::ValueRef, ArgRepr::RawF64) => tagged_to_raw_f64_unsupported(b, val),
        (ArgRepr::RawInt, ArgRepr::ValueRef) => {
            emit_raw_int_as_abi_value_ref(b, jmod, runtime, val)
        }
        (ArgRepr::RawF64, ArgRepr::ValueRef) => {
            emit_raw_float_as_abi_value_ref(b, jmod, runtime, val)
        }
        (ArgRepr::RawInt, ArgRepr::RawF64) => b.ins().fcvt_from_sint(types::F64, val),
        (ArgRepr::RawF64, ArgRepr::RawInt) => b.ins().fcvt_to_sint(types::I64, val),
        (ArgRepr::Condition, _) | (_, ArgRepr::Condition) => {
            unreachable!("Condition vars are never coerced")
        }
        (ArgRepr::ValueRef, ArgRepr::ValueRef)
        | (ArgRepr::RawInt, ArgRepr::RawInt)
        | (ArgRepr::RawF64, ArgRepr::RawF64) => {
            unreachable!("same-repr coerce: handled by early return")
        }
    }
}

pub(crate) fn tagged_to_raw_f64_unsupported(
    b: &mut FunctionBuilder<'_>,
    v: ir::Value,
) -> ir::Value {
    let _ = (b, v);
    panic!("tagged float decoding has been retired")
}
