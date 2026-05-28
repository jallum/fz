//! Primitive lowering helpers for codegen.

use super::*;
use crate::fz_ir::{BinOp, Const, Prim, UnOp};
use cranelift_codegen::ir::{
    self, BlockArg, InstBuilder, MemFlags,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, FuncId, Linkage};
use fz_runtime::heap::FieldKind;
use std::collections::HashMap;

pub(crate) fn emit_map_get_value_ref_for_key<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    map: crate::fz_ir::Var,
    key: crate::fz_ir::Var,
    cache: &mut CodegenCache,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> ir::Value {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let map_ref = tagged_get(cx, var_env, b, jmod, runtime, map.0, cache);
    let key_kind = expected_runtime_value_kind(t, fn_types, block_env, key);
    match key_kind {
        Some(fz_runtime::any_value::ValueKind::ATOM) => {
            let kv = codegen_value_raw_atom(
                cx,
                b,
                jmod,
                runtime,
                cache,
                binding_for_var(var_env, key.0),
            );
            let fref = jmod.declare_func_in_func(runtime.map_get_atom_key_ref_id, b.func);
            let inst = b.ins().call(fref, &[map_ref, kv]);
            b.inst_results(inst)[0]
        }
        Some(fz_runtime::any_value::ValueKind::INT) => {
            let kv = codegen_value_raw_int(cx, b, jmod, runtime, binding_for_var(var_env, key.0));
            let fref = jmod.declare_func_in_func(runtime.map_get_int_key_ref_id, b.func);
            let inst = b.ins().call(fref, &[map_ref, kv]);
            b.inst_results(inst)[0]
        }
        Some(fz_runtime::any_value::ValueKind::FLOAT) => {
            let key_float =
                codegen_value_raw_float(cx, b, jmod, runtime, binding_for_var(var_env, key.0));
            let fref = jmod.declare_func_in_func(runtime.map_get_float_key_ref_id, b.func);
            let inst = b.ins().call(fref, &[map_ref, key_float]);
            b.inst_results(inst)[0]
        }
        _ => {
            let fref = jmod.declare_func_in_func(runtime.map_get_ref_id, b.func);
            let key_ref = tagged_get(cx, var_env, b, jmod, runtime, key.0, cache);
            let inst = b.ins().call(fref, &[map_ref, key_ref]);
            b.inst_results(inst)[0]
        }
    }
}

pub(crate) fn emit_map_put_for_key_and_value<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    map_bits: ir::Value,
    key: crate::fz_ir::Var,
    value: crate::fz_ir::Var,
    cache: &mut CodegenCache,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> ir::Value {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let key_kind = expected_runtime_value_kind(t, fn_types, block_env, key);
    let value_kind = expected_runtime_value_kind(t, fn_types, block_env, value);
    let scalar_put_id = match (key_kind, value_kind) {
        (
            Some(fz_runtime::any_value::ValueKind::ATOM),
            Some(fz_runtime::any_value::ValueKind::INT),
        ) => Some(runtime.map_put_atom_key_int_id),
        (
            Some(fz_runtime::any_value::ValueKind::ATOM),
            Some(fz_runtime::any_value::ValueKind::FLOAT),
        ) => Some(runtime.map_put_atom_key_float_id),
        (
            Some(fz_runtime::any_value::ValueKind::ATOM),
            Some(fz_runtime::any_value::ValueKind::ATOM),
        ) => Some(runtime.map_put_atom_key_atom_id),
        (
            Some(fz_runtime::any_value::ValueKind::INT),
            Some(fz_runtime::any_value::ValueKind::INT),
        ) => Some(runtime.map_put_int_key_int_id),
        (
            Some(fz_runtime::any_value::ValueKind::INT),
            Some(fz_runtime::any_value::ValueKind::FLOAT),
        ) => Some(runtime.map_put_int_key_float_id),
        (
            Some(fz_runtime::any_value::ValueKind::INT),
            Some(fz_runtime::any_value::ValueKind::ATOM),
        ) => Some(runtime.map_put_int_key_atom_id),
        (
            Some(fz_runtime::any_value::ValueKind::FLOAT),
            Some(fz_runtime::any_value::ValueKind::INT),
        ) => Some(runtime.map_put_float_key_int_id),
        (
            Some(fz_runtime::any_value::ValueKind::FLOAT),
            Some(fz_runtime::any_value::ValueKind::FLOAT),
        ) => Some(runtime.map_put_float_key_float_id),
        (
            Some(fz_runtime::any_value::ValueKind::FLOAT),
            Some(fz_runtime::any_value::ValueKind::ATOM),
        ) => Some(runtime.map_put_float_key_atom_id),
        _ => None,
    };
    if let Some(func_id) = scalar_put_id {
        let key_arg = match key_kind {
            Some(fz_runtime::any_value::ValueKind::INT) => {
                codegen_value_raw_int(cx, b, jmod, runtime, binding_for_var(var_env, key.0))
            }
            Some(fz_runtime::any_value::ValueKind::FLOAT) => {
                codegen_value_raw_float(cx, b, jmod, runtime, binding_for_var(var_env, key.0))
            }
            Some(fz_runtime::any_value::ValueKind::ATOM) => {
                codegen_value_raw_atom(cx, b, jmod, runtime, cache, binding_for_var(var_env, key.0))
            }
            Some(_) => unreachable!("scalar map put requires scalar key kind"),
            None => unreachable!("scalar map put requires known key kind"),
        };
        let value_arg = match value_kind {
            Some(fz_runtime::any_value::ValueKind::INT) => {
                codegen_value_raw_int(cx, b, jmod, runtime, binding_for_var(var_env, value.0))
            }
            Some(fz_runtime::any_value::ValueKind::FLOAT) => {
                codegen_value_raw_float(cx, b, jmod, runtime, binding_for_var(var_env, value.0))
            }
            Some(fz_runtime::any_value::ValueKind::ATOM) => codegen_value_raw_atom(
                cx,
                b,
                jmod,
                runtime,
                cache,
                binding_for_var(var_env, value.0),
            ),
            Some(_) => unreachable!("scalar map put requires scalar value kind"),
            None => unreachable!("scalar map put requires known value kind"),
        };
        let fref = jmod.declare_func_in_func(func_id, b.func);
        let inst = b.ins().call(fref, &[map_bits, key_arg, value_arg]);
        return b.inst_results(inst)[0];
    }

    let key_ref = tagged_get(cx, var_env, b, jmod, runtime, key.0, cache);
    let key_ref = mark_published_ref_aliased(b, jmod, runtime, key_ref);
    let (fref, args): (ir::FuncRef, Vec<ir::Value>) = match value_kind {
        Some(fz_runtime::any_value::ValueKind::INT) => (
            jmod.declare_func_in_func(runtime.map_put_int_id, b.func),
            vec![
                map_bits,
                key_ref,
                codegen_value_raw_int(cx, b, jmod, runtime, binding_for_var(var_env, value.0)),
            ],
        ),
        Some(fz_runtime::any_value::ValueKind::FLOAT) => {
            let value_f64 =
                codegen_value_raw_float(cx, b, jmod, runtime, binding_for_var(var_env, value.0));
            (
                jmod.declare_func_in_func(runtime.map_put_float_id, b.func),
                vec![map_bits, key_ref, value_f64],
            )
        }
        Some(fz_runtime::any_value::ValueKind::ATOM) => (
            jmod.declare_func_in_func(runtime.map_put_atom_id, b.func),
            vec![
                map_bits,
                key_ref,
                codegen_value_raw_atom(
                    cx,
                    b,
                    jmod,
                    runtime,
                    cache,
                    binding_for_var(var_env, value.0),
                ),
            ],
        ),
        _ => {
            let value_ref = tagged_get(cx, var_env, b, jmod, runtime, value.0, cache);
            let value_ref = mark_published_ref_aliased(b, jmod, runtime, value_ref);
            (
                jmod.declare_func_in_func(runtime.map_put_ref_id, b.func),
                vec![map_bits, key_ref, value_ref],
            )
        }
    };
    let inst = b.ins().call(fref, &args);
    b.inst_results(inst)[0]
}

fn codegen_value_raw_kind_parts(
    b: &mut FunctionBuilder<'_>,
    value: CodegenValue,
) -> Option<(ir::Value, fz_runtime::any_value::ValueKind)> {
    match value {
        CodegenValue::RawInt(raw)
        | CodegenValue::Known {
            payload: raw,
            kind: fz_runtime::any_value::ValueKind::INT,
        } => Some((raw, fz_runtime::any_value::ValueKind::INT)),
        CodegenValue::RawF64(raw) => {
            let bits = b.ins().bitcast(types::I64, MemFlags::new(), raw);
            Some((bits, fz_runtime::any_value::ValueKind::FLOAT))
        }
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::FLOAT,
        } => Some((payload, fz_runtime::any_value::ValueKind::FLOAT)),
        CodegenValue::Known {
            payload,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        } => Some((payload, fz_runtime::any_value::ValueKind::ATOM)),
        CodegenValue::Known { payload, kind }
            if kind.is_heap() || kind == fz_runtime::any_value::ValueKind::LIST =>
        {
            Some((payload, kind))
        }
        _ => None,
    }
}

fn emit_map_destination_put<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    map_bits: ir::Value,
    key: CodegenValue,
    value: CodegenValue,
) {
    if let (Some((key_raw, key_kind)), Some((value_raw, value_kind))) = (
        codegen_value_raw_kind_parts(b, key),
        codegen_value_raw_kind_parts(b, value),
    ) && key_kind.is_scalar()
        && value_kind.is_scalar()
    {
        let fref = jmod.declare_func_in_func(runtime.map_dest_put_parts_id, b.func);
        let key_kind = b.ins().iconst(types::I64, key_kind.tag() as i64);
        let value_kind = b.ins().iconst(types::I64, value_kind.tag() as i64);
        b.ins()
            .call(fref, &[map_bits, key_raw, key_kind, value_raw, value_kind]);
    } else {
        let key_ref = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, key);
        let value_ref = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, value);
        let key_ref = mark_published_ref_aliased(b, jmod, runtime, key_ref);
        let value_ref = mark_published_ref_aliased(b, jmod, runtime, value_ref);
        let fref = jmod.declare_func_in_func(runtime.map_dest_put_ref_id, b.func);
        b.ins().call(fref, &[map_bits, key_ref, value_ref]);
    }
}

pub(crate) fn emit_list_cons_bif<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    head: crate::fz_ir::Var,
    head_kind: Option<fz_runtime::any_value::ValueKind>,
    tail: ListTailBits,
    cache: &mut CodegenCache,
) -> ir::Value {
    let runtime = env.runtime;
    let tail_ref = cx.list_tail_ref_word(b, cache, tail);
    let head_value = binding_for_var(var_env, head.0);
    let (func_id, args): (FuncId, Vec<ir::Value>) = match head_kind {
        Some(fz_runtime::any_value::ValueKind::INT) => (
            runtime.list_cons_int_id,
            vec![
                codegen_value_raw_int(cx, b, jmod, runtime, head_value),
                tail_ref,
            ],
        ),
        Some(fz_runtime::any_value::ValueKind::FLOAT) => (
            runtime.list_cons_float_id,
            vec![
                codegen_value_raw_float(cx, b, jmod, runtime, head_value),
                tail_ref,
            ],
        ),
        Some(fz_runtime::any_value::ValueKind::ATOM) => (
            runtime.list_cons_atom_id,
            vec![
                codegen_value_raw_atom(cx, b, jmod, runtime, cache, head_value),
                tail_ref,
            ],
        ),
        None if matches!(
            head_value,
            CodegenValue::RawInt(_)
                | CodegenValue::Known {
                    kind: fz_runtime::any_value::ValueKind::INT,
                    ..
                }
        ) =>
        {
            (
                runtime.list_cons_int_id,
                vec![
                    codegen_value_raw_int(cx, b, jmod, runtime, head_value),
                    tail_ref,
                ],
            )
        }
        None if matches!(
            head_value,
            CodegenValue::RawF64(_)
                | CodegenValue::Known {
                    kind: fz_runtime::any_value::ValueKind::FLOAT,
                    ..
                }
        ) =>
        {
            (
                runtime.list_cons_float_id,
                vec![
                    codegen_value_raw_float(cx, b, jmod, runtime, head_value),
                    tail_ref,
                ],
            )
        }
        None if matches!(
            head_value,
            CodegenValue::Known {
                kind: fz_runtime::any_value::ValueKind::ATOM,
                ..
            }
        ) =>
        {
            (
                runtime.list_cons_atom_id,
                vec![
                    codegen_value_raw_atom(cx, b, jmod, runtime, cache, head_value),
                    tail_ref,
                ],
            )
        }
        None => (
            runtime.list_cons_any_id,
            vec![
                codegen_value_as_any_ref(cx, b, jmod, runtime, cache, head_value),
                tail_ref,
            ],
        ),
        _ => (
            runtime.list_cons_any_id,
            vec![
                codegen_value_as_any_ref(cx, b, jmod, runtime, cache, head_value),
                tail_ref,
            ],
        ),
    };
    cx.list_cons_with(b, jmod, func_id, &args)
}

/// Lower collection-typed Prim variants (List, Tuple, AllocStruct, Bitstring,
/// Map, Vec) to a tagged `ir::Value`. Called by `lower_prim` for these arms.
pub(crate) fn lower_collection_prim<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    cache: &mut CodegenCache,
    block_id: crate::fz_ir::BlockId,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> Result<LowerOut, CodegenError> {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let tuple_schema_ids = env.tuple_schema_ids;
    let v: LowerOut = match prim {
        Prim::ListHead(c) => {
            let list_ref = known_list_ref_for_var(var_env, b, jmod, runtime, cache, block_id, c.0);
            LowerOut::ValueRefWord(cx.list_head(b, jmod, list_ref))
        }
        Prim::ListTail(c) => {
            let list_ref = known_list_ref_for_var(var_env, b, jmod, runtime, cache, block_id, c.0);
            LowerOut::ValueRefWord(cx.list_tail(b, jmod, list_ref))
        }
        Prim::MakeList(elems, tail) => {
            if elems.len() == 1
                && let Some(tail_var) = tail
            {
                let tail_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, tail_var.0, cache);
                let tail = list_tail_bits_for_var(t, fn_types, block_env, *tail_var, tail_bits);
                if let Some(reused) = emit_owned_cons_reuse_or_alloc(
                    cx, b, jmod, runtime, var_env, cache, elems[0], tail,
                ) {
                    return Ok(LowerOut::ValueRef(reused));
                }
            }
            // Default tail of a list-literal is the empty list (`[]`),
            // NOT the nil atom value — distinct runtime bit patterns.
            let mut acc = match tail {
                Some(tail_var) => {
                    let tail_bits =
                        any_ref_for_var(cx, var_env, b, jmod, runtime, tail_var.0, cache);
                    list_tail_bits_for_var(t, fn_types, block_env, *tail_var, tail_bits)
                }
                None => ListTailBits::Empty,
            };
            for e in elems.iter().rev() {
                let cons = emit_list_cons_bif(
                    cx,
                    b,
                    jmod,
                    env,
                    var_env,
                    *e,
                    expected_runtime_value_kind(t, fn_types, block_env, *e),
                    acc,
                    cache,
                );
                acc = ListTailBits::NonEmptyValueRef(cons);
            }
            match acc {
                ListTailBits::NonEmptyValueRef(bits) | ListTailBits::ValueRef(bits) => {
                    LowerOut::ValueRef(bits)
                }
                ListTailBits::Empty => {
                    LowerOut::ValueRefWord(emit_empty_list_value_ref_word(b, cache))
                }
            }
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
                let value = binding_for_var(var_env, e.0);
                emit_struct_set_field_value(cx, b, jmod, runtime, cache, p, i, value);
            }
            LowerOut::ValueRef(p)
        }
        Prim::DestTupleBegin { arity, .. } => {
            let schema_id = *tuple_schema_ids.get(arity).ok_or_else(|| {
                CodegenError::new(format!(
                    "tuple arity {} not pre-registered (compile() walk missed it?)",
                    arity
                ))
            })?;
            let fref = jmod.declare_func_in_func(runtime.alloc_struct_id, b.func);
            let sid = b.ins().iconst(types::I32, schema_id as i64);
            let inst = b.ins().call(fref, &[sid]);
            LowerOut::ValueRef(b.inst_results(inst)[0])
        }
        Prim::DestTupleSet {
            dest, index, value, ..
        } => {
            let dest_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, dest.0, cache);
            let field_value = binding_for_var(var_env, value.0);
            emit_struct_set_field_value(
                cx,
                b,
                jmod,
                runtime,
                cache,
                dest_bits,
                *index as usize,
                field_value,
            );
            LowerOut::DeadUnit
        }
        Prim::DestFreeze { dest, .. } => {
            let dest_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, dest.0, cache);
            LowerOut::ValueRef(dest_bits)
        }
        Prim::DestListBegin { .. } => LowerOut::DeadUnit,
        Prim::DestListCons { head, tail, .. } => {
            if let Some(tail_var) = tail {
                let tail_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, tail_var.0, cache);
                let tail = list_tail_bits_for_var(t, fn_types, block_env, *tail_var, tail_bits);
                if let Some(reused) = emit_owned_cons_reuse_or_alloc(
                    cx, b, jmod, runtime, var_env, cache, *head, tail,
                ) {
                    return Ok(LowerOut::ValueRef(reused));
                }
            }
            let acc = match tail {
                Some(tail_var) => {
                    let tail_bits =
                        any_ref_for_var(cx, var_env, b, jmod, runtime, tail_var.0, cache);
                    list_tail_bits_for_var(t, fn_types, block_env, *tail_var, tail_bits)
                }
                None => ListTailBits::Empty,
            };
            let cons = emit_list_cons_bif(
                cx,
                b,
                jmod,
                env,
                var_env,
                *head,
                expected_runtime_value_kind(t, fn_types, block_env, *head),
                acc,
                cache,
            );
            LowerOut::ValueRef(cons)
        }
        Prim::DestListFreeze { list, .. } => {
            let list_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, list.0, cache);
            LowerOut::ValueRef(list_bits)
        }
        Prim::TupleField(c, idx) => {
            if let Some(binding) = cache.tuple_field_params.get(&(c.0, *idx)).copied() {
                return Ok(lower_out_for_codegen_value(binding));
            }
            // Every TupleField is gated by a preceding `Prim::TypeTest`
            // that runtime-checks the subject is a matching-arity Struct
            // heap value, so the load is provably safe. A SIGSEGV here
            // would be an IR integrity bug worth surfacing loudly — do
            // NOT add `notrap`, which would silently mask it.
            let fref = jmod.declare_func_in_func(runtime.struct_get_field_id, b.func);
            let field_offset = b
                .ins()
                .iconst(types::I32, (*idx as i64) * SLOT_BYTES as i64);
            let struct_ref = tagged_get(cx, var_env, b, jmod, runtime, c.0, cache);
            let inst = b.ins().call(fref, &[struct_ref, field_offset]);
            LowerOut::ValueRefWord(b.inst_results(inst)[0])
        }
        Prim::MakeBitstring(fields) => {
            let begin = jmod.declare_func_in_func(runtime.bs_begin_id, b.func);
            b.ins().call(begin, &[]);
            let write = jmod.declare_func_in_func(runtime.bs_write_ref_id, b.func);
            for f in fields {
                let value_ref = tagged_get(cx, var_env, b, jmod, runtime, f.value.0, cache);
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
                        let unb = as_raw_i64(cx, var_env, b, jmod, runtime, v.0);
                        let truncated = b.ins().ireduce(types::I32, unb);
                        (b.ins().iconst(types::I32, 1), truncated)
                    }
                };
                b.ins().call(
                    write,
                    &[
                        value_ref,
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
            LowerOut::ValueRef(b.inst_results(inst)[0])
        }
        Prim::ConstBitstring(bytes, bit_len) => {
            // Split paths by payload size:
            //   * Below threshold: intern bytes and call
            //     `fz_alloc_bitstring_const(ptr, byte_len, bit_len)` —
            //     runtime allocates an inline strict bitstring.
            //   * Above threshold: emit a bytes-payload symbol and a
            //     40-byte static SharedBin symbol in `.data` (refcount=1
            //     anchor, relocs for bytes_ptr + noop destructor) and
            //     call `fz_alloc_procbin_from_static(static_ptr)`.
            let above_threshold = bytes.len() > fz_runtime::heap::SHARED_BIN_THRESHOLD_BYTES;
            let syms = {
                let mut cache = env.bs_const_data.borrow_mut();
                if let Some(syms) = cache.get(bytes) {
                    // Cached. If the existing entry lacks the SharedBin
                    // symbol but this call site needs it, populate now.
                    let mut syms = *syms;
                    if above_threshold && syms.sharedbin_id.is_none() {
                        syms.sharedbin_id = Some(define_static_sharedbin(
                            jmod,
                            runtime,
                            syms.bytes_id,
                            bytes,
                            *bit_len,
                            cache.len(),
                        )?);
                        cache.insert(bytes.clone(), syms);
                    }
                    syms
                } else {
                    let idx = cache.len();
                    let bytes_name = format!(".fz_bs_const_{}", idx);
                    let bytes_id = jmod
                        .declare_data(&bytes_name, Linkage::Local, false, false)
                        .map_err(|e| CodegenError::new(format!("declare {}: {}", bytes_name, e)))?;
                    let mut desc = DataDescription::new();
                    // Append invisible trailing NUL; not counted in the
                    // static SharedBin's bytes_len field. Underwrites the
                    // cstring extern marshal contract for literal binaries.
                    let mut payload: Vec<u8> = bytes.clone();
                    payload.push(0);
                    desc.define(payload.into_boxed_slice());
                    desc.set_align(1);
                    jmod.define_data(bytes_id, &desc)
                        .map_err(|e| CodegenError::new(format!("define {}: {}", bytes_name, e)))?;
                    let sharedbin_id = if above_threshold {
                        Some(define_static_sharedbin(
                            jmod, runtime, bytes_id, bytes, *bit_len, idx,
                        )?)
                    } else {
                        None
                    };
                    let syms = BsConstSyms {
                        bytes_id,
                        sharedbin_id,
                    };
                    cache.insert(bytes.clone(), syms);
                    syms
                }
            };
            if let Some(sb_id) = syms.sharedbin_id {
                let gv = jmod.declare_data_in_func(sb_id, b.func);
                let sb_ptr = b.ins().symbol_value(types::I64, gv);
                let fref = jmod.declare_func_in_func(runtime.alloc_procbin_from_static_id, b.func);
                let inst = b.ins().call(fref, &[sb_ptr]);
                LowerOut::ValueRef(b.inst_results(inst)[0])
            } else {
                let gv = jmod.declare_data_in_func(syms.bytes_id, b.func);
                let ptr_v = b.ins().symbol_value(types::I64, gv);
                let byte_len_v = b.ins().iconst(types::I64, bytes.len() as i64);
                let bit_len_v = b.ins().iconst(types::I64, *bit_len as i64);
                let fref = jmod.declare_func_in_func(runtime.alloc_bitstring_const_id, b.func);
                let inst = b.ins().call(fref, &[ptr_v, byte_len_v, bit_len_v]);
                LowerOut::ValueRef(b.inst_results(inst)[0])
            }
        }
        Prim::BitReaderInit(v) => {
            let value_ref = tagged_get(cx, var_env, b, jmod, runtime, v.0, cache);
            let fref = jmod.declare_func_in_func(runtime.bs_reader_init_ref_id, b.func);
            let inst = b.ins().call(fref, &[value_ref]);
            LowerOut::ValueRef(b.inst_results(inst)[0])
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
            let reader_ref = tagged_get(cx, var_env, b, jmod, runtime, reader.0, cache);
            let (size_present, size_value) = match size {
                None => (0, b.ins().iconst(types::I32, 0)),
                Some(crate::fz_ir::BitSizeIr::Literal(n)) => {
                    (1, b.ins().iconst(types::I32, *n as i64))
                }
                Some(crate::fz_ir::BitSizeIr::Var(v)) => {
                    let unb = as_raw_i64(cx, var_env, b, jmod, runtime, v.0);
                    let truncated = b.ins().ireduce(types::I32, unb);
                    (1, truncated)
                }
            };
            let field_spec = fz_runtime::ir_runtime::fz_bs_field_spec(
                encode_bit_type(*ty),
                size_present,
                unit.unwrap_or(default_unit_for(*ty)),
                encode_endian(*endian),
                *signed as u32,
                *is_last as u32,
            );
            let field_spec = b.ins().iconst(types::I64, field_spec as i64);
            let fref = jmod.declare_func_in_func(runtime.bs_read_field_ref_id, b.func);
            let inst = b.ins().call(fref, &[reader_ref, field_spec, size_value]);
            LowerOut::ValueRef(b.inst_results(inst)[0])
        }
        Prim::MakeMap(entries) => {
            let mut map_bits = if entries.is_empty() {
                let empty = jmod.declare_func_in_func(runtime.map_empty_id, b.func);
                let inst = b.ins().call(empty, &[]);
                b.inst_results(inst)[0]
            } else {
                b.ins().iconst(types::I64, 0)
            };
            for (k, v) in entries {
                map_bits = emit_map_put_for_key_and_value(
                    cx, b, jmod, t, env, var_env, map_bits, *k, *v, cache, block_env,
                );
            }
            LowerOut::ValueRef(map_bits)
        }
        Prim::MapUpdate(base, entries) => {
            let mut map_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, base.0, cache);
            for (k, v) in entries {
                map_bits = emit_map_put_for_key_and_value(
                    cx, b, jmod, t, env, var_env, map_bits, *k, *v, cache, block_env,
                );
            }
            LowerOut::ValueRef(map_bits)
        }
        Prim::DestMapBegin { base, extra, .. } => {
            let extra = b.ins().iconst(types::I32, *extra as i64);
            if let Some(base) = base {
                let base_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, base.0, cache);
                let fref = jmod.declare_func_in_func(runtime.map_dest_begin_update_id, b.func);
                let inst = b.ins().call(fref, &[base_bits, extra]);
                LowerOut::ValueRef(b.inst_results(inst)[0])
            } else {
                let fref = jmod.declare_func_in_func(runtime.map_dest_begin_id, b.func);
                let inst = b.ins().call(fref, &[extra]);
                LowerOut::ValueRef(b.inst_results(inst)[0])
            }
        }
        Prim::DestMapPut {
            map, key, value, ..
        } => {
            let map_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, map.0, cache);
            let key = binding_for_var(var_env, key.0);
            let value = binding_for_var(var_env, value.0);
            emit_map_destination_put(cx, b, jmod, runtime, cache, map_bits, key, value);
            LowerOut::DeadUnit
        }
        Prim::DestMapFreeze { map, .. } => {
            let map_bits = any_ref_for_var(cx, var_env, b, jmod, runtime, map.0, cache);
            let fref = jmod.declare_func_in_func(runtime.map_dest_freeze_id, b.func);
            let inst = b.ins().call(fref, &[map_bits]);
            LowerOut::ValueRef(b.inst_results(inst)[0])
        }
        Prim::MapGet(m, k) => {
            let value_ref = emit_map_get_value_ref_for_key(
                cx, b, jmod, t, env, var_env, *m, *k, cache, block_env,
            );
            LowerOut::ValueRefWord(value_ref)
        }
        Prim::MatcherMapGet(m, k) => {
            let fref = jmod.declare_func_in_func(runtime.matcher_map_get_ref_id, b.func);
            let map_ref = tagged_get(cx, var_env, b, jmod, runtime, m.0, cache);
            let key_ref = tagged_get(cx, var_env, b, jmod, runtime, k.0, cache);
            let inst = b.ins().call(fref, &[map_ref, key_ref]);
            LowerOut::ValueRefWord(b.inst_results(inst)[0])
        }
        Prim::IsMatcherMapMiss(v) => {
            let value_ref = tagged_get(cx, var_env, b, jmod, runtime, v.0, cache);
            let tag = cx.ref_tag(b, jmod, value_ref);
            let is_miss = b.ins().icmp_imm(
                IntCC::Equal,
                tag,
                fz_runtime::any_value::ValueKind::NULL.tag() as i64,
            );
            LowerOut::Strict(strict_bool(b, is_miss))
        }
        _ => unreachable!("lower_collection_prim: not a collection prim"),
    };
    Ok(v)
}

fn lower_out_for_codegen_value(value: CodegenValue) -> LowerOut {
    match value {
        CodegenValue::AnyRef(v) => LowerOut::ValueRef(v),
        CodegenValue::Known { .. } => LowerOut::Strict(value),
        CodegenValue::RawInt(v) => LowerOut::RawI64(v),
        CodegenValue::RawF64(v) => LowerOut::RawF64(v),
        CodegenValue::Condition(v) => LowerOut::Condition(v),
    }
}

#[allow(clippy::too_many_arguments)]
fn marshal_extern_arg<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    var: crate::fz_ir::Var,
    ty: crate::fz_ir::ExternTy,
) -> Result<ir::Value, CodegenError> {
    use crate::fz_ir::ExternTy;
    Ok(match ty {
        ExternTy::I64 => as_raw_i64(cx, var_env, b, jmod, runtime, var.0),
        ExternTy::F64 => as_raw_f64(cx, var_env, b, jmod, runtime, var.0),
        ExternTy::Binary | ExternTy::CString => {
            let helper_id = match ty {
                ExternTy::CString => runtime.binary_as_cstring_id,
                _ => runtime.binary_as_ptr_id,
            };
            let helper_fref = jmod.declare_func_in_func(helper_id, b.func);
            let bits = tagged_get(cx, var_env, b, jmod, runtime, var.0, cache);
            let call = b.ins().call(helper_fref, &[bits]);
            b.inst_results(call)[0]
        }
        ExternTy::Any => tagged_get(cx, var_env, b, jmod, runtime, var.0, cache),
        ExternTy::Unit | ExternTy::Never => {
            return Err(CodegenError::new(format!(
                "{:?} is not a valid extern argument marshal class",
                ty
            )));
        }
    })
}

fn format_extern_shape(
    ret: crate::fz_ir::ExternTy,
    fixed: &[crate::fz_ir::ExternTy],
    variadic: &[crate::fz_ir::ExternTy],
) -> String {
    let fixed = fixed
        .iter()
        .map(|ty| format!("{:?}", ty))
        .collect::<Vec<_>>()
        .join(", ");
    let variadic = variadic
        .iter()
        .map(|ty| format!("{:?}", ty))
        .collect::<Vec<_>>()
        .join(", ");
    format!("ret={:?} fixed=[{}] variadic=[{}]", ret, fixed, variadic)
}

fn variadic_dispatcher(
    runtime: &RuntimeRefs,
    ret: crate::fz_ir::ExternTy,
    fixed: &[crate::fz_ir::ExternTy],
    variadic: &[crate::fz_ir::ExternTy],
) -> Result<FuncId, CodegenError> {
    use crate::fz_ir::ExternTy;
    match (ret, fixed, variadic) {
        (ExternTy::I64, [ExternTy::CString, ExternTy::I64], [ExternTy::I64]) => {
            Ok(runtime.extern_var_i64_cstring_i64_i64_to_i64_id)
        }
        (ExternTy::I64, [ExternTy::CString], [ExternTy::I64]) => {
            Ok(runtime.extern_var_i64_cstring_i64_to_i64_id)
        }
        _ => Err(CodegenError::new(format!(
            "unsupported variadic extern shape: {}",
            format_extern_shape(ret, fixed, variadic)
        ))),
    }
}

fn emit_extern_symbol_name<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    caller_fn_id: crate::fz_ir::FnId,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
    symbol: &str,
) -> Result<ir::Value, CodegenError> {
    if symbol.as_bytes().contains(&0) {
        return Err(CodegenError::new(format!(
            "extern symbol `{}` contains a NUL byte",
            symbol
        )));
    }
    let name = format!(
        ".fz_extern_symbol_{}_{}_{}",
        caller_fn_id.0, block_id.0, stmt_idx
    );
    let data_id = jmod
        .declare_data(&name, Linkage::Local, false, false)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
    let mut payload = symbol.as_bytes().to_vec();
    payload.push(0);
    let mut desc = DataDescription::new();
    desc.define(payload.into_boxed_slice());
    desc.set_align(1);
    jmod.define_data(data_id, &desc)
        .map_err(|e| CodegenError::new(format!("define {}: {}", name, e)))?;
    let gv = jmod.declare_data_in_func(data_id, b.func);
    Ok(b.ins().symbol_value(types::I64, gv))
}

#[allow(clippy::too_many_arguments)]
fn emit_variadic_extern_call<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    eid: crate::fz_ir::ExternId,
    args: &[crate::fz_ir::ExternArg],
    dest_var: crate::fz_ir::Var,
    caller_fn_id: crate::fz_ir::FnId,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
) -> Result<LowerOut, CodegenError> {
    let decl = env.module.extern_by_id(eid);
    let mut arg_tys = Vec::with_capacity(args.len());
    for arg_idx in 0..args.len() {
        let site = crate::fz_ir::ExternMarshalSite {
            block: block_id,
            stmt_idx,
            arg_idx,
        };
        let Some(&ty) = env.fn_types.extern_marshals.get(&site) else {
            return Err(CodegenError::new(format!(
                "variadic extern `{}` has unresolved marshal metadata at {:?}",
                decl.symbol, site
            )));
        };
        arg_tys.push(ty);
    }

    let fixed_count = decl.params.len();
    let fixed = &arg_tys[..fixed_count];
    let variadic = &arg_tys[fixed_count..];
    let dispatcher = variadic_dispatcher(env.runtime, decl.ret, fixed, variadic)?;
    let symbol_ptr = emit_extern_symbol_name(
        b,
        jmod,
        caller_fn_id,
        block_id,
        stmt_idx,
        decl.symbol.as_str(),
    )?;
    let lookup_fref = jmod.declare_func_in_func(env.runtime.extern_symbol_addr_id, b.func);
    let lookup = b.ins().call(lookup_fref, &[symbol_ptr]);
    let fn_ptr = b.inst_results(lookup)[0];

    let mut call_args = Vec::with_capacity(args.len() + 1);
    call_args.push(fn_ptr);
    for (arg, ty) in args.iter().zip(arg_tys.iter().copied()) {
        call_args.push(marshal_extern_arg(
            cx,
            b,
            jmod,
            env.runtime,
            var_env,
            cache,
            arg.var,
            ty,
        )?);
    }

    let dispatcher_fref = jmod.declare_func_in_func(dispatcher, b.func);
    let inst = b.ins().call(dispatcher_fref, &call_args);
    if matches!(
        decl.ret,
        crate::fz_ir::ExternTy::Unit | crate::fz_ir::ExternTy::Never
    ) {
        if cache.used_vars.contains(&dest_var.0) {
            return Ok(LowerOut::Strict(strict_const_value(
                b,
                fz_runtime::any_value::AnyValue::nil_atom(),
            )));
        }
        return Ok(LowerOut::DeadUnit);
    }
    let raw = b.inst_results(inst)[0];
    match decl.ret {
        crate::fz_ir::ExternTy::I64 => Ok(LowerOut::RawI64(raw)),
        crate::fz_ir::ExternTy::F64 => Ok(LowerOut::RawF64(raw)),
        crate::fz_ir::ExternTy::Any
        | crate::fz_ir::ExternTy::Binary
        | crate::fz_ir::ExternTy::CString => Ok(LowerOut::ValueRef(raw)),
        crate::fz_ir::ExternTy::Unit | crate::fz_ir::ExternTy::Never => unreachable!(),
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_prim<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    dest_var: crate::fz_ir::Var,
    cache: &mut CodegenCache,
    // `caller_fn_id`/`block_id`/`stmt_idx` identify per-stmt side tables such
    // as variadic extern marshal plans and generated static data symbols.
    caller_fn_id: crate::fz_ir::FnId,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
    block_env: Option<&HashMap<crate::fz_ir::Var, crate::types::Ty>>,
) -> Result<LowerOut, CodegenError> {
    if cache.skipped_tuple_return_vars.contains(&dest_var.0)
        || cache.skipped_list_tail_return_vars.contains(&dest_var.0)
    {
        return Ok(LowerOut::DeadUnit);
    }
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let spec_registry = env.spec_registry;
    let fn_ids = env.fn_ids;
    let param_reprs = env.param_reprs;
    let return_reprs = env.return_reprs;
    // Helper: every consumer site below that wants one-word ValueRef uses
    // this. Sites that want a raw f64 (float fast paths only) call
    // `as_raw_f64` directly.
    //
    // The match below produces a one-word ValueRef ir::Value for most prims.
    // The few prims that can produce a raw f64 (currently: typed float
    // BinOp::{Add,Sub,Mul,Div,Lt,Le,Gt,Ge,Eq,Neq}) early-return
    // `LowerOut::RawF64(_)` inside their arm. Everything else falls
    // through the match and is wrapped in `LowerOut::ValueRef(_)` at the
    // bottom of the function.
    match prim {
        Prim::Const(c) => match c {
            // Emit the raw payload when the consumer's type is
            // int-monomorphic; ValueRef consumers retag via `tagged_get`
            // at their use site. Without this fast path every
            // int-arithmetic / RawInt-slot consumer would decode via
            // `as_raw_i64`.
            Const::Int(n) => {
                if ty_is_int(t, fn_types, dest_var) {
                    cache.raw_int_consts.insert(dest_var.0, *n);
                    return Ok(LowerOut::RawI64(b.ins().iconst(types::I64, *n)));
                }
                Ok(LowerOut::StrictConst(fz_runtime::any_value::AnyValue::int(
                    *n,
                )))
            }
            Const::True => Ok(LowerOut::StrictConst(
                fz_runtime::any_value::AnyValue::bool_atom(true),
            )),
            Const::False => Ok(LowerOut::StrictConst(
                fz_runtime::any_value::AnyValue::bool_atom(false),
            )),
            Const::Nil => Ok(LowerOut::StrictConst(
                fz_runtime::any_value::AnyValue::nil_atom(),
            )),
            Const::Atom(id) => Ok(LowerOut::StrictConst(
                fz_runtime::any_value::AnyValue::atom(*id),
            )),
            Const::Float(f) => {
                if ty_is_float(t, fn_types, dest_var) {
                    return Ok(LowerOut::RawF64(b.ins().f64const(*f)));
                }
                Err(CodegenError::new(
                    "Float literal inferred outside float representation",
                ))
            }
        },
        Prim::BinOp(op, a, bv) => {
            // Tagged operands are materialised lazily inside the cmp helper
            // via `tagged_get`. Typed-float fast paths read raw via
            // `as_raw_f64` and never trigger the box round-trip; only
            // tagged-path branches (int fast path, scalar Eq/Neq,
            // dispatch fallback) pay it.
            match op {
                BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::Div | BinOp::Mod => {
                    lower_arith_binop(
                        cx, b, jmod, t, fn_types, var_env, cache, runtime, *op, *a, *bv,
                    )
                }
                BinOp::Eq | BinOp::Neq => lower_eq_binop(
                    cx, b, jmod, t, fn_types, var_env, cache, runtime, *op, *a, *bv, dest_var,
                ),
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => lower_cmp_binop(
                    cx, b, jmod, t, fn_types, var_env, cache, runtime, *op, *a, *bv, dest_var,
                ),
                BinOp::And | BinOp::Or => {
                    lower_bool_binop(cx, b, jmod, runtime, var_env, cache, *op, *a, *bv, dest_var)
                }
            }
        }
        Prim::UnOp(op, x) => match op {
            UnOp::Neg => {
                let xi = as_raw_i64(cx, var_env, b, jmod, runtime, x.0);
                Ok(LowerOut::RawI64(b.ins().ineg(xi)))
            }
            UnOp::Not => {
                let xv = *var_env.get(&x.0).expect("not operand");
                let truthy = codegen_value_truthy(cx, b, jmod, runtime, xv);
                let zero = b.ins().iconst(types::I8, 0);
                let inv = b.ins().icmp(IntCC::Equal, truthy, zero);
                if cache.if_only_conds.contains(&dest_var.0) {
                    return Ok(LowerOut::Condition(inv));
                }
                Ok(LowerOut::Strict(strict_bool(b, inv)))
            }
        },
        Prim::Extern(eid, args) => {
            let decl = env.module.extern_by_id(*eid);
            let arg_vars: Vec<crate::fz_ir::Var> = args.iter().map(|arg| arg.var).collect();
            if decl.symbol == "fz_panic" && args.len() == 1 {
                return lower_extern_fz_panic(
                    cx, b, jmod, runtime, var_env, cache, &arg_vars, dest_var,
                );
            }
            if decl.symbol == "fz_send" && args.len() == 2 {
                return lower_extern_fz_send(cx, b, jmod, runtime, var_env, cache, &arg_vars);
            }
            if decl.symbol == "fz_self" && args.is_empty() {
                return lower_extern_fz_self(b, jmod);
            }
            if decl.symbol == "fz_make_ref" && args.is_empty() {
                return lower_extern_fz_make_ref(b, jmod);
            }
            if decl.symbol == "fz_spawn" && args.len() == 1 {
                return lower_extern_fz_spawn(cx, b, jmod, runtime, var_env, cache, &arg_vars);
            }
            if decl.symbol == "fz_spawn_opt" && args.len() == 2 {
                return lower_extern_fz_spawn_opt(cx, b, jmod, runtime, var_env, cache, &arg_vars);
            }
            if decl.symbol == "fz_make_resource" && args.len() == 2 {
                return lower_extern_fz_make_resource(
                    cx, b, jmod, runtime, var_env, cache, &arg_vars,
                );
            }
            if decl.variadic {
                return emit_variadic_extern_call(
                    cx,
                    b,
                    jmod,
                    env,
                    var_env,
                    cache,
                    *eid,
                    args,
                    dest_var,
                    caller_fn_id,
                    block_id,
                    stmt_idx,
                );
            }
            lower_extern_generic(
                cx, b, jmod, runtime, var_env, cache, decl, eid, args, dest_var,
            )
        }
        Prim::IsEmptyList(c) => {
            // Empty list is the null-address List ref.
            let cmp = if let Some(CodegenValue::AnyRef(value)) = var_env.get(&c.0).copied() {
                let tag = cx.ref_tag(b, jmod, value);
                let empty_list_v = cx.empty_list_ref(b, cache);
                let is_list = b.ins().icmp_imm(
                    IntCC::Equal,
                    tag,
                    fz_runtime::any_value::ValueKind::LIST.tag() as i64,
                );
                let is_empty_word = b.ins().icmp(IntCC::Equal, value, empty_list_v);
                b.ins().band(is_list, is_empty_word)
            } else {
                let cv = tagged_get(cx, var_env, b, jmod, runtime, c.0, cache);
                let empty_list_v = emit_empty_list_value_ref_word(b, cache);
                b.ins().icmp(IntCC::Equal, cv, empty_list_v)
            };
            if cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(b, cmp)))
        }
        Prim::BitReaderDone(r) => {
            let rv = tagged_get(cx, var_env, b, jmod, runtime, r.0, cache);
            let fref = jmod.declare_func_in_func(runtime.bs_reader_done_ref_id, b.func);
            let inst = b.ins().call(fref, &[rv]);
            let cmp = b.inst_results(inst)[0];
            if cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(b, cmp)))
        }
        Prim::MapGet(m, k) if ty_is_float(t, fn_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(
                cx, b, jmod, t, env, var_env, *m, *k, cache, block_env,
            );
            let load_float = jmod.declare_func_in_func(runtime.ref_load_float_id, b.func);
            let load_inst = b.ins().call(load_float, &[value_ref]);
            Ok(LowerOut::RawF64(b.inst_results(load_inst)[0]))
        }
        Prim::MapGet(m, k) if ty_is_int(t, fn_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(
                cx, b, jmod, t, env, var_env, *m, *k, cache, block_env,
            );
            let load_int = jmod.declare_func_in_func(runtime.ref_load_int_id, b.func);
            let load_inst = b.ins().call(load_int, &[value_ref]);
            Ok(LowerOut::RawI64(b.inst_results(load_inst)[0]))
        }
        Prim::MapGet(m, k) if ty_is_atom(t, fn_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(
                cx, b, jmod, t, env, var_env, *m, *k, cache, block_env,
            );
            let load_atom = jmod.declare_func_in_func(runtime.ref_load_atom_id, b.func);
            let load_inst = b.ins().call(load_atom, &[value_ref]);
            Ok(LowerOut::RawI64(b.inst_results(load_inst)[0]))
        }
        Prim::ListHead(c)
            if list_projection_is_safe(t, fn_types, *c, block_env)
                && ty_is_int(t, fn_types, dest_var) =>
        {
            let list_ref = known_list_ref_for_var(var_env, b, jmod, runtime, cache, block_id, c.0);
            Ok(LowerOut::RawI64(cx.list_head_int(b, jmod, list_ref)))
        }
        Prim::ListHead(c)
            if list_projection_is_safe(t, fn_types, *c, block_env)
                && ty_is_float(t, fn_types, dest_var) =>
        {
            let list_ref = known_list_ref_for_var(var_env, b, jmod, runtime, cache, block_id, c.0);
            Ok(LowerOut::RawF64(cx.list_head_float(b, jmod, list_ref)))
        }
        Prim::ListTail(c) if list_projection_is_safe(t, fn_types, *c, block_env) => {
            let list_ref = known_list_ref_for_var(var_env, b, jmod, runtime, cache, block_id, c.0);
            Ok(LowerOut::ValueRefWord(cx.list_tail(b, jmod, list_ref)))
        }
        Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeTuple(..)
        | Prim::DestTupleBegin { .. }
        | Prim::DestTupleSet { .. }
        | Prim::DestFreeze { .. }
        | Prim::DestListBegin { .. }
        | Prim::DestListCons { .. }
        | Prim::DestListFreeze { .. }
        | Prim::TupleField(..)
        | Prim::MakeBitstring(..)
        | Prim::ConstBitstring(..)
        | Prim::BitReaderInit(..)
        | Prim::BitReadField { .. }
        | Prim::MakeMap(..)
        | Prim::MapUpdate(..)
        | Prim::DestMapBegin { .. }
        | Prim::DestMapPut { .. }
        | Prim::DestMapFreeze { .. }
        | Prim::MapGet(..)
        | Prim::MatcherMapGet(..)
        | Prim::IsMatcherMapMiss(..) => lower_collection_prim(
            cx, b, jmod, t, env, var_env, prim, cache, block_id, block_env,
        ),
        Prim::MakeClosure(mk_ident, fn_id, captured) => lower_make_closure(
            cx,
            b,
            jmod,
            runtime,
            cache,
            var_env,
            fn_ids,
            spec_registry,
            param_reprs,
            return_reprs,
            mk_ident,
            *fn_id,
            captured,
            block_id,
            stmt_idx,
        ),
        // lower_program_full erases all Prim::Brand before returning.
        // Reaching codegen with one means ir_brand_erase didn't run (or
        // a caller injected Brand after lowering); surface loudly rather
        // than silently lowering as identity.
        Prim::Brand(_, _) => unreachable!(
            "Prim::Brand reached codegen — erasure should run inside lower_program_full"
        ),

        Prim::TypeTest(v, descr) => lower_type_test(
            cx, b, jmod, env, var_env, cache, runtime, *v, descr, dest_var,
        ),
    }
}

/// Lower a `Prim::TypeTest`. Combines a scalar-kind disjunction
/// (int/float/atom-id) with an optional tuple-arity check on struct
/// values; final result is `Condition` if the test feeds an `if`,
/// otherwise a strict bool.
fn lower_type_test<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    runtime: &RuntimeRefs,
    v: crate::fz_ir::Var,
    descr_ty: &crate::types::Ty,
    dest_var: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError> {
    let descr = crate::concrete_types::ty_descr(descr_ty);
    let tuple_has_negations = descr.type_test_tuple_has_negations();
    let tuple_arities = descr.type_test_tuple_arities();

    let value = *var_env.get(&v.0).expect("type-test subject");

    let scalar = emit_scalar_kind_checks(cx, b, jmod, runtime, env.module, descr, value)?;

    let tuple_flag = if !tuple_arities.is_empty() {
        if tuple_has_negations {
            panic!("TypeTest: negated tuple clauses not yet supported");
        }
        Some(emit_tuple_arity_check(
            cx,
            b,
            jmod,
            runtime,
            env.tuple_schema_ids,
            cache,
            value,
            &tuple_arities,
        ))
    } else {
        None
    };

    let flag = match (scalar, tuple_flag) {
        (None, None) => b.ins().iconst(types::I8, 0),
        (Some(s), None) => s,
        (None, Some(t)) => t,
        (Some(s), Some(t)) => b.ins().bor(s, t),
    };
    if cache.if_only_conds.contains(&dest_var.0) {
        return Ok(LowerOut::Condition(flag));
    }
    Ok(LowerOut::Strict(strict_bool(b, flag)))
}

/// Scalar kind checks: emits icmps that or-into the returned flag
/// and ignores heap-bearing axes. For finite atom literal sets we
/// compare the raw atom id.
fn emit_scalar_kind_checks<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    module: &crate::fz_ir::Module,
    descr: &crate::concrete_types::Descr,
    value: CodegenValue,
) -> Result<Option<ir::Value>, CodegenError> {
    let ints = descr.type_test_has_ints();
    let floats = descr.type_test_has_floats();
    let mut scalar: Option<ir::Value> = None;
    let or_in = |b: &mut FunctionBuilder<'_>, f: ir::Value, scalar: &mut Option<ir::Value>| {
        *scalar = Some(match scalar.take() {
            None => f,
            Some(p) => b.ins().bor(p, f),
        });
    };
    if ints {
        let c = codegen_value_is_tag(
            cx,
            b,
            jmod,
            runtime,
            value,
            fz_runtime::any_value::ValueKind::INT,
        );
        or_in(b, c, &mut scalar);
    }
    if floats {
        let c = codegen_value_is_tag(
            cx,
            b,
            jmod,
            runtime,
            value,
            fz_runtime::any_value::ValueKind::FLOAT,
        );
        or_in(b, c, &mut scalar);
    }
    if descr.type_test_atom_is_any() {
        let c = codegen_value_is_tag(
            cx,
            b,
            jmod,
            runtime,
            value,
            fz_runtime::any_value::ValueKind::ATOM,
        );
        or_in(b, c, &mut scalar);
    } else if descr.type_test_atom_is_cofinite() {
        return Err(CodegenError::new(
            "TypeTest: cofinite atom literal sets not yet implemented",
        ));
    } else {
        let names = descr.type_test_atom_literals();
        if !names.is_empty() {
            let name_to_id: std::collections::HashMap<&str, u32> = module
                .atom_names
                .iter()
                .enumerate()
                .map(|(i, n)| (n.as_str(), i as u32))
                .collect();
            for name in names {
                let Some(id) = name_to_id.get(name.as_str()).copied() else {
                    // Pattern wants an atom the module never interns
                    // -> no value can match; skip.
                    continue;
                };
                let atom_id_match = codegen_value_atom_id_is(cx, b, jmod, runtime, value, id);
                or_in(b, atom_id_match, &mut scalar);
            }
        }
    }
    Ok(scalar)
}

/// Tuple arity check: gates on the STRUCT tag, then compares the
/// struct's schema id against the per-arity tuple-schema ids.
fn emit_tuple_arity_check<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    cache: &mut CodegenCache,
    value: CodegenValue,
    tuple_arities: &[usize],
) -> ir::Value {
    let is_struct = codegen_value_is_tag(
        cx,
        b,
        jmod,
        runtime,
        value,
        fz_runtime::any_value::ValueKind::STRUCT,
    );
    let struct_blk = b.create_block();
    let tuple_join = b.create_block();
    b.append_block_param(tuple_join, types::I8);
    let false8 = b.ins().iconst(types::I8, 0);
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins().brif(
        is_struct,
        struct_blk,
        &no_args,
        tuple_join,
        &[BlockArg::Value(false8)],
    );

    b.switch_to_block(struct_blk);
    b.seal_block(struct_blk);
    let struct_ref = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, value);
    let fref = jmod.declare_func_in_func(runtime.struct_schema_id_ref_id, b.func);
    let inst = b.ins().call(fref, &[struct_ref]);
    let schema_raw = b.inst_results(inst)[0];
    let schema64 = b.ins().uextend(types::I64, schema_raw);
    let mut tf: Option<ir::Value> = None;
    for arity in tuple_arities {
        if let Some(&sid) = tuple_schema_ids.get(arity) {
            let want = b.ins().iconst(types::I64, sid as i64);
            let schema_match = b.ins().icmp(IntCC::Equal, schema64, want);
            let combined = b.ins().band(is_struct, schema_match);
            tf = Some(match tf.take() {
                None => combined,
                Some(prev) => b.ins().bor(prev, combined),
            });
        }
    }
    let tr = tf.unwrap_or_else(|| b.ins().iconst(types::I8, 0));
    b.ins().jump(tuple_join, &[BlockArg::Value(tr)]);

    b.switch_to_block(tuple_join);
    b.seal_block(tuple_join);
    b.block_params(tuple_join)[0]
}

/// Lower a `Prim::BinOp` arithmetic op (Add/Sub/Mul/Div/Mod).
/// Three code paths: float coercion (int+float mix), typed fast path
/// (same-kind int or float), and tagged dispatch fallback that splits
/// on runtime tag tests.
fn lower_arith_binop<M, T>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    var_env: &HashMap<u32, CodegenValue>,
    _cache: &mut CodegenCache,
    runtime: &RuntimeRefs,
    op: BinOp,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
{
    let mop = op;
    let a_float = ty_is_float(t, fn_types, a);
    let b_float = ty_is_float(t, fn_types, bv);
    let a_int = ty_is_int(t, fn_types, a);
    let b_int = ty_is_int(t, fn_types, bv);
    let a_repr = var_env.get(&a.0).expect("binop lhs").repr();
    let b_repr = var_env.get(&bv.0).expect("binop rhs").repr();
    if !matches!(mop, BinOp::Mod)
        && (((a_float && b_int) || (a_int && b_float))
            || matches!(
                (a_repr, b_repr),
                (ArgRepr::RawF64, ArgRepr::RawInt) | (ArgRepr::RawInt, ArgRepr::RawF64)
            ))
    {
        let af = as_known_numeric_f64(var_env, b, a.0);
        let bf = as_known_numeric_f64(var_env, b, bv.0);
        return Ok(LowerOut::RawF64(match mop {
            BinOp::Add => b.ins().fadd(af, bf),
            BinOp::Sub => b.ins().fsub(af, bf),
            BinOp::Mul => b.ins().fmul(af, bf),
            BinOp::Div => b.ins().fdiv(af, bf),
            _ => unreachable!(),
        }));
    }
    // Typed fast paths: float (skipped for Mod) and int.
    if let Some(out) = try_typed_binop_fast_path(
        cx,
        t,
        fn_types,
        a,
        bv,
        b,
        jmod,
        runtime,
        var_env,
        |b, af, bf| {
            if matches!(mop, BinOp::Mod) {
                return None;
            }
            Some(LowerOut::RawF64(match mop {
                BinOp::Add => b.ins().fadd(af, bf),
                BinOp::Sub => b.ins().fsub(af, bf),
                BinOp::Mul => b.ins().fmul(af, bf),
                BinOp::Div => b.ins().fdiv(af, bf),
                _ => unreachable!(),
            }))
        },
        |b, ai, bi| {
            Some(LowerOut::RawI64(match mop {
                BinOp::Add => b.ins().iadd(ai, bi),
                BinOp::Sub => b.ins().isub(ai, bi),
                BinOp::Mul => b.ins().imul(ai, bi),
                BinOp::Div => b.ins().sdiv(ai, bi),
                BinOp::Mod => b.ins().srem(ai, bi),
                _ => unreachable!(),
            }))
        },
    ) {
        return Ok(out);
    }
    let av = *var_env.get(&a.0).expect("arith lhs");
    let bv_value = *var_env.get(&bv.0).expect("arith rhs");
    let a_is_int = codegen_value_is_tag(
        cx,
        b,
        jmod,
        runtime,
        av,
        fz_runtime::any_value::ValueKind::INT,
    );
    let b_is_int = codegen_value_is_tag(
        cx,
        b,
        jmod,
        runtime,
        bv_value,
        fz_runtime::any_value::ValueKind::INT,
    );
    let both_int = b.ins().band(a_is_int, b_is_int);
    let fast_blk = b.create_block();
    let slow_blk = b.create_block();
    let join_blk = b.create_block();
    b.append_block_param(join_blk, types::I64);
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins()
        .brif(both_int, fast_blk, &no_args, slow_blk, &no_args);

    b.switch_to_block(fast_blk);
    b.seal_block(fast_blk);
    let ai = codegen_value_raw_int(cx, b, jmod, runtime, av);
    let bi = codegen_value_raw_int(cx, b, jmod, runtime, bv_value);
    {
        let raw = match mop {
            BinOp::Add => b.ins().iadd(ai, bi),
            BinOp::Sub => b.ins().isub(ai, bi),
            BinOp::Mul => b.ins().imul(ai, bi),
            BinOp::Div => b.ins().sdiv(ai, bi),
            BinOp::Mod => b.ins().srem(ai, bi),
            _ => unreachable!(),
        };
        b.ins().jump(join_blk, &[BlockArg::Value(raw)]);
    }

    b.switch_to_block(slow_blk);
    b.seal_block(slow_blk);
    let unsupported_ref =
        jmod.declare_func_in_func(runtime.dynamic_float_arith_unsupported_id, b.func);
    let inst = b.ins().call(unsupported_ref, &[]);
    let slow_raw = b.inst_results(inst)[0];
    b.ins().jump(join_blk, &[BlockArg::Value(slow_raw)]);

    b.switch_to_block(join_blk);
    b.seal_block(join_blk);
    Ok(LowerOut::RawI64(b.block_params(join_blk)[0]))
}

/// Lower a `Prim::BinOp` Eq/Neq. Folds kind-disjoint operands to a
/// constant; otherwise picks native fcmp/icmp for same-kind float/int,
/// raw atom compare for atom/nil/bool pairs, or calls the runtime
/// value_eq_ref for the heterogeneous fallback.
fn lower_eq_binop<M, T>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    runtime: &RuntimeRefs,
    op: BinOp,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
    dest_var: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
{
    let is_eq = matches!(op, BinOp::Eq);
    let int_cc = if is_eq { IntCC::Equal } else { IntCC::NotEqual };
    let f_cc = if is_eq {
        FloatCC::Equal
    } else {
        FloatCC::NotEqual
    };

    // Kind-disjoint fold doesn't need either operand.
    if descrs_disjoint(t, fn_types, a, bv) {
        let raw = b.ins().iconst(
            types::I64,
            if is_eq {
                fz_runtime::any_value::FALSE_ATOM_ID as i64
            } else {
                fz_runtime::any_value::TRUE_ATOM_ID as i64
            },
        );
        return Ok(LowerOut::Strict(CodegenValue::known(
            raw,
            fz_runtime::any_value::ValueKind::ATOM,
        )));
    }
    let a_repr = var_env.get(&a.0).expect("eq lhs").repr();
    let b_repr = var_env.get(&bv.0).expect("eq rhs").repr();
    // Same-kind float: native fcmp on raw f64.
    if (ty_is_float(t, fn_types, a) && ty_is_float(t, fn_types, bv))
        || matches!((a_repr, b_repr), (ArgRepr::RawF64, ArgRepr::RawF64))
    {
        let af = as_raw_f64(cx, var_env, b, jmod, runtime, a.0);
        let bf = as_raw_f64(cx, var_env, b, jmod, runtime, bv.0);
        let cmp = b.ins().fcmp(f_cc, af, bf);
        if cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(b, cmp)));
    }
    // Same-kind int: native icmp on raw i64. Must not
    // mix raw and tagged operands — bit-eq is only
    // correct when both are in the same encoding.
    if ty_is_int(t, fn_types, a) && ty_is_int(t, fn_types, bv) {
        let ai = as_raw_i64(cx, var_env, b, jmod, runtime, a.0);
        let bi = as_raw_i64(cx, var_env, b, jmod, runtime, bv.0);
        let cmp = b.ins().icmp(int_cc, ai, bi);
        if cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(b, cmp)));
    }
    if (ty_is_atom(t, fn_types, a) && ty_is_atom(t, fn_types, bv))
        || (descr_is_nil_or_bool(t, fn_types, a) && descr_is_nil_or_bool(t, fn_types, bv))
    {
        let avp =
            codegen_value_raw_atom(cx, b, jmod, runtime, cache, binding_for_var(var_env, a.0));
        let bvp =
            codegen_value_raw_atom(cx, b, jmod, runtime, cache, binding_for_var(var_env, bv.0));
        let same_raw = b.ins().icmp(int_cc, avp, bvp);
        if cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(same_raw));
        }
        Ok(LowerOut::Strict(strict_bool(b, same_raw)))
    } else {
        let a_ref = tagged_get(cx, var_env, b, jmod, runtime, a.0, cache);
        let b_ref = tagged_get(cx, var_env, b, jmod, runtime, bv.0, cache);
        let fref = jmod.declare_func_in_func(runtime.value_eq_ref_id, b.func);
        let inst = b.ins().call(fref, &[a_ref, b_ref]);
        let eq = b.inst_results(inst)[0];
        let eq_bool = b.ins().icmp_imm(IntCC::NotEqual, eq, 0);
        let cmp = if is_eq {
            eq_bool
        } else {
            b.ins().bxor_imm(eq_bool, 1)
        };
        if cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        Ok(LowerOut::Strict(strict_bool(b, cmp)))
    }
}

/// Lower a `Prim::BinOp` ordered comparison (Lt/Le/Gt/Ge). Typed fast
/// paths emit native fcmp/icmp; the dispatch fallback splits on the
/// int-tag test and falls back to an inlined float promote+fcmp slow
/// path for any non-int-int operand mix.
fn lower_cmp_binop<M, T>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    t: &mut T,
    fn_types: &crate::ir_planner::SpecPlan,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    runtime: &RuntimeRefs,
    op: BinOp,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
    dest_var: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty>,
{
    let icc = match op {
        BinOp::Lt => IntCC::SignedLessThan,
        BinOp::Le => IntCC::SignedLessThanOrEqual,
        BinOp::Gt => IntCC::SignedGreaterThan,
        BinOp::Ge => IntCC::SignedGreaterThanOrEqual,
        _ => unreachable!(),
    };
    let fcc = match op {
        BinOp::Lt => FloatCC::LessThan,
        BinOp::Le => FloatCC::LessThanOrEqual,
        BinOp::Gt => FloatCC::GreaterThan,
        BinOp::Ge => FloatCC::GreaterThanOrEqual,
        _ => unreachable!(),
    };
    // Typed fast paths: float and int.
    // Safety: the two closures are mutually exclusive — only the
    // float arm fires for float operands and only the int arm fires
    // for int operands, so the two reborrow sites never alias.
    let dest_id = dest_var.0;
    let cache_ptr = cache as *mut CodegenCache;
    if let Some(out) = try_typed_binop_fast_path(
        cx,
        t,
        fn_types,
        a,
        bv,
        b,
        jmod,
        runtime,
        var_env,
        |b, af, bf| {
            let cmp = b.ins().fcmp(fcc, af, bf);
            let cache_ref = unsafe { &mut *cache_ptr };
            if cache_ref.if_only_conds.contains(&dest_id) {
                return Some(LowerOut::Condition(cmp));
            }
            Some(LowerOut::Strict(strict_bool(b, cmp)))
        },
        |b, ai, bi| {
            let cmp = b.ins().icmp(icc, ai, bi);
            let cache_ref = unsafe { &mut *cache_ptr };
            if cache_ref.if_only_conds.contains(&dest_id) {
                return Some(LowerOut::Condition(cmp));
            }
            Some(LowerOut::Strict(strict_bool(b, cmp)))
        },
    ) {
        return Ok(out);
    }
    let av = *var_env.get(&a.0).expect("cmp lhs");
    let bv_value = *var_env.get(&bv.0).expect("cmp rhs");
    let a_is_int = codegen_value_is_tag(
        cx,
        b,
        jmod,
        runtime,
        av,
        fz_runtime::any_value::ValueKind::INT,
    );
    let b_is_int = codegen_value_is_tag(
        cx,
        b,
        jmod,
        runtime,
        bv_value,
        fz_runtime::any_value::ValueKind::INT,
    );
    let both_int = b.ins().band(a_is_int, b_is_int);
    let fast_blk = b.create_block();
    let slow_blk = b.create_block();
    let join_blk = b.create_block();
    b.append_block_param(join_blk, types::I8);
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins()
        .brif(both_int, fast_blk, &no_args, slow_blk, &no_args);

    b.switch_to_block(fast_blk);
    b.seal_block(fast_blk);
    let ai = codegen_value_raw_int(cx, b, jmod, runtime, av);
    let bi = codegen_value_raw_int(cx, b, jmod, runtime, bv_value);
    let cmp = b.ins().icmp(icc, ai, bi);
    b.ins().jump(join_blk, &[BlockArg::Value(cmp)]);

    b.switch_to_block(slow_blk);
    b.seal_block(slow_blk);
    // Inlined float-cmp slow path: promote both operands
    // to f64 and emit native fcmp.
    let pfref = jmod.declare_func_in_func(runtime.promote_f64_id, b.func);
    let fcc = match op {
        BinOp::Lt => FloatCC::LessThan,
        BinOp::Le => FloatCC::LessThanOrEqual,
        BinOp::Gt => FloatCC::GreaterThan,
        BinOp::Ge => FloatCC::GreaterThanOrEqual,
        _ => unreachable!(),
    };
    let av = tagged_get(cx, var_env, b, jmod, runtime, a.0, cache);
    let bvv = tagged_get(cx, var_env, b, jmod, runtime, bv.0, cache);
    let i0 = b.ins().call(pfref, &[av]);
    let af = b.inst_results(i0)[0];
    let i1 = b.ins().call(pfref, &[bvv]);
    let bf = b.inst_results(i1)[0];
    let cmp = b.ins().fcmp(fcc, af, bf);
    b.ins().jump(join_blk, &[BlockArg::Value(cmp)]);

    b.switch_to_block(join_blk);
    b.seal_block(join_blk);
    Ok(LowerOut::Strict(strict_bool(
        b,
        b.block_params(join_blk)[0],
    )))
}

/// Lower a `Prim::BinOp` short-circuit-free boolean op (And/Or).
/// Both operands are coerced to truthy i8s and combined with
/// `band`/`bor`.
fn lower_bool_binop<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    op: BinOp,
    a: crate::fz_ir::Var,
    bv: crate::fz_ir::Var,
    dest_var: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError> {
    let av = *var_env.get(&a.0).expect("bool lhs");
    let bvv = *var_env.get(&bv.0).expect("bool rhs");
    let at = codegen_value_truthy(cx, b, jmod, runtime, av);
    let bt = codegen_value_truthy(cx, b, jmod, runtime, bvv);
    let combined = match op {
        BinOp::And => b.ins().band(at, bt),
        BinOp::Or => b.ins().bor(at, bt),
        _ => unreachable!(),
    };
    if cache.if_only_conds.contains(&dest_var.0) {
        return Ok(LowerOut::Condition(combined));
    }
    let _ = cache;
    Ok(LowerOut::Strict(strict_bool(b, combined)))
}

/// `fz_panic(value)`: forwards one ValueRef to the runtime fatal path.
fn lower_extern_fz_panic<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    args: &[crate::fz_ir::Var],
    dest_var: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError> {
    let value_ref = tagged_get(cx, var_env, b, jmod, runtime, args[0].0, cache);
    let sig = sig1(&[types::I64], &[]);
    let func_id = jmod
        .declare_function("fz_panic", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_panic: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    b.ins().call(fref, &[value_ref]);
    if cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(strict_const_value(
            b,
            fz_runtime::any_value::AnyValue::nil_atom(),
        )));
    }
    Ok(LowerOut::DeadUnit)
}

/// `fz_send(receiver, msg)`: marshals `msg` as a single ABI ValueRef
/// arg and forwards to `fz_send_ref`. The wrapper's declared return type
/// drives normal return coercion from this boxed ABI result.
fn lower_extern_fz_send<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    args: &[crate::fz_ir::Var],
) -> Result<LowerOut, CodegenError> {
    let receiver = as_raw_i64(cx, var_env, b, jmod, runtime, args[0].0);
    let msg_binding = *var_env.get(&args[1].0).expect("fz_send msg var");
    let mut msg_args = Vec::with_capacity(1);
    push_binding_as_abi_args(
        cx,
        &mut msg_args,
        b,
        jmod,
        runtime,
        cache,
        msg_binding,
        ArgRepr::ValueRef,
    );
    let msg_ref = msg_args[0];
    let sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let func_id = jmod
        .declare_function("fz_send_ref", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_send_ref: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    let inst = b.ins().call(fref, &[receiver, msg_ref]);
    Ok(LowerOut::ValueRefWord(b.inst_results(inst)[0]))
}

/// `fz_self()`: returns the current process id from `fz_self_raw`.
fn lower_extern_fz_self<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
) -> Result<LowerOut, CodegenError> {
    let sig = sig1(&[], &[types::I64]);
    let func_id = jmod
        .declare_function("fz_self_raw", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_self_raw: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    let inst = b.ins().call(fref, &[]);
    Ok(LowerOut::RawI64(b.inst_results(inst)[0]))
}

/// `fz_make_ref()`: allocates a fresh opaque ref via `fz_make_ref_raw`.
fn lower_extern_fz_make_ref<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
) -> Result<LowerOut, CodegenError> {
    let sig = sig1(&[], &[types::I64]);
    let func_id = jmod
        .declare_function("fz_make_ref_raw", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_make_ref_raw: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    let inst = b.ins().call(fref, &[]);
    Ok(LowerOut::RawI64(b.inst_results(inst)[0]))
}

/// `fz_spawn(closure)`: forwards the closure ref to `fz_spawn_ref`.
fn lower_extern_fz_spawn<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    args: &[crate::fz_ir::Var],
) -> Result<LowerOut, CodegenError> {
    let closure_ref = tagged_get(cx, var_env, b, jmod, runtime, args[0].0, cache);
    let sig = sig1(&[types::I64], &[types::I64]);
    let func_id = jmod
        .declare_function("fz_spawn_ref", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_spawn_ref: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    let inst = b.ins().call(fref, &[closure_ref]);
    Ok(LowerOut::RawI64(b.inst_results(inst)[0]))
}

/// `fz_spawn_opt(closure, min_heap_size)`: variant of `fz_spawn` that
/// also passes a heap-size hint through to `fz_spawn_opt_ref`.
fn lower_extern_fz_spawn_opt<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    args: &[crate::fz_ir::Var],
) -> Result<LowerOut, CodegenError> {
    let closure_ref = tagged_get(cx, var_env, b, jmod, runtime, args[0].0, cache);
    let min_heap_size = as_raw_i64(cx, var_env, b, jmod, runtime, args[1].0);
    let sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let func_id = jmod
        .declare_function("fz_spawn_opt_ref", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_spawn_opt_typed: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    let inst = b.ins().call(fref, &[closure_ref, min_heap_size]);
    Ok(LowerOut::RawI64(b.inst_results(inst)[0]))
}

/// `fz_make_resource(payload, dtor)`: builds a runtime resource with
/// the raw payload bits and the destructor closure ref.
fn lower_extern_fz_make_resource<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    args: &[crate::fz_ir::Var],
) -> Result<LowerOut, CodegenError> {
    let payload_raw = codegen_value_raw_int(
        cx,
        b,
        jmod,
        runtime,
        *var_env
            .get(&args[0].0)
            .expect("unbound make_resource payload"),
    );
    let dtor_ref = tagged_get(cx, var_env, b, jmod, runtime, args[1].0, cache);
    let sig = sig1(&[types::I64, types::I64], &[types::I64]);
    let func_id = jmod
        .declare_function("fz_make_resource_ref", Linkage::Import, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_make_resource_ref: {}", e)))?;
    let fref = jmod.declare_func_in_func(func_id, b.func);
    let inst = b.ins().call(fref, &[payload_raw, dtor_ref]);
    Ok(LowerOut::ValueRef(b.inst_results(inst)[0]))
}

/// Generic extern fallback: marshals each arg per its declared
/// `ExternTy`, looks up (or caches) the FuncRef, and packages the
/// return as RawI64 / ValueRef / nil / DeadUnit per the decl shape.
fn lower_extern_generic<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    cache: &mut CodegenCache,
    decl: &crate::fz_ir::ExternDecl,
    eid: &crate::fz_ir::ExternId,
    args: &[crate::fz_ir::ExternArg],
    dest_var: crate::fz_ir::Var,
) -> Result<LowerOut, CodegenError> {
    use crate::fz_ir::ExternTy;
    let param_tys: Vec<ir::Type> = decl
        .params
        .iter()
        .map(|t| match t {
            ExternTy::F64 => types::F64,
            _ => types::I64,
        })
        .collect();
    let returns_value = !matches!(decl.ret, ExternTy::Unit | ExternTy::Never);
    let ret_tys: &[ir::Type] = if returns_value {
        match decl.ret {
            ExternTy::F64 => &[types::F64],
            _ => &[types::I64],
        }
    } else {
        &[]
    };
    let sig = sig1(&param_tys, ret_tys);
    let fref = if let Some(&cached) = cache.extern_funcs.get(eid) {
        cached
    } else {
        let func_id = jmod
            .declare_function(&decl.symbol, Linkage::Import, &sig)
            .map_err(|e| CodegenError::new(format!("declare extern `{}`: {}", decl.symbol, e)))?;
        let fref = jmod.declare_func_in_func(func_id, b.func);
        cache.extern_funcs.insert(*eid, fref);
        fref
    };
    let param_kinds: Vec<ExternTy> = decl.params.clone();
    // Arity is enforced in ir_lower; this assert is
    // defense-in-depth so a future caller that bypasses lowering
    // can't silently truncate args via `.zip()`.
    assert_eq!(
        args.len(),
        param_kinds.len(),
        "extern `{}` codegen: arg count {} != param count {}",
        decl.symbol,
        args.len(),
        param_kinds.len()
    );
    let arg_vals: Vec<ir::Value> = args
        .iter()
        .zip(param_kinds.iter())
        .map(|(v, ty)| marshal_extern_arg(cx, b, jmod, runtime, var_env, cache, v.var, *ty))
        .collect::<Result<_, _>>()?;
    let inst = b.ins().call(fref, &arg_vals);
    if returns_value {
        let raw = b.inst_results(inst)[0];
        if matches!(decl.ret, ExternTy::I64) {
            return Ok(LowerOut::RawI64(raw));
        }
        return Ok(LowerOut::ValueRef(raw));
    }
    if cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(strict_const_value(
            b,
            fz_runtime::any_value::AnyValue::nil_atom(),
        )));
    }
    Ok(LowerOut::DeadUnit)
}

/// Lower a `Prim::MakeClosure`. Three code paths: null-stub (no body
/// spec registered), zero-capture singleton, and non-zero capture
/// alloc+populate. Resolves the narrow SpecId via the lambda's full
/// input-type key (captures from caller's `fn_types`, args = `any`).
pub(crate) fn lower_make_closure<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    var_env: &HashMap<u32, CodegenValue>,
    fn_ids: &HashMap<u32, FuncId>,
    spec_registry: &SpecRegistry,
    param_reprs: &[Vec<ArgRepr>],
    return_reprs: &[ArgRepr],
    mk_ident: &crate::fz_ir::CallsiteIdent,
    fn_id: crate::fz_ir::FnId,
    captured: &[crate::fz_ir::Var],
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
) -> Result<LowerOut, CodegenError> {
    // Allocate a closure env, store the body code pointer, then
    // write captures through the runtime's schema-backed accessor.
    // Resolve the narrow SpecId via the lambda's full input-type
    // key (captures from caller's `fn_types`, args = `any`) and
    // pick the typed stub keyed by that SpecId.
    let n_caps = captured.len();
    // The lambda body is the any-key body spec (SpecId.0 ==
    // FnId.0). Look up directly; fall back to any registered
    // narrow spec for this FnId when the any-key was dropped;
    // emit a null-stub closure when neither exists (value is
    // constructable but unreachable as a call target).
    let _ = (block_id, stmt_idx, mk_ident);
    let cl_sid_opt = if fn_ids.contains_key(&fn_id.0) {
        Some(fn_id.0)
    } else {
        spec_registry
            .iter()
            .find(|(s, key)| key.fn_id == fn_id && fn_ids.contains_key(&s.0))
            .map(|(s, _)| s.0)
    };
    let Some(cl_sid) = cl_sid_opt else {
        return Ok(LowerOut::ValueRef(emit_null_stub_closure(
            b, jmod, runtime, fn_id, n_caps,
        )));
    };
    // Zero-capture MakeClosure: look up the per-Process static
    // singleton instead of allocating per call site. The
    // singleton's code pointer holds the closure-target body
    // address. See docs/cps-in-clif.md §8.2.
    if captured.is_empty() {
        return Ok(LowerOut::ValueRef(fetch_static_closure(
            jmod, b, runtime, cl_sid,
        )));
    }
    Ok(LowerOut::ValueRef(emit_capturing_closure(
        cx,
        b,
        jmod,
        runtime,
        cache,
        var_env,
        fn_ids,
        param_reprs,
        return_reprs,
        fn_id,
        cl_sid,
        captured,
    )?))
}

/// Null-code closure: alloc, write null code pointer, leave capture
/// slots uninitialized (the body that would read them doesn't exist).
/// halt_kind is irrelevant for an un-invoked closure; pick 0.
fn emit_null_stub_closure<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    fn_id: crate::fz_ir::FnId,
    n_caps: usize,
) -> ir::Value {
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
    let fid_v = b.ins().iconst(types::I32, fn_id.0 as i64);
    let nc_v = b.ins().iconst(types::I32, n_caps as i64);
    let hk_v = b.ins().iconst(types::I32, 0);
    let null = b.ins().iconst(types::I64, 0);
    let inst = b.ins().call(alloc_fref, &[fid_v, nc_v, hk_v, null]);
    b.inst_results(inst)[0]
}

/// Non-zero captures: alloc closure heap object, write body's
/// func_addr, and store captures as env fields. The body has
/// closure-target sig `(args..., self, cont) tail` and projects
/// captures from `self` in its entry harness.
fn emit_capturing_closure<M: cranelift_module::Module>(
    cx: &mut CodegenFn<'_>,
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    runtime: &RuntimeRefs,
    cache: &mut CodegenCache,
    var_env: &HashMap<u32, CodegenValue>,
    fn_ids: &HashMap<u32, FuncId>,
    param_reprs: &[Vec<ArgRepr>],
    return_reprs: &[ArgRepr],
    fn_id: crate::fz_ir::FnId,
    cl_sid: u32,
    captured: &[crate::fz_ir::Var],
) -> Result<ir::Value, CodegenError> {
    let n_caps = captured.len();
    let body_func_id = *fn_ids.get(&cl_sid).ok_or_else(|| {
        CodegenError::new(format!(
            "no body FuncId for closure SpecId({}) \
             (FnId({}), {} captures)",
            cl_sid, fn_id.0, n_caps
        ))
    })?;
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_closure_id, b.func);
    let fid_v = b.ins().iconst(types::I32, fn_id.0 as i64);
    let nc_v = b.ins().iconst(types::I32, n_caps as i64);
    // halt_kind from body's return repr so fz_spawn_entry can
    // pick the matching halt-cont singleton.
    let body_return_repr = return_reprs[cl_sid as usize];
    let hk_v = b
        .ins()
        .iconst(types::I32, body_return_repr.halt_kind() as i64);
    let body_addr = fn_addr(jmod, body_func_id, b);
    let inst = b.ins().call(alloc_fref, &[fid_v, nc_v, hk_v, body_addr]);
    let cl_ptr = b.inst_results(inst)[0];
    // The closure env stores captures as opaque refs. The body's
    // entry harness coerces each capture to its narrow repr.
    for (i, cv) in captured.iter().enumerate() {
        let vb = var_env
            .get(&cv.0)
            .expect("MakeClosure: captured var unbound");
        let to = param_reprs[cl_sid as usize][i];
        if to == ArgRepr::ValueRef {
            let capture = codegen_value_as_any_ref(cx, b, jmod, runtime, cache, *vb);
            store_closure_capture_ref_word(cx, b, jmod, runtime, cl_ptr, n_caps, i, capture);
        } else {
            let mut capture = Vec::with_capacity(1);
            push_binding_as_abi_args(
                cx,
                &mut capture,
                b,
                jmod,
                runtime,
                cache,
                *vb,
                ArgRepr::ValueRef,
            );
            store_closure_capture_ref_word(cx, b, jmod, runtime, cl_ptr, n_caps, i, capture[0]);
        }
    }
    Ok(cl_ptr)
}
