//! Primitive lowering helpers for codegen.

use super::runtime_test::{KindEvidence, RuntimeTestEmitter, emit_runtime_type_test};
use super::*;
use crate::finite_set::FiniteSet;
use crate::fz_ir::{
    BinOp, BitSizeIr, BlockId, Const, ExternArg, ExternDecl, ExternId, ExternMarshalSite, ExternTy, FnId, Prim, UnOp,
    Var,
};
use crate::runtime_type_predicate::{RuntimeTypePredicate, lowering_tests_position};
use crate::types::ClosureTarget;
use cranelift_codegen::ir::{
    self, BlockArg, InstBuilder, MemFlags,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage};
use fz_runtime::any_value::{AnyValue, FALSE_ATOM_ID, TRUE_ATOM_ID, ValueKind, struct_size_for_payload};
use fz_runtime::heap::SHARED_BIN_THRESHOLD_BYTES;
use fz_runtime::ir_runtime::fz_bs_field_spec;
use std::collections::HashMap;

pub(crate) fn emit_map_get_value_ref_for_key<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    map: Var,
    key: Var,
    block_env: Option<&HashMap<Var, Ty>>,
) -> ir::Value {
    let runtime = env.runtime;
    let value_types = env.active_value_types();
    let map_ref = body.tagged_var(var_env, map.0);
    let process = body.process_arg();
    let key_kind = expected_runtime_value_kind(t, value_types, block_env, key);
    match key_kind {
        Some(ValueKind::ATOM) => {
            let kv = body.value_raw_atom(binding_for_var(var_env, key.0));
            let fref = body
                .jmod
                .declare_func_in_func(runtime.map_get_atom_key_ref_id, body.b.func);
            let inst = body.b.ins().call(fref, &[process, map_ref, kv]);
            body.b.inst_results(inst)[0]
        }
        Some(ValueKind::INT) => {
            let kv = body.value_raw_int(binding_for_var(var_env, key.0));
            let fref = body
                .jmod
                .declare_func_in_func(runtime.map_get_int_key_ref_id, body.b.func);
            let inst = body.b.ins().call(fref, &[process, map_ref, kv]);
            body.b.inst_results(inst)[0]
        }
        Some(ValueKind::FLOAT) => {
            let key_float = body.value_raw_float(binding_for_var(var_env, key.0));
            let fref = body
                .jmod
                .declare_func_in_func(runtime.map_get_float_key_ref_id, body.b.func);
            let inst = body.b.ins().call(fref, &[process, map_ref, key_float]);
            body.b.inst_results(inst)[0]
        }
        _ => {
            let fref = body.jmod.declare_func_in_func(runtime.map_get_ref_id, body.b.func);
            let key_ref = body.tagged_var(var_env, key.0);
            let inst = body.b.ins().call(fref, &[process, map_ref, key_ref]);
            body.b.inst_results(inst)[0]
        }
    }
}

fn emit_map_destination_put<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    map_bits: ir::Value,
    key: CodegenValue,
    value: CodegenValue,
) {
    if let (Some((key_raw, key_kind)), Some((value_raw, value_kind))) =
        (value_raw_kind_parts(body, key), value_raw_kind_parts(body, value))
        && key_kind.is_scalar()
        && value_kind.is_scalar()
    {
        let fref = body
            .jmod
            .declare_func_in_func(runtime.map_dest_put_parts_id, body.b.func);
        let key_kind = body.b.ins().iconst(types::I64, key_kind.tag() as i64);
        let value_kind = body.b.ins().iconst(types::I64, value_kind.tag() as i64);
        let process = body.process_arg();
        body.b
            .ins()
            .call(fref, &[process, map_bits, key_raw, key_kind, value_raw, value_kind]);
    } else {
        let key_ref = body.value_as_any_ref(key);
        let value_ref = body.value_as_any_ref(value);
        let key_ref = body.mark_published_ref_aliased(key_ref);
        let value_ref = body.mark_published_ref_aliased(value_ref);
        let fref = body.jmod.declare_func_in_func(runtime.map_dest_put_ref_id, body.b.func);
        let process = body.process_arg();
        body.b.ins().call(fref, &[process, map_bits, key_ref, value_ref]);
    }
}

pub(crate) fn emit_list_cons_bif<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    head: Var,
    head_kind: Option<ValueKind>,
    tail: ListTailBits,
) -> ir::Value {
    let runtime = env.runtime;
    let tail_ref = body.list_tail_ref_word(tail);
    let head_value = binding_for_var(var_env, head.0);
    let (func_id, args): (FuncId, Vec<ir::Value>) = match head_kind {
        Some(ValueKind::INT) => (runtime.list_cons_int_id, vec![body.value_raw_int(head_value), tail_ref]),
        Some(ValueKind::FLOAT) => (
            runtime.list_cons_float_id,
            vec![body.value_raw_float(head_value), tail_ref],
        ),
        Some(ValueKind::ATOM) => (
            runtime.list_cons_atom_id,
            vec![body.value_raw_atom(head_value), tail_ref],
        ),
        None if matches!(
            head_value,
            CodegenValue::RawInt(_)
                | CodegenValue::Known {
                    kind: ValueKind::INT,
                    ..
                }
        ) =>
        {
            (runtime.list_cons_int_id, vec![body.value_raw_int(head_value), tail_ref])
        }
        None if matches!(
            head_value,
            CodegenValue::RawF64(_)
                | CodegenValue::Known {
                    kind: ValueKind::FLOAT,
                    ..
                }
        ) =>
        {
            (
                runtime.list_cons_float_id,
                vec![body.value_raw_float(head_value), tail_ref],
            )
        }
        None if matches!(
            head_value,
            CodegenValue::Known {
                kind: ValueKind::ATOM,
                ..
            } | CodegenValue::RawAtom(_)
        ) =>
        {
            (
                runtime.list_cons_atom_id,
                vec![body.value_raw_atom(head_value), tail_ref],
            )
        }
        None => (
            runtime.list_cons_any_id,
            vec![body.value_as_any_ref(head_value), tail_ref],
        ),
        _ => (
            runtime.list_cons_any_id,
            vec![body.value_as_any_ref(head_value), tail_ref],
        ),
    };
    body.list_cons_with(func_id, &args)
}

fn static_literal_field_for_var(
    cache: &CodegenCache,
    var_env: &HashMap<u32, CodegenValue>,
    var: Var,
) -> Option<StaticLiteralField> {
    if !var_env.contains_key(&var.0) {
        return None;
    }
    if let Some(value) = cache.static_scalar_consts.get(&var.0) {
        return match value {
            AnyValue::HeapRef(_) => None,
            value => Some(StaticLiteralField::Scalar(*value)),
        };
    }
    cache
        .static_struct_refs
        .get(&var.0)
        .map(|static_ref| StaticLiteralField::Struct(static_ref.data_id))
}

fn try_static_struct_literal<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    dest_var: Var,
    schema_id: u32,
    fields: &[Var],
) -> Result<Option<ir::Value>, CodegenError> {
    let Some(static_fields) = fields
        .iter()
        .map(|field| static_literal_field_for_var(body.cache, var_env, *field))
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(None);
    };

    let data_id = define_static_struct_literal(body, env, dest_var, schema_id, &static_fields)?;
    Ok(Some(static_struct_ref_word(body, dest_var, data_id)))
}

fn define_static_struct_literal<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    dest_var: Var,
    schema_id: u32,
    fields: &[StaticLiteralField],
) -> Result<DataId, CodegenError> {
    let raw_bytes = fields.len() * SLOT_BYTES as usize;
    let kind_bytes = (fields.len() + 7) & !7;
    let payload_size = raw_bytes + kind_bytes;
    let total_size = struct_size_for_payload(payload_size);
    let mut buf = vec![0u8; total_size];
    buf[0..4].copy_from_slice(&schema_id.to_le_bytes());
    buf[4..8].copy_from_slice(&0u32.to_le_bytes());

    let mut child_relocs = Vec::new();
    let raw_base = 8;
    let kind_base = raw_base + raw_bytes;
    for (idx, field) in fields.iter().enumerate() {
        let raw_offset = raw_base + idx * SLOT_BYTES as usize;
        let kind_offset = kind_base + idx;
        match *field {
            StaticLiteralField::Scalar(value) => {
                buf[raw_offset..raw_offset + SLOT_BYTES as usize].copy_from_slice(&value.raw().to_le_bytes());
                buf[kind_offset] = value.kind().tag();
            }
            StaticLiteralField::Struct(data_id) => {
                child_relocs.push((raw_offset, data_id));
                buf[kind_offset] = ValueKind::STRUCT.tag();
            }
        }
    }

    let idx = body.cache.static_struct_count;
    body.cache.static_struct_count += 1;
    let name = format!(
        ".fz_static_struct_{}_{}_{}_{}",
        env.active_body_fn_id.0, env.active_spec_id, dest_var.0, idx
    );
    let data_id = body
        .jmod
        .declare_data(&name, Linkage::Local, /*writable=*/ false, false)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
    let mut desc = DataDescription::new();
    desc.define(buf.into_boxed_slice());
    desc.set_align(16);
    for (offset, child_id) in child_relocs {
        let child_gv = body.jmod.declare_data_in_data(child_id, &mut desc);
        desc.write_data_addr(offset as u32, child_gv, 0);
    }
    body.jmod
        .define_data(data_id, &desc)
        .map_err(|e| CodegenError::new(format!("define {}: {}", name, e)))?;
    Ok(data_id)
}

fn static_struct_ref_word<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    dest_var: Var,
    data_id: DataId,
) -> ir::Value {
    let gv = body.jmod.declare_data_in_func(data_id, body.b.func);
    let addr = body.b.ins().symbol_value(types::I64, gv);
    let ref_word = body.heap_ref_word_from_addr(addr, ValueKind::STRUCT);
    body.cache
        .static_struct_refs
        .insert(dest_var.0, StaticStructRef { data_id });
    ref_word
}

fn alloc_struct_for_schema<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    schema_id: u32,
) -> ir::Value {
    let fref = body.jmod.declare_func_in_func(runtime.alloc_struct_id, body.b.func);
    let sid = body.b.ins().iconst(types::I32, schema_id as i64);
    let process = body.process_arg();
    let inst = body.b.ins().call(fref, &[process, sid]);
    body.b.inst_results(inst)[0]
}

/// Lower collection-typed Prim variants (List, Tuple, AllocStruct, Bitstring,
/// Map, Vec) to a tagged `ir::Value`. Called by `lower_prim` for these arms.
pub(crate) fn lower_collection_prim<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    dest_var: Var,
    block_id: BlockId,
    block_env: Option<&HashMap<Var, Ty>>,
) -> Result<LowerOut, CodegenError> {
    let runtime = env.runtime;
    let value_types = env.active_value_types();
    let tuple_schema_ids = env.tuple_schema_ids;
    let v: LowerOut = match prim {
        Prim::ListHead(c) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            LowerOut::ValueRefWord(body.list_head(list_ref))
        }
        Prim::ListTail(c) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            LowerOut::ValueRefWord(body.list_tail(list_ref))
        }
        Prim::MakeList(elems, tail) => {
            if elems.len() == 1
                && let Some(tail_var) = tail
            {
                let tail_bits = body.any_ref_for_var(var_env, tail_var.0);
                let tail = list_tail_bits_for_var(t, value_types, block_env, *tail_var, tail_bits);
                let reused = emit_reusable_cons_or_alloc(body, var_env, elems[0], tail);
                if let Some(reused) = reused {
                    return Ok(LowerOut::ValueRef(reused));
                }
            }
            // Default tail of a list-literal is the empty list (`[]`),
            // NOT the nil atom value — distinct runtime bit patterns.
            let mut acc = match tail {
                Some(tail_var) => {
                    let tail_bits = body.any_ref_for_var(var_env, tail_var.0);
                    list_tail_bits_for_var(t, value_types, block_env, *tail_var, tail_bits)
                }
                None => ListTailBits::Empty,
            };
            for e in elems.iter().rev() {
                let cons = emit_list_cons_bif(
                    body,
                    env,
                    var_env,
                    *e,
                    expected_runtime_value_kind(t, value_types, block_env, *e),
                    acc,
                );
                acc = ListTailBits::NonEmptyValueRef(cons);
            }
            match acc {
                ListTailBits::NonEmptyValueRef(bits) | ListTailBits::ValueRef(bits) => LowerOut::ValueRef(bits),
                ListTailBits::Empty => LowerOut::ValueRefWord(body.empty_list_ref()),
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
            if let Some(static_ref) = try_static_struct_literal(body, env, var_env, dest_var, schema_id, elems)? {
                return Ok(LowerOut::ValueRefWord(static_ref));
            }
            let p = alloc_struct_for_schema(body, runtime, schema_id);
            for (i, e) in elems.iter().enumerate() {
                let value = binding_for_var(var_env, e.0);
                body.struct_set_field(p, i, value);
            }
            LowerOut::ValueRef(p)
        }
        Prim::MakeStruct { module, fields } => {
            let schema_id = *env.named_schema_ids.get(module).ok_or_else(|| {
                CodegenError::new(format!(
                    "struct schema {} not pre-registered (compile() walk missed it?)",
                    module
                ))
            })?;
            let field_vars = fields.iter().map(|(_, field_var)| *field_var).collect::<Vec<_>>();
            if let Some(static_ref) = try_static_struct_literal(body, env, var_env, dest_var, schema_id, &field_vars)? {
                return Ok(LowerOut::ValueRefWord(static_ref));
            }
            let p = alloc_struct_for_schema(body, runtime, schema_id);
            for (i, (_, field_var)) in fields.iter().enumerate() {
                let value = binding_for_var(var_env, field_var.0);
                body.struct_set_field(p, i, value);
            }
            LowerOut::ValueRef(p)
        }
        Prim::TupleField(c, idx) => {
            if let Some(binding) = body.cache.tuple_field_params.get(&(c.0, *idx)).copied() {
                return Ok(lower_out_for_codegen_value(binding));
            }
            // Every TupleField is gated by a preceding runtime type-test predicate
            // that runtime-checks the subject is a matching-arity Struct
            // heap value, so the load is provably safe. A SIGSEGV here
            // would be an IR integrity bug worth surfacing loudly — do
            // NOT add `notrap`, which would silently mask it.
            let fref = body.jmod.declare_func_in_func(runtime.struct_get_field_id, body.b.func);
            let field_offset = body.b.ins().iconst(types::I32, (*idx as i64) * SLOT_BYTES as i64);
            let struct_ref = body.tagged_var(var_env, c.0);
            let process = body.process_arg();
            let inst = body.b.ins().call(fref, &[process, struct_ref, field_offset]);
            LowerOut::ValueRefWord(body.b.inst_results(inst)[0])
        }
        Prim::StructField(c, field) => {
            let atom_id = env
                .module
                .atom_names
                .iter()
                .position(|name| name == field)
                .ok_or_else(|| CodegenError::new(format!("field atom `{}` not interned", field)))?;
            let fref = body
                .jmod
                .declare_func_in_func(runtime.struct_get_named_field_id, body.b.func);
            let struct_ref = body.tagged_var(var_env, c.0);
            let process = body.process_arg();
            let atom = body.b.ins().iconst(types::I64, atom_id as i64);
            let inst = body.b.ins().call(fref, &[process, struct_ref, atom]);
            LowerOut::ValueRefWord(body.b.inst_results(inst)[0])
        }
        Prim::MakeBitstring(fields) => {
            let begin = body.jmod.declare_func_in_func(runtime.bs_begin_id, body.b.func);
            let process = body.process_arg();
            body.b.ins().call(begin, &[process]);
            let write = body.jmod.declare_func_in_func(runtime.bs_write_ref_id, body.b.func);
            for f in fields {
                let value_ref = body.tagged_var(var_env, f.value.0);
                let ty_tag = body.b.ins().iconst(types::I32, encode_bit_type(f.ty) as i64);
                let unit = body
                    .b
                    .ins()
                    .iconst(types::I32, f.unit.unwrap_or(default_unit_for(f.ty)) as i64);
                let endian = body.b.ins().iconst(types::I32, encode_endian(f.endian) as i64);
                let signed = body.b.ins().iconst(types::I32, f.signed as i64);
                let (size_present, size_value) = match &f.size {
                    None => (body.b.ins().iconst(types::I32, 0), body.b.ins().iconst(types::I32, 0)),
                    Some(BitSizeIr::Literal(n)) => (
                        body.b.ins().iconst(types::I32, 1),
                        body.b.ins().iconst(types::I32, *n as i64),
                    ),
                    Some(BitSizeIr::Var(v)) => {
                        let unb = body.as_raw_i64(var_env, v.0);
                        let truncated = body.b.ins().ireduce(types::I32, unb);
                        (body.b.ins().iconst(types::I32, 1), truncated)
                    }
                };
                body.b.ins().call(
                    write,
                    &[
                        process,
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
            let fin = body.jmod.declare_func_in_func(runtime.bs_finalize_id, body.b.func);
            let process = body.process_arg();
            let inst = body.b.ins().call(fin, &[process]);
            LowerOut::ValueRef(body.b.inst_results(inst)[0])
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
            let above_threshold = bytes.len() > SHARED_BIN_THRESHOLD_BYTES;
            let syms = {
                let mut bs_cache = env.bs_const_data.borrow_mut();
                if let Some(syms) = bs_cache.get(bytes) {
                    // Cached. If the existing entry lacks the SharedBin
                    // symbol but this call site needs it, populate now.
                    let mut syms = *syms;
                    if above_threshold && syms.sharedbin_id.is_none() {
                        syms.sharedbin_id = Some(define_static_sharedbin(
                            body.jmod,
                            runtime,
                            syms.bytes_id,
                            bytes,
                            *bit_len,
                            bs_cache.len(),
                        )?);
                        bs_cache.insert(bytes.clone(), syms);
                    }
                    syms
                } else {
                    let idx = bs_cache.len();
                    let bytes_name = format!(".fz_bs_const_{}", idx);
                    let bytes_id = body
                        .jmod
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
                    body.jmod
                        .define_data(bytes_id, &desc)
                        .map_err(|e| CodegenError::new(format!("define {}: {}", bytes_name, e)))?;
                    let sharedbin_id = if above_threshold {
                        Some(define_static_sharedbin(
                            body.jmod, runtime, bytes_id, bytes, *bit_len, idx,
                        )?)
                    } else {
                        None
                    };
                    let syms = BsConstSyms { bytes_id, sharedbin_id };
                    bs_cache.insert(bytes.clone(), syms);
                    syms
                }
            };
            if let Some(sb_id) = syms.sharedbin_id {
                let gv = body.jmod.declare_data_in_func(sb_id, body.b.func);
                let sb_ptr = body.b.ins().symbol_value(types::I64, gv);
                let fref = body
                    .jmod
                    .declare_func_in_func(runtime.alloc_procbin_from_static_id, body.b.func);
                let process = body.process_arg();
                let inst = body.b.ins().call(fref, &[process, sb_ptr]);
                LowerOut::ValueRef(body.b.inst_results(inst)[0])
            } else {
                let gv = body.jmod.declare_data_in_func(syms.bytes_id, body.b.func);
                let ptr_v = body.b.ins().symbol_value(types::I64, gv);
                let byte_len_v = body.b.ins().iconst(types::I64, bytes.len() as i64);
                let bit_len_v = body.b.ins().iconst(types::I64, *bit_len as i64);
                let fref = body
                    .jmod
                    .declare_func_in_func(runtime.alloc_bitstring_const_id, body.b.func);
                let process = body.process_arg();
                let inst = body.b.ins().call(fref, &[process, ptr_v, byte_len_v, bit_len_v]);
                LowerOut::ValueRef(body.b.inst_results(inst)[0])
            }
        }
        Prim::BitReaderInit(v) => {
            let value_ref = body.tagged_var(var_env, v.0);
            let process = body.process_arg();
            let fref = body
                .jmod
                .declare_func_in_func(runtime.bs_reader_init_ref_id, body.b.func);
            let inst = body.b.ins().call(fref, &[process, value_ref]);
            LowerOut::ValueRef(body.b.inst_results(inst)[0])
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
            let reader_ref = body.tagged_var(var_env, reader.0);
            let (size_present, size_value) = match size {
                None => (0, body.b.ins().iconst(types::I32, 0)),
                Some(BitSizeIr::Literal(n)) => (1, body.b.ins().iconst(types::I32, *n as i64)),
                Some(BitSizeIr::Var(v)) => {
                    let unb = body.as_raw_i64(var_env, v.0);
                    let truncated = body.b.ins().ireduce(types::I32, unb);
                    (1, truncated)
                }
            };
            let field_spec = fz_bs_field_spec(
                encode_bit_type(*ty),
                size_present,
                unit.unwrap_or(default_unit_for(*ty)),
                encode_endian(*endian),
                *signed as u32,
                *is_last as u32,
            );
            let field_spec = body.b.ins().iconst(types::I64, field_spec as i64);
            let process = body.process_arg();
            let fref = body
                .jmod
                .declare_func_in_func(runtime.bs_read_field_ref_id, body.b.func);
            let inst = body.b.ins().call(fref, &[process, reader_ref, field_spec, size_value]);
            LowerOut::ValueRef(body.b.inst_results(inst)[0])
        }
        Prim::DestMapBegin { base, extra, .. } => {
            let extra = body.b.ins().iconst(types::I32, *extra as i64);
            if let Some(base) = base {
                let base_bits = body.any_ref_for_var(var_env, base.0);
                let fref = body
                    .jmod
                    .declare_func_in_func(runtime.map_dest_begin_update_id, body.b.func);
                let process = body.process_arg();
                let inst = body.b.ins().call(fref, &[process, base_bits, extra]);
                LowerOut::ValueRef(body.b.inst_results(inst)[0])
            } else {
                let fref = body.jmod.declare_func_in_func(runtime.map_dest_begin_id, body.b.func);
                let process = body.process_arg();
                let inst = body.b.ins().call(fref, &[process, extra]);
                LowerOut::ValueRef(body.b.inst_results(inst)[0])
            }
        }
        Prim::DestMapPut { map, key, value, .. } => {
            let map_bits = body.any_ref_for_var(var_env, map.0);
            let key = binding_for_var(var_env, key.0);
            let value = binding_for_var(var_env, value.0);
            emit_map_destination_put(body, runtime, map_bits, key, value);
            LowerOut::DeadUnit
        }
        Prim::DestMapFreeze { map, .. } => {
            let map_bits = body.any_ref_for_var(var_env, map.0);
            let fref = body.jmod.declare_func_in_func(runtime.map_dest_freeze_id, body.b.func);
            let process = body.process_arg();
            let inst = body.b.ins().call(fref, &[process, map_bits]);
            LowerOut::ValueRef(body.b.inst_results(inst)[0])
        }
        Prim::MapGet(m, k) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k, block_env);
            LowerOut::ValueRefWord(value_ref)
        }
        Prim::MatcherMapGet(m, k) => {
            let fref = body
                .jmod
                .declare_func_in_func(runtime.matcher_map_get_ref_id, body.b.func);
            let map_ref = body.tagged_var(var_env, m.0);
            let key_ref = body.tagged_var(var_env, k.0);
            let process = body.process_arg();
            let inst = body.b.ins().call(fref, &[process, map_ref, key_ref]);
            LowerOut::ValueRefWord(body.b.inst_results(inst)[0])
        }
        Prim::IsMatcherMapMiss(v) => {
            let value_ref = body.tagged_var(var_env, v.0);
            let tag = body.ref_tag(value_ref);
            let is_miss = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::NULL.tag() as i64);
            LowerOut::Strict(strict_bool(body.b, is_miss))
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
        CodegenValue::RawAtom(_) => LowerOut::Strict(value),
        CodegenValue::Condition(v) => LowerOut::Condition(v),
    }
}

#[allow(clippy::too_many_arguments)]
fn marshal_extern_arg<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    var: Var,
    ty: ExternTy,
) -> Result<ir::Value, CodegenError> {
    Ok(match ty {
        ExternTy::I64 => body.as_raw_i64(var_env, var.0),
        ExternTy::F64 => body.as_raw_f64(var_env, var.0),
        ExternTy::Binary | ExternTy::CString => {
            let helper_id = match ty {
                ExternTy::CString => runtime.binary_as_cstring_id,
                _ => runtime.binary_as_ptr_id,
            };
            let helper_fref = body.jmod.declare_func_in_func(helper_id, body.b.func);
            let bits = body.tagged_var(var_env, var.0);
            let call = body.b.ins().call(helper_fref, &[bits]);
            body.b.inst_results(call)[0]
        }
        ExternTy::Any => body.tagged_var(var_env, var.0),
        ExternTy::Unit | ExternTy::Never => {
            return Err(CodegenError::new(format!(
                "{:?} is not a valid extern argument marshal class",
                ty
            )));
        }
    })
}

fn format_extern_shape(ret: ExternTy, fixed: &[ExternTy], variadic: &[ExternTy]) -> String {
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
    ret: ExternTy,
    fixed: &[ExternTy],
    variadic: &[ExternTy],
) -> Result<FuncId, CodegenError> {
    match (ret, fixed, variadic) {
        (ExternTy::I64, [ExternTy::CString, ExternTy::I64], [ExternTy::I64]) => {
            Ok(runtime.extern_var_i64_cstring_i64_i64_to_i64_id)
        }
        (ExternTy::I64, [ExternTy::CString], [ExternTy::I64]) => Ok(runtime.extern_var_i64_cstring_i64_to_i64_id),
        _ => Err(CodegenError::new(format!(
            "unsupported variadic extern shape: {}",
            format_extern_shape(ret, fixed, variadic)
        ))),
    }
}

fn emit_extern_symbol_name<M: cranelift_module::Module>(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut M,
    caller_fn_id: FnId,
    block_id: BlockId,
    stmt_idx: usize,
    symbol: &str,
) -> Result<ir::Value, CodegenError> {
    if symbol.as_bytes().contains(&0) {
        return Err(CodegenError::new(format!(
            "extern symbol `{}` contains a NUL byte",
            symbol
        )));
    }
    let name = format!(".fz_extern_symbol_{}_{}_{}", caller_fn_id.0, block_id.0, stmt_idx);
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
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    eid: ExternId,
    args: &[ExternArg],
    dest_var: Var,
    caller_fn_id: FnId,
    block_id: BlockId,
    stmt_idx: usize,
) -> Result<LowerOut, CodegenError> {
    let decl = env.module.extern_by_id(eid);
    let mut arg_tys = Vec::with_capacity(args.len());
    for arg_idx in 0..args.len() {
        let site = ExternMarshalSite {
            block: block_id,
            stmt_idx,
            arg_idx,
        };
        let Some(&ty) = env.active_native_body().extern_marshals.get(&site) else {
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
        body.b,
        body.jmod,
        caller_fn_id,
        block_id,
        stmt_idx,
        decl.symbol.as_str(),
    )?;
    let lookup_fref = body
        .jmod
        .declare_func_in_func(env.runtime.extern_symbol_addr_id, body.b.func);
    let lookup = body.b.ins().call(lookup_fref, &[symbol_ptr]);
    let fn_ptr = body.b.inst_results(lookup)[0];

    let mut call_args = Vec::with_capacity(args.len() + 1);
    call_args.push(fn_ptr);
    for (arg, ty) in args.iter().zip(arg_tys.iter().copied()) {
        call_args.push(marshal_extern_arg(body, env.runtime, var_env, arg.var, ty)?);
    }

    let dispatcher_fref = body.jmod.declare_func_in_func(dispatcher, body.b.func);
    let inst = body.b.ins().call(dispatcher_fref, &call_args);
    if matches!(decl.ret, ExternTy::Unit | ExternTy::Never) {
        if body.cache.used_vars.contains(&dest_var.0) {
            return Ok(LowerOut::Strict(strict_const_value(body.b, AnyValue::nil_atom())));
        }
        return Ok(LowerOut::DeadUnit);
    }
    let raw = body.b.inst_results(inst)[0];
    match decl.ret {
        ExternTy::I64 => Ok(LowerOut::RawI64(raw)),
        ExternTy::F64 => Ok(LowerOut::RawF64(raw)),
        ExternTy::Any | ExternTy::Binary | ExternTy::CString => Ok(LowerOut::ValueRef(raw)),
        ExternTy::Unit | ExternTy::Never => unreachable!(),
    }
}

#[allow(clippy::too_many_arguments)]
pub(crate) fn lower_prim<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    dest_var: Var,
    // `caller_fn_id`/`block_id`/`stmt_idx` identify per-stmt side tables such
    // as variadic extern marshal plans and generated static data symbols.
    caller_fn_id: FnId,
    block_id: BlockId,
    stmt_idx: usize,
    block_env: Option<&HashMap<Var, Ty>>,
) -> Result<LowerOut, CodegenError> {
    let runtime = env.runtime;
    let value_types = env.active_value_types();
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
                body.cache.static_scalar_consts.insert(dest_var.0, AnyValue::int(*n));
                if ty_is_int(t, value_types, dest_var) {
                    body.cache.raw_int_consts.insert(dest_var.0, *n);
                    return Ok(LowerOut::RawI64(body.b.ins().iconst(types::I64, *n)));
                }
                Ok(LowerOut::StrictConst(AnyValue::int(*n)))
            }
            Const::True => Ok(LowerOut::StrictConst(AnyValue::bool_atom(true))),
            Const::False => Ok(LowerOut::StrictConst(AnyValue::bool_atom(false))),
            Const::Nil => Ok(LowerOut::StrictConst(AnyValue::nil_atom())),
            Const::Atom(id) => Ok(LowerOut::StrictConst(AnyValue::atom(*id))),
            Const::Float(f) => {
                body.cache.static_scalar_consts.insert(dest_var.0, AnyValue::float(*f));
                if ty_is_float(t, value_types, dest_var) {
                    return Ok(LowerOut::RawF64(body.b.ins().f64const(*f)));
                }
                Ok(LowerOut::StrictConst(AnyValue::float(*f)))
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
                    lower_arith_binop(body, t, value_types, var_env, runtime, *op, *a, *bv)
                }
                BinOp::Eq | BinOp::Neq => {
                    lower_eq_binop(body, t, value_types, var_env, runtime, *op, *a, *bv, dest_var)
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    lower_cmp_binop(body, t, value_types, var_env, runtime, *op, *a, *bv, dest_var)
                }
                BinOp::And | BinOp::Or => lower_bool_binop(body, var_env, *op, *a, *bv, dest_var),
            }
        }
        Prim::UnOp(op, x) => match op {
            UnOp::Neg => {
                let xi = body.as_raw_i64(var_env, x.0);
                Ok(LowerOut::RawI64(body.b.ins().ineg(xi)))
            }
            UnOp::Not => {
                let xv = *var_env.get(&x.0).expect("not operand");
                let truthy = body.value_truthy(xv);
                let zero = body.b.ins().iconst(types::I8, 0);
                let inv = body.b.ins().icmp(IntCC::Equal, truthy, zero);
                if body.cache.if_only_conds.contains(&dest_var.0) {
                    return Ok(LowerOut::Condition(inv));
                }
                Ok(LowerOut::Strict(strict_bool(body.b, inv)))
            }
        },
        Prim::Extern(_, eid, args) => {
            let decl = env.module.extern_by_id(*eid);
            let arg_vars: Vec<Var> = args.iter().map(|arg| arg.var).collect();
            if decl.symbol == "fz_panic" && args.len() == 1 {
                return lower_extern_fz_panic(body, var_env, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_send" && args.len() == 2 {
                return lower_extern_fz_send(body, var_env, &arg_vars);
            }
            if decl.symbol == "fz_self" && args.is_empty() {
                return lower_extern_fz_self(body);
            }
            if decl.symbol == "fz_process_heap_alloc_stats" && args.is_empty() {
                let process = body.process_arg();
                let sig = sig1(&[types::I64], &[types::I64]);
                let func_id = body
                    .jmod
                    .declare_function("fz_process_heap_alloc_stats", Linkage::Import, &sig)
                    .map_err(|e| CodegenError::new(format!("declare fz_process_heap_alloc_stats: {}", e)))?;
                let fref = body.jmod.declare_func_in_func(func_id, body.b.func);
                let inst = body.b.ins().call(fref, &[process]);
                return Ok(LowerOut::ValueRef(body.b.inst_results(inst)[0]));
            }
            if decl.symbol == "fz_make_ref" && args.is_empty() {
                return lower_extern_fz_make_ref(body);
            }
            if decl.symbol == "fz_spawn" && args.len() == 1 {
                return lower_extern_fz_spawn(body, var_env, &arg_vars);
            }
            if decl.symbol == "fz_spawn_opt" && args.len() == 2 {
                return lower_extern_fz_spawn_opt(body, var_env, &arg_vars);
            }
            if decl.symbol == "fz_make_resource" && args.len() == 2 {
                return lower_extern_fz_make_resource(body, var_env, &arg_vars);
            }
            if decl.symbol == "fz_dbg_value" && args.len() == 1 {
                return lower_extern_fz_dbg_value(body, var_env, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_binary_concat" && args.len() == 2 {
                return lower_extern_fz_binary_concat(body, var_env, &arg_vars, dest_var);
            }
            if matches!(decl.symbol.as_str(), "fz_op_add_ii" | "fz_op_add_if" | "fz_op_add_ff") && args.len() == 2 {
                return lower_extern_fz_op_arith(body, t, value_types, var_env, runtime, BinOp::Add, &arg_vars);
            }
            if matches!(
                decl.symbol.as_str(),
                "fz_op_sub_ii" | "fz_op_sub_if" | "fz_op_sub_fi" | "fz_op_sub_ff"
            ) && args.len() == 2
            {
                return lower_extern_fz_op_arith(body, t, value_types, var_env, runtime, BinOp::Sub, &arg_vars);
            }
            if matches!(decl.symbol.as_str(), "fz_op_mul_ii" | "fz_op_mul_if" | "fz_op_mul_ff") && args.len() == 2 {
                return lower_extern_fz_op_arith(body, t, value_types, var_env, runtime, BinOp::Mul, &arg_vars);
            }
            if matches!(
                decl.symbol.as_str(),
                "fz_op_div_ii" | "fz_op_div_if" | "fz_op_div_fi" | "fz_op_div_ff"
            ) && args.len() == 2
            {
                return lower_extern_fz_op_arith(body, t, value_types, var_env, runtime, BinOp::Div, &arg_vars);
            }
            if matches!(
                decl.symbol.as_str(),
                "fz_op_rem_ii" | "fz_op_rem_if" | "fz_op_rem_fi" | "fz_op_rem_ff"
            ) && args.len() == 2
            {
                return lower_extern_fz_op_arith(body, t, value_types, var_env, runtime, BinOp::Mod, &arg_vars);
            }
            if decl.symbol == "fz_op_eq" && args.len() == 2 {
                return lower_extern_fz_op_cmp(body, t, value_types, var_env, runtime, BinOp::Eq, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_op_neq" && args.len() == 2 {
                return lower_extern_fz_op_cmp(body, t, value_types, var_env, runtime, BinOp::Neq, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_op_lt" && args.len() == 2 {
                return lower_extern_fz_op_cmp(body, t, value_types, var_env, runtime, BinOp::Lt, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_op_lte" && args.len() == 2 {
                return lower_extern_fz_op_cmp(body, t, value_types, var_env, runtime, BinOp::Le, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_op_gt" && args.len() == 2 {
                return lower_extern_fz_op_cmp(body, t, value_types, var_env, runtime, BinOp::Gt, &arg_vars, dest_var);
            }
            if decl.symbol == "fz_op_gte" && args.len() == 2 {
                return lower_extern_fz_op_cmp(body, t, value_types, var_env, runtime, BinOp::Ge, &arg_vars, dest_var);
            }
            if decl.variadic {
                return emit_variadic_extern_call(
                    body,
                    env,
                    var_env,
                    *eid,
                    args,
                    dest_var,
                    caller_fn_id,
                    block_id,
                    stmt_idx,
                );
            }
            lower_extern_generic(body, runtime, var_env, decl, eid, args, dest_var)
        }
        Prim::IsEmptyList(c) => {
            // Empty list is the null-address List ref.
            let cmp = if let Some(CodegenValue::AnyRef(value)) = var_env.get(&c.0).copied() {
                let tag = body.ref_tag(value);
                let empty_list_v = body.empty_list_ref();
                let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
                let is_empty_word = body.b.ins().icmp(IntCC::Equal, value, empty_list_v);
                body.b.ins().band(is_list, is_empty_word)
            } else {
                let cv = body.tagged_var(var_env, c.0);
                let empty_list_v = body.empty_list_ref();
                body.b.ins().icmp(IntCC::Equal, cv, empty_list_v)
            };
            if body.cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
        }
        Prim::IsListCons(c) => {
            let cmp = if let Some(CodegenValue::AnyRef(value)) = var_env.get(&c.0).copied() {
                let tag = body.ref_tag(value);
                let empty_list_v = body.empty_list_ref();
                let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
                let is_empty_word = body.b.ins().icmp(IntCC::Equal, value, empty_list_v);
                let not_empty = body.b.ins().icmp_imm(IntCC::Equal, is_empty_word, 0);
                body.b.ins().band(is_list, not_empty)
            } else {
                let cv = body.tagged_var(var_env, c.0);
                let tag = body.ref_tag(cv);
                let empty_list_v = body.empty_list_ref();
                let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
                let is_empty_word = body.b.ins().icmp(IntCC::Equal, cv, empty_list_v);
                let not_empty = body.b.ins().icmp_imm(IntCC::Equal, is_empty_word, 0);
                body.b.ins().band(is_list, not_empty)
            };
            if body.cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
        }
        Prim::BitReaderDone(r) => {
            let rv = body.tagged_var(var_env, r.0);
            let fref = body
                .jmod
                .declare_func_in_func(runtime.bs_reader_done_ref_id, body.b.func);
            let process = body.process_arg();
            let inst = body.b.ins().call(fref, &[process, rv]);
            let cmp = body.b.inst_results(inst)[0];
            if body.cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
        }
        Prim::MapGet(m, k) if ty_is_float(t, value_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k, block_env);
            let load_float = body.jmod.declare_func_in_func(runtime.ref_load_float_id, body.b.func);
            let load_inst = body.b.ins().call(load_float, &[value_ref]);
            Ok(LowerOut::RawF64(body.b.inst_results(load_inst)[0]))
        }
        Prim::MapGet(m, k) if ty_is_int(t, value_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k, block_env);
            let load_int = body.jmod.declare_func_in_func(runtime.ref_load_int_id, body.b.func);
            let load_inst = body.b.ins().call(load_int, &[value_ref]);
            Ok(LowerOut::RawI64(body.b.inst_results(load_inst)[0]))
        }
        Prim::MapGet(m, k) if ty_is_atom(t, value_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k, block_env);
            let load_atom = body.jmod.declare_func_in_func(runtime.ref_load_atom_id, body.b.func);
            let load_inst = body.b.ins().call(load_atom, &[value_ref]);
            Ok(LowerOut::RawI64(body.b.inst_results(load_inst)[0]))
        }
        Prim::ListHead(c)
            if list_projection_is_safe(t, value_types, *c, block_env) && ty_is_int(t, value_types, dest_var) =>
        {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            Ok(LowerOut::RawI64(body.list_head_int(list_ref)))
        }
        Prim::ListHead(c)
            if list_projection_is_safe(t, value_types, *c, block_env) && ty_is_float(t, value_types, dest_var) =>
        {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            Ok(LowerOut::RawF64(body.list_head_float(list_ref)))
        }
        Prim::ListTail(c) if list_projection_is_safe(t, value_types, *c, block_env) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            Ok(LowerOut::ValueRefWord(body.list_tail(list_ref)))
        }
        Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeTuple(..)
        | Prim::MakeStruct { .. }
        | Prim::TupleField(..)
        | Prim::StructField(..)
        | Prim::MakeBitstring(..)
        | Prim::ConstBitstring(..)
        | Prim::BitReaderInit(..)
        | Prim::BitReadField { .. }
        | Prim::DestMapBegin { .. }
        | Prim::DestMapPut { .. }
        | Prim::DestMapFreeze { .. }
        | Prim::MapGet(..)
        | Prim::MatcherMapGet(..)
        | Prim::IsMatcherMapMiss(..) => {
            lower_collection_prim(body, t, env, var_env, prim, dest_var, block_id, block_env)
        }
        Prim::MakeFnRef(_, fn_id) => lower_make_fn_ref(body, env, *fn_id),
        Prim::MakeClosure(_, fn_id, captured) => lower_make_closure(body, env, var_env, *fn_id, captured),
        Prim::RuntimeTypeTest(v, descr) => {
            lower_runtime_type_predicate(body, env, var_env, runtime, *v, descr, dest_var)
        }
        Prim::ClosureCapture { closure, target, index } => {
            lower_closure_capture(body, env, var_env, *closure, *target, *index)
        }
    }
}

/// Read capture `index` back out of a closure, in the representation the
/// callable's own boundary wrote it in.
///
/// `emit_capturing_closure` stores each capture through the boundary's
/// `capture_reprs`; this is the same table read the other way, so the load and
/// the store cannot drift. A callable minted at several capture layouts has
/// several boundaries, and they must agree about this slot or there is no one
/// answer to read.
fn lower_closure_capture<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    closure: Var,
    target: ClosureTarget,
    index: u32,
) -> Result<LowerOut, CodegenError> {
    let mut reprs = env
        .surface
        .callable_boundaries_for_target(target)
        .map(|boundary| boundary.capture_reprs.get(index as usize).copied());
    let repr = match reprs.next() {
        Some(Some(repr)) if reprs.all(|other| other == Some(repr)) => repr,
        _ => {
            return Err(CodegenError::new(format!(
                "closure capture {index} of callable {} has no single settled representation",
                target.0
            )));
        }
    };
    let value = *var_env.get(&closure.0).expect("closure capture subject");
    let closure_ref = body.value_as_any_ref(value);
    Ok(LowerOut::Strict(body.closure_capture_as_binding(
        closure_ref,
        index as usize,
        repr,
    )))
}

/// Lower a `RuntimeTypeTest` prim.
///
/// Two subject shapes reach here. Usually the value is in hand and the shared
/// emitter reads it. Under destination-passing the tuple was never boxed --
/// `fz-qwf` delivered its fields as separate parameters -- so there is no
/// value to read, and the test is answered against the FIELDS instead, which
/// is exactly what a per-position test wants anyway (fz-kdt.133).
fn lower_runtime_type_predicate<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    runtime: &RuntimeRefs,
    v: Var,
    predicate: &RuntimeTypePredicate,
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    let flag = if let Some(delivered) = delivered_tuple_fields(body, v)
        && !predicate.allow_other_structs
        && predicate.named_structs.is_none()
    {
        emit_delivered_tuple_test(body, env, runtime, predicate, &delivered)?
    } else {
        let value = *var_env.get(&v.0).expect("type-test subject");
        let mut emitter = PrimTestEmitter { body, env, runtime };
        emit_runtime_type_test(&mut emitter, value, predicate)?
    };
    if body.cache.if_only_conds.contains(&dest_var.0) {
        return Ok(LowerOut::Condition(flag));
    }
    Ok(LowerOut::Strict(strict_bool(body.b, flag)))
}

/// The field parameters a destination-passing boundary delivered in place of a
/// tuple, in position order, or `None` where the subject is an ordinary value.
fn delivered_tuple_fields<M: cranelift_module::Module>(
    body: &CodegenFn<'_, '_, '_, M>,
    tuple: Var,
) -> Option<Vec<CodegenValue>> {
    let mut fields = Vec::new();
    for index in 0.. {
        match body.cache.tuple_field_params.get(&(tuple.0, index)) {
            Some(field) => fields.push(*field),
            None => break,
        }
    }
    (!fields.is_empty()).then_some(fields)
}

/// Answer a type test about a tuple that was delivered as separate fields.
///
/// The arity is a compile-time fact here -- it is how many parameters the
/// boundary handed over -- so the arity half of the question is decided
/// without touching a value. The SHAPE half is not: the WHOLE test was answered
/// with that one constant until fz-kdt.119 made the predicate payload-aware, at
/// which point a constant would have been silently wrong on exactly the lanes
/// destination-passing optimized (fz-kdt.133). The fields are right here, so
/// each position is asked directly, with no tuple to rebuild.
///
/// Measured at the landing: `tuple_field_params` is EMPTY at every one of the
/// 1783 type tests the corpus lowers, so this path is not reached today and the
/// hazard it repairs was latent rather than live. It is kept rather than
/// deleted because the alternative is the `expect` below firing on the day
/// destination-passing does deliver a type-tested tuple, and a correct answer
/// beats a loud crash.
fn emit_delivered_tuple_test<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    runtime: &RuntimeRefs,
    predicate: &RuntimeTypePredicate,
    fields: &[CodegenValue],
) -> Result<ir::Value, CodegenError> {
    if !predicate.tuples.arities().contains(&fields.len()) {
        return Ok(body.b.ins().iconst(types::I8, 0));
    }
    if !predicate.tuples.is_exact() {
        return Ok(body.b.ins().iconst(types::I8, 1));
    }
    let mut emitter = PrimTestEmitter { body, env, runtime };
    let mut hit = emitter.body.b.ins().iconst(types::I8, 0);
    for shape in predicate
        .tuples
        .shapes()
        .iter()
        .filter(|shape| shape.len() == fields.len())
    {
        let mut matched: Option<ir::Value> = None;
        for (field, position) in fields.iter().zip(shape) {
            if !lowering_tests_position(position) {
                continue;
            }
            let flag = emit_runtime_type_test(&mut emitter, *field, position)?;
            matched = Some(match matched {
                None => flag,
                Some(prev) => emitter.body.b.ins().band(prev, flag),
            });
        }
        let matched = matched.unwrap_or_else(|| emitter.body.b.ins().iconst(types::I8, 1));
        hit = emitter.body.b.ins().bor(hit, matched);
    }
    Ok(hit)
}

/// The compiled-body door onto the shared runtime-test emitter.
struct PrimTestEmitter<'a, 'b, 'env, 'fb, M: cranelift_module::Module> {
    body: &'a mut CodegenFn<'b, 'env, 'fb, M>,
    env: &'a CodegenEnv<'a>,
    runtime: &'a RuntimeRefs,
}

impl<'fb, M: cranelift_module::Module> RuntimeTestEmitter<'fb> for PrimTestEmitter<'_, '_, '_, 'fb, M> {
    type Value = CodegenValue;

    fn builder(&mut self) -> &mut FunctionBuilder<'fb> {
        self.body.b
    }

    fn atom_names(&self) -> &[String] {
        &self.env.module.atom_names
    }

    fn tuple_schema_ids(&self) -> &HashMap<usize, u32> {
        self.env.tuple_schema_ids
    }

    fn named_schema_ids(&self) -> &HashMap<String, u32> {
        self.env.named_schema_ids
    }

    fn kind_evidence(&self, value: CodegenValue) -> KindEvidence {
        match value {
            CodegenValue::AnyRef(_) => KindEvidence::Tagged,
            CodegenValue::RawInt(_) => KindEvidence::Unboxed(ValueKind::INT),
            CodegenValue::RawF64(_) => KindEvidence::Unboxed(ValueKind::FLOAT),
            CodegenValue::RawAtom(_) | CodegenValue::Condition(_) => KindEvidence::Unboxed(ValueKind::ATOM),
            CodegenValue::Known {
                kind: ValueKind::INT, ..
            } => KindEvidence::Unboxed(ValueKind::INT),
            CodegenValue::Known {
                kind: ValueKind::FLOAT, ..
            } => KindEvidence::Unboxed(ValueKind::FLOAT),
            CodegenValue::Known {
                kind: ValueKind::ATOM, ..
            } => KindEvidence::Unboxed(ValueKind::ATOM),
            CodegenValue::Known { .. } => KindEvidence::Opaque,
        }
    }

    fn kind_flag(&mut self, value: CodegenValue, kind: ValueKind) -> Result<ir::Value, CodegenError> {
        Ok(self.body.value_is_tag(value, kind))
    }

    fn raw_int(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        Ok(self.body.value_raw_int(value))
    }

    fn raw_float_bits(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let raw = self.body.value_raw_float(value);
        Ok(self.body.b.ins().bitcast(types::I64, MemFlags::new(), raw))
    }

    fn raw_atom(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        Ok(self.body.value_raw_atom(value))
    }

    fn empty_list_flag(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        Ok(emit_is_empty_list_flag(self.body, value))
    }

    fn cons_flag(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        Ok(emit_is_list_cons_flag(self.body, value))
    }

    fn schema_id(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let struct_ref = self.body.value_as_any_ref(value);
        let fref = self
            .body
            .jmod
            .declare_func_in_func(self.runtime.struct_schema_id_ref_id, self.body.b.func);
        let inst = self.body.b.ins().call(fref, &[struct_ref]);
        let raw = self.body.b.inst_results(inst)[0];
        Ok(self.body.b.ins().uextend(types::I64, raw))
    }

    fn tuple_field(&mut self, value: CodegenValue, index: usize) -> Result<CodegenValue, CodegenError> {
        let struct_ref = self.body.value_as_any_ref(value);
        let fref = self
            .body
            .jmod
            .declare_func_in_func(self.runtime.struct_get_field_id, self.body.b.func);
        let offset = self.body.b.ins().iconst(types::I32, (index as i64) * SLOT_BYTES as i64);
        let process = self.body.process_arg();
        let inst = self.body.b.ins().call(fref, &[process, struct_ref, offset]);
        Ok(CodegenValue::AnyRef(self.body.b.inst_results(inst)[0]))
    }

    fn closure_code(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let closure_ref = self.body.value_as_any_ref(value);
        Ok(self.body.closure_code_ref(closure_ref))
    }

    fn callable_addresses(&mut self, targets: &FiniteSet<ClosureTarget>) -> Result<Vec<ir::Value>, CodegenError> {
        let mut func_ids = Vec::new();
        for target in &targets.values {
            for boundary in self.env.surface.callable_boundaries_for_target(*target) {
                let boundary_id = boundary.boundary_id.as_u32();
                let func_id = self.env.callable_boundary_fn_ids.get(&boundary_id).ok_or_else(|| {
                    CodegenError::new(format!(
                        "callable identity test names callable boundary {boundary_id}, which was never published",
                    ))
                })?;
                func_ids.push(*func_id);
            }
        }
        Ok(func_ids
            .into_iter()
            .map(|func_id| fn_addr(self.body.jmod, func_id, self.body.b))
            .collect())
    }
}

fn emit_is_empty_list_flag<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    value: CodegenValue,
) -> ir::Value {
    if let CodegenValue::AnyRef(value_ref) = value {
        let tag = body.ref_tag(value_ref);
        let empty_list_v = body.empty_list_ref();
        let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
        let is_empty_word = body.b.ins().icmp(IntCC::Equal, value_ref, empty_list_v);
        body.b.ins().band(is_list, is_empty_word)
    } else {
        let cv = body.value_as_any_ref(value);
        let empty_list_v = body.empty_list_ref();
        body.b.ins().icmp(IntCC::Equal, cv, empty_list_v)
    }
}

fn emit_is_list_cons_flag<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    value: CodegenValue,
) -> ir::Value {
    if let CodegenValue::AnyRef(value_ref) = value {
        let tag = body.ref_tag(value_ref);
        let empty_list_v = body.empty_list_ref();
        let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
        let is_empty_word = body.b.ins().icmp(IntCC::Equal, value_ref, empty_list_v);
        let not_empty = body.b.ins().icmp_imm(IntCC::Equal, is_empty_word, 0);
        body.b.ins().band(is_list, not_empty)
    } else {
        let cv = body.value_as_any_ref(value);
        let tag = body.ref_tag(cv);
        let empty_list_v = body.empty_list_ref();
        let is_list = body.b.ins().icmp_imm(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
        let is_empty_word = body.b.ins().icmp(IntCC::Equal, cv, empty_list_v);
        let not_empty = body.b.ins().icmp_imm(IntCC::Equal, is_empty_word, 0);
        body.b.ins().band(is_list, not_empty)
    }
}

/// Same-kind typed fast path for a binop: when the typer proves both
/// operands share the int or float lane, extract their raw values and
/// run the matching op closure, bypassing tagged dispatch. Returns None
/// when neither lane applies (caller falls back to runtime tag tests).
fn try_typed_binop_fast_path<T, F, I, M>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    a: Var,
    bv: Var,
    var_env: &HashMap<u32, CodegenValue>,
    float_op: F,
    int_op: I,
) -> Option<LowerOut>
where
    T: Types<Ty = Ty>,
    M: cranelift_module::Module,
    F: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> Option<LowerOut>,
    I: FnOnce(&mut FunctionBuilder<'_>, ir::Value, ir::Value) -> Option<LowerOut>,
{
    let a_repr = var_env.get(&a.0).expect("binop lhs").repr();
    let b_repr = var_env.get(&bv.0).expect("binop rhs").repr();
    if !matches!(
        (a_repr, b_repr),
        (ArgRepr::RawInt, ArgRepr::RawInt) | (ArgRepr::RawF64, ArgRepr::RawF64)
    ) {
        return None;
    }
    if ty_is_float(t, value_types, a) && ty_is_float(t, value_types, bv) {
        let af = body.as_raw_f64(var_env, a.0);
        let bf = body.as_raw_f64(var_env, bv.0);
        if let Some(out) = float_op(body.b, af, bf) {
            return Some(out);
        }
    }
    if ty_is_int(t, value_types, a) && ty_is_int(t, value_types, bv) {
        let ai = body.as_raw_i64(var_env, a.0);
        let bi = body.as_raw_i64(var_env, bv.0);
        if let Some(out) = int_op(body.b, ai, bi) {
            return Some(out);
        }
    }
    None
}

/// Lower a `Prim::BinOp` arithmetic op (Add/Sub/Mul/Div/Mod).
/// Three code paths: float coercion (int+float mix), typed fast path
/// (same-kind int or float), and tagged dispatch fallback that splits
/// on runtime tag tests.
fn lower_arith_binop<M, T>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    runtime: &RuntimeRefs,
    op: BinOp,
    a: Var,
    bv: Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
{
    let mop = op;
    let a_repr = var_env.get(&a.0).expect("binop lhs").repr();
    let b_repr = var_env.get(&bv.0).expect("binop rhs").repr();
    if matches!(
        (a_repr, b_repr),
        (ArgRepr::RawF64, ArgRepr::RawInt) | (ArgRepr::RawInt, ArgRepr::RawF64)
    ) && !matches!(mop, BinOp::Mod)
    {
        let af = as_known_numeric_f64(var_env, body.b, a.0);
        let bf = as_known_numeric_f64(var_env, body.b, bv.0);
        return Ok(LowerOut::RawF64(match mop {
            BinOp::Add => body.b.ins().fadd(af, bf),
            BinOp::Sub => body.b.ins().fsub(af, bf),
            BinOp::Mul => body.b.ins().fmul(af, bf),
            BinOp::Div => body.b.ins().fdiv(af, bf),
            _ => unreachable!(),
        }));
    }
    // Typed fast paths: float (skipped for Mod) and int.
    if let Some(out) = try_typed_binop_fast_path(
        body,
        t,
        value_types,
        a,
        bv,
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
    let a_is_int = body.value_is_tag(av, ValueKind::INT);
    let b_is_int = body.value_is_tag(bv_value, ValueKind::INT);
    let both_int = body.b.ins().band(a_is_int, b_is_int);
    let fast_blk = body.b.create_block();
    let slow_blk = body.b.create_block();
    let join_blk = body.b.create_block();
    body.b.append_block_param(join_blk, types::I64);
    let no_args: Vec<BlockArg> = Vec::new();
    body.b.ins().brif(both_int, fast_blk, &no_args, slow_blk, &no_args);

    body.b.switch_to_block(fast_blk);
    body.b.seal_block(fast_blk);
    let ai = body.value_raw_int_for_checked_branch(av);
    let bi = body.value_raw_int_for_checked_branch(bv_value);
    {
        let raw = match mop {
            BinOp::Add => body.b.ins().iadd(ai, bi),
            BinOp::Sub => body.b.ins().isub(ai, bi),
            BinOp::Mul => body.b.ins().imul(ai, bi),
            BinOp::Div => body.b.ins().sdiv(ai, bi),
            BinOp::Mod => body.b.ins().srem(ai, bi),
            _ => unreachable!(),
        };
        body.b.ins().jump(join_blk, &[BlockArg::Value(raw)]);
    }

    body.b.switch_to_block(slow_blk);
    body.b.seal_block(slow_blk);
    let unsupported_ref = body
        .jmod
        .declare_func_in_func(runtime.dynamic_float_arith_unsupported_id, body.b.func);
    let inst = body.b.ins().call(unsupported_ref, &[]);
    let slow_raw = body.b.inst_results(inst)[0];
    body.b.ins().jump(join_blk, &[BlockArg::Value(slow_raw)]);

    body.b.switch_to_block(join_blk);
    body.b.seal_block(join_blk);
    Ok(LowerOut::RawI64(body.b.block_params(join_blk)[0]))
}

/// If `raw_side` is natively unboxed (`RawInt`/`RawAtom`, or a `Known`
/// int/atom constant) and `dyn_side` is a genuinely dynamic, unproven-kind
/// value (`ValueRef` repr), return `raw_side`'s `ValueKind` + raw payload
/// alongside `dyn_side`'s `Var`.
///
/// This is what lets `==`/`!=` between an unboxed int/atom (a raw register
/// value — a literal, a monomorphized parameter, a projected tag, etc.) and
/// an opaque `AnyValueRef`-repr value skip materializing the unboxed side
/// into a heap scalar box (what `tagged_var` would do) just to call the
/// fully generic `fz_value_eq_ref`. Instead the runtime checks the dynamic
/// side's actual tag against the known kind and compares raw payloads
/// directly — `fz_value_eq_raw_const` — with no allocation on either side.
/// Float is deliberately excluded: float equality has IEEE-754 semantics
/// (-0.0 == 0.0, NaN != NaN) that a bitwise payload compare would violate.
fn raw_scalar_vs_dynamic(
    var_env: &HashMap<u32, CodegenValue>,
    raw_side: Var,
    dyn_side: Var,
) -> Option<(ValueKind, ir::Value, Var)> {
    let (kind, raw) = match binding_for_var(var_env, raw_side.0) {
        CodegenValue::RawAtom(payload) => (ValueKind::ATOM, payload),
        CodegenValue::RawInt(payload) => (ValueKind::INT, payload),
        CodegenValue::Known {
            payload,
            kind: kind @ (ValueKind::ATOM | ValueKind::INT),
        } => (kind, payload),
        _ => return None,
    };
    if binding_for_var(var_env, dyn_side.0).repr() != ArgRepr::ValueRef {
        return None;
    }
    Some((kind, raw, dyn_side))
}

/// Lower a `Prim::BinOp` Eq/Neq. Folds kind-disjoint operands to a
/// constant; otherwise picks native fcmp/icmp for same-kind float/int,
/// raw atom compare for atom/nil/bool pairs, the no-allocation raw-scalar
/// check when only one side is an unboxed int/atom, or calls the runtime
/// value_eq_ref for the fully heterogeneous fallback.
fn lower_eq_binop<M, T>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    runtime: &RuntimeRefs,
    op: BinOp,
    a: Var,
    bv: Var,
    dest_var: Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
{
    let is_eq = matches!(op, BinOp::Eq);
    let int_cc = if is_eq { IntCC::Equal } else { IntCC::NotEqual };
    let f_cc = if is_eq { FloatCC::Equal } else { FloatCC::NotEqual };

    // Value-disjoint (brand-erased) fold doesn't need either operand.
    if descrs_value_disjoint(t, value_types, a, bv) {
        let raw = body.b.ins().iconst(
            types::I64,
            if is_eq {
                FALSE_ATOM_ID as i64
            } else {
                TRUE_ATOM_ID as i64
            },
        );
        return Ok(LowerOut::Strict(CodegenValue::known(raw, ValueKind::ATOM)));
    }
    let a_repr = var_env.get(&a.0).expect("eq lhs").repr();
    let b_repr = var_env.get(&bv.0).expect("eq rhs").repr();
    // Same-kind float: native fcmp on raw f64.
    if (ty_is_float(t, value_types, a) && ty_is_float(t, value_types, bv))
        || matches!((a_repr, b_repr), (ArgRepr::RawF64, ArgRepr::RawF64))
    {
        let af = body.as_raw_f64(var_env, a.0);
        let bf = body.as_raw_f64(var_env, bv.0);
        let cmp = body.b.ins().fcmp(f_cc, af, bf);
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(body.b, cmp)));
    }
    // Same-kind int: native icmp on raw i64. Must not
    // mix raw and tagged operands — bit-eq is only
    // correct when both are in the same encoding.
    if (ty_is_int(t, value_types, a) && ty_is_int(t, value_types, bv))
        || matches!((a_repr, b_repr), (ArgRepr::RawInt, ArgRepr::RawInt))
    {
        let ai = body.as_raw_i64(var_env, a.0);
        let bi = body.as_raw_i64(var_env, bv.0);
        let cmp = body.b.ins().icmp(int_cc, ai, bi);
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(body.b, cmp)));
    }
    if (ty_is_atom(t, value_types, a) && ty_is_atom(t, value_types, bv))
        || (descr_is_nil_or_bool(t, value_types, a) && descr_is_nil_or_bool(t, value_types, bv))
        || matches!((a_repr, b_repr), (ArgRepr::RawAtom, ArgRepr::RawAtom))
    {
        let avp = body.value_raw_atom(binding_for_var(var_env, a.0));
        let bvp = body.value_raw_atom(binding_for_var(var_env, bv.0));
        let same_raw = body.b.ins().icmp(int_cc, avp, bvp);
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(same_raw));
        }
        Ok(LowerOut::Strict(strict_bool(body.b, same_raw)))
    } else if let Some((kind, raw, dyn_var)) =
        raw_scalar_vs_dynamic(var_env, a, bv).or_else(|| raw_scalar_vs_dynamic(var_env, bv, a))
    {
        // One side is an unboxed int/atom and the other's static type isn't
        // known to match: skip boxing the unboxed side into a heap scalar
        // (what `tagged_var` would do below) and instead hand the runtime
        // its raw payload directly, checked against the dynamic side's
        // actual tag.
        let dyn_ref = body.tagged_var(var_env, dyn_var.0);
        let kind_tag = body.b.ins().iconst(types::I32, i64::from(kind.tag()));
        let fref = body
            .jmod
            .declare_func_in_func(runtime.value_eq_raw_const_id, body.b.func);
        let inst = body.b.ins().call(fref, &[dyn_ref, kind_tag, raw]);
        let eq = body.b.inst_results(inst)[0];
        let eq_bool = body.b.ins().icmp_imm(IntCC::NotEqual, eq, 0);
        let cmp = if is_eq {
            eq_bool
        } else {
            body.b.ins().bxor_imm(eq_bool, 1)
        };
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
    } else {
        let a_ref = body.tagged_var(var_env, a.0);
        let b_ref = body.tagged_var(var_env, bv.0);
        let process = body.process_arg();
        let fref = body.jmod.declare_func_in_func(runtime.value_eq_ref_id, body.b.func);
        let inst = body.b.ins().call(fref, &[process, a_ref, b_ref]);
        let eq = body.b.inst_results(inst)[0];
        let eq_bool = body.b.ins().icmp_imm(IntCC::NotEqual, eq, 0);
        let cmp = if is_eq {
            eq_bool
        } else {
            body.b.ins().bxor_imm(eq_bool, 1)
        };
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
    }
}

/// Lower a `Prim::BinOp` ordered comparison (Lt/Le/Gt/Ge). Typed fast
/// paths emit native fcmp/icmp; the dispatch fallback splits on the
/// int-tag test and falls back to an inlined float promote+fcmp slow
/// path for any non-int-int operand mix.
fn lower_cmp_binop<M, T>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    runtime: &RuntimeRefs,
    op: BinOp,
    a: Var,
    bv: Var,
    dest_var: Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
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
    let if_only = body.cache.if_only_conds.contains(&dest_var.0);
    if let Some(out) = try_typed_binop_fast_path(
        body,
        t,
        value_types,
        a,
        bv,
        var_env,
        |b, af, bf| {
            let cmp = b.ins().fcmp(fcc, af, bf);
            if if_only {
                return Some(LowerOut::Condition(cmp));
            }
            Some(LowerOut::Strict(strict_bool(b, cmp)))
        },
        |b, ai, bi| {
            let cmp = b.ins().icmp(icc, ai, bi);
            if if_only {
                return Some(LowerOut::Condition(cmp));
            }
            Some(LowerOut::Strict(strict_bool(b, cmp)))
        },
    ) {
        return Ok(out);
    }
    let av = *var_env.get(&a.0).expect("cmp lhs");
    let bv_value = *var_env.get(&bv.0).expect("cmp rhs");
    let a_is_int = body.value_is_tag(av, ValueKind::INT);
    let b_is_int = body.value_is_tag(bv_value, ValueKind::INT);
    let both_int = body.b.ins().band(a_is_int, b_is_int);
    let fast_blk = body.b.create_block();
    let slow_blk = body.b.create_block();
    let join_blk = body.b.create_block();
    body.b.append_block_param(join_blk, types::I8);
    let no_args: Vec<BlockArg> = Vec::new();
    body.b.ins().brif(both_int, fast_blk, &no_args, slow_blk, &no_args);

    body.b.switch_to_block(fast_blk);
    body.b.seal_block(fast_blk);
    let ai = body.value_raw_int_for_checked_branch(av);
    let bi = body.value_raw_int_for_checked_branch(bv_value);
    let cmp = body.b.ins().icmp(icc, ai, bi);
    body.b.ins().jump(join_blk, &[BlockArg::Value(cmp)]);

    body.b.switch_to_block(slow_blk);
    body.b.seal_block(slow_blk);
    // Inlined float-cmp slow path: promote both operands
    // to f64 and emit native fcmp.
    let pfref = body.jmod.declare_func_in_func(runtime.promote_f64_id, body.b.func);
    let fcc = match op {
        BinOp::Lt => FloatCC::LessThan,
        BinOp::Le => FloatCC::LessThanOrEqual,
        BinOp::Gt => FloatCC::GreaterThan,
        BinOp::Ge => FloatCC::GreaterThanOrEqual,
        _ => unreachable!(),
    };
    let av = body.tagged_var(var_env, a.0);
    let bvv = body.tagged_var(var_env, bv.0);
    let i0 = body.b.ins().call(pfref, &[av]);
    let af = body.b.inst_results(i0)[0];
    let i1 = body.b.ins().call(pfref, &[bvv]);
    let bf = body.b.inst_results(i1)[0];
    let cmp = body.b.ins().fcmp(fcc, af, bf);
    body.b.ins().jump(join_blk, &[BlockArg::Value(cmp)]);

    body.b.switch_to_block(join_blk);
    body.b.seal_block(join_blk);
    let result = body.b.block_params(join_blk)[0];
    Ok(LowerOut::Strict(strict_bool(body.b, result)))
}

/// Lower a `Prim::BinOp` short-circuit-free boolean op (And/Or).
/// Both operands are coerced to truthy i8s and combined with
/// `band`/`bor`.
fn lower_bool_binop<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    op: BinOp,
    a: Var,
    bv: Var,
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    let av = *var_env.get(&a.0).expect("bool lhs");
    let bvv = *var_env.get(&bv.0).expect("bool rhs");
    let at = body.value_truthy(av);
    let bt = body.value_truthy(bvv);
    let combined = match op {
        BinOp::And => body.b.ins().band(at, bt),
        BinOp::Or => body.b.ins().bor(at, bt),
        _ => unreachable!(),
    };
    if body.cache.if_only_conds.contains(&dest_var.0) {
        return Ok(LowerOut::Condition(combined));
    }
    Ok(LowerOut::Strict(strict_bool(body.b, combined)))
}

// fz "process intrinsics": externs the front end exposes but the runtime
// implements as BIFs that need the running process (and/or bespoke arg
// marshaling). Each marshals its args, then routes through `body.call_named`
// — the one declare→call path — and wraps the result per its ABI. The process,
// when needed, is the pinned register (`process_arg`), prepended here rather
// than appearing in the fz extern decl.

/// `fz_panic(value)`: forwards one ValueRef to the runtime fatal path.
fn lower_extern_fz_panic<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    let value_ref = body.tagged_var(var_env, args[0].0);
    let process = body.process_arg();
    body.call_named("fz_panic", &[process, value_ref]);
    if body.cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(strict_const_value(body.b, AnyValue::nil_atom())));
    }
    Ok(LowerOut::DeadUnit)
}

/// `fz_dbg_value(value)`: prints the value and returns it. The runtime BIF
/// renders atom names off the process and routes output through the process's
/// ExecCtx telemetry sink, so the process is prepended from the pinned register.
fn lower_extern_fz_dbg_value<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    let value_ref = body.tagged_var(var_env, args[0].0);
    let process = body.process_arg();
    let call = body.call_named("fz_dbg_value", &[process, value_ref]);
    let result = body.b.inst_results(call)[0];
    if body.cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(CodegenValue::AnyRef(result)));
    }
    Ok(LowerOut::DeadUnit)
}

fn lower_extern_fz_binary_concat<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    let process = body.process_arg();
    let left = body.tagged_var(var_env, args[0].0);
    let right = body.tagged_var(var_env, args[1].0);
    let call = body.call_named("fz_binary_concat", &[process, left, right]);
    let result = body.b.inst_results(call)[0];
    if body.cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(CodegenValue::AnyRef(result)));
    }
    Ok(LowerOut::DeadUnit)
}

fn lower_extern_fz_op_arith<M, T>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    runtime: &RuntimeRefs,
    op: BinOp,
    args: &[Var],
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
{
    lower_arith_binop(body, t, value_types, var_env, runtime, op, args[0], args[1])
}

fn lower_extern_fz_op_cmp<M, T>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    runtime: &RuntimeRefs,
    op: BinOp,
    args: &[Var],
    dest_var: Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
{
    match op {
        BinOp::Eq | BinOp::Neq => {
            lower_eq_binop(body, t, value_types, var_env, runtime, op, args[0], args[1], dest_var)
        }
        BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
            lower_cmp_binop(body, t, value_types, var_env, runtime, op, args[0], args[1], dest_var)
        }
        _ => unreachable!(),
    }
}

/// `fz_send(receiver, msg)`: marshals `msg` as a single ABI ValueRef arg and
/// forwards to `fz_send_ref`.
fn lower_extern_fz_send<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
) -> Result<LowerOut, CodegenError> {
    let receiver = body.as_raw_i64(var_env, args[0].0);
    let msg_binding = *var_env.get(&args[1].0).expect("fz_send msg var");
    let mut msg_args = Vec::with_capacity(1);
    body.push_binding_as_abi_arg(&mut msg_args, msg_binding, ArgRepr::ValueRef);
    let msg_ref = msg_args[0];
    let process = body.process_arg();
    let inst = body.call_named("fz_send_ref", &[process, receiver, msg_ref]);
    Ok(LowerOut::ValueRefWord(body.b.inst_results(inst)[0]))
}

/// `fz_self()`: the current process id from `fz_self_raw`.
fn lower_extern_fz_self<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
) -> Result<LowerOut, CodegenError> {
    let process = body.process_arg();
    let inst = body.call_named("fz_self_raw", &[process]);
    Ok(LowerOut::RawI64(body.b.inst_results(inst)[0]))
}

/// `fz_make_ref()`: a fresh opaque ref from `fz_make_ref_raw` (no process).
fn lower_extern_fz_make_ref<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
) -> Result<LowerOut, CodegenError> {
    let inst = body.call_named("fz_make_ref_raw", &[]);
    Ok(LowerOut::RawI64(body.b.inst_results(inst)[0]))
}

/// `fz_spawn(closure)`: forwards the closure ref to `fz_spawn_ref`.
fn lower_extern_fz_spawn<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
) -> Result<LowerOut, CodegenError> {
    let closure_ref = body.tagged_var(var_env, args[0].0);
    let process = body.process_arg();
    let inst = body.call_named("fz_spawn_ref", &[process, closure_ref]);
    Ok(LowerOut::RawI64(body.b.inst_results(inst)[0]))
}

/// `fz_spawn_opt(closure, min_heap_size)`: `fz_spawn` plus a heap-size hint.
fn lower_extern_fz_spawn_opt<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
) -> Result<LowerOut, CodegenError> {
    let closure_ref = body.tagged_var(var_env, args[0].0);
    let min_heap_size = body.as_raw_i64(var_env, args[1].0);
    let process = body.process_arg();
    let inst = body.call_named("fz_spawn_opt_ref", &[process, closure_ref, min_heap_size]);
    Ok(LowerOut::RawI64(body.b.inst_results(inst)[0]))
}

/// `fz_make_resource(payload, dtor)`: raw payload bits + destructor closure ref.
fn lower_extern_fz_make_resource<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    args: &[Var],
) -> Result<LowerOut, CodegenError> {
    let payload = *var_env.get(&args[0].0).expect("unbound make_resource payload");
    let payload_raw = body.value_raw_int(payload);
    let dtor_ref = body.tagged_var(var_env, args[1].0);
    let process = body.process_arg();
    let inst = body.call_named("fz_make_resource_ref", &[process, payload_raw, dtor_ref]);
    Ok(LowerOut::ValueRef(body.b.inst_results(inst)[0]))
}

/// Generic extern fallback: marshals each arg per its declared
/// `ExternTy`, looks up (or caches) the FuncRef, and packages the
/// return as RawI64 / ValueRef / nil / DeadUnit per the decl shape.
fn lower_extern_generic<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    runtime: &RuntimeRefs,
    var_env: &HashMap<u32, CodegenValue>,
    decl: &ExternDecl,
    eid: &ExternId,
    args: &[ExternArg],
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
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
    let fref = if let Some(&cached) = body.cache.extern_funcs.get(eid) {
        cached
    } else {
        let func_id = body
            .jmod
            .declare_function(&decl.symbol, Linkage::Import, &sig)
            .map_err(|e| CodegenError::new(format!("declare extern `{}`: {}", decl.symbol, e)))?;
        let fref = body.jmod.declare_func_in_func(func_id, body.b.func);
        body.cache.extern_funcs.insert(*eid, fref);
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
        .map(|(v, ty)| marshal_extern_arg(body, runtime, var_env, v.var, *ty))
        .collect::<Result<_, _>>()?;
    let inst = body.b.ins().call(fref, &arg_vals);
    if returns_value {
        let raw = body.b.inst_results(inst)[0];
        if matches!(decl.ret, ExternTy::I64) {
            return Ok(LowerOut::RawI64(raw));
        }
        return Ok(LowerOut::ValueRef(raw));
    }
    if body.cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(strict_const_value(body.b, AnyValue::nil_atom())));
    }
    Ok(LowerOut::DeadUnit)
}

fn settled_callable_boundary_id(env: &CodegenEnv<'_>, fn_id: FnId) -> Result<u32, CodegenError> {
    let boundary_id = env
        .surface
        .callable_boundary_for_identity(fn_id)
        .ok_or_else(|| {
            CodegenError::new(format!(
                "native callable identity FnId({}) has no settled callable boundary",
                fn_id.0
            ))
        })?
        .boundary_id
        .as_u32();
    if !env.callable_boundary_fn_ids.contains_key(&boundary_id) {
        return Err(CodegenError::new(format!(
            "native callable value for FnId({}) references unpublished callable boundary {}",
            fn_id.0, boundary_id
        )));
    }
    Ok(boundary_id)
}

/// Lower a `Prim::MakeFnRef`. Thin callable values carry no env, so codegen
/// materializes the planned callable-boundary singleton directly instead of
/// routing through closure allocation.
pub(crate) fn lower_make_fn_ref<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    fn_id: FnId,
) -> Result<LowerOut, CodegenError> {
    let cl_sid = settled_callable_boundary_id(env, fn_id)?;
    Ok(LowerOut::ValueRef(fetch_static_closure(
        body.jmod,
        body.b,
        env.runtime,
        cl_sid,
    )))
}

/// Lower a `Prim::MakeClosure`. Env-carrying closures allocate a closure
/// object, store the callable-boundary code pointer, then write captures through
/// the runtime's schema-backed accessor.
pub(crate) fn lower_make_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    fn_id: FnId,
    captured: &[Var],
) -> Result<LowerOut, CodegenError> {
    if captured.is_empty() {
        return Err(CodegenError::new(format!(
            "MakeClosure for FnId({}) reached codegen with zero captures; thin callable values must lower as MakeFnRef",
            fn_id.0
        )));
    }
    let cl_sid = settled_callable_boundary_id(env, fn_id)?;
    Ok(LowerOut::ValueRef(emit_capturing_closure(
        body,
        var_env,
        env.surface,
        env.callable_boundary_fn_ids,
        fn_id,
        cl_sid,
        captured,
    )?))
}

/// Non-zero captures: alloc closure heap object, write body's
/// func_addr, and store captures as env fields. The body has
/// closure-target sig `(args..., self, cont) tail` and projects
/// captures from `self` in its entry harness.
fn emit_capturing_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    surface: &NativeCodegenSurface<'_>,
    callable_boundary_fn_ids: &HashMap<u32, FuncId>,
    fn_id: FnId,
    cl_sid: u32,
    captured: &[Var],
) -> Result<ir::Value, CodegenError> {
    let n_caps = captured.len();
    let body_func_id = *callable_boundary_fn_ids.get(&cl_sid).ok_or_else(|| {
        CodegenError::new(format!(
            "no callable-boundary FuncId for closure SpecId({}) \
             (FnId({}), {} captures)",
            cl_sid, fn_id.0, n_caps
        ))
    })?;
    let boundary = surface.callable_boundary(cl_sid).ok_or_else(|| {
        CodegenError::new(format!(
            "no callable-boundary surface for closure SpecId({}) (FnId({}), {} captures)",
            cl_sid, fn_id.0, n_caps
        ))
    })?;
    // The boundary decides the call surface, so it is also the authority on
    // the closure's arity (fz-gk4).
    let arity_v = body.b.ins().iconst(types::I32, boundary.arg_reprs.len() as i64);
    let nc_v = body.b.ins().iconst(types::I32, n_caps as i64);
    let halt_repr = boundary.task_halt_repr.unwrap_or(ArgRepr::ValueRef);
    let hk_v = body.b.ins().iconst(types::I32, halt_repr.halt_kind() as i64);
    let body_addr = fn_addr(body.jmod, body_func_id, body.b);
    let cl_ptr = body.alloc_closure(arity_v, nc_v, hk_v, body_addr);
    for (i, cv) in captured.iter().enumerate() {
        match closure_capture_for_var_as(body, var_env, cv.0, boundary.capture_reprs[i]) {
            ClosureCapture::RefWord(value) => body.store_closure_capture_ref_word(cl_ptr, i, value),
            ClosureCapture::RawInt(value) => body.store_closure_capture_i64(cl_ptr, i, value),
            ClosureCapture::RawF64(value) => body.store_closure_capture_f64(cl_ptr, i, value),
            ClosureCapture::RawAtom(value) => body.store_closure_capture_atom(cl_ptr, i, value),
        }
    }
    Ok(cl_ptr)
}
