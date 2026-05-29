use std::collections::HashMap;

use super::*;
use crate::fz_ir::{Module, Prim, Var};
use crate::types::Types;
use fz_runtime::any_value::AnyValueRef;
use fz_runtime::any_value::ValueKind;

pub(super) fn interp_list_cons(
    proc: *mut fz_runtime::process::Process,
    head: AnyValue,
    tail: AnyValue,
    context: &str,
) -> Result<AnyValue, String> {
    let bits = with_value_ref(tail, context, |tail_ref| match head {
        AnyValue::Int(value) => Ok::<u64, String>(fz_runtime::ir_runtime::fz_list_cons_int(
            proc, value, tail_ref,
        )),
        AnyValue::Float(value) => Ok::<u64, String>(fz_runtime::ir_runtime::fz_list_cons_float(
            proc, value, tail_ref,
        )),
        AnyValue::Atom(value) => Ok::<u64, String>(fz_runtime::ir_runtime::fz_list_cons_atom(
            proc,
            value as u64,
            tail_ref,
        )),
        AnyValue::Null | AnyValue::EmptyList | AnyValue::Ref(_) => {
            let head = head
                .as_ref_word()
                .map_err(|err| format!("{context}: cannot create head ref: {err}"))?;
            Ok(fz_runtime::ir_runtime::fz_list_cons_ref(
                proc, head, tail_ref,
            ))
        }
    })??;
    interp_value_from_ref_word(bits, context)
}

pub(super) fn interp_map_put(
    proc: *mut fz_runtime::process::Process,
    map_bits: u64,
    key: AnyValue,
    value: AnyValue,
    context: &str,
) -> Result<u64, String> {
    with_value_ref(key, context, |key_ref| match value {
        AnyValue::Int(value) => Ok::<u64, String>(fz_runtime::ir_runtime::fz_map_put_int(
            proc, map_bits, key_ref, value,
        )),
        AnyValue::Float(value) => Ok::<u64, String>(fz_runtime::ir_runtime::fz_map_put_float(
            proc, map_bits, key_ref, value,
        )),
        AnyValue::Atom(value) => Ok::<u64, String>(fz_runtime::ir_runtime::fz_map_put_atom(
            proc,
            map_bits,
            key_ref,
            value as u64,
        )),
        AnyValue::Null | AnyValue::EmptyList | AnyValue::Ref(_) => {
            let value_ref = value
                .as_ref_word()
                .map_err(|err| format!("{context}: cannot create value ref: {err}"))?;
            Ok(fz_runtime::ir_runtime::fz_map_put_ref(
                proc, map_bits, key_ref, value_ref,
            ))
        }
    })?
}

pub(super) fn interp_list_head(value: AnyValue) -> Result<AnyValue, String> {
    let slot = value.value()?;
    if !interp_is_list_cons(slot) {
        return Err(format!("ListHead: subject is not a list cons ({:?})", slot));
    }
    with_value_ref(value, "ListHead", |list_ref| {
        fz_runtime::ir_runtime::fz_list_head_ref(list_ref)
    })
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "ListHead"))
}

pub(super) fn interp_list_tail(value: AnyValue) -> Result<AnyValue, String> {
    let slot = value.value()?;
    if !interp_is_list_cons(slot) {
        return Err(format!("ListTail: subject is not a list cons ({:?})", slot));
    }
    with_value_ref(value, "ListTail", |list_ref| {
        fz_runtime::ir_runtime::fz_list_tail_ref(list_ref)
    })
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "ListTail"))
}

pub(super) fn interp_map_get(
    proc: *mut fz_runtime::process::Process,
    map: AnyValue,
    key: AnyValue,
) -> Result<AnyValue, String> {
    let map_slot = map.value()?;
    if map_slot.kind() != ValueKind::RESOURCE && !is_map_value(map_slot) {
        return Ok(interp_nil_value());
    }
    with_value_ref(map, "MapGet map", |map_ref| {
        with_value_ref(key, "MapGet key", |key_ref| {
            fz_runtime::ir_runtime::fz_map_get_ref(proc, map_ref, key_ref)
        })
    })?
    .and_then(|ref_word| interp_value_from_ref_word(ref_word, "MapGet"))
}

pub(super) fn eval_prim<T: Types<Ty = crate::types::Ty>>(
    runtime: &mut IrInterpRuntime,
    t: &mut T,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
    fn_types: &crate::ir_planner::SpecPlan,
    block_id: crate::fz_ir::BlockId,
    stmt_idx: usize,
    prim: &Prim,
    env: &HashMap<Var, AnyValue>,
) -> Result<AnyValue, String> {
    Ok(match prim {
        Prim::Const(c) => const_to_interp(c),
        Prim::BinOp(op, a, b) => {
            let av = env_get(env, *a)?;
            let bv = env_get(env, *b)?;
            eval_binop(*op, av, bv)?
        }
        Prim::UnOp(op, a) => {
            let av = env_get(env, *a)?;
            eval_unop(*op, av)?
        }
        Prim::Extern(eid, args) => {
            let vars: Vec<_> = args.iter().map(|arg| arg.var).collect();
            let arg_vals = collect(env, &vars)?;
            call_extern(
                runtime, t, module, tel, fn_types, block_id, stmt_idx, *eid, args, &arg_vals,
            )?
        }
        Prim::MakeBitstring(fields) => {
            // fz-cty.7 — mirror src/ir_codegen.rs Prim::MakeBitstring: drive the
            // same runtime BitWriter through the same extern "C" calls the JIT
            // and AOT paths use, so all three paths funnel through the shared
            // bitstring substrate.
            use crate::ast::BitType as AstBitType;
            use crate::fz_ir::BitSizeIr;
            fn encode_bit_type(t: AstBitType) -> u32 {
                match t {
                    AstBitType::Integer => 0,
                    AstBitType::Float => 1,
                    AstBitType::Binary => 2,
                    AstBitType::Bits => 3,
                    AstBitType::Utf8 => 4,
                    AstBitType::Utf16 => 5,
                    AstBitType::Utf32 => 6,
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
            fn default_unit_for(ty: AstBitType) -> u32 {
                match ty {
                    AstBitType::Integer | AstBitType::Float | AstBitType::Bits => 1,
                    AstBitType::Binary => 8,
                    AstBitType::Utf8 | AstBitType::Utf16 | AstBitType::Utf32 => 1,
                }
            }
            fz_runtime::ir_runtime::fz_bs_begin(runtime.cur_proc());
            for f in fields {
                let value_v = env_get(env, f.value)?;
                let ty_tag = encode_bit_type(f.ty);
                let unit = f.unit.unwrap_or(default_unit_for(f.ty));
                let endian_tag = encode_endian(f.endian);
                let signed = f.signed as u32;
                let (size_present, size_value) = match &f.size {
                    None => (0u32, 0u32),
                    Some(BitSizeIr::Literal(n)) => (1, *n),
                    Some(BitSizeIr::Var(v)) => {
                        let raw = env_get(env, *v)?;
                        let n = raw
                            .as_i64()
                            .ok_or_else(|| "bit size var must be an integer".to_string())?;
                        (1, n as u32)
                    }
                };
                fz_runtime::ir_runtime::fz_bs_write_field_ref(
                    value_v.as_ref_word()?,
                    ty_tag,
                    size_present,
                    size_value,
                    unit,
                    endian_tag,
                    signed,
                );
            }
            interp_value_from_ref_word(
                fz_runtime::ir_runtime::fz_bs_finalize(runtime.cur_proc()),
                "MakeBitstring",
            )?
        }
        Prim::ConstBitstring(bytes, bit_len) => {
            // fz-cty.8 — bytes are owned by the Module (and live as long as
            // the interp run), so it's safe to alloc straight from them via
            // the shared runtime FFI; identical to the JIT/AOT lowering.
            interp_value_from_ref_word(
                fz_runtime::ir_runtime::fz_alloc_bitstring_const(
                    runtime.cur_proc(),
                    bytes.as_ptr() as u64,
                    bytes.len() as u64,
                    *bit_len,
                ),
                "ConstBitstring",
            )?
        }
        Prim::MakeClosure(_, fn_id, captured) => {
            let cap_vals: Vec<AnyValue> = collect(env, captured)?;
            let heap = &mut unsafe { &mut *runtime.cur_proc() }.heap;
            let bits = heap.alloc_closure_slots(fn_id.0, cap_vals.len(), 0);
            let p = fz_runtime::any_value::closure_addr_from_tagged(bits).expect("new closure ptr");
            unsafe { std::ptr::write(p.add(8) as *mut u64, fn_id.0 as u64) };
            for (i, value) in cap_vals.iter().enumerate() {
                unsafe { heap.write_closure_capture_value(p, i, value.value()?) };
            }
            let closure_addr =
                fz_runtime::any_value::closure_addr_from_tagged(bits).expect("closure bits");
            AnyValue::Ref(
                AnyValueRef::from_heap_object(ValueKind::CLOSURE, closure_addr)
                    .expect("closure ref"),
            )
        }
        Prim::MakeTuple(elems) => {
            let arity = elems.len();
            let schema_id = interp_tuple_schema_id(runtime, arity);
            let p = unsafe { &mut *runtime.cur_proc() }
                .heap
                .alloc_struct(schema_id);
            for (i, v) in elems.iter().enumerate() {
                let val = env_get(env, *v)?;
                unsafe { &mut *runtime.cur_proc() }.heap.write_field_slot(
                    p,
                    (i * 8) as u32,
                    val.value()?,
                );
            }
            AnyValue::Ref(AnyValueRef::from_heap_object(ValueKind::STRUCT, p).expect("tuple ref"))
        }
        Prim::DestTupleBegin { arity, .. } => {
            let schema_id = interp_tuple_schema_id(runtime, *arity);
            let p = unsafe { &mut *runtime.cur_proc() }
                .heap
                .alloc_struct(schema_id);
            AnyValue::Ref(AnyValueRef::from_heap_object(ValueKind::STRUCT, p).expect("tuple ref"))
        }
        Prim::DestTupleSet {
            dest, index, value, ..
        } => {
            let dest = env_get(env, *dest)?;
            let dest_value = dest.value()?;
            if dest_value.kind() != ValueKind::STRUCT {
                return Err("DestTupleSet: destination is not a Struct".to_string());
            }
            let p = dest_value
                .heap_addr()
                .ok_or_else(|| "DestTupleSet: null destination".to_string())?;
            let value = env_get(env, *value)?.value()?;
            unsafe { &mut *runtime.cur_proc() }
                .heap
                .write_field_slot(p, index * 8, value);
            AnyValue::Atom(fz_runtime::any_value::NIL_ATOM_ID)
        }
        Prim::DestFreeze { dest, .. } => env_get(env, *dest)?,
        Prim::TupleField(c, idx) => {
            let cv = env_get(env, *c)?;
            let slot = cv.value()?;
            if slot.kind() != ValueKind::STRUCT {
                return Err("TupleField: subject is not a Struct".to_string());
            }
            with_value_ref(cv, "TupleField", |struct_ref| {
                fz_runtime::ir_runtime::fz_struct_get_field_ref(
                    runtime.cur_proc(),
                    struct_ref,
                    idx * 8,
                )
            })
            .and_then(|ref_word| interp_value_from_ref_word(ref_word, "TupleField"))?
        }
        Prim::TypeTest(v, descr) => {
            let descr = crate::concrete_types::ty_descr(descr.as_ref());
            let val = env_get(env, *v)?;
            if matches!(val, AnyValue::Float(_)) {
                return Ok(interp_bool_value(descr.type_test_has_floats()));
            }
            if matches!(val, AnyValue::Int(_)) {
                return Ok(interp_bool_value(descr.type_test_has_ints()));
            }
            let val = val.value()?;
            let mut matched = false;
            if descr.type_test_has_ints() {
                matched |= val.kind() == ValueKind::INT;
            }
            if descr.type_test_atom_is_any() {
                matched |= val.kind() == ValueKind::ATOM;
            } else if descr.type_test_atom_is_cofinite() {
                return Err(
                    "TypeTest: cofinite atom literal sets not yet supported in interpreter".into(),
                );
            } else {
                let names = descr.type_test_atom_literals();
                if !names.is_empty() {
                    matched |= val.kind() == ValueKind::ATOM;
                    if val.kind() == ValueKind::ATOM {
                        let id = val.raw() as u32;
                        for name in &names {
                            if let Some(pos) = module.atom_names.iter().position(|n| n == name)
                                && pos as u32 == id
                            {
                                matched = true;
                                break;
                            }
                        }
                    }
                }
            }
            assert!(
                !descr.type_test_tuple_has_negations(),
                "TypeTest: negated tuple clauses not yet supported"
            );
            if val.kind() == ValueKind::STRUCT
                && let Some(sp) = val.heap_addr()
            {
                let actual_schema =
                    unsafe { fz_runtime::any_value::struct_schema_id(sp as *const u8) };
                for arity in descr.type_test_tuple_arities() {
                    let want_schema = interp_tuple_schema_id(runtime, arity);
                    if actual_schema == want_schema {
                        matched = true;
                        break;
                    }
                }
            }
            interp_bool_value(matched)
        }
        Prim::ListHead(c) => {
            let cv = env_get(env, *c)?;
            interp_list_head(cv)?
        }
        Prim::ListTail(c) => {
            let cv = env_get(env, *c)?;
            interp_list_tail(cv)?
        }
        Prim::IsEmptyList(c) => {
            let cv = env_get(env, *c)?;
            interp_bool_value(cv.is_empty_list())
        }
        Prim::MapGet(m, k) => {
            let mv = env_get(env, *m)?;
            let kv = env_get(env, *k)?;
            interp_map_get(runtime.cur_proc(), mv, kv)?
        }
        Prim::MatcherMapGet(m, k) => {
            let mv = env_get(env, *m)?;
            let kv = env_get(env, *k)?;
            let map = mv.value()?;
            if !is_map_value(map) {
                return Err("MatcherMapGet expects a map".to_string());
            }
            let value = with_value_ref(mv, "MatcherMapGet map", |map_ref| {
                with_value_ref(kv, "MatcherMapGet key", |key_ref| {
                    fz_runtime::ir_runtime::fz_matcher_map_get_ref(
                        runtime.cur_proc(),
                        map_ref,
                        key_ref,
                    )
                })
            })??;
            interp_value_from_ref_word(value, "MatcherMapGet")?
        }
        Prim::IsMatcherMapMiss(v) => {
            let value = env_get(env, *v)?;
            interp_bool_value(matches!(value, AnyValue::Null))
        }
        Prim::MakeMap(entries) => {
            let mut map_bits = if entries.is_empty() {
                fz_runtime::ir_runtime::fz_map_empty(runtime.cur_proc())
            } else {
                0
            };
            for (kv, vv) in entries {
                let k = env_get(env, *kv)?;
                let v = env_get(env, *vv)?;
                map_bits = interp_map_put(runtime.cur_proc(), map_bits, k, v, "MakeMap")?;
            }
            interp_value_from_ref_word(map_bits, "MakeMap")?
        }
        Prim::MapUpdate(base, entries) => {
            let base = env_get(env, *base)?;
            let mut map_bits = base.value()?.ref_word().raw_word();
            for (kv, vv) in entries {
                let k = env_get(env, *kv)?;
                let v = env_get(env, *vv)?;
                map_bits = interp_map_put(runtime.cur_proc(), map_bits, k, v, "MapUpdate")?;
            }
            interp_value_from_ref_word(map_bits, "MapUpdate")?
        }
        Prim::DestMapBegin { base, extra, .. } => {
            let map_bits = match base {
                Some(base) => {
                    let base = env_get(env, *base)?;
                    fz_runtime::ir_runtime::fz_map_dest_begin_update(
                        runtime.cur_proc(),
                        base.value()?.ref_word().raw_word(),
                        *extra as u32,
                    )
                }
                None => {
                    fz_runtime::ir_runtime::fz_map_dest_begin(runtime.cur_proc(), *extra as u32)
                }
            };
            interp_value_from_ref_word(map_bits, "DestMapBegin")?
        }
        Prim::DestMapPut {
            map, key, value, ..
        } => {
            let map = env_get(env, *map)?;
            let key = env_get(env, *key)?;
            let value = env_get(env, *value)?;
            let key = key.value()?;
            let value = value.value()?;
            fz_runtime::ir_runtime::fz_map_dest_put_parts(
                runtime.cur_proc(),
                map.value()?.ref_word().raw_word(),
                key.raw(),
                key.kind().tag() as u64,
                value.raw(),
                value.kind().tag() as u64,
            );
            AnyValue::Atom(fz_runtime::any_value::NIL_ATOM_ID)
        }
        Prim::DestMapFreeze { map, .. } => {
            let map = env_get(env, *map)?;
            let map_bits = fz_runtime::ir_runtime::fz_map_dest_freeze(
                runtime.cur_proc(),
                map.value()?.ref_word().raw_word(),
            );
            interp_value_from_ref_word(map_bits, "DestMapFreeze")?
        }
        Prim::MakeList(elems, tail) => {
            // Mirror ir_codegen: fold cons from right, starting with
            // `tail` (defaulted to the empty list).
            let mut acc = match tail {
                Some(t) => env_get(env, *t)?,
                None => interp_empty_list_value(),
            };
            for e in elems.iter().rev() {
                let ev = env_get(env, *e)?;
                acc = interp_list_cons(runtime.cur_proc(), ev, acc, "MakeList")?;
            }
            acc
        }
        Prim::DestListBegin { .. } => AnyValue::Atom(fz_runtime::any_value::NIL_ATOM_ID),
        Prim::DestListCons { head, tail, .. } => {
            let head = env_get(env, *head)?;
            let tail = match tail {
                Some(t) => env_get(env, *t)?,
                None => interp_empty_list_value(),
            };
            interp_list_cons(runtime.cur_proc(), head, tail, "DestListCons")?
        }
        Prim::DestListFreeze { list, .. } => env_get(env, *list)?,
        // fz-axu.23 (M2) — lower_program_full erases Prim::Brand
        // before the interp sees the module. Surface a stray Brand
        // instead of silently aliasing.
        Prim::Brand(_, _) => unreachable!(
            "Prim::Brand reached interp — erasure should run inside lower_program_full"
        ),
        _ => {
            return Err(format!(
                "interp .5.2: prim {:?} not yet supported (lands in fz-ul4.23.5.3+)",
                std::mem::discriminant(prim)
            ));
        }
    })
}
