//! Primitive lowering helpers for codegen.

use super::binary_compare::{BinaryCompare, emit_binary_compare};
use super::bitstring_literal::BitstringLiteral;
use super::construction::{
    AlignedSegment, aligned_segments, descriptor_spec, emit_aligned_construction, emit_append,
    starts_with_unsized_binary,
};
use super::map_literal::lower_make_map;
use super::recipe::{Emitted, emit_box, emit_cell, emit_in_body, emit_inline, emit_slice};
use super::repr::ExternLane;
use super::runtime_test::{
    ConstructionTest, KindEvidence, RuntimeTestEmitter, emit_runtime_type_branch, emit_runtime_type_flag,
};
use super::*;
use crate::ast::BitType;
use crate::fast_hash::HashMap;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitMatchField, BitSizeIr, BlockId, Const, ExternArg, ExternDecl, ExternId, ExternMarshalSite,
    ExternTy, FieldSizeIr, FnId, FrameLane, ModuleAtoms, Prim, UnOp, Var,
};
use crate::runtime_type_predicate::{CallableShapes, Listing, RuntimeTypePredicate};
use cranelift_codegen::ir::{
    self, BlockArg, InstBuilder, MemFlagsData, StackSlotData, StackSlotKind, TrapCode,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataId, FuncId, Linkage, Module};
use fz_runtime::any_value::{
    AnyValue, BITSTRING_BIT_LEN_SHIFT, BITSTRING_BYTES_OFFSET, BITSTRING_HEADER_LEN_MASK, FALSE_ATOM_ID, SlotLayout,
    StructName, TRUE_ATOM_ID, ValueKind, shared_struct_header_word,
};
use fz_runtime::bits::BINVIEW_BYTES_PTR_OFFSET;
use fz_runtime::construction::FzBsField;
use fz_runtime::extern_binary::{fz_binary_as_cstring, fz_binary_as_ptr};
use fz_runtime::ir_runtime::fz_unbox_opaque;
use fz_runtime::ir_runtime::{
    fz_alloc_binview_from_static, fz_bs_build, fz_bs_field_end, fz_bs_field_spec, fz_bs_read_int_ref,
    fz_function_arity, fz_int_float_cmp, fz_list_cons_any, fz_list_cons_stored, fz_map_dest_begin_update,
    fz_map_dest_freeze, fz_map_dest_put, fz_map_get_ref, fz_map_named_schema_ref, fz_matcher_map_get_ref,
    fz_pinned_binary_segment_size, fz_ref_load_atom, fz_ref_load_float, fz_ref_load_int, fz_struct_get_field_ref,
    fz_struct_get_named_field_ref, fz_struct_is_named_ref, fz_struct_module, fz_struct_schema_id_ref,
    fz_value_cmp_raw_const, fz_value_cmp_ref, fz_value_eq_raw_const, fz_value_eq_ref, fz_value_eq_widening_ref,
};
use fz_runtime::process_abi::PROCESS_UNWINDING_OFFSET;
use std::mem::{align_of, offset_of, size_of};
use target_lexicon::{Architecture, OperatingSystem, Triple};

pub(crate) fn emit_map_get_value_ref_for_key<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    map: Var,
    key: Var,
) -> ir::Value {
    let map_ref = body.tagged_var(var_env, map.0);
    let [key_word, key_kind] = map_key_parts(body, t, env, var_env, key);
    let process = body.process_arg();
    runtime_call1!(body, fz_map_get_ref, [process, map_ref, key_word, key_kind])
}

/// A map key as the word a map stores for it and its kind. A key the type
/// says is an atom, integer or float gives its own word beside that constant
/// kind, whatever binding holds it; any other key is read as `stored_parts`
/// reads it.
fn map_key_parts<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    key: Var,
) -> [ir::Value; 2] {
    let binding = binding_for_var(var_env, key.0);
    let (word, kind) = match expected_runtime_value_kind(t, env.active_value_types(), key) {
        Some(ValueKind::ATOM) => (body.value_raw_atom(binding), ValueKind::ATOM),
        Some(ValueKind::INT) => (body.value_raw_int(binding), ValueKind::INT),
        Some(ValueKind::FLOAT) => {
            let float = body.value_raw_float(binding);
            (
                body.b.ins().bitcast(types::I64, MemFlagsData::new(), float),
                ValueKind::FLOAT,
            )
        }
        _ => return stored_parts(body, binding),
    };
    [word, body.b.ins().iconst(types::I64, i64::from(kind.tag()))]
}

/// Put one entry in a map destination; the answer is the reference to the
/// destination to continue with.
pub(super) fn emit_map_destination_put<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    map_bits: ir::Value,
    key: CodegenValue,
    value: CodegenValue,
) -> ir::Value {
    let [key_word, key_kind] = stored_parts(body, key);
    let [value_word, value_kind] = stored_parts(body, value);
    let process = body.process_arg();
    runtime_call1!(
        body,
        fz_map_dest_put,
        [process, map_bits, key_word, key_kind, value_word, value_kind]
    )
}

/// A cell onto the tail, through the inline row of the runtime entry `$item`
/// when the tail is known to be a list, and through the entry itself when it
/// may not be: the entry places a terminator cell for a tail that is not a
/// list.
macro_rules! list_cons_entry {
    (@word $arg:ident) => { _ };
    ($body:expr, $tail:expr, $item:ident, [$($arg:ident),+ $(,)?]) => {{
        let args = [$($arg),+];
        if $tail.is_list() {
            emit_cell($body, stringify!($item), &args)
        } else {
            let item: unsafe extern "C" fn($(list_cons_entry!(@word $arg)),+) -> _ = $item;
            let call = $body.call_runtime(stringify!($item), item, &args);
            $body.sole_result(call)
        }
    }};
}

pub(crate) fn emit_list_cons_bif<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    head: Var,
    head_kind: Option<ValueKind>,
    tail: ListTailBits,
) -> ir::Value {
    let [tail_word, tail_kind] = body.list_tail_words(tail);
    let head_value = binding_for_var(var_env, head.0);
    let process = body.process_arg();
    if let Some([head_word, head_kind]) = cons_head_words(body, head_kind, head_value) {
        return list_cons_entry!(
            body,
            tail,
            fz_list_cons_stored,
            [process, head_word, head_kind, tail_word, tail_kind]
        );
    }
    let head_ref = body.value_as_any_ref(head_value);
    list_cons_entry!(body, tail, fz_list_cons_any, [process, head_ref, tail_word, tail_kind])
}

/// The head as the stored word and kind a cell holds it in, when the head is a
/// number the call site holds unboxed or a value that already travels as a
/// stored pair. `None` is a head that is one ref word.
fn cons_head_words<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    head_kind: Option<ValueKind>,
    head_value: CodegenValue,
) -> Option<[ir::Value; 2]> {
    let scalar_kind = cons_head_kind(head_kind, head_value);
    let word = match scalar_kind {
        Some(ValueKind::INT) => body.value_raw_int(head_value),
        Some(ValueKind::FLOAT) => {
            let float = body.value_raw_float(head_value);
            body.b.ins().bitcast(types::I64, MemFlagsData::new(), float)
        }
        Some(ValueKind::ATOM) => body.value_raw_atom(head_value),
        _ if matches!(head_value, CodegenValue::Stored { .. }) => return Some(body.value_stored_words(head_value)),
        _ => return None,
    };
    let kind = scalar_kind.expect("a scalar head has its kind");
    Some([word, body.b.ins().iconst(types::I64, i64::from(kind.tag()))])
}

/// The scalar kind a cons head can be stored in unboxed: the kind the caller
/// proved, or the one the binding already carries. `None` conses a tagged
/// value ref.
fn cons_head_kind(head_kind: Option<ValueKind>, head_value: CodegenValue) -> Option<ValueKind> {
    if head_kind.is_some() {
        return head_kind;
    }
    match head_value {
        CodegenValue::RawInt(_)
        | CodegenValue::Known {
            kind: ValueKind::INT, ..
        } => Some(ValueKind::INT),
        CodegenValue::RawF64(_)
        | CodegenValue::Known {
            kind: ValueKind::FLOAT, ..
        } => Some(ValueKind::FLOAT),
        CodegenValue::RawAtom(_)
        | CodegenValue::Known {
            kind: ValueKind::ATOM, ..
        } => Some(ValueKind::ATOM),
        _ => None,
    }
}

/// The slot content a var gives a read-only aggregate: its immediate or the
/// read-only object it is, and `None` for a var that is neither.
pub(super) fn static_literal_field_for_var(
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
        .static_objects
        .get(&var.0)
        .copied()
        .map(StaticLiteralField::Object)
}

fn try_static_struct_literal<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    dest_var: Var,
    schema_id: u32,
    name: StructName,
    fields: &[Var],
) -> Result<Option<CodegenValue>, CodegenError> {
    let Some(static_fields) = fields
        .iter()
        .map(|field| static_literal_field_for_var(body.cache, var_env, *field))
        .collect::<Option<Vec<_>>>()
    else {
        return Ok(None);
    };

    let data_id = define_static_struct_literal(body, env, dest_var, schema_id, name, &static_fields)?;
    Ok(Some(static_object_literal(body, dest_var, data_id, ValueKind::STRUCT)))
}

fn define_static_struct_literal<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    dest_var: Var,
    schema_id: u32,
    name: StructName,
    fields: &[StaticLiteralField],
) -> Result<DataId, CodegenError> {
    let layout = SlotLayout::of(fields.len());
    let mut buf = vec![0u8; layout.size()];
    buf[0..8].copy_from_slice(&shared_struct_header_word(schema_id, name).to_le_bytes());

    let mut child_relocs = Vec::new();
    for (idx, field) in fields.iter().enumerate() {
        let raw_offset = SlotLayout::slot_offset(idx);
        let kind_offset = layout.kind_offset(idx);
        match *field {
            StaticLiteralField::Scalar(value) => {
                buf[raw_offset..raw_offset + SLOT_BYTES as usize].copy_from_slice(&value.raw().to_le_bytes());
                buf[kind_offset] = value.kind().tag();
            }
            StaticLiteralField::Object(object) => {
                child_relocs.push((raw_offset, object.data_id));
                buf[kind_offset] = object.kind.tag();
            }
        }
    }

    let name = static_object_name(body, env, "struct", dest_var);
    let addresses = child_relocs
        .into_iter()
        .map(|(offset, child)| (offset, StaticAddress::Data(child)))
        .collect::<Vec<_>>();
    define_read_only_object(body.jmod, &name, buf, &addresses)
}

/// A symbol for the next read-only object of `what` this function defines.
pub(super) fn static_object_name<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    what: &str,
    dest_var: Var,
) -> String {
    let idx = body.cache.static_object_count;
    body.cache.static_object_count += 1;
    format!(
        ".fz_static_{what}_{}_{}_{}_{}",
        env.active_body_fn_id.0, env.active_spec_id, dest_var.0, idx
    )
}

/// The value of the read-only object `data_id` that `dest_var` is, which a
/// later literal aggregate can embed by data relocation.
pub(super) fn static_object_literal<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    dest_var: Var,
    data_id: DataId,
    kind: ValueKind,
) -> CodegenValue {
    body.cache
        .static_objects
        .insert(dest_var.0, StaticObject { data_id, kind });
    body.static_object_value(data_id, kind)
}

/// A struct or tuple of `fields`: read-only program data when every field is
/// a constant, otherwise one allocation with each field stored in place.
fn build_struct<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    dest_var: Var,
    schema_id: u32,
    name: StructName,
    fields: &[Var],
) -> Result<LowerOut, CodegenError> {
    if let Some(static_ref) = try_static_struct_literal(body, env, var_env, dest_var, schema_id, name, fields)? {
        return Ok(LowerOut::Strict(static_ref));
    }
    let object = body.alloc_struct(schema_id, name, fields.len());
    for (index, field) in fields.iter().enumerate() {
        let addressed = addressed_object_share(t, env.active_value_types(), *field);
        body.store_field(&object, index, binding_for_var(var_env, field.0), addressed);
    }
    Ok(LowerOut::ValueRef(object.reference))
}

/// The binary a construction spells: built in place when every segment is a
/// whole number of bytes of a kind compiled code writes, else by one call to
/// `fz_bs_build` over a descriptor per segment. A construction that starts with
/// an unsized binary is an append, which the runtime extends in place when that
/// binary is a view; see `emit_append`.
fn lower_make_bitstring<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    fields: &[BitFieldIr],
) -> LowerOut {
    if let Some(segments) = aligned_segments(fields) {
        let values: Vec<_> = segments
            .iter()
            .copied()
            .zip(fields)
            .map(|(segment, f)| {
                let value = match segment {
                    AlignedSegment::Integer { .. } => body.as_raw_i64(var_env, f.value.0),
                    AlignedSegment::Binary { .. } | AlignedSegment::Literal(_) => body.tagged_var(var_env, f.value.0),
                };
                (segment, value)
            })
            .collect();
        if starts_with_unsized_binary(&segments) {
            let built = emit_append(body, &values);
            return LowerOut::ValueRef(built);
        }
        return LowerOut::ValueRef(emit_aligned_construction(body, &values));
    }
    LowerOut::ValueRef(build_by_runtime(body, var_env, fields))
}

/// The ref word of the binary `fz_bs_build` makes from a descriptor per segment.
fn build_by_runtime<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    fields: &[BitFieldIr],
) -> ir::Value {
    let process = body.process_arg();
    let slot = body.b.create_sized_stack_slot(StackSlotData::new(
        StackSlotKind::ExplicitSlot,
        (fields.len() * size_of::<FzBsField>()) as u32,
        align_of::<FzBsField>().trailing_zeros() as u8,
    ));
    for (index, f) in fields.iter().enumerate() {
        let (size_present, size_value) = match &f.size {
            None => (0, body.b.ins().iconst(types::I64, 0)),
            Some(FieldSizeIr::Literal(n)) => (1, body.b.ins().iconst(types::I64, *n as i64)),
            Some(FieldSizeIr::Var(v)) => (1, body.as_raw_i64(var_env, v.0)),
        };
        let spec = descriptor_spec(f, size_present);
        let value = if f.ty == BitType::Float {
            body.as_float_word(var_env, f.value.0)
        } else if f.ty.writes_scalar_word() {
            body.as_raw_i64(var_env, f.value.0)
        } else {
            body.tagged_var(var_env, f.value.0)
        };
        let spec = body.b.ins().iconst(types::I64, spec as i64);
        let base = index * size_of::<FzBsField>();
        for (offset, word) in [
            (offset_of!(FzBsField, spec), spec),
            (offset_of!(FzBsField, size), size_value),
            (offset_of!(FzBsField, value), value),
        ] {
            body.b.ins().stack_store(types::I64, word, slot, (base + offset) as i32);
        }
    }
    let descriptors = body.b.ins().stack_addr(types::I64, slot, 0);
    let count = body.b.ins().iconst(types::I64, fields.len() as i64);
    runtime_call1!(body, fz_bs_build, [process, descriptors, count])
}

/// Lower collection-typed Prim variants (List, Tuple, AllocStruct, Bitstring,
/// Map, Vec) to a tagged `ir::Value`. Called by `lower_prim` for these arms.
pub(crate) fn lower_collection_prim<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    dest_var: Var,
    block_id: BlockId,
) -> Result<LowerOut, CodegenError> {
    let value_types = env.active_value_types();
    let tuple_schema_ids = env.tuple_schema_ids;
    let v: LowerOut = match prim {
        Prim::ListHead(c) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            LowerOut::ValueRefWord(body.list_head(list_ref))
        }
        Prim::ListTail(c) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            let shape = list_shape(t, value_types, *c);
            LowerOut::ValueRefWord(body.list_tail(list_ref, shape))
        }
        Prim::MakeList(elems, tail, retention) => {
            if elems.len() == 1
                && let Some(tail_var) = tail
                && let Some(retention) = retention
            {
                let tail = list_tail_bits_for_var(body, t, value_types, var_env, *tail_var);
                let reused = emit_list_retention_or_alloc(body, var_env, elems[0], tail, *retention);
                if let Some(reused) = reused {
                    return Ok(LowerOut::ValueRef(reused));
                }
            }
            // Default tail of a list-literal is the empty list (`[]`),
            // NOT the nil atom value — distinct runtime bit patterns.
            let mut acc = match tail {
                Some(tail_var) => list_tail_bits_for_var(body, t, value_types, var_env, *tail_var),
                None => ListTailBits::Empty,
            };
            for e in elems.iter().rev() {
                let cons = emit_list_cons_bif(body, var_env, *e, expected_runtime_value_kind(t, value_types, *e), acc);
                acc = ListTailBits::NonEmptyValueRef(cons);
            }
            match acc {
                ListTailBits::NonEmptyValueRef(bits) | ListTailBits::ValueRef(bits) => LowerOut::ValueRef(bits),
                ListTailBits::Empty => LowerOut::ValueRefWord(body.empty_list_ref()),
                ListTailBits::Checked(_) => unreachable!("a list with no elements has no tail to check"),
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
            build_struct(body, t, env, var_env, dest_var, schema_id, StructName::Anonymous, elems)?
        }
        Prim::MakeStruct { module, fields } => {
            let schema_id = *env.named_schema_ids.get(module).ok_or_else(|| {
                CodegenError::new(format!(
                    "struct schema {} not pre-registered (compile() walk missed it?)",
                    module
                ))
            })?;
            let field_vars = fields.iter().map(|(_, field_var)| *field_var).collect::<Vec<_>>();
            build_struct(
                body,
                t,
                env,
                var_env,
                dest_var,
                schema_id,
                StructName::Named,
                &field_vars,
            )?
        }
        Prim::TupleField(c, idx) => {
            // Every TupleField is gated by a preceding runtime type-test predicate
            // that runtime-checks the subject is a matching-arity Struct
            // heap value, so the load is provably safe. A SIGSEGV here
            // would be an IR integrity bug worth surfacing loudly — do
            // NOT add `notrap`, which would silently mask it.
            let field_offset = body.b.ins().iconst(types::I32, (*idx as i64) * SLOT_BYTES as i64);
            let struct_ref = body.tagged_var(var_env, c.0);
            let process = body.process_arg();
            LowerOut::ValueRefWord(runtime_call1!(
                body,
                fz_struct_get_field_ref,
                [process, struct_ref, field_offset]
            ))
        }
        Prim::StructField(c, field) => {
            let atom_id = env
                .module
                .atoms
                .id_of(field.as_str())
                .ok_or_else(|| CodegenError::new(format!("field atom `{}` not interned", field)))?;
            let struct_ref = body.tagged_var(var_env, c.0);
            let process = body.process_arg();
            let atom = body.b.ins().iconst(types::I64, atom_id as i64);
            LowerOut::ValueRefWord(runtime_call1!(
                body,
                fz_struct_get_named_field_ref,
                [process, struct_ref, atom]
            ))
        }
        Prim::StructModule(c) => {
            let struct_ref = body.tagged_var(var_env, c.0);
            let process = body.process_arg();
            LowerOut::ValueRefWord(runtime_call1!(body, fz_struct_module, [process, struct_ref]))
        }
        Prim::MakeBitstring(fields) => lower_make_bitstring(body, var_env, fields),
        Prim::ConstBitstring(bytes, bit_len) => {
            let literal = env
                .bitstring_literals
                .borrow_mut()
                .literal(body.jmod, bytes, *bit_len)?;
            match literal {
                BitstringLiteral::Object(object) => {
                    LowerOut::Strict(static_object_literal(body, dest_var, object, ValueKind::BITSTRING))
                }
                BitstringLiteral::Shared(shared) => {
                    let gv = body.jmod.declare_data_in_func(shared, body.b.func);
                    let shared = body.b.ins().symbol_value(types::I64, gv);
                    let bit_len = body.b.ins().iconst(types::I64, *bit_len as i64);
                    let process = body.process_arg();
                    LowerOut::ValueRef(runtime_call1!(
                        body,
                        fz_alloc_binview_from_static,
                        [process, shared, bit_len]
                    ))
                }
            }
        }
        Prim::MakeMap { entries, in_key_order } => {
            return lower_make_map(body, t, env, var_env, dest_var, entries, *in_key_order);
        }
        Prim::DestMapBeginUpdate(base) => {
            let process = body.process_arg();
            let base_bits = body.any_ref_for_var(var_env, base.0);
            LowerOut::ValueRef(runtime_call1!(body, fz_map_dest_begin_update, [process, base_bits]))
        }
        Prim::DestMapPut { map, key, value } => {
            let map_bits = body.any_ref_for_var(var_env, map.0);
            let key = binding_for_var(var_env, key.0);
            let value = binding_for_var(var_env, value.0);
            LowerOut::ValueRef(emit_map_destination_put(body, map_bits, key, value))
        }
        Prim::StructWith {
            base,
            module,
            arity,
            stores,
            rewrite,
        } => {
            let base_ref = body.any_ref_for_var(var_env, base.0);
            let slot_blk = body.b.create_block();
            let keyed_blk = body.b.create_block();
            let join_blk = body.b.create_block();
            body.b.append_block_param(join_blk, types::I64);
            let no_args: Vec<BlockArg> = Vec::new();
            let in_struct_layout = body.has_struct_layout(base_ref, struct_schema_id(env, module)?);
            body.b
                .ins()
                .brif(in_struct_layout, slot_blk, &no_args, keyed_blk, &no_args);

            body.b.switch_to_block(slot_blk);
            body.b.seal_block(slot_blk);
            let object = body.reuse_or_copy_struct(base_ref, *arity as usize, *rewrite);
            for store in stores {
                let addressed = addressed_object_share(t, value_types, store.value);
                body.store_field(
                    &object,
                    store.slot as usize,
                    binding_for_var(var_env, store.value.0),
                    addressed,
                );
            }
            body.b.ins().jump(join_blk, &[BlockArg::Value(object.reference)]);

            body.b.switch_to_block(keyed_blk);
            body.b.seal_block(keyed_blk);
            body.b.set_cold_block(keyed_blk);
            let process = body.process_arg();
            let mut map = runtime_call1!(body, fz_map_dest_begin_update, [process, base_ref]);
            for store in stores {
                map = emit_map_destination_put(
                    body,
                    map,
                    binding_for_var(var_env, store.key.0),
                    binding_for_var(var_env, store.value.0),
                );
            }
            let process = body.process_arg();
            let updated = runtime_call1!(body, fz_map_dest_freeze, [process, map]);
            body.b.ins().jump(join_blk, &[BlockArg::Value(updated)]);

            body.b.switch_to_block(join_blk);
            body.b.seal_block(join_blk);
            LowerOut::ValueRef(body.b.block_params(join_blk)[0])
        }
        Prim::DestMapFreeze(map) => {
            let map_bits = body.any_ref_for_var(var_env, map.0);
            let process = body.process_arg();
            LowerOut::ValueRef(runtime_call1!(body, fz_map_dest_freeze, [process, map_bits]))
        }
        Prim::MapGet(m, k) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k);
            LowerOut::ValueRefWord(value_ref)
        }
        Prim::MatcherMapGet(m, k) => {
            let map_ref = body.tagged_var(var_env, m.0);
            let process = body.process_arg();
            let scan = one_word_key(body, binding_for_var(var_env, k.0))
                .map(|(word, kind)| WordKeyFind::emit(body.b, process, map_ref, word, kind));
            let [key_word, key_kind] = stored_parts(body, binding_for_var(var_env, k.0));
            let answer = runtime_call1!(body, fz_matcher_map_get_ref, [process, map_ref, key_word, key_kind]);
            LowerOut::ValueRefWord(match scan {
                Some(scan) => scan.finish(body.b, answer),
                None => answer,
            })
        }
        Prim::IsMapMiss(v) => {
            let is_miss = body.value_is_tag(binding_for_var(var_env, v.0), ValueKind::NULL);
            LowerOut::Strict(strict_bool(body.b, is_miss))
        }
        _ => unreachable!("lower_collection_prim: not a collection prim"),
    };
    Ok(v)
}

/// The word and kind of a map key that is an integer or an atom wherever this
/// code runs. Such a key is found where the test stands (`WordKeyFind`).
fn one_word_key<M: Module>(body: &mut CodegenFn<'_, '_, M>, key: CodegenValue) -> Option<(ir::Value, ValueKind)> {
    value_raw_kind_parts(body, key).filter(|(_, kind)| matches!(*kind, ValueKind::INT | ValueKind::ATOM))
}

/// How far a match field reaches from where it starts.
enum MatchExtent {
    /// A fixed number of bits: `size * unit`.
    Bits(ir::Value),
    /// To the end of the binary: the last, unsized `binary` or `bits` field.
    Rest,
    /// No extent: an unsized `binary` or `bits` field that is not the last.
    Never,
    /// A `utf8` field: its bytes say how wide it is, so only the runtime that
    /// reads them can say where it ends (`BitFieldEnd`).
    Bytes,
    /// A `utf16` or `utf32` field, which the runtime refuses when it reads.
    Unsupported,
}

/// A match field's size operand widened to 64 bits. A size is the low 32 bits
/// of the integer it names.
fn emit_match_field_size<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    size: &Option<BitSizeIr>,
) -> Option<ir::Value> {
    let narrow = match size.as_ref()? {
        BitSizeIr::Literal(n) => return Some(body.b.ins().iconst(types::I64, *n as i64)),
        BitSizeIr::Var(v) => {
            let raw = body.as_raw_i64(var_env, v.0);
            body.b.ins().ireduce(types::I32, raw)
        }
        BitSizeIr::ByteSizeOf(v) => {
            let pinned = body.tagged_var(var_env, v.0);
            runtime_call1!(body, fz_pinned_binary_segment_size, [pinned])
        }
    };
    Some(body.b.ins().uextend(types::I64, narrow))
}

/// The operands the runtime's field functions take: the field's packed spec and
/// its size, which is 0 when the field names none.
fn emit_runtime_field_operands<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    field: &BitMatchField,
) -> (ir::Value, ir::Value) {
    let size_value = match emit_match_field_size(body, var_env, &field.size) {
        Some(size) => body.b.ins().ireduce(types::I32, size),
        None => body.b.ins().iconst(types::I32, 0),
    };
    let field_spec = fz_bs_field_spec(
        field.ty.tag(),
        field.size.is_some() as u32,
        field.unit.unwrap_or(field.ty.default_unit()),
        field.endian.tag(),
        field.signed as u32,
        field.is_last as u32,
    );
    (body.b.ins().iconst(types::I64, field_spec as i64), size_value)
}

fn match_field_extent<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    field: &BitMatchField,
) -> MatchExtent {
    if let Some(bits) = field.static_bits() {
        return MatchExtent::Bits(body.b.ins().iconst(types::I64, bits as i64));
    }
    let unit = field.unit.unwrap_or(field.ty.default_unit()) as i64;
    let sized = |body: &mut CodegenFn<'_, '_, M>, default_size: i64| {
        let bits = match emit_match_field_size(body, var_env, &field.size) {
            Some(size) => body.b.ins().imul_imm_s(size, unit),
            None => body.b.ins().iconst(types::I64, default_size * unit),
        };
        MatchExtent::Bits(bits)
    };
    match field.ty {
        BitType::Integer => sized(body, 8),
        BitType::Float => sized(body, 64),
        BitType::Binary | BitType::Bits => match (&field.size, field.is_last) {
            (Some(_), _) => sized(body, 0),
            (None, true) => MatchExtent::Rest,
            (None, false) => MatchExtent::Never,
        },
        BitType::Utf8 => MatchExtent::Bytes,
        BitType::Utf16 | BitType::Utf32 => MatchExtent::Unsupported,
    }
}

/// The bit length `BitstringBitLen` answers for a value that is not a binary:
/// no binary has a negative length.
const NOT_A_BINARY: i64 = -1;

fn load_word(b: &mut FunctionBuilder<'_>, address: ir::Value, offset: usize) -> ir::Value {
    b.ins()
        .load(types::I64, MemFlagsData::trusted(), address, offset as i32)
}

/// The bit length of a reference the lowering has proven a binary. An inline
/// bitstring and a binary view both lead with the same header word, whose
/// length field sits below the shared mark.
pub(crate) fn emit_proven_binary_bit_len(b: &mut FunctionBuilder<'_>, source_ref: ir::Value) -> ir::Value {
    let addr = address_field(b, source_ref);
    let header = load_word(b, addr, 0);
    bit_len_of_header(b, header)
}

/// Bits of a binary's header word above the length field.
const HEADER_BITS_ABOVE_LEN: u32 = BITSTRING_HEADER_LEN_MASK.leading_zeros();

/// How far the length field sits from the low end once those bits are gone.
const HEADER_LEN_RIGHT_SHIFT: u32 = HEADER_BITS_ABOVE_LEN + BITSTRING_BIT_LEN_SHIFT;

const _: () = assert!(
    BITSTRING_HEADER_LEN_MASK & (BITSTRING_HEADER_LEN_MASK + 1) == 0,
    "the length mask is a run of low bits, so shifting out the bits above it isolates the field"
);

/// The bit length a binary's header word holds: `(header & LEN_MASK) >> SHIFT`
/// as a shift left that drops the bits above the field and a shift right that
/// drops the clear nibble below it, which the target does in one instruction.
pub(crate) fn bit_len_of_header(b: &mut FunctionBuilder<'_>, header: ir::Value) -> ir::Value {
    let field_at_top = b.ins().ishl_imm_u(header, i64::from(HEADER_BITS_ABOVE_LEN));
    b.ins().ushr_imm_u(field_at_top, i64::from(HEADER_LEN_RIGHT_SHIFT))
}

/// The bit length of a binary; `NOT_A_BINARY` for any other value. One test of
/// the reference's kind against the set of kinds a binary is held in decides
/// whether it is a binary, and the length is read the same way from either form.
fn emit_binary_bit_len<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    source_ref: ir::Value,
) -> ir::Value {
    let kind = kind_field(body.b, source_ref);
    let is_binary = kind_is_one_of(body.b, kind, ValueKind::is_binary_repr);
    let read_b = body.b.create_block();
    let miss_b = body.b.create_block();
    let join_b = body.b.create_block();
    body.b.append_block_param(join_b, types::I64);
    body.b.ins().brif(is_binary, read_b, &[], miss_b, &[]);

    body.b.switch_to_block(read_b);
    body.b.seal_block(read_b);
    let length = emit_proven_binary_bit_len(body.b, source_ref);
    body.b.ins().jump(join_b, &[BlockArg::Value(length)]);

    body.b.switch_to_block(miss_b);
    body.b.seal_block(miss_b);
    let missed = body.b.ins().iconst(types::I64, NOT_A_BINARY);
    body.b.ins().jump(join_b, &[BlockArg::Value(missed)]);

    body.b.switch_to_block(join_b);
    body.b.seal_block(join_b);
    body.b.block_params(join_b)[0]
}

/// The address of a binary's first byte: inline bytes follow the header, and a
/// view holds the address in its second word.
fn emit_binary_base<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, source_ref: ir::Value) -> ir::Value {
    let addr = address_field(body.b, source_ref);
    let kind = kind_field(body.b, source_ref);
    let is_view = body
        .b
        .ins()
        .icmp_imm_s(IntCC::Equal, kind, ValueKind::BINVIEW.tag() as i64);
    let view_b = body.b.create_block();
    let inline_b = body.b.create_block();
    let join_b = body.b.create_block();
    body.b.append_block_param(join_b, types::I64);
    body.b.ins().brif(is_view, view_b, &[], inline_b, &[]);

    body.b.switch_to_block(view_b);
    body.b.seal_block(view_b);
    let from_view = load_word(body.b, addr, BINVIEW_BYTES_PTR_OFFSET);
    body.b.ins().jump(join_b, &[BlockArg::Value(from_view)]);

    body.b.switch_to_block(inline_b);
    body.b.seal_block(inline_b);
    let from_inline = body.b.ins().iadd_imm_s(addr, BITSTRING_BYTES_OFFSET as i64);
    body.b.ins().jump(join_b, &[BlockArg::Value(from_inline)]);

    body.b.switch_to_block(join_b);
    body.b.seal_block(join_b);
    body.b.block_params(join_b)[0]
}

/// The big-endian integer of `bytes` bytes at `base + offset`, read in loads of
/// four, two and one bytes, most significant first.
fn emit_big_endian_load<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    base: ir::Value,
    byte_offset: u32,
    bytes: u8,
) -> ir::Value {
    let mut value = body.b.ins().iconst(types::I64, 0);
    let mut at = byte_offset as i32;
    let mut remaining = bytes;
    while remaining > 0 {
        let chunk: u8 = match remaining {
            4.. => 4,
            2..=3 => 2,
            _ => 1,
        };
        let ty = match chunk {
            4 => types::I32,
            2 => types::I16,
            _ => types::I8,
        };
        let loaded = body.b.ins().load(ty, MemFlagsData::new(), base, at);
        let ordered = if chunk > 1 { body.b.ins().bswap(loaded) } else { loaded };
        let widened = body.b.ins().uextend(types::I64, ordered);
        let shifted = body.b.ins().ishl_imm_u(value, i64::from(chunk) * 8);
        value = body.b.ins().bor(shifted, widened);
        at += i32::from(chunk);
        remaining -= chunk;
    }
    value
}

/// The match prims: the position a match carries is an integer, so "does the
/// next field fit" and "where does it end" are arithmetic on it, and a read is
/// a call that cannot miss.
fn lower_bit_match_prim<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    Ok(match prim {
        Prim::BitstringBitLen(source) => {
            let source_ref = body.tagged_var(var_env, source.0);
            LowerOut::RawI64(emit_binary_bit_len(body, source_ref))
        }
        Prim::BinaryBitLen(source) => {
            let source_ref = body.tagged_var(var_env, source.0);
            LowerOut::RawI64(emit_proven_binary_bit_len(body.b, source_ref))
        }
        Prim::BitstringBase(source) => {
            let source_ref = body.tagged_var(var_env, source.0);
            LowerOut::RawI64(emit_binary_base(body, source_ref))
        }
        Prim::BitReadByteInt {
            base,
            byte_offset,
            bytes,
        } => {
            let base = body.as_raw_i64(var_env, base.0);
            LowerOut::RawI64(emit_big_endian_load(body, base, *byte_offset, *bytes))
        }
        Prim::BitReadByteIntAt { base, pos, bytes } => {
            let base = body.as_raw_i64(var_env, base.0);
            let pos = body.as_raw_i64(var_env, pos.0);
            LowerOut::RawI64(emit_int_read_at_bit(body, base, pos, *bytes))
        }
        Prim::BitFieldFits { pos, bit_len, field } => {
            let pos = body.as_raw_i64(var_env, pos.0);
            let bit_len = body.as_raw_i64(var_env, bit_len.0);
            let fits = match match_field_extent(body, var_env, field) {
                MatchExtent::Never => body.b.ins().iconst(types::I8, 0),
                MatchExtent::Rest if field.ty == BitType::Binary => {
                    let rest = body.b.ins().isub(bit_len, pos);
                    let negative_or_partial = body.b.ins().band_imm_u(rest, i64::MIN | 7);
                    body.b.ins().icmp_imm_s(IntCC::Equal, negative_or_partial, 0)
                }
                MatchExtent::Rest | MatchExtent::Unsupported => body.b.ins().iconst(types::I8, 1),
                MatchExtent::Bytes => panic!("BitFieldFits is asked of a utf8 field: its end is BitFieldEnd's"),
                MatchExtent::Bits(total) => {
                    let end = body.b.ins().iadd(pos, total);
                    let within = body.b.ins().icmp(IntCC::SignedLessThanOrEqual, end, bit_len);
                    let width_ok = match field.ty {
                        BitType::Integer => Some(body.b.ins().icmp_imm_s(IntCC::UnsignedLessThanOrEqual, total, 64)),
                        BitType::Float => {
                            let is_32 = body.b.ins().icmp_imm_s(IntCC::Equal, total, 32);
                            let is_64 = body.b.ins().icmp_imm_s(IntCC::Equal, total, 64);
                            Some(body.b.ins().bor(is_32, is_64))
                        }
                        _ => None,
                    };
                    match width_ok {
                        Some(width_ok) => body.b.ins().band(width_ok, within),
                        None => within,
                    }
                }
            };
            if body.cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(fits));
            }
            LowerOut::Strict(strict_bool(body.b, fits))
        }
        Prim::BitFieldNext { pos, field } => {
            let pos = body.as_raw_i64(var_env, pos.0);
            let MatchExtent::Bits(total) = match_field_extent(body, var_env, field) else {
                panic!("BitFieldNext is asked of a sized field: the last field reads to the end");
            };
            LowerOut::RawI64(body.b.ins().iadd(pos, total))
        }
        Prim::BitFieldEnd { source, pos, field } => {
            let source_ref = body.tagged_var(var_env, source.0);
            let pos = body.as_raw_i64(var_env, pos.0);
            let (field_spec, size_value) = emit_runtime_field_operands(body, var_env, field);
            LowerOut::RawI64(runtime_call1!(
                body,
                fz_bs_field_end,
                [field_spec, size_value, pos, source_ref]
            ))
        }
        Prim::BitReadField { source, pos, field } => {
            let source_ref = body.tagged_var(var_env, source.0);
            let pos = body.as_raw_i64(var_env, pos.0);
            if field.ty.reads_as_integer() {
                let (field_spec, size_value) = emit_runtime_field_operands(body, var_env, field);
                LowerOut::RawI64(runtime_call1!(
                    body,
                    fz_bs_read_int_ref,
                    [source_ref, pos, field_spec, size_value]
                ))
            } else {
                let bit_len = match match_field_extent(body, var_env, field) {
                    MatchExtent::Bits(bits) => bits,
                    MatchExtent::Rest => {
                        let source_bits = emit_proven_binary_bit_len(body.b, source_ref);
                        body.b.ins().isub(source_bits, pos)
                    }
                    MatchExtent::Never | MatchExtent::Bytes | MatchExtent::Unsupported => {
                        panic!("a binary field with no extent is never read")
                    }
                };
                let process = body.process_arg();
                LowerOut::ValueRef(emit_slice(
                    body,
                    "fz_bs_slice_ref",
                    &[process, source_ref, pos, bit_len],
                ))
            }
        }
        _ => unreachable!("lower_bit_match_prim: not a bit match prim"),
    })
}

/// A whole-byte integer field at a runtime bit position, loaded from the
/// binary's bytes at `base`. On a byte boundary the field is the `bytes` bytes
/// there; off it, the field sits inside the `bytes + 1` bytes that cover it,
/// shifted down past the bits before it. The field is known to fit, so both
/// loads stay inside the binary.
fn emit_int_read_at_bit<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    base: ir::Value,
    pos: ir::Value,
    bytes: u8,
) -> ir::Value {
    let byte_pos = body.b.ins().ushr_imm_u(pos, 3);
    let address = body.b.ins().iadd(base, byte_pos);
    let bit_in_byte = body.b.ins().band_imm_u(pos, 7);
    let on_boundary = body.b.ins().icmp_imm_s(IntCC::Equal, bit_in_byte, 0);
    let aligned_b = body.b.create_block();
    let straddling_b = body.b.create_block();
    let join_b = body.b.create_block();
    body.b.append_block_param(join_b, types::I64);
    body.b.ins().brif(on_boundary, aligned_b, &[], straddling_b, &[]);

    body.b.switch_to_block(aligned_b);
    body.b.seal_block(aligned_b);
    let aligned = emit_big_endian_load(body, address, 0, bytes);
    body.b.ins().jump(join_b, &[BlockArg::Value(aligned)]);

    body.b.switch_to_block(straddling_b);
    body.b.seal_block(straddling_b);
    let covering = emit_big_endian_load(body, address, 0, bytes + 1);
    let eight = body.b.ins().iconst(types::I64, 8);
    let drop_bits = body.b.ins().isub(eight, bit_in_byte);
    let shifted = body.b.ins().ushr(covering, drop_bits);
    let mask = (1_u64 << (u32::from(bytes) * 8)) - 1;
    let straddling = body.b.ins().band_imm_u(shifted, mask as i64);
    body.b.ins().jump(join_b, &[BlockArg::Value(straddling)]);

    body.b.switch_to_block(join_b);
    body.b.seal_block(join_b);
    body.b.block_params(join_b)[0]
}

/// `fz_abi` selects what a declared parameter type MEANS.
///
/// A C function taking `binary` wants a `*const u8` into the bytes. An fz
/// runtime helper taking `binary` wants the tagged value ref, because it works
/// in fz's own representation and may allocate a new one. Same declaration,
/// two conventions -- which is why the ABI has to reach this far rather than
/// being consumed at the front door.
fn marshal_extern_arg<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    var: Var,
    ty: ExternTy,
    fz_abi: bool,
) -> Result<ir::Value, CodegenError> {
    Ok(match ty {
        ExternTy::I64 => body.as_raw_i64(var_env, var.0),
        ExternTy::Opaque(kind) => {
            let value_ref = body.tagged_var(var_env, var.0);
            unbox_opaque_word(body, value_ref, kind)
        }
        // A C `int` parameter is the low half of the fz integer.
        ExternTy::I32 => {
            let word = body.as_raw_i64(var_env, var.0);
            body.b.ins().ireduce(types::I32, word)
        }
        ExternTy::F64 => body.as_raw_f64(var_env, var.0),
        ExternTy::Bool => {
            let atom = body.coerce_binding_to(
                *var_env.get(&var.0).expect("bound extern boolean argument"),
                ArgRepr::RawAtom,
            );
            let is_true = body.b.ins().icmp_imm_s(IntCC::Equal, atom, TRUE_ATOM_ID as i64);
            body.b.ins().uextend(types::I64, is_true)
        }
        ExternTy::Binary | ExternTy::CString if fz_abi => body.tagged_var(var_env, var.0),
        ExternTy::CString => {
            let bits = body.tagged_var(var_env, var.0);
            let process = body.process_arg();
            runtime_call1!(body, fz_binary_as_cstring, [process, bits])
        }
        ExternTy::Binary => {
            let bits = body.tagged_var(var_env, var.0);
            runtime_call1!(body, fz_binary_as_ptr, [bits])
        }
        ExternTy::Any => body.tagged_var(var_env, var.0),
        ExternTy::Unit | ExternTy::Never | ExternTy::BinaryCursor | ExternTy::StoredValue => {
            return Err(CodegenError::new(format!(
                "{:?} is not a valid extern argument marshal class",
                ty
            )));
        }
    })
}

/// A pid or reference word an extern returned, held as a value of its kind.
fn box_extern_opaque_word<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    raw: ir::Value,
    kind: ValueKind,
) -> ir::Value {
    let process = body.process_arg();
    box_opaque_word(body, process, raw, kind)
}

/// The ref word of a pid or reference word. A pid is packed into the ref; a
/// reference is boxed on the heap by the runtime.
fn box_opaque_word<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    process: ir::Value,
    raw: ir::Value,
    kind: ValueKind,
) -> ir::Value {
    if kind == ValueKind::PID {
        return immediate_ref_word(body.b, raw, kind);
    }
    let kind = body.b.ins().iconst(types::I64, kind.tag() as i64);
    emit_box(body, "fz_box_opaque_for_any", &[process, raw, kind])
}

/// The pid or reference word a ref word holds. A pid is read from the ref; a
/// reference is read through its heap box by the runtime.
fn unbox_opaque_word<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    value_ref: ir::Value,
    kind: ValueKind,
) -> ir::Value {
    if kind == ValueKind::PID {
        return address_field(body.b, value_ref);
    }
    let kind = body.b.ins().iconst(types::I64, kind.tag() as i64);
    runtime_call1!(body, fz_unbox_opaque, [value_ref, kind])
}

fn emit_variadic_extern_call<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    eid: ExternId,
    args: &[ExternArg],
    dest_var: Var,
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
    let ret = decl
        .ret
        .scalar_ty()
        .ok_or_else(|| CodegenError::new("variadic extern aggregate returns are unsupported"))?;
    if ret == ExternTy::F64 {
        return Err(CodegenError::new(format!(
            "variadic extern `{}` returns a float, which the generated variadic call does not carry",
            decl.symbol
        )));
    }

    let mut marshalled = Vec::with_capacity(args.len());
    for (arg, ty) in args.iter().zip(arg_tys.iter().copied()) {
        marshalled.push((marshal_extern_arg(body, var_env, arg.var, ty, false)?, ty));
    }
    // A parameter that carries no value has no lane; `marshal_extern_arg`
    // refuses one above, so the word it would occupy here is never reached.
    let fixed: Vec<(ir::Value, ir::Type)> = marshalled[..fixed_count]
        .iter()
        .map(|(value, ty)| (*value, ty.lane().unwrap_or(types::I64)))
        .collect();
    // Every variadic value is one integer word: the marshal classes a variadic
    // argument can resolve to are all integer-lane, which is what makes the
    // generated call correct on every target (see `variadic.rs`). C promotes a
    // narrower integer to a full word in the tail, so a `c_int` there is sign
    // extended back to the word it was reduced from.
    let variadic: Vec<ir::Value> = marshalled[fixed_count..]
        .iter()
        .map(|(value, ty)| match ty {
            ExternTy::I32 => body.b.ins().sextend(types::I64, *value),
            _ => *value,
        })
        .collect();

    let callee = foreign_symbol_addr(body, eid, decl.symbol.as_str())?;
    let isa = body.jmod.isa();
    let result = emit_variadic_c_call(body.b, isa, callee, &fixed, &variadic, ret.lane());

    let Some(raw) = result else {
        if body.cache.used_vars.contains(&dest_var.0) {
            return Ok(LowerOut::Strict(strict_const_value(body.b, AnyValue::nil_atom())));
        }
        return Ok(LowerOut::DeadUnit);
    };
    match ret {
        ExternTy::I64 => Ok(LowerOut::RawI64(raw)),
        ExternTy::Opaque(kind) => Ok(LowerOut::ValueRef(box_extern_opaque_word(body, raw, kind))),
        ExternTy::I32 => Ok(LowerOut::RawI64(body.b.ins().sextend(types::I64, raw))),
        ExternTy::Bool => Ok(LowerOut::Strict(decode_foreign_boolean_word(
            body,
            raw,
            body.cache.if_only_conds.contains(&dest_var.0),
        ))),
        ExternTy::Any | ExternTy::Binary | ExternTy::CString => Ok(LowerOut::ValueRef(raw)),
        ExternTy::F64 => unreachable!("a float-returning variadic extern is refused above"),
        ExternTy::Unit | ExternTy::Never => unreachable!("a lane-less return produced no result"),
        ExternTy::BinaryCursor | ExternTy::StoredValue => {
            unreachable!("`binary_cursor` and `stored_value` stand only as parameters")
        }
    }
}

/// The address of a foreign symbol, for a call emitted indirectly.
///
/// A variadic call's parameter list is built per call site, so the symbol is
/// declared once as an ordinary import to name it for the linker (or the JIT's
/// symbol lookup) and then reached through its address. The declared signature
/// is a placeholder: nothing ever calls through it.
/// The reference this function calls extern `eid` through, declared with `sig`
/// on first use.
fn extern_call_ref<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    eid: ExternId,
    symbol: &str,
    sig: &ir::Signature,
) -> Result<ir::FuncRef, CodegenError> {
    if let Some(&cached) = body.cache.extern_calls.get(&eid) {
        return Ok(cached);
    }
    let func_id = body
        .jmod
        .declare_function(symbol, Linkage::Import, sig)
        .map_err(|e| CodegenError::new(format!("declare extern `{symbol}`: {e}")))?;
    let fref = import_call_ref(body.jmod, func_id, body.b.func);
    body.cache.extern_calls.insert(eid, fref);
    Ok(fref)
}

fn foreign_symbol_addr<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    eid: ExternId,
    symbol: &str,
) -> Result<ir::Value, CodegenError> {
    let fref = if let Some(&cached) = body.cache.extern_addrs.get(&eid) {
        cached
    } else {
        let sig = body.jmod.make_signature();
        let func_id = body
            .jmod
            .declare_function(symbol, Linkage::Import, &sig)
            .map_err(|e| CodegenError::new(format!("declare extern `{}`: {}", symbol, e)))?;
        let fref = body.jmod.declare_func_in_func(func_id, body.b.func);
        body.cache.extern_addrs.insert(eid, fref);
        fref
    };
    Ok(body.b.ins().func_addr(types::I64, fref))
}

pub(crate) fn lower_prim<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    prim: &Prim,
    dest_var: Var,
    // `block_id`/`stmt_idx` identify the per-stmt side table holding a
    // variadic extern call's resolved marshal classes.
    block_id: BlockId,
    stmt_idx: usize,
) -> Result<LowerOut, CodegenError> {
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
        Prim::Share(value) => {
            let binding = binding_for_var(var_env, value.0);
            body.share_as(binding, share_class(t, value_types, *value));
            Ok(LowerOut::Strict(binding))
        }
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
                BinOp::Eq | BinOp::Neq | BinOp::Identical => {
                    lower_eq_binop(body, t, value_types, var_env, *op, *a, *bv, dest_var)
                }
                BinOp::Lt | BinOp::Le | BinOp::Gt | BinOp::Ge => {
                    lower_cmp_binop(body, t, value_types, var_env, *op, *a, *bv, dest_var)
                }
                BinOp::And | BinOp::Or => lower_bool_binop(body, var_env, *op, *a, *bv, dest_var),
            }
        }
        Prim::UnOp(op, x) => match op {
            UnOp::Neg => lower_neg(body, t, value_types, var_env, *x),
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
        Prim::MachineCall(..) => Err(CodegenError::new(
            "a machine call answers its lanes as a multi-result statement, never as one variable",
        )),
        Prim::Extern(_, eid, args) => {
            let decl = env.module.extern_by_id(*eid);
            if decl.variadic {
                return emit_variadic_extern_call(body, env, var_env, *eid, args, dest_var, block_id, stmt_idx);
            }
            lower_extern_generic(body, var_env, decl, eid, args, dest_var)
        }
        Prim::IsEmptyList(c) => {
            let cmp = emit_is_empty_list_flag(body, binding_for_var(var_env, c.0));
            if body.cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
        }
        Prim::IsListCons(c) => {
            let cmp = emit_is_list_cons_flag(body, binding_for_var(var_env, c.0));
            if body.cache.if_only_conds.contains(&dest_var.0) {
                return Ok(LowerOut::Condition(cmp));
            }
            Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
        }
        Prim::PopHandler => {
            closure::pop_handler_record(body);
            Ok(LowerOut::DeadUnit)
        }
        Prim::StructSlot {
            base,
            module,
            slot,
            field,
        } => {
            let read = if ty_is_float(t, value_types, dest_var) {
                SlotRead::Float
            } else if ty_is_int(t, value_types, dest_var) {
                SlotRead::Int
            } else if ty_is_atom(t, value_types, dest_var) {
                SlotRead::Atom
            } else {
                SlotRead::Reference
            };
            lower_struct_slot(body, env, var_env, *base, module, *slot, field, read)
        }
        Prim::TupleField(object, slot) if ty_is_float(t, value_types, dest_var) => {
            let object_ref = body.tagged_var(var_env, object.0);
            Ok(LowerOut::RawF64(body.load_slot(object_ref, *slot, types::F64)))
        }
        Prim::TupleField(object, slot) if ty_is_int(t, value_types, dest_var) => {
            let object_ref = body.tagged_var(var_env, object.0);
            Ok(LowerOut::RawI64(body.load_slot(object_ref, *slot, types::I64)))
        }
        Prim::TupleField(object, slot) if ty_is_atom(t, value_types, dest_var) => {
            let object_ref = body.tagged_var(var_env, object.0);
            let atom = body.load_slot(object_ref, *slot, types::I64);
            Ok(LowerOut::Strict(CodegenValue::RawAtom(atom)))
        }
        Prim::MapGet(m, k) if ty_is_float(t, value_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k);
            Ok(LowerOut::RawF64(runtime_call1!(body, fz_ref_load_float, [value_ref])))
        }
        Prim::MapGet(m, k) if ty_is_int(t, value_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k);
            Ok(LowerOut::RawI64(runtime_call1!(body, fz_ref_load_int, [value_ref])))
        }
        Prim::MapGet(m, k) if ty_is_atom(t, value_types, dest_var) => {
            let value_ref = emit_map_get_value_ref_for_key(body, t, env, var_env, *m, *k);
            let atom = runtime_call1!(body, fz_ref_load_atom, [value_ref]);
            Ok(LowerOut::Strict(CodegenValue::RawAtom(atom)))
        }
        Prim::ListHead(c) if ty_is_int(t, value_types, dest_var) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            Ok(LowerOut::RawI64(body.list_head_int(list_ref)))
        }
        Prim::ListHead(c) if ty_is_float(t, value_types, dest_var) => {
            let list_ref = known_list_ref_for_var(var_env, body.b, body.cache, block_id, c.0);
            Ok(LowerOut::RawF64(body.list_head_float(list_ref)))
        }
        Prim::ListHead(..)
        | Prim::ListTail(..)
        | Prim::MakeList(..)
        | Prim::MakeTuple(..)
        | Prim::MakeStruct { .. }
        | Prim::TupleField(..)
        | Prim::StructField(..)
        | Prim::StructModule(..)
        | Prim::MakeBitstring(..)
        | Prim::ConstBitstring(..)
        | Prim::MakeMap { .. }
        | Prim::DestMapBeginUpdate(..)
        | Prim::DestMapPut { .. }
        | Prim::DestMapFreeze(..)
        | Prim::StructWith { .. }
        | Prim::MapGet(..)
        | Prim::MatcherMapGet(..)
        | Prim::IsMapMiss(..) => lower_collection_prim(body, t, env, var_env, prim, dest_var, block_id),
        Prim::BitstringBitLen(..)
        | Prim::BinaryBitLen(..)
        | Prim::BitstringBase(..)
        | Prim::BitReadByteInt { .. }
        | Prim::BitReadByteIntAt { .. }
        | Prim::BitFieldFits { .. }
        | Prim::BitFieldNext { .. }
        | Prim::BitFieldEnd { .. }
        | Prim::BitReadField { .. } => lower_bit_match_prim(body, var_env, prim, dest_var),
        Prim::MakeFnRef(_, fn_id) => lower_make_fn_ref(body, env, *fn_id),
        Prim::MakeClosure(_, fn_id, captured) => lower_make_closure(body, env, var_env, *fn_id, captured),
        Prim::RuntimeTypeTest(v, descr) => lower_runtime_type_predicate(body, env, var_env, *v, descr, dest_var),
        Prim::ClosureCapture { closure, index } => lower_closure_capture(body, var_env, *closure, *index),
        Prim::Frame => Ok(LowerOut::ValueRef(
            body.cache
                .own_continuation
                .expect("only a continuation runs in a body frame"),
        )),
        Prim::FrameLoad { frame, slot, lane } => {
            let frame = frame_word(var_env, *frame);
            Ok(LowerOut::Strict(body.frame_load(frame, *slot, *lane)))
        }
        Prim::FrameStore {
            frame,
            slot,
            lane,
            value,
        } => {
            let frame = frame_word(var_env, *frame);
            let capture = closure_capture_for_var_as(body, var_env, value.0, lane_repr(*lane));
            let frame = body.frame_store(frame, frame_width(env), *slot, capture);
            Ok(LowerOut::ValueRef(frame))
        }
        Prim::FrameClear { frame, slot } => {
            let frame = frame_word(var_env, *frame);
            let frame = body.frame_clear(frame, frame_width(env), *slot);
            Ok(LowerOut::ValueRef(frame))
        }
    }
}

fn frame_word(var_env: &HashMap<u32, CodegenValue>, frame: Var) -> ir::Value {
    match var_env.get(&frame.0) {
        Some(CodegenValue::AnyRef(word)) => *word,
        _ => panic!("a body frame is bound to a continuation word"),
    }
}

fn frame_width(env: &CodegenEnv<'_>) -> u32 {
    env.active_native_body()
        .frame
        .as_ref()
        .expect("a body that touches a frame runs in one")
        .slots
}

fn lane_repr(lane: FrameLane) -> ArgRepr {
    match lane {
        FrameLane::Ref => ArgRepr::ValueRef,
        FrameLane::Int => ArgRepr::RawInt,
        FrameLane::Float => ArgRepr::RawF64,
        FrameLane::Atom => ArgRepr::RawAtom,
        FrameLane::Stored => ArgRepr::Stored,
    }
}

/// The captured value's kind byte makes every lexical slot self-describing.
fn lower_closure_capture<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    closure: Var,
    index: u32,
) -> Result<LowerOut, CodegenError> {
    let value = *var_env.get(&closure.0).expect("closure capture subject");
    let closure_ref = body.value_as_any_ref(value);
    Ok(LowerOut::ValueRef(body.closure_capture_ref_at(
        closure_ref,
        index as usize,
        CaptureCount::InHeader,
    )))
}

/// Lower a `RuntimeTypeTest` prim.
///
/// The subject is one value the surrounding code already holds, and the shared
/// emitter reads it. A tuple a caller delivered lane-wise never reaches here:
/// entry dispatch answers its arity from the transport shape instead.
fn lower_runtime_type_predicate<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    v: Var,
    predicate: &RuntimeTypePredicate,
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    let value = *var_env.get(&v.0).expect("type-test subject");
    let mut emitter = PrimTestEmitter { body, env };
    let flag = emit_runtime_type_flag(&mut emitter, value, predicate)?;
    if body.cache.if_only_conds.contains(&dest_var.0) {
        return Ok(LowerOut::Condition(flag));
    }
    Ok(LowerOut::Strict(strict_bool(body.b, flag)))
}

/// Lower a type test that only feeds its block's `if`: the shared emitter
/// branches straight to the `if`'s successors.
pub(super) fn lower_runtime_type_branch<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    test: BranchingTypeTest<'_>,
) -> Result<(), CodegenError> {
    let value = *var_env.get(&test.subject.0).expect("type-test subject");
    let mut emitter = PrimTestEmitter { body, env };
    emit_runtime_type_branch(&mut emitter, value, test.predicate, test.admit, test.reject)
}

/// The compiled-body door onto the shared runtime-test emitter.
struct PrimTestEmitter<'a, 'b, 'fb, M: cranelift_module::Module> {
    body: &'a mut CodegenFn<'b, 'fb, M>,
    env: &'a CodegenEnv<'a>,
}

impl<'fb, M: cranelift_module::Module> RuntimeTestEmitter<'fb> for PrimTestEmitter<'_, '_, 'fb, M> {
    type Value = CodegenValue;

    fn builder(&mut self) -> &mut FunctionBuilder<'fb> {
        self.body.b
    }

    fn atoms(&self) -> &ModuleAtoms {
        &self.env.module.atoms
    }

    fn tuple_schema_ids(&self) -> &HashMap<usize, u32> {
        self.env.tuple_schema_ids
    }

    fn named_schema_ids(&self) -> &HashMap<fz_runtime::module_name::ModuleName, u32> {
        self.env.named_schema_ids
    }

    fn kind_evidence(&self, value: CodegenValue) -> KindEvidence {
        match value {
            CodegenValue::AnyRef(_) | CodegenValue::Stored { .. } => KindEvidence::Tagged,
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
            CodegenValue::Known {
                kind: ValueKind::LIST, ..
            } => KindEvidence::Opaque,
            CodegenValue::Known { kind, .. } if kind.is_heap() => KindEvidence::Static(kind),
            CodegenValue::Known { .. } => KindEvidence::Opaque,
        }
    }

    fn kind_flag(&mut self, value: CodegenValue, kind: ValueKind) -> Result<ir::Value, CodegenError> {
        Ok(self.body.value_is_tag(value, kind))
    }

    fn kind_in(&mut self, value: CodegenValue, kinds: &[ValueKind]) -> Result<ir::Value, CodegenError> {
        let tag = self.body.value_type_tag(value);
        let tag = self.body.b.ins().uextend(types::I64, tag);
        let member = kind_is_one_of(self.body.b, tag, |kind| kinds.contains(&kind));
        Ok(self.body.b.ins().ireduce(types::I8, member))
    }

    fn bitstring_bit_len(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let source_ref = self.body.value_as_any_ref(value);
        Ok(emit_proven_binary_bit_len(self.body.b, source_ref))
    }

    fn raw_int(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        Ok(self.body.value_raw_int(value))
    }

    fn raw_float_bits(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let raw = self.body.value_raw_float(value);
        Ok(self.body.b.ins().bitcast(types::I64, MemFlagsData::new(), raw))
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
        let raw = runtime_call1!(self.body, fz_struct_schema_id_ref, [struct_ref]);
        Ok(self.body.b.ins().uextend(types::I64, raw))
    }

    fn struct_is_named(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let struct_ref = self.body.value_as_any_ref(value);
        Ok(runtime_condition!(self.body, fz_struct_is_named_ref, [struct_ref]))
    }

    fn map_named_schema(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let map_ref = self.body.value_as_any_ref(value);
        let process = self.body.process_arg();
        let raw = runtime_call1!(self.body, fz_map_named_schema_ref, [process, map_ref]);
        Ok(self.body.b.ins().uextend(types::I64, raw))
    }

    fn tuple_field(&mut self, value: CodegenValue, index: usize) -> Result<CodegenValue, CodegenError> {
        let struct_ref = self.body.value_as_any_ref(value);
        let offset = self.body.b.ins().iconst(types::I32, (index as i64) * SLOT_BYTES as i64);
        let process = self.body.process_arg();
        Ok(CodegenValue::AnyRef(runtime_call1!(
            self.body,
            fz_struct_get_field_ref,
            [process, struct_ref, offset]
        )))
    }

    fn list_head(&mut self, value: CodegenValue) -> Result<CodegenValue, CodegenError> {
        let list_ref = self.body.value_as_any_ref(value);
        Ok(CodegenValue::AnyRef(self.body.list_head(list_ref)))
    }

    fn closure_code(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let closure_ref = self.body.value_as_any_ref(value);
        Ok(self.body.closure_code_ref(closure_ref))
    }

    fn closure_arity(&mut self, value: CodegenValue) -> Result<ir::Value, CodegenError> {
        let closure_ref = self.body.value_as_any_ref(value);
        let process = self.body.process_arg();
        Ok(runtime_call1!(self.body, fz_function_arity, [process, closure_ref]))
    }

    fn closure_capture(&mut self, value: CodegenValue, index: usize) -> Result<CodegenValue, CodegenError> {
        let closure_ref = self.body.value_as_any_ref(value);
        Ok(CodegenValue::AnyRef(self.body.closure_capture_ref_at(
            closure_ref,
            index,
            CaptureCount::InHeader,
        )))
    }

    fn callable_constructions(&mut self, callables: &CallableShapes) -> Result<Vec<ConstructionTest>, CodegenError> {
        let mut listed = Vec::new();
        for (boundary, listing) in self.env.surface.callable_boundaries_listed_by(callables) {
            let boundary_id = boundary.boundary_id.as_u32();
            let func_id = self.env.callable_boundary_fn_ids.get(&boundary_id).ok_or_else(|| {
                CodegenError::new(format!(
                    "callable identity test names callable boundary {boundary_id}, which was never published",
                ))
            })?;
            let by_captures = match listing {
                Listing::ByCaptures(alternatives) => Some(alternatives),
                Listing::Listed | Listing::Unlisted => None,
            };
            listed.push((*func_id, by_captures));
        }
        Ok(listed
            .into_iter()
            .map(|(func_id, by_captures)| ConstructionTest {
                address: fn_addr(self.body.jmod, func_id, self.body.b),
                by_captures,
            })
            .collect())
    }
}

fn emit_is_empty_list_flag<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    value: CodegenValue,
) -> ir::Value {
    if let CodegenValue::AnyRef(value_ref) = value {
        let tag = body.ref_tag(value_ref);
        let empty_list_v = body.empty_list_ref();
        let is_list = body.b.ins().icmp_imm_s(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
        let is_empty_word = body.b.ins().icmp(IntCC::Equal, value_ref, empty_list_v);
        body.b.ins().band(is_list, is_empty_word)
    } else if let CodegenValue::Stored { word, kind } = value {
        let (is_list, is_empty) = stored_list_flags(body, word, kind);
        body.b.ins().band(is_list, is_empty)
    } else {
        held_outside_a_ref_is_empty_list(body, value)
    }
}

/// Whether a stored pair names a list, and whether the list is the empty one:
/// the empty list is the one list whose payload is the null address.
fn stored_list_flags<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    word: ir::Value,
    kind: ir::Value,
) -> (ir::Value, ir::Value) {
    let is_list = body
        .b
        .ins()
        .icmp_imm_s(IntCC::Equal, kind, ValueKind::LIST.tag() as i64);
    let empty_payload = fz_runtime::any_value::AnyValueRef::empty_list().raw_word()
        & fz_runtime::any_value::AnyValueRefPacking::current().payload_mask();
    let is_empty = body.b.ins().icmp_imm_s(IntCC::Equal, word, empty_payload as i64);
    (is_list, is_empty)
}

/// Whether a value codegen holds outside a ref is the empty list. Such a value
/// names its kind and the only list it can be is the empty one, so the answer
/// is known without making a ref to read it from.
fn held_outside_a_ref_is_empty_list<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    value: CodegenValue,
) -> ir::Value {
    body.value_is_tag(value, ValueKind::LIST)
}

fn emit_is_list_cons_flag<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    value: CodegenValue,
) -> ir::Value {
    if let CodegenValue::AnyRef(value_ref) = value {
        let tag = body.ref_tag(value_ref);
        let empty_list_v = body.empty_list_ref();
        let is_list = body.b.ins().icmp_imm_s(IntCC::Equal, tag, ValueKind::LIST.tag() as i64);
        let is_empty_word = body.b.ins().icmp(IntCC::Equal, value_ref, empty_list_v);
        let not_empty = body.b.ins().icmp_imm_s(IntCC::Equal, is_empty_word, 0);
        body.b.ins().band(is_list, not_empty)
    } else if let CodegenValue::Stored { word, kind } = value {
        let (is_list, is_empty) = stored_list_flags(body, word, kind);
        let not_empty = body.b.ins().icmp_imm_s(IntCC::Equal, is_empty, 0);
        body.b.ins().band(is_list, not_empty)
    } else {
        body.b.ins().iconst(types::I8, 0)
    }
}

/// Negation is PER-LANE. `ineg` on a float's bits is not negation of that
/// float -- it is two's complement applied to an IEEE-754 encoding, which lands
/// nowhere near the answer. For one operand the codegen
/// value's repr IS the lane.
///
/// Before this, `-3.0` reached `as_raw_i64` and aborted with "cannot read raw
/// i64 from non-integer value" on `run` and `build` while `interp` answered
/// `-3.0` (fz-5xp.33). A negative float literal is not an exotic input.
fn lower_neg<M, T>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    x: Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
{
    let repr = var_env.get(&x.0).expect("neg operand").repr();
    if matches!(repr, ArgRepr::RawF64) || ty_is_float(t, value_types, x) {
        let xf = body.as_raw_f64(var_env, x.0);
        return Ok(LowerOut::RawF64(body.b.ins().fneg(xf)));
    }
    if matches!(repr, ArgRepr::RawInt) || ty_is_int(t, value_types, x) {
        let xi = body.as_raw_i64(var_env, x.0);
        return Ok(LowerOut::RawI64(body.b.ins().ineg(xi)));
    }
    // Neither lane is provable, so ask the value at runtime.
    //
    // An expression never gets here -- the front door rewrites `-x` to
    // `Kernel.-/1`, whose typed clauses dispatch (fz-5xp.38). A GUARD
    // does: it is lowered inside the dispatch plan rather than as a call, so
    // `when -x > 0.0` on an operand the plan has not yet narrowed reached
    // `as_raw_i64` and aborted in `fz_unbox_int` (fz-5xp.47).
    let value = *var_env.get(&x.0).expect("neg operand");
    let is_int = body.value_is_tag(value, ValueKind::INT);
    let int_blk = body.b.create_block();
    let float_blk = body.b.create_block();
    let join_blk = body.b.create_block();
    body.b.append_block_param(join_blk, types::I64);
    let no_args: Vec<BlockArg> = Vec::new();
    body.b.ins().brif(is_int, int_blk, &no_args, float_blk, &no_args);

    body.b.switch_to_block(int_blk);
    body.b.seal_block(int_blk);
    let raw_int = body.value_raw_int_for_checked_branch(value);
    let negated_int = body.b.ins().ineg(raw_int);
    let boxed_int = body.box_int_for_any(negated_int);
    body.b.ins().jump(join_blk, &[BlockArg::Value(boxed_int)]);

    body.b.switch_to_block(float_blk);
    body.b.seal_block(float_blk);
    let raw_float = body.value_raw_float(value);
    let negated_float = body.b.ins().fneg(raw_float);
    let boxed_float = body.box_float_for_any(negated_float);
    body.b.ins().jump(join_blk, &[BlockArg::Value(boxed_float)]);

    body.b.switch_to_block(join_blk);
    body.b.seal_block(join_blk);
    Ok(LowerOut::ValueRef(body.b.block_params(join_blk)[0]))
}

/// Same-kind typed fast path for a binop: when the typer proves both
/// operands share the int or float lane, extract their raw values and
/// run the matching op closure, bypassing tagged dispatch. Returns None
/// when neither lane applies (caller falls back to runtime tag tests).
fn try_typed_binop_fast_path<T, F, I, M>(
    body: &mut CodegenFn<'_, '_, M>,
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
/// Float is deliberately excluded: widening equality equates signed zeros,
/// while structural identity distinguishes their bits.
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
/// The OP says which of the two questions is being asked. `Eq`/`Neq` are the
/// `==` operator, which compares numbers by value, so `1 == 1.0` is true.
/// `Identical` is structural identity -- `===`, and what every kind of matching
/// asks -- for which `1` and `1.0` are different values and the
/// value-disjointness fold applies.
///
/// This used to be a `widen_numerics: bool` that each CALL SITE set from what
/// it knew about its caller, which is how a guard came to ask the matching
/// question and answer `same?(1, 1.0)` as `:different` (fz-5xp.24).
fn lower_eq_binop<M, T>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
    op: BinOp,
    a: Var,
    bv: Var,
    dest_var: Var,
) -> Result<LowerOut, CodegenError>
where
    M: cranelift_module::Module,
    T: Types<Ty = Ty>,
{
    let is_eq = matches!(op, BinOp::Eq | BinOp::Identical);
    let widen_numerics = matches!(op, BinOp::Eq | BinOp::Neq);
    let int_cc = if is_eq { IntCC::Equal } else { IntCC::NotEqual };
    let f_cc = if is_eq { FloatCC::Equal } else { FloatCC::NotEqual };

    // fz-5xp.18 — an integer and a float are value-disjoint for MATCHING
    // (Elixir's `case 1.0 do 1 -> ...` does not match, and neither does fz's)
    // but not for `==`, which compares numbers by value: `1 == 1.0` is true.
    // A mixed numeric pair therefore skips the disjointness fold and asks the
    // exact numeric comparator without rounding the integer through f64.
    let a_is_int = ty_is_int(t, value_types, a);
    let b_is_int = ty_is_int(t, value_types, bv);
    let a_is_float = ty_is_float(t, value_types, a);
    let b_is_float = ty_is_float(t, value_types, bv);
    let mixed_numeric = widen_numerics && ((a_is_int && b_is_float) || (a_is_float && b_is_int));
    if mixed_numeric {
        let ordering = emit_mixed_numeric_cmp(body, var_env, a, bv, a_is_int);
        let cmp = body.b.ins().icmp_imm_s(int_cc, ordering, 0);
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(body.b, cmp)));
    }

    // Value-disjointness is a MATCHING question: `1.0` never matches `1`, and
    // `[int]` never matches `[float]`. Under `==` it is not decisive, because
    // widening bridges exactly those pairs -- `[1] == [1.0]` is true. So the
    // operator path skips the fold and lets the comparator decide; only
    // matching, which passes `widen_numerics: false`, still folds.
    if !widen_numerics && descrs_value_disjoint(t, value_types, a, bv) {
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
        // `==` is IEEE, so `0.0 == -0.0` is true. `===` and matching ask
        // identity, where those are different values -- compare the bits.
        let cmp = if widen_numerics {
            body.b.ins().fcmp(f_cc, af, bf)
        } else {
            let ai = body.b.ins().bitcast(types::I64, MemFlagsData::new(), af);
            let bi = body.b.ins().bitcast(types::I64, MemFlagsData::new(), bf);
            body.b.ins().icmp(int_cc, ai, bi)
        };
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
    // Two bitstrings are equal when `Bin` says so, under `==` and `===` alike:
    // the comparison is inline unless the bytes must be read.
    if ty_is_bitstring(t, value_types, a) && ty_is_bitstring(t, value_types, bv) {
        let left = body.tagged_var(var_env, a.0);
        let right = body.tagged_var(var_env, bv.0);
        let which = if is_eq { BinaryCompare::Eq } else { BinaryCompare::Neq };
        let process = body.process_arg();
        let cmp = emit_binary_compare(body, which, &[process, left, right]);
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
    } else if let Some((kind, raw, dyn_var)) = raw_scalar_vs_dynamic(var_env, a, bv)
        .or_else(|| raw_scalar_vs_dynamic(var_env, bv, a))
        // `fz_value_eq_raw_const` is a kind+payload compare, so it answers
        // `launder(1.0) == 1` as false. Under `==` an unboxed INT may still
        // equal a dynamic float, so that pair goes to the widening comparator
        // instead. Atoms have no such partner and keep the fast path.
        .filter(|(kind, _, _)| !(widen_numerics && *kind == ValueKind::INT))
    {
        // One side is an unboxed int/atom and the other's static type isn't
        // known to match: skip boxing the unboxed side into a heap scalar
        // (what `tagged_var` would do below) and instead hand the runtime
        // its raw payload directly, checked against the dynamic side's
        // actual tag.
        let dyn_ref = body.tagged_var(var_env, dyn_var.0);
        let kind_tag = body.b.ins().iconst(types::I32, i64::from(kind.tag()));
        let eq_bool = runtime_condition!(body, fz_value_eq_raw_const, [dyn_ref, kind_tag, raw]);
        let cmp = if is_eq {
            eq_bool
        } else {
            body.b.ins().bxor_imm_u(eq_bool, 1)
        };
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
    } else {
        let [a_word, a_kind] = stored_parts(body, binding_for_var(var_env, a.0));
        let [b_word, b_kind] = stored_parts(body, binding_for_var(var_env, bv.0));
        let process = body.process_arg();
        // The `==` operator widens numerics; structural identity does not. The
        // flag that separates the two static arms has to separate the dynamic
        // one as well, or the widening leaks into pinned matches,
        // `Enum.member?/2` and `--`.
        let eq = if widen_numerics {
            runtime_call1!(
                body,
                fz_value_eq_widening_ref,
                [process, a_word, a_kind, b_word, b_kind]
            )
        } else {
            runtime_call1!(body, fz_value_eq_ref, [process, a_word, a_kind, b_word, b_kind])
        };
        let eq_bool = body.b.ins().icmp_imm_s(IntCC::NotEqual, eq, 0);
        let cmp = if is_eq {
            eq_bool
        } else {
            body.b.ins().bxor_imm_u(eq_bool, 1)
        };
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        Ok(LowerOut::Strict(strict_bool(body.b, cmp)))
    }
}

/// Lower a `Prim::BinOp` ordered comparison (Lt/Le/Gt/Ge). Typed fast
/// paths emit native fcmp/icmp for same-kind lanes and the shared exact
/// comparator for mixed numeric lanes; dynamic values ask the term comparator.
fn lower_cmp_binop<M, T>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    value_types: &HashMap<Var, Ty>,
    var_env: &HashMap<u32, CodegenValue>,
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
    if ty_is_bitstring(t, value_types, a) && ty_is_bitstring(t, value_types, bv) {
        let which = match op {
            BinOp::Lt => BinaryCompare::Lt,
            BinOp::Le => BinaryCompare::Lte,
            BinOp::Gt => BinaryCompare::Gt,
            _ => BinaryCompare::Gte,
        };
        let left = body.tagged_var(var_env, a.0);
        let right = body.tagged_var(var_env, bv.0);
        let process = body.process_arg();
        let cmp = emit_binary_compare(body, which, &[process, left, right]);
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(body.b, cmp)));
    }
    let a_is_int = ty_is_int(t, value_types, a);
    if (a_is_int && ty_is_float(t, value_types, bv))
        || (ty_is_float(t, value_types, a) && ty_is_int(t, value_types, bv))
    {
        let ordering = emit_mixed_numeric_cmp(body, var_env, a, bv, a_is_int);
        let cmp = body.b.ins().icmp_imm_s(icc, ordering, 0);
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(body.b, cmp)));
    }
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
    // One side unboxed and the other dynamic. An integer against a dynamic
    // value asks the dynamic side's kind inline and compares the two integers
    // with one `icmp`; any other kind, or an atom on the raw side, goes to the
    // runtime with the unboxed side's kind and payload, so no heap scalar is
    // boxed just to form an `AnyValueRef`.
    // `raw_scalar_vs_dynamic(x, y)` succeeds when `x` is the unboxed side, so
    // the first arm has the unboxed operand on the LEFT (swap = 1) and the
    // second has it on the right (swap = 0).
    if let Some((kind, raw, dyn_var, swap)) = raw_scalar_vs_dynamic(var_env, a, bv)
        .map(|(k, r, d)| (k, r, d, 1u32))
        .or_else(|| raw_scalar_vs_dynamic(var_env, bv, a).map(|(k, r, d)| (k, r, d, 0u32)))
    {
        let dyn_value = *var_env.get(&dyn_var.0).expect("cmp dynamic operand");
        let ordered_slow = |body: &mut CodegenFn<'_, '_, M>| {
            let dyn_ref = body.tagged_var(var_env, dyn_var.0);
            let kind_tag = body.b.ins().iconst(types::I32, i64::from(kind.tag()));
            let swap_flag = body.b.ins().iconst(types::I32, i64::from(swap));
            let process = body.process_arg();
            let ordering = runtime_call1!(
                body,
                fz_value_cmp_raw_const,
                [process, dyn_ref, kind_tag, raw, swap_flag]
            );
            let zero = body.b.ins().iconst(types::I64, 0);
            body.b.ins().icmp(icc, ordering, zero)
        };
        let cmp = if kind == ValueKind::INT {
            let is_int = body.value_is_tag(dyn_value, ValueKind::INT);
            let fast_blk = body.b.create_block();
            let slow_blk = body.b.create_block();
            let join_blk = body.b.create_block();
            body.b.append_block_param(join_blk, types::I8);
            let no_args: Vec<BlockArg> = Vec::new();
            body.b.ins().brif(is_int, fast_blk, &no_args, slow_blk, &no_args);

            body.b.switch_to_block(fast_blk);
            body.b.seal_block(fast_blk);
            let dyn_int = body.value_raw_int_for_checked_branch(dyn_value);
            let (left, right) = if swap == 1 { (raw, dyn_int) } else { (dyn_int, raw) };
            let fast = body.b.ins().icmp(icc, left, right);
            body.b.ins().jump(join_blk, &[BlockArg::Value(fast)]);

            body.b.switch_to_block(slow_blk);
            body.b.seal_block(slow_blk);
            let slow = ordered_slow(body);
            body.b.ins().jump(join_blk, &[BlockArg::Value(slow)]);

            body.b.switch_to_block(join_blk);
            body.b.seal_block(join_blk);
            body.b.block_params(join_blk)[0]
        } else {
            ordered_slow(body)
        };
        if body.cache.if_only_conds.contains(&dest_var.0) {
            return Ok(LowerOut::Condition(cmp));
        }
        return Ok(LowerOut::Strict(strict_bool(body.b, cmp)));
    }

    // Neither side is unboxed, so each carries its own kind. Two integers are
    // the common case, and comparing them must not box either operand, which
    // keeps a guard like `h < p` at zero scalar boxes: both kinds are tested
    // inline and the integers compared with one `icmp`.
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

    // Anything else asks `fz_value_cmp_ref`, the one dynamic ordering, shared
    // with the interpreter and with the `bb` intrinsic. Ordering is answered
    // in one place so that a mixed pair like `2 >= 1.0` cannot get one answer
    // here and another under the interpreter.
    body.b.switch_to_block(slow_blk);
    body.b.seal_block(slow_blk);
    let [left_word, left_kind] = stored_parts(body, binding_for_var(var_env, a.0));
    let [right_word, right_kind] = stored_parts(body, binding_for_var(var_env, bv.0));
    let process = body.process_arg();
    let ordering = runtime_call1!(
        body,
        fz_value_cmp_ref,
        [process, left_word, left_kind, right_word, right_kind]
    );
    let zero = body.b.ins().iconst(types::I64, 0);
    let slow_cmp = body.b.ins().icmp(icc, ordering, zero);
    body.b.ins().jump(join_blk, &[BlockArg::Value(slow_cmp)]);

    body.b.switch_to_block(join_blk);
    body.b.seal_block(join_blk);
    let result = body.b.block_params(join_blk)[0];
    Ok(LowerOut::Strict(strict_bool(body.b, result)))
}

/// Lower a `Prim::BinOp` short-circuit-free boolean op (And/Or).
/// Both operands are booleans -- the language-level operators halt on
/// anything else before one is made -- so they combine with `band`/`bor`.
fn lower_bool_binop<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
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

fn emit_mixed_numeric_cmp<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    left: Var,
    right: Var,
    left_is_int: bool,
) -> ir::Value {
    let (integer, float) = if left_is_int {
        (body.as_raw_i64(var_env, left.0), body.as_raw_f64(var_env, right.0))
    } else {
        (body.as_raw_i64(var_env, right.0), body.as_raw_f64(var_env, left.0))
    };
    let ordering = runtime_call1!(body, fz_int_float_cmp, [integer, float]);
    if left_is_int {
        ordering
    } else {
        body.b.ins().ineg(ordering)
    }
}

/// Generic extern fallback: marshals each arg per its declared `ExternTy`,
/// looks up (or caches) the FuncRef, and packages the return as
/// RawI64 / RawF64 / ValueRef / nil / DeadUnit per the decl shape.
fn lower_extern_generic<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    decl: &ExternDecl,
    eid: &ExternId,
    args: &[ExternArg],
    dest_var: Var,
) -> Result<LowerOut, CodegenError> {
    // An `extern "fz"` helper receives the current process as an implicit
    // first argument. Declaring it means a new allocating primitive is a
    // declaration plus a Rust function, not another rung in a name-keyed chain
    // here and two more in the interpreter.
    let takes_process = decl.abi.takes_process();
    let mut param_tys: Vec<ir::Type> = Vec::with_capacity(decl.params.len() + 1);
    if takes_process {
        param_tys.push(types::I64);
    }
    // A parameter that carries no value has no lane; `marshal_extern_arg`
    // refuses one, so the word it would occupy here is never reached.
    param_tys.extend(decl.params.iter().flat_map(|t| t.param_lanes()));
    let ret = decl.ret.scalar_ty().ok_or_else(|| {
        CodegenError::new(format!(
            "extern `{}` aggregate result reached scalar Prim::Extern lowering",
            decl.symbol
        ))
    })?;
    let ret_lane = ret.lane();
    let returns_value = ret_lane.is_some();
    let param_kinds = &decl.params;
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
    let process_arg = takes_process.then(|| body.process_arg());
    let mut arg_vals: Vec<ir::Value> = Vec::with_capacity(param_tys.len());
    for (arg, ty) in args.iter().zip(param_kinds.iter().copied()) {
        if ty == ExternTy::StoredValue {
            arg_vals.extend(stored_parts(body, binding_for_var(var_env, arg.var.0)));
        } else {
            arg_vals.push(marshal_extern_arg(body, var_env, arg.var, ty, takes_process)?);
        }
    }
    let row_args: Vec<ir::Value> = process_arg.into_iter().chain(arg_vals.iter().copied()).collect();
    if let Some(out) = inline_scalar_extern(body, decl, ret, &row_args, dest_var)? {
        return Ok(out);
    }
    let mut sig = body.jmod.make_signature();
    sig.params.extend(param_tys.iter().copied().map(ir::AbiParam::new));
    sig.returns.extend(ret_lane.map(ir::AbiParam::new));
    let fref = extern_call_ref(body, *eid, &decl.symbol, &sig)?;
    let call_args: Vec<ir::Value> = match process_arg {
        Some(process) => std::iter::once(process).chain(arg_vals).collect(),
        None => arg_vals,
    };
    let inst = body.b.ins().call(fref, &call_args);
    if ret == ExternTy::Never {
        continue_after_raise(body);
    }
    if returns_value {
        let raw = body.b.inst_results(inst)[0];
        // The declared RETURN says what came back, and each wire type has its
        // own lane. `F64` used to fall into the `ValueRef` arm, which told
        // everything downstream that a raw f64 was a tagged value ref: the
        // consumer then unboxed it, and the result was an unbox helper applied
        // to an f64 that failed Cranelift verification.
        return Ok(match ret {
            ExternTy::I64 => LowerOut::RawI64(raw),
            ExternTy::Opaque(kind) => LowerOut::ValueRef(box_extern_opaque_word(body, raw, kind)),
            // A C `int` result fills only the low half of the return
            // register, so the fz integer is its sign extension. Reading the
            // whole register instead is what turned `open`'s -1 into
            // 4294967295 on a platform whose libc leaves the upper half zero.
            ExternTy::I32 => LowerOut::RawI64(body.b.ins().sextend(types::I64, raw)),
            ExternTy::Bool => LowerOut::Strict(decode_foreign_boolean_word(
                body,
                raw,
                body.cache.if_only_conds.contains(&dest_var.0),
            )),
            ExternTy::F64 => LowerOut::RawF64(raw),
            ExternTy::Any | ExternTy::Binary | ExternTy::CString => LowerOut::ValueRef(raw),
            // Spelled out rather than defaulted: the defect above WAS a wire
            // type falling into the `ValueRef` arm because nobody had listed
            // it. A wildcard here would silently do it again to the next
            // variant added; `returns_value` already excluded these two.
            ExternTy::Unit | ExternTy::Never => unreachable!("a non-returning extern took the returns_value path"),
            ExternTy::BinaryCursor | ExternTy::StoredValue => {
                unreachable!("`binary_cursor` and `stored_value` stand only as parameters")
            }
        });
    }
    if body.cache.used_vars.contains(&dest_var.0) {
        return Ok(LowerOut::Strict(strict_const_value(body.b, AnyValue::nil_atom())));
    }
    Ok(LowerOut::DeadUnit)
}

/// The scalar extern `decl` computed in place by its recipe, when the table
/// has a row for its symbol. The row's answer must be the lane the declaration
/// returns: a disagreement is an error, not a conversion.
fn inline_scalar_extern<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    decl: &ExternDecl,
    ret: ExternTy,
    args: &[ir::Value],
    dest_var: Var,
) -> Result<Option<LowerOut>, CodegenError> {
    let Some(emitted) = emit_in_body(body, &decl.symbol, args) else {
        return Ok(None);
    };
    let disagreement = |what: &str| {
        CodegenError::new(format!(
            "recipe for extern `{}` answers {what}, but the declaration returns {ret:?}",
            decl.symbol
        ))
    };
    Ok(Some(match (emitted, ret) {
        (Emitted::Value(value), ExternTy::I64) if body.b.func.dfg.value_type(value) == types::I64 => {
            LowerOut::RawI64(value)
        }
        (Emitted::Value(value), ExternTy::F64) if body.b.func.dfg.value_type(value) == types::F64 => {
            LowerOut::RawF64(value)
        }
        (Emitted::Condition(condition), ExternTy::Bool) => LowerOut::Strict(condition_value(
            body.b,
            condition,
            body.cache.if_only_conds.contains(&dest_var.0),
        )),
        (Emitted::Value(_), _) => return Err(disagreement("a value of another lane")),
        (Emitted::Condition(_), _) => return Err(disagreement("a condition")),
        (Emitted::Checked { .. }, _) => return Err(disagreement("a checked pair")),
    }))
}

/// What follows a call that cannot return: the callee raised. `fz_panic` either
/// delivered the raise to a handler or failed the process, and in both cases
/// this frame returns, as a yield does, so every frame above it unwinds to
/// the quantum entry, which resumes the delivered handler or ends the process.
/// A process that neither failed nor has a delivered handler was ended by an
/// extern that broke its `none` contract, which traps. Code after the call is
/// unreachable and lands in a block nothing enters.
pub(super) fn continue_after_raise<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>) {
    let unwinds = process_is_unwinding(body);
    body.b.ins().trapz(unwinds, TrapCode::user(1).unwrap());
    return_unwinding(body);
    let after = body.b.create_block();
    body.b.switch_to_block(after);
    body.b.seal_block(after);
}

/// Nonzero when the process raised: it failed, or a handler was delivered. The
/// pinned register is read again here, not taken from the block's cached copy,
/// so that no value is held across the call that raised, which would take a
/// callee-saved register that every caller of this function then saves.
fn process_is_unwinding<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>) -> ir::Value {
    let process = body.b.ins().get_pinned_reg(types::I64);
    body.b
        .ins()
        .uload8(types::I64, MemFlagsData::trusted(), process, PROCESS_UNWINDING_OFFSET)
}

/// Returns from this function with the lanes its signature declares, each
/// zero: a continuation function returns 0 to its caller, which is the quantum
/// entry; a machine function returns zeros to a caller that checks for the
/// raise before it reads them.
fn return_unwinding<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>) {
    let lanes = body
        .b
        .func
        .signature
        .returns
        .iter()
        .map(|lane| lane.value_type)
        .collect::<Vec<_>>();
    let zeros = lanes
        .into_iter()
        .map(|lane| match lane {
            types::F64 => body.b.ins().f64const(0.0),
            lane => body.b.ins().iconst(lane, 0),
        })
        .collect::<Vec<_>>();
    body.b.ins().return_(&zeros);
}

/// Calls machine function `callee` on `args` and answers the lanes it
/// returns. A raise in the callee returns from this function too, before the
/// lanes are read, and control goes on in the block where the callee returned
/// normally.
pub(super) fn lower_machine_call<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    callee: FnId,
    args: &[Var],
) -> Vec<CodegenValue> {
    let callee_fid = *env.fn_ids.get(&callee.0).expect("machine callee fn_id missing");
    let callee_fref = body.jmod.declare_func_in_func(callee_fid, body.b.func);
    let call_args = body.coerce_call_args(args, &env.param_reprs[callee.0 as usize], var_env);
    let call = body.b.ins().call(callee_fref, &call_args);
    let lanes = body.b.inst_results(call).to_vec();
    if env.raising_machines.contains(&callee) {
        return_if_raised(body);
    }
    let mut cursor = 0;
    env.body_return_reprs(callee.0)
        .into_iter()
        .map(|repr| take_param_binding(&lanes, &mut cursor, repr))
        .collect()
}

fn return_if_raised<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>) {
    let unwinds = process_is_unwinding(body);
    let raised = body.b.create_block();
    let returned = body.b.create_block();
    body.b.ins().brif(unwinds, raised, &[], returned, &[]);
    body.b.switch_to_block(raised);
    body.b.seal_block(raised);
    body.b.set_cold_block(raised);
    return_unwinding(body);
    body.b.switch_to_block(returned);
    body.b.seal_block(returned);
}

/// The values a pair-returning extern binds to `vars`. A boolean field whose
/// variable is only ever branched on is a raw condition.
pub(crate) fn lower_extern_pair<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    decl: &ExternDecl,
    eid: &ExternId,
    args: &[ExternArg],
    vars: &[Var],
) -> Result<Vec<CodegenValue>, CodegenError> {
    let Some(fields) = decl.ret.pair_fields() else {
        return Err(CodegenError::new(format!(
            "extern `{}` reached pair lowering with scalar result {:?}",
            decl.symbol, decl.ret
        )));
    };
    if vars.len() != fields.len() {
        return Err(CodegenError::new(format!(
            "extern `{}` produces {} result lanes for {} bindings",
            decl.symbol,
            fields.len(),
            vars.len()
        )));
    }
    if decl.abi != crate::fz_ir::ExternAbi::C || decl.variadic {
        return Err(CodegenError::new(format!(
            "extern `{}` pair results require one fixed `C` declaration",
            decl.symbol
        )));
    }
    if args.len() != decl.params.len() {
        return Err(CodegenError::new(format!(
            "extern `{}` codegen: arg count {} != param count {}",
            decl.symbol,
            args.len(),
            decl.params.len()
        )));
    }
    let branch_only = [0, 1].map(|field| body.cache.if_only_conds.contains(&vars[field].0));
    let call_args = args
        .iter()
        .zip(decl.params.iter().copied())
        .map(|(arg, ty)| marshal_extern_arg(body, var_env, arg.var, ty, false))
        .collect::<Result<Vec<_>, _>>()?;
    if let Some(inline) = inline_checked_extern(body, decl, fields, &call_args, branch_only)? {
        return Ok(inline);
    }
    let mut sig = body.jmod.make_signature();
    sig.params.extend(
        decl.params
            .iter()
            .map(|ty| ir::AbiParam::new(ty.lane().unwrap_or(types::I64))),
    );
    let physical = c_pair_return_types(body.jmod.isa().triple(), fields)?;
    sig.returns.extend(physical.iter().copied().map(ir::AbiParam::new));
    let fref = extern_call_ref(body, *eid, &decl.symbol, &sig)?;
    let call = body.b.ins().call(fref, &call_args);
    let results = body.b.inst_results(call).to_vec();
    results
        .into_iter()
        .zip(physical)
        .zip(fields)
        .zip(branch_only)
        .map(|(((value, physical), semantic), branch_only)| {
            decode_pair_result(body, value, physical, semantic, branch_only)
        })
        .collect()
}

/// The pair a checked extern's recipe computes in place, when the table has a
/// row for its symbol: the value in the declared first field's lane, and the
/// failure condition in the boolean second field.
fn inline_checked_extern<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    decl: &ExternDecl,
    fields: [ExternTy; 2],
    args: &[ir::Value],
    branch_only: [bool; 2],
) -> Result<Option<Vec<CodegenValue>>, CodegenError> {
    let Some(emitted) = emit_inline(body.b, &decl.symbol, args) else {
        return Ok(None);
    };
    let Emitted::Checked { value, failed } = emitted else {
        return Err(CodegenError::new(format!(
            "recipe for extern `{}` answers {emitted:?}, but the declaration returns a pair",
            decl.symbol
        )));
    };
    let first = match (fields, body.b.func.dfg.value_type(value)) {
        ([ExternTy::I64, ExternTy::Bool], types::I64) => CodegenValue::RawInt(value),
        ([ExternTy::F64, ExternTy::Bool], types::F64) => CodegenValue::RawF64(value),
        _ => {
            return Err(CodegenError::new(format!(
                "recipe for extern `{}` answers a checked {} value, but the declaration returns {fields:?}",
                decl.symbol,
                body.b.func.dfg.value_type(value)
            )));
        }
    };
    let failed = condition_value(body.b, failed, branch_only[1]);
    Ok(Some(vec![first, failed]))
}

pub(super) fn c_pair_return_types(triple: &Triple, fields: [ExternTy; 2]) -> Result<[ir::Type; 2], CodegenError> {
    // A pair field rides a whole return register. The shared front end builds
    // a pair only out of the three wire types that do, and naming them here
    // keeps a narrower lane from being mapped into one of those registers.
    if let Some(field) = fields
        .iter()
        .find(|field| !matches!(field, ExternTy::I64 | ExternTy::F64 | ExternTy::Bool))
    {
        return Err(CodegenError::new(format!(
            "{field:?} is not a scalar C pair field; a pair field is integer, float, or boolean"
        )));
    }
    let natural = |field: ExternTy| field.lane().unwrap_or(types::I64);
    match triple.architecture {
        Architecture::X86_64 | Architecture::X86_64h
            if matches!(
                triple.operating_system,
                OperatingSystem::Linux | OperatingSystem::Darwin(_)
            ) =>
        {
            Ok(fields.map(natural))
        }
        Architecture::Aarch64(_)
            if matches!(
                triple.operating_system,
                OperatingSystem::Linux | OperatingSystem::Darwin(_)
            ) =>
        {
            if fields == [ExternTy::F64, ExternTy::F64] {
                Ok([types::F64, types::F64])
            } else {
                Ok([types::I64, types::I64])
            }
        }
        Architecture::X86_64 | Architecture::X86_64h | Architecture::Aarch64(_) => Err(CodegenError::new(format!(
            "C scalar-pair returns are unsupported on target {triple}; only Linux and Darwin x86_64 SysV or AArch64 are verified"
        ))),
        ref architecture => Err(CodegenError::new(format!(
            "C scalar-pair returns are unsupported on target architecture {architecture}"
        ))),
    }
}

fn decode_pair_result<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    value: ir::Value,
    physical: ir::Type,
    semantic: ExternTy,
    branch_only: bool,
) -> Result<CodegenValue, CodegenError> {
    Ok(match semantic {
        ExternTy::I64 => CodegenValue::RawInt(value),
        ExternTy::F64 if physical == types::F64 => CodegenValue::RawF64(value),
        ExternTy::F64 => CodegenValue::RawF64(body.b.ins().bitcast(types::F64, MemFlagsData::new(), value)),
        ExternTy::Bool => decode_foreign_boolean_word(body, value, branch_only),
        other => {
            return Err(CodegenError::new(format!("{other:?} is not a scalar C pair field")));
        }
    })
}

/// A C boolean word, which is zero or not, as the binding its variable's
/// consumers read.
fn decode_foreign_boolean_word<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    word: ir::Value,
    branch_only: bool,
) -> CodegenValue {
    let condition = body.b.ins().icmp_imm_s(IntCC::NotEqual, word, 0);
    condition_value(body.b, condition, branch_only)
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
/// references the planned callable-boundary static closure directly instead of
/// routing through closure allocation.
fn struct_schema_id(env: &CodegenEnv<'_>, module: &fz_runtime::module_name::ModuleName) -> Result<u32, CodegenError> {
    env.named_schema_ids
        .get(module)
        .copied()
        .ok_or_else(|| CodegenError::new(format!("struct schema `{module}` is not registered for codegen")))
}

/// What a slot read answers: the raw word of a slot whose kind the types
/// name, or a reference to whatever the slot holds.
#[derive(Clone, Copy)]
enum SlotRead {
    Float,
    Int,
    Atom,
    Reference,
}

/// Read field `field` of `base`, a map the types say is a `module` struct.
/// The types do not say how it is laid out. In the struct layout the field
/// is loaded from `slot`; a struct that has grown a key, or was built as a
/// map, is in the entries layout and the field is found by name.
#[allow(clippy::too_many_arguments)]
fn lower_struct_slot<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    base: Var,
    module: &fz_runtime::module_name::ModuleName,
    slot: u32,
    field: &str,
    read: SlotRead,
) -> Result<LowerOut, CodegenError> {
    let schema_id = struct_schema_id(env, module)?;
    let field_atom = env
        .module
        .atoms
        .id_of(field)
        .ok_or_else(|| CodegenError::new(format!("field atom `{field}` not interned")))?;
    let base_ref = body.tagged_var(var_env, base.0);
    let lane = match read {
        SlotRead::Float => types::F64,
        SlotRead::Int | SlotRead::Atom | SlotRead::Reference => types::I64,
    };
    let slot_blk = body.b.create_block();
    let named_blk = body.b.create_block();
    let join_blk = body.b.create_block();
    body.b.append_block_param(join_blk, lane);
    let no_args: Vec<BlockArg> = Vec::new();
    let in_struct_layout = body.has_struct_layout(base_ref, schema_id);
    body.b
        .ins()
        .brif(in_struct_layout, slot_blk, &no_args, named_blk, &no_args);

    body.b.switch_to_block(slot_blk);
    body.b.seal_block(slot_blk);
    let from_slot = match read {
        SlotRead::Float | SlotRead::Int | SlotRead::Atom => body.load_slot(base_ref, slot, lane),
        SlotRead::Reference => {
            let field_offset = body.b.ins().iconst(types::I32, slot as i64 * SLOT_BYTES as i64);
            let process = body.process_arg();
            runtime_call1!(body, fz_struct_get_field_ref, [process, base_ref, field_offset])
        }
    };
    body.b.ins().jump(join_blk, &[BlockArg::Value(from_slot)]);

    body.b.switch_to_block(named_blk);
    body.b.seal_block(named_blk);
    body.b.set_cold_block(named_blk);
    let atom = body.b.ins().iconst(types::I64, field_atom as i64);
    let process = body.process_arg();
    let found = runtime_call1!(body, fz_struct_get_named_field_ref, [process, base_ref, atom]);
    let by_name = match read {
        SlotRead::Float => runtime_call1!(body, fz_ref_load_float, [found]),
        SlotRead::Int => runtime_call1!(body, fz_ref_load_int, [found]),
        SlotRead::Atom => runtime_call1!(body, fz_ref_load_atom, [found]),
        SlotRead::Reference => found,
    };
    body.b.ins().jump(join_blk, &[BlockArg::Value(by_name)]);

    body.b.switch_to_block(join_blk);
    body.b.seal_block(join_blk);
    let value = body.b.block_params(join_blk)[0];
    Ok(match read {
        SlotRead::Float => LowerOut::RawF64(value),
        SlotRead::Int => LowerOut::RawI64(value),
        SlotRead::Atom => LowerOut::Strict(CodegenValue::RawAtom(value)),
        SlotRead::Reference => LowerOut::ValueRefWord(value),
    })
}

pub(crate) fn lower_make_fn_ref<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    env: &CodegenEnv<'_>,
    fn_id: FnId,
) -> Result<LowerOut, CodegenError> {
    let cl_sid = settled_callable_boundary_id(env, fn_id)?;
    Ok(LowerOut::Strict(CodegenValue::known(
        static_closure_ref(body, env, cl_sid)?,
        ValueKind::CLOSURE,
    )))
}

/// Lower a `Prim::MakeClosure`. Env-carrying closures allocate a closure
/// object, store the callable-boundary code pointer, then write captures through
/// the runtime's schema-backed accessor.
pub(crate) fn lower_make_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
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

/// Non-zero captures: place the closure heap object, write its header and
/// body's func_addr, and store captures as env fields. The body has
/// closure-target sig `(args..., self, cont) tail` and projects
/// captures from `self` in its entry harness.
fn emit_capturing_closure<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
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
    let cl_ptr = body.alloc_closure(boundary.denotation, arity_v, nc_v, hk_v, body_addr);
    for (i, cv) in captured.iter().enumerate() {
        let repr = boundary.capture_reprs[i];
        if matches!(repr, ArgRepr::ValueRef | ArgRepr::Stored) {
            body.store_closure_capture_value(cl_ptr, i, binding_for_var(var_env, cv.0));
            continue;
        }
        match closure_capture_for_var_as(body, var_env, cv.0, repr) {
            ClosureCapture::RefWord(_) | ClosureCapture::Stored { .. } => {
                unreachable!("a raw-lane capture is neither a reference word nor a stored pair")
            }
            ClosureCapture::RawInt(value) => body.store_closure_capture_i64(cl_ptr, i, value),
            ClosureCapture::RawF64(value) => body.store_closure_capture_f64(cl_ptr, i, value),
            ClosureCapture::RawAtom(value) => body.store_closure_capture_atom(cl_ptr, i, value),
        }
    }
    Ok(cl_ptr)
}

#[cfg(test)]
#[path = "prim_test.rs"]
mod prim_test;
