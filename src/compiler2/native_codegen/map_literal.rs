//! A map literal in compiled code.
//!
//! The entries of a literal that are in key order with no key repeated
//! (`Prim::MakeMap { in_key_order: true }`) are built in the cheapest form
//! they allow:
//!
//! - Read-only program data, when every key and value is an immediate or
//!   another read-only object. The map is emitted once, with the bytes the
//!   runtime's builder writes, and a use is its address. Nothing allocates and
//!   nothing writes it: no code writes into a published map, and the collector
//!   and deep copy pass a literal by pointer. A static map holds only
//!   immediates and read-only objects, because the collector neither moves nor
//!   traces it, so a heap reference in one would never be updated.
//! - One inline allocation, when every key is a literal atom or other
//!   immediate and the values are run-time values. The tag bytes, key words
//!   and value words are stored in place. The allocation never collects, so
//!   the values stay where they are until the last store, and a heap value is
//!   marked shared as the runtime marks the values it puts.
//! - The runtime's destination protocol otherwise: begin, one put per entry,
//!   then publish.
//!
//! Entries not in key order are sorted by the runtime when it freezes the
//! destination.

use super::prim::{emit_map_destination_put, static_literal_field_for_var, static_object_literal, static_object_name};
use super::recipe::constant_of;
use super::type_pred::addressed_object_share;
use super::*;
use crate::fast_hash::HashMap;
use crate::fz_ir::Var;
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use fz_runtime::any_value::{
    AnyValue, MAP_FLAT_MAX, ValueKind, map_header_word, map_keys_offset, map_pack_tag, map_size_for_count,
    map_tag_bytes_len, map_values_offset,
};
use fz_runtime::ir_runtime::{fz_map_dest_begin, fz_map_dest_freeze, fz_map_dest_publish};

/// A flat map's read-only image: its bytes, and the offset of each word that
/// holds the address of another read-only object.
pub(super) struct StaticMapImage {
    pub(super) bytes: Vec<u8>,
    pub(super) addresses: Vec<(usize, StaticAddress)>,
}

/// The image of the flat map of `entries`, which are in key order with no key
/// repeated. The runtime's own functions place every word. The bytes after the
/// last value are the object's alignment pad, which no writer stores and
/// nothing reads.
pub(super) fn static_map_image(
    entries: &[(StaticLiteralField, StaticLiteralField)],
) -> Result<StaticMapImage, CodegenError> {
    let count = entries.len();
    if count > MAP_FLAT_MAX {
        return Err(CodegenError::new(format!(
            "a read-only map is flat, which holds at most {MAP_FLAT_MAX} entries, not {count}"
        )));
    }
    let mut image = StaticMapImage {
        bytes: vec![0u8; map_size_for_count(count)],
        addresses: Vec::new(),
    };
    image.bytes[0..8].copy_from_slice(&map_header_word(count).to_le_bytes());
    for (index, (key, value)) in entries.iter().enumerate() {
        let key_kind = image.store(*key, map_keys_offset(count) + 8 * index)?;
        let value_kind = image.store(*value, map_values_offset(count) + 8 * index)?;
        image.bytes[8 + index] = map_pack_tag(key_kind, value_kind);
    }
    Ok(image)
}

impl StaticMapImage {
    /// Write `field` as the word at `offset` and answer its kind. An
    /// immediate is its raw word; an object is the address the linker fills in.
    fn store(&mut self, field: StaticLiteralField, offset: usize) -> Result<ValueKind, CodegenError> {
        match field {
            StaticLiteralField::Scalar(AnyValue::HeapRef(_) | AnyValue::Null) => Err(CodegenError::new(
                "a read-only map holds immediates and read-only objects, never a heap reference",
            )),
            StaticLiteralField::Scalar(value) => {
                self.bytes[offset..offset + 8].copy_from_slice(&value.raw().to_le_bytes());
                Ok(value.kind())
            }
            StaticLiteralField::Object(object) => {
                self.addresses.push((offset, StaticAddress::Data(object.data_id)));
                Ok(object.kind)
            }
        }
    }
}

/// `Prim::MakeMap`: the value of the published map of `entries`.
pub(super) fn lower_make_map<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    dest_var: Var,
    entries: &[(Var, Var)],
    in_key_order: bool,
) -> Result<LowerOut, CodegenError> {
    if !body.cache.live_vars.contains(&dest_var.0) {
        // Nothing reads the map: a build is no effect, so it is not made.
        return Ok(LowerOut::Strict(strict_const_value(body.b, AnyValue::nil_atom())));
    }
    if in_key_order && let Some(fields) = static_entries(body.cache, var_env, entries) {
        let image = static_map_image(&fields)?;
        let name = static_object_name(body, env, "map", dest_var);
        let data_id = define_read_only_object(body.jmod, &name, image.bytes, &image.addresses)?;
        return Ok(LowerOut::Strict(static_object_literal(
            body,
            dest_var,
            data_id,
            ValueKind::MAP,
        )));
    }
    if in_key_order && let Some(keys) = immediate_keys(body.cache, var_env, entries) {
        return Ok(LowerOut::ValueRef(emit_inline_map(
            body, t, env, var_env, entries, &keys,
        )));
    }
    Ok(LowerOut::ValueRef(emit_destination_map(
        body,
        var_env,
        entries,
        in_key_order,
    )))
}

/// Every entry as read-only slots, when every key and value is one and the
/// map is flat.
fn static_entries(
    cache: &CodegenCache,
    var_env: &HashMap<u32, CodegenValue>,
    entries: &[(Var, Var)],
) -> Option<Vec<(StaticLiteralField, StaticLiteralField)>> {
    if entries.len() > MAP_FLAT_MAX {
        return None;
    }
    entries
        .iter()
        .map(|(key, value)| {
            Some((
                static_literal_field_for_var(cache, var_env, *key)?,
                static_literal_field_for_var(cache, var_env, *value)?,
            ))
        })
        .collect()
}

/// The key of every entry as an immediate, when each is one and the map is
/// flat.
fn immediate_keys(
    cache: &CodegenCache,
    var_env: &HashMap<u32, CodegenValue>,
    entries: &[(Var, Var)],
) -> Option<Vec<AnyValue>> {
    if entries.len() > MAP_FLAT_MAX {
        return None;
    }
    entries
        .iter()
        .map(|(key, _)| match static_literal_field_for_var(cache, var_env, *key)? {
            StaticLiteralField::Scalar(key @ (AnyValue::Atom(_) | AnyValue::Int(_))) => Some(key),
            _ => None,
        })
        .collect()
}

/// A flat map placed in one allocation: the tag bytes a word at a time, the
/// key words as constants and each value as its stored form. A tag byte is a
/// constant when the value's kind is known while compiling.
fn emit_inline_map<M: cranelift_module::Module, T: Types<Ty = Ty>>(
    body: &mut CodegenFn<'_, '_, M>,
    t: &mut T,
    env: &CodegenEnv<'_>,
    var_env: &HashMap<u32, CodegenValue>,
    entries: &[(Var, Var)],
    keys: &[AnyValue],
) -> ir::Value {
    let count = entries.len();
    let map = body.alloc_flat_map(count);
    let flags = MemFlagsData::trusted();
    let mut tags = vec![(0u64, Vec::<(usize, ir::Value)>::new()); map_tag_bytes_len(count) / 8];
    for (index, ((_, value), key_word)) in entries.iter().zip(keys).enumerate() {
        let addressed = addressed_object_share(t, env.active_value_types(), *value);
        let (word, kind) = body.stored_entry(binding_for_var(var_env, value.0), addressed);
        let key_tag = u64::from(key_word.kind().tag()) << 4;
        let (constant_tags, dynamic_kinds) = &mut tags[index / 8];
        match constant_of(body.b, kind) {
            Some(known) => *constant_tags |= (key_tag | known as u64) << (8 * (index % 8)),
            None => {
                *constant_tags |= key_tag << (8 * (index % 8));
                dynamic_kinds.push((index % 8, kind));
            }
        }
        let key_word = body.b.ins().iconst(types::I64, key_word.raw() as i64);
        body.b.ins().store(
            flags,
            key_word,
            map.address,
            (map_keys_offset(count) + 8 * index) as i32,
        );
        body.b
            .ins()
            .store(flags, word, map.address, (map_values_offset(count) + 8 * index) as i32);
    }
    for (word_index, (constant_tags, dynamic_kinds)) in tags.into_iter().enumerate() {
        let mut tag_word = body.b.ins().iconst(types::I64, constant_tags as i64);
        for (lane, kind) in dynamic_kinds {
            let kind = body.b.ins().uextend(types::I64, kind);
            let placed = body.b.ins().ishl_imm_u(kind, 8 * lane as i64);
            tag_word = body.b.ins().bor(tag_word, placed);
        }
        body.b
            .ins()
            .store(flags, tag_word, map.address, (8 + 8 * word_index) as i32);
    }
    map.reference
}

/// The map built by the runtime's destination protocol: an entry put at a
/// time, then published as it stands when it is in key order and sorted
/// otherwise.
fn emit_destination_map<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    var_env: &HashMap<u32, CodegenValue>,
    entries: &[(Var, Var)],
    in_key_order: bool,
) -> ir::Value {
    let process = body.process_arg();
    let capacity = body.b.ins().iconst(types::I32, entries.len() as i64);
    let mut map = runtime_call1!(body, fz_map_dest_begin, [process, capacity]);
    for (key, value) in entries {
        let (key, value) = (binding_for_var(var_env, key.0), binding_for_var(var_env, value.0));
        map = emit_map_destination_put(body, map, key, value);
    }
    let process = body.process_arg();
    if in_key_order {
        runtime_call1!(body, fz_map_dest_publish, [process, map])
    } else {
        runtime_call1!(body, fz_map_dest_freeze, [process, map])
    }
}

#[cfg(test)]
#[path = "map_literal_test.rs"]
mod map_literal_test;
