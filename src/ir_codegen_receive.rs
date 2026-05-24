//! fz-70q (B3) — selective-receive matcher fn codegen.
//!
//! Emits the leaf matcher fn for a `Term::ReceiveMatched`. The matcher
//! ABI matches `fz_runtime::park::MatcherFn` (see runtime/src/park.rs):
//!
//! ```text
//! extern "C" fn(msg_value: u64, msg_kind: u8, pinned: *const ValueRoot, out: *mut ValueRoot) -> u32
//! ```
//!
//! - `msg_value` / `msg_kind`: side-tagged candidate message.
//! - `pinned`: pointer to `ValueRoot` entries, in the order
//!   they appear in `Term::ReceiveMatched::pinned`.
//! - `out`: caller-supplied `[ValueRoot; bound_arity]`
//!   scratch buffer; the matcher writes the winning clause's bound-var
//!   values here.
//! - returns `0` on miss; `k > 0` is the 1-based clause index (caller
//!   indexes `clause_bodies[k-1]`).
//!
//! Production codegen consumes the cached AST-free `Matcher` attached to
//! `Term::ReceiveMatched`; it does not rebuild a PatternMatrix/Matcher from receive
//! clauses.

use crate::fz_ir::{Module, ReceiveClause, Var};
use crate::ir_codegen::{
    CodegenError, EMPTY_LIST_BITS, SLOT_BYTES, VRX_TAG_BITSTRING, VRX_TAG_MASK, VRX_TAG_PROCBIN,
    VRX_TAG_STRUCT, emit_fn_body_stats, emit_value_slot_as_tagged_ref,
    emit_value_slot_from_tagged_ref, vrx_ptr_addr,
};
use crate::matcher::{Matcher, MatcherConst, MatcherNode, MatcherTest};
use cranelift_codegen::ir::{
    self, AbiParam, InstBuilder, MemFlags, Signature, condcodes::IntCC, types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage};
use std::collections::HashMap;

/// Cranelift signature for the matcher fn family. Matches
/// `fz_runtime::park::MatcherFn`.
pub(crate) fn matcher_signature() -> Signature {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // msg_value
    sig.params.push(AbiParam::new(types::I8)); // msg_kind
    sig.params.push(AbiParam::new(types::I64)); // pinned_ptr
    sig.params.push(AbiParam::new(types::I64)); // out_ptr
    sig.returns.push(AbiParam::new(types::I32));
    sig
}

/// Declare a matcher fn in `module`. The caller is responsible for
/// pairing this with a single `emit_matcher_body` call before finalize.
pub(crate) fn declare_matcher<M: cranelift_module::Module>(
    module: &mut M,
    name: &str,
) -> Result<FuncId, CodegenError> {
    module
        .declare_function(name, Linkage::Local, &matcher_signature())
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))
}

/// Emit the receive ABI matcher directly from the cached AST-free
/// [`Matcher`]. The clause slice is still used for ABI metadata
/// (`bound_names` and guard rejection), but matching control flow comes from
/// `matcher` instead of rebuilding PatternMatrix/Matcher from receive patterns.
#[allow(clippy::too_many_arguments)]
pub(crate) fn emit_matcher_body_from_matcher<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    matcher_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    pinned: &[(String, Var)],
    clauses: &[ReceiveClause],
    matcher: &Matcher,
    value_eq_typed_id: Option<FuncId>,
    matcher_eq_bytes_id: Option<FuncId>,
    matcher_map_get_id: Option<FuncId>,
    matcher_map_get_ref_id: Option<FuncId>,
    map_is_map_id: Option<FuncId>,
    bs_reader_init_id: Option<FuncId>,
    bs_read_field_id: Option<FuncId>,
    struct_get_field_id: Option<FuncId>,
    list_is_cons_id: Option<FuncId>,
    list_head_id: Option<FuncId>,
    list_tail_id: Option<FuncId>,
) -> Result<(usize, usize), CodegenError> {
    let pinned_indices: HashMap<String, usize> = pinned
        .iter()
        .enumerate()
        .map(|(i, (n, _))| (n.clone(), i))
        .collect();
    let bound_indices_per_clause: Vec<HashMap<String, usize>> = clauses
        .iter()
        .map(|c| {
            c.bound_names
                .iter()
                .enumerate()
                .map(|(i, n)| (n.clone(), i))
                .collect()
        })
        .collect();

    let mut unique_bytes = Vec::new();
    collect_binary_literals_in_matcher(matcher, &mut unique_bytes);
    let mut binary_data_ids: HashMap<Vec<u8>, DataId> = HashMap::new();
    for (idx, bytes) in unique_bytes.into_iter().enumerate() {
        if binary_data_ids.contains_key(&bytes) {
            continue;
        }
        let name = format!(".fz_matcher_bin_{}_{}", matcher_id.as_u32(), idx);
        let did = module
            .declare_data(&name, Linkage::Local, false, false)
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        let mut desc = DataDescription::new();
        desc.define(bytes.clone().into_boxed_slice());
        desc.set_align(1);
        module
            .define_data(did, &desc)
            .map_err(|e| CodegenError::new(format!("define {}: {}", name, e)))?;
        binary_data_ids.insert(bytes, did);
    }

    let mut compile_err: Option<CodegenError> = None;
    let stats = emit_fn_body_stats(module, fbctx, matcher_signature(), matcher_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let msg = b.block_params(entry)[0];
        let msg_kind = b.block_params(entry)[1];
        let pinned_ptr = b.block_params(entry)[2];
        let out_ptr = b.block_params(entry)[3];

        let miss_block = b.create_block();
        let binary_data_gvs: HashMap<Vec<u8>, ir::GlobalValue> = binary_data_ids
            .iter()
            .map(|(bytes, did)| (bytes.clone(), m.declare_data_in_func(*did, b.func)))
            .collect();
        let value_eq_typed_fref = value_eq_typed_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let matcher_eq_bytes_fref =
            matcher_eq_bytes_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let matcher_map_get_fref =
            matcher_map_get_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let matcher_map_get_ref_fref =
            matcher_map_get_ref_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let map_is_map_fref = map_is_map_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let bs_reader_init_fref = bs_reader_init_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let bs_read_field_fref = bs_read_field_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let struct_get_field_fref =
            struct_get_field_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let list_is_cons_fref = list_is_cons_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let list_head_fref = list_head_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let list_tail_fref = list_tail_id.map(|fid| m.declare_func_in_func(fid, b.func));

        let ctx = MatcherCtx {
            fz_module,
            tuple_schema_ids,
            bound_indices_per_clause: &bound_indices_per_clause,
            pinned_indices: &pinned_indices,
            pinned_ptr,
            out_ptr,
            matcher,
            inputs: vec![msg],
            input_kinds: vec![msg_kind],
            binary_data_gvs: &binary_data_gvs,
            value_eq_typed_fref,
            matcher_eq_bytes_fref,
            matcher_map_get_fref,
            matcher_map_get_ref_fref,
            map_is_map_fref,
            bs_reader_init_fref,
            bs_read_field_fref,
            struct_get_field_fref,
            list_is_cons_fref,
            list_head_fref,
            list_tail_fref,
        };

        let mut state = MatcherEmitState::default();
        if let Err(e) = emit_matcher_node(b, &ctx, matcher.root, miss_block, &mut state) {
            compile_err = Some(e);
            finish_failed_matcher_body(b, miss_block);
            return;
        }

        b.switch_to_block(miss_block);
        b.seal_block(miss_block);
        let zero = b.ins().iconst(types::I32, 0);
        b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define matcher fn: {}", e)))?;

    if let Some(e) = compile_err {
        return Err(e);
    }
    Ok(stats)
}

struct MatcherCtx<'a> {
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    bound_indices_per_clause: &'a [HashMap<String, usize>],
    pinned_indices: &'a HashMap<String, usize>,
    pinned_ptr: ir::Value,
    out_ptr: ir::Value,
    matcher: &'a Matcher,
    inputs: Vec<ir::Value>,
    input_kinds: Vec<ir::Value>,
    binary_data_gvs: &'a HashMap<Vec<u8>, ir::GlobalValue>,
    value_eq_typed_fref: Option<ir::FuncRef>,
    matcher_eq_bytes_fref: Option<ir::FuncRef>,
    matcher_map_get_fref: Option<ir::FuncRef>,
    matcher_map_get_ref_fref: Option<ir::FuncRef>,
    map_is_map_fref: Option<ir::FuncRef>,
    bs_reader_init_fref: Option<ir::FuncRef>,
    bs_read_field_fref: Option<ir::FuncRef>,
    struct_get_field_fref: Option<ir::FuncRef>,
    list_is_cons_fref: Option<ir::FuncRef>,
    list_head_fref: Option<ir::FuncRef>,
    list_tail_fref: Option<ir::FuncRef>,
}

#[derive(Default, Clone)]
struct MatcherEmitState {
    values: HashMap<crate::matcher::SubjectRef, ReceiveValue>,
    bitstring_fields: HashMap<(crate::matcher::SubjectRef, u32), ReceiveValue>,
    direct_bindings: HashMap<String, ReceiveValue>,
}

#[derive(Clone, Copy)]
struct ReceiveValue {
    raw: ir::Value,
    kind: ir::Value,
}

impl ReceiveValue {
    fn heap_bits(self, b: &mut FunctionBuilder<'_>) -> ir::Value {
        let kind64 = b.ins().uextend(types::I64, self.kind);
        b.ins().bor(self.raw, kind64)
    }
}

fn receive_value_from_root_parts(
    b: &mut FunctionBuilder<'_>,
    raw: ir::Value,
    kind: ir::Value,
) -> ReceiveValue {
    let kind64 = b.ins().uextend(types::I64, kind);
    let list_kind = fz_runtime::fz_value::ValueKind::LIST.tag() as i64;
    let resource_kind = fz_runtime::fz_value::ValueKind::RESOURCE.tag() as i64;
    let heap_lo = b
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, kind64, list_kind);
    let heap_hi = b
        .ins()
        .icmp_imm(IntCC::UnsignedLessThanOrEqual, kind64, resource_kind);
    let heap_kind = b.ins().band(heap_lo, heap_hi);
    let raw_not_zero = b.ins().icmp_imm(IntCC::NotEqual, raw, 0);
    let has_heap_pointer = b.ins().band(heap_kind, raw_not_zero);
    let heap_raw = b.ins().band_imm(raw, !VRX_TAG_MASK);
    ReceiveValue {
        raw: b.ins().select(has_heap_pointer, heap_raw, raw),
        kind,
    }
}

fn value_root_raw(b: &mut FunctionBuilder<'_>, value: ReceiveValue) -> ir::Value {
    let kind64 = b.ins().uextend(types::I64, value.kind);
    let list_kind = fz_runtime::fz_value::ValueKind::LIST.tag() as i64;
    let resource_kind = fz_runtime::fz_value::ValueKind::RESOURCE.tag() as i64;
    let heap_lo = b
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, kind64, list_kind);
    let heap_hi = b
        .ins()
        .icmp_imm(IntCC::UnsignedLessThanOrEqual, kind64, resource_kind);
    let heap_kind = b.ins().band(heap_lo, heap_hi);
    let raw_not_zero = b.ins().icmp_imm(IntCC::NotEqual, value.raw, 0);
    let is_heap = b.ins().band(heap_kind, raw_not_zero);
    let heap_bits = b.ins().bor(value.raw, kind64);
    b.ins().select(is_heap, heap_bits, value.raw)
}

fn value_root_raw_offset(idx: usize) -> i32 {
    (idx * std::mem::size_of::<fz_runtime::fz_value::ValueRoot>()) as i32
}

fn value_root_kind_offset(idx: usize) -> i32 {
    value_root_raw_offset(idx) + SLOT_BYTES
}

fn load_value_root(
    b: &mut FunctionBuilder<'_>,
    base: ir::Value,
    idx: usize,
) -> (ir::Value, ir::Value) {
    let raw = b.ins().load(
        types::I64,
        MemFlags::trusted(),
        base,
        value_root_raw_offset(idx),
    );
    let kind = b.ins().load(
        types::I8,
        MemFlags::trusted(),
        base,
        value_root_kind_offset(idx),
    );
    (raw, kind)
}

fn load_receive_value_root(
    b: &mut FunctionBuilder<'_>,
    base: ir::Value,
    idx: usize,
) -> ReceiveValue {
    let (raw, kind) = load_value_root(b, base, idx);
    receive_value_from_root_parts(b, raw, kind)
}

fn store_receive_value_root(
    b: &mut FunctionBuilder<'_>,
    base: ir::Value,
    idx: usize,
    value: ReceiveValue,
) {
    let raw = value_root_raw(b, value);
    b.ins()
        .store(MemFlags::trusted(), raw, base, value_root_raw_offset(idx));
    b.ins().store(
        MemFlags::trusted(),
        value.kind,
        base,
        value_root_kind_offset(idx),
    );
}

fn finish_failed_matcher_body(b: &mut FunctionBuilder<'_>, miss_block: ir::Block) {
    let zero = b.ins().iconst(types::I32, 0);
    b.ins().return_(&[zero]);
    let to_miss = b.create_block();
    b.switch_to_block(to_miss);
    b.seal_block(to_miss);
    b.ins().jump(miss_block, &[]);
    b.switch_to_block(miss_block);
    b.seal_block(miss_block);
    let zero2 = b.ins().iconst(types::I32, 0);
    b.ins().return_(&[zero2]);
}

fn emit_matcher_node(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    node_id: crate::matcher::NodeId,
    miss: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<(), CodegenError> {
    let node = ctx
        .matcher
        .node(node_id)
        .ok_or_else(|| CodegenError::new(format!("matcher node {:?} out of bounds", node_id)))?;
    match node {
        MatcherNode::Fail { .. } => {
            b.ins().jump(miss, &[]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        MatcherNode::Leaf(leaf) => {
            let bound = &ctx.bound_indices_per_clause[leaf.body_id as usize];
            for binding in &leaf.bindings {
                let val = resolve_matcher_subject(b, ctx, &binding.source, state)?;
                if let Some(&idx) = bound.get(&binding.name) {
                    store_receive_value_root(b, ctx.out_ptr, idx, val);
                }
            }
            let k = b.ins().iconst(types::I32, (leaf.body_id + 1) as i64);
            b.ins().return_(&[k]);
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            for (key, case_node) in cases {
                let match_b = b.create_block();
                let next_b = b.create_block();
                emit_matcher_switch_key_test(b, ctx, val, kind, key, match_b, next_b)?;
                b.switch_to_block(match_b);
                b.seal_block(match_b);
                let mut case_state = state.clone();
                emit_matcher_node(b, ctx, *case_node, miss, &mut case_state)?;
                b.switch_to_block(next_b);
                b.seal_block(next_b);
            }
            emit_matcher_node(b, ctx, *default, miss, state)
        }
        MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => {
            let true_b = b.create_block();
            let false_b = b.create_block();
            let true_values = emit_matcher_test(b, ctx, test, true_b, false_b, state)?;
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
            true_state.values.extend(true_values);
            emit_matcher_node(b, ctx, *on_true, miss, &mut true_state)?;
            b.switch_to_block(false_b);
            b.seal_block(false_b);
            emit_matcher_node(b, ctx, *on_false, miss, state)
        }
        MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let value = emit_matcher_guard_expr(b, ctx, expr, state)?;
            let truthy = emit_truthy_cmp(b, value);
            let true_b = b.create_block();
            let false_b = b.create_block();
            b.ins().brif(truthy, true_b, &[], false_b, &[]);
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
            emit_matcher_node(b, ctx, *on_true, miss, &mut true_state)?;
            b.switch_to_block(false_b);
            b.seal_block(false_b);
            emit_matcher_node(b, ctx, *on_false, miss, state)
        }
    }
}

fn resolve_matcher_subject(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    sref: &crate::matcher::SubjectRef,
    state: &mut MatcherEmitState,
) -> Result<ReceiveValue, CodegenError> {
    if let Some(v) = state.values.get(sref).copied() {
        return Ok(v);
    }
    let v = match sref {
        crate::matcher::SubjectRef::Input(id) => {
            let raw = *ctx.inputs.get(id.0 as usize).ok_or_else(|| {
                CodegenError::new(format!("receive ABI matcher has no input {:?}", id))
            })?;
            if let Some(kind) = ctx.input_kinds.get(id.0 as usize).copied() {
                receive_value_from_root_parts(b, raw, kind)
            } else {
                matcher_value_from_heap_bits(b, raw)
            }
        }
        crate::matcher::SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_matcher_subject(b, ctx, tuple, state)?;
            emit_struct_get_field(b, ctx, parent, *index)?
        }
        crate::matcher::SubjectRef::ListHead(list) => {
            let parent = resolve_matcher_subject(b, ctx, list, state)?;
            let Some(fref) = ctx.list_head_fref else {
                return Err(CodegenError::new(
                    "ListHead matcher projection requires fz_list_head",
                ));
            };
            let parent_ref = emit_value_slot_as_tagged_ref(b, parent.raw, parent.kind);
            let inst = b.ins().call(fref, &[parent_ref]);
            let out_ref = b.inst_results(inst)[0];
            let (raw, kind) = emit_value_slot_from_tagged_ref(b, out_ref);
            ReceiveValue { raw, kind }
        }
        crate::matcher::SubjectRef::ListTail(list) => {
            let parent = resolve_matcher_subject(b, ctx, list, state)?;
            let Some(fref) = ctx.list_tail_fref else {
                return Err(CodegenError::new(
                    "ListTail matcher projection requires fz_list_tail",
                ));
            };
            let parent_ref = emit_value_slot_as_tagged_ref(b, parent.raw, parent.kind);
            let inst = b.ins().call(fref, &[parent_ref]);
            let out_ref = b.inst_results(inst)[0];
            let (raw, kind) = emit_value_slot_from_tagged_ref(b, out_ref);
            ReceiveValue { raw, kind }
        }
        crate::matcher::SubjectRef::MapValue { map, key } => {
            let map = resolve_matcher_subject(b, ctx, map, state)?;
            emit_matcher_map_get_value(b, ctx, map, key)?
        }
        crate::matcher::SubjectRef::BitstringField { bitstring, index } => *state
            .bitstring_fields
            .get(&((**bitstring).clone(), *index))
            .ok_or_else(|| {
                CodegenError::new(format!(
                    "receive ABI matcher bitstring field {:?} not available",
                    sref
                ))
            })?,
    };
    state.values.insert(sref.clone(), v);
    Ok(v)
}

fn matcher_value_from_heap_bits(b: &mut FunctionBuilder<'_>, bits: ir::Value) -> ReceiveValue {
    let is_empty = b.ins().icmp_imm(IntCC::Equal, bits, EMPTY_LIST_BITS);
    let zero = b.ins().iconst(types::I64, 0);
    let raw_heap = b.ins().band_imm(bits, !VRX_TAG_MASK);
    let raw = b.ins().select(is_empty, zero, raw_heap);
    let tag64 = b.ins().band_imm(bits, VRX_TAG_MASK);
    let heap_kind = b.ins().ireduce(types::I8, tag64);
    let list_kind = b.ins().iconst(
        types::I8,
        fz_runtime::fz_value::ValueKind::LIST.tag() as i64,
    );
    let kind = b.ins().select(is_empty, list_kind, heap_kind);
    ReceiveValue { raw, kind }
}

fn load_pinned_matcher_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    pinned: crate::matcher::PinnedId,
) -> Result<ReceiveValue, CodegenError> {
    let p = ctx
        .matcher
        .pinned
        .get(pinned.0 as usize)
        .ok_or_else(|| CodegenError::new(format!("pinned {:?} out of bounds", pinned)))?;
    if let Some(var) = p.var {
        let raw = *ctx.inputs.get(var.0 as usize).ok_or_else(|| {
            CodegenError::new(format!("pinned helper input {:?} out of bounds", var))
        })?;
        let kind = *ctx.input_kinds.get(var.0 as usize).ok_or_else(|| {
            CodegenError::new(format!(
                "pinned helper input {:?} has no side-tag kind",
                var
            ))
        })?;
        return Ok(receive_value_from_root_parts(b, raw, kind));
    }

    let &idx = ctx.pinned_indices.get(&p.name).ok_or_else(|| {
        CodegenError::new(format!("pinned ^{} not in matcher's pinned table", p.name))
    })?;
    Ok(load_receive_value_root(b, ctx.pinned_ptr, idx))
}

fn emit_matcher_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    test: &MatcherTest,
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<Vec<(crate::matcher::SubjectRef, ReceiveValue)>, CodegenError> {
    let mut true_values = Vec::new();
    match test {
        MatcherTest::EqConst { subject, value } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_matcher_const_test(b, ctx, val, value, true_b, false_b)?;
        }
        MatcherTest::EqPinned { subject, pinned } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let want = load_pinned_matcher_value(b, ctx, *pinned)?;
            emit_typed_eq_branch(b, ctx, val, want, true_b, false_b)?;
        }
        MatcherTest::TupleArity { subject, arity } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let bits = val.heap_bits(b);
            emit_tuple_arity_test(
                b,
                ctx.tuple_schema_ids,
                bits,
                *arity as usize,
                true_b,
                false_b,
            )?;
        }
        MatcherTest::ListCons { subject } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let bits = val.heap_bits(b);
            emit_list_cons_test(b, ctx, bits, true_b, false_b)?;
        }
        MatcherTest::MapKind { subject } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let bits = val.heap_bits(b);
            emit_map_kind_test(b, ctx, bits, true_b, false_b)?;
        }
        MatcherTest::MapHasKey { subject, key } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let got = emit_matcher_map_get_value(b, ctx, val, key)?;
            true_values.push((crate::matcher::map_value_subject(subject, key), got));
            let cmp = emit_not_matcher_map_miss(b, got);
            b.ins().brif(cmp, true_b, &[], false_b, &[]);
        }
        MatcherTest::Bitstring { subject, fields } => {
            emit_bitstring_test(b, ctx, subject, fields, true_b, false_b, state)?;
        }
        MatcherTest::Type { .. } => Err(CodegenError::new(
            "receive ABI matcher cannot emit type tests yet",
        ))?,
    }
    Ok(true_values)
}

fn emit_matcher_side_tag_const_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    value: &MatcherConst,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<bool, CodegenError> {
    let Some((want_kind, want_value)) = matcher_const_side_tag(ctx.fz_module, value)? else {
        return Ok(false);
    };
    let kind64 = b.ins().uextend(types::I64, val.kind);
    let kind_ok = b.ins().icmp_imm(IntCC::Equal, kind64, want_kind as i64);
    let value_ok = b.ins().icmp_imm(IntCC::Equal, val.raw, want_value as i64);
    let ok = b.ins().band(kind_ok, value_ok);
    b.ins().brif(ok, match_b, &[], next_b, &[]);
    Ok(true)
}

fn matcher_const_side_tag(
    module: &Module,
    value: &MatcherConst,
) -> Result<Option<(u8, u64)>, CodegenError> {
    Ok(match value {
        MatcherConst::Int(n) => Some((fz_runtime::fz_value::ValueKind::INT.tag(), *n as u64)),
        MatcherConst::FloatBits(bits) => {
            Some((fz_runtime::fz_value::ValueKind::FLOAT.tag(), *bits))
        }
        MatcherConst::AtomName(name) => {
            let Some(id) = module.atom_names.iter().position(|n| n == name) else {
                return Ok(None);
            };
            Some((fz_runtime::fz_value::ValueKind::ATOM.tag(), id as u64))
        }
        MatcherConst::Bool(v) => Some((
            fz_runtime::fz_value::ValueKind::ATOM.tag(),
            if *v {
                fz_runtime::fz_value::TRUE_ATOM_ID as u64
            } else {
                fz_runtime::fz_value::FALSE_ATOM_ID as u64
            },
        )),
        MatcherConst::Nil => Some((
            fz_runtime::fz_value::ValueKind::ATOM.tag(),
            fz_runtime::fz_value::NIL_ATOM_ID as u64,
        )),
        MatcherConst::EmptyList => Some((fz_runtime::fz_value::ValueKind::LIST.tag(), 0)),
        _ => None,
    })
}

fn matcher_const_value(
    module: &Module,
    value: &MatcherConst,
) -> Result<Option<MatcherConstValue>, CodegenError> {
    Ok(match value {
        MatcherConst::Int(n) => Some(MatcherConstValue {
            raw: *n as u64,
            kind: fz_runtime::fz_value::ValueKind::INT,
        }),
        MatcherConst::FloatBits(bits) => Some(MatcherConstValue {
            raw: *bits,
            kind: fz_runtime::fz_value::ValueKind::FLOAT,
        }),
        MatcherConst::AtomName(name) => {
            module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|id| MatcherConstValue {
                    raw: id as u64,
                    kind: fz_runtime::fz_value::ValueKind::ATOM,
                })
        }
        MatcherConst::Bool(v) => Some(MatcherConstValue {
            raw: if *v {
                fz_runtime::fz_value::TRUE_ATOM_ID as u64
            } else {
                fz_runtime::fz_value::FALSE_ATOM_ID as u64
            },
            kind: fz_runtime::fz_value::ValueKind::ATOM,
        }),
        MatcherConst::Nil => Some(MatcherConstValue {
            raw: fz_runtime::fz_value::NIL_ATOM_ID as u64,
            kind: fz_runtime::fz_value::ValueKind::ATOM,
        }),
        MatcherConst::EmptyList => Some(MatcherConstValue {
            raw: 0,
            kind: fz_runtime::fz_value::ValueKind::LIST,
        }),
        MatcherConst::Utf8Binary(_) | MatcherConst::PreparedKey(_) => None,
    })
}

struct MatcherConstValue {
    raw: u64,
    kind: fz_runtime::fz_value::ValueKind,
}

fn emit_matcher_switch_key_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    kind: &crate::matcher::SwitchKind,
    key: &crate::matcher::SwitchKey,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match (kind, key) {
        (crate::matcher::SwitchKind::Atom, crate::matcher::SwitchKey::AtomName(name)) => {
            let c = MatcherConst::AtomName(name.clone());
            emit_matcher_const_test(b, ctx, val, &c, match_b, next_b)?;
            Ok(())
        }
        (crate::matcher::SwitchKind::Int, crate::matcher::SwitchKey::Int(n)) => {
            let c = MatcherConst::Int(*n);
            emit_matcher_const_test(b, ctx, val, &c, match_b, next_b)?;
            Ok(())
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(v)) => {
            let c = MatcherConst::Bool(*v);
            emit_matcher_const_test(b, ctx, val, &c, match_b, next_b)?;
            Ok(())
        }
        (crate::matcher::SwitchKind::Nil, crate::matcher::SwitchKey::Nil) => {
            emit_matcher_const_test(b, ctx, val, &MatcherConst::Nil, match_b, next_b)?;
            Ok(())
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Nil) => {
            emit_matcher_const_test(b, ctx, val, &MatcherConst::EmptyList, match_b, next_b)?;
            Ok(())
        }
        (crate::matcher::SwitchKind::TupleArity, crate::matcher::SwitchKey::Arity(arity)) => {
            let bits = val.heap_bits(b);
            emit_tuple_arity_test(
                b,
                ctx.tuple_schema_ids,
                bits,
                *arity as usize,
                match_b,
                next_b,
            )
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::EmptyList) => {
            emit_matcher_const_test(b, ctx, val, &MatcherConst::EmptyList, match_b, next_b)?;
            Ok(())
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Cons) => {
            let bits = val.heap_bits(b);
            emit_list_cons_test(b, ctx, bits, match_b, next_b)
        }
        (crate::matcher::SwitchKind::Float, crate::matcher::SwitchKey::FloatBits(bits)) => {
            emit_matcher_const_test(
                b,
                ctx,
                val,
                &MatcherConst::FloatBits(*bits),
                match_b,
                next_b,
            )
        }
        (crate::matcher::SwitchKind::Binary, crate::matcher::SwitchKey::Utf8Binary(bytes)) => {
            let bits = val.heap_bits(b);
            emit_binary_literal_test(
                b,
                ctx.binary_data_gvs,
                ctx.matcher_eq_bytes_fref,
                bits,
                bytes,
                match_b,
                next_b,
            )
        }
        _ => Err(CodegenError::new(format!(
            "Matcher Switch kind/key combination not yet supported in receive matcher: {:?} / {:?}",
            kind, key
        ))),
    }
}

fn emit_matcher_const_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    value: &MatcherConst,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match value {
        MatcherConst::FloatBits(_)
        | MatcherConst::Int(_)
        | MatcherConst::AtomName(_)
        | MatcherConst::Bool(_)
        | MatcherConst::Nil
        | MatcherConst::EmptyList => {
            let emitted = emit_matcher_side_tag_const_test(b, ctx, val, value, match_b, next_b)?;
            if !emitted {
                b.ins().jump(next_b, &[]);
            }
            Ok(())
        }
        MatcherConst::Utf8Binary(bytes) => {
            let bits = val.heap_bits(b);
            emit_binary_literal_test(
                b,
                ctx.binary_data_gvs,
                ctx.matcher_eq_bytes_fref,
                bits,
                bytes,
                match_b,
                next_b,
            )
        }
        MatcherConst::PreparedKey(_) => Err(CodegenError::new(
            "prepared heap map keys are not supported in receive ABI matcher yet (fz-puj.54.6)",
        )),
    }
}

fn emit_matcher_map_get_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    map: ReceiveValue,
    key: &MatcherConst,
) -> Result<ReceiveValue, CodegenError> {
    if let MatcherConst::PreparedKey(index) = key {
        let Some(map_get_ref_fref) = ctx.matcher_map_get_ref_fref else {
            return Err(CodegenError::new(
                "Prepared map matcher key requires fz_matcher_map_get_ref",
            ));
        };
        let name = crate::matcher::prepared_key_name(*index as usize);
        let &idx = ctx.pinned_indices.get(&name).ok_or_else(|| {
            CodegenError::new(format!(
                "prepared matcher key {} not in pinned table",
                index
            ))
        })?;
        let (key_raw, key_kind) = load_value_root(b, ctx.pinned_ptr, idx);
        let map_ref = emit_value_slot_as_tagged_ref(b, map.raw, map.kind);
        let key_ref = emit_value_slot_as_tagged_ref(b, key_raw, key_kind);
        let inst = b.ins().call(map_get_ref_fref, &[map_ref, key_ref]);
        let out_ref = b.inst_results(inst)[0];
        let (raw, kind) = emit_value_slot_from_tagged_ref(b, out_ref);
        return Ok(ReceiveValue { raw, kind });
    }
    let Some(map_get_ref_fref) = ctx.matcher_map_get_ref_fref else {
        return Err(CodegenError::new(
            "Map matcher test requires fz_matcher_map_get_ref; runtime not linked in this context",
        ));
    };
    let Some(key_value) = matcher_const_value(ctx.fz_module, key)? else {
        return Err(CodegenError::new(format!(
            "map-pattern key {:?} cannot be materialized in receive ABI matcher",
            key
        )));
    };
    let key_raw = b.ins().iconst(types::I64, key_value.raw as i64);
    let key_kind = b.ins().iconst(types::I8, key_value.kind.tag() as i64);
    let map_ref = emit_value_slot_as_tagged_ref(b, map.raw, map.kind);
    let key_ref = emit_value_slot_as_tagged_ref(b, key_raw, key_kind);
    let inst = b.ins().call(map_get_ref_fref, &[map_ref, key_ref]);
    let out_ref = b.inst_results(inst)[0];
    let (raw, kind) = emit_value_slot_from_tagged_ref(b, out_ref);
    Ok(ReceiveValue { raw, kind })
}

fn emit_bitstring_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    subject: &crate::matcher::SubjectRef,
    fields: &[crate::matcher::MatcherBitField],
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<(), CodegenError> {
    let Some(init_fref) = ctx.bs_reader_init_fref else {
        return Err(CodegenError::new(
            "Bitstring matcher test requires fz_bs_reader_init",
        ));
    };
    let Some(read_fref) = ctx.bs_read_field_fref else {
        return Err(CodegenError::new(
            "Bitstring matcher test requires fz_bs_read_field",
        ));
    };
    let value = resolve_matcher_subject(b, ctx, subject, state)?;
    emit_bitstring_like_guard(b, value, false_b);
    let init = b.ins().call(init_fref, &[value.raw, value.kind]);
    let mut reader = b.inst_results(init)[0];

    for (index, field) in fields.iter().enumerate() {
        let (size_present, size_value) = emit_matcher_bit_size(b, field, state)?;
        let ty = b
            .ins()
            .iconst(types::I32, matcher_bit_type_tag(field.ty) as i64);
        let unit = b.ins().iconst(
            types::I32,
            field.unit.unwrap_or(default_matcher_bit_unit(field.ty)) as i64,
        );
        let endian = b
            .ins()
            .iconst(types::I32, matcher_endian_tag(field.endian) as i64);
        let signed = b.ins().iconst(types::I32, field.signed as i64);
        let is_last = b
            .ins()
            .iconst(types::I32, (index + 1 == fields.len()) as i64);
        let reader_raw = b.ins().band_imm(reader, !0xf);
        let reader_kind = b.ins().iconst(types::I8, VRX_TAG_STRUCT);
        let inst = b.ins().call(
            read_fref,
            &[
                reader_raw,
                reader_kind,
                ty,
                size_present,
                size_value,
                unit,
                endian,
                signed,
                is_last,
            ],
        );
        let result = b.inst_results(inst)[0];
        let ok_bits = emit_struct_get_field_from_bits(b, ctx, result, 0)?;
        let ok = matcher_value_from_heap_bits(b, ok_bits);
        let ok_truthy = emit_truthy_cmp(b, ok);
        let next_b = b.create_block();
        b.ins().brif(ok_truthy, next_b, &[], false_b, &[]);
        b.switch_to_block(next_b);
        b.seal_block(next_b);
        let result_value = matcher_value_from_heap_bits(b, result);
        let extracted = emit_struct_get_field(b, ctx, result_value, 1)?;
        reader = emit_struct_get_field_value_from_bits(b, ctx, result, 2)?.heap_bits(b);
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            state.direct_bindings.insert(name.clone(), extracted);
        }
    }

    let bit_len = emit_struct_get_field_from_bits(b, ctx, reader, 1)?;
    let pos = emit_struct_get_field_from_bits(b, ctx, reader, 2)?;
    let done = b.ins().icmp(IntCC::Equal, bit_len, pos);
    b.ins().brif(done, true_b, &[], false_b, &[]);
    Ok(())
}

fn emit_struct_get_field(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    struct_value: ReceiveValue,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    emit_struct_get_field_value(b, ctx, struct_value, field_index)
}

fn emit_struct_get_field_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    struct_value: ReceiveValue,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    let Some(fref) = ctx.struct_get_field_fref else {
        return Err(CodegenError::new(
            "struct field projection requires fz_struct_get_field",
        ));
    };
    let field_offset = b
        .ins()
        .iconst(types::I32, field_index as i64 * SLOT_BYTES as i64);
    let struct_ref = emit_value_slot_as_tagged_ref(b, struct_value.raw, struct_value.kind);
    let inst = b.ins().call(fref, &[struct_ref, field_offset]);
    let out_ref = b.inst_results(inst)[0];
    let (raw, kind) = emit_value_slot_from_tagged_ref(b, out_ref);
    Ok(ReceiveValue { raw, kind })
}

fn emit_struct_get_field_value_from_bits(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    struct_bits: ir::Value,
    field_index: u32,
) -> Result<ReceiveValue, CodegenError> {
    let struct_value = matcher_value_from_heap_bits(b, struct_bits);
    emit_struct_get_field_value(b, ctx, struct_value, field_index)
}

fn emit_struct_get_field_from_bits(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    struct_bits: ir::Value,
    field_index: u32,
) -> Result<ir::Value, CodegenError> {
    Ok(emit_struct_get_field_value_from_bits(b, ctx, struct_bits, field_index)?.raw)
}

fn emit_bitstring_like_guard(b: &mut FunctionBuilder<'_>, val: ReceiveValue, miss: ir::Block) {
    let tag = b.ins().uextend(types::I64, val.kind);
    let cont = b.create_block();
    let ptr_path = b.create_block();
    let strict_bs_tag = b.ins().iconst(types::I64, VRX_TAG_BITSTRING);
    let is_strict_bs = b.ins().icmp(IntCC::Equal, tag, strict_bs_tag);
    let strict_proc_tag = b.ins().iconst(types::I64, VRX_TAG_PROCBIN);
    let is_strict_proc = b.ins().icmp(IntCC::Equal, tag, strict_proc_tag);
    let is_strict = b.ins().bor(is_strict_bs, is_strict_proc);
    b.ins().brif(is_strict, cont, &[], ptr_path, &[]);
    b.switch_to_block(ptr_path);
    b.seal_block(ptr_path);
    b.ins().jump(miss, &[]);
    b.switch_to_block(cont);
    b.seal_block(cont);
}

fn emit_matcher_bit_size(
    b: &mut FunctionBuilder<'_>,
    field: &crate::matcher::MatcherBitField,
    state: &MatcherEmitState,
) -> Result<(ir::Value, ir::Value), CodegenError> {
    match &field.size {
        None => Ok((b.ins().iconst(types::I32, 0), b.ins().iconst(types::I32, 0))),
        Some(crate::matcher::MatcherBitSize::Literal(n)) => Ok((
            b.ins().iconst(types::I32, 1),
            b.ins().iconst(types::I32, *n as i64),
        )),
        Some(crate::matcher::MatcherBitSize::BindingName(name)) => {
            let value = state.direct_bindings.get(name).copied().ok_or_else(|| {
                CodegenError::new(format!("bitstring size binding `{}` not available", name))
            })?;
            Ok((b.ins().iconst(types::I32, 1), strict_int_i32(b, value)))
        }
    }
}

fn strict_int_i32(b: &mut FunctionBuilder<'_>, v: ReceiveValue) -> ir::Value {
    b.ins().ireduce(types::I32, v.raw)
}

fn matcher_bit_type_tag(ty: crate::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::matcher::MatcherBitType::Integer => 0,
        crate::matcher::MatcherBitType::Float => 1,
        crate::matcher::MatcherBitType::Binary => 2,
        crate::matcher::MatcherBitType::Bits => 3,
        crate::matcher::MatcherBitType::Utf8 => 4,
        crate::matcher::MatcherBitType::Utf16 => 5,
        crate::matcher::MatcherBitType::Utf32 => 6,
    }
}

fn matcher_endian_tag(endian: crate::matcher::MatcherEndian) -> u32 {
    match endian {
        crate::matcher::MatcherEndian::Big => 0,
        crate::matcher::MatcherEndian::Little => 1,
        crate::matcher::MatcherEndian::Native => 2,
    }
}

fn default_matcher_bit_unit(ty: crate::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::matcher::MatcherBitType::Integer
        | crate::matcher::MatcherBitType::Float
        | crate::matcher::MatcherBitType::Bits => 1,
        crate::matcher::MatcherBitType::Binary => 8,
        crate::matcher::MatcherBitType::Utf8
        | crate::matcher::MatcherBitType::Utf16
        | crate::matcher::MatcherBitType::Utf32 => 1,
    }
}

fn emit_matcher_guard_expr(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    expr: &crate::matcher::GuardExpr,
    state: &mut MatcherEmitState,
) -> Result<ReceiveValue, CodegenError> {
    use crate::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    Ok(match expr {
        GuardExpr::Const(c) => {
            let Some(value) = matcher_const_value(ctx.fz_module, c)? else {
                return Err(CodegenError::new(format!(
                    "guard const {:?} cannot be materialized in receive ABI matcher",
                    c
                )));
            };
            ReceiveValue {
                raw: b.ins().iconst(types::I64, value.raw as i64),
                kind: b.ins().iconst(types::I8, value.kind.tag() as i64),
            }
        }
        GuardExpr::Subject(subject) => resolve_matcher_subject(b, ctx, subject, state)?,
        GuardExpr::Pinned(pinned) => load_pinned_matcher_value(b, ctx, *pinned)?,
        GuardExpr::Unary { op, expr } => {
            let v = emit_matcher_guard_expr(b, ctx, expr, state)?;
            match op {
                GuardUnaryOp::Not => {
                    let truthy = emit_truthy_cmp(b, v);
                    emit_bool_value_from_truthy(b, truthy, true)
                }
                GuardUnaryOp::Neg => {
                    let z = b.ins().iconst(types::I64, 0);
                    let neg = b.ins().isub(z, v.raw);
                    int_value(b, neg)
                }
            }
        }
        GuardExpr::Binary { op, lhs, rhs } => {
            if matches!(op, GuardBinOp::And | GuardBinOp::Or) {
                return emit_short_circuit_guard(b, ctx, *op, lhs, rhs, state);
            }
            let l = emit_matcher_guard_expr(b, ctx, lhs, state)?;
            let r = emit_matcher_guard_expr(b, ctx, rhs, state)?;
            match op {
                GuardBinOp::Add => {
                    let sum = b.ins().iadd(l.raw, r.raw);
                    int_value(b, sum)
                }
                GuardBinOp::Sub => {
                    let diff = b.ins().isub(l.raw, r.raw);
                    int_value(b, diff)
                }
                GuardBinOp::Mul => {
                    let prod = b.ins().imul(l.raw, r.raw);
                    int_value(b, prod)
                }
                GuardBinOp::Div => {
                    let quot = b.ins().sdiv(l.raw, r.raw);
                    int_value(b, quot)
                }
                GuardBinOp::Rem => {
                    let rem = b.ins().srem(l.raw, r.raw);
                    int_value(b, rem)
                }
                GuardBinOp::Eq => {
                    let cmp = emit_typed_eq_cmp(b, ctx, l, r)?;
                    emit_bool_value(b, cmp)
                }
                GuardBinOp::Neq => {
                    let eq = emit_typed_eq_cmp(b, ctx, l, r)?;
                    let neq = b.ins().bxor_imm(eq, 1);
                    emit_bool_value(b, neq)
                }
                GuardBinOp::Lt => emit_int_cmp_value(b, IntCC::SignedLessThan, l, r),
                GuardBinOp::LtEq => emit_int_cmp_value(b, IntCC::SignedLessThanOrEqual, l, r),
                GuardBinOp::Gt => emit_int_cmp_value(b, IntCC::SignedGreaterThan, l, r),
                GuardBinOp::GtEq => emit_int_cmp_value(b, IntCC::SignedGreaterThanOrEqual, l, r),
                GuardBinOp::And => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
                GuardBinOp::Or => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
            }
        }
        GuardExpr::Dispatch { inputs, dispatch } => {
            let values = inputs
                .iter()
                .map(|input| emit_matcher_guard_expr(b, ctx, input, state))
                .collect::<Result<Vec<_>, _>>()?;
            emit_guard_dispatch(b, ctx, dispatch, values)?
        }
    })
}

fn emit_guard_dispatch(
    b: &mut FunctionBuilder<'_>,
    parent: &MatcherCtx<'_>,
    dispatch: &crate::matcher::GuardDispatch,
    inputs: Vec<ReceiveValue>,
) -> Result<ReceiveValue, CodegenError> {
    let done = b.create_block();
    b.append_block_param(done, types::I64);
    b.append_block_param(done, types::I8);
    let ctx = MatcherCtx {
        fz_module: parent.fz_module,
        tuple_schema_ids: parent.tuple_schema_ids,
        bound_indices_per_clause: parent.bound_indices_per_clause,
        pinned_indices: parent.pinned_indices,
        pinned_ptr: parent.pinned_ptr,
        out_ptr: parent.out_ptr,
        matcher: &dispatch.matcher,
        inputs: inputs.iter().map(|v| v.raw).collect(),
        input_kinds: inputs.iter().map(|v| v.kind).collect(),
        binary_data_gvs: parent.binary_data_gvs,
        value_eq_typed_fref: parent.value_eq_typed_fref,
        matcher_eq_bytes_fref: parent.matcher_eq_bytes_fref,
        matcher_map_get_fref: parent.matcher_map_get_fref,
        matcher_map_get_ref_fref: parent.matcher_map_get_ref_fref,
        map_is_map_fref: parent.map_is_map_fref,
        bs_reader_init_fref: parent.bs_reader_init_fref,
        bs_read_field_fref: parent.bs_read_field_fref,
        struct_get_field_fref: parent.struct_get_field_fref,
        list_is_cons_fref: parent.list_is_cons_fref,
        list_head_fref: parent.list_head_fref,
        list_tail_fref: parent.list_tail_fref,
    };
    let mut state = MatcherEmitState::default();
    emit_guard_dispatch_node(
        b,
        &ctx,
        &dispatch.bodies,
        dispatch.matcher.root,
        done,
        &mut state,
    )?;
    b.switch_to_block(done);
    b.seal_block(done);
    Ok(ReceiveValue {
        raw: b.block_params(done)[0],
        kind: b.block_params(done)[1],
    })
}

fn emit_guard_dispatch_node(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    bodies: &[crate::matcher::GuardExpr],
    node_id: crate::matcher::NodeId,
    done: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<(), CodegenError> {
    let node = ctx.matcher.node(node_id).ok_or_else(|| {
        CodegenError::new(format!("guard dispatch node {:?} out of bounds", node_id))
    })?;
    match node {
        MatcherNode::Fail { .. } => {
            let false_value = bool_const_value(b, false);
            b.ins().jump(
                done,
                &[
                    ir::BlockArg::Value(false_value.raw),
                    ir::BlockArg::Value(false_value.kind),
                ],
            );
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        MatcherNode::Leaf(leaf) => {
            let body = bodies.get(leaf.body_id as usize).ok_or_else(|| {
                CodegenError::new(format!(
                    "guard dispatch body {} out of bounds",
                    leaf.body_id
                ))
            })?;
            let value = emit_matcher_guard_expr(b, ctx, body, state)?;
            b.ins().jump(
                done,
                &[
                    ir::BlockArg::Value(value.raw),
                    ir::BlockArg::Value(value.kind),
                ],
            );
            let dead = b.create_block();
            b.switch_to_block(dead);
            b.seal_block(dead);
            Ok(())
        }
        MatcherNode::Switch {
            subject,
            kind,
            cases,
            default,
            ..
        } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            for (key, case_node) in cases {
                let match_b = b.create_block();
                let next_b = b.create_block();
                emit_matcher_switch_key_test(b, ctx, val, kind, key, match_b, next_b)?;
                b.switch_to_block(match_b);
                b.seal_block(match_b);
                let mut case_state = state.clone();
                emit_guard_dispatch_node(b, ctx, bodies, *case_node, done, &mut case_state)?;
                b.switch_to_block(next_b);
                b.seal_block(next_b);
            }
            emit_guard_dispatch_node(b, ctx, bodies, *default, done, state)
        }
        MatcherNode::Test {
            test,
            on_true,
            on_false,
            ..
        } => {
            let true_b = b.create_block();
            let false_b = b.create_block();
            let true_values = emit_matcher_test(b, ctx, test, true_b, false_b, state)?;
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
            true_state.values.extend(true_values);
            emit_guard_dispatch_node(b, ctx, bodies, *on_true, done, &mut true_state)?;
            b.switch_to_block(false_b);
            b.seal_block(false_b);
            emit_guard_dispatch_node(b, ctx, bodies, *on_false, done, state)
        }
        MatcherNode::Guard {
            expr,
            on_true,
            on_false,
            ..
        } => {
            let value = emit_matcher_guard_expr(b, ctx, expr, state)?;
            let truthy = emit_truthy_cmp(b, value);
            let true_b = b.create_block();
            let false_b = b.create_block();
            b.ins().brif(truthy, true_b, &[], false_b, &[]);
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
            emit_guard_dispatch_node(b, ctx, bodies, *on_true, done, &mut true_state)?;
            b.switch_to_block(false_b);
            b.seal_block(false_b);
            emit_guard_dispatch_node(b, ctx, bodies, *on_false, done, state)
        }
    }
}

fn emit_short_circuit_guard(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    op: crate::matcher::GuardBinOp,
    lhs: &crate::matcher::GuardExpr,
    rhs: &crate::matcher::GuardExpr,
    state: &mut MatcherEmitState,
) -> Result<ReceiveValue, CodegenError> {
    let lhs_value = emit_matcher_guard_expr(b, ctx, lhs, state)?;
    let lhs_truthy = emit_truthy_cmp(b, lhs_value);
    let rhs_b = b.create_block();
    let done_b = b.create_block();
    b.append_block_param(done_b, types::I64);
    b.append_block_param(done_b, types::I8);

    let true_value = bool_const_value(b, true);
    let false_value = bool_const_value(b, false);
    match op {
        crate::matcher::GuardBinOp::And => b.ins().brif(
            lhs_truthy,
            rhs_b,
            &[],
            done_b,
            &[
                ir::BlockArg::Value(false_value.raw),
                ir::BlockArg::Value(false_value.kind),
            ],
        ),
        crate::matcher::GuardBinOp::Or => b.ins().brif(
            lhs_truthy,
            done_b,
            &[
                ir::BlockArg::Value(true_value.raw),
                ir::BlockArg::Value(true_value.kind),
            ],
            rhs_b,
            &[],
        ),
        _ => unreachable!("non-short-circuit guard op"),
    };

    b.switch_to_block(rhs_b);
    b.seal_block(rhs_b);
    let mut rhs_state = state.clone();
    let rhs_value = emit_matcher_guard_expr(b, ctx, rhs, &mut rhs_state)?;
    let rhs_truthy = emit_truthy_cmp(b, rhs_value);
    let rhs_bool = emit_bool_value_from_truthy(b, rhs_truthy, false);
    b.ins().jump(
        done_b,
        &[
            ir::BlockArg::Value(rhs_bool.raw),
            ir::BlockArg::Value(rhs_bool.kind),
        ],
    );

    b.switch_to_block(done_b);
    b.seal_block(done_b);
    Ok(ReceiveValue {
        raw: b.block_params(done_b)[0],
        kind: b.block_params(done_b)[1],
    })
}

fn int_value(b: &mut FunctionBuilder<'_>, raw: ir::Value) -> ReceiveValue {
    ReceiveValue {
        raw,
        kind: b
            .ins()
            .iconst(types::I8, fz_runtime::fz_value::ValueKind::INT.tag() as i64),
    }
}

fn bool_const_value(b: &mut FunctionBuilder<'_>, value: bool) -> ReceiveValue {
    let raw = if value {
        fz_runtime::fz_value::TRUE_ATOM_ID
    } else {
        fz_runtime::fz_value::FALSE_ATOM_ID
    };
    ReceiveValue {
        raw: b.ins().iconst(types::I64, raw as i64),
        kind: b.ins().iconst(
            types::I8,
            fz_runtime::fz_value::ValueKind::ATOM.tag() as i64,
        ),
    }
}

fn emit_int_cmp_value(
    b: &mut FunctionBuilder<'_>,
    cc: IntCC,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> ReceiveValue {
    let cmp = b.ins().icmp(cc, lhs.raw, rhs.raw);
    emit_bool_value(b, cmp)
}

fn emit_bool_value(b: &mut FunctionBuilder<'_>, cmp: ir::Value) -> ReceiveValue {
    emit_bool_value_from_truthy(b, cmp, false)
}

fn emit_bool_value_from_truthy(
    b: &mut FunctionBuilder<'_>,
    truthy: ir::Value,
    invert: bool,
) -> ReceiveValue {
    let t = b
        .ins()
        .iconst(types::I64, fz_runtime::fz_value::TRUE_ATOM_ID as i64);
    let f = b
        .ins()
        .iconst(types::I64, fz_runtime::fz_value::FALSE_ATOM_ID as i64);
    let raw = if invert {
        b.ins().select(truthy, f, t)
    } else {
        b.ins().select(truthy, t, f)
    };
    ReceiveValue {
        raw,
        kind: b.ins().iconst(
            types::I8,
            fz_runtime::fz_value::ValueKind::ATOM.tag() as i64,
        ),
    }
}

fn emit_truthy_cmp(b: &mut FunctionBuilder<'_>, v: ReceiveValue) -> ir::Value {
    let kind64 = b.ins().uextend(types::I64, v.kind);
    let is_atom = b.ins().icmp_imm(
        IntCC::Equal,
        kind64,
        fz_runtime::fz_value::ValueKind::ATOM.tag() as i64,
    );
    let is_false = b.ins().icmp_imm(
        IntCC::Equal,
        v.raw,
        fz_runtime::fz_value::FALSE_ATOM_ID as i64,
    );
    let is_nil = b.ins().icmp_imm(
        IntCC::Equal,
        v.raw,
        fz_runtime::fz_value::NIL_ATOM_ID as i64,
    );
    let false_or_nil = b.ins().bor(is_false, is_nil);
    let atom_falsey = b.ins().band(is_atom, false_or_nil);
    b.ins().bxor_imm(atom_falsey, 1)
}

fn emit_typed_eq_cmp(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    let Some(fref) = ctx.value_eq_typed_fref else {
        let kind_eq = b.ins().icmp(IntCC::Equal, lhs.kind, rhs.kind);
        let raw_eq = b.ins().icmp(IntCC::Equal, lhs.raw, rhs.raw);
        return Ok(b.ins().band(kind_eq, raw_eq));
    };
    let call = b.ins().call(fref, &[lhs.raw, lhs.kind, rhs.raw, rhs.kind]);
    let eq = b.inst_results(call)[0];
    Ok(b.ins().icmp_imm(IntCC::NotEqual, eq, 0))
}

fn emit_typed_eq_branch(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let cmp = emit_typed_eq_cmp(b, ctx, lhs, rhs)?;
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

fn emit_not_matcher_map_miss(b: &mut FunctionBuilder<'_>, value: ReceiveValue) -> ir::Value {
    let kind64 = b.ins().uextend(types::I64, value.kind);
    b.ins().icmp_imm(
        IntCC::NotEqual,
        kind64,
        fz_runtime::fz_value::ValueKind::NULL.tag() as i64,
    )
}

fn emit_map_kind_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ir::Value,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = ctx.map_is_map_fref else {
        return Err(CodegenError::new(
            "MapKind matcher test requires fz_map_is_map",
        ));
    };
    let inst = b.ins().call(fref, &[val]);
    let ok = b.inst_results(inst)[0];
    let zero = b.ins().iconst(types::I8, 0);
    let cmp = b.ins().icmp(IntCC::NotEqual, ok, zero);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

/// Chain of equality / load checks that verifies `val` is a tuple of
/// the given arity. Branches to `match_b` on success, `next_b` on any
/// mismatch. Mirrors `compile_tuple_shape` but parameterised on match
/// vs miss target blocks.
fn emit_tuple_arity_test(
    b: &mut FunctionBuilder<'_>,
    tuple_schema_ids: &HashMap<usize, u32>,
    val: ir::Value,
    arity: usize,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let expected_schema_id = *tuple_schema_ids.get(&arity).ok_or_else(|| {
        CodegenError::new(format!(
            "matcher tuple arity {} not pre-registered (compile() walk missed it?)",
            arity
        ))
    })?;

    // tag == TAG_STRUCT
    let tag = b.ins().band_imm(val, VRX_TAG_MASK);
    let struct_tag = b.ins().iconst(types::I64, VRX_TAG_STRUCT);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp(IntCC::Equal, tag, struct_tag);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    // schema == expected_schema_id
    let addr = vrx_ptr_addr(b, val);
    let schema = b.ins().load(types::I32, MemFlags::trusted(), addr, 0);
    let schema_want = b.ins().iconst(types::I32, expected_schema_id as i64);
    let cmp4 = b.ins().icmp(IntCC::Equal, schema, schema_want);
    b.ins().brif(cmp4, match_b, &[], next_b, &[]);
    Ok(())
}

fn collect_binary_literals_in_matcher(matcher: &Matcher, out: &mut Vec<Vec<u8>>) {
    for key in &matcher.prepared_keys {
        collect_binary_literals_in_const(key, out);
    }
    for node in &matcher.nodes {
        match node {
            MatcherNode::Switch { cases, .. } => {
                for (key, _) in cases {
                    if let crate::matcher::SwitchKey::Utf8Binary(bytes) = key {
                        out.push(bytes.clone());
                    }
                }
            }
            MatcherNode::Test { test, .. } => collect_binary_literals_in_test(test, out),
            MatcherNode::Guard { expr, .. } => collect_binary_literals_in_guard(expr, out),
            MatcherNode::Fail { .. } | MatcherNode::Leaf(_) => {}
        }
    }
}

fn collect_binary_literals_in_guard(expr: &crate::matcher::GuardExpr, out: &mut Vec<Vec<u8>>) {
    use crate::matcher::GuardExpr;
    match expr {
        GuardExpr::Const(c) => collect_binary_literals_in_const(c, out),
        GuardExpr::Unary { expr, .. } => collect_binary_literals_in_guard(expr, out),
        GuardExpr::Binary { lhs, rhs, .. } => {
            collect_binary_literals_in_guard(lhs, out);
            collect_binary_literals_in_guard(rhs, out);
        }
        GuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_binary_literals_in_guard(input, out);
            }
            collect_binary_literals_in_matcher(&dispatch.matcher, out);
            for body in &dispatch.bodies {
                collect_binary_literals_in_guard(body, out);
            }
        }
        GuardExpr::Subject(_) | GuardExpr::Pinned(_) => {}
    }
}

fn collect_binary_literals_in_const(value: &MatcherConst, out: &mut Vec<Vec<u8>>) {
    if let MatcherConst::Utf8Binary(bytes) = value {
        out.push(bytes.clone());
    }
}

fn collect_binary_literals_in_test(test: &MatcherTest, out: &mut Vec<Vec<u8>>) {
    match test {
        MatcherTest::EqConst {
            value: MatcherConst::Utf8Binary(bytes),
            ..
        } => out.push(bytes.clone()),
        MatcherTest::MapHasKey {
            key: MatcherConst::Utf8Binary(bytes),
            ..
        } => out.push(bytes.clone()),
        MatcherTest::Bitstring { .. }
        | MatcherTest::EqConst { .. }
        | MatcherTest::EqPinned { .. }
        | MatcherTest::TupleArity { .. }
        | MatcherTest::ListCons { .. }
        | MatcherTest::MapKind { .. }
        | MatcherTest::MapHasKey { .. }
        | MatcherTest::Type { .. } => {}
    }
}

/// fz-puj.45 (X4) — emit the call sequence that compares `val` against a
/// constant byte literal via `fz_matcher_eq_bytes`. Branches to
/// `match_b` when the helper returns 1, `next_b` when it returns 0.
/// Errors when the runtime helper isn't linked (unit-test mode).
fn emit_binary_literal_test(
    b: &mut FunctionBuilder<'_>,
    binary_data_gvs: &HashMap<Vec<u8>, ir::GlobalValue>,
    matcher_eq_bytes_fref: Option<ir::FuncRef>,
    val: ir::Value,
    bytes: &[u8],
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = matcher_eq_bytes_fref else {
        return Err(CodegenError::new(
            "Pattern::Binary in receive matcher requires fz_matcher_eq_bytes; \
             runtime not linked in this context (fz-puj.45)",
        ));
    };
    let gv = binary_data_gvs.get(bytes).ok_or_else(|| {
        CodegenError::new(format!(
            "Binary literal of {} bytes missing pre-declared .data symbol (fz-puj.45)",
            bytes.len()
        ))
    })?;
    let bytes_ptr = b.ins().symbol_value(types::I64, *gv);
    let byte_len = b.ins().iconst(types::I64, bytes.len() as i64);
    let inst = b.ins().call(fref, &[val, bytes_ptr, byte_len]);
    let res = b.inst_results(inst)[0];
    let zero = b.ins().iconst(types::I32, 0);
    let cmp = b.ins().icmp(IntCC::NotEqual, res, zero);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

/// fz-puj.44 (X3) — verify `val` is a List cons cell. New strict list
/// cells are headerless and carried by the `TAG_LIST` low nibble, so this
/// routes through the runtime predicate instead of reading a prefix kind.
fn emit_list_cons_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ir::Value,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = ctx.list_is_cons_fref else {
        return Err(CodegenError::new(
            "ListCons matcher test requires fz_list_is_cons",
        ));
    };
    let inst = b.ins().call(fref, &[val]);
    let ok = b.inst_results(inst)[0];
    let zero = b.ins().iconst(types::I8, 0);
    let cmp = b.ins().icmp(IntCC::NotEqual, ok, zero);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp as AstBinOp, Expr as AstExpr, Pattern as AstPattern, Spanned};
    use crate::diag::Span;
    use crate::fz_ir::{FnId, ReceiveClause, Var};
    use cranelift_codegen::settings::{self, Configurable};
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::Module as CraneliftModule;
    use fz_runtime::fz_value::{ValueKind, ValueRoot, ValueSlot};
    use fz_runtime::heap::{Schema, SchemaRegistry};
    use fz_runtime::process::{CurrentProcessGuard, Process, current_process};
    use std::cell::RefCell;
    use std::rc::Rc;

    fn make_jit() -> (JITModule, FunctionBuilderContext) {
        let isa_builder = cranelift_native::builder().expect("native isa");
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "none").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("isa finish");
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        builder.symbol(
            "fz_struct_get_field_ref",
            fz_runtime::ir_runtime::fz_struct_get_field_ref as *const u8,
        );
        (JITModule::new(builder), FunctionBuilderContext::new())
    }

    type MatcherAbi = extern "C" fn(u64, u8, *const ValueRoot, *mut ValueRoot) -> u32;

    fn empty_module() -> Module {
        let mut m = Module::default();
        m.atom_names.push("nil".into());
        m.atom_names.push("true".into());
        m.atom_names.push("false".into());
        m
    }

    fn sp<T>(node: T) -> Spanned<T> {
        Spanned::dummy(node)
    }

    fn clause_meta(bound_names: Vec<&str>) -> ReceiveClause {
        ReceiveClause {
            bound_names: bound_names.into_iter().map(str::to_string).collect(),
            guard: None,
            body: FnId(0),
            span: Span::DUMMY,
        }
    }

    fn matcher_from_rows(
        rows: Vec<(AstPattern, Option<Spanned<AstExpr>>)>,
    ) -> crate::matcher::Matcher {
        let pattern_matrix = crate::pattern_matrix::PatternMatrix {
            subjects: vec![Var(0)],
            rows: rows
                .into_iter()
                .enumerate()
                .map(|(i, (pattern, guard))| crate::pattern_matrix::Row {
                    patterns: vec![sp(pattern)],
                    preconditions: Vec::new(),
                    bindings: Vec::new(),
                    guard,
                    body_id: i as crate::pattern_matrix::BodyId,
                })
                .collect(),
        };
        crate::pattern_matrix::compile_pattern_matrix(pattern_matrix).expect("compile matcher")
    }

    fn finalize_and_get(mut jmod: JITModule, fid: FuncId) -> MatcherAbi {
        jmod.finalize_definitions().expect("finalize");
        let addr = jmod.get_finalized_function(fid);
        Box::leak(Box::new(jmod));
        unsafe { std::mem::transmute(addr) }
    }

    fn build_matcher_fn(
        jmod: &mut JITModule,
        fbctx: &mut FunctionBuilderContext,
        fz_module: &Module,
        tuple_schemas: &HashMap<usize, u32>,
        pinned: &[(String, Var)],
        clauses: &[ReceiveClause],
        matcher: &Matcher,
        name: &str,
    ) -> MatcherAbi {
        let fid = declare_matcher(jmod, name).expect("declare matcher");
        let mut sig = jmod.make_signature();
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I32));
        sig.returns.push(AbiParam::new(types::I64));
        let struct_get_field_id = jmod
            .declare_function("fz_struct_get_field_ref", Linkage::Import, &sig)
            .expect("declare fz_struct_get_field_ref");
        emit_matcher_body_from_matcher(
            jmod,
            fbctx,
            fid,
            fz_module,
            tuple_schemas,
            pinned,
            clauses,
            matcher,
            None,
            None,
            None,
            None,
            None,
            None,
            None,
            Some(struct_get_field_id),
            None,
            None,
            None,
        )
        .expect("emit cached matcher");
        finalize_and_get(std::mem::replace(jmod, make_jit().0), fid)
    }

    #[test]
    fn cached_matcher_int_literal_hits_only_exact_tagged_value() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned = Vec::new();
        let clauses = vec![clause_meta(vec![])];
        let matcher = matcher_from_rows(vec![(AstPattern::Int(42), None)]);
        let f = build_matcher_fn(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            &matcher,
            "cached_matcher_int_42",
        );
        let pin: [ValueRoot; 0] = [];
        let mut out: [ValueRoot; 0] = [];
        assert_eq!(
            f(
                42,
                fz_runtime::fz_value::ValueKind::INT.tag(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            1
        );
        assert_eq!(
            f(
                41,
                fz_runtime::fz_value::ValueKind::INT.tag(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            0
        );
    }

    #[test]
    fn cached_matcher_var_writes_input_to_out_slot_zero() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned = Vec::new();
        let clauses = vec![clause_meta(vec!["x"])];
        let matcher = matcher_from_rows(vec![(AstPattern::Var("x".into()), None)]);
        let f = build_matcher_fn(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            &matcher,
            "cached_matcher_var_x",
        );
        let pin: [ValueRoot; 0] = [];
        let mut out = [ValueRoot::new(0, ValueKind::NULL)];
        let msg = 7;
        assert_eq!(
            f(msg, ValueKind::INT.tag(), pin.as_ptr(), out.as_mut_ptr()),
            1
        );
        assert_eq!(out[0], ValueRoot::new(msg as i64 as u64, ValueKind::INT));
    }

    #[test]
    fn cached_matcher_guard_falls_through_when_false() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned = Vec::new();
        let clauses = vec![clause_meta(vec!["x"]), clause_meta(vec![])];
        let guard = sp(AstExpr::BinOp(
            AstBinOp::Gt,
            Box::new(sp(AstExpr::Var("x".into()))),
            Box::new(sp(AstExpr::Int(10))),
        ));
        let matcher = matcher_from_rows(vec![
            (AstPattern::Var("x".into()), Some(guard)),
            (AstPattern::Wildcard, None),
        ]);
        let f = build_matcher_fn(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            &matcher,
            "cached_matcher_guard_gt",
        );
        let pin: [ValueRoot; 0] = [];
        let mut out = [ValueRoot::new(0, ValueKind::NULL)];
        assert_eq!(
            f(11, ValueKind::INT.tag(), pin.as_ptr(), out.as_mut_ptr()),
            1
        );
        assert_eq!(out[0], ValueRoot::new(11, ValueKind::INT));
        assert_eq!(
            f(9, ValueKind::INT.tag(), pin.as_ptr(), out.as_mut_ptr()),
            2
        );
    }

    #[test]
    fn cached_matcher_guard_reads_pinned_capture() {
        let (mut jmod, mut fbctx) = make_jit();
        let m = empty_module();
        let tuple_ids = HashMap::new();
        let pinned = vec![("limit".to_string(), Var(0))];
        let clauses = vec![clause_meta(vec![]), clause_meta(vec![])];
        let guard = sp(AstExpr::BinOp(
            AstBinOp::Eq,
            Box::new(sp(AstExpr::Var("limit".into()))),
            Box::new(sp(AstExpr::Int(9))),
        ));
        let matcher = matcher_from_rows(vec![
            (AstPattern::Wildcard, Some(guard)),
            (AstPattern::Wildcard, None),
        ]);
        let f = build_matcher_fn(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            &matcher,
            "cached_matcher_guard_pinned",
        );
        let mut out: [ValueRoot; 0] = [];
        let pin_9 = [ValueRoot::new(9, ValueKind::INT)];
        let pin_8 = [ValueRoot::new(8, ValueKind::INT)];
        assert_eq!(
            f(
                0xfeed,
                ValueKind::INT.tag(),
                pin_9.as_ptr(),
                out.as_mut_ptr()
            ),
            1
        );
        assert_eq!(
            f(
                0xfeed,
                ValueKind::INT.tag(),
                pin_8.as_ptr(),
                out.as_mut_ptr()
            ),
            2
        );
    }

    #[test]
    fn cached_matcher_tuple_with_atom_pinned_var_matches_arrived_message() {
        let (mut jmod, mut fbctx) = make_jit();
        let mut m = empty_module();
        m.atom_names.push("reply".into());

        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        let mut process = Box::new(Process::new(schemas));
        let _guard = CurrentProcessGuard::install(process.as_mut() as *mut Process);
        let tuple_schema_id = current_process()
            .heap
            .register_schema(Schema::tuple_of_arity(3));
        let mut tuple_ids = HashMap::new();
        tuple_ids.insert(3, tuple_schema_id);

        let pinned = vec![("ref".to_string(), Var(0))];
        let clauses = vec![clause_meta(vec!["v"])];
        let pat = AstPattern::Tuple(vec![
            sp(AstPattern::Atom("reply".into())),
            sp(AstPattern::Pinned("ref".into())),
            sp(AstPattern::Var("v".into())),
        ]);
        let matcher = matcher_from_rows(vec![(pat, None)]);
        let f = build_matcher_fn(
            &mut jmod,
            &mut fbctx,
            &m,
            &tuple_ids,
            &pinned,
            &clauses,
            &matcher,
            "cached_matcher_tuple_reply",
        );

        let tuple_p = current_process().heap.alloc_struct(tuple_schema_id);
        current_process()
            .heap
            .write_field_slot(tuple_p, 0, ValueSlot::atom(3));
        current_process()
            .heap
            .write_field_slot(tuple_p, 8, ValueSlot::int(170));
        current_process()
            .heap
            .write_field_slot(tuple_p, 16, ValueSlot::int(23));

        let pin = [ValueRoot::new(170, ValueKind::INT)];
        let mut out = [ValueRoot::new(0, ValueKind::NULL)];
        let val = (tuple_p as u64) | VRX_TAG_STRUCT as u64;
        assert_eq!(
            f(val, ValueKind::STRUCT.tag(), pin.as_ptr(), out.as_mut_ptr()),
            1
        );
        assert_eq!(out[0], ValueRoot::new(23, ValueKind::INT));

        let pin_other = [ValueRoot::new(255, ValueKind::INT)];
        let mut out2 = [ValueRoot::new(0, ValueKind::NULL)];
        assert_eq!(
            f(
                val,
                ValueKind::STRUCT.tag(),
                pin_other.as_ptr(),
                out2.as_mut_ptr()
            ),
            0
        );
    }
}
