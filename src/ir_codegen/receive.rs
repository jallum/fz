//! Selective-receive matcher fn codegen.
//!
//! Emits the leaf matcher fn for a `Term::ReceiveMatched`. The matcher
//! ABI matches `fz_runtime::park::MatcherFn` (see runtime/src/park.rs):
//!
//! ```text
//! extern "C" fn(msg_ref: u64, pinned: *const AnyValueRef, out: *mut AnyValueRef) -> u32
//! ```
//!
//! - `msg_ref`: one-word tagged candidate message.
//! - `pinned`: pointer to `AnyValueRef` entries, in the order
//!   they appear in `Term::ReceiveMatched::pinned`.
//! - `out`: caller-supplied `[AnyValueRef; bound_arity]`
//!   scratch buffer; the matcher writes the winning clause's bound-var
//!   values here.
//! - returns `0` on miss; `k > 0` is the 1-based clause index (caller
//!   indexes `clause_bodies[k-1]`).
//!
//! Production codegen consumes the cached AST-free `Matcher` attached to
//! `Term::ReceiveMatched`; it does not rebuild a PatternMatrix/Matcher from receive
//! clauses.

use crate::exec::matcher::{Matcher, MatcherConst, MatcherNode, MatcherTest};
use crate::fz_ir::{Module, ReceiveClause, Var};
use crate::ir_codegen::{CodegenError, SLOT_BYTES, emit_fn_body_stats};
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
    sig.params.push(AbiParam::new(types::I64)); // process (*mut Process)
    sig.params.push(AbiParam::new(types::I64)); // msg_ref
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

/// Optional runtime helper `FuncId`s required to emit the receive ABI
/// matcher body. Each field corresponds to a `fz_runtime` helper that the
/// matcher may call depending on the patterns it encounters; missing helpers
/// turn into specific `CodegenError`s if the matcher tries to use them.
#[derive(Clone, Copy)]
pub(crate) struct MatcherRuntimeHelpers {
    pub value_eq_typed_id: Option<FuncId>,
    pub matcher_eq_bytes_id: Option<FuncId>,
    pub matcher_map_get_id: Option<FuncId>,
    pub matcher_map_get_ref_id: Option<FuncId>,
    pub type_of_id: Option<FuncId>,
    pub unbox_int_id: Option<FuncId>,
    pub unbox_float_id: Option<FuncId>,
    pub unbox_atom_id: Option<FuncId>,
    pub struct_schema_id_ref_id: Option<FuncId>,
    pub truthy_ref_id: Option<FuncId>,
    pub box_int_for_any_id: Option<FuncId>,
    pub box_float_for_any_id: Option<FuncId>,
    pub box_atom_for_any_id: Option<FuncId>,
    pub map_is_map_id: Option<FuncId>,
    pub bs_reader_init_id: Option<FuncId>,
    pub bs_read_field_id: Option<FuncId>,
    pub struct_get_field_id: Option<FuncId>,
    pub list_is_cons_id: Option<FuncId>,
    pub list_head_id: Option<FuncId>,
    pub list_tail_id: Option<FuncId>,
}

/// Per-function-body `FuncRef`s for the runtime helpers in
/// [`MatcherRuntimeHelpers`], obtained by `declare_func_in_func` on the
/// matcher function builder.
#[derive(Clone, Copy)]
struct MatcherRuntimeRefs {
    value_eq_typed_fref: Option<ir::FuncRef>,
    matcher_eq_bytes_fref: Option<ir::FuncRef>,
    // Carried for API parity with `MatcherRuntimeHelpers::matcher_map_get_id`;
    // current emit paths use the `_ref` variant instead.
    #[allow(dead_code)]
    matcher_map_get_fref: Option<ir::FuncRef>,
    matcher_map_get_ref_fref: Option<ir::FuncRef>,
    type_of_fref: Option<ir::FuncRef>,
    unbox_int_fref: Option<ir::FuncRef>,
    unbox_float_fref: Option<ir::FuncRef>,
    unbox_atom_fref: Option<ir::FuncRef>,
    struct_schema_id_ref_fref: Option<ir::FuncRef>,
    truthy_ref_fref: Option<ir::FuncRef>,
    box_int_for_any_fref: Option<ir::FuncRef>,
    box_float_for_any_fref: Option<ir::FuncRef>,
    box_atom_for_any_fref: Option<ir::FuncRef>,
    map_is_map_fref: Option<ir::FuncRef>,
    bs_reader_init_fref: Option<ir::FuncRef>,
    bs_read_field_fref: Option<ir::FuncRef>,
    struct_get_field_fref: Option<ir::FuncRef>,
    list_is_cons_fref: Option<ir::FuncRef>,
    list_head_fref: Option<ir::FuncRef>,
    list_tail_fref: Option<ir::FuncRef>,
}

/// Emit the receive ABI matcher directly from the cached AST-free
/// [`Matcher`]. The clause slice is still used for ABI metadata
/// (`bound_names` and guard rejection), but matching control flow comes from
/// `matcher` instead of rebuilding PatternMatrix/Matcher from receive patterns.
pub(crate) fn emit_matcher_body_from_matcher<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    matcher_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    pinned: &[(String, Var)],
    clauses: &[ReceiveClause],
    matcher: &Matcher,
    helpers: &MatcherRuntimeHelpers,
) -> Result<(usize, usize), CodegenError> {
    let MatcherRuntimeHelpers {
        value_eq_typed_id,
        matcher_eq_bytes_id,
        matcher_map_get_id,
        matcher_map_get_ref_id,
        type_of_id,
        unbox_int_id,
        unbox_float_id,
        unbox_atom_id,
        struct_schema_id_ref_id,
        truthy_ref_id,
        box_int_for_any_id,
        box_float_for_any_id,
        box_atom_for_any_id,
        map_is_map_id,
        bs_reader_init_id,
        bs_read_field_id,
        struct_get_field_id,
        list_is_cons_id,
        list_head_id,
        list_tail_id,
    } = *helpers;
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
        let process = b.block_params(entry)[0];
        let msg_ref = b.block_params(entry)[1];
        let pinned_ptr = b.block_params(entry)[2];
        let out_ptr = b.block_params(entry)[3];
        let msg = receive_value_from_ref_word(b, msg_ref);

        let miss_block = b.create_block();
        let binary_data_gvs: HashMap<Vec<u8>, ir::GlobalValue> = binary_data_ids
            .iter()
            .map(|(bytes, did)| (bytes.clone(), m.declare_data_in_func(*did, b.func)))
            .collect();
        let runtime = MatcherRuntimeRefs {
            value_eq_typed_fref: value_eq_typed_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            matcher_eq_bytes_fref: matcher_eq_bytes_id
                .map(|fid| m.declare_func_in_func(fid, b.func)),
            matcher_map_get_fref: matcher_map_get_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            matcher_map_get_ref_fref: matcher_map_get_ref_id
                .map(|fid| m.declare_func_in_func(fid, b.func)),
            type_of_fref: type_of_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            unbox_int_fref: unbox_int_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            unbox_float_fref: unbox_float_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            unbox_atom_fref: unbox_atom_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            struct_schema_id_ref_fref: struct_schema_id_ref_id
                .map(|fid| m.declare_func_in_func(fid, b.func)),
            truthy_ref_fref: truthy_ref_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            box_int_for_any_fref: box_int_for_any_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            box_float_for_any_fref: box_float_for_any_id
                .map(|fid| m.declare_func_in_func(fid, b.func)),
            box_atom_for_any_fref: box_atom_for_any_id
                .map(|fid| m.declare_func_in_func(fid, b.func)),
            map_is_map_fref: map_is_map_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            bs_reader_init_fref: bs_reader_init_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            bs_read_field_fref: bs_read_field_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            struct_get_field_fref: struct_get_field_id
                .map(|fid| m.declare_func_in_func(fid, b.func)),
            list_is_cons_fref: list_is_cons_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            list_head_fref: list_head_id.map(|fid| m.declare_func_in_func(fid, b.func)),
            list_tail_fref: list_tail_id.map(|fid| m.declare_func_in_func(fid, b.func)),
        };

        let ctx = MatcherCtx {
            process,
            fz_module,
            tuple_schema_ids,
            bound_indices_per_clause: &bound_indices_per_clause,
            pinned_indices: &pinned_indices,
            pinned_ptr,
            out_ptr,
            matcher,
            inputs: vec![msg],
            binary_data_gvs: &binary_data_gvs,
            runtime,
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

#[derive(Clone, Copy)]
enum ReceiveValue {
    AnyRef(ir::Value),
    Int(ir::Value),
    Float(ir::Value),
    Atom(ir::Value),
    Null,
    EmptyList,
}

struct MatcherCtx<'a> {
    /// The running receiver's `Process*` (matcher fn's first param). Field
    /// projections that need heap state (struct fields via the schema registry,
    /// map values) pass it to their BIFs — the matcher fn is invoked from Rust,
    /// not through the pinned-register ABI, so it carries the process explicitly.
    process: ir::Value,
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    bound_indices_per_clause: &'a [HashMap<String, usize>],
    pinned_indices: &'a HashMap<String, usize>,
    pinned_ptr: ir::Value,
    out_ptr: ir::Value,
    matcher: &'a Matcher,
    inputs: Vec<ReceiveValue>,
    binary_data_gvs: &'a HashMap<Vec<u8>, ir::GlobalValue>,
    runtime: MatcherRuntimeRefs,
}

#[derive(Default, Clone)]
struct MatcherEmitState {
    values: HashMap<crate::exec::matcher::SubjectRef, ReceiveValue>,
    bitstring_fields: HashMap<(crate::exec::matcher::SubjectRef, u32), ReceiveValue>,
    direct_bindings: HashMap<String, ReceiveValue>,
}

fn emit_receive_value_ref(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(value_ref) => Ok(value_ref),
        ReceiveValue::Int(raw) => {
            let Some(fref) = ctx.runtime.box_int_for_any_fref else {
                return Err(CodegenError::new(
                    "int any-boundary requires fz_box_int_for_any",
                ));
            };
            let inst = b.ins().call(fref, &[ctx.process, raw]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Float(raw) => {
            let Some(fref) = ctx.runtime.box_float_for_any_fref else {
                return Err(CodegenError::new(
                    "float any-boundary requires fz_box_float_for_any",
                ));
            };
            let inst = b.ins().call(fref, &[ctx.process, raw]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Atom(raw) => {
            let Some(fref) = ctx.runtime.box_atom_for_any_fref else {
                return Err(CodegenError::new(
                    "atom any-boundary requires fz_box_atom_for_any",
                ));
            };
            let inst = b.ins().call(fref, &[ctx.process, raw]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Null => Ok(b.ins().iconst(types::I64, 0)),
        ReceiveValue::EmptyList => Ok(b.ins().iconst(
            types::I64,
            fz_runtime::any_value::AnyValueRef::empty_list().raw_word() as i64,
        )),
    }
}

fn receive_value_from_ref_word(_b: &mut FunctionBuilder<'_>, value_ref: ir::Value) -> ReceiveValue {
    ReceiveValue::AnyRef(value_ref)
}

fn receive_value_tag(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.type_of_fref else {
                return Err(CodegenError::new("any type test requires fz_type_of"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        ReceiveValue::Int(_) => Ok(b.ins().iconst(
            types::I8,
            fz_runtime::any_value::ValueKind::INT.tag() as i64,
        )),
        ReceiveValue::Float(_) => Ok(b.ins().iconst(
            types::I8,
            fz_runtime::any_value::ValueKind::FLOAT.tag() as i64,
        )),
        ReceiveValue::Atom(_) => Ok(b.ins().iconst(
            types::I8,
            fz_runtime::any_value::ValueKind::ATOM.tag() as i64,
        )),
        ReceiveValue::Null => Ok(b.ins().iconst(
            types::I8,
            fz_runtime::any_value::ValueKind::NULL.tag() as i64,
        )),
        ReceiveValue::EmptyList => Ok(b.ins().iconst(
            types::I8,
            fz_runtime::any_value::ValueKind::LIST.tag() as i64,
        )),
    }
}

fn receive_value_int(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Int(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.unbox_int_fref else {
                return Err(CodegenError::new("int unbox requires fz_unbox_int"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        _ => Err(CodegenError::new("expected int receive value")),
    }
}

fn receive_value_float(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Float(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.unbox_float_fref else {
                return Err(CodegenError::new("float unbox requires fz_unbox_float"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        _ => Err(CodegenError::new("expected float receive value")),
    }
}

fn receive_value_atom(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Atom(raw) => Ok(raw),
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.unbox_atom_fref else {
                return Err(CodegenError::new("atom unbox requires fz_unbox_atom"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            Ok(b.inst_results(inst)[0])
        }
        _ => Err(CodegenError::new("expected atom receive value")),
    }
}

fn value_ref_offset(idx: usize) -> i32 {
    (idx * SLOT_BYTES as usize) as i32
}

fn load_receive_value_ref(
    b: &mut FunctionBuilder<'_>,
    base: ir::Value,
    idx: usize,
) -> ReceiveValue {
    let value_ref = b
        .ins()
        .load(types::I64, MemFlags::trusted(), base, value_ref_offset(idx));
    receive_value_from_ref_word(b, value_ref)
}

fn store_receive_value_ref(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    base: ir::Value,
    idx: usize,
    value: ReceiveValue,
) -> Result<(), CodegenError> {
    let value_ref = emit_receive_value_ref(b, ctx, value)?;
    b.ins()
        .store(MemFlags::trusted(), value_ref, base, value_ref_offset(idx));
    Ok(())
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
    node_id: crate::exec::matcher::NodeId,
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
                    store_receive_value_ref(b, ctx, ctx.out_ptr, idx, val)?;
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
            let truthy = emit_truthy_cmp(b, ctx, value)?;
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
    sref: &crate::exec::matcher::SubjectRef,
    state: &mut MatcherEmitState,
) -> Result<ReceiveValue, CodegenError> {
    if let Some(v) = state.values.get(sref).copied() {
        return Ok(v);
    }
    let v = match sref {
        crate::exec::matcher::SubjectRef::Input(id) => {
            *ctx.inputs.get(id.0 as usize).ok_or_else(|| {
                CodegenError::new(format!("receive ABI matcher has no input {:?}", id))
            })?
        }
        crate::exec::matcher::SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_matcher_subject(b, ctx, tuple, state)?;
            emit_struct_get_field(b, ctx, parent, *index)?
        }
        crate::exec::matcher::SubjectRef::ListHead(list) => {
            let parent = resolve_matcher_subject(b, ctx, list, state)?;
            let Some(fref) = ctx.runtime.list_head_fref else {
                return Err(CodegenError::new(
                    "ListHead matcher projection requires fz_list_head",
                ));
            };
            let parent_ref = emit_receive_value_ref(b, ctx, parent)?;
            // fz_list_head_ref is a pure read — no process needed.
            let inst = b.ins().call(fref, &[parent_ref]);
            let out_ref = b.inst_results(inst)[0];
            receive_value_from_ref_word(b, out_ref)
        }
        crate::exec::matcher::SubjectRef::ListTail(list) => {
            let parent = resolve_matcher_subject(b, ctx, list, state)?;
            let Some(fref) = ctx.runtime.list_tail_fref else {
                return Err(CodegenError::new(
                    "ListTail matcher projection requires fz_list_tail",
                ));
            };
            let parent_ref = emit_receive_value_ref(b, ctx, parent)?;
            // fz_list_tail_ref is a pure read — no process needed.
            let inst = b.ins().call(fref, &[parent_ref]);
            let out_ref = b.inst_results(inst)[0];
            receive_value_from_ref_word(b, out_ref)
        }
        crate::exec::matcher::SubjectRef::MapValue { map, key } => {
            let map = resolve_matcher_subject(b, ctx, map, state)?;
            emit_matcher_map_get_value(b, ctx, map, key)?
        }
        crate::exec::matcher::SubjectRef::BitstringField { bitstring, index } => *state
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

fn load_pinned_matcher_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    pinned: crate::exec::matcher::PinnedId,
) -> Result<ReceiveValue, CodegenError> {
    let p = ctx
        .matcher
        .pinned
        .get(pinned.0 as usize)
        .ok_or_else(|| CodegenError::new(format!("pinned {:?} out of bounds", pinned)))?;
    if let Some(var) = p.var {
        return ctx.inputs.get(var.0 as usize).copied().ok_or_else(|| {
            CodegenError::new(format!("pinned helper input {:?} out of bounds", var))
        });
    }

    let &idx = ctx.pinned_indices.get(&p.name).ok_or_else(|| {
        CodegenError::new(format!("pinned ^{} not in matcher's pinned table", p.name))
    })?;
    Ok(load_receive_value_ref(b, ctx.pinned_ptr, idx))
}

fn emit_matcher_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    test: &MatcherTest,
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<Vec<(crate::exec::matcher::SubjectRef, ReceiveValue)>, CodegenError> {
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
            emit_tuple_arity_test(
                b,
                ctx,
                ctx.tuple_schema_ids,
                val,
                *arity as usize,
                true_b,
                false_b,
            )?;
        }
        MatcherTest::ListCons { subject } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_list_cons_test(b, ctx, val, true_b, false_b)?;
        }
        MatcherTest::MapKind { subject } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_map_kind_test(b, ctx, val, true_b, false_b)?;
        }
        MatcherTest::MapHasKey { subject, key } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let got = emit_matcher_map_get_value(b, ctx, val, key)?;
            true_values.push((crate::exec::matcher::map_value_subject(subject, key), got));
            let cmp = emit_not_matcher_map_miss(b, ctx, got)?;
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
    let Some(want) = matcher_const_value(ctx.fz_module, value)? else {
        return Ok(false);
    };
    match (want.kind, val) {
        (fz_runtime::any_value::ValueKind::INT, ReceiveValue::Int(raw)) => {
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        (fz_runtime::any_value::ValueKind::FLOAT, ReceiveValue::Float(raw)) => {
            let raw_bits = b.ins().bitcast(types::I64, MemFlags::new(), raw);
            let want_bits = b.ins().iconst(types::I64, want.raw as i64);
            let ok = b.ins().icmp(IntCC::Equal, raw_bits, want_bits);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        (fz_runtime::any_value::ValueKind::ATOM, ReceiveValue::Atom(raw)) => {
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        (fz_runtime::any_value::ValueKind::LIST, ReceiveValue::EmptyList) if want.raw == 0 => {
            b.ins().jump(match_b, &[]);
        }
        (_, ReceiveValue::AnyRef(value_ref)) => {
            emit_any_ref_const_test(b, ctx, value_ref, want, match_b, next_b)?;
        }
        _ => {
            b.ins().jump(next_b, &[]);
        }
    }
    Ok(true)
}

fn emit_any_ref_const_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value_ref: ir::Value,
    want: MatcherConstValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    if want.kind == fz_runtime::any_value::ValueKind::LIST && want.raw == 0 {
        let empty = b.ins().iconst(
            types::I64,
            fz_runtime::any_value::AnyValueRef::empty_list().raw_word() as i64,
        );
        let ok = b.ins().icmp(IntCC::Equal, value_ref, empty);
        b.ins().brif(ok, match_b, &[], next_b, &[]);
        return Ok(());
    }
    let want_tag = want.kind;
    if want_tag.is_heap() {
        b.ins().jump(next_b, &[]);
        return Ok(());
    };
    let tag = receive_value_tag(b, ctx, ReceiveValue::AnyRef(value_ref))?;
    let tag64 = b.ins().uextend(types::I64, tag);
    let type_ok = b.ins().icmp_imm(IntCC::Equal, tag64, want_tag.tag() as i64);
    let value_block = b.create_block();
    b.ins().brif(type_ok, value_block, &[], next_b, &[]);
    b.switch_to_block(value_block);
    b.seal_block(value_block);
    match want.kind {
        fz_runtime::any_value::ValueKind::INT => {
            let raw = receive_value_int(b, ctx, ReceiveValue::AnyRef(value_ref))?;
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        fz_runtime::any_value::ValueKind::FLOAT => {
            let raw = receive_value_float(b, ctx, ReceiveValue::AnyRef(value_ref))?;
            let raw_bits = b.ins().bitcast(types::I64, MemFlags::new(), raw);
            let want_bits = b.ins().iconst(types::I64, want.raw as i64);
            let ok = b.ins().icmp(IntCC::Equal, raw_bits, want_bits);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        fz_runtime::any_value::ValueKind::ATOM => {
            let raw = receive_value_atom(b, ctx, ReceiveValue::AnyRef(value_ref))?;
            let ok = b.ins().icmp_imm(IntCC::Equal, raw, want.raw as i64);
            b.ins().brif(ok, match_b, &[], next_b, &[]);
        }
        fz_runtime::any_value::ValueKind::LIST if want.raw == 0 => {
            b.ins().jump(match_b, &[]);
        }
        _ => {
            b.ins().jump(next_b, &[]);
        }
    }
    Ok(())
}

fn matcher_const_value(
    module: &Module,
    value: &MatcherConst,
) -> Result<Option<MatcherConstValue>, CodegenError> {
    Ok(match value {
        MatcherConst::Int(n) => Some(MatcherConstValue {
            raw: *n as u64,
            kind: fz_runtime::any_value::ValueKind::INT,
        }),
        MatcherConst::FloatBits(bits) => Some(MatcherConstValue {
            raw: *bits,
            kind: fz_runtime::any_value::ValueKind::FLOAT,
        }),
        MatcherConst::AtomName(name) => {
            module
                .atom_names
                .iter()
                .position(|n| n == name)
                .map(|id| MatcherConstValue {
                    raw: id as u64,
                    kind: fz_runtime::any_value::ValueKind::ATOM,
                })
        }
        MatcherConst::Bool(v) => Some(MatcherConstValue {
            raw: if *v {
                fz_runtime::any_value::TRUE_ATOM_ID as u64
            } else {
                fz_runtime::any_value::FALSE_ATOM_ID as u64
            },
            kind: fz_runtime::any_value::ValueKind::ATOM,
        }),
        MatcherConst::Nil => Some(MatcherConstValue {
            raw: fz_runtime::any_value::NIL_ATOM_ID as u64,
            kind: fz_runtime::any_value::ValueKind::ATOM,
        }),
        MatcherConst::EmptyList => Some(MatcherConstValue {
            raw: 0,
            kind: fz_runtime::any_value::ValueKind::LIST,
        }),
        MatcherConst::Utf8Binary(_) | MatcherConst::PreparedKey(_) => None,
    })
}

#[derive(Clone, Copy)]
struct MatcherConstValue {
    raw: u64,
    kind: fz_runtime::any_value::ValueKind,
}

fn matcher_const_receive_value(
    b: &mut FunctionBuilder<'_>,
    value: MatcherConstValue,
) -> ReceiveValue {
    match value.kind {
        fz_runtime::any_value::ValueKind::INT => {
            ReceiveValue::Int(b.ins().iconst(types::I64, value.raw as i64))
        }
        fz_runtime::any_value::ValueKind::FLOAT => {
            let bits = b.ins().iconst(types::I64, value.raw as i64);
            ReceiveValue::Float(b.ins().bitcast(types::F64, MemFlags::new(), bits))
        }
        fz_runtime::any_value::ValueKind::ATOM => {
            ReceiveValue::Atom(b.ins().iconst(types::I64, value.raw as i64))
        }
        fz_runtime::any_value::ValueKind::NULL => ReceiveValue::Null,
        fz_runtime::any_value::ValueKind::LIST if value.raw == 0 => ReceiveValue::EmptyList,
        _ => unreachable!("matcher constants only materialize scalar, null, or empty list values"),
    }
}

fn emit_matcher_switch_key_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    kind: &crate::exec::matcher::SwitchKind,
    key: &crate::exec::matcher::SwitchKey,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match (kind, key) {
        (
            crate::exec::matcher::SwitchKind::Atom,
            crate::exec::matcher::SwitchKey::AtomName(name),
        ) => {
            let c = MatcherConst::AtomName(name.clone());
            emit_matcher_const_test(b, ctx, val, &c, match_b, next_b)?;
            Ok(())
        }
        (crate::exec::matcher::SwitchKind::Int, crate::exec::matcher::SwitchKey::Int(n)) => {
            let c = MatcherConst::Int(*n);
            emit_matcher_const_test(b, ctx, val, &c, match_b, next_b)?;
            Ok(())
        }
        (crate::exec::matcher::SwitchKind::Bool, crate::exec::matcher::SwitchKey::Bool(v)) => {
            let c = MatcherConst::Bool(*v);
            emit_matcher_const_test(b, ctx, val, &c, match_b, next_b)?;
            Ok(())
        }
        (crate::exec::matcher::SwitchKind::Nil, crate::exec::matcher::SwitchKey::Nil) => {
            emit_matcher_const_test(b, ctx, val, &MatcherConst::Nil, match_b, next_b)?;
            Ok(())
        }
        (crate::exec::matcher::SwitchKind::ListCons, crate::exec::matcher::SwitchKey::Nil) => {
            emit_matcher_const_test(b, ctx, val, &MatcherConst::EmptyList, match_b, next_b)?;
            Ok(())
        }
        (
            crate::exec::matcher::SwitchKind::TupleArity,
            crate::exec::matcher::SwitchKey::Arity(arity),
        ) => emit_tuple_arity_test(
            b,
            ctx,
            ctx.tuple_schema_ids,
            val,
            *arity as usize,
            match_b,
            next_b,
        ),
        (
            crate::exec::matcher::SwitchKind::ListCons,
            crate::exec::matcher::SwitchKey::EmptyList,
        ) => {
            emit_matcher_const_test(b, ctx, val, &MatcherConst::EmptyList, match_b, next_b)?;
            Ok(())
        }
        (crate::exec::matcher::SwitchKind::ListCons, crate::exec::matcher::SwitchKey::Cons) => {
            emit_list_cons_test(b, ctx, val, match_b, next_b)
        }
        (
            crate::exec::matcher::SwitchKind::Float,
            crate::exec::matcher::SwitchKey::FloatBits(bits),
        ) => emit_matcher_const_test(
            b,
            ctx,
            val,
            &MatcherConst::FloatBits(*bits),
            match_b,
            next_b,
        ),
        (
            crate::exec::matcher::SwitchKind::Binary,
            crate::exec::matcher::SwitchKey::Utf8Binary(bytes),
        ) => {
            let bits = emit_receive_value_ref(b, ctx, val)?;
            emit_binary_literal_test(
                b,
                ctx.binary_data_gvs,
                ctx.runtime.matcher_eq_bytes_fref,
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
            let bits = emit_receive_value_ref(b, ctx, val)?;
            emit_binary_literal_test(
                b,
                ctx.binary_data_gvs,
                ctx.runtime.matcher_eq_bytes_fref,
                bits,
                bytes,
                match_b,
                next_b,
            )
        }
        MatcherConst::PreparedKey(_) => Err(CodegenError::new(
            "prepared heap map keys are not supported in receive ABI matcher yet",
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
        let Some(map_get_ref_fref) = ctx.runtime.matcher_map_get_ref_fref else {
            return Err(CodegenError::new(
                "Prepared map matcher key requires fz_matcher_map_get_ref",
            ));
        };
        let name = crate::exec::matcher::prepared_key_name(*index as usize);
        let &idx = ctx.pinned_indices.get(&name).ok_or_else(|| {
            CodegenError::new(format!(
                "prepared matcher key {} not in pinned table",
                index
            ))
        })?;
        let key = load_receive_value_ref(b, ctx.pinned_ptr, idx);
        let map_ref = emit_receive_value_ref(b, ctx, map)?;
        let key_ref = emit_receive_value_ref(b, ctx, key)?;
        let inst = b
            .ins()
            .call(map_get_ref_fref, &[ctx.process, map_ref, key_ref]);
        let out_ref = b.inst_results(inst)[0];
        return Ok(receive_value_from_ref_word(b, out_ref));
    }
    let Some(map_get_ref_fref) = ctx.runtime.matcher_map_get_ref_fref else {
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
    let map_ref = emit_receive_value_ref(b, ctx, map)?;
    let key_value = matcher_const_receive_value(b, key_value);
    let key_ref = emit_receive_value_ref(b, ctx, key_value)?;
    let inst = b
        .ins()
        .call(map_get_ref_fref, &[ctx.process, map_ref, key_ref]);
    let out_ref = b.inst_results(inst)[0];
    Ok(receive_value_from_ref_word(b, out_ref))
}

fn emit_bitstring_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    subject: &crate::exec::matcher::SubjectRef,
    fields: &[crate::exec::matcher::MatcherBitField],
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<(), CodegenError> {
    let Some(init_fref) = ctx.runtime.bs_reader_init_fref else {
        return Err(CodegenError::new(
            "Bitstring matcher test requires fz_bs_reader_init",
        ));
    };
    let Some(read_fref) = ctx.runtime.bs_read_field_fref else {
        return Err(CodegenError::new(
            "Bitstring matcher test requires fz_bs_read_field",
        ));
    };
    let value = resolve_matcher_subject(b, ctx, subject, state)?;
    emit_bitstring_like_guard(b, ctx, value, false_b)?;
    let value_ref = emit_receive_value_ref(b, ctx, value)?;
    let init = b.ins().call(init_fref, &[ctx.process, value_ref]);
    let mut reader = b.inst_results(init)[0];

    for (index, field) in fields.iter().enumerate() {
        let (size_present, size_value) = emit_matcher_bit_size(b, ctx, field, state)?;
        let field_spec = fz_runtime::ir_runtime::fz_bs_field_spec(
            matcher_bit_type_tag(field.ty),
            size_present,
            field.unit.unwrap_or(default_matcher_bit_unit(field.ty)),
            matcher_endian_tag(field.endian),
            field.signed as u32,
            (index + 1 == fields.len()) as u32,
        );
        let field_spec = b.ins().iconst(types::I64, field_spec as i64);
        let inst = b
            .ins()
            .call(read_fref, &[ctx.process, reader, field_spec, size_value]);
        let result = b.inst_results(inst)[0];
        let result_value = ReceiveValue::AnyRef(result);
        let ok = emit_struct_get_field(b, ctx, result_value, 0)?;
        let ok_truthy = emit_truthy_cmp(b, ctx, ok)?;
        let next_b = b.create_block();
        b.ins().brif(ok_truthy, next_b, &[], false_b, &[]);
        b.switch_to_block(next_b);
        b.seal_block(next_b);
        let extracted = emit_struct_get_field(b, ctx, result_value, 1)?;
        let next_reader = emit_struct_get_field(b, ctx, result_value, 2)?;
        reader = emit_receive_value_ref(b, ctx, next_reader)?;
        state
            .bitstring_fields
            .insert((subject.clone(), index as u32), extracted);
        for name in &field.direct_bindings {
            state.direct_bindings.insert(name.clone(), extracted);
        }
    }

    let reader_value = ReceiveValue::AnyRef(reader);
    let bit_len_value = emit_struct_get_field(b, ctx, reader_value, 1)?;
    let bit_len = receive_value_int(b, ctx, bit_len_value)?;
    let pos_value = emit_struct_get_field(b, ctx, reader_value, 2)?;
    let pos = receive_value_int(b, ctx, pos_value)?;
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
    let Some(fref) = ctx.runtime.struct_get_field_fref else {
        return Err(CodegenError::new(
            "struct field projection requires fz_struct_get_field",
        ));
    };
    let field_offset = b
        .ins()
        .iconst(types::I32, field_index as i64 * SLOT_BYTES as i64);
    let struct_ref = emit_receive_value_ref(b, ctx, struct_value)?;
    let inst = b.ins().call(fref, &[ctx.process, struct_ref, field_offset]);
    let out_ref = b.inst_results(inst)[0];
    Ok(receive_value_from_ref_word(b, out_ref))
}

fn emit_bitstring_like_guard(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    miss: ir::Block,
) -> Result<(), CodegenError> {
    let tag8 = receive_value_tag(b, ctx, val)?;
    let tag = b.ins().uextend(types::I64, tag8);
    let cont = b.create_block();
    let ptr_path = b.create_block();
    let is_strict_bs = b.ins().icmp_imm(
        IntCC::Equal,
        tag,
        fz_runtime::any_value::ValueKind::BITSTRING.tag() as i64,
    );
    let is_strict_proc = b.ins().icmp_imm(
        IntCC::Equal,
        tag,
        fz_runtime::any_value::ValueKind::PROCBIN.tag() as i64,
    );
    let is_strict = b.ins().bor(is_strict_bs, is_strict_proc);
    b.ins().brif(is_strict, cont, &[], ptr_path, &[]);
    b.switch_to_block(ptr_path);
    b.seal_block(ptr_path);
    b.ins().jump(miss, &[]);
    b.switch_to_block(cont);
    b.seal_block(cont);
    Ok(())
}

fn emit_matcher_bit_size(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    field: &crate::exec::matcher::MatcherBitField,
    state: &MatcherEmitState,
) -> Result<(u32, ir::Value), CodegenError> {
    match &field.size {
        None => Ok((0, b.ins().iconst(types::I32, 0))),
        Some(crate::exec::matcher::MatcherBitSize::Literal(n)) => {
            Ok((1, b.ins().iconst(types::I32, *n as i64)))
        }
        Some(crate::exec::matcher::MatcherBitSize::BindingName(name)) => {
            let value = state.direct_bindings.get(name).copied().ok_or_else(|| {
                CodegenError::new(format!("bitstring size binding `{}` not available", name))
            })?;
            Ok((1, strict_int_i32(b, ctx, value)?))
        }
    }
}

fn strict_int_i32(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    v: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    let raw = receive_value_int(b, ctx, v)?;
    Ok(b.ins().ireduce(types::I32, raw))
}

fn matcher_bit_type_tag(ty: crate::exec::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::exec::matcher::MatcherBitType::Integer => 0,
        crate::exec::matcher::MatcherBitType::Float => 1,
        crate::exec::matcher::MatcherBitType::Binary => 2,
        crate::exec::matcher::MatcherBitType::Bits => 3,
        crate::exec::matcher::MatcherBitType::Utf8 => 4,
        crate::exec::matcher::MatcherBitType::Utf16 => 5,
        crate::exec::matcher::MatcherBitType::Utf32 => 6,
    }
}

fn matcher_endian_tag(endian: crate::exec::matcher::MatcherEndian) -> u32 {
    match endian {
        crate::exec::matcher::MatcherEndian::Big => 0,
        crate::exec::matcher::MatcherEndian::Little => 1,
        crate::exec::matcher::MatcherEndian::Native => 2,
    }
}

fn default_matcher_bit_unit(ty: crate::exec::matcher::MatcherBitType) -> u32 {
    match ty {
        crate::exec::matcher::MatcherBitType::Integer
        | crate::exec::matcher::MatcherBitType::Float
        | crate::exec::matcher::MatcherBitType::Bits => 1,
        crate::exec::matcher::MatcherBitType::Binary => 8,
        crate::exec::matcher::MatcherBitType::Utf8
        | crate::exec::matcher::MatcherBitType::Utf16
        | crate::exec::matcher::MatcherBitType::Utf32 => 1,
    }
}

fn emit_matcher_guard_expr(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    expr: &crate::exec::matcher::GuardExpr,
    state: &mut MatcherEmitState,
) -> Result<ReceiveValue, CodegenError> {
    use crate::exec::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    Ok(match expr {
        GuardExpr::Const(c) => {
            let Some(value) = matcher_const_value(ctx.fz_module, c)? else {
                return Err(CodegenError::new(format!(
                    "guard const {:?} cannot be materialized in receive ABI matcher",
                    c
                )));
            };
            matcher_const_receive_value(b, value)
        }
        GuardExpr::Subject(subject) => resolve_matcher_subject(b, ctx, subject, state)?,
        GuardExpr::Pinned(pinned) => load_pinned_matcher_value(b, ctx, *pinned)?,
        GuardExpr::Unary { op, expr } => {
            let v = emit_matcher_guard_expr(b, ctx, expr, state)?;
            match op {
                GuardUnaryOp::Not => {
                    let truthy = emit_truthy_cmp(b, ctx, v)?;
                    emit_bool_value_from_truthy(b, truthy, true)
                }
                GuardUnaryOp::Neg => {
                    let z = b.ins().iconst(types::I64, 0);
                    let raw = receive_value_int(b, ctx, v)?;
                    let neg = b.ins().isub(z, raw);
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
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let sum = b.ins().iadd(l, r);
                    int_value(b, sum)
                }
                GuardBinOp::Sub => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let diff = b.ins().isub(l, r);
                    int_value(b, diff)
                }
                GuardBinOp::Mul => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let prod = b.ins().imul(l, r);
                    int_value(b, prod)
                }
                GuardBinOp::Div => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let quot = b.ins().sdiv(l, r);
                    int_value(b, quot)
                }
                GuardBinOp::Rem => {
                    let l = receive_value_int(b, ctx, l)?;
                    let r = receive_value_int(b, ctx, r)?;
                    let rem = b.ins().srem(l, r);
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
                GuardBinOp::Lt => emit_int_cmp_value(b, ctx, IntCC::SignedLessThan, l, r)?,
                GuardBinOp::LtEq => emit_int_cmp_value(b, ctx, IntCC::SignedLessThanOrEqual, l, r)?,
                GuardBinOp::Gt => emit_int_cmp_value(b, ctx, IntCC::SignedGreaterThan, l, r)?,
                GuardBinOp::GtEq => {
                    emit_int_cmp_value(b, ctx, IntCC::SignedGreaterThanOrEqual, l, r)?
                }
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
    dispatch: &crate::exec::matcher::GuardDispatch,
    inputs: Vec<ReceiveValue>,
) -> Result<ReceiveValue, CodegenError> {
    let done = b.create_block();
    b.append_block_param(done, types::I64);
    let ctx = MatcherCtx {
        process: parent.process,
        fz_module: parent.fz_module,
        tuple_schema_ids: parent.tuple_schema_ids,
        bound_indices_per_clause: parent.bound_indices_per_clause,
        pinned_indices: parent.pinned_indices,
        pinned_ptr: parent.pinned_ptr,
        out_ptr: parent.out_ptr,
        matcher: &dispatch.matcher,
        inputs,
        binary_data_gvs: parent.binary_data_gvs,
        runtime: parent.runtime,
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
    Ok(ReceiveValue::AnyRef(b.block_params(done)[0]))
}

fn emit_guard_dispatch_node(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    bodies: &[crate::exec::matcher::GuardExpr],
    node_id: crate::exec::matcher::NodeId,
    done: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<(), CodegenError> {
    let node = ctx.matcher.node(node_id).ok_or_else(|| {
        CodegenError::new(format!("guard dispatch node {:?} out of bounds", node_id))
    })?;
    match node {
        MatcherNode::Fail { .. } => {
            let false_value = bool_const_value(b, false);
            let false_ref = emit_receive_value_ref(b, ctx, false_value)?;
            b.ins().jump(done, &[ir::BlockArg::Value(false_ref)]);
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
            let value_ref = emit_receive_value_ref(b, ctx, value)?;
            b.ins().jump(done, &[ir::BlockArg::Value(value_ref)]);
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
            let truthy = emit_truthy_cmp(b, ctx, value)?;
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
    op: crate::exec::matcher::GuardBinOp,
    lhs: &crate::exec::matcher::GuardExpr,
    rhs: &crate::exec::matcher::GuardExpr,
    state: &mut MatcherEmitState,
) -> Result<ReceiveValue, CodegenError> {
    let lhs_value = emit_matcher_guard_expr(b, ctx, lhs, state)?;
    let lhs_truthy = emit_truthy_cmp(b, ctx, lhs_value)?;
    let rhs_b = b.create_block();
    let done_b = b.create_block();
    b.append_block_param(done_b, types::I64);

    let true_value = bool_const_value(b, true);
    let false_value = bool_const_value(b, false);
    let true_ref = emit_receive_value_ref(b, ctx, true_value)?;
    let false_ref = emit_receive_value_ref(b, ctx, false_value)?;
    match op {
        crate::exec::matcher::GuardBinOp::And => b.ins().brif(
            lhs_truthy,
            rhs_b,
            &[],
            done_b,
            &[ir::BlockArg::Value(false_ref)],
        ),
        crate::exec::matcher::GuardBinOp::Or => b.ins().brif(
            lhs_truthy,
            done_b,
            &[ir::BlockArg::Value(true_ref)],
            rhs_b,
            &[],
        ),
        _ => unreachable!("non-short-circuit guard op"),
    };

    b.switch_to_block(rhs_b);
    b.seal_block(rhs_b);
    let mut rhs_state = state.clone();
    let rhs_value = emit_matcher_guard_expr(b, ctx, rhs, &mut rhs_state)?;
    let rhs_truthy = emit_truthy_cmp(b, ctx, rhs_value)?;
    let rhs_bool = emit_bool_value_from_truthy(b, rhs_truthy, false);
    let rhs_ref = emit_receive_value_ref(b, ctx, rhs_bool)?;
    b.ins().jump(done_b, &[ir::BlockArg::Value(rhs_ref)]);

    b.switch_to_block(done_b);
    b.seal_block(done_b);
    Ok(ReceiveValue::AnyRef(b.block_params(done_b)[0]))
}

fn int_value(_b: &mut FunctionBuilder<'_>, raw: ir::Value) -> ReceiveValue {
    ReceiveValue::Int(raw)
}

fn bool_const_value(b: &mut FunctionBuilder<'_>, value: bool) -> ReceiveValue {
    let raw = if value {
        fz_runtime::any_value::TRUE_ATOM_ID
    } else {
        fz_runtime::any_value::FALSE_ATOM_ID
    };
    ReceiveValue::Atom(b.ins().iconst(types::I64, raw as i64))
}

fn emit_int_cmp_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    cc: IntCC,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ReceiveValue, CodegenError> {
    let lhs = receive_value_int(b, ctx, lhs)?;
    let rhs = receive_value_int(b, ctx, rhs)?;
    let cmp = b.ins().icmp(cc, lhs, rhs);
    Ok(emit_bool_value(b, cmp))
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
        .iconst(types::I64, fz_runtime::any_value::TRUE_ATOM_ID as i64);
    let f = b
        .ins()
        .iconst(types::I64, fz_runtime::any_value::FALSE_ATOM_ID as i64);
    let raw = if invert {
        b.ins().select(truthy, f, t)
    } else {
        b.ins().select(truthy, t, f)
    };
    ReceiveValue::Atom(raw)
}

fn emit_truthy_cmp(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    v: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match v {
        ReceiveValue::AnyRef(value_ref) => {
            let Some(fref) = ctx.runtime.truthy_ref_fref else {
                return Err(CodegenError::new("any truthiness requires fz_truthy_ref"));
            };
            let inst = b.ins().call(fref, &[value_ref]);
            let truthy = b.inst_results(inst)[0];
            let zero = b.ins().iconst(types::I8, 0);
            Ok(b.ins().icmp(IntCC::NotEqual, truthy, zero))
        }
        ReceiveValue::Atom(raw) => {
            let is_false = b.ins().icmp_imm(
                IntCC::Equal,
                raw,
                fz_runtime::any_value::FALSE_ATOM_ID as i64,
            );
            let is_nil =
                b.ins()
                    .icmp_imm(IntCC::Equal, raw, fz_runtime::any_value::NIL_ATOM_ID as i64);
            let false_or_nil = b.ins().bor(is_false, is_nil);
            Ok(b.ins().bxor_imm(false_or_nil, 1))
        }
        ReceiveValue::Null => Ok(b.ins().iconst(types::I8, 0)),
        ReceiveValue::Int(_) | ReceiveValue::Float(_) | ReceiveValue::EmptyList => {
            Ok(b.ins().iconst(types::I8, 1))
        }
    }
}

fn emit_typed_eq_cmp(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    lhs: ReceiveValue,
    rhs: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match (lhs, rhs) {
        (ReceiveValue::Int(a), ReceiveValue::Int(bv)) => {
            return Ok(b.ins().icmp(IntCC::Equal, a, bv));
        }
        (ReceiveValue::Float(a), ReceiveValue::Float(bv)) => {
            let a = b.ins().bitcast(types::I64, MemFlags::new(), a);
            let bv = b.ins().bitcast(types::I64, MemFlags::new(), bv);
            return Ok(b.ins().icmp(IntCC::Equal, a, bv));
        }
        (ReceiveValue::Atom(a), ReceiveValue::Atom(bv)) => {
            return Ok(b.ins().icmp(IntCC::Equal, a, bv));
        }
        (ReceiveValue::Null, ReceiveValue::Null)
        | (ReceiveValue::EmptyList, ReceiveValue::EmptyList) => {
            return Ok(b.ins().iconst(types::I8, 1));
        }
        _ => {}
    }
    let Some(fref) = ctx.runtime.value_eq_typed_fref else {
        return Err(CodegenError::new(
            "mixed/ref equality requires fz_value_eq_ref",
        ));
    };
    let lhs_ref = emit_receive_value_ref(b, ctx, lhs)?;
    let rhs_ref = emit_receive_value_ref(b, ctx, rhs)?;
    let call = b.ins().call(fref, &[ctx.process, lhs_ref, rhs_ref]);
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

fn emit_not_matcher_map_miss(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    value: ReceiveValue,
) -> Result<ir::Value, CodegenError> {
    match value {
        ReceiveValue::Null => Ok(b.ins().iconst(types::I8, 0)),
        ReceiveValue::AnyRef(_) => {
            let tag = receive_value_tag(b, ctx, value)?;
            let tag64 = b.ins().uextend(types::I64, tag);
            Ok(b.ins().icmp_imm(
                IntCC::NotEqual,
                tag64,
                fz_runtime::any_value::ValueKind::NULL.tag() as i64,
            ))
        }
        _ => Ok(b.ins().iconst(types::I8, 1)),
    }
}

fn emit_map_kind_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = ctx.runtime.map_is_map_fref else {
        return Err(CodegenError::new(
            "MapKind matcher test requires fz_map_is_map",
        ));
    };
    let map_ref = emit_receive_value_ref(b, ctx, val)?;
    let inst = b.ins().call(fref, &[map_ref]);
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
    ctx: &MatcherCtx<'_>,
    tuple_schema_ids: &HashMap<usize, u32>,
    val: ReceiveValue,
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

    let tag = receive_value_tag(b, ctx, val)?;
    let tag64 = b.ins().uextend(types::I64, tag);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp_imm(
        IntCC::Equal,
        tag64,
        fz_runtime::any_value::ValueKind::STRUCT.tag() as i64,
    );
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    let Some(fref) = ctx.runtime.struct_schema_id_ref_fref else {
        return Err(CodegenError::new(
            "tuple arity matcher test requires fz_struct_schema_id_ref",
        ));
    };
    let struct_ref = emit_receive_value_ref(b, ctx, val)?;
    let inst = b.ins().call(fref, &[struct_ref]);
    let schema = b.inst_results(inst)[0];
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
                    if let crate::exec::matcher::SwitchKey::Utf8Binary(bytes) = key {
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

fn collect_binary_literals_in_guard(
    expr: &crate::exec::matcher::GuardExpr,
    out: &mut Vec<Vec<u8>>,
) {
    use crate::exec::matcher::GuardExpr;
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

/// Emit the call sequence that compares `val` against a constant byte
/// literal via `fz_matcher_eq_bytes`. Branches to `match_b` when the
/// helper returns 1, `next_b` when it returns 0. Errors when the runtime
/// helper isn't linked (unit-test mode).
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
             runtime not linked in this context",
        ));
    };
    let gv = binary_data_gvs.get(bytes).ok_or_else(|| {
        CodegenError::new(format!(
            "Binary literal of {} bytes missing pre-declared .data symbol",
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

/// Verify `val` is a List cons cell. Strict list cells are headerless
/// and carried by the `TAG_LIST` low nibble, so this routes through the
/// runtime predicate instead of reading a prefix kind.
fn emit_list_cons_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ReceiveValue,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let Some(fref) = ctx.runtime.list_is_cons_fref else {
        return Err(CodegenError::new(
            "ListCons matcher test requires fz_list_is_cons",
        ));
    };
    let list_ref = emit_receive_value_ref(b, ctx, val)?;
    let inst = b.ins().call(fref, &[list_ref]);
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
    use fz_runtime::any_value::AnyValue;
    use fz_runtime::any_value::AnyValueRef;
    use fz_runtime::any_value::ValueKind;
    use fz_runtime::heap::{Schema, SchemaRegistry};
    use fz_runtime::process::Process;
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
        // Production symbol registration — keep the test linker in lockstep with
        // the real JIT so signatures can't drift (tests use production code).
        crate::ir_codegen::backend::register_runtime_symbols(&mut builder);
        (JITModule::new(builder), FunctionBuilderContext::new())
    }

    type MatcherAbi = extern "C" fn(*mut Process, u64, *const AnyValueRef, *mut AnyValueRef) -> u32;

    /// Stand up a fresh process for a matcher test. The caller holds the box
    /// and threads `process.as_mut()` to the matcher fn (its 1st arg) and to
    /// `int_ref` — exactly as production threads the process. No ambient state.
    fn new_process() -> Box<Process> {
        let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
        Box::new(Process::new(schemas))
    }

    /// Box a scalar onto `proc`'s heap via the production BIF — same call the
    /// compiled/interpreted any-boundary uses.
    fn int_ref(proc: *mut Process, value: i64) -> AnyValueRef {
        let raw = fz_runtime::ir_runtime::fz_box_int_for_any(proc, value);
        AnyValueRef::from_raw_word(raw).expect("int ref")
    }

    fn struct_ref(addr: *mut u8) -> AnyValueRef {
        AnyValueRef::from_heap_object(ValueKind::STRUCT, addr.cast_const()).expect("struct ref")
    }

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
            ident: crate::fz_ir::CallsiteIdent::synthetic(),
            bound_names: bound_names.into_iter().map(str::to_string).collect(),
            guard: None,
            body: FnId(0),
            span: Span::DUMMY,
        }
    }

    fn matcher_from_rows(
        rows: Vec<(AstPattern, Option<Spanned<AstExpr>>)>,
    ) -> crate::exec::matcher::Matcher {
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
        // Declare the runtime symbols from the production source so the matcher's
        // helper signatures can never drift from the real pipeline (tests use
        // production code). Mirrors the MatcherRuntimeHelpers wiring in driver.rs.
        let runtime = crate::ir_codegen::runtime_syms::declare_runtime_symbols(jmod)
            .expect("declare runtime symbols");
        emit_matcher_body_from_matcher(
            jmod,
            fbctx,
            fid,
            fz_module,
            tuple_schemas,
            pinned,
            clauses,
            matcher,
            &MatcherRuntimeHelpers {
                value_eq_typed_id: Some(runtime.value_eq_ref_id),
                matcher_eq_bytes_id: Some(runtime.matcher_eq_bytes_id),
                matcher_map_get_id: Some(runtime.matcher_map_get_id),
                matcher_map_get_ref_id: Some(runtime.matcher_map_get_ref_id),
                type_of_id: Some(runtime.type_of_id),
                unbox_int_id: Some(runtime.unbox_int_id),
                unbox_float_id: Some(runtime.unbox_float_id),
                unbox_atom_id: Some(runtime.unbox_atom_id),
                struct_schema_id_ref_id: Some(runtime.struct_schema_id_ref_id),
                truthy_ref_id: Some(runtime.truthy_ref_id),
                box_int_for_any_id: Some(runtime.box_int_for_any_id),
                box_float_for_any_id: Some(runtime.box_float_for_any_id),
                box_atom_for_any_id: Some(runtime.box_atom_for_any_id),
                map_is_map_id: Some(runtime.map_is_map_id),
                bs_reader_init_id: Some(runtime.bs_reader_init_ref_id),
                bs_read_field_id: Some(runtime.bs_read_field_ref_id),
                struct_get_field_id: Some(runtime.struct_get_field_id),
                list_is_cons_id: Some(runtime.list_is_cons_id),
                list_head_id: Some(runtime.list_head_fallback_id),
                list_tail_id: Some(runtime.list_tail_fallback_id),
            },
        )
        .expect("emit cached matcher");
        finalize_and_get(std::mem::replace(jmod, make_jit().0), fid)
    }

    #[test]
    fn cached_matcher_int_literal_hits_only_exact_tagged_value() {
        let mut process = new_process();
        let pp = process.as_mut() as *mut Process;
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
        let pin: [AnyValueRef; 0] = [];
        let mut out: [AnyValueRef; 0] = [];
        assert_eq!(
            f(
                pp,
                int_ref(pp, 42).raw_word(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            1
        );
        assert_eq!(
            f(
                pp,
                int_ref(pp, 41).raw_word(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            0
        );
    }

    #[test]
    fn cached_matcher_var_writes_input_to_out_slot_zero() {
        let mut process = new_process();
        let pp = process.as_mut() as *mut Process;
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
        let pin: [AnyValueRef; 0] = [];
        let mut out = [AnyValueRef::null()];
        let msg = 7;
        assert_eq!(
            f(
                pp,
                int_ref(pp, msg).raw_word(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            1
        );
        assert_eq!(out[0].load_int().expect("out int"), msg);
    }

    #[test]
    fn cached_matcher_guard_falls_through_when_false() {
        let mut process = new_process();
        let pp = process.as_mut() as *mut Process;
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
        let pin: [AnyValueRef; 0] = [];
        let mut out = [AnyValueRef::null()];
        assert_eq!(
            f(
                pp,
                int_ref(pp, 11).raw_word(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            1
        );
        assert_eq!(out[0].load_int().expect("out int"), 11);
        assert_eq!(
            f(
                pp,
                int_ref(pp, 9).raw_word(),
                pin.as_ptr(),
                out.as_mut_ptr()
            ),
            2
        );
    }

    #[test]
    fn cached_matcher_guard_reads_pinned_capture() {
        let mut process = new_process();
        let pp = process.as_mut() as *mut Process;
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
        let mut out: [AnyValueRef; 0] = [];
        let pin_9 = [int_ref(pp, 9)];
        let pin_8 = [int_ref(pp, 8)];
        assert_eq!(
            f(
                pp,
                int_ref(pp, 0).raw_word(),
                pin_9.as_ptr(),
                out.as_mut_ptr()
            ),
            1
        );
        assert_eq!(
            f(
                pp,
                int_ref(pp, 0).raw_word(),
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
        let pp = process.as_mut() as *mut Process;
        let tuple_schema_id = unsafe { &mut *pp }
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

        let tuple_p = unsafe { &mut *pp }.heap.alloc_struct(tuple_schema_id);
        let proc = unsafe { &mut *pp };
        proc.heap.write_field_slot(tuple_p, 0, AnyValue::atom(3));
        proc.heap.write_field_slot(tuple_p, 8, AnyValue::int(170));
        proc.heap.write_field_slot(tuple_p, 16, AnyValue::int(23));

        let pin = [int_ref(pp, 170)];
        let mut out = [AnyValueRef::null()];
        let val = struct_ref(tuple_p);
        assert_eq!(f(pp, val.raw_word(), pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0].load_int().expect("out int"), 23);

        let pin_other = [int_ref(pp, 255)];
        let mut out2 = [AnyValueRef::null()];
        assert_eq!(
            f(pp, val.raw_word(), pin_other.as_ptr(), out2.as_mut_ptr()),
            0
        );
    }
}
