//! fz-70q (B3) — selective-receive matcher fn codegen.
//!
//! Emits the leaf matcher fn for a `Term::ReceiveMatched`. The matcher
//! ABI matches `fz_runtime::park::MatcherFn` (see runtime/src/park.rs):
//!
//! ```text
//! extern "C" fn(msg: u64, pinned: *const u64, out: *mut u64) -> u32
//! ```
//!
//! - `msg`: candidate message (raw FzValue bits).
//! - `pinned`: pointer to `[u64; n_pinned]` with each `^name`'s value
//!   bits, in the order they appear in `Term::ReceiveMatched::pinned`.
//! - `out`: caller-supplied `[u64; bound_arity]` scratch buffer; the
//!   matcher writes the winning clause's bound-var values here.
//! - returns `0` on miss; `k > 0` is the 1-based clause index (caller
//!   indexes `clause_bodies[k-1]`).
//!
//! Production codegen consumes the cached AST-free `Matcher` attached to
//! `Term::ReceiveMatched`; it does not rebuild a Matrix/Decision from receive
//! clauses.

use crate::fz_ir::{Module, ReceiveClause, Var};
use crate::ir_codegen::{
    CodegenError, EMPTY_LIST_BITS, HEADER_SIZE, NIL_BITS, SLOT_BYTES, TAG_ATOM, TAG_INT, TAG_MASK,
    TAG_PTR, TRUE_BITS, emit_fn_body,
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
    sig.params.push(AbiParam::new(types::I64)); // msg
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
/// `matcher` instead of rebuilding Matrix/Decision from receive patterns.
pub(crate) fn emit_matcher_body_from_matcher<M: cranelift_module::Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    matcher_id: FuncId,
    fz_module: &Module,
    tuple_schema_ids: &HashMap<usize, u32>,
    pinned: &[(String, Var)],
    clauses: &[ReceiveClause],
    matcher: &Matcher,
    matcher_eq_bytes_id: Option<FuncId>,
    matcher_map_get_id: Option<FuncId>,
) -> Result<(), CodegenError> {
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
    emit_fn_body(module, fbctx, matcher_signature(), matcher_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let msg = b.block_params(entry)[0];
        let pinned_ptr = b.block_params(entry)[1];
        let out_ptr = b.block_params(entry)[2];

        let miss_block = b.create_block();
        let binary_data_gvs: HashMap<Vec<u8>, ir::GlobalValue> = binary_data_ids
            .iter()
            .map(|(bytes, did)| (bytes.clone(), m.declare_data_in_func(*did, b.func)))
            .collect();
        let matcher_eq_bytes_fref =
            matcher_eq_bytes_id.map(|fid| m.declare_func_in_func(fid, b.func));
        let matcher_map_get_fref =
            matcher_map_get_id.map(|fid| m.declare_func_in_func(fid, b.func));

        let ctx = MatcherCtx {
            fz_module,
            tuple_schema_ids,
            bound_indices_per_clause: &bound_indices_per_clause,
            pinned_indices: &pinned_indices,
            pinned_ptr,
            out_ptr,
            matcher,
            msg,
            binary_data_gvs: &binary_data_gvs,
            matcher_eq_bytes_fref,
            matcher_map_get_fref,
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
    Ok(())
}

struct MatcherCtx<'a> {
    fz_module: &'a Module,
    tuple_schema_ids: &'a HashMap<usize, u32>,
    bound_indices_per_clause: &'a [HashMap<String, usize>],
    pinned_indices: &'a HashMap<String, usize>,
    pinned_ptr: ir::Value,
    out_ptr: ir::Value,
    matcher: &'a Matcher,
    msg: ir::Value,
    binary_data_gvs: &'a HashMap<Vec<u8>, ir::GlobalValue>,
    matcher_eq_bytes_fref: Option<ir::FuncRef>,
    matcher_map_get_fref: Option<ir::FuncRef>,
}

#[derive(Default, Clone)]
struct MatcherEmitState {
    values: HashMap<crate::matcher::SubjectRef, ir::Value>,
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
            if leaf.guard.is_some() {
                return Err(CodegenError::new(
                    "receive ABI matcher expected guards to lower into MatcherNode::Guard",
                ));
            }
            let bound = &ctx.bound_indices_per_clause[leaf.body_id as usize];
            for binding in &leaf.bindings {
                let val = resolve_matcher_subject(b, ctx, &binding.source, state)?;
                if let Some(&idx) = bound.get(&binding.name) {
                    b.ins().store(
                        MemFlags::trusted(),
                        val,
                        ctx.out_ptr,
                        (idx * SLOT_BYTES as usize) as i32,
                    );
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
            emit_matcher_test(b, ctx, test, true_b, false_b, state)?;
            b.switch_to_block(true_b);
            b.seal_block(true_b);
            let mut true_state = state.clone();
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
) -> Result<ir::Value, CodegenError> {
    if let Some(v) = state.values.get(sref).copied() {
        return Ok(v);
    }
    let v = match sref {
        crate::matcher::SubjectRef::Input(id) if id.0 == 0 => ctx.msg,
        crate::matcher::SubjectRef::Input(id) => {
            return Err(CodegenError::new(format!(
                "receive ABI matcher has no input {:?}",
                id
            )));
        }
        crate::matcher::SubjectRef::TupleField { tuple, index } => {
            let parent = resolve_matcher_subject(b, ctx, tuple, state)?;
            let off = HEADER_SIZE + (*index as i32) * SLOT_BYTES;
            b.ins().load(types::I64, MemFlags::trusted(), parent, off)
        }
        crate::matcher::SubjectRef::ListHead(list) => {
            let parent = resolve_matcher_subject(b, ctx, list, state)?;
            b.ins().load(types::I64, MemFlags::trusted(), parent, 16)
        }
        crate::matcher::SubjectRef::ListTail(list) => {
            let parent = resolve_matcher_subject(b, ctx, list, state)?;
            b.ins().load(types::I64, MemFlags::trusted(), parent, 24)
        }
        crate::matcher::SubjectRef::MapValue { map, key } => {
            let map = resolve_matcher_subject(b, ctx, map, state)?;
            emit_matcher_map_get_value(b, ctx, map, key)?
        }
        crate::matcher::SubjectRef::BitstringField { .. } => {
            return Err(CodegenError::new(
                "receive ABI matcher cannot materialize bitstring fields yet (fz-puj.50)",
            ));
        }
    };
    state.values.insert(sref.clone(), v);
    Ok(v)
}

fn emit_matcher_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    test: &MatcherTest,
    true_b: ir::Block,
    false_b: ir::Block,
    state: &mut MatcherEmitState,
) -> Result<(), CodegenError> {
    match test {
        MatcherTest::EqConst { subject, value } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_matcher_const_test(b, ctx, val, value, true_b, false_b)
        }
        MatcherTest::EqPinned { subject, pinned } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let p =
                ctx.matcher.pinned.get(pinned.0 as usize).ok_or_else(|| {
                    CodegenError::new(format!("pinned {:?} out of bounds", pinned))
                })?;
            let &idx = ctx.pinned_indices.get(&p.name).ok_or_else(|| {
                CodegenError::new(format!("pinned ^{} not in matcher's pinned table", p.name))
            })?;
            let want = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                ctx.pinned_ptr,
                (idx * SLOT_BYTES as usize) as i32,
            );
            let cmp = b.ins().icmp(IntCC::Equal, val, want);
            b.ins().brif(cmp, true_b, &[], false_b, &[]);
            Ok(())
        }
        MatcherTest::TupleArity { subject, arity } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_tuple_arity_test(
                b,
                ctx.tuple_schema_ids,
                val,
                *arity as usize,
                true_b,
                false_b,
            )
        }
        MatcherTest::ListCons { subject } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_list_cons_test(b, val, true_b, false_b)
        }
        MatcherTest::MapKind { subject } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            emit_heap_kind_test(b, val, 7, true_b, false_b);
            Ok(())
        }
        MatcherTest::MapHasKey { subject, key } => {
            let val = resolve_matcher_subject(b, ctx, subject, state)?;
            let got = emit_matcher_map_get_value(b, ctx, val, key)?;
            let nil = b.ins().iconst(types::I64, NIL_BITS);
            let cmp = b.ins().icmp(IntCC::NotEqual, got, nil);
            b.ins().brif(cmp, true_b, &[], false_b, &[]);
            Ok(())
        }
        MatcherTest::Bitstring { .. } => Err(CodegenError::new(
            "receive ABI matcher cannot emit bitstring tests yet (fz-puj.50)",
        )),
        MatcherTest::Type { .. } => Err(CodegenError::new(
            "receive ABI matcher cannot emit type tests yet",
        )),
    }
}

fn emit_matcher_switch_key_test(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    val: ir::Value,
    kind: &crate::matcher::SwitchKind,
    key: &crate::matcher::SwitchKey,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match (kind, key) {
        (crate::matcher::SwitchKind::Atom, crate::matcher::SwitchKey::AtomName(name)) => {
            let Some(bits) =
                matcher_const_bits(ctx.fz_module, &MatcherConst::AtomName(name.clone()))?
            else {
                b.ins().jump(next_b, &[]);
                return Ok(());
            };
            br_bits_eq_to_blocks(b, val, bits, match_b, next_b);
            Ok(())
        }
        (crate::matcher::SwitchKind::Int, crate::matcher::SwitchKey::Int(n)) => {
            br_bits_eq_to_blocks(b, val, ((*n as u64) << 3) | TAG_INT as u64, match_b, next_b);
            Ok(())
        }
        (crate::matcher::SwitchKind::Bool, crate::matcher::SwitchKey::Bool(v)) => {
            let bits = if *v {
                TRUE_BITS as u64
            } else {
                fz_runtime::fz_value::FALSE_BITS
            };
            br_bits_eq_to_blocks(b, val, bits, match_b, next_b);
            Ok(())
        }
        (crate::matcher::SwitchKind::Nil, crate::matcher::SwitchKey::Nil)
        | (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Nil) => {
            br_bits_eq_to_blocks(b, val, NIL_BITS as u64, match_b, next_b);
            Ok(())
        }
        (crate::matcher::SwitchKind::TupleArity, crate::matcher::SwitchKey::Arity(arity)) => {
            emit_tuple_arity_test(
                b,
                ctx.tuple_schema_ids,
                val,
                *arity as usize,
                match_b,
                next_b,
            )
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::EmptyList) => {
            br_bits_eq_to_blocks(b, val, EMPTY_LIST_BITS as u64, match_b, next_b);
            Ok(())
        }
        (crate::matcher::SwitchKind::ListCons, crate::matcher::SwitchKey::Cons) => {
            emit_list_cons_test(b, val, match_b, next_b)
        }
        (crate::matcher::SwitchKind::Float, crate::matcher::SwitchKey::FloatBits(bits)) => {
            emit_float_literal_test(b, val, *bits, match_b, next_b)
        }
        (crate::matcher::SwitchKind::Binary, crate::matcher::SwitchKey::Utf8Binary(bytes)) => {
            emit_binary_literal_test(
                b,
                ctx.binary_data_gvs,
                ctx.matcher_eq_bytes_fref,
                val,
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
    val: ir::Value,
    value: &MatcherConst,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    match value {
        MatcherConst::FloatBits(bits) => emit_float_literal_test(b, val, *bits, match_b, next_b),
        MatcherConst::Utf8Binary(bytes) => emit_binary_literal_test(
            b,
            ctx.binary_data_gvs,
            ctx.matcher_eq_bytes_fref,
            val,
            bytes,
            match_b,
            next_b,
        ),
        MatcherConst::PreparedKey(_) => Err(CodegenError::new(
            "prepared heap map keys are not supported in receive ABI matcher yet (fz-puj.54.6)",
        )),
        other => {
            let Some(bits) = matcher_const_bits(ctx.fz_module, other)? else {
                b.ins().jump(next_b, &[]);
                return Ok(());
            };
            br_bits_eq_to_blocks(b, val, bits, match_b, next_b);
            Ok(())
        }
    }
}

fn emit_matcher_map_get_value(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    map: ir::Value,
    key: &MatcherConst,
) -> Result<ir::Value, CodegenError> {
    let Some(fref) = ctx.matcher_map_get_fref else {
        return Err(CodegenError::new(
            "Map matcher test requires fz_matcher_map_get; runtime not linked in this context",
        ));
    };
    let Some(key_bits) = matcher_const_bits(ctx.fz_module, key)? else {
        return Err(CodegenError::new(format!(
            "map-pattern key {:?} cannot be materialized in receive ABI matcher",
            key
        )));
    };
    let key_v = b.ins().iconst(types::I64, key_bits as i64);
    let inst = b.ins().call(fref, &[map, key_v]);
    Ok(b.inst_results(inst)[0])
}

fn emit_matcher_guard_expr(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    expr: &crate::matcher::GuardExpr,
    state: &mut MatcherEmitState,
) -> Result<ir::Value, CodegenError> {
    use crate::matcher::{GuardBinOp, GuardExpr, GuardUnaryOp};
    Ok(match expr {
        GuardExpr::Const(c) => {
            let Some(bits) = matcher_const_bits(ctx.fz_module, c)? else {
                return Err(CodegenError::new(format!(
                    "guard const {:?} cannot be materialized in receive ABI matcher",
                    c
                )));
            };
            b.ins().iconst(types::I64, bits as i64)
        }
        GuardExpr::Subject(subject) => resolve_matcher_subject(b, ctx, subject, state)?,
        GuardExpr::Pinned(pinned) => {
            let p =
                ctx.matcher.pinned.get(pinned.0 as usize).ok_or_else(|| {
                    CodegenError::new(format!("pinned {:?} out of bounds", pinned))
                })?;
            let &idx = ctx.pinned_indices.get(&p.name).ok_or_else(|| {
                CodegenError::new(format!("pinned ^{} not in matcher's pinned table", p.name))
            })?;
            b.ins().load(
                types::I64,
                MemFlags::trusted(),
                ctx.pinned_ptr,
                (idx * SLOT_BYTES as usize) as i32,
            )
        }
        GuardExpr::Unary { op, expr } => {
            let v = emit_matcher_guard_expr(b, ctx, expr, state)?;
            match op {
                GuardUnaryOp::Not => {
                    let truthy = emit_truthy_cmp(b, v);
                    emit_bool_bits_from_truthy(b, truthy, true)
                }
                GuardUnaryOp::Neg => {
                    let i = untag_int(b, v);
                    let z = b.ins().iconst(types::I64, 0);
                    let neg = b.ins().isub(z, i);
                    tag_int(b, neg)
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
                    let li = untag_int(b, l);
                    let ri = untag_int(b, r);
                    let sum = b.ins().iadd(li, ri);
                    tag_int(b, sum)
                }
                GuardBinOp::Sub => {
                    let li = untag_int(b, l);
                    let ri = untag_int(b, r);
                    let diff = b.ins().isub(li, ri);
                    tag_int(b, diff)
                }
                GuardBinOp::Mul => {
                    let li = untag_int(b, l);
                    let ri = untag_int(b, r);
                    let prod = b.ins().imul(li, ri);
                    tag_int(b, prod)
                }
                GuardBinOp::Div => {
                    let li = untag_int(b, l);
                    let ri = untag_int(b, r);
                    let quot = b.ins().sdiv(li, ri);
                    tag_int(b, quot)
                }
                GuardBinOp::Rem => {
                    let li = untag_int(b, l);
                    let ri = untag_int(b, r);
                    let rem = b.ins().srem(li, ri);
                    tag_int(b, rem)
                }
                GuardBinOp::Eq => {
                    let cmp = b.ins().icmp(IntCC::Equal, l, r);
                    emit_bool_bits(b, cmp)
                }
                GuardBinOp::Neq => {
                    let cmp = b.ins().icmp(IntCC::NotEqual, l, r);
                    emit_bool_bits(b, cmp)
                }
                GuardBinOp::Lt => emit_int_cmp_bits(b, IntCC::SignedLessThan, l, r),
                GuardBinOp::LtEq => emit_int_cmp_bits(b, IntCC::SignedLessThanOrEqual, l, r),
                GuardBinOp::Gt => emit_int_cmp_bits(b, IntCC::SignedGreaterThan, l, r),
                GuardBinOp::GtEq => emit_int_cmp_bits(b, IntCC::SignedGreaterThanOrEqual, l, r),
                GuardBinOp::And => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
                GuardBinOp::Or => {
                    unreachable!("short-circuit guard op handled before eager operands")
                }
            }
        }
    })
}

fn emit_short_circuit_guard(
    b: &mut FunctionBuilder<'_>,
    ctx: &MatcherCtx<'_>,
    op: crate::matcher::GuardBinOp,
    lhs: &crate::matcher::GuardExpr,
    rhs: &crate::matcher::GuardExpr,
    state: &mut MatcherEmitState,
) -> Result<ir::Value, CodegenError> {
    let lhs_value = emit_matcher_guard_expr(b, ctx, lhs, state)?;
    let lhs_truthy = emit_truthy_cmp(b, lhs_value);
    let rhs_b = b.create_block();
    let done_b = b.create_block();
    b.append_block_param(done_b, types::I64);

    let true_bits = b.ins().iconst(types::I64, TRUE_BITS as i64);
    let false_bits = b
        .ins()
        .iconst(types::I64, fz_runtime::fz_value::FALSE_BITS as i64);
    match op {
        crate::matcher::GuardBinOp::And => b.ins().brif(
            lhs_truthy,
            rhs_b,
            &[],
            done_b,
            &[ir::BlockArg::Value(false_bits)],
        ),
        crate::matcher::GuardBinOp::Or => b.ins().brif(
            lhs_truthy,
            done_b,
            &[ir::BlockArg::Value(true_bits)],
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
    let rhs_bool = emit_bool_bits_from_truthy(b, rhs_truthy, false);
    b.ins().jump(done_b, &[ir::BlockArg::Value(rhs_bool)]);

    b.switch_to_block(done_b);
    b.seal_block(done_b);
    Ok(b.block_params(done_b)[0])
}

fn untag_int(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().sshr_imm(v, 3)
}

fn tag_int(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    let shifted = b.ins().ishl_imm(v, 3);
    b.ins().bor_imm(shifted, TAG_INT as i64)
}

fn emit_int_cmp_bits(
    b: &mut FunctionBuilder<'_>,
    cc: IntCC,
    lhs: ir::Value,
    rhs: ir::Value,
) -> ir::Value {
    let li = untag_int(b, lhs);
    let ri = untag_int(b, rhs);
    let cmp = b.ins().icmp(cc, li, ri);
    emit_bool_bits(b, cmp)
}

fn emit_bool_bits(b: &mut FunctionBuilder<'_>, cmp: ir::Value) -> ir::Value {
    emit_bool_bits_from_truthy(b, cmp, false)
}

fn emit_bool_bits_from_truthy(
    b: &mut FunctionBuilder<'_>,
    truthy: ir::Value,
    invert: bool,
) -> ir::Value {
    let t = b.ins().iconst(types::I64, TRUE_BITS as i64);
    let f = b
        .ins()
        .iconst(types::I64, fz_runtime::fz_value::FALSE_BITS as i64);
    if invert {
        b.ins().select(truthy, f, t)
    } else {
        b.ins().select(truthy, t, f)
    }
}

fn emit_truthy_cmp(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    let false_v = b
        .ins()
        .iconst(types::I64, fz_runtime::fz_value::FALSE_BITS as i64);
    let nil_v = b.ins().iconst(types::I64, NIL_BITS);
    let not_false = b.ins().icmp(IntCC::NotEqual, v, false_v);
    let not_nil = b.ins().icmp(IntCC::NotEqual, v, nil_v);
    b.ins().band(not_false, not_nil)
}

fn matcher_const_bits(
    fz_module: &Module,
    value: &MatcherConst,
) -> Result<Option<u64>, CodegenError> {
    Ok(match value {
        MatcherConst::Int(n) => Some(((*n as u64) << 3) | TAG_INT as u64),
        MatcherConst::AtomName(name) => fz_module
            .atom_names
            .iter()
            .position(|n| n == name)
            .map(|id| ((id as u64) << 3) | TAG_ATOM as u64),
        MatcherConst::Bool(true) => Some(TRUE_BITS as u64),
        MatcherConst::Bool(false) => Some(fz_runtime::fz_value::FALSE_BITS),
        MatcherConst::Nil => Some(NIL_BITS as u64),
        MatcherConst::EmptyList => Some(EMPTY_LIST_BITS as u64),
        MatcherConst::FloatBits(_) | MatcherConst::Utf8Binary(_) | MatcherConst::PreparedKey(_) => {
            None
        }
    })
}

fn br_bits_eq_to_blocks(
    b: &mut FunctionBuilder<'_>,
    val: ir::Value,
    bits: u64,
    match_b: ir::Block,
    next_b: ir::Block,
) {
    let want = b.ins().iconst(types::I64, bits as i64);
    let cmp = b.ins().icmp(IntCC::Equal, val, want);
    b.ins().brif(cmp, match_b, &[], next_b, &[]);
}

fn emit_heap_kind_test(
    b: &mut FunctionBuilder<'_>,
    val: ir::Value,
    kind: u16,
    match_b: ir::Block,
    next_b: ir::Block,
) {
    let tag = b.ins().band_imm(val, TAG_MASK);
    let ptr_tag = b.ins().iconst(types::I64, TAG_PTR);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp(IntCC::Equal, tag, ptr_tag);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
    let c1 = b.create_block();
    let cmp1 = b.ins().icmp(IntCC::NotEqual, val, empty);
    b.ins().brif(cmp1, c1, &[], next_b, &[]);
    b.switch_to_block(c1);
    b.seal_block(c1);

    let null = b.ins().iconst(types::I64, 0);
    let c2 = b.create_block();
    let cmp2 = b.ins().icmp(IntCC::NotEqual, val, null);
    b.ins().brif(cmp2, c2, &[], next_b, &[]);
    b.switch_to_block(c2);
    b.seal_block(c2);

    let actual = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
    let want = b.ins().iconst(types::I16, kind as i64);
    let cmp3 = b.ins().icmp(IntCC::Equal, actual, want);
    b.ins().brif(cmp3, match_b, &[], next_b, &[]);
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

    // tag == TAG_PTR
    let tag = b.ins().band_imm(val, TAG_MASK);
    let zero_tag = b.ins().iconst(types::I64, TAG_PTR);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp(IntCC::Equal, tag, zero_tag);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    // val != EMPTY_LIST_BITS
    let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
    let c1 = b.create_block();
    let cmp1 = b.ins().icmp(IntCC::NotEqual, val, empty);
    b.ins().brif(cmp1, c1, &[], next_b, &[]);
    b.switch_to_block(c1);
    b.seal_block(c1);

    // val != 0
    let null = b.ins().iconst(types::I64, 0);
    let c2 = b.create_block();
    let cmp2 = b.ins().icmp(IntCC::NotEqual, val, null);
    b.ins().brif(cmp2, c2, &[], next_b, &[]);
    b.switch_to_block(c2);
    b.seal_block(c2);

    // kind == 0 (tuple)
    let kind = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
    let kind_want = b.ins().iconst(types::I16, 0);
    let c3 = b.create_block();
    let cmp3 = b.ins().icmp(IntCC::Equal, kind, kind_want);
    b.ins().brif(cmp3, c3, &[], next_b, &[]);
    b.switch_to_block(c3);
    b.seal_block(c3);

    // schema == expected_schema_id
    let schema = b.ins().load(types::I32, MemFlags::trusted(), val, 8);
    let schema_want = b.ins().iconst(types::I32, expected_schema_id as i64);
    let cmp4 = b.ins().icmp(IntCC::Equal, schema, schema_want);
    b.ins().brif(cmp4, match_b, &[], next_b, &[]);
    Ok(())
}

/// fz-puj.46 (X5) — verify `val` is a HeapKind::Float boxed at `f64`
/// payload offset 16 and equal to `bits` at the bit level. Mirrors
/// emit_list_cons_test's tag/kind chain.
fn emit_float_literal_test(
    b: &mut FunctionBuilder<'_>,
    val: ir::Value,
    bits: u64,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let tag = b.ins().band_imm(val, TAG_MASK);
    let zero_tag = b.ins().iconst(types::I64, TAG_PTR);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp(IntCC::Equal, tag, zero_tag);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
    let c1 = b.create_block();
    let cmp1 = b.ins().icmp(IntCC::NotEqual, val, empty);
    b.ins().brif(cmp1, c1, &[], next_b, &[]);
    b.switch_to_block(c1);
    b.seal_block(c1);

    let null = b.ins().iconst(types::I64, 0);
    let c2 = b.create_block();
    let cmp2 = b.ins().icmp(IntCC::NotEqual, val, null);
    b.ins().brif(cmp2, c2, &[], next_b, &[]);
    b.switch_to_block(c2);
    b.seal_block(c2);

    // HeapHeader::kind == HeapKind::Float (= 9).
    let kind = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
    let kind_want = b.ins().iconst(types::I16, 9);
    let c3 = b.create_block();
    let cmp3 = b.ins().icmp(IntCC::Equal, kind, kind_want);
    b.ins().brif(cmp3, c3, &[], next_b, &[]);
    b.switch_to_block(c3);
    b.seal_block(c3);

    // Bit-compare the f64 payload at offset 16.
    let payload = b.ins().load(types::I64, MemFlags::trusted(), val, 16);
    let want = b.ins().iconst(types::I64, bits as i64);
    let cmp4 = b.ins().icmp(IntCC::Equal, payload, want);
    b.ins().brif(cmp4, match_b, &[], next_b, &[]);
    Ok(())
}

fn collect_binary_literals_in_matcher(matcher: &Matcher, out: &mut Vec<Vec<u8>>) {
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
    use crate::matcher::{GuardExpr, MatcherConst};
    match expr {
        GuardExpr::Const(MatcherConst::Utf8Binary(bytes)) => out.push(bytes.clone()),
        GuardExpr::Unary { expr, .. } => collect_binary_literals_in_guard(expr, out),
        GuardExpr::Binary { lhs, rhs, .. } => {
            collect_binary_literals_in_guard(lhs, out);
            collect_binary_literals_in_guard(rhs, out);
        }
        GuardExpr::Const(_) | GuardExpr::Subject(_) | GuardExpr::Pinned(_) => {}
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

/// fz-puj.44 (X3) — verify `val` is a List cons cell. Branches to
/// `match_b` only when tag == TAG_PTR, val is neither EMPTY_LIST_BITS
/// nor null, and HeapHeader::kind == HeapKind::List (= 1). On any
/// mismatch branches to `next_b`. Inside the match_b arm,
/// SubjectRef::ListHead/ListTail then project head/tail at offsets
/// 16/24 — safe because the cons-check has dominated those loads.
fn emit_list_cons_test(
    b: &mut FunctionBuilder<'_>,
    val: ir::Value,
    match_b: ir::Block,
    next_b: ir::Block,
) -> Result<(), CodegenError> {
    let tag = b.ins().band_imm(val, TAG_MASK);
    let zero_tag = b.ins().iconst(types::I64, TAG_PTR);
    let c0 = b.create_block();
    let cmp0 = b.ins().icmp(IntCC::Equal, tag, zero_tag);
    b.ins().brif(cmp0, c0, &[], next_b, &[]);
    b.switch_to_block(c0);
    b.seal_block(c0);

    let empty = b.ins().iconst(types::I64, EMPTY_LIST_BITS);
    let c1 = b.create_block();
    let cmp1 = b.ins().icmp(IntCC::NotEqual, val, empty);
    b.ins().brif(cmp1, c1, &[], next_b, &[]);
    b.switch_to_block(c1);
    b.seal_block(c1);

    let null = b.ins().iconst(types::I64, 0);
    let c2 = b.create_block();
    let cmp2 = b.ins().icmp(IntCC::NotEqual, val, null);
    b.ins().brif(cmp2, c2, &[], next_b, &[]);
    b.switch_to_block(c2);
    b.seal_block(c2);

    // HeapHeader::kind (offset 0, i16) == HeapKind::List (= 1).
    let kind = b.ins().load(types::I16, MemFlags::trusted(), val, 0);
    let kind_want = b.ins().iconst(types::I16, 1);
    let cmp3 = b.ins().icmp(IntCC::Equal, kind, kind_want);
    b.ins().brif(cmp3, match_b, &[], next_b, &[]);
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

    fn make_jit() -> (JITModule, FunctionBuilderContext) {
        let isa_builder = cranelift_native::builder().expect("native isa");
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "none").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("isa finish");
        let builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        (JITModule::new(builder), FunctionBuilderContext::new())
    }

    type MatcherAbi = extern "C" fn(u64, *const u64, *mut u64) -> u32;

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
        let matrix = crate::pattern_matrix::Matrix {
            subjects: vec![Var(0)],
            rows: rows
                .into_iter()
                .enumerate()
                .map(|(i, (pattern, guard))| crate::pattern_matrix::Row {
                    patterns: vec![sp(pattern)],
                    preconditions: Vec::new(),
                    guard,
                    body_id: i as crate::pattern_matrix::BodyId,
                })
                .collect(),
        };
        crate::pattern_matrix::compile_matcher_subset(matrix).expect("compile matcher")
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
        let pin: [u64; 0] = [];
        let mut out = [0u64; 0];
        let tagged_42: u64 = (42u64 << 3) | (TAG_INT as u64);
        let tagged_41: u64 = (41u64 << 3) | (TAG_INT as u64);
        assert_eq!(f(tagged_42, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(tagged_41, pin.as_ptr(), out.as_mut_ptr()), 0);
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
        let pin: [u64; 0] = [];
        let mut out = [0u64; 1];
        let msg = ((7u64) << 3) | (TAG_INT as u64);
        assert_eq!(f(msg, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0], msg);
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
        let pin: [u64; 0] = [];
        let mut out = [0u64; 1];
        let tagged_11 = (11u64 << 3) | (TAG_INT as u64);
        let tagged_9 = (9u64 << 3) | (TAG_INT as u64);
        assert_eq!(f(tagged_11, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0], tagged_11);
        assert_eq!(f(tagged_9, pin.as_ptr(), out.as_mut_ptr()), 2);
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
        let mut out = [0u64; 0];
        let pin_9 = [(9u64 << 3) | (TAG_INT as u64)];
        let pin_8 = [(8u64 << 3) | (TAG_INT as u64)];
        assert_eq!(f(0xfeed, pin_9.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(f(0xfeed, pin_8.as_ptr(), out.as_mut_ptr()), 2);
    }

    #[test]
    fn cached_matcher_tuple_with_atom_pinned_var_matches_arrived_message() {
        use fz_runtime::fz_value::{HeapHeader, HeapKind};

        let (mut jmod, mut fbctx) = make_jit();
        let mut m = empty_module();
        m.atom_names.push("reply".into());

        let mut tuple_ids = HashMap::new();
        tuple_ids.insert(3, 7u32);

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

        let mut buf: Box<[u64; 8]> = Box::new([0u64; 8]);
        let base = buf.as_mut_ptr() as *mut u8;
        unsafe {
            let header = HeapHeader {
                kind: HeapKind::Struct as u16,
                flags: 0,
                size_bytes: 40,
                schema_id: 7,
                _reserved: 0,
            };
            std::ptr::write(base as *mut HeapHeader, header);
            let reply_bits: u64 = (3u64 << 3) | (TAG_ATOM as u64);
            let pin_bits: u64 = 0xaa;
            let payload_bits: u64 = 0xbb;
            std::ptr::write(base.add(16) as *mut u64, reply_bits);
            std::ptr::write(base.add(24) as *mut u64, pin_bits);
            std::ptr::write(base.add(32) as *mut u64, payload_bits);
        }

        let pin = [0xaau64];
        let mut out = [0u64; 1];
        let val = base as u64;
        assert_eq!(f(val, pin.as_ptr(), out.as_mut_ptr()), 1);
        assert_eq!(out[0], 0xbb);

        let pin_other = [0xffu64];
        let mut out2 = [0u64; 1];
        assert_eq!(f(val, pin_other.as_ptr(), out2.as_mut_ptr()), 0);
    }
}
