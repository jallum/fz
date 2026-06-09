//! Per-function Cranelift body emission.

use super::*;
use crate::compiler::source::Span;
use crate::fz_ir::{Block, FnIr, PhysicalCapability, Prim, SourceInfo, Stmt, Term, Var};
use crate::ir_dce::classify_var_uses;
use crate::ir_planner::fn_types::SpecKey;
use crate::types::{ClosureTypes, Ty, Types};
use cranelift_codegen::{
    Context,
    ir::{self, InstBuilder, types},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use fz_runtime::heap::Schema;
use std::collections::{HashMap, HashSet};

pub(crate) fn compile_fn<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    jmod: &mut M,
    t: &mut T,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    f: &FnIr,
    this_spec_id: u32,
    source: &SourceInfo,
) -> Result<(), CodegenError> {
    let fn_types = env.fn_types;
    let param_reprs = env.param_reprs;
    let native_abi_fns = env.native_abi_fns;
    let cont_target_fns = env.cont_target_fns;
    let cont_fns = env.cont_fns;
    let closure_capture_counts = env.closure_capture_counts;
    let is_native = native_abi_fns.contains(&f.id);
    let is_cont_fn = cont_fns.contains(&f.id);
    // Closure-target fn shape: `(args..., self, cont) tail`. Only takes
    // effect for native fns; uniform fns still go through the
    // closure-stub adapter.
    let closure_target_n_caps: Option<usize> = if is_native && !is_cont_fn {
        closure_capture_counts.get(&f.id).copied()
    } else {
        None
    };
    let demand_abi = DemandAbi::new(env.body_key(this_spec_id));
    // When this fn is never invoked from any fz IR site (not a direct
    // callee, not a continuation, not a closure target), it can only
    // enter via the trampoline entry, which writes null into the frame's
    // slot 0. cont_ptr is therefore statically null at runtime;
    // emit_return can elide the load/icmp/brif dispatch and emit a
    // halt-only path. `cont_target_fns` is the set of FnIds ever
    // referenced from fz IR.
    let cont_ptr_known_null = !cont_target_fns.contains(&f.id);
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    let reachable_fz_blocks: HashSet<u32> = fn_types.reachable_blocks.iter().map(|id| id.0).collect();
    if !reachable_fz_blocks.contains(&f.entry.0) {
        return Err(CodegenError::new(format!(
            "spec for {}#{} does not include entry block {:?}",
            f.name, f.id.0, f.entry
        )));
    }

    let mut block_map: HashMap<u32, ir::Block> = HashMap::new();
    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    if is_native {
        // Native fn entry: one block_param per fz arg whose type matches
        // param_reprs[i] (F64 for raw float, I64 for raw int or tagged).
        // No frame_ptr; native fns run synchronously inside their caller
        // and never visit the trampoline.
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // Cont fn entry: result's Cranelift type matches
            // my_param_reprs[0].cl_type(). Body sees the value in its
            // native shape — no coerce at entry.
            //
            // Scheduler-resumed receive continuations override the default
            // one-result input shape via `cont_extras_count`: their bound
            // values and captures are loaded from the closure env, leaving
            // only `self` in the Tail-CC signature.
            let extras_count = demand_abi.continuation_extras(env.cont_extras_count.get(&f.id).copied());
            for (i, r) in my_param_reprs[..extras_count].iter().enumerate() {
                let _ = i;
                append_block_param_for_repr(&mut b, entry_cl, *r);
            }
            b.append_block_param(entry_cl, types::I64); // self
        } else if let Some(n_caps) = closure_target_n_caps {
            // Closure-target fn entry: `(args..., self:i64, cont:i64) tail`.
            // n_args = total - n_caps.
            let n_args = my_param_reprs.len().saturating_sub(n_caps);
            for r in &my_param_reprs[..n_args] {
                append_block_param_for_repr(&mut b, entry_cl, *r);
            }
            b.append_block_param(entry_cl, types::I64); // self
            b.append_block_param(entry_cl, types::I64); // cont
        } else {
            for r in my_param_reprs {
                append_block_param_for_repr(&mut b, entry_cl, *r);
            }
            b.append_block_param(entry_cl, types::I64); // cont
        }
    } else {
        b.append_block_param(entry_cl, types::I64); // frame_ptr
        b.append_block_param(entry_cl, types::I64); // host_ctx
    }

    for blk in &f.blocks {
        if blk.id == f.entry {
            continue;
        }
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for _ in &blk.params {
            b.append_block_param(cl_blk, types::I64);
        }
    }

    b.switch_to_block(entry_cl);
    b.seal_block(entry_cl);

    // One machine for the whole function. Its cache starts empty: the entry
    // harness never reads the cache -- it produces the inputs the cache is then
    // populated from. Builder, module, cache, and import table are bound once,
    // here.
    let mut cache = CodegenCache::default();
    let mut body = CodegenFn::new(env, &mut b, jmod, &mut cache);
    let EntryHarnessOut {
        mut var_env,
        frame_ptr,
        host_ctx,
        cont_param,
        tuple_field_params,
    } = build_entry_harness(
        &mut body,
        env,
        schemas,
        f,
        this_spec_id,
        is_native,
        is_cont_fn,
        closure_target_n_caps,
        entry_cl,
    );

    {
        let (if_only, all_used) = classify_var_uses(f);
        let (tuple_return_fields, skipped_tuple_return_vars) =
            tuple_return_delivery_plan(f, env.body_key(this_spec_id), is_cont_fn);
        body.cache.if_only_conds = if_only.into_iter().map(|v| v.0).collect();
        body.cache.used_vars = all_used.into_iter().map(|v| v.0).collect();
        body.cache.tuple_field_params = tuple_field_params;
        body.cache.skipped_tuple_return_vars = skipped_tuple_return_vars;
        body.cache.tuple_return_fields = tuple_return_fields;
        body.cache.owned_cons_reuse_sources = owned_cons_reuse_sources(f);
    }
    // Walk blocks in declared order with entry first. Unreachable
    // fz_ir blocks are filtered out — they have no Cranelift counterpart.
    let mut order: Vec<&Block> = Vec::with_capacity(f.blocks.len());
    if let Some(eb) = f.blocks.iter().find(|b| b.id == f.entry) {
        order.push(eb);
    }
    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        if blk.id != f.entry {
            order.push(blk);
        }
    }

    for blk in &order {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            body.b.switch_to_block(cl_blk);
            let params: Vec<ir::Value> = body.b.block_params(cl_blk).to_vec();
            let mut param_cursor = 0;
            for p in &blk.params {
                let fallback = t.any();
                let repr = ArgRepr::for_block_param_ty(t, &fn_types.vars.get(p).cloned().unwrap_or(fallback));
                var_env.insert(p.0, take_param_binding(body.b, &params, &mut param_cursor, repr));
            }
        }

        // Per-stmt source location: ir_lower records spans into
        // SourceInfo.stmt_spans; encode each as a Cranelift SourceLoc so
        // `fz dump --emit clif` can render `; @file:line:col` comments.
        let stmt_spans = source.stmt_spans.get(&(f.id, blk.id));
        let block_env = fn_types.block_envs.get(&blk.id);
        for (idx, stmt) in blk.stmts.iter().enumerate() {
            let span = stmt_spans.and_then(|v| v.get(idx)).copied().unwrap_or(Span::DUMMY);
            body.b.set_srcloc(span_to_srcloc(span));
            let Stmt::Let(v, prim) = stmt;
            let out = lower_prim(&mut body, t, env, &var_env, prim, *v, f.id, blk.id, idx, block_env)?;
            if !matches!(out, LowerOut::DeadUnit) {
                let binding = match out {
                    LowerOut::StrictConst(value) => {
                        body.cache.static_scalar_consts.insert(v.0, value);
                        let raw = body.b.ins().iconst(types::I64, value.raw() as i64);
                        CodegenValue::known(raw, value.kind())
                    }
                    LowerOut::Strict(value) => value,
                    LowerOut::ValueRefWord(value) => CodegenValue::any_ref(value),
                    LowerOut::ValueRef(value) => CodegenValue::any_ref(value),
                    _ => {
                        let repr = if out.is_raw_f64() {
                            ArgRepr::RawF64
                        } else if out.is_raw_i64() {
                            ArgRepr::RawInt
                        } else if out.is_condition() {
                            ArgRepr::Condition
                        } else {
                            ArgRepr::ValueRef
                        };
                        CodegenValue::from_abi_value(out.value(), repr)
                    }
                };
                var_env.insert(v.0, binding);
            }
        }
        // Terminator gets its own srcloc (often the same as the last
        // stmt for Return blocks; distinct for Call/Goto).
        let term_span = source.term_span.get(&(f.id, blk.id)).copied().unwrap_or(Span::DUMMY);
        body.b.set_srcloc(span_to_srcloc(term_span));

        // Repr-aware Goto coercion. Mirrors coerce_call_args but for
        // intra-function block edges. Each arg is coerced to the repr
        // the target block param actually needs (derived from
        // fn_types.vars), so RawInt values flow through without a
        // box/unbox round-trip at block joins.
        if let Term::Goto(target, args) = &blk.terminator {
            if !block_map.contains_key(&target.0) {
                return Err(CodegenError::new(format!(
                    "reachable block {:?} in {}#{} jumps to spec-unreachable block {:?}",
                    blk.id, f.name, f.id.0, target
                )));
            }
            for (param, arg) in f.block(*target).params.iter().zip(args.iter()) {
                let fallback = t.any();
                let want = ArgRepr::for_block_param_ty(t, &fn_types.vars.get(param).cloned().unwrap_or(fallback));
                let vb = *var_env.get(&arg.0).expect("unbound goto arg");
                if let Some(coerced) = body.coerce_goto_arg(vb, want) {
                    var_env.insert(arg.0, coerced);
                }
            }
        }

        emit_terminator(
            &mut body,
            t,
            env,
            schemas,
            &var_env,
            blk,
            &block_map,
            is_native,
            is_cont_fn,
            this_spec_id,
            f.id,
            cont_ptr_known_null,
            frame_ptr,
            host_ctx,
            cont_param,
            &fn_types.vars,
            block_env,
        )?;
    }

    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            body.b.seal_block(cl_blk);
        }
    }
    drop(body);
    b.finalize();
    Ok(())
}

fn owned_cons_reuse_sources(f: &FnIr) -> HashMap<u32, Var> {
    f.physical_capabilities
        .iter()
        .map(|fact| match fact.capability {
            PhysicalCapability::OwnedConsReuse { head } => (head.0, fact.source),
        })
        .collect()
}

fn tuple_return_delivery_plan(
    f: &FnIr,
    spec_key: &SpecKey,
    is_cont_fn: bool,
) -> (HashMap<u32, Vec<Var>>, HashSet<u32>) {
    if is_cont_fn && spec_key.demand.tuple_field_arity().is_some() {
        return (HashMap::new(), HashSet::new());
    }
    let arity = match DemandAbi::new(spec_key).tuple_field_arity() {
        Some(arity) => arity,
        None => return (HashMap::new(), HashSet::new()),
    };
    let mut plans = HashMap::new();
    let mut skipped = HashSet::new();
    for blk in &f.blocks {
        let Term::Return(ret) = &blk.terminator else {
            continue;
        };
        if let Some((dest, fields, vars_to_skip)) = tuple_dest_chain_for_return(blk, *ret, arity) {
            let _ = dest;
            plans.insert(ret.0, fields);
            skipped.extend(vars_to_skip);
        } else if let Some(fields) = tuple_make_for_return(blk, *ret, arity) {
            plans.insert(ret.0, fields);
            skipped.insert(ret.0);
        }
    }
    (plans, skipped)
}

fn tuple_make_for_return(blk: &Block, ret: Var, arity: usize) -> Option<Vec<Var>> {
    for Stmt::Let(v, prim) in &blk.stmts {
        if *v == ret
            && let Prim::MakeTuple(fields) = prim
            && fields.len() == arity
        {
            return Some(fields.clone());
        }
    }
    None
}

fn tuple_dest_chain_for_return(blk: &Block, ret: Var, arity: usize) -> Option<(Var, Vec<Var>, HashSet<u32>)> {
    let mut freeze_dest = None;
    for Stmt::Let(v, prim) in &blk.stmts {
        if *v == ret
            && let Prim::DestFreeze { dest, .. } = prim
        {
            freeze_dest = Some(*dest);
            break;
        }
    }
    let dest = freeze_dest?;
    let mut saw_begin = None;
    let mut fields: Vec<Option<Var>> = vec![None; arity];
    let mut skipped = HashSet::new();
    skipped.insert(ret.0);
    for Stmt::Let(v, prim) in &blk.stmts {
        match prim {
            Prim::DestTupleBegin { arity: a, .. } if *v == dest && *a == arity => {
                saw_begin = Some(*v);
                skipped.insert(v.0);
            }
            Prim::DestTupleSet {
                dest: d, index, value, ..
            } if *d == dest && (*index as usize) < arity => {
                fields[*index as usize] = Some(*value);
                skipped.insert(v.0);
            }
            _ => {}
        }
    }
    saw_begin?;
    let fields: Option<Vec<_>> = fields.into_iter().collect();
    Some((dest, fields?, skipped))
}
