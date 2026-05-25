//! Per-function Cranelift body emission.

use super::*;
use crate::fz_ir::{Stmt, Term};
use cranelift_codegen::{
    Context,
    ir::{self, InstBuilder, types},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use fz_runtime::heap::Schema;
use std::collections::HashMap;

pub(crate) fn compile_fn<
    M: cranelift_module::Module,
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    jmod: &mut M,
    t: &mut T,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    env: &CodegenEnv<'_>,
    schemas: &[Schema],
    f: &crate::fz_ir::FnIr,
    this_spec_id: u32,
    source: &crate::fz_ir::SourceInfo,
) -> Result<(), CodegenError> {
    let runtime = env.runtime;
    let fn_types = env.fn_types;
    let param_reprs = env.param_reprs;
    let natively_callable = env.natively_callable;
    let cont_target_fns = env.cont_target_fns;
    let cont_fns = env.cont_fns;
    let closure_n_captures = env.closure_n_captures;
    let is_native = natively_callable.contains(&f.id);
    let is_cont_fn = cont_fns.contains(&f.id);
    // fz-cps.1.2 — closure-target fn shape per §2.1: `(args..., self,
    // cont) tail`. Only takes effect for native fns; uniform fns still
    // go through the closure-stub adapter for now.
    let closure_target_n_caps: Option<usize> = if is_native && !is_cont_fn {
        closure_n_captures.get(&f.id).copied()
    } else {
        None
    };
    // fz-ul4.27.18: when this fn is never invoked from any fz IR site
    // (not a direct callee, not a continuation, not a closure target),
    // it can only enter via the trampoline entry, which writes null
    // into the frame's slot 0. cont_ptr is therefore statically null at
    // runtime; emit_return can elide the load/icmp/brif dispatch and
    // emit a halt-only path. The `cont_target_fns` parameter is the
    // upstream set of "ever referenced from fz IR" FnIds.
    let cont_ptr_known_null = !cont_target_fns.contains(&f.id);
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    // fz-ul4.30 — reachability filter. `ir_lower` emits an unconditional
    // `fail_block` per fn (Halt with :function_clause atom) for clauses
    // whose patterns fail at runtime, and similar match-fail blocks for
    // `cond` / lambda bodies. Single-clause fns with bare-var params
    // never Goto their fail_block, leaving it as dead CLIF. Worse, the
    // dead Halt's `return` was previously typed `i64` regardless of the
    // fn's sig — under .27.13's per-type return typing this trips the
    // Cranelift verifier (f64 sig vs i64 return). Skip emitting those
    // blocks entirely.
    let reachable_fz_blocks: std::collections::HashSet<u32> = {
        let blk_idx: HashMap<u32, &crate::fz_ir::Block> =
            f.blocks.iter().map(|b| (b.id.0, b)).collect();
        let mut reach: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let mut stack: Vec<u32> = vec![f.entry.0];
        while let Some(bid) = stack.pop() {
            if !reach.insert(bid) {
                continue;
            }
            let Some(blk) = blk_idx.get(&bid) else {
                continue;
            };
            match &blk.terminator {
                Term::Goto(t, _) => stack.push(t.0),
                Term::If { then_b, else_b, .. } => {
                    stack.push(then_b.0);
                    stack.push(else_b.0);
                }
                // Return / TailCall / Halt / Call / CallClosure /
                // TailCallClosure / Receive don't pass control to other
                // fz_ir blocks within this fn; codegen lowers them into
                // Cranelift sub-blocks owned by the lowering site itself.
                _ => {}
            }
        }
        reach
    };

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
        // fz-ul4.27.6.2.3 / .27.13 — native fn entry: one block_param per
        // fz arg whose type matches my param_reprs[i] (F64 for raw float,
        // I64 for raw int or tagged), plus a trailing host_ctx i64. No
        // frame_ptr; native fns run synchronously inside their caller and
        // never visit the trampoline.
        let my_param_reprs = &param_reprs[this_spec_id as usize];
        if is_cont_fn {
            // fz-ul4.27.22.3 cont fn entry per §2.1: result's Cranelift
            // type matches my_param_reprs[0].cl_type() (RawInt=i64,
            // RawF64=f64, ValueRef=i64). Body sees the value in its native
            // shape — no coerce at entry.
            //
            // Scheduler-resumed receive continuations override the default
            // one-result input shape via `cont_extras_count`: their bound
            // values and captures are loaded from the closure env, leaving
            // only `self` in the Tail-CC signature.
            let extras_count = env.cont_extras_count.get(&f.id).copied().unwrap_or(1);
            for (i, r) in my_param_reprs[..extras_count].iter().enumerate() {
                let _ = i;
                append_block_param_for_repr(&mut b, entry_cl, *r);
            }
            b.append_block_param(entry_cl, types::I64); // self
        } else if let Some(n_caps) = closure_target_n_caps {
            // fz-cps.1.2 closure-target fn entry per §2.1:
            // `(args..., self:i64, cont:i64) tail`. n_args = total - n_caps.
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

    let EntryHarnessOut {
        mut var_env,
        frame_ptr,
        host_ctx,
        cont_param,
    } = build_entry_harness(
        &mut b,
        jmod,
        env,
        schemas,
        f,
        this_spec_id,
        is_native,
        is_cont_fn,
        closure_target_n_caps,
        entry_cl,
    );

    let mut cache = {
        let (if_only, all_used) = crate::ir_dce::classify_var_uses(f);
        CodegenCache {
            if_only_conds: if_only.into_iter().map(|v| v.0).collect(),
            used_vars: all_used.into_iter().map(|v| v.0).collect(),
            ..CodegenCache::default()
        }
    };

    // Walk blocks in declared order with entry first. Unreachable
    // fz_ir blocks (fz-ul4.30) are filtered out — they have no
    // Cranelift counterpart.
    let mut order: Vec<&crate::fz_ir::Block> = Vec::with_capacity(f.blocks.len());
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
            b.switch_to_block(cl_blk);
            let params: Vec<ir::Value> = b.block_params(cl_blk).to_vec();
            let mut param_cursor = 0;
            for p in &blk.params {
                let fallback = t.any();
                let repr = ArgRepr::for_block_param_ty(
                    t,
                    &fn_types.vars.get(p).cloned().unwrap_or(fallback),
                );
                var_env.insert(
                    p.0,
                    take_param_binding(&mut b, &params, &mut param_cursor, repr),
                );
            }
        }

        // Per-stmt source location: ir_lower records spans into
        // SourceInfo.stmt_spans; encode each as a Cranelift SourceLoc so
        // `fz dump --emit clif` can render `; @file:line:col` comments.
        // fz-ul4.23.7.
        let stmt_spans = source.stmt_spans.get(&(f.id, blk.id));
        let block_env = fn_types.block_envs.get(&blk.id);
        for (idx, stmt) in blk.stmts.iter().enumerate() {
            let span = stmt_spans
                .and_then(|v| v.get(idx))
                .copied()
                .unwrap_or(crate::diag::Span::DUMMY);
            b.set_srcloc(span_to_srcloc(span));
            let Stmt::Let(v, prim) = stmt;
            let out = lower_prim(
                &mut b, jmod, t, env, &var_env, prim, *v, &mut cache, f.id, blk.id, idx, block_env,
            )?;
            if !matches!(out, LowerOut::DeadUnit) {
                let binding = match out {
                    LowerOut::StrictConst(value) => {
                        let raw = b.ins().iconst(types::I64, value.raw() as i64);
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
        let term_span = source
            .term_span
            .get(&(f.id, blk.id))
            .copied()
            .unwrap_or(crate::diag::Span::DUMMY);
        b.set_srcloc(span_to_srcloc(term_span));

        // fz-xs2 fz-ul4.rep.2: repr-aware Goto coercion.  Mirrors
        // coerce_call_args but for intra-function block edges.  Each arg is
        // coerced to the repr the target block param actually needs (derived
        // from fn_types.vars), so RawInt values flow through without a
        // box/unbox round-trip at inliner seams.
        if let Term::Goto(target, args) = &blk.terminator {
            for (param, arg) in f.block(*target).params.iter().zip(args.iter()) {
                let fallback = t.any();
                let want = ArgRepr::for_block_param_ty(
                    t,
                    &fn_types.vars.get(param).cloned().unwrap_or(fallback),
                );
                let vb = *var_env.get(&arg.0).expect("unbound goto arg");
                if want == ArgRepr::ValueRef {
                    let value_ref = codegen_value_as_any_ref(&mut b, jmod, runtime, &mut cache, vb);
                    var_env.insert(arg.0, CodegenValue::any_ref(value_ref));
                } else if vb.repr() != want {
                    let coerced = coerce_binding_to(&mut b, jmod, runtime, vb, want);
                    var_env.insert(arg.0, CodegenValue::from_abi_value(coerced, want));
                }
            }
        }

        emit_terminator(
            &mut b,
            jmod,
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
            &mut cache,
            block_env,
        )?;
    }

    for blk in &f.blocks {
        if !reachable_fz_blocks.contains(&blk.id.0) {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.seal_block(cl_blk);
        }
    }
    b.finalize();
    // fz-ul4.32.1 — publish Value -> Ty for the dump path. Only the
    // values bound to fz Vars are recorded; pure Cranelift intermediates
    // (iconst, ishl_imm, ...) stay unannotated. Pure overhead when
    // IR_TEXT_RECORD is disabled is the `with` + None-check.
    VALUE_DESCR_RECORD.with(|c| {
        if let Some(map) = c.borrow_mut().as_mut() {
            map.clear();
            for (var_id, vb) in &var_env {
                if let Some(d) = fn_types.vars.get(&crate::fz_ir::Var(*var_id)) {
                    map.insert(vb.value().as_u32(), d.clone());
                }
            }
        }
    });
    Ok(())
}
