//! Per-function Cranelift body emission.

use super::*;
use crate::fast_hash::HashMap;
use crate::fz_ir::{Block, FnIr, Prim, SourceInfo, Stmt};
use crate::ir_dce::classify_var_uses;
use crate::source::Span;
use crate::types::{ClosureTypes, Types};
use cranelift_codegen::{
    Context,
    ir::{self, InstBuilder, types},
};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};

pub(crate) fn compile_fn<M: cranelift_module::Module, T: Types<Ty = Ty> + ClosureTypes>(
    jmod: &mut M,
    t: &mut T,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    env: &CodegenEnv<'_>,
    f: &FnIr,
    this_spec_id: u32,
    source: &SourceInfo,
) -> Result<(), CodegenError> {
    let param_reprs = env.param_reprs;
    let cont_fns = env.cont_fns;
    let native_body = env.body_native(this_spec_id);
    let is_cont_fn = cont_fns.contains(&f.id);
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    let mut block_map: HashMap<u32, ir::Block> = HashMap::default();
    for blk in &f.blocks {
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    // One block_param per fz arg whose type matches param_reprs[i] (F64 for
    // raw float, I64 for raw int or tagged), then the trailing cont (or, for a
    // continuation fn, `self`).
    let my_param_reprs = &param_reprs[this_spec_id as usize];
    if is_cont_fn {
        // Cont fn entry: result's Cranelift type matches
        // my_param_reprs[0].cl_type(). Body sees the value in its
        // native shape — no coerce at entry.
        //
        // Scheduler-resumed receive continuations override the default
        // one-result input shape via their settled continuation ABI: their bound
        // values and captures are loaded from the closure env, leaving
        // only `self` in the Tail-CC signature.
        let extras_count = continuation_entry_extra_count(native_body);
        for r in &my_param_reprs[..extras_count] {
            append_block_param_for_repr(&mut b, entry_cl, *r);
        }
        b.append_block_param(entry_cl, types::I64); // self
    } else {
        for r in my_param_reprs {
            append_block_param_for_repr(&mut b, entry_cl, *r);
        }
        b.append_block_param(entry_cl, types::I64); // cont
    }

    for blk in &f.blocks {
        if blk.id == f.entry {
            continue;
        }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for p in &blk.params {
            append_block_param_for_repr(&mut b, cl_blk, block_param_repr(native_body, p));
        }
    }

    // A tail call to this very function is a jump back to its head. Cranelift
    // never branches to the function's first block, so the first block only
    // forwards the parameters to the head, which is the block that harness
    // and body begin in.
    let loops = !is_cont_fn && closes_a_loop_at_its_head(f);
    if loops {
        let first = b.create_block();
        b.append_block_params_for_function_params(first);
        b.switch_to_block(first);
        b.seal_block(first);
        let params: Vec<ir::BlockArg> = b.block_params(first).iter().map(|v| ir::BlockArg::Value(*v)).collect();
        b.ins().jump(entry_cl, &params);
        b.switch_to_block(entry_cl);
    } else {
        b.switch_to_block(entry_cl);
        b.seal_block(entry_cl);
    }

    // One machine for the whole function. Its cache starts empty: the entry
    // harness never reads the cache -- it produces the inputs the cache is then
    // populated from. Builder, module, cache, and import table are bound once,
    // here.
    let mut cache = CodegenCache::default();
    let mut body = CodegenFn::new(&mut b, jmod, &mut cache, env.site_scope());
    let EntryHarnessOut {
        mut var_env,
        cont_param,
        self_ref,
    } = build_entry_harness(&mut body, env, f, this_spec_id, is_cont_fn, entry_cl);

    body.cache.own_continuation = self_ref;
    body.cache.loop_head = loops.then_some(entry_cl);
    {
        let (if_only, all_used) = classify_var_uses(f);
        body.cache.if_only_conds = if_only.into_iter().map(|v| v.0).collect();
        body.cache.used_vars = all_used.into_iter().map(|v| v.0).collect();
    }
    // Walk blocks in declared order with entry first.
    let mut order: Vec<&Block> = Vec::with_capacity(f.blocks.len());
    order.push(f.block(f.entry));
    for blk in &f.blocks {
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
                let repr = block_param_repr(native_body, p);
                var_env.insert(p.0, take_param_binding(body.b, &params, &mut param_cursor, repr));
            }
        }

        // Per-stmt source location: ir_lower records spans into
        // SourceInfo.stmt_spans; encode each as a Cranelift SourceLoc so
        // Compiler2 CLIF dumps can render `; @file:line:col` comments.
        let stmt_spans = source.stmt_spans.get(&(f.id, blk.id));
        let branching_test = type_test_that_only_branches(blk, &body.cache.if_only_conds, &block_map);
        let lowered = blk.stmts.len() - usize::from(branching_test.is_some());
        for (idx, stmt) in blk.stmts[..lowered].iter().enumerate() {
            let span = stmt_spans.and_then(|v| v.get(idx)).copied().unwrap_or(Span::DUMMY);
            body.b.set_srcloc(span_to_srcloc(span));
            match stmt {
                Stmt::Let(v, prim) => {
                    let out = lower_prim(&mut body, t, env, &var_env, prim, *v, blk.id, idx)?;
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
                Stmt::LetMany(vars, Prim::Extern(_, eid, args)) => {
                    let decl = env.module.extern_by_id(*eid);
                    let values = lower_extern_pair(&mut body, &var_env, decl, eid, args, vars)?;
                    var_env.extend(vars.iter().map(|var| var.0).zip(values));
                }
                Stmt::LetMany(_, prim) => {
                    return Err(CodegenError::new(format!(
                        "multi-result lowering is unsupported for {prim:?}"
                    )));
                }
            }
        }
        // Terminator gets its own srcloc (often the same as the last
        // stmt for Return blocks; distinct for Call/Goto).
        let term_span = source.term_span.get(&(f.id, blk.id)).copied().unwrap_or(Span::DUMMY);
        body.b.set_srcloc(span_to_srcloc(term_span));

        match branching_test {
            Some(test) => lower_runtime_type_branch(&mut body, env, &var_env, test)?,
            None => emit_terminator(&mut body, env, &var_env, blk, &block_map, this_spec_id, f, cont_param)?,
        }
    }

    for blk in &f.blocks {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            body.b.seal_block(cl_blk);
        }
    }
    drop(body);
    if loops {
        b.seal_block(entry_cl);
    }
    b.finalize(jmod.target_config());
    Ok(())
}

/// Whether some block of `f` tail-calls `f` itself.
fn closes_a_loop_at_its_head(f: &FnIr) -> bool {
    f.blocks.iter().any(|blk| {
        matches!(
            &blk.terminator,
            crate::fz_ir::Term::TailCall { callee: crate::fz_ir::DirectCallTarget::Local(callee), .. } if *callee == f.id
        )
    })
}
