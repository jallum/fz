//! Split from src/ir_codegen.rs (fz-ame.7). Mechanical move only.

#![allow(unused_imports)]

use super::*;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;

pub(crate) fn compile_with_backend_impl<
    B: Backend,
    T: crate::types::Types<Ty = crate::types::Ty>
        + crate::types::ClosureTypes
        + crate::types::LiteralTypes
        + crate::types::RenderTypes
        + crate::types::VisibilityTypes,
>(
    t: &mut T,
    module: &Module,
    mut backend: B,
    pre_types: Option<&crate::ir_typer::ModuleTypes>,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<B::Output, CodegenError> {
    let export_dispatch = backend.export_dispatch();
    let runtime = declare_runtime_symbols(backend.module_mut(), export_dispatch)?;

    let mut fbctx = FunctionBuilderContext::new();

    // fz-ul4.27.22.3 — emit fz_main_entry. Generic shim: takes the
    // entry fn ptr + a halt-cont singleton ptr supplied by the Rust
    // caller (caller picks the singleton matching the entry fn's
    // return_repr kind). Body just `call_indirect Tail main_fp(halt_cl)`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.main_entry_id,
            |_m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let main_fp = b.block_params(entry)[0];
                let halt_cl = b.block_params(entry)[1];
                let mut main_sig = Signature::new(CallConv::Tail);
                main_sig.params.push(AbiParam::new(types::I64));
                main_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(main_sig);
                let inst = b.ins().call_indirect(sig_ref, main_fp, &[halt_cl]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_main_entry: {}", e)))?;
    }

    // fz-4mk.3a — emit fz_drain_dtor_entry. SystemV scheduler-callable
    // shim that invokes a 1-arg resource dtor closure with its payload.
    // Body: pick a Strict halt-cont via fz_get_halt_cont, read the body
    // addr through the closure ABI, and Tail-CC indirect-call
    // `(payload_ref, closure, halt_cl)`. Result is discarded by the caller.
    // Sig: `(closure:i64, payload_ref:i64) -> i64 system_v`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.drain_dtor_entry_id,
            |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let closure = b.block_params(entry)[0];
                let payload_ref = b.block_params(entry)[1];
                // Strict halt-cont (kind=0). Dtor return is discarded;
                // ValueRef is harmless and avoids RawInt/F64 unboxing.
                let strict_addr = fn_addr(m, runtime.halt_cont_body_strict_id, b);
                let zero = b.ins().iconst(types::I32, 0);
                let ghc_fref = m.declare_func_in_func(runtime.get_halt_cont_id, b.func);
                let halt_inst = b.ins().call(ghc_fref, &[strict_addr, zero]);
                let halt_cl = b.inst_results(halt_inst)[0];
                let code = load_closure_code_ref(b, m, &runtime, closure);
                // fz-cps.1.2 §2.1 closure-target body sig:
                // `(args..., self, cont) tail -> i64`. Generic args are
                // one-word ValueRefs.
                let mut closure_sig = Signature::new(CallConv::Tail);
                closure_sig.params.push(AbiParam::new(types::I64)); // x ValueRef
                closure_sig.params.push(AbiParam::new(types::I64)); // self
                closure_sig.params.push(AbiParam::new(types::I64)); // cont
                closure_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(closure_sig);
                let inst = b
                    .ins()
                    .call_indirect(sig_ref, code, &[payload_ref, closure, halt_cl]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_drain_dtor_entry: {}", e)))?;
    }

    // fz-cps.1.11 — emit fz_spawn_entry. SystemV scheduler-callable shim
    // that invokes a zero-arg closure with a fresh halt-cont. Used by
    // `Runtime::spawn_closure` to launch the new task's first fn via
    // the closure-target sig `(self, cont) tail`. The closure body
    // tail-chains into a halt-cont; halt sets process.halt_value.
    // Sig: `(closure:i64) -> i64 system_v`.
    {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.spawn_entry_id,
            |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let closure = b.block_params(entry)[0];
                // fz-ul4.27.22.6 — pick the matching halt-cont based on the
                // spawned closure's halt_kind (packed into the high 2 bits of
                // object-local closure `flags` at MakeClosure time). For
                // RawInt-returning bodies, this routes the i64 raw payload
                // into halt_cont_body_i64. Pre-22.6 this was hardcoded ValueRef.
                //
                // Closure metadata layout:
                //   off 0  : kind (u16)         off 4  : size_bytes (u32)
                //   off 2  : flags (u16)        off 8  : schema_id (u32)
                //                               off 12 : _reserved (u32)
                // flags low 14 bits = captured_count; high 2 bits = halt_kind.
                let kind = load_closure_halt_kind_ref(b, m, &runtime, closure);
                // Select halt_cont_body_addr by kind. Branchless via three
                // func_addrs + a tiny dispatch — keeps the spawn shim a leaf.
                let a_strict = fn_addr(m, runtime.halt_cont_body_strict_id, b);
                let a_i64 = fn_addr(m, runtime.halt_cont_body_i64_id, b);
                let a_f64 = fn_addr(m, runtime.halt_cont_body_f64_id, b);
                let one = b.ins().iconst(types::I32, 1);
                let two = b.ins().iconst(types::I32, 2);
                let is_i64 = b.ins().icmp(IntCC::Equal, kind, one);
                let is_f64 = b.ins().icmp(IntCC::Equal, kind, two);
                let pick_i64_or_tagged = b.ins().select(is_i64, a_i64, a_strict);
                let hcb_addr = b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
                let ghc_fref = m.declare_func_in_func(runtime.get_halt_cont_id, b.func);
                let halt_inst = b.ins().call(ghc_fref, &[hcb_addr, kind]);
                let halt_cl = b.inst_results(halt_inst)[0];
                // Read closure body addr through the runtime ABI and invoke as
                // closure-target sig `(self, cont) tail` (zero user args).
                let code = load_closure_code_ref(b, m, &runtime, closure);
                let mut closure_sig = Signature::new(CallConv::Tail);
                closure_sig.params.push(AbiParam::new(types::I64)); // self
                closure_sig.params.push(AbiParam::new(types::I64)); // cont
                closure_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(closure_sig);
                let inst = b.ins().call_indirect(sig_ref, code, &[closure, halt_cl]);
                let r = b.inst_results(inst)[0];
                b.ins().return_(&[r]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define fz_spawn_entry: {}", e)))?;
    }

    // fz-ul4.27.22.3 — emit three fz_halt_cont_body fns, one per repr.
    // Generic ValueRef bodies receive `(value_ref, self)`; RawInt / RawF64
    // variants stay narrow as `(value, self)`.
    {
        let mut sig = Signature::new(CallConv::Tail);
        push_repr_param(&mut sig, ArgRepr::ValueRef);
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            sig,
            runtime.halt_cont_body_strict_id,
            |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let value_ref = b.block_params(entry)[0];
                let hi_fref = m.declare_func_in_func(runtime.halt_implicit_ref_id, b.func);
                b.ins().call(hi_fref, &[value_ref]);
                let zero = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[zero]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    }
    for (body_id, val_ty, halt_impl_id) in [
        (
            runtime.halt_cont_body_i64_id,
            types::I64,
            runtime.halt_implicit_i64_id,
        ),
        (
            runtime.halt_cont_body_f64_id,
            types::F64,
            runtime.halt_implicit_f64_id,
        ),
    ] {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(val_ty));
        sig.params.push(AbiParam::new(types::I64));
        sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(backend.module_mut(), &mut fbctx, sig, body_id, |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let val = b.block_params(entry)[0];
            let hi_fref = m.declare_func_in_func(halt_impl_id, b.func);
            b.ins().call(hi_fref, &[val]);
            let zero = b.ins().iconst(types::I64, 0);
            b.ins().return_(&[zero]);
        })
        .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    }

    // Register a heap Schema for every tuple arity used by MakeTuple, so the
    // GC tracer can walk fields and so codegen can iconst the schema_id.
    // Also detect any bitstring prim so we can pre-register arity-1 / arity-3
    // schemas used by the reader / result tuples even if no MakeTuple uses
    // those arities directly.
    // fz-ul4.38 — BTreeSet so iteration order is deterministic. Schema ids
    // are assigned by registration order; the AOT runtime registers in the
    // same sorted order so its ids match what codegen baked into the CLIF.
    let mut tuple_arities: std::collections::BTreeSet<usize> = std::collections::BTreeSet::new();
    let mut has_bs_prim = false;
    for f in &module.fns {
        for blk in &f.blocks {
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                match prim {
                    Prim::MakeTuple(args) => {
                        tuple_arities.insert(args.len());
                    }
                    Prim::MakeBitstring(_)
                    | Prim::BitReaderInit(_)
                    | Prim::BitReadField { .. }
                    | Prim::BitReaderDone(_) => {
                        has_bs_prim = true;
                    }
                    // fz-ul4.36 — also register schemas for arities that
                    // appear in TypeTest tuple descriptors. The runtime
                    // check compares schema_id; without pre-registration
                    // we'd have no id to compare against.
                    Prim::TypeTest(_, descr) => {
                        for arity in
                            crate::concrete_types::ty_descr(descr).type_test_tuple_arities()
                        {
                            tuple_arities.insert(arity);
                        }
                    }
                    _ => {}
                }
            }
        }
    }
    if has_bs_prim {
        tuple_arities.insert(1);
        tuple_arities.insert(3);
    }
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    let mut tuple_schema_ids: HashMap<usize, u32> = HashMap::new();
    {
        let mut reg = user_schemas.borrow_mut();
        for &arity in &tuple_arities {
            let id = reg.register(Schema::tuple_of_arity(arity));
            tuple_schema_ids.insert(arity, id);
        }
    }
    let (bs_tuple_arity1_schema, bs_tuple_arity3_schema) = if has_bs_prim {
        (
            Some(*tuple_schema_ids.get(&1).expect("arity-1 schema registered")),
            Some(*tuple_schema_ids.get(&3).expect("arity-3 schema registered")),
        )
    } else {
        (None, None)
    };

    // frame_sizes is computed after `schemas` is built (post-spec_registry).

    // Run the typer ahead of codegen so per-fn Var->type info is
    // available during lowering.
    let mut working = module.clone();
    let owned_pre_types;
    let pre_types = match pre_types {
        Some(pre_types) => pre_types,
        None => {
            owned_pre_types = crate::ir_typer::type_module(t, &working, tel);
            &owned_pre_types
        }
    };
    // fz-ul4.29.10.3 — lower known-target CallClosure / TailCallClosure
    // to direct Call / TailCall. After this, the final type_module sees
    // direct dispatch where the closure-stub used to live, and
    // .29.12.6's any-key drop logic can remove the now-dead any-key.
    //
    // Uses the same `pre_types`: `fn_constants` tracks Vars bound to
    // `Prim::Const(Value::Fn)` / `Prim::MakeClosure`, neither of which
    // is touched. So `pre_types.fn_constants` is identical to whatever
    // a re-type would produce. No separate `mid_types` call needed.
    crate::ir_typer::rewrite_known_target_closures(t, &mut working, pre_types);
    #[cfg(not(test))]
    crate::ir_inline::inline_module(&mut working);
    #[cfg(test)]
    if !INLINE_DISABLED.with(|d| d.get()) {
        crate::ir_inline::inline_module(&mut working);
    }
    crate::ir_fuse::fuse_blocks_with_telemetry(&mut working, tel);
    // fz-jg5.4 (RED.3) — compile-time reducer pass. Folds calls whose
    // return is statically known; reduces If-on-bool-literal to Goto.
    // Plugs in after ir_inline + ir_fuse so it sees a cleaner call graph.
    // See docs/bodies-are-boundaries.md.
    // fz-uwq.9 — reducer returns a ReducerLog (Consumed / Stalled
    // facts). Codegen doesn't consume it directly; the dump pipeline
    // does. Codegen drives reduction only for its IR-rewriting effect.
    #[cfg(not(test))]
    let _ = crate::ir_reducer::reduce_module_with_telemetry(t, &mut working, tel);
    #[cfg(test)]
    if !REDUCER_DISABLED.with(|d| d.get()) {
        let _ = crate::ir_reducer::reduce_module_with_telemetry(t, &mut working, tel);
    }
    // fz-uwq.2 — single-use cont collapse runs pre-typer, alongside the
    // other call-shape mutations (`fuse_blocks`, `reduce_module`). The
    // `debug_assert_unique_conts` check at the end of `ir_lower` (fz-uwq.1)
    // guarantees this pass sees each continuation fn exactly once, so it
    // can be applied before the typer commits to specs. See
    // `docs/dispatch-as-typer-output.md` (Worry 1).
    crate::ir_inline::inline_single_use_conts(&mut working);
    let module_types = crate::ir_typer::type_module(t, &working, tel);
    // fz-uwq.14 — snapshot per-fn call-shape multisets right after the
    // typer commits to specs. The post-typer passes (branch_fold, fold,
    // const_bs::fold, dce_module, dce_module_level) may FOLD calls away
    // (Direct → Return when the reducer would have done it; If → Goto
    // when a branch collapses) but must never INVENT new ones — the
    // typer's spec set wouldn't cover invented calls. The assertion at
    // the end of this pipeline pins the invariant: every fn's
    // call-shape multiset post-codegen is a subset (per-kind) of the
    // post-typer multiset.
    #[cfg(debug_assertions)]
    let call_shapes_pre = super::invariants::snapshot_call_shapes(&working);
    // fz-fyq.4 — fold one-sided-dead Ifs to Gotos; DCE below removes
    // the orphaned blocks and the now-unused TypeTest stmts.
    crate::ir_branch_fold::fold_module_with_telemetry(&mut working, &module_types, tel);
    crate::ir_fold::fold_module(&mut working, &module_types);
    // fz-cty.8 — fold byte-literal MakeBitstring into ConstBitstring before
    // DCE so the per-byte Const(Int) operand stmts go dead in the same pass.
    crate::ir_const_bs::fold_module(&mut working);
    crate::ir_dce::dce_module_with_telemetry(&mut working, tel);
    // fz-ul4.11.29: sweep IR fns unreachable from main after inlining.
    crate::ir_dce::dce_module_level(&mut working);
    #[cfg(debug_assertions)]
    super::invariants::assert_no_new_call_shapes(&working, &call_shapes_pre);
    let module = &working;

    // fz-ul4.29.2.1 — Build the SpecRegistry.
    //
    // Register any-keys first, in FnId.0 order — this preserves the
    // invariant `any-key SpecId.0 == FnId.0` so closure / Spawn / Receive
    // paths (and any other "use any-key" path) can keep using fn_id.0
    // directly as a schema_id / Cranelift func key. Narrow specs from
    // `module_types.specs` get SpecIds ≥ n_fns appended afterwards.
    let mut spec_registry = SpecRegistry::new();
    let mut fns_by_fnid: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns_by_fnid.sort_by_key(|f| f.id.0);
    for f in &fns_by_fnid {
        let n_params = f.block(f.entry).params.len();
        let any_ty = t.any();
        let any_key = f.semantic_key(vec![any_ty; n_params]);
        // fz-ul4.29.12.6 — skip registering F's any-key when the typer
        // dropped it (every callsite of F has typed coverage). The next
        // registration via `register_any_key_at` pads slot F.0 with a
        // sentinel automatically, preserving the `SpecId.0 == FnId.0`
        // invariant for the surviving any-keys.
        if !module_types.specs.contains_key(&(f.id, any_key.clone())) {
            continue;
        }
        let precedence = *module_types
            .spec_precedence
            .get(&(f.id, any_key.clone()))
            .unwrap_or(&0);
        let sid = spec_registry.register_any_key_at_with_precedence(t, f.id, any_key, precedence);
        debug_assert_eq!(sid.0, f.id.0);
    }
    // Append narrow specs in a deterministic order (FnId.0, then descr-tuple
    // bytes) so CLIF emission is reproducible across runs.
    let any_ty = t.any();
    let mut narrow_keys: Vec<(FnId, Vec<crate::types::KeySlot>)> = module_types
        .specs
        .keys()
        .filter(|(fid, key)| {
            let Some(f) = module.fns.iter().find(|f| f.id == *fid) else {
                return true;
            };
            let n_params = f.block(f.entry).params.len();
            let any_key = f.semantic_key(vec![any_ty.clone(); n_params]);
            // Filter the any-keys (already registered).
            key != &any_key
        })
        .cloned()
        .collect();
    narrow_keys.sort_by(|a, b| {
        a.0.0
            .cmp(&b.0.0)
            .then_with(|| format!("{:?}", a.1).cmp(&format!("{:?}", b.1)))
    });
    for (fid, key) in narrow_keys {
        let precedence = *module_types
            .spec_precedence
            .get(&(fid, key.clone()))
            .unwrap_or(&0);
        spec_registry.register_with_precedence(t, fid, key, precedence);
    }

    let spec_count = spec_registry.len();
    let spec_keys: Vec<(FnId, Vec<crate::types::KeySlot>)> = spec_registry
        .iter()
        .map(|(_, fid, key)| (fid, key.to_vec()))
        .collect();
    // SpecId.0 -> module.fns index (None when the SpecId is a sentinel
    // slot for a missing FnId.0 — cps_split sparsity).
    let mut idx_of: HashMap<FnId, usize> = HashMap::new();
    for (i, f) in module.fns.iter().enumerate() {
        idx_of.insert(f.id, i);
    }
    // fz-ul4.29.12.6 — treat slots whose typer FnTypes is absent as
    // sentinels too. Three cases collapse here:
    //   * cps_split sparsity: FnId not in module → `idx_of.get` = None.
    //   * Pre-existing sentinel slot (empty-key padding) for a missing
    //     FnId.0 → no entry in `module_types.specs` either.
    //   * Dropped any-key (.29.12.6): FnId exists in module but its
    //     any-key body was pruned by the typer → no entry in
    //     `module_types.specs`. Codegen must skip compilation for the
    //     slot; no consumer can index into it because `resolve` only
    //     returns SpecIds with a real registration.
    let spec_fnidx: Vec<Option<usize>> = spec_keys
        .iter()
        .map(|(fid, key)| {
            if !module_types.specs.contains_key(&(*fid, key.clone())) {
                return None;
            }
            idx_of.get(fid).copied()
        })
        .collect();
    let spec_fn_types: Vec<Option<&crate::ir_typer::FnTypes>> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, (fid, key))| {
            spec_fnidx[sid]?;
            module_types.specs.get(&(*fid, key.clone()))
        })
        .collect();

    // fz-ul4.29.12.2 — collect typed closure shapes keyed by the
    // lambda's resolved narrow SpecId. Each `Prim::MakeClosure` site
    // is inspected per *caller* spec (so closures built in different
    // caller specializations with different capture types produce
    // distinct lambda SpecIds → distinct stubs). The key fed to
    // `spec_registry.resolve` is `[capture_descrs..., any, ...]` —
    // padded to the lambda's full arity. The .29.12.2 typer change
    // (in `ir_typer::type_module`'s worklist) registers a narrow
    // spec for every MakeClosure's capture-type tuple, so
    // exact-match resolve succeeds; the any-key remains a subsumption
    // backstop. Value = capture count (== `captured.len()`); needed
    // to split entry params into `[captures..., args...]` at stub
    // declaration / invocation.
    let mut closure_shapes: std::collections::BTreeMap<u32, usize> =
        std::collections::BTreeMap::new();
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            continue;
        };
        let f = &module.fns[idx];
        let Some(_) = spec_fn_types[sid] else {
            continue;
        };
        for blk in &f.blocks {
            for stmt in blk.stmts.iter() {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_ident, lam_fn_id, captured) = prim {
                    // fz-try B1+B2 — the lambda body is the any-key
                    // body spec (SpecId.0 == FnId.0 via
                    // register_any_key_at). MakeClosure is construction,
                    // not dispatch — look up the body directly.
                    // When the any-key was dropped (.29.12.6), fall back
                    // to any registered narrow spec for this FnId; if
                    // none, the closure value has no live call target
                    // (every invocation got inlined to direct Call) —
                    // skip; the null-stub path in MakeClosure prim
                    // codegen handles allocation.
                    let cl_sid = if spec_fnidx
                        .get(lam_fn_id.0 as usize)
                        .copied()
                        .flatten()
                        .is_some()
                    {
                        Some(lam_fn_id.0)
                    } else {
                        spec_registry
                            .iter()
                            .find(|(s, fid, _)| {
                                *fid == *lam_fn_id && spec_fnidx[s.0 as usize].is_some()
                            })
                            .map(|(s, _, _)| s.0)
                    };
                    let Some(cl_sid) = cl_sid else {
                        continue;
                    };
                    closure_shapes.insert(cl_sid, captured.len());
                }
            }
        }
    }

    // fz-ul4.27.6.2.1 — Parking + native-callability analyses. Stored in
    // metadata; consumed at declare-time below (.6.2.2) for per-fn sigs
    // and at compile_fn / emit_call (.6.2.3-4) for ABI bifurcation.
    // fz-ul4.27.14.1: this block moved up to feed the new
    // `uniform_cont_reachable_specs` analysis that gates the schema /
    // ABI slot-0 force-ValueRef decision below.
    let parking_reachable = crate::parking::parking_reachable(module);
    let mut natively_callable = crate::parking::natively_callable(module, &parking_reachable);

    // fz-cps.1.2 (fz-siu.1.2): the set of fns used as continuations.
    // A cont fn has sig `(result:i64, self:i64) tail` per
    // docs/cps-in-clif.md §2.1 — no host_ctx, no trailing cont param.
    // Its body projects captures from `self`, and its "next k" is one
    // of those captures.
    let cont_fns: std::collections::HashSet<crate::fz_ir::FnId> = {
        use crate::fz_ir::Term;
        let mut s = std::collections::HashSet::new();
        for f in &module.fns {
            for b in &f.blocks {
                match &b.terminator {
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive {
                        continuation,
                        ident: _,
                    } => {
                        s.insert(continuation.fn_id);
                    }
                    // fz-70q.5.5 — clause body / guard / after fns are
                    // dispatched (via cont stub) into their Tail-CC entry,
                    // so they must wear the cont-fn sig shape. The
                    // companion `cont_extras_count` map sets receive
                    // outcome bodies to `(self) tail`; bound values and
                    // captures live inside the outcome closure env.
                    Term::ReceiveMatched { clauses, after, .. } => {
                        for c in clauses {
                            s.insert(c.body);
                            if let Some(g) = c.guard {
                                s.insert(g);
                            }
                        }
                        if let Some(a) = after {
                            s.insert(a.body);
                        }
                    }
                    _ => {}
                }
            }
        }
        s
    };
    let _ = &cont_fns; // fz-cps.1.2: consumed by sig builder + entry harness in next step.

    // fz-cps.1.2 — set of fns appearing as a MakeClosure target. Per
    // docs/cps-in-clif.md §2.1 these get sig `(args..., self:i64, cont:i64)
    // tail` and their body projects captures from `self`. Disjoint
    // from cont_fns by construction (conts are anonymous continuations
    // synthesized by the lowerer; MakeClosure targets are user lambdas
    // or top-level fns passed as values). If overlap occurs in some
    // future fz-IR, cont-fn shape wins (Receive parking would otherwise
    // misread the result slot).
    let (closure_target_fns, closure_n_captures): (
        std::collections::HashSet<crate::fz_ir::FnId>,
        std::collections::HashMap<crate::fz_ir::FnId, usize>,
    ) = {
        use crate::fz_ir::{Prim, Stmt, Term};
        let mut targets = std::collections::HashSet::new();
        let mut counts: std::collections::HashMap<crate::fz_ir::FnId, usize> =
            std::collections::HashMap::new();
        let mut direct_called = std::collections::HashSet::new();
        for f in &module.fns {
            for b in &f.blocks {
                match &b.terminator {
                    Term::Call { callee, .. } | Term::TailCall { callee, .. } => {
                        direct_called.insert(*callee);
                    }
                    _ => {}
                }
                for stmt in &b.stmts {
                    let Stmt::Let(_, prim) = stmt;
                    if let Prim::MakeClosure(_, fid, captured) = prim {
                        targets.insert(*fid);
                        let n = captured.len();
                        if let Some(prev) = counts.get(fid) {
                            debug_assert_eq!(
                                *prev, n,
                                "MakeClosure n_captures mismatch for fn {}: \
                                 {} vs {}",
                                fid.0, prev, n
                            );
                        }
                        counts.insert(*fid, n);
                    }
                }
            }
        }
        // fz-cps.1.8: closure-target sig is universal. Every MakeClosure
        // target gets `(args..., self, cont) tail` regardless of whether
        // it is also direct-called. Direct callers load the
        // per-Process static singleton (registered in fz-siu.1.7) and
        // pass it as `self`. See docs/cps-in-clif.md §8.2 acceptance:
        // both indirect calls lower to `return_call_indirect` against
        // this sig.
        //
        // Invariant: a closure-target fn that is ALSO direct-called must
        // have zero captures — direct callers have no captures to bind.
        // Asserted below.
        for fid in &targets {
            if direct_called.contains(fid) {
                debug_assert_eq!(
                    counts[fid], 0,
                    "fz-siu.1.8: fn {} is both direct-called and a non-zero-cap \
                     closure target — direct callers can't supply captures",
                    fid.0,
                );
            }
        }
        let _ = direct_called;
        (targets, counts)
    };
    let _ = (&closure_target_fns, &closure_n_captures);
    // fz-ul4.27.6.4 follow-up: heap-safe captures.
    //
    // A native cont chain routes the caller's captured vars through
    // Cranelift virtual stack slots / registers as it crosses the
    // synchronous call to the (native) callee. Those slots are
    // invisible to the GC's heap-frame tracer — safe for non-heap
    // payloads (tagged int / atom / nil / bool, which are just bits),
    // unsafe for heap pointers (list cons, struct,
    // closure, etc.) because a GC firing inside the callee would
    // reclaim the unreachable objects.
    //
    // Stack-map emission + a stack-walking tracer would lift this
    // restriction (filed as a follow-up). Until then we shrink
    // `natively_callable` so it only admits conts whose every use
    // site has heap-safe captures. A cont removed by this pass cascades
    // through the fixed point — its callers may no longer satisfy the
    // chain's "every Term::Call cont is native" invariant.
    // fz-cps.1.2: `non_heap` / `is_non_heap_descr` removed with the
    // type-aware shrink — see (a) below. The descriptor types stay in
    // crate::types for other callers.
    // Single combined fixed point. Each iter re-enforces every invariant
    // so cascading removals don't leave an inconsistent set:
    //   (a) Term::Call's callee + cont both native, captures non-heap.
    //   (b) Term::TailCall's callee native, args non-heap.
    //   (c) Cont validity: if f is used as cont in some Term::Call, the
    //       caller's callee at that site must be native (so the site
    //       picks the native-chain branch) and captures non-heap.
    loop {
        let mut to_remove: Vec<crate::fz_ir::FnId> = Vec::new();
        // (a) and (b): body invariants.
        for f in module.fns.iter() {
            if !natively_callable.contains(&f.id) {
                continue;
            }
            let body_ok = f.blocks.iter().all(|b| match &b.terminator {
                Term::Return(_) | Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => true,
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    // fz-cps.1.2: non-heap-args restriction lifted. The
                    // cont chain no longer routes args through Cranelift
                    // register slots invisible to the GC tracer — every
                    // cont is now a heap-allocated closure (§2.2), and
                    // the GC roots come from scheduler-owned closure roots,
                    // not from a stack walk.
                    natively_callable.contains(callee)
                        && natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCall { callee, .. } => natively_callable.contains(callee),
                Term::ExportCall { .. } => false,
                Term::ExportTailCall { .. } => true,
                // fz-cps.1.8 — closure-call terminators admitted; bodies
                // are Tail-CC with closure-target sig. Cont (if
                // any) must also be native so the cont-return chain is
                // unbroken.
                Term::CallClosure { continuation, .. } => {
                    natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCallClosure { .. } => true,
                Term::Receive {
                    continuation,
                    ident: _,
                } => natively_callable.contains(&continuation.fn_id),
                // fz-70q.5.5 — admit ReceiveMatched on the same terms
                // as parking.rs's natively_callable: native iff every
                // body / guard / after fn is native. Cont-stub seam
                // bridges the Tail-CC body into the SystemV scheduler
                // resume path so the enclosing fn's ABI is unconstrained.
                Term::ReceiveMatched { clauses, after, .. } => {
                    let body_ok = clauses.iter().all(|c| {
                        natively_callable.contains(&c.body)
                            && c.guard.is_none_or(|g| natively_callable.contains(&g))
                    });
                    let after_ok = after
                        .as_ref()
                        .is_none_or(|a| natively_callable.contains(&a.body));
                    body_ok && after_ok
                }
            });
            if !body_ok {
                to_remove.push(f.id);
            }
        }
        // (c) Cont validity: cont must reach via a native Term::Call site.
        // fz-cps.1.2: capture heap-safety is no longer required (see
        // explanation in (a) above). The structural check remains: the
        // caller's callee at every cont reach site must still be native.
        for f in &module.fns {
            if !natively_callable.contains(&f.id) {
                continue;
            }
            if to_remove.contains(&f.id) {
                continue;
            }
            let mut cont_unsafe = false;
            'outer: for caller in module.fns.iter() {
                for b in &caller.blocks {
                    let Term::Call {
                        ident: _,
                        callee,
                        continuation,
                        ..
                    } = &b.terminator
                    else {
                        continue;
                    };
                    if continuation.fn_id != f.id {
                        continue;
                    }
                    if !natively_callable.contains(callee) {
                        cont_unsafe = true;
                        break 'outer;
                    }
                }
            }
            if cont_unsafe {
                to_remove.push(f.id);
            }
        }
        if to_remove.is_empty() {
            break;
        }
        for id in to_remove {
            natively_callable.remove(&id);
        }
    }

    // fz-ul4.27.22.16 — `uniform_cont_reachable_specs` deleted. The
    // analysis flagged conts reachable from uniform callees / ValueRef-
    // unconditional writers so their entry slot 0 + schema kind would
    // be forced to ValueRef/AnyValue. Post-22.12, every callsite that
    // would have flagged a cont either:
    //   - resolves via closure_lit to a narrow body spec whose ABI
    //     already matches the cont's narrow slot 0 (direct dispatch);
    //   - flows through the unresolved indirect ValueRef seam, which
    //     `tagged_slot0_cont_specs` (CallClosure / Receive branches)
    //     already covers.
    // Disabling the force changed only line numbers in
    // closure_typed_captures.clif (verified by experiment) — no
    // codegen content shifted. The analysis is dead.

    // fz-ul4.27.18 — per-FnId set: fns invoked from any fz IR site
    // (as a direct callee, a continuation, or a closure target).
    // A fn NOT in this set has no fz IR caller and can only enter via
    // the trampoline entry (which writes null into the frame's slot 0).
    // For such a fn, cont_ptr is statically null at runtime; emit_return
    // can specialize to a halt-only path, skipping the runtime
    // `load v0+16; icmp eq 0; brif` dispatch entirely.
    let mut ir_referenced_fns: std::collections::HashSet<crate::fz_ir::FnId> =
        std::collections::HashSet::new();
    for f in &module.fns {
        for blk in &f.blocks {
            match &blk.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    ir_referenced_fns.insert(*callee);
                    ir_referenced_fns.insert(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => {
                    ir_referenced_fns.insert(*callee);
                }
                Term::CallClosure { continuation, .. } | Term::Receive { continuation, .. } => {
                    ir_referenced_fns.insert(continuation.fn_id);
                }
                _ => {}
            }
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, fid, _) = prim {
                    ir_referenced_fns.insert(*fid);
                }
            }
        }
    }
    // Rebind for the existing parameter name threading. The contained
    // fns are exactly the "never specializable as halt-only" set.
    let cont_target_fns = ir_referenced_fns;

    // Rebuild schemas: one entry per SpecId, refined entry-param kinds
    // from THAT spec's FnTypes. The any-key SpecId for FnId K lands at
    // index K (invariant) so any code path that uses fn_id.0 as a
    // schema_id continues to hit the right schema. Sentinel SpecIds
    // (missing-FnId slots) get a zero-field placeholder schema; they're
    // never reached at runtime.
    let mut schemas: Vec<Schema> = Vec::with_capacity(spec_count);
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = &module.fns[idx];
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
        let entry_block = f.block(f.entry);
        let mut kinds: Vec<FieldKind> = entry_block
            .params
            .iter()
            .map(|_| FieldKind::AnyValue)
            .collect();
        let any = t.any();
        for (j, p) in entry_block.params.iter().enumerate() {
            match ArgRepr::from_ty(t, &ft.vars.get(p).cloned().unwrap_or_else(|| any.clone())) {
                ArgRepr::RawF64 => kinds[j] = FieldKind::RawF64,
                ArgRepr::RawInt => kinds[j] = FieldKind::RawI64,
                _ => {}
            }
        }
        // fz-ul4.27.22.16 — uniform_cont_reachable slot-0 AnyValue force
        // retired; tagged_slot0_cont_specs covers every case post-22.12.
        schemas.push(build_frame_schema(&f.name, &kinds));
    }

    // Per-spec frame sizes (consumed by `fz_alloc_frame_dyn` and the AOT
    // frame-size dispatch fn). Indexed by SpecId.0.
    let frame_sizes: Vec<u32> = schemas
        .iter()
        .map(|s| s.allocation_payload_size() as u32)
        .collect();

    // fz-i82.2 — per-spec return type comes from the typer's LFP
    // (`module_types.effective_returns`). That walk filters by
    // `reachable_blocks` AND propagates through every exit terminator
    // including `Term::Call` / `Term::CallClosure` / `Term::Receive`
    // with a continuation; the cont side (`cont_slot0_descr`) already
    // reads from the same map. Reading it here too means the producer
    // abi and the cont's slot-0 abi agree by construction — the
    // mismatch that fz-i82 manifested cannot recur.
    //
    // Halt-only specs converge to `none()` in the LFP; substitute
    // `any` so `ArgRepr::from_descr` doesn't pick RawF64 (none is a
    // subtype of every set, including float). The value never reaches
    // anyone for a halt-only spec, but the abi must still be valid.
    let any = t.any();
    let none = t.none();
    let return_tys: Vec<crate::types::Ty> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, (fid, key))| {
            if spec_fnidx[sid].is_none() {
                return any.clone();
            }
            let ret = module_types
                .effective_returns
                .get(&(*fid, key.clone()))
                .cloned()
                .unwrap_or_else(|| any.clone());
            if t.is_subtype(&ret, &none) {
                any.clone()
            } else {
                ret
            }
        })
        .collect();

    // fz-ul4.27.13 — Per-spec entry-param ArgReprs + return ArgRepr.
    // Drives both `build_fn_signature` (AbiParam types) and call-site
    // coerce (raw int / raw f64 vs one-word ValueRef). Sentinel slots get
    // empty params + ValueRef return; they're never declared.
    let param_reprs: Vec<Vec<ArgRepr>> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let reprs = build_param_reprs(
                    t,
                    f,
                    spec_fn_types[sid].expect("non-sentinel spec must have FnTypes"),
                );
                // fz-ul4.27.22.16 — uniform_cont_reachable slot-0 ValueRef
                // force retired; tagged_slot0_cont_specs is sufficient.
                // fz-ul4.27.22.12 — arg-slot force at closure body retired.
                // The 22.5 capture-slot wins are preserved (CAPTURE slots
                // [0..n_caps) keep their per-spec narrow reprs). ARG slots
                // now also honor build_param_reprs' typed output: with
                // 22.10's closure_lit-typed MakeClosure and 22.11's direct
                // return_call dispatch, every closure-call site resolves
                // to a single body spec whose ABI the caller targets
                // exactly — no need to flatten arg slots to ValueRef for
                // indirect-sig matching.
                //
                // The indirect fallback path in TailCallClosure still
                // assumes all-ValueRef at the seam, so closures used
                // polymorphically (union of closure_lits, opaque arrow)
                // still go through the ValueRef path correctly: the body's
                // narrow ABI on the direct path is compatible because
                // each direct callsite coerces explicitly.
                let _ = closure_n_captures;
                reprs
            }
            None => Vec::new(),
        })
        .collect();
    // fz-ntz (fz-3zx.2) — transitive closure of fns whose return is
    // ValueRef-by-construction. Seeded with closure-target fns (forced
    // all-ValueRef sig by fz-cps.1.8) and fns whose terminator on any
    // block is Term::TailCallClosure (return_call_indirect against the
    // closure-target sig forwards ValueRef bits). Propagated through
    // Term::TailCall: if F tail-calls into a ValueRef-returning callee,
    // F itself returns ValueRef. The result drives BOTH the return_reprs
    // force (below) AND the tagged_slot0_cont_specs check (next block):
    // producer-side ABI and consumer-side schema stay aligned.
    // fz-ul4.27.22.12 — per-spec tagged-return tracking. Pre-22.12 the
    // set was keyed by FnId, conflating all specs of the same fn. With
    // closure_lit-driven per-spec resolution (22.10-22.11), one spec of
    // a fn can have a fully-resolved TailCallClosure (returning the
    // body's narrow repr) while a sibling spec's TailCallClosure stays
    // opaque (returning ValueRef through the indirect seam). Per-spec is
    // the precise grain.
    //
    // Seed: spec has an UNRESOLVED TailCallClosure (or returns through
    // the all-ValueRef indirect ABI). Resolved-via-closure_lit
    // TailCallClosure does not seed — it's structurally a typed
    // tail-call to the resolved body, equivalent to Term::TailCall.
    //
    // Propagation: spec's terminator chains into another spec that's
    // already tagged. Per-spec analysis uses each block's terminator
    // under this spec's env (spec_fn_types[sid]).
    let tagged_return_specs: std::collections::HashSet<u32> = {
        let mut set: std::collections::HashSet<u32> = std::collections::HashSet::new();
        let any_ty = t.any();
        // Seed: spec has an unresolved TailCallClosure.
        for (sid, &entry) in spec_fnidx.iter().enumerate() {
            let Some(idx) = entry else {
                continue;
            };
            let f = &module.fns[idx];
            for b in &f.blocks {
                if let Term::TailCallClosure {
                    closure,
                    args,
                    ident: _,
                } = &b.terminator
                    && spec_fn_types
                        .get(sid)
                        .and_then(|o| *o)
                        .and_then(|ft| {
                            resolve_tcc_body(t, closure, args, ft, module, &spec_registry)
                                .map(|(_, s)| s)
                        })
                        .is_none()
                {
                    set.insert(sid as u32);
                    break;
                }
            }
        }
        // fz-try.15 — also seed: spec's body is a closure-target body.
        // Closure-target ABI is structurally uniform ValueRef (the seam
        // can't carry typed returns); the body coerces at Term::Return,
        // and every spec of a closure-target fn that's reachable via
        // the closure-target sig returns ValueRef on the wire. Direct
        // callers of zero-cap closure-targets (.siu.1.8 invariant) go
        // through the same body and receive ValueRef too — they unbox
        // locally if they want narrow.
        for (sid, &entry) in spec_fnidx.iter().enumerate() {
            let Some(idx) = entry else {
                continue;
            };
            let fid = module.fns[idx].id;
            if closure_target_fns.contains(&fid) {
                set.insert(sid as u32);
            }
        }
        // Propagation: spec's terminator chains into a tagged spec.
        loop {
            let mut changed = false;
            for (sid, &entry) in spec_fnidx.iter().enumerate() {
                if set.contains(&(sid as u32)) {
                    continue;
                }
                let Some(idx) = entry else {
                    continue;
                };
                let f = &module.fns[idx];
                let propagates = f.blocks.iter().any(|b| match &b.terminator {
                    Term::TailCall { callee, args, .. } => {
                        // Resolve callee's spec sid under this spec's env.
                        let csid = (|| {
                            let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                            let arg_tys: Vec<crate::types::Ty> = args
                                .iter()
                                .map(|av| {
                                    ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                })
                                .collect();
                            spec_registry.resolve(t, *callee, &arg_tys).map(|s| s.0)
                        })()
                        .unwrap_or(callee.0);
                        set.contains(&csid)
                    }
                    Term::TailCallClosure {
                        closure,
                        args,
                        ident: _,
                    } => {
                        let body_sid = spec_fn_types.get(sid).and_then(|o| *o).and_then(|ft| {
                            resolve_tcc_body(t, closure, args, ft, module, &spec_registry)
                                .map(|(_, s)| s)
                        });
                        match body_sid {
                            Some(body_sid) => set.contains(&body_sid),
                            None => true, // unresolved is tagged by definition
                        }
                    }
                    Term::Call { continuation, .. }
                    | Term::CallClosure { continuation, .. }
                    | Term::Receive {
                        continuation,
                        ident: _,
                    } => {
                        // Cont's any-key spec id == continuation.fn_id.0.
                        set.contains(&continuation.fn_id.0)
                    }
                    _ => false,
                });
                if propagates {
                    set.insert(sid as u32);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        set
    };
    // Fn-id-level coarse view for older consumers (tagged_slot0_cont_specs
    // below queries by FnId). True iff ANY spec of the fn is tagged.
    let tagged_return_fns: std::collections::HashSet<crate::fz_ir::FnId> = {
        let mut s = std::collections::HashSet::new();
        for &sid in &tagged_return_specs {
            if let Some(idx) = spec_fnidx[sid as usize] {
                s.insert(module.fns[idx].id);
            }
        }
        s
    };

    // fz-ul4.27.22.3 — cont specs whose producer is a closure-target
    // (or whose producer is a Receive / CallClosure with unknown
    // target) must accept ValueRef at slot 0. The producer returns
    // ValueRef (forced for closure-target; opaque for unknown closure /
    // mailbox), and the cont's wire sig at the seam must agree.
    // fz-ntz extends "closure-target" to "ValueRef-returning"
    // (`tagged_return_fns`) so direct-Calls into a ValueRef-returning
    // fn also force the cont's slot 0 to AnyValue.
    let mut tagged_slot0_cont_specs: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    // fz-uwq.8 — read the producer→cont dispatch facts from
    // `FnTypes.dispatches[Cont]` instead of re-walking terminators and
    // calling `cont_input_key` + `spec_registry.resolve`. The typer
    // already named which `(cont_fn, cont_key)` each Cont site
    // dispatches to (per spec); we just need to know which of those
    // producers are ValueRef-returning, then look up the cont's SpecId.
    for sid_caller in 0..spec_count {
        let Some(caller_idx) = spec_fnidx[sid_caller] else {
            continue;
        };
        let caller = &module.fns[caller_idx];
        // Sentinel slots (closure-target floor with no typer body)
        // have no dispatches.
        let Some(caller_ft) = spec_fn_types[sid_caller] else {
            continue;
        };
        for blk in &caller.blocks {
            // Which terminators produce a ValueRef value into their cont's
            // slot 0? CallClosure / Receive always (opaque closure /
            // mailbox produce ValueRef); Call only when the callee is in
            // `tagged_return_fns` (fz-ntz).
            let Some(term_ident) = blk.terminator.ident() else {
                continue;
            };
            let produces_tagged_slot0 = match &blk.terminator {
                Term::Call { callee, .. } => tagged_return_fns.contains(callee),
                Term::CallClosure { .. } | Term::Receive { .. } => true,
                _ => false,
            };
            if !produces_tagged_slot0 {
                continue;
            }
            let cid = crate::fz_ir::CallsiteId {
                caller: caller.id,
                ident: term_ident.clone(),
                slot: crate::fz_ir::EmitSlot::Cont,
            };
            if let Some((cont_fn, cont_key)) = caller_ft.dispatches.get(&cid)
                && let Some(sid) = spec_registry.resolve_key(t, *cont_fn, cont_key)
            {
                tagged_slot0_cont_specs.insert(sid.0);
            }
        }
    }
    let param_reprs: Vec<Vec<ArgRepr>> = param_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, mut reprs)| {
            if !reprs.is_empty() && tagged_slot0_cont_specs.contains(&(sid as u32)) {
                reprs[0] = ArgRepr::ValueRef;
            }
            reprs
        })
        .collect();
    let return_reprs: Vec<ArgRepr> = return_tys
        .iter()
        .map(|ty| ArgRepr::from_ty(t, ty))
        .collect();
    // fz-cps.1.8 — closure-target spec bodies return ValueRef i64, matching
    // the closure-target sig in §8.2's target clif. fz-ntz extends this
    // to every fn in `tagged_return_fns`: a fn whose only exit is
    // Term::TailCallClosure (or which TailCalls into one) forwards the
    // closure-target's ValueRef return bits through its own outer sig.
    // Declaring that outer return as RawInt/RawF64 would let the
    // caller read tag-shifted bits as a raw number (e.g. 42 → 337).
    let return_reprs: Vec<ArgRepr> = return_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, r)| {
            // fz-ul4.27.22.12 — per-spec override (was per-fn pre-22.12).
            // tagged_return_specs is the precise grain; specs whose
            // TailCallClosure resolves via closure_lit keep their narrow
            // return repr.
            if tagged_return_specs.contains(&(sid as u32)) {
                ArgRepr::ValueRef
            } else {
                r
            }
        })
        .collect();

    // Scheduler-resumed continuations receive only their closure `self`.
    // Message values, pattern binds, and captures live in the closure env,
    // so their Tail-CC sig has zero typed extras before `self`.
    let mut cont_extras_count: HashMap<crate::fz_ir::FnId, usize> = HashMap::new();
    for f in &module.fns {
        for blk in &f.blocks {
            match &blk.terminator {
                Term::Receive { continuation, .. } => {
                    cont_extras_count.insert(continuation.fn_id, 0);
                }
                Term::ReceiveMatched { clauses, after, .. } => {
                    for c in clauses {
                        cont_extras_count.insert(c.body, 0);
                        if let Some(g) = c.guard {
                            cont_extras_count.insert(g, 0);
                        }
                    }
                    if let Some(a) = after {
                        cont_extras_count.insert(a.body, 0);
                    }
                }
                _ => {}
            }
        }
    }

    // fz-ul4.27.6.2.2/.3 — Per-spec Cranelift Signature. Native fns get
    // typed-arity i64s + host_ctx; uniform fns get (i64, i64) -> i64.
    // Sentinel slots get the uniform sig — they're never declared.
    let fn_sigs: Vec<Signature> = (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let is_native = natively_callable.contains(&f.id);
                build_fn_signature(
                    &param_reprs[sid],
                    return_reprs[sid],
                    is_native,
                    cont_fns.contains(&f.id),
                    // fz-cps.1.2: closure-target fn shape gated on
                    // native (uniform closure targets still go through
                    // the existing stub adapter).
                    if is_native {
                        closure_n_captures.get(&f.id).copied()
                    } else {
                        None
                    },
                    cont_extras_count.get(&f.id).copied(),
                )
            }
            None => {
                let mut sig = Signature::new(CallConv::Tail);
                sig.params.push(AbiParam::new(types::I64));
                sig.params.push(AbiParam::new(types::I64));
                sig.returns.push(AbiParam::new(types::I64));
                sig
            }
        })
        .collect();

    // Declare one Cranelift function per real SpecId, named
    // `fz_fn_{spec_id.0}`. Sentinel slots are skipped — no module
    // declaration is made. Any-key SpecId.0 == FnId.0 so the existing
    // closure / Spawn / Receive paths (which iconst fn_id.0 as the
    // schema_id) keep landing on the right entry.
    let linkage = backend.fn_linkage();
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for sid in 0..spec_count {
        if spec_fnidx[sid].is_none() {
            continue;
        }
        let name = format!("fz_fn_{}", sid);
        let id = backend
            .module_mut()
            .declare_function(&name, linkage, &fn_sigs[sid])
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(sid as u32, id);
    }

    let mut mid_flight_cont_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    let mut mid_flight_cont_tail_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> =
        HashMap::new();
    let spec_heap_allocates: Vec<bool> = (0..spec_count)
        .map(|sid| {
            spec_fnidx[sid]
                .map(|idx| fn_may_allocate_heap(&module.fns[idx]))
                .unwrap_or(false)
        })
        .collect();
    for (caller_sid, caller_fid, caller_key) in spec_registry.iter() {
        let Some(caller_idx) = spec_fnidx[caller_sid.0 as usize] else {
            continue;
        };
        let caller_key = caller_key.to_vec();
        let Some(fn_types) = module_types.specs.get(&(caller_fid, caller_key)) else {
            continue;
        };
        let f = &module.fns[caller_idx];
        for blk in &f.blocks {
            if let crate::fz_ir::Term::TailCall {
                ident,
                callee,
                is_back_edge: true,
                ..
            } = &blk.terminator
            {
                if !fn_types.reachable_blocks.contains(&blk.id) {
                    continue;
                };
                if !natively_callable.contains(callee) {
                    continue;
                }
                let cid = crate::fz_ir::CallsiteId {
                    caller: caller_fid,
                    ident: ident.clone(),
                    slot: crate::fz_ir::EmitSlot::Direct,
                };
                let Some(target) = fn_types.dispatches.get(&cid) else {
                    continue;
                };
                let Some(callee_sid) = spec_registry.resolve_key(t, target.0, &target.1) else {
                    continue;
                };
                let callee_sid = callee_sid.0;
                let mut arg_shapes: Vec<MidFlightArgShape> = param_reprs[callee_sid as usize]
                    .iter()
                    .copied()
                    .map(MidFlightArgShape::Value)
                    .collect();
                if closure_n_captures.contains_key(callee) {
                    arg_shapes.push(MidFlightArgShape::HeapRef);
                }
                arg_shapes.push(MidFlightArgShape::HeapRef);
                let key = (callee_sid, arg_shapes);
                if mid_flight_cont_fn_ids.contains_key(&key) {
                    continue;
                }
                let cont_name = format!(
                    "fz_mid_flight_cont_fn_{}_{}",
                    callee_sid,
                    mid_flight_cont_fn_ids.len()
                );
                let mut cont_sig = Signature::new(CallConv::SystemV);
                cont_sig.params.push(AbiParam::new(types::I64));
                cont_sig.returns.push(AbiParam::new(types::I64));
                let cont_id = backend
                    .module_mut()
                    .declare_function(&cont_name, Linkage::Local, &cont_sig)
                    .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_name, e)))?;
                let cont_tail_name = format!("{cont_name}_tail");
                let mut cont_tail_sig = Signature::new(CallConv::Tail);
                cont_tail_sig.params.push(AbiParam::new(types::I64));
                cont_tail_sig.returns.push(AbiParam::new(types::I64));
                let cont_tail_id = backend
                    .module_mut()
                    .declare_function(&cont_tail_name, Linkage::Local, &cont_tail_sig)
                    .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_tail_name, e)))?;
                mid_flight_cont_fn_ids.insert(key.clone(), cont_id);
                mid_flight_cont_tail_fn_ids.insert(key, cont_tail_id);
            }
        }
    }

    // fz-q8d.2 — per-module ConstBitstring symbol cache. Same byte payload
    // across the whole module shares one set of symbols:
    //   * `bytes_id`: the raw payload (Local, read-only).
    //   * `sharedbin_id`: present only for above-threshold payloads — a
    //     40-byte static SharedBin in `.data` with refcount=1 anchor, plus
    //     two relocations (bytes_ptr and the noop destructor). Below-
    //     threshold payloads have `None` here and continue to flow through
    //     `fz_alloc_bitstring_const` for inline / runtime-decided storage.
    let bs_const_data: std::cell::RefCell<HashMap<Vec<u8>, BsConstSyms>> =
        std::cell::RefCell::new(HashMap::new());

    // fz-ul4.42 — set of SpecIds reachable from main + closure-dispatched
    // fns. Specs not in this set get a trap-stub body instead of full
    // codegen. Closure-target specs (those in `closure_shapes`) are seeded
    // explicitly because runtime closure dispatch through code pointers isn't
    // visible to the IR-body BFS. See ir_typer::reachable_specs.
    let reachable: std::collections::HashSet<u32> = crate::ir_typer::reachable_specs(
        t,
        module,
        &spec_registry,
        &module_types,
        closure_shapes.keys().copied(),
    );

    // fz-70q.3 — pre-pass over Term::ReceiveMatched sites.
    //
    //   * `matcher_fn_ids`: one matcher FuncId per site, keyed by
    //     `(fn_id.0, block_id.0)`. Declared up front so the park-site
    //     terminator arm can take a `func_addr` of an as-yet-unemitted
    //     symbol; the body is emitted in a post-fn-loop pass below.
    //   * `cont_extras_count`: per-clause-body / guard / after-body fn
    //     extras count consumed by build_entry_harness today (Tail-CC
    //     inputs ahead of `self`).
    //
    // (`cont_extras_count` is now built up-front above, before fn_sigs.)
    let mut matcher_fn_ids: HashMap<(u32, u32), FuncId> = HashMap::new();
    let mut receive_matched_sites: Vec<(crate::fz_ir::FnId, crate::fz_ir::BlockId)> = Vec::new();
    for f in &module.fns {
        for blk in &f.blocks {
            let Term::ReceiveMatched {
                clauses,
                matcher,
                after,
                pinned,
                captures,
                ..
            } = &blk.terminator
            else {
                continue;
            };
            let name = format!("fz_matcher_fn_{}_b{}", f.id.0, blk.id.0);
            let m_id = super::receive::declare_matcher(backend.module_mut(), &name)?;
            matcher_fn_ids.insert((f.id.0, blk.id.0), m_id);
            receive_matched_sites.push((f.id, blk.id));
            tel.execute(
                &["fz", "codegen", "receive", "site"],
                &crate::measurements! {
                    fn_id: f.id.0 as u64,
                    block_id: blk.id.0 as u64,
                    clause_count: clauses.len() as u64,
                    after_count: if after.is_some() { 1u64 } else { 0u64 },
                    pinned_count: pinned.len() as u64,
                    capture_count: captures.len() as u64,
                    matcher_input_count: matcher.inputs.len() as u64,
                    matcher_prepared_key_count: matcher.prepared_keys.len() as u64,
                    matcher_node_count: matcher.nodes.len() as u64,
                },
                &crate::metadata! {
                    module_path: module.module_path().to_owned(),
                    fn_name: f.name.clone(),
                    matcher: crate::telemetry::value::opaque(matcher),
                },
            );
        }
    }

    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            continue;
        };
        let func_id = *fn_ids.get(&(sid as u32)).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sigs[sid].clone();

        // fz-ul4.42 — unreached spec: emit a trap stub so the symbol exists
        // (other emitted code may name it via fz_fn_{sid}) but the body is
        // a single unreachable trap. Skip the @spec header annotation,
        // verifier, and any further per-spec analysis.
        if !reachable.contains(&(sid as u32)) {
            use cranelift_codegen::ir::TrapCode;
            use cranelift_frontend::FunctionBuilder;
            {
                let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                b.ins().trap(TrapCode::user(1).unwrap());
                b.finalize();
            }
            backend
                .module_mut()
                .define_function(func_id, &mut ctx)
                .map_err(|e| CodegenError::new(format!("define unreached fz_fn_{}: {}", sid, e)))?;
            backend.module_mut().clear_context(&mut ctx);
            continue;
        }
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have FnTypes");
        // fz-ul4.43.B — per-spec fold. Clone the FnIr and fold against this
        // spec's FnTypes so dead arms (TypeTests whose subject is provably
        // inside/outside the test descr in THIS spec's env) collapse before
        // codegen. The pre-codegen `fold_module` already folds the any-key
        // case; this is the multi-spec case it bails on.
        let f_owned: crate::fz_ir::FnIr = {
            let mut clone = module.fns[idx].clone();
            crate::ir_fold::fold_fn_with_types(t, &mut clone, ft);
            // fz-ul4.43.D.1 — per-spec DCE + fuse after per-spec fold.
            // Fold rewrites Term::If→Goto when cond folds; DCE removes the
            // dead stmts and unreachable blocks; fuse_fn collapses the
            // remaining Goto-chains so inline_tail_calls_once's
            // is_pure_tail_caller predicate (single-block + TailCall) can
            // see these tiny per-spec bodies as inlinable.
            crate::ir_dce::dce_fn_with_telemetry(module.module_path(), &mut clone, tel);
            crate::ir_fuse::fuse_fn_with_telemetry(module.module_path(), &mut clone, tel);
            clone
        };
        let f = &f_owned;

        let want_asm = ASM_RECORD.with(|c| c.borrow().is_some());
        if want_asm {
            ctx.set_disasm(true);
        }
        let cg_env = CodegenEnv {
            runtime: &runtime,
            module,
            fn_types: ft,
            spec_registry: &spec_registry,
            fn_ids: &fn_ids,
            mid_flight_cont_tail_fn_ids: &mid_flight_cont_tail_fn_ids,
            spec_heap_allocates: &spec_heap_allocates,
            tuple_schema_ids: &tuple_schema_ids,
            bs_const_data: &bs_const_data,
            param_reprs: &param_reprs,
            return_reprs: &return_reprs,
            natively_callable: &natively_callable,
            cont_target_fns: &cont_target_fns,
            cont_fns: &cont_fns,
            closure_n_captures: &closure_n_captures,
            cont_extras_count: &cont_extras_count,
            matcher_fn_ids: &matcher_fn_ids,
            export_dispatch,
        };
        // Any-key SpecId.0 == FnId.0 (invariant); use the bare fn name so
        // tests / `fz dump --emit clif` can refer to functions by source
        // name. Narrow specs append `_s{sid}` to keep names distinct.
        let display_name = if (sid as u32) == f.id.0 {
            f.name.clone()
        } else {
            format!("{}_s{}", f.name, sid)
        };
        {
            use crate::telemetry::TelemetryExt as _;

            let _span = tel.span(
                &["fz", "codegen", "lower_function"],
                crate::metadata! {
                    body_kind: "fz_spec",
                    module_path: module.module_path().to_owned(),
                    fn_name: display_name.clone(),
                    fn_id: f.id.0 as u64,
                    spec_id: sid as u64,
                },
            );
            compile_fn(
                backend.module_mut(),
                t,
                &mut ctx,
                &mut fbctx,
                &cg_env,
                &schemas,
                f,
                sid as u32,
                &module.source,
            )?;
            let (block_count, instruction_count) = cranelift_body_stats(&ctx.func);
            tel.execute(
                &["fz", "codegen", "function_lowered"],
                &crate::measurements! {
                    fn_id: f.id.0 as u64,
                    spec_id: sid as u64,
                    block_count: block_count as u64,
                    instruction_count: instruction_count as u64,
                    fz_block_count: f.blocks.len() as u64,
                },
                &crate::metadata! {
                    body_kind: "fz_spec",
                    module_path: module.module_path().to_owned(),
                    fn_name: display_name.clone(),
                },
            );
        }
        // fz-ul4.32.1 — annotate raw CLIF with IR types + ArgReprs so
        // `fz dump --emit clif` shows what the typer
        // decided, not just what was lowered.
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                // fz-323 — pin func.name to the real FuncId so the banner
                // `function u0:N(...)` carries the same id space as body
                // refs; cranelift_module's define_function does this
                // assignment anyway, we just need it before display().
                ctx.func.name = ir::UserFuncName::user(0, func_id.as_u32());
                let raw = ctx.func.display().to_string();
                let key_tys = codegen_key_to_tys(t, &spec_keys[sid].1);
                let header = build_typer_header(
                    t,
                    f,
                    ft,
                    &key_tys,
                    &return_tys[sid],
                    &param_reprs[sid],
                    return_reprs[sid],
                );
                let func_names = snapshot_func_names(backend.module_mut().declarations());
                let annotated = VALUE_DESCR_RECORD.with(|vd| {
                    let b = vd.borrow();
                    match b.as_ref() {
                        Some(map) => annotate_clif_dump(&raw, map, &func_names, &header),
                        None => {
                            let empty = HashMap::new();
                            annotate_clif_dump(&raw, &empty, &func_names, &header)
                        }
                    }
                });
                v.push((display_name.clone(), annotated));
            }
        });
        let fn_span = module.source.fn_span_of(f.id);
        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verifier::verify_function(&ctx.func, &flags).map_err(|e| {
            CodegenError::new(format!(
                "verify {}:\n{}\n--- IR ---\n{}",
                display_name,
                e,
                ctx.func.display()
            ))
            .with_span(fn_span)
        })?;
        backend
            .module_mut()
            .define_function(func_id, &mut ctx)
            .map_err(|e| {
                CodegenError::new(format!("define {}: {}", display_name, e)).with_span(fn_span)
            })?;
        if want_asm
            && let Some(cc) = ctx.compiled_code()
            && let Some(vcode) = cc.vcode.as_ref()
        {
            ASM_RECORD.with(|c| {
                if let Some(v) = c.borrow_mut().as_mut() {
                    v.push((display_name.clone(), vcode.clone()));
                }
            });
        }
        backend.module_mut().clear_context(&mut ctx);
    }

    // fz-cps.1.8 — stub compilation loop deleted alongside stub
    // registration. compile_closure_stub itself is dead code until
    // fz-siu.1.13 cleanup; left in place to avoid a noisy delete in this
    // commit.

    // fz-70q.3 — emit matcher fn bodies for every Term::ReceiveMatched
    // site discovered in the pre-pass above. Matchers were declared
    // before the fn-compilation loop so the park-site terminator arm
    // could take `func_addr` of the still-undefined symbols. Bodies are
    // pure leaf fns (no allocation, no extern) per F3; the emitter
    // refuses any clause with a guard.is_some() and points at fz-70q.2.2.
    for (fn_id, blk_id) in &receive_matched_sites {
        let f = module.fn_by_id(*fn_id);
        let blk = f.blocks.iter().find(|b| b.id == *blk_id).unwrap();
        let Term::ReceiveMatched {
            clauses,
            pinned,
            matcher,
            ..
        } = &blk.terminator
        else {
            unreachable!("receive_matched_sites holds only Term::ReceiveMatched terms");
        };
        let m_id = matcher_fn_ids[&(fn_id.0, blk_id.0)];
        let display_name = format!("fz_matcher_fn_{}_b{}", fn_id.0, blk_id.0);
        let (block_count, instruction_count) = {
            use crate::telemetry::TelemetryExt as _;

            let _span = tel.span(
                &["fz", "codegen", "lower_function"],
                crate::metadata! {
                    body_kind: "receive_matcher",
                    module_path: module.module_path().to_owned(),
                    fn_name: display_name.clone(),
                    fn_id: fn_id.0 as u64,
                    block_id: blk_id.0 as u64,
                },
            );
            super::receive::emit_matcher_body_from_matcher(
                backend.module_mut(),
                &mut fbctx,
                m_id,
                module,
                &tuple_schema_ids,
                pinned.as_slice(),
                clauses.as_slice(),
                matcher,
                Some(runtime.value_eq_ref_id),
                Some(runtime.matcher_eq_bytes_id),
                Some(runtime.matcher_map_get_id),
                Some(runtime.matcher_map_get_ref_id),
                Some(runtime.type_of_id),
                Some(runtime.unbox_int_id),
                Some(runtime.unbox_float_id),
                Some(runtime.unbox_atom_id),
                Some(runtime.struct_schema_id_ref_id),
                Some(runtime.truthy_ref_id),
                Some(runtime.box_int_for_any_id),
                Some(runtime.box_float_for_any_id),
                Some(runtime.box_atom_for_any_id),
                Some(runtime.map_is_map_id),
                Some(runtime.bs_reader_init_ref_id),
                Some(runtime.bs_read_field_ref_id),
                Some(runtime.struct_get_field_id),
                Some(runtime.list_is_cons_id),
                Some(runtime.list_head_fallback_id),
                Some(runtime.list_tail_fallback_id),
            )?
        };
        tel.execute(
            &["fz", "codegen", "function_lowered"],
            &crate::measurements! {
                fn_id: fn_id.0 as u64,
                block_id: blk_id.0 as u64,
                block_count: block_count as u64,
                instruction_count: instruction_count as u64,
                clause_count: clauses.len() as u64,
                pinned_count: pinned.len() as u64,
                matcher_input_count: matcher.inputs.len() as u64,
                matcher_prepared_key_count: matcher.prepared_keys.len() as u64,
                matcher_node_count: matcher.nodes.len() as u64,
            },
            &crate::metadata! {
                body_kind: "receive_matcher",
                module_path: module.module_path().to_owned(),
                fn_name: display_name,
                matcher: crate::telemetry::value::opaque(matcher),
            },
        );
    }

    let main_fn_id = module.fn_by_name("main").map(|f| f.id);

    // fz-cps.1.7 — collect zero-capture closure-target specs for static
    // singletons. fz-cps.1.8 — code_ptr is the body's func_addr directly
    // (closure-target sig `(args, self, cont) tail`), not a SystemV stub.
    // The singleton acts both as `self` for direct callers (zero-cap
    // bodies ignore self) and as the closure handed to MakeClosure(fid,
    // []) sites. See docs/cps-in-clif.md §8.2.
    let static_closure_targets: Vec<(u32, u32, FuncId, u32)> = closure_shapes
        .iter()
        .filter(|(_, n_caps)| **n_caps == 0)
        .map(|(cl_sid, _)| {
            let fn_id = spec_keys[*cl_sid as usize].0;
            let body_fid = *fn_ids
                .get(cl_sid)
                .expect("zero-cap closure spec must have a body FuncId");
            // fz-ul4.27.22.6: pack halt_kind so fz_spawn_entry can pick
            // the matching halt-cont singleton at task launch.
            let halt_kind = return_reprs[*cl_sid as usize].halt_kind();
            (*cl_sid, fn_id.0, body_fid, halt_kind)
        })
        .collect();

    let diagnostics = crate::ir_typer::collect_diagnostics(t, module, &module_types);
    // fz-ul4.27.22.3 — per-spec chain analysis: for each registered
    // spec, walk its exit terminators and follow callee resolutions
    // transitively. The chain's halt-seam kind = JOIN of every Return
    // contributing along reachable paths.
    let chain_repr: Vec<ArgRepr> = {
        let join =
            |a: ArgRepr, b: ArgRepr| -> ArgRepr { if a == b { a } else { ArgRepr::ValueRef } };
        let mut chain: Vec<Option<ArgRepr>> = vec![None; spec_count];
        let any_ty = t.any();
        for _ in 0..(spec_count * 4 + 16) {
            let mut changed = false;
            for sid in 0..spec_count {
                let Some(idx) = spec_fnidx[sid] else {
                    continue;
                };
                let f = &module.fns[idx];
                let mut contributions: Vec<ArgRepr> = Vec::new();
                for blk in &f.blocks {
                    match &blk.terminator {
                        Term::Return(_) => {
                            contributions.push(return_reprs[sid]);
                        }
                        Term::TailCall { callee, args, .. } => {
                            let csid = (|| {
                                let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                                let arg_tys: Vec<crate::types::Ty> = args
                                    .iter()
                                    .map(|av| {
                                        ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone())
                                    })
                                    .collect();
                                spec_registry.resolve(t, *callee, &arg_tys).map(|s| s.0)
                            })()
                            .unwrap_or(callee.0);
                            if let Some(c) = chain.get(csid as usize).and_then(|o| *o) {
                                contributions.push(c);
                            }
                        }
                        Term::Call { continuation, .. }
                        | Term::CallClosure { continuation, .. }
                        | Term::Receive {
                            continuation,
                            ident: _,
                        } => {
                            // Cont's chain: under the caller's per-spec
                            // env, the cont's resolved sid via the typer's
                            // cont_input_key (already done elsewhere) —
                            // here we use the cont's any-key as a sound
                            // over-approximation. JOIN refines later.
                            let cont_sid = continuation.fn_id.0;
                            if let Some(c) = chain.get(cont_sid as usize).and_then(|o| *o) {
                                contributions.push(c);
                            }
                        }
                        Term::TailCallClosure {
                            closure,
                            args,
                            ident: _,
                        } => {
                            // fz-ul4.27.22.12 — closure_lit-driven chain
                            // resolution. When this spec's env types the
                            // closure as `closure_lit(F, K)`, the resolved
                            // body's chain feeds ours. Mirrors 22.11's
                            // direct-dispatch resolution but at the
                            // pre-codegen analysis stage so halt_kind
                            // selection (fz_spawn_entry, halt-cont
                            // singletons) picks the right kind.
                            let resolved_body =
                                spec_fn_types.get(sid).and_then(|o| *o).and_then(|ft| {
                                    resolve_tcc_body(t, closure, args, ft, module, &spec_registry)
                                        .map(|(_, s)| s)
                                });
                            match resolved_body {
                                Some(body_sid) => {
                                    if let Some(c) = chain.get(body_sid as usize).and_then(|o| *o) {
                                        contributions.push(c);
                                    }
                                }
                                None => {
                                    // Indirect closure dispatch uses the
                                    // all-ValueRef seam ABI, so anything
                                    // returning through it is ValueRef.
                                    contributions.push(ArgRepr::ValueRef);
                                }
                            }
                        }
                        _ => {}
                    }
                }
                if contributions.is_empty() {
                    continue;
                }
                let joined = contributions.into_iter().reduce(join).unwrap();
                if chain[sid] != Some(joined) {
                    chain[sid] = Some(joined);
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        chain
            .into_iter()
            .map(|o| o.unwrap_or(ArgRepr::ValueRef))
            .collect()
    };
    let fn_halt_kinds: HashMap<u32, u32> = {
        let mut m: HashMap<u32, u32> = HashMap::new();
        for f in &module.fns {
            // Use the fn's any-key spec sid for the entry-time chain.
            let sid = f.id.0 as usize;
            if let Some(r) = chain_repr.get(sid).copied() {
                m.insert(f.id.0, r.halt_kind());
            }
        }
        m
    };
    for ((callee_sid, arg_shapes), stub_id) in mid_flight_cont_fn_ids.clone() {
        let key = (callee_sid, arg_shapes.clone());
        let tail_id = *mid_flight_cont_tail_fn_ids.get(&key).ok_or_else(|| {
            CodegenError::new(format!("missing mid-flight continuation tail {callee_sid}"))
        })?;
        let callee_fid = *fn_ids
            .get(&callee_sid)
            .ok_or_else(|| CodegenError::new(format!("missing callee FuncId {callee_sid}")))?;
        let stub_name = format!("fz_mid_flight_cont_fn_{callee_sid}");
        let mut stub_sig = Signature::new(CallConv::SystemV);
        stub_sig.params.push(AbiParam::new(types::I64));
        stub_sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            stub_sig,
            stub_id,
            move |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let self_bits = b.block_params(entry)[0];
                let tail_ref = m.declare_func_in_func(tail_id, b.func);
                let inst = b.ins().call(tail_ref, &[self_bits]);
                let result = b.inst_results(inst)[0];
                b.ins().return_(&[result]);
            },
        )
        .map_err(|e| CodegenError::new(format!("define {}: {}", stub_name, e)))?;

        let tail_name = format!("fz_mid_flight_cont_fn_{callee_sid}_tail");
        let mut tail_sig = Signature::new(CallConv::Tail);
        tail_sig.params.push(AbiParam::new(types::I64));
        tail_sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(
            backend.module_mut(),
            &mut fbctx,
            tail_sig,
            tail_id,
            move |m, b| {
                let entry = b.create_block();
                b.append_block_params_for_function_params(entry);
                b.switch_to_block(entry);
                b.seal_block(entry);
                let self_bits = b.block_params(entry)[0];
                let mut args =
                    Vec::with_capacity(arg_shapes.iter().map(MidFlightArgShape::abi_arity).sum());
                let get_capture =
                    m.declare_func_in_func(runtime.closure_get_capture_ref_id, b.func);
                for (i, arg_shape) in arg_shapes.iter().enumerate() {
                    let index = b.ins().iconst(types::I64, i as i64);
                    let inst = b.ins().call(get_capture, &[self_bits, index]);
                    let value_ref = b.inst_results(inst)[0];
                    arg_shape.replay_from_capture(
                        b,
                        m,
                        &runtime,
                        CodegenValue::AnyRef(value_ref),
                        &mut args,
                    );
                }
                let mut callee_sig = Signature::new(CallConv::Tail);
                for arg_shape in &arg_shapes {
                    arg_shape.push_param(&mut callee_sig);
                }
                callee_sig.returns.push(AbiParam::new(types::I64));
                let sig_ref = b.func.import_signature(callee_sig);
                let callee_ref = m.declare_func_in_func(callee_fid, b.func);
                let fn_ptr = b.ins().func_addr(types::I64, callee_ref);
                b.ins().return_call_indirect(sig_ref, fn_ptr, &args);
            },
        )
        .map_err(|e| CodegenError::new(format!("define {}: {}", tail_name, e)))?;
    }
    // fz-70q.5.5 — single SystemV `fz_resume(cont) -> i64` shim. Bound
    // args live in the outcome closure env, so the shim sig is fixed
    // regardless of clause arity. Body:
    //     code = call fz_closure_code_ref(cont)
    //     call_indirect Tail(cont) -> i64
    //     return result
    let resume_id: FuncId = {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64)); // cont
        sig.returns.push(AbiParam::new(types::I64));
        let id = backend
            .module_mut()
            .declare_function("fz_resume", Linkage::Local, &sig)
            .map_err(|e| CodegenError::new(format!("declare fz_resume: {}", e)))?;
        emit_fn_body(backend.module_mut(), &mut fbctx, sig, id, |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let cont = b.block_params(entry)[0];
            let code = load_closure_code_ref(b, m, &runtime, cont);
            let mut stub_sig = Signature::new(CallConv::Tail);
            stub_sig.params.push(AbiParam::new(types::I64)); // self
            stub_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = b.func.import_signature(stub_sig);
            let inst = b.ins().call_indirect(sig_ref, code, &[cont]);
            let r = b.inst_results(inst)[0];
            b.ins().return_(&[r]);
        })
        .map_err(|e| CodegenError::new(format!("define fz_resume: {}", e)))?;
        id
    };

    let metadata = CompiledMetadata {
        fn_ids,
        exports_by_id: module
            .exports
            .iter()
            .map(|export| (export.id, export.key.clone()))
            .collect(),
        export_fns: module
            .exports
            .iter()
            .map(|export| (export.key.clone(), export.local_fn))
            .collect(),
        user_schemas,
        frame_sizes,
        atom_names: module.atom_names.clone(),
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
        tuple_arities: tuple_arities.iter().map(|&a| a as u32).collect(),
        diagnostics,
        main_fn_id,
        static_closure_targets,
        spawn_entry_id: runtime.spawn_entry_id,
        main_entry_id: runtime.main_entry_id,
        drain_dtor_entry_id: runtime.drain_dtor_entry_id,
        halt_cont_body_ids: [
            runtime.halt_cont_body_strict_id,
            runtime.halt_cont_body_i64_id,
            runtime.halt_cont_body_f64_id,
        ],
        fn_halt_kinds,
        resume_id,
    };

    // Backend-specific metadata carriers (no-op for JIT; dispatch + main
    // shim + atom blob for AOT) emit before finalize so any data /
    // function declarations land in the same Module that finalize hands
    // off.
    backend.emit_metadata_carriers(&mut fbctx, &metadata)?;
    backend.finalize(metadata)
}
