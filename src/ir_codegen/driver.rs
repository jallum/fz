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

fn prepare_codegen_body(module: &Module, fn_idx: usize) -> crate::fz_ir::FnIr {
    module.fns[fn_idx].clone()
}

fn push_reachable_spec<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    spec_registry: &crate::frontend::spec_registry::SpecRegistry,
    reached: &mut std::collections::HashSet<u32>,
    worklist: &mut Vec<u32>,
    fid: FnId,
    key: Vec<crate::types::Ty>,
) {
    let key =
        crate::ir_planner::fn_types::SpecKey::value(fid, crate::types::key_slots_from_tys(key));
    if let Some(next) = spec_registry.resolve_spec_key(t, &key)
        && reached.insert(next.0)
    {
        worklist.push(next.0);
    }
}

fn push_dispatch_target<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    spec_registry: &crate::frontend::spec_registry::SpecRegistry,
    reached: &mut std::collections::HashSet<u32>,
    worklist: &mut Vec<u32>,
    caller: FnId,
    ident: &crate::fz_ir::CallsiteIdent,
    slot: crate::fz_ir::EmitSlot,
    ft: &crate::ir_planner::SpecPlan,
) {
    let cid = crate::fz_ir::CallsiteId {
        caller,
        ident: ident.clone(),
        slot,
    };
    let Some(target) = ft.local_call_target(&cid) else {
        return;
    };
    if let Some(next) = spec_registry.resolve_spec_key(t, target)
        && reached.insert(next.0)
    {
        worklist.push(next.0);
    }
}

fn augment_reachable_for_codegen_bodies<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_registry: &crate::frontend::spec_registry::SpecRegistry,
    module_plan: &crate::ir_planner::ModulePlan,
    codegen_bodies: &[Option<crate::fz_ir::FnIr>],
    reached: &mut std::collections::HashSet<u32>,
) {
    let spec_keys: Vec<_> = spec_registry.iter().map(|(_, key)| key.clone()).collect();
    let ft_of = |sid: u32| -> Option<&crate::ir_planner::SpecPlan> {
        let key = spec_keys.get(sid as usize)?;
        module_plan.specs.get(key)
    };

    let mut worklist: Vec<u32> = reached.iter().copied().collect();
    while let Some(sid) = worklist.pop() {
        let Some(body) = codegen_bodies.get(sid as usize).and_then(Option::as_ref) else {
            continue;
        };
        let Some(ft) = ft_of(sid) else { continue };

        for blk in &body.blocks {
            if !ft.reachable_blocks.contains(&blk.id) {
                continue;
            }
            let env = crate::ir_planner::reachable::env_at_terminator(t, ft, blk, module);
            let any_ty = t.any();
            let arg_tys = |args: &[crate::fz_ir::Var]| -> Vec<crate::types::Ty> {
                args.iter()
                    .map(|av| env.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                    .collect()
            };
            let pad_to_arity = |callee: FnId, mut tys: Vec<crate::types::Ty>| {
                if let Some(&j) = module.fn_idx.get(&callee) {
                    let np = module.fns[j].block(module.fns[j].entry).params.len();
                    while tys.len() < np {
                        tys.push(any_ty.clone());
                    }
                    tys.truncate(np);
                }
                tys
            };
            match &blk.terminator {
                Term::Call {
                    ident,
                    callee,
                    args,
                    continuation,
                    ..
                } => {
                    push_dispatch_target(
                        t,
                        spec_registry,
                        reached,
                        &mut worklist,
                        body.id,
                        ident,
                        crate::fz_ir::EmitSlot::Direct,
                        ft,
                    );
                    push_dispatch_target(
                        t,
                        spec_registry,
                        reached,
                        &mut worklist,
                        body.id,
                        ident,
                        crate::fz_ir::EmitSlot::Cont,
                        ft,
                    );
                    let _ = (callee, args, continuation);
                }
                Term::TailCall {
                    ident,
                    callee,
                    args,
                    ..
                } => {
                    push_dispatch_target(
                        t,
                        spec_registry,
                        reached,
                        &mut worklist,
                        body.id,
                        ident,
                        crate::fz_ir::EmitSlot::Direct,
                        ft,
                    );
                    let _ = (callee, args);
                }
                Term::CallClosure {
                    ident,
                    closure,
                    args,
                    continuation,
                    ..
                } => {
                    if let Some(target) = ft.known_fn(closure) {
                        push_reachable_spec(
                            t,
                            spec_registry,
                            reached,
                            &mut worklist,
                            target,
                            pad_to_arity(target, arg_tys(args)),
                        );
                    }
                    push_dispatch_target(
                        t,
                        spec_registry,
                        reached,
                        &mut worklist,
                        body.id,
                        ident,
                        crate::fz_ir::EmitSlot::Cont,
                        ft,
                    );
                    let _ = continuation;
                }
                Term::TailCallClosure { closure, args, .. } => {
                    if let Some(target) = ft.known_fn(closure) {
                        push_reachable_spec(
                            t,
                            spec_registry,
                            reached,
                            &mut worklist,
                            target,
                            pad_to_arity(target, arg_tys(args)),
                        );
                    }
                }
                Term::Receive {
                    continuation,
                    ident,
                    ..
                } => {
                    push_dispatch_target(
                        t,
                        spec_registry,
                        reached,
                        &mut worklist,
                        body.id,
                        ident,
                        crate::fz_ir::EmitSlot::Cont,
                        ft,
                    );
                    let _ = continuation;
                }
                Term::ReceiveMatched { clauses, after, .. } => {
                    for c in clauses {
                        let key =
                            crate::fz_ir::receive_outcome_spec_key(&any_ty, c.bound_names.len());
                        push_reachable_spec(t, spec_registry, reached, &mut worklist, c.body, key);
                        if let Some(g) = c.guard {
                            let key = crate::fz_ir::receive_outcome_spec_key(
                                &any_ty,
                                c.bound_names.len(),
                            );
                            push_reachable_spec(t, spec_registry, reached, &mut worklist, g, key);
                        }
                    }
                    if let Some(a) = after {
                        let key = crate::fz_ir::receive_outcome_spec_key(&any_ty, 0);
                        push_reachable_spec(t, spec_registry, reached, &mut worklist, a.body, key);
                    }
                }
                _ => {}
            }
        }
    }
}

/// Walk every fn body collecting tuple arities used by MakeTuple /
/// DestTupleBegin / TypeTest descrs, detecting any bitstring prim, then
/// registering a deterministic-id Schema per arity in `user_schemas`.
///
/// Returns `(tuple_arities, tuple_schema_ids, bs_tuple_arity1_schema,
/// bs_tuple_arity3_schema)`. Arity-1 / arity-3 schemas used by the
/// bitstring reader / result tuples are pre-registered when any bs prim
/// is present even if no MakeTuple uses those arities directly. BTreeSet
/// iteration keeps assignment order deterministic so the AOT runtime's
/// ids match what codegen baked in.
fn collect_tuple_arities_and_register_schemas(
    module: &Module,
    user_schemas: &std::cell::RefCell<fz_runtime::heap::SchemaRegistry>,
) -> (
    std::collections::BTreeSet<usize>,
    HashMap<usize, u32>,
    Option<u32>,
    Option<u32>,
) {
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
                    Prim::DestTupleBegin { arity, .. } => {
                        tuple_arities.insert(*arity);
                    }
                    Prim::MakeBitstring(_)
                    | Prim::BitReaderInit(_)
                    | Prim::BitReadField { .. }
                    | Prim::BitReaderDone(_) => {
                        has_bs_prim = true;
                    }
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
    (
        tuple_arities,
        tuple_schema_ids,
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
    )
}

/// The set of fns used as continuations. A cont fn has sig
/// `(result:i64, self:i64) tail` per docs/cps-in-clif.md §2.1 —
/// no host_ctx, no trailing cont param. Its body projects captures
/// from `self`, and its "next k" is one of those captures.
///
/// Clause body / guard / after fns of Term::ReceiveMatched are also
/// included: they get dispatched via cont stub into their Tail-CC entry,
/// so they must wear the cont-fn sig shape. The companion
/// `cont_extras_count` map sets receive outcome bodies to `(self) tail`;
/// bound values and captures live inside the outcome closure env.
fn collect_cont_fns(module: &Module) -> std::collections::HashSet<crate::fz_ir::FnId> {
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
}

/// Set of fns appearing as a MakeClosure target and their capture counts.
/// Per docs/cps-in-clif.md §2.1 these get sig
/// `(args..., self:i64, cont:i64) tail` and their body projects captures
/// from `self`. Disjoint from cont_fns by construction.
///
/// Closure-target sig is universal: every MakeClosure target gets
/// `(args..., self, cont) tail` regardless of whether it is also
/// direct-called. Direct callers load a per-Process static singleton and
/// pass it as `self`. See docs/cps-in-clif.md §8.2.
///
/// Invariant: a closure-target fn that is also direct-called must have
/// zero captures — direct callers have no captures to bind.
fn collect_closure_targets(
    module: &Module,
) -> (
    std::collections::HashSet<crate::fz_ir::FnId>,
    std::collections::HashMap<crate::fz_ir::FnId, usize>,
) {
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
    for fid in &targets {
        if direct_called.contains(fid) {
            debug_assert_eq!(
                counts[fid], 0,
                "fn {} is both direct-called and a non-zero-cap \
                 closure target — direct callers can't supply captures",
                fid.0,
            );
        }
    }
    (targets, counts)
}

/// Per-FnId set: fns invoked from any fz IR site (as a direct callee,
/// a continuation, or a closure target). A fn NOT in this set has no
/// fz IR caller and can only enter via the trampoline entry (which
/// writes null into the frame's slot 0). For such a fn, cont_ptr is
/// statically null at runtime; emit_return can specialize to a
/// halt-only path, skipping the runtime
/// `load v0+16; icmp eq 0; brif` dispatch entirely.
///
/// The contained fns are exactly the "never specializable as halt-only"
/// set.
fn collect_cont_target_fns(module: &Module) -> std::collections::HashSet<crate::fz_ir::FnId> {
    let mut cont_target_fns: std::collections::HashSet<crate::fz_ir::FnId> =
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
                    cont_target_fns.insert(*callee);
                    cont_target_fns.insert(continuation.fn_id);
                }
                Term::TailCall { callee, .. } => {
                    cont_target_fns.insert(*callee);
                }
                Term::CallClosure { continuation, .. } | Term::Receive { continuation, .. } => {
                    cont_target_fns.insert(continuation.fn_id);
                }
                _ => {}
            }
            for stmt in &blk.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, fid, _) = prim {
                    cont_target_fns.insert(*fid);
                }
            }
        }
    }
    cont_target_fns
}

/// Scheduler-resumed continuations receive only their closure `self`.
/// Message values, pattern binds, and captures live in the closure env,
/// so their Tail-CC sig has zero typed extras before `self`.
fn collect_cont_extras_count(module: &Module) -> HashMap<crate::fz_ir::FnId, usize> {
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
    cont_extras_count
}

/// Single combined fixed point over `natively_callable`. Each iter
/// re-enforces every invariant so cascading removals don't leave an
/// inconsistent set:
///   (a) Term::Call's callee + cont both native.
///   (b) Term::TailCall's callee native.
///   (c) Cont validity: if f is used as cont in some Term::Call, the
///       caller's callee at that site must be native (so the site
///       picks the native-chain branch).
fn shrink_natively_callable(
    module: &Module,
    natively_callable: &mut std::collections::HashSet<crate::fz_ir::FnId>,
) {
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
                    natively_callable.contains(callee)
                        && natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCall { callee, .. } => natively_callable.contains(callee),
                // Closure-call terminators admitted; bodies are Tail-CC
                // with closure-target sig. Cont (if any) must also be
                // native so the cont-return chain is unbroken.
                Term::CallClosure { continuation, .. } => {
                    natively_callable.contains(&continuation.fn_id)
                }
                Term::TailCallClosure { .. } => true,
                Term::Receive {
                    continuation,
                    ident: _,
                } => natively_callable.contains(&continuation.fn_id),
                // ReceiveMatched is native iff every body / guard / after
                // fn is native. Cont-stub seam bridges the Tail-CC body
                // into the SystemV scheduler resume path so the
                // enclosing fn's ABI is unconstrained.
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
        // (c) Cont validity: the caller's callee at every cont reach
        // site must be native.
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
}

/// Collect typed closure shapes keyed by the lambda's resolved narrow
/// SpecId. Each `Prim::MakeClosure` site is inspected per *caller*
/// spec (so closures built in different caller specializations with
/// different capture types produce distinct lambda SpecIds → distinct
/// stubs). The key fed to `spec_registry.resolve` is
/// `[capture_descrs..., any, ...]` — padded to the lambda's full
/// arity. The typer registers a narrow spec for every MakeClosure's
/// capture-type tuple, so exact-match resolve succeeds; the any-key
/// remains a subsumption backstop. Value = capture count
/// (== `captured.len()`); needed to split entry params into
/// `[captures..., args...]` at stub declaration / invocation.
fn build_closure_shapes(
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
    spec_registry: &SpecRegistry,
) -> std::collections::BTreeMap<u32, usize> {
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
                    // The lambda body is the any-key body spec
                    // (SpecId.0 == FnId.0 via register_any_key_at).
                    // MakeClosure is construction, not dispatch — look
                    // up the body directly. When the any-key was
                    // dropped, fall back to any registered narrow spec
                    // for this FnId; if none, the closure value has no
                    // live call target (every invocation got inlined to
                    // direct Call) — skip; the null-stub path in
                    // MakeClosure prim codegen handles allocation.
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
                            .find(|(s, key)| {
                                key.fn_id == *lam_fn_id && spec_fnidx[s.0 as usize].is_some()
                            })
                            .map(|(s, _)| s.0)
                    };
                    let Some(cl_sid) = cl_sid else {
                        continue;
                    };
                    closure_shapes.insert(cl_sid, captured.len());
                }
            }
        }
    }
    closure_shapes
}

/// Build per-SpecId frame schemas, refining entry-param kinds from each
/// spec's SpecPlan. The any-key SpecId for FnId K lands at index K
/// (invariant) so any code path that uses fn_id.0 as a schema_id
/// continues to hit the right schema. Sentinel SpecIds (missing-FnId
/// slots) get a zero-field placeholder schema; they're never reached at
/// runtime.
fn build_per_spec_schemas<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
) -> Vec<Schema> {
    let mut schemas: Vec<Schema> = Vec::with_capacity(spec_count);
    for sid in 0..spec_count {
        let Some(idx) = spec_fnidx[sid] else {
            schemas.push(build_frame_schema("__sentinel", &[]));
            continue;
        };
        let f = &module.fns[idx];
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have SpecPlan");
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
        schemas.push(build_frame_schema(&f.name, &kinds));
    }
    schemas
}

/// Per-spec return ABI type comes first from an instantiated declared spec
/// when the function has one, then from the typer's LFP
/// (`module_plan.effective_returns`). The LFP walk filters by
/// `reachable_blocks` AND propagates through every exit terminator
/// including `Term::Call` / `Term::CallClosure` / `Term::Receive`
/// with a continuation; the cont side (`cont_slot0_descr`) already
/// reads declared returns before consulting the same map. Mirroring that
/// precedence here means the producer ABI and the cont's slot-0 ABI agree
/// by construction.
///
/// Halt-only specs converge to `none()` in the LFP; substitute
/// `any` so `ArgRepr::from_descr` doesn't pick RawF64 (none is a
/// subtype of every set, including float). The value never reaches
/// anyone for a halt-only spec, but the ABI must still be valid.
fn derive_return_tys<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &crate::fz_ir::Module,
    spec_keys: &[crate::ir_planner::fn_types::SpecKey],
    spec_fnidx: &[Option<usize>],
    module_plan: &crate::ir_planner::ModulePlan,
) -> Vec<crate::types::Ty> {
    let any = t.any();
    let none = t.none();
    spec_keys
        .iter()
        .enumerate()
        .map(|(sid, key)| {
            if spec_fnidx[sid].is_none() {
                return any.clone();
            }
            if let Some(ret) = declared_return_for_spec_key(t, module, key) {
                return ret;
            }
            let ret = module_plan
                .effective_returns
                .get(key)
                .cloned()
                .unwrap_or_else(|| any.clone());
            if t.is_subtype(&ret, &none) {
                any.clone()
            } else {
                ret
            }
        })
        .collect()
}

fn declared_return_for_spec_key<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &crate::fz_ir::Module,
    key: &crate::ir_planner::fn_types::SpecKey,
) -> Option<crate::types::Ty> {
    let spec = module.declared_specs.get(&key.fn_id)?.exactly_one()?;
    let arg_tys = crate::types::key_slots_to_tys(t, &key.input);
    if spec.params.len() != arg_tys.len() {
        return None;
    }
    let owner = &module.fn_by_id(key.fn_id).owner_module;
    let result = crate::types::instantiate_scheme_result(
        t,
        &spec.params,
        &spec.result,
        &spec.constraints,
        &arg_tys,
    )
    .known()?;
    Some(t.mint_owned_resource_aliases(result, owner, &module.opaque_inners))
}

/// Per-spec entry-param ArgReprs. Drives `build_fn_signature`
/// (AbiParam types) and call-site coerce (raw int / raw f64 vs one-word
/// ValueRef). Sentinel slots get empty params; they're never declared.
///
/// CAPTURE slots [0..n_caps) keep their per-spec narrow reprs. ARG slots
/// honor build_param_reprs' typed output: closure_lit-typed MakeClosure
/// combined with direct return_call dispatch means every closure-call
/// site resolves to a single body spec whose ABI the caller targets
/// exactly. Any concrete `SpecKey` input is authoritative for that entry
/// slot's ABI; the entry var may still be generic while the selected spec
/// is already concrete.
///
/// The indirect fallback path in TailCallClosure still assumes
/// all-ValueRef at the seam, so closures used polymorphically (union of
/// closure_lits, opaque arrow) still go through the ValueRef path
/// correctly: the body's narrow ABI on the direct path is compatible
/// because each direct callsite coerces explicitly.
fn derive_param_reprs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
    spec_keys: &[crate::ir_planner::fn_types::SpecKey],
    cont_fns: &std::collections::HashSet<crate::fz_ir::FnId>,
) -> Vec<Vec<ArgRepr>> {
    (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let ft = spec_fn_types[sid].expect("non-sentinel spec must have SpecPlan");
                if spec_keys[sid].input.iter().all(Option::is_none) {
                    build_param_reprs(t, f, ft)
                } else {
                    build_param_reprs_for_spec(t, f, ft, &spec_keys[sid], cont_fns.contains(&f.id))
                }
            }
            None => Vec::new(),
        })
        .collect()
}

/// Per-spec tagged-return tracking: transitive closure of specs
/// whose return is ValueRef-by-construction. Drives BOTH the
/// return_reprs force AND the tagged_slot0_cont_specs check so
/// producer-side ABI and consumer-side schema stay aligned. One spec of
/// a fn can have a fully-resolved TailCallClosure (returning the body's
/// narrow repr) while a sibling spec's TailCallClosure stays opaque
/// (returning ValueRef through the indirect seam) — per-spec is the
/// precise grain.
///
/// Seed: spec has an UNRESOLVED TailCallClosure (returns through the
/// all-ValueRef indirect ABI), or spec's body is a closure-target body.
/// Closure-target ABI is structurally uniform ValueRef.
///
/// Propagation: spec's terminator chains into another spec that's
/// already tagged. Per-spec analysis uses each block's terminator under
/// this spec's env (spec_fn_types[sid]).
fn compute_tagged_return_specs<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
    spec_registry: &SpecRegistry,
    closure_target_fns: &std::collections::HashSet<crate::fz_ir::FnId>,
) -> std::collections::HashSet<u32> {
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
                        resolve_tcc_body(t, closure, args, ft, module, spec_registry)
                            .map(|(_, s)| s)
                    })
                    .is_none()
            {
                set.insert(sid as u32);
                break;
            }
        }
    }
    // Also seed: spec's body is a closure-target body.
    for (sid, &entry) in spec_fnidx.iter().enumerate() {
        let Some(idx) = entry else {
            continue;
        };
        let fid = module.fns[idx].id;
        if closure_target_fns.contains(&fid) {
            set.insert(sid as u32);
        }
    }
    // Propagation.
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
                    let csid = (|| {
                        let ft = spec_fn_types.get(sid).and_then(|o| *o)?;
                        let arg_tys: Vec<crate::types::Ty> = args
                            .iter()
                            .map(|av| ft.vars.get(av).cloned().unwrap_or_else(|| any_ty.clone()))
                            .collect();
                        let key = crate::ir_planner::fn_types::SpecKey::value(
                            *callee,
                            crate::types::key_slots_from_tys(arg_tys),
                        );
                        spec_registry.resolve_spec_key(t, &key).map(|s| s.0)
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
                        resolve_tcc_body(t, closure, args, ft, module, spec_registry)
                            .map(|(_, s)| s)
                    });
                    match body_sid {
                        Some(body_sid) => set.contains(&body_sid),
                        None => true,
                    }
                }
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive {
                    continuation,
                    ident: _,
                } => set.contains(&continuation.fn_id.0),
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
}

/// Fn-id-level coarse view of `tagged_return_specs` for consumers that
/// query by FnId. True iff ANY spec of the fn is tagged.
fn derive_tagged_return_fns(
    module: &Module,
    spec_fnidx: &[Option<usize>],
    tagged_return_specs: &std::collections::HashSet<u32>,
) -> std::collections::HashSet<crate::fz_ir::FnId> {
    let mut s = std::collections::HashSet::new();
    for &sid in tagged_return_specs {
        if let Some(idx) = spec_fnidx[sid as usize] {
            s.insert(module.fns[idx].id);
        }
    }
    s
}

/// Cont specs whose producer is ValueRef-returning (closure-target,
/// or Receive / CallClosure with unknown target, or any fn in
/// `tagged_return_fns`) must accept ValueRef at slot 0. The producer
/// returns ValueRef and the cont's wire sig at the seam must agree.
///
/// Reads the producer→cont call-edge facts from
/// `SpecPlan.call_edges[Cont]` instead of re-walking terminators and
/// calling `cont_input_key` + `spec_registry.resolve`. The typer already
/// named which `(cont_fn, cont_key)` each Cont site dispatches to
/// (per spec).
fn compute_tagged_slot0_cont_specs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
    spec_registry: &SpecRegistry,
    tagged_return_fns: &std::collections::HashSet<crate::fz_ir::FnId>,
) -> std::collections::HashSet<u32> {
    let mut tagged_slot0_cont_specs: std::collections::HashSet<u32> =
        std::collections::HashSet::new();
    for sid_caller in 0..spec_count {
        let Some(caller_idx) = spec_fnidx[sid_caller] else {
            continue;
        };
        let caller = &module.fns[caller_idx];
        let Some(caller_ft) = spec_fn_types[sid_caller] else {
            continue;
        };
        for blk in &caller.blocks {
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
            if let Some(cont_key) = caller_ft.local_call_target(&cid)
                && let Some(sid) = spec_registry.resolve_spec_key(t, cont_key)
            {
                tagged_slot0_cont_specs.insert(sid.0);
            }
        }
    }
    tagged_slot0_cont_specs
}

/// Per-spec chain analysis: for each registered spec, walk its exit
/// terminators and follow callee resolutions transitively. The chain's
/// halt-seam kind = JOIN of every Return contributing along reachable
/// paths.
///
/// Closure_lit-driven chain resolution: when this spec's env types the
/// closure as `closure_lit(F, K)`, the resolved body's chain feeds ours,
/// so halt_kind selection (fz_entry_thunk, halt-cont singletons) picks
/// the right kind. Indirect closure dispatch uses the all-ValueRef seam
/// ABI, so anything returning through it is ValueRef.
fn compute_chain_repr<
    T: crate::types::Types<Ty = crate::types::Ty> + crate::types::ClosureTypes,
>(
    t: &mut T,
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
    spec_registry: &SpecRegistry,
    return_reprs: &[ArgRepr],
) -> Vec<ArgRepr> {
    let join = |a: ArgRepr, b: ArgRepr| -> ArgRepr { if a == b { a } else { ArgRepr::ValueRef } };
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
                            let key = crate::ir_planner::fn_types::SpecKey::value(
                                *callee,
                                crate::types::key_slots_from_tys(arg_tys),
                            );
                            spec_registry.resolve_spec_key(t, &key).map(|s| s.0)
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
                        let resolved_body =
                            spec_fn_types.get(sid).and_then(|o| *o).and_then(|ft| {
                                resolve_tcc_body(t, closure, args, ft, module, spec_registry)
                                    .map(|(_, s)| s)
                            });
                        match resolved_body {
                            Some(body_sid) => {
                                if let Some(c) = chain.get(body_sid as usize).and_then(|o| *o) {
                                    contributions.push(c);
                                }
                            }
                            None => {
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
}

/// Per-fn halt-kind: looked up via the fn's any-key spec sid for the
/// entry-time chain.
fn derive_fn_halt_kinds(module: &Module, chain_repr: &[ArgRepr]) -> HashMap<u32, u32> {
    let mut m: HashMap<u32, u32> = HashMap::new();
    for f in &module.fns {
        let sid = f.id.0 as usize;
        if let Some(r) = chain_repr.get(sid).copied() {
            m.insert(f.id.0, r.halt_kind());
        }
    }
    m
}

/// Per-spec Cranelift Signature. Native fns get typed-arity i64s +
/// host_ctx; uniform fns get (i64, i64) -> i64. Sentinel slots get the
/// uniform sig — they're never declared.
///
/// Closure-target fn shape is gated on native (uniform closure targets
/// still go through the existing stub adapter).
#[allow(clippy::too_many_arguments)]
fn build_fn_sigs(
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_keys: &[crate::ir_planner::fn_types::SpecKey],
    param_reprs: &[Vec<ArgRepr>],
    return_reprs: &[ArgRepr],
    natively_callable: &std::collections::HashSet<crate::fz_ir::FnId>,
    cont_fns: &std::collections::HashSet<crate::fz_ir::FnId>,
    closure_n_captures: &std::collections::HashMap<crate::fz_ir::FnId, usize>,
    cont_extras_count: &HashMap<crate::fz_ir::FnId, usize>,
) -> Vec<Signature> {
    (0..spec_count)
        .map(|sid| match spec_fnidx[sid] {
            Some(idx) => {
                let f = &module.fns[idx];
                let is_native = natively_callable.contains(&f.id);
                let demand_abi = DemandAbi::new(&spec_keys[sid]);
                build_fn_signature(
                    &param_reprs[sid],
                    return_reprs[sid],
                    is_native,
                    cont_fns.contains(&f.id),
                    if is_native {
                        closure_n_captures.get(&f.id).copied()
                    } else {
                        None
                    },
                    demand_abi.has_list_tail_native_param(is_native, cont_fns.contains(&f.id)),
                    demand_abi
                        .tuple_field_arity()
                        .or_else(|| cont_extras_count.get(&f.id).copied()),
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
        .collect()
}

/// Collect zero-capture closure-target specs for static singletons.
/// code_ptr is the body's func_addr directly (closure-target sig
/// `(args, self, cont) tail`), not a SystemV stub. The singleton acts
/// both as `self` for direct callers (zero-cap bodies ignore self) and
/// as the closure handed to MakeClosure(fid, []) sites. See
/// docs/cps-in-clif.md §8.2.
///
/// Pack halt_kind so fz_entry_thunk can pick the matching halt-cont
/// singleton at task launch.
fn collect_static_closure_targets(
    closure_shapes: &std::collections::BTreeMap<u32, usize>,
    spec_keys: &[crate::ir_planner::fn_types::SpecKey],
    fn_ids: &HashMap<u32, FuncId>,
    return_reprs: &[ArgRepr],
) -> Vec<(u32, u32, FuncId, u32)> {
    closure_shapes
        .iter()
        .filter(|(_, n_caps)| **n_caps == 0)
        .map(|(cl_sid, _)| {
            let fn_id = spec_keys[*cl_sid as usize].fn_id;
            let body_fid = *fn_ids
                .get(cl_sid)
                .expect("zero-cap closure spec must have a body FuncId");
            let halt_kind = return_reprs[*cl_sid as usize].halt_kind();
            (*cl_sid, fn_id.0, body_fid, halt_kind)
        })
        .collect()
}

/// Build the SpecRegistry.
///
/// Register any-keys first, in FnId.0 order — this preserves the
/// invariant `any-key SpecId.0 == FnId.0` so closure / Spawn / Receive
/// paths (and any other "use any-key" path) can keep using fn_id.0
/// directly as a schema_id / Cranelift func key. Narrow specs from
/// `module_plan.specs` get SpecIds ≥ n_fns appended afterwards in a
/// deterministic order (FnId.0, then descr-tuple bytes) so CLIF emission
/// is reproducible across runs.
fn build_spec_registry<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    module_plan: &crate::ir_planner::ModulePlan,
) -> SpecRegistry {
    let mut spec_registry = SpecRegistry::new();
    let mut fns_by_fnid: Vec<&crate::fz_ir::FnIr> = module.fns.iter().collect();
    fns_by_fnid.sort_by_key(|f| f.id.0);
    for f in &fns_by_fnid {
        let n_params = f.block(f.entry).params.len();
        let any_ty = t.any();
        let any_key = f.semantic_key(vec![any_ty; n_params]);
        // Skip registering F's any-key when the typer dropped it (every
        // callsite of F has typed coverage). The next registration via
        // `register_any_key_at` pads slot F.0 with a sentinel
        // automatically, preserving the `SpecId.0 == FnId.0` invariant
        // for the surviving any-keys.
        let spec_key = crate::ir_planner::fn_types::SpecKey::value(f.id, any_key.clone());
        if !module_plan.specs.contains_key(&spec_key) {
            continue;
        }
        let precedence = *module_plan.spec_precedence.get(&spec_key).unwrap_or(&0);
        let sid = spec_registry.register_any_key_at_with_precedence(t, f.id, any_key, precedence);
        debug_assert_eq!(sid.0, f.id.0);
    }
    let any_ty = t.any();
    let mut narrow_keys: Vec<crate::ir_planner::fn_types::SpecKey> = module_plan
        .specs
        .keys()
        .filter(|spec_key| {
            let Some(f) = module.fns.iter().find(|f| f.id == spec_key.fn_id) else {
                return true;
            };
            let n_params = f.block(f.entry).params.len();
            let any_key = f.semantic_key(vec![any_ty.clone(); n_params]);
            // Filter the any-keys (already registered).
            !(spec_key.demand.is_value() && spec_key.input == any_key)
        })
        .cloned()
        .collect();
    narrow_keys.sort_by(|a, b| {
        a.fn_id
            .0
            .cmp(&b.fn_id.0)
            .then_with(|| format!("{:?}", a.input).cmp(&format!("{:?}", b.input)))
            .then_with(|| format!("{:?}", a.demand).cmp(&format!("{:?}", b.demand)))
    });
    for spec_key in narrow_keys {
        let precedence = *module_plan.spec_precedence.get(&spec_key).unwrap_or(&0);
        spec_registry.register_spec_key_with_precedence(t, spec_key, precedence);
    }
    spec_registry
}

/// Build the per-SpecId index tables: `spec_keys` mirrors registry order;
/// `spec_fnidx` maps SpecId.0 → module.fns index (None when the SpecId
/// is a sentinel slot for a missing FnId.0 — cps_split sparsity,
/// pre-existing sentinel padding, or a dropped any-key); `spec_fn_types`
/// borrows the matching SpecPlan from `module_plan.specs` for every
/// non-sentinel slot. Codegen skips compilation for sentinel slots; no
/// consumer can index into them because `resolve` only returns SpecIds
/// with a real registration.
fn build_spec_index_tables<'a>(
    module: &Module,
    spec_registry: &SpecRegistry,
    module_plan: &'a crate::ir_planner::ModulePlan,
) -> (
    Vec<crate::ir_planner::fn_types::SpecKey>,
    Vec<Option<usize>>,
    Vec<Option<&'a crate::ir_planner::SpecPlan>>,
) {
    let spec_keys: Vec<crate::ir_planner::fn_types::SpecKey> =
        spec_registry.iter().map(|(_, key)| key.clone()).collect();
    let mut idx_of: HashMap<FnId, usize> = HashMap::new();
    for (i, f) in module.fns.iter().enumerate() {
        idx_of.insert(f.id, i);
    }
    let spec_fnidx: Vec<Option<usize>> = spec_keys
        .iter()
        .map(|key| {
            if !module_plan.specs.contains_key(key) {
                return None;
            }
            idx_of.get(&key.fn_id).copied()
        })
        .collect();
    let spec_fn_types: Vec<Option<&crate::ir_planner::SpecPlan>> = spec_keys
        .iter()
        .enumerate()
        .map(|(sid, key)| {
            spec_fnidx[sid]?;
            module_plan.specs.get(key)
        })
        .collect();
    (spec_keys, spec_fnidx, spec_fn_types)
}

/// Build the per-SpecId codegen bodies. Non-sentinel specs get the
/// authoritative post-plan module body; sentinel slots get `None`.
fn prepare_codegen_bodies(
    module: &Module,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    spec_fn_types: &[Option<&crate::ir_planner::SpecPlan>],
) -> Vec<Option<crate::fz_ir::FnIr>> {
    let mut codegen_bodies: Vec<Option<crate::fz_ir::FnIr>> = Vec::with_capacity(spec_count);
    for sid in 0..spec_count {
        match (spec_fnidx[sid], spec_fn_types[sid]) {
            (Some(idx), Some(ft)) => {
                let _ = ft;
                codegen_bodies.push(Some(prepare_codegen_body(module, idx)));
            }
            _ => codegen_bodies.push(None),
        }
    }
    codegen_bodies
}

/// Force slot 0 of every cont spec in `tagged_slot0_cont_specs` to
/// ValueRef so the producer's ValueRef return matches the cont's wire
/// sig at the seam.
fn refine_param_reprs_for_tagging(
    param_reprs: Vec<Vec<ArgRepr>>,
    tagged_slot0_cont_specs: &std::collections::HashSet<u32>,
) -> Vec<Vec<ArgRepr>> {
    param_reprs
        .into_iter()
        .enumerate()
        .map(|(sid, mut reprs)| {
            if !reprs.is_empty() && tagged_slot0_cont_specs.contains(&(sid as u32)) {
                reprs[0] = ArgRepr::ValueRef;
            }
            reprs
        })
        .collect()
}

/// Derive per-spec return ArgRepr from `return_tys`, then force ValueRef
/// for every spec in `tagged_return_specs`. Closure-target spec bodies
/// return ValueRef i64, matching the closure-target sig
/// (cps-in-clif.md §8.2). This extends to every fn in
/// `tagged_return_fns`: a fn whose only exit is `Term::TailCallClosure`
/// (or which TailCalls into one) forwards the closure-target's ValueRef
/// return bits through its own outer sig. Declaring that outer return as
/// RawInt/RawF64 would let the caller read tag-shifted bits as a raw
/// number (e.g. 42 → 337).
///
/// `tagged_return_specs` is the precise grain; specs whose
/// `TailCallClosure` resolves via closure_lit keep their narrow return
/// repr.
fn build_return_reprs<T: crate::types::Types<Ty = crate::types::Ty>>(
    t: &mut T,
    return_tys: &[crate::types::Ty],
    tagged_return_specs: &std::collections::HashSet<u32>,
) -> Vec<ArgRepr> {
    return_tys
        .iter()
        .enumerate()
        .map(|(sid, ty)| {
            let r = ArgRepr::from_ty(t, ty);
            if tagged_return_specs.contains(&(sid as u32)) {
                ArgRepr::ValueRef
            } else {
                r
            }
        })
        .collect()
}

/// Emit fz_main_trampoline. The closure-target body for a main-style
/// entry's synthetic inner closure. The inner closure carries the raw
/// `(cont)` main fn pointer in capture[0] (a raw int, so GC never treats it
/// as a heap reference). Closure-target sig `(self, cont) tail`: read main_fp
/// from capture[0] and `call_indirect Tail main_fp(cont)`. This bridges a
/// plain main fn — whose body sig is `(cont)` — into the uniform
/// entry-thunk + `fz_resume` dispatch path without forcing a closure-target
/// body onto the entry fn itself.
fn emit_main_trampoline<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &super::runtime_syms::RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.main_trampoline_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let self_cl = b.block_params(entry)[0];
        let cont = b.block_params(entry)[1];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        // capture[0] holds the raw `(cont)` main fn pointer (raw int).
        let zero = cg.b.ins().iconst(types::I64, 0);
        let main_fp = cg.closure_capture_i64(self_cl, zero);
        let mut main_sig = Signature::new(CallConv::Tail);
        main_sig.params.push(AbiParam::new(types::I64));
        main_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(main_sig);
        let inst = cg.b.ins().call_indirect(sig_ref, main_fp, &[cont]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_main_trampoline: {}", e)))
}

/// Emit fz_drain_dtor_entry. SystemV scheduler-callable shim that
/// invokes a 1-arg resource dtor closure with its payload. Picks a
/// Strict halt-cont via fz_get_halt_cont, reads the body addr through
/// the closure ABI, and Tail-CC indirect-calls
/// `(payload_ref, closure, halt_cl)`. Result is discarded by the caller.
/// Sig: `(closure:i64, payload_ref:i64) -> i64 system_v`.
fn emit_drain_dtor_entry<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &super::runtime_syms::RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64));
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.drain_dtor_entry_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let closure = b.block_params(entry)[0];
        let payload_ref = b.block_params(entry)[1];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        // Strict halt-cont (kind=0). Dtor return is discarded;
        // ValueRef avoids RawInt/F64 unboxing.
        let strict_addr = cg.func_addr(runtime.halt_cont_body_strict_id);
        let zero = cg.b.ins().iconst(types::I32, 0);
        let halt_cl = cg.get_halt_cont(strict_addr, zero);
        let code = cg.closure_code_ref(closure);
        // Closure-target body sig: `(args..., self, cont) tail -> i64`.
        // Generic args are one-word ValueRefs.
        let mut closure_sig = Signature::new(CallConv::Tail);
        closure_sig.params.push(AbiParam::new(types::I64)); // x ValueRef
        closure_sig.params.push(AbiParam::new(types::I64)); // self
        closure_sig.params.push(AbiParam::new(types::I64)); // cont
        closure_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(closure_sig);
        let inst =
            cg.b.ins()
                .call_indirect(sig_ref, code, &[payload_ref, closure, halt_cl]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_drain_dtor_entry: {}", e)))
}

/// Emit fz_entry_thunk. The uniform first-entry wrapper for a freshly
/// spawned task. A task's `runnable` is an entry thunk whose single capture
/// is the task's inner closure (a user lambda for `spawn_closure`, or the
/// synthetic `fz_main_trampoline` closure for a main-style entry). The
/// scheduler resumes the thunk through the one `fz_resume` shim, so the thunk
/// has the resume-shaped closure-target sig `(self) -> i64 tail`. The body
/// reads the inner closure from capture[0], picks the halt-cont matching the
/// inner closure's halt_kind, and tail-calls the inner body `(inner, halt_cl)`
/// — exactly the launch the retired `fz_spawn_entry` performed, but driven
/// off the captured inner instead of a scheduler argument.
///
/// Closure metadata layout:
///   off 0  : kind (u16)         off 4  : size_bytes (u32)
///   off 2  : flags (u16)        off 8  : schema_id (u32)
///                               off 12 : _reserved (u32)
/// flags low 14 bits = captured_count; high 2 bits = halt_kind.
fn emit_entry_thunk<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &super::runtime_syms::RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.entry_thunk_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let self_cl = b.block_params(entry)[0];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        // capture[0] is the inner closure to launch.
        let zero_idx = cg.b.ins().iconst(types::I64, 0);
        let closure = cg.closure_capture_ref(self_cl, zero_idx);
        let kind = cg.closure_halt_kind_ref(closure);
        // Select halt_cont_body_addr by kind. Branchless via three
        // func_addrs + a tiny dispatch — keeps the thunk a leaf.
        let a_strict = cg.func_addr(runtime.halt_cont_body_strict_id);
        let a_i64 = cg.func_addr(runtime.halt_cont_body_i64_id);
        let a_f64 = cg.func_addr(runtime.halt_cont_body_f64_id);
        let one = cg.b.ins().iconst(types::I32, 1);
        let two = cg.b.ins().iconst(types::I32, 2);
        let is_i64 = cg.b.ins().icmp(IntCC::Equal, kind, one);
        let is_f64 = cg.b.ins().icmp(IntCC::Equal, kind, two);
        let pick_i64_or_tagged = cg.b.ins().select(is_i64, a_i64, a_strict);
        let hcb_addr = cg.b.ins().select(is_f64, a_f64, pick_i64_or_tagged);
        let halt_cl = cg.get_halt_cont(hcb_addr, kind);
        // Read inner closure body addr through the runtime ABI and invoke as
        // closure-target sig `(self, cont) tail` (zero user args).
        let code = cg.closure_code_ref(closure);
        let mut closure_sig = Signature::new(CallConv::Tail);
        closure_sig.params.push(AbiParam::new(types::I64)); // self
        closure_sig.params.push(AbiParam::new(types::I64)); // cont
        closure_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(closure_sig);
        let inst = cg.b.ins().call_indirect(sig_ref, code, &[closure, halt_cl]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_entry_thunk: {}", e)))
}

/// Emit three fz_halt_cont_body fns, one per repr. Generic ValueRef
/// bodies receive `(value_ref, self)`; RawInt / RawF64 variants stay
/// narrow as `(value, self)`.
fn emit_halt_cont_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &super::runtime_syms::RuntimeRefs,
) -> Result<(), CodegenError> {
    let mut sig = Signature::new(CallConv::Tail);
    push_repr_param(&mut sig, ArgRepr::ValueRef);
    sig.params.push(AbiParam::new(types::I64));
    sig.returns.push(AbiParam::new(types::I64));
    emit_fn_body(m, fbctx, sig, runtime.halt_cont_body_strict_id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let value_ref = b.block_params(entry)[0];
        let hi_fref = m.declare_func_in_func(runtime.halt_implicit_ref_id, b.func);
        let process = b.ins().get_pinned_reg(types::I64);
        b.ins().call(hi_fref, &[process, value_ref]);
        let zero = b.ins().iconst(types::I64, 0);
        b.ins().return_(&[zero]);
    })
    .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
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
        emit_fn_body(m, fbctx, sig, body_id, |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let val = b.block_params(entry)[0];
            let hi_fref = m.declare_func_in_func(halt_impl_id, b.func);
            let process = b.ins().get_pinned_reg(types::I64);
            b.ins().call(hi_fref, &[process, val]);
            let zero = b.ins().iconst(types::I64, 0);
            b.ins().return_(&[zero]);
        })
        .map_err(|e| CodegenError::new(format!("define halt_cont_body: {}", e)))?;
    }
    Ok(())
}

/// Single SystemV `fz_resume(cont) -> i64` shim. Bound args live in
/// the outcome closure env, so the shim sig is fixed regardless of
/// clause arity. Body:
///     code = call fz_closure_code_ref(cont)
///     call_indirect Tail(cont) -> i64
///     return result
fn emit_resume<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &super::runtime_syms::RuntimeRefs,
) -> Result<FuncId, CodegenError> {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // cont
    sig.returns.push(AbiParam::new(types::I64));
    let id = m
        .declare_function("fz_resume", Linkage::Local, &sig)
        .map_err(|e| CodegenError::new(format!("declare fz_resume: {}", e)))?;
    emit_fn_body(m, fbctx, sig, id, |m, b| {
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let cont = b.block_params(entry)[0];
        let mut shim_cache = CodegenCache::default();
        let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
        let code = cg.closure_code_ref(cont);
        let mut stub_sig = Signature::new(CallConv::Tail);
        stub_sig.params.push(AbiParam::new(types::I64)); // self
        stub_sig.returns.push(AbiParam::new(types::I64));
        let sig_ref = cg.b.func.import_signature(stub_sig);
        let inst = cg.b.ins().call_indirect(sig_ref, code, &[cont]);
        let r = cg.b.inst_results(inst)[0];
        cg.b.ins().return_(&[r]);
    })
    .map_err(|e| CodegenError::new(format!("define fz_resume: {}", e)))?;
    Ok(id)
}

/// Declare one Cranelift function per real SpecId, named
/// `fz_fn_{spec_id.0}`. Sentinel slots are skipped — no module
/// declaration is made. Any-key SpecId.0 == FnId.0 so the existing
/// closure / Spawn / Receive paths (which iconst fn_id.0 as the
/// schema_id) keep landing on the right entry.
fn declare_spec_fns<M: cranelift_module::Module>(
    m: &mut M,
    linkage: Linkage,
    spec_count: usize,
    spec_fnidx: &[Option<usize>],
    fn_sigs: &[Signature],
) -> Result<HashMap<u32, FuncId>, CodegenError> {
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for sid in 0..spec_count {
        if spec_fnidx[sid].is_none() {
            continue;
        }
        let name = format!("fz_fn_{}", sid);
        let id = m
            .declare_function(&name, linkage, &fn_sigs[sid])
            .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(sid as u32, id);
    }
    Ok(fn_ids)
}

/// Pre-pass over Term::ReceiveMatched sites: one matcher FuncId per
/// site, keyed by `(fn_id.0, block_id.0)`. Declared up front so the
/// park-site terminator arm can take a `func_addr` of an as-yet-unemitted
/// symbol; the body is emitted in a post-fn-loop pass.
type MatcherFnIds = HashMap<(u32, u32), FuncId>;
type ReceiveMatchedSites = Vec<(crate::fz_ir::FnId, crate::fz_ir::BlockId)>;
type MidFlightContFnIds = HashMap<(u32, Vec<MidFlightArgShape>), FuncId>;

fn declare_matcher_fns<M: cranelift_module::Module>(
    m: &mut M,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<(MatcherFnIds, ReceiveMatchedSites), CodegenError> {
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
            let m_id = super::receive::declare_matcher(m, &name)?;
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
    Ok((matcher_fn_ids, receive_matched_sites))
}

/// Emit matcher fn bodies for every Term::ReceiveMatched site
/// discovered in the pre-pass above. Matchers were declared before the
/// fn-compilation loop so the park-site terminator arm could take
/// `func_addr` of the still-undefined symbols. Bodies are pure leaf fns
/// (no allocation, no extern); the emitter refuses any clause with a
/// guard.
#[allow(clippy::too_many_arguments)]
fn emit_matcher_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    module: &Module,
    runtime: &super::runtime_syms::RuntimeRefs,
    tuple_schema_ids: &HashMap<usize, u32>,
    matcher_fn_ids: &HashMap<(u32, u32), FuncId>,
    receive_matched_sites: &[(crate::fz_ir::FnId, crate::fz_ir::BlockId)],
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<(), CodegenError> {
    for (fn_id, blk_id) in receive_matched_sites {
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
                m,
                fbctx,
                m_id,
                module,
                tuple_schema_ids,
                pinned.as_slice(),
                clauses.as_slice(),
                matcher,
                &super::receive::MatcherRuntimeHelpers {
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
    Ok(())
}

/// Emit SystemV stub + Tail-CC body for every declared mid-flight
/// continuation. The SystemV stub bridges scheduler-resume into Tail-CC;
/// the tail body replays each argument from the closure capture array
/// and `return_call_indirect`s the callee body with its narrow ABI.
fn emit_mid_flight_cont_bodies<M: cranelift_module::Module>(
    m: &mut M,
    fbctx: &mut FunctionBuilderContext,
    runtime: &super::runtime_syms::RuntimeRefs,
    fn_ids: &HashMap<u32, FuncId>,
    mid_flight_cont_fn_ids: &HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
    mid_flight_cont_tail_fn_ids: &HashMap<(u32, Vec<MidFlightArgShape>), FuncId>,
) -> Result<(), CodegenError> {
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
        emit_fn_body(m, fbctx, stub_sig, stub_id, move |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let self_bits = b.block_params(entry)[0];
            let tail_ref = m.declare_func_in_func(tail_id, b.func);
            let inst = b.ins().call(tail_ref, &[self_bits]);
            let result = b.inst_results(inst)[0];
            b.ins().return_(&[result]);
        })
        .map_err(|e| CodegenError::new(format!("define {}: {}", stub_name, e)))?;

        let tail_name = format!("fz_mid_flight_cont_fn_{callee_sid}_tail");
        let mut tail_sig = Signature::new(CallConv::Tail);
        tail_sig.params.push(AbiParam::new(types::I64));
        tail_sig.returns.push(AbiParam::new(types::I64));
        emit_fn_body(m, fbctx, tail_sig, tail_id, move |m, b| {
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let self_bits = b.block_params(entry)[0];
            let mut args =
                Vec::with_capacity(arg_shapes.iter().map(MidFlightArgShape::abi_arity).sum());
            let mut shim_cache = CodegenCache::default();
            let mut cg = CodegenFn::for_runtime_shim(runtime, b, m, &mut shim_cache);
            for (i, arg_shape) in arg_shapes.iter().enumerate() {
                let value_ref = cg.closure_capture_ref_at(self_bits, i);
                arg_shape.replay_from_capture(&mut cg, CodegenValue::AnyRef(value_ref), &mut args);
            }
            let mut callee_sig = Signature::new(CallConv::Tail);
            for arg_shape in &arg_shapes {
                arg_shape.push_param(&mut callee_sig);
            }
            callee_sig.returns.push(AbiParam::new(types::I64));
            let sig_ref = cg.b.func.import_signature(callee_sig);
            let fn_ptr = cg.func_addr(callee_fid);
            cg.b.ins().return_call_indirect(sig_ref, fn_ptr, &args);
        })
        .map_err(|e| CodegenError::new(format!("define {}: {}", tail_name, e)))?;
    }
    Ok(())
}

/// Declare SystemV + Tail-CC stubs for every back-edge TailCall to a
/// native callee. Each (callee_sid, arg_shapes) tuple uniquely keys a
/// pair of mid-flight continuation FuncIds; the SystemV stub bridges
/// scheduler-resume into Tail-CC and the Tail-CC body replays the saved
/// arguments before tail-calling the callee. Returns the two FuncId maps
/// consumed by the body-emission pass.
#[allow(clippy::too_many_arguments)]
fn declare_mid_flight_conts<
    T: crate::types::Types<Ty = crate::types::Ty>,
    M: cranelift_module::Module,
>(
    t: &mut T,
    m: &mut M,
    module: &Module,
    module_plan: &crate::ir_planner::ModulePlan,
    spec_registry: &SpecRegistry,
    spec_fnidx: &[Option<usize>],
    param_reprs: &[Vec<ArgRepr>],
    natively_callable: &std::collections::HashSet<crate::fz_ir::FnId>,
    closure_n_captures: &std::collections::HashMap<crate::fz_ir::FnId, usize>,
) -> Result<(MidFlightContFnIds, MidFlightContFnIds), CodegenError> {
    let mut mid_flight_cont_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> = HashMap::new();
    let mut mid_flight_cont_tail_fn_ids: HashMap<(u32, Vec<MidFlightArgShape>), FuncId> =
        HashMap::new();
    for (caller_sid, caller_key) in spec_registry.iter() {
        let Some(caller_idx) = spec_fnidx[caller_sid.0 as usize] else {
            continue;
        };
        let Some(fn_types) = module_plan.specs.get(caller_key) else {
            continue;
        };
        let f = &module.fns[caller_idx];
        for blk in &f.blocks {
            if let crate::fz_ir::Term::TailCall {
                ident,
                callee,
                args,
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
                    caller: caller_key.fn_id,
                    ident: ident.clone(),
                    slot: crate::fz_ir::EmitSlot::Direct,
                };
                let Some(target) = fn_types.local_call_target(&cid) else {
                    continue;
                };
                let Some(callee_sid) = spec_registry.resolve_spec_key(t, target) else {
                    continue;
                };
                let callee_sid = callee_sid.0;
                let mut arg_shapes: Vec<MidFlightArgShape> = param_reprs[callee_sid as usize]
                    .iter()
                    .take(args.len())
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
                let cont_id = m
                    .declare_function(&cont_name, Linkage::Local, &cont_sig)
                    .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_name, e)))?;
                let cont_tail_name = format!("{cont_name}_tail");
                let mut cont_tail_sig = Signature::new(CallConv::Tail);
                cont_tail_sig.params.push(AbiParam::new(types::I64));
                cont_tail_sig.returns.push(AbiParam::new(types::I64));
                let cont_tail_id = m
                    .declare_function(&cont_tail_name, Linkage::Local, &cont_tail_sig)
                    .map_err(|e| CodegenError::new(format!("declare {}: {}", cont_tail_name, e)))?;
                mid_flight_cont_fn_ids.insert(key.clone(), cont_id);
                mid_flight_cont_tail_fn_ids.insert(key, cont_tail_id);
            }
        }
    }
    Ok((mid_flight_cont_fn_ids, mid_flight_cont_tail_fn_ids))
}

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
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<B::Output, CodegenError> {
    if let Some(edge) = module.external_call_edges.first() {
        return Err(CodegenError::new(format!(
            "unresolved external module call `{}`",
            edge.target
        )));
    }

    let runtime = declare_runtime_symbols(backend.module_mut())?;

    let mut fbctx = FunctionBuilderContext::new();

    emit_main_trampoline(backend.module_mut(), &mut fbctx, &runtime)?;
    emit_drain_dtor_entry(backend.module_mut(), &mut fbctx, &runtime)?;
    emit_entry_thunk(backend.module_mut(), &mut fbctx, &runtime)?;
    emit_halt_cont_bodies(backend.module_mut(), &mut fbctx, &runtime)?;

    // Register a heap Schema for every tuple arity used by MakeTuple, so the
    // GC tracer can walk fields and so codegen can iconst the schema_id.
    // Also detect any bitstring prim so we can pre-register arity-1 / arity-3
    // schemas used by the reader / result tuples even if no MakeTuple uses
    // those arities directly.
    //
    // BTreeSet so iteration order is deterministic. Schema ids are assigned
    // by registration order; the AOT runtime registers in the same sorted
    // order so its ids match what codegen baked into the CLIF.
    let user_schemas = std::rc::Rc::new(std::cell::RefCell::new(
        fz_runtime::heap::SchemaRegistry::new(),
    ));
    user_schemas.borrow_mut().closure_env(0);
    let (tuple_arities, tuple_schema_ids, bs_tuple_arity1_schema, bs_tuple_arity3_schema) =
        collect_tuple_arities_and_register_schemas(module, &user_schemas);
    let named_schema_ids = {
        let mut ids = HashMap::new();
        let mut reg = user_schemas.borrow_mut();
        for (name, fields) in &module.struct_schemas {
            let id = reg.register(fz_runtime::heap::Schema::named_struct(
                name.clone(),
                fields.clone(),
            ));
            ids.insert(name.clone(), id);
        }
        ids
    };

    // frame_sizes is computed after `schemas` is built (post-spec_registry).

    // Run the typer ahead of codegen so per-fn Var->type info is
    // available during lowering.
    let mut working = module.clone();
    // Lower known-target CallClosure / TailCallClosure to direct
    // Call / TailCall, then erase any module-constant zero-capture closure
    // that now survives only as a threaded value (its entry-param slots,
    // matching call args, continuation captures, and the dead MakeClosure).
    // After this, the final plan_module sees direct dispatch where the
    // closure-stub used to live, and the erased lambda is no longer a
    // closure-target — so the inliner below splices it and the lazy-cont
    // gate sees a closure-free frame.
    //
    // Both transforms read only callable capabilities + per-fn effects — never
    // effective returns, call edges, or dead branches — so this derives a
    // capability-only plan, not a full specializing one. It is interprocedural
    // over the linked working module (so provider-library entry params carry
    // KnownFn capabilities the shallow pretyped `_pre_types` cannot see) but
    // skips the return-type fixpoint, and emits no `planner.planned` event. The
    // authoritative plan is derived once, below, after these transforms settle —
    // there is no longer a second specializing plan here (fz-hfc.3 / inv1).
    let capabilities = crate::ir_planner::plan_callable_capabilities(t, &working);
    crate::ir_planner::rewrite_known_target_closures(t, &mut working, &capabilities);
    #[cfg(not(test))]
    crate::ir_inline::inline_module_with_plan(&mut working, &capabilities);
    #[cfg(test)]
    if !INLINE_DISABLED.with(|d| d.get()) {
        crate::ir_inline::inline_module_with_plan(&mut working, &capabilities);
    }
    crate::ir_fuse::fuse_blocks_with_telemetry(&mut working, tel);
    // Compile-time reducer pass. Folds calls whose return is statically
    // known; reduces If-on-bool-literal to Goto. Runs after
    // ir_inline + ir_fuse so it sees a cleaner call graph.
    // See docs/bodies-are-boundaries.md.
    //
    // Reducer returns a ReducerLog consumed by the dump pipeline, not
    // by codegen; codegen drives reduction only for its rewriting effect.
    #[cfg(not(test))]
    let _ = crate::ir_reducer::reduce_module_with_telemetry(t, &mut working, tel);
    #[cfg(test)]
    if !REDUCER_DISABLED.with(|d| d.get()) {
        let _ = crate::ir_reducer::reduce_module_with_telemetry(t, &mut working, tel);
    }
    // Single-use cont collapse runs pre-planner, alongside the other
    // call-shape mutations (`fuse_blocks`, `reduce_module`). The
    // `debug_assert_unique_conts` check at the end of `ir_lower`
    // guarantees this pass sees each continuation fn exactly once, so it
    // can be applied before the planner commits to specs. See
    // `.agent/docs/dispatch-as-planner-output.md` (Worry 1).
    crate::ir_inline::inline_single_use_conts(&mut working);
    // Honour `:: never`: cut dead tails after diverging calls (e.g. inlined
    // `assert`'s `panic` branch) so the single authoritative plan below — and
    // the codegen that reads it — never see a reachable ⊥-typed tail.
    crate::ir_diverge::truncate_diverging_blocks(module.module_path(), &mut working, tel);
    let shaping_plan = crate::ir_planner::plan_module_with_role(t, &working, tel, "shaping");
    // Fold one-sided-dead Ifs to Gotos and singleton prims before the
    // authoritative plan. These rewrites change block topology, so codegen's
    // dispatch facts must be produced from the settled body, not remapped after
    // the fact.
    crate::ir_branch_fold::fold_module_with_telemetry(&mut working, &shaping_plan, tel);
    crate::ir_fold::fold_module(&mut working, &shaping_plan);
    // Fold byte-literal MakeBitstring into ConstBitstring before DCE so
    // the per-byte Const(Int) operand stmts go dead in the same pass.
    crate::ir_const_bs::fold_module(&mut working);
    crate::ir_dce::dce_module_with_telemetry(&mut working, tel);
    // Sweep IR fns unreachable from main after inlining.
    crate::ir_dce::dce_module_level(&mut working);
    let mut module_plan = crate::ir_planner::plan_module(t, &working, tel);
    // Snapshot per-fn call-shape multisets after the authoritative planner
    // commits to specs. Later codegen-local rewrites may consume call shapes
    // but must not invent new ones.
    #[cfg(debug_assertions)]
    let call_shapes_pre = super::invariants::snapshot_call_shapes(&working);
    // Destination lowering desugars MakeTuple/MakeList/MakeMap/MapUpdate into
    // token-linear Dest* sequences. It is intra-block, adds no blocks and no
    // call edges, and preserves every original construction *result* var —
    // already typed by the authoritative plan above. Its only new SSA names are
    // dest holders and init tokens, which codegen lowers from runtime value
    // bindings, never from plan types. So the authoritative plan stays valid for
    // everything codegen reads after lowering: no post-destination re-plan, and
    // no reconciliation of a second plan against the first (fz-hfc.4 / inv1).
    crate::ir_dest::lower_destinations(&mut working);
    crate::ir_dest::verify_module(&working).map_err(|errors| {
        CodegenError::new(format!(
            "destination-passing IR invariant failed:\n{}",
            errors
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join("\n")
        ))
    })?;
    #[cfg(debug_assertions)]
    super::invariants::assert_no_new_call_shapes(&working, &call_shapes_pre);
    let diagnostics = crate::ir_extern_marshal::resolve_module_types(t, &working, &mut module_plan);
    if let Some(diagnostic) = diagnostics.into_iter().next() {
        return Err(CodegenError::new(diagnostic.message).with_span(diagnostic.primary.span));
    }
    let module = &working;

    let spec_registry = build_spec_registry(t, module, &module_plan);
    let spec_count = spec_registry.len();
    let (spec_keys, spec_fnidx, spec_fn_types) =
        build_spec_index_tables(module, &spec_registry, &module_plan);

    let closure_shapes = build_closure_shapes(
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        &spec_registry,
    );

    // Parking + native-callability analyses. Consumed at declare-time
    // below for per-fn sigs and at compile_fn / emit_call for ABI
    // bifurcation.
    let parking_reachable = crate::parking::parking_reachable(module);
    let mut natively_callable = crate::parking::natively_callable(module, &parking_reachable);

    let cont_fns = collect_cont_fns(module);
    let _ = &cont_fns; // consumed by sig builder + entry harness below.

    // Set of fns appearing as a MakeClosure target. Per
    // docs/cps-in-clif.md §2.1 these get sig `(args..., self:i64, cont:i64)
    // tail` and their body projects captures from `self`. Disjoint
    // from cont_fns by construction (conts are anonymous continuations
    // synthesized by the lowerer; MakeClosure targets are user lambdas
    // or top-level fns passed as values). If overlap occurs in some
    // future fz-IR, cont-fn shape wins (Receive parking would otherwise
    // misread the result slot).
    let (closure_target_fns, closure_n_captures) = collect_closure_targets(module);
    let _ = (&closure_target_fns, &closure_n_captures);
    shrink_natively_callable(module, &mut natively_callable);

    let cont_target_fns = collect_cont_target_fns(module);

    let schemas = build_per_spec_schemas(t, module, spec_count, &spec_fnidx, &spec_fn_types);

    // Per-spec frame sizes (consumed by `fz_alloc_frame_dyn` and the AOT
    // frame-size dispatch fn). Indexed by SpecId.0.
    let frame_sizes: Vec<u32> = schemas
        .iter()
        .map(|s| s.allocation_payload_size() as u32)
        .collect();

    let return_tys = derive_return_tys(t, module, &spec_keys, &spec_fnidx, &module_plan);

    let param_reprs = derive_param_reprs(
        t,
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        &spec_keys,
        &cont_fns,
    );
    let _ = &closure_n_captures;
    let tagged_return_specs = compute_tagged_return_specs(
        t,
        module,
        &spec_fnidx,
        &spec_fn_types,
        &spec_registry,
        &closure_target_fns,
    );
    let tagged_return_fns = derive_tagged_return_fns(module, &spec_fnidx, &tagged_return_specs);
    let tagged_slot0_cont_specs = compute_tagged_slot0_cont_specs(
        t,
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        &spec_registry,
        &tagged_return_fns,
    );
    let param_reprs = refine_param_reprs_for_tagging(param_reprs, &tagged_slot0_cont_specs);
    let return_reprs = build_return_reprs(t, &return_tys, &tagged_return_specs);

    let cont_extras_count = collect_cont_extras_count(module);

    let fn_sigs = build_fn_sigs(
        module,
        spec_count,
        &spec_fnidx,
        &spec_keys,
        &param_reprs,
        &return_reprs,
        &natively_callable,
        &cont_fns,
        &closure_n_captures,
        &cont_extras_count,
    );

    let linkage = backend.fn_linkage();
    let fn_ids = declare_spec_fns(
        backend.module_mut(),
        linkage,
        spec_count,
        &spec_fnidx,
        &fn_sigs,
    )?;

    let (mid_flight_cont_fn_ids, mid_flight_cont_tail_fn_ids) = declare_mid_flight_conts(
        t,
        backend.module_mut(),
        module,
        &module_plan,
        &spec_registry,
        &spec_fnidx,
        &param_reprs,
        &natively_callable,
        &closure_n_captures,
    )?;

    // Per-module ConstBitstring symbol cache. Same byte payload across
    // the whole module shares one set of symbols:
    //   * `bytes_id`: the raw payload (Local, read-only).
    //   * `sharedbin_id`: present only for above-threshold payloads — a
    //     40-byte static SharedBin in `.data` with refcount=1 anchor, plus
    //     two relocations (bytes_ptr and the noop destructor). Below-
    //     threshold payloads have `None` here and continue to flow through
    //     `fz_alloc_bitstring_const` for inline / runtime-decided storage.
    let bs_const_data: std::cell::RefCell<HashMap<Vec<u8>, BsConstSyms>> =
        std::cell::RefCell::new(HashMap::new());

    let codegen_bodies = prepare_codegen_bodies(module, spec_count, &spec_fnidx, &spec_fn_types);

    // Set of SpecIds reachable from main + closure-dispatched fns.
    // Specs not in this set get a trap-stub body instead of full
    // codegen. Closure-target specs (those in `closure_shapes`) are seeded
    // explicitly because runtime closure dispatch through code pointers isn't
    // visible to the IR-body BFS. See ir_planner::reachable_specs.
    let mut reachable: std::collections::HashSet<u32> = crate::ir_planner::reachable_specs(
        t,
        module,
        &spec_registry,
        &module_plan,
        closure_shapes.keys().copied(),
    );
    // Per-spec folding can turn a reachable `Call + Cont` into a direct
    // `TailCall` to the continuation spec. Augment from the exact folded
    // bodies codegen will emit so dead-spec pruning cannot leave a trap stub
    // behind a generated direct edge.
    augment_reachable_for_codegen_bodies(
        t,
        module,
        &spec_registry,
        &module_plan,
        &codegen_bodies,
        &mut reachable,
    );

    let (matcher_fn_ids, receive_matched_sites) =
        declare_matcher_fns(backend.module_mut(), module, tel)?;
    let verifier_isa = host_isa();

    for sid in 0..spec_count {
        let Some(_idx) = spec_fnidx[sid] else {
            continue;
        };
        let func_id = *fn_ids.get(&(sid as u32)).unwrap();
        let mut ctx = backend.module_mut().make_context();
        ctx.func.signature = fn_sigs[sid].clone();

        // Unreached spec: emit a trap stub so the symbol exists (other
        // emitted code may name it via fz_fn_{sid}) but the body is a
        // single unreachable trap. Skip the @spec header annotation,
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
        let ft = spec_fn_types[sid].expect("non-sentinel spec must have SpecPlan");
        // Per-spec fold + DCE + fuse: dead arms (TypeTests whose subject
        // is provably inside/outside the test descr in THIS spec's env)
        // collapse before codegen. The pre-codegen `fold_module` already
        // folds the any-key case; this is the multi-spec case it bails on.
        // Reuses the precomputed body used by codegen reachability so the
        // emitted body and trap-stub pruning derive from the same call
        // graph.
        let f = codegen_bodies[sid]
            .as_ref()
            .expect("reachable real spec must have a prepared body");

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
            tuple_schema_ids: &tuple_schema_ids,
            named_schema_ids: &named_schema_ids,
            bs_const_data: &bs_const_data,
            param_reprs: &param_reprs,
            return_reprs: &return_reprs,
            spec_keys: &spec_keys,
            natively_callable: &natively_callable,
            cont_target_fns: &cont_target_fns,
            cont_fns: &cont_fns,
            closure_n_captures: &closure_n_captures,
            cont_extras_count: &cont_extras_count,
            matcher_fn_ids: &matcher_fn_ids,
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
        // Annotate raw CLIF with IR types + ArgReprs so
        // `fz dump --emit clif` shows what the typer decided, not just
        // what was lowered.
        IR_TEXT_RECORD.with(|c| {
            if let Some(v) = c.borrow_mut().as_mut() {
                // Pin func.name to the real FuncId so the banner
                // `function u0:N(...)` carries the same id space as
                // body refs; cranelift_module's define_function does
                // this assignment anyway, we just need it before display().
                ctx.func.name = ir::UserFuncName::user(0, func_id.as_u32());
                let raw = ctx.func.display().to_string();
                let key_tys = codegen_key_to_tys(t, &spec_keys[sid].input);
                let header = build_typer_header(
                    t,
                    f,
                    ft,
                    &key_tys,
                    &spec_keys[sid].demand,
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
        cranelift_codegen::verifier::verify_function(&ctx.func, verifier_isa.as_ref()).map_err(
            |e| {
                CodegenError::new(format!(
                    "verify {}:\n{}\n--- IR ---\n{}",
                    display_name,
                    e,
                    ctx.func.display()
                ))
                .with_span(fn_span)
            },
        )?;
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

    emit_matcher_bodies(
        backend.module_mut(),
        &mut fbctx,
        module,
        &runtime,
        &tuple_schema_ids,
        &matcher_fn_ids,
        &receive_matched_sites,
        tel,
    )?;

    let main_fn_id = module.fn_by_name("main").map(|f| f.id);

    let static_closure_targets =
        collect_static_closure_targets(&closure_shapes, &spec_keys, &fn_ids, &return_reprs);

    let diagnostics = crate::ir_planner::collect_diagnostics(t, module, &module_plan, tel);
    let chain_repr = compute_chain_repr(
        t,
        module,
        spec_count,
        &spec_fnidx,
        &spec_fn_types,
        &spec_registry,
        &return_reprs,
    );
    let fn_halt_kinds = derive_fn_halt_kinds(module, &chain_repr);
    emit_mid_flight_cont_bodies(
        backend.module_mut(),
        &mut fbctx,
        &runtime,
        &fn_ids,
        &mid_flight_cont_fn_ids,
        &mid_flight_cont_tail_fn_ids,
    )?;
    let resume_id = emit_resume(backend.module_mut(), &mut fbctx, &runtime)?;

    let metadata = CompiledMetadata {
        fn_ids,
        user_schemas,
        frame_sizes,
        atom_names: module.atom_names.clone(),
        bs_tuple_arity1_schema,
        bs_tuple_arity3_schema,
        tuple_arities: tuple_arities.iter().map(|&a| a as u32).collect(),
        named_schemas: module
            .struct_schemas
            .iter()
            .map(|(name, fields)| (name.clone(), fields.clone()))
            .collect(),
        diagnostics,
        main_fn_id,
        static_closure_targets,
        entry_thunk_id: runtime.entry_thunk_id,
        main_trampoline_id: runtime.main_trampoline_id,
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
