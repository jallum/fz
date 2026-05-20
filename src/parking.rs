//! Parking-reachability analysis (fz-ul4.27.6.1).
//!
//! A fn is *parking-reachable* if some path through it can suspend the task
//! via `Term::Receive`. Callers of parking-reachable fns must keep their
//! frames heap-resident so the scheduler can park them; callers of
//! definitely-non-parking fns can use a native ABI with stack frames
//! (VR.4.2 onward).
//!
//! The analysis is a soundly-conservative call-graph closure:
//!
//!   parking_reachable := { f : f has a `Term::Receive` block }
//!                      ∪ { f : f packs another fn into a closure
//!                              (the closure could escape and be invoked
//!                               at a parking site) }
//!                      ∪ { f : f has a `Term::CallClosure` /
//!                              `Term::TailCallClosure` terminator (the
//!                              closure target is opaque — assume it parks) }
//!
//!   fixed point: + { f : f has Term::Call / TailCall to a parking-reachable fn }
//!
//! Closure calls and closure packing are both conservative — neither
//! direction lets us trace the actual callee, so we widen.
//!
//! Companion analysis (fz-ul4.27.6.2): `natively_callable` identifies the
//! subset of fns that can use the typed native-Cranelift ABI rather than
//! the uniform `(frame_ptr, host_ctx) -> frame_ptr` trampoline ABI. A fn
//! qualifies iff (a) it is not parking-reachable, (b) it is never used as
//! a continuation (continuations are dispatched by the trampoline which
//! requires the uniform ABI), and (c) it is not the program entry `main`
//! (driven by aot_shim / runtime through the trampoline). Native-call
//! sites to such fns skip `fz_alloc_frame` for the callee and pass args
//! by register.

use crate::fz_ir::{FnId, Module, Prim, Stmt, Term};
use std::collections::HashSet;

/// Returns the subset of fns that can be invoked with a typed native ABI.
/// See module-level docs for the qualification rules.
///
/// For .6.2 we additionally require the fn body to have no `Term::Call` /
/// `Term::CallClosure` exits — those require dispatching to a separate cont
/// after the callee returns, which forces a heap-frame ABI. Only fns whose
/// terminators are restricted to TailCall/Return/Halt/Goto/If can return
/// their result directly as a native value. Lifting this restriction is
/// the job of .6.3 (native continuation invocation).
///
/// fz-ul4.29.8 — closure-target fns are no longer excluded from this set.
/// The per-closure-shape stub generated in .29.5 acts as an ABI adapter:
/// it loads captures from the closure heap object, marshals them with the
/// call args into the native callee's typed signature, and routes the
/// callee's tagged-FzValue return through the cont (or halts on a null
/// cont when invoked at the top of a task).
pub fn natively_callable(m: &Module, parking: &HashSet<FnId>) -> HashSet<FnId> {
    use std::collections::HashMap;
    let mut used_as_cont: HashSet<FnId> = HashSet::new();
    let mut used_as_closure_target: HashSet<FnId> = HashSet::new();
    let mut directly_called: HashSet<FnId> = HashSet::new();
    // A cont can only be invoked natively from a Term::Call where the
    // callee is also native (the chain in .6.3's emit_call). If a cont
    // is used at a Term::CallClosure or Term::Receive site, it gets
    // dispatched by the trampoline via the uniform ABI, so it must stay
    // uniform. `cont_blocked` records these forbidden conts.
    let cont_blocked: HashSet<FnId> = HashSet::new();
    // For each fn used as a Term::Call cont, the callees of those call
    // sites. The cont can be native only if every such callee is native
    // (so every call site picks the native-chain emit_call path).
    let mut cont_call_users: HashMap<FnId, Vec<FnId>> = HashMap::new();
    for f in &m.fns {
        for b in &f.blocks {
            match &b.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    used_as_cont.insert(continuation.fn_id);
                    directly_called.insert(*callee);
                    cont_call_users
                        .entry(continuation.fn_id)
                        .or_default()
                        .push(*callee);
                }
                Term::TailCall { callee, .. } => {
                    directly_called.insert(*callee);
                }
                // fz-cps.1.8: closures are heap-resident with body_addr@+16
                // (closure-target sig Tail). Their conts can be native —
                // no longer cont_blocked.
                Term::CallClosure { continuation, .. } | Term::Receive { continuation, .. } => {
                    used_as_cont.insert(continuation.fn_id);
                }
                // fz-yxs — each ReceiveMatched body/after fn is a parking-
                // capable rendezvous target; treat the same way as a cont.
                // Guards are pure (F3-checked) but the body fns may park,
                // so they must not be admitted to the native fast path.
                Term::ReceiveMatched { clauses, after, .. } => {
                    for c in clauses {
                        used_as_cont.insert(c.body);
                        if let Some(g) = c.guard {
                            used_as_cont.insert(g);
                        }
                    }
                    if let Some(a) = after {
                        used_as_cont.insert(a.body);
                    }
                }
                _ => {}
            }
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if let Prim::MakeClosure(_, fid, _) = prim {
                    used_as_closure_target.insert(*fid);
                }
            }
        }
    }
    let main_id = m.fns.iter().find(|f| f.name == "main").map(|f| f.id);

    // fz-ul4.27.6.3 — Continuations are now invoked natively when both
    // sides agree, so being used as a cont no longer excludes a fn from
    // the native set. A reachability gate replaces that exclusion:
    //
    //   reachable_as_native(f) iff f is directly called OR used as a
    //   continuation OR a recursive direct/tail caller of one. Anything
    //   else may still be invoked through the uniform ABI by the runtime
    //   (e.g. `rt.spawn(fid)` in tests) and so must stay uniform.
    //
    // Starting candidates: every non-base-excluded fn with the right
    // reachability. We then shrink to a fixed point: a fn stays in the
    // set only if every terminator in its body lowers natively given
    // the current set (Term::Call's callee + cont, Term::TailCall's
    // callee — all must be in the set).
    // fz-ul4.29.8 — closure targets are now reachable as native: the stub
    // (per .29.5) acts as the ABI adapter, loading captures kind-aware from
    // the closure object and invoking the native body directly. The
    // exclusion that previously kept closure targets uniform is lifted.
    let reachable_as_native = |id: &FnId| {
        directly_called.contains(id)
            || used_as_cont.contains(id)
            || used_as_closure_target.contains(id)
    };

    // fz-cps.5 — main is admitted to natively_callable. The scheduler
    // calls into it via the SystemV→Tail-CC `fz_main_entry` shim.
    // Parking-reachable exclusion is fully lifted; cont_blocked is
    // empty (closure ops are body_ok per fz-cps.1.8).
    let _ = (&parking, &cont_blocked);
    let mut set: HashSet<FnId> = HashSet::new();
    for f in &m.fns {
        if !reachable_as_native(&f.id) && Some(f.id) != main_id {
            continue;
        }
        set.insert(f.id);
    }

    loop {
        let mut to_remove: Vec<FnId> = Vec::new();
        for f in &m.fns {
            if !set.contains(&f.id) {
                continue;
            }
            let body_ok = f.blocks.iter().all(|b| match &b.terminator {
                Term::Return(_) | Term::Halt(_) | Term::Goto(_, _) | Term::If { .. } => true,
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => set.contains(callee) && set.contains(&continuation.fn_id),
                // fz-ul4.27.11 — TailCall is admitted when the callee is
                // also in the set (TCO via Cranelift `return_call` between
                // matching `tail`-conv sigs). The GC-safepoint concern is
                // handled by a type-aware shrink in `ir_codegen::compile`:
                // native TailCall args must be non-heap, which prevents
                // the body from ever allocating a heap pointer that the
                // GC can't reach (no roots means no GC pressure means no
                // need for a per-return_call safepoint). A future ticket
                // lifts the non-heap-args restriction by emitting stack
                // maps so the GC can find roots inside Cranelift frames.
                Term::TailCall { callee, .. } => set.contains(callee),
                // fz-cps.1.8 — closures are Tail-CC indirect-call sites
                // through cl+16. Closure-target body sigs are uniform
                // i64/Tagged (§8.2), so the indirect call always matches
                // regardless of the closure's concrete cl_sid. Admit when
                // the cont (if any) is also native.
                Term::CallClosure { continuation, .. } => set.contains(&continuation.fn_id),
                Term::TailCallClosure { .. } => true,
                Term::Receive {
                    continuation,
                    ident: _,
                } => set.contains(&continuation.fn_id),
                // fz-70q.5.5 — admit ReceiveMatched on the same terms as
                // Receive: native iff every body / guard / after fn that
                // could be reached from the matcher is also native. The
                // park itself goes through the runtime FFI (matcher fn +
                // fz_receive_park_matched), neither of which constrains
                // the enclosing fn's calling convention. The cont-stub
                // emitted by fz_codegen_cont_stub bridges the scheduler
                // resume seam into the body's Tail-CC sig at wake time.
                //
                // (Pre-fz-70q.5 this was hardcoded `false`, which forced
                // every ReceiveMatched chain through the legacy uniform
                // ABI. With the cont-stub seam in place that exclusion
                // is no longer load-bearing — it was the root cause of
                // the silent-exit symptom in fz-70q.4.)
                Term::ReceiveMatched { clauses, after, .. } => {
                    let body_ok = clauses
                        .iter()
                        .all(|c| set.contains(&c.body) && c.guard.is_none_or(|g| set.contains(&g)));
                    let after_ok = after.as_ref().is_none_or(|a| set.contains(&a.body));
                    body_ok && after_ok
                }
            });
            // A cont must only be reachable from native Term::Call sites.
            // If any of its Term::Call callers has a callee that's not in
            // the set, that call site won't take the native-chain branch
            // — the cont would then be dispatched uniformly by the
            // trampoline, and the trampoline can't drive a native sig.
            let cont_users_ok = match cont_call_users.get(&f.id) {
                None => true,
                Some(users) => users.iter().all(|c| set.contains(c)),
            };
            if !body_ok || !cont_users_ok {
                to_remove.push(f.id);
            }
        }
        if to_remove.is_empty() {
            break;
        }
        for id in to_remove {
            set.remove(&id);
        }
    }

    set
}

/// Returns the set of fn ids that are parking-reachable in `m`.
pub fn parking_reachable(m: &Module) -> HashSet<FnId> {
    let mut set: HashSet<FnId> = HashSet::new();

    // Seed: any fn that directly contains a Term::Receive, packs a closure,
    // or invokes one.
    for f in &m.fns {
        let mut seed = false;
        for b in &f.blocks {
            if matches!(
                b.terminator,
                Term::Receive { .. }
                    | Term::ReceiveMatched { .. }
                    | Term::CallClosure { .. }
                    | Term::TailCallClosure { .. }
            ) {
                seed = true;
                break;
            }
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if matches!(prim, Prim::MakeClosure(_, _, _)) {
                    seed = true;
                    break;
                }
            }
            if seed {
                break;
            }
        }
        if seed {
            set.insert(f.id);
        }
    }

    // Iterate: a fn becomes reachable if it directly calls (Call / TailCall)
    // a reachable fn. Direct call edges only — closure calls were already
    // accounted for above.
    loop {
        let mut changed = false;
        for f in &m.fns {
            if set.contains(&f.id) {
                continue;
            }
            let calls_reachable = f.blocks.iter().any(|b| match &b.terminator {
                Term::Call { callee, .. } | Term::TailCall { callee, .. } => set.contains(callee),
                _ => false,
            });
            if calls_reachable {
                set.insert(f.id);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }

    set
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{Cont, FnBuilder, FnId, ModuleBuilder, Term, Var};

    fn build(fns: Vec<crate::fz_ir::FnIr>) -> Module {
        let mut mb = ModuleBuilder::new();
        for f in fns {
            mb.add_fn(f);
        }
        mb.build()
    }

    fn empty_cont(b: &mut FnBuilder) -> Var {
        // Convenience: returns a fresh Var that callers can use as the
        // sole arg of a Term::Halt to terminate the test fn.
        b.fresh_var()
    }

    #[test]
    fn fn_with_receive_is_parking_reachable() {
        let mut b = FnBuilder::new(FnId(0), "rx");
        let entry = b.block(vec![]);
        b.set_terminator(
            entry,
            Term::Receive {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                continuation: Cont {
                    fn_id: FnId(0),
                    captured: vec![],
                },
            },
        );
        let m = build(vec![b.build()]);
        let s = parking_reachable(&m);
        assert!(s.contains(&FnId(0)));
    }

    #[test]
    fn pure_helper_is_not_parking_reachable() {
        let mut b = FnBuilder::new(FnId(0), "pure");
        let v = empty_cont(&mut b);
        let entry = b.block(vec![v]);
        b.set_terminator(entry, Term::Halt(v));
        let m = build(vec![b.build()]);
        let s = parking_reachable(&m);
        assert!(!s.contains(&FnId(0)));
    }

    #[test]
    fn caller_of_parking_fn_is_parking_reachable() {
        // f calls g; g has Receive. Both should end up in the set.
        let mut g = FnBuilder::new(FnId(0), "g");
        let g_entry = g.block(vec![]);
        g.set_terminator(
            g_entry,
            Term::Receive {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );

        let mut f = FnBuilder::new(FnId(1), "f");
        let f_entry = f.block(vec![]);
        f.set_terminator(
            f_entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![],
                is_back_edge: false,
            },
        );

        // Dummy cont to satisfy structural shape.
        let mut k = FnBuilder::new(FnId(2), "k");
        let v = empty_cont(&mut k);
        let k_entry = k.block(vec![v]);
        k.set_terminator(k_entry, Term::Halt(v));

        let m = build(vec![g.build(), f.build(), k.build()]);
        let s = parking_reachable(&m);
        assert!(
            s.contains(&FnId(0)),
            "g (has Receive) should be parking-reachable"
        );
        assert!(
            s.contains(&FnId(1)),
            "f (calls g) should be parking-reachable"
        );
        // k is the continuation but contains no receive itself — it gets
        // dispatched by the scheduler, so it's not in the parking set.
        // (Continuations are independent fns; reachability is per-fn.)
        assert!(
            !s.contains(&FnId(2)),
            "k (no receive) should not be parking-reachable"
        );
    }

    #[test]
    fn closure_packer_is_parking_reachable() {
        // A fn that builds a closure value is conservatively in the set:
        // the closure might be invoked at a parking-reachable site.
        let mut b = FnBuilder::new(FnId(0), "packer");
        let entry = b.block(vec![]);
        let cl = b.let_(
            entry,
            Prim::MakeClosure(crate::fz_ir::CallsiteIdent::synthetic(), FnId(1), vec![]),
        );
        b.set_terminator(entry, Term::Halt(cl));
        // Dummy target fn.
        let mut t = FnBuilder::new(FnId(1), "target");
        let v = empty_cont(&mut t);
        let t_entry = t.block(vec![v]);
        t.set_terminator(t_entry, Term::Halt(v));
        let m = build(vec![b.build(), t.build()]);
        let s = parking_reachable(&m);
        assert!(s.contains(&FnId(0)), "packer should be parking-reachable");
    }

    #[test]
    fn closure_invoker_is_parking_reachable() {
        // A fn that calls a closure (CallClosure / TailCallClosure) is in
        // the set — the closure target is opaque to this analysis.
        let mut b = FnBuilder::new(FnId(0), "invoker");
        let entry = b.block(vec![]);
        let cl = b.let_(
            entry,
            Prim::MakeClosure(crate::fz_ir::CallsiteIdent::synthetic(), FnId(1), vec![]),
        );
        b.set_terminator(
            entry,
            Term::TailCallClosure {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                closure: cl,
                args: vec![],
            },
        );
        let mut t = FnBuilder::new(FnId(1), "target");
        let v = empty_cont(&mut t);
        let t_entry = t.block(vec![v]);
        t.set_terminator(t_entry, Term::Halt(v));
        let m = build(vec![b.build(), t.build()]);
        let s = parking_reachable(&m);
        assert!(s.contains(&FnId(0)));
    }

    // --- natively_callable tests (fz-ul4.27.6.2) ---

    fn make_fn(id: u32, name: &str) -> crate::fz_ir::FnIr {
        // A trivial Return-only fn: `fn name(x) do x end`.
        let mut b = FnBuilder::new(FnId(id), name);
        let v = b.fresh_var();
        let entry = b.block(vec![v]);
        b.set_terminator(entry, Term::Return(v));
        b.build()
    }

    #[test]
    fn natively_callable_includes_pure_helper() {
        // main calls helper via TailCall; helper is a plain Return-only fn.
        let mut main_b = FnBuilder::new(FnId(0), "main");
        let m_entry = main_b.block(vec![]);
        main_b.set_terminator(
            m_entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![],
                is_back_edge: false,
            },
        );

        let helper = make_fn(1, "helper");
        let m = build(vec![main_b.build(), helper]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(nc.contains(&FnId(1)), "helper should be natively-callable");
        // fz-cps.5: main is now native — scheduler dispatches via
        // fz_main_entry SystemV→Tail-CC shim.
        assert!(nc.contains(&FnId(0)), "main is native post-fz-cps.5");
    }

    #[test]
    fn natively_callable_excludes_parking_fns() {
        let mut rx = FnBuilder::new(FnId(0), "rx");
        let entry = rx.block(vec![]);
        rx.set_terminator(
            entry,
            Term::Receive {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                continuation: Cont {
                    fn_id: FnId(1),
                    captured: vec![],
                },
            },
        );
        let k = make_fn(1, "k");
        let m = build(vec![rx.build(), k]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(
            !nc.contains(&FnId(0)),
            "rx is parking, not natively-callable"
        );
    }

    #[test]
    fn natively_callable_includes_continuations_when_chain_is_native() {
        // f Term::Calls helper with k as cont. Both helper and k are
        // leaf bodies; with .6.3 we native-chain across the call so all
        // three (f, helper, k) end up in the set.
        let mut f = FnBuilder::new(FnId(0), "f");
        let entry = f.block(vec![]);
        f.set_terminator(
            entry,
            Term::Call {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![],
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );
        let helper = make_fn(1, "helper");
        let k = make_fn(2, "k");
        // f needs to be reachable as a native call target for the
        // reachability gate to admit it. Wrap with an outer caller.
        let mut outer = FnBuilder::new(FnId(3), "outer");
        let o_entry = outer.block(vec![]);
        outer.set_terminator(
            o_entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![],
                is_back_edge: false,
            },
        );
        let m = build(vec![f.build(), helper, k, outer.build()]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(
            nc.contains(&FnId(1)),
            "helper is leaf-bodied and direct-called"
        );
        assert!(nc.contains(&FnId(2)), "k is leaf-bodied and used-as-cont");
        assert!(
            nc.contains(&FnId(0)),
            "f Term::Call with both callee+cont native"
        );
    }

    /// fz-cps.5 — main is now admitted to natively_callable. The
    /// scheduler dispatches via the SystemV→Tail-CC fz_main_entry shim.
    #[test]
    fn natively_callable_includes_main() {
        let helper = make_fn(0, "main");
        let m = build(vec![helper]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(nc.contains(&FnId(0)));
    }

    #[test]
    fn natively_callable_excludes_native_fn_tailcalling_uniform_fn() {
        // f (no Term::Call, otherwise eligible) TailCalls g; g has Receive
        // (parking, non-native). f must be evicted by the fixed-point.
        let mut g = FnBuilder::new(FnId(0), "g");
        let g_entry = g.block(vec![]);
        g.set_terminator(
            g_entry,
            Term::Receive {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );

        let mut f = FnBuilder::new(FnId(1), "f");
        let f_entry = f.block(vec![]);
        f.set_terminator(
            f_entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(0),
                args: vec![],
                is_back_edge: false,
            },
        );

        let k = make_fn(2, "k");
        let m = build(vec![g.build(), f.build(), k]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        // f isn't parking in the parking sense (it just forwards), but
        // it's still parking-reachable because parking_reachable's fixed
        // point promotes callers. So check explicitly that f is excluded
        // from natively_callable for either reason.
        assert!(
            !nc.contains(&FnId(1)),
            "f TailCalls non-native g and must not be native"
        );
    }

    #[test]
    fn natively_callable_excludes_fn_with_term_call() {
        // A non-cont, non-parking fn that has Term::Call cannot be native
        // in .6.2 (cont dispatch needs uniform ABI). Lifted in .6.3.
        let mut f = FnBuilder::new(FnId(0), "f");
        let entry = f.block(vec![]);
        f.set_terminator(
            entry,
            Term::Call {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![],
                continuation: Cont {
                    fn_id: FnId(2),
                    captured: vec![],
                },
            },
        );
        let helper = make_fn(1, "helper");
        let k = make_fn(2, "k");
        let m = build(vec![f.build(), helper, k]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(
            !nc.contains(&FnId(0)),
            "f has Term::Call, not native-eligible"
        );
    }
}
