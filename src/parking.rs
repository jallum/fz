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
pub fn natively_callable(m: &Module, parking: &HashSet<FnId>) -> HashSet<FnId> {
    let mut used_as_cont: HashSet<FnId> = HashSet::new();
    for f in &m.fns {
        for b in &f.blocks {
            match &b.terminator {
                Term::Call { continuation, .. }
                | Term::CallClosure { continuation, .. }
                | Term::Receive { continuation } => {
                    used_as_cont.insert(continuation.fn_id);
                }
                _ => {}
            }
        }
    }
    let main_id = m.fns.iter().find(|f| f.name == "main").map(|f| f.id);

    fn body_only_tail_or_return(f: &crate::fz_ir::FnIr) -> bool {
        f.blocks.iter().all(|b| !matches!(
            b.terminator,
            Term::Call { .. } | Term::CallClosure { .. } | Term::Receive { .. }
        ))
    }

    let mut set = HashSet::new();
    for f in &m.fns {
        if parking.contains(&f.id) { continue; }
        if used_as_cont.contains(&f.id) { continue; }
        if Some(f.id) == main_id { continue; }
        if !body_only_tail_or_return(f) { continue; }
        set.insert(f.id);
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
            if matches!(b.terminator,
                Term::Receive { .. }
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. })
            {
                seed = true;
                break;
            }
            for stmt in &b.stmts {
                let Stmt::Let(_, prim) = stmt;
                if matches!(prim, Prim::MakeClosure(_, _)) {
                    seed = true;
                    break;
                }
            }
            if seed { break; }
        }
        if seed { set.insert(f.id); }
    }

    // Iterate: a fn becomes reachable if it directly calls (Call / TailCall)
    // a reachable fn. Direct call edges only — closure calls were already
    // accounted for above.
    loop {
        let mut changed = false;
        for f in &m.fns {
            if set.contains(&f.id) { continue; }
            let calls_reachable = f.blocks.iter().any(|b| match &b.terminator {
                Term::Call { callee, .. } | Term::TailCall { callee, .. } => {
                    set.contains(callee)
                }
                _ => false,
            });
            if calls_reachable {
                set.insert(f.id);
                changed = true;
            }
        }
        if !changed { break; }
    }

    set
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{Cont, FnBuilder, FnId, ModuleBuilder, Term, Var};

    fn build(fns: Vec<crate::fz_ir::FnIr>) -> Module {
        let mut mb = ModuleBuilder::new();
        for f in fns { mb.add_fn(f); }
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
        b.set_terminator(entry, Term::Receive {
            continuation: Cont { fn_id: FnId(0), captured: vec![] },
        });
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
        g.set_terminator(g_entry, Term::Receive {
            continuation: Cont { fn_id: FnId(2), captured: vec![] },
        });

        let mut f = FnBuilder::new(FnId(1), "f");
        let f_entry = f.block(vec![]);
        f.set_terminator(f_entry, Term::TailCall { callee: FnId(0), args: vec![] });

        // Dummy cont to satisfy structural shape.
        let mut k = FnBuilder::new(FnId(2), "k");
        let v = empty_cont(&mut k);
        let k_entry = k.block(vec![v]);
        k.set_terminator(k_entry, Term::Halt(v));

        let m = build(vec![g.build(), f.build(), k.build()]);
        let s = parking_reachable(&m);
        assert!(s.contains(&FnId(0)), "g (has Receive) should be parking-reachable");
        assert!(s.contains(&FnId(1)), "f (calls g) should be parking-reachable");
        // k is the continuation but contains no receive itself — it gets
        // dispatched by the scheduler, so it's not in the parking set.
        // (Continuations are independent fns; reachability is per-fn.)
        assert!(!s.contains(&FnId(2)), "k (no receive) should not be parking-reachable");
    }

    #[test]
    fn closure_packer_is_parking_reachable() {
        // A fn that builds a closure value is conservatively in the set:
        // the closure might be invoked at a parking-reachable site.
        let mut b = FnBuilder::new(FnId(0), "packer");
        let entry = b.block(vec![]);
        let cl = b.let_(entry, Prim::MakeClosure(FnId(1), vec![]));
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
        let cl = b.let_(entry, Prim::MakeClosure(FnId(1), vec![]));
        b.set_terminator(entry, Term::TailCallClosure { closure: cl, args: vec![] });
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
        main_b.set_terminator(m_entry, Term::TailCall { callee: FnId(1), args: vec![] });

        let helper = make_fn(1, "helper");
        let m = build(vec![main_b.build(), helper]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(nc.contains(&FnId(1)), "helper should be natively-callable");
        assert!(!nc.contains(&FnId(0)), "main is never natively-callable");
    }

    #[test]
    fn natively_callable_excludes_parking_fns() {
        let mut rx = FnBuilder::new(FnId(0), "rx");
        let entry = rx.block(vec![]);
        rx.set_terminator(entry, Term::Receive {
            continuation: Cont { fn_id: FnId(1), captured: vec![] },
        });
        let k = make_fn(1, "k");
        let m = build(vec![rx.build(), k]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(!nc.contains(&FnId(0)), "rx is parking, not natively-callable");
    }

    #[test]
    fn natively_callable_excludes_continuations() {
        // f Term::Calls helper with k as cont. k is the cont and must stay
        // on uniform ABI even though it has no parking or Term::Call.
        let mut f = FnBuilder::new(FnId(0), "f");
        let entry = f.block(vec![]);
        f.set_terminator(entry, Term::Call {
            callee: FnId(1),
            args: vec![],
            continuation: Cont { fn_id: FnId(2), captured: vec![] },
        });
        let helper = make_fn(1, "helper");
        let k = make_fn(2, "k");
        let m = build(vec![f.build(), helper, k]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(!nc.contains(&FnId(2)), "k is used as a continuation");
        assert!(nc.contains(&FnId(1)), "helper is not a cont and can be native");
        assert!(!nc.contains(&FnId(0)), "f has Term::Call exits");
    }

    #[test]
    fn natively_callable_excludes_main() {
        // main with only Return — still excluded because it's main.
        let helper = make_fn(0, "main");
        let m = build(vec![helper]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(!nc.contains(&FnId(0)));
    }

    #[test]
    fn natively_callable_excludes_fn_with_term_call() {
        // A non-cont, non-parking fn that has Term::Call cannot be native
        // in .6.2 (cont dispatch needs uniform ABI). Lifted in .6.3.
        let mut f = FnBuilder::new(FnId(0), "f");
        let entry = f.block(vec![]);
        f.set_terminator(entry, Term::Call {
            callee: FnId(1),
            args: vec![],
            continuation: Cont { fn_id: FnId(2), captured: vec![] },
        });
        let helper = make_fn(1, "helper");
        let k = make_fn(2, "k");
        let m = build(vec![f.build(), helper, k]);
        let parking = parking_reachable(&m);
        let nc = natively_callable(&m, &parking);
        assert!(!nc.contains(&FnId(0)), "f has Term::Call, not native-eligible");
    }
}
