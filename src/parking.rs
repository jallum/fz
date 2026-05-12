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

use crate::fz_ir::{FnId, Module, Prim, Stmt, Term};
use std::collections::HashSet;

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
}
