//! Honour `:: never` by truncating control flow after a diverging call.
//!
//! A call to a `:: never` extern (e.g. `fz_panic`) does not return, so any
//! statement or terminator after it in the same block is unreachable.
//! Inlining a function with a never-branch — `assert`'s `else: panic` is the
//! canonical case — splices that never value into the caller's continuation,
//! leaving a reachable-but-dead tail-call whose argument is bottom-typed. The
//! planner cannot give that callsite a call edge (its argument is `none`) and
//! codegen then panics when it tries to emit the dead terminator.
//!
//! This pass makes the IR honour `never` by construction: a block is cut at
//! its first diverging call and re-terminated with `Halt`, so the dead tail
//! never reaches the planner or codegen.

use crate::fz_ir::{ExternId, ExternTy, Module, Prim, Stmt, Term};
use crate::telemetry::Telemetry;
use std::collections::HashSet;

/// Truncate every block at its first `:: never` extern call.
pub fn truncate_diverging_blocks(module_path: &str, m: &mut Module, tel: &dyn Telemetry) {
    let never: HashSet<ExternId> = m
        .externs
        .iter()
        .filter(|e| e.ret == ExternTy::Never)
        .map(|e| e.id)
        .collect();
    if never.is_empty() {
        return;
    }
    for f in &mut m.fns {
        for b in &mut f.blocks {
            let cut = b
                .stmts
                .iter()
                .position(|Stmt::Let(_, prim)| matches!(prim, Prim::Extern(_, eid, _) if never.contains(eid)));
            let Some(idx) = cut else { continue };
            let Stmt::Let(result, _) = b.stmts[idx];
            // No dead tail: the diverging call is already the block's last
            // statement and the block halts on its result. There is nothing to
            // cut, so skip it rather than report a truncation that didn't happen.
            let nothing_to_cut = idx + 1 == b.stmts.len() && matches!(b.terminator, Term::Halt(v) if v == result);
            if nothing_to_cut {
                continue;
            }
            b.stmts.truncate(idx + 1);
            b.terminator = Term::Halt(result);
            tel.execute(
                &["fz", "ir", "diverge", "block_truncated"],
                &crate::measurements! {
                    fn_id: f.id.0 as u64,
                    block_id: b.id.0 as u64,
                },
                &crate::metadata! {
                    module_path: module_path.to_owned(),
                    fn_name: f.name.clone(),
                },
            );
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::Span;
    use crate::fz_ir::{
        CallsiteIdent, Const, ExternArg, ExternDecl, ExternId, FnBuilder, FnId, ModuleBuilder, Term, Var,
    };
    use crate::telemetry::{Capture, ConfiguredTelemetry};
    use crate::types::{ConcreteTypes, Types};

    const TRUNCATED: &[&str] = &["fz", "ir", "diverge", "block_truncated"];

    /// Declare `fz_panic :: never` as extern 0 on the module.
    fn push_panic_extern(m: &mut Module, panic_id: ExternId) {
        let mut ct = ConcreteTypes;
        let any = Types::any(&mut ct);
        m.externs.push(ExternDecl {
            id: panic_id,
            fz_name: "fz_panic".into(),
            symbol: "fz_panic".into(),
            params: vec![ExternTy::Any],
            variadic: false,
            ret: ExternTy::Never,
            ret_descr: any,
        });
        m.extern_idx.insert(panic_id, 0);
    }

    fn tail_call(callee: FnId, args: Vec<Var>) -> Term {
        Term::TailCall {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee,
            args,
            is_back_edge: false,
        }
    }

    /// Run the pass under a capturing telemetry so tests can read the
    /// `block_truncated` signal as well as the resulting IR.
    fn run(m: &mut Module) -> Capture {
        let tel = ConfiguredTelemetry::new();
        let cap = Capture::new();
        tel.attach(&[], cap.handler());
        truncate_diverging_blocks("test", m, &tel);
        cap
    }

    /// A block whose first statement is a `:: never` call, followed by a dead
    /// statement and a tail-call, is cut to `[nil-const, never-call]` +
    /// `Halt(result)` and reports exactly one truncation.
    #[test]
    fn truncates_dead_tail_after_never_call() {
        let panic_id = ExternId(0);
        let mut b = FnBuilder::new(FnId(0), "caller");
        let entry = b.block(vec![]);
        let arg = b.let_(entry, Prim::Const(Const::Nil));
        let result = b.let_(
            entry,
            Prim::Extern(
                CallsiteIdent::synthetic(),
                panic_id,
                vec![ExternArg::fixed(arg, ExternTy::Any)],
            ),
        );
        // Dead code after the diverging call: another const + a tail-call.
        let _dead = b.let_(entry, Prim::Const(Const::Int(7)));
        b.set_terminator(entry, tail_call(FnId(1), vec![result]));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        push_panic_extern(&mut m, panic_id);

        let cap = run(&mut m);

        let entry_block = m.fns[0].block(m.fns[0].entry);
        assert_eq!(
            entry_block.stmts.len(),
            2,
            "stmts cut to [nil-const, never-call]; dead const dropped"
        );
        assert!(
            matches!(entry_block.terminator, Term::Halt(v) if v == result),
            "block re-terminated with Halt on the diverging call's result"
        );
        assert_eq!(cap.count(TRUNCATED), 1, "one block_truncated event");
    }

    /// A block whose diverging call is already the terminator has no dead tail:
    /// the pass leaves it untouched and reports no truncation.
    #[test]
    fn already_terminal_diverging_block_emits_no_event() {
        let panic_id = ExternId(0);
        let mut b = FnBuilder::new(FnId(0), "caller");
        let entry = b.block(vec![]);
        let arg = b.let_(entry, Prim::Const(Const::Nil));
        let result = b.let_(
            entry,
            Prim::Extern(
                CallsiteIdent::synthetic(),
                panic_id,
                vec![ExternArg::fixed(arg, ExternTy::Any)],
            ),
        );
        b.set_terminator(entry, Term::Halt(result));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();
        push_panic_extern(&mut m, panic_id);

        let cap = run(&mut m);

        let entry_block = m.fns[0].block(m.fns[0].entry);
        assert_eq!(entry_block.stmts.len(), 2, "block left intact");
        assert!(matches!(entry_block.terminator, Term::Halt(v) if v == result));
        assert_eq!(
            cap.count(TRUNCATED),
            0,
            "no truncation reported when there is nothing to cut"
        );
    }

    /// A block with no `:: never` call is untouched and reports nothing.
    #[test]
    fn leaves_ordinary_blocks_alone() {
        let mut b = FnBuilder::new(FnId(0), "caller");
        let entry = b.block(vec![]);
        let v = b.let_(entry, Prim::Const(Const::Int(1)));
        b.set_terminator(entry, tail_call(FnId(1), vec![v]));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();

        let cap = run(&mut m);

        let entry_block = m.fns[0].block(m.fns[0].entry);
        assert!(matches!(entry_block.terminator, Term::TailCall { callee: FnId(1), .. }));
        assert_eq!(cap.count(TRUNCATED), 0);
    }
}
