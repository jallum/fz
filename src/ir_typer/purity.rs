// ----------------------------------------------------------------------
// fz-e4u — pure-codegen subset check
// ----------------------------------------------------------------------
//
// Used by fz-recv to enforce that pattern arms and guard expressions in
// `receive do … end` lower only to read-only / non-allocating primitives.
// When this property holds for an expression, its compiled matcher can be
// invoked from the sender thread (per docs/receive-matched.md §2.3,
// §3.4) with no allocator interaction, no FFI re-entry, and no GC race.
//
// The check is a pure structural walk over `&[Stmt]` and an optional
// terminator. It does **not** consult the typer's worklist results; it
// runs strictly on the IR produced by lowering. fz-yxs (E2) wires the
// check into the `Term::ReceiveMatched` typer rule.
//
// The API below is consumed by `collect_diagnostics`' Term::ReceiveMatched
// guard scan (fz-yxs).

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpureKind {
    /// The prim allocates on the per-process heap. Variant name is the
    /// offending Prim's variant label for diagnostics.
    Allocates(&'static str),
    /// `Prim::Extern(_)` — any FFI call. Even a side-effect-free FFI is
    /// rejected because the check has no way to verify its body, and a
    /// rogue FFI can allocate, send, receive, or re-enter the scheduler.
    Extern,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpureTerm {
    /// `Call` / `TailCall` / `CallClosure` / `TailCallClosure` — invoke
    /// arbitrary user code with arbitrary effects.
    Call,
    /// `Receive` — a matcher invoking receive would deadlock the scheduler.
    Receive,
    /// `Halt` — exits the task; meaningless inside a matcher.
    Halt,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ImpureError {
    Stmt { index: usize, kind: ImpureKind },
    Term(ImpureTerm),
}

/// True iff `p` is in the pure-codegen subset. See module-level comment
/// for the rationale; see `docs/receive-matched.md §2.3` for the design
/// constraint this enforces.
pub fn prim_is_pure(p: &crate::fz_ir::Prim) -> Result<(), ImpureKind> {
    use crate::fz_ir::Prim::*;
    match p {
        Const(_)
        | BinOp(_, _, _)
        | UnOp(_, _)
        | ListHead(_)
        | ListTail(_)
        | IsEmptyList(_)
        | TupleField(_, _)
        | MapGet(_, _)
        | MatcherMapGet(_, _)
        | IsMatcherMapMiss(_)
        | BitReaderInit(_)
        | BitReadField { .. }
        | BitReaderDone(_)
        | TypeTest(_, _)
        | Brand(_, _) => Ok(()),

        MakeTuple(_) => Err(ImpureKind::Allocates("MakeTuple")),
        MakeList(_, _) => Err(ImpureKind::Allocates("MakeList")),
        MakeClosure(_, _, _) => Err(ImpureKind::Allocates("MakeClosure")),
        MakeMap(_) => Err(ImpureKind::Allocates("MakeMap")),
        MapUpdate(_, _) => Err(ImpureKind::Allocates("MapUpdate")),
        MakeBitstring(_) => Err(ImpureKind::Allocates("MakeBitstring")),
        ConstBitstring(_, _) => Err(ImpureKind::Allocates("ConstBitstring")),

        Extern(_, _) => Err(ImpureKind::Extern),
    }
}

/// Walk every Let-bound Prim in `stmts`; first offender wins.
pub fn check_pure_codegen(stmts: &[crate::fz_ir::Stmt]) -> Result<(), ImpureError> {
    use crate::fz_ir::Stmt;
    for (i, s) in stmts.iter().enumerate() {
        let Stmt::Let(_, p) = s;
        prim_is_pure(p).map_err(|kind| ImpureError::Stmt { index: i, kind })?;
    }
    Ok(())
}

/// Only Goto / If / Return are allowed in matcher / guard lowering.
pub fn check_pure_term(term: &crate::fz_ir::Term) -> Result<(), ImpureError> {
    use crate::fz_ir::Term::*;
    match term {
        Goto(_, _) | If { .. } | Return(_) => Ok(()),
        Call { .. } | TailCall { .. } | CallClosure { .. } | TailCallClosure { .. } => {
            Err(ImpureError::Term(ImpureTerm::Call))
        }
        Receive { .. } | ReceiveMatched { .. } => Err(ImpureError::Term(ImpureTerm::Receive)),
        Halt(_) => Err(ImpureError::Term(ImpureTerm::Halt)),
    }
}

#[cfg(test)]
mod purity_tests {
    use super::*;
    use crate::fz_ir::{BinOp, BlockId, BranchOrigin, Const, ExternId, Prim, Stmt, Term, Var};
    use crate::types::Types;

    fn v(n: u32) -> Var {
        Var(n)
    }
    fn s(p: Prim) -> Stmt {
        Stmt::Let(v(0), p)
    }

    #[test]
    fn pure_const_int_accepted() {
        assert!(check_pure_codegen(&[s(Prim::Const(Const::Int(42)))]).is_ok());
    }

    #[test]
    fn pure_tuple_field_accepted() {
        assert!(check_pure_codegen(&[s(Prim::TupleField(v(1), 0))]).is_ok());
    }

    #[test]
    fn pure_list_head_tail_is_empty_accepted() {
        let stmts = vec![
            s(Prim::ListHead(v(1))),
            s(Prim::ListTail(v(1))),
            s(Prim::IsEmptyList(v(1))),
        ];
        assert!(check_pure_codegen(&stmts).is_ok());
    }

    #[test]
    fn pure_binop_unop_accepted() {
        let stmts = vec![
            s(Prim::BinOp(BinOp::Eq, v(1), v(2))),
            s(Prim::BinOp(BinOp::Add, v(1), v(2))),
        ];
        assert!(check_pure_codegen(&stmts).is_ok());
    }

    #[test]
    fn pure_type_test_accepted() {
        let mut t = crate::types::ConcreteTypes;
        let stmts = vec![s(Prim::TypeTest(v(1), Box::new(t.int())))];
        assert!(check_pure_codegen(&stmts).is_ok());
    }

    #[test]
    fn pure_map_get_accepted() {
        assert!(check_pure_codegen(&[s(Prim::MapGet(v(1), v(2)))]).is_ok());
    }

    #[test]
    fn make_tuple_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeTuple(vec![v(1), v(2)]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeTuple"),
                ..
            })
        ));
    }

    #[test]
    fn make_list_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeList(vec![v(1)], None))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeList"),
                ..
            })
        ));
    }

    #[test]
    fn make_map_and_update_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeMap(vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeMap"),
                ..
            })
        ));
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MapUpdate(v(1), vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MapUpdate"),
                ..
            })
        ));
    }

    #[test]
    fn make_bitstring_rejected() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::MakeBitstring(vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Allocates("MakeBitstring"),
                ..
            })
        ));
    }

    #[test]
    fn extern_rejected_even_if_harmless() {
        assert!(matches!(
            check_pure_codegen(&[s(Prim::Extern(ExternId(0), vec![]))]),
            Err(ImpureError::Stmt {
                kind: ImpureKind::Extern,
                ..
            })
        ));
    }

    #[test]
    fn first_impure_stmt_index_reported() {
        let stmts = vec![
            s(Prim::Const(Const::Int(1))),
            s(Prim::TupleField(v(1), 0)),
            s(Prim::MakeTuple(vec![v(1)])),
            s(Prim::MakeList(vec![v(1)], None)),
        ];
        match check_pure_codegen(&stmts) {
            Err(ImpureError::Stmt { index, .. }) => assert_eq!(index, 2),
            other => panic!("expected Stmt error at index 2, got {:?}", other),
        }
    }

    #[test]
    fn term_goto_if_return_accepted() {
        assert!(check_pure_term(&Term::Goto(BlockId(0), vec![])).is_ok());
        assert!(check_pure_term(&Term::Return(v(0))).is_ok());
        assert!(
            check_pure_term(&Term::If {
                cond: v(0),
                then_b: BlockId(0),
                else_b: BlockId(1),
                origin: BranchOrigin::PatternBind,
            })
            .is_ok()
        );
    }

    #[test]
    fn term_halt_rejected() {
        assert!(matches!(
            check_pure_term(&Term::Halt(v(0))),
            Err(ImpureError::Term(ImpureTerm::Halt))
        ));
    }

    // fz-puj.30 (G1) — module-level matcher purity check.

    fn build_module_with_matcher(extra_let: Option<Prim>, term: Term) -> crate::fz_ir::Module {
        use crate::fz_ir::{FnBuilder, FnCategory, FnId, Module};
        let mut m = Module::default();
        let fid = FnId(100);
        let mut b = FnBuilder::new(fid, "match_x").with_category(FnCategory::Matcher);
        let p = b.fresh_var();
        let entry = b.block(vec![p]);
        if let Some(prim) = extra_let {
            let _ = b.let_(entry, prim);
        }
        b.set_terminator(entry, term);
        let f = b.build();
        m.fn_idx.insert(f.id, m.fns.len());
        m.fns.push(f);
        m
    }

    #[test]
    fn matcher_purity_accepts_pure_router() {
        let module =
            build_module_with_matcher(Some(Prim::Const(Const::Int(0))), Term::Return(v(0)));
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert!(
            diags.is_empty(),
            "pure matcher should produce no diags: {:?}",
            diags
        );
    }

    #[test]
    fn matcher_purity_rejects_extern_stmt() {
        let module =
            build_module_with_matcher(Some(Prim::Extern(ExternId(0), vec![])), Term::Return(v(0)));
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert_eq!(diags.len(), 1);
        assert_eq!(diags[0].code, crate::diag::codes::TYPE_IMPURE_MATCHER);
        assert!(diags[0].message.contains("extern"));
    }

    #[test]
    fn matcher_purity_rejects_call_terminator() {
        use crate::fz_ir::{CallsiteIdent, Cont, FnId};
        let module = build_module_with_matcher(
            None,
            Term::Call {
                ident: CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                callee: FnId(99),
                args: vec![v(0)],
                continuation: Cont {
                    fn_id: FnId(98),
                    captured: vec![],
                },
            },
        );
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert_eq!(diags.len(), 1);
        assert!(diags[0].message.contains("Call"));
    }

    #[test]
    fn matcher_purity_allows_tailcall() {
        use crate::fz_ir::{CallsiteIdent, FnId};
        let module = build_module_with_matcher(
            None,
            Term::TailCall {
                ident: CallsiteIdent::from_source(crate::diag::Span::DUMMY),
                callee: FnId(99),
                args: vec![v(0)],
                is_back_edge: false,
            },
        );
        let diags = crate::ir_typer::check_matcher_purity(&module);
        assert!(
            diags.is_empty(),
            "matcher with TailCall terminator should be pure: {:?}",
            diags
        );
    }
}
