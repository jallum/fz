//! Destination-passing IR verification.
//!
//! The runtime contract is stricter than ordinary SSA: a destination is an
//! unpublished construction location, and its init token is linear. This
//! verifier keeps that contract explicit before any backend learns how to
//! lower destination primitives.

use crate::fz_ir::{BlockId, FnId, FnIr, InitTokenId, Module, Prim, Stmt, Var};
use std::collections::{HashMap, HashSet};
use std::fmt;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DestVerifyError {
    pub fn_id: FnId,
    pub block: BlockId,
    pub stmt_idx: usize,
    pub kind: DestVerifyErrorKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DestVerifyErrorKind {
    DuplicateTokenDefinition(InitTokenId),
    UndefinedTokenUse(InitTokenId),
    TokenReuse(InitTokenId),
    DuplicateFieldWrite { dest: Var, index: u32 },
    FieldOutOfBounds { dest: Var, index: u32, arity: usize },
    FreezeIncomplete { dest: Var, missing: Vec<u32> },
    FreezeUnknownDest(Var),
    FrozenDestWrite(Var),
    UnfrozenDest { dest: Var },
}

impl fmt::Display for DestVerifyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "{} {} stmt#{}: {}",
            self.fn_id, self.block, self.stmt_idx, self.kind
        )
    }
}

impl fmt::Display for DestVerifyErrorKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            DestVerifyErrorKind::DuplicateTokenDefinition(token) => {
                write!(f, "destination token {} is defined more than once", token)
            }
            DestVerifyErrorKind::UndefinedTokenUse(token) => {
                write!(f, "destination token {} is used before definition", token)
            }
            DestVerifyErrorKind::TokenReuse(token) => {
                write!(f, "destination token {} is used more than once", token)
            }
            DestVerifyErrorKind::DuplicateFieldWrite { dest, index } => {
                write!(
                    f,
                    "destination {} field {} is initialized twice",
                    dest, index
                )
            }
            DestVerifyErrorKind::FieldOutOfBounds { dest, index, arity } => write!(
                f,
                "destination {} field {} is outside tuple arity {}",
                dest, index, arity
            ),
            DestVerifyErrorKind::FreezeIncomplete { dest, missing } => {
                write!(
                    f,
                    "destination {} freezes before fields {:?} are initialized",
                    dest, missing
                )
            }
            DestVerifyErrorKind::FreezeUnknownDest(dest) => {
                write!(f, "destination {} freezes without a begin primitive", dest)
            }
            DestVerifyErrorKind::FrozenDestWrite(dest) => {
                write!(f, "destination {} is written after freeze", dest)
            }
            DestVerifyErrorKind::UnfrozenDest { dest } => {
                write!(f, "destination {} is never frozen", dest)
            }
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TokenState {
    Available,
    Consumed,
}

#[derive(Debug, Clone)]
struct TupleDestState {
    arity: usize,
    fields: HashSet<u32>,
    frozen: bool,
}

pub fn verify_module(module: &Module) -> Result<(), Vec<DestVerifyError>> {
    let mut errors = Vec::new();
    for f in &module.fns {
        let mut tokens: HashMap<InitTokenId, TokenState> = HashMap::new();
        let mut dests: HashMap<Var, TupleDestState> = HashMap::new();

        for block in &f.blocks {
            for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
                let crate::fz_ir::Stmt::Let(dest_var, prim) = stmt;
                let loc = |kind| DestVerifyError {
                    fn_id: f.id,
                    block: block.id,
                    stmt_idx,
                    kind,
                };
                match prim {
                    Prim::DestTupleBegin { token, arity } => {
                        if tokens.insert(*token, TokenState::Available).is_some() {
                            errors.push(loc(DestVerifyErrorKind::DuplicateTokenDefinition(*token)));
                        }
                        dests.insert(
                            *dest_var,
                            TupleDestState {
                                arity: *arity,
                                fields: HashSet::new(),
                                frozen: false,
                            },
                        );
                    }
                    Prim::DestTupleSet {
                        dest,
                        token,
                        index,
                        next,
                        ..
                    } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                        if tokens.insert(*next, TokenState::Available).is_some() {
                            errors.push(loc(DestVerifyErrorKind::DuplicateTokenDefinition(*next)));
                        }
                        match dests.get_mut(dest) {
                            Some(state) if state.frozen => {
                                errors.push(loc(DestVerifyErrorKind::FrozenDestWrite(*dest)));
                            }
                            Some(state) => {
                                if (*index as usize) >= state.arity {
                                    errors.push(loc(DestVerifyErrorKind::FieldOutOfBounds {
                                        dest: *dest,
                                        index: *index,
                                        arity: state.arity,
                                    }));
                                } else if !state.fields.insert(*index) {
                                    errors.push(loc(DestVerifyErrorKind::DuplicateFieldWrite {
                                        dest: *dest,
                                        index: *index,
                                    }));
                                }
                            }
                            None => errors.push(loc(DestVerifyErrorKind::FreezeUnknownDest(*dest))),
                        }
                    }
                    Prim::DestFreeze { dest, token } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                        match dests.get_mut(dest) {
                            Some(state) => {
                                let missing: Vec<u32> = (0..state.arity as u32)
                                    .filter(|i| !state.fields.contains(i))
                                    .collect();
                                if missing.is_empty() {
                                    state.frozen = true;
                                } else {
                                    errors.push(loc(DestVerifyErrorKind::FreezeIncomplete {
                                        dest: *dest,
                                        missing,
                                    }));
                                }
                            }
                            None => errors.push(loc(DestVerifyErrorKind::FreezeUnknownDest(*dest))),
                        }
                    }
                    _ => {}
                }
            }
        }

        let last_block = f.blocks.last().map(|b| b.id).unwrap_or(BlockId(0));
        for (dest, state) in dests {
            if !state.frozen {
                errors.push(DestVerifyError {
                    fn_id: f.id,
                    block: last_block,
                    stmt_idx: usize::MAX,
                    kind: DestVerifyErrorKind::UnfrozenDest { dest },
                });
            }
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(errors)
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TupleDestLowering {
    pub fn_id: FnId,
    pub result: Var,
    pub dest: Var,
    pub units: Vec<Var>,
}

pub fn lower_tuple_destinations(module: &mut Module) -> Vec<TupleDestLowering> {
    let mut lowered = Vec::new();
    for f in &mut module.fns {
        lower_tuple_destinations_in_fn(f, &mut lowered);
    }
    lowered
}

fn lower_tuple_destinations_in_fn(f: &mut FnIr, lowered: &mut Vec<TupleDestLowering>) {
    let mut next_var = next_var_id(f);
    let mut next_token = next_token_id(f);
    for block in &mut f.blocks {
        let old_stmts = std::mem::take(&mut block.stmts);
        let mut new_stmts = Vec::with_capacity(old_stmts.len());
        for stmt in old_stmts {
            match stmt {
                Stmt::Let(result, Prim::MakeTuple(elems)) => {
                    let dest = fresh_var(&mut next_var);
                    let first_token = fresh_token(&mut next_token);
                    let mut units = Vec::with_capacity(elems.len());
                    new_stmts.push(Stmt::Let(
                        dest,
                        Prim::DestTupleBegin {
                            token: first_token,
                            arity: elems.len(),
                        },
                    ));
                    let mut token = first_token;
                    for (index, value) in elems.into_iter().enumerate() {
                        let next = fresh_token(&mut next_token);
                        let unit = fresh_var(&mut next_var);
                        units.push(unit);
                        new_stmts.push(Stmt::Let(
                            unit,
                            Prim::DestTupleSet {
                                dest,
                                token,
                                index: index as u32,
                                value,
                                next,
                            },
                        ));
                        token = next;
                    }
                    lowered.push(TupleDestLowering {
                        fn_id: f.id,
                        result,
                        dest,
                        units,
                    });
                    new_stmts.push(Stmt::Let(result, Prim::DestFreeze { dest, token }));
                }
                other => new_stmts.push(other),
            }
        }
        block.stmts = new_stmts;
    }
}

fn next_var_id(f: &FnIr) -> u32 {
    let mut next = 0;
    for block in &f.blocks {
        next = next.max(block.params.iter().map(|v| v.0 + 1).max().unwrap_or(0));
        for stmt in &block.stmts {
            let Stmt::Let(dest, prim) = stmt;
            next = next.max(dest.0 + 1);
            visit_prim_vars(prim, |v| next = next.max(v.0 + 1));
        }
        visit_term_vars(&block.terminator, |v| next = next.max(v.0 + 1));
    }
    next
}

fn next_token_id(f: &FnIr) -> u32 {
    let mut next = 0;
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(_, prim) = stmt;
            match prim {
                Prim::DestTupleBegin { token, .. } => next = next.max(token.0 + 1),
                Prim::DestTupleSet { token, next: n, .. } => {
                    next = next.max(token.0 + 1).max(n.0 + 1);
                }
                Prim::DestFreeze { token, .. } => next = next.max(token.0 + 1),
                _ => {}
            }
        }
    }
    next
}

fn fresh_var(next: &mut u32) -> Var {
    let v = Var(*next);
    *next += 1;
    v
}

fn fresh_token(next: &mut u32) -> InitTokenId {
    let token = InitTokenId(*next);
    *next += 1;
    token
}

fn consume_token(
    tokens: &mut HashMap<InitTokenId, TokenState>,
    token: InitTokenId,
    errors: &mut Vec<DestVerifyError>,
    loc: impl Fn(DestVerifyErrorKind) -> DestVerifyError,
) {
    match tokens.get_mut(&token) {
        Some(state @ TokenState::Available) => {
            *state = TokenState::Consumed;
        }
        Some(TokenState::Consumed) => {
            errors.push(loc(DestVerifyErrorKind::TokenReuse(token)));
        }
        None => {
            errors.push(loc(DestVerifyErrorKind::UndefinedTokenUse(token)));
        }
    }
}

fn visit_prim_vars(prim: &Prim, mut visit: impl FnMut(Var)) {
    match prim {
        Prim::Const(_) | Prim::DestTupleBegin { .. } | Prim::ConstBitstring(_, _) => {}
        Prim::BinOp(_, a, b) | Prim::MapGet(a, b) | Prim::MatcherMapGet(a, b) => {
            visit(*a);
            visit(*b);
        }
        Prim::UnOp(_, v)
        | Prim::ListHead(v)
        | Prim::ListTail(v)
        | Prim::IsEmptyList(v)
        | Prim::TupleField(v, _)
        | Prim::IsMatcherMapMiss(v)
        | Prim::BitReaderInit(v)
        | Prim::BitReaderDone(v)
        | Prim::Brand(v, _) => visit(*v),
        Prim::Extern(_, args) | Prim::MakeTuple(args) => {
            for v in args {
                visit(*v);
            }
        }
        Prim::DestTupleSet { dest, value, .. } => {
            visit(*dest);
            visit(*value);
        }
        Prim::DestFreeze { dest, .. } => visit(*dest),
        Prim::MakeList(elems, tail) => {
            for v in elems {
                visit(*v);
            }
            if let Some(tail) = tail {
                visit(*tail);
            }
        }
        Prim::MakeClosure(_, _, caps) => {
            for v in caps {
                visit(*v);
            }
        }
        Prim::MakeMap(entries) => {
            for (k, v) in entries {
                visit(*k);
                visit(*v);
            }
        }
        Prim::MapUpdate(base, entries) => {
            visit(*base);
            for (k, v) in entries {
                visit(*k);
                visit(*v);
            }
        }
        Prim::MakeBitstring(fields) => {
            for field in fields {
                visit(field.value);
                if let Some(crate::fz_ir::BitSizeIr::Var(v)) = field.size {
                    visit(v);
                }
            }
        }
        Prim::BitReadField { reader, size, .. } => {
            visit(*reader);
            if let Some(crate::fz_ir::BitSizeIr::Var(v)) = size {
                visit(*v);
            }
        }
        Prim::TypeTest(v, _) => visit(*v),
    }
}

fn visit_term_vars(term: &crate::fz_ir::Term, mut visit: impl FnMut(Var)) {
    use crate::fz_ir::Term;
    match term {
        Term::Goto(_, args) | Term::TailCall { args, .. } | Term::TailCallClosure { args, .. } => {
            for v in args {
                visit(*v);
            }
        }
        Term::If { cond, .. } | Term::Return(cond) | Term::Halt(cond) => visit(*cond),
        Term::Call {
            args, continuation, ..
        }
        | Term::CallClosure {
            args, continuation, ..
        } => {
            for v in args {
                visit(*v);
            }
            for v in &continuation.captured {
                visit(*v);
            }
        }
        Term::Receive { continuation, .. } => {
            for v in &continuation.captured {
                visit(*v);
            }
        }
        Term::ReceiveMatched {
            after,
            pinned,
            captures,
            ..
        } => {
            for (_, v) in pinned {
                visit(*v);
            }
            for v in captures {
                visit(*v);
            }
            if let Some(after) = after {
                visit(after.timeout);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{Const, FnBuilder, FnId, ModuleBuilder, Prim, Term};

    fn module_with(stmts: impl IntoIterator<Item = Prim>) -> Module {
        let mut b = FnBuilder::new(FnId(0), "dp_test");
        let entry = b.block(vec![]);
        let mut last = None;
        for prim in stmts {
            last = Some(b.let_(entry, prim));
        }
        b.set_terminator(entry, Term::Halt(last.unwrap_or(Var(0))));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        mb.build()
    }

    fn const_i(value: i64) -> Prim {
        Prim::Const(Const::Int(value))
    }

    #[test]
    fn lowers_make_tuple_to_destination_skeleton() {
        let mut b = FnBuilder::new(FnId(0), "tuple_dp");
        let entry = b.block(vec![]);
        let a = b.let_(entry, const_i(1));
        let b_value = b.let_(entry, const_i(2));
        let tuple = b.let_(entry, Prim::MakeTuple(vec![a, b_value]));
        b.set_terminator(entry, Term::Halt(tuple));
        let mut mb = ModuleBuilder::new();
        mb.add_fn(b.build());
        let mut m = mb.build();

        lower_tuple_destinations(&mut m);
        verify_module(&m).expect("lowered tuple DP must verify");
        let body = m.to_string();
        assert!(body.contains("dest_tuple_begin(arity=2, token=tok0)"));
        assert!(body.contains("dest_tuple_set(v3, tok0, field=0, value=v0, next=tok1)"));
        assert!(body.contains("dest_tuple_set(v3, tok1, field=1, value=v1, next=tok2)"));
        assert!(body.contains("let v2 = dest_freeze(v3, tok2)"));
    }

    #[test]
    fn accepts_legal_tuple_skeleton() {
        let m = module_with([
            Prim::DestTupleBegin {
                token: InitTokenId(0),
                arity: 2,
            },
            const_i(10),
            Prim::DestTupleSet {
                dest: Var(0),
                token: InitTokenId(0),
                index: 0,
                value: Var(1),
                next: InitTokenId(1),
            },
            const_i(20),
            Prim::DestTupleSet {
                dest: Var(0),
                token: InitTokenId(1),
                index: 1,
                value: Var(3),
                next: InitTokenId(2),
            },
            Prim::DestFreeze {
                dest: Var(0),
                token: InitTokenId(2),
            },
        ]);
        assert_eq!(verify_module(&m), Ok(()));
    }

    #[test]
    fn rejects_duplicate_field_write() {
        let m = module_with([
            Prim::DestTupleBegin {
                token: InitTokenId(0),
                arity: 1,
            },
            const_i(10),
            Prim::DestTupleSet {
                dest: Var(0),
                token: InitTokenId(0),
                index: 0,
                value: Var(1),
                next: InitTokenId(1),
            },
            Prim::DestTupleSet {
                dest: Var(0),
                token: InitTokenId(1),
                index: 0,
                value: Var(1),
                next: InitTokenId(2),
            },
            Prim::DestFreeze {
                dest: Var(0),
                token: InitTokenId(2),
            },
        ]);
        let errs = verify_module(&m).expect_err("duplicate field write should fail");
        assert!(errs.iter().any(|e| matches!(
            e.kind,
            DestVerifyErrorKind::DuplicateFieldWrite {
                dest: Var(0),
                index: 0
            }
        )));
    }

    #[test]
    fn rejects_missing_field_before_freeze() {
        let m = module_with([
            Prim::DestTupleBegin {
                token: InitTokenId(0),
                arity: 2,
            },
            const_i(10),
            Prim::DestTupleSet {
                dest: Var(0),
                token: InitTokenId(0),
                index: 0,
                value: Var(1),
                next: InitTokenId(1),
            },
            Prim::DestFreeze {
                dest: Var(0),
                token: InitTokenId(1),
            },
        ]);
        let errs = verify_module(&m).expect_err("incomplete freeze should fail");
        assert!(errs.iter().any(|e| matches!(
            &e.kind,
            DestVerifyErrorKind::FreezeIncomplete { dest: Var(0), missing } if missing == &vec![1]
        )));
    }

    #[test]
    fn rejects_token_reuse() {
        let m = module_with([
            Prim::DestTupleBegin {
                token: InitTokenId(0),
                arity: 1,
            },
            const_i(10),
            Prim::DestTupleSet {
                dest: Var(0),
                token: InitTokenId(0),
                index: 0,
                value: Var(1),
                next: InitTokenId(1),
            },
            Prim::DestFreeze {
                dest: Var(0),
                token: InitTokenId(0),
            },
        ]);
        let errs = verify_module(&m).expect_err("token reuse should fail");
        assert!(
            errs.iter()
                .any(|e| matches!(e.kind, DestVerifyErrorKind::TokenReuse(InitTokenId(0))))
        );
    }
}
