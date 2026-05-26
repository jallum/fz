//! Destination-passing IR verification.
//!
//! The runtime contract is stricter than ordinary SSA: a destination is an
//! unpublished construction location, and its init token is linear. This
//! verifier keeps that contract explicit before any backend learns how to
//! lower destination primitives.

use crate::fz_ir::{BlockId, FnId, InitTokenId, Module, Prim, Var};
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
