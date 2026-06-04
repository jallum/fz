//! Destination-passing IR verification.
//!
//! The runtime contract is stricter than ordinary SSA: a destination is an
//! unpublished construction location, and its init token is linear. This
//! verifier keeps that contract explicit before any backend learns how to
//! lower destination primitives.

use crate::fz_ir::{BlockId, FnId, FnIr, InitTokenId, Module, Prim, Stmt, Var, visit_prim_vars, visit_term_vars};
use std::collections::HashMap;
use std::fmt;
use std::mem::take;

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
        write!(f, "{} {} stmt#{}: {}", self.fn_id, self.block, self.stmt_idx, self.kind)
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
                write!(f, "destination {} field {} is initialized twice", dest, index)
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
pub(crate) enum TokenState {
    Available,
    Consumed,
}

#[derive(Debug, Clone)]
pub(crate) struct TupleDestState<Field> {
    arity: usize,
    fields: Vec<Option<Field>>,
    frozen: bool,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DestTokenTransitionError {
    DuplicateTokenDefinition(InitTokenId),
    UndefinedTokenUse(InitTokenId),
    TokenReuse(InitTokenId),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum TupleDestTransitionError {
    DuplicateFieldWrite { dest: Var, index: u32 },
    FieldOutOfBounds { dest: Var, index: u32, arity: usize },
    FreezeIncomplete { dest: Var, missing: Vec<u32> },
    FreezeUnknownDest(Var),
    FrozenDestWrite(Var),
}

pub(crate) fn define_init_token(
    tokens: &mut HashMap<InitTokenId, TokenState>,
    token: InitTokenId,
) -> Result<(), DestTokenTransitionError> {
    if tokens.insert(token, TokenState::Available).is_some() {
        Err(DestTokenTransitionError::DuplicateTokenDefinition(token))
    } else {
        Ok(())
    }
}

pub(crate) fn consume_init_token(
    tokens: &mut HashMap<InitTokenId, TokenState>,
    token: InitTokenId,
) -> Result<(), DestTokenTransitionError> {
    match tokens.get_mut(&token) {
        Some(state @ TokenState::Available) => {
            *state = TokenState::Consumed;
            Ok(())
        }
        Some(TokenState::Consumed) => Err(DestTokenTransitionError::TokenReuse(token)),
        None => Err(DestTokenTransitionError::UndefinedTokenUse(token)),
    }
}

pub(crate) fn begin_tuple_dest<Field>(dests: &mut HashMap<Var, TupleDestState<Field>>, dest: Var, arity: usize) {
    dests.insert(
        dest,
        TupleDestState {
            arity,
            fields: (0..arity).map(|_| None).collect(),
            frozen: false,
        },
    );
}

pub(crate) fn set_tuple_dest_field<Field>(
    dests: &mut HashMap<Var, TupleDestState<Field>>,
    dest: Var,
    index: u32,
    field: Field,
) -> Result<(), TupleDestTransitionError> {
    match dests.get_mut(&dest) {
        Some(state) if state.frozen => Err(TupleDestTransitionError::FrozenDestWrite(dest)),
        Some(state) => {
            let Some(slot) = state.fields.get_mut(index as usize) else {
                return Err(TupleDestTransitionError::FieldOutOfBounds {
                    dest,
                    index,
                    arity: state.arity,
                });
            };
            if slot.is_some() {
                Err(TupleDestTransitionError::DuplicateFieldWrite { dest, index })
            } else {
                *slot = Some(field);
                Ok(())
            }
        }
        None => Err(TupleDestTransitionError::FreezeUnknownDest(dest)),
    }
}

pub(crate) fn freeze_tuple_dest<Field: Clone>(
    dests: &mut HashMap<Var, TupleDestState<Field>>,
    dest: Var,
) -> Result<Vec<Field>, TupleDestTransitionError> {
    let Some(state) = dests.get_mut(&dest) else {
        return Err(TupleDestTransitionError::FreezeUnknownDest(dest));
    };
    let missing: Vec<u32> = state
        .fields
        .iter()
        .enumerate()
        .filter_map(|(i, field)| field.is_none().then_some(i as u32))
        .collect();
    if !missing.is_empty() {
        return Err(TupleDestTransitionError::FreezeIncomplete { dest, missing });
    }
    state.frozen = true;
    Ok(state
        .fields
        .iter()
        .map(|field| field.clone().expect("missing fields checked above"))
        .collect())
}

pub(crate) fn tuple_dest_is_frozen<Field>(state: &TupleDestState<Field>) -> bool {
    state.frozen
}

pub fn verify_module(module: &Module) -> Result<(), Vec<DestVerifyError>> {
    let mut errors = Vec::new();
    for f in &module.fns {
        let mut tokens: HashMap<InitTokenId, TokenState> = HashMap::new();
        let mut dests: HashMap<Var, TupleDestState<()>> = HashMap::new();

        for block in &f.blocks {
            for (stmt_idx, stmt) in block.stmts.iter().enumerate() {
                let Stmt::Let(dest_var, prim) = stmt;
                let loc = |kind| DestVerifyError {
                    fn_id: f.id,
                    block: block.id,
                    stmt_idx,
                    kind,
                };
                match prim {
                    Prim::DestTupleBegin { token, arity } => {
                        if let Err(err) = define_init_token(&mut tokens, *token) {
                            errors.push(loc(token_error_kind(err)));
                        }
                        begin_tuple_dest(&mut dests, *dest_var, *arity);
                    }
                    Prim::DestTupleSet {
                        dest,
                        token,
                        index,
                        next,
                        ..
                    } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                        if let Err(err) = define_init_token(&mut tokens, *next) {
                            errors.push(loc(token_error_kind(err)));
                        }
                        if let Err(err) = set_tuple_dest_field(&mut dests, *dest, *index, ()) {
                            errors.push(loc(tuple_error_kind(err)));
                        }
                    }
                    Prim::DestFreeze { dest, token } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                        if let Err(err) = freeze_tuple_dest(&mut dests, *dest) {
                            errors.push(loc(tuple_error_kind(err)));
                        }
                    }
                    Prim::DestListBegin { token } => define_token(&mut tokens, *token, &mut errors, loc),
                    Prim::DestListCons { token, next, .. } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                        if tokens.insert(*next, TokenState::Available).is_some() {
                            errors.push(loc(DestVerifyErrorKind::DuplicateTokenDefinition(*next)));
                        }
                    }
                    Prim::DestListFreeze { token, .. } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                    }
                    Prim::DestMapBegin { token, .. } => define_token(&mut tokens, *token, &mut errors, loc),
                    Prim::DestMapPut { token, next, .. } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                        define_token(&mut tokens, *next, &mut errors, loc);
                    }
                    Prim::DestMapFreeze { token, .. } => {
                        consume_token(&mut tokens, *token, &mut errors, loc);
                    }
                    _ => {}
                }
            }
        }

        let last_block = f.blocks.last().map(|b| b.id).unwrap_or(BlockId(0));
        for (dest, state) in dests {
            if !tuple_dest_is_frozen(&state) {
                errors.push(DestVerifyError {
                    fn_id: f.id,
                    block: last_block,
                    stmt_idx: usize::MAX,
                    kind: DestVerifyErrorKind::UnfrozenDest { dest },
                });
            }
        }
    }

    if errors.is_empty() { Ok(()) } else { Err(errors) }
}

fn token_error_kind(err: DestTokenTransitionError) -> DestVerifyErrorKind {
    match err {
        DestTokenTransitionError::DuplicateTokenDefinition(token) => {
            DestVerifyErrorKind::DuplicateTokenDefinition(token)
        }
        DestTokenTransitionError::UndefinedTokenUse(token) => DestVerifyErrorKind::UndefinedTokenUse(token),
        DestTokenTransitionError::TokenReuse(token) => DestVerifyErrorKind::TokenReuse(token),
    }
}

fn tuple_error_kind(err: TupleDestTransitionError) -> DestVerifyErrorKind {
    match err {
        TupleDestTransitionError::DuplicateFieldWrite { dest, index } => {
            DestVerifyErrorKind::DuplicateFieldWrite { dest, index }
        }
        TupleDestTransitionError::FieldOutOfBounds { dest, index, arity } => {
            DestVerifyErrorKind::FieldOutOfBounds { dest, index, arity }
        }
        TupleDestTransitionError::FreezeIncomplete { dest, missing } => {
            DestVerifyErrorKind::FreezeIncomplete { dest, missing }
        }
        TupleDestTransitionError::FreezeUnknownDest(dest) => DestVerifyErrorKind::FreezeUnknownDest(dest),
        TupleDestTransitionError::FrozenDestWrite(dest) => DestVerifyErrorKind::FrozenDestWrite(dest),
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

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ListDestLowering {
    pub fn_id: FnId,
    pub result: Var,
    pub conses: Vec<Var>,
}

pub fn lower_list_destinations(module: &mut Module) -> Vec<ListDestLowering> {
    let mut lowered = Vec::new();
    for f in &mut module.fns {
        lower_list_destinations_in_fn(f, &mut lowered);
    }
    lowered
}

pub fn lower_destinations(module: &mut Module) {
    lower_tuple_destinations(module);
    lower_list_destinations(module);
    lower_map_destinations(module);
}

pub fn lower_map_destinations(module: &mut Module) {
    for f in &mut module.fns {
        lower_map_destinations_in_fn(f);
    }
}

fn lower_map_destinations_in_fn(f: &mut FnIr) {
    let mut next_var = next_var_id(f);
    let mut next_token = next_token_id(f);
    for block in &mut f.blocks {
        let old_stmts = take(&mut block.stmts);
        let mut new_stmts = Vec::with_capacity(old_stmts.len());
        for stmt in old_stmts {
            match stmt {
                Stmt::Let(result, Prim::MakeMap(entries)) => {
                    lower_map_destination(&mut new_stmts, result, None, entries, &mut next_var, &mut next_token);
                }
                Stmt::Let(result, Prim::MapUpdate(base, entries)) => {
                    lower_map_destination(
                        &mut new_stmts,
                        result,
                        Some(base),
                        entries,
                        &mut next_var,
                        &mut next_token,
                    );
                }
                other => new_stmts.push(other),
            }
        }
        block.stmts = new_stmts;
    }
}

fn lower_map_destination(
    new_stmts: &mut Vec<Stmt>,
    result: Var,
    base: Option<Var>,
    entries: Vec<(Var, Var)>,
    next_var: &mut u32,
    next_token: &mut u32,
) {
    let map = fresh_var(next_var);
    let mut token = fresh_token(next_token);
    new_stmts.push(Stmt::Let(
        map,
        Prim::DestMapBegin {
            token,
            base,
            extra: entries.len(),
        },
    ));
    for (key, value) in entries {
        let next = fresh_token(next_token);
        let unit = fresh_var(next_var);
        new_stmts.push(Stmt::Let(
            unit,
            Prim::DestMapPut {
                map,
                token,
                key,
                value,
                next,
            },
        ));
        token = next;
    }
    new_stmts.push(Stmt::Let(result, Prim::DestMapFreeze { map, token }));
}

fn lower_list_destinations_in_fn(f: &mut FnIr, lowered: &mut Vec<ListDestLowering>) {
    let mut next_var = next_var_id(f);
    let mut next_token = next_token_id(f);
    for block in &mut f.blocks {
        let old_stmts = take(&mut block.stmts);
        let mut new_stmts = Vec::with_capacity(old_stmts.len());
        for stmt in old_stmts {
            match stmt {
                Stmt::Let(result, Prim::MakeList(elems, tail)) if !elems.is_empty() => {
                    let mut token = fresh_token(&mut next_token);
                    let begin_unit = fresh_var(&mut next_var);
                    new_stmts.push(Stmt::Let(begin_unit, Prim::DestListBegin { token }));
                    let mut acc = tail;
                    let mut conses = Vec::with_capacity(elems.len());
                    for head in elems.into_iter().rev() {
                        let next = fresh_token(&mut next_token);
                        let cons = fresh_var(&mut next_var);
                        new_stmts.push(Stmt::Let(
                            cons,
                            Prim::DestListCons {
                                token,
                                head,
                                tail: acc,
                                next,
                            },
                        ));
                        conses.push(cons);
                        acc = Some(cons);
                        token = next;
                    }
                    let list = acc.expect("non-empty list lowering produced a cons");
                    lowered.push(ListDestLowering {
                        fn_id: f.id,
                        result,
                        conses,
                    });
                    new_stmts.push(Stmt::Let(result, Prim::DestListFreeze { list, token }));
                }
                other => new_stmts.push(other),
            }
        }
        block.stmts = new_stmts;
    }
}

fn lower_tuple_destinations_in_fn(f: &mut FnIr, lowered: &mut Vec<TupleDestLowering>) {
    let mut next_var = next_var_id(f);
    let mut next_token = next_token_id(f);
    for block in &mut f.blocks {
        let old_stmts = take(&mut block.stmts);
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
                Prim::DestListBegin { token } => next = next.max(token.0 + 1),
                Prim::DestListCons { token, next: n, .. } => {
                    next = next.max(token.0 + 1).max(n.0 + 1);
                }
                Prim::DestListFreeze { token, .. } => next = next.max(token.0 + 1),
                Prim::DestMapBegin { token, .. } => next = next.max(token.0 + 1),
                Prim::DestMapPut { token, next: n, .. } => {
                    next = next.max(token.0 + 1).max(n.0 + 1);
                }
                Prim::DestMapFreeze { token, .. } => next = next.max(token.0 + 1),
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

fn define_token(
    tokens: &mut HashMap<InitTokenId, TokenState>,
    token: InitTokenId,
    errors: &mut Vec<DestVerifyError>,
    loc: impl Fn(DestVerifyErrorKind) -> DestVerifyError,
) {
    if tokens.insert(token, TokenState::Available).is_some() {
        errors.push(loc(DestVerifyErrorKind::DuplicateTokenDefinition(token)));
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
mod ir_dest_test;
