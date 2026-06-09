//! IR Var substitution helpers.
//!
//! Planner/codegen-adjacent transforms use these helpers when they rewrite
//! local bodies and need every Var use in a `Prim`, `Stmt`, or `Term` updated
//! coherently. This module does not own a standalone optimization pass.

use crate::fz_ir::{BitFieldIr, BitSizeIr, Cont, ExternArg, Prim, ReceiveAfter, Stmt, Term, Var};
use std::collections::HashMap;

fn subst_var(v: Var, subst: &HashMap<Var, Var>) -> Var {
    *subst.get(&v).unwrap_or(&v)
}

pub(crate) fn subst_prim(p: &Prim, subst: &HashMap<Var, Var>) -> Prim {
    let sv = |v: Var| subst_var(v, subst);
    match p {
        Prim::Const(c) => Prim::Const(c.clone()),
        Prim::MakeFnRef(ident, fid) => Prim::MakeFnRef(ident.clone(), *fid),
        Prim::BinOp(op, a, b) => Prim::BinOp(*op, sv(*a), sv(*b)),
        Prim::UnOp(op, a) => Prim::UnOp(*op, sv(*a)),
        Prim::Extern(ident, eid, args) => Prim::Extern(
            ident.clone(),
            *eid,
            args.iter().map(|x| ExternArg { var: sv(x.var), ..*x }).collect(),
        ),
        Prim::ListHead(a) => Prim::ListHead(sv(*a)),
        Prim::ListTail(a) => Prim::ListTail(sv(*a)),
        Prim::IsEmptyList(a) => Prim::IsEmptyList(sv(*a)),
        Prim::IsListCons(a) => Prim::IsListCons(sv(*a)),
        Prim::MakeTuple(args) => Prim::MakeTuple(args.iter().map(|x| sv(*x)).collect()),
        Prim::MakeStruct { module, fields } => Prim::MakeStruct {
            module: module.clone(),
            fields: fields.iter().map(|(name, v)| (name.clone(), sv(*v))).collect(),
        },
        Prim::DestTupleBegin { token, arity } => Prim::DestTupleBegin {
            token: *token,
            arity: *arity,
        },
        Prim::DestTupleSet {
            dest,
            token,
            index,
            value,
            next,
        } => Prim::DestTupleSet {
            dest: sv(*dest),
            token: *token,
            index: *index,
            value: sv(*value),
            next: *next,
        },
        Prim::DestFreeze { dest, token } => Prim::DestFreeze {
            dest: sv(*dest),
            token: *token,
        },
        Prim::DestListBegin { token } => Prim::DestListBegin { token: *token },
        Prim::DestListCons {
            token,
            head,
            tail,
            next,
        } => Prim::DestListCons {
            token: *token,
            head: sv(*head),
            tail: tail.map(sv),
            next: *next,
        },
        Prim::DestListFreeze { list, token } => Prim::DestListFreeze {
            list: sv(*list),
            token: *token,
        },
        Prim::TupleField(a, i) => Prim::TupleField(sv(*a), *i),
        Prim::StructField(a, name) => Prim::StructField(sv(*a), name.clone()),
        Prim::MakeList(els, tail) => Prim::MakeList(els.iter().map(|x| sv(*x)).collect(), tail.map(sv)),
        // fz-kgk — subst_prim rewrites Var operands only; callable identities
        // stay.
        Prim::MakeClosure(ident, fid, caps) => {
            Prim::MakeClosure(ident.clone(), *fid, caps.iter().map(|x| sv(*x)).collect())
        }
        Prim::MakeMap(entries) => Prim::MakeMap(entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect()),
        Prim::MapUpdate(base, entries) => {
            Prim::MapUpdate(sv(*base), entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect())
        }
        Prim::DestMapBegin { token, base, extra } => Prim::DestMapBegin {
            token: *token,
            base: base.map(sv),
            extra: *extra,
        },
        Prim::DestMapPut {
            map,
            token,
            key,
            value,
            next,
        } => Prim::DestMapPut {
            map: sv(*map),
            token: *token,
            key: sv(*key),
            value: sv(*value),
            next: *next,
        },
        Prim::DestMapFreeze { map, token } => Prim::DestMapFreeze {
            map: sv(*map),
            token: *token,
        },
        Prim::MapGet(a, b) => Prim::MapGet(sv(*a), sv(*b)),
        Prim::MatcherMapGet(a, b) => Prim::MatcherMapGet(sv(*a), sv(*b)),
        Prim::IsMatcherMapMiss(value) => Prim::IsMatcherMapMiss(sv(*value)),
        Prim::ConstBitstring(bytes, bit_len) => Prim::ConstBitstring(bytes.clone(), *bit_len),
        Prim::MakeBitstring(fields) => Prim::MakeBitstring(
            fields
                .iter()
                .map(|f| BitFieldIr {
                    value: sv(f.value),
                    ty: f.ty,
                    size: f.size.as_ref().map(|s| match s {
                        BitSizeIr::Literal(n) => BitSizeIr::Literal(*n),
                        BitSizeIr::Var(v) => BitSizeIr::Var(sv(*v)),
                    }),
                    endian: f.endian,
                    signed: f.signed,
                    unit: f.unit,
                })
                .collect(),
        ),
        Prim::BitReaderInit(a) => Prim::BitReaderInit(sv(*a)),
        Prim::BitReaderDone(a) => Prim::BitReaderDone(sv(*a)),
        Prim::BitReadField {
            reader,
            ty,
            size,
            endian,
            signed,
            unit,
            is_last,
        } => Prim::BitReadField {
            reader: sv(*reader),
            ty: *ty,
            size: size.as_ref().map(|s| match s {
                BitSizeIr::Literal(n) => BitSizeIr::Literal(*n),
                BitSizeIr::Var(v) => BitSizeIr::Var(sv(*v)),
            }),
            endian: *endian,
            signed: *signed,
            unit: *unit,
            is_last: *is_last,
        },
        Prim::TypeTest(a, d) => Prim::TypeTest(sv(*a), d.clone()),
        Prim::RuntimeTypeTestShim(a, d) => Prim::RuntimeTypeTestShim(sv(*a), d.clone()),
        Prim::Brand(a, name) => Prim::Brand(sv(*a), name.clone()),
    }
}

fn subst_cont(c: &Cont, subst: &HashMap<Var, Var>) -> Cont {
    Cont {
        fn_id: c.fn_id,
        captured: c.captured.iter().map(|x| subst_var(*x, subst)).collect(),
    }
}

pub(crate) fn subst_term(t: &Term, subst: &HashMap<Var, Var>) -> Term {
    let sv = |v: Var| subst_var(v, subst);
    match t {
        // BlockId targets are NOT substituted — only Var args are.
        Term::Goto(b, args) => Term::Goto(*b, args.iter().map(|x| sv(*x)).collect()),
        Term::If {
            cond,
            then_b,
            else_b,
            origin,
        } => Term::If {
            cond: sv(*cond),
            then_b: *then_b,
            else_b: *else_b,
            origin: *origin,
        },
        // fz-kgk — subst_term rewrites internals (Var substitution); the
        // wrapping callsite identity stays.
        Term::Call {
            ident,
            callee,
            args,
            continuation,
        } => Term::Call {
            ident: ident.clone(),
            callee: *callee,
            args: args.iter().map(|x| sv(*x)).collect(),
            continuation: subst_cont(continuation, subst),
        },
        Term::TailCall {
            ident,
            callee,
            args,
            is_back_edge,
        } => Term::TailCall {
            ident: ident.clone(),
            callee: *callee,
            args: args.iter().map(|x| sv(*x)).collect(),
            is_back_edge: *is_back_edge,
        },
        Term::CallClosure {
            ident,
            closure,
            args,
            continuation,
        } => Term::CallClosure {
            ident: ident.clone(),
            closure: sv(*closure),
            args: args.iter().map(|x| sv(*x)).collect(),
            continuation: subst_cont(continuation, subst),
        },
        Term::TailCallClosure { closure, args, ident } => Term::TailCallClosure {
            ident: ident.clone(),
            closure: sv(*closure),
            args: args.iter().map(|x| sv(*x)).collect(),
        },
        Term::Return(a) => Term::Return(sv(*a)),
        Term::Halt(a) => Term::Halt(sv(*a)),
        // fz-yxs — pinned/captures Vars are substituted; the timeout Var
        // (if present on an after clause) is substituted too. Clause and
        // after body/guard FnIds are not Vars and pass through unchanged.
        Term::ReceiveMatched {
            ident,
            clauses,
            dispatch,
            after,
            pinned,
            captures,
        } => Term::ReceiveMatched {
            ident: ident.clone(),
            clauses: clauses.clone(),
            dispatch: dispatch.clone(),
            after: after.as_ref().map(|a| ReceiveAfter {
                ident: a.ident.clone(),
                timeout: sv(a.timeout),
                body: a.body,
                span: a.span,
            }),
            pinned: pinned.iter().map(|(n, v)| (n.clone(), sv(*v))).collect(),
            captures: captures.iter().map(|x| sv(*x)).collect(),
        },
    }
}

pub(crate) fn subst_stmt(s: &Stmt, subst: &HashMap<Var, Var>) -> Stmt {
    let Stmt::Let(v, p) = s;
    // The bound variable `v` is never substituted — it's a definition site,
    // not a use. Only Vars that appear as operands in `p` are substituted.
    Stmt::Let(*v, subst_prim(p, subst))
}
