use crate::fz_ir::{
    BitSizeIr, Block, BlockId, Cont, FnCategory, FnId, FnIr, Module, Prim, Stmt, Term, Var,
};
use crate::ir_fuse::{subst_stmt, subst_term};
use std::collections::{HashMap, HashSet};

const INLINE_BUDGET: usize = 8;
const MATCHER_INLINE_BUDGET: usize = 12;
const MAX_ITERATIONS: usize = 3;
const GROWTH_CAP: usize = 4;

// ---------- predicates ----------

pub fn is_leaf(f: &FnIr) -> bool {
    f.blocks.iter().all(|b| {
        !matches!(
            b.terminator,
            Term::Call { .. }
                | Term::TailCall { .. }
                | Term::CallClosure { .. }
                | Term::TailCallClosure { .. }
                | Term::Receive { .. }
                | Term::ReceiveMatched { .. }
        )
    })
}

pub fn stmt_count(f: &FnIr) -> usize {
    f.blocks.iter().map(|b| b.stmts.len()).sum()
}

pub fn is_inlinable(f: &FnIr) -> bool {
    // fz-puj.52.8 — callable matcher routers inline only through the
    // matcher shell. The inliner also refuses to inline callees into a
    // Matcher, so leaf bodies stay behind the match decision point instead
    // of being cloned with the router. Router bodies are often mostly
    // terminators rather than stmts, so stmt_count alone misses clone cost.
    if is_matcher_router(f) {
        return matcher_inline_cost(f) <= MATCHER_INLINE_BUDGET;
    }
    is_leaf(f) && stmt_count(f) <= INLINE_BUDGET
}

pub fn matcher_inline_cost(f: &FnIr) -> usize {
    stmt_count(f) + (f.blocks.len() * 2)
}

/// Small matcher fns are pure control-flow routers. They can contain
/// multiple blocks and tail-call leaves/fail continuations, so they are not
/// leaves, but splicing them at a tail-call site is semantically the same as
/// inlining a hand-written branch tree.
pub fn is_matcher_router(f: &FnIr) -> bool {
    // ExternMatcher is deliberately excluded: it carries an `extern "C"`
    // call convention (msg, pinned, out) -> u32 dictated by the receive
    // matcher contract, so splicing its body at an internal tail-call site
    // would be a call-convention violation.
    //
    // fz-puj.35 (H5) — Return is admitted alongside the other tail
    // shapes. After an earlier pass inlines a leaf clause cont fn into
    // the matcher, the matcher's TailCall(clause_cont) becomes Return(v).
    // Splicing such a matcher at a TailCall site turns the caller's tail
    // into Return(v) (correct); at a Call site, `inline_calls_once`
    // rewrites Return(v) to TailCall(cont, [v, ...captures]).
    f.category == FnCategory::Matcher
        && f.blocks.iter().all(|b| {
            matches!(
                b.terminator,
                Term::Goto(..)
                    | Term::If { .. }
                    | Term::TailCall { .. }
                    | Term::Halt(_)
                    | Term::Return(_)
            )
        })
}

/// fz-ul4.43.D.0 — A "pure tail caller" is a single-block fn whose only
/// terminator is `TailCall(target, args)`. Its stmts compute the args
/// then transfer control. Inlining it through a caller's TailCall
/// substitutes args into the stmts and splices the inner TailCall up to
/// the caller — turning chained tail-calls into one.
///
/// This is the shape lower_multi_clause/case/with mint for clause bodies
/// that end in a recursive call (e.g. `count(n-1, acc+1)`). Without
/// this path, those cont fns are permanent overhead since `is_inlinable`
/// requires a leaf. With it, the matrix-leaf cont_fn becomes free for
/// the common recursive-body shape.
pub fn is_pure_tail_caller(f: &FnIr) -> bool {
    if f.blocks.len() != 1 {
        return false;
    }
    let b = &f.blocks[0];
    if !matches!(
        b.terminator,
        Term::TailCall { .. } | Term::TailCallClosure { .. }
    ) {
        return false;
    }
    if stmt_count(f) > INLINE_BUDGET {
        return false;
    }
    true
}

/// Fns referenced by any `MakeClosure` in the module. These must remain
/// callable as closure targets and must never be inlined away — inlining
/// their only direct callsite would make the planner's reachability analysis
/// drop them from `module_plan.specs`, breaking the `.29.12.2` spec-fnidx
/// table that codegen uses to find live closure stubs.
fn closure_targets(m: &Module) -> HashSet<FnId> {
    let mut set = HashSet::new();
    for f in &m.fns {
        for b in &f.blocks {
            for s in &b.stmts {
                let Stmt::Let(_, Prim::MakeClosure(_, fid, _)) = s else {
                    continue;
                };
                set.insert(*fid);
            }
        }
    }
    set
}

// ---------- alpha-rename ----------

fn max_var(f: &FnIr) -> u32 {
    let mut m = 0u32;
    for b in &f.blocks {
        for p in &b.params {
            m = m.max(p.0);
        }
        for s in &b.stmts {
            let Stmt::Let(v, prim) = s;
            m = m.max(v.0);
            m = m.max(max_var_in_prim(prim));
        }
        m = m.max(max_var_in_term(&b.terminator));
    }
    m
}

fn max_block(f: &FnIr) -> u32 {
    f.blocks.iter().map(|b| b.id.0).max().unwrap_or(0)
}

fn max_var_in_prim(p: &Prim) -> u32 {
    let mut m = 0u32;
    let mut v = |x: Var| m = m.max(x.0);
    match p {
        Prim::Const(_) => {}
        Prim::BinOp(_, a, b) => {
            v(*a);
            v(*b);
        }
        Prim::UnOp(_, a) => v(*a),
        Prim::Extern(_, args) => args.iter().for_each(|x| v(x.var)),
        Prim::ListHead(a) | Prim::ListTail(a) | Prim::IsEmptyList(a) => v(*a),
        Prim::MakeTuple(args) => args.iter().for_each(|x| v(*x)),
        Prim::DestTupleBegin { .. } => {}
        Prim::DestTupleSet { dest, value, .. } => {
            v(*dest);
            v(*value);
        }
        Prim::DestFreeze { dest, .. } => v(*dest),
        Prim::DestListBegin { .. } => {}
        Prim::DestListCons { head, tail, .. } => {
            v(*head);
            if let Some(tail) = tail {
                v(*tail);
            }
        }
        Prim::DestListFreeze { list, .. } => v(*list),
        Prim::TupleField(a, _) => v(*a),
        Prim::MakeList(els, tail) => {
            els.iter().for_each(|x| v(*x));
            if let Some(t) = tail {
                v(*t);
            }
        }
        Prim::MakeClosure(_, _, caps) => caps.iter().for_each(|x| v(*x)),
        Prim::MakeMap(entries) => entries.iter().for_each(|(k, val)| {
            v(*k);
            v(*val);
        }),
        Prim::MapUpdate(base, entries) => {
            v(*base);
            entries.iter().for_each(|(k, val)| {
                v(*k);
                v(*val);
            });
        }
        Prim::DestMapBegin { base, .. } => {
            if let Some(base) = base {
                v(*base);
            }
        }
        Prim::DestMapPut {
            map, key, value, ..
        } => {
            v(*map);
            v(*key);
            v(*value);
        }
        Prim::DestMapFreeze { map, .. } => v(*map),
        Prim::MapGet(a, b) | Prim::MatcherMapGet(a, b) => {
            v(*a);
            v(*b);
        }
        Prim::IsMatcherMapMiss(value) => v(*value),
        Prim::MakeBitstring(fields) => fields.iter().for_each(|f| {
            v(f.value);
            if let Some(BitSizeIr::Var(sv)) = &f.size {
                v(*sv);
            }
        }),
        Prim::ConstBitstring(_, _) => {}
        Prim::BitReaderInit(a) | Prim::BitReaderDone(a) => v(*a),
        Prim::BitReadField { reader, size, .. } => {
            v(*reader);
            if let Some(BitSizeIr::Var(sv)) = size {
                v(*sv);
            }
        }
        Prim::TypeTest(a, _) => v(*a),
        Prim::Brand(a, _) => v(*a),
    }
    m
}

fn max_var_in_term(t: &Term) -> u32 {
    let mut m = 0u32;
    let mut v = |x: Var| m = m.max(x.0);
    match t {
        Term::Goto(_, args) => args.iter().for_each(|x| v(*x)),
        Term::If { cond, .. } => v(*cond),
        Term::Call {
            ident: _,
            args,
            continuation,
            ..
        } => {
            args.iter().for_each(|x| v(*x));
            continuation.captured.iter().for_each(|x| v(*x));
        }
        Term::TailCall { args, .. } => args.iter().for_each(|x| v(*x)),
        Term::CallClosure {
            ident: _,
            closure,
            args,
            continuation,
        } => {
            v(*closure);
            args.iter().for_each(|x| v(*x));
            continuation.captured.iter().for_each(|x| v(*x));
        }
        Term::TailCallClosure {
            closure,
            args,
            ident: _,
        } => {
            v(*closure);
            args.iter().for_each(|x| v(*x));
        }
        Term::Return(a) | Term::Halt(a) => v(*a),
        Term::Receive {
            continuation,
            ident: _,
        } => continuation.captured.iter().for_each(|x| v(*x)),
        Term::ReceiveMatched {
            pinned,
            captures,
            after,
            ..
        } => {
            pinned.iter().for_each(|(_, x)| v(*x));
            captures.iter().for_each(|x| v(*x));
            if let Some(a) = after {
                v(a.timeout);
            }
        }
    }
    m
}

/// Return a copy of `callee` with all Var and BlockId values shifted by
/// `var_shift` and `block_shift` respectively. Also returns the forward maps
/// (original → renamed) for callers that need to substitute entry params.
pub fn alpha_rename(callee: &FnIr, caller: &FnIr) -> FnIr {
    let var_shift = max_var(caller) + 1;
    let block_shift = max_block(caller) + 1;
    let into_fn = caller.id;

    let shift_v = |v: Var| Var(v.0 + var_shift);
    let shift_b = |b: BlockId| BlockId(b.0 + block_shift);

    // fz-kgk — when alpha-renaming a callee body into a caller, every
    // call-shape Term and every MakeClosure stmt gets a FRESH ident via
    // `fork_inlined`. Same source span, new identity. The cloned
    // callsite is a distinct dispatch in the caller's per-spec view.
    let fork = |parent: &crate::fz_ir::CallsiteIdent| -> crate::fz_ir::CallsiteIdent {
        crate::fz_ir::CallsiteIdent::fork_inlined(parent, into_fn)
    };

    let rename_prim = |p: &Prim| -> Prim {
        let sv = |v: Var| Var(v.0 + var_shift);
        match p {
            Prim::Const(c) => Prim::Const(c.clone()),
            Prim::BinOp(op, a, b) => Prim::BinOp(*op, sv(*a), sv(*b)),
            Prim::UnOp(op, a) => Prim::UnOp(*op, sv(*a)),
            Prim::Extern(eid, args) => Prim::Extern(
                *eid,
                args.iter()
                    .map(|x| crate::fz_ir::ExternArg {
                        var: sv(x.var),
                        ..*x
                    })
                    .collect(),
            ),
            Prim::ListHead(a) => Prim::ListHead(sv(*a)),
            Prim::ListTail(a) => Prim::ListTail(sv(*a)),
            Prim::IsEmptyList(a) => Prim::IsEmptyList(sv(*a)),
            Prim::MakeTuple(args) => Prim::MakeTuple(args.iter().map(|x| sv(*x)).collect()),
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
            Prim::MakeList(els, tail) => {
                Prim::MakeList(els.iter().map(|x| sv(*x)).collect(), tail.map(sv))
            }
            Prim::MakeClosure(ident, fid, caps) => {
                Prim::MakeClosure(fork(ident), *fid, caps.iter().map(|x| sv(*x)).collect())
            }
            Prim::MakeMap(entries) => {
                Prim::MakeMap(entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect())
            }
            Prim::MapUpdate(base, entries) => Prim::MapUpdate(
                sv(*base),
                entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect(),
            ),
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
                    .map(|f| crate::fz_ir::BitFieldIr {
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
            Prim::TypeTest(a, d) => Prim::TypeTest(sv(*a), d.clone()),
            Prim::Brand(a, name) => Prim::Brand(sv(*a), name.clone()),
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
        }
    };

    let rename_cont = |c: &Cont| -> Cont {
        Cont {
            fn_id: c.fn_id,
            captured: c.captured.iter().map(|x| shift_v(*x)).collect(),
        }
    };

    let rename_term = |t: &Term| -> Term {
        let sv = shift_v;
        let sb = shift_b;
        match t {
            Term::Goto(b, args) => Term::Goto(sb(*b), args.iter().map(|x| sv(*x)).collect()),
            Term::If {
                cond,
                then_b,
                else_b,
                origin,
            } => Term::If {
                cond: sv(*cond),
                then_b: sb(*then_b),
                else_b: sb(*else_b),
                origin: *origin,
            },
            Term::Call {
                ident,
                callee,
                args,
                continuation,
            } => Term::Call {
                ident: fork(ident),
                callee: *callee,
                args: args.iter().map(|x| sv(*x)).collect(),
                continuation: rename_cont(continuation),
            },
            Term::TailCall {
                ident,
                callee,
                args,
                is_back_edge,
            } => Term::TailCall {
                ident: fork(ident),
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
                ident: fork(ident),
                closure: sv(*closure),
                args: args.iter().map(|x| sv(*x)).collect(),
                continuation: rename_cont(continuation),
            },
            Term::TailCallClosure {
                closure,
                args,
                ident,
            } => Term::TailCallClosure {
                ident: fork(ident),
                closure: sv(*closure),
                args: args.iter().map(|x| sv(*x)).collect(),
            },
            Term::Return(a) => Term::Return(sv(*a)),
            Term::Halt(a) => Term::Halt(sv(*a)),
            Term::Receive {
                continuation,
                ident,
            } => Term::Receive {
                ident: fork(ident),
                continuation: rename_cont(continuation),
            },
            // fz-yxs — alpha-rename Vars (pinned/captures/timeout) and
            // mint fresh idents. Clause/after body FnIds and patterns
            // are not renamed: they live as module-level fns and source-
            // level AST respectively, neither participates in the var/
            // block shift.
            Term::ReceiveMatched {
                ident,
                clauses,
                matcher,
                after,
                pinned,
                captures,
            } => Term::ReceiveMatched {
                ident: fork(ident),
                clauses: clauses.clone(),
                matcher: matcher.clone(),
                after: after.as_ref().map(|a| crate::fz_ir::ReceiveAfter {
                    timeout: sv(a.timeout),
                    body: a.body,
                    span: a.span,
                }),
                pinned: pinned.iter().map(|(n, v)| (n.clone(), sv(*v))).collect(),
                captures: captures.iter().map(|x| sv(*x)).collect(),
            },
        }
    };

    let blocks: Vec<Block> = callee
        .blocks
        .iter()
        .map(|b| Block {
            id: shift_b(b.id),
            params: b.params.iter().map(|x| shift_v(*x)).collect(),
            stmts: b
                .stmts
                .iter()
                .map(|s| {
                    let Stmt::Let(v, p) = s;
                    Stmt::Let(shift_v(*v), rename_prim(p))
                })
                .collect(),
            terminator: rename_term(&b.terminator),
        })
        .collect();

    FnIr {
        id: callee.id,
        name: callee.name.clone(),
        frame_schema_id: 0,
        blocks,
        entry: shift_b(callee.entry),
        category: callee.category,
        owner_module: callee.owner_module.clone(),
        ignored_entry_params: callee.ignored_entry_params.clone(),
    }
}

// ---------- absorb ----------

/// Inline `callee` at block `bi` of `caller`.
///
/// Substitutes `args` for the callee's entry-block params, appends the entry
/// block's stmts to caller's block, sets the caller terminator to the entry
/// terminator, and splices in the remaining callee blocks — all without
/// creating a Goto.  `callee` must already be alpha-renamed so its vars are
/// disjoint from `caller`'s.
pub fn absorb_callee(caller: &mut FnIr, bi: usize, mut callee: FnIr, args: &[Var]) {
    let entry_id = callee.entry;
    let entry_idx = callee
        .blocks
        .iter()
        .position(|b| b.id == entry_id)
        .expect("callee entry block missing");

    let params: Vec<Var> = callee.blocks[entry_idx].params.clone();
    debug_assert_eq!(
        params.len(),
        args.len(),
        "absorb_callee: arity mismatch — {} params vs {} args",
        params.len(),
        args.len()
    );

    let subst: HashMap<Var, Var> = params.into_iter().zip(args.iter().copied()).collect();

    if !subst.is_empty() {
        for b in &mut callee.blocks {
            b.stmts = b.stmts.iter().map(|s| subst_stmt(s, &subst)).collect();
            b.terminator = subst_term(&b.terminator, &subst);
        }
    }

    let entry_block = callee.blocks.remove(entry_idx);
    // entry_block.params is now stale but we discard the block after splicing.

    caller.blocks[bi].stmts.extend(entry_block.stmts);
    caller.blocks[bi].terminator = entry_block.terminator;
    caller.blocks.extend(callee.blocks);
}

// ---------- pass: inline_tail_calls_once ----------

/// One pass over `m`: for every `TailCall { callee, args }` where `callee` is
/// inlinable, replace the block's terminator with a `Goto` to the callee's
/// (alpha-renamed) entry, substituting `args` for the entry params.
/// Returns the number of inlinings performed.
pub fn inline_tail_calls_once(m: &mut Module) -> usize {
    let mut count = 0;
    let closure_fns = closure_targets(m);

    // Collect (fn_idx, block_idx) pairs that need inlining.
    // Borrow check: we need to read callee and mutate caller separately.
    let work: Vec<(usize, usize, FnId, Vec<Var>)> = m
        .fns
        .iter()
        .enumerate()
        .flat_map(|(fi, f)| {
            f.blocks.iter().enumerate().filter_map(move |(bi, b)| {
                if let Term::TailCall { callee, args, .. } = &b.terminator {
                    let callee = *callee;
                    let args = args.clone();
                    Some((fi, bi, callee, args))
                } else {
                    None
                }
            })
        })
        .collect();

    for (fi, bi, callee_id, args) in work {
        if m.fns[fi].category == FnCategory::Matcher {
            continue;
        }
        if closure_fns.contains(&callee_id) {
            continue; // closure target — must stay callable, don't inline
        }
        // fz-jg5.12 (RED.9): @spec'd fns are reduction boundaries.
        if m.boundary_fns.contains(&callee_id) {
            continue;
        }
        let callee_idx = match m.fn_idx.get(&callee_id) {
            Some(&i) => i,
            None => continue,
        };
        if callee_idx == fi {
            continue; // self-recursive — skip
        }
        if !is_inlinable(&m.fns[callee_idx]) && !is_pure_tail_caller(&m.fns[callee_idx]) {
            continue;
        }

        let callee = m.fns[callee_idx].clone();
        let caller = &m.fns[fi];
        let renamed = alpha_rename(&callee, caller);

        absorb_callee(&mut m.fns[fi], bi, renamed, &args);
        count += 1;
    }

    count
}

// ---------- pass: inline_calls_once ----------

/// One pass over `m`: for every `Call { callee, args, continuation: Cont { fn_id: K, captured } }`
/// where `callee` is inlinable, inline the callee body and rewrite each
/// `Return(v')` in the callee to `TailCall(K, [v', captured...])`.
/// Returns the number of inlinings performed.
pub fn inline_calls_once(m: &mut Module) -> usize {
    let mut count = 0;
    let closure_fns = closure_targets(m);

    type InlineWorkItem = (
        usize,
        usize,
        FnId,
        Vec<Var>,
        FnId,
        Vec<Var>,
        crate::fz_ir::CallsiteIdent,
    );
    let work: Vec<InlineWorkItem> = m
        .fns
        .iter()
        .enumerate()
        .flat_map(|(fi, f)| {
            f.blocks.iter().enumerate().filter_map(move |(bi, b)| {
                if let Term::Call {
                    ident,
                    callee,
                    args,
                    continuation,
                } = &b.terminator
                {
                    Some((
                        fi,
                        bi,
                        *callee,
                        args.clone(),
                        continuation.fn_id,
                        continuation.captured.clone(),
                        ident.clone(),
                    ))
                } else {
                    None
                }
            })
        })
        .collect();

    for (fi, bi, callee_id, args, cont_fn, cont_captured, call_ident) in work {
        if m.fns[fi].category == FnCategory::Matcher {
            continue;
        }
        if closure_fns.contains(&callee_id) {
            continue;
        }
        // fz-jg5.12 (RED.9): @spec'd fns are reduction boundaries. The
        // user signed a contract by declaring the spec; honor it across
        // every "inline" pass, not just the reducer.
        if m.boundary_fns.contains(&callee_id) {
            continue;
        }
        let callee_idx = match m.fn_idx.get(&callee_id) {
            Some(&i) => i,
            None => continue,
        };
        if callee_idx == fi {
            continue;
        }
        if !is_inlinable(&m.fns[callee_idx]) {
            continue;
        }

        let callee = m.fns[callee_idx].clone();
        let caller = &m.fns[fi];
        let mut renamed = alpha_rename(&callee, caller);

        // Rewrite each Return(v') in the renamed body to
        // TailCall(K, [v', cont_captured...]).
        //
        // fz-kgk — Each rewritten TailCall is a NEW callsite (didn't
        // exist before inline-splice). Mint a synthesized ident whose
        // origin records the parent Call's identity, so the divergence
        // narrative can name which Call's splice introduced this site.
        for b in &mut renamed.blocks {
            if let Term::Return(ret_val) = b.terminator {
                let mut tail_args = vec![ret_val];
                tail_args.extend_from_slice(&cont_captured);
                b.terminator = Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::synthesize_from_return(
                        &call_ident,
                        call_ident.span(),
                    ),
                    callee: cont_fn,
                    args: tail_args,
                    is_back_edge: false,
                };
            }
        }

        absorb_callee(&mut m.fns[fi], bi, renamed, &args);
        count += 1;
    }

    count
}

// ---------- pass: inline_single_use_conts_once ----------

/// One pass: for every continuation fn `k` that is:
///   - the callee of exactly one `TailCall` (in fn F at block B), and
///   - referenced by at most one `Cont { fn_id: k }` in some `Term::Call`
///     with empty captures,
///
/// inline k's blocks into F (replacing the TailCall with a Goto), then:
///   - if there was a `Term::Call { callee: G, continuation: Cont { fn_id: k } }`
///     in some fn M, convert it to `TailCall { callee: G, args }` — the
///     continuation has been absorbed into F.
///   - remove k from the module.
///
/// This eliminates the CPS-overhead functions that fold+DCE produce when a
/// `Term::If` becomes `Term::Goto`: the surviving single-path continuation
/// chain collapses into one function.
pub fn inline_single_use_conts_once(m: &mut Module) -> usize {
    use std::collections::HashMap;
    let closure_fns = closure_targets(m);

    // Count non-back-edge TailCall sites per FnId.
    let mut tc_sites: HashMap<FnId, Vec<(usize, usize)>> = HashMap::new();
    // Count back-edge TailCall references per FnId (any function targeting k
    // via a back-edge). Removing k while these exist would leave them dangling.
    let mut be_tc_count: HashMap<FnId, usize> = HashMap::new();
    for (fi, f) in m.fns.iter().enumerate() {
        for (bi, b) in f.blocks.iter().enumerate() {
            if let Term::TailCall {
                ident: _,
                callee,
                is_back_edge,
                ..
            } = &b.terminator
            {
                if *is_back_edge {
                    *be_tc_count.entry(*callee).or_insert(0) += 1;
                } else {
                    tc_sites.entry(*callee).or_default().push((fi, bi));
                }
            }
        }
    }

    // Count Cont references per FnId.
    let mut cont_sites: HashMap<FnId, Vec<(usize, usize)>> = HashMap::new();
    // Count direct Term::Call callee references per FnId (not as continuation).
    // A function appearing here as callee is a live use — inlining+removing it
    // would leave those Call sites dangling.
    let mut direct_call_sites: HashMap<FnId, usize> = HashMap::new();
    for (fi, f) in m.fns.iter().enumerate() {
        for (bi, b) in f.blocks.iter().enumerate() {
            let k = match &b.terminator {
                Term::Call {
                    ident: _,
                    callee,
                    continuation,
                    ..
                } => {
                    *direct_call_sites.entry(*callee).or_insert(0) += 1;
                    Some(continuation.fn_id)
                }
                Term::CallClosure { continuation, .. } => Some(continuation.fn_id),
                Term::Receive {
                    continuation,
                    ident: _,
                } => Some(continuation.fn_id),
                _ => None,
            };
            if let Some(kid) = k {
                cont_sites.entry(kid).or_default().push((fi, bi));
            }
        }
    }

    for (k_id, tcs) in &tc_sites {
        if tcs.len() != 1 {
            continue;
        }
        let (caller_fi, caller_bi) = tcs[0];
        if closure_fns.contains(k_id) {
            continue;
        }
        // Skip if k appears as a direct callee in any Term::Call — removing it
        // would leave those sites dangling (catches non-tail recursion and
        // multi-site user functions like step(step(step(...)))).
        if direct_call_sites.get(k_id).copied().unwrap_or(0) > 0 {
            continue;
        }
        // Skip if any back-edge TailCall targets k (mutual or direct
        // back-edge recursion — removing k would leave those sites dangling).
        if be_tc_count.get(k_id).copied().unwrap_or(0) > 0 {
            continue;
        }
        let k_idx = match m.fn_idx.get(k_id) {
            Some(&i) => i,
            None => continue,
        };
        if k_idx == caller_fi {
            continue; // self-tail — skip
        }
        // No receive boundary inside k — runtime async boundaries can't be
        // inlined away. ReceiveMatched parks a closure template whose env
        // layout is fixed at the park site; absorbing that continuation into
        // its caller can leave the resumed body expecting a different outcome
        // closure shape.
        if m.fns[k_idx].blocks.iter().any(|b| {
            matches!(
                b.terminator,
                Term::Receive { .. } | Term::ReceiveMatched { .. }
            )
        }) {
            continue;
        }
        // No self-references inside k — inlining removes k from the module,
        // so any Term::Call/TailCall with callee==k_id would become dangling.
        // This catches both back-edge tail-recursion and non-tail recursion.
        if m.fns[k_idx].blocks.iter().any(|b| match &b.terminator {
            Term::TailCall { callee, .. } | Term::Call { callee, .. } => callee == k_id,
            _ => false,
        }) {
            continue;
        }
        // At most one Cont ref, and if so captured must be empty.
        let conts = cont_sites.get(k_id).map(|v| v.as_slice()).unwrap_or(&[]);
        if conts.len() > 1 {
            continue;
        }
        let cont_site = conts.first().copied();
        if let Some((m_fi, m_bi)) = cont_site {
            let ok = match &m.fns[m_fi].blocks[m_bi].terminator {
                Term::Call { continuation, .. } | Term::CallClosure { continuation, .. } => {
                    continuation.fn_id == *k_id && continuation.captured.is_empty()
                }
                _ => false,
            };
            if !ok {
                continue;
            }
        }

        // Inline k into caller.
        let tail_args = match &m.fns[caller_fi].blocks[caller_bi].terminator {
            Term::TailCall { args, .. } => args.clone(),
            _ => continue,
        };
        let k_fn = m.fns[k_idx].clone();
        let renamed = alpha_rename(&k_fn, &m.fns[caller_fi]);
        absorb_callee(&mut m.fns[caller_fi], caller_bi, renamed, &tail_args);

        // Convert the Term::Call at the Cont site to TailCall.
        //
        // fz-kgk — INHERIT the original Call/CallClosure's ident on the
        // new TailCall/TailCallClosure. Same callsite, transformed
        // terminator shape (cont was absorbed into caller, so the call
        // can now hand its result back directly via TailCall).
        if let Some((m_fi, m_bi)) = cont_site {
            let new_term = match &m.fns[m_fi].blocks[m_bi].terminator {
                Term::Call {
                    ident,
                    callee,
                    args,
                    ..
                } => Some(Term::TailCall {
                    ident: ident.clone(),
                    callee: *callee,
                    args: args.clone(),
                    is_back_edge: false,
                }),
                Term::CallClosure {
                    ident,
                    closure,
                    args,
                    ..
                } => Some(Term::TailCallClosure {
                    ident: ident.clone(),
                    closure: *closure,
                    args: args.clone(),
                }),
                _ => None,
            };
            if let Some(t) = new_term {
                m.fns[m_fi].blocks[m_bi].terminator = t;
            }
        }

        // Remove k and rebuild the index.
        m.fns.remove(k_idx);
        m.fn_idx.clear();
        for (i, f) in m.fns.iter().enumerate() {
            m.fn_idx.insert(f.id, i);
        }

        return 1; // restart — indices changed
    }
    0
}

/// Run single-use continuation inlining to fixed-point.
///
/// fz-uwq.2 — this pass now runs pre-planner, so no `ModulePlan` exist
/// yet to surgically maintain. The subsequent `plan_module` call in
/// the codegen pipeline observes the post-inline module directly.
pub fn inline_single_use_conts(m: &mut Module) {
    loop {
        if inline_single_use_conts_once(m) == 0 {
            break;
        }
    }
}

// ---------- driver ----------

/// Run both inliner passes to fixed-point (up to MAX_ITERATIONS rounds).
/// Returns total inlinings performed.
pub fn inline_module(m: &mut Module) -> usize {
    let base_stmts: usize = m.fns.iter().map(stmt_count).sum();
    let cap = base_stmts * GROWTH_CAP + 1;
    let mut total = 0;

    for _ in 0..MAX_ITERATIONS {
        let n = inline_tail_calls_once(m) + inline_calls_once(m);
        if n == 0 {
            break;
        }
        total += n;
        let new_stmts: usize = m.fns.iter().map(stmt_count).sum();
        if new_stmts > cap {
            break;
        }
    }

    total
}

// ---------- tests ----------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fz_ir::{
        BinOp, BranchOrigin, Const, FnBuilder, FnCategory, FnId, FnIr, ModuleBuilder, Prim, Stmt,
        Term, Var,
    };
    use crate::types::Types;

    fn make_leaf_add1() -> FnIr {
        // fn add1(x) { let one = 1; let s = x+one; return s }
        let mut b = FnBuilder::new(FnId(1), "add1");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let s = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
        b.set_terminator(entry, Term::Return(s));
        b.build()
    }

    fn make_caller_tail(callee: FnId) -> FnIr {
        // fn caller(y) { tail_call callee(y) }
        let mut b = FnBuilder::new(FnId(0), "caller");
        let y = b.fresh_var();
        let entry = b.block(vec![y]);
        b.set_terminator(
            entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee,
                args: vec![y],
                is_back_edge: false,
            },
        );
        b.build()
    }

    fn make_caller_call(callee: FnId) -> FnIr {
        // fn caller(y) { call callee(y) -> cont(K, captured=[]) }
        let k = FnId(99);
        let mut b = FnBuilder::new(FnId(0), "caller");
        let y = b.fresh_var();
        let entry = b.block(vec![y]);
        b.set_terminator(
            entry,
            Term::Call {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee,
                args: vec![y],
                continuation: Cont {
                    fn_id: k,
                    captured: vec![],
                },
            },
        );
        b.build()
    }

    fn make_wildcard_matcher(callee: FnId) -> FnIr {
        let mut b = FnBuilder::new(FnId(10), "match_wildcard").with_category(FnCategory::Matcher);
        let msg = b.fresh_var();
        let entry = b.block(vec![msg]);
        b.set_terminator(
            entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee,
                args: vec![msg],
                is_back_edge: false,
            },
        );
        b.build()
    }

    fn make_bool_matcher(then_callee: FnId, else_callee: FnId) -> FnIr {
        let mut b = FnBuilder::new(FnId(10), "match_bool").with_category(FnCategory::Matcher);
        let msg = b.fresh_var();
        let entry = b.block(vec![msg]);
        let then_b = b.block(vec![]);
        let else_b = b.block(vec![]);
        let lit = b.let_(entry, Prim::Const(Const::True));
        let cond = b.let_(entry, Prim::BinOp(BinOp::Eq, msg, lit));
        b.set_terminator(
            entry,
            Term::If {
                cond,
                then_b,
                else_b,
                origin: BranchOrigin::ClauseDispatch,
            },
        );
        b.set_terminator(
            then_b,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: then_callee,
                args: vec![msg],
                is_back_edge: false,
            },
        );
        b.set_terminator(
            else_b,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: else_callee,
                args: vec![msg],
                is_back_edge: false,
            },
        );
        b.build()
    }

    fn make_tuple_matcher(arity_1: FnId, arity_2: FnId, fallback: FnId) -> FnIr {
        let mut b = FnBuilder::new(FnId(10), "match_tuple").with_category(FnCategory::Matcher);
        let msg = b.fresh_var();
        let entry = b.block(vec![msg]);
        let arity_1_b = b.block(vec![]);
        let arity_2_test_b = b.block(vec![]);
        let arity_2_b = b.block(vec![]);
        let fallback_b = b.block(vec![]);

        let mut types = crate::types::ConcreteTypes;
        let any = types.any();
        let tuple_1 = types.tuple(std::slice::from_ref(&any));
        let tuple_2 = types.tuple(&[any.clone(), any]);

        let is_arity_1 = b.let_(entry, Prim::TypeTest(msg, Box::new(tuple_1)));
        b.set_terminator(
            entry,
            Term::If {
                cond: is_arity_1,
                then_b: arity_1_b,
                else_b: arity_2_test_b,
                origin: BranchOrigin::ClauseDispatch,
            },
        );
        let is_arity_2 = b.let_(arity_2_test_b, Prim::TypeTest(msg, Box::new(tuple_2)));
        b.set_terminator(
            arity_2_test_b,
            Term::If {
                cond: is_arity_2,
                then_b: arity_2_b,
                else_b: fallback_b,
                origin: BranchOrigin::ClauseDispatch,
            },
        );
        for (block, callee) in [
            (arity_1_b, arity_1),
            (arity_2_b, arity_2),
            (fallback_b, fallback),
        ] {
            b.set_terminator(
                block,
                Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::synthetic(),
                    callee,
                    args: vec![msg],
                    is_back_edge: false,
                },
            );
        }
        b.build()
    }

    fn make_large_matcher(leaf: FnId, fallback: FnId, tests: usize) -> FnIr {
        let mut b = FnBuilder::new(FnId(10), "match_large").with_category(FnCategory::Matcher);
        let msg = b.fresh_var();
        let entry = b.block(vec![msg]);
        let mut test_blocks = Vec::with_capacity(tests);
        test_blocks.push(entry);
        for _ in 1..tests {
            test_blocks.push(b.block(vec![]));
        }
        let leaf_b = b.block(vec![]);
        let fallback_b = b.block(vec![]);

        for (i, block) in test_blocks.iter().copied().enumerate() {
            let lit = b.let_(block, Prim::Const(Const::Int(i as i64)));
            let cond = b.let_(block, Prim::BinOp(BinOp::Eq, msg, lit));
            let else_b = test_blocks.get(i + 1).copied().unwrap_or(fallback_b);
            b.set_terminator(
                block,
                Term::If {
                    cond,
                    then_b: leaf_b,
                    else_b,
                    origin: BranchOrigin::ClauseDispatch,
                },
            );
        }
        for (block, callee) in [(leaf_b, leaf), (fallback_b, fallback)] {
            b.set_terminator(
                block,
                Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::synthetic(),
                    callee,
                    args: vec![msg],
                    is_back_edge: false,
                },
            );
        }
        b.build()
    }

    // --- is_leaf ---

    #[test]
    fn is_leaf_pure_return() {
        assert!(is_leaf(&make_leaf_add1()));
    }

    #[test]
    fn is_leaf_tail_call_is_not_leaf() {
        let f = make_caller_tail(FnId(1));
        assert!(!is_leaf(&f));
    }

    #[test]
    fn is_leaf_call_is_not_leaf() {
        let f = make_caller_call(FnId(1));
        assert!(!is_leaf(&f));
    }

    #[test]
    fn is_leaf_receive_is_not_leaf() {
        let mut b = FnBuilder::new(FnId(0), "recv");
        let entry = b.block(vec![]);
        b.set_terminator(
            entry,
            Term::Receive {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                continuation: Cont {
                    fn_id: FnId(7),
                    captured: vec![],
                },
            },
        );
        assert!(!is_leaf(&b.build()));
    }

    #[test]
    fn is_leaf_receive_matched_is_not_leaf() {
        let mut b = FnBuilder::new(FnId(0), "recv_matched");
        let entry = b.block(vec![]);
        let matcher = crate::matcher::Matcher {
            inputs: Vec::new(),
            pinned: Vec::new(),
            prepared_keys: Vec::new(),
            nodes: vec![crate::matcher::MatcherNode::Fail {
                span: crate::diag::Span::DUMMY,
            }],
            root: crate::matcher::NodeId(0),
        };
        b.set_terminator(
            entry,
            Term::ReceiveMatched {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                clauses: Vec::new(),
                matcher: std::sync::Arc::new(matcher),
                after: None,
                pinned: Vec::new(),
                captures: Vec::new(),
            },
        );
        assert!(!is_leaf(&b.build()));
    }

    #[test]
    fn is_leaf_call_closure_is_not_leaf() {
        let mut b = FnBuilder::new(FnId(0), "cc");
        let cl = b.fresh_var();
        let entry = b.block(vec![cl]);
        b.set_terminator(
            entry,
            Term::CallClosure {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                closure: cl,
                args: vec![],
                continuation: Cont {
                    fn_id: FnId(7),
                    captured: vec![],
                },
            },
        );
        assert!(!is_leaf(&b.build()));
    }

    #[test]
    fn is_leaf_tail_call_closure_is_not_leaf() {
        let mut b = FnBuilder::new(FnId(0), "tcc");
        let cl = b.fresh_var();
        let entry = b.block(vec![cl]);
        b.set_terminator(
            entry,
            Term::TailCallClosure {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                closure: cl,
                args: vec![],
            },
        );
        assert!(!is_leaf(&b.build()));
    }

    // --- stmt_count ---

    #[test]
    fn stmt_count_sums_all_blocks() {
        let f = make_leaf_add1(); // 2 stmts in one block
        assert_eq!(stmt_count(&f), 2);
    }

    #[test]
    fn stmt_count_multi_block() {
        let mut b = FnBuilder::new(FnId(0), "f");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let _a = b.let_(entry, Prim::Const(Const::Int(1)));
        let next = b.block(vec![]);
        let _c = b.let_(next, Prim::Const(Const::Int(2)));
        let _d = b.let_(next, Prim::Const(Const::Int(3)));
        b.set_terminator(entry, Term::Goto(next, vec![]));
        b.set_terminator(next, Term::Halt(Var(0)));
        assert_eq!(stmt_count(&b.build()), 3);
    }

    #[test]
    fn matcher_inline_cost_counts_blocks_and_stmts() {
        let matcher = make_tuple_matcher(FnId(20), FnId(21), FnId(22));
        assert_eq!(stmt_count(&matcher), 2);
        assert_eq!(matcher.blocks.len(), 5);
        assert_eq!(matcher_inline_cost(&matcher), 12);
        assert!(is_inlinable(&matcher));
    }

    #[test]
    fn large_matcher_router_exceeds_inline_budget() {
        let matcher = make_large_matcher(FnId(20), FnId(21), 6);
        assert!(is_matcher_router(&matcher));
        assert!(
            matcher_inline_cost(&matcher) > MATCHER_INLINE_BUDGET,
            "test premise: large matcher cost must exceed budget"
        );
        assert!(!is_inlinable(&matcher));
    }

    // --- alpha_rename ---

    #[test]
    fn alpha_rename_shifts_vars_above_caller_max() {
        let callee = make_leaf_add1(); // vars 0,1,2; blocks 0
        let caller = make_caller_tail(FnId(1)); // vars 0; blocks 0
        let renamed = alpha_rename(&callee, &caller);

        // caller max_var = 0, so callee vars shift by 1
        // callee var 0 → 1, var 1 → 2, var 2 → 3
        for b in &renamed.blocks {
            for p in &b.params {
                assert!(p.0 >= 1, "renamed param {} should be >= 1", p.0);
            }
            for s in &b.stmts {
                let Stmt::Let(v, _) = s;
                assert!(v.0 >= 1, "renamed let-var {} should be >= 1", v.0);
            }
        }
        // block shift: caller max_block = 0, so callee block 0 → 1
        assert_eq!(renamed.entry.0, 1);
    }

    #[test]
    fn alpha_rename_no_var_collision_with_caller() {
        let callee = make_leaf_add1();
        let caller = make_caller_tail(FnId(1));
        let renamed = alpha_rename(&callee, &caller);

        let caller_vars: std::collections::HashSet<u32> = caller
            .blocks
            .iter()
            .flat_map(|b| b.params.iter().map(|v| v.0))
            .collect();
        for b in &renamed.blocks {
            for p in &b.params {
                assert!(!caller_vars.contains(&p.0));
            }
        }
    }

    #[test]
    fn alpha_rename_prim_binop_vars_shifted() {
        let callee = make_leaf_add1(); // entry block has BinOp(Add, v0, v1)
        let caller = make_caller_tail(FnId(1)); // max_var = 0 → shift = 1
        let renamed = alpha_rename(&callee, &caller);

        let entry = renamed
            .blocks
            .iter()
            .find(|b| b.id == renamed.entry)
            .unwrap();
        // stmts[1] should be BinOp(Add, v1, v2) after shift-by-1 from v0,v1
        match &entry.stmts[1] {
            Stmt::Let(_, Prim::BinOp(BinOp::Add, a, b)) => {
                assert_eq!(a.0, 1);
                assert_eq!(b.0, 2);
            }
            other => panic!("expected shifted BinOp, got {:?}", other),
        }
    }

    #[test]
    fn alpha_rename_make_list_tail_var_shifted() {
        let mut b = FnBuilder::new(FnId(1), "lst");
        let x = b.fresh_var(); // v0
        let t = b.fresh_var(); // v1
        let entry = b.block(vec![x, t]);
        let _l = b.let_(entry, Prim::MakeList(vec![x], Some(t)));
        b.set_terminator(entry, Term::Return(x));
        let callee = b.build();

        let caller = make_caller_tail(FnId(1)); // max_var = 0 → shift = 1
        let renamed = alpha_rename(&callee, &caller);
        let eb = renamed
            .blocks
            .iter()
            .find(|b| b.id == renamed.entry)
            .unwrap();
        match &eb.stmts[0] {
            Stmt::Let(_, Prim::MakeList(els, Some(tail))) => {
                assert_eq!(els[0].0, 1);
                assert_eq!(tail.0, 2);
            }
            other => panic!("expected MakeList with tail, got {:?}", other),
        }
    }

    // --- absorb_callee ---

    #[test]
    fn absorb_callee_no_goto_no_params() {
        // After absorb: the call-site block must NOT end with a Goto that still
        // carries args (the old splice_blocks + Goto artifact).
        let callee = make_leaf_add1(); // entry has 1 param `x`
        let caller = make_caller_tail(FnId(1));
        let renamed = alpha_rename(&callee, &caller);

        // The arg that was heading to the TailCall — pick caller's entry param.
        let caller_entry = caller.blocks.iter().find(|b| b.id == caller.entry).unwrap();
        let y = caller_entry.params[0];

        let mut caller_mut = caller;
        // bi=0: the entry block index (only one block in caller)
        absorb_callee(&mut caller_mut, 0, renamed, &[y]);

        // The entry block must NOT be a Goto with args.
        let entry = caller_mut
            .blocks
            .iter()
            .find(|b| b.id == caller_mut.entry)
            .unwrap();
        if let Term::Goto(_, args) = &entry.terminator {
            assert!(
                args.is_empty(),
                "absorb_callee must not leave a parameterized Goto; got args={args:?}"
            );
        }

        // The entry block must have no params (callee entry params were consumed).
        // (Caller's own params are on the block, but callee's were substituted away.)
        // The callee add1 had stmts: let one=1, let s=x+one; check they were absorbed.
        assert!(
            entry.stmts.len() >= 2,
            "callee stmts must be absorbed into caller entry; got {}",
            entry.stmts.len()
        );
    }

    // --- inline_tail_calls_once ---

    #[test]
    fn inline_tail_calls_absorbs_callee_no_goto() {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(FnId(1)));
        mb.add_fn(make_leaf_add1());
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 1);

        // absorb_callee: entry block must NOT be a Goto with args.
        // The callee (add1) had 2 stmts; they must be present in the caller entry.
        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        let entry = caller.blocks.iter().find(|b| b.id == caller.entry).unwrap();
        assert!(
            !matches!(&entry.terminator, Term::Goto(_, args) if !args.is_empty()),
            "must not leave a parameterized Goto after absorb"
        );
        assert!(
            entry.stmts.len() >= 2,
            "callee stmts must be absorbed into entry; got {}",
            entry.stmts.len()
        );
    }

    /// fz-ul4.43.D.0 — pure-tail-caller callee merges through inliner.
    /// Shape: `caller(y) -> TailCall(K, [y])`; `K(x) -> let v = x+1;
    /// TailCall(target, [v])`. After inline: caller block ends in
    /// `TailCall(target, [y+1])` — one tail-call instead of two.
    #[test]
    fn inline_tail_calls_absorbs_pure_tail_caller() {
        let target = FnId(2);
        // K: pure-tail-caller
        let mut b = FnBuilder::new(FnId(1), "k");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let one = b.let_(entry, Prim::Const(Const::Int(1)));
        let v = b.let_(entry, Prim::BinOp(BinOp::Add, x, one));
        b.set_terminator(
            entry,
            Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: target,
                args: vec![v],
                is_back_edge: false,
            },
        );
        let k = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(FnId(1)));
        mb.add_fn(k);
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 1, "pure-tail-caller must be inlined");

        // Caller's terminator should now be a TailCall to `target`, not to K.
        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        let entry_b = caller.blocks.iter().find(|b| b.id == caller.entry).unwrap();
        match &entry_b.terminator {
            Term::TailCall { callee, .. } => {
                assert_eq!(*callee, target, "must tail-call through to target");
            }
            other => panic!("expected TailCall(target), got {:?}", other),
        }
        // K's stmts (the +1 computation) must be spliced into the caller block.
        assert!(
            entry_b.stmts.len() >= 2,
            "K's stmts must be absorbed; got {}",
            entry_b.stmts.len()
        );
    }

    fn assert_no_tail_call_to(m: &Module, callee_id: FnId) {
        let has_tail_call = m.fns.iter().any(|f| {
            f.blocks.iter().any(
                |b| matches!(&b.terminator, Term::TailCall { callee, .. } if *callee == callee_id),
            )
        });
        assert!(
            !has_tail_call,
            "expected no TailCall to {:?} after inlining",
            callee_id
        );
    }

    #[test]
    fn inline_tail_calls_absorbs_one_arm_wildcard_matcher() {
        let matcher_id = FnId(10);
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(matcher_id));
        mb.add_fn(make_wildcard_matcher(FnId(20)));
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 1, "wildcard matcher should inline at tail site");
        assert_no_tail_call_to(&m, matcher_id);
    }

    #[test]
    fn inline_tail_calls_absorbs_two_arm_bool_matcher() {
        let matcher_id = FnId(10);
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(matcher_id));
        mb.add_fn(make_bool_matcher(FnId(20), FnId(21)));
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 1, "bool matcher should inline at tail site");
        assert_no_tail_call_to(&m, matcher_id);

        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        assert!(
            caller
                .blocks
                .iter()
                .any(|b| matches!(b.terminator, Term::If { .. })),
            "inlined caller should contain the matcher branch"
        );
    }

    #[test]
    fn inline_tail_calls_absorbs_three_arm_tuple_matcher() {
        let matcher_id = FnId(10);
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(matcher_id));
        mb.add_fn(make_tuple_matcher(FnId(20), FnId(21), FnId(22)));
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 1, "tuple matcher should inline at tail site");
        assert_no_tail_call_to(&m, matcher_id);

        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        let branch_count = caller
            .blocks
            .iter()
            .filter(|b| matches!(b.terminator, Term::If { .. }))
            .count();
        assert_eq!(branch_count, 2, "three-arm tuple matcher keeps both tests");
    }

    #[test]
    fn inline_tail_calls_skips_large_matcher_router() {
        let matcher_id = FnId(10);
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(matcher_id));
        mb.add_fn(make_large_matcher(FnId(20), FnId(21), 6));
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 0, "large matcher should stay out of the caller");

        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        assert!(
            caller.blocks.iter().any(
                |b| matches!(&b.terminator, Term::TailCall { callee, .. } if *callee == matcher_id)
            ),
            "caller should retain its TailCall to the large matcher"
        );
    }

    #[test]
    fn inline_module_does_not_inline_leaf_body_into_matcher_before_matcher_inline() {
        let matcher_id = FnId(10);
        let leaf_id = FnId(20);
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(matcher_id));
        mb.add_fn(make_wildcard_matcher(leaf_id));
        let mut leaf = FnBuilder::new(leaf_id, "leaf_body");
        let x = leaf.fresh_var();
        let entry = leaf.block(vec![x]);
        let mut result = x;
        for _ in 0..INLINE_BUDGET {
            let one = leaf.let_(entry, Prim::Const(Const::Int(1)));
            result = leaf.let_(entry, Prim::BinOp(BinOp::Add, result, one));
        }
        leaf.set_terminator(entry, Term::Return(result));
        mb.add_fn(leaf.build());
        let mut m = mb.build();

        let n = inline_module(&mut m);
        assert_eq!(n, 1, "only the matcher shell should inline");

        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        assert!(
            caller.blocks.iter().any(
                |b| matches!(&b.terminator, Term::TailCall { callee, .. } if *callee == leaf_id)
            ),
            "caller should branch through the inlined matcher shell and still tail-call the leaf"
        );
        assert!(
            !caller
                .blocks
                .iter()
                .flat_map(|b| &b.stmts)
                .any(|s| matches!(s, Stmt::Let(_, Prim::BinOp(BinOp::Add, _, _)))),
            "leaf arithmetic must not be cloned through the matcher decision point"
        );
    }

    #[test]
    fn inline_tail_calls_skips_non_inlinable() {
        // Make add1 exceed the budget by adding 9 stmts.
        let mut b = FnBuilder::new(FnId(1), "big");
        let x = b.fresh_var();
        let entry = b.block(vec![x]);
        let mut v = x;
        for _ in 0..9 {
            v = b.let_(entry, Prim::BinOp(BinOp::Add, v, x));
        }
        b.set_terminator(entry, Term::Return(v));
        let big = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(FnId(1)));
        mb.add_fn(big);
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 0);
    }

    // --- inline_calls_once ---

    #[test]
    fn inline_calls_rewrites_return_to_tail_call_k() {
        let k = FnId(99);
        let mut b = FnBuilder::new(FnId(0), "caller");
        let y = b.fresh_var();
        let entry = b.block(vec![y]);
        b.set_terminator(
            entry,
            Term::Call {
                ident: crate::fz_ir::CallsiteIdent::synthetic(),
                callee: FnId(1),
                args: vec![y],
                continuation: Cont {
                    fn_id: k,
                    captured: vec![],
                },
            },
        );
        let caller_fn = b.build();

        let mut mb = ModuleBuilder::new();
        mb.add_fn(caller_fn);
        mb.add_fn(make_leaf_add1());
        let mut m = mb.build();

        let n = inline_calls_once(&mut m);
        assert_eq!(n, 1);

        // There should now be a block with TailCall(K, [...]) terminator.
        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        let has_tail_k = caller
            .blocks
            .iter()
            .any(|b| matches!(&b.terminator, Term::TailCall { callee, .. } if *callee == k));
        assert!(has_tail_k, "expected TailCall(K=99) after inlining");
    }

    // --- inline_module ---

    #[test]
    fn inline_module_returns_nonzero_for_inlinable() {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(FnId(1)));
        mb.add_fn(make_leaf_add1());
        let mut m = mb.build();
        assert!(inline_module(&mut m) > 0);
    }

    #[test]
    fn inline_module_is_idempotent_after_saturation() {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(FnId(1)));
        mb.add_fn(make_leaf_add1());
        let mut m = mb.build();
        inline_module(&mut m);
        // Second run: no new TailCall sites targeting add1 remain.
        assert_eq!(inline_module(&mut m), 0);
    }

    // --- ir_interp parity: semantics preserved across inline ---

    fn lower_src(src: &str) -> crate::fz_ir::Module {
        let toks = crate::lexer::Lexer::new(src).tokenize().unwrap();
        let prog = crate::parser::Parser::new(toks).parse_program().unwrap();
        crate::ir_lower::lower_program(&mut crate::types::ConcreteTypes, &prog).unwrap()
    }

    fn interp(m: &crate::fz_ir::Module) -> i64 {
        crate::ir_interp::run_main(&crate::telemetry::NullTelemetry, m).expect("interp failed")
    }

    fn parity(src: &str) {
        let orig = lower_src(src);
        let expected = interp(&orig);

        let mut inlined = orig.clone();
        inline_module(&mut inlined);
        let got = interp(&inlined);

        assert_eq!(
            got, expected,
            "interp parity failed for:\n{}\nexpected {}, got {}",
            src, expected, got
        );
    }

    #[test]
    fn parity_tail_call_inlined() {
        // main tail-calls add1(41) → inlined → same result 42
        parity("fn add1(x), do: x + 1\nfn main(), do: add1(41)");
    }

    #[test]
    fn parity_call_cont_inlined() {
        // double(5) called with continuation → inlined → same result 10
        parity("fn double(x), do: x * 2\nfn main(), do: double(5)");
    }

    #[test]
    fn parity_non_leaf_not_changed() {
        // fact(5) — fact is not a leaf (calls itself); not inlined; same result
        parity(
            "fn fact(0), do: 1\n\
             fn fact(n), do: n * fact(n - 1)\n\
             fn main(), do: fact(5)",
        );
    }

    #[test]
    fn parity_over_budget_not_changed() {
        // chain of 9 adds — exceeds INLINE_BUDGET; not inlined
        parity(
            "fn big(x), do: x + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1\n\
             fn main(), do: big(0)",
        );
    }

    #[test]
    fn parity_chain_inline() {
        // main → inc → double, both leaves → chain inlined → same result
        parity(
            "fn inc(x), do: x + 1\n\
             fn double(x), do: x * 2\n\
             fn main(), do: double(inc(3))",
        );
    }

    #[test]
    fn parity_no_inline_sites() {
        // main just returns a constant — no call sites to inline
        parity("fn main(), do: 42");
    }

    #[test]
    fn parity_count_loop() {
        // Recursive loop with step inlined: loop_(100, 0) == 100
        parity(
            "fn step(x), do: x + 1\n\
             fn loop_(0, acc), do: acc\n\
             fn loop_(n, acc), do: loop_(n - 1, step(acc))\n\
             fn main(), do: loop_(100, 0)",
        );
    }

    #[test]
    fn parity_receive_callee_not_inlined() {
        // A fn that contains Receive is not a leaf and must not be inlined.
        // We can't build a source-level program with Receive that terminates
        // deterministically (needs a mailbox), so test at IR level: verify
        // is_leaf returns false for a fn with Receive (see is_leaf_receive_is_not_leaf
        // above) — which is the guard that prevents inlining.
        // Semantic parity for Receive-containing programs is exercised by the
        // existing scheduler tests (fz-ul4.19.x fixture suite).
    }

    #[test]
    fn tail_call_site_eliminated_after_inline() {
        // Concrete IR proof: after inlining, no TailCall to add1 remains.
        let src = "fn add1(x), do: x + 1\nfn main(), do: add1(41)";
        let orig = lower_src(src);
        let add1_id = orig.fn_by_name("add1").unwrap().id;

        let mut inlined = orig.clone();
        inline_module(&mut inlined);

        let has_tail_call_to_add1 = inlined.fns.iter().any(|f| {
            f.blocks.iter().any(
                |b| matches!(&b.terminator, Term::TailCall { callee, .. } if *callee == add1_id),
            )
        });
        assert!(
            !has_tail_call_to_add1,
            "expected no TailCall to add1 after inlining, but one remains"
        );
    }

    #[test]
    fn call_site_eliminated_after_inline() {
        // After inlining double into its only Call site, no Call to double remains.
        let src = "fn double(x), do: x * 2\nfn main(), do: double(5)";
        let orig = lower_src(src);
        let double_id = orig.fn_by_name("double").unwrap().id;

        let mut inlined = orig.clone();
        inline_module(&mut inlined);

        let has_call_to_double = inlined.fns.iter().any(|f| {
            f.blocks
                .iter()
                .any(|b| matches!(&b.terminator, Term::Call { callee, .. } if *callee == double_id))
        });
        assert!(
            !has_call_to_double,
            "expected no Call to double after inlining, but one remains"
        );
    }

    // GC root invariant: no test-accessible GC trigger exists in the current
    // runtime (fz-ul4.11 is the Tracing GC epic; the trigger hook is part of
    // that work). The semantic correctness guarantee — that inlined values are
    // visible and correct — is covered by the parity tests above, which run
    // all computations through the interpreter. The JIT-level GC stress test
    // is deferred to fz-ul4.11 as documented there.

    // ----- fz-efb — inliner gate for fz-duq's tightness claim -----

    /// fz-efb — fz-duq's lowering wraps each if/case/cond/with arm in a
    /// per-arm continuation fn so arm-internal CPS-splits stay confined.
    /// The "tightness" claim rests on the inliner collapsing tiny one-call
    /// continuations back into their callers — otherwise the IR (and
    /// golden CLIF) bloats. This test gates that property: for a simple
    /// `if` with leaf arms, after `inline_module` + `dce_module_level`,
    /// no `if_*` cont fns should survive in the module.
    ///
    /// If this test fails, it's evidence that the inliner can't collapse
    /// the fz-duq cont-fn shape for some reason — investigate before
    /// blessing any drifted goldens on real fixtures.
    #[test]
    fn fz_efb_leaf_arm_if_collapses_to_single_fn() {
        // Single source-level fn `pos` with a tail-position if whose arms
        // are pure literals (no calls, no Receive). fz-duq.2 mints
        // `if_then`/`if_else` cont fns for both arms; the inliner should
        // inline them back into pos and DCE should remove the now-dead
        // fns.
        let src = "fn pos(x), do: if x > 0, do: 1, else: -1\n\
                   fn main(), do: dbg(pos(5))";
        let mut m = lower_src(src);
        crate::ir_inline::inline_module(&mut m);
        crate::ir_dce::dce_module_level(&mut m);

        let leftover: Vec<&str> = m
            .fns
            .iter()
            .map(|f| f.name.as_str())
            .filter(|n| {
                n.starts_with("if_then") || n.starts_with("if_else") || n.starts_with("if_join")
            })
            .collect();

        assert!(
            leftover.is_empty(),
            "expected fz-duq per-arm cont fns to be inlined+DCE'd away for leaf-arm if; \
             found leftover: {:?}",
            leftover,
        );
    }
}
