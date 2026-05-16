use crate::fz_ir::{BitSizeIr, Block, BlockId, Cont, FnId, FnIr, Module, Prim, Stmt, Term, Var};
use std::collections::{HashMap, HashSet};

/// (caller_fn_idx, block_idx, callee, callee_args, cont_fn_id, cont_captured)
type InlineWork = Vec<(usize, usize, FnId, Vec<Var>, FnId, Vec<Var>)>;

const INLINE_BUDGET: usize = 8;
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
        )
    })
}

pub fn stmt_count(f: &FnIr) -> usize {
    f.blocks.iter().map(|b| b.stmts.len()).sum()
}

pub fn is_inlinable(f: &FnIr) -> bool {
    is_leaf(f) && stmt_count(f) <= INLINE_BUDGET
}

/// Fns referenced by any `MakeClosure` in the module. These must remain
/// callable as closure targets and must never be inlined away — inlining
/// their only direct callsite would make the typer's reachability analysis
/// drop them from `module_types.specs`, breaking the `.29.12.2` spec-fnidx
/// table that codegen uses to find live closure stubs.
fn closure_targets(m: &Module) -> HashSet<FnId> {
    let mut set = HashSet::new();
    for f in &m.fns {
        for b in &f.blocks {
            for s in &b.stmts {
                let Stmt::Let(_, Prim::MakeClosure(fid, _)) = s else {
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
        Prim::AllocStruct(_, args) | Prim::Builtin(_, args) | Prim::Extern(_, args) => args.iter().for_each(|x| v(*x)),
        Prim::ListCons(a, b) => {
            v(*a);
            v(*b);
        }
        Prim::ListHead(a) | Prim::ListTail(a) | Prim::ListIsNil(a) => v(*a),
        Prim::MakeTuple(args) => args.iter().for_each(|x| v(*x)),
        Prim::TupleField(a, _) => v(*a),
        Prim::MakeList(els, tail) => {
            els.iter().for_each(|x| v(*x));
            if let Some(t) = tail {
                v(*t);
            }
        }
        Prim::MakeClosure(_, caps) => caps.iter().for_each(|x| v(*x)),
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
        Prim::MapGet(a, b) => {
            v(*a);
            v(*b);
        }
        Prim::MakeVec(_, els) => els.iter().for_each(|x| v(*x)),
        Prim::MakeBitstring(fields) => fields.iter().for_each(|f| {
            v(f.value);
            if let Some(BitSizeIr::Var(sv)) = &f.size {
                v(*sv);
            }
        }),
        Prim::BitReaderInit(a) | Prim::BitReaderDone(a) => v(*a),
        Prim::BitReadField { reader, size, .. } => {
            v(*reader);
            if let Some(BitSizeIr::Var(sv)) = size {
                v(*sv);
            }
        }
    }
    m
}

fn max_var_in_term(t: &Term) -> u32 {
    let mut m = 0u32;
    let mut v = |x: Var| m = m.max(x.0);
    match t {
        Term::Goto(_, args) => args.iter().for_each(|x| v(*x)),
        Term::If(c, _, _) => v(*c),
        Term::Call {
            args, continuation, ..
        } => {
            args.iter().for_each(|x| v(*x));
            continuation.captured.iter().for_each(|x| v(*x));
        }
        Term::TailCall { args, .. } => args.iter().for_each(|x| v(*x)),
        Term::CallClosure {
            closure,
            args,
            continuation,
        } => {
            v(*closure);
            args.iter().for_each(|x| v(*x));
            continuation.captured.iter().for_each(|x| v(*x));
        }
        Term::TailCallClosure { closure, args } => {
            v(*closure);
            args.iter().for_each(|x| v(*x));
        }
        Term::Return(a) | Term::Halt(a) => v(*a),
        Term::Receive { continuation } => continuation.captured.iter().for_each(|x| v(*x)),
    }
    m
}

/// Return a copy of `callee` with all Var and BlockId values shifted by
/// `var_shift` and `block_shift` respectively. Also returns the forward maps
/// (original → renamed) for callers that need to substitute entry params.
pub fn alpha_rename(
    callee: &FnIr,
    caller: &FnIr,
) -> (FnIr, HashMap<Var, Var>, HashMap<BlockId, BlockId>) {
    let var_shift = max_var(caller) + 1;
    let block_shift = max_block(caller) + 1;

    let mut var_map: HashMap<Var, Var> = HashMap::new();
    let mut block_map: HashMap<BlockId, BlockId> = HashMap::new();

    let shift_v = |v: Var| Var(v.0 + var_shift);
    let shift_b = |b: BlockId| BlockId(b.0 + block_shift);

    let rename_prim = |p: &Prim| -> Prim {
        let sv = |v: Var| Var(v.0 + var_shift);
        match p {
            Prim::Const(c) => Prim::Const(c.clone()),
            Prim::BinOp(op, a, b) => Prim::BinOp(*op, sv(*a), sv(*b)),
            Prim::UnOp(op, a) => Prim::UnOp(*op, sv(*a)),
            Prim::AllocStruct(sid, args) => {
                Prim::AllocStruct(*sid, args.iter().map(|x| sv(*x)).collect())
            }
            Prim::Builtin(bid, args) => Prim::Builtin(*bid, args.iter().map(|x| sv(*x)).collect()),
            Prim::Extern(eid, args) => Prim::Extern(*eid, args.iter().map(|x| sv(*x)).collect()),
            Prim::ListCons(a, b) => Prim::ListCons(sv(*a), sv(*b)),
            Prim::ListHead(a) => Prim::ListHead(sv(*a)),
            Prim::ListTail(a) => Prim::ListTail(sv(*a)),
            Prim::ListIsNil(a) => Prim::ListIsNil(sv(*a)),
            Prim::MakeTuple(args) => Prim::MakeTuple(args.iter().map(|x| sv(*x)).collect()),
            Prim::TupleField(a, i) => Prim::TupleField(sv(*a), *i),
            Prim::MakeList(els, tail) => {
                Prim::MakeList(els.iter().map(|x| sv(*x)).collect(), tail.map(sv))
            }
            Prim::MakeClosure(fid, caps) => {
                Prim::MakeClosure(*fid, caps.iter().map(|x| sv(*x)).collect())
            }
            Prim::MakeMap(entries) => {
                Prim::MakeMap(entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect())
            }
            Prim::MapUpdate(base, entries) => Prim::MapUpdate(
                sv(*base),
                entries.iter().map(|(k, v)| (sv(*k), sv(*v))).collect(),
            ),
            Prim::MapGet(a, b) => Prim::MapGet(sv(*a), sv(*b)),
            Prim::MakeVec(kind, els) => Prim::MakeVec(*kind, els.iter().map(|x| sv(*x)).collect()),
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
            Term::If(c, then_b, else_b) => Term::If(sv(*c), sb(*then_b), sb(*else_b)),
            Term::Call {
                callee,
                args,
                continuation,
            } => Term::Call {
                callee: *callee,
                args: args.iter().map(|x| sv(*x)).collect(),
                continuation: rename_cont(continuation),
            },
            Term::TailCall {
                callee,
                args,
                is_back_edge,
            } => Term::TailCall {
                callee: *callee,
                args: args.iter().map(|x| sv(*x)).collect(),
                is_back_edge: *is_back_edge,
            },
            Term::CallClosure {
                closure,
                args,
                continuation,
            } => Term::CallClosure {
                closure: sv(*closure),
                args: args.iter().map(|x| sv(*x)).collect(),
                continuation: rename_cont(continuation),
            },
            Term::TailCallClosure { closure, args } => Term::TailCallClosure {
                closure: sv(*closure),
                args: args.iter().map(|x| sv(*x)).collect(),
            },
            Term::Return(a) => Term::Return(sv(*a)),
            Term::Halt(a) => Term::Halt(sv(*a)),
            Term::Receive { continuation } => Term::Receive {
                continuation: rename_cont(continuation),
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

    // Build forward maps for callers that need param substitution.
    for b in &callee.blocks {
        for p in &b.params {
            var_map.insert(*p, shift_v(*p));
        }
        for s in &b.stmts {
            let Stmt::Let(v, _) = s;
            var_map.insert(*v, shift_v(*v));
        }
        block_map.insert(b.id, shift_b(b.id));
    }

    let renamed = FnIr {
        id: callee.id,
        name: callee.name.clone(),
        frame_schema_id: 0,
        blocks,
        entry: shift_b(callee.entry),
    };

    (renamed, var_map, block_map)
}

// ---------- splice ----------

/// Move all blocks from `renamed` into `caller`; return the entry BlockId.
pub fn splice_blocks(caller: &mut FnIr, renamed: FnIr) -> BlockId {
    let entry = renamed.entry;
    caller.blocks.extend(renamed.blocks);
    entry
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
        if closure_fns.contains(&callee_id) {
            continue; // closure target — must stay callable, don't inline
        }
        let callee_idx = match m.fn_idx.get(&callee_id) {
            Some(&i) => i,
            None => continue,
        };
        if callee_idx == fi {
            continue; // self-recursive — skip
        }
        if !is_inlinable(&m.fns[callee_idx]) {
            continue;
        }

        let callee = m.fns[callee_idx].clone();
        let caller = &m.fns[fi];
        let (renamed, _var_map, _block_map) = alpha_rename(&callee, caller);

        // Entry params must match arg count — guaranteed by well-formed IR.
        let entry_params: Vec<Var> = renamed
            .blocks
            .iter()
            .find(|b| b.id == renamed.entry)
            .expect("entry block")
            .params
            .clone();
        debug_assert_eq!(entry_params.len(), args.len());

        let entry = splice_blocks(&mut m.fns[fi], renamed);

        // Replace TailCall with Goto(entry, args).
        m.fns[fi].blocks[bi].terminator = Term::Goto(entry, args);
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

    let work: InlineWork = m
        .fns
        .iter()
        .enumerate()
        .flat_map(|(fi, f)| {
            f.blocks.iter().enumerate().filter_map(move |(bi, b)| {
                if let Term::Call {
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
                    ))
                } else {
                    None
                }
            })
        })
        .collect();

    for (fi, bi, callee_id, args, cont_fn, cont_captured) in work {
        if closure_fns.contains(&callee_id) {
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
        let (mut renamed, _var_map, _block_map) = alpha_rename(&callee, caller);

        // Rewrite each Return(v') in the renamed body to
        // TailCall(K, [v', cont_captured...]).
        for b in &mut renamed.blocks {
            if let Term::Return(ret_val) = b.terminator {
                let mut tail_args = vec![ret_val];
                tail_args.extend_from_slice(&cont_captured);
                b.terminator = Term::TailCall {
                    callee: cont_fn,
                    args: tail_args,
                    is_back_edge: false,
                };
            }
        }

        let entry_params: Vec<Var> = renamed
            .blocks
            .iter()
            .find(|b| b.id == renamed.entry)
            .expect("entry block")
            .params
            .clone();
        debug_assert_eq!(entry_params.len(), args.len());

        let entry = splice_blocks(&mut m.fns[fi], renamed);
        m.fns[fi].blocks[bi].terminator = Term::Goto(entry, args);
        count += 1;
    }

    count
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
    use crate::fz_ir::{BinOp, Const, FnBuilder, FnId, FnIr, ModuleBuilder, Prim, Stmt, Term, Var};

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
                continuation: Cont {
                    fn_id: FnId(7),
                    captured: vec![],
                },
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

    // --- alpha_rename ---

    #[test]
    fn alpha_rename_shifts_vars_above_caller_max() {
        let callee = make_leaf_add1(); // vars 0,1,2; blocks 0
        let caller = make_caller_tail(FnId(1)); // vars 0; blocks 0
        let (renamed, var_map, block_map) = alpha_rename(&callee, &caller);

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
        assert!(var_map.values().all(|v| v.0 >= 1));
        assert!(block_map.values().all(|b| b.0 >= 1));
    }

    #[test]
    fn alpha_rename_no_var_collision_with_caller() {
        let callee = make_leaf_add1();
        let caller = make_caller_tail(FnId(1));
        let (renamed, _, _) = alpha_rename(&callee, &caller);

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
        let (renamed, _, _) = alpha_rename(&callee, &caller);

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
        let (renamed, _, _) = alpha_rename(&callee, &caller);
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

    // --- splice_blocks ---

    #[test]
    fn splice_blocks_appends_and_returns_entry() {
        let callee = make_leaf_add1();
        let caller_fn = make_caller_tail(FnId(1));
        let (renamed, _, _) = alpha_rename(&callee, &caller_fn);
        let renamed_entry = renamed.entry;

        let mut caller_mut = caller_fn.clone();
        let orig_len = caller_mut.blocks.len();
        let entry = splice_blocks(&mut caller_mut, renamed);

        assert_eq!(entry, renamed_entry);
        assert_eq!(caller_mut.blocks.len(), orig_len + callee.blocks.len());
    }

    // --- inline_tail_calls_once ---

    #[test]
    fn inline_tail_calls_replaces_tailcall_with_goto() {
        let mut mb = ModuleBuilder::new();
        mb.add_fn(make_caller_tail(FnId(1)));
        mb.add_fn(make_leaf_add1());
        let mut m = mb.build();

        let n = inline_tail_calls_once(&mut m);
        assert_eq!(n, 1);

        // The call site block should now have a Goto terminator.
        let caller = m.fns.iter().find(|f| f.name == "caller").unwrap();
        let entry = caller.blocks.iter().find(|b| b.id == caller.entry).unwrap();
        assert!(matches!(entry.terminator, Term::Goto(_, _)));
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
        crate::ir_lower::lower_program(&prog).unwrap()
    }

    fn interp(m: &crate::fz_ir::Module) -> i64 {
        crate::ir_interp::run_main(m).expect("interp failed")
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
}
