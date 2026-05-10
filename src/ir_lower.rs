//! AST -> fz-IR translator (core).
//!
//! Scope (per fz-ul4.11.16):
//! - Expr: literals, Var, BinOp, UnOp, Block, If, Match, List, Tuple, Call,
//!   Lambda. Multi-clause fn dispatch.
//! - Patterns: Wildcard, Var, literals, Tuple, List, As.
//! - Out of scope (returns LowerError::Unsupported): Case, Cond, With, Map,
//!   MapUpdate, Index, Bitstring expr/pattern, VecLit, Map patterns, Quote/
//!   Unquote at IR translation. These land in fz-ul4.11.17.
//!
//! CPS-split: every non-tail Call closes the current fn with Term::Call and
//! starts a fresh continuation FnIr. The continuation's entry block params
//! are [result_var, ...captured_vars]. Captured = all in-scope locals at the
//! call site (conservative; .11.6 liveness narrows later). Tail-position
//! calls use Term::TailCall.

#![allow(dead_code)]

use crate::ast::{BinOp as AstBinOp, Expr, FnDef, Item, Pattern, Program, UnOp as AstUnOp};
use crate::fz_ir::{
    BinOp, BlockId, BuiltinId, Const, Cont, FnBuilder, FnId, Module, ModuleBuilder, Prim, Term,
    UnOp, Var,
};
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq)]
pub enum LowerError {
    Unsupported(String),
    Unbound(String),
    ArityMismatch { name: String, expected: usize, got: usize },
    PostExpansionNode(String),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::Unsupported(s) => write!(f, "unsupported: {}", s),
            LowerError::Unbound(n) => write!(f, "unbound: {}", n),
            LowerError::ArityMismatch { name, expected, got } => {
                write!(f, "arity mismatch for {}: expected {}, got {}", name, expected, got)
            }
            LowerError::PostExpansionNode(s) => write!(f, "post-expansion node leaked: {}", s),
        }
    }
}

/// Atom interner: maps atom names to stable u32 ids.
#[derive(Default)]
pub struct AtomTable {
    map: HashMap<String, u32>,
}

impl AtomTable {
    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.map.get(name) {
            return id;
        }
        let id = self.map.len() as u32;
        self.map.insert(name.to_string(), id);
        id
    }

    /// Return atom names in id order: id N -> names[N].
    pub fn names(&self) -> Vec<String> {
        let mut out = vec![String::new(); self.map.len()];
        for (k, &id) in &self.map {
            out[id as usize] = k.clone();
        }
        out
    }
}

/// Builtin registry. Stable ids 0..N seeded for the v1 set.
pub struct BuiltinTable {
    map: HashMap<String, BuiltinId>,
}

impl BuiltinTable {
    pub fn new() -> Self {
        let mut t = Self { map: HashMap::new() };
        for name in ["print", "assert", "assert_eq", "assert_neq"] {
            let id = BuiltinId(t.map.len() as u32);
            t.map.insert(name.into(), id);
        }
        t
    }
    pub fn lookup(&self, name: &str) -> Option<BuiltinId> {
        self.map.get(name).copied()
    }
}

impl Default for BuiltinTable {
    fn default() -> Self {
        Self::new()
    }
}

/// Map of source-fn name -> primary FnId (the entry IR fn for a multi-clause source fn).
type FnMap = HashMap<(String, usize), FnId>;

pub struct LowerCtx {
    pub atoms: AtomTable,
    pub builtins: BuiltinTable,
    pub mb: ModuleBuilder,
    pub fns: FnMap,
    /// Currently-being-built fn.
    cur: Option<FnBuilder>,
    /// Currently-active block within `cur`.
    cur_block: Option<BlockId>,
    /// Locals env: source name -> IR Var.
    env: HashMap<String, Var>,
    /// Order of names in env (for stable captured-list building).
    env_order: Vec<String>,
    /// True after an expression sets a terminator on the current block
    /// itself (TailCall, etc.). Caller should NOT overwrite with Return.
    terminated: bool,
    next_temp: u32,
}

impl LowerCtx {
    pub fn new() -> Self {
        Self {
            atoms: AtomTable::default(),
            builtins: BuiltinTable::new(),
            mb: ModuleBuilder::new(),
            fns: HashMap::new(),
            cur: None,
            cur_block: None,
            env: HashMap::new(),
            env_order: Vec::new(),
            terminated: false,
            next_temp: 0,
        }
    }

    /// Park a temporary in env under a fresh "_tN" name so it survives any
    /// CPS-split triggered by subsequent lowering. After the split, look it
    /// up by the same name to get its rebound continuation-local Var.
    fn park(&mut self, v: Var) -> String {
        let name = format!("_t{}", self.next_temp);
        self.next_temp += 1;
        self.bind(&name, v);
        name
    }

    fn unpark(&self, name: &str) -> Var {
        self.env.get(name).copied().expect("unpark: missing temp")
    }

    fn unbind(&mut self, name: &str) {
        self.env.remove(name);
        if let Some(i) = self.env_order.iter().position(|n| n == name) {
            self.env_order.remove(i);
        }
    }

    fn bind(&mut self, name: &str, v: Var) {
        if !self.env.contains_key(name) {
            self.env_order.push(name.to_string());
        }
        self.env.insert(name.to_string(), v);
    }

    fn lookup(&self, name: &str) -> Option<Var> {
        self.env.get(name).copied()
    }

    fn captured_snapshot(&self) -> Vec<(String, Var)> {
        let mut out = Vec::with_capacity(self.env_order.len());
        for n in &self.env_order {
            if let Some(v) = self.env.get(n) {
                out.push((n.clone(), *v));
            }
        }
        out
    }

    fn cur_mut(&mut self) -> &mut FnBuilder {
        self.cur.as_mut().expect("no current fn")
    }

    fn cur_block(&self) -> BlockId {
        self.cur_block.expect("no current block")
    }

    fn let_(&mut self, prim: Prim) -> Var {
        let blk = self.cur_block();
        self.cur_mut().let_(blk, prim)
    }

    fn set_term(&mut self, term: Term) {
        let blk = self.cur_block();
        self.cur_mut().set_terminator(blk, term);
    }
}

impl Default for LowerCtx {
    fn default() -> Self {
        Self::new()
    }
}

pub fn lower_program(prog: &Program) -> Result<Module, LowerError> {
    let mut ctx = LowerCtx::new();

    // First pass: assign FnIds to every top-level FnDef.
    for item in &prog.items {
        match item.as_ref() {
            Item::Fn(fn_def) => {
                let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
                let id = ctx.mb.fresh_fn_id();
                ctx.fns.insert((fn_def.name.clone(), arity), id);
            }
            Item::Module(_) => {
                return Err(LowerError::Unsupported(
                    "Item::Module should be flattened by resolve before lowering".into(),
                ));
            }
            Item::Alias { .. } | Item::Import { .. } => {
                return Err(LowerError::Unsupported(
                    "alias/import should be consumed by resolve before lowering".into(),
                ));
            }
            Item::MacroCall { name, .. } => {
                return Err(LowerError::PostExpansionNode(format!("MacroCall({})", name)));
            }
        }
    }

    // Second pass: lower each fn.
    for item in &prog.items {
        if let Item::Fn(fn_def) = item.as_ref() {
            lower_fn(&mut ctx, fn_def)?;
        }
    }

    Ok(ctx.mb.build())
}

fn lower_fn(ctx: &mut LowerCtx, fn_def: &FnDef) -> Result<(), LowerError> {
    if fn_def.is_macro {
        // Macros are consumed by expansion before lowering.
        return Ok(());
    }
    let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
    let fn_id = *ctx
        .fns
        .get(&(fn_def.name.clone(), arity))
        .ok_or_else(|| LowerError::Unbound(format!("fn {}/{}", fn_def.name, arity)))?;

    let mut builder = FnBuilder::new(fn_id, fn_def.name.clone());
    // Mint param vars for the entry block.
    let param_vars: Vec<Var> = (0..arity).map(|_| builder.fresh_var()).collect();
    let entry = builder.block(param_vars.clone());
    ctx.cur = Some(builder);
    ctx.cur_block = Some(entry);
    ctx.env.clear();
    ctx.env_order.clear();

    ctx.terminated = false;
    if fn_def.clauses.len() == 1 {
        let clause = &fn_def.clauses[0];
        // Bind params via patterns; on fail, halt with :match_error.
        // Seal fail_block FIRST so CPS-split during body lowering can't orphan it.
        let fail_block = ctx.cur_mut().block(vec![]);
        ctx.cur_block = Some(fail_block);
        let me = ctx.atoms.intern("match_error");
        let mev = ctx.let_(Prim::Const(Const::Atom(me)));
        ctx.set_term(Term::Halt(mev));
        ctx.cur_block = Some(entry);

        for (pv, pat) in param_vars.iter().zip(&clause.params) {
            lower_pattern_bind(ctx, *pv, pat, fail_block)?;
        }
        if let Some(_g) = &clause.guard {
            return Err(LowerError::Unsupported("guards (deferred)".into()));
        }
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
        }
    } else {
        lower_multi_clause(ctx, fn_def, &param_vars, entry)?;
    }

    let built = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(built);
    ctx.cur_block = None;
    Ok(())
}

fn lower_multi_clause(
    ctx: &mut LowerCtx,
    fn_def: &FnDef,
    param_vars: &[Var],
    entry: BlockId,
) -> Result<(), LowerError> {
    // Plan: entry already exists, current_block points to it.
    // For each clause, allocate a "try" block (no params; relies on params being
    // available via Var ids that are stable within this FnIr). Entry Goto's
    // first try block. Each try block tests its patterns; on success, runs the
    // body and returns; on fail, Goto's the next try block (or fail block).

    // Allocate try blocks up front so terminators can reference them.
    let try_blocks: Vec<BlockId> = (0..fn_def.clauses.len())
        .map(|_| ctx.cur_mut().block(vec![]))
        .collect();
    let fail_block = ctx.cur_mut().block(vec![]);

    // Seal fail_block FIRST so CPS-split during clause body lowering can't orphan it.
    ctx.cur_block = Some(fail_block);
    let fc = ctx.atoms.intern("function_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(fc)));
    ctx.set_term(Term::Halt(v));

    // Entry -> first try block.
    ctx.cur_mut().set_terminator(entry, Term::Goto(try_blocks[0], vec![]));

    for (i, clause) in fn_def.clauses.iter().enumerate() {
        if let Some(_g) = &clause.guard {
            return Err(LowerError::Unsupported("guards (deferred)".into()));
        }
        let next = try_blocks.get(i + 1).copied().unwrap_or(fail_block);
        ctx.cur_block = Some(try_blocks[i]);
        ctx.env.clear();
        ctx.env_order.clear();
        ctx.terminated = false;
        for (pv, pat) in param_vars.iter().zip(&clause.params) {
            lower_pattern_bind(ctx, *pv, pat, next)?;
        }
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
        }
    }

    Ok(())
}

fn lower_expr(ctx: &mut LowerCtx, e: &Expr, is_tail: bool) -> Result<Var, LowerError> {
    match e {
        Expr::Int(n) => Ok(ctx.let_(Prim::Const(Const::Int(*n)))),
        Expr::Float(x) => Ok(ctx.let_(Prim::Const(Const::Float(*x)))),
        Expr::Str(s) => Ok(ctx.let_(Prim::Const(Const::Str(s.clone())))),
        Expr::Atom(s) => {
            let id = ctx.atoms.intern(s);
            Ok(ctx.let_(Prim::Const(Const::Atom(id))))
        }
        Expr::Bool(true) => Ok(ctx.let_(Prim::Const(Const::True))),
        Expr::Bool(false) => Ok(ctx.let_(Prim::Const(Const::False))),
        Expr::Nil => Ok(ctx.let_(Prim::Const(Const::Nil))),

        Expr::Var(name) => ctx.lookup(name).ok_or_else(|| LowerError::Unbound(name.clone())),

        Expr::BinOp(op, a, b) => {
            let va_raw = lower_expr(ctx, a, false)?;
            let park_a = ctx.park(va_raw);
            let vb = lower_expr(ctx, b, false)?;
            let va = ctx.unpark(&park_a);
            ctx.unbind(&park_a);
            let irop = lower_binop(*op)?;
            Ok(ctx.let_(Prim::BinOp(irop, va, vb)))
        }
        Expr::UnOp(op, x) => {
            let v = lower_expr(ctx, x, false)?;
            let irop = match op {
                AstUnOp::Neg => UnOp::Neg,
                AstUnOp::Not => UnOp::Not,
            };
            Ok(ctx.let_(Prim::UnOp(irop, v)))
        }

        Expr::Block(exprs) => {
            if exprs.is_empty() {
                return Ok(ctx.let_(Prim::Const(Const::Nil)));
            }
            let last = exprs.len() - 1;
            let saved_env = ctx.env.clone();
            let saved_order = ctx.env_order.clone();
            let mut result = Var(0);
            for (i, ex) in exprs.iter().enumerate() {
                let tail = is_tail && i == last;
                result = lower_expr(ctx, ex, tail)?;
            }
            // Block scope ends: restore env so block-bound vars don't leak.
            // (Match expressions inside a block do bind into the surrounding
            // scope per fz semantics, so we keep new bindings in saved scope.
            // Actually: fz match expressions bind to the enclosing scope
            // for the rest of that scope. Simplest semantics: blocks DO
            // propagate bindings outward, so we don't restore.)
            let _ = saved_env;
            let _ = saved_order;
            Ok(result)
        }

        Expr::If(cond, then_e, else_opt) => lower_if(ctx, cond, then_e, else_opt, is_tail),

        Expr::Match(pat, expr) => {
            let v = lower_expr(ctx, expr, false)?;
            // Match-expr in expr position binds vars and evaluates to the
            // matched value; on failure -> halt :match_error.
            let fail_block = ctx.cur_mut().block(vec![]);
            lower_pattern_bind(ctx, v, pat, fail_block)?;
            // After match, control is in current_block; result is the matched value.
            // Set fail block (only reached on dynamic mismatch).
            let saved = ctx.cur_block();
            ctx.cur_block = Some(fail_block);
            let me = ctx.atoms.intern("match_error");
            let mev = ctx.let_(Prim::Const(Const::Atom(me)));
            ctx.set_term(Term::Halt(mev));
            ctx.cur_block = Some(saved);
            Ok(v)
        }

        Expr::List(elems, tail) => {
            let parks = lower_seq(ctx, elems)?;
            let tail_park = if let Some(t) = tail {
                let v = lower_expr(ctx, t, false)?;
                Some(ctx.park(v))
            } else {
                None
            };
            let vs: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            let tail_v = tail_park.as_ref().map(|n| ctx.unpark(n));
            for n in &parks { ctx.unbind(n); }
            if let Some(n) = &tail_park { ctx.unbind(n); }
            Ok(ctx.let_(Prim::MakeList(vs, tail_v)))
        }
        Expr::Tuple(elems) => {
            let parks = lower_seq(ctx, elems)?;
            let vs: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            for n in &parks { ctx.unbind(n); }
            Ok(ctx.let_(Prim::MakeTuple(vs)))
        }

        Expr::Call(target, args) => {
            // Lower arg exprs first; park each so they survive subsequent splits.
            let parks = lower_seq(ctx, args)?;
            let arg_vars: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            for n in &parks { ctx.unbind(n); }
            // Resolve callee.
            let callee_name = match target.as_ref() {
                Expr::Var(n) => n.clone(),
                Expr::Dot(_, _) => {
                    return Err(LowerError::Unsupported(
                        "Expr::Dot should be resolved before lowering".into(),
                    ));
                }
                _ => {
                    return Err(LowerError::Unsupported(
                        "Call target other than Var/Dot (deferred)".into(),
                    ));
                }
            };
            // Builtin?
            if let Some(bid) = ctx.builtins.lookup(&callee_name) {
                return Ok(ctx.let_(Prim::Builtin(bid, arg_vars)));
            }
            let arity = arg_vars.len();
            let callee = *ctx.fns.get(&(callee_name.clone(), arity)).ok_or_else(|| {
                LowerError::Unbound(format!("fn {}/{}", callee_name, arity))
            })?;
            if is_tail {
                ctx.set_term(Term::TailCall { callee, args: arg_vars });
                ctx.terminated = true;
                Ok(Var(0))
            } else {
                cps_split_call(ctx, callee, arg_vars)
            }
        }

        Expr::Lambda(params, body) => lower_lambda(ctx, params, body),

        // Out of scope -> fz-ul4.11.17:
        Expr::Case(_, _) => Err(LowerError::Unsupported("Case (.11.17)".into())),
        Expr::Cond(_) => Err(LowerError::Unsupported("Cond (.11.17)".into())),
        Expr::With(_, _, _) => Err(LowerError::Unsupported("With (.11.17)".into())),
        Expr::Map(_) => Err(LowerError::Unsupported("Map (.11.17)".into())),
        Expr::MapUpdate(_, _) => Err(LowerError::Unsupported("MapUpdate (.11.17)".into())),
        Expr::Index(_, _) => Err(LowerError::Unsupported("Index (.11.17)".into())),
        Expr::Bitstring(_) => Err(LowerError::Unsupported("Bitstring (.11.17)".into())),
        Expr::VecLit(_, _) => Err(LowerError::Unsupported("VecLit (.11.17)".into())),
        Expr::Dot(_, _) => Err(LowerError::Unsupported(
            "Expr::Dot should be resolved before lowering".into(),
        )),
        Expr::Quote(_) => Err(LowerError::PostExpansionNode("Quote".into())),
        Expr::Unquote(_) => Err(LowerError::PostExpansionNode("Unquote".into())),
    }
    // Note: lower_if is implemented as a separate function below to keep the
    // var/block dance clean; the unreachable!() above is replaced via a
    // direct branch into it before this match.
}

fn lower_if(
    ctx: &mut LowerCtx,
    cond: &Expr,
    then_e: &Expr,
    else_opt: &Option<Box<Expr>>,
    is_tail: bool,
) -> Result<Var, LowerError> {
    let cv = lower_expr(ctx, cond, false)?;
    let then_b = ctx.cur_mut().block(vec![]);
    let else_b = ctx.cur_mut().block(vec![]);
    let join_param = ctx.cur_mut().fresh_var();
    let join_b = ctx.cur_mut().block(vec![join_param]);
    ctx.set_term(Term::If(cv, then_b, else_b));

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    ctx.cur_block = Some(then_b);
    let tv = lower_expr(ctx, then_e, is_tail)?;
    ctx.set_term(Term::Goto(join_b, vec![tv]));

    ctx.env = saved_env.clone();
    ctx.env_order = saved_order.clone();
    ctx.cur_block = Some(else_b);
    let ev = if let Some(else_e) = else_opt {
        lower_expr(ctx, else_e, is_tail)?
    } else {
        ctx.let_(Prim::Const(Const::Nil))
    };
    ctx.set_term(Term::Goto(join_b, vec![ev]));

    ctx.env = saved_env;
    ctx.env_order = saved_order;
    ctx.cur_block = Some(join_b);
    Ok(join_param)
}

fn lower_lambda(
    ctx: &mut LowerCtx,
    params: &[Pattern],
    body: &Expr,
) -> Result<Var, LowerError> {
    // Capture all in-scope locals.
    let captured = ctx.captured_snapshot();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();

    // Mint a fresh fn for the lambda.
    let lam_id = ctx.mb.fresh_fn_id();

    // Save current state and switch to building the lambda fn.
    let saved_cur = ctx.cur.take();
    let saved_block = ctx.cur_block.take();
    let saved_env = std::mem::take(&mut ctx.env);
    let saved_order = std::mem::take(&mut ctx.env_order);

    let mut lam_builder = FnBuilder::new(lam_id, format!("lambda_{}", lam_id.0));
    // Entry params = captured + lambda params.
    let cap_params: Vec<Var> = captured.iter().map(|_| lam_builder.fresh_var()).collect();
    let lam_param_vars: Vec<Var> = params.iter().map(|_| lam_builder.fresh_var()).collect();
    let mut entry_params = cap_params.clone();
    entry_params.extend(lam_param_vars.clone());
    let lam_entry = lam_builder.block(entry_params);

    ctx.cur = Some(lam_builder);
    ctx.cur_block = Some(lam_entry);
    // Bind captured + params in env.
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    // Seal fail_block FIRST so CPS-split during body lowering can't orphan it.
    let fail_block = ctx.cur_mut().block(vec![]);
    ctx.cur_block = Some(fail_block);
    let me = ctx.atoms.intern("match_error");
    let mev = ctx.let_(Prim::Const(Const::Atom(me)));
    ctx.set_term(Term::Halt(mev));
    ctx.cur_block = Some(lam_entry);

    ctx.terminated = false;
    for (pv, pat) in lam_param_vars.iter().zip(params) {
        lower_pattern_bind(ctx, *pv, pat, fail_block)?;
    }
    let result = lower_expr(ctx, body, true)?;
    if !ctx.terminated {
        ctx.set_term(Term::Return(result));
    }

    let lam_fn = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(lam_fn);

    // Restore caller state.
    ctx.cur = saved_cur;
    ctx.cur_block = saved_block;
    ctx.env = saved_env;
    ctx.env_order = saved_order;

    Ok(ctx.let_(Prim::MakeClosure(lam_id, captured_vars)))
}

fn cps_split_call(
    ctx: &mut LowerCtx,
    callee: FnId,
    arg_vars: Vec<Var>,
) -> Result<Var, LowerError> {
    let captured = ctx.captured_snapshot();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();
    let cont_id = ctx.mb.fresh_fn_id();

    // Terminate current block with the call.
    ctx.set_term(Term::Call {
        callee,
        args: arg_vars,
        continuation: Cont { fn_id: cont_id, captured: captured_vars.clone() },
    });

    // Finalize current fn.
    let done = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(done);

    // Start the continuation fn.
    let mut kbuilder = FnBuilder::new(cont_id, format!("k_{}", cont_id.0));
    let result_param = kbuilder.fresh_var();
    let cap_params: Vec<Var> = captured.iter().map(|_| kbuilder.fresh_var()).collect();
    let mut params = vec![result_param];
    params.extend(cap_params.clone());
    let entry = kbuilder.block(params);
    ctx.cur = Some(kbuilder);
    ctx.cur_block = Some(entry);

    // Rebind env: each captured name -> its new param Var.
    ctx.env.clear();
    ctx.env_order.clear();
    for ((name, _), nv) in captured.iter().zip(&cap_params) {
        ctx.bind(name, *nv);
    }
    Ok(result_param)
}

/// Lower a sequence of subexpressions, parking each result in env so that any
/// CPS-split triggered by a later element rebinds the earlier results into the
/// continuation. Caller unparks/unbinds.
fn lower_seq(ctx: &mut LowerCtx, exprs: &[Expr]) -> Result<Vec<String>, LowerError> {
    let mut parks = Vec::with_capacity(exprs.len());
    for e in exprs {
        let v = lower_expr(ctx, e, false)?;
        parks.push(ctx.park(v));
    }
    Ok(parks)
}

fn lower_binop(op: AstBinOp) -> Result<BinOp, LowerError> {
    Ok(match op {
        AstBinOp::Add => BinOp::Add,
        AstBinOp::Sub => BinOp::Sub,
        AstBinOp::Mul => BinOp::Mul,
        AstBinOp::Div => BinOp::Div,
        AstBinOp::Rem => BinOp::Mod,
        AstBinOp::Eq => BinOp::Eq,
        AstBinOp::Neq => BinOp::Neq,
        AstBinOp::Lt => BinOp::Lt,
        AstBinOp::LtEq => BinOp::Le,
        AstBinOp::Gt => BinOp::Gt,
        AstBinOp::GtEq => BinOp::Ge,
        AstBinOp::And => BinOp::And,
        AstBinOp::Or => BinOp::Or,
        AstBinOp::Pipe => {
            return Err(LowerError::Unsupported(
                "BinOp::Pipe should be desugared before lowering".into(),
            ));
        }
        AstBinOp::Cons => {
            // a | b — handled at construction sites (List with tail).
            return Err(LowerError::Unsupported(
                "BinOp::Cons should be desugared into List with tail".into(),
            ));
        }
    })
}

/// Lower a pattern that matches `subject_var`. On match failure, jump to
/// `fail_block`. After a successful match, the current block is "all matched
/// so far"; `lower_pattern_bind` may split into new blocks via If terminators.
fn lower_pattern_bind(
    ctx: &mut LowerCtx,
    subject: Var,
    pat: &Pattern,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    match pat {
        Pattern::Wildcard => Ok(()),
        Pattern::Var(name) => {
            ctx.bind(name, subject);
            Ok(())
        }
        Pattern::Int(n) => emit_eq_check(ctx, subject, Prim::Const(Const::Int(*n)), fail_block),
        Pattern::Float(x) => emit_eq_check(ctx, subject, Prim::Const(Const::Float(*x)), fail_block),
        Pattern::Str(s) => emit_eq_check(ctx, subject, Prim::Const(Const::Str(s.clone())), fail_block),
        Pattern::Atom(s) => {
            let id = ctx.atoms.intern(s);
            emit_eq_check(ctx, subject, Prim::Const(Const::Atom(id)), fail_block)
        }
        Pattern::Bool(true) => emit_eq_check(ctx, subject, Prim::Const(Const::True), fail_block),
        Pattern::Bool(false) => emit_eq_check(ctx, subject, Prim::Const(Const::False), fail_block),
        Pattern::Nil => emit_eq_check(ctx, subject, Prim::Const(Const::Nil), fail_block),
        Pattern::As(name, inner) => {
            ctx.bind(name, subject);
            lower_pattern_bind(ctx, subject, inner, fail_block)
        }
        Pattern::Tuple(elems) => {
            // Project field i; recurse.
            for (i, elem_pat) in elems.iter().enumerate() {
                let fv = ctx.let_(Prim::TupleField(subject, i as u32));
                lower_pattern_bind(ctx, fv, elem_pat, fail_block)?;
            }
            Ok(())
        }
        Pattern::List(elems, tail) => {
            // Walk: for each elem, check is_nil(cur) is false, take head/tail.
            let mut cur = subject;
            for elem_pat in elems {
                let isnil = ctx.let_(Prim::ListIsNil(cur));
                let cont_b = ctx.cur_mut().block(vec![]);
                ctx.set_term(Term::If(isnil, fail_block, cont_b));
                ctx.cur_block = Some(cont_b);
                let h = ctx.let_(Prim::ListHead(cur));
                let t = ctx.let_(Prim::ListTail(cur));
                lower_pattern_bind(ctx, h, elem_pat, fail_block)?;
                cur = t;
            }
            match tail {
                Some(tail_pat) => lower_pattern_bind(ctx, cur, tail_pat, fail_block),
                None => {
                    // Must end with nil.
                    let isnil = ctx.let_(Prim::ListIsNil(cur));
                    let cont_b = ctx.cur_mut().block(vec![]);
                    ctx.set_term(Term::If(isnil, cont_b, fail_block));
                    ctx.cur_block = Some(cont_b);
                    Ok(())
                }
            }
        }
        Pattern::Map(_) => Err(LowerError::Unsupported("Map pattern (.11.17)".into())),
        Pattern::Bitstring(_) => Err(LowerError::Unsupported("Bitstring pattern (.11.17)".into())),
    }
}

fn emit_eq_check(
    ctx: &mut LowerCtx,
    subject: Var,
    lit: Prim,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let lit_v = ctx.let_(lit);
    let eq_v = ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit_v));
    let cont_b = ctx.cur_mut().block(vec![]);
    ctx.set_term(Term::If(eq_v, cont_b, fail_block));
    ctx.cur_block = Some(cont_b);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp, Expr, FnClause, FnDef, Item, Pattern, Program, UnOp};
    use std::rc::Rc;

    fn fn_def(name: &str, clauses: Vec<FnClause>) -> Rc<Item> {
        Rc::new(Item::Fn(FnDef {
            name: name.into(),
            clauses,
            is_macro: false,
            doc: None,
        }))
    }

    fn cl(params: Vec<Pattern>, body: Expr) -> FnClause {
        FnClause { params, guard: None, body }
    }

    fn lower_one(items: Vec<Rc<Item>>) -> Module {
        let prog = Program { items };
        lower_program(&prog).expect("lower failed")
    }

    #[test]
    fn lower_const_int_returns_in_entry_block() {
        let f = fn_def("f", vec![cl(vec![], Expr::Int(42))]);
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("const(42)"), "{}", s);
        assert!(s.contains("return v"), "{}", s);
    }

    #[test]
    fn lower_var_lookup() {
        // fn id(x), do: x
        let f = fn_def(
            "id",
            vec![cl(vec![Pattern::Var("x".into())], Expr::Var("x".into()))],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("return v0"), "got:\n{}", s);
    }

    #[test]
    fn lower_binop_add() {
        // fn add1(x), do: x + 1
        let f = fn_def(
            "add1",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::BinOp(
                    BinOp::Add,
                    Box::new(Expr::Var("x".into())),
                    Box::new(Expr::Int(1)),
                ),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("const(1)"), "{}", s);
        assert!(s.contains(" + "), "{}", s);
    }

    #[test]
    fn lower_unop_neg() {
        let f = fn_def(
            "neg",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::UnOp(UnOp::Neg, Box::new(Expr::Var("x".into()))),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("- v0"));
    }

    #[test]
    fn lower_tail_call_uses_tail_call() {
        // fn caller(x), do: callee(x)
        // fn callee(y), do: y
        let caller = fn_def(
            "caller",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::Call(
                    Box::new(Expr::Var("callee".into())),
                    vec![Expr::Var("x".into())],
                ),
            )],
        );
        let callee = fn_def(
            "callee",
            vec![cl(vec![Pattern::Var("y".into())], Expr::Var("y".into()))],
        );
        let m = lower_one(vec![caller, callee]);
        let s = format!("{}", m);
        assert!(s.contains("tail_call"), "got:\n{}", s);
    }

    #[test]
    fn lower_nontail_call_splits_into_continuation() {
        // fn caller(x), do: callee(x) + 1
        let caller = fn_def(
            "caller",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::BinOp(
                    BinOp::Add,
                    Box::new(Expr::Call(
                        Box::new(Expr::Var("callee".into())),
                        vec![Expr::Var("x".into())],
                    )),
                    Box::new(Expr::Int(1)),
                ),
            )],
        );
        let callee = fn_def(
            "callee",
            vec![cl(vec![Pattern::Var("y".into())], Expr::Var("y".into()))],
        );
        let m = lower_one(vec![caller, callee]);
        let s = format!("{}", m);
        assert!(s.contains("call fn1"), "expected explicit call, got:\n{}", s);
        assert!(s.contains("cont(fn"), "expected continuation, got:\n{}", s);
        // continuation fn must exist
        assert!(s.contains("k_2") || s.contains("k_3") || s.contains("lambda_") || s.matches("fn ").count() >= 3,
                "expected continuation fn, got:\n{}", s);
    }

    #[test]
    fn lower_if_uses_join_block() {
        // fn pos(x), do: if x > 0, do: 1, else: -1
        let f = fn_def(
            "pos",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::If(
                    Box::new(Expr::BinOp(
                        BinOp::Gt,
                        Box::new(Expr::Var("x".into())),
                        Box::new(Expr::Int(0)),
                    )),
                    Box::new(Expr::Int(1)),
                    Some(Box::new(Expr::UnOp(UnOp::Neg, Box::new(Expr::Int(1))))),
                ),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("if v"), "expected If terminator: {}", s);
        assert!(s.contains("goto bb"), "expected Goto to join: {}", s);
    }

    #[test]
    fn lower_block_evaluates_last_expr() {
        let f = fn_def(
            "b",
            vec![cl(
                vec![],
                Expr::Block(vec![Expr::Int(1), Expr::Int(2), Expr::Int(3)]),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("const(1)"), "{}", s);
        assert!(s.contains("const(2)"), "{}", s);
        assert!(s.contains("const(3)"), "{}", s);
        // Returns the last expression — its var is whichever fresh_var produced const(3).
        assert!(s.contains("return v"), "{}", s);
    }

    #[test]
    fn lower_list_makes_list_prim() {
        let f = fn_def(
            "l",
            vec![cl(vec![], Expr::List(vec![Expr::Int(1), Expr::Int(2)], None))],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("list(["), "{}", s);
        assert!(!s.contains("list([] |"), "no-tail list shouldn't have | sep: {}", s);
    }

    #[test]
    fn lower_list_with_tail() {
        let f = fn_def(
            "l",
            vec![cl(
                vec![Pattern::Var("t".into())],
                Expr::List(vec![Expr::Int(1)], Some(Box::new(Expr::Var("t".into())))),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("] | v0)"), "expected list with v0 (param t) tail: {}", s);
    }

    #[test]
    fn lower_tuple_makes_tuple_prim() {
        let f = fn_def(
            "t",
            vec![cl(vec![], Expr::Tuple(vec![Expr::Int(1), Expr::Atom("ok".into())]))],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("tuple(["), "{}", s);
    }

    #[test]
    fn lower_tuple_pattern_projects_fields() {
        // fn first({a, b}), do: a
        let f = fn_def(
            "first",
            vec![cl(
                vec![Pattern::Tuple(vec![
                    Pattern::Var("a".into()),
                    Pattern::Var("b".into()),
                ])],
                Expr::Var("a".into()),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("tuple_field(v0, 0)"), "got:\n{}", s);
        assert!(s.contains("tuple_field(v0, 1)"), "got:\n{}", s);
    }

    #[test]
    fn lower_match_expr_binds_var() {
        // fn m(p), do: (x = p; x)  — Block of [Match, Var]
        let f = fn_def(
            "m",
            vec![cl(
                vec![Pattern::Var("p".into())],
                Expr::Block(vec![
                    Expr::Match(Pattern::Var("x".into()), Box::new(Expr::Var("p".into()))),
                    Expr::Var("x".into()),
                ]),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("return v0"), "got:\n{}", s);
    }

    #[test]
    fn multi_clause_dispatch_emits_try_blocks() {
        // fn fact(0), do: 1
        // fn fact(n), do: n * fact(n - 1)
        let f = fn_def(
            "fact",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Int(1)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::BinOp(
                        BinOp::Mul,
                        Box::new(Expr::Var("n".into())),
                        Box::new(Expr::Call(
                            Box::new(Expr::Var("fact".into())),
                            vec![Expr::BinOp(
                                BinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            )],
                        )),
                    ),
                ),
            ],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        // Entry Goto's first try block; first try tests == 0; on fail, Goto next try.
        assert!(s.contains("goto bb"), "got:\n{}", s);
        assert!(s.contains("if v"), "expected pattern test If: {}", s);
        // Fail-fallthrough block: halt with an interned atom (rendered as :atom_N).
        assert!(s.contains("halt v"), "expected halt in fail block:\n{}", s);
        assert!(s.contains(":atom_"), "expected interned atom in fail block:\n{}", s);
    }

    #[test]
    fn lower_lambda_creates_separate_fn_and_closure() {
        // fn mk(x), do: fn(y) -> x + y end
        let f = fn_def(
            "mk",
            vec![cl(
                vec![Pattern::Var("x".into())],
                Expr::Lambda(
                    vec![Pattern::Var("y".into())],
                    Box::new(Expr::BinOp(
                        BinOp::Add,
                        Box::new(Expr::Var("x".into())),
                        Box::new(Expr::Var("y".into())),
                    )),
                ),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("closure(fn"), "expected closure prim, got:\n{}", s);
        assert!(s.contains("lambda_"), "expected lambda fn name: {}", s);
        assert_eq!(m.fns.len(), 2);
    }

    #[test]
    fn builtin_call_lowers_to_builtin_prim() {
        let f = fn_def(
            "p",
            vec![cl(
                vec![],
                Expr::Call(
                    Box::new(Expr::Var("print".into())),
                    vec![Expr::Int(1)],
                ),
            )],
        );
        let m = lower_one(vec![f]);
        let s = format!("{}", m);
        assert!(s.contains("builtin#0("), "got:\n{}", s);
    }

    #[test]
    fn unbound_var_returns_lower_error() {
        let f = fn_def("f", vec![cl(vec![], Expr::Var("missing".into()))]);
        let prog = Program { items: vec![f] };
        let err = lower_program(&prog).unwrap_err();
        assert!(matches!(err, LowerError::Unbound(_)));
    }

    #[test]
    fn unbound_callee_returns_lower_error() {
        let f = fn_def(
            "f",
            vec![cl(
                vec![],
                Expr::Call(
                    Box::new(Expr::Var("nonesuch".into())),
                    vec![Expr::Int(1)],
                ),
            )],
        );
        let prog = Program { items: vec![f] };
        let err = lower_program(&prog).unwrap_err();
        assert!(matches!(err, LowerError::Unbound(_)));
    }

    #[test]
    fn case_returns_unsupported() {
        let f = fn_def(
            "f",
            vec![cl(
                vec![],
                Expr::Case(Box::new(Expr::Int(1)), vec![]),
            )],
        );
        let prog = Program { items: vec![f] };
        let err = lower_program(&prog).unwrap_err();
        assert!(matches!(err, LowerError::Unsupported(_)));
    }

    #[test]
    fn quote_returns_post_expansion_node() {
        let f = fn_def(
            "f",
            vec![cl(vec![], Expr::Quote(Box::new(Expr::Int(1))))],
        );
        let prog = Program { items: vec![f] };
        let err = lower_program(&prog).unwrap_err();
        assert!(matches!(err, LowerError::PostExpansionNode(_)));
    }
}
