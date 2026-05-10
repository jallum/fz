//! fz-ul4.12.1 — typed-AST → Cranelift IR for the in-scope subset.
//!
//! Scope: scalars (int/float/bool/atom/nil) and tuples-of-scalars; arithmetic,
//! comparisons, boolean ops, if/case on scalar+tuple patterns, direct calls,
//! single-clause functions only. Multi-clause + guards + TCO are .12.5;
//! drivers (JIT/AOT) are .12.3 / .12.4; runtime ABI is .12.2.
//!
//! Tuples are flattened to multiple Cranelift SSA values at every level
//! (params, returns, locals, branch joins) — no heap, no stack slots.
//! This works because tuple shapes are statically known in the in-scope
//! subset, and Cranelift functions support multiple return values natively.
//!
//! This ticket exposes a pure lowering API; tests provide LowerTy annotations
//! directly. .12.3 will plumb the typer's inferred types in.

use crate::ast::*;
use cranelift_codegen::ir::condcodes::{FloatCC, IntCC};
use cranelift_codegen::ir::types as clt;
use cranelift_codegen::ir::{
    AbiParam, BlockArg, Function, InstBuilder, Signature, UserFuncName, Value,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings;
use cranelift_codegen::verifier::verify_function;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use std::collections::HashMap;

fn vals_to_block_args(vs: &[Value]) -> Vec<BlockArg> {
    vs.iter().copied().map(BlockArg::Value).collect()
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LowerTy {
    I64,
    F64,
    Bool,
    Atom,
    Nil,
    Tuple(Vec<LowerTy>),
}

impl LowerTy {
    /// Flatten to a sequence of Cranelift primitive types.
    fn flatten(&self, out: &mut Vec<clt::Type>) {
        match self {
            LowerTy::I64 => out.push(clt::I64),
            LowerTy::F64 => out.push(clt::F64),
            LowerTy::Bool => out.push(clt::I8),
            LowerTy::Atom => out.push(clt::I32),
            LowerTy::Nil => out.push(clt::I8),
            LowerTy::Tuple(ts) => {
                for t in ts {
                    t.flatten(out);
                }
            }
        }
    }

    fn flat_arity(&self) -> usize {
        match self {
            LowerTy::Tuple(ts) => ts.iter().map(|t| t.flat_arity()).sum(),
            _ => 1,
        }
    }

    fn is_scalar(&self) -> bool {
        !matches!(self, LowerTy::Tuple(_))
    }
}

#[derive(Clone, Debug)]
pub struct FnSig {
    pub params: Vec<LowerTy>,
    pub ret: LowerTy,
}

impl FnSig {
    pub fn to_cranelift(&self, call_conv: CallConv) -> Signature {
        let mut sig = Signature::new(call_conv);
        let mut buf = Vec::new();
        for p in &self.params {
            buf.clear();
            p.flatten(&mut buf);
            for t in &buf {
                sig.params.push(AbiParam::new(*t));
            }
        }
        buf.clear();
        self.ret.flatten(&mut buf);
        for t in &buf {
            sig.returns.push(AbiParam::new(*t));
        }
        sig
    }
}

#[derive(Debug)]
pub enum LowerError {
    Unsupported(String),
    TypeMismatch(String),
    Internal(String),
}

impl std::fmt::Display for LowerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            LowerError::Unsupported(s) => write!(f, "codegen: unsupported in .12 scope: {}", s),
            LowerError::TypeMismatch(s) => write!(f, "codegen: type mismatch: {}", s),
            LowerError::Internal(s) => write!(f, "codegen: internal: {}", s),
        }
    }
}

impl std::error::Error for LowerError {}

/// A lowered value tracked during body lowering. Tuples carry their per-leaf
/// SSA values; scalars carry one. Atoms are interned to i32 ids by the host.
#[derive(Clone, Debug)]
enum LV {
    Scalar(LowerTy, Value),
    Tuple(Vec<LV>),
}

impl LV {
    fn ty(&self) -> LowerTy {
        match self {
            LV::Scalar(t, _) => t.clone(),
            LV::Tuple(elems) => LowerTy::Tuple(elems.iter().map(|e| e.ty()).collect()),
        }
    }

    fn flatten(&self, out: &mut Vec<Value>) {
        match self {
            LV::Scalar(_, v) => out.push(*v),
            LV::Tuple(es) => {
                for e in es {
                    e.flatten(out);
                }
            }
        }
    }

    /// Rebuild an LV from a flat slice of Cranelift values according to `ty`.
    fn unflatten(ty: &LowerTy, vals: &[Value], idx: &mut usize) -> LV {
        match ty {
            LowerTy::Tuple(ts) => {
                let mut elems = Vec::with_capacity(ts.len());
                for t in ts {
                    elems.push(LV::unflatten(t, vals, idx));
                }
                LV::Tuple(elems)
            }
            _ => {
                let v = vals[*idx];
                *idx += 1;
                LV::Scalar(ty.clone(), v)
            }
        }
    }
}

/// Per-compilation-unit atom interning. Ids are sequential 0..N-1 in order
/// of first appearance, so AOT can emit `fz_register_atom(i, name, len)`
/// calls in id order at binary startup and the runtime's table will line
/// up. JIT (.12.4) calls `fz_runtime::intern` from the driver after
/// lowering to populate the shared runtime table in matching order.
#[derive(Default)]
pub struct AtomInterner {
    pub names: Vec<String>,
    seen: HashMap<String, u32>,
}

impl AtomInterner {
    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.seen.get(name) {
            return id;
        }
        let id = self.names.len() as u32;
        self.names.push(name.to_string());
        self.seen.insert(name.to_string(), id);
        id
    }
}

/// Result of lowering a single function. The driver (.12.3 AOT / .12.4 JIT)
/// uses the import tables to resolve `UserExternalName(ns, id)` references
/// in the function back to real symbols:
/// - namespace 0 = user functions; id is an index into `callee_imports`.
/// - namespace 1 = runtime builtins; id is an index into `builtin_imports`.
pub struct LowerResult {
    pub func: Function,
    pub callee_imports: Vec<String>,
    pub builtin_imports: Vec<&'static str>,
}

/// Public API: lower a function (one or more clauses) with explicit signature
/// info.
///
/// `callees` provides signatures for any cross-function calls in the body
/// (including the function being lowered, for self-recursion). Tail-position
/// self-calls compile to a jump back to a per-fn TCO header; non-tail
/// self-calls are normal `call` instructions.
pub fn lower_fn(
    def: &FnDef,
    sig: &FnSig,
    callees: &HashMap<String, FnSig>,
    atoms: &mut AtomInterner,
) -> Result<LowerResult, LowerError> {
    if def.clauses.is_empty() {
        return Err(LowerError::Internal(format!("{}: zero clauses", def.name)));
    }
    for c in &def.clauses {
        if c.params.len() != sig.params.len() {
            return Err(LowerError::Internal(format!(
                "{}: arity mismatch — sig has {}, clause has {}",
                def.name,
                sig.params.len(),
                c.params.len()
            )));
        }
    }

    let cl_sig = sig.to_cranelift(CallConv::SystemV);
    let mut func = Function::with_name_signature(UserFuncName::user(0, 0), cl_sig);
    let mut fbctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut func, &mut fbctx);

    // Entry block: receives the function's incoming args.
    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);
    let entry_params: Vec<Value> = builder.block_params(entry).to_vec();

    // TCO header: a block parameterized like entry. Tail-position self-calls
    // jump here with new arg values, so each iteration re-runs clause
    // dispatch on fresh values without growing the stack.
    let tco_hdr = builder.create_block();
    let mut flat_param_tys: Vec<clt::Type> = Vec::new();
    for pty in &sig.params {
        pty.flatten(&mut flat_param_tys);
    }
    for t in &flat_param_tys {
        builder.append_block_param(tco_hdr, *t);
    }
    let entry_args = vals_to_block_args(&entry_params);
    builder.ins().jump(tco_hdr, &entry_args);
    builder.switch_to_block(tco_hdr);
    // tco_hdr is sealed only after all clauses have been lowered, so any
    // tail-position self-calls have a chance to add themselves as
    // predecessors. Sealing is done in lower_fn after lower_clauses returns.

    // Build per-arg LVs from the TCO header's params.
    let tco_params: Vec<Value> = builder.block_params(tco_hdr).to_vec();
    let mut idx = 0;
    let mut arg_lvs: Vec<LV> = Vec::with_capacity(sig.params.len());
    for pty in &sig.params {
        arg_lvs.push(LV::unflatten(pty, &tco_params, &mut idx));
    }

    let mut ctx = LoweringCtx {
        builder,
        callees,
        atoms,
        callee_refs: HashMap::new(),
        builtin_refs: HashMap::new(),
        case_result_ty: None,
        self_name: def.name.clone(),
        self_sig: sig.clone(),
        tco_hdr,
    };

    ctx.lower_clauses(&def.clauses, &arg_lvs, &sig.ret)?;
    ctx.builder.seal_block(tco_hdr);

    // Capture import tables in id order before finalize() consumes ctx.
    let callee_imports = order_by_id(&ctx.callee_refs, &ctx.builder, /*ns=*/ 0);
    let builtin_imports = order_by_id_static(&ctx.builtin_refs, &ctx.builder, /*ns=*/ 1);

    ctx.builder.finalize();
    Ok(LowerResult { func, callee_imports, builtin_imports })
}

fn order_by_id(
    refs: &HashMap<String, cranelift_codegen::ir::FuncRef>,
    builder: &FunctionBuilder<'_>,
    ns: u32,
) -> Vec<String> {
    let mut out: Vec<(u32, String)> = refs
        .iter()
        .map(|(name, fr)| {
            let id = user_id_of(builder, *fr, ns).expect("callee FuncRef must be user-named");
            (id, name.clone())
        })
        .collect();
    out.sort_by_key(|(id, _)| *id);
    out.into_iter().map(|(_, n)| n).collect()
}

fn order_by_id_static(
    refs: &HashMap<&'static str, cranelift_codegen::ir::FuncRef>,
    builder: &FunctionBuilder<'_>,
    ns: u32,
) -> Vec<&'static str> {
    let mut out: Vec<(u32, &'static str)> = refs
        .iter()
        .map(|(name, fr)| {
            let id = user_id_of(builder, *fr, ns).expect("builtin FuncRef must be user-named");
            (id, *name)
        })
        .collect();
    out.sort_by_key(|(id, _)| *id);
    out.into_iter().map(|(_, n)| n).collect()
}

fn user_id_of(
    builder: &FunctionBuilder<'_>,
    fr: cranelift_codegen::ir::FuncRef,
    expect_ns: u32,
) -> Option<u32> {
    let ext = &builder.func.dfg.ext_funcs[fr];
    match ext.name {
        cranelift_codegen::ir::ExternalName::User(uref) => {
            let u = &builder.func.params.user_named_funcs()[uref];
            if u.namespace == expect_ns { Some(u.index) } else { None }
        }
        _ => None,
    }
}

pub fn verify(func: &Function) -> Result<(), String> {
    let flags = settings::Flags::new(settings::builder());
    verify_function(func, &flags).map_err(|e| e.to_string())
}

struct LoweringCtx<'a, 'b> {
    builder: FunctionBuilder<'b>,
    callees: &'a HashMap<String, FnSig>,
    atoms: &'a mut AtomInterner,
    /// Imported FuncRef cache — populated lazily as calls are emitted.
    /// In .12.1 (no Module yet), cross-fn calls are emitted via direct
    /// SigRef-only calls when the test harness drives lowering. The full
    /// Module wiring lands in .12.3/.12.4. For now, calls produce an
    /// `Unsupported` error so the lowering surface is testable without
    /// a host Module — except for self-recursion via the same mechanism.
    callee_refs: HashMap<String, cranelift_codegen::ir::FuncRef>,
    /// Imported FuncRefs for runtime builtins (fz_print_*, fz_panic, …).
    /// Distinct from user-fn callees: emitted under namespace 1 so the host
    /// Module (.12.3/.12.4) can resolve them to the runtime staticlib's
    /// `extern "C"` symbols.
    builtin_refs: HashMap<&'static str, cranelift_codegen::ir::FuncRef>,
    case_result_ty: Option<LowerTy>,
    /// Name of the function currently being lowered. Used to detect tail-
    /// position self-calls for TCO.
    self_name: String,
    /// Signature of the function currently being lowered. Tail self-calls
    /// type-check against this and jump to `tco_hdr`.
    self_sig: FnSig,
    /// TCO header block: a per-fn jump target whose block params shape
    /// matches `self_sig`. Tail self-calls evaluate new args and jump here.
    tco_hdr: cranelift_codegen::ir::Block,
}

impl<'a, 'b> LoweringCtx<'a, 'b> {
    fn lower_expr(&mut self, e: &Expr, env: &HashMap<String, LV>) -> Result<LV, LowerError> {
        match e {
            Expr::Int(n) => {
                let v = self.builder.ins().iconst(clt::I64, *n);
                Ok(LV::Scalar(LowerTy::I64, v))
            }
            Expr::Float(f) => {
                let v = self.builder.ins().f64const(*f);
                Ok(LV::Scalar(LowerTy::F64, v))
            }
            Expr::Bool(b) => {
                let v = self.builder.ins().iconst(clt::I8, if *b { 1 } else { 0 });
                Ok(LV::Scalar(LowerTy::Bool, v))
            }
            Expr::Atom(a) => {
                let id = self.atoms.intern(a);
                let v = self.builder.ins().iconst(clt::I32, id as i64);
                Ok(LV::Scalar(LowerTy::Atom, v))
            }
            Expr::Nil => {
                let v = self.builder.ins().iconst(clt::I8, 0);
                Ok(LV::Scalar(LowerTy::Nil, v))
            }
            Expr::Var(name) => env.get(name).cloned().ok_or_else(|| {
                LowerError::Internal(format!("unbound var in codegen: {}", name))
            }),
            Expr::Tuple(elems) => {
                let mut out = Vec::with_capacity(elems.len());
                for e in elems {
                    out.push(self.lower_expr(e, env)?);
                }
                Ok(LV::Tuple(out))
            }
            Expr::BinOp(op, l, r) => {
                let lv = self.lower_expr(l, env)?;
                let rv = self.lower_expr(r, env)?;
                self.lower_binop(*op, lv, rv)
            }
            Expr::UnOp(op, x) => {
                let xv = self.lower_expr(x, env)?;
                self.lower_unop(*op, xv)
            }
            Expr::If(cond, then_e, else_e) => {
                let else_e = else_e.as_ref().ok_or_else(|| {
                    LowerError::Unsupported("if without else (.12 requires both arms)".into())
                })?;
                self.lower_if(cond, then_e, else_e, env)
            }
            Expr::Block(stmts) => self.lower_block(stmts, env),
            Expr::Match(_, _) => Err(LowerError::Unsupported(
                "Expr::Match outside Block (use `name = expr` as a Block stmt)".into(),
            )),
            Expr::Case(scrut, clauses) => self.lower_case(scrut, clauses, env),
            Expr::Call(target, args) => self.lower_call(target, args, env),
            other => Err(LowerError::Unsupported(format!("expr: {:?}", other))),
        }
    }

    fn lower_block(&mut self, stmts: &[Expr], env: &HashMap<String, LV>) -> Result<LV, LowerError> {
        let mut local_env = env.clone();
        let mut last: Option<LV> = None;
        for (i, s) in stmts.iter().enumerate() {
            let is_last = i + 1 == stmts.len();
            match s {
                Expr::Match(pat, rhs) => {
                    let v = self.lower_expr(rhs, &local_env)?;
                    self.bind_pattern(pat, v, &mut local_env)?;
                    if is_last {
                        last = Some(LV::Scalar(
                            LowerTy::Nil,
                            self.builder.ins().iconst(clt::I8, 0),
                        ));
                    }
                }
                _ => {
                    let v = self.lower_expr(s, &local_env)?;
                    if is_last {
                        last = Some(v);
                    }
                }
            }
        }
        last.ok_or_else(|| LowerError::Unsupported("empty block".into()))
    }

    fn bind_pattern(
        &mut self,
        pat: &Pattern,
        val: LV,
        env: &mut HashMap<String, LV>,
    ) -> Result<(), LowerError> {
        match pat {
            Pattern::Var(n) => {
                env.insert(n.clone(), val);
                Ok(())
            }
            Pattern::Wildcard => Ok(()),
            Pattern::Tuple(ps) => match val {
                LV::Tuple(vs) if vs.len() == ps.len() => {
                    for (p, v) in ps.iter().zip(vs.into_iter()) {
                        self.bind_pattern(p, v, env)?;
                    }
                    Ok(())
                }
                _ => Err(LowerError::TypeMismatch(
                    "tuple pattern on non-tuple value".into(),
                )),
            },
            other => Err(LowerError::Unsupported(format!(
                "binding pattern: {:?} (lands in .12.5)",
                other
            ))),
        }
    }

    fn lower_if(
        &mut self,
        cond: &Expr,
        then_e: &Expr,
        else_e: &Expr,
        env: &HashMap<String, LV>,
    ) -> Result<LV, LowerError> {
        let c = self.lower_expr(cond, env)?;
        let cv = match c {
            LV::Scalar(LowerTy::Bool, v) => v,
            other => {
                return Err(LowerError::TypeMismatch(format!(
                    "if condition must be bool, got {:?}",
                    other.ty()
                )));
            }
        };
        let then_blk = self.builder.create_block();
        let else_blk = self.builder.create_block();
        let join_blk = self.builder.create_block();
        self.builder.ins().brif(cv, then_blk, &[], else_blk, &[]);

        self.builder.switch_to_block(then_blk);
        self.builder.seal_block(then_blk);
        let then_v = self.lower_expr(then_e, env)?;
        let mut then_flat = Vec::new();
        then_v.flatten(&mut then_flat);
        for v in &then_flat {
            let ty = self.builder.func.dfg.value_type(*v);
            self.builder.append_block_param(join_blk, ty);
        }
        let then_args = vals_to_block_args(&then_flat);
        self.builder.ins().jump(join_blk, &then_args);

        self.builder.switch_to_block(else_blk);
        self.builder.seal_block(else_blk);
        let else_v = self.lower_expr(else_e, env)?;
        if else_v.ty() != then_v.ty() {
            return Err(LowerError::TypeMismatch(format!(
                "if arms differ: then={:?} else={:?}",
                then_v.ty(),
                else_v.ty()
            )));
        }
        let mut else_flat = Vec::new();
        else_v.flatten(&mut else_flat);
        let else_args = vals_to_block_args(&else_flat);
        self.builder.ins().jump(join_blk, &else_args);

        self.builder.switch_to_block(join_blk);
        self.builder.seal_block(join_blk);
        let params: Vec<Value> = self.builder.block_params(join_blk).to_vec();
        let mut idx = 0;
        Ok(LV::unflatten(&then_v.ty(), &params, &mut idx))
    }

    fn lower_case(
        &mut self,
        scrut: &Expr,
        clauses: &[MatchClause],
        env: &HashMap<String, LV>,
    ) -> Result<LV, LowerError> {
        if clauses.is_empty() {
            return Err(LowerError::Unsupported("empty case".into()));
        }
        let scrut_v = self.lower_expr(scrut, env)?;

        // Pre-compute result type from first clause's body under its bindings,
        // then assert subsequent clauses match. This requires lowering each
        // body once, but we need to chain blocks in flow order; so we pick
        // result-type from the first clause's body LV after lowering.
        //
        // Strategy: chain test→body→join. Each clause has a `body_blk` and a
        // `next_blk` (the next clause's test, or a panic block for fall-
        // through on the last clause).
        let mut body_blks = Vec::with_capacity(clauses.len());
        let mut next_blks = Vec::with_capacity(clauses.len());
        let join_blk = self.builder.create_block();
        for _ in 0..clauses.len() {
            body_blks.push(self.builder.create_block());
            next_blks.push(self.builder.create_block());
        }
        let panic_blk = self.builder.create_block();

        // Wire the test chain.
        // For clause i: in next_blks[i-1] (or current block for i=0), test the
        // pattern; on success → body_blks[i] (with bindings), on failure →
        // next_blks[i] which either continues to clause i+1 or to panic.
        for (i, clause) in clauses.iter().enumerate() {
            if i == 0 {
                // current block already active
            } else {
                self.builder.switch_to_block(next_blks[i - 1]);
                self.builder.seal_block(next_blks[i - 1]);
            }

            if clause.guard.is_some() {
                return Err(LowerError::Unsupported("case guards (.12.5)".into()));
            }

            let fail_blk = if i + 1 < clauses.len() {
                next_blks[i]
            } else {
                next_blks[i] // last clause failure → next_blks[last] which we'll wire to panic
            };
            let bindings = self.test_pattern(&clause.pattern, &scrut_v, body_blks[i], fail_blk)?;
            // body_blks[i] has been set up by test_pattern with the right
            // bindings injected via block params.
            self.builder.switch_to_block(body_blks[i]);
            self.builder.seal_block(body_blks[i]);
            let mut body_env = env.clone();
            for (name, lv) in bindings {
                body_env.insert(name, lv);
            }
            let body_lv = self.lower_expr(&clause.body, &body_env)?;
            // First body sets the join block's param shape.
            if i == 0 {
                let mut flat = Vec::new();
                body_lv.flatten(&mut flat);
                for v in &flat {
                    let ty = self.builder.func.dfg.value_type(*v);
                    self.builder.append_block_param(join_blk, ty);
                }
                let args = vals_to_block_args(&flat);
                self.builder.ins().jump(join_blk, &args);
                self.case_result_ty = Some(body_lv.ty());
            } else {
                let expected = self.case_result_ty.clone().unwrap();
                if body_lv.ty() != expected {
                    return Err(LowerError::TypeMismatch(format!(
                        "case clause body types differ: clause0={:?} clause{}={:?}",
                        expected,
                        i,
                        body_lv.ty()
                    )));
                }
                let mut flat = Vec::new();
                body_lv.flatten(&mut flat);
                let args = vals_to_block_args(&flat);
                self.builder.ins().jump(join_blk, &args);
            }
        }

        // Wire the last failure block to panic.
        let last_fail = next_blks.last().copied().unwrap();
        self.builder.switch_to_block(last_fail);
        self.builder.seal_block(last_fail);
        let no_args: Vec<BlockArg> = Vec::new();
        self.builder.ins().jump(panic_blk, &no_args);

        self.builder.switch_to_block(panic_blk);
        self.builder.seal_block(panic_blk);
        // Trap on no-match. Real panic with formatted message lands in .12.2.
        self.builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(1).unwrap());

        // Continue at join.
        self.builder.switch_to_block(join_blk);
        self.builder.seal_block(join_blk);
        let result_ty = self.case_result_ty.take().unwrap();
        let params: Vec<Value> = self.builder.block_params(join_blk).to_vec();
        let mut idx = 0;
        Ok(LV::unflatten(&result_ty, &params, &mut idx))
    }

    /// Test a pattern against a value. On match, jump to `success` with
    /// bindings (also returned to the caller for env extension). On fail,
    /// jump to `fail`.
    fn test_pattern(
        &mut self,
        pat: &Pattern,
        val: &LV,
        success: cranelift_codegen::ir::Block,
        fail: cranelift_codegen::ir::Block,
    ) -> Result<Vec<(String, LV)>, LowerError> {
        let mut bindings = Vec::new();
        let cond = self.match_cond(pat, val, &mut bindings)?;
        match cond {
            MatchCond::Always => {
                let no_args: Vec<BlockArg> = Vec::new();
                self.builder.ins().jump(success, &no_args);
            }
            MatchCond::OnValue(v) => {
                let no_args: Vec<BlockArg> = Vec::new();
                self.builder
                    .ins()
                    .brif(v, success, &no_args, fail, &no_args);
            }
        }
        Ok(bindings)
    }

    /// Build the boolean (i8 or none-meaning-always) that says "this pattern
    /// matches this value". Collects var bindings.
    fn match_cond(
        &mut self,
        pat: &Pattern,
        val: &LV,
        bindings: &mut Vec<(String, LV)>,
    ) -> Result<MatchCond, LowerError> {
        match (pat, val) {
            (Pattern::Wildcard, _) => Ok(MatchCond::Always),
            (Pattern::Var(n), v) => {
                bindings.push((n.clone(), v.clone()));
                Ok(MatchCond::Always)
            }
            (Pattern::Int(k), LV::Scalar(LowerTy::I64, v)) => {
                let kv = self.builder.ins().iconst(clt::I64, *k);
                let eq = self.builder.ins().icmp(IntCC::Equal, *v, kv);
                Ok(MatchCond::OnValue(eq))
            }
            (Pattern::Float(k), LV::Scalar(LowerTy::F64, v)) => {
                let kv = self.builder.ins().f64const(*k);
                let eq = self.builder.ins().fcmp(FloatCC::Equal, *v, kv);
                Ok(MatchCond::OnValue(eq))
            }
            (Pattern::Bool(k), LV::Scalar(LowerTy::Bool, v)) => {
                let kv = self.builder.ins().iconst(clt::I8, if *k { 1 } else { 0 });
                let eq = self.builder.ins().icmp(IntCC::Equal, *v, kv);
                Ok(MatchCond::OnValue(eq))
            }
            (Pattern::Atom(a), LV::Scalar(LowerTy::Atom, v)) => {
                let id = self.atoms.intern(a);
                let kv = self.builder.ins().iconst(clt::I32, id as i64);
                let eq = self.builder.ins().icmp(IntCC::Equal, *v, kv);
                Ok(MatchCond::OnValue(eq))
            }
            (Pattern::Nil, LV::Scalar(LowerTy::Nil, _)) => Ok(MatchCond::Always),
            (Pattern::Tuple(ps), LV::Tuple(vs)) if ps.len() == vs.len() => {
                let mut acc: Option<Value> = None;
                for (p, v) in ps.iter().zip(vs.iter()) {
                    let sub = self.match_cond(p, v, bindings)?;
                    let cur = match sub {
                        MatchCond::Always => continue,
                        MatchCond::OnValue(b) => b,
                    };
                    acc = Some(match acc {
                        None => cur,
                        Some(prev) => self.builder.ins().band(prev, cur),
                    });
                }
                Ok(match acc {
                    None => MatchCond::Always,
                    Some(b) => MatchCond::OnValue(b),
                })
            }
            (p, v) => Err(LowerError::TypeMismatch(format!(
                "pattern {:?} cannot match value of type {:?}",
                p,
                v.ty()
            ))),
        }
    }

    fn lower_call(
        &mut self,
        target: &Expr,
        args: &[Expr],
        env: &HashMap<String, LV>,
    ) -> Result<LV, LowerError> {
        let name = match target {
            Expr::Var(n) => n.clone(),
            other => {
                return Err(LowerError::Unsupported(format!(
                    "call target other than Var: {:?}",
                    other
                )));
            }
        };
        // Builtins dispatch on argument type to the right runtime symbol;
        // they aren't entries in `callees`.
        if let Some(lv) = self.try_lower_builtin(&name, args, env)? {
            return Ok(lv);
        }
        let sig = self
            .callees
            .get(&name)
            .ok_or_else(|| LowerError::Internal(format!("unknown callee: {}", name)))?
            .clone();
        if sig.params.len() != args.len() {
            return Err(LowerError::TypeMismatch(format!(
                "call {}: arity {} vs {} args",
                name,
                sig.params.len(),
                args.len()
            )));
        }
        let mut flat_args: Vec<Value> = Vec::new();
        for (a, pty) in args.iter().zip(sig.params.iter()) {
            let lv = self.lower_expr(a, env)?;
            expect_assignable(pty, &lv.ty()).map_err(LowerError::TypeMismatch)?;
            lv.flatten(&mut flat_args);
        }

        // Import the callee as a SigRef-only indirect call would require an
        // address; instead we declare an external function via a unique
        // UserExternalName. The actual symbol resolution happens at link
        // time (.12.3) or via JIT module (.12.4). For .12.1 we build a
        // FuncRef referring to a user-named external function.
        let func_ref = self.import_callee(&name, &sig)?;
        let inst = self.builder.ins().call(func_ref, &flat_args);
        let results: Vec<Value> = self.builder.inst_results(inst).to_vec();
        let mut idx = 0;
        Ok(LV::unflatten(&sig.ret, &results, &mut idx))
    }

    fn try_lower_builtin(
        &mut self,
        name: &str,
        args: &[Expr],
        env: &HashMap<String, LV>,
    ) -> Result<Option<LV>, LowerError> {
        match name {
            "print" => {
                if args.len() != 1 {
                    return Err(LowerError::TypeMismatch(format!(
                        "print/1 called with {} args",
                        args.len()
                    )));
                }
                let arg = self.lower_expr(&args[0], env)?;
                let (sym, sig) = match arg.ty() {
                    LowerTy::I64 => (
                        "fz_print_i64",
                        FnSig { params: vec![LowerTy::I64], ret: LowerTy::Nil },
                    ),
                    LowerTy::F64 => (
                        "fz_print_f64",
                        FnSig { params: vec![LowerTy::F64], ret: LowerTy::Nil },
                    ),
                    LowerTy::Bool => (
                        "fz_print_bool",
                        FnSig { params: vec![LowerTy::Bool], ret: LowerTy::Nil },
                    ),
                    LowerTy::Atom => (
                        "fz_print_atom",
                        FnSig { params: vec![LowerTy::Atom], ret: LowerTy::Nil },
                    ),
                    LowerTy::Nil => (
                        "fz_print_nil",
                        FnSig { params: vec![], ret: LowerTy::Nil },
                    ),
                    LowerTy::Tuple(_) => {
                        return Err(LowerError::Unsupported(
                            "print of tuple — needs a runtime helper, lands in .12.5".into(),
                        ));
                    }
                };
                let fr = self.import_runtime(sym, &sig)?;
                let mut flat_args = Vec::new();
                if !matches!(arg.ty(), LowerTy::Nil) {
                    arg.flatten(&mut flat_args);
                }
                let _ = self.builder.ins().call(fr, &flat_args);
                let z = self.builder.ins().iconst(clt::I8, 0);
                Ok(Some(LV::Scalar(LowerTy::Nil, z)))
            }
            _ => Ok(None),
        }
    }

    fn import_runtime(
        &mut self,
        sym: &'static str,
        sig: &FnSig,
    ) -> Result<cranelift_codegen::ir::FuncRef, LowerError> {
        if let Some(fr) = self.builtin_refs.get(sym) {
            return Ok(*fr);
        }
        let cl_sig = sig.to_cranelift(CallConv::SystemV);
        let sig_ref = self.builder.import_signature(cl_sig);
        // Namespace 1 is the runtime; the host Module maps id → runtime
        // staticlib symbol via a fixed table (.12.3/.12.4).
        let id = self.builtin_refs.len() as u32;
        let user_name_ref = self
            .builder
            .func
            .declare_imported_user_function(cranelift_codegen::ir::UserExternalName::new(1, id));
        let ext_data = cranelift_codegen::ir::ExtFuncData {
            name: cranelift_codegen::ir::ExternalName::user(user_name_ref),
            signature: sig_ref,
            colocated: false,
            patchable: false,
        };
        let fr = self.builder.func.import_function(ext_data);
        self.builtin_refs.insert(sym, fr);
        Ok(fr)
    }

    fn import_callee(
        &mut self,
        name: &str,
        sig: &FnSig,
    ) -> Result<cranelift_codegen::ir::FuncRef, LowerError> {
        if let Some(fr) = self.callee_refs.get(name) {
            return Ok(*fr);
        }
        let cl_sig = sig.to_cranelift(CallConv::SystemV);
        let sig_ref = self.builder.import_signature(cl_sig);
        // Use the index in callee_refs as a stable per-function id; .12.3/.12.4
        // map UserExternalName(0, idx) → a real symbol via the host Module.
        let id = self.callee_refs.len() as u32;
        let user_name_ref = self
            .builder
            .func
            .declare_imported_user_function(cranelift_codegen::ir::UserExternalName::new(0, id));
        let ext_data = cranelift_codegen::ir::ExtFuncData {
            name: cranelift_codegen::ir::ExternalName::user(user_name_ref),
            signature: sig_ref,
            colocated: false,
            patchable: false,
        };
        let fr = self.builder.func.import_function(ext_data);
        self.callee_refs.insert(name.to_string(), fr);
        Ok(fr)
    }

    fn lower_binop(&mut self, op: BinOp, l: LV, r: LV) -> Result<LV, LowerError> {
        use BinOp::*;
        match (&l, &r) {
            (LV::Scalar(LowerTy::I64, lv), LV::Scalar(LowerTy::I64, rv)) => {
                let ins = self.builder.ins();
                let v = match op {
                    Add => ins.iadd(*lv, *rv),
                    Sub => ins.isub(*lv, *rv),
                    Mul => ins.imul(*lv, *rv),
                    Div => ins.sdiv(*lv, *rv),
                    Rem => ins.srem(*lv, *rv),
                    Eq => return Ok(LV::Scalar(LowerTy::Bool, ins.icmp(IntCC::Equal, *lv, *rv))),
                    Neq => return Ok(LV::Scalar(LowerTy::Bool, ins.icmp(IntCC::NotEqual, *lv, *rv))),
                    Lt => return Ok(LV::Scalar(LowerTy::Bool, ins.icmp(IntCC::SignedLessThan, *lv, *rv))),
                    LtEq => return Ok(LV::Scalar(LowerTy::Bool, ins.icmp(IntCC::SignedLessThanOrEqual, *lv, *rv))),
                    Gt => return Ok(LV::Scalar(LowerTy::Bool, ins.icmp(IntCC::SignedGreaterThan, *lv, *rv))),
                    GtEq => return Ok(LV::Scalar(LowerTy::Bool, ins.icmp(IntCC::SignedGreaterThanOrEqual, *lv, *rv))),
                    other => {
                        return Err(LowerError::Unsupported(format!(
                            "BinOp {:?} on int (e.g. cons/pipe — out of scope)",
                            other
                        )));
                    }
                };
                Ok(LV::Scalar(LowerTy::I64, v))
            }
            (LV::Scalar(LowerTy::F64, lv), LV::Scalar(LowerTy::F64, rv)) => {
                let ins = self.builder.ins();
                let v = match op {
                    Add => ins.fadd(*lv, *rv),
                    Sub => ins.fsub(*lv, *rv),
                    Mul => ins.fmul(*lv, *rv),
                    Div => ins.fdiv(*lv, *rv),
                    Eq => return Ok(LV::Scalar(LowerTy::Bool, ins.fcmp(FloatCC::Equal, *lv, *rv))),
                    Neq => return Ok(LV::Scalar(LowerTy::Bool, ins.fcmp(FloatCC::NotEqual, *lv, *rv))),
                    Lt => return Ok(LV::Scalar(LowerTy::Bool, ins.fcmp(FloatCC::LessThan, *lv, *rv))),
                    LtEq => return Ok(LV::Scalar(LowerTy::Bool, ins.fcmp(FloatCC::LessThanOrEqual, *lv, *rv))),
                    Gt => return Ok(LV::Scalar(LowerTy::Bool, ins.fcmp(FloatCC::GreaterThan, *lv, *rv))),
                    GtEq => return Ok(LV::Scalar(LowerTy::Bool, ins.fcmp(FloatCC::GreaterThanOrEqual, *lv, *rv))),
                    other => {
                        return Err(LowerError::Unsupported(format!(
                            "BinOp {:?} on float",
                            other
                        )));
                    }
                };
                Ok(LV::Scalar(LowerTy::F64, v))
            }
            (LV::Scalar(LowerTy::Bool, lv), LV::Scalar(LowerTy::Bool, rv)) => {
                let ins = self.builder.ins();
                let v = match op {
                    And => ins.band(*lv, *rv),
                    Or => ins.bor(*lv, *rv),
                    Eq => ins.icmp(IntCC::Equal, *lv, *rv),
                    Neq => ins.icmp(IntCC::NotEqual, *lv, *rv),
                    other => {
                        return Err(LowerError::Unsupported(format!(
                            "BinOp {:?} on bool",
                            other
                        )));
                    }
                };
                Ok(LV::Scalar(LowerTy::Bool, v))
            }
            (LV::Scalar(LowerTy::Atom, lv), LV::Scalar(LowerTy::Atom, rv)) => {
                let ins = self.builder.ins();
                let v = match op {
                    Eq => ins.icmp(IntCC::Equal, *lv, *rv),
                    Neq => ins.icmp(IntCC::NotEqual, *lv, *rv),
                    other => {
                        return Err(LowerError::Unsupported(format!(
                            "BinOp {:?} on atom",
                            other
                        )));
                    }
                };
                Ok(LV::Scalar(LowerTy::Bool, v))
            }
            _ => Err(LowerError::TypeMismatch(format!(
                "BinOp {:?} on incompatible types: {:?} vs {:?}",
                op,
                l.ty(),
                r.ty()
            ))),
        }
    }

    /// Multi-clause function dispatch. Each clause tests its parameter
    /// patterns (combined via `band`), then its guard if any; on full match
    /// jumps to its body block, on fail to next clause's test block. Last
    /// clause's fail block traps. Bodies emit their own returns via
    /// `lower_expr_tail`.
    fn lower_clauses(
        &mut self,
        clauses: &[FnClause],
        args: &[LV],
        ret_ty: &LowerTy,
    ) -> Result<(), LowerError> {
        let n = clauses.len();
        let mut next_blks: Vec<cranelift_codegen::ir::Block> = (0..n)
            .map(|_| self.builder.create_block())
            .collect();
        let panic_blk = self.builder.create_block();

        for (i, clause) in clauses.iter().enumerate() {
            if i > 0 {
                self.builder.switch_to_block(next_blks[i - 1]);
                self.builder.seal_block(next_blks[i - 1]);
            }
            let body_blk = self.builder.create_block();
            let fail_blk = next_blks[i];

            // Build pattern-match boolean across all param patterns.
            let mut bindings: Vec<(String, LV)> = Vec::new();
            let mut acc: Option<Value> = None;
            for (pat, lv) in clause.params.iter().zip(args.iter()) {
                let cond = self.match_cond(pat, lv, &mut bindings)?;
                if let MatchCond::OnValue(b) = cond {
                    acc = Some(match acc {
                        None => b,
                        Some(prev) => self.builder.ins().band(prev, b),
                    });
                }
            }

            // Guard, if present, gets its own block so bindings are in scope.
            if let Some(guard) = &clause.guard {
                let guard_blk = self.builder.create_block();
                let no_args: Vec<BlockArg> = Vec::new();
                match acc {
                    None => { self.builder.ins().jump(guard_blk, &no_args); }
                    Some(b) => {
                        self.builder.ins().brif(b, guard_blk, &no_args, fail_blk, &no_args);
                    }
                }
                self.builder.switch_to_block(guard_blk);
                self.builder.seal_block(guard_blk);
                let mut env: HashMap<String, LV> = HashMap::new();
                for (name, lv) in &bindings {
                    env.insert(name.clone(), lv.clone());
                }
                let gv = self.lower_expr(guard, &env)?;
                let gv_b = match gv {
                    LV::Scalar(LowerTy::Bool, v) => v,
                    other => {
                        return Err(LowerError::TypeMismatch(format!(
                            "guard must be bool, got {:?}",
                            other.ty()
                        )));
                    }
                };
                let no_args: Vec<BlockArg> = Vec::new();
                self.builder
                    .ins()
                    .brif(gv_b, body_blk, &no_args, fail_blk, &no_args);
            } else {
                let no_args: Vec<BlockArg> = Vec::new();
                match acc {
                    None => { self.builder.ins().jump(body_blk, &no_args); }
                    Some(b) => {
                        self.builder.ins().brif(b, body_blk, &no_args, fail_blk, &no_args);
                    }
                }
            }

            // Body block: bindings active, lower body in tail position.
            self.builder.switch_to_block(body_blk);
            self.builder.seal_block(body_blk);
            let mut env: HashMap<String, LV> = HashMap::new();
            for (name, lv) in &bindings {
                env.insert(name.clone(), lv.clone());
            }
            self.lower_expr_tail(&clause.body, &env, ret_ty)?;
        }

        // Last failure → panic.
        let last_fail = *next_blks.last().unwrap();
        self.builder.switch_to_block(last_fail);
        self.builder.seal_block(last_fail);
        let no_args: Vec<BlockArg> = Vec::new();
        self.builder.ins().jump(panic_blk, &no_args);

        self.builder.switch_to_block(panic_blk);
        self.builder.seal_block(panic_blk);
        self.builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(2).unwrap());
        let _ = next_blks; // keep for clarity
        Ok(())
    }

    /// Lower an expression in tail position. Emits its own terminator —
    /// either `return_` for normal exits or `jump` to the TCO header for
    /// self-tail-calls. Recurses for control-flow forms (Block/If/Case)
    /// so each branch arm can independently emit its own terminator.
    fn lower_expr_tail(
        &mut self,
        e: &Expr,
        env: &HashMap<String, LV>,
        ret_ty: &LowerTy,
    ) -> Result<(), LowerError> {
        match e {
            Expr::Block(stmts) => self.lower_block_tail(stmts, env, ret_ty),
            Expr::If(c, t, els) => {
                let els = els.as_ref().ok_or_else(|| {
                    LowerError::Unsupported("if without else (.12 requires both arms)".into())
                })?;
                self.lower_if_tail(c, t, els, env, ret_ty)
            }
            Expr::Case(scrut, clauses) => self.lower_case_tail(scrut, clauses, env, ret_ty),
            Expr::Call(target, args) => {
                if let Expr::Var(name) = target.as_ref() {
                    if name == &self.self_name {
                        return self.emit_tail_self_call(args, env);
                    }
                }
                // Non-tail-eligible call: lower normally and return.
                let lv = self.lower_expr(e, env)?;
                self.emit_normal_return(lv, ret_ty)
            }
            _ => {
                let lv = self.lower_expr(e, env)?;
                self.emit_normal_return(lv, ret_ty)
            }
        }
    }

    fn emit_normal_return(&mut self, lv: LV, ret_ty: &LowerTy) -> Result<(), LowerError> {
        expect_assignable(ret_ty, &lv.ty()).map_err(LowerError::TypeMismatch)?;
        let mut rv = Vec::new();
        lv.flatten(&mut rv);
        self.builder.ins().return_(&rv);
        Ok(())
    }

    fn emit_tail_self_call(
        &mut self,
        args: &[Expr],
        env: &HashMap<String, LV>,
    ) -> Result<(), LowerError> {
        if args.len() != self.self_sig.params.len() {
            return Err(LowerError::TypeMismatch(format!(
                "tail self-call: arity {} vs {} args",
                self.self_sig.params.len(),
                args.len()
            )));
        }
        let mut flat: Vec<Value> = Vec::new();
        let param_tys = self.self_sig.params.clone();
        for (a, pty) in args.iter().zip(param_tys.iter()) {
            let lv = self.lower_expr(a, env)?;
            expect_assignable(pty, &lv.ty()).map_err(LowerError::TypeMismatch)?;
            lv.flatten(&mut flat);
        }
        let jump_args = vals_to_block_args(&flat);
        self.builder.ins().jump(self.tco_hdr, &jump_args);
        Ok(())
    }

    fn lower_block_tail(
        &mut self,
        stmts: &[Expr],
        env: &HashMap<String, LV>,
        ret_ty: &LowerTy,
    ) -> Result<(), LowerError> {
        let mut local_env = env.clone();
        if stmts.is_empty() {
            return Err(LowerError::Unsupported("empty block".into()));
        }
        for (i, s) in stmts.iter().enumerate() {
            let is_last = i + 1 == stmts.len();
            if is_last {
                return self.lower_expr_tail(s, &local_env, ret_ty);
            }
            match s {
                Expr::Match(pat, rhs) => {
                    let v = self.lower_expr(rhs, &local_env)?;
                    self.bind_pattern(pat, v, &mut local_env)?;
                }
                _ => {
                    let _ = self.lower_expr(s, &local_env)?;
                }
            }
        }
        unreachable!()
    }

    fn lower_if_tail(
        &mut self,
        cond: &Expr,
        then_e: &Expr,
        else_e: &Expr,
        env: &HashMap<String, LV>,
        ret_ty: &LowerTy,
    ) -> Result<(), LowerError> {
        let cv = self.lower_expr(cond, env)?;
        let bv = match cv {
            LV::Scalar(LowerTy::Bool, v) => v,
            other => {
                return Err(LowerError::TypeMismatch(format!(
                    "if condition must be bool, got {:?}",
                    other.ty()
                )));
            }
        };
        let then_blk = self.builder.create_block();
        let else_blk = self.builder.create_block();
        let no_args: Vec<BlockArg> = Vec::new();
        self.builder
            .ins()
            .brif(bv, then_blk, &no_args, else_blk, &no_args);

        self.builder.switch_to_block(then_blk);
        self.builder.seal_block(then_blk);
        self.lower_expr_tail(then_e, env, ret_ty)?;

        self.builder.switch_to_block(else_blk);
        self.builder.seal_block(else_blk);
        self.lower_expr_tail(else_e, env, ret_ty)?;
        Ok(())
    }

    fn lower_case_tail(
        &mut self,
        scrut: &Expr,
        clauses: &[MatchClause],
        env: &HashMap<String, LV>,
        ret_ty: &LowerTy,
    ) -> Result<(), LowerError> {
        if clauses.is_empty() {
            return Err(LowerError::Unsupported("empty case".into()));
        }
        let scrut_v = self.lower_expr(scrut, env)?;

        let n = clauses.len();
        let next_blks: Vec<cranelift_codegen::ir::Block> = (0..n)
            .map(|_| self.builder.create_block())
            .collect();
        let panic_blk = self.builder.create_block();

        for (i, clause) in clauses.iter().enumerate() {
            if i > 0 {
                self.builder.switch_to_block(next_blks[i - 1]);
                self.builder.seal_block(next_blks[i - 1]);
            }
            let body_blk = self.builder.create_block();
            let fail_blk = next_blks[i];
            let mut bindings: Vec<(String, LV)> = Vec::new();
            let cond = self.match_cond(&clause.pattern, &scrut_v, &mut bindings)?;
            let no_args: Vec<BlockArg> = Vec::new();

            // Optional guard layered on top.
            if let Some(guard) = &clause.guard {
                let guard_blk = self.builder.create_block();
                match cond {
                    MatchCond::Always => { self.builder.ins().jump(guard_blk, &no_args); }
                    MatchCond::OnValue(b) => {
                        self.builder.ins().brif(b, guard_blk, &no_args, fail_blk, &no_args);
                    }
                }
                self.builder.switch_to_block(guard_blk);
                self.builder.seal_block(guard_blk);
                let mut g_env = env.clone();
                for (n, lv) in &bindings {
                    g_env.insert(n.clone(), lv.clone());
                }
                let gv = self.lower_expr(guard, &g_env)?;
                let gv_b = match gv {
                    LV::Scalar(LowerTy::Bool, v) => v,
                    other => {
                        return Err(LowerError::TypeMismatch(format!(
                            "case guard must be bool, got {:?}",
                            other.ty()
                        )));
                    }
                };
                self.builder
                    .ins()
                    .brif(gv_b, body_blk, &no_args, fail_blk, &no_args);
            } else {
                match cond {
                    MatchCond::Always => { self.builder.ins().jump(body_blk, &no_args); }
                    MatchCond::OnValue(b) => {
                        self.builder.ins().brif(b, body_blk, &no_args, fail_blk, &no_args);
                    }
                }
            }

            self.builder.switch_to_block(body_blk);
            self.builder.seal_block(body_blk);
            let mut body_env = env.clone();
            for (name, lv) in &bindings {
                body_env.insert(name.clone(), lv.clone());
            }
            self.lower_expr_tail(&clause.body, &body_env, ret_ty)?;
        }

        let last_fail = *next_blks.last().unwrap();
        self.builder.switch_to_block(last_fail);
        self.builder.seal_block(last_fail);
        let no_args: Vec<BlockArg> = Vec::new();
        self.builder.ins().jump(panic_blk, &no_args);
        self.builder.switch_to_block(panic_blk);
        self.builder.seal_block(panic_blk);
        self.builder
            .ins()
            .trap(cranelift_codegen::ir::TrapCode::user(3).unwrap());
        Ok(())
    }

    fn lower_unop(&mut self, op: UnOp, x: LV) -> Result<LV, LowerError> {
        match (&op, &x) {
            (UnOp::Neg, LV::Scalar(LowerTy::I64, v)) => {
                let z = self.builder.ins().iconst(clt::I64, 0);
                let r = self.builder.ins().isub(z, *v);
                Ok(LV::Scalar(LowerTy::I64, r))
            }
            (UnOp::Neg, LV::Scalar(LowerTy::F64, v)) => {
                let r = self.builder.ins().fneg(*v);
                Ok(LV::Scalar(LowerTy::F64, r))
            }
            (UnOp::Not, LV::Scalar(LowerTy::Bool, v)) => {
                let one = self.builder.ins().iconst(clt::I8, 1);
                let r = self.builder.ins().bxor(*v, one);
                Ok(LV::Scalar(LowerTy::Bool, r))
            }
            _ => Err(LowerError::TypeMismatch(format!(
                "UnOp {:?} on {:?}",
                op,
                x.ty()
            ))),
        }
    }
}

#[derive(Clone, Copy)]
enum MatchCond {
    Always,
    OnValue(Value),
}

fn expect_assignable(expected: &LowerTy, got: &LowerTy) -> Result<(), String> {
    if expected == got {
        Ok(())
    } else {
        Err(format!("expected {:?}, got {:?}", expected, got))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn parse_one(src: &str) -> FnDef {
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        for item in &prog.items {
            if let Item::Fn(d) = &**item {
                if !d.is_macro {
                    return d.clone();
                }
            }
        }
        panic!("no fn in source");
    }

    fn lower_one(src: &str, sig: FnSig) -> Function {
        let def = parse_one(src);
        let callees = HashMap::new();
        let mut atoms = AtomInterner::default();
        let r = lower_fn(&def, &sig, &callees, &mut atoms).expect("lower");
        verify(&r.func).expect("verify");
        r.func
    }

    fn ty_i64() -> LowerTy { LowerTy::I64 }
    fn ty_f64() -> LowerTy { LowerTy::F64 }
    fn ty_bool() -> LowerTy { LowerTy::Bool }
    fn ty_atom() -> LowerTy { LowerTy::Atom }

    #[test]
    fn lowers_int_arith() {
        let f = lower_one(
            "fn step(n) do n * 2 + 1 end",
            FnSig { params: vec![ty_i64()], ret: ty_i64() },
        );
        let s = f.display().to_string();
        assert!(s.contains("imul"));
        assert!(s.contains("iadd"));
    }

    #[test]
    fn lowers_float_arith() {
        let f = lower_one(
            "fn fadd(a, b) do a + b end",
            FnSig { params: vec![ty_f64(), ty_f64()], ret: ty_f64() },
        );
        let s = f.display().to_string();
        assert!(s.contains("fadd"));
    }

    #[test]
    fn lowers_comparison_to_bool() {
        let f = lower_one(
            "fn is_pos(n) do n > 0 end",
            FnSig { params: vec![ty_i64()], ret: ty_bool() },
        );
        let s = f.display().to_string();
        assert!(s.contains("icmp"));
    }

    #[test]
    fn lowers_if_else() {
        let f = lower_one(
            "fn abs(n) do if n < 0 do -n else n end end",
            FnSig { params: vec![ty_i64()], ret: ty_i64() },
        );
        let s = f.display().to_string();
        assert!(s.contains("brif"));
        assert!(s.contains("jump"));
    }

    #[test]
    fn lowers_tuple_and_destructure() {
        let f = lower_one(
            "fn swap(t) do case t do {a, b} -> {b, a} end end",
            FnSig {
                params: vec![LowerTy::Tuple(vec![ty_i64(), ty_i64()])],
                ret: LowerTy::Tuple(vec![ty_i64(), ty_i64()]),
            },
        );
        // Two i64 params and two i64 returns after flattening.
        assert_eq!(f.signature.params.len(), 2);
        assert_eq!(f.signature.returns.len(), 2);
    }

    #[test]
    fn lowers_case_with_literal_clauses() {
        let f = lower_one(
            "fn classify(n) do case n do 0 -> :zero; _ -> :other end end",
            FnSig { params: vec![ty_i64()], ret: ty_atom() },
        );
        let s = f.display().to_string();
        assert!(s.contains("brif"));
    }

    #[test]
    fn lowers_block_with_match_binding() {
        let f = lower_one(
            "fn calc(x) do y = x * 2; z = y + 1; z end",
            FnSig { params: vec![ty_i64()], ret: ty_i64() },
        );
        let s = f.display().to_string();
        assert!(s.contains("imul"));
        assert!(s.contains("iadd"));
    }

    #[test]
    fn lowers_call_to_known_callee() {
        let def = parse_one("fn use_dbl(x) do dbl(x) + 1 end");
        let mut callees = HashMap::new();
        callees.insert(
            "dbl".to_string(),
            FnSig { params: vec![ty_i64()], ret: ty_i64() },
        );
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![ty_i64()], ret: ty_i64() },
            &callees,
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
        let s = r.func.display().to_string();
        assert!(s.contains("call"));
        assert_eq!(r.callee_imports, vec!["dbl".to_string()]);
    }

    #[test]
    fn lowers_self_recursion() {
        // Recursive call OK at the lowering level — TCO is .12.5.
        let def = parse_one("fn rec(n) do if n == 0 do 0 else rec(n - 1) end end");
        let mut callees = HashMap::new();
        callees.insert(
            "rec".to_string(),
            FnSig { params: vec![ty_i64()], ret: ty_i64() },
        );
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![ty_i64()], ret: ty_i64() },
            &callees,
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
    }

    #[test]
    fn lowers_multi_clause_with_literal_dispatch() {
        let toks = Lexer::new("fn f(0), do: 0\nfn f(n), do: n").tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let def = match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            _ => panic!(),
        };
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![ty_i64()], ret: ty_i64() },
            &HashMap::new(),
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
        let s = r.func.display().to_string();
        // Two clauses → at least one brif on the first clause's literal test.
        assert!(s.contains("brif"));
    }

    #[test]
    fn lowers_clause_with_guard() {
        let toks = Lexer::new("fn classify(n) when n > 0, do: 1\nfn classify(_), do: 0")
            .tokenize()
            .unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let def = match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            _ => panic!(),
        };
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![ty_i64()], ret: ty_i64() },
            &HashMap::new(),
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
    }

    #[test]
    fn lowers_tail_self_call_to_jump() {
        // Tail recursion: `tally(n - 1, acc + n)` is a tail call to self.
        let toks = Lexer::new(
            "fn tally(0, acc), do: acc\nfn tally(n, acc), do: tally(n - 1, acc + n)",
        )
        .tokenize()
        .unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let def = match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            _ => panic!(),
        };
        let mut callees = HashMap::new();
        callees.insert(
            "tally".to_string(),
            FnSig { params: vec![ty_i64(), ty_i64()], ret: ty_i64() },
        );
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![ty_i64(), ty_i64()], ret: ty_i64() },
            &callees,
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
        let s = r.func.display().to_string();
        // Tail self-call must NOT emit a `call` to itself — it should be a
        // `jump` to the TCO header instead.
        assert!(
            !s.contains("call "),
            "expected tail-self-call to be jump, not call:\n{}",
            s
        );
    }

    #[test]
    fn lowers_param_tuple_pattern() {
        let toks = Lexer::new("fn first({a, _}), do: a").tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let def = match &*prog.items[0] {
            Item::Fn(d) => d.clone(),
            _ => panic!(),
        };
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig {
                params: vec![LowerTy::Tuple(vec![ty_i64(), ty_i64()])],
                ret: ty_i64(),
            },
            &HashMap::new(),
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
    }

    #[test]
    fn rejects_unsupported_expr() {
        let def = parse_one("fn lst() do [1, 2, 3] end");
        let mut atoms = AtomInterner::default();
        let res = lower_fn(
            &def,
            &FnSig { params: vec![], ret: ty_i64() },
            &HashMap::new(),
            &mut atoms,
        );
        assert!(matches!(res, Err(LowerError::Unsupported(_))));
    }

    #[test]
    fn lowers_print_int_to_runtime_builtin() {
        let def = parse_one("fn p(n) do print(n) end");
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![ty_i64()], ret: LowerTy::Nil },
            &HashMap::new(),
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
        assert_eq!(r.builtin_imports, vec!["fz_print_i64"]);
        assert!(r.callee_imports.is_empty());
    }

    #[test]
    fn lowers_print_atom_to_runtime_builtin() {
        let def = parse_one("fn p() do print(:hello) end");
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![], ret: LowerTy::Nil },
            &HashMap::new(),
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
        assert_eq!(r.builtin_imports, vec!["fz_print_atom"]);
        // Atom was interned in the shared runtime table.
        assert!(atoms.names.iter().any(|n| n == "hello"));
    }

    #[test]
    fn lowers_print_nil_with_zero_args() {
        let def = parse_one("fn p() do print(nil) end");
        let mut atoms = AtomInterner::default();
        let r = lower_fn(
            &def,
            &FnSig { params: vec![], ret: LowerTy::Nil },
            &HashMap::new(),
            &mut atoms,
        )
        .expect("lower");
        verify(&r.func).expect("verify");
        assert_eq!(r.builtin_imports, vec!["fz_print_nil"]);
    }

    #[test]
    fn rejects_print_of_tuple() {
        let def = parse_one("fn p(t) do print(t) end");
        let mut atoms = AtomInterner::default();
        let res = lower_fn(
            &def,
            &FnSig {
                params: vec![LowerTy::Tuple(vec![ty_i64(), ty_i64()])],
                ret: LowerTy::Nil,
            },
            &HashMap::new(),
            &mut atoms,
        );
        assert!(matches!(res, Err(LowerError::Unsupported(_))));
    }

    #[test]
    fn atom_interner_is_local_and_sequential() {
        let def = parse_one("fn p() do print(:hello) end");
        let mut atoms = AtomInterner::default();
        let _ = lower_fn(
            &def,
            &FnSig { params: vec![], ret: LowerTy::Nil },
            &HashMap::new(),
            &mut atoms,
        )
        .unwrap();
        // Fresh interner → :hello gets id 0 regardless of any prior runtime
        // intern state in the process.
        assert_eq!(atoms.names, vec!["hello".to_string()]);
    }

    #[test]
    fn rejects_type_mismatch() {
        let def = parse_one("fn bad(n) do n + 1 end");
        let mut atoms = AtomInterner::default();
        // Claim float param/return; body is int — should mismatch.
        let res = lower_fn(
            &def,
            &FnSig { params: vec![ty_f64()], ret: ty_f64() },
            &HashMap::new(),
            &mut atoms,
        );
        assert!(matches!(res, Err(LowerError::TypeMismatch(_))));
    }
}
