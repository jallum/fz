use super::*;
use crate::ast::{
    BinOp as AstBinOp, BitField as AstBitField, BitSize as AstBitSize, Expr, FnDef, MatchClause,
    Pattern, Spanned, UnOp as AstUnOp, WithBinding,
};
use crate::diag::Span;
use crate::fz_ir::{
    BinOp, BitFieldIr, BitSizeIr, BlockId, Const, ExternArg, ExternDecl, ExternTy, FnBuilder, Prim,
    Term, UnOp, Var,
};

use crate::pattern_matrix::{BodyId, PatternMatrix, Row};
pub(crate) fn lower_fn<T: crate::types::Types<Ty = crate::types::Ty>>(
    ctx: &mut LowerCtx,
    t: &mut T,
    fn_def: &FnDef,
    category: crate::fz_ir::FnCategory,
) -> Result<(), LowerError> {
    if fn_def.is_macro {
        // Macros are consumed by expansion before lowering.
        return Ok(());
    }
    let arity = fn_def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
    let fn_id = *ctx
        .fns
        .get(&(fn_def.name.clone(), arity))
        .ok_or_else(|| LowerError::Unbound {
            span: fn_def.name_span,
            name: format!("fn {}/{}", fn_def.name, arity),
        })?;

    let owner_module = fn_def
        .name
        .rfind('.')
        .map(|i| fn_def.name[..i].to_string())
        .unwrap_or_default();
    ctx.current_owner_module = owner_module.clone();
    let mut builder = FnBuilder::new(fn_id, fn_def.name.clone())
        .with_category(category)
        .with_owner_module(owner_module);
    // Mint param vars for the entry block.
    let param_vars: Vec<Var> = (0..arity).map(|_| builder.fresh_var()).collect();
    let entry = builder.block(param_vars.clone());
    ctx.cur = Some(builder);
    ctx.cur_fn_id = Some(fn_id);
    ctx.fn_spans.insert(fn_id, fn_def.span);
    ctx.cur_block = Some(entry);
    ctx.env.clear();
    ctx.env_order.clear();

    // Pre-record param var metadata. The pattern walker overwrites with
    // the pattern's binding-site info if the pattern is `Var(n)`; here we
    // default to the clause's first param-pattern span so even
    // wildcard / tuple-destructured params have *some* source position.
    for (i, pv) in param_vars.iter().enumerate() {
        let pat_span = fn_def
            .clauses
            .first()
            .and_then(|c| c.params.get(i))
            .map(|p| p.span)
            .unwrap_or(Span::DUMMY);
        ctx.var_meta.insert((fn_id, *pv), (pat_span, String::new()));
    }

    ctx.terminated = false;
    if fn_def.clauses.len() == 1 {
        let clause = &fn_def.clauses[0];
        for (pv, (pat, annot)) in param_vars
            .iter()
            .zip(clause.params.iter().zip(clause.param_annotations.iter()))
        {
            if matches!(pat.node, Pattern::Wildcard) && annot.is_none() {
                ctx.cur_mut().mark_param_ignored(*pv);
            }
        }
        // Bind params via patterns; on fail, halt with :match_error.
        // Seal fail_block FIRST so CPS-split during body lowering can't orphan it.
        let fail_block = ctx.cur_mut().block(vec![]);
        ctx.cur_block = Some(fail_block);
        let me = ctx.atoms.intern("match_error");
        let mev = ctx.let_(Prim::Const(Const::Atom(me)));
        ctx.set_term(Term::Halt(mev));
        ctx.cur_block = Some(entry);

        let prev_origin = ctx.branch_origin;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        for (pv, pat) in param_vars.iter().zip(&clause.params) {
            lower_pattern_bind(ctx, *pv, pat, fail_block)?;
            // Record the pattern's span on the param Var if not yet named
            // by the pattern walker (e.g. tuple-destructured params).
            ctx.name_var(*pv, "", pat.span);
        }
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ParamGuard;
        emit_param_type_guards(ctx, t, clause, &param_vars, fail_block)?;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        if let Some(g) = &clause.guard {
            let guard_var = lower_expr(ctx, g, false)?;
            let body_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(guard_var, body_b, fail_block);
            ctx.cur_block = Some(body_b);
            ctx.terminated = false;
        }
        ctx.branch_origin = prev_origin;
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        if !ctx.terminated {
            ctx.set_term(Term::Return(result));
        }
    } else {
        lower_multi_clause(ctx, t, fn_def, &param_vars, entry)?;
    }

    let built = ctx.cur.take().unwrap().build();
    ctx.mb.add_fn(built);
    ctx.cur_block = None;
    Ok(())
}
pub(crate) fn bind_param_topname(ctx: &mut LowerCtx, pv: Var, pat: &Spanned<Pattern>) {
    let mut cur = pat;
    while let Pattern::As(name, inner) = &cur.node {
        ctx.bind(name, pv);
        cur = inner;
    }
    if let Pattern::Var(name) = &cur.node {
        ctx.bind(name, pv);
    }
}
pub(crate) fn lower_expr(
    ctx: &mut LowerCtx,
    e: &Spanned<Expr>,
    is_tail: bool,
) -> Result<Var, LowerError> {
    let sp = e.span;
    match &e.node {
        Expr::Int(n) => Ok(ctx.let_at(Prim::Const(Const::Int(*n)), sp)),
        Expr::Float(x) => Ok(ctx.let_at(Prim::Const(Const::Float(*x)), sp)),
        Expr::Binary(bytes) => {
            // fz-axu.11 (L3) — every `"…"` literal lowers to a
            // `utf8`-branded const bitstring. UTF-8 validity is a lexer
            // invariant (see read_quoted_binary_bytes in src/lexer.rs); raw
            // bytes flow through `<<…>>` syntax instead.
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_at(Prim::ConstBitstring(bytes.clone(), bit_len), sp);
            Ok(ctx.let_at(Prim::Brand(bs, "utf8".to_string()), sp))
        }
        Expr::Atom(s) => {
            let id = ctx.atoms.intern(s);
            Ok(ctx.let_at(Prim::Const(Const::Atom(id)), sp))
        }
        Expr::Bool(true) => Ok(ctx.let_at(Prim::Const(Const::True), sp)),
        Expr::Bool(false) => Ok(ctx.let_at(Prim::Const(Const::False), sp)),
        Expr::Nil => Ok(ctx.let_at(Prim::Const(Const::Nil), sp)),

        Expr::Var(name) => {
            if let Some(v) = ctx.lookup(name) {
                return Ok(v);
            }
            // Fall back: bare top-level fn name used as a value -> 0-captured
            // closure pointing at the fn's IR id. With no explicit arity in
            // the bare-name form, picks the first matching name (overloads
            // disambiguate via the explicit `&name/arity` form — see the
            // `Expr::FnRef` arm).
            if let Some((_, fn_id)) = ctx
                .fns
                .iter()
                .find(|((n, _), _)| n == name)
                .map(|(k, v)| (k.clone(), *v))
            {
                return Ok(ctx.let_at(Prim::make_closure(sp, fn_id, vec![]), sp));
            }
            Err(LowerError::Unbound {
                span: sp,
                name: name.clone(),
            })
        }

        // fz-swt.5: `&name/arity` — explicit, arity-aware fn reference.
        // Direct (name, arity) lookup in the same fn map Call uses, so an
        // overloaded name resolves unambiguously to the requested clause.
        Expr::FnRef { name, arity } => {
            if let Some(&fn_id) = ctx.fns.get(&(name.clone(), *arity)) {
                return Ok(ctx.let_at(Prim::make_closure(sp, fn_id, vec![]), sp));
            }
            // fz-eol — `&libc::close/1`: synthesize (and cache) a top-level
            // wrapper fn that forwards its args to the named extern, then
            // return a closure pointing at that wrapper.
            if let Some(eid) = ctx.externs.lookup(name) {
                let decl = ctx
                    .extern_decls
                    .iter()
                    .find(|d| d.id == eid)
                    .expect("extern table out of sync with extern_decls");
                if decl.params.len() == *arity {
                    let fn_id = ctx.ensure_extern_wrapper(eid);
                    return Ok(ctx.let_at(Prim::make_closure(sp, fn_id, vec![]), sp));
                }
            }
            Err(LowerError::Unbound {
                span: sp,
                name: format!("fn {}/{}", name, arity),
            })
        }

        Expr::BinOp(op, a, b) => {
            let va_raw = lower_expr(ctx, a, false)?;
            let park_a = ctx.park(va_raw);
            let vb = lower_expr(ctx, b, false)?;
            let va = ctx.unpark(&park_a);
            ctx.unbind(&park_a);
            let irop = lower_binop(*op, sp)?;
            Ok(ctx.let_at(Prim::BinOp(irop, va, vb), sp))
        }
        Expr::UnOp(op, x) => {
            let v = lower_expr(ctx, x, false)?;
            let irop = match op {
                AstUnOp::Neg => UnOp::Neg,
                AstUnOp::Not => UnOp::Not,
            };
            Ok(ctx.let_at(Prim::UnOp(irop, v), sp))
        }
        Expr::Ascribe(inner, _) => lower_expr(ctx, inner, is_tail),

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

        Expr::If(cond, then_e, else_opt) => lower_if(ctx, cond, then_e, else_opt, is_tail, sp),

        Expr::Match(pat, expr) => {
            let v = lower_expr(ctx, expr, false)?;
            let fail_block = ctx.cur_mut().block(vec![]);
            let prev_origin = ctx.branch_origin;
            ctx.branch_origin = crate::fz_ir::BranchOrigin::PatternBind;
            let res = lower_pattern_bind(ctx, v, pat, fail_block);
            ctx.branch_origin = prev_origin;
            res?;
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
            for n in &parks {
                ctx.unbind(n);
            }
            if let Some(n) = &tail_park {
                ctx.unbind(n);
            }
            Ok(ctx.let_(Prim::MakeList(vs, tail_v)))
        }
        Expr::Tuple(elems) => {
            let parks = lower_seq(ctx, elems)?;
            let vs: Vec<Var> = parks.iter().map(|n| ctx.unpark(n)).collect();
            for n in &parks {
                ctx.unbind(n);
            }
            Ok(ctx.let_(Prim::MakeTuple(vs)))
        }

        Expr::Call(target, args) => {
            // Lower arg exprs first; park each so they survive subsequent splits.
            let lowered_args = lower_call_args(ctx, args)?;
            let arg_vars: Vec<Var> = lowered_args.iter().map(|a| a.var).collect();
            // Resolve callee.
            let callee_name = match &target.node {
                Expr::Var(n) => n.clone(),
                _ => {
                    return Err(LowerError::Unsupported {
                        span: target.span,
                        what: "Call target other than Var (deferred)".into(),
                    });
                }
            };
            // Local closure value? (Shadows fn lookup if a local of the same name exists.)
            if let Some(local_var) = ctx.lookup(&callee_name) {
                if is_tail {
                    ctx.set_term_at(
                        Term::TailCallClosure {
                            ident: crate::fz_ir::CallsiteIdent::from_source(sp),
                            closure: local_var,
                            args: arg_vars,
                        },
                        sp,
                    );
                    ctx.terminated = true;
                    return Ok(Var(0));
                } else {
                    return cps_split_call_closure(ctx, local_var, arg_vars, sp);
                }
            }
            // fz-ul4.19.3: `receive(...)` is a Term, not a Prim — it's a
            // scheduler-mediated yield point. After CPS-style splitting,
            // it has the same continuation shape as Term::Call but no
            // callee fn.
            if callee_name == "receive" {
                if !arg_vars.is_empty() {
                    return Err(LowerError::Unsupported {
                        span: sp,
                        what: format!("receive/{} not supported (use receive/0)", arg_vars.len()),
                    });
                }
                if is_tail {
                    // Tail receive: the received message becomes the fn's
                    // return value. Lower as receive into a synthetic
                    // continuation that just Returns its arg.
                    return cps_split_receive(ctx, sp, /* tail */ true);
                }
                return cps_split_receive(ctx, sp, /* tail */ false);
            }
            // fz-ul4.29.9 / fz-ext.7 — spawn is special: wrap the closure arg
            // in fz_spawn_thunk before dispatching to fz_spawn / fz_spawn_opt.
            // This must be checked before the generic ExternTable lookup so that
            // `spawn` (user-facing name) resolves to the thunk-wrapped fz_spawn
            // extern, not a non-existent user fn.
            if callee_name == "spawn" && (arg_vars.len() == 1 || arg_vars.len() == 2) {
                let thunk_id = ctx.ensure_spawn_thunk();
                let wrapper = ctx.let_at(Prim::make_closure(sp, thunk_id, vec![arg_vars[0]]), sp);
                let mut new_args = vec![wrapper];
                new_args.extend_from_slice(&arg_vars[1..]);
                let sym = if arg_vars.len() == 1 {
                    "fz_spawn"
                } else {
                    "fz_spawn_opt"
                };
                let eid = ctx
                    .externs
                    .lookup(sym)
                    .expect("fz_spawn/fz_spawn_opt must be in runtime.fz");
                let decl = ctx
                    .extern_decls
                    .iter()
                    .find(|d| d.id == eid)
                    .expect("ExternTable entry must have matching ExternDecl");
                let extern_args =
                    extern_args_for_call(decl, sym, new_args, vec![None; decl.params.len()], sp)?;
                return Ok(ctx.let_at(Prim::Extern(eid, extern_args), sp));
            }
            // Extern (runtime.fz / user-declared `extern "C" fn`)?
            if let Some(eid) = ctx.externs.lookup(&callee_name) {
                let decl = ctx
                    .extern_decls
                    .iter()
                    .find(|d| d.id == eid)
                    .expect("ExternTable entry must have matching ExternDecl");
                let extern_args = extern_args_for_call(
                    decl,
                    &callee_name,
                    arg_vars,
                    lowered_args.into_iter().map(|a| a.ascription).collect(),
                    sp,
                )?;
                return Ok(ctx.let_at(Prim::Extern(eid, extern_args), sp));
            }
            let arity = arg_vars.len();
            let callee =
                *ctx.fns
                    .get(&(callee_name.clone(), arity))
                    .ok_or_else(|| LowerError::Unbound {
                        span: target.span,
                        name: format!("fn {}/{}", callee_name, arity),
                    })?;
            if is_tail {
                ctx.set_term_at(
                    Term::TailCall {
                        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                        callee,
                        args: arg_vars,
                        is_back_edge: false, // annotate_back_edges fills this in post-lowering
                    },
                    sp,
                );
                ctx.terminated = true;
                Ok(Var(0))
            } else {
                cps_split_call(ctx, callee, arg_vars, sp)
            }
        }

        Expr::Lambda(params, body) => lower_lambda(ctx, params, body, sp),

        Expr::Case(Some(subject), clauses) => lower_case(ctx, subject, clauses, is_tail, sp),
        Expr::Case(None, _) => Err(LowerError::Unsupported {
            span: sp,
            what: "headless case must appear on the right side of a pipe".into(),
        }),
        Expr::Cond(arms) => lower_cond(ctx, arms, is_tail, sp),
        Expr::With(bindings, body, else_clauses) => {
            lower_with(ctx, bindings, body, else_clauses, is_tail, sp)
        }
        // fz-yxs — selective receive: lower into Term::ReceiveMatched with
        // per-clause body/guard fns and an optional after body fn.
        Expr::Receive { clauses, after } => {
            lower_receive(ctx, clauses, after.as_deref(), is_tail, sp)
        }
        Expr::Map(entries) => lower_map(ctx, entries),
        Expr::MapUpdate(base, entries) => lower_map_update(ctx, base, entries),
        Expr::Index(map, key) => lower_index(ctx, map, key),
        Expr::Bitstring(fields) => lower_bitstring_expr(ctx, fields),
        Expr::Quote(_) => Err(LowerError::PostExpansionNode {
            span: sp,
            what: "Quote".into(),
        }),
        Expr::Unquote(_) => Err(LowerError::PostExpansionNode {
            span: sp,
            what: "Unquote".into(),
        }),
    }
    // Note: lower_if is implemented as a separate function below to keep the
    // var/block dance clean; the unreachable!() above is replaced via a
    // direct branch into it before this match.
}
/// Lower a sequence of subexpressions, parking each result in env so that any
/// CPS-split triggered by a later element rebinds the earlier results into the
/// continuation. Caller unparks/unbinds.
pub(crate) fn lower_seq(
    ctx: &mut LowerCtx,
    exprs: &[Spanned<Expr>],
) -> Result<Vec<String>, LowerError> {
    let mut parks = Vec::with_capacity(exprs.len());
    for e in exprs {
        let v = lower_expr(ctx, e, false)?;
        parks.push(ctx.park(v));
    }
    Ok(parks)
}

struct LoweredCallArg {
    var: Var,
    ascription: Option<crate::ast::TypeExprBody>,
}

fn lower_call_args(
    ctx: &mut LowerCtx,
    args: &[Spanned<Expr>],
) -> Result<Vec<LoweredCallArg>, LowerError> {
    let mut parks = Vec::with_capacity(args.len());
    let mut ascriptions = Vec::with_capacity(args.len());
    for arg in args {
        let (expr, ascription) = match &arg.node {
            Expr::Ascribe(inner, ty) => (inner.as_ref(), Some(ty.clone())),
            _ => (arg, None),
        };
        let v = lower_expr(ctx, expr, false)?;
        parks.push(ctx.park(v));
        ascriptions.push(ascription);
    }
    let mut out = Vec::with_capacity(parks.len());
    for (park, ascription) in parks.iter().zip(ascriptions) {
        out.push(LoweredCallArg {
            var: ctx.unpark(park),
            ascription,
        });
    }
    for park in &parks {
        ctx.unbind(park);
    }
    Ok(out)
}

fn extern_args_for_call(
    decl: &ExternDecl,
    callee_name: &str,
    arg_vars: Vec<Var>,
    ascriptions: Vec<Option<crate::ast::TypeExprBody>>,
    span: Span,
) -> Result<Vec<ExternArg>, LowerError> {
    let fixed = decl.params.len();
    let actual = arg_vars.len();
    if (!decl.variadic && actual != fixed) || (decl.variadic && actual < fixed) {
        let expected = if decl.variadic {
            format!("at least {}", fixed)
        } else {
            fixed.to_string()
        };
        return Err(LowerError::Unsupported {
            span,
            what: format!(
                "extern \"C\" fn {}/{} called with {} arg(s)",
                callee_name, expected, actual
            ),
        });
    }

    arg_vars
        .into_iter()
        .zip(ascriptions)
        .enumerate()
        .map(|(i, (var, ascription))| {
            if i < fixed {
                let fixed_ty = decl.params[i];
                if let Some(body) = ascription {
                    let ascribed = extern_ty_from_ascription(&body, span)?;
                    if ascribed != fixed_ty {
                        return Err(LowerError::Unsupported {
                            span,
                            what: format!(
                                "extern \"C\" fn {} arg {} ascribed as {:?}, declared as {:?}",
                                callee_name,
                                i + 1,
                                ascribed,
                                fixed_ty
                            ),
                        });
                    }
                }
                Ok(ExternArg::fixed(var, fixed_ty))
            } else if let Some(body) = ascription {
                Ok(ExternArg::ascribed(
                    var,
                    extern_ty_from_ascription(&body, span)?,
                ))
            } else {
                Ok(ExternArg::auto(var))
            }
        })
        .collect()
}

fn extern_ty_from_ascription(
    body: &crate::ast::TypeExprBody,
    span: Span,
) -> Result<ExternTy, LowerError> {
    let Some(tok) = body.0.first().map(|t| &t.tok) else {
        return Err(LowerError::Unsupported {
            span,
            what: "empty extern call-arg ascription".into(),
        });
    };
    let name = match tok {
        crate::lexer::Tok::Ident(name) | crate::lexer::Tok::Upper(name) => name.as_str(),
        crate::lexer::Tok::Nil => "nil",
        _ => {
            return Err(LowerError::Unsupported {
                span,
                what: format!("unsupported extern call-arg ascription token {:?}", tok),
            });
        }
    };
    super::extern_table::extern_ty_from_name(name).ok_or_else(|| LowerError::Unsupported {
        span,
        what: format!("unknown extern call-arg ascription `{}`", name),
    })
}

pub(super) fn lower_binop(op: AstBinOp, span: Span) -> Result<BinOp, LowerError> {
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
            return Err(LowerError::Unsupported {
                span,
                what: "BinOp::Pipe should be desugared before lowering".into(),
            });
        }
        AstBinOp::Cons => {
            // a | b — handled at construction sites (List with tail).
            return Err(LowerError::Unsupported {
                span,
                what: "BinOp::Cons should be desugared into List with tail".into(),
            });
        }
    })
}

/// Lower a pattern that matches `subject_var`. On match failure, jump to
/// `fail_block`. After a successful match, the current block is "all matched
/// so far"; `lower_pattern_bind` may split into new blocks via If terminators.
pub(crate) fn lower_pattern_bind(
    ctx: &mut LowerCtx,
    subject: Var,
    spat: &Spanned<Pattern>,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let pat_span = spat.span;
    match &spat.node {
        Pattern::Wildcard => Ok(()),
        Pattern::Var(name) => {
            ctx.bind(name, subject);
            // Record `subject`'s source name + binding-site span so
            // diagnostics can render the user's identifier later.
            ctx.name_var(subject, name, pat_span);
            Ok(())
        }
        // fz-5vj — `^name` pinned pattern. Lowering lands in fz-yxs (E2)
        // alongside Term::ReceiveMatched. Outside `receive` the typer
        // should already have rejected `^name` per the receive-only
        // syntactic role; reaching here is a planning bug.
        Pattern::Pinned(name) => Err(LowerError::Unsupported {
            span: pat_span,
            what: format!("pinned pattern `^{}` lowering lands in fz-yxs (E2)", name),
        }),
        Pattern::Int(n) => emit_eq_check(ctx, subject, Prim::Const(Const::Int(*n)), fail_block),
        Pattern::Float(x) => emit_eq_check(ctx, subject, Prim::Const(Const::Float(*x)), fail_block),
        Pattern::Binary(bytes) => {
            // fz-axu.11 (L3) — quoted binary patterns lower the same as
            // Expr::Binary: utf8-branded const bitstring, equality-check
            // against the subject. UTF-8 validity is a lexer invariant.
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            let lit_v = ctx.let_(Prim::Brand(bs, "utf8".to_string()));
            let eq_v = ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit_v));
            let cont_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(eq_v, cont_b, fail_block);
            ctx.cur_block = Some(cont_b);
            Ok(())
        }
        Pattern::Atom(s) => {
            let id = ctx.atoms.intern(s);
            emit_eq_check(ctx, subject, Prim::Const(Const::Atom(id)), fail_block)
        }
        Pattern::Bool(true) => emit_eq_check(ctx, subject, Prim::Const(Const::True), fail_block),
        Pattern::Bool(false) => emit_eq_check(ctx, subject, Prim::Const(Const::False), fail_block),
        Pattern::Nil => emit_eq_check(ctx, subject, Prim::Const(Const::Nil), fail_block),
        Pattern::As(name, inner) => {
            ctx.bind(name, subject);
            ctx.name_var(subject, name, pat_span);
            lower_pattern_bind(ctx, subject, inner, fail_block)
        }
        Pattern::Tuple(elems) => match_tuple(ctx, subject, elems, fail_block),
        Pattern::List(elems, tail) => match_list(ctx, subject, elems, tail.as_deref(), fail_block),
        Pattern::Map(entries) => match_map(ctx, subject, entries, fail_block),
        Pattern::Bitstring(fields) => match_bitstring(ctx, subject, fields, fail_block),
    }
}

/// fz-ul4.43.H — Constructor pattern helpers. Each emits the IR for a
/// single subject against the constructor pattern. On match success, the
/// helper leaves ctx.cur_block at a "success" block where any bindings
/// from inner sub-patterns are in env and the caller continues lowering
/// inline. On match failure, control jumps to `fail_block` via Term::If
/// terminators along the way.
///
/// Shared by `lower_pattern_bind` and list-cons lowering.
pub(super) fn match_tuple(
    ctx: &mut LowerCtx,
    subject: Var,
    elems: &[Spanned<Pattern>],
    fail_block: BlockId,
) -> Result<(), LowerError> {
    // fz-ben — TypeTest tuple-of-arity-N before projecting fields. For
    // non-tuple subjects (e.g. an atom flowing into `{:ok, x} <- :err`),
    // projection would read heap garbage without the type test gate.
    let n = elems.len();
    let tuple_ty = concrete_any_tuple(n);
    let test = ctx.let_(Prim::TypeTest(subject, Box::new(tuple_ty)));
    let project_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(test, project_b, fail_block);
    ctx.cur_block = Some(project_b);
    for (i, elem_pat) in elems.iter().enumerate() {
        let fv = ctx.let_(Prim::TupleField(subject, i as u32));
        lower_pattern_bind(ctx, fv, elem_pat, fail_block)?;
    }
    Ok(())
}

pub(super) fn match_list(
    ctx: &mut LowerCtx,
    subject: Var,
    elems: &[Spanned<Pattern>],
    tail: Option<&Spanned<Pattern>>,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let mut cur = subject;
    for elem_pat in elems {
        let isnil = ctx.let_(Prim::IsEmptyList(cur));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(isnil, fail_block, cont_b);
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
            let isnil = ctx.let_(Prim::IsEmptyList(cur));
            let cont_b = ctx.cur_mut().block(vec![]);
            ctx.set_if_term(isnil, cont_b, fail_block);
            ctx.cur_block = Some(cont_b);
            Ok(())
        }
    }
}

pub(super) fn match_map(
    ctx: &mut LowerCtx,
    subject: Var,
    entries: &[(Spanned<Pattern>, Spanned<Pattern>)],
    fail_block: BlockId,
) -> Result<(), LowerError> {
    for (key_pat, val_pat) in entries {
        let key_var = lower_pattern_as_key_expr(ctx, key_pat)?;
        let got = ctx.let_(Prim::MapGet(subject, key_var));
        let nil_v = ctx.let_(Prim::Const(Const::Nil));
        let is_nil = ctx.let_(Prim::BinOp(BinOp::Eq, got, nil_v));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(is_nil, fail_block, cont_b);
        ctx.cur_block = Some(cont_b);
        lower_pattern_bind(ctx, got, val_pat, fail_block)?;
    }
    Ok(())
}

pub(super) fn match_bitstring(
    ctx: &mut LowerCtx,
    subject: Var,
    fields: &[AstBitField<Spanned<Pattern>>],
    fail_block: BlockId,
) -> Result<(), LowerError> {
    // Initialize a reader, then per field: read with size resolved against
    // any IR vars bound by EARLIER fields' patterns; check success;
    // pattern-bind the extracted value (which may bind names visible to
    // later fields' size resolution); thread the new reader. Finally
    // require the reader is fully consumed.
    let mut reader = ctx.let_(Prim::BitReaderInit(subject));
    let n = fields.len();
    for (i, field) in fields.iter().enumerate() {
        let is_last = i + 1 == n;
        let size_ir = lower_bit_size(ctx, &field.spec.size, field.value.span)?;
        let result = ctx.let_(Prim::BitReadField {
            reader,
            ty: field.spec.ty,
            size: size_ir,
            endian: field.spec.endian,
            signed: field.spec.signed,
            unit: field.spec.unit,
            is_last,
        });
        let ok = ctx.let_(Prim::TupleField(result, 0));
        let cont_b = ctx.cur_mut().block(vec![]);
        ctx.set_if_term(ok, cont_b, fail_block);
        ctx.cur_block = Some(cont_b);
        let extracted = ctx.let_(Prim::TupleField(result, 1));
        let next_reader = ctx.let_(Prim::TupleField(result, 2));
        // Park reader so any CPS-split inside the pattern keeps it.
        let r_park = ctx.park(next_reader);
        lower_pattern_bind(ctx, extracted, &field.value, fail_block)?;
        reader = ctx.unpark(&r_park);
        ctx.unbind(&r_park);
    }
    let done = ctx.let_(Prim::BitReaderDone(reader));
    let cont_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(done, cont_b, fail_block);
    ctx.cur_block = Some(cont_b);
    Ok(())
}

/// Lower a Pattern that represents a map key. Map keys in patterns are
/// constants (atoms, ints, strings, ...) — no var-binding allowed.
pub(super) fn lower_pattern_as_key_expr(
    ctx: &mut LowerCtx,
    sp: &Spanned<Pattern>,
) -> Result<Var, LowerError> {
    Ok(match &sp.node {
        Pattern::Int(n) => ctx.let_(Prim::Const(Const::Int(*n))),
        Pattern::Float(x) => ctx.let_(Prim::Const(Const::Float(*x))),
        Pattern::Binary(bytes) => {
            // fz-axu.11 (L3) — map-key pattern: same lowering as
            // Expr::Binary / Pattern::Binary. UTF-8 validity is a lexer
            // invariant (see read_quoted_binary_bytes in src/lexer.rs).
            let bit_len = (bytes.len() * 8) as u64;
            let bs = ctx.let_(Prim::ConstBitstring(bytes.clone(), bit_len));
            ctx.let_(Prim::Brand(bs, "utf8".to_string()))
        }
        Pattern::Atom(s) => {
            let id = ctx.atoms.intern(s);
            ctx.let_(Prim::Const(Const::Atom(id)))
        }
        Pattern::Bool(true) => ctx.let_(Prim::Const(Const::True)),
        Pattern::Bool(false) => ctx.let_(Prim::Const(Const::False)),
        Pattern::Nil => ctx.let_(Prim::Const(Const::Nil)),
        other => {
            return Err(LowerError::Unsupported {
                span: sp.span,
                what: format!(
                    "map-pattern keys must be constants, got {:?}",
                    std::mem::discriminant(other)
                ),
            });
        }
    })
}

pub(super) fn lower_bit_size(
    ctx: &LowerCtx,
    size: &Option<AstBitSize>,
    span: Span,
) -> Result<Option<BitSizeIr>, LowerError> {
    Ok(match size {
        None => None,
        Some(AstBitSize::Literal(n)) => Some(BitSizeIr::Literal(*n)),
        Some(AstBitSize::Var(name)) => {
            let v = ctx.lookup(name).ok_or_else(|| LowerError::Unbound {
                span,
                name: format!("bit size var {}", name),
            })?;
            Some(BitSizeIr::Var(v))
        }
    })
}

pub(super) fn emit_eq_check(
    ctx: &mut LowerCtx,
    subject: Var,
    lit: Prim,
    fail_block: BlockId,
) -> Result<(), LowerError> {
    let lit_v = ctx.let_(lit);
    let eq_v = ctx.let_(Prim::BinOp(BinOp::Eq, subject, lit_v));
    let cont_b = ctx.cur_mut().block(vec![]);
    ctx.set_if_term(eq_v, cont_b, fail_block);
    ctx.cur_block = Some(cont_b);
    Ok(())
}

// ----------------------------------------------------------------------
// Expression lowerings added in fz-ul4.11.17
// ----------------------------------------------------------------------

pub(super) fn lower_map(
    ctx: &mut LowerCtx,
    entries: &[(Spanned<Expr>, Spanned<Expr>)],
) -> Result<Var, LowerError> {
    let mut key_parks = Vec::with_capacity(entries.len());
    let mut val_parks = Vec::with_capacity(entries.len());
    for (k, v) in entries {
        let kv = lower_expr(ctx, k, false)?;
        key_parks.push(ctx.park(kv));
        let vv = lower_expr(ctx, v, false)?;
        val_parks.push(ctx.park(vv));
    }
    let pairs: Vec<(Var, Var)> = key_parks
        .iter()
        .zip(val_parks.iter())
        .map(|(kn, vn)| (ctx.unpark(kn), ctx.unpark(vn)))
        .collect();
    for n in &key_parks {
        ctx.unbind(n);
    }
    for n in &val_parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MakeMap(pairs)))
}

pub(super) fn lower_map_update(
    ctx: &mut LowerCtx,
    base: &Spanned<Expr>,
    entries: &[(Spanned<Expr>, Spanned<Expr>)],
) -> Result<Var, LowerError> {
    let bv = lower_expr(ctx, base, false)?;
    let base_park = ctx.park(bv);
    let mut key_parks = Vec::with_capacity(entries.len());
    let mut val_parks = Vec::with_capacity(entries.len());
    for (k, v) in entries {
        let kv = lower_expr(ctx, k, false)?;
        key_parks.push(ctx.park(kv));
        let vv = lower_expr(ctx, v, false)?;
        val_parks.push(ctx.park(vv));
    }
    let base_v = ctx.unpark(&base_park);
    let pairs: Vec<(Var, Var)> = key_parks
        .iter()
        .zip(val_parks.iter())
        .map(|(kn, vn)| (ctx.unpark(kn), ctx.unpark(vn)))
        .collect();
    ctx.unbind(&base_park);
    for n in &key_parks {
        ctx.unbind(n);
    }
    for n in &val_parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MapUpdate(base_v, pairs)))
}

pub(super) fn lower_index(
    ctx: &mut LowerCtx,
    m: &Spanned<Expr>,
    k: &Spanned<Expr>,
) -> Result<Var, LowerError> {
    let mv = lower_expr(ctx, m, false)?;
    let m_park = ctx.park(mv);
    let kv = lower_expr(ctx, k, false)?;
    let m_resolved = ctx.unpark(&m_park);
    ctx.unbind(&m_park);
    Ok(ctx.let_(Prim::MapGet(m_resolved, kv)))
}

pub(super) fn lower_bitstring_expr(
    ctx: &mut LowerCtx,
    fields: &[AstBitField<Spanned<Expr>>],
) -> Result<Var, LowerError> {
    // Lower each field's value expression, parking results so any CPS-split in
    // a later field's value still rebinds earlier ones.
    let mut value_parks = Vec::with_capacity(fields.len());
    for f in fields {
        let v = lower_expr(ctx, &f.value, false)?;
        value_parks.push(ctx.park(v));
    }
    let mut ir_fields: Vec<BitFieldIr> = Vec::with_capacity(fields.len());
    for (f, vn) in fields.iter().zip(value_parks.iter()) {
        ir_fields.push(BitFieldIr {
            value: ctx.unpark(vn),
            ty: f.spec.ty,
            size: lower_bit_size(ctx, &f.spec.size, f.value.span)?,
            endian: f.spec.endian,
            signed: f.spec.signed,
            unit: f.spec.unit,
        });
    }
    for n in &value_parks {
        ctx.unbind(n);
    }
    Ok(ctx.let_(Prim::MakeBitstring(ir_fields)))
}
pub(super) fn lower_case(
    ctx: &mut LowerCtx,
    subject: &Spanned<Expr>,
    clauses: &[MatchClause],
    is_tail: bool,
    case_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.3 — Per-clause + optional join continuation fns. Same shape
    // as lower_if's fix from fz-duq.2, generalized to N clauses with
    // pattern bind on each.
    //
    // Outer fn: lowers subject, allocates try_blocks + fail_block. The
    // try_blocks form a fail-cascade chain (pattern mismatch → next try
    // block; final mismatch → fail_block → Halt(:case_clause)). At the
    // end of each try_block (after pattern bind succeeded), the block
    // TailCalls a per-clause continuation fn passing the current env
    // (outer + pattern-bound names). The clause body lives in its own fn
    // so any internal CPS-split stays confined to that clause's lineage.
    //
    // The clause-fn captures are snapshotted *after* pattern bind so the
    // newly-bound pattern names are included.
    // fz-ul4.43.F — PatternMatrix dispatch replaces the per-clause try_blocks
    // cascade. body_cb mints per-clause cont fns (case bodies always
    // wrap; no inline fast path here unlike multi_clause). join_opt
    // handles non-tail return-value plumbing.
    if clauses.is_empty() {
        return Err(LowerError::Unsupported {
            span: subject.span,
            what: "case with no clauses".into(),
        });
    }
    let sv = lower_expr(ctx, subject, false)?;

    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "case_join",
            case_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    let fail_block = ctx.cur_mut().block(vec![]);
    let saved_block = ctx.cur_block();
    ctx.cur_block = Some(fail_block);
    let cc = ctx.atoms.intern("case_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(cc)));
    ctx.set_term(Term::Halt(v));
    ctx.cur_block = Some(saved_block);

    let matrix_entry = ctx.cur_mut().block(vec![]);
    ctx.set_term(Term::Goto(matrix_entry, vec![]));
    ctx.cur_block = Some(matrix_entry);
    ctx.terminated = false;

    let pattern_matrix = PatternMatrix {
        subjects: vec![sv],
        rows: clauses
            .iter()
            .enumerate()
            .map(|(i, c)| Row {
                patterns: vec![c.pattern.clone()],
                preconditions: Vec::new(),
                bindings: Vec::new(),
                guard: c.guard.clone(),
                body_id: i as BodyId,
            })
            .collect(),
    };

    let saved_env = ctx.env.clone();
    let saved_order = ctx.env_order.clone();

    let mut clause_conts: Vec<Option<ContFn>> = (0..clauses.len()).map(|_| None).collect();
    let prev_origin = ctx.branch_origin;
    ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
    {
        let clauses_ref = clauses;
        let clause_conts_ref = &mut clause_conts;
        let saved_env_ref = &saved_env;
        let saved_order_ref = &saved_order;
        let mut cb = |ctx: &mut LowerCtx,
                      body_id: BodyId,
                      bindings: Vec<(String, Var)>,
                      _preconds: Vec<(Var, crate::types::Ty)>,
                      guard: Option<crate::ast::Spanned<crate::ast::Expr>>,
                      fall_block: BlockId|
         -> Result<(), LowerError> {
            let i = body_id as usize;
            let clause = &clauses_ref[i];
            ctx.env = saved_env_ref.clone();
            ctx.env_order = saved_order_ref.clone();
            for (name, var) in &bindings {
                ctx.bind(name, *var);
            }
            if let Some(g) = &guard {
                let guard_var = lower_expr(ctx, g, false)?;
                let body_b = ctx.cur_mut().block(vec![]);
                ctx.set_if_term(guard_var, body_b, fall_block);
                ctx.cur_block = Some(body_b);
                ctx.terminated = false;
            }
            let clause_cont = mint_cont_fn(
                ctx,
                format!("case_clause_{}", i),
                clause.span,
                crate::fz_ir::FnCategory::ControlFlowCont,
            );
            let captures = ctx.visible_locals();
            let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
            ctx.set_term(Term::TailCall {
                ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                callee: clause_cont.id,
                args: capture_vars,
                is_back_edge: false,
            });
            ctx.terminated = true;
            clause_conts_ref[i] = Some(clause_cont);
            Ok(())
        };
        let result = lower_pattern_matrix_to_current_fn(ctx, pattern_matrix, fail_block, &mut cb);
        ctx.branch_origin = prev_origin;
        result?;
    }

    for (i, clause) in clauses.iter().enumerate() {
        let Some(cont) = clause_conts[i].clone() else {
            continue;
        };
        let _ = switch_to_cont_fn(ctx, &cont, 0);
        let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}

pub(super) fn lower_cond(
    ctx: &mut LowerCtx,
    arms: &[(Spanned<Expr>, Spanned<Expr>)],
    is_tail: bool,
    cond_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.4 — Per-arm continuation fns. Each arm fn evaluates its test
    // and dispatches: true → lower body, finalize; false → TailCall the
    // next arm fn (or the fail fn for the last arm). Because tests in
    // cond can themselves contain calls (unlike `case` pattern bind),
    // wrapping the entire arm in its own fn confines arm-internal
    // CPS-splits — fixing the latent test-side analogue of fz-84m as well
    // as the body side.
    //
    // The outer fn TailCalls the first arm. fail_cont halts `:cond_clause`.
    if arms.is_empty() {
        let cc = ctx.atoms.intern("cond_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.terminated = true;
        return Ok(Var(0));
    }

    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "cond_join",
            cond_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // Per-arm cont fns + fail cont.
    let arm_conts: Vec<ContFn> = (0..arms.len())
        .map(|i| {
            mint_cont_fn(
                ctx,
                format!("cond_arm_{}", i),
                arms[i].0.span,
                crate::fz_ir::FnCategory::ControlFlowCont,
            )
        })
        .collect();
    let fail_cont = mint_cont_fn(
        ctx,
        "cond_fail",
        cond_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );

    // Outer fn: TailCall first arm.
    let captures = ctx.visible_locals();
    let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
    ctx.set_term(Term::TailCall {
        ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
        callee: arm_conts[0].id,
        args: capture_vars,
        is_back_edge: false,
    });

    // Build each arm fn.
    for (i, (test, body)) in arms.iter().enumerate() {
        let next_id = arm_conts.get(i + 1).map(|c| c.id).unwrap_or(fail_cont.id);
        let _ = switch_to_cont_fn(ctx, &arm_conts[i], 0);
        let cv = lower_expr(ctx, test, false)?;

        // body_b + fall_b in whatever fn ctx.cur is now (arm_conts[i] or
        // a CPS-split descendant if the test contained a non-tail call).
        let body_b = ctx.cur_mut().block(vec![]);
        let fall_b = ctx.cur_mut().block(vec![]);
        let prev_origin = ctx.branch_origin;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        ctx.set_if_term(cv, body_b, fall_b);
        ctx.branch_origin = prev_origin;

        // fall_b: TailCall next arm (or fail). Captures are the current
        // env, which includes the outer captures (rebound into the arm fn
        // or its CPS-split descendant) plus any temps from test lowering.
        let fall_captures = ctx.visible_locals();
        let fall_capture_vars: Vec<Var> = fall_captures.iter().map(|(_, v)| *v).collect();
        ctx.cur_block = Some(fall_b);
        ctx.set_term(Term::TailCall {
            ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
            callee: next_id,
            args: fall_capture_vars,
            is_back_edge: false,
        });

        // body_b: lower the body inline, finalize.
        ctx.cur_block = Some(body_b);
        ctx.terminated = false;
        let result = lower_expr(ctx, body, /* is_tail */ true)?;
        finalize_arm(ctx, result, join_opt.as_ref());
    }

    // Build fail_cont: halt :cond_clause.
    let _ = switch_to_cont_fn(ctx, &fail_cont, 0);
    let cc = ctx.atoms.intern("cond_clause");
    let v = ctx.let_(Prim::Const(Const::Atom(cc)));
    ctx.set_term(Term::Halt(v));
    ctx.terminated = true;

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}
pub(super) fn lower_with(
    ctx: &mut LowerCtx,
    bindings: &[WithBinding],
    body: &Spanned<Expr>,
    else_clauses: &[MatchClause],
    is_tail: bool,
    with_span: Span,
) -> Result<Var, LowerError> {
    // fz-duq.4 — `with` lowers into:
    //   * Main path (in outer fn + CPS descendants): walk bindings.
    //     Each Match binding emits a per-binding `mismatch_b` block whose
    //     terminator TailCalls `with_fail_cont` (a continuation fn)
    //     carrying the unmatched value plus the outer captures.
    //   * `with_fail_cont` (cont fn): dispatches over else_clauses via
    //     try_blocks + per-else-clause body cont fns. No else_clauses →
    //     halt :with_clause.
    //   * Main body: lowered inline at the end of the main path; on
    //     fall-through (`!ctx.terminated`), finalize_arm emits either
    //     Return (tail) or TailCall(with_join_cont, ...).
    //
    // The old design used a single `join_b` block + `with_fail` block in
    // the outer fn; any CPS-split inside a binding/body/else-clause body
    // stranded those blocks in a finalized fn. Continuation-fn shape
    // makes the lowering robust to all CPS-split positions.

    let join_opt = if is_tail {
        None
    } else {
        Some(mint_cont_fn(
            ctx,
            "with_join",
            with_span,
            crate::fz_ir::FnCategory::ControlFlowCont,
        ))
    };

    // with_fail_cont: a continuation fn that receives (unmatched_value,
    // ...outer_captures). Minted now so we know its FnId before walking
    // bindings.
    let with_fail_cont = mint_cont_fn(
        ctx,
        "with_fail",
        with_span,
        crate::fz_ir::FnCategory::ControlFlowCont,
    );

    // -- Main path: walk bindings.
    for binding in bindings {
        match binding {
            WithBinding::Bare(e) => {
                lower_expr(ctx, e, false)?;
            }
            WithBinding::Match(pat, e) => {
                let v = lower_expr(ctx, e, false)?;
                // Park v so any CPS-split during pattern lowering rebinds it.
                let v_park = ctx.park(v);
                // Per-binding mismatch block — TailCalls with_fail_cont
                // with [unmatched, ...outer_captures]. Captures resolved
                // by name (with_fail_cont's outer_captured) from current
                // env, which may be a CPS-split descendant of outer.
                let mismatch_b = ctx.cur_mut().block(vec![]);
                let saved_blk = ctx.cur_block();
                ctx.cur_block = Some(mismatch_b);
                let v_in_mismatch = ctx.unpark(&v_park);
                let mut args = Vec::with_capacity(1 + with_fail_cont.outer_captured.len());
                args.push(v_in_mismatch);
                for (name, _) in &with_fail_cont.outer_captured {
                    let cv = ctx.env.get(name).copied().unwrap_or_else(|| {
                        panic!(
                            "lower_with: captured name `{}` not in env at mismatch",
                            name
                        )
                    });
                    args.push(cv);
                }
                ctx.set_term(Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                    callee: with_fail_cont.id,
                    args,
                    is_back_edge: false,
                });
                ctx.cur_block = Some(saved_blk);
                let v_resolved = ctx.unpark(&v_park);
                ctx.unbind(&v_park);
                let prev_origin = ctx.branch_origin;
                ctx.branch_origin = crate::fz_ir::BranchOrigin::PatternBind;
                let res = lower_pattern_bind(ctx, v_resolved, pat, mismatch_b);
                ctx.branch_origin = prev_origin;
                res?;
            }
        }
    }

    // Main body lowered inline. Finalize via join_opt or Return.
    let result = lower_expr(ctx, body, /* is_tail */ true)?;
    finalize_arm(ctx, result, join_opt.as_ref());

    // -- Build with_fail_cont. Receives (unmatched_value, ...captures).
    let extras = switch_to_cont_fn(ctx, &with_fail_cont, 1);
    let unmatched_v = extras[0];

    if else_clauses.is_empty() {
        let cc = ctx.atoms.intern("with_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.terminated = true;
    } else {
        let fail_block = ctx.cur_mut().block(vec![]);
        let saved_block = ctx.cur_block();
        ctx.cur_block = Some(fail_block);
        let cc = ctx.atoms.intern("with_clause");
        let v = ctx.let_(Prim::Const(Const::Atom(cc)));
        ctx.set_term(Term::Halt(v));
        ctx.cur_block = Some(saved_block);

        let matrix_entry = ctx.cur_mut().block(vec![]);
        ctx.set_term(Term::Goto(matrix_entry, vec![]));
        ctx.cur_block = Some(matrix_entry);
        ctx.terminated = false;

        let pattern_matrix = PatternMatrix {
            subjects: vec![unmatched_v],
            rows: else_clauses
                .iter()
                .enumerate()
                .map(|(i, c)| Row {
                    patterns: vec![c.pattern.clone()],
                    preconditions: Vec::new(),
                    bindings: Vec::new(),
                    guard: c.guard.clone(),
                    body_id: i as BodyId,
                })
                .collect(),
        };

        let saved_fail_env = ctx.env.clone();
        let saved_fail_order = ctx.env_order.clone();

        let mut else_conts: Vec<Option<ContFn>> = (0..else_clauses.len()).map(|_| None).collect();
        let prev_origin = ctx.branch_origin;
        ctx.branch_origin = crate::fz_ir::BranchOrigin::ClauseDispatch;
        {
            let else_conts_ref = &mut else_conts;
            let saved_fail_env_ref = &saved_fail_env;
            let saved_fail_order_ref = &saved_fail_order;
            let mut cb = |ctx: &mut LowerCtx,
                          body_id: BodyId,
                          bindings: Vec<(String, Var)>,
                          _preconds: Vec<(Var, crate::types::Ty)>,
                          guard: Option<crate::ast::Spanned<crate::ast::Expr>>,
                          fall_block: BlockId|
             -> Result<(), LowerError> {
                let i = body_id as usize;
                let clause = &else_clauses[i];
                ctx.env = saved_fail_env_ref.clone();
                ctx.env_order = saved_fail_order_ref.clone();
                for (name, var) in &bindings {
                    ctx.bind(name, *var);
                }
                if let Some(g) = &guard {
                    let guard_var = lower_expr(ctx, g, false)?;
                    let body_b = ctx.cur_mut().block(vec![]);
                    ctx.set_if_term(guard_var, body_b, fall_block);
                    ctx.cur_block = Some(body_b);
                    ctx.terminated = false;
                }
                let cont = mint_cont_fn(
                    ctx,
                    format!("with_else_{}", i),
                    clause.span,
                    crate::fz_ir::FnCategory::ControlFlowCont,
                );
                let captures = ctx.visible_locals();
                let capture_vars: Vec<Var> = captures.iter().map(|(_, v)| *v).collect();
                ctx.set_term(Term::TailCall {
                    ident: crate::fz_ir::CallsiteIdent::from_source(Span::DUMMY),
                    callee: cont.id,
                    args: capture_vars,
                    is_back_edge: false,
                });
                ctx.terminated = true;
                else_conts_ref[i] = Some(cont);
                Ok(())
            };
            let result =
                lower_pattern_matrix_to_current_fn(ctx, pattern_matrix, fail_block, &mut cb);
            ctx.branch_origin = prev_origin;
            result?;
        }

        for (i, clause) in else_clauses.iter().enumerate() {
            let Some(cont) = else_conts[i].clone() else {
                continue;
            };
            let _ = switch_to_cont_fn(ctx, &cont, 0);
            let result = lower_expr(ctx, &clause.body, /* is_tail */ true)?;
            finalize_arm(ctx, result, join_opt.as_ref());
        }
    }

    if let Some(join) = &join_opt {
        let extras = switch_to_cont_fn(ctx, join, 1);
        Ok(extras[0])
    } else {
        ctx.terminated = true;
        Ok(Var(0))
    }
}
