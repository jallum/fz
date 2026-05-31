use super::*;
use crate::ast::{BitSize as AstBitSize, Expr, MatchClause, Pattern, Spanned, WithBinding};
use crate::diag::Span;
use crate::fz_ir::{Const, FnBuilder, Prim, Term, Var};
use std::collections::HashSet;

pub(crate) fn lower_lambda(
    ctx: &mut LowerCtx,
    params: &[Spanned<Pattern>],
    body: &Spanned<Expr>,
    span: Span,
) -> Result<Var, LowerError> {
    let free_names = lambda_free_names(params, body);
    let captured: Vec<(String, Var)> = ctx
        .visible_locals()
        .into_iter()
        .filter(|(name, _)| free_names.contains(name))
        .collect();
    let captured_vars: Vec<Var> = captured.iter().map(|(_, v)| *v).collect();

    // Mint a fresh fn for the lambda.
    let lam_id = ctx.mb.fresh_fn_id();

    // Save current state and switch to building the lambda fn.
    let saved_cur = ctx.cur.take();
    let saved_cur_fn_id = ctx.cur_fn_id;
    let saved_block = ctx.cur_block.take();
    let saved_env = std::mem::take(&mut ctx.env);
    let saved_order = std::mem::take(&mut ctx.env_order);
    let saved_terminated = ctx.terminated;
    let saved_branch_origin = ctx.branch_origin;

    let mut lam_builder = FnBuilder::new(lam_id, format!("lambda_{}", lam_id.0))
        .with_category(crate::fz_ir::FnCategory::LambdaLift)
        .with_owner_module(ctx.current_owner_module.clone());
    // Entry params = captured + lambda params.
    let cap_params: Vec<Var> = captured.iter().map(|_| lam_builder.fresh_var()).collect();
    let lam_param_vars: Vec<Var> = params.iter().map(|_| lam_builder.fresh_var()).collect();
    let mut entry_params = cap_params.clone();
    entry_params.extend(lam_param_vars.clone());
    let lam_entry = lam_builder.block(entry_params);

    ctx.cur = Some(lam_builder);
    ctx.cur_fn_id = Some(lam_id);
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
        if matches!(pat.node, Pattern::Wildcard) {
            ctx.cur_mut().mark_param_ignored(*pv);
        }
    }
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
    ctx.cur_fn_id = saved_cur_fn_id;
    ctx.cur_block = saved_block;
    ctx.env = saved_env;
    ctx.env_order = saved_order;
    ctx.terminated = saved_terminated;
    ctx.branch_origin = saved_branch_origin;

    Ok(ctx.let_at(Prim::make_closure(span, lam_id, captured_vars), span))
}
pub(super) fn lambda_free_names(
    params: &[Spanned<Pattern>],
    body: &Spanned<Expr>,
) -> HashSet<String> {
    let mut bound = HashSet::new();
    for param in params {
        bind_pattern_names(&param.node, &mut bound);
    }
    let mut free = HashSet::new();
    collect_expr_free_names(&body.node, &mut bound, &mut free);
    free
}

pub(super) fn collect_expr_free_names(
    expr: &Expr,
    bound: &mut HashSet<String>,
    free: &mut HashSet<String>,
) {
    match expr {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::FnRef { .. }
        // fz-g58.2.6 — `&N` placeholder binds nothing and references nothing
        // outer; the `&(...)` body's free names come from recursing into it.
        | Expr::CaptureArg(_) => {}
        Expr::Capture(body) => collect_expr_free_names(&body.node, bound, free),
        Expr::Var(name) => record_free_name(name, bound, free),
        Expr::List(items, tail) => {
            for item in items {
                collect_expr_free_names(&item.node, bound, free);
            }
            if let Some(tail) = tail {
                collect_expr_free_names(&tail.node, bound, free);
            }
        }
        Expr::Tuple(items) => {
            for item in items {
                collect_expr_free_names(&item.node, bound, free);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                collect_expr_free_names(&field.value.node, bound, free);
                collect_bit_size_free_names(&field.spec.size, bound, free);
            }
        }
        Expr::Map(entries) => {
            for (key, value) in entries {
                collect_expr_free_names(&key.node, bound, free);
                collect_expr_free_names(&value.node, bound, free);
            }
        }
        Expr::MapUpdate(base, entries) => {
            collect_expr_free_names(&base.node, bound, free);
            for (key, value) in entries {
                collect_expr_free_names(&key.node, bound, free);
                collect_expr_free_names(&value.node, bound, free);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_expr_free_names(&value.node, bound, free);
            }
        }
        Expr::Index(base, key) => {
            collect_expr_free_names(&base.node, bound, free);
            collect_expr_free_names(&key.node, bound, free);
        }
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            collect_expr_free_names(&callee.node, bound, free);
            for arg in args {
                collect_expr_free_names(&arg.node, bound, free);
            }
        }
        Expr::BinOp(_, lhs, rhs) => {
            collect_expr_free_names(&lhs.node, bound, free);
            collect_expr_free_names(&rhs.node, bound, free);
        }
        Expr::UnOp(_, value) | Expr::Ascribe(value, _) => {
            collect_expr_free_names(&value.node, bound, free)
        }
        Expr::If(cond, then_e, else_e) => {
            collect_expr_free_names(&cond.node, bound, free);
            collect_expr_free_names_in_nested_scope(&then_e.node, bound, free);
            if let Some(else_e) = else_e {
                collect_expr_free_names_in_nested_scope(&else_e.node, bound, free);
            }
        }
        Expr::Case(subject, clauses) => {
            if let Some(subject) = subject {
                collect_expr_free_names(&subject.node, bound, free);
            }
            collect_match_clause_free_names(clauses, bound, free);
        }
        Expr::Cond(arms) => {
            for (test, body) in arms {
                collect_expr_free_names_in_nested_scope(&test.node, bound, free);
                collect_expr_free_names_in_nested_scope(&body.node, bound, free);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            let saved = bound.clone();
            for binding in bindings {
                match binding {
                    WithBinding::Bare(expr) => collect_expr_free_names(&expr.node, bound, free),
                    WithBinding::Match(pattern, expr) => {
                        collect_expr_free_names(&expr.node, bound, free);
                        collect_pattern_free_names(&pattern.node, bound, free);
                        bind_pattern_names(&pattern.node, bound);
                    }
                }
            }
            collect_expr_free_names(&body.node, bound, free);
            *bound = saved;
            collect_match_clause_free_names(else_clauses, bound, free);
        }
        Expr::Receive { clauses, after } => {
            collect_match_clause_free_names(clauses, bound, free);
            if let Some(after) = after {
                collect_expr_free_names(&after.timeout.node, bound, free);
                collect_expr_free_names(&after.body.node, bound, free);
            }
        }
        Expr::Match(pattern, rhs) => {
            collect_expr_free_names(&rhs.node, bound, free);
            collect_pattern_free_names(&pattern.node, bound, free);
            bind_pattern_names(&pattern.node, bound);
        }
        Expr::Block(exprs) => {
            for expr in exprs {
                collect_expr_free_names(&expr.node, bound, free);
            }
        }
        Expr::Lambda(clauses) => {
            // Free names span every clause: each clause binds its own params,
            // and its guard + body may reference outer names independently.
            for clause in clauses {
                let mut nested = bound.clone();
                for param in &clause.params {
                    bind_pattern_names(&param.node, &mut nested);
                }
                if let Some(guard) = &clause.guard {
                    collect_expr_free_names(&guard.node, &mut nested, free);
                }
                collect_expr_free_names(&clause.body.node, &mut nested, free);
            }
        }
        Expr::Quote(inner) | Expr::Unquote(inner) => {
            collect_expr_free_names(&inner.node, bound, free);
        }
    }
}

pub(super) fn collect_match_clause_free_names(
    clauses: &[MatchClause],
    bound: &mut HashSet<String>,
    free: &mut HashSet<String>,
) {
    for clause in clauses {
        let mut nested = bound.clone();
        collect_pattern_free_names(&clause.pattern.node, bound, free);
        bind_pattern_names(&clause.pattern.node, &mut nested);
        if let Some(guard) = &clause.guard {
            collect_expr_free_names(&guard.node, &mut nested, free);
        }
        collect_expr_free_names(&clause.body.node, &mut nested, free);
    }
}

pub(super) fn collect_expr_free_names_in_nested_scope(
    expr: &Expr,
    bound: &HashSet<String>,
    free: &mut HashSet<String>,
) {
    let mut nested = bound.clone();
    collect_expr_free_names(expr, &mut nested, free);
}

pub(super) fn collect_pattern_free_names(
    pattern: &Pattern,
    bound: &HashSet<String>,
    free: &mut HashSet<String>,
) {
    match pattern {
        Pattern::Pinned(name) => record_free_name(name, bound, free),
        Pattern::Tuple(items) => {
            for item in items {
                collect_pattern_free_names(&item.node, bound, free);
            }
        }
        Pattern::List(items, tail) => {
            for item in items {
                collect_pattern_free_names(&item.node, bound, free);
            }
            if let Some(tail) = tail {
                collect_pattern_free_names(&tail.node, bound, free);
            }
        }
        Pattern::Map(entries) => {
            for (key, value) in entries {
                collect_pattern_free_names(&key.node, bound, free);
                collect_pattern_free_names(&value.node, bound, free);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, value) in fields {
                collect_pattern_free_names(&value.node, bound, free);
            }
        }
        Pattern::As(_, inner) => collect_pattern_free_names(&inner.node, bound, free),
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_free_names(&field.value.node, bound, free);
                collect_bit_size_free_names(&field.spec.size, bound, free);
            }
        }
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
    }
}

pub(crate) fn bind_pattern_names(pattern: &Pattern, bound: &mut HashSet<String>) {
    let mut names = Vec::new();
    collect_pattern_bound_names(pattern, &mut names);
    bound.extend(names);
}

pub(super) fn collect_bit_size_free_names(
    size: &Option<AstBitSize>,
    bound: &HashSet<String>,
    free: &mut HashSet<String>,
) {
    if let Some(AstBitSize::Var(name)) = size {
        record_free_name(name, bound, free);
    }
}

pub(super) fn record_free_name(name: &str, bound: &HashSet<String>, free: &mut HashSet<String>) {
    if !bound.contains(name) {
        free.insert(name.to_string());
    }
}

/// fz-yxs — collect the names a pattern would bind, in source-traversal
/// order. Mirrors `collect_one` but emits only the names; the matcher
/// (B3) consumes the same source pattern AST and lines its extracted
/// slots up with this same order, so each clause body fn's first
/// `bound_names.len()` params receive the bound values positionally.
pub(crate) fn collect_pattern_bound_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Wildcard
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil
        | Pattern::Pinned(_) => {}
        Pattern::Var(name) => out.push(name.clone()),
        Pattern::As(name, inner) => {
            out.push(name.clone());
            collect_pattern_bound_names(&inner.node, out);
        }
        Pattern::Tuple(elems) => {
            for e in elems {
                collect_pattern_bound_names(&e.node, out);
            }
        }
        Pattern::List(elems, tail) => {
            for e in elems {
                collect_pattern_bound_names(&e.node, out);
            }
            if let Some(t) = tail {
                collect_pattern_bound_names(&t.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (_k, v) in entries {
                collect_pattern_bound_names(&v.node, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, v) in fields {
                collect_pattern_bound_names(&v.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_bound_names(&field.value.node, out);
            }
        }
    }
}

/// fz-yxs — collect every `^name` reference appearing in a pattern.
pub(crate) fn collect_pattern_pinned_names(p: &Pattern, out: &mut Vec<String>) {
    match p {
        Pattern::Pinned(name) => out.push(name.clone()),
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
        Pattern::As(_, inner) => collect_pattern_pinned_names(&inner.node, out),
        Pattern::Tuple(elems) => {
            for e in elems {
                collect_pattern_pinned_names(&e.node, out);
            }
        }
        Pattern::List(elems, tail) => {
            for e in elems {
                collect_pattern_pinned_names(&e.node, out);
            }
            if let Some(t) = tail {
                collect_pattern_pinned_names(&t.node, out);
            }
        }
        Pattern::Map(entries) => {
            for (k, v) in entries {
                collect_pattern_pinned_names(&k.node, out);
                collect_pattern_pinned_names(&v.node, out);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, v) in fields {
                collect_pattern_pinned_names(&v.node, out);
            }
        }
        Pattern::Bitstring(fields) => {
            for field in fields {
                collect_pattern_pinned_names(&field.value.node, out);
            }
        }
    }
}
