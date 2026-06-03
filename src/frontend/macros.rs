//! fz-ul4.10.3 — macro expansion pass.
//!
//! Runs between parse and type-check. Walks every fn body; when a call's
//! target is the name of a `defmacro`, the args are *reified* (not
//! evaluated) into Values, the macro body is run via the interp with its
//! params bound to those values, and the returned Value is decoded back to
//! an Expr that replaces the original call. The expanded form is then
//! re-walked so a macro can expand to another macro call.
//!
//! Hygiene is .10.4. For now, gensyms are the user's responsibility (and
//! a stack-overflow guard catches runaway expansion).

use crate::ast::*;
use crate::diag::{Diagnostic, Span, SpanOrigin, codes};
use crate::exec::ast_value::{expr_to_value, value_to_expr};
use crate::exec::eval::CompileTimeEvaluator;
use crate::exec::value::Value;
use std::collections::{HashMap, HashSet};
use std::error::Error;
use std::fmt;
use std::rc::Rc;

const MAX_EXPANSION_DEPTH: usize = 200;

/// Errors produced by the macro expansion pass. Every variant that
/// corresponds to a user-visible failure carries the macro call's
/// `call_span` plus an optional `def_span` (the `defmacro` declaration);
/// the renderer emits "expanded from `<macro>` at …" trailers from these.
#[derive(Debug, Clone)]
pub enum MacroError {
    /// Item-level call to a name that isn't a `defmacro`.
    NotADefmacro { name: String, call_span: Span },
    /// One of the macro's arguments couldn't be reified to a Value.
    ArgReification {
        name: String,
        call_span: Span,
        def_span: Option<Span>,
        inner: String,
    },
    /// The macro body itself errored at runtime.
    BodyFailed {
        name: String,
        call_span: Span,
        def_span: Option<Span>,
        inner: String,
    },
    /// The macro returned a Value that couldn't be decoded back to AST.
    ReturnDecode {
        name: String,
        call_span: Span,
        def_span: Option<Span>,
        inner: String,
    },
    /// Runaway expansion (exceeded `MAX_EXPANSION_DEPTH`).
    ExpansionLoop { span: Span, max_depth: usize },
    /// `expand_with` saw a pre-resolution Item (Module/Alias/Import/MacroCall).
    /// This is a compiler-internal invariant violation, not user error.
    PostResolutionLeftover { span: Span },
    /// Setting up the scratch interp before expansion failed. No span
    /// available — this is rare and signals an issue earlier in the pipe.
    LoadFailed { inner: String },
}

impl MacroError {
    pub fn to_diagnostic(&self) -> Diagnostic {
        match self {
            Self::NotADefmacro { name, call_span } => Diagnostic::error(
                codes::MACRO_NOT_A_DEFMACRO,
                format!("item-level call `{}(...)` is not a defmacro", name),
                *call_span,
            ),
            Self::ArgReification {
                name,
                call_span,
                def_span,
                inner,
            } => {
                let mut d = Diagnostic::error(
                    codes::MACRO_ARG_REIFICATION_FAILED,
                    format!("macro `{}` argument reification failed: {}", name, inner),
                    *call_span,
                );
                if let Some(ds) = def_span {
                    d = d.with_secondary(*ds, "macro defined here");
                }
                d
            }
            Self::BodyFailed {
                name,
                call_span,
                def_span,
                inner,
            } => {
                let mut d = Diagnostic::error(
                    codes::MACRO_BODY_FAILED,
                    format!("macro `{}` body failed: {}", name, inner),
                    *call_span,
                );
                if let Some(ds) = def_span {
                    d = d.with_secondary(*ds, "macro defined here");
                }
                d
            }
            Self::ReturnDecode {
                name,
                call_span,
                def_span,
                inner,
            } => {
                let mut d = Diagnostic::error(
                    codes::MACRO_RETURN_DECODE_FAILED,
                    format!("macro `{}` return decode failed: {}", name, inner),
                    *call_span,
                );
                if let Some(ds) = def_span {
                    d = d.with_secondary(*ds, "macro defined here");
                }
                d
            }
            Self::ExpansionLoop { span, max_depth } => Diagnostic::error(
                codes::MACRO_EXPANSION_LOOP,
                format!("macro expansion exceeded {} levels (likely a runaway macro)", max_depth),
                *span,
            ),
            Self::PostResolutionLeftover { span } => Diagnostic::error(
                codes::INTERNAL_POST_RESOLUTION_LEFTOVER,
                "expand_with: pre-resolution Item reached macro expander; \
                 resolve::flatten_modules must run first",
                *span,
            ),
            Self::LoadFailed { inner } => Diagnostic::error(
                codes::MACRO_BODY_FAILED,
                format!("macro expansion setup failed: {}", inner),
                Span::DUMMY,
            ),
        }
    }
}

impl fmt::Display for MacroError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.to_diagnostic().message)
    }
}

impl Error for MacroError {}

/// Expand all macro calls in `prog` in place. Builds a scratch interp from
/// the program (so macros can call other macros and regular fns), then
/// expands every non-macro fn body. Macro bodies themselves are left
/// untouched — they're meta-code, not subject to expansion.
pub fn expand_program(prog: &mut Program) -> Result<(), Box<MacroError>> {
    // Always run the item-level pass first (it doesn't need the macros set
    // since collect_macros walks both Item::Fn and the resulting Item::Fn
    // post-splice). After items are spliced, run expression-level expansion.
    let macros = collect_macros(prog);
    let interp = CompileTimeEvaluator::new();
    interp
        .load_program(prog)
        .map_err(|e| Box::new(MacroError::LoadFailed { inner: e }))?;

    // Item-level expansion: replace Item::MacroCall with whatever items
    // the macro returns. Expanded items are appended to a fresh vec; the
    // macro set may grow during this pass if a macro returns more macros
    // (rare, but possible).
    expand_items(prog, &interp, &macros)?;

    // Expression-level expansion across the (now-final) fn bodies.
    let macros = collect_macros(prog);
    expand_with(prog, &interp, &macros)
}

/// Walk top-level items and module bodies; for each Item::MacroCall whose
/// target is a defmacro, run the macro and splice its returned items in.
fn expand_items(
    prog: &mut Program,
    interp: &CompileTimeEvaluator,
    macros: &HashSet<String>,
) -> Result<(), Box<MacroError>> {
    prog.items = expand_item_list(prog.items.clone(), interp, macros)?;
    Ok(())
}

fn expand_item_list(
    items: Vec<Rc<Item>>,
    interp: &CompileTimeEvaluator,
    macros: &HashSet<String>,
) -> Result<Vec<Rc<Item>>, Box<MacroError>> {
    let mut out: Vec<Rc<Item>> = Vec::new();
    for item in items {
        match &*item {
            Item::MacroCall {
                name,
                name_span: _,
                args,
                parent_module,
                span,
            } => {
                let call_span = *span;
                let def_span = interp.macro_def_spans.borrow().get(name).copied();
                if !macros.contains(name) {
                    return Err(Box::new(MacroError::NotADefmacro {
                        name: name.clone(),
                        call_span,
                    }));
                }
                let arg_vs = args
                    .iter()
                    .map(expr_to_value)
                    .collect::<Result<Vec<_>, _>>()
                    .map_err(|e| {
                        Box::new(MacroError::ArgReification {
                            name: name.clone(),
                            call_span,
                            def_span,
                            inner: e,
                        })
                    })?;
                let prev = interp.gensym_table.borrow_mut().take();
                *interp.gensym_table.borrow_mut() = Some(HashMap::new());
                let ret = interp.call_named(name, arg_vs);
                *interp.gensym_table.borrow_mut() = prev;
                let ret = ret.map_err(|e| {
                    Box::new(MacroError::BodyFailed {
                        name: name.clone(),
                        call_span,
                        def_span,
                        inner: e,
                    })
                })?;
                let mut items = value_to_items(&ret).map_err(|e| {
                    Box::new(MacroError::ReturnDecode {
                        name: name.clone(),
                        call_span,
                        def_span,
                        inner: e,
                    })
                })?;
                for it in &mut items {
                    if let Item::Fn(def) = it {
                        if let Some(path) = parent_module {
                            // .16.5: spliced fn lands under parent module.
                            def.name = format!("{}.{}", path, def.name);
                        }
                        // Stamp the macro call's span on the synthesized
                        // fn's metadata + every node in every clause so
                        // diagnostics can point at the user's invocation
                        // and the macro's definition.
                        def.name_span = call_span;
                        def.span = call_span;
                        for clause in &mut def.clauses {
                            clause.span = call_span;
                            for p in &mut clause.params {
                                stamp_pattern(p, call_span, def_span);
                            }
                            stamp_expanded(&mut clause.body, call_span, def_span);
                            if let Some(g) = &mut clause.guard {
                                stamp_expanded(g, call_span, def_span);
                            }
                        }
                    }
                }
                for it in items {
                    out.push(Rc::new(it));
                }
            }
            Item::Module(m) => {
                let new_items = expand_item_list(m.items.clone(), interp, macros)?;
                out.push(Rc::new(Item::Module(ModuleDef {
                    name: m.name.clone(),
                    name_span: m.name_span,
                    items: new_items,
                    attrs: m.attrs.clone(),
                    span: m.span,
                })));
            }
            _ => out.push(item.clone()),
        }
    }
    Ok(out)
}

/// Decode a macro's return Value into one or more `Item`s.
///
/// Accepted shapes:
///
/// - `{:fn_def, name_atom, body_value}` — produces `Item::Fn` with a
///   single zero-arg clause. v1 is intentionally narrow: tests are all
///   zero-arg, and we can grow this when more shapes are needed.
/// - `Value::List([item_value, ...])` — multiple items in declaration
///   order. Each element is decoded recursively.
pub fn value_to_items(v: &Value) -> Result<Vec<Item>, String> {
    match v {
        Value::Tuple(t) if t.len() == 3 => {
            let tag = match &t[0] {
                Value::Atom(s) => s.to_string(),
                _ => return Err("expected item tag atom at tuple[0]".into()),
            };
            match tag.as_str() {
                "fn_def" => {
                    let name = match &t[1] {
                        Value::Atom(s) => s.to_string(),
                        _ => return Err(":fn_def expects an atom name".into()),
                    };
                    let body = value_to_expr(&t[2])?;
                    let span = Span::DUMMY;
                    Ok(vec![Item::Fn(FnDef {
                        name,
                        name_span: span,
                        clauses: vec![FnClause {
                            param_annotations: vec![],
                            params: vec![],
                            guard: None,
                            body,
                            span,
                        }],
                        is_macro: false,
                        is_private: false,
                        extern_abi: None,
                        extern_params: vec![],
                        extern_ret_tokens: TypeExprBody(vec![]),
                        variadic: false,
                        attrs: Vec::new(),
                        span,
                    })])
                }
                other => Err(format!("unknown item tag :{}", other)),
            }
        }
        Value::List(xs) => {
            let mut out = Vec::new();
            for x in xs.iter() {
                out.extend(value_to_items(x)?);
            }
            Ok(out)
        }
        other => Err(format!(
            "macro at item-position must return :fn_def tuple or list of items, got {:?}",
            other
        )),
    }
}

/// Like `expand_program` but uses an interp the caller already has loaded
/// (used by the REPL, which carries macros across input lines).
pub fn expand_with(
    prog: &mut Program,
    interp: &CompileTimeEvaluator,
    macros: &HashSet<String>,
) -> Result<(), Box<MacroError>> {
    for item in &mut prog.items {
        // We Rc::make_mut to get an exclusive ref. At this point in the
        // pipeline the program has just been parsed and isn't shared.
        let item_mut = Rc::make_mut(item);
        match item_mut {
            Item::Fn(def) => {
                if def.is_macro {
                    continue;
                }
                for clause in &mut def.clauses {
                    expand_expr(&mut clause.body, interp, macros, 0)?;
                    if let Some(g) = &mut clause.guard {
                        expand_expr(g, interp, macros, 0)?;
                    }
                }
            }
            Item::Module(m) => {
                return Err(Box::new(MacroError::PostResolutionLeftover { span: m.span }));
            }
            Item::Protocol(p) => {
                return Err(Box::new(MacroError::PostResolutionLeftover { span: p.span }));
            }
            Item::ProtocolImpl(i) => {
                return Err(Box::new(MacroError::PostResolutionLeftover { span: i.span }));
            }
            Item::Struct(_) => {}
            Item::Alias { span, .. } | Item::Import { span, .. } | Item::MacroCall { span, .. } => {
                return Err(Box::new(MacroError::PostResolutionLeftover { span: *span }));
            }
        }
    }
    Ok(())
}

/// Collect names of all macros defined in `prog`. Also exposed for the
/// REPL, which needs to know the live macro set without re-walking the
/// program every input.
pub fn collect_macros(prog: &Program) -> HashSet<String> {
    let mut out = HashSet::new();
    for item in &prog.items {
        match &**item {
            Item::Fn(def) => {
                if def.is_macro {
                    out.insert(def.name.clone());
                }
            }
            Item::Module(_)
            | Item::Struct(_)
            | Item::Protocol(_)
            | Item::ProtocolImpl(_)
            | Item::Alias { .. }
            | Item::Import { .. }
            | Item::MacroCall { .. } => {
                // Pre-flatten programs may still hit this path in tests;
                // be tolerant since post-flatten there are none.
            }
        }
    }
    out
}

pub fn expand_expr(
    e: &mut Spanned<Expr>,
    interp: &CompileTimeEvaluator,
    macros: &HashSet<String>,
    depth: usize,
) -> Result<(), Box<MacroError>> {
    expand_expr_inner(e, interp, macros, depth, false)
}

fn expand_expr_inner(
    e: &mut Spanned<Expr>,
    interp: &CompileTimeEvaluator,
    macros: &HashSet<String>,
    depth: usize,
    in_capture: bool,
) -> Result<(), Box<MacroError>> {
    if depth > MAX_EXPANSION_DEPTH {
        return Err(Box::new(MacroError::ExpansionLoop {
            span: e.span,
            max_depth: MAX_EXPANSION_DEPTH,
        }));
    }

    // Macro calls are handled BEFORE recursing into args — the macro
    // receives args quoted, not expanded.
    if let Expr::Call(callee, args) = &mut e.node
        && let Expr::Var(name) = &callee.node
        && macros.contains(name)
    {
        let call_span = e.span;
        let def_span = interp.macro_def_spans.borrow().get(name).copied();
        let arg_vs = args
            .iter()
            .map(expr_to_value)
            .collect::<Result<Vec<_>, _>>()
            .map_err(|inner| {
                Box::new(MacroError::ArgReification {
                    name: name.clone(),
                    call_span,
                    def_span,
                    inner,
                })
            })?;
        let prev = interp.gensym_table.borrow_mut().take();
        *interp.gensym_table.borrow_mut() = Some(HashMap::new());
        let ret_res = interp.call_named(name, arg_vs);
        *interp.gensym_table.borrow_mut() = prev;
        let ret = ret_res.map_err(|inner| {
            Box::new(MacroError::BodyFailed {
                name: name.clone(),
                call_span,
                def_span,
                inner,
            })
        })?;
        let mut new_e = value_to_expr(&ret).map_err(|inner| {
            Box::new(MacroError::ReturnDecode {
                name: name.clone(),
                call_span,
                def_span,
                inner,
            })
        })?;
        // The decoded tree is entirely DUMMY-spanned. Stamp every
        // node with the call's span + Expanded lineage so any later
        // diagnostic can point at the user's `Foo(args)` and show
        // "expanded from `Foo`, defined at <file>:<line>:<col>".
        stamp_expanded(&mut new_e, call_span, def_span);
        *e = new_e;
        return expand_expr_inner(e, interp, macros, depth + 1, in_capture);
    }

    // Default: recurse into children.
    match &mut e.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        // fz-g58.2.6 — `&N` is a leaf; `&(...)` body is expanded below.
        | Expr::CaptureArg(_) => {}
        Expr::Capture(body) => expand_expr_inner(body, interp, macros, depth, true)?,

        Expr::List(xs, tail) => {
            for x in xs {
                expand_expr_inner(x, interp, macros, depth, in_capture)?;
            }
            if let Some(t) = tail {
                expand_expr_inner(t, interp, macros, depth, in_capture)?;
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                expand_expr_inner(x, interp, macros, depth, in_capture)?;
            }
        }
        Expr::Bitstring(fields) => {
            for f in fields {
                expand_expr_inner(&mut f.value, interp, macros, depth, in_capture)?;
            }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                expand_expr_inner(k, interp, macros, depth, in_capture)?;
                expand_expr_inner(v, interp, macros, depth, in_capture)?;
            }
        }
        Expr::MapUpdate(m, pairs) => {
            expand_expr_inner(m, interp, macros, depth, in_capture)?;
            for (k, v) in pairs {
                expand_expr_inner(k, interp, macros, depth, in_capture)?;
                expand_expr_inner(v, interp, macros, depth, in_capture)?;
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, v) in fields {
                expand_expr_inner(v, interp, macros, depth, in_capture)?;
            }
        }
        Expr::Index(o, i) => {
            expand_expr_inner(o, interp, macros, depth, in_capture)?;
            expand_expr_inner(i, interp, macros, depth, in_capture)?;
        }
        Expr::Call(callee, args) => {
            expand_expr_inner(callee, interp, macros, depth, in_capture)?;
            for a in args.iter_mut() {
                expand_expr_inner(a, interp, macros, depth, in_capture)?;
            }
            if let Expr::BinOp(BinOp::Pipe, lhs, rhs) = &callee.node {
                let mut new_args = Vec::with_capacity(args.len() + 1);
                new_args.push((**lhs).clone());
                new_args.extend(args.iter().cloned());
                e.node = Expr::Call(Box::new((**rhs).clone()), new_args);
            }
        }
        Expr::ClosureCall(callee, args) => {
            expand_expr_inner(callee, interp, macros, depth, in_capture)?;
            for a in args.iter_mut() {
                expand_expr_inner(a, interp, macros, depth, in_capture)?;
            }
        }
        Expr::BinOp(op, l, r) => {
            expand_expr_inner(l, interp, macros, depth, in_capture)?;
            expand_expr_inner(r, interp, macros, depth, in_capture)?;
            match *op {
                BinOp::Pipe => {
                    let lhs = (**l).clone();
                    match &mut r.node {
                        Expr::Call(callee, args) => {
                            let mut new_args = Vec::with_capacity(args.len() + 1);
                            new_args.push(lhs);
                            new_args.extend(args.iter().cloned());
                            e.node = Expr::Call(callee.clone(), new_args);
                        }
                        Expr::ClosureCall(callee, args) => {
                            let mut new_args = Vec::with_capacity(args.len() + 1);
                            new_args.push(lhs);
                            new_args.extend(args.iter().cloned());
                            e.node = Expr::ClosureCall(callee.clone(), new_args);
                        }
                        Expr::Case(scrut @ None, arms) => {
                            *scrut = Some(Box::new(lhs));
                            e.node = Expr::Case(scrut.clone(), arms.clone());
                        }
                        _ => {}
                    }
                }
                BinOp::ListConcat => {
                    e.node = call2("List.concat", (**l).clone(), (**r).clone());
                }
                BinOp::ListSubtract => {
                    e.node = call2("List.subtract", (**l).clone(), (**r).clone());
                }
                BinOp::BinConcat => {
                    e.node = call2("Kernel.fz_binary_concat", (**l).clone(), (**r).clone());
                }
                BinOp::Range => {
                    e.node = call3(
                        "Range.new",
                        (**l).clone(),
                        (**r).clone(),
                        Spanned::new(Expr::Int(1), e.span),
                    );
                }
                BinOp::RangeStep => {
                    if let Some((first, last)) = range_new_args(l) {
                        e.node = call3("Range.new", first, last, (**r).clone());
                    }
                }
                BinOp::In => {
                    e.node = call2("Enum.member?", (**r).clone(), (**l).clone());
                }
                BinOp::NotIn => {
                    let member = call2("Enum.member?", (**r).clone(), (**l).clone());
                    e.node = Expr::UnOp(UnOp::Not, Box::new(Spanned::new(member, e.span)));
                }
                BinOp::Add
                | BinOp::Sub
                | BinOp::Mul
                | BinOp::Div
                | BinOp::Rem
                | BinOp::Eq
                | BinOp::Neq
                | BinOp::Lt
                | BinOp::LtEq
                | BinOp::Gt
                | BinOp::GtEq
                | BinOp::And
                | BinOp::Or
                | BinOp::Cons => {}
            }
        }
        Expr::UnOp(_, x) | Expr::Ascribe(x, _) => {
            expand_expr_inner(x, interp, macros, depth, in_capture)?
        }
        Expr::If(c, t, els) => {
            expand_expr_inner(c, interp, macros, depth, in_capture)?;
            expand_expr_inner(t, interp, macros, depth, in_capture)?;
            if let Some(e) = els {
                expand_expr_inner(e, interp, macros, depth, in_capture)?;
            }
        }
        Expr::Case(scr, arms) => {
            if let Some(scr) = scr {
                expand_expr_inner(scr, interp, macros, depth, in_capture)?;
            }
            for arm in arms {
                expand_expr_inner(&mut arm.body, interp, macros, depth, in_capture)?;
                if let Some(g) = &mut arm.guard {
                    expand_expr_inner(g, interp, macros, depth, in_capture)?;
                }
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                expand_expr_inner(c, interp, macros, depth, in_capture)?;
                expand_expr_inner(b, interp, macros, depth, in_capture)?;
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for b in bindings {
                match b {
                    WithBinding::Match(_, e) => {
                        expand_expr_inner(e, interp, macros, depth, in_capture)?
                    }
                    WithBinding::Bare(e) => {
                        expand_expr_inner(e, interp, macros, depth, in_capture)?
                    }
                }
            }
            expand_expr_inner(body, interp, macros, depth, in_capture)?;
            for arm in else_clauses {
                expand_expr_inner(&mut arm.body, interp, macros, depth, in_capture)?;
                if let Some(g) = &mut arm.guard {
                    expand_expr_inner(g, interp, macros, depth, in_capture)?;
                }
            }
        }
        Expr::Match(_, rhs) => expand_expr_inner(rhs, interp, macros, depth, in_capture)?,
        Expr::Lambda(clauses) => {
            for clause in clauses.iter_mut() {
                if let Some(guard) = &mut clause.guard {
                    expand_expr_inner(guard, interp, macros, depth, in_capture)?;
                }
                expand_expr_inner(&mut clause.body, interp, macros, depth, in_capture)?;
            }
        }
        // fz-5vj — recurse into receive clauses' bodies/guards and the
        // after timeout/body. Patterns are leaves at expansion time
        // (no macro-call positions inside patterns).
        Expr::Receive { clauses, after } => {
            for arm in clauses {
                expand_expr_inner(&mut arm.body, interp, macros, depth, in_capture)?;
                if let Some(g) = &mut arm.guard {
                    expand_expr_inner(g, interp, macros, depth, in_capture)?;
                }
            }
            if let Some(af) = after {
                expand_expr_inner(&mut af.timeout, interp, macros, depth, in_capture)?;
                expand_expr_inner(&mut af.body, interp, macros, depth, in_capture)?;
            }
        }

        Expr::Quote(_) | Expr::Unquote(_) => {}
    }
    desugar_lambda_sugars(e, in_capture);
    Ok(())
}

fn call2(name: &str, left: Spanned<Expr>, right: Spanned<Expr>) -> Expr {
    Expr::Call(
        Box::new(Spanned::new(Expr::Var(name.to_string()), left.span)),
        vec![left, right],
    )
}

fn call3(name: &str, first: Spanned<Expr>, second: Spanned<Expr>, third: Spanned<Expr>) -> Expr {
    Expr::Call(
        Box::new(Spanned::new(Expr::Var(name.to_string()), first.span)),
        vec![first, second, third],
    )
}

fn range_new_args(e: &Spanned<Expr>) -> Option<(Spanned<Expr>, Spanned<Expr>)> {
    let Expr::Call(callee, args) = &e.node else {
        return None;
    };
    let Expr::Var(name) = &callee.node else {
        return None;
    };
    if name == "Range.new" && args.len() == 3 {
        Some((args[0].clone(), args[1].clone()))
    } else {
        None
    }
}

fn desugar_lambda_sugars(e: &mut Spanned<Expr>, in_capture: bool) {
    match &mut e.node {
        Expr::CaptureArg(n) if !in_capture => {
            let name = capture_arg_name(*n);
            e.node = capture_lambda(*n, Spanned::new(Expr::Var(name), e.span), e.span);
        }
        Expr::Capture(body) => {
            let arity = max_capture_arg(body).unwrap_or(0);
            replace_capture_args(body);
            e.node = capture_lambda(arity, (**body).clone(), e.span);
        }
        Expr::Lambda(clauses) if lambda_direct_clause(clauses).is_none() => {
            if let Some(rewritten) = desugar_multi_clause_lambda(clauses, e.span) {
                e.node = rewritten;
            }
        }
        _ => {}
    }
}

fn capture_lambda(arity: usize, body: Spanned<Expr>, span: Span) -> Expr {
    let params = (1..=arity)
        .map(|n| Spanned::new(Pattern::Var(capture_arg_name(n)), span))
        .collect();
    Expr::Lambda(vec![LambdaClause {
        params,
        guard: None,
        body,
        span,
    }])
}

fn capture_arg_name(n: usize) -> String {
    format!("__fz_capture_arg_{}", n)
}

fn max_capture_arg(e: &Spanned<Expr>) -> Option<usize> {
    let mut max = None;
    visit_expr(e, &mut |expr| {
        if let Expr::CaptureArg(n) = expr {
            max = Some(max.map_or(*n, |m: usize| m.max(*n)));
        }
    });
    max
}

fn replace_capture_args(e: &mut Spanned<Expr>) {
    visit_expr_mut(e, &mut |expr, _span| {
        if let Expr::CaptureArg(n) = expr {
            *expr = Expr::Var(capture_arg_name(*n));
        }
    });
}

fn desugar_multi_clause_lambda(clauses: &[LambdaClause], span: Span) -> Option<Expr> {
    let arity = clauses.first()?.params.len();
    if clauses.iter().any(|clause| clause.params.len() != arity) {
        return None;
    }

    let params: Vec<Spanned<Pattern>> = (0..arity)
        .map(|i| Spanned::new(Pattern::Var(lambda_arg_name(i)), span))
        .collect();
    let subject = lambda_case_subject(arity, span);
    let arms = clauses
        .iter()
        .map(|clause| MatchClause {
            pattern: lambda_clause_pattern(&clause.params, span),
            guard: clause.guard.clone(),
            body: clause.body.clone(),
            span: clause.span,
        })
        .collect();

    Some(Expr::Lambda(vec![LambdaClause {
        params,
        guard: None,
        body: Spanned::new(Expr::Case(Some(Box::new(subject)), arms), span),
        span,
    }]))
}

fn lambda_arg_name(i: usize) -> String {
    format!("__fz_lambda_arg_{}", i)
}

fn lambda_case_subject(arity: usize, span: Span) -> Spanned<Expr> {
    if arity == 1 {
        Spanned::new(Expr::Var(lambda_arg_name(0)), span)
    } else {
        Spanned::new(
            Expr::Tuple(
                (0..arity)
                    .map(|i| Spanned::new(Expr::Var(lambda_arg_name(i)), span))
                    .collect(),
            ),
            span,
        )
    }
}

fn lambda_clause_pattern(params: &[Spanned<Pattern>], span: Span) -> Spanned<Pattern> {
    if params.len() == 1 {
        params[0].clone()
    } else {
        Spanned::new(Pattern::Tuple(params.to_vec()), span)
    }
}

fn visit_expr(e: &Spanned<Expr>, f: &mut impl FnMut(&Expr)) {
    f(&e.node);
    match &e.node {
        Expr::Capture(body) => visit_expr(body, f),
        Expr::List(xs, tail) => {
            for x in xs {
                visit_expr(x, f);
            }
            if let Some(t) = tail {
                visit_expr(t, f);
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                visit_expr(x, f);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                visit_expr(&field.value, f);
            }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                visit_expr(k, f);
                visit_expr(v, f);
            }
        }
        Expr::MapUpdate(base, pairs) => {
            visit_expr(base, f);
            for (k, v) in pairs {
                visit_expr(k, f);
                visit_expr(v, f);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, v) in fields {
                visit_expr(v, f);
            }
        }
        Expr::Index(base, key) | Expr::BinOp(_, base, key) => {
            visit_expr(base, f);
            visit_expr(key, f);
        }
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            visit_expr(callee, f);
            for arg in args {
                visit_expr(arg, f);
            }
        }
        Expr::UnOp(_, inner) | Expr::Ascribe(inner, _) => visit_expr(inner, f),
        Expr::If(c, t, els) => {
            visit_expr(c, f);
            visit_expr(t, f);
            if let Some(e) = els {
                visit_expr(e, f);
            }
        }
        Expr::Case(subject, arms) => {
            if let Some(subject) = subject {
                visit_expr(subject, f);
            }
            for arm in arms {
                if let Some(g) = &arm.guard {
                    visit_expr(g, f);
                }
                visit_expr(&arm.body, f);
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                visit_expr(c, f);
                visit_expr(b, f);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, expr) | WithBinding::Bare(expr) => visit_expr(expr, f),
                }
            }
            visit_expr(body, f);
            for arm in else_clauses {
                if let Some(g) = &arm.guard {
                    visit_expr(g, f);
                }
                visit_expr(&arm.body, f);
            }
        }
        Expr::Match(_, rhs) => visit_expr(rhs, f),
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(g) = &clause.guard {
                    visit_expr(g, f);
                }
                visit_expr(&clause.body, f);
            }
        }
        Expr::Receive { clauses, after } => {
            for arm in clauses {
                if let Some(g) = &arm.guard {
                    visit_expr(g, f);
                }
                visit_expr(&arm.body, f);
            }
            if let Some(after) = after {
                visit_expr(&after.timeout, f);
                visit_expr(&after.body, f);
            }
        }
        Expr::Quote(inner) | Expr::Unquote(inner) => visit_expr(inner, f),
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        | Expr::CaptureArg(_) => {}
    }
}

fn visit_expr_mut(e: &mut Spanned<Expr>, f: &mut impl FnMut(&mut Expr, Span)) {
    let span = e.span;
    f(&mut e.node, span);
    match &mut e.node {
        Expr::Capture(body) => visit_expr_mut(body, f),
        Expr::List(xs, tail) => {
            for x in xs {
                visit_expr_mut(x, f);
            }
            if let Some(t) = tail {
                visit_expr_mut(t, f);
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                visit_expr_mut(x, f);
            }
        }
        Expr::Bitstring(fields) => {
            for field in fields {
                visit_expr_mut(&mut field.value, f);
            }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                visit_expr_mut(k, f);
                visit_expr_mut(v, f);
            }
        }
        Expr::MapUpdate(base, pairs) => {
            visit_expr_mut(base, f);
            for (k, v) in pairs {
                visit_expr_mut(k, f);
                visit_expr_mut(v, f);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, v) in fields {
                visit_expr_mut(v, f);
            }
        }
        Expr::Index(base, key) | Expr::BinOp(_, base, key) => {
            visit_expr_mut(base, f);
            visit_expr_mut(key, f);
        }
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            visit_expr_mut(callee, f);
            for arg in args {
                visit_expr_mut(arg, f);
            }
        }
        Expr::UnOp(_, inner) | Expr::Ascribe(inner, _) => visit_expr_mut(inner, f),
        Expr::If(c, t, els) => {
            visit_expr_mut(c, f);
            visit_expr_mut(t, f);
            if let Some(e) = els {
                visit_expr_mut(e, f);
            }
        }
        Expr::Case(subject, arms) => {
            if let Some(subject) = subject {
                visit_expr_mut(subject, f);
            }
            for arm in arms {
                if let Some(g) = &mut arm.guard {
                    visit_expr_mut(g, f);
                }
                visit_expr_mut(&mut arm.body, f);
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                visit_expr_mut(c, f);
                visit_expr_mut(b, f);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for binding in bindings {
                match binding {
                    WithBinding::Match(_, expr) | WithBinding::Bare(expr) => visit_expr_mut(expr, f),
                }
            }
            visit_expr_mut(body, f);
            for arm in else_clauses {
                if let Some(g) = &mut arm.guard {
                    visit_expr_mut(g, f);
                }
                visit_expr_mut(&mut arm.body, f);
            }
        }
        Expr::Match(_, rhs) => visit_expr_mut(rhs, f),
        Expr::Lambda(clauses) => {
            for clause in clauses {
                if let Some(g) = &mut clause.guard {
                    visit_expr_mut(g, f);
                }
                visit_expr_mut(&mut clause.body, f);
            }
        }
        Expr::Receive { clauses, after } => {
            for arm in clauses {
                if let Some(g) = &mut arm.guard {
                    visit_expr_mut(g, f);
                }
                visit_expr_mut(&mut arm.body, f);
            }
            if let Some(after) = after {
                visit_expr_mut(&mut after.timeout, f);
                visit_expr_mut(&mut after.body, f);
            }
        }
        Expr::Quote(inner) | Expr::Unquote(inner) => visit_expr_mut(inner, f),
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        | Expr::CaptureArg(_) => {}
    }
}

/// Walk `e` and stamp every node with `SpanOrigin::Expanded { macro_call,
/// definition }`. DUMMY spans are rewritten to `macro_call` so a diagnostic
/// on a child of the expansion always points at the user's call site. Real
/// (non-DUMMY) spans encountered inside the tree are preserved — that's
/// the v2 case where Values carry their own spans through quote round-trip;
/// in v1 every decoded node is DUMMY so nothing is preserved yet.
fn stamp_expanded(e: &mut Spanned<Expr>, macro_call: Span, definition: Option<Span>) {
    let origin = SpanOrigin::Expanded { macro_call, definition };
    e.origin = origin;
    if e.span.is_dummy() {
        e.span = macro_call;
    }
    match &mut e.node {
        Expr::Int(_)
        | Expr::Float(_)
        | Expr::Binary(_)
        | Expr::Atom(_)
        | Expr::Bool(_)
        | Expr::Nil
        | Expr::Var(_)
        | Expr::FnRef { .. }
        // fz-g58.2.6 — `&N` is a leaf; `&(...)` body is stamped below.
        | Expr::CaptureArg(_) => {}
        Expr::Capture(body) => stamp_expanded(body, macro_call, definition),
        Expr::List(xs, tail) => {
            for x in xs {
                stamp_expanded(x, macro_call, definition);
            }
            if let Some(t) = tail {
                stamp_expanded(t, macro_call, definition);
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                stamp_expanded(x, macro_call, definition);
            }
        }
        Expr::Bitstring(fields) => {
            for f in fields {
                stamp_expanded(&mut f.value, macro_call, definition);
            }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                stamp_expanded(k, macro_call, definition);
                stamp_expanded(v, macro_call, definition);
            }
        }
        Expr::MapUpdate(m, pairs) => {
            stamp_expanded(m, macro_call, definition);
            for (k, v) in pairs {
                stamp_expanded(k, macro_call, definition);
                stamp_expanded(v, macro_call, definition);
            }
        }
        Expr::Struct { fields, .. } => {
            for (_, v) in fields {
                stamp_expanded(v, macro_call, definition);
            }
        }
        Expr::Index(o, i) => {
            stamp_expanded(o, macro_call, definition);
            stamp_expanded(i, macro_call, definition);
        }
        Expr::Call(callee, args) | Expr::ClosureCall(callee, args) => {
            stamp_expanded(callee, macro_call, definition);
            for a in args {
                stamp_expanded(a, macro_call, definition);
            }
        }
        Expr::BinOp(_, l, r) => {
            stamp_expanded(l, macro_call, definition);
            stamp_expanded(r, macro_call, definition);
        }
        Expr::UnOp(_, x) | Expr::Ascribe(x, _) => stamp_expanded(x, macro_call, definition),
        Expr::If(c, t, els) => {
            stamp_expanded(c, macro_call, definition);
            stamp_expanded(t, macro_call, definition);
            if let Some(e) = els {
                stamp_expanded(e, macro_call, definition);
            }
        }
        Expr::Case(scr, arms) => {
            if let Some(scr) = scr {
                stamp_expanded(scr, macro_call, definition);
            }
            for arm in arms {
                stamp_pattern(&mut arm.pattern, macro_call, definition);
                stamp_expanded(&mut arm.body, macro_call, definition);
                if let Some(g) = &mut arm.guard {
                    stamp_expanded(g, macro_call, definition);
                }
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                stamp_expanded(c, macro_call, definition);
                stamp_expanded(b, macro_call, definition);
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for b in bindings {
                match b {
                    WithBinding::Match(p, ex) => {
                        stamp_pattern(p, macro_call, definition);
                        stamp_expanded(ex, macro_call, definition);
                    }
                    WithBinding::Bare(ex) => stamp_expanded(ex, macro_call, definition),
                }
            }
            stamp_expanded(body, macro_call, definition);
            for arm in else_clauses {
                stamp_pattern(&mut arm.pattern, macro_call, definition);
                stamp_expanded(&mut arm.body, macro_call, definition);
                if let Some(g) = &mut arm.guard {
                    stamp_expanded(g, macro_call, definition);
                }
            }
        }
        Expr::Match(p, rhs) => {
            stamp_pattern(p, macro_call, definition);
            stamp_expanded(rhs, macro_call, definition);
        }
        Expr::Lambda(clauses) => {
            for clause in clauses.iter_mut() {
                for p in &mut clause.params {
                    stamp_pattern(p, macro_call, definition);
                }
                if let Some(guard) = &mut clause.guard {
                    stamp_expanded(guard, macro_call, definition);
                }
                stamp_expanded(&mut clause.body, macro_call, definition);
            }
        }
        // fz-5vj — stamp through receive clauses + after.
        Expr::Receive { clauses, after } => {
            for arm in clauses {
                stamp_pattern(&mut arm.pattern, macro_call, definition);
                stamp_expanded(&mut arm.body, macro_call, definition);
                if let Some(g) = &mut arm.guard {
                    stamp_expanded(g, macro_call, definition);
                }
            }
            if let Some(af) = after {
                stamp_expanded(&mut af.timeout, macro_call, definition);
                stamp_expanded(&mut af.body, macro_call, definition);
            }
        }
        Expr::Quote(inner) | Expr::Unquote(inner) => stamp_expanded(inner, macro_call, definition),
    }
}

fn stamp_pattern(p: &mut Spanned<Pattern>, macro_call: Span, definition: Option<Span>) {
    let origin = SpanOrigin::Expanded { macro_call, definition };
    p.origin = origin;
    if p.span.is_dummy() {
        p.span = macro_call;
    }
    match &mut p.node {
        Pattern::Wildcard
        | Pattern::Var(_)
        | Pattern::Pinned(_) // fz-5vj — `^name`; leaf, name resolves outward
        | Pattern::Int(_)
        | Pattern::Float(_)
        | Pattern::Binary(_)
        | Pattern::Atom(_)
        | Pattern::Bool(_)
        | Pattern::Nil => {}
        Pattern::Tuple(xs) => {
            for x in xs {
                stamp_pattern(x, macro_call, definition);
            }
        }
        Pattern::List(heads, tail) => {
            for h in heads {
                stamp_pattern(h, macro_call, definition);
            }
            if let Some(t) = tail {
                stamp_pattern(t, macro_call, definition);
            }
        }
        Pattern::Map(pairs) => {
            for (k, v) in pairs {
                stamp_pattern(k, macro_call, definition);
                stamp_pattern(v, macro_call, definition);
            }
        }
        Pattern::Struct { fields, .. } => {
            for (_, v) in fields {
                stamp_pattern(v, macro_call, definition);
            }
        }
        Pattern::As(_, inner) => stamp_pattern(inner, macro_call, definition),
        Pattern::Bitstring(fields) => {
            for f in fields {
                stamp_pattern(&mut f.value, macro_call, definition);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::frontend::resolve::flatten_modules;
    use crate::parser::Parser;
    use crate::parser::lexer::Lexer;
    use crate::types::ConcreteTypes;

    fn parse(src: &str) -> Program {
        let toks = Lexer::new(src).tokenize().expect("lex");
        Parser::new(toks).parse_program().expect("parse")
    }

    /// Run the full pipeline (parse → flatten → expand → eval main) and
    /// return main's return value.
    fn run(src: &str) -> Value {
        let prog = parse(src);
        let mut ct = ConcreteTypes;
        let mut prog = flatten_modules(&mut ct, prog).expect("flatten");
        expand_program(&mut prog).expect("expand");
        let interp = CompileTimeEvaluator::new();
        interp.load_program(&prog).expect("load");
        interp.call_named("main", vec![]).expect("eval")
    }

    fn expanded_main_body(src: &str) -> Expr {
        let mut prog = parse(src);
        expand_program(&mut prog).expect("expand");
        let item = prog.items.first().expect("main item");
        let Item::Fn(def) = &**item else {
            panic!("expected fn item");
        };
        def.clauses[0].body.node.clone()
    }

    #[test]
    fn defmacro_increments_arg() {
        // Classic Elixir-shape macro: receives arg as quoted form, returns
        // a quote that adds 1 to it.
        let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do
  plus_one(41)
end
"#;
        assert!(matches!(run(src), Value::Int(42)));
    }

    #[test]
    fn macro_inside_fn_body() {
        let src = r#"
defmacro double(x) do
  quote do: unquote(x) * 2
end
fn run() do
  a = double(10)
  b = double(20)
  a + b
end
fn main() do run() end
"#;
        assert!(matches!(run(src), Value::Int(60)));
    }

    #[test]
    fn macro_returns_a_call() {
        // Macro that splices its arg into a call to a regular fn.
        let src = r#"
fn helper(x) do x * 3 end
defmacro use_helper(x) do
  quote do: helper(unquote(x))
end
fn main() do use_helper(7) end
"#;
        assert!(matches!(run(src), Value::Int(21)));
    }

    #[test]
    fn nested_macro_expansion() {
        // Macro M2 wraps M1's output. Expander must re-expand the result.
        let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: m1(unquote(x)) end
fn main() do m2(40) end
"#;
        assert!(matches!(run(src), Value::Int(41)));
    }

    #[test]
    fn macro_args_are_not_pre_expanded() {
        // If macro args were expanded first, m2(m1(0)) would call m1 first
        // and m2 would see 1. Macros receive args quoted, so m2 sees the
        // AST of `m1(0)` and decides what to do with it. Here m2 just
        // splices it into its result, so the final code is `m1(0) + 5` =
        // 1 + 5 = 6.
        let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: unquote(x) + 5 end
fn main() do m2(m1(0)) end
"#;
        assert!(matches!(run(src), Value::Int(6)));
    }

    #[test]
    fn runaway_macro_caught() {
        // A macro that expands to itself: m(x) -> m(x). Should bail at the
        // depth limit instead of overflowing the stack.
        let src = r#"
defmacro loop_m(x) do
  quote do: loop_m(unquote(x))
end
fn main() do loop_m(0) end
"#;
        let mut prog = parse(src);
        let res = expand_program(&mut prog);
        assert!(res.is_err(), "expected expansion error");
        assert!(
            matches!(*res.unwrap_err(), MacroError::ExpansionLoop { .. }),
            "expected ExpansionLoop variant"
        );
    }

    #[test]
    fn hygiene_macro_local_does_not_shadow_caller() {
        // Without hygiene, the macro's `t = 99` would clobber the
        // caller's `t`. With hygiene, the macro's `t` becomes a fresh
        // gensym so the caller's binding survives.
        let src = r#"
defmacro set_local() do
  quote do: t = 99
end
fn main() do
  t = 1
  set_local()
  t
end
"#;
        let v = run(src);
        assert!(
            matches!(v, Value::Int(1)),
            "expected caller's t (1) to survive, got {:?}",
            v
        );
    }

    #[test]
    fn hygiene_unquoted_var_keeps_caller_name() {
        // Vars spliced via unquote come from the caller's evaluation
        // context — their VALUES, not their names — so hygiene doesn't
        // affect them. Here unquote(x) splices the literal 7.
        let src = r#"
defmacro emit(x) do
  quote do: unquote(x) + 1
end
fn main() do
  x = 7
  emit(x)
end
"#;
        assert!(matches!(run(src), Value::Int(8)));
    }

    #[test]
    fn hygiene_consistent_within_one_invocation() {
        // The same macro-introduced name used twice in the body must map
        // to the SAME gensym, otherwise t = something; t + t breaks.
        let src = r#"
defmacro double_via_temp(x) do
  quote do
    t = unquote(x)
    t + t
  end
end
fn main() do
  t = 100
  double_via_temp(21)
end
"#;
        // Macro returns Block([t__hyg_N = 21, t__hyg_N + t__hyg_N]) → 42.
        // Caller's t stays at 100; macro's t__hyg_N is 21+21.
        assert!(matches!(run(src), Value::Int(42)));
    }

    #[test]
    fn cross_module_macro_resolves_quote_against_home_module() {
        // Macro M.bump's body refers to bare `helper`. Resolution
        // qualifies it as M.helper inside the quote, so when expanded
        // into a different module's caller the spliced AST carries the
        // home-module path.
        let src = r#"
defmodule M do
  fn helper(x), do: x + 100
  defmacro bump(x) do
    quote do: helper(unquote(x))
  end
end
defmodule User do
  fn run(), do: M.bump(7)
end
fn main() do User.run() end
"#;
        // M.bump expands at compile time into M.helper(7) (a fully
        // qualified call), so the result is 107.
        assert!(matches!(run(src), Value::Int(107)), "expected 107, got {:?}", run(src));
    }

    #[test]
    fn imported_macro_works_unqualified() {
        let src = r#"
defmodule M do
  defmacro bump(x), do: quote do: unquote(x) + 1
end
defmodule User do
  import M, only: [bump: 1]
  fn run(), do: bump(41)
end
fn main() do User.run() end
"#;
        assert!(matches!(run(src), Value::Int(42)));
    }

    #[test]
    fn item_macro_produces_fn_def() {
        // `make_const(name, value)` builds a zero-arg fn that returns the
        // given value. Demonstrates the .16.3 item-producing path:
        // - top-level Item::MacroCall is parsed (.16.2),
        // - the macro returns {:fn_def, name_atom, body_expr},
        // - the expander splices in a real Item::Fn,
        // - the rest of the program can call it.
        let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

make_const(:answer, 42)

fn main() do
  answer()
end
"#;
        assert!(matches!(run(src), Value::Int(42)), "expected 42, got {:?}", run(src));
    }

    #[test]
    fn item_macro_produces_list_of_fns() {
        // Returning a list of :fn_def tuples splices multiple items.
        let src = r#"
defmacro pair(a, b) do
  [
    {:fn_def, :first, a},
    {:fn_def, :second, b}
  ]
end

pair(10, 20)

fn main() do
  first() + second()
end
"#;
        assert!(matches!(run(src), Value::Int(30)));
    }

    #[test]
    fn item_macro_inside_defmodule_qualifies_names() {
        // .16.5: the resolver stamps the parent module path on the
        // MacroCall so the splicer can prefix the spliced fn names.
        let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

defmodule Constants do
  make_const(:pi_ish, 314)
end

fn main() do
  Constants.pi_ish()
end
"#;
        assert!(matches!(run(src), Value::Int(314)), "expected 314, got {:?}", run(src));
    }

    #[test]
    fn no_macros_is_a_noop() {
        // Pipeline without macros must not regress.
        let src = "fn main() do 1 + 2 end";
        let mut prog = parse(src);
        expand_program(&mut prog).expect("expand");
        let interp = CompileTimeEvaluator::new();
        interp.load_program(&prog).expect("load");
        let v = interp.call_named("main", vec![]).expect("eval");
        assert!(matches!(v, Value::Int(3)));
    }

    #[test]
    fn pipe_into_call_rewrites_during_expansion() {
        let src = "fn add2(x), do: x + 2\nfn main(), do: 1 |> add2()";
        assert!(matches!(run(src), Value::Int(3)));
    }

    #[test]
    fn operator_sugars_rewrite_to_runtime_calls() {
        let body = expanded_main_body(
            r#"fn main() do
  {
    [1] ++ [2],
    [1, 2, 1] -- [1],
    "a" <> "b",
    1..3,
    1..3//2
  }
end"#,
        );
        let Expr::Tuple(values) = &body else {
            panic!("expected tuple");
        };

        assert_call_name(&values[0], "List.concat", 2);
        assert_call_name(&values[1], "List.subtract", 2);
        assert_call_name(&values[2], "Kernel.fz_binary_concat", 2);
        assert_call_name(&values[3], "Range.new", 3);
        assert_call_name(&values[4], "Range.new", 3);
    }

    #[test]
    fn membership_sugars_rewrite_to_enum_member() {
        let body = expanded_main_body(
            r#"fn main() do
  {
    2 in [1, 2, 3],
    4 not in [1, 2, 3]
  }
end"#,
        );
        let Expr::Tuple(values) = &body else {
            panic!("expected tuple");
        };

        assert_call_name(&values[0], "Enum.member?", 2);
        let Expr::UnOp(UnOp::Not, inner) = &values[1].node else {
            panic!("expected not wrapping Enum.member?, got {:?}", values[1].node);
        };
        assert_call_name(inner, "Enum.member?", 2);
    }

    fn assert_call_name(expr: &Spanned<Expr>, expected: &str, arity: usize) {
        let Expr::Call(callee, args) = &expr.node else {
            panic!("expected call, got {:?}", expr.node);
        };
        let Expr::Var(name) = &callee.node else {
            panic!("expected var callee, got {:?}", callee.node);
        };
        assert_eq!(name, expected);
        assert_eq!(args.len(), arity);
    }

    #[test]
    fn capture_shorthand_desugars_to_runnable_lambda() {
        let src = "fn main() do\n  f = &(&1 + &2)\n  f.(20, 22)\nend";
        assert!(matches!(run(src), Value::Int(42)));
    }

    #[test]
    fn bare_capture_arg_desugars_to_identity_lambda() {
        let src = "fn main() do\n  f = &1\n  f.(42)\nend";
        assert!(matches!(run(src), Value::Int(42)));
    }

    #[test]
    fn multi_clause_lambda_desugars_to_case_dispatch() {
        let src = r#"
fn main() do
  f = fn
    0 -> :zero
    n when n > 0 -> :pos
    _ -> :other
  end
  {f.(0), f.(2), f.(-1)}
end
"#;
        let got = run(src);
        assert_eq!(format!("{}", got), "{:zero, :pos, :other}");
    }

    // ----- .20.3: SpanOrigin lineage on expanded code -----

    /// Source-only fn bodies retain `SpanOrigin::Source` after expansion.
    /// (Sanity-checks the default — without this we couldn't trust any
    /// of the Expanded checks below.)
    #[test]
    fn parser_nodes_have_source_origin() {
        let src = "fn main(), do: 1 + 2";
        let mut prog = parse(src);
        expand_program(&mut prog).expect("expand");
        let Item::Fn(def) = &*prog.items[0] else { panic!() };
        let body = &def.clauses[0].body;
        assert!(matches!(body.origin, SpanOrigin::Source));
    }

    /// After a macro expands, the synthesized body carries
    /// `SpanOrigin::Expanded { macro_call: <call-site span> }`. The
    /// `macro_call` span equals the body before expansion (the call
    /// expression at the post-resolution AST).
    #[test]
    fn macro_expansion_stamps_expanded_origin() {
        let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do plus_one(41) end
"#;
        let mut prog = parse(src);

        // Capture the macro call's span BEFORE expansion replaces it.
        let call_span_before = {
            let Item::Fn(def) = &*prog
                .items
                .iter()
                .find_map(|it| match &**it {
                    Item::Fn(d) if d.name == "main" => Some(it.clone()),
                    _ => None,
                })
                .unwrap()
            else {
                panic!()
            };
            // main's body is the macro Call expression directly.
            def.clauses[0].body.span
        };

        expand_program(&mut prog).expect("expand");

        let Item::Fn(def) = &*prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(it.clone()),
                _ => None,
            })
            .unwrap()
        else {
            panic!()
        };
        let body = &def.clauses[0].body;
        // The post-expansion body is `unquote_result + 1`. It must carry
        // Expanded lineage pointing at the original call site, plus a
        // definition span pointing at the defmacro declaration.
        let (macro_call, definition) = match body.origin {
            SpanOrigin::Expanded { macro_call, definition } => (macro_call, definition),
            other => panic!("expected Expanded lineage, got {:?}", other),
        };
        assert_eq!(
            macro_call, call_span_before,
            "macro_call should point at the user's plus_one(41) call"
        );
        // The defmacro plus_one(x) do … end declaration must be the source
        // for `definition`.
        let def_span = definition.expect("definition span should be populated");
        let def_text = &src[def_span.start as usize..def_span.end as usize];
        assert!(
            def_text.starts_with("defmacro plus_one"),
            "definition span should slice the defmacro declaration, got {:?}",
            def_text
        );
        // The body's own span should also point at the call site (since
        // the decoded tree had DUMMY everywhere, we filled it in).
        assert_eq!(body.span, call_span_before);
    }

    /// Children of an expanded tree inherit the same macro_call lineage.
    /// (v1: every decoded node was DUMMY, so the walker stamps them all.)
    #[test]
    fn macro_expansion_lineage_reaches_children() {
        let src = r#"
defmacro plus_one(x) do
  quote do: unquote(x) + 1
end
fn main() do plus_one(41) end
"#;
        let mut prog = parse(src);
        expand_program(&mut prog).expect("expand");
        let Item::Fn(def) = &*prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(it.clone()),
                _ => None,
            })
            .unwrap()
        else {
            panic!()
        };
        let body = &def.clauses[0].body;
        // The body is BinOp(Add, lhs, rhs). Both operands should carry
        // Expanded lineage.
        let Expr::BinOp(_, lhs, rhs) = &body.node else {
            panic!("expected BinOp, got {:?}", body.node);
        };
        assert!(
            matches!(lhs.origin, SpanOrigin::Expanded { .. }),
            "lhs should carry Expanded lineage, got {:?}",
            lhs.origin
        );
        assert!(
            matches!(rhs.origin, SpanOrigin::Expanded { .. }),
            "rhs should carry Expanded lineage, got {:?}",
            rhs.origin
        );
    }

    /// Nested macros: when M2 expands into M1(unquote(x)) and M1 then
    /// expands, the FINAL node's lineage points at... the OUTERMOST
    /// user call site (M2(40)), per the design decision in the ticket.
    /// (Each re-expansion stamps with its own call_span, overwriting the
    /// previous Expanded marker. Since `expand_expr` recurses depth-first
    /// after the rewrite, the OUTER expansion runs last and wins.)
    #[test]
    fn nested_macro_lineage_keeps_outermost_call_site() {
        let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: m1(unquote(x)) end
fn main() do m2(40) end
"#;
        let mut prog = parse(src);
        let outer_call_span = {
            let Item::Fn(def) = &*prog
                .items
                .iter()
                .find_map(|it| match &**it {
                    Item::Fn(d) if d.name == "main" => Some(it.clone()),
                    _ => None,
                })
                .unwrap()
            else {
                panic!()
            };
            def.clauses[0].body.span
        };
        expand_program(&mut prog).expect("expand");
        let Item::Fn(def) = &*prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "main" => Some(it.clone()),
                _ => None,
            })
            .unwrap()
        else {
            panic!()
        };
        let body = &def.clauses[0].body;
        match body.origin {
            SpanOrigin::Expanded { macro_call, .. } => {
                assert_eq!(
                    macro_call, outer_call_span,
                    "outermost call site should win for nested macros"
                );
            }
            other => panic!("expected Expanded lineage, got {:?}", other),
        }
    }

    /// Item-macros that produce `:fn_def` tuples: the synthesized
    /// `Item::Fn` body inherits the Expanded lineage of the
    /// `Item::MacroCall` that produced it. `make_const(:answer, 42)`
    /// splices an `answer/0` fn whose body should point at the
    /// `make_const(...)` call site.
    #[test]
    fn item_macro_splice_body_carries_expanded_lineage() {
        let src = r#"
defmacro make_const(name, value) do
  {:fn_def, name, value}
end

make_const(:answer, 42)

fn main(), do: answer()
"#;
        let mut prog = parse(src);
        // Find the original `make_const(...)` MacroCall's span before expansion.
        let macro_call_span = prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::MacroCall { name, span, .. } if name == "make_const" => Some(*span),
                _ => None,
            })
            .expect("make_const MacroCall pre-expansion");

        expand_program(&mut prog).expect("expand");

        let Item::Fn(answer) = &*prog
            .items
            .iter()
            .find_map(|it| match &**it {
                Item::Fn(d) if d.name == "answer" => Some(it.clone()),
                _ => None,
            })
            .expect("answer fn after expansion")
        else {
            panic!()
        };
        let body = &answer.clauses[0].body;
        match body.origin {
            SpanOrigin::Expanded { macro_call, definition } => {
                assert_eq!(
                    macro_call, macro_call_span,
                    "spliced fn's body should point at the make_const(...) call"
                );
                let def_span = definition.expect("definition span on item-macro splice");
                let def_text = &src[def_span.start as usize..def_span.end as usize];
                assert!(
                    def_text.starts_with("defmacro make_const"),
                    "definition span should slice the defmacro declaration"
                );
            }
            other => panic!("expected Expanded origin, got {:?}", other),
        }
    }

    // ----- .21 step 2: MacroError carries a real call-site Span -----

    /// A runaway macro produces an `ExpansionLoop` whose Span points at
    /// the offending expression (the recursive `loop_m(...)` node), not
    /// `Span::DUMMY`. The renderer relies on this to underline source.
    #[test]
    fn expansion_loop_diag_has_real_span() {
        let src = r#"
defmacro loop_m(x) do
  quote do: loop_m(unquote(x))
end
fn main() do loop_m(0) end
"#;
        let mut prog = parse(src);
        let err = expand_program(&mut prog).unwrap_err();
        let d = err.to_diagnostic();
        assert_ne!(d.primary.span, Span::DUMMY, "ExpansionLoop should carry a real span");
        assert_eq!(d.code, codes::MACRO_EXPANSION_LOOP);
    }

    /// A body-failure carries both the call-site span (primary) and the
    /// defmacro span (secondary), so the renderer can show both locations.
    #[test]
    fn body_failed_diag_has_call_and_def_spans() {
        // Macro body that calls a non-existent function: the body errors at
        // runtime, surfacing as MacroError::BodyFailed.
        let src = r#"
defmacro bad() do
  no_such_function()
end
fn main() do bad() end
"#;
        let mut prog = parse(src);
        let err = expand_program(&mut prog).unwrap_err();
        match *err {
            MacroError::BodyFailed {
                call_span, def_span, ..
            } => {
                assert_ne!(call_span, Span::DUMMY, "BodyFailed should carry a real call_span");
                let ds = def_span.expect("def_span should be populated");
                let def_text = &src[ds.start as usize..ds.end as usize];
                assert!(
                    def_text.starts_with("defmacro bad"),
                    "def_span should slice the defmacro decl, got {:?}",
                    def_text
                );
            }
            other => panic!("expected BodyFailed, got {:?}", other),
        }
    }

    /// Definition span is `None` if the macro isn't loaded via
    /// `load_program` — sanity-checking the lookup fallback so that
    /// an unknown macro doesn't crash, just yields a None definition.
    /// (This case is reachable from the REPL when a macro is referenced
    /// before its defining input has been processed; the planner/expander
    /// errors out earlier today, but the lineage path stays safe.)
    #[test]
    fn missing_def_span_falls_back_to_none() {
        use crate::diag::{FileId, Span};
        // Build a tree manually and stamp with no definition.
        let mut e = Spanned::dummy(Expr::Int(42));
        let call_span = Span::new(FileId(0), 10, 20);
        super::stamp_expanded(&mut e, call_span, None);
        match e.origin {
            SpanOrigin::Expanded { macro_call, definition } => {
                assert_eq!(macro_call, call_span);
                assert_eq!(definition, None);
            }
            other => panic!("got {:?}", other),
        }
    }
}
