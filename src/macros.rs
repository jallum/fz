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
use crate::ast_value::{expr_to_value, value_to_expr};
use crate::diag::{Diagnostic, Span, SpanOrigin, codes};
use crate::eval::CompileTimeEvaluator;
use crate::value::Value;

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
                format!(
                    "macro expansion exceeded {} levels (likely a runaway macro)",
                    max_depth
                ),
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

impl std::fmt::Display for MacroError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.to_diagnostic().message)
    }
}

impl std::error::Error for MacroError {}

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
    macros: &std::collections::HashSet<String>,
) -> Result<(), Box<MacroError>> {
    prog.items = expand_item_list(prog.items.clone(), interp, macros)?;
    Ok(())
}

fn expand_item_list(
    items: Vec<std::rc::Rc<Item>>,
    interp: &CompileTimeEvaluator,
    macros: &std::collections::HashSet<String>,
) -> Result<Vec<std::rc::Rc<Item>>, Box<MacroError>> {
    let mut out: Vec<std::rc::Rc<Item>> = Vec::new();
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
                *interp.gensym_table.borrow_mut() = Some(std::collections::HashMap::new());
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
                    out.push(std::rc::Rc::new(it));
                }
            }
            Item::Module(m) => {
                let new_items = expand_item_list(m.items.clone(), interp, macros)?;
                out.push(std::rc::Rc::new(Item::Module(ModuleDef {
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
                    let span = crate::diag::Span::DUMMY;
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
    macros: &std::collections::HashSet<String>,
) -> Result<(), Box<MacroError>> {
    for item in &mut prog.items {
        // We Rc::make_mut to get an exclusive ref. At this point in the
        // pipeline the program has just been parsed and isn't shared.
        let item_mut = std::rc::Rc::make_mut(item);
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
                return Err(Box::new(MacroError::PostResolutionLeftover {
                    span: m.span,
                }));
            }
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
pub fn collect_macros(prog: &Program) -> std::collections::HashSet<String> {
    let mut out = std::collections::HashSet::new();
    for item in &prog.items {
        match &**item {
            Item::Fn(def) => {
                if def.is_macro {
                    out.insert(def.name.clone());
                }
            }
            Item::Module(_) | Item::Alias { .. } | Item::Import { .. } | Item::MacroCall { .. } => {
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
    macros: &std::collections::HashSet<String>,
    depth: usize,
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
        *interp.gensym_table.borrow_mut() = Some(std::collections::HashMap::new());
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
        return expand_expr(e, interp, macros, depth + 1);
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
        | Expr::FnRef { .. } => {}

        Expr::List(xs, tail) => {
            for x in xs {
                expand_expr(x, interp, macros, depth)?;
            }
            if let Some(t) = tail {
                expand_expr(t, interp, macros, depth)?;
            }
        }
        Expr::Tuple(xs) | Expr::Block(xs) => {
            for x in xs {
                expand_expr(x, interp, macros, depth)?;
            }
        }
        Expr::Bitstring(fields) => {
            for f in fields {
                expand_expr(&mut f.value, interp, macros, depth)?;
            }
        }
        Expr::Map(pairs) => {
            for (k, v) in pairs {
                expand_expr(k, interp, macros, depth)?;
                expand_expr(v, interp, macros, depth)?;
            }
        }
        Expr::MapUpdate(m, pairs) => {
            expand_expr(m, interp, macros, depth)?;
            for (k, v) in pairs {
                expand_expr(k, interp, macros, depth)?;
                expand_expr(v, interp, macros, depth)?;
            }
        }
        Expr::Index(o, i) => {
            expand_expr(o, interp, macros, depth)?;
            expand_expr(i, interp, macros, depth)?;
        }
        Expr::Call(callee, args) => {
            expand_expr(callee, interp, macros, depth)?;
            for a in args.iter_mut() {
                expand_expr(a, interp, macros, depth)?;
            }
            if let Expr::BinOp(BinOp::Pipe, lhs, rhs) = &callee.node {
                let mut new_args = Vec::with_capacity(args.len() + 1);
                new_args.push((**lhs).clone());
                new_args.extend(args.iter().cloned());
                e.node = Expr::Call(Box::new((**rhs).clone()), new_args);
            }
        }
        Expr::BinOp(op, l, r) => {
            expand_expr(l, interp, macros, depth)?;
            expand_expr(r, interp, macros, depth)?;
            if *op == BinOp::Pipe {
                let lhs = (**l).clone();
                match &mut r.node {
                    Expr::Call(callee, args) => {
                        let mut new_args = Vec::with_capacity(args.len() + 1);
                        new_args.push(lhs);
                        new_args.extend(args.iter().cloned());
                        e.node = Expr::Call(callee.clone(), new_args);
                    }
                    Expr::Case(scrut @ None, arms) => {
                        *scrut = Some(Box::new(lhs));
                        e.node = Expr::Case(scrut.clone(), arms.clone());
                    }
                    _ => {}
                }
            }
        }
        Expr::UnOp(_, x) | Expr::Ascribe(x, _) => expand_expr(x, interp, macros, depth)?,
        Expr::If(c, t, els) => {
            expand_expr(c, interp, macros, depth)?;
            expand_expr(t, interp, macros, depth)?;
            if let Some(e) = els {
                expand_expr(e, interp, macros, depth)?;
            }
        }
        Expr::Case(scr, arms) => {
            if let Some(scr) = scr {
                expand_expr(scr, interp, macros, depth)?;
            }
            for arm in arms {
                expand_expr(&mut arm.body, interp, macros, depth)?;
                if let Some(g) = &mut arm.guard {
                    expand_expr(g, interp, macros, depth)?;
                }
            }
        }
        Expr::Cond(pairs) => {
            for (c, b) in pairs {
                expand_expr(c, interp, macros, depth)?;
                expand_expr(b, interp, macros, depth)?;
            }
        }
        Expr::With(bindings, body, else_clauses) => {
            for b in bindings {
                match b {
                    WithBinding::Match(_, e) => expand_expr(e, interp, macros, depth)?,
                    WithBinding::Bare(e) => expand_expr(e, interp, macros, depth)?,
                }
            }
            expand_expr(body, interp, macros, depth)?;
            for arm in else_clauses {
                expand_expr(&mut arm.body, interp, macros, depth)?;
                if let Some(g) = &mut arm.guard {
                    expand_expr(g, interp, macros, depth)?;
                }
            }
        }
        Expr::Match(_, rhs) => expand_expr(rhs, interp, macros, depth)?,
        Expr::Lambda(_, body) => expand_expr(body, interp, macros, depth)?,
        // fz-5vj — recurse into receive clauses' bodies/guards and the
        // after timeout/body. Patterns are leaves at expansion time
        // (no macro-call positions inside patterns).
        Expr::Receive { clauses, after } => {
            for arm in clauses {
                expand_expr(&mut arm.body, interp, macros, depth)?;
                if let Some(g) = &mut arm.guard {
                    expand_expr(g, interp, macros, depth)?;
                }
            }
            if let Some(af) = after {
                expand_expr(&mut af.timeout, interp, macros, depth)?;
                expand_expr(&mut af.body, interp, macros, depth)?;
            }
        }

        Expr::Quote(_) | Expr::Unquote(_) => {}
    }
    Ok(())
}

/// Walk `e` and stamp every node with `SpanOrigin::Expanded { macro_call,
/// definition }`. DUMMY spans are rewritten to `macro_call` so a diagnostic
/// on a child of the expansion always points at the user's call site. Real
/// (non-DUMMY) spans encountered inside the tree are preserved — that's
/// the v2 case where Values carry their own spans through quote round-trip;
/// in v1 every decoded node is DUMMY so nothing is preserved yet.
fn stamp_expanded(e: &mut Spanned<Expr>, macro_call: Span, definition: Option<Span>) {
    let origin = SpanOrigin::Expanded {
        macro_call,
        definition,
    };
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
        | Expr::FnRef { .. } => {}
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
        Expr::Index(o, i) => {
            stamp_expanded(o, macro_call, definition);
            stamp_expanded(i, macro_call, definition);
        }
        Expr::Call(callee, args) => {
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
        Expr::Lambda(params, body) => {
            for p in params {
                stamp_pattern(p, macro_call, definition);
            }
            stamp_expanded(body, macro_call, definition);
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
    let origin = SpanOrigin::Expanded {
        macro_call,
        definition,
    };
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
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    fn parse(src: &str) -> Program {
        let toks = Lexer::new(src).tokenize().expect("lex");
        Parser::new(toks).parse_program().expect("parse")
    }

    /// Run the full pipeline (parse → flatten → expand → eval main) and
    /// return main's return value.
    fn run(src: &str) -> crate::value::Value {
        let prog = parse(src);
        let mut ct = crate::types::ConcreteTypes;
        let mut prog = crate::resolve::flatten_modules(&mut ct, prog).expect("flatten");
        expand_program(&mut prog).expect("expand");
        let interp = CompileTimeEvaluator::new();
        interp.load_program(&prog).expect("load");
        interp.call_named("main", vec![]).expect("eval")
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
        assert!(matches!(run(src), crate::value::Value::Int(42)));
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
        assert!(matches!(run(src), crate::value::Value::Int(60)));
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
        assert!(matches!(run(src), crate::value::Value::Int(21)));
    }

    #[test]
    fn nested_macro_expansion() {
        // Macro M2 wraps M1's output. Expander must re-expand the result.
        let src = r#"
defmacro m1(x) do quote do: unquote(x) + 1 end
defmacro m2(x) do quote do: m1(unquote(x)) end
fn main() do m2(40) end
"#;
        assert!(matches!(run(src), crate::value::Value::Int(41)));
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
        assert!(matches!(run(src), crate::value::Value::Int(6)));
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
            matches!(v, crate::value::Value::Int(1)),
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
        assert!(matches!(run(src), crate::value::Value::Int(8)));
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
        assert!(matches!(run(src), crate::value::Value::Int(42)));
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
        assert!(
            matches!(run(src), crate::value::Value::Int(107)),
            "expected 107, got {:?}",
            run(src)
        );
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
        assert!(matches!(run(src), crate::value::Value::Int(42)));
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
        assert!(
            matches!(run(src), crate::value::Value::Int(42)),
            "expected 42, got {:?}",
            run(src)
        );
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
        assert!(matches!(run(src), crate::value::Value::Int(30)));
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
        assert!(
            matches!(run(src), crate::value::Value::Int(314)),
            "expected 314, got {:?}",
            run(src)
        );
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
        assert!(matches!(v, crate::value::Value::Int(3)));
    }

    #[test]
    fn pipe_into_call_rewrites_during_expansion() {
        let src = "fn add2(x), do: x + 2\nfn main(), do: 1 |> add2()";
        assert!(matches!(run(src), crate::value::Value::Int(3)));
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
        let Item::Fn(def) = &*prog.items[0] else {
            panic!()
        };
        let body = &def.clauses[0].body;
        assert!(matches!(body.origin, crate::diag::SpanOrigin::Source));
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
            crate::diag::SpanOrigin::Expanded {
                macro_call,
                definition,
            } => (macro_call, definition),
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
            matches!(lhs.origin, crate::diag::SpanOrigin::Expanded { .. }),
            "lhs should carry Expanded lineage, got {:?}",
            lhs.origin
        );
        assert!(
            matches!(rhs.origin, crate::diag::SpanOrigin::Expanded { .. }),
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
            crate::diag::SpanOrigin::Expanded { macro_call, .. } => {
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
            crate::diag::SpanOrigin::Expanded {
                macro_call,
                definition,
            } => {
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
        assert_ne!(
            d.primary.span,
            Span::DUMMY,
            "ExpansionLoop should carry a real span"
        );
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
                call_span,
                def_span,
                ..
            } => {
                assert_ne!(
                    call_span,
                    Span::DUMMY,
                    "BodyFailed should carry a real call_span"
                );
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
        use crate::diag::Span;
        // Build a tree manually and stamp with no definition.
        let mut e = Spanned::dummy(Expr::Int(42));
        let call_span = Span::new(crate::diag::FileId(0), 10, 20);
        super::stamp_expanded(&mut e, call_span, None);
        match e.origin {
            crate::diag::SpanOrigin::Expanded {
                macro_call,
                definition,
            } => {
                assert_eq!(macro_call, call_span);
                assert_eq!(definition, None);
            }
            other => panic!("got {:?}", other),
        }
    }
}
