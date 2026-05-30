//! Compile-time AST evaluator.
//!
//! Macro expansion runs `defmacro` bodies through `CompileTimeEvaluator` to
//! produce expanded AST fragments. The REPL and test runner no longer use this
//! type for user runtime semantics; runtime code lowers to IR and executes on
//! `ir_interp`.
//!
//! The `CallHook` field is a vestige of the retired direct-style JIT tier-up
//! policy (fz-ul4.11.9); ir_codegen does not use it. Kept dormant for now;
//! removable once the test suite is audited for any remaining consumers.

use crate::ast::*;
use crate::exec::bitstr::*;
use crate::exec::value::*;
use std::cell::RefCell;
use std::collections::{HashMap, VecDeque};
use std::rc::Rc;

pub type EvalResult = Result<Value, String>;

/// fz-ul4.31.6 — Resolve and pretty-print a fn's `@spec` for REPL
/// `?<name>` surfacing. Returns `None` when the fn has no `@spec` OR
/// when the spec body fails to resolve (the validation pass surfaces
/// that as a `spec/violation` diagnostic; the REPL renderer just skips
/// the spec line).
pub fn format_spec_text(def: &FnDef, prog: &Program) -> Option<String> {
    let spec = def.attrs.iter().find_map(|a| match a {
        Attribute::Spec(s) => Some(s),
        _ => None,
    })?;
    let module_path: String = match def.name.rfind('.') {
        Some(i) => def.name[..i].to_string(),
        None => String::new(),
    };
    let empty = crate::type_expr::ModuleTypeEnv::new();
    let env = prog.module_type_envs.get(&module_path).unwrap_or(&empty);
    let mut ct = crate::types::ConcreteTypes;
    let resolved = crate::type_expr::resolve_spec_decl(&mut ct, spec, env).ok()?;
    let params: Vec<String> = resolved.params.iter().map(|ty| ct.display(ty)).collect();
    Some(format!(
        "({}) -> {}",
        params.join(", "),
        ct.display(&resolved.result)
    ))
}

/// Vestigial hook from the retired direct-style JIT tier-up policy (.11.9).
/// ir_codegen's tier policy is structural (always JIT), so this hook is
/// never installed in production paths today.
pub type CallHook = Rc<dyn Fn(&str, &CompileTimeEvaluator)>;

pub struct CompileTimeEvaluator {
    pub globals: Env,
    pub on_user_call: RefCell<Option<CallHook>>,
    runtime: RefCell<EvalRuntime>,
    /// Names of fns flagged `defmacro` in the loaded program(s). Used by
    /// the macro expansion pass; persists across REPL inputs so a macro
    /// defined on one line is callable from later inputs.
    pub macro_names: RefCell<std::collections::HashSet<String>>,
    /// Spans of each defmacro's full definition (FnDef.span). Looked up
    /// during expansion to populate `SpanOrigin::Expanded { definition }`
    /// on synthesized nodes, so a diagnostic can render
    /// "expanded from `Foo`, defined at <file>:<line>:<col>".
    pub macro_def_spans: RefCell<std::collections::HashMap<String, crate::diag::Span>>,
    /// Per-invocation hygiene table set by the macro expander before
    /// running a macro body. When `Some`, `reify_with_unquotes` renames
    /// Var/Match-lhs names through this map (lazily filling in fresh
    /// gensyms) so the caller's locals can't collide with the macro's.
    /// `None` outside of macro expansion — quote then preserves names
    /// literally.
    pub gensym_table: RefCell<Option<std::collections::HashMap<String, String>>>,
    /// Qualified-module-path → `@moduledoc` text. Populated by
    /// `load_program` (and the REPL load path) so `?M` can find the doc.
    pub module_docs: RefCell<std::collections::HashMap<String, String>>,
}

#[derive(Debug)]
struct EvalRuntime {
    current_pid: u32,
    next_pid: u32,
    next_ref: u64,
    mailboxes: HashMap<u32, VecDeque<Value>>,
}

impl EvalRuntime {
    fn new() -> Self {
        let mut mailboxes = HashMap::new();
        mailboxes.insert(1, VecDeque::new());
        Self {
            current_pid: 1,
            next_pid: 2,
            next_ref: 1,
            mailboxes,
        }
    }
}

impl CompileTimeEvaluator {
    pub fn new() -> Self {
        let globals = Env::empty().child();
        let me = Self {
            globals,
            on_user_call: RefCell::new(None),
            runtime: RefCell::new(EvalRuntime::new()),
            macro_names: RefCell::new(std::collections::HashSet::new()),
            macro_def_spans: RefCell::new(std::collections::HashMap::new()),
            gensym_table: RefCell::new(None),
            module_docs: RefCell::new(std::collections::HashMap::new()),
        };
        me.install_builtins();
        me
    }

    fn install_builtins(&self) {
        let builtins: &[(&'static str, usize, BuiltinFn)] = &[
            ("print", 1, |args, _| {
                println!("{}", args[0]);
                Ok(Value::Nil)
            }),
            ("is_integer", 1, |args, _| {
                Ok(Value::Bool(matches!(args[0], Value::Int(_))))
            }),
            ("is_atom", 1, |args, _| {
                Ok(Value::Bool(matches!(args[0], Value::Atom(_))))
            }),
            ("length", 1, |args, _| match &args[0] {
                Value::List(xs) => Ok(Value::Int(xs.len() as i64)),
                _ => Err("length/1 expects a list".into()),
            }),
            ("map_get", 2, |args, _| match &args[0] {
                Value::Map(m) => Ok(m.get(&args[1]).cloned().unwrap_or(Value::Nil)),
                _ => Err("map_get(map, key)".into()),
            }),
            ("map_put", 3, |args, _| match &args[0] {
                Value::Map(m) => Ok(Value::Map(Rc::new(m.put(args[1].clone(), args[2].clone())))),
                _ => Err("map_put(map, key, val)".into()),
            }),
            ("Utf8.valid?", 1, |args, _| {
                Ok(Value::Bool(
                    utf8_bytes(&args[0]).is_some_and(|bytes| std::str::from_utf8(&bytes).is_ok()),
                ))
            }),
            ("Utf8.from_bytes", 1, |args, _| match utf8_bytes(&args[0]) {
                Some(bytes) if std::str::from_utf8(&bytes).is_ok() => {
                    Ok(Value::Tuple(Rc::new(vec![
                        Value::Atom(Rc::from("ok")),
                        args[0].clone(),
                    ])))
                }
                _ => Ok(Value::Tuple(Rc::new(vec![
                    Value::Atom(Rc::from("error")),
                    Value::Atom(Rc::from("invalid_utf8")),
                ]))),
            }),
            // Handled inside CompileTimeEvaluator::apply so they can access the REPL/eval
            // task registry without exposing CompileTimeEvaluator through BuiltinFn.
            ("self", 0, |_, _| {
                unreachable!("self/0 handled by CompileTimeEvaluator::apply")
            }),
            ("send", 2, |_, _| {
                unreachable!("send/2 handled by CompileTimeEvaluator::apply")
            }),
            ("spawn", 1, |_, _| {
                unreachable!("spawn/1 handled by CompileTimeEvaluator::apply")
            }),
            ("make_ref", 0, |_, _| {
                unreachable!("make_ref/0 handled by CompileTimeEvaluator::apply")
            }),
            ("receive", 0, |_, _| {
                unreachable!("receive/0 handled by CompileTimeEvaluator::apply")
            }),
        ];
        for (name, arity, func) in builtins {
            self.globals.bind(
                name,
                Value::Builtin(Rc::new(Builtin {
                    name,
                    arity: *arity,
                    func: *func,
                })),
            );
        }
    }

    pub fn load_program(&self, prog: &Program) -> Result<(), String> {
        // Merge any moduledocs flatten_modules captured. Later loads
        // overwrite earlier ones for the same path (REPL re-defining a
        // module replaces its @moduledoc).
        for (path, doc) in &prog.module_docs {
            self.module_docs
                .borrow_mut()
                .insert(path.clone(), doc.clone());
        }
        // Two-pass-ish: bind names first so clauses can be mutually recursive,
        // but since each FnDef is a single Closure value capturing self.globals,
        // a single pass works as long as the closure looks up names lazily
        // through the env (which it does).
        for item in &prog.items {
            match &**item {
                Item::Fn(def) => {
                    if def.is_macro {
                        self.macro_names.borrow_mut().insert(def.name.clone());
                        self.macro_def_spans
                            .borrow_mut()
                            .insert(def.name.clone(), def.span);
                    }
                    // Macros load alongside regular fns so the expansion pass
                    // can dispatch them by name through the same interp.
                    let spec_text = format_spec_text(def, prog);
                    let closure = Value::Closure(Rc::new(Closure {
                        name: Some(def.name.clone()),
                        clauses: def.clauses.clone(),
                        env: self.globals.clone(),
                        doc: def.doc().map(String::from),
                        spec_text,
                    }));
                    self.globals.bind(&def.name, closure);
                }
                // Modules should have been flattened by `resolve::flatten_modules`
                // before reaching this point. If one slips through (e.g. a
                // direct test caller), error loudly.
                Item::Module(_)
                | Item::Protocol(_)
                | Item::ProtocolImpl(_)
                | Item::Alias { .. }
                | Item::Import { .. } => {
                    return Err("load_program: pre-resolution Item reached interp; \
                     resolve::flatten_modules must run after parse"
                        .into());
                }
                // Skipped during the macro-expansion pre-load (the
                // expander needs the interp ready to call macros, but the
                // MacroCalls themselves haven't been expanded yet). Once
                // expansion finishes, no MacroCalls survive.
                Item::MacroCall { .. } => continue,
            }
        }
        Ok(())
    }

    pub fn call_named(&self, name: &str, args: Vec<Value>) -> EvalResult {
        let f = self
            .globals
            .lookup(name)
            .ok_or_else(|| format!("undefined: {}", name))?;
        self.apply(&f, args)
    }

    pub fn apply(&self, callee: &Value, args: Vec<Value>) -> EvalResult {
        match callee {
            Value::Builtin(b) => {
                if args.len() != b.arity && !runtime_builtin_accepts_arity(b.name, args.len()) {
                    return Err(format!(
                        "{}/{} called with {} args",
                        b.name,
                        b.arity,
                        args.len()
                    ));
                }
                if let Some(value) = self.apply_runtime_builtin(b.name, &args)? {
                    return Ok(value);
                }
                let apply_cb = |c: &Value, a: Vec<Value>| self.apply(c, a);
                (b.func)(&args, &apply_cb)
            }
            Value::Closure(c) => {
                if let Some(name) = &c.name {
                    let hook = self.on_user_call.borrow().clone();
                    if let Some(h) = hook {
                        h(name, self);
                    }
                }
                self.dispatch_clauses(c, args)
            }
            other => Err(format!("not callable: {}", other)),
        }
    }

    fn apply_runtime_builtin(&self, name: &str, args: &[Value]) -> Result<Option<Value>, String> {
        match name {
            "self" => {
                let pid = self.runtime.borrow().current_pid;
                Ok(Some(Value::Int(pid as i64)))
            }
            "send" => {
                let Value::Int(pid) = args[0] else {
                    return Err("send/2: pid must be an integer".into());
                };
                let pid = u32::try_from(pid).map_err(|_| format!("send/2: bad pid {}", pid))?;
                let msg = args[1].clone();
                self.runtime
                    .borrow_mut()
                    .mailboxes
                    .entry(pid)
                    .or_default()
                    .push_back(msg.clone());
                Ok(Some(msg))
            }
            "spawn" => {
                let pid = {
                    let mut runtime = self.runtime.borrow_mut();
                    let pid = runtime.next_pid;
                    runtime.next_pid += 1;
                    runtime.mailboxes.entry(pid).or_default();
                    pid
                };
                let prev = {
                    let mut runtime = self.runtime.borrow_mut();
                    let prev = runtime.current_pid;
                    runtime.current_pid = pid;
                    prev
                };
                let result = self.apply(&args[0], Vec::new());
                self.runtime.borrow_mut().current_pid = prev;
                result?;
                Ok(Some(Value::Int(pid as i64)))
            }
            "make_ref" => {
                let id = {
                    let mut runtime = self.runtime.borrow_mut();
                    let id = runtime.next_ref;
                    runtime.next_ref += 1;
                    id
                };
                Ok(Some(Value::Ref(id)))
            }
            "receive" => Ok(Some(self.receive_next()?)),
            _ => Ok(None),
        }
    }

    fn receive_next(&self) -> EvalResult {
        let pid = self.runtime.borrow().current_pid;
        self.runtime
            .borrow_mut()
            .mailboxes
            .entry(pid)
            .or_default()
            .pop_front()
            .ok_or_else(|| "receive/0 would block on an empty mailbox".to_string())
    }

    fn receive_match(
        &self,
        clauses: &[MatchClause],
        after: &Option<Box<AfterClause>>,
        env: &Env,
    ) -> EvalResult {
        let pid = self.runtime.borrow().current_pid;
        let messages: Vec<Value> = self
            .runtime
            .borrow()
            .mailboxes
            .get(&pid)
            .map(|mailbox| mailbox.iter().cloned().collect())
            .unwrap_or_default();

        for (msg_idx, msg) in messages.iter().enumerate() {
            for cl in clauses {
                let frame = env.child();
                if !match_pattern(&cl.pattern.node, msg, &frame) {
                    continue;
                }
                if let Some(g) = &cl.guard {
                    let gv = self.eval(g, &frame)?;
                    if !is_truthy(&gv) {
                        continue;
                    }
                }
                let removed = self
                    .runtime
                    .borrow_mut()
                    .mailboxes
                    .entry(pid)
                    .or_default()
                    .remove(msg_idx)
                    .expect("message index from snapshot must still exist");
                debug_assert!(value_eq(&removed, msg));
                return self.eval(&cl.body, &frame);
            }
        }

        if let Some(after) = after {
            let timeout = self.eval(&after.timeout, env)?;
            match timeout {
                Value::Int(0) => self.eval(&after.body, env),
                Value::Atom(ref atom) if atom.as_ref() == "infinity" => {
                    Err("receive would block on an empty mailbox".into())
                }
                other => Err(format!(
                    "receive after {} is not supported by the AST evaluator",
                    other
                )),
            }
        } else {
            Err("receive would block on an empty mailbox".into())
        }
    }

    fn dispatch_clauses(&self, c: &Closure, args: Vec<Value>) -> EvalResult {
        for clause in &c.clauses {
            if clause.params.len() != args.len() {
                continue;
            }
            if !clause
                .param_annotations
                .iter()
                .zip(args.iter())
                .all(|(ann, value)| param_annotation_matches(ann.as_ref(), value))
            {
                continue;
            }
            let frame = c.env.child();
            let mut all_match = true;
            for (p, v) in clause.params.iter().zip(args.iter()) {
                if !match_pattern(&p.node, v, &frame) {
                    all_match = false;
                    break;
                }
            }
            if !all_match {
                continue;
            }
            if let Some(g) = &clause.guard {
                let gv = self.eval(g, &frame)?;
                if !is_truthy(&gv) {
                    continue;
                }
            }
            return self.eval(&clause.body, &frame);
        }
        Err(format!(
            "no clause matched in {}/{} with args [{}]",
            c.name.as_deref().unwrap_or("anon"),
            c.clauses.first().map(|cl| cl.params.len()).unwrap_or(0),
            args.iter()
                .map(|v| format!("{}", v))
                .collect::<Vec<_>>()
                .join(", "),
        ))
    }

    pub fn eval(&self, e: &Spanned<Expr>, env: &Env) -> EvalResult {
        match &e.node {
            Expr::Int(n) => Ok(Value::Int(*n)),
            Expr::Float(f) => Ok(Value::Float(*f)),
            Expr::Binary(bytes) => Ok(Value::Binary(Rc::from(bytes.as_slice()))),
            Expr::Atom(a) => Ok(Value::Atom(Rc::from(a.as_str()))),
            Expr::Bool(b) => Ok(Value::Bool(*b)),
            Expr::Nil => Ok(Value::Nil),
            Expr::Var(n) => env.lookup(n).ok_or_else(|| format!("undefined: {}", n)),
            // fz-swt.5: explicit fn reference resolves through the same
            // global-name lookup as a bare name. The arity check lives in
            // call-site dispatch on the resulting Closure.
            Expr::FnRef { name, arity: _ } => env
                .lookup(name)
                .ok_or_else(|| format!("undefined: {}", name)),
            Expr::Ascribe(inner, _) => self.eval(inner, env),
            Expr::List(xs, tail) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.eval(x, env)?);
                }
                if let Some(t) = tail {
                    let tv = self.eval(t, env)?;
                    match tv {
                        Value::List(rest) => out.extend(rest.iter().cloned()),
                        Value::Nil => {}
                        other => {
                            return Err(format!("list cons tail must be a list, got {}", other));
                        }
                    }
                }
                Ok(Value::List(Rc::new(out)))
            }
            Expr::Tuple(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.eval(x, env)?);
                }
                Ok(Value::Tuple(Rc::new(out)))
            }
            Expr::Map(pairs) => {
                let mut m = FzMap::new();
                for (k, v) in pairs {
                    let kv = self.eval(k, env)?;
                    let vv = self.eval(v, env)?;
                    m = m.put(kv, vv);
                }
                Ok(Value::Map(Rc::new(m)))
            }
            Expr::MapUpdate(base, pairs) => {
                let bv = self.eval(base, env)?;
                let m = match bv {
                    Value::Map(m) => m,
                    other => return Err(format!("`%{{m | ...}}` requires a map, got {}", other)),
                };
                let mut out = (*m).clone();
                for (k, v) in pairs {
                    let kv = self.eval(k, env)?;
                    let vv = self.eval(v, env)?;
                    out = out.put(kv, vv);
                }
                Ok(Value::Map(Rc::new(out)))
            }
            Expr::Index(target, key) => {
                let tv = self.eval(target, env)?;
                let kv = self.eval(key, env)?;
                match tv {
                    Value::Map(m) => Ok(m.get(&kv).cloned().unwrap_or(Value::Nil)),
                    other => Err(format!("index `[]` on non-map: {}", other)),
                }
            }
            Expr::Bitstring(fields) => {
                let mut writer = BitWriter::new();
                for f in fields {
                    let v = self.eval(&f.value, env)?;
                    encode_field(&v, &f.spec, env, &mut writer)?;
                }
                Ok(writer.finalize())
            }
            Expr::Call(f, args) => {
                let callee = self.eval(f, env)?;
                let mut vs = Vec::with_capacity(args.len());
                for a in args {
                    vs.push(self.eval(a, env)?);
                }
                self.apply(&callee, vs)
            }
            Expr::BinOp(op, l, r) => {
                if *op == BinOp::Pipe {
                    return Err("BinOp::Pipe should be desugared before eval".into());
                }
                if *op == BinOp::And {
                    let lv = self.eval(l, env)?;
                    return if is_truthy(&lv) {
                        self.eval(r, env)
                    } else {
                        Ok(lv)
                    };
                }
                if *op == BinOp::Or {
                    let lv = self.eval(l, env)?;
                    return if is_truthy(&lv) {
                        Ok(lv)
                    } else {
                        self.eval(r, env)
                    };
                }
                let lv = self.eval(l, env)?;
                let rv = self.eval(r, env)?;
                eval_binop(*op, &lv, &rv)
            }
            Expr::UnOp(op, x) => {
                let v = self.eval(x, env)?;
                match (op, v) {
                    (UnOp::Neg, Value::Int(n)) => Ok(Value::Int(-n)),
                    (UnOp::Neg, Value::Float(f)) => Ok(Value::Float(-f)),
                    (UnOp::Not, v) => Ok(Value::Bool(!is_truthy(&v))),
                    (UnOp::Neg, v) => Err(format!("`-` on {}", v)),
                }
            }
            Expr::If(c, t, els) => {
                let cv = self.eval(c, env)?;
                if is_truthy(&cv) {
                    self.eval(t, env)
                } else if let Some(e) = els {
                    self.eval(e, env)
                } else {
                    Ok(Value::Nil)
                }
            }
            Expr::Case(Some(scrut), clauses) => {
                let sv = self.eval(scrut, env)?;
                for cl in clauses {
                    let frame = env.child();
                    if !match_pattern(&cl.pattern.node, &sv, &frame) {
                        continue;
                    }
                    if let Some(g) = &cl.guard {
                        let gv = self.eval(g, &frame)?;
                        if !is_truthy(&gv) {
                            continue;
                        }
                    }
                    return self.eval(&cl.body, &frame);
                }
                Err(format!("no case clause matched: {}", sv))
            }
            Expr::Case(None, _) => Err("headless case must be desugared before eval".into()),
            Expr::Cond(_) => Err("cond not implemented".into()),
            Expr::Receive { clauses, after } => self.receive_match(clauses, after, env),
            Expr::With(bindings, body, else_clauses) => {
                let frame = env.child();
                for b in bindings {
                    match b {
                        WithBinding::Match(pat, e) => {
                            let v = self.eval(e, &frame)?;
                            if !match_pattern(&pat.node, &v, &frame) {
                                for cl in else_clauses {
                                    let f2 = frame.child();
                                    if !match_pattern(&cl.pattern.node, &v, &f2) {
                                        continue;
                                    }
                                    if let Some(g) = &cl.guard {
                                        let gv = self.eval(g, &f2)?;
                                        if !is_truthy(&gv) {
                                            continue;
                                        }
                                    }
                                    return self.eval(&cl.body, &f2);
                                }
                                if !else_clauses.is_empty() {
                                    return Err(format!("no else clause matched in `with`: {}", v));
                                }
                                return Ok(v);
                            }
                        }
                        WithBinding::Bare(e) => {
                            self.eval(e, &frame)?;
                        }
                    }
                }
                self.eval(body, &frame)
            }
            Expr::Match(pat, rhs) => {
                let v = self.eval(rhs, env)?;
                if !match_pattern(&pat.node, &v, env) {
                    return Err(format!("match failed: {}", v));
                }
                Ok(v)
            }
            Expr::Block(exprs) => {
                let frame = env.child();
                let mut last = Value::Nil;
                for e in exprs {
                    last = self.eval(e, &frame)?;
                }
                Ok(last)
            }
            Expr::Lambda(params, body) => Ok(Value::Closure(Rc::new(Closure {
                name: None,
                clauses: vec![FnClause {
                    param_annotations: vec![None; params.len()],
                    params: params.clone(),
                    guard: None,
                    body: (**body).clone(),
                    span: e.span,
                }],
                env: env.clone(),
                doc: None,
                spec_text: None,
            }))),
            Expr::Quote(inner) => self.reify_with_unquotes(inner, env),
            Expr::Unquote(_) => Err("unquote used outside `quote`".into()),
        }
    }

    /// Walk an Expr like `ast_value::expr_to_value`, but when an
    /// `Expr::Unquote(e)` is encountered, eval `e` in `env` and splice the
    /// resulting Value into the reified output.
    fn reify_with_unquotes(&self, e: &Spanned<Expr>, env: &Env) -> EvalResult {
        use crate::exec::ast_value::expr_to_value;
        match &e.node {
            Expr::Unquote(inner) => self.eval(inner, env),
            Expr::Ascribe(inner, _) => self.reify_with_unquotes(inner, env),

            Expr::Var(name) => Ok(reified_var(self.hygiene_rename(name))),

            Expr::Match(pat, rhs) => {
                use crate::ast::Pattern;
                let lhs_name = match &pat.node {
                    Pattern::Var(n) => n.clone(),
                    _ => return Err("quote: only Pattern::Var on lhs of `=` in v1".into()),
                };
                let lhs = reified_var(self.hygiene_rename(&lhs_name));
                let rv = self.reify_with_unquotes(rhs, env)?;
                Ok(quoted_node("=", Value::List(Rc::new(vec![lhs, rv]))))
            }

            // Compound exprs: recurse so unquotes inside them get spliced.
            Expr::List(xs, tail) => {
                if tail.is_some() {
                    return Err("quote: list cons-tail not yet supported".into());
                }
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.reify_with_unquotes(x, env)?);
                }
                Ok(Value::List(Rc::new(out)))
            }
            Expr::Tuple(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.reify_with_unquotes(x, env)?);
                }
                if out.len() == 2 {
                    Ok(Value::Tuple(Rc::new(out)))
                } else {
                    Ok(quoted_node("{}", Value::List(Rc::new(out))))
                }
            }
            Expr::Call(callee, args) => {
                let name = match &callee.node {
                    Expr::Var(n) => n.clone(),
                    _ => return Err("quote: only direct named calls supported".into()),
                };
                let mut arg_vs = Vec::with_capacity(args.len());
                for a in args {
                    arg_vs.push(self.reify_with_unquotes(a, env)?);
                }
                Ok(quoted_node(&name, Value::List(Rc::new(arg_vs))))
            }
            Expr::BinOp(op, l, r) => {
                let lv = self.reify_with_unquotes(l, env)?;
                let rv = self.reify_with_unquotes(r, env)?;
                Ok(quoted_node(
                    crate::exec::ast_value::binop_atom(*op),
                    Value::List(Rc::new(vec![lv, rv])),
                ))
            }
            Expr::UnOp(op, x) => {
                let xv = self.reify_with_unquotes(x, env)?;
                Ok(quoted_node(
                    crate::exec::ast_value::unop_atom(*op),
                    Value::List(Rc::new(vec![xv])),
                ))
            }
            Expr::Block(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs {
                    out.push(self.reify_with_unquotes(x, env)?);
                }
                Ok(quoted_node("__block__", Value::List(Rc::new(out))))
            }
            Expr::If(c, t, els) => {
                let cv = self.reify_with_unquotes(c, env)?;
                let tv = self.reify_with_unquotes(t, env)?;
                let mut kw = vec![tuple_kv("do", tv)];
                if let Some(e) = els {
                    kw.push(tuple_kv("else", self.reify_with_unquotes(e, env)?));
                }
                Ok(quoted_node(
                    "if",
                    Value::List(Rc::new(vec![cv, Value::List(Rc::new(kw))])),
                ))
            }

            // Leaves with no possible unquote inside: defer to reifier.
            _ => expr_to_value(e),
        }
    }
}

#[cfg(test)]
#[allow(clippy::items_after_test_module)] // mid-file: quote/unquote/`...`-pattern tests
// sit between the parse/lower helpers above and
// the CompileTimeEvaluator impl that runs them.
mod quote_tests {
    use super::*;
    use crate::parser::Parser;
    use crate::parser::lexer::Lexer;

    /// Eval `expr_src` (wrapped in a fn body, called from main) and return
    /// the value it produced.
    fn eval_in_main(expr_src: &str) -> Value {
        let src = format!("fn _go() do {} end\nfn main() do _go() end", expr_src);
        let toks = Lexer::new(&src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let interp = CompileTimeEvaluator::new();
        interp.load_program(&prog).expect("load");
        // Evaluate _go directly so we get its return value, not main's nil.
        interp.call_named("_go", vec![]).expect("eval")
    }

    #[test]
    fn quote_literal_is_self() {
        assert!(matches!(eval_in_main("quote do: 42"), Value::Int(42)));
        assert!(matches!(eval_in_main("quote do: :ok"), Value::Atom(s) if &*s == "ok"));
    }

    #[test]
    fn quote_var_is_3_tuple() {
        let v = eval_in_main("quote do: foo");
        let Value::Tuple(t) = &v else {
            panic!("expected tuple, got {}", v)
        };
        assert_eq!(t.len(), 3);
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "foo"));
    }

    #[test]
    fn quote_binop_reifies() {
        let v = eval_in_main("quote do: 1 + 2");
        let Value::Tuple(t) = &v else { panic!() };
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "+"));
        let Value::List(args) = &t[2] else { panic!() };
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0], Value::Int(1)));
        assert!(matches!(&args[1], Value::Int(2)));
    }

    #[test]
    fn unquote_splices_value() {
        // x = 5; quote do: 1 + unquote(x)  →  {:+, %{}, [1, 5]}
        let v = eval_in_main("x = 5\nquote do: 1 + unquote(x)");
        let Value::Tuple(t) = &v else { panic!() };
        let Value::List(args) = &t[2] else { panic!() };
        assert!(matches!(&args[0], Value::Int(1)));
        assert!(matches!(&args[1], Value::Int(5)));
    }

    #[test]
    fn unquote_in_call_args() {
        let v = eval_in_main("y = :hello\nquote do: dbg(unquote(y), 1)");
        let Value::Tuple(t) = &v else { panic!() };
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "dbg"));
        let Value::List(args) = &t[2] else { panic!() };
        assert!(matches!(&args[0], Value::Atom(s) if &**s == "hello"));
        assert!(matches!(&args[1], Value::Int(1)));
    }

    #[test]
    fn unquote_outside_quote_errors() {
        let src = "fn main() do unquote(1) end";
        let toks = Lexer::new(src).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let interp = CompileTimeEvaluator::new();
        interp.load_program(&prog).unwrap();
        let res = interp.call_named("main", vec![]);
        assert!(
            res.is_err(),
            "expected unquote-outside-quote error, got {:?}",
            res
        );
        assert!(
            res.as_ref().unwrap_err().contains("unquote"),
            "expected message to mention unquote, got {:?}",
            res
        );
    }

    #[test]
    fn make_ref_returns_distinct_opaque_refs() {
        let v = eval_in_main("{make_ref(), make_ref()}");
        let Value::Tuple(items) = v else {
            panic!("expected tuple, got {}", v);
        };
        assert_eq!(items.len(), 2);
        assert!(matches!(items[0], Value::Ref(_)));
        assert!(matches!(items[1], Value::Ref(_)));
        assert!(
            !value_eq(&items[0], &items[1]),
            "two make_ref/0 calls must produce distinct refs"
        );
    }

    #[test]
    fn map_update_inserts_missing_keys() {
        let v = eval_in_main("m = %{a: 1}\nn = %{m | b: 2}\nn[:b]");
        assert!(matches!(v, Value::Int(2)), "got {}", v);
    }

    #[test]
    fn typed_param_annotations_filter_clause_dispatch() {
        let src = "\
fn check(x :: integer) do :is_int end
fn check(x) do :other end
fn main() do {check(42), check(:foo)} end
";
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let interp = CompileTimeEvaluator::new();
        interp.load_program(&prog).expect("load");
        let v = interp.call_named("main", vec![]).expect("eval");
        let Value::Tuple(items) = v else {
            panic!("expected tuple, got {}", v);
        };
        assert!(matches!(&items[0], Value::Atom(atom) if atom.as_ref() == "is_int"));
        assert!(matches!(&items[1], Value::Atom(atom) if atom.as_ref() == "other"));
    }
}

impl CompileTimeEvaluator {
    /// If a hygiene table is active, return the gensym for `name`,
    /// allocating one on first use. Otherwise return `name` unchanged.
    fn hygiene_rename(&self, name: &str) -> String {
        let mut tbl_ref = self.gensym_table.borrow_mut();
        let Some(tbl) = tbl_ref.as_mut() else {
            return name.to_string();
        };
        if let Some(g) = tbl.get(name) {
            return g.clone();
        }
        let id = next_gensym_id();
        let fresh = format!("{}__hyg_{}", name, id);
        tbl.insert(name.to_string(), fresh.clone());
        fresh
    }
}

fn next_gensym_id() -> u64 {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    COUNTER.fetch_add(1, Ordering::Relaxed)
}

fn reified_var(name: String) -> Value {
    Value::Tuple(Rc::new(vec![
        Value::Atom(Rc::from(name.as_str())),
        Value::Map(Rc::new(crate::exec::value::FzMap::new())),
        Value::Atom(Rc::from("user")),
    ]))
}

fn quoted_node(name: &str, args: Value) -> Value {
    Value::Tuple(Rc::new(vec![
        Value::Atom(Rc::from(name)),
        Value::Map(Rc::new(crate::exec::value::FzMap::new())),
        args,
    ]))
}

fn tuple_kv(key: &str, val: Value) -> Value {
    Value::Tuple(Rc::new(vec![Value::Atom(Rc::from(key)), val]))
}

fn is_truthy(v: &Value) -> bool {
    !matches!(v, Value::Bool(false) | Value::Nil)
}

fn utf8_bytes(value: &Value) -> Option<Vec<u8>> {
    match value {
        Value::Binary(bytes) => Some(bytes.to_vec()),
        Value::BitStr(bs) if bs.bit_len.is_multiple_of(8) => {
            Some(bs.bytes[..bs.bit_len / 8].to_vec())
        }
        _ => None,
    }
}

fn runtime_builtin_accepts_arity(name: &str, arity: usize) -> bool {
    matches!((name, arity), ("spawn", 2))
}

fn param_annotation_matches(annotation: Option<&TypeExprBody>, value: &Value) -> bool {
    let Some(annotation) = annotation else {
        return true;
    };
    let [tok] = annotation.0.as_slice() else {
        return true;
    };
    let crate::parser::lexer::Tok::Ident(name) = &tok.tok else {
        return true;
    };
    match name.as_str() {
        "any" => true,
        "integer" | "int" => matches!(value, Value::Int(_)),
        "float" => matches!(value, Value::Float(_)),
        "atom" => matches!(value, Value::Atom(_)),
        "bool" | "boolean" => matches!(value, Value::Bool(_)),
        "binary" => matches!(value, Value::Binary(_)),
        "nil" => matches!(value, Value::Nil),
        "list" => matches!(value, Value::List(_)),
        "map" => matches!(value, Value::Map(_)),
        "tuple" => matches!(value, Value::Tuple(_)),
        "ref" => matches!(value, Value::Ref(_)),
        _ => true,
    }
}

fn eval_binop(op: BinOp, a: &Value, b: &Value) -> EvalResult {
    use Value::*;
    Ok(match (op, a, b) {
        (BinOp::Add, Int(x), Int(y)) => Int(x + y),
        (BinOp::Sub, Int(x), Int(y)) => Int(x - y),
        (BinOp::Mul, Int(x), Int(y)) => Int(x * y),
        (BinOp::Div, Int(x), Int(y)) => {
            if *y == 0 {
                return Err("integer division by zero".into());
            }
            Int(x / y)
        }
        (BinOp::Rem, Int(x), Int(y)) => {
            if *y == 0 {
                return Err("integer mod by zero".into());
            }
            Int(x % y)
        }
        (BinOp::Add, Float(x), Float(y)) => Float(x + y),
        (BinOp::Sub, Float(x), Float(y)) => Float(x - y),
        (BinOp::Mul, Float(x), Float(y)) => Float(x * y),
        (BinOp::Div, Float(x), Float(y)) => Float(x / y),

        (BinOp::Eq, x, y) => Bool(value_eq(x, y)),
        (BinOp::Neq, x, y) => Bool(!value_eq(x, y)),
        (BinOp::Lt, Int(x), Int(y)) => Bool(x < y),
        (BinOp::LtEq, Int(x), Int(y)) => Bool(x <= y),
        (BinOp::Gt, Int(x), Int(y)) => Bool(x > y),
        (BinOp::GtEq, Int(x), Int(y)) => Bool(x >= y),
        (BinOp::Lt, Float(x), Float(y)) => Bool(x < y),
        (BinOp::LtEq, Float(x), Float(y)) => Bool(x <= y),
        (BinOp::Gt, Float(x), Float(y)) => Bool(x > y),
        (BinOp::GtEq, Float(x), Float(y)) => Bool(x >= y),

        (op, a, b) => return Err(format!("type error: {:?} {} {}", op, a, b)),
    })
}
