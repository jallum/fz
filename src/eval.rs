use crate::ast::*;
use crate::bitstr::*;
use crate::value::*;
use std::cell::RefCell;
use std::rc::Rc;

pub type EvalResult = Result<Value, String>;

/// Hook invoked when a user-defined Closure is applied. Receives the user
/// fn name and the Interp so it can patch globals (used by the JIT tier-up
/// policy: count calls per user_name, JIT-compile when hot, rebind to
/// Value::Jit).
pub type CallHook = Rc<dyn Fn(&str, &Interp)>;

pub struct Interp {
    pub globals: Env,
    pub on_user_call: RefCell<Option<CallHook>>,
    /// Names of fns flagged `defmacro` in the loaded program(s). Used by
    /// the macro expansion pass; persists across REPL inputs so a macro
    /// defined on one line is callable from later inputs.
    pub macro_names: RefCell<std::collections::HashSet<String>>,
}

impl Interp {
    pub fn new() -> Self {
        let globals = Env::empty().child();
        let me = Self {
            globals,
            on_user_call: RefCell::new(None),
            macro_names: RefCell::new(std::collections::HashSet::new()),
        };
        me.install_builtins();
        me
    }

    fn install_builtins(&self) {
        let builtins: &[(&'static str, usize, BuiltinFn)] = &[
            ("print", 1, |args, _| { println!("{}", args[0]); Ok(Value::Nil) }),
            ("is_integer", 1, |args, _| Ok(Value::Bool(matches!(args[0], Value::Int(_))))),
            ("is_atom", 1, |args, _| Ok(Value::Bool(matches!(args[0], Value::Atom(_))))),
            ("is_vec", 1, |args, _| Ok(Value::Bool(matches!(args[0], Value::Vec(_))))),
            ("length", 1, |args, _| match &args[0] {
                Value::List(xs) => Ok(Value::Int(xs.len() as i64)),
                Value::Vec(v) => Ok(Value::Int(v.len() as i64)),
                _ => Err("length/1 expects a list or vec".into()),
            }),
            ("vec_get", 2, |args, _| match (&args[0], &args[1]) {
                (Value::Vec(v), Value::Int(i)) => v.get(*i as usize)
                    .ok_or_else(|| format!("vec_get: index {} out of bounds (len {})", i, v.len())),
                _ => Err("vec_get(vec, int)".into()),
            }),
            ("vec_map", 2, |args, apply| {
                // data-first for pipes: vec_map(vec, fn)
                let v = match &args[0] { Value::Vec(v) => v, _ => return Err("vec_map(vec, fn)".into()) };
                let f = &args[1];
                let n = v.len();
                // Specialize on element kind for the eventual SIMD path; for now,
                // we just preserve kind when the result type is consistent.
                match v {
                    FzVec::I64(xs) => {
                        let mut out: Vec<i64> = Vec::with_capacity(n);
                        let mut promote_f64: Option<Vec<f64>> = None;
                        for x in xs.iter() {
                            let r = apply(f, vec![Value::Int(*x)])?;
                            match r {
                                Value::Int(n) => {
                                    if let Some(ref mut buf) = promote_f64 { buf.push(n as f64); }
                                    else { out.push(n); }
                                }
                                Value::Float(fl) => {
                                    let mut buf: Vec<f64> = out.drain(..).map(|i| i as f64).collect();
                                    buf.push(fl);
                                    promote_f64 = Some(buf);
                                }
                                other => return Err(format!("vec_map on i64 vec: fn returned non-numeric {}", other)),
                            }
                        }
                        Ok(Value::Vec(match promote_f64 {
                            Some(b) => FzVec::F64(Rc::new(b)),
                            None => FzVec::I64(Rc::new(out)),
                        }))
                    }
                    FzVec::F64(xs) => {
                        let mut out = Vec::with_capacity(n);
                        for x in xs.iter() {
                            match apply(f, vec![Value::Float(*x)])? {
                                Value::Float(fl) => out.push(fl),
                                Value::Int(i) => out.push(i as f64),
                                other => return Err(format!("vec_map on f64 vec: fn returned non-numeric {}", other)),
                            }
                        }
                        Ok(Value::Vec(FzVec::F64(Rc::new(out))))
                    }
                    FzVec::U8(xs) => {
                        let mut out = Vec::with_capacity(n);
                        for x in xs.iter() {
                            match apply(f, vec![Value::Int(*x as i64)])? {
                                Value::Int(i) if (0..=255).contains(&i) => out.push(i as u8),
                                Value::Int(i) => return Err(format!("vec_map on byte vec: {} out of u8 range", i)),
                                other => return Err(format!("vec_map on byte vec: fn returned non-int {}", other)),
                            }
                        }
                        Ok(Value::Vec(FzVec::U8(Rc::new(out))))
                    }
                    FzVec::Bit(_) => Err("vec_map on bit vec not yet supported".into()),
                }
            }),
            ("map_get", 2, |args, _| match &args[0] {
                Value::Map(m) => Ok(m.get(&args[1]).cloned().unwrap_or(Value::Nil)),
                _ => Err("map_get(map, key)".into()),
            }),
            ("map_put", 3, |args, _| match &args[0] {
                Value::Map(m) => Ok(Value::Map(Rc::new(m.put(args[1].clone(), args[2].clone())))),
                _ => Err("map_put(map, key, val)".into()),
            }),
            ("vec_reduce", 3, |args, apply| {
                // data-first: vec_reduce(vec, init, fn)
                let v = match &args[0] { Value::Vec(v) => v, _ => return Err("vec_reduce(vec, init, fn)".into()) };
                let mut acc = args[1].clone();
                let f = &args[2];
                let n = v.len();
                for i in 0..n {
                    let x = v.get(i).unwrap();
                    acc = apply(f, vec![acc, x])?;
                }
                Ok(acc)
            }),
        ];
        for (name, arity, func) in builtins {
            self.globals.bind(name, Value::Builtin(Rc::new(Builtin {
                name, arity: *arity, func: *func
            })));
        }
    }

    pub fn load_program(&self, prog: &Program) -> Result<(), String> {
        // Two-pass-ish: bind names first so clauses can be mutually recursive,
        // but since each FnDef is a single Closure value capturing self.globals,
        // a single pass works as long as the closure looks up names lazily
        // through the env (which it does).
        for item in &prog.items {
            match &**item {
                Item::Fn(def) => {
                    if def.is_macro {
                        self.macro_names.borrow_mut().insert(def.name.clone());
                    }
                    // Macros load alongside regular fns so the expansion pass
                    // can dispatch them by name through the same interp.
                    let closure = Value::Closure(Rc::new(Closure {
                        name: Some(def.name.clone()),
                        clauses: def.clauses.clone(),
                        env: self.globals.clone(),
                    }));
                    self.globals.bind(&def.name, closure);
                }
            }
        }
        Ok(())
    }

    pub fn call_named(&self, name: &str, args: Vec<Value>) -> EvalResult {
        let f = self.globals.lookup(name).ok_or_else(|| format!("undefined: {}", name))?;
        self.apply(&f, args)
    }

    pub fn apply(&self, callee: &Value, args: Vec<Value>) -> EvalResult {
        match callee {
            Value::Builtin(b) => {
                if args.len() != b.arity {
                    return Err(format!("{}/{} called with {} args", b.name, b.arity, args.len()));
                }
                let apply_cb = |c: &Value, a: Vec<Value>| self.apply(c, a);
                (b.func)(&args, &apply_cb)
            }
            Value::Closure(c) => {
                if let Some(name) = &c.name {
                    let hook = self.on_user_call.borrow().clone();
                    if let Some(h) = hook { h(name, self); }
                }
                self.dispatch_clauses(c, args)
            }
            Value::Jit(j) => crate::jit::call_jit(j, args),
            other => Err(format!("not callable: {}", other)),
        }
    }

    fn dispatch_clauses(&self, c: &Closure, args: Vec<Value>) -> EvalResult {
        for clause in &c.clauses {
            if clause.params.len() != args.len() { continue; }
            let frame = c.env.child();
            let mut all_match = true;
            for (p, v) in clause.params.iter().zip(args.iter()) {
                if !match_pattern(p, v, &frame) { all_match = false; break; }
            }
            if !all_match { continue; }
            if let Some(g) = &clause.guard {
                let gv = self.eval(g, &frame)?;
                if !is_truthy(&gv) { continue; }
            }
            return self.eval(&clause.body, &frame);
        }
        Err(format!(
            "no clause matched in {}/{} with args [{}]",
            c.name.as_deref().unwrap_or("anon"),
            c.clauses.first().map(|cl| cl.params.len()).unwrap_or(0),
            args.iter().map(|v| format!("{}", v)).collect::<Vec<_>>().join(", "),
        ))
    }

    pub fn eval(&self, e: &Expr, env: &Env) -> EvalResult {
        match e {
            Expr::Int(n)     => Ok(Value::Int(*n)),
            Expr::Float(f)   => Ok(Value::Float(*f)),
            Expr::Str(s)     => Ok(Value::Str(Rc::from(s.as_str()))),
            Expr::Atom(a)    => Ok(Value::Atom(Rc::from(a.as_str()))),
            Expr::Bool(b)    => Ok(Value::Bool(*b)),
            Expr::Nil        => Ok(Value::Nil),
            Expr::Var(n) => env.lookup(n).ok_or_else(|| format!("undefined: {}", n)),
            Expr::List(xs, tail) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs { out.push(self.eval(x, env)?); }
                if let Some(t) = tail {
                    let tv = self.eval(t, env)?;
                    match tv {
                        Value::List(rest) => out.extend(rest.iter().cloned()),
                        Value::Nil => {}
                        other => return Err(format!("list cons tail must be a list, got {}", other)),
                    }
                }
                Ok(Value::List(Rc::new(out)))
            }
            Expr::Tuple(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs { out.push(self.eval(x, env)?); }
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
                    if !out.has(&kv) {
                        return Err(format!("update: key {} not present in map", kv));
                    }
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
            Expr::VecLit(kind, elems) => {
                let vs: Vec<Value> = elems.iter().map(|e| self.eval(e, env)).collect::<Result<_, _>>()?;
                Ok(Value::Vec(build_vec(*kind, &vs)?))
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
                // Pipe lowering happens in BinOp; here we just have direct calls.
                let callee = self.eval(f, env)?;
                let mut vs = Vec::with_capacity(args.len());
                for a in args { vs.push(self.eval(a, env)?); }
                self.apply(&callee, vs)
            }
            Expr::Dot(_, _) => Err("module access not implemented".into()),
            Expr::BinOp(op, l, r) => {
                if *op == BinOp::Pipe {
                    // a |> f(args)  ==  f(a, args)
                    // a |> f         ==  f(a)
                    let lv = self.eval(l, env)?;
                    return match &**r {
                        Expr::Call(callee, args) => {
                            let cv = self.eval(callee, env)?;
                            let mut vs = Vec::with_capacity(args.len() + 1);
                            vs.push(lv);
                            for a in args { vs.push(self.eval(a, env)?); }
                            self.apply(&cv, vs)
                        }
                        _ => {
                            let cv = self.eval(r, env)?;
                            self.apply(&cv, vec![lv])
                        }
                    };
                }
                if *op == BinOp::And {
                    let lv = self.eval(l, env)?;
                    return if is_truthy(&lv) { self.eval(r, env) } else { Ok(lv) };
                }
                if *op == BinOp::Or {
                    let lv = self.eval(l, env)?;
                    return if is_truthy(&lv) { Ok(lv) } else { self.eval(r, env) };
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
            Expr::Case(scrut, clauses) => {
                let sv = self.eval(scrut, env)?;
                for cl in clauses {
                    let frame = env.child();
                    if !match_pattern(&cl.pattern, &sv, &frame) { continue; }
                    if let Some(g) = &cl.guard {
                        let gv = self.eval(g, &frame)?;
                        if !is_truthy(&gv) { continue; }
                    }
                    return self.eval(&cl.body, &frame);
                }
                Err(format!("no case clause matched: {}", sv))
            }
            Expr::Cond(_) => Err("cond not implemented".into()),
            Expr::With(bindings, body, else_clauses) => {
                let frame = env.child();
                for b in bindings {
                    match b {
                        WithBinding::Match(pat, e) => {
                            let v = self.eval(e, &frame)?;
                            if !match_pattern(pat, &v, &frame) {
                                // Failed match: try else clauses, fall back to value itself
                                for cl in else_clauses {
                                    let f2 = frame.child();
                                    if !match_pattern(&cl.pattern, &v, &f2) { continue; }
                                    if let Some(g) = &cl.guard {
                                        let gv = self.eval(g, &f2)?;
                                        if !is_truthy(&gv) { continue; }
                                    }
                                    return self.eval(&cl.body, &f2);
                                }
                                if !else_clauses.is_empty() {
                                    return Err(format!("no else clause matched in `with`: {}", v));
                                }
                                return Ok(v);
                            }
                        }
                        WithBinding::Bare(e) => { self.eval(e, &frame)?; }
                    }
                }
                self.eval(body, &frame)
            }
            Expr::Match(pat, rhs) => {
                let v = self.eval(rhs, env)?;
                if !match_pattern(pat, &v, env) {
                    return Err(format!("match failed: {}", v));
                }
                Ok(v)
            }
            Expr::Block(exprs) => {
                let frame = env.child();
                let mut last = Value::Nil;
                for e in exprs { last = self.eval(e, &frame)?; }
                Ok(last)
            }
            Expr::Lambda(params, body) => {
                Ok(Value::Closure(Rc::new(Closure {
                    name: None,
                    clauses: vec![FnClause {
                        params: params.clone(),
                        guard: None,
                        body: (**body).clone(),
                    }],
                    env: env.clone(),
                })))
            }
            Expr::Quote(inner) => self.reify_with_unquotes(inner, env),
            Expr::Unquote(_) => Err("unquote used outside `quote`".into()),
        }
    }

    /// Walk an Expr like `ast_value::expr_to_value`, but when an
    /// `Expr::Unquote(e)` is encountered, eval `e` in `env` and splice the
    /// resulting Value into the reified output.
    fn reify_with_unquotes(&self, e: &Expr, env: &Env) -> EvalResult {
        use crate::ast_value::expr_to_value;
        match e {
            Expr::Unquote(inner) => self.eval(inner, env),

            // Compound exprs: recurse so unquotes inside them get spliced.
            Expr::List(xs, tail) => {
                if tail.is_some() {
                    return Err("quote: list cons-tail not yet supported".into());
                }
                let mut out = Vec::with_capacity(xs.len());
                for x in xs { out.push(self.reify_with_unquotes(x, env)?); }
                Ok(Value::List(Rc::new(out)))
            }
            Expr::Tuple(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs { out.push(self.reify_with_unquotes(x, env)?); }
                if out.len() == 2 {
                    Ok(Value::Tuple(Rc::new(out)))
                } else {
                    Ok(quoted_node("{}", Value::List(Rc::new(out))))
                }
            }
            Expr::Call(callee, args) => {
                let name = match &**callee {
                    Expr::Var(n) => n.clone(),
                    _ => return Err("quote: only direct named calls supported".into()),
                };
                let mut arg_vs = Vec::with_capacity(args.len());
                for a in args { arg_vs.push(self.reify_with_unquotes(a, env)?); }
                Ok(quoted_node(&name, Value::List(Rc::new(arg_vs))))
            }
            Expr::BinOp(op, l, r) => {
                let lv = self.reify_with_unquotes(l, env)?;
                let rv = self.reify_with_unquotes(r, env)?;
                Ok(quoted_node(crate::ast_value::binop_atom(*op),
                    Value::List(Rc::new(vec![lv, rv]))))
            }
            Expr::UnOp(op, x) => {
                let xv = self.reify_with_unquotes(x, env)?;
                Ok(quoted_node(crate::ast_value::unop_atom(*op),
                    Value::List(Rc::new(vec![xv]))))
            }
            Expr::Block(xs) => {
                let mut out = Vec::with_capacity(xs.len());
                for x in xs { out.push(self.reify_with_unquotes(x, env)?); }
                Ok(quoted_node("__block__", Value::List(Rc::new(out))))
            }
            Expr::If(c, t, els) => {
                let cv = self.reify_with_unquotes(c, env)?;
                let tv = self.reify_with_unquotes(t, env)?;
                let mut kw = vec![tuple_kv("do", tv)];
                if let Some(e) = els {
                    kw.push(tuple_kv("else", self.reify_with_unquotes(e, env)?));
                }
                Ok(quoted_node("if", Value::List(Rc::new(vec![
                    cv, Value::List(Rc::new(kw)),
                ]))))
            }

            // Leaves with no possible unquote inside: defer to reifier.
            _ => expr_to_value(e),
        }
    }
}

#[cfg(test)]
mod quote_tests {
    use super::*;
    use crate::lexer::Lexer;
    use crate::parser::Parser;

    /// Eval `expr_src` (wrapped in a fn body, called from main) and return
    /// the value it produced.
    fn eval_in_main(expr_src: &str) -> Value {
        let src = format!(
            "fn _go() do {} end\nfn main() do _go() end",
            expr_src
        );
        let toks = Lexer::new(&src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let interp = Interp::new();
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
        let Value::Tuple(t) = &v else { panic!("expected tuple, got {}", v) };
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
        let v = eval_in_main("y = :hello\nquote do: print(unquote(y), 1)");
        let Value::Tuple(t) = &v else { panic!() };
        assert!(matches!(&t[0], Value::Atom(s) if &**s == "print"));
        let Value::List(args) = &t[2] else { panic!() };
        assert!(matches!(&args[0], Value::Atom(s) if &**s == "hello"));
        assert!(matches!(&args[1], Value::Int(1)));
    }

    #[test]
    fn unquote_outside_quote_errors() {
        let src = "fn main() do unquote(1) end";
        let toks = Lexer::new(src).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let interp = Interp::new();
        interp.load_program(&prog).unwrap();
        let res = interp.call_named("main", vec![]);
        assert!(res.is_err(), "expected unquote-outside-quote error, got {:?}", res);
        assert!(res.as_ref().unwrap_err().contains("unquote"),
            "expected message to mention unquote, got {:?}", res);
    }
}

fn quoted_node(name: &str, args: Value) -> Value {
    Value::Tuple(Rc::new(vec![
        Value::Atom(Rc::from(name)),
        Value::Map(Rc::new(crate::value::FzMap::new())),
        args,
    ]))
}

fn tuple_kv(key: &str, val: Value) -> Value {
    Value::Tuple(Rc::new(vec![Value::Atom(Rc::from(key)), val]))
}

fn build_vec(kind: VecKind, vs: &[Value]) -> Result<FzVec, String> {
    match kind {
        VecKind::Numeric => {
            let any_float = vs.iter().any(|v| matches!(v, Value::Float(_)));
            if any_float {
                let mut buf = Vec::with_capacity(vs.len());
                for v in vs {
                    match v {
                        Value::Float(f) => buf.push(*f),
                        Value::Int(i)   => buf.push(*i as f64),
                        other => return Err(format!("~v[..] expects numbers, got {}", other)),
                    }
                }
                Ok(FzVec::F64(Rc::new(buf)))
            } else {
                let mut buf = Vec::with_capacity(vs.len());
                for v in vs {
                    match v {
                        Value::Int(i) => buf.push(*i),
                        other => return Err(format!("~v[..] expects numbers, got {}", other)),
                    }
                }
                Ok(FzVec::I64(Rc::new(buf)))
            }
        }
        VecKind::Bytes => {
            let mut buf = Vec::with_capacity(vs.len());
            for v in vs {
                match v {
                    Value::Int(i) if (0..=255).contains(i) => buf.push(*i as u8),
                    Value::Int(i) => return Err(format!("~b[..] element {} out of u8 range", i)),
                    other => return Err(format!("~b[..] expects bytes, got {}", other)),
                }
            }
            Ok(FzVec::U8(Rc::new(buf)))
        }
        VecKind::Bits => {
            let mut bits = Vec::with_capacity(vs.len());
            for v in vs {
                match v {
                    Value::Int(0) => bits.push(0),
                    Value::Int(1) => bits.push(1),
                    Value::Bool(false) => bits.push(0),
                    Value::Bool(true)  => bits.push(1),
                    other => return Err(format!("~bits[..] expects 0/1 or true/false, got {}", other)),
                }
            }
            Ok(FzVec::Bit(Rc::new(BitVec::from_bits(&bits))))
        }
    }
}

fn is_truthy(v: &Value) -> bool {
    match v {
        Value::Bool(false) | Value::Nil => false,
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
            if *y == 0 { return Err("integer division by zero".into()); }
            Int(x / y)
        }
        (BinOp::Rem, Int(x), Int(y)) => {
            if *y == 0 { return Err("integer mod by zero".into()); }
            Int(x % y)
        }
        (BinOp::Add, Float(x), Float(y)) => Float(x + y),
        (BinOp::Sub, Float(x), Float(y)) => Float(x - y),
        (BinOp::Mul, Float(x), Float(y)) => Float(x * y),
        (BinOp::Div, Float(x), Float(y)) => Float(x / y),

        (BinOp::Eq, x, y)  => Bool(value_eq(x, y)),
        (BinOp::Neq, x, y) => Bool(!value_eq(x, y)),
        (BinOp::Lt, Int(x), Int(y))   => Bool(x < y),
        (BinOp::LtEq, Int(x), Int(y)) => Bool(x <= y),
        (BinOp::Gt, Int(x), Int(y))   => Bool(x > y),
        (BinOp::GtEq, Int(x), Int(y)) => Bool(x >= y),
        (BinOp::Lt, Float(x), Float(y))   => Bool(x < y),
        (BinOp::LtEq, Float(x), Float(y)) => Bool(x <= y),
        (BinOp::Gt, Float(x), Float(y))   => Bool(x > y),
        (BinOp::GtEq, Float(x), Float(y)) => Bool(x >= y),

        (op, a, b) => return Err(format!("type error: {:?} {} {}", op, a, b)),
    })
}

