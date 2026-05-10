use crate::ast::*;
use crate::value::*;
use std::rc::Rc;

pub type EvalResult = Result<Value, String>;

pub struct Interp {
    pub globals: Env,
}

impl Interp {
    pub fn new() -> Self {
        let globals = Env::empty().child();
        let me = Self { globals };
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
                    if def.is_macro { continue; } // macros not yet expanded
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
            Value::Closure(c) => self.dispatch_clauses(c, args),
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
            Expr::Map(_) => Err("maps not implemented".into()),
            Expr::VecLit(kind, elems) => {
                let vs: Vec<Value> = elems.iter().map(|e| self.eval(e, env)).collect::<Result<_, _>>()?;
                Ok(Value::Vec(build_vec(*kind, &vs)?))
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
            Expr::With(_, _) => Err("with not implemented".into()),
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
        }
    }
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

fn value_eq(a: &Value, b: &Value) -> bool {
    use Value::*;
    match (a, b) {
        (Int(x), Int(y)) => x == y,
        (Float(x), Float(y)) => x == y,
        (Bool(x), Bool(y)) => x == y,
        (Atom(x), Atom(y)) => x.as_ref() == y.as_ref(),
        (Str(x), Str(y))   => x.as_ref() == y.as_ref(),
        (Nil, Nil) => true,
        (List(x), List(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a,b)| value_eq(a,b)),
        (Tuple(x), Tuple(y)) => x.len() == y.len() && x.iter().zip(y.iter()).all(|(a,b)| value_eq(a,b)),
        _ => false,
    }
}
