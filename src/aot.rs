#![cfg(any())] // fz-ul4.11.9: legacy direct-style codegen retired; preserved verbatim for intent verification once ir_codegen reaches feature parity (.11.10-.11.14). To re-enable, drop this attr.
//! fz-ul4.12.3 — AOT driver: source → standalone executable.
//!
//! Pipeline: parse → type → monomorphize (typer Descr → codegen LowerTy) →
//! lower each fn → ObjectModule → object file → cc + fz-runtime staticlib →
//! binary.
//!
//! Standalone per the .12 scope decision: any feature outside the in-scope
//! subset (heap types, multi-clause, closures, etc.) is a compile-time
//! error, named with the source location. The runtime is the fz-runtime
//! staticlib; no interpreter is shipped in the binary.

use crate::ast::*;
use crate::codegen::{lower_fn, AtomInterner, FnSig, LowerError, LowerResult, LowerTy};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::typer::Typer;
use crate::types::*;
use cranelift_codegen::ir::{self, AbiParam, ExternalName, InstBuilder, Signature, UserExternalName, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Typer Descr → codegen LowerTy
// ---------------------------------------------------------------------------

/// Map a typer descriptor to a unique LowerTy. Returns `None` for descriptors
/// outside the .12 in-scope subset (unions across kinds, heap types, `any`,
/// imprecise singletons, etc.).
pub fn derive_lowerty(d: &Descr) -> Option<LowerTy> {
    if d.is_empty() {
        return None;
    }

    // Reject anything outside scalar+tuple before classifying.
    let any_list = !d.lists.is_empty();
    let any_func = !d.funcs.is_empty();
    let any_map = !d.maps.is_empty();
    let any_str = !d.strs.is_none();
    let basic_other = (d.basic.raw()
        & !(BasicBits::NIL.raw() | BasicBits::BOOL.raw()))
        != 0;
    if any_list || any_func || any_map || any_str || basic_other {
        return None;
    }

    let has_nil = d.basic.contains_all(BasicBits::NIL);
    let has_bool = d.basic.contains_all(BasicBits::BOOL);
    let has_int = !d.ints.is_none();
    let has_float = !d.floats.is_none();
    let has_atom = !d.atoms.is_none();
    let has_tuple = !d.tuples.is_empty();

    // Exactly one axis populated.
    let count = [has_nil, has_bool, has_int, has_float, has_atom, has_tuple]
        .iter()
        .filter(|b| **b)
        .count();
    if count != 1 {
        return None;
    }

    if has_nil { return Some(LowerTy::Nil); }
    if has_bool { return Some(LowerTy::Bool); }
    if has_int { return Some(LowerTy::I64); }
    if has_float { return Some(LowerTy::F64); }
    if has_atom { return Some(LowerTy::Atom); }

    // Tuple: must be a single positive shape with no negatives, all-scalar
    // components recursively reducible.
    if d.tuples.len() == 1 {
        let conj = &d.tuples[0];
        if conj.neg.is_empty() && conj.pos.len() == 1 {
            let elems: Option<Vec<LowerTy>> =
                conj.pos[0].elems.iter().map(derive_lowerty).collect();
            return elems.map(LowerTy::Tuple);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Monomorphization
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct MonoFn {
    /// Codegen symbol name. Equals `user_name` for non-polymorphic fns; for
    /// polymorphic / higher-order specializations it's `user_name__<slot-mangle>`.
    pub name: String,
    /// The user-facing fn name shared by all specializations of this def.
    pub user_name: String,
    pub sig: FnSig,
    pub def: FnDef,
    /// Higher-order param bindings (fz-ul4.4.2). Maps a param-name to the
    /// concrete user fn it's β-reduced to in this specialization. Empty for
    /// non-HOF specializations. The codegen drops these params from the
    /// runtime signature and rewrites in-body calls to the param to direct
    /// calls to the bound user fn.
    pub param_bindings: std::collections::HashMap<String, String>,
}

/// One arg position at a call site. Either a runtime-present scalar/tuple
/// value (carries its LowerTy) or a higher-order binding to a top-level user
/// fn (β-reduced at codegen time, no runtime presence).
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum CallSlot {
    Lower(LowerTy),
    UserFn(String),
}

/// Mangle a callsite's (user_name, slots) into a candidate codegen symbol
/// name. Used both at specializer time (to assign symbols) and at call-site
/// lowering time (to dispatch). Backward-compatible with the LowerTy-only
/// scheme: if every slot is `Lower`, the output matches the prior format.
pub fn mangle_call(user_name: &str, slots: &[CallSlot]) -> String {
    let mut s = String::from(user_name);
    s.push_str("__");
    for (i, slot) in slots.iter().enumerate() {
        if i > 0 { s.push('_'); }
        match slot {
            CallSlot::Lower(lt) => mangle_lt(lt, &mut s),
            CallSlot::UserFn(n) => { s.push('F'); s.push_str(n); }
        }
    }
    s
}

fn mangle_lt(lt: &LowerTy, out: &mut String) {
    match lt {
        LowerTy::I64 => out.push_str("I64"),
        LowerTy::F64 => out.push_str("F64"),
        LowerTy::Bool => out.push_str("Bool"),
        LowerTy::Atom => out.push_str("Atom"),
        LowerTy::Nil => out.push_str("Nil"),
        LowerTy::Tuple(ts) => {
            out.push('T');
            out.push_str(&ts.len().to_string());
            for t in ts { out.push('_'); mangle_lt(t, out); }
        }
    }
}

/// Build a slot list for a call site. Each arg position becomes either
/// `Lower(lt)` (runtime scalar/tuple) or `UserFn(name)` (β-reducible HOF
/// arg). Returns None when an arg is neither: that call site can't drive a
/// specialization in the .12 subset.
pub fn build_call_slots(
    args: &[Descr],
    fn_args: Option<&[Option<String>]>,
) -> Option<Vec<CallSlot>> {
    let mut slots = Vec::with_capacity(args.len());
    for (i, arg) in args.iter().enumerate() {
        if let Some(lt) = derive_lowerty(arg) {
            slots.push(CallSlot::Lower(lt));
            continue;
        }
        // Not a runtime-lowerable scalar — try HOF binding.
        let bound = fn_args
            .and_then(|fa| fa.get(i).cloned().flatten());
        match bound {
            Some(name) => slots.push(CallSlot::UserFn(name)),
            None => return None,
        }
    }
    Some(slots)
}

/// Walk a HOF specialization's body for syntactic calls to its β-reduced
/// params. For each call, derive each arg's `CallSlot` from the spec's
/// runtime env (a map of AST param name → LowerTy for non-bound positions
/// plus the param_bindings for HOF positions). Returns a list of
/// `(callee_user_name, slots)` pairs that the bound callees need to be
/// specialized at.
///
/// Conservative: only handles the simple-and-common shapes — args that are
/// scalar literals, runtime params (Var → LowerTy), bound HOF params
/// (Var → UserFn), or self-calls of the bound callee with the same args.
/// More complex arg expressions (binops, nested calls) yield None for that
/// arg and the implied call is dropped.
pub fn discover_implied_hof_specs(
    def: &FnDef,
    runtime_env: &std::collections::HashMap<String, LowerTy>,
    param_bindings: &std::collections::HashMap<String, String>,
) -> Vec<(String, Vec<CallSlot>)> {
    let mut out = Vec::new();
    for clause in &def.clauses {
        walk_for_implied(&clause.body, runtime_env, param_bindings, &mut out);
    }
    out
}

fn walk_for_implied(
    e: &Expr,
    runtime_env: &std::collections::HashMap<String, LowerTy>,
    param_bindings: &std::collections::HashMap<String, String>,
    out: &mut Vec<(String, Vec<CallSlot>)>,
) {
    use crate::ast::Expr;
    if let Expr::Call(callee, args) = e {
        if let Expr::Var(pname) = &**callee {
            if let Some(target) = param_bindings.get(pname) {
                let mut slots: Option<Vec<CallSlot>> = Some(Vec::with_capacity(args.len()));
                for a in args {
                    let s = match a {
                        Expr::Int(_) => Some(CallSlot::Lower(LowerTy::I64)),
                        Expr::Float(_) => Some(CallSlot::Lower(LowerTy::F64)),
                        Expr::Bool(_) => Some(CallSlot::Lower(LowerTy::Bool)),
                        Expr::Atom(_) => Some(CallSlot::Lower(LowerTy::Atom)),
                        Expr::Nil => Some(CallSlot::Lower(LowerTy::Nil)),
                        Expr::Var(n) => {
                            if let Some(callee) = param_bindings.get(n) {
                                Some(CallSlot::UserFn(callee.clone()))
                            } else {
                                runtime_env.get(n).cloned().map(CallSlot::Lower)
                            }
                        }
                        _ => None,
                    };
                    match s {
                        Some(slot) => slots.as_mut().unwrap().push(slot),
                        None => { slots = None; break; }
                    }
                }
                if let Some(slots) = slots {
                    out.push((target.clone(), slots));
                }
            }
        }
    }
    // Recurse into subexpressions.
    match e {
        Expr::Call(c, args) => {
            walk_for_implied(c, runtime_env, param_bindings, out);
            for a in args { walk_for_implied(a, runtime_env, param_bindings, out); }
        }
        Expr::BinOp(_, l, r) => { walk_for_implied(l, runtime_env, param_bindings, out); walk_for_implied(r, runtime_env, param_bindings, out); }
        Expr::UnOp(_, x) => walk_for_implied(x, runtime_env, param_bindings, out),
        Expr::If(c, t, els) => {
            walk_for_implied(c, runtime_env, param_bindings, out);
            walk_for_implied(t, runtime_env, param_bindings, out);
            if let Some(e2) = els { walk_for_implied(e2, runtime_env, param_bindings, out); }
        }
        Expr::Case(s, cls) => {
            walk_for_implied(s, runtime_env, param_bindings, out);
            for c in cls { walk_for_implied(&c.body, runtime_env, param_bindings, out); }
        }
        Expr::Block(es) => for e in es { walk_for_implied(e, runtime_env, param_bindings, out); },
        Expr::Tuple(es) | Expr::List(es, _) => for e in es { walk_for_implied(e, runtime_env, param_bindings, out); },
        _ => {}
    }
}

/// Build a runtime env mapping AST param names → LowerTy for non-bound
/// positions of a HOF spec. Used to derive implied callee specs.
pub fn runtime_env_for_spec(
    def: &FnDef,
    sig: &FnSig,
    param_bindings: &std::collections::HashMap<String, String>,
) -> std::collections::HashMap<String, LowerTy> {
    let mut env = std::collections::HashMap::new();
    let first = match def.clauses.first() { Some(c) => c, None => return env };
    let mut sig_iter = sig.params.iter();
    for p in &first.params {
        match p {
            crate::ast::Pattern::Var(n) => {
                if param_bindings.contains_key(n) { continue; }
                if let Some(lt) = sig_iter.next() {
                    env.insert(n.clone(), lt.clone());
                }
            }
            _ => { sig_iter.next(); }
        }
    }
    env
}

/// Find a fn def in the program by user name.
pub fn find_def<'a>(prog: &'a Program, name: &str) -> Option<&'a FnDef> {
    prog.items.iter().find_map(|i| match &**i {
        Item::Fn(d) if d.name == name => Some(d),
        _ => None,
    })
}

/// Build a MonoFn for a call-site slot shape. Drops fn-bound positions from
/// the runtime signature, populates `param_bindings` with the captured
/// callees, and runs `specialize_return` under params that bind fn-typed
/// slots to their concrete user-fn arrows. Returns None if the body can't
/// type-check at this shape, the return doesn't lower, or any fn-bound
/// param isn't a Pattern::Var (we only β-reduce simple param names).
pub fn specialize_def(typer: &mut Typer, def: &FnDef, slots: &[CallSlot]) -> Option<MonoFn> {
    let arity = def.clauses.first().map(|c| c.params.len()).unwrap_or(0);
    if slots.len() != arity { return None; }

    // Build per-param Descrs for retyping. Lower slots use lowerty_to_descr;
    // UserFn slots use the bound fn's globals arrow type.
    let mut params_descr: Vec<Descr> = Vec::with_capacity(arity);
    for slot in slots {
        match slot {
            CallSlot::Lower(lt) => params_descr.push(lowerty_to_descr(lt)),
            CallSlot::UserFn(callee) => {
                let arr = typer.globals.get(callee).cloned()?;
                params_descr.push(arr);
            }
        }
    }

    // Map β-reducible param names. Any clause that doesn't have a Pattern::Var
    // at a UserFn-slot position can't be β-reduced — abort the specialization.
    let mut param_bindings: std::collections::HashMap<String, String> =
        std::collections::HashMap::new();
    for clause in &def.clauses {
        if clause.params.len() != arity { return None; }
        for (i, slot) in slots.iter().enumerate() {
            if let CallSlot::UserFn(callee) = slot {
                let crate::ast::Pattern::Var(pname) = &clause.params[i] else { return None };
                match param_bindings.get(pname) {
                    Some(existing) if existing != callee => return None,
                    _ => { param_bindings.insert(pname.clone(), callee.clone()); }
                }
            }
        }
    }

    let ret_d = crate::typer::specialize_return(typer, def, &params_descr);
    let ret = derive_lowerty(&ret_d)?;
    let runtime_params: Vec<LowerTy> = slots.iter().filter_map(|s| match s {
        CallSlot::Lower(lt) => Some(lt.clone()),
        CallSlot::UserFn(_) => None,
    }).collect();
    let sym = mangle_call(&def.name, slots);
    Some(MonoFn {
        name: sym,
        user_name: def.name.clone(),
        sig: FnSig { params: runtime_params, ret },
        def: def.clone(),
        param_bindings,
    })
}

/// Map a LowerTy back to the most-permissive Descr that lowers to it. Used
/// by the specializer to bind params at a particular shape when retyping a
/// polymorphic fn body.
pub fn lowerty_to_descr(lt: &LowerTy) -> Descr {
    match lt {
        LowerTy::I64 => Descr::int(),
        LowerTy::F64 => Descr::float(),
        LowerTy::Bool => Descr::bool_t(),
        LowerTy::Atom => Descr::atom_top(),
        LowerTy::Nil => Descr::nil(),
        LowerTy::Tuple(ts) => Descr::tuple_of(ts.iter().map(lowerty_to_descr).collect::<Vec<_>>()),
    }
}

/// Walk every user fn and derive a LowerTy signature from the typer's
/// inferred arrow type. For polymorphic fns (typer arrow doesn't reduce to
/// a single LowerTy sig), enumerate distinct call-site shapes and emit one
/// MonoFn per shape (fz-ul4.6). Errors if any fn falls outside the in-scope
/// subset *and* has no usable specialization.
pub fn monomorphize(prog: &Program, typer: &mut Typer) -> Result<Vec<MonoFn>, Vec<String>> {
    let mut out = Vec::new();
    let mut errs = Vec::new();
    for item in &prog.items {
        let Item::Fn(def) = &**item else { continue };
        if def.is_macro {
            continue;
        }
        let arrow = match typer.globals.get(&def.name).cloned() {
            Some(t) => t,
            None => {
                errs.push(format!("{}: typer has no entry", def.name));
                continue;
            }
        };

        if let Some((params, ret)) = extract_simple_arrow(&arrow) {
            out.push(MonoFn {
                name: def.name.clone(),
                user_name: def.name.clone(),
                sig: FnSig { params, ret },
                def: def.clone(),
                param_bindings: std::collections::HashMap::new(),
            });
            continue;
        }

        // Polymorphic / higher-order: enumerate distinct call-site slot shapes.
        let mut seen: std::collections::HashSet<Vec<CallSlot>> = Default::default();
        let call_shapes = typer.call_shapes.get(&def.name).cloned().unwrap_or_default();
        let call_fn_args = typer.call_fn_args.get(&def.name).cloned().unwrap_or_default();
        for (site_idx, args) in call_shapes.iter().enumerate() {
            let fn_args = call_fn_args.get(site_idx);
            let Some(slots) = build_call_slots(args, fn_args.map(|v| &**v)) else { continue };
            if !seen.insert(slots.clone()) { continue; }
            let Some(spec) = specialize_def(typer, def, &slots) else { continue };
            out.push(spec);
        }
    }

    // Closure under HOF call sites: each emitted HOF spec implies that its
    // bound callees get specialized at the shapes the HOF body calls them
    // with. Run *before* the per-fn coverage check so a user fn that's only
    // ever invoked via a HOF arg (e.g. `apply2(double, ..)`) still yields a
    // MonoFn for `double` here.
    let mut sym_seen: std::collections::HashSet<String> =
        out.iter().map(|m| m.name.clone()).collect();
    let mut worklist: Vec<(String, Vec<CallSlot>)> = Vec::new();
    for m in &out {
        if m.param_bindings.is_empty() { continue; }
        let renv = runtime_env_for_spec(&m.def, &m.sig, &m.param_bindings);
        for pair in discover_implied_hof_specs(&m.def, &renv, &m.param_bindings) {
            worklist.push(pair);
        }
    }
    while let Some((callee, slots)) = worklist.pop() {
        let sym = mangle_call(&callee, &slots);
        if sym_seen.contains(&sym) { continue; }
        let Some(def) = find_def(prog, &callee) else { continue };
        let Some(spec) = specialize_def(typer, def, &slots) else { continue };
        sym_seen.insert(sym);
        if !spec.param_bindings.is_empty() {
            let renv = runtime_env_for_spec(&spec.def, &spec.sig, &spec.param_bindings);
            for pair in discover_implied_hof_specs(&spec.def, &renv, &spec.param_bindings) {
                worklist.push(pair);
            }
        }
        out.push(spec);
    }

    // Now flag any user fn that produced zero MonoFns (no shape extracts and
    // no HOF site needed it).
    let covered: std::collections::HashSet<String> =
        out.iter().map(|m| m.user_name.clone()).collect();
    for item in &prog.items {
        let Item::Fn(def) = &**item else { continue };
        if def.is_macro { continue; }
        if covered.contains(&def.name) { continue; }
        let arrow = typer.globals.get(&def.name).cloned().unwrap_or_else(Descr::none);
        errs.push(format!(
            "{}: type {} is not a single monomorphic arrow in the .12 scalar+tuple subset",
            def.name, format_descr_short(&arrow)
        ));
    }
    if !errs.is_empty() {
        return Err(errs);
    }

    Ok(out)
}

pub fn extract_simple_arrow(d: &Descr) -> Option<(Vec<LowerTy>, LowerTy)> {
    // Expect one DNF func conjunction with no negatives. Multi-clause fns
    // produce an intersection of arrows (one positive per clause); we accept
    // them if all positives reduce to the same LowerTy signature.
    if d.funcs.len() != 1 {
        return None;
    }
    let conj = &d.funcs[0];
    if !conj.neg.is_empty() || conj.pos.is_empty() {
        return None;
    }
    let mut sig: Option<(Vec<LowerTy>, LowerTy)> = None;
    for arrow in &conj.pos {
        let params: Vec<LowerTy> = arrow.args.iter().map(derive_lowerty).collect::<Option<_>>()?;
        let ret = derive_lowerty(&arrow.ret)?;
        match &sig {
            None => sig = Some((params, ret)),
            Some((p0, r0)) => {
                if p0 != &params || r0 != &ret {
                    return None;
                }
            }
        }
    }
    sig
}

fn format_descr_short(d: &Descr) -> String {
    // Best-effort short formatter; types.rs has its own Display.
    format!("{}", d)
}

// ---------------------------------------------------------------------------
// Build pipeline
// ---------------------------------------------------------------------------

/// Names of runtime C-ABI symbols the compiler can reference.
const RUNTIME_SYMBOLS: &[(&str, &[LowerTy], Option<LowerTy>)] = &[
    ("fz_print_i64", &[LowerTy::I64], None),
    ("fz_print_f64", &[LowerTy::F64], None),
    ("fz_print_bool", &[LowerTy::Bool], None),
    ("fz_print_atom", &[LowerTy::Atom], None),
    ("fz_print_nil", &[], None),
];

fn runtime_sig(params: &[LowerTy], ret: Option<LowerTy>) -> FnSig {
    FnSig {
        params: params.to_vec(),
        ret: ret.unwrap_or(LowerTy::Nil),
    }
}

fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", "true").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

#[derive(Debug)]
pub struct BuildError(pub String);

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fz build: {}", self.0)
    }
}
impl std::error::Error for BuildError {}

impl From<String> for BuildError { fn from(s: String) -> Self { Self(s) } }

/// Build an executable from `src_path` to `out_path`. Returns an error if
/// any step fails (parse, type, monomorphize, codegen, link).
pub fn build(src_path: &Path, out_path: &Path) -> Result<(), BuildError> {
    let src = std::fs::read_to_string(src_path)
        .map_err(|e| BuildError(format!("reading {}: {}", src_path.display(), e)))?;
    let toks = Lexer::new(&src)
        .tokenize()
        .map_err(|e| BuildError(format!("{}", e)))?;
    let prog = Parser::new(toks)
        .parse_program()
        .map_err(|e| BuildError(format!("{}", e)))?;
    let mut prog = crate::resolve::flatten_modules(prog)
        .map_err(|e| BuildError(format!("module resolution: {}", e)))?;
    crate::macros::expand_program(&mut prog)
        .map_err(|e| BuildError(format!("macro expansion: {}", e)))?;
    let mut typer = Typer::new();
    typer.type_program(&prog);
    if !typer.errors.is_empty() {
        return Err(BuildError(format!(
            "type errors:\n  {}",
            typer.errors.join("\n  ")
        )));
    }
    let monos = monomorphize(&prog, &mut typer)
        .map_err(|errs| BuildError(format!("not in .12 scope:\n  {}", errs.join("\n  "))))?;

    // Locate user main.
    let main_mono = monos
        .iter()
        .find(|m| m.name == "main" && m.sig.params.is_empty())
        .ok_or_else(|| {
            BuildError("no `fn main()` defined (AOT requires a zero-arg main)".into())
        })?
        .clone();

    let isa = host_isa();
    let obj_builder = ObjectBuilder::new(
        isa,
        out_path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "fz_obj".into()),
        cranelift_module::default_libcall_names(),
    )
    .map_err(|e| BuildError(format!("ObjectBuilder: {}", e)))?;
    let mut module = ObjectModule::new(obj_builder);

    // Declare runtime symbols.
    let mut runtime_ids: HashMap<&'static str, FuncId> = HashMap::new();
    for (sym, params, ret) in RUNTIME_SYMBOLS {
        let sig = runtime_sig(params, ret.clone());
        let cl_sig = sig.to_cranelift(CallConv::SystemV);
        let id = module
            .declare_function(sym, Linkage::Import, &cl_sig)
            .map_err(|e| BuildError(format!("declare {}: {}", sym, e)))?;
        runtime_ids.insert(sym, id);
    }
    // fz_register_atom signature: (u32, *const u8, usize) -> ()
    let reg_sig = {
        let mut s = Signature::new(CallConv::SystemV);
        s.params.push(AbiParam::new(ir::types::I32));
        s.params.push(AbiParam::new(ir::types::I64));
        s.params.push(AbiParam::new(ir::types::I64));
        s
    };
    let reg_id = module
        .declare_function("fz_register_atom", Linkage::Import, &reg_sig)
        .map_err(|e| BuildError(format!("declare fz_register_atom: {}", e)))?;

    // Declare each user fn (rename `main` → `fz_user_main` to free `main`
    // for the C entry-point shim).
    let mut user_ids: HashMap<String, FuncId> = HashMap::new();
    for m in &monos {
        let sym = if m.name == "main" { "fz_user_main".to_string() } else { m.name.clone() };
        let cl_sig = m.sig.to_cranelift(CallConv::SystemV);
        let id = module
            .declare_function(&sym, Linkage::Export, &cl_sig)
            .map_err(|e| BuildError(format!("declare {}: {}", sym, e)))?;
        user_ids.insert(m.name.clone(), id);
    }

    // Lower and define each user fn.
    let callee_sigs: HashMap<String, FnSig> = monos
        .iter()
        .map(|m| (m.name.clone(), m.sig.clone()))
        .collect();
    let user_fns_set: std::collections::HashSet<String> = monos.iter()
        .map(|m| m.user_name.clone())
        .collect();
    let mut atoms = AtomInterner::default();
    for m in &monos {
        let r = crate::codegen::lower_fn_with(
            &m.def, &m.sig, &callee_sigs, &mut atoms,
            &m.param_bindings, &user_fns_set,
        ).map_err(|e: LowerError| BuildError(format!("{}: {}", m.name, e)))?;
        let LowerResult { mut func, callee_imports, builtin_imports } = r;
        rewrite_user_names(&mut func, &callee_imports, &builtin_imports, &user_ids, &runtime_ids)?;
        let mut ctx = Context::for_function(func);
        let user_id = user_ids[&m.name];
        module
            .define_function(user_id, &mut ctx)
            .map_err(|e| BuildError(format!("{}: {}", m.name, e)))?;
    }

    // Emit one data object per interned atom name (UTF-8 bytes, no NUL).
    let atom_data_ids = emit_atom_data(&mut module, &atoms.names)?;

    // Emit `main` C entry-point shim.
    emit_c_main_shim(
        &mut module,
        &main_mono,
        &user_ids,
        &runtime_ids,
        reg_id,
        &atom_data_ids,
        &atoms.names,
    )?;

    // Finish module → object bytes → write .o → link.
    let obj_product = module.finish();
    let obj_bytes = obj_product
        .emit()
        .map_err(|e| BuildError(format!("emit: {}", e)))?;
    let obj_path = out_path.with_extension("o");
    std::fs::write(&obj_path, &obj_bytes)
        .map_err(|e| BuildError(format!("write {}: {}", obj_path.display(), e)))?;

    // Invoke cc to link with the runtime staticlib.
    link(&obj_path, out_path)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn rewrite_user_names(
    func: &mut ir::Function,
    callee_imports: &[String],
    builtin_imports: &[&'static str],
    user_ids: &HashMap<String, FuncId>,
    runtime_ids: &HashMap<&'static str, FuncId>,
) -> Result<(), BuildError> {
    let entries: Vec<(ir::UserExternalNameRef, UserExternalName)> = func
        .params
        .user_named_funcs()
        .iter()
        .map(|(r, n)| (r, n.clone()))
        .collect();
    for (r, name) in entries {
        let new_id = match name.namespace {
            0 => {
                let callee = &callee_imports[name.index as usize];
                // `main` was renamed to `fz_user_main` at declaration time;
                // self-recursion through "main" goes to the same FuncId.
                let id = user_ids.get(callee).ok_or_else(|| {
                    BuildError(format!("internal: callee {} not declared", callee))
                })?;
                id.as_u32()
            }
            1 => {
                let sym = builtin_imports[name.index as usize];
                let id = runtime_ids
                    .get(sym)
                    .ok_or_else(|| BuildError(format!("internal: runtime {} not declared", sym)))?;
                id.as_u32()
            }
            _ => return Err(BuildError(format!("unknown namespace {}", name.namespace))),
        };
        func.params
            .reset_user_func_name(r, UserExternalName { namespace: 0, index: new_id });
    }
    Ok(())
}

fn emit_atom_data(
    module: &mut ObjectModule,
    names: &[String],
) -> Result<Vec<cranelift_module::DataId>, BuildError> {
    let mut out = Vec::with_capacity(names.len());
    for (i, n) in names.iter().enumerate() {
        let mut data = DataDescription::new();
        data.define(n.as_bytes().to_vec().into_boxed_slice());
        let id = module
            .declare_data(&format!("fz_atom_{}", i), Linkage::Local, false, false)
            .map_err(|e| BuildError(format!("declare atom data {}: {}", i, e)))?;
        module
            .define_data(id, &data)
            .map_err(|e| BuildError(format!("define atom data {}: {}", i, e)))?;
        out.push(id);
    }
    Ok(out)
}

fn emit_c_main_shim(
    module: &mut ObjectModule,
    main_mono: &MonoFn,
    user_ids: &HashMap<String, FuncId>,
    _runtime_ids: &HashMap<&'static str, FuncId>,
    reg_id: FuncId,
    atom_data_ids: &[cranelift_module::DataId],
    atom_names: &[String],
) -> Result<(), BuildError> {
    // C-ABI: int main(int argc, char** argv).
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(ir::types::I32));
    sig.params.push(AbiParam::new(ir::types::I64));
    sig.returns.push(AbiParam::new(ir::types::I32));
    let main_id = module
        .declare_function("main", Linkage::Export, &sig)
        .map_err(|e| BuildError(format!("declare main: {}", e)))?;

    let mut func = ir::Function::with_name_signature(UserFuncName::user(0, main_id.as_u32()), sig);
    let mut fbctx = cranelift_frontend::FunctionBuilderContext::new();
    let mut builder = cranelift_frontend::FunctionBuilder::new(&mut func, &mut fbctx);

    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);

    // Register atoms in id order.
    let reg_fr = module.declare_func_in_func(reg_id, builder.func);
    for (i, name) in atom_names.iter().enumerate() {
        let data_gv = module.declare_data_in_func(atom_data_ids[i], builder.func);
        let ptr = builder.ins().symbol_value(ir::types::I64, data_gv);
        let id_v = builder.ins().iconst(ir::types::I32, i as i64);
        let len_v = builder.ins().iconst(ir::types::I64, name.len() as i64);
        builder.ins().call(reg_fr, &[id_v, ptr, len_v]);
    }

    // Call user main (`fz_user_main`).
    let user_main_id = user_ids[&main_mono.name];
    let user_main_fr = module.declare_func_in_func(user_main_id, builder.func);
    let inst = builder.ins().call(user_main_fr, &[]);
    let _ = builder.inst_results(inst); // discard whatever main returns

    // return 0
    let zero = builder.ins().iconst(ir::types::I32, 0);
    builder.ins().return_(&[zero]);

    builder.finalize();
    let mut ctx = Context::for_function(func);
    module
        .define_function(main_id, &mut ctx)
        .map_err(|e| BuildError(format!("define main: {}", e)))?;
    Ok(())
}

fn link(obj_path: &Path, out_path: &Path) -> Result<(), BuildError> {
    let runtime_lib = locate_runtime_staticlib()
        .ok_or_else(|| BuildError("could not locate libfz_runtime.a — run `cargo build` first".into()))?;
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    let mut cmd = Command::new(&cc);
    cmd.arg(obj_path).arg(&runtime_lib).arg("-o").arg(out_path);
    if cfg!(target_os = "macos") {
        // Quiet macOS linker warnings about no version min specified.
        cmd.arg("-Wl,-no_warn_duplicate_libraries");
    }
    let out = cmd
        .output()
        .map_err(|e| BuildError(format!("invoke {}: {}", cc, e)))?;
    if !out.status.success() {
        return Err(BuildError(format!(
            "linker failed (status {}):\nstdout: {}\nstderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    Ok(())
}

fn locate_runtime_staticlib() -> Option<std::path::PathBuf> {
    // 1) FZ_RUNTIME_LIB env override.
    if let Ok(p) = std::env::var("FZ_RUNTIME_LIB") {
        let pb = std::path::PathBuf::from(p);
        if pb.exists() {
            return Some(pb);
        }
    }
    // 2) Look in `<cargo manifest>/target/{debug,release}` (test/`cargo run`).
    if let Ok(base) = std::env::var("CARGO_MANIFEST_DIR") {
        for profile in &["debug", "release"] {
            let p = std::path::Path::new(&base)
                .join("target")
                .join(profile)
                .join("libfz_runtime.a");
            if p.exists() {
                return Some(p);
            }
        }
    }
    // 3) Look next to the running executable (e.g. target/debug/fz alongside
    //    target/debug/libfz_runtime.a).
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let p = dir.join("libfz_runtime.a");
            if p.exists() {
                return Some(p);
            }
            // Test binaries live in target/debug/deps/; staticlib is one up.
            if let Some(parent) = dir.parent() {
                let p = parent.join("libfz_runtime.a");
                if p.exists() {
                    return Some(p);
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowerty_for_scalars() {
        assert_eq!(derive_lowerty(&Descr::int()), Some(LowerTy::I64));
        assert_eq!(derive_lowerty(&Descr::float()), Some(LowerTy::F64));
        assert_eq!(derive_lowerty(&Descr::bool_t()), Some(LowerTy::Bool));
        assert_eq!(derive_lowerty(&Descr::atom_top()), Some(LowerTy::Atom));
        assert_eq!(derive_lowerty(&Descr::atom_lit("x")), Some(LowerTy::Atom));
        assert_eq!(derive_lowerty(&Descr::nil()), Some(LowerTy::Nil));
        assert_eq!(derive_lowerty(&Descr::int_lit(7)), Some(LowerTy::I64));
    }

    #[test]
    fn lowerty_rejects_unions_across_kinds() {
        let d = Descr::int().union(&Descr::nil());
        assert_eq!(derive_lowerty(&d), None);
    }

    #[test]
    fn lowerty_rejects_heap_types() {
        assert_eq!(derive_lowerty(&Descr::list_of(Descr::int())), None);
        assert_eq!(derive_lowerty(&Descr::str_t()), None);
        assert_eq!(derive_lowerty(&Descr::map_top()), None);
    }

    #[test]
    fn lowerty_for_tuple_of_scalars() {
        let d = Descr::tuple_of([Descr::int(), Descr::bool_t()]);
        assert_eq!(
            derive_lowerty(&d),
            Some(LowerTy::Tuple(vec![LowerTy::I64, LowerTy::Bool]))
        );
    }

    #[test]
    fn lowerty_rejects_tuple_with_heap_component() {
        let d = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert_eq!(derive_lowerty(&d), None);
    }

    /// Build `src` to `out_name`, run, and return stdout.
    fn build_and_run(test_name: &str, file_name: &str, src: &str) -> String {
        let (src_path, dir) = crate::test_support::write_fixture(test_name, file_name, src);
        let bin = dir.join(file_name.trim_end_matches(".fz"));
        build(&src_path, &bin).expect("build");
        let out = Command::new(&bin).output().expect("run");
        assert!(out.status.success(), "binary exit: {}", out.status);
        String::from_utf8_lossy(&out.stdout).into_owned()
    }

    fn assert_contains_all(stdout: &str, needles: &[&str]) {
        for n in needles {
            assert!(stdout.contains(n), "stdout missing {:?}:\n{}", n, stdout);
        }
    }

    #[test]
    fn end_to_end_aot_runs_binary() {
        if locate_runtime_staticlib().is_none() {
            eprintln!("skip: libfz_runtime.a not present");
            return;
        }
        let stdout = build_and_run(
            "aot-hello", "hello.fz",
            include_str!("../fixtures/hello.fz"),
        );
        assert_contains_all(&stdout, &["42", ":ok"]);
    }

    #[test]
    fn end_to_end_aot_multi_clause_runs() {
        if locate_runtime_staticlib().is_none() {
            eprintln!("skip: libfz_runtime.a not present");
            return;
        }
        let stdout = build_and_run(
            "aot-multi", "multi_clause.fz",
            include_str!("../fixtures/multi_clause.fz"),
        );
        assert_contains_all(&stdout, &[":zero", ":positive", ":negative", "120"]);
    }

    #[test]
    fn end_to_end_aot_polymorphic_runs() {
        if locate_runtime_staticlib().is_none() {
            eprintln!("skip: libfz_runtime.a not present");
            return;
        }
        let stdout = build_and_run(
            "aot-poly", "polymorphic.fz",
            include_str!("../fixtures/polymorphic.fz"),
        );
        assert_contains_all(&stdout, &["42", ":hello", "true"]);
    }

    #[test]
    fn end_to_end_aot_higher_order_runs() {
        if locate_runtime_staticlib().is_none() {
            eprintln!("skip: libfz_runtime.a not present");
            return;
        }
        let stdout = build_and_run(
            "aot-hof", "higher_order.fz",
            include_str!("../fixtures/higher_order.fz"),
        );
        assert_contains_all(&stdout, &["42", "-7", "-10"]);
    }

    #[test]
    fn rejects_heap_typed_fn_at_aot() {
        let src = "fn make() do [1, 2, 3] end\nfn main() do print(make()) end";
        let toks = Lexer::new(src).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let mut t = Typer::new();
        t.type_program(&prog);
        let res = monomorphize(&prog, &mut t);
        assert!(res.is_err());
    }
}
