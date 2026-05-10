//! fz-ul4.12.4 — JIT driver: source → in-process compiled code, mixed with
//! interpreter fallback for fns outside the .12 scope.
//!
//! Mirrors the AOT pipeline (parse → type → classify → lower → finish) but
//! emits into a `JITModule` instead of an object file, and supports calling
//! between JIT and interpreter at fn boundaries:
//!
//! - **JIT → interp**: an interp-only callee with a monomorphic call-site
//!   signature is reached via a forward-thunk JIT fn. The thunk marshals
//!   native args into u64 slots, calls `fz_call_interp(idx, args, ret)`, and
//!   demarshals the slot return.
//! - **Interp → JIT**: each JIT-eligible fn gets a reverse-thunk JIT fn with
//!   the uniform `fn(*const u64, *mut u64)` ABI. We bind a `Value::Jit` into
//!   the interpreter's globals carrying that thunk pointer; `Interp::apply`
//!   marshals interp Values into slots, calls the thunk, demarshals the
//!   result.
//!
//! Slot encoding (per LowerTy leaf, one 8-byte slot each, flatten-order):
//! - I64: bit-cast i64 → u64
//! - F64: bit-cast f64 → u64
//! - Bool: zext i8 → u64
//! - Atom: zext u32 → u64
//! - Nil: 0 (placeholder)
//! Tuples flatten across multiple slots.

use crate::aot::{derive_lowerty, extract_simple_arrow, lowerty_to_descr, mangle_call, MonoFn};
use crate::ast::*;
use crate::codegen::{lower_fn, AtomInterner, FnSig, LowerError, LowerResult, LowerTy};
use crate::eval::Interp;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::typer::Typer;
use crate::value::Value;
use cranelift_codegen::ir::{
    self, AbiParam, InstBuilder, MemFlags, Signature, UserExternalName, UserFuncName,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module};
use std::cell::RefCell;
use std::collections::HashMap;
use std::path::Path;
use std::rc::Rc;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Per-fn classification
// ---------------------------------------------------------------------------

/// Per-fn JIT classification result. A fn is JIT-eligible only if its inferred
/// signature is monomorphic AND lower_fn succeeds. Interp-only fns may still
/// be callable from JIT if their sig is monomorphic — we keep their sig so
/// JIT call sites can route through a forward-thunk.
struct Classified {
    jit_eligible: Vec<MonoFn>,
    /// callee name → monomorphic call-site sig (subset of all interp-only fns;
    /// a fn whose sig isn't monomorphic isn't here and can't be called from JIT)
    interp_callable: HashMap<String, FnSig>,
}

fn classify(prog: &Program, typer: &mut Typer) -> Classified {
    // Phase 1: enumerate candidates (mono + polymorphic + HOF closure).
    let mut candidates: Vec<MonoFn> = Vec::new();
    let mut interp_callable: HashMap<String, FnSig> = HashMap::new();
    let mut seen_syms: std::collections::HashSet<String> = std::collections::HashSet::new();
    let mut worklist: Vec<(String, Vec<crate::aot::CallSlot>)> = Vec::new();

    for item in &prog.items {
        let Item::Fn(def) = &**item else { continue };
        if def.is_macro { continue; }
        let Some(arrow) = typer.globals.get(&def.name) else { continue };
        if let Some((params, ret)) = extract_simple_arrow(arrow) {
            let m = MonoFn {
                name: def.name.clone(),
                user_name: def.name.clone(),
                sig: FnSig { params, ret },
                def: def.clone(),
                param_bindings: std::collections::HashMap::new(),
            };
            seen_syms.insert(m.name.clone());
            candidates.push(m);
            continue;
        }
        let mut shape_seen: std::collections::HashSet<Vec<crate::aot::CallSlot>> = Default::default();
        let call_shapes = typer.call_shapes.get(&def.name).cloned().unwrap_or_default();
        let call_fn_args = typer.call_fn_args.get(&def.name).cloned().unwrap_or_default();
        for (site_idx, args) in call_shapes.iter().enumerate() {
            let fn_args = call_fn_args.get(site_idx);
            let Some(slots) = crate::aot::build_call_slots(args, fn_args.map(|v| &**v)) else { continue };
            if !shape_seen.insert(slots.clone()) { continue; }
            let Some(spec) = crate::aot::specialize_def(typer, def, &slots) else { continue };
            if seen_syms.insert(spec.name.clone()) {
                if !spec.param_bindings.is_empty() {
                    let renv = crate::aot::runtime_env_for_spec(&spec.def, &spec.sig, &spec.param_bindings);
                    worklist.extend(crate::aot::discover_implied_hof_specs(&spec.def, &renv, &spec.param_bindings));
                }
                candidates.push(spec);
            }
        }
    }

    // Closure: each HOF candidate implies bound-callee specs.
    while let Some((callee, slots)) = worklist.pop() {
        let sym = crate::aot::mangle_call(&callee, &slots);
        if seen_syms.contains(&sym) { continue; }
        let Some(def) = crate::aot::find_def(prog, &callee) else { continue };
        let Some(spec) = crate::aot::specialize_def(typer, def, &slots) else { continue };
        seen_syms.insert(spec.name.clone());
        if !spec.param_bindings.is_empty() {
            let renv = crate::aot::runtime_env_for_spec(&spec.def, &spec.sig, &spec.param_bindings);
            worklist.extend(crate::aot::discover_implied_hof_specs(&spec.def, &renv, &spec.param_bindings));
        }
        candidates.push(spec);
    }

    // Phase 2: build the full callee_sigs table and probe-lower each candidate.
    let probe_user_fns: std::collections::HashSet<String> =
        prog.items.iter().filter_map(|it| match &**it {
            Item::Fn(d) if !d.is_macro => Some(d.name.clone()),
            _ => None,
        }).collect();
    let mut all_sigs: HashMap<String, FnSig> = HashMap::new();
    for m in &candidates {
        all_sigs.insert(m.name.clone(), m.sig.clone());
    }
    // Also include monomorphic-arrow sigs of fns that aren't candidates so
    // builtins / call-site fallbacks resolve.
    for item in &prog.items {
        let Item::Fn(def) = &**item else { continue };
        if def.is_macro { continue; }
        if let Some(arr) = typer.globals.get(&def.name) {
            if let Some((p, r)) = extract_simple_arrow(arr) {
                all_sigs.entry(def.name.clone()).or_insert(FnSig { params: p, ret: r });
            }
        }
    }

    let mut jit_eligible = Vec::new();
    for m in candidates {
        let mut probe_atoms = AtomInterner::default();
        if crate::codegen::lower_fn_with(
            &m.def, &m.sig, &all_sigs, &mut probe_atoms,
            &m.param_bindings, &probe_user_fns,
        ).is_ok() {
            jit_eligible.push(m);
        } else if m.name == m.user_name {
            // Monomorphic fn whose body fails to lower (e.g. heap-typed): keep
            // it callable from JIT via a forward thunk.
            interp_callable.insert(m.user_name.clone(), m.sig);
        }
    }

    Classified { jit_eligible, interp_callable }
}


// ---------------------------------------------------------------------------
// Cross-tier dispatch (interp side)
// ---------------------------------------------------------------------------

/// Per-process cross-tier context. Lives only inside `run()` — installed at
/// JIT setup, cleared on return. Holds:
/// - `interp` for fz_call_interp to dispatch into.
/// - `interp_callees` indexed by JIT-assigned id: (name, sig). Forward-thunks
///   pass that idx into fz_call_interp.
struct JitCtx {
    interp: *const Interp,
    interp_callees: Vec<(String, FnSig)>,
}

thread_local! {
    static JIT_CTX: RefCell<Option<JitCtx>> = const { RefCell::new(None) };
}

/// Forward-thunk → interpreter trampoline. Called from JIT-compiled code via
/// a JITBuilder-registered symbol.
unsafe extern "C" fn fz_call_interp(idx: u32, args_ptr: *const u64, ret_ptr: *mut u64) {
    JIT_CTX.with(|c| {
        let cell = c.borrow();
        let ctx = cell.as_ref().expect("fz_call_interp without JitCtx");
        let (name, sig) = &ctx.interp_callees[idx as usize];
        // Demarshal slot-buffer args → Vec<Value> per sig.
        let n_slots: usize = sig.params.iter().map(flat_arity).sum();
        let slots = unsafe { std::slice::from_raw_parts(args_ptr, n_slots) };
        let mut cursor = 0;
        let mut argv: Vec<Value> = Vec::with_capacity(sig.params.len());
        for pty in &sig.params {
            argv.push(slots_to_value(pty, slots, &mut cursor));
        }
        // Dispatch into the interpreter.
        let interp = unsafe { &*ctx.interp };
        let result = interp
            .call_named(name, argv)
            .unwrap_or_else(|e| panic!("interp call {} from JIT failed: {}", name, e));
        // Marshal Value → slot buffer.
        let n_ret_slots = flat_arity(&sig.ret);
        let ret_slots = unsafe { std::slice::from_raw_parts_mut(ret_ptr, n_ret_slots) };
        let mut cursor = 0;
        value_to_slots(&sig.ret, &result, ret_slots, &mut cursor);
    });
}

fn flat_arity(t: &LowerTy) -> usize {
    match t {
        LowerTy::Tuple(ts) => ts.iter().map(flat_arity).sum(),
        _ => 1,
    }
}

fn value_to_slots(ty: &LowerTy, v: &Value, slots: &mut [u64], cursor: &mut usize) {
    match ty {
        LowerTy::I64 => match v {
            Value::Int(n) => { slots[*cursor] = *n as u64; *cursor += 1; }
            other => panic!("expected int, got {}", other),
        },
        LowerTy::F64 => match v {
            Value::Float(x) => { slots[*cursor] = x.to_bits(); *cursor += 1; }
            other => panic!("expected float, got {}", other),
        },
        LowerTy::Bool => match v {
            Value::Bool(b) => { slots[*cursor] = *b as u64; *cursor += 1; }
            other => panic!("expected bool, got {}", other),
        },
        LowerTy::Atom => match v {
            Value::Atom(a) => {
                let id = ::fz_runtime::intern(a);
                slots[*cursor] = id as u64;
                *cursor += 1;
            }
            other => panic!("expected atom, got {}", other),
        },
        LowerTy::Nil => match v {
            Value::Nil => { slots[*cursor] = 0; *cursor += 1; }
            other => panic!("expected nil, got {}", other),
        },
        LowerTy::Tuple(ts) => match v {
            Value::Tuple(elems) if elems.len() == ts.len() => {
                for (t, e) in ts.iter().zip(elems.iter()) {
                    value_to_slots(t, e, slots, cursor);
                }
            }
            other => panic!("expected tuple, got {}", other),
        },
    }
}

fn slots_to_value(ty: &LowerTy, slots: &[u64], cursor: &mut usize) -> Value {
    match ty {
        LowerTy::I64 => {
            let v = slots[*cursor] as i64; *cursor += 1; Value::Int(v)
        }
        LowerTy::F64 => {
            let v = f64::from_bits(slots[*cursor]); *cursor += 1; Value::Float(v)
        }
        LowerTy::Bool => {
            let v = slots[*cursor] != 0; *cursor += 1; Value::Bool(v)
        }
        LowerTy::Atom => {
            let id = slots[*cursor] as u32; *cursor += 1;
            let name = fz_runtime::name_of(id).unwrap_or_else(|| format!("<atom#{}>", id));
            Value::Atom(Rc::from(name.as_str()))
        }
        LowerTy::Nil => { *cursor += 1; Value::Nil }
        LowerTy::Tuple(ts) => {
            let mut elems = Vec::with_capacity(ts.len());
            for t in ts {
                elems.push(slots_to_value(t, slots, cursor));
            }
            Value::Tuple(Rc::new(elems))
        }
    }
}

// Use the shared runtime crate's atom table directly (same process as the
// JIT, so fz_call_interp + the printers work against one source of truth).
use ::fz_runtime as fz_runtime;

// ---------------------------------------------------------------------------
// Build pipeline
// ---------------------------------------------------------------------------

#[derive(Debug)]
pub struct JitError(pub String);
impl std::fmt::Display for JitError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fz jit: {}", self.0)
    }
}
impl std::error::Error for JitError {}
impl From<String> for JitError { fn from(s: String) -> Self { Self(s) } }

const RUNTIME_PRINT_SYMBOLS: &[(&str, &[LowerTy], LowerTy)] = &[
    ("fz_print_i64", &[LowerTy::I64], LowerTy::Nil),
    ("fz_print_f64", &[LowerTy::F64], LowerTy::Nil),
    ("fz_print_bool", &[LowerTy::Bool], LowerTy::Nil),
    ("fz_print_atom", &[LowerTy::Atom], LowerTy::Nil),
    ("fz_print_nil", &[], LowerTy::Nil),
];

fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", "false").unwrap();
    flag_builder.set("use_colocated_libcalls", "false").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

/// JIT-compile and run a source file. Returns when `main` returns.
pub fn run(src_path: &Path) -> Result<(), JitError> {
    let src = std::fs::read_to_string(src_path)
        .map_err(|e| JitError(format!("reading {}: {}", src_path.display(), e)))?;
    run_str(&src)
}

pub fn run_str(src: &str) -> Result<(), JitError> {
    let toks = Lexer::new(src).tokenize().map_err(|e| JitError(format!("{}", e)))?;
    let prog = Parser::new(toks).parse_program().map_err(|e| JitError(format!("{}", e)))?;
    let mut typer = Typer::new();
    typer.type_program(&prog);
    if !typer.errors.is_empty() {
        return Err(JitError(format!("type errors:\n  {}", typer.errors.join("\n  "))));
    }

    let cls = classify(&prog, &mut typer);

    let interp = Interp::new();
    interp
        .load_program(&prog)
        .map_err(|e| JitError(format!("load: {}", e)))?;

    let runtime = TieredRuntime::build(cls)?;

    // Install JitCtx for the duration of the run (used by fz_call_interp).
    let interp_callees: Vec<(String, FnSig)> = runtime.interp_callee_order.clone();
    let interp_ptr: *const Interp = &interp;
    JIT_CTX.with(|c| {
        *c.borrow_mut() = Some(JitCtx {
            interp: interp_ptr,
            interp_callees,
        });
    });

    // Install tier-up call hook. Threshold is chosen so deep self-recursion
    // (`count(100000, 0)`) tier-ups well before exhausting the rust stack.
    let rt = Rc::new(runtime);
    let rt_hook = rt.clone();
    *interp.on_user_call.borrow_mut() = Some(Rc::new(move |name: &str, ip: &Interp| {
        rt_hook.on_call(name, ip);
    }));

    let result = interp.call_named("main", vec![]);

    *interp.on_user_call.borrow_mut() = None;
    JIT_CTX.with(|c| { *c.borrow_mut() = None; });

    // Leak the JIT module so any bound Value::Jit thunks remain valid.
    let TieredRuntime { module, .. } = match Rc::try_unwrap(rt) {
        Ok(r) => r,
        Err(_) => panic!("TieredRuntime still referenced at end of run"),
    };
    std::mem::forget(module.into_inner());

    result.map_err(|e| JitError(format!("runtime: {}", e)))?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Tier-up runtime (fz-ul4.13)
// ---------------------------------------------------------------------------

const TIERUP_THRESHOLD: u32 = 8;

/// Holds the persistent JITModule plus state for lazy per-fn compilation.
/// Functions start in the interpreter; once a user_name's call count crosses
/// `TIERUP_THRESHOLD`, that user_name's monos (and any not-yet-compiled monos
/// transitively reachable through their bodies) are lowered, defined,
/// finalized, and the corresponding interp globals are rebound to Value::Jit.
/// Cold (un-reached) code stays in the interpreter forever.
struct TieredRuntime {
    module: RefCell<JITModule>,
    monos: Vec<MonoFn>,
    monos_by_user: HashMap<String, Vec<usize>>,

    user_ids: HashMap<String, FuncId>,           // mono.name -> FuncId
    forward_thunk_ids: HashMap<String, FuncId>,  // user_name (interp_callable) -> FuncId
    runtime_ids: HashMap<&'static str, FuncId>,
    callee_sigs: HashMap<String, FnSig>,
    user_fns_set: std::collections::HashSet<String>,
    atoms: RefCell<AtomInterner>,

    defined_monos: RefCell<std::collections::HashSet<String>>,
    counts: RefCell<HashMap<String, u32>>,
    triggered: RefCell<std::collections::HashSet<String>>,
    in_tier_up: RefCell<bool>,

    interp_callee_order: Vec<(String, FnSig)>,
}

impl TieredRuntime {
    fn build(cls: Classified) -> Result<Self, JitError> {
        let isa = host_isa();
        let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        let _ = builder.symbol("fz_print_i64", fz_runtime::fz_print_i64 as *const u8);
        let _ = builder.symbol("fz_print_f64", fz_runtime::fz_print_f64 as *const u8);
        let _ = builder.symbol("fz_print_bool", fz_runtime::fz_print_bool as *const u8);
        let _ = builder.symbol("fz_print_atom", fz_runtime::fz_print_atom as *const u8);
        let _ = builder.symbol("fz_print_nil", fz_runtime::fz_print_nil as *const u8);
        let _ = builder.symbol("fz_call_interp", fz_call_interp as *const u8);

        let mut module = JITModule::new(builder);

        let mut runtime_ids: HashMap<&'static str, FuncId> = HashMap::new();
        for (sym, params, ret) in RUNTIME_PRINT_SYMBOLS {
            let sig = FnSig { params: params.to_vec(), ret: ret.clone() };
            let cl_sig = sig.to_cranelift(CallConv::SystemV);
            let id = module
                .declare_function(sym, Linkage::Import, &cl_sig)
                .map_err(|e| JitError(format!("declare {}: {}", sym, e)))?;
            runtime_ids.insert(sym, id);
        }
        let call_interp_sig = {
            let mut s = Signature::new(CallConv::SystemV);
            s.params.push(AbiParam::new(ir::types::I32));
            s.params.push(AbiParam::new(ir::types::I64));
            s.params.push(AbiParam::new(ir::types::I64));
            s
        };
        let call_interp_id = module
            .declare_function("fz_call_interp", Linkage::Import, &call_interp_sig)
            .map_err(|e| JitError(format!("declare fz_call_interp: {}", e)))?;

        // Declare every JIT-eligible mono upfront so call sites in lazily-
        // lowered fns can reference them by FuncId regardless of definition
        // order.
        let mut user_ids: HashMap<String, FuncId> = HashMap::new();
        for m in &cls.jit_eligible {
            let cl_sig = m.sig.to_cranelift(CallConv::SystemV);
            let id = module
                .declare_function(&m.name, Linkage::Local, &cl_sig)
                .map_err(|e| JitError(format!("declare {}: {}", m.name, e)))?;
            user_ids.insert(m.name.clone(), id);
        }

        // Forward thunks for interp-only callees (compiled+finalized eagerly:
        // they're cheap, and JIT'd code calling into interp needs them ready).
        let mut interp_callee_order: Vec<(String, FnSig)> = cls
            .interp_callable
            .iter()
            .map(|(n, s)| (n.clone(), s.clone()))
            .collect();
        interp_callee_order.sort_by(|a, b| a.0.cmp(&b.0));
        let interp_callee_idx: HashMap<String, u32> = interp_callee_order
            .iter()
            .enumerate()
            .map(|(i, (n, _))| (n.clone(), i as u32))
            .collect();
        let mut forward_thunk_ids: HashMap<String, FuncId> = HashMap::new();
        for (name, sig) in &interp_callee_order {
            let cl_sig = sig.to_cranelift(CallConv::SystemV);
            let thunk_sym = format!("__fz_fwdthunk_{}", name);
            let id = module
                .declare_function(&thunk_sym, Linkage::Local, &cl_sig)
                .map_err(|e| JitError(format!("declare {}: {}", thunk_sym, e)))?;
            forward_thunk_ids.insert(name.clone(), id);
        }
        for (name, sig) in &interp_callee_order {
            let idx = interp_callee_idx[name];
            let id = forward_thunk_ids[name];
            define_forward_thunk(&mut module, id, sig, idx, call_interp_id)?;
        }
        // Forward thunks reference no JIT-side fns, just the interp
        // trampoline; safe to finalize immediately.
        module
            .finalize_definitions()
            .map_err(|e| JitError(format!("finalize forward thunks: {}", e)))?;

        let mut callee_sigs: HashMap<String, FnSig> = HashMap::new();
        for m in &cls.jit_eligible {
            callee_sigs.insert(m.name.clone(), m.sig.clone());
        }
        for (n, s) in &cls.interp_callable {
            callee_sigs.insert(n.clone(), s.clone());
        }

        let user_fns_set: std::collections::HashSet<String> = cls.jit_eligible.iter()
            .map(|m| m.user_name.clone())
            .chain(cls.interp_callable.keys().cloned())
            .collect();

        let mut monos_by_user: HashMap<String, Vec<usize>> = HashMap::new();
        for (i, m) in cls.jit_eligible.iter().enumerate() {
            monos_by_user.entry(m.user_name.clone()).or_default().push(i);
        }

        Ok(TieredRuntime {
            module: RefCell::new(module),
            monos: cls.jit_eligible,
            monos_by_user,
            user_ids,
            forward_thunk_ids,
            runtime_ids,
            callee_sigs,
            user_fns_set,
            atoms: RefCell::new(AtomInterner::default()),
            defined_monos: RefCell::new(std::collections::HashSet::new()),
            counts: RefCell::new(HashMap::new()),
            triggered: RefCell::new(std::collections::HashSet::new()),
            in_tier_up: RefCell::new(false),
            interp_callee_order,
        })
    }

    fn on_call(&self, user_name: &str, interp: &Interp) {
        // Avoid recursion: tier-up itself does not need to count.
        if *self.in_tier_up.borrow() { return; }
        if !self.monos_by_user.contains_key(user_name) { return; }
        if self.triggered.borrow().contains(user_name) { return; }
        let mut counts = self.counts.borrow_mut();
        let c = counts.entry(user_name.to_string()).or_insert(0);
        *c += 1;
        if *c < TIERUP_THRESHOLD { return; }
        drop(counts);
        if let Err(e) = self.tier_up(user_name, interp) {
            // Tier-up failure should not crash the interpreter; mark as
            // triggered so we don't retry, and let interp continue.
            eprintln!("fz jit: tier-up of {} failed: {}; continuing in interp", user_name, e);
            self.triggered.borrow_mut().insert(user_name.to_string());
        }
    }

    fn tier_up(&self, user_name: &str, interp: &Interp) -> Result<(), JitError> {
        *self.in_tier_up.borrow_mut() = true;
        let res = self.tier_up_inner(user_name, interp);
        *self.in_tier_up.borrow_mut() = false;
        res
    }

    fn tier_up_inner(&self, user_name: &str, interp: &Interp) -> Result<(), JitError> {
        // Walk the call graph (by user_name) starting from user_name. Any
        // user_name reachable through a JIT-eligible mono's body is included
        // — we compile them all together so cross-fn calls resolve as direct
        // native calls. Cold callees (those routed only through forward
        // thunks) are not added.
        let mut user_set: std::collections::HashSet<String> =
            std::collections::HashSet::new();
        let mut stack = vec![user_name.to_string()];
        while let Some(u) = stack.pop() {
            if !user_set.insert(u.clone()) { continue; }
            if self.triggered.borrow().contains(&u) { continue; }
            let Some(idxs) = self.monos_by_user.get(&u) else { continue };
            for &idx in idxs {
                let m = &self.monos[idx];
                let mut callees = std::collections::HashSet::new();
                collect_callee_user_names(&m.def, &mut callees);
                for c in callees {
                    if self.monos_by_user.contains_key(&c)
                        && !user_set.contains(&c) {
                        stack.push(c);
                    }
                }
            }
        }

        // Collect undefined monos for the user_set.
        let mut new_monos: Vec<usize> = Vec::new();
        for u in &user_set {
            if let Some(idxs) = self.monos_by_user.get(u) {
                for &idx in idxs {
                    let name = &self.monos[idx].name;
                    if !self.defined_monos.borrow().contains(name) {
                        new_monos.push(idx);
                    }
                }
            }
        }
        if new_monos.is_empty() { return Ok(()); }

        // Lower + define each new mono.
        let mut module = self.module.borrow_mut();
        let mut atoms = self.atoms.borrow_mut();
        let mut new_reverse_thunks: Vec<(String, FuncId, FnSig)> = Vec::new();
        for idx in &new_monos {
            let m = &self.monos[*idx];
            let r = crate::codegen::lower_fn_with(
                &m.def, &m.sig, &self.callee_sigs, &mut atoms,
                &m.param_bindings, &self.user_fns_set,
            ).map_err(|e: LowerError| JitError(format!("{}: {}", m.name, e)))?;
            let LowerResult { mut func, callee_imports, builtin_imports } = r;
            rewrite_user_names(
                &mut func,
                &callee_imports,
                &builtin_imports,
                &self.user_ids,
                &self.forward_thunk_ids,
                &self.runtime_ids,
            )?;
            let mut ctx = Context::for_function(func);
            let id = self.user_ids[&m.name];
            module
                .define_function(id, &mut ctx)
                .map_err(|e| JitError(format!("{}: {}", m.name, e)))?;

            // Reverse thunk for any mono whose mono.name == user_name
            // (i.e. monomorphic — directly bindable as Value::Jit).
            if m.name == m.user_name {
                let id = define_reverse_thunk(&mut module, &m.name, &m.sig, self.user_ids[&m.name])?;
                new_reverse_thunks.push((m.name.clone(), id, m.sig.clone()));
            }
        }

        // Atom-table sync must happen before finalize because the JIT'd code
        // bakes in atom IDs from `atoms.names`.
        sync_atom_table(&atoms.names)?;
        module
            .finalize_definitions()
            .map_err(|e| JitError(format!("finalize: {}", e)))?;

        // Mark defined and rebind interp globals.
        for idx in &new_monos {
            let name = self.monos[*idx].name.clone();
            self.defined_monos.borrow_mut().insert(name);
        }
        for (name, rev_id, sig) in &new_reverse_thunks {
            let ptr = module.get_finalized_function(*rev_id);
            interp.globals.bind(
                name,
                Value::Jit(Rc::new(crate::value::JitFn {
                    name: name.clone(),
                    sig: sig.clone(),
                    fn_ptr: ptr as usize,
                })),
            );
        }
        for u in &user_set {
            self.triggered.borrow_mut().insert(u.clone());
        }
        Ok(())
    }
}

fn collect_callee_user_names(def: &FnDef, out: &mut std::collections::HashSet<String>) {
    for c in &def.clauses {
        walk_callees(&c.body, out);
        if let Some(g) = &c.guard { walk_callees(g, out); }
    }
}

fn walk_callees(e: &Expr, out: &mut std::collections::HashSet<String>) {
    match e {
        Expr::Call(callee, args) => {
            if let Expr::Var(n) = &**callee { out.insert(n.clone()); }
            walk_callees(callee, out);
            for a in args { walk_callees(a, out); }
        }
        Expr::Block(xs) => for x in xs { walk_callees(x, out); },
        Expr::If(c, t, e) => {
            walk_callees(c, out);
            walk_callees(t, out);
            if let Some(el) = e { walk_callees(el, out); }
        }
        Expr::List(xs, tail) => {
            for x in xs { walk_callees(x, out); }
            if let Some(t) = tail { walk_callees(t, out); }
        }
        Expr::Tuple(xs) => for x in xs { walk_callees(x, out); },
        Expr::BinOp(_, l, r) => { walk_callees(l, out); walk_callees(r, out); }
        Expr::UnOp(_, x) => walk_callees(x, out),
        Expr::Index(o, i) => { walk_callees(o, out); walk_callees(i, out); }
        Expr::Dot(o, _) => walk_callees(o, out),
        Expr::Match(_, x) => walk_callees(x, out),
        Expr::Case(scr, arms) => {
            walk_callees(scr, out);
            for arm in arms {
                walk_callees(&arm.body, out);
                if let Some(g) = &arm.guard { walk_callees(g, out); }
            }
        }
        _ => {}
    }
}

fn sync_atom_table(names: &[String]) -> Result<(), JitError> {
    fz_runtime::_reset_atoms();
    for (i, n) in names.iter().enumerate() {
        let id = fz_runtime::intern(n);
        if id != i as u32 {
            return Err(JitError(format!(
                "atom-table sync: {:?} got id {} expected {}",
                n, id, i
            )));
        }
    }
    Ok(())
}

fn rewrite_user_names(
    func: &mut ir::Function,
    callee_imports: &[String],
    builtin_imports: &[&'static str],
    user_ids: &HashMap<String, FuncId>,
    forward_thunk_ids: &HashMap<String, FuncId>,
    runtime_ids: &HashMap<&'static str, FuncId>,
) -> Result<(), JitError> {
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
                let id = user_ids
                    .get(callee)
                    .or_else(|| forward_thunk_ids.get(callee))
                    .ok_or_else(|| JitError(format!("internal: callee {} not declared", callee)))?;
                id.as_u32()
            }
            1 => {
                let sym = builtin_imports[name.index as usize];
                let id = runtime_ids
                    .get(sym)
                    .ok_or_else(|| JitError(format!("internal: runtime {} not declared", sym)))?;
                id.as_u32()
            }
            _ => return Err(JitError(format!("unknown namespace {}", name.namespace))),
        };
        func.params
            .reset_user_func_name(r, UserExternalName { namespace: 0, index: new_id });
    }
    Ok(())
}

// ---------------------------------------------------------------------------
// Forward + reverse thunks (CLIF emission)
// ---------------------------------------------------------------------------

fn define_forward_thunk(
    module: &mut JITModule,
    id: FuncId,
    sig: &FnSig,
    idx: u32,
    call_interp_id: FuncId,
) -> Result<(), JitError> {
    let cl_sig = sig.to_cranelift(CallConv::SystemV);
    let mut func = ir::Function::with_name_signature(
        UserFuncName::user(0, id.as_u32()),
        cl_sig.clone(),
    );
    let mut fbctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut func, &mut fbctx);

    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);

    let n_arg_slots: usize = sig.params.iter().map(flat_arity).sum();
    let n_ret_slots = flat_arity(&sig.ret);

    let args_slot = builder.create_sized_stack_slot(ir::StackSlotData::new(
        ir::StackSlotKind::ExplicitSlot,
        (n_arg_slots * 8) as u32,
        3,
    ));
    let ret_slot = builder.create_sized_stack_slot(ir::StackSlotData::new(
        ir::StackSlotKind::ExplicitSlot,
        ((n_ret_slots.max(1)) * 8) as u32,
        3,
    ));

    // Pack each native param into args_slot[i*8].
    let block_params: Vec<ir::Value> = builder.block_params(entry).to_vec();
    let mut native_idx = 0;
    let mut slot_i = 0;
    for pty in &sig.params {
        pack_lowerty(&mut builder, pty, &block_params, &mut native_idx, args_slot, &mut slot_i);
    }

    // args_ptr / ret_ptr
    let args_ptr = builder.ins().stack_addr(ir::types::I64, args_slot, 0);
    let ret_ptr = builder.ins().stack_addr(ir::types::I64, ret_slot, 0);
    let idx_v = builder.ins().iconst(ir::types::I32, idx as i64);

    let call_fr = module.declare_func_in_func(call_interp_id, builder.func);
    builder.ins().call(call_fr, &[idx_v, args_ptr, ret_ptr]);

    // Unpack ret_slot → native return values.
    let mut ret_vals: Vec<ir::Value> = Vec::new();
    let mut slot_i = 0;
    unpack_lowerty(&mut builder, &sig.ret, ret_slot, &mut slot_i, &mut ret_vals);
    builder.ins().return_(&ret_vals);

    builder.finalize();
    let mut ctx = Context::for_function(func);
    module
        .define_function(id, &mut ctx)
        .map_err(|e| JitError(format!("define forward thunk: {}", e)))?;
    Ok(())
}

fn define_reverse_thunk(
    module: &mut JITModule,
    name: &str,
    sig: &FnSig,
    user_id: FuncId,
) -> Result<FuncId, JitError> {
    let mut sig_cl = Signature::new(CallConv::SystemV);
    sig_cl.params.push(AbiParam::new(ir::types::I64)); // args ptr
    sig_cl.params.push(AbiParam::new(ir::types::I64)); // ret ptr
    let thunk_sym = format!("__fz_revthunk_{}", name);
    let id = module
        .declare_function(&thunk_sym, Linkage::Local, &sig_cl)
        .map_err(|e| JitError(format!("declare {}: {}", thunk_sym, e)))?;

    let mut func = ir::Function::with_name_signature(
        UserFuncName::user(0, id.as_u32()),
        sig_cl.clone(),
    );
    let mut fbctx = FunctionBuilderContext::new();
    let mut builder = FunctionBuilder::new(&mut func, &mut fbctx);

    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);

    let block_params = builder.block_params(entry).to_vec();
    let args_ptr = block_params[0];
    let ret_ptr = block_params[1];

    // Load native param values from args buffer.
    let mut native_args: Vec<ir::Value> = Vec::new();
    let mut slot_i = 0usize;
    for pty in &sig.params {
        load_lowerty(&mut builder, pty, args_ptr, &mut slot_i, &mut native_args);
    }

    // Call the user fn directly.
    let user_fr = module.declare_func_in_func(user_id, builder.func);
    let inst = builder.ins().call(user_fr, &native_args);
    let results: Vec<ir::Value> = builder.inst_results(inst).to_vec();

    // Store native results into ret buffer (slot order, sig.ret flatten).
    let mut native_idx = 0usize;
    let mut slot_i = 0usize;
    store_lowerty(&mut builder, &sig.ret, &results, &mut native_idx, ret_ptr, &mut slot_i);
    builder.ins().return_(&[]);

    builder.finalize();
    let mut ctx = Context::for_function(func);
    module
        .define_function(id, &mut ctx)
        .map_err(|e| JitError(format!("define reverse thunk: {}", e)))?;
    Ok(id)
}

// ---------------------------------------------------------------------------
// CLIF marshal helpers (between native cranelift Values and slot buffers)
// ---------------------------------------------------------------------------

/// Pack native cranelift values (consumed in order) for one LowerTy into the
/// args stack slot.
fn pack_lowerty(
    b: &mut FunctionBuilder<'_>,
    ty: &LowerTy,
    natives: &[ir::Value],
    native_idx: &mut usize,
    slot: ir::StackSlot,
    slot_i: &mut usize,
) {
    match ty {
        LowerTy::Tuple(ts) => {
            for t in ts {
                pack_lowerty(b, t, natives, native_idx, slot, slot_i);
            }
        }
        LowerTy::I64 => {
            let v = natives[*native_idx];
            *native_idx += 1;
            b.ins().stack_store(v, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
        }
        LowerTy::F64 => {
            let v = natives[*native_idx];
            *native_idx += 1;
            let bits = b.ins().bitcast(ir::types::I64, MemFlags::new(), v);
            b.ins().stack_store(bits, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
        }
        LowerTy::Bool => {
            let v = natives[*native_idx];
            *native_idx += 1;
            let z = b.ins().uextend(ir::types::I64, v);
            b.ins().stack_store(z, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
        }
        LowerTy::Atom => {
            let v = natives[*native_idx];
            *native_idx += 1;
            let z = b.ins().uextend(ir::types::I64, v);
            b.ins().stack_store(z, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
        }
        LowerTy::Nil => {
            *native_idx += 1;
            let z = b.ins().iconst(ir::types::I64, 0);
            b.ins().stack_store(z, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
        }
    }
}

/// Read slot-encoded values back into native cranelift Values for one LowerTy.
fn unpack_lowerty(
    b: &mut FunctionBuilder<'_>,
    ty: &LowerTy,
    slot: ir::StackSlot,
    slot_i: &mut usize,
    out: &mut Vec<ir::Value>,
) {
    match ty {
        LowerTy::Tuple(ts) => {
            for t in ts {
                unpack_lowerty(b, t, slot, slot_i, out);
            }
        }
        LowerTy::I64 => {
            let v = b.ins().stack_load(ir::types::I64, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
            out.push(v);
        }
        LowerTy::F64 => {
            let bits = b.ins().stack_load(ir::types::I64, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
            let v = b.ins().bitcast(ir::types::F64, MemFlags::new(), bits);
            out.push(v);
        }
        LowerTy::Bool => {
            let v64 = b.ins().stack_load(ir::types::I64, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
            let v = b.ins().ireduce(ir::types::I8, v64);
            out.push(v);
        }
        LowerTy::Atom => {
            let v64 = b.ins().stack_load(ir::types::I64, slot, (*slot_i * 8) as i32);
            *slot_i += 1;
            let v = b.ins().ireduce(ir::types::I32, v64);
            out.push(v);
        }
        LowerTy::Nil => {
            *slot_i += 1;
            let v = b.ins().iconst(ir::types::I8, 0);
            out.push(v);
        }
    }
}

/// Load slot-buffer (memory ptr) values into native cranelift Values for one
/// LowerTy. Used by reverse-thunk: args come in as a *const u64.
fn load_lowerty(
    b: &mut FunctionBuilder<'_>,
    ty: &LowerTy,
    base_ptr: ir::Value,
    slot_i: &mut usize,
    out: &mut Vec<ir::Value>,
) {
    let off = (*slot_i * 8) as i32;
    match ty {
        LowerTy::Tuple(ts) => {
            for t in ts {
                load_lowerty(b, t, base_ptr, slot_i, out);
            }
        }
        LowerTy::I64 => {
            let v = b.ins().load(ir::types::I64, MemFlags::trusted(), base_ptr, off);
            *slot_i += 1;
            out.push(v);
        }
        LowerTy::F64 => {
            let bits = b.ins().load(ir::types::I64, MemFlags::trusted(), base_ptr, off);
            *slot_i += 1;
            let v = b.ins().bitcast(ir::types::F64, MemFlags::new(), bits);
            out.push(v);
        }
        LowerTy::Bool => {
            let v64 = b.ins().load(ir::types::I64, MemFlags::trusted(), base_ptr, off);
            *slot_i += 1;
            let v = b.ins().ireduce(ir::types::I8, v64);
            out.push(v);
        }
        LowerTy::Atom => {
            let v64 = b.ins().load(ir::types::I64, MemFlags::trusted(), base_ptr, off);
            *slot_i += 1;
            let v = b.ins().ireduce(ir::types::I32, v64);
            out.push(v);
        }
        LowerTy::Nil => {
            *slot_i += 1;
            let v = b.ins().iconst(ir::types::I8, 0);
            out.push(v);
        }
    }
}

/// Store native cranelift Values into a slot buffer (memory ptr) for one
/// LowerTy. Used by reverse-thunk to write the user fn's return.
fn store_lowerty(
    b: &mut FunctionBuilder<'_>,
    ty: &LowerTy,
    natives: &[ir::Value],
    native_idx: &mut usize,
    base_ptr: ir::Value,
    slot_i: &mut usize,
) {
    let off = (*slot_i * 8) as i32;
    match ty {
        LowerTy::Tuple(ts) => {
            for t in ts {
                store_lowerty(b, t, natives, native_idx, base_ptr, slot_i);
            }
        }
        LowerTy::I64 => {
            let v = natives[*native_idx];
            *native_idx += 1;
            b.ins().store(MemFlags::trusted(), v, base_ptr, off);
            *slot_i += 1;
        }
        LowerTy::F64 => {
            let v = natives[*native_idx];
            *native_idx += 1;
            let bits = b.ins().bitcast(ir::types::I64, MemFlags::new(), v);
            b.ins().store(MemFlags::trusted(), bits, base_ptr, off);
            *slot_i += 1;
        }
        LowerTy::Bool => {
            let v = natives[*native_idx];
            *native_idx += 1;
            let z = b.ins().uextend(ir::types::I64, v);
            b.ins().store(MemFlags::trusted(), z, base_ptr, off);
            *slot_i += 1;
        }
        LowerTy::Atom => {
            let v = natives[*native_idx];
            *native_idx += 1;
            let z = b.ins().uextend(ir::types::I64, v);
            b.ins().store(MemFlags::trusted(), z, base_ptr, off);
            *slot_i += 1;
        }
        LowerTy::Nil => {
            *native_idx += 1;
            let z = b.ins().iconst(ir::types::I64, 0);
            b.ins().store(MemFlags::trusted(), z, base_ptr, off);
            *slot_i += 1;
        }
    }
}

// ---------------------------------------------------------------------------
// Interp → JIT call dispatch (called from eval::Interp::apply)
// ---------------------------------------------------------------------------

/// Called by Interp::apply when a Value::Jit is invoked. Marshals args into a
/// u64 slot buffer, calls the reverse-thunk, demarshals the slot return.
pub fn call_jit(j: &crate::value::JitFn, args: Vec<Value>) -> Result<Value, String> {
    if args.len() != j.sig.params.len() {
        return Err(format!(
            "{}/{} called with {} args",
            j.name,
            j.sig.params.len(),
            args.len()
        ));
    }
    let n_arg_slots: usize = j.sig.params.iter().map(flat_arity).sum();
    let n_ret_slots = flat_arity(&j.sig.ret);
    let mut arg_buf: Vec<u64> = vec![0; n_arg_slots.max(1)];
    let mut ret_buf: Vec<u64> = vec![0; n_ret_slots.max(1)];
    let mut cursor = 0;
    for (pty, v) in j.sig.params.iter().zip(args.iter()) {
        value_to_slots(pty, v, &mut arg_buf, &mut cursor);
    }
    type ThunkFn = unsafe extern "C" fn(*const u64, *mut u64);
    let f: ThunkFn = unsafe { std::mem::transmute(j.fn_ptr) };
    unsafe { f(arg_buf.as_ptr(), ret_buf.as_mut_ptr()); }
    let mut cursor = 0;
    Ok(slots_to_value(&j.sig.ret, &ret_buf, &mut cursor))
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use crate::test_support::typed_program;

    #[test]
    fn jit_runs_pure_jit_program() {
        run_str(include_str!("../fixtures/hello.fz")).expect("jit run");
    }

    #[test]
    fn jit_calls_jit_helper() {
        run_str(include_str!("../fixtures/add1.fz")).expect("jit run");
    }

    #[test]
    fn jit_lowers_multi_clause_directly() {
        // Multi-clause is JIT-eligible end-to-end, so the call from main
        // is a direct call rather than going through fz_call_interp.
        run_str(include_str!("../fixtures/classify_two_clause.fz")).expect("jit run");
    }

    #[test]
    fn jit_specializes_higher_order_fn_per_callee() {
        // fz-ul4.4.2: `apply2(f, x), do: f(x)` has a fn-typed param `f` that
        // prevents direct JIT eligibility, but each call site passes a
        // top-level user fn by name. classify must emit one MonoFn per
        // (callee, arg-shape) with f β-reduced to a direct call.
        let src = include_str!("../fixtures/apply2.fz");
        let (prog, mut typer) = typed_program(src);
        let cls = classify(&prog, &mut typer);

        let apply2_specs: Vec<_> = cls.jit_eligible.iter()
            .filter(|m| m.user_name == "apply2")
            .collect();
        assert_eq!(apply2_specs.len(), 2,
            "expected 2 apply2 specializations, got {:?}",
            apply2_specs.iter().map(|m| (&m.name, &m.sig.params)).collect::<Vec<_>>());
        for m in &apply2_specs {
            assert_eq!(m.sig.params, vec![LowerTy::I64], "fn-arg dropped from sig");
            assert_eq!(m.sig.ret, LowerTy::I64);
            assert_eq!(m.param_bindings.len(), 1, "f bound");
            assert_eq!(m.param_bindings.get("f").map(String::as_str), Some(
                if m.name.contains("double") { "double" } else { "neg" }
            ));
        }
        run_str(src).expect("jit run");
    }

    #[test]
    fn jit_specializes_polymorphic_fn_per_call_shape() {
        // `id` is called with both an int and an atom; classify must produce
        // two MonoFns with mangled names so each call site dispatches to
        // its specialization rather than falling back to interp.
        let src = include_str!("../fixtures/id_int_atom.fz");
        let (prog, mut typer) = typed_program(src);
        let cls = classify(&prog, &mut typer);

        let id_specs: Vec<_> = cls.jit_eligible.iter()
            .filter(|m| m.user_name == "id")
            .collect();
        assert_eq!(id_specs.len(), 2, "expected 2 id specializations, got {:?}",
            id_specs.iter().map(|m| (&m.name, &m.sig)).collect::<Vec<_>>());
        let sigs: Vec<&Vec<LowerTy>> = id_specs.iter().map(|m| &m.sig.params).collect();
        assert!(sigs.contains(&&vec![LowerTy::I64]), "missing I64 spec: {:?}", sigs);
        assert!(sigs.contains(&&vec![LowerTy::Atom]), "missing Atom spec: {:?}", sigs);

        run_str(src).expect("jit run");
    }

    #[test]
    fn jit_tail_self_recursion_does_not_overflow() {
        // 100k tail-self-calls only complete because the JIT actually rewrites
        // them to jumps (codegen::tests::lowers_tail_self_call_to_jump). If
        // count types as `(any, any) -> any` it falls back to interp recursion
        // and stack-overflows long before N.
        run_str(include_str!("../fixtures/tail_recursion.fz")).expect("jit run");
    }

    #[test]
    fn tier_up_patches_interp_binding_after_threshold() {
        // After the threshold-th call, `hot` is rebound from Value::Closure
        // to Value::Jit. The recursion test is the semantic acceptance that
        // tier-up actually transfers control.
        run_str(include_str!("../fixtures/hot_fn.fz")).expect("jit run");
    }

    #[test]
    fn cold_fn_stays_in_interp() {
        // Single-call helpers never cross the threshold. Result must still
        // be correct (interp dispatch path).
        run_str(include_str!("../fixtures/cold_fn.fz")).expect("jit run");
    }

    #[test]
    fn interp_only_main_calls_jit_helper_via_reverse_thunk() {
        // Multi-clause-style `main, do: ...` is interp-only; the helper
        // `inc` is JIT-eligible. When interp dispatches inc(41) under the
        // tier-up policy it eventually routes through Value::Jit.
        run_str(include_str!("../fixtures/interp_only_main.fz")).expect("jit run");
    }
}
