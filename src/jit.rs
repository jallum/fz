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

use crate::aot::{extract_simple_arrow, MonoFn};
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

fn classify(prog: &Program, typer: &Typer) -> Classified {
    let mut jit_eligible = Vec::new();
    let mut interp_callable: HashMap<String, FnSig> = HashMap::new();

    for item in &prog.items {
        let Item::Fn(def) = &**item else { continue };
        if def.is_macro {
            continue;
        }
        let Some(arrow) = typer.globals.get(&def.name) else { continue };
        let Some((params, ret)) = extract_simple_arrow(arrow) else { continue };
        let sig = FnSig { params, ret };

        // lower_fn must succeed for JIT eligibility (multi-clause + guards
        // + tail-call self-recursion all work as of .12.5).
        let mut probe_atoms = AtomInterner::default();
        let mut probe_callees: HashMap<String, FnSig> = HashMap::new();
        // Self in scope so probe doesn't trip on self-recursive calls;
        // real lowering below uses full callee sigs.
        probe_callees.insert(def.name.clone(), sig.clone());
        if lower_fn(def, &sig, &probe_callees, &mut probe_atoms).is_ok() {
            jit_eligible.push(MonoFn {
                name: def.name.clone(),
                sig,
                def: def.clone(),
            });
        } else {
            interp_callable.insert(def.name.clone(), sig);
        }
    }

    // A fn that called another monomorphic fn whose body fails to lower is
    // already filtered above (probe lowers without that callee in scope, so
    // the probe will fail or unknown-callee error). Leaving the heuristic
    // simple — refining belongs in .13 tier-up policy.

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

    let cls = classify(&prog, &typer);

    // Set up Interp (loads all fns; we override JIT-eligible ones with
    // Value::Jit after compile).
    let interp = Interp::new();
    interp
        .load_program(&prog)
        .map_err(|e| JitError(format!("load: {}", e)))?;

    // Build JITModule.
    let isa = host_isa();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());

    // Register host symbols (runtime printers + cross-tier trampoline).
    let _ = builder.symbol("fz_print_i64", fz_runtime::fz_print_i64 as *const u8);
    let _ = builder.symbol("fz_print_f64", fz_runtime::fz_print_f64 as *const u8);
    let _ = builder.symbol("fz_print_bool", fz_runtime::fz_print_bool as *const u8);
    let _ = builder.symbol("fz_print_atom", fz_runtime::fz_print_atom as *const u8);
    let _ = builder.symbol("fz_print_nil", fz_runtime::fz_print_nil as *const u8);
    let _ = builder.symbol("fz_call_interp", fz_call_interp as *const u8);

    let mut module = JITModule::new(builder);

    // Declare runtime print symbols.
    let mut runtime_ids: HashMap<&'static str, FuncId> = HashMap::new();
    for (sym, params, ret) in RUNTIME_PRINT_SYMBOLS {
        let sig = FnSig { params: params.to_vec(), ret: ret.clone() };
        let cl_sig = sig.to_cranelift(CallConv::SystemV);
        let id = module
            .declare_function(sym, Linkage::Import, &cl_sig)
            .map_err(|e| JitError(format!("declare {}: {}", sym, e)))?;
        runtime_ids.insert(sym, id);
    }
    // fz_call_interp signature: (u32, *const u64, *mut u64) -> ()
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

    // Declare each JIT-eligible user fn.
    let mut user_ids: HashMap<String, FuncId> = HashMap::new();
    for m in &cls.jit_eligible {
        let cl_sig = m.sig.to_cranelift(CallConv::SystemV);
        let id = module
            .declare_function(&m.name, Linkage::Local, &cl_sig)
            .map_err(|e| JitError(format!("declare {}: {}", m.name, e)))?;
        user_ids.insert(m.name.clone(), id);
    }

    // Assign idx + declare a forward-thunk for each interp-only callable fn.
    // (Indices align with JitCtx.interp_callees order.)
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

    // Lower each user fn. For its callees:
    // - JIT-eligible → user_ids[name]
    // - interp-only-callable → forward_thunk_ids[name] (looks like a regular call)
    // The lowering API in codegen.rs needs callee sigs for *both*; combine.
    let mut callee_sigs: HashMap<String, FnSig> = HashMap::new();
    for m in &cls.jit_eligible {
        callee_sigs.insert(m.name.clone(), m.sig.clone());
    }
    for (n, s) in &cls.interp_callable {
        callee_sigs.insert(n.clone(), s.clone());
    }

    let mut atoms = AtomInterner::default();
    for m in &cls.jit_eligible {
        let r = lower_fn(&m.def, &m.sig, &callee_sigs, &mut atoms)
            .map_err(|e: LowerError| JitError(format!("{}: {}", m.name, e)))?;
        let LowerResult { mut func, callee_imports, builtin_imports } = r;
        rewrite_user_names(
            &mut func,
            &callee_imports,
            &builtin_imports,
            &user_ids,
            &forward_thunk_ids,
            &runtime_ids,
        )?;
        let mut ctx = Context::for_function(func);
        let id = user_ids[&m.name];
        module
            .define_function(id, &mut ctx)
            .map_err(|e| JitError(format!("{}: {}", m.name, e)))?;
    }

    // Define each forward-thunk: native sig in → marshal to slots → call
    // fz_call_interp(idx, args_ptr, ret_ptr) → demarshal native return.
    for (name, sig) in &interp_callee_order {
        let idx = interp_callee_idx[name];
        let id = forward_thunk_ids[name];
        define_forward_thunk(&mut module, id, sig, idx, call_interp_id)?;
    }

    // Define one reverse-thunk per JIT-eligible fn (uniform `(args, ret)`
    // ABI for Interp → JIT calls).
    let mut reverse_thunk_ids: HashMap<String, FuncId> = HashMap::new();
    for m in &cls.jit_eligible {
        let id = define_reverse_thunk(&mut module, &m.name, &m.sig, user_ids[&m.name])?;
        reverse_thunk_ids.insert(m.name.clone(), id);
    }

    // Atom-table sync: JIT shares this process's runtime atom table, but
    // codegen's local AtomInterner assigned 0..N-1 ids. Register the names in
    // order so the runtime's table matches what codegen baked in.
    sync_atom_table(&atoms.names)?;

    module
        .finalize_definitions()
        .map_err(|e| JitError(format!("finalize: {}", e)))?;

    // Get reverse-thunk ptrs and bind into Interp as Value::Jit replacements.
    for m in &cls.jit_eligible {
        let id = reverse_thunk_ids[&m.name];
        let ptr = module.get_finalized_function(id);
        interp.globals.bind(
            &m.name,
            Value::Jit(Rc::new(crate::value::JitFn {
                name: m.name.clone(),
                sig: m.sig.clone(),
                fn_ptr: ptr as usize,
            })),
        );
    }

    // Install JitCtx for the duration of the call.
    let interp_callees: Vec<(String, FnSig)> = interp_callee_order;
    let interp_ptr: *const Interp = &interp;
    JIT_CTX.with(|c| {
        *c.borrow_mut() = Some(JitCtx {
            interp: interp_ptr,
            interp_callees,
        });
    });

    // Run main. If main is JIT-eligible, dispatch through Value::Jit (already
    // bound). Otherwise fall through to the closure that load_program made.
    let result = interp.call_named("main", vec![]);
    JIT_CTX.with(|c| { *c.borrow_mut() = None; });

    // Keep the JITModule alive for the lifetime of any leftover closures
    // (none here, but jitted code pages would otherwise be freed). We leak
    // the module — fine for a one-shot run.
    std::mem::forget(module);

    result.map_err(|e| JitError(format!("runtime: {}", e)))?;
    Ok(())
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

    fn run_capture(src: &str) -> Result<(), JitError> {
        run_str(src)
    }

    #[test]
    fn jit_runs_pure_jit_program() {
        // No interp callees needed.
        let src = r#"
fn main() do
  print(40 + 2)
  print(:ok)
  print(true)
  print(nil)
end
"#;
        run_capture(src).expect("jit run");
    }

    #[test]
    fn jit_calls_jit_helper() {
        let src = r#"
fn add1(n) do n + 1 end
fn main() do
  print(add1(41))
end
"#;
        run_capture(src).expect("jit run");
    }

    #[test]
    fn jit_lowers_multi_clause_directly() {
        // Multi-clause is now JIT-eligible end-to-end, so the call from main
        // is a direct call rather than going through fz_call_interp.
        let src = r#"
fn classify(0), do: :zero
fn classify(_), do: :other
fn main() do
  print(classify(0))
  print(classify(7))
end
"#;
        run_capture(src).expect("jit run");
    }

    #[test]
    fn jit_tail_self_recursion_does_not_overflow() {
        // 100k tail-self-calls only complete because the JIT actually rewrites
        // them to jumps (codegen::tests::lowers_tail_self_call_to_jump). If
        // count types as `(any, any) -> any` it falls back to interp recursion
        // and stack-overflows long before N. Acceptance criterion for the
        // typer-recursive-widening ticket.
        let src = r#"
fn count(0, acc), do: acc
fn count(n, acc), do: count(n - 1, acc + 1)
fn main() do
  print(count(100000, 0))
end
"#;
        run_capture(src).expect("jit run");
    }

    #[test]
    fn interp_only_main_calls_jit_helper_via_reverse_thunk() {
        // `main` is multi-clause → interp-only. `inc` is JIT-eligible.
        // When interp dispatches inc(41) it must route through Value::Jit.
        let src = r#"
fn inc(n) do n + 1 end
fn main(), do: print(inc(41))
"#;
        run_capture(src).expect("jit run");
    }
}
