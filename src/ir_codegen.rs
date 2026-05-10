//! Cranelift codegen for fz-IR (CPS form).
//!
//! Per-fz-IR-fn ABI: `extern "C" fn(host_ctx: *mut u8) -> *mut u8`
//!   * `host_ctx` is an opaque pointer the host (trampoline) supplies. Builtins
//!     and Halt/Return write their result through it.
//!   * Return value: the next frame pointer to invoke, or null to halt.
//!
//! .11.7 scope: scalar Const/BinOp/UnOp on ints + booleans + atoms (untagged
//! i64), Goto/If, Builtin(print) wired through host runtime, Halt/Return
//! signal completion. NO frame allocation, NO Term::Call/CallClosure/TailCall.
//! Frames land in .11.8.

#![allow(dead_code)]

use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use cranelift_codegen::ir::{
    self, condcodes::IntCC, types, AbiParam, BlockArg, InstBuilder, Signature,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module as ClModule};
use std::collections::HashMap;
use std::sync::Arc;

#[derive(Debug, Clone)]
pub struct CodegenError(pub String);
impl std::fmt::Display for CodegenError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "codegen: {}", self.0)
    }
}
impl std::error::Error for CodegenError {}
impl From<String> for CodegenError {
    fn from(s: String) -> Self { Self(s) }
}

/// Compiled module: holds the persistent JITModule plus a per-fz-IR-fn
/// pointer table. The host runs a fn via `compiled.run(fn_id)`.
pub struct CompiledModule {
    module: JITModule,
    fn_ptrs: HashMap<u32, *const u8>,
}

unsafe impl Send for CompiledModule {}

impl CompiledModule {
    pub fn fn_ptr(&self, fn_id: FnId) -> Option<*const u8> {
        self.fn_ptrs.get(&fn_id.0).copied()
    }

    /// Invoke a compiled fn with a fresh HostCtx. Returns the halt result
    /// (the i64 written via Term::Halt/Return) or the next frame pointer
    /// when one is returned (always null in .11.7). For .11.7 tests, this
    /// is the trampoline driver.
    pub fn run(&self, fn_id: FnId) -> i64 {
        let ptr = self.fn_ptr(fn_id).expect("unknown fn id");
        let mut host_ctx = HostCtx { halt_value: 0 };
        let f: extern "C" fn(*mut u8) -> *mut u8 = unsafe { std::mem::transmute(ptr) };
        let mut frame: *mut u8 = f(&mut host_ctx as *mut HostCtx as *mut u8);
        // Trampoline: keep invoking returned frames until null. In .11.7 the
        // body never returns a non-null frame, so this loop runs zero times.
        while !frame.is_null() {
            // Read schema_id from the (heap) frame header — but in .11.7 we
            // don't have real frames yet, so this branch is unreachable.
            // Land it for .11.8 by looking up fn_ptr from a per-schema table.
            let _ = frame;
            break;
        }
        host_ctx.halt_value
    }
}

#[repr(C)]
pub struct HostCtx {
    pub halt_value: i64,
}

// ----- runtime fns called from JIT'd code -----

extern "C" fn fz_test_print_i64(n: i64) {
    TEST_CAPTURE.with(|c| c.borrow_mut().push(n));
}

thread_local! {
    pub static TEST_CAPTURE: std::cell::RefCell<Vec<i64>> = std::cell::RefCell::new(Vec::new());
}

pub fn test_capture_take() -> Vec<i64> {
    TEST_CAPTURE.with(|c| std::mem::take(&mut *c.borrow_mut()))
}

extern "C" fn fz_halt(host_ctx: *mut u8, value: i64) {
    unsafe { (*(host_ctx as *mut HostCtx)).halt_value = value; }
}

// ---------------------------------------------------------------------------
// Compiler
// ---------------------------------------------------------------------------

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

pub fn compile(module: &Module) -> Result<CompiledModule, CodegenError> {
    let isa = host_isa();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    builder.symbol("fz_test_print_i64", fz_test_print_i64 as *const u8);
    builder.symbol("fz_halt", fz_halt as *const u8);
    let mut jmod = JITModule::new(builder);

    // Declare runtime imports.
    let print_sig = {
        let mut s = Signature::new(CallConv::SystemV);
        s.params.push(AbiParam::new(types::I64));
        s
    };
    let print_id = jmod
        .declare_function("fz_test_print_i64", Linkage::Import, &print_sig)
        .map_err(|e| CodegenError(format!("declare print: {}", e)))?;
    let halt_sig = {
        let mut s = Signature::new(CallConv::SystemV);
        s.params.push(AbiParam::new(types::I64));
        s.params.push(AbiParam::new(types::I64));
        s
    };
    let halt_id = jmod
        .declare_function("fz_halt", Linkage::Import, &halt_sig)
        .map_err(|e| CodegenError(format!("declare halt: {}", e)))?;

    // Per-fn signature: extern "C" fn(*mut u8) -> *mut u8.
    let fn_sig = {
        let mut s = Signature::new(CallConv::SystemV);
        s.params.push(AbiParam::new(types::I64));
        s.returns.push(AbiParam::new(types::I64));
        s
    };

    // Declare every fn first so call sites can reference each other (none in
    // .11.7, but landed for .11.8).
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for f in &module.fns {
        let name = format!("fz_fn_{}", f.id.0);
        let id = jmod
            .declare_function(&name, Linkage::Local, &fn_sig)
            .map_err(|e| CodegenError(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(f.id.0, id);
    }

    let mut fbctx = FunctionBuilderContext::new();
    let runtime = RuntimeRefs { print_id, halt_id };

    for f in &module.fns {
        let func_id = *fn_ids.get(&f.id.0).unwrap();
        let mut ctx = jmod.make_context();
        ctx.func.signature = fn_sig.clone();
        compile_fn(&mut jmod, &mut ctx, &mut fbctx, &fn_ids, &runtime, f)?;
        jmod
            .define_function(func_id, &mut ctx)
            .map_err(|e| CodegenError(format!("define {}: {}", f.name, e)))?;
        jmod.clear_context(&mut ctx);
    }

    jmod.finalize_definitions().map_err(|e| CodegenError(format!("finalize: {}", e)))?;

    let mut fn_ptrs: HashMap<u32, *const u8> = HashMap::new();
    for (fz_fn_id, func_id) in &fn_ids {
        let ptr = jmod.get_finalized_function(*func_id);
        fn_ptrs.insert(*fz_fn_id, ptr);
    }

    Ok(CompiledModule { module: jmod, fn_ptrs })
}

#[derive(Clone, Copy)]
struct RuntimeRefs {
    print_id: FuncId,
    halt_id: FuncId,
}

fn compile_fn(
    jmod: &mut JITModule,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    fn_ids: &HashMap<u32, FuncId>,
    runtime: &RuntimeRefs,
    f: &crate::fz_ir::FnIr,
) -> Result<(), CodegenError> {
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    // One Cranelift block per fz-IR block. Mint them up front so terminators
    // can branch to forward blocks.
    let mut block_map: HashMap<u32, ir::Block> = HashMap::new();
    for blk in &f.blocks {
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    // The Cranelift fn's parameter list lives on the entry block.
    b.append_block_param(entry_cl, types::I64); // host_ctx

    // For each non-entry block, append a Cranelift block param per fz block param.
    for blk in &f.blocks {
        if blk.id == f.entry { continue; }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for _ in &blk.params {
            b.append_block_param(cl_blk, types::I64);
        }
    }

    b.switch_to_block(entry_cl);
    b.seal_block(entry_cl);

    // host_ctx is the entry block's only Cranelift param.
    let host_ctx_val = b.block_params(entry_cl)[0];

    // var_map: fz Var -> Cranelift Value. Cleared per-block? No — Vars are
    // unique within a fn, so a flat map is fine.
    let mut var_map: HashMap<u32, ir::Value> = HashMap::new();

    // Entry block params are the fn's args. In .11.7 fns don't take args from
    // a frame (no frame yet) — entry-fz-params have no Cranelift counterpart.
    // For now, assign them undef / iconst 0 so codegen doesn't blow up on
    // unbound refs in pathological tests; real codegen lands in .11.8.
    for p in &f.blocks.iter().find(|b| b.id == f.entry).unwrap().params {
        let v = b.ins().iconst(types::I64, 0);
        var_map.insert(p.0, v);
    }

    // Walk all blocks (entry first, then others in declared order).
    let mut order: Vec<&crate::fz_ir::Block> = Vec::with_capacity(f.blocks.len());
    if let Some(entry_blk) = f.blocks.iter().find(|b| b.id == f.entry) {
        order.push(entry_blk);
    }
    for blk in &f.blocks {
        if blk.id != f.entry { order.push(blk); }
    }

    let mut sealed: std::collections::HashSet<u32> = std::collections::HashSet::new();
    sealed.insert(f.entry.0);

    for blk in &order {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.switch_to_block(cl_blk);
            // Bind block params.
            for (p, val) in blk.params.iter().zip(b.block_params(cl_blk).iter().copied().collect::<Vec<_>>()) {
                var_map.insert(p.0, val);
            }
        }

        for stmt in &blk.stmts {
            let Stmt::Let(v, prim) = stmt;
            let val = lower_prim(&mut b, jmod, runtime, &var_map, host_ctx_val, prim)?;
            var_map.insert(v.0, val);
        }

        match &blk.terminator {
            Term::Goto(target, args) => {
                let tgt = *block_map.get(&target.0).unwrap();
                let arg_vals: Vec<BlockArg> = args
                    .iter()
                    .map(|v| BlockArg::Value(*var_map.get(&v.0).expect("unbound goto arg")))
                    .collect();
                b.ins().jump(tgt, &arg_vals);
            }
            Term::If(c, t, e) => {
                let cv = *var_map.get(&c.0).expect("unbound if cond");
                let t_b = *block_map.get(&t.0).unwrap();
                let e_b = *block_map.get(&e.0).unwrap();
                let no_args: Vec<BlockArg> = Vec::new();
                b.ins().brif(cv, t_b, &no_args, e_b, &no_args);
            }
            Term::Halt(v) | Term::Return(v) => {
                let val = *var_map.get(&v.0).expect("unbound halt val");
                // Call fz_halt(host_ctx, val) and return null.
                let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                b.ins().call(halt_fref, &[host_ctx_val, val]);
                let null = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[null]);
            }
            Term::TailCall { .. }
            | Term::TailCallClosure { .. }
            | Term::Call { .. }
            | Term::CallClosure { .. } => {
                return Err(CodegenError(format!(
                    "Term::{:?} requires frame allocation; lands in .11.8",
                    std::mem::discriminant(&blk.terminator)
                )));
            }
        }

        sealed.insert(blk.id.0);
    }

    // Seal all blocks (we walked in declared order; non-entry blocks weren't
    // sealed inline).
    for blk in &f.blocks {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry { b.seal_block(cl_blk); }
    }
    b.finalize();
    Ok(())
}

fn lower_prim(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    env: &HashMap<u32, ir::Value>,
    host_ctx_val: ir::Value,
    prim: &Prim,
) -> Result<ir::Value, CodegenError> {
    Ok(match prim {
        Prim::Const(c) => match c {
            Const::Int(n) => b.ins().iconst(types::I64, *n),
            Const::True => b.ins().iconst(types::I64, 1),
            Const::False => b.ins().iconst(types::I64, 0),
            Const::Nil => b.ins().iconst(types::I64, 0),
            Const::Atom(id) => b.ins().iconst(types::I64, *id as i64),
            Const::Float(_) | Const::Str(_) => {
                return Err(CodegenError("Float/Str codegen lands in .11.10+".into()));
            }
        },
        Prim::BinOp(op, a, bv) => {
            let av = *env.get(&a.0).expect("unbound binop a");
            let bvv = *env.get(&bv.0).expect("unbound binop b");
            match op {
                BinOp::Add => b.ins().iadd(av, bvv),
                BinOp::Sub => b.ins().isub(av, bvv),
                BinOp::Mul => b.ins().imul(av, bvv),
                BinOp::Div => b.ins().sdiv(av, bvv),
                BinOp::Mod => b.ins().srem(av, bvv),
                BinOp::Eq => { let v = b.ins().icmp(IntCC::Equal, av, bvv); bool_to_i64(b, v) }
                BinOp::Neq => { let v = b.ins().icmp(IntCC::NotEqual, av, bvv); bool_to_i64(b, v) }
                BinOp::Lt => { let v = b.ins().icmp(IntCC::SignedLessThan, av, bvv); bool_to_i64(b, v) }
                BinOp::Le => { let v = b.ins().icmp(IntCC::SignedLessThanOrEqual, av, bvv); bool_to_i64(b, v) }
                BinOp::Gt => { let v = b.ins().icmp(IntCC::SignedGreaterThan, av, bvv); bool_to_i64(b, v) }
                BinOp::Ge => { let v = b.ins().icmp(IntCC::SignedGreaterThanOrEqual, av, bvv); bool_to_i64(b, v) }
                BinOp::And => b.ins().band(av, bvv),
                BinOp::Or => b.ins().bor(av, bvv),
            }
        }
        Prim::UnOp(op, x) => {
            let xv = *env.get(&x.0).expect("unbound unop x");
            match op {
                UnOp::Neg => b.ins().ineg(xv),
                UnOp::Not => {
                    let zero = b.ins().iconst(types::I64, 0);
                    let cmp = b.ins().icmp(IntCC::Equal, xv, zero);
                    bool_to_i64(b, cmp)
                }
            }
        }
        Prim::Builtin(bid, args) => {
            // .11.7: only "print" wired (id 0). Others land later.
            if bid.0 != 0 {
                return Err(CodegenError(format!(
                    "builtin#{} not wired in .11.7 (only print)",
                    bid.0
                )));
            }
            if args.len() != 1 {
                return Err(CodegenError("print/1 expected".into()));
            }
            let av = *env.get(&args[0].0).expect("unbound print arg");
            let fref = jmod.declare_func_in_func(runtime.print_id, b.func);
            b.ins().call(fref, &[av]);
            // print returns nil; encode as 0.
            b.ins().iconst(types::I64, 0)
        }
        // Heap-typed prims land in later tickets.
        Prim::AllocStruct(_, _)
        | Prim::ListCons(_, _)
        | Prim::ListHead(_)
        | Prim::ListTail(_)
        | Prim::ListIsNil(_)
        | Prim::MakeTuple(_)
        | Prim::TupleField(_, _)
        | Prim::MakeList(_, _)
        | Prim::MakeClosure(_, _)
        | Prim::MakeMap(_)
        | Prim::MapUpdate(_, _)
        | Prim::MapGet(_, _)
        | Prim::MakeVec(_, _)
        | Prim::MakeBitstring(_)
        | Prim::BitReaderInit(_)
        | Prim::BitReadField { .. }
        | Prim::BitReaderDone(_) => {
            return Err(CodegenError(
                "heap/aggregate prims require frames + heap (.11.8+)".into(),
            ));
        }
    })
}

fn bool_to_i64(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    // Cranelift's icmp returns an i8 in newer versions; uextend to i64.
    b.ins().uextend(types::I64, v)
}

// Suppress unused warnings until later tickets exercise them.
#[allow(dead_code)]
fn _kp(_: &Var) {}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BinOp as ABinOp, Expr, FnClause, FnDef, Item, Pattern, Program};
    use crate::ir_lower::lower_program;
    use std::rc::Rc;

    fn fn_def(name: &str, clauses: Vec<FnClause>) -> Rc<Item> {
        Rc::new(Item::Fn(FnDef {
            name: name.into(),
            clauses,
            is_macro: false,
            doc: None,
        }))
    }

    fn cl(params: Vec<Pattern>, body: Expr) -> FnClause {
        FnClause { params, guard: None, body }
    }

    fn lower(items: Vec<Rc<Item>>) -> Module {
        lower_program(&Program { items }).unwrap()
    }

    #[test]
    fn const_int_runs_and_halts_with_value() {
        // fn main, do: 42
        let m = lower(vec![fn_def("main", vec![cl(vec![], Expr::Int(42))])]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 42);
    }

    #[test]
    fn binop_int_addition_runs() {
        // fn main, do: 40 + 2
        let m = lower(vec![fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::BinOp(ABinOp::Add, Box::new(Expr::Int(40)), Box::new(Expr::Int(2))),
            )],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 42);
    }

    #[test]
    fn binop_chain_runs() {
        // (1 + 2) * 7  = 21
        let m = lower(vec![fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::BinOp(
                    ABinOp::Mul,
                    Box::new(Expr::BinOp(
                        ABinOp::Add,
                        Box::new(Expr::Int(1)),
                        Box::new(Expr::Int(2)),
                    )),
                    Box::new(Expr::Int(7)),
                ),
            )],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 21);
    }

    #[test]
    fn if_then_else_runs() {
        // if 1 < 2 then 100 else 200
        let m = lower(vec![fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::If(
                    Box::new(Expr::BinOp(
                        ABinOp::Lt,
                        Box::new(Expr::Int(1)),
                        Box::new(Expr::Int(2)),
                    )),
                    Box::new(Expr::Int(100)),
                    Some(Box::new(Expr::Int(200))),
                ),
            )],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 100);
    }

    #[test]
    fn print_builtin_routes_through_runtime() {
        // fn main, do: print(40 + 2)
        let m = lower(vec![fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::Call(
                    Box::new(Expr::Var("print".into())),
                    vec![Expr::BinOp(
                        ABinOp::Add,
                        Box::new(Expr::Int(40)),
                        Box::new(Expr::Int(2)),
                    )],
                ),
            )],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let _ = test_capture_take(); // clear
        let cm = compile(&m).unwrap();
        let _ = cm.run(entry);
        let captured = test_capture_take();
        assert_eq!(captured, vec![42]);
    }

    #[test]
    fn unop_neg_runs() {
        let m = lower(vec![fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::UnOp(crate::ast::UnOp::Neg, Box::new(Expr::Int(7))),
            )],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), -7);
    }

    #[test]
    fn atom_const_returns_atom_id() {
        // fn main, do: :ok    — halt value = atom id (interned)
        let m = lower(vec![fn_def(
            "main",
            vec![cl(vec![], Expr::Atom("ok".into()))],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        // "match_error" interned first by lower_fn's fail block, so "ok" -> id 1.
        assert_eq!(cm.run(entry), 1);
    }
}
