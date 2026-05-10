//! Cranelift codegen for fz-IR (CPS form).
//!
//! Per-fz-IR-fn ABI: `extern "C" fn(frame_ptr: *mut u8, host_ctx: *mut u8) -> *mut u8`
//!   * `frame_ptr` points to a heap-allocated frame: HeapHeader (16 B) + slots.
//!     Slot 0 = continuation pointer. Slots 1..N+1 = entry params for this fn.
//!   * `host_ctx` is an opaque pointer the host (trampoline) supplies. Halt
//!     writes the final value through it.
//!   * Return value: the next frame pointer to invoke (the trampoline calls
//!     it next), or null to halt.
//!
//! Frame schema is regenerated here as the source of truth for codegen + the
//! GC tracer: [cont_ptr, ...entry_params], all FzValue slots. (Replaces the
//! placeholder schema computed in .11.6.)
//!
//! .11.8 scope additions over .11.7: Term::Call (allocates continuation frame
//! + callee frame), Term::TailCall (frame reuse when callee shares schema,
//! else fresh alloc), Term::Return (writes result into continuation frame's
//! result slot or halts on null), real trampoline. Out of scope:
//! Term::CallClosure / TailCallClosure (closure invocation needs heap-typed
//! closures — lands later), and heap-typed prims (.11.10+).

#![allow(dead_code)]

use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp, Var};
use crate::heap::{FieldDescriptor, FieldKind, Schema};
use cranelift_codegen::ir::{
    self, condcodes::IntCC, types, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{FuncId, Linkage, Module as ClModule};
use std::collections::HashMap;
use std::sync::Arc;

const HEADER_SIZE: i32 = 16;
const SLOT_BYTES: i32 = 8;

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

/// Compiled module: persistent JITModule + per-fn ptr table + schemas. The
/// host runs a fn via `compiled.run(fn_id)`.
pub struct CompiledModule {
    module: JITModule,
    /// fz_fn_id -> compiled fn ptr.
    fn_ptrs: HashMap<u32, *const u8>,
    /// Per-fn frame schema (size, layout). Indexed by fz_fn_id (1:1 with
    /// schema_id).
    schemas: Vec<Schema>,
}

unsafe impl Send for CompiledModule {}

impl CompiledModule {
    pub fn fn_ptr(&self, fn_id: FnId) -> Option<*const u8> {
        self.fn_ptrs.get(&fn_id.0).copied()
    }

    pub fn schema_for(&self, fn_id: FnId) -> &Schema {
        &self.schemas[fn_id.0 as usize]
    }

    /// Run the trampoline with `fn_id` as the entry fn. The fn must take 0
    /// entry params (the typical `main` shape). Returns the i64 written via
    /// the final Term::Halt / Term::Return-with-null-cont.
    pub fn run(&self, fn_id: FnId) -> i64 {
        let entry_schema = &self.schemas[fn_id.0 as usize];
        let frame = unsafe { fz_alloc_frame(fn_id.0, entry_schema.size) };
        // Continuation pointer = null (entry fn).
        unsafe {
            let cont_slot = frame.add(HEADER_SIZE as usize) as *mut *mut u8;
            *cont_slot = std::ptr::null_mut();
        }
        let mut host_ctx = HostCtx { halt_value: 0 };
        let mut cur = frame;
        // Cap iterations to detect infinite trampolines in tests.
        let mut iters: usize = 0;
        let cap: usize = 10_000_000;
        while !cur.is_null() {
            iters += 1;
            if iters > cap {
                panic!("trampoline exceeded {} iterations", cap);
            }
            let header = cur as *const crate::fz_value::HeapHeader;
            let schema_id = unsafe { (*header).schema_id };
            let fn_ptr = self
                .fn_ptrs
                .get(&schema_id)
                .copied()
                .unwrap_or_else(|| panic!("no fn for schema_id {}", schema_id));
            let f: extern "C" fn(*mut u8, *mut u8) -> *mut u8 =
                unsafe { std::mem::transmute(fn_ptr) };
            cur = f(cur, &mut host_ctx as *mut HostCtx as *mut u8);
        }
        host_ctx.halt_value
    }
}

#[repr(C)]
pub struct HostCtx {
    pub halt_value: i64,
}

// ----- Runtime fns called from JIT'd code -----

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

extern "C" fn fz_alloc_frame(schema_id: u32, total_size: u32) -> *mut u8 {
    use std::alloc::{alloc_zeroed, Layout};
    // Round size up to a multiple of 16 to keep allocator happy and ensure
    // the resulting block aligns whatever follows.
    let rounded = ((total_size as usize) + 15) & !15;
    let layout = Layout::from_size_align(rounded, 16).expect("bad frame layout");
    let p = unsafe { alloc_zeroed(layout) };
    if p.is_null() {
        std::alloc::handle_alloc_error(layout);
    }
    unsafe {
        let hp = p as *mut crate::fz_value::HeapHeader;
        (*hp) = crate::fz_value::HeapHeader {
            kind: 0, // Struct
            flags: 0,
            size_bytes: total_size,
            schema_id,
            _reserved: 0,
        };
    }
    p
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

/// Build a [cont_ptr, ...entry_params] schema for a fn. All FzValue slots.
fn build_frame_schema(name: &str, num_entry_params: usize) -> Schema {
    let n_fields = 1 + num_entry_params;
    let mut fields = Vec::with_capacity(n_fields);
    for i in 0..n_fields {
        fields.push(FieldDescriptor {
            offset: (i * SLOT_BYTES as usize) as u32,
            kind: FieldKind::FzValue,
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: HEADER_SIZE as u32 + (n_fields as u32) * SLOT_BYTES as u32,
        fields,
    }
}

pub fn compile(module: &Module) -> Result<CompiledModule, CodegenError> {
    // Compute per-fn schemas indexed by FnId.0 (cps_split inserts continuation
    // fns out of declaration order, so module.fns[i].id.0 != i in general).
    let max_id = module.fns.iter().map(|f| f.id.0).max().unwrap_or(0);
    let placeholder = build_frame_schema("__placeholder", 0);
    let mut schemas: Vec<Schema> = vec![placeholder; (max_id + 1) as usize];
    for f in &module.fns {
        let entry_block = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
        let n_params = entry_block.params.len();
        schemas[f.id.0 as usize] = build_frame_schema(&f.name, n_params);
    }

    let isa = host_isa();
    let mut builder = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
    builder.symbol("fz_test_print_i64", fz_test_print_i64 as *const u8);
    builder.symbol("fz_halt", fz_halt as *const u8);
    builder.symbol("fz_alloc_frame", fz_alloc_frame as *const u8);
    let mut jmod = JITModule::new(builder);

    // Declare runtime imports.
    let print_sig = sig1(&[types::I64], &[]);
    let print_id = jmod
        .declare_function("fz_test_print_i64", Linkage::Import, &print_sig)
        .map_err(|e| CodegenError(format!("declare print: {}", e)))?;
    let halt_sig = sig1(&[types::I64, types::I64], &[]);
    let halt_id = jmod
        .declare_function("fz_halt", Linkage::Import, &halt_sig)
        .map_err(|e| CodegenError(format!("declare halt: {}", e)))?;
    let alloc_sig = sig1(&[types::I32, types::I32], &[types::I64]);
    let alloc_id = jmod
        .declare_function("fz_alloc_frame", Linkage::Import, &alloc_sig)
        .map_err(|e| CodegenError(format!("declare alloc: {}", e)))?;

    // Per-fn signature: extern "C" fn(*mut u8, *mut u8) -> *mut u8.
    let fn_sig = sig1(&[types::I64, types::I64], &[types::I64]);

    // Declare every fn first so call sites can reference each other.
    let mut fn_ids: HashMap<u32, FuncId> = HashMap::new();
    for f in &module.fns {
        let name = format!("fz_fn_{}", f.id.0);
        let id = jmod
            .declare_function(&name, Linkage::Local, &fn_sig)
            .map_err(|e| CodegenError(format!("declare {}: {}", name, e)))?;
        fn_ids.insert(f.id.0, id);
    }

    let mut fbctx = FunctionBuilderContext::new();
    let runtime = RuntimeRefs { print_id, halt_id, alloc_id };

    for f in &module.fns {
        let func_id = *fn_ids.get(&f.id.0).unwrap();
        let mut ctx = jmod.make_context();
        ctx.func.signature = fn_sig.clone();
        compile_fn(&mut jmod, &mut ctx, &mut fbctx, &fn_ids, &runtime, &schemas, f)?;
        let flags = settings::Flags::new(settings::builder());
        cranelift_codegen::verifier::verify_function(&ctx.func, &flags)
            .map_err(|e| CodegenError(format!("verify {}:\n{}\n--- IR ---\n{}", f.name, e, ctx.func.display())))?;
        jmod
            .define_function(func_id, &mut ctx)
            .map_err(|e| CodegenError(format!("define {}: {}", f.name, e)))?;
        jmod.clear_context(&mut ctx);
    }

    jmod.finalize_definitions().map_err(|e| CodegenError(format!("finalize: {}", e)))?;

    let mut fn_ptrs: HashMap<u32, *const u8> = HashMap::new();
    for (fz_fn_id, func_id) in &fn_ids {
        fn_ptrs.insert(*fz_fn_id, jmod.get_finalized_function(*func_id));
    }

    Ok(CompiledModule { module: jmod, fn_ptrs, schemas })
}

fn sig1(params: &[ir::Type], rets: &[ir::Type]) -> Signature {
    let mut s = Signature::new(CallConv::SystemV);
    for p in params { s.params.push(AbiParam::new(*p)); }
    for r in rets { s.returns.push(AbiParam::new(*r)); }
    s
}

#[derive(Clone, Copy)]
struct RuntimeRefs {
    print_id: FuncId,
    halt_id: FuncId,
    alloc_id: FuncId,
}

fn compile_fn(
    jmod: &mut JITModule,
    ctx: &mut Context,
    fbctx: &mut FunctionBuilderContext,
    fn_ids: &HashMap<u32, FuncId>,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    f: &crate::fz_ir::FnIr,
) -> Result<(), CodegenError> {
    let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);

    let mut block_map: HashMap<u32, ir::Block> = HashMap::new();
    for blk in &f.blocks {
        let cl_blk = b.create_block();
        block_map.insert(blk.id.0, cl_blk);
    }
    let entry_cl = *block_map.get(&f.entry.0).unwrap();
    b.append_block_param(entry_cl, types::I64); // frame_ptr
    b.append_block_param(entry_cl, types::I64); // host_ctx

    for blk in &f.blocks {
        if blk.id == f.entry { continue; }
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        for _ in &blk.params {
            b.append_block_param(cl_blk, types::I64);
        }
    }

    b.switch_to_block(entry_cl);
    b.seal_block(entry_cl);

    let frame_ptr = b.block_params(entry_cl)[0];
    let host_ctx = b.block_params(entry_cl)[1];

    // Load entry params from frame slots [1..N+1] (offsets 24, 32, ...).
    let mut var_map: HashMap<u32, ir::Value> = HashMap::new();
    let entry_blk = f.blocks.iter().find(|b| b.id == f.entry).unwrap();
    for (i, p) in entry_blk.params.iter().enumerate() {
        let off = HEADER_SIZE + ((i as i32 + 1) * SLOT_BYTES);
        let val = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, off);
        var_map.insert(p.0, val);
    }

    // Walk blocks in declared order with entry first.
    let mut order: Vec<&crate::fz_ir::Block> = Vec::with_capacity(f.blocks.len());
    if let Some(eb) = f.blocks.iter().find(|b| b.id == f.entry) {
        order.push(eb);
    }
    for blk in &f.blocks {
        if blk.id != f.entry { order.push(blk); }
    }

    for blk in &order {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry {
            b.switch_to_block(cl_blk);
            let params: Vec<ir::Value> = b.block_params(cl_blk).iter().copied().collect();
            for (p, val) in blk.params.iter().zip(params.iter()) {
                var_map.insert(p.0, *val);
            }
        }

        for stmt in &blk.stmts {
            let Stmt::Let(v, prim) = stmt;
            let val = lower_prim(&mut b, jmod, runtime, &var_map, prim)?;
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
            Term::Halt(v) => {
                let val = *var_map.get(&v.0).expect("unbound halt val");
                let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
                b.ins().call(halt_fref, &[host_ctx, val]);
                let null = b.ins().iconst(types::I64, 0);
                b.ins().return_(&[null]);
            }
            Term::Return(v) => {
                let val = *var_map.get(&v.0).expect("unbound return val");
                emit_return(&mut b, jmod, runtime, frame_ptr, host_ctx, val);
            }
            Term::Call { callee, args, continuation } => {
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound call arg"))
                    .collect();
                let cap_vals: Vec<ir::Value> = continuation
                    .captured
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound captured val"))
                    .collect();
                emit_call(
                    &mut b,
                    jmod,
                    runtime,
                    schemas,
                    frame_ptr,
                    callee.0,
                    &arg_vals,
                    Some((continuation.fn_id.0, &cap_vals)),
                );
            }
            Term::TailCall { callee, args } => {
                let arg_vals: Vec<ir::Value> = args
                    .iter()
                    .map(|v| *var_map.get(&v.0).expect("unbound tailcall arg"))
                    .collect();
                emit_tail_call(
                    &mut b,
                    jmod,
                    runtime,
                    schemas,
                    f.id.0,
                    frame_ptr,
                    callee.0,
                    &arg_vals,
                );
            }
            Term::CallClosure { .. } | Term::TailCallClosure { .. } => {
                return Err(CodegenError(
                    "closure call codegen lands later (heap-typed closures)".into(),
                ));
            }
        }
    }

    for blk in &f.blocks {
        let cl_blk = *block_map.get(&blk.id.0).unwrap();
        if blk.id != f.entry { b.seal_block(cl_blk); }
    }
    b.finalize();
    Ok(())
}

/// Term::Return: load my cont_ptr from frame[16]. If null, halt.
/// Otherwise write `val` to cont_frame[24] (continuation's "result" slot —
/// always entry param 0) and return cont_ptr.
fn emit_return(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    frame_ptr: ir::Value,
    host_ctx: ir::Value,
    val: ir::Value,
) {
    let cont_ptr = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
    let zero = b.ins().iconst(types::I64, 0);
    let is_null = b.ins().icmp(IntCC::Equal, cont_ptr, zero);

    let halt_blk = b.create_block();
    let invoke_blk = b.create_block();
    let no_args: Vec<BlockArg> = Vec::new();
    b.ins().brif(is_null, halt_blk, &no_args, invoke_blk, &no_args);

    // halt: fz_halt(host_ctx, val); return null.
    b.switch_to_block(halt_blk);
    b.seal_block(halt_blk);
    let halt_fref = jmod.declare_func_in_func(runtime.halt_id, b.func);
    b.ins().call(halt_fref, &[host_ctx, val]);
    let null = b.ins().iconst(types::I64, 0);
    b.ins().return_(&[null]);

    // invoke: write val to cont[24], return cont_ptr.
    b.switch_to_block(invoke_blk);
    b.seal_block(invoke_blk);
    let result_off = HEADER_SIZE + SLOT_BYTES;
    b.ins().store(MemFlags::trusted(), val, cont_ptr, result_off);
    b.ins().return_(&[cont_ptr]);
}

/// Term::Call: allocate continuation frame + callee frame. Continuation
/// frame = [my_cont_ptr, result_placeholder, ...captured]. Callee frame =
/// [cont_frame_ptr, ...args]. Return callee frame ptr.
fn emit_call(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    frame_ptr: ir::Value,
    callee_id: u32,
    args: &[ir::Value],
    cont: Option<(u32, &[ir::Value])>,
) {
    let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);

    // Read my cont_ptr from current frame[16] — this becomes the cont frame's cont_ptr.
    let my_cont = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);

    let cont_frame_val = match cont {
        Some((cont_fn_id, captured)) => {
            let cont_schema = &schemas[cont_fn_id as usize];
            let sid = b.ins().iconst(types::I32, cont_fn_id as i64);
            let sz = b.ins().iconst(types::I32, cont_schema.size as i64);
            let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
            let cf = b.inst_results(call_inst)[0];
            // Slot 0 (offset 16): cont_ptr = my_cont (my own continuation).
            b.ins().store(MemFlags::trusted(), my_cont, cf, HEADER_SIZE);
            // Slot 1 (offset 24) is the continuation's "result" param —
            // left uninitialized; will be filled by callee's Term::Return.
            // Slots 2..K+2: captured vars in declaration order.
            for (i, cv) in captured.iter().enumerate() {
                let off = HEADER_SIZE + SLOT_BYTES * (2 + i as i32);
                b.ins().store(MemFlags::trusted(), *cv, cf, off);
            }
            cf
        }
        None => my_cont,
    };

    // Allocate callee frame.
    let callee_schema = &schemas[callee_id as usize];
    let sid = b.ins().iconst(types::I32, callee_id as i64);
    let sz = b.ins().iconst(types::I32, callee_schema.size as i64);
    let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
    let callee_frame = b.inst_results(call_inst)[0];
    // Slot 0: cont_ptr = cont_frame_val.
    b.ins().store(MemFlags::trusted(), cont_frame_val, callee_frame, HEADER_SIZE);
    // Slots 1..N+1: args.
    for (i, av) in args.iter().enumerate() {
        let off = HEADER_SIZE + SLOT_BYTES * (1 + i as i32);
        b.ins().store(MemFlags::trusted(), *av, callee_frame, off);
    }

    b.ins().return_(&[callee_frame]);
}

/// Term::TailCall: if callee shares schema with caller, overwrite caller's
/// frame in place. Otherwise allocate a new frame. Either way, cont_ptr is
/// preserved (the parent's continuation).
fn emit_tail_call(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    schemas: &[Schema],
    self_id: u32,
    frame_ptr: ir::Value,
    callee_id: u32,
    args: &[ir::Value],
) {
    let callee_schema = &schemas[callee_id as usize];

    if self_id == callee_id {
        // Same schema: overwrite slots 1..N+1 with new args. Slot 0 (cont) stays.
        for (i, av) in args.iter().enumerate() {
            let off = HEADER_SIZE + SLOT_BYTES * (1 + i as i32);
            b.ins().store(MemFlags::trusted(), *av, frame_ptr, off);
        }
        b.ins().return_(&[frame_ptr]);
    } else {
        // Different schema: alloc fresh, copy cont_ptr, write args.
        let my_cont = b.ins().load(types::I64, MemFlags::trusted(), frame_ptr, HEADER_SIZE);
        let alloc_fref = jmod.declare_func_in_func(runtime.alloc_id, b.func);
        let sid = b.ins().iconst(types::I32, callee_id as i64);
        let sz = b.ins().iconst(types::I32, callee_schema.size as i64);
        let call_inst = b.ins().call(alloc_fref, &[sid, sz]);
        let nf = b.inst_results(call_inst)[0];
        b.ins().store(MemFlags::trusted(), my_cont, nf, HEADER_SIZE);
        for (i, av) in args.iter().enumerate() {
            let off = HEADER_SIZE + SLOT_BYTES * (1 + i as i32);
            b.ins().store(MemFlags::trusted(), *av, nf, off);
        }
        b.ins().return_(&[nf]);
    }
}

fn lower_prim(
    b: &mut FunctionBuilder<'_>,
    jmod: &mut JITModule,
    runtime: &RuntimeRefs,
    env: &HashMap<u32, ir::Value>,
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
            if bid.0 != 0 {
                return Err(CodegenError(format!(
                    "builtin#{} not wired (only print)",
                    bid.0
                )));
            }
            if args.len() != 1 {
                return Err(CodegenError("print/1 expected".into()));
            }
            let av = *env.get(&args[0].0).expect("unbound print arg");
            let fref = jmod.declare_func_in_func(runtime.print_id, b.func);
            b.ins().call(fref, &[av]);
            b.ins().iconst(types::I64, 0)
        }
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
                "heap/aggregate prims land in later tickets".into(),
            ));
        }
    })
}

fn bool_to_i64(b: &mut FunctionBuilder<'_>, v: ir::Value) -> ir::Value {
    b.ins().uextend(types::I64, v)
}

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
        let m = lower(vec![fn_def("main", vec![cl(vec![], Expr::Int(42))])]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 42);
    }

    #[test]
    fn binop_int_addition_runs() {
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
        let _ = test_capture_take();
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
        let m = lower(vec![fn_def(
            "main",
            vec![cl(vec![], Expr::Atom("ok".into()))],
        )]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 1); // "match_error" interned first.
    }

    // ----- .11.8 frame-allocation tests -----

    #[test]
    fn add1_via_call_returns_42() {
        // fn add1(n), do: n + 1
        // fn main(), do: add1(41)
        let add1 = fn_def(
            "add1",
            vec![cl(
                vec![Pattern::Var("n".into())],
                Expr::BinOp(ABinOp::Add, Box::new(Expr::Var("n".into())), Box::new(Expr::Int(1))),
            )],
        );
        let main = fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::Call(Box::new(Expr::Var("add1".into())), vec![Expr::Int(41)]),
            )],
        );
        let m = lower(vec![add1, main]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 42);
    }

    #[test]
    fn binop_with_inner_nontail_call() {
        // fn add1(n), do: n + 1
        // fn main(), do: add1(40) + 2     — Call to add1 is NON-tail.
        let add1 = fn_def(
            "add1",
            vec![cl(
                vec![Pattern::Var("n".into())],
                Expr::BinOp(ABinOp::Add, Box::new(Expr::Var("n".into())), Box::new(Expr::Int(1))),
            )],
        );
        let main = fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::BinOp(
                    ABinOp::Add,
                    Box::new(Expr::Call(Box::new(Expr::Var("add1".into())), vec![Expr::Int(40)])),
                    Box::new(Expr::Int(2)),
                ),
            )],
        );
        let m = lower(vec![add1, main]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 43);
    }

    #[test]
    fn fact_5_smaller_repro() {
        // Smaller version of fact: just fact(5) = 120.
        let fact = fn_def(
            "fact",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Int(1)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::BinOp(
                        ABinOp::Mul,
                        Box::new(Expr::Var("n".into())),
                        Box::new(Expr::Call(
                            Box::new(Expr::Var("fact".into())),
                            vec![Expr::BinOp(
                                ABinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            )],
                        )),
                    ),
                ),
            ],
        );
        let main = fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::Call(Box::new(Expr::Var("fact".into())), vec![Expr::Int(5)]),
            )],
        );
        let m = lower(vec![fact, main]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 120);
    }

    #[test]
    fn fact_10_runs_via_recursion_and_continuation_chain() {
        // fn fact(0), do: 1
        // fn fact(n), do: n * fact(n - 1)
        // fn main(), do: fact(10)
        let fact = fn_def(
            "fact",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Int(1)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::BinOp(
                        ABinOp::Mul,
                        Box::new(Expr::Var("n".into())),
                        Box::new(Expr::Call(
                            Box::new(Expr::Var("fact".into())),
                            vec![Expr::BinOp(
                                ABinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            )],
                        )),
                    ),
                ),
            ],
        );
        let main = fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::Call(Box::new(Expr::Var("fact".into())), vec![Expr::Int(10)]),
            )],
        );
        let m = lower(vec![fact, main]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 3628800);
    }

    #[test]
    fn count_100k_stays_bounded_via_tail_call_frame_reuse() {
        // fn count(0, acc), do: acc
        // fn count(n, acc), do: count(n - 1, acc + 1)    — tail call
        let count = fn_def(
            "count",
            vec![
                cl(
                    vec![Pattern::Int(0), Pattern::Var("acc".into())],
                    Expr::Var("acc".into()),
                ),
                cl(
                    vec![Pattern::Var("n".into()), Pattern::Var("acc".into())],
                    Expr::Call(
                        Box::new(Expr::Var("count".into())),
                        vec![
                            Expr::BinOp(
                                ABinOp::Sub,
                                Box::new(Expr::Var("n".into())),
                                Box::new(Expr::Int(1)),
                            ),
                            Expr::BinOp(
                                ABinOp::Add,
                                Box::new(Expr::Var("acc".into())),
                                Box::new(Expr::Int(1)),
                            ),
                        ],
                    ),
                ),
            ],
        );
        let main = fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::Call(
                    Box::new(Expr::Var("count".into())),
                    vec![Expr::Int(100_000), Expr::Int(0)],
                ),
            )],
        );
        let m = lower(vec![count, main]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 100_000);
    }

    #[test]
    fn mutual_recursion_even_odd_small_n() {
        // fn even(0), do: true
        // fn even(n), do: odd(n - 1)
        // fn odd(0), do: false
        // fn odd(n), do: even(n - 1)
        let even = fn_def(
            "even",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Bool(true)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::Call(
                        Box::new(Expr::Var("odd".into())),
                        vec![Expr::BinOp(
                            ABinOp::Sub,
                            Box::new(Expr::Var("n".into())),
                            Box::new(Expr::Int(1)),
                        )],
                    ),
                ),
            ],
        );
        let odd = fn_def(
            "odd",
            vec![
                cl(vec![Pattern::Int(0)], Expr::Bool(false)),
                cl(
                    vec![Pattern::Var("n".into())],
                    Expr::Call(
                        Box::new(Expr::Var("even".into())),
                        vec![Expr::BinOp(
                            ABinOp::Sub,
                            Box::new(Expr::Var("n".into())),
                            Box::new(Expr::Int(1)),
                        )],
                    ),
                ),
            ],
        );
        let main = fn_def(
            "main",
            vec![cl(
                vec![],
                Expr::Call(Box::new(Expr::Var("even".into())), vec![Expr::Int(10)]),
            )],
        );
        let m = lower(vec![even, odd, main]);
        let entry = m.fn_by_name("main").unwrap().id;
        let cm = compile(&m).unwrap();
        assert_eq!(cm.run(entry), 1); // true
    }
}
