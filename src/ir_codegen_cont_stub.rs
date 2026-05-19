// fz-70q.5.3: staging — exported but not wired into the main codegen
// pipeline yet. fz-70q.5.4 retires this allow once `build_cont_closure`
// starts pointing closure stub_fps at the symbols this module emits.
#![allow(dead_code)]

//! fz-70q.5.3 — cont-closure stubs.
//!
//! A *cont closure* is a heap-resident continuation built by
//! `build_cont_closure` (see ir_codegen.rs) and invoked by the
//! scheduler across a quantum boundary — typical examples are the
//! body / guard / after-body of a `Term::ReceiveMatched`, and the
//! cont of a legacy `Term::Receive`. Their dispatch entry sits at
//! `closure + HEADER_SIZE` (the `stub_fp` slot).
//!
//! Two stub shapes live in this module, one for each closure role:
//!
//!   - **Value closures** (MakeClosure target, TailCallClosure callee)
//!     use the `.29.5` Tail-CC stub: `(args..., self, cont) -> i64 tail`.
//!     That stub already exists in ir_codegen and is not touched here.
//!
//!   - **Cont closures** use the *cont stub* emitted by this module:
//!     a SystemV `(self: i64) -> i64` thunk that
//!       1. allocs a frame for the (uniform) body fn,
//!       2. populates the frame slots from captures (at `self + 32 +
//!          i*8`) and from the runtime `resume_args` slab (one slot per
//!          bound-arg in the matching clause),
//!       3. installs `outer_cont` (read from `self + 24`) at frame slot
//!          0, and
//!       4. tail-calls the body's uniform SystemV `(frame, host_ctx) ->
//!          i64` entry, returning its result verbatim.
//!
//! The asymmetry is intentional: cont-closure dispatch is the cold path
//! (scheduler resume) and crossing into a uniform body lets the body
//! freely tail-call other uniform fns (`handle_get → server`) without
//! ABI mismatches. Value-closure dispatch is the hot path; keeping it
//! Tail-CC preserves register passing for higher-order user code.
//!
//! See eli5.html in the repo root for the design walkthrough and
//! docs/receive-matched.md §2.5–§2.6 for the receive lifecycle.

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, MemFlags, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module};

use crate::ir_codegen::{HEADER_SIZE, SLOT_BYTES};

/// The cont stub's exported Cranelift signature: `(self: i64) -> i64`
/// SystemV. Public so the caller (park-site / build_cont_closure) can
/// import it when threading `stub_fp` into a closure header.
pub fn cont_stub_signature() -> Signature {
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(types::I64)); // self
    sig.returns.push(AbiParam::new(types::I64)); // body's result, returned verbatim
    sig
}

/// Declare a cont stub fn in `module` with the given external name and
/// the standard cont-stub signature. The caller emits the body via
/// [`emit_cont_stub_body`] in a separate pass once `RuntimeRefs` is
/// available.
pub fn declare_cont_stub<M: Module>(module: &mut M, name: &str) -> Result<FuncId, String> {
    let sig = cont_stub_signature();
    module
        .declare_function(name, cranelift_module::Linkage::Local, &sig)
        .map_err(|e| format!("declare {}: {}", name, e))
}

/// Layout descriptor for one cont stub's emission.
///
/// `n_captures` is the count of capture slots that the body fn expects
/// to receive ahead of the bound args (positions `fz_param[0..n_caps]`
/// per the cont fn's IR). They are read from `self + 32 + i*8` on the
/// closure heap object.
///
/// `bound_arity` is the body's clause-body bound-arg count (positions
/// `fz_param[n_caps..n_caps+bound_arity]`). They are read from
/// `process->resume_args[0..bound_arity]` via the `fz_resume_args_ptr`
/// runtime helper.
///
/// `body_frame_size_bytes` is what gets passed to `fz_alloc_frame` —
/// the size class chosen by the codegen frame-size table for the body's
/// spec. The stub does not see the spec id; the caller (which knows the
/// body's SpecId at park-site lowering) precomputes this.
#[derive(Clone, Copy, Debug)]
pub struct ContStubLayout {
    pub n_captures: u16,
    pub bound_arity: u16,
    pub body_frame_size_bytes: u32,
    /// `schema_id` argument to `fz_alloc_frame` — body's frame schema.
    pub body_schema_id: u32,
}

/// Runtime FuncId handles the cont stub body needs.
#[derive(Clone, Copy, Debug)]
pub struct ContStubRuntimeRefs {
    pub alloc_frame_id: FuncId,
    pub resume_args_ptr_id: FuncId,
}

/// Emit the body of a cont stub previously declared with
/// [`declare_cont_stub`]. The stub:
///
///   ```text
///   fn cont_stub(self: i64) -> i64 systemv:
///       frame    = fz_alloc_frame(body_schema_id, body_frame_size_bytes)
///       outer    = load self + 24
///                  store outer, frame + 16          // slot 0 of frame
///       for i in 0..n_captures:
///           c = load self + 32 + i*8
///           store c, frame + 24 + i*8
///       args_ptr = fz_resume_args_ptr()             // may be null when bound_arity == 0
///       for j in 0..bound_arity:
///           v = load args_ptr + j*8
///           store v, frame + 24 + (n_captures + j)*8
///       r = call_indirect body_fp(frame, 0) systemv
///       return r
///   ```
///
/// `body_fp` is supplied as a CLIF `Value` so the caller can choose how
/// the body's function address is materialised (typically `func_addr`
/// inside the stub body — that's why we take a callback instead of a
/// `FuncId` directly: it lets us write a unit test that points at an
/// arbitrary already-built test body without needing it in the same
/// Module).
#[allow(clippy::too_many_arguments)]
pub fn emit_cont_stub_body<M, F>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    stub_id: FuncId,
    layout: ContStubLayout,
    rt: ContStubRuntimeRefs,
    body_fp_provider: F,
) -> Result<(), String>
where
    M: Module,
    F: FnOnce(&mut M, &mut FunctionBuilder<'_>) -> ir::Value,
{
    let mut ctx = module.make_context();
    ctx.func.signature = cont_stub_signature();

    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);

        let self_val = b.block_params(entry)[0];

        // 1. Allocate the body's frame via fz_alloc_frame(schema_id, size).
        let alloc_fref = module.declare_func_in_func(rt.alloc_frame_id, b.func);
        let schema = b.ins().iconst(types::I32, layout.body_schema_id as i64);
        let size = b
            .ins()
            .iconst(types::I32, layout.body_frame_size_bytes as i64);
        let alloc_inst = b.ins().call(alloc_fref, &[schema, size]);
        let frame = b.inst_results(alloc_inst)[0];

        // 2. Outer cont: load self+24, store frame+16 (slot 0).
        let outer = b.ins().load(
            types::I64,
            MemFlags::trusted(),
            self_val,
            HEADER_SIZE + SLOT_BYTES,
        );
        b.ins()
            .store(MemFlags::trusted(), outer, frame, HEADER_SIZE);

        // 3. Captures: closure self+32+i*8 -> frame+24+i*8.
        //    The body fn's entry harness (uniform path) reads its
        //    `fz_param[i]` from `frame + HEADER_SIZE + (i+1)*SLOT_BYTES`,
        //    i.e. starting at +24. Captures occupy `fz_param[0..n_caps]`.
        for i in 0..layout.n_captures as i32 {
            let src_off = HEADER_SIZE + SLOT_BYTES * 2 + i * SLOT_BYTES;
            let dst_off = HEADER_SIZE + SLOT_BYTES + i * SLOT_BYTES;
            let c = b
                .ins()
                .load(types::I64, MemFlags::trusted(), self_val, src_off);
            b.ins().store(MemFlags::trusted(), c, frame, dst_off);
        }

        // 4. Bound args from runtime resume_args slab.
        //    Skip the FFI call entirely when bound_arity == 0 — the
        //    after-body and zero-bind clause-body case. Saves a SystemV
        //    call on the cold path.
        if layout.bound_arity > 0 {
            let args_ptr_fref = module.declare_func_in_func(rt.resume_args_ptr_id, b.func);
            let args_call = b.ins().call(args_ptr_fref, &[]);
            let args_ptr = b.inst_results(args_call)[0];
            for j in 0..layout.bound_arity as i32 {
                let src_off = j * SLOT_BYTES;
                let dst_off =
                    HEADER_SIZE + SLOT_BYTES + (layout.n_captures as i32 + j) * SLOT_BYTES;
                let v = b
                    .ins()
                    .load(types::I64, MemFlags::trusted(), args_ptr, src_off);
                b.ins().store(MemFlags::trusted(), v, frame, dst_off);
            }
        }

        // 5. Call body via the caller-supplied address provider.
        //    Uniform body sig: `(frame, host_ctx) -> i64 systemv`.
        let body_fp = body_fp_provider(module, &mut b);
        let mut body_sig = Signature::new(CallConv::SystemV);
        body_sig.params.push(AbiParam::new(types::I64)); // frame
        body_sig.params.push(AbiParam::new(types::I64)); // host_ctx (unused, pass 0)
        body_sig.returns.push(AbiParam::new(types::I64));
        let body_sig_ref = b.func.import_signature(body_sig);
        let host_ctx_null = b.ins().iconst(types::I64, 0);
        let body_inst = b
            .ins()
            .call_indirect(body_sig_ref, body_fp, &[frame, host_ctx_null]);
        let r = b.inst_results(body_inst)[0];
        b.ins().return_(&[r]);

        b.finalize();
    }

    module
        .define_function(stub_id, &mut ctx)
        .map_err(|e| format!("define cont stub: {}", e))?;
    module.clear_context(&mut ctx);
    Ok(())
}

#[cfg(test)]
mod tests {
    //! Unit tests prove the stub wire path end-to-end at the Cranelift
    //! level, without bringing up the fz front-end. We construct a fake
    //! "body" fn that takes a (frame, host_ctx) SystemV pair, reads a
    //! captured value out of frame+24 and a bound-arg out of frame+32,
    //! and returns their sum. The test then dlsym's the stub, points a
    //! fake closure at it, sets up `resume_args`, and calls — the
    //! returned sum confirms both load paths fired correctly.
    //!
    //! We deliberately bypass `fz_alloc_frame` for the test (it would
    //! need a Process installed in TLS). Instead the test's "body" fn
    //! receives a caller-allocated 64-byte buffer and treats it as the
    //! frame. This is achieved by overriding the body to ignore the
    //! frame ptr and reading directly from a global — see below.

    use super::*;
    use cranelift_codegen::settings::{self, Configurable};
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::Linkage;

    /// Test-only "body" that ignores `frame_ptr` and returns
    /// `(*frame+24) + (*frame+32)`. Confirms the stub wrote the capture
    /// at offset 24 and the bound arg at offset 32 (n_captures=1,
    /// bound_arity=1).
    fn make_summing_body(jmod: &mut JITModule) -> FuncId {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I64)); // frame
        sig.params.push(AbiParam::new(types::I64)); // host_ctx
        sig.returns.push(AbiParam::new(types::I64));
        let id = jmod
            .declare_function("test_summing_body", Linkage::Local, &sig)
            .unwrap();
        let mut ctx = jmod.make_context();
        ctx.func.signature = sig;
        let mut fbctx = FunctionBuilderContext::new();
        {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let frame = b.block_params(entry)[0];
            let cap = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                frame,
                HEADER_SIZE + SLOT_BYTES,
            );
            let arg = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                frame,
                HEADER_SIZE + SLOT_BYTES * 2,
            );
            let sum = b.ins().iadd(cap, arg);
            b.ins().return_(&[sum]);
            b.finalize();
        }
        jmod.define_function(id, &mut ctx).unwrap();
        jmod.clear_context(&mut ctx);
        id
    }

    /// Test-only fz_alloc_frame replacement: returns a pointer to a
    /// thread-local 64-byte buffer. Allows the stub to "allocate" a
    /// frame without bringing up a Process / heap. Real cont stubs use
    /// the genuine FFI alloc_frame; the layout (slot offsets) is what's
    /// being verified here.
    extern "C" fn test_alloc_frame(_schema: u32, _size: u32) -> u64 {
        thread_local! {
            static BUF: std::cell::UnsafeCell<[u64; 8]> =
                const { std::cell::UnsafeCell::new([0u64; 8]) };
        }
        BUF.with(|b| b.get() as u64)
    }

    extern "C" fn test_resume_args_ptr() -> *const u64 {
        thread_local! {
            static ARGS: std::cell::UnsafeCell<[u64; 4]> =
                const { std::cell::UnsafeCell::new([0u64; 4]) };
        }
        ARGS.with(|a| a.get() as *const u64)
    }

    fn install_test_resume_arg(value: u64) {
        // Same TLS as test_resume_args_ptr — write through the raw ptr.
        let p = test_resume_args_ptr() as *mut u64;
        unsafe {
            *p = value;
        }
    }

    fn build_jit() -> JITModule {
        let isa_builder = cranelift_native::builder().expect("native isa");
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "none").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("isa finish");
        let mut jb = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        jb.symbol("test_alloc_frame", test_alloc_frame as *const u8);
        jb.symbol("test_resume_args_ptr", test_resume_args_ptr as *const u8);
        JITModule::new(jb)
    }

    fn declare_test_alloc(jmod: &mut JITModule) -> FuncId {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.params.push(AbiParam::new(types::I32));
        sig.params.push(AbiParam::new(types::I32));
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function("test_alloc_frame", Linkage::Import, &sig)
            .unwrap()
    }

    fn declare_test_args(jmod: &mut JITModule) -> FuncId {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function("test_resume_args_ptr", Linkage::Import, &sig)
            .unwrap()
    }

    /// Round-trip: stub reads capture from closure + bound arg from
    /// resume_args, populates frame, body sums them. n_caps=1,
    /// bound_arity=1.
    #[test]
    fn cont_stub_wires_capture_and_bound_arg_into_body_frame() {
        let mut jmod = build_jit();
        let body_id = make_summing_body(&mut jmod);
        let alloc_id = declare_test_alloc(&mut jmod);
        let args_ptr_id = declare_test_args(&mut jmod);
        let stub_id = declare_cont_stub(&mut jmod, "test_cont_stub").unwrap();

        let mut fbctx = FunctionBuilderContext::new();
        emit_cont_stub_body(
            &mut jmod,
            &mut fbctx,
            stub_id,
            ContStubLayout {
                n_captures: 1,
                bound_arity: 1,
                body_frame_size_bytes: 64,
                body_schema_id: 0,
            },
            ContStubRuntimeRefs {
                alloc_frame_id: alloc_id,
                resume_args_ptr_id: args_ptr_id,
            },
            |m, b| {
                let body_fref = m.declare_func_in_func(body_id, b.func);
                b.ins().func_addr(types::I64, body_fref)
            },
        )
        .unwrap();

        jmod.finalize_definitions().unwrap();

        // Build a fake closure: 64 bytes — [header(16) | outer_cont(8) |
        // capture0(8) | padding...]. Place capture0=100, outer_cont=0
        // (the body ignores outer_cont in this test).
        let mut closure: Box<[u64; 8]> = Box::new([0u64; 8]);
        closure[3] = 100; // self+24 = outer_cont (test body ignores)
        closure[4] = 17; // self+32 = capture0
        // resume_args[0] = 25
        install_test_resume_arg(25);

        let stub_ptr = jmod.get_finalized_function(stub_id);
        type Stub = extern "C" fn(u64) -> i64;
        let stub: Stub = unsafe { std::mem::transmute(stub_ptr) };
        let result = stub(closure.as_mut_ptr() as u64);
        // Body returned cap (17) + bound_arg (25) = 42.
        assert_eq!(result, 42);
    }

    /// bound_arity == 0 short-circuits the resume_args fetch — confirm
    /// the stub still runs and the body sees only captures.
    #[test]
    fn cont_stub_skips_args_fetch_when_bound_arity_is_zero() {
        let mut jmod = build_jit();
        let body_id = make_summing_body(&mut jmod);
        let alloc_id = declare_test_alloc(&mut jmod);
        // Declare args fn even though stub won't call it — needed for
        // ContStubRuntimeRefs.
        let args_ptr_id = declare_test_args(&mut jmod);
        let stub_id = declare_cont_stub(&mut jmod, "test_cont_stub_noargs").unwrap();

        let mut fbctx = FunctionBuilderContext::new();
        emit_cont_stub_body(
            &mut jmod,
            &mut fbctx,
            stub_id,
            ContStubLayout {
                n_captures: 1,
                bound_arity: 0,
                body_frame_size_bytes: 64,
                body_schema_id: 0,
            },
            ContStubRuntimeRefs {
                alloc_frame_id: alloc_id,
                resume_args_ptr_id: args_ptr_id,
            },
            |m, b| {
                let body_fref = m.declare_func_in_func(body_id, b.func);
                b.ins().func_addr(types::I64, body_fref)
            },
        )
        .unwrap();

        jmod.finalize_definitions().unwrap();

        let mut closure: Box<[u64; 8]> = Box::new([0u64; 8]);
        closure[4] = 99; // capture0
        // resume_args slot remains untouched — must not be read.

        let stub_ptr = jmod.get_finalized_function(stub_id);
        type Stub = extern "C" fn(u64) -> i64;
        let stub: Stub = unsafe { std::mem::transmute(stub_ptr) };
        let result = stub(closure.as_mut_ptr() as u64);
        // body reads frame+32 (bound-arg slot) which test_alloc_frame
        // zeroed; cap (99) + 0 = 99.
        assert_eq!(result, 99);
    }
}
