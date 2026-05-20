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
//!     a SystemV `(self: i64) -> i64` thunk that reads N bound args from
//!     the runtime's `resume_args` slab (via `fz_resume_args_ptr`) and
//!     bridges into the body fn's Tail-CC entry
//!     `(bound_0, …, bound_{N-1}, self) tail`. Captures live INSIDE the
//!     closure heap object — the body's entry harness loads them from
//!     `self + 32 + i*8` itself, so the stub doesn't have to forward
//!     them as Cranelift params.
//!
//! The asymmetry is intentional: cont-closure dispatch is the cold path
//! (scheduler resume) so a SystemV→Tail bridge per cont fn is fine.
//! Value-closure dispatch is the hot path; keeping it Tail-CC end to
//! end preserves register passing for higher-order user code.
//!
//! Why the stub is per cont fn rather than per arity:
//! the bridge needs the body's exact Tail-CC sig (which encodes
//! `bound_arity` typed param slots) at compile time. A single
//! variadic shim would have to either choose a fixed maximum (the path
//! we discarded with the fz_resume_matched_N family) or pass args
//! through memory regardless of arity (which buys nothing over the
//! per-fn stub).
//!
//! See eli5.html in the repo root for the design walkthrough and
//! docs/receive-matched.md §2.5–§2.6 for the receive lifecycle.

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, MemFlags, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module};

#[cfg(test)]
use crate::ir_codegen::HEADER_SIZE;
use crate::ir_codegen::SLOT_BYTES;

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
/// `bound_arity` is the body's clause-body bound-arg count, matching the
/// `cont_extras_count` for this FnId in ir_codegen. The body's Tail-CC
/// entry has `bound_arity + 1` typed i64 params (`(bound_0, …,
/// bound_{N-1}, self)`); the stub reads each bound arg from
/// `process->resume_args[j]` via `fz_resume_args_ptr` and forwards them
/// in register order.
///
/// Captures are not passed via the stub — the body's entry harness loads
/// them from `self + 32 + i*8` on the closure heap object itself.
#[derive(Clone, Copy, Debug)]
pub struct ContStubLayout {
    pub bound_arity: u16,
}

/// Runtime FuncId handles the cont stub body needs.
#[derive(Clone, Copy, Debug)]
pub struct ContStubRuntimeRefs {
    pub resume_args_ptr_id: FuncId,
}

/// Emit the body of a cont stub previously declared with
/// [`declare_cont_stub`]. The stub:
///
///   ```text
///   fn cont_stub(self: i64) -> i64 systemv:
///       args_ptr = fz_resume_args_ptr()             // skipped when bound_arity == 0
///       for j in 0..bound_arity:
///           arg_j = load args_ptr + j*8
///       r = call_indirect body_fp(arg_0, ..., arg_{N-1}, self) tail
///       return r
///   ```
///
/// `body_fp` is supplied as a CLIF `Value` so the caller can choose how
/// the body's function address is materialised (typically `func_addr`
/// inside the stub body — that's why we take a callback instead of a
/// `FuncId` directly: it lets us write a unit test that points at an
/// arbitrary already-built test body without needing it in the same
/// Module).
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

        // 1. Bound args from runtime resume_args slab. Skip the FFI call
        //    entirely when bound_arity == 0 (after-body and zero-bind
        //    clause-body cases) — saves a SystemV call on the cold path.
        let mut bound_args: Vec<ir::Value> = Vec::with_capacity(layout.bound_arity as usize);
        if layout.bound_arity > 0 {
            let args_ptr_fref = module.declare_func_in_func(rt.resume_args_ptr_id, b.func);
            let args_call = b.ins().call(args_ptr_fref, &[]);
            let args_ptr = b.inst_results(args_call)[0];
            for j in 0..layout.bound_arity as i32 {
                let off = j * SLOT_BYTES;
                let v = b.ins().load(types::I64, MemFlags::trusted(), args_ptr, off);
                bound_args.push(v);
            }
        }

        // 2. Tail-CC bridge into the body fn.
        //    Body sig: `(bound_0, ..., bound_{N-1}, self) -> i64 tail`.
        //    Captures are NOT forwarded — body's entry harness loads
        //    them from `self + 32 + i*8` on the closure heap itself.
        let body_fp = body_fp_provider(module, &mut b);
        let mut body_sig = Signature::new(CallConv::Tail);
        for _ in 0..layout.bound_arity {
            body_sig.params.push(AbiParam::new(types::I64));
        }
        body_sig.params.push(AbiParam::new(types::I64)); // self
        body_sig.returns.push(AbiParam::new(types::I64));
        let body_sig_ref = b.func.import_signature(body_sig);

        let mut call_args: Vec<ir::Value> = bound_args;
        call_args.push(self_val);
        let body_inst = b.ins().call_indirect(body_sig_ref, body_fp, &call_args);
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
    //! Unit tests prove the SystemV→Tail-CC bridge at the Cranelift
    //! level without bringing up the fz front-end. We build a Tail-CC
    //! "body" that takes `(bound, self) -> i64` and returns `bound +
    //! *self+32` (i.e. bound arg + first capture from the closure
    //! object). The test then dlsym's the stub, points a fake closure
    //! at it, sets up `resume_args`, and asserts the sum.

    use super::*;
    use cranelift_codegen::settings::{self, Configurable};
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::Linkage;

    /// Tail-CC body: `fn body(bound: i64, self: i64) -> i64` that
    /// returns `bound + load(self+32)`. Mirrors what a ReceiveMatched
    /// clause body would do — read a capture out of the closure heap
    /// header (which the stub does NOT forward as a Cranelift param).
    fn make_summing_tail_body(jmod: &mut JITModule) -> FuncId {
        let mut sig = Signature::new(CallConv::Tail);
        sig.params.push(AbiParam::new(types::I64)); // bound
        sig.params.push(AbiParam::new(types::I64)); // self
        sig.returns.push(AbiParam::new(types::I64));
        let id = jmod
            .declare_function("test_summing_tail_body", Linkage::Local, &sig)
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
            let bound = b.block_params(entry)[0];
            let self_val = b.block_params(entry)[1];
            let cap = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                self_val,
                HEADER_SIZE + SLOT_BYTES * 2, // self + 32 (first capture)
            );
            let sum = b.ins().iadd(bound, cap);
            b.ins().return_(&[sum]);
            b.finalize();
        }
        jmod.define_function(id, &mut ctx).unwrap();
        jmod.clear_context(&mut ctx);
        id
    }

    extern "C" fn test_resume_args_ptr() -> *const u64 {
        thread_local! {
            static ARGS: std::cell::UnsafeCell<[u64; 4]> =
                const { std::cell::UnsafeCell::new([0u64; 4]) };
        }
        ARGS.with(|a| a.get() as *const u64)
    }

    fn install_test_resume_arg(value: u64) {
        let p = test_resume_args_ptr() as *mut u64;
        unsafe { *p = value };
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
        jb.symbol("test_resume_args_ptr", test_resume_args_ptr as *const u8);
        JITModule::new(jb)
    }

    fn declare_test_args(jmod: &mut JITModule) -> FuncId {
        let mut sig = Signature::new(CallConv::SystemV);
        sig.returns.push(AbiParam::new(types::I64));
        jmod.declare_function("test_resume_args_ptr", Linkage::Import, &sig)
            .unwrap()
    }

    /// Round-trip: stub forwards bound arg via Tail-CC, body adds it
    /// to a capture read from the closure object.
    #[test]
    fn cont_stub_forwards_bound_arg_and_lets_body_read_captures() {
        let mut jmod = build_jit();
        let body_id = make_summing_tail_body(&mut jmod);
        let args_ptr_id = declare_test_args(&mut jmod);
        let stub_id = declare_cont_stub(&mut jmod, "test_cont_stub").unwrap();

        let mut fbctx = FunctionBuilderContext::new();
        emit_cont_stub_body(
            &mut jmod,
            &mut fbctx,
            stub_id,
            ContStubLayout { bound_arity: 1 },
            ContStubRuntimeRefs {
                resume_args_ptr_id: args_ptr_id,
            },
            |m, b| {
                let body_fref = m.declare_func_in_func(body_id, b.func);
                b.ins().func_addr(types::I64, body_fref)
            },
        )
        .unwrap();

        jmod.finalize_definitions().unwrap();

        // Closure layout: 64 bytes. Header at 0..16; outer_cont at 16..24;
        // capture0 at 24..32; ... but the body reads self+32 (HEADER_SIZE
        // + SLOT_BYTES*2 = 32) so we plant the test capture there.
        let mut closure: Box<[u64; 8]> = Box::new([0u64; 8]);
        closure[4] = 17; // self+32 = capture (Tail-CC body reads here)
        install_test_resume_arg(25);

        let stub_ptr = jmod.get_finalized_function(stub_id);
        type Stub = extern "C" fn(u64) -> i64;
        let stub: Stub = unsafe { std::mem::transmute(stub_ptr) };
        let result = stub(closure.as_mut_ptr() as u64);
        assert_eq!(result, 17 + 25);
    }

    /// bound_arity == 0 short-circuits the resume_args fetch entirely.
    /// Tail-CC body sig becomes `(self) -> i64 tail`.
    #[test]
    fn cont_stub_skips_args_fetch_when_bound_arity_is_zero() {
        // Build a 0-bound Tail body: `fn body(self) -> i64 { load self+32 }`.
        let mut jmod = build_jit();
        let body_id = {
            let mut sig = Signature::new(CallConv::Tail);
            sig.params.push(AbiParam::new(types::I64)); // self only
            sig.returns.push(AbiParam::new(types::I64));
            let id = jmod
                .declare_function("test_cap_only_body", Linkage::Local, &sig)
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
                let self_val = b.block_params(entry)[0];
                let cap = b.ins().load(
                    types::I64,
                    MemFlags::trusted(),
                    self_val,
                    HEADER_SIZE + SLOT_BYTES * 2,
                );
                b.ins().return_(&[cap]);
                b.finalize();
            }
            jmod.define_function(id, &mut ctx).unwrap();
            jmod.clear_context(&mut ctx);
            id
        };
        // Declare args fn even though stub won't call it — required for
        // the runtime refs struct.
        let args_ptr_id = declare_test_args(&mut jmod);
        let stub_id = declare_cont_stub(&mut jmod, "test_cont_stub_noargs").unwrap();

        let mut fbctx = FunctionBuilderContext::new();
        emit_cont_stub_body(
            &mut jmod,
            &mut fbctx,
            stub_id,
            ContStubLayout { bound_arity: 0 },
            ContStubRuntimeRefs {
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

        let stub_ptr = jmod.get_finalized_function(stub_id);
        type Stub = extern "C" fn(u64) -> i64;
        let stub: Stub = unsafe { std::mem::transmute(stub_ptr) };
        let result = stub(closure.as_mut_ptr() as u64);
        assert_eq!(result, 99);
    }
}
