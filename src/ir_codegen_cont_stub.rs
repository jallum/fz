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
//!     a SystemV `(self: i64) -> i64` thunk that bridges into the body
//!     fn's Tail-CC entry `(self) tail`. Receive matcher hits materialize
//!     outcome closures whose env is `[outer_cont, bound..., captures...]`;
//!     the body's entry harness loads that env directly.
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

use cranelift_codegen::ir::{self, AbiParam, InstBuilder, Signature, types};
use cranelift_codegen::isa::CallConv;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{FuncId, Module};

#[cfg(test)]
use crate::ir_codegen::HEADER_SIZE;

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
/// `bound_arity` is retained as diagnostic layout metadata for the parked
/// matcher. Stubs no longer pass bound args in registers; bound values and
/// captures both live in the outcome closure env.
#[derive(Clone, Copy, Debug)]
pub struct ContStubLayout {
    pub bound_arity: u16,
}

/// Emit the body of a cont stub previously declared with
/// [`declare_cont_stub`]. The stub:
///
///   ```text
///   fn cont_stub(self: i64) -> i64 systemv:
///       r = call_indirect body_fp(self) tail
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

        let _ = layout;
        // Tail-CC bridge into the body fn. Body sig: `(self) -> i64 tail`.
        let body_fp = body_fp_provider(module, &mut b);
        let mut body_sig = Signature::new(CallConv::Tail);
        body_sig.params.push(AbiParam::new(types::I64)); // self
        body_sig.returns.push(AbiParam::new(types::I64));
        let body_sig_ref = b.func.import_signature(body_sig);

        let body_inst = b.ins().call_indirect(body_sig_ref, body_fp, &[self_val]);
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
    //! "body" that takes `(self) -> i64` and reads bound values plus
    //! captures from the outcome closure env.

    use super::*;
    use crate::ir_codegen::SLOT_BYTES;
    use cranelift_codegen::ir::MemFlags;
    use cranelift_codegen::settings::{self, Configurable};
    use cranelift_jit::{JITBuilder, JITModule};
    use cranelift_module::Linkage;

    /// Tail-CC body: `fn body(self: i64) -> i64` that returns
    /// `load(self+32) + load(self+40)`. Mirrors what a ReceiveMatched
    /// clause body does after outcome materialization: bound values and
    /// captures both live in the closure env.
    fn make_summing_tail_body(jmod: &mut JITModule) -> FuncId {
        let mut sig = Signature::new(CallConv::Tail);
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
            let self_val = b.block_params(entry)[0];
            let bound = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                self_val,
                HEADER_SIZE + SLOT_BYTES * 2,
            );
            let cap = b.ins().load(
                types::I64,
                MemFlags::trusted(),
                self_val,
                HEADER_SIZE + SLOT_BYTES * 3,
            );
            let sum = b.ins().iadd(bound, cap);
            b.ins().return_(&[sum]);
            b.finalize();
        }
        jmod.define_function(id, &mut ctx).unwrap();
        jmod.clear_context(&mut ctx);
        id
    }

    fn build_jit() -> JITModule {
        let isa_builder = cranelift_native::builder().expect("native isa");
        let mut flag_builder = settings::builder();
        flag_builder.set("opt_level", "none").unwrap();
        flag_builder.set("is_pic", "false").unwrap();
        let isa = isa_builder
            .finish(settings::Flags::new(flag_builder))
            .expect("isa finish");
        let jb = JITBuilder::with_isa(isa, cranelift_module::default_libcall_names());
        JITModule::new(jb)
    }

    /// Round-trip: stub invokes a body that reads both bound arg and capture
    /// from the outcome closure object.
    #[test]
    fn cont_stub_lets_body_read_outcome_env() {
        let mut jmod = build_jit();
        let body_id = make_summing_tail_body(&mut jmod);
        let stub_id = declare_cont_stub(&mut jmod, "test_cont_stub").unwrap();

        let mut fbctx = FunctionBuilderContext::new();
        emit_cont_stub_body(
            &mut jmod,
            &mut fbctx,
            stub_id,
            ContStubLayout { bound_arity: 1 },
            |m, b| {
                let body_fref = m.declare_func_in_func(body_id, b.func);
                b.ins().func_addr(types::I64, body_fref)
            },
        )
        .unwrap();

        jmod.finalize_definitions().unwrap();

        let mut closure: Box<[u64; 8]> = Box::new([0u64; 8]);
        closure[4] = 25; // self+32 = bound0
        closure[5] = 17; // self+40 = capture0

        let stub_ptr = jmod.get_finalized_function(stub_id);
        type Stub = extern "C" fn(u64) -> i64;
        let stub: Stub = unsafe { std::mem::transmute(stub_ptr) };
        let result = stub(closure.as_mut_ptr() as u64);
        assert_eq!(result, 17 + 25);
    }

    /// bound_arity is metadata now; the stub still calls `(self) -> i64 tail`.
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
        let stub_id = declare_cont_stub(&mut jmod, "test_cont_stub_noargs").unwrap();

        let mut fbctx = FunctionBuilderContext::new();
        emit_cont_stub_body(
            &mut jmod,
            &mut fbctx,
            stub_id,
            ContStubLayout { bound_arity: 0 },
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
