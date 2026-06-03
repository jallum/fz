#![allow(unused_imports)]

use super::*;
use crate::fz_ir::{BinOp, Const, FnId, Module, Prim, Stmt, Term, UnOp};
use cranelift_codegen::Context;
use cranelift_codegen::ir::{
    self, AbiParam, BlockArg, InstBuilder, MemFlags, Signature,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::verifier::verify_function;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{JITBuilder, JITModule};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::heap::{FieldDescriptor, FieldKind, Schema};
use std::collections::HashMap;
use std::sync::Arc;

/// Emit the AOT C-callable main entry. Drives the cps-in-clif startup:
/// `fz_aot_setup` → per-closure `fz_aot_register_static_closure` →
/// `fz_aot_run_main`. Entry-body addresses (fz_entry_thunk,
/// fz_main_trampoline, fz_halt_cont_body) are taken via Cranelift `func_addr`
/// against the Local symbols emitted by planned codegen.
#[allow(clippy::too_many_arguments)]
pub(crate) fn emit_aot_c_main<M: ClModule>(
    jmod: &mut M,
    fbctx: &mut FunctionBuilderContext,
    c_main_id: FuncId,
    c_main_sig: &Signature,
    main_fz_func_id: FuncId,
    main_halt_kind: u32,
    main_trampoline_id: FuncId,
    halt_cont_body_ids: [FuncId; 3],
    entry_thunk_id: FuncId,
    static_closure_targets: &[(u32, u32, FuncId, u32 /* halt_kind */)],
    atom_blob_data: Option<DataId>,
    atom_blob_len: u32,
    setup_id: FuncId,
    reg_id: FuncId,
    run_id: FuncId,
    reg_tuples_id: FuncId,
    tuple_arities_data: Option<DataId>,
    tuple_arities_len: u32,
    reg_named_schemas_id: FuncId,
    named_schemas_data: Option<DataId>,
    named_schemas_len: u32,
    set_drain_id: FuncId,
    drain_dtor_entry_id: FuncId,
    set_resume_id: FuncId,
    resume_id: FuncId,
) -> Result<(), CodegenError> {
    let mut ctx = jmod.make_context();
    ctx.func.signature = c_main_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);

        // Atom blob: symbol address + byte length.
        let atom_blob_addr = match atom_blob_data {
            Some(data_id) => {
                let gv = jmod.declare_data_in_func(data_id, b.func);
                b.ins().symbol_value(types::I64, gv)
            }
            None => b.ins().iconst(types::I64, 0),
        };
        let atom_blob_len_v = b.ins().iconst(types::I32, atom_blob_len as i64);

        // Shim addresses (Local symbols in this object).
        let hcb_strict_addr = fn_addr(jmod, halt_cont_body_ids[0], &mut b);
        let hcb_i64_addr = fn_addr(jmod, halt_cont_body_ids[1], &mut b);
        let hcb_f64_addr = fn_addr(jmod, halt_cont_body_ids[2], &mut b);
        let mt_addr = fn_addr(jmod, main_trampoline_id, &mut b);
        let et_addr = fn_addr(jmod, entry_thunk_id, &mut b);
        let main_fp = fn_addr(jmod, main_fz_func_id, &mut b);

        // proc = fz_aot_setup(atom_blob, atom_blob_len,
        //                     hcb_strict, hcb_i64, hcb_f64,
        //                     entry_thunk_addr)
        let setup_fref = jmod.declare_func_in_func(setup_id, b.func);
        let setup_call = b.ins().call(
            setup_fref,
            &[
                atom_blob_addr,
                atom_blob_len_v,
                hcb_strict_addr,
                hcb_i64_addr,
                hcb_f64_addr,
                et_addr,
            ],
        );
        let proc_v = b.inst_results(setup_call)[0];

        // Register tuple schemas before any code that might allocate one.
        // Static closures use AllocStruct (not MakeTuple), but keeping
        // schema setup adjacent to process setup preserves invariant ordering.
        {
            let tuple_arities_addr = match tuple_arities_data {
                Some(data_id) => {
                    let gv = jmod.declare_data_in_func(data_id, b.func);
                    b.ins().symbol_value(types::I64, gv)
                }
                None => b.ins().iconst(types::I64, 0),
            };
            let tuple_arities_len_v = b.ins().iconst(types::I32, tuple_arities_len as i64);
            let reg_tuples_fref = jmod.declare_func_in_func(reg_tuples_id, b.func);
            b.ins()
                .call(reg_tuples_fref, &[proc_v, tuple_arities_addr, tuple_arities_len_v]);
        }
        {
            let named_schemas_addr = match named_schemas_data {
                Some(data_id) => {
                    let gv = jmod.declare_data_in_func(data_id, b.func);
                    b.ins().symbol_value(types::I64, gv)
                }
                None => b.ins().iconst(types::I64, 0),
            };
            let named_schemas_len_v = b.ins().iconst(types::I32, named_schemas_len as i64);
            let reg_named_fref = jmod.declare_func_in_func(reg_named_schemas_id, b.func);
            b.ins()
                .call(reg_named_fref, &[proc_v, named_schemas_addr, named_schemas_len_v]);
        }

        for (cl_sid, fn_id, body_func_id, halt_kind) in static_closure_targets {
            let cl_sid_v = b.ins().iconst(types::I32, *cl_sid as i64);
            let fn_id_v = b.ins().iconst(types::I32, *fn_id as i64);
            let body_addr = fn_addr(jmod, *body_func_id, &mut b);
            let hk_v = b.ins().iconst(types::I32, *halt_kind as i64);
            let reg_fref = jmod.declare_func_in_func(reg_id, b.func);
            b.ins().call(reg_fref, &[proc_v, cl_sid_v, fn_id_v, body_addr, hk_v]);
        }

        // Register the drain-dtor entry shim so the AOT run-queue loop
        // can fire pending dtors at task-exit.
        {
            let drain_addr = fn_addr(jmod, drain_dtor_entry_id, &mut b);
            let set_drain_fref = jmod.declare_func_in_func(set_drain_id, b.func);
            b.ins().call(set_drain_fref, &[proc_v, drain_addr]);
        }

        // Register the `fz_resume` shim so the AOT run-queue loop can
        // resume `runnable` continuations.
        {
            let resume_addr_v = fn_addr(jmod, resume_id, &mut b);
            let set_resume_fref = jmod.declare_func_in_func(set_resume_id, b.func);
            b.ins().call(set_resume_fref, &[proc_v, resume_addr_v]);
        }

        // fz_aot_run_main(proc, main_fp, main_trampoline_addr, main_halt_kind):
        // wraps main_fp in a synthetic inner closure (via fz_main_trampoline)
        // + entry thunk. The halt kind must match the entry fn's computed
        // halt seam so the root task picks the right halt continuation body.
        let run_fref = jmod.declare_func_in_func(run_id, b.func);
        let main_halt_kind_v = b.ins().iconst(types::I32, main_halt_kind as i64);
        let run_call = b.ins().call(run_fref, &[proc_v, main_fp, mt_addr, main_halt_kind_v]);
        let result = b.inst_results(run_call)[0];
        b.ins().return_(&[result]);

        b.seal_all_blocks();
        b.finalize();
    }
    let flags = settings::Flags::new(settings::builder());
    verify_function(&ctx.func, &flags).map_err(|e| CodegenError::new(format!("verify C main: {}", e)))?;
    jmod.define_function(c_main_id, &mut ctx)
        .map_err(|e| CodegenError::new(format!("define C main: {}", e)))?;
    jmod.clear_context(&mut ctx);
    Ok(())
}

/// Symbol set for one unique ConstBitstring byte payload.
#[derive(Clone, Copy)]
pub(crate) struct BsConstSyms {
    /// Byte payload symbol (Local data, read-only). Always present.
    pub(crate) bytes_id: DataId,
    /// Static `SharedBin` symbol (Local data, writable so the refcount
    /// anchor lives in .data). `Some` for above-threshold payloads,
    /// `None` for below-threshold (which keep the inline / runtime
    /// allocation path via `fz_alloc_bitstring_const`).
    pub(crate) sharedbin_id: Option<DataId>,
}

/// Emit a 40-byte static `SharedBin` symbol in `.data`:
///
///   offset  0..8   refcount = 1 (LE u64, anchor — never decremented to 0)
///   offset  8..16  bit_len (LE u64)
///   offset 16..24  bytes_ptr — relocation to the bytes payload symbol
///   offset 24..32  bytes_len (LE u64)
///   offset 32..40  destructor — function-address relocation to noop
///
/// The destructor relocation is to `shared_bin_destructor_noop`, declared
/// as `Linkage::Import` so the linker resolves it to the runtime export.
pub(crate) fn define_static_sharedbin<M: ClModule>(
    jmod: &mut M,
    runtime: &RuntimeRefs,
    bytes_id: DataId,
    bytes: &[u8],
    bit_len: u64,
    idx: usize,
) -> Result<DataId, CodegenError> {
    let sb_name = format!(".fz_bs_sb_{}", idx);
    let sb_id = jmod
        .declare_data(&sb_name, Linkage::Local, /*writable=*/ true, false)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", sb_name, e)))?;
    let mut buf = vec![0u8; 40];
    buf[0..8].copy_from_slice(&1u64.to_le_bytes());
    buf[8..16].copy_from_slice(&bit_len.to_le_bytes());
    // bytes_ptr at 16..24 — zero placeholder; relocation patches at link.
    buf[24..32].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
    // destructor at 32..40 — zero placeholder; function-addr reloc patches.
    let mut desc = DataDescription::new();
    desc.define(buf.into_boxed_slice());
    desc.set_align(8);
    let bytes_gv = jmod.declare_data_in_data(bytes_id, &mut desc);
    desc.write_data_addr(16, bytes_gv, 0);
    let dtor_fref = jmod.declare_func_in_data(runtime.shared_bin_destructor_noop_id, &mut desc);
    desc.write_function_addr(32, dtor_fref);
    jmod.define_data(sb_id, &desc)
        .map_err(|e| CodegenError::new(format!("define {}: {}", sb_name, e)))?;
    Ok(sb_id)
}
