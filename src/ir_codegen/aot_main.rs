use super::*;
use crate::compiler2::native_codegen::runtime_call::{
    RuntimeCaller, RuntimeFn, declare_runtime_fn, runtime_call, runtime_fn_id,
};
use cranelift_codegen::ir::{self, InstBuilder, Signature, types};
use cranelift_codegen::settings;
use cranelift_codegen::verifier::verify_function;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module as ClModule};
use fz_runtime::aot_shim::{
    fz_aot_register_closure_denotations, fz_aot_register_named_schemas, fz_aot_register_static_closure,
    fz_aot_register_tuple_schemas, fz_aot_run_main, fz_aot_set_drain_dtor_entry, fz_aot_set_resume_addr, fz_aot_setup,
};
use fz_runtime::procbin::{SHARED_BIN_BYTES, shared_bin_destructor_noop};
use std::collections::HashMap;

/// The C `main` body under construction: the module that declares a symbol
/// and the builder that emits the call, together, so the startup calls reach
/// the runtime through their Rust function items.
struct AotMain<'a, 'fb, M: ClModule> {
    jmod: &'a mut M,
    b: &'a mut FunctionBuilder<'fb>,
    runtime_funcs: HashMap<&'static str, ir::FuncRef>,
}

impl<M: ClModule> RuntimeCaller for AotMain<'_, '_, M> {
    fn runtime_func_ref<F: RuntimeFn + Copy>(&mut self, name: &'static str, item: F) -> ir::FuncRef {
        if let Some(&callee) = self.runtime_funcs.get(name) {
            return callee;
        }
        let id = declare_runtime_fn(self.jmod, name, item);
        let callee = self.jmod.declare_func_in_func(id, self.b.func);
        self.runtime_funcs.insert(name, callee);
        callee
    }

    fn emit_call(&mut self, callee: ir::FuncRef, args: &[ir::Value]) -> ir::Inst {
        self.b.ins().call(callee, args)
    }

    fn sole_result(&self, call: ir::Inst) -> ir::Value {
        self.b.inst_results(call)[0]
    }
}

impl<M: ClModule> AotMain<'_, '_, M> {
    /// The address of a Local symbol this object defines.
    fn local_addr(&mut self, id: FuncId) -> ir::Value {
        let fref = self.jmod.declare_func_in_func(id, self.b.func);
        self.b.ins().func_addr(types::I64, fref)
    }

    /// A data symbol's address, or a null word where there is no data.
    fn data_addr(&mut self, data: Option<DataId>) -> ir::Value {
        match data {
            Some(data_id) => {
                let gv = self.jmod.declare_data_in_func(data_id, self.b.func);
                self.b.ins().symbol_value(types::I64, gv)
            }
            None => self.b.ins().iconst(types::I64, 0),
        }
    }

    fn iconst32(&mut self, value: u32) -> ir::Value {
        self.b.ins().iconst(types::I32, value as i64)
    }
}

/// Emit the AOT C-callable main entry. Drives the cps-in-clif startup:
/// `fz_aot_setup` -> per-closure `fz_aot_register_static_closure` ->
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
    halt_cont_body_ids: [FuncId; 4],
    entry_thunk_id: FuncId,
    static_closure_targets: &[(
        u32, /* cl_sid */
        u32, /* arity */
        FuncId,
        u32, /* halt_kind */
        fz_runtime::any_value::ClosureDenotationId,
    )],
    atom_blob_data: Option<DataId>,
    atom_blob_len: u32,
    closure_denotations_data: Option<DataId>,
    closure_denotations_len: u32,
    tuple_arities_data: Option<DataId>,
    tuple_arities_len: u32,
    named_schemas_data: Option<DataId>,
    named_schemas_len: u32,
    drain_dtor_entry_id: FuncId,
    resume_id: FuncId,
) -> Result<(), CodegenError> {
    let mut ctx = jmod.make_context();
    ctx.func.signature = c_main_sig.clone();
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        let mut main = AotMain {
            jmod,
            b: &mut b,
            runtime_funcs: HashMap::new(),
        };
        let &[argc, argv] = main.b.block_params(entry) else {
            unreachable!("C main has argc and argv parameters")
        };

        // Atom blob: symbol address + byte length.
        let atom_blob_addr = main.data_addr(atom_blob_data);
        let atom_blob_len_v = main.iconst32(atom_blob_len);

        // Shim addresses (Local symbols in this object).
        let hcb_strict_addr = main.local_addr(halt_cont_body_ids[0]);
        let hcb_i64_addr = main.local_addr(halt_cont_body_ids[1]);
        let hcb_f64_addr = main.local_addr(halt_cont_body_ids[2]);
        let hcb_atom_addr = main.local_addr(halt_cont_body_ids[3]);
        let mt_addr = main.local_addr(main_trampoline_id);
        let et_addr = main.local_addr(entry_thunk_id);
        let main_fp = main.local_addr(main_fz_func_id);

        let setup = runtime_call!(
            main,
            fz_aot_setup,
            [
                atom_blob_addr,
                atom_blob_len_v,
                hcb_strict_addr,
                hcb_i64_addr,
                hcb_f64_addr,
                hcb_atom_addr,
                et_addr,
                argc,
                argv,
            ]
        );
        let proc_v = main.sole_result(setup);

        // Install the same typed source-denotation table used by the compiler
        // before any user closure can participate in term comparison.
        {
            let denotations_addr = main.data_addr(closure_denotations_data);
            let denotations_len = main.iconst32(closure_denotations_len);
            runtime_call!(
                main,
                fz_aot_register_closure_denotations,
                [proc_v, denotations_addr, denotations_len]
            );
        }

        // Register tuple schemas before any code that might allocate one.
        // Static closures use AllocStruct (not MakeTuple), but keeping schema
        // setup adjacent to process setup preserves invariant ordering. The
        // registry takes one Tuple{N} entry per arity in array order, and that
        // order is the codegen schema iteration order, so the schema ids baked
        // into the CLIF resolve to the same schemas.
        {
            let tuple_arities_addr = main.data_addr(tuple_arities_data);
            let tuple_arities_len_v = main.iconst32(tuple_arities_len);
            runtime_call!(
                main,
                fz_aot_register_tuple_schemas,
                [proc_v, tuple_arities_addr, tuple_arities_len_v]
            );
        }
        {
            let named_schemas_addr = main.data_addr(named_schemas_data);
            let named_schemas_len_v = main.iconst32(named_schemas_len);
            runtime_call!(
                main,
                fz_aot_register_named_schemas,
                [proc_v, named_schemas_addr, named_schemas_len_v]
            );
        }

        for (cl_sid, arity, body_func_id, halt_kind, denotation) in static_closure_targets {
            let cl_sid_v = main.iconst32(*cl_sid);
            let arity_v = main.iconst32(*arity);
            let body_addr = main.local_addr(*body_func_id);
            let hk_v = main.iconst32(*halt_kind);
            let denotation_v = main.iconst32(denotation.as_u32());
            runtime_call!(
                main,
                fz_aot_register_static_closure,
                [proc_v, cl_sid_v, arity_v, body_addr, hk_v, denotation_v]
            );
        }

        // Register the drain-dtor entry shim so the AOT run-queue loop
        // can fire pending dtors at task-exit.
        {
            let drain_addr = main.local_addr(drain_dtor_entry_id);
            runtime_call!(main, fz_aot_set_drain_dtor_entry, [proc_v, drain_addr]);
        }

        // Register the `fz_resume` shim so the AOT run-queue loop can
        // resume `runnable` continuations.
        {
            let resume_addr_v = main.local_addr(resume_id);
            runtime_call!(main, fz_aot_set_resume_addr, [proc_v, resume_addr_v]);
        }

        // fz_aot_run_main(proc, main_fp, main_trampoline_addr, main_halt_kind):
        // wraps main_fp in a synthetic inner closure (via fz_main_trampoline)
        // + entry thunk. The halt kind must match the entry fn's computed
        // halt seam so the root task picks the right halt continuation body.
        let main_halt_kind_v = main.iconst32(main_halt_kind);
        let run_call = runtime_call!(main, fz_aot_run_main, [proc_v, main_fp, mt_addr, main_halt_kind_v]);
        let result = main.sole_result(run_call);
        main.b.ins().return_(&[result]);

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

/// Emit a static `SharedBin` symbol in `.data`, `SHARED_BIN_BYTES` wide:
///
///   offset  0..8   refcount = 1 (LE u64, anchor — never decremented to 0)
///   offset  8..16  bit_len (LE u64)
///   offset 16..24  bytes_ptr — relocation to the bytes payload symbol
///   offset 24..32  bytes_len (LE u64)
///   offset 32..40  destructor — function-address relocation to noop
///   offset 40..48  padding to the type's 16-byte alignment
///
/// The alignment is not cosmetic and must match `SharedBin`'s: a ProcBin
/// stub carries this address in the word Cheney forwards through, so an
/// address ending in `TAG_FWD`'s 0x8 makes a live stub read as forwarded
/// (fz-5xp.60). Two statics emitted back to back at 8-alignment put the
/// second one exactly there.
///
/// The destructor relocation is to `shared_bin_destructor_noop`, declared
/// as `Linkage::Import` so the linker resolves it to the runtime export.
pub(crate) fn define_static_sharedbin<M: ClModule>(
    jmod: &mut M,
    bytes_id: DataId,
    bytes: &[u8],
    bit_len: u64,
    idx: usize,
) -> Result<DataId, CodegenError> {
    let sb_name = format!(".fz_bs_sb_{}", idx);
    let sb_id = jmod
        .declare_data(&sb_name, Linkage::Local, /*writable=*/ true, false)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", sb_name, e)))?;
    let mut buf = vec![0u8; SHARED_BIN_BYTES];
    buf[0..8].copy_from_slice(&1u64.to_le_bytes());
    buf[8..16].copy_from_slice(&bit_len.to_le_bytes());
    // bytes_ptr at 16..24 — zero placeholder; relocation patches at link.
    buf[24..32].copy_from_slice(&(bytes.len() as u64).to_le_bytes());
    // destructor at 32..40 — zero placeholder; function-addr reloc patches.
    let mut desc = DataDescription::new();
    desc.define(buf.into_boxed_slice());
    desc.set_align(16);
    let bytes_gv = jmod.declare_data_in_data(bytes_id, &mut desc);
    desc.write_data_addr(16, bytes_gv, 0);
    let dtor_id = runtime_fn_id!(jmod, shared_bin_destructor_noop(_));
    let dtor_fref = jmod.declare_func_in_data(dtor_id, &mut desc);
    desc.write_function_addr(32, dtor_fref);
    jmod.define_data(sb_id, &desc)
        .map_err(|e| CodegenError::new(format!("define {}: {}", sb_name, e)))?;
    Ok(sb_id)
}
