//! Low-level Cranelift helpers shared by codegen modules.

use super::*;
use crate::source::Span;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, Signature, SourceLoc, condcodes::IntCC, types};
use cranelift_codegen::isa::TargetIsa;
use cranelift_codegen::settings::{self, Configurable, Flags};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::{ArenaMemoryProvider, JITBuilder};
use cranelift_module::{FuncId, Module, ModuleError};
use cranelift_native::builder;
use fz_runtime::any_value::{
    AnyValueRefPacking, MAP_FLAT_COUNT_SHIFT, MAP_KIND_BYTES_OFFSET, MAP_NOT_FLAT_MASK, ValueKind,
};
use std::sync::Arc;

/// Where compiled code runs, which decides how it reaches the functions it
/// imports: the runtime's helpers, externs, and Cranelift's own library calls.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CodeHome {
    /// In this process, in the JIT's arena. The runtime lives in the process
    /// image, which may lie beyond a direct branch's reach, so a call loads
    /// its callee's address and branches through a register.
    ThisProcess,
    /// Linked into an executable with the runtime archive. The linker places
    /// every import within reach (a C library function gets a stub or PLT
    /// entry), so a call is one direct branch. The code is position
    /// independent: macOS rejects text relocations in an executable.
    Executable,
}

/// Build the host ISA for code that runs in `home`.
pub(crate) fn host_isa_for(home: CodeHome) -> Arc<dyn TargetIsa> {
    let linked_with_imports = match home {
        CodeHome::ThisProcess => "false",
        CodeHome::Executable => "true",
    };
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", linked_with_imports).unwrap();
    flag_builder.set("use_colocated_libcalls", linked_with_imports).unwrap();
    // Cranelift's Tail CC implementation asserts frame pointers are present.
    // macOS preserves them by default; Linux does not.
    flag_builder.set("preserve_frame_pointers", "true").unwrap();
    flag_builder.set("enable_pinned_reg", "true").unwrap();
    let isa_builder = builder().expect("host ISA");
    isa_builder.finish(Flags::new(flag_builder)).expect("isa finish")
}

/// The span a JIT module's code and data share. JIT code addresses its own
/// data pc-relative with a signed 32-bit page distance, so a module that keeps
/// everything inside one span of 2^31 bytes reaches all of it.
pub(crate) const JIT_ARENA_BYTES: usize = 1 << 31;

/// A builder for a JIT module that places its code and data inside one
/// reservation of `JIT_ARENA_BYTES`. Left to the system allocator, a large
/// function's code and its data land in regions gigabytes apart, beyond any
/// pc-relative reach. The reservation is address space only; memory is
/// committed as the module writes it.
pub(crate) fn jit_builder() -> JITBuilder {
    let mut builder = JITBuilder::with_isa(
        host_isa_for(CodeHome::ThisProcess),
        cranelift_module::default_libcall_names(),
    );
    let arena = ArenaMemoryProvider::new_with_size(JIT_ARENA_BYTES).expect("reserve the JIT module's address space");
    builder.memory_provider(Box::new(arena));
    builder
}

/// The reference a function calls the import `id` through. Where the module's
/// code is linked together with its imports, the reference is near
/// (colocated) and the call is a direct branch. Only calls take this
/// reference: a near address is pc-relative and cannot name a function in a
/// shared library, so taking an import's address declares it afresh.
pub(crate) fn import_call_ref<M: Module>(module: &mut M, id: FuncId, func: &mut ir::Function) -> ir::FuncRef {
    let near = module.isa().flags().use_colocated_libcalls();
    let callee = module.declare_func_in_func(id, func);
    func.dfg.ext_funcs[callee].colocated = near;
    callee
}

/// Declare `id` in the current function and return its address as an i64.
/// Collapses the ubiquitous `declare_func_in_func` + `func_addr` pair.
pub(crate) fn fn_addr<M: Module>(jmod: &mut M, id: FuncId, b: &mut FunctionBuilder<'_>) -> ir::Value {
    let fref = jmod.declare_func_in_func(id, b.func);
    b.ins().func_addr(types::I64, fref)
}

/// Emit a single Cranelift function: make_context → set sig → build body →
/// finalize → define_function → clear_context. Eliminates the boilerplate
/// repeated for every runtime shim (fz_main_entry, fz_spawn_entry, etc.).
pub(crate) fn emit_fn_body<M: Module>(
    module: &mut M,
    fbctx: &mut FunctionBuilderContext,
    sig: Signature,
    func_id: FuncId,
    body: impl FnOnce(&mut M, &mut FunctionBuilder<'_>),
) -> Result<(), Box<ModuleError>> {
    let mut ctx = module.make_context();
    ctx.func.signature = sig;
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, fbctx);
        body(module, &mut b);
        b.finalize(module.target_config());
    }
    module.define_function(func_id, &mut ctx).map_err(Box::new)?;
    module.clear_context(&mut ctx);
    Ok(())
}

/// Pack a Span into a Cranelift SourceLoc (u32): 8 bits source_version + 24
/// bits start offset. Dummy spans become SourceLoc::default() so they
/// don't generate noise in the dump.
pub(crate) fn span_to_srcloc(s: Span) -> SourceLoc {
    if s.is_dummy() {
        return SourceLoc::default();
    }
    let source_version = (s.source_version.as_u32() & 0xFF) << 24;
    let offset = s.start & 0x00FF_FFFF;
    SourceLoc::new(source_version | offset)
}

pub(crate) fn cached_iconst(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, val: i64) -> ir::Value {
    if let Some(blk) = b.current_block() {
        if let Some(&v) = cache.const_cache.get(&(blk, val)) {
            return v;
        }
        let v = b.ins().iconst(types::I64, val);
        cache.const_cache.insert((blk, val), v);
        return v;
    }
    b.ins().iconst(types::I64, val)
}

/// The ref word of the atom or pid whose payload is `raw`: the payload sits in
/// the address field under the kind's tag. It names no object, so no arch
/// clears an address first.
pub(crate) fn immediate_ref_word(b: &mut FunctionBuilder<'_>, raw: ir::Value, kind: ValueKind) -> ir::Value {
    debug_assert!(kind.is_immediate());
    let tag_word = (u64::from(kind.tag()) << AnyValueRefPacking::current().tag_shift()) as i64;
    b.ins().bor_imm_u(raw, tag_word)
}

/// The kind of a ref word, in the low bits of an `I64`: the kind field with
/// the literal bit dropped. The single reading of a word's kind.
pub(crate) fn kind_field(b: &mut FunctionBuilder<'_>, ref_word: ir::Value) -> ir::Value {
    let packing = AnyValueRefPacking::current();
    let without_literal = b.ins().band_imm_u(ref_word, !packing.literal_bit() as i64);
    b.ins().ushr_imm_u(without_literal, packing.tag_shift() as i64)
}

/// The address field of a ref word: the object it names, or the payload of an
/// atom or pid. Kind and literal bit are dropped. The single reading of a
/// word's address.
pub(crate) fn address_field(b: &mut FunctionBuilder<'_>, ref_word: ir::Value) -> ir::Value {
    b.ins()
        .band_imm_u(ref_word, AnyValueRefPacking::current().address_mask() as i64)
}

/// The address field of a ref word together with its literal bit: the stored
/// form of a reference that names an object.
pub(crate) fn payload_field(b: &mut FunctionBuilder<'_>, ref_word: ir::Value) -> ir::Value {
    b.ins()
        .band_imm_u(ref_word, AnyValueRefPacking::current().payload_mask() as i64)
}

/// A map key test whose key is one word of a kind known when compiling. The
/// flat map is searched where the test stands; `slow` is entered for a map in
/// any other layout and is the caller's to fill with the runtime's lookup.
pub(crate) struct FlatMapScan {
    slow: ir::Block,
    done: ir::Block,
    found: ir::Value,
}

impl FlatMapScan {
    /// Search the flat map `map_ref` names for the key `key_word` of
    /// `key_kind`. The builder is left in the slow block.
    pub(crate) fn emit(
        b: &mut FunctionBuilder<'_>,
        map_ref: ir::Value,
        key_word: ir::Value,
        key_kind: ValueKind,
    ) -> Self {
        let flags = MemFlagsData::trusted();
        let [
            header_blk,
            scan_blk,
            head_blk,
            body_blk,
            kind_blk,
            next_blk,
            hit_blk,
            miss_blk,
        ] = std::array::from_fn(|_| b.create_block());
        let slow = b.create_block();
        let done = b.create_block();
        let found = b.append_block_param(done, types::I64);
        let index = b.append_block_param(head_blk, types::I64);

        let kind = kind_field(b, map_ref);
        let is_map = b.ins().icmp_imm_s(IntCC::Equal, kind, ValueKind::MAP.tag() as i64);
        b.ins().brif(is_map, header_blk, &[], slow, &[]);

        b.switch_to_block(header_blk);
        b.seal_block(header_blk);
        let map = address_field(b, map_ref);
        let header = b.ins().load(types::I64, flags, map, 0);
        let not_flat = b.ins().band_imm_u(header, MAP_NOT_FLAT_MASK as i64);
        b.ins().brif(not_flat, slow, &[], scan_blk, &[]);

        b.switch_to_block(scan_blk);
        b.seal_block(scan_blk);
        let count = b.ins().ushr_imm_u(header, MAP_FLAT_COUNT_SHIFT);
        let kinds = b.ins().iadd_imm_s(map, MAP_KIND_BYTES_OFFSET);
        let rounded = b.ins().iadd_imm_s(count, 7);
        let kind_bytes = b.ins().band_imm_s(rounded, -8);
        let keys = b.ins().iadd(kinds, kind_bytes);
        let zero = b.ins().iconst(types::I64, 0);
        b.ins().jump(head_blk, &[BlockArg::Value(zero)]);

        b.switch_to_block(head_blk);
        let in_map = b.ins().icmp(IntCC::UnsignedLessThan, index, count);
        b.ins().brif(in_map, body_blk, &[], miss_blk, &[]);

        b.switch_to_block(body_blk);
        b.seal_block(body_blk);
        let offset = b.ins().ishl_imm_u(index, 3);
        let key_slot = b.ins().iadd(keys, offset);
        let stored = b.ins().load(types::I64, flags, key_slot, 0);
        let same_word = b.ins().icmp(IntCC::Equal, stored, key_word);
        b.ins().brif(same_word, kind_blk, &[], next_blk, &[]);

        b.switch_to_block(kind_blk);
        b.seal_block(kind_blk);
        let kind_slot = b.ins().iadd(kinds, index);
        let kind_byte = b.ins().uload8(types::I64, flags, kind_slot, 0);
        let stored_kind = b.ins().ushr_imm_u(kind_byte, 4);
        let same_kind = b.ins().icmp_imm_s(IntCC::Equal, stored_kind, key_kind.tag() as i64);
        b.ins().brif(same_kind, hit_blk, &[], next_blk, &[]);

        b.switch_to_block(next_blk);
        b.seal_block(next_blk);
        let following = b.ins().iadd_imm_s(index, 1);
        b.ins().jump(head_blk, &[BlockArg::Value(following)]);
        b.seal_block(head_blk);

        b.switch_to_block(hit_blk);
        b.seal_block(hit_blk);
        let key_bytes = b.ins().ishl_imm_u(count, 3);
        let values = b.ins().iadd(keys, key_bytes);
        let found_at = b.ins().iadd(values, offset);
        let value_word = b.ins().load(types::I64, flags, found_at, 0);
        let value_kind = b.ins().band_imm_u(kind_byte, 0xF);
        let value_ref = stored_ref_word(b, found_at, value_word, value_kind);
        b.ins().jump(done, &[BlockArg::Value(value_ref)]);

        b.switch_to_block(miss_blk);
        b.seal_block(miss_blk);
        let packing = AnyValueRefPacking::current();
        let null = b.ins().iconst(
            types::I64,
            (u64::from(ValueKind::NULL.tag()) << packing.tag_shift()) as i64,
        );
        b.ins().jump(done, &[BlockArg::Value(null)]);

        b.switch_to_block(slow);
        b.seal_block(slow);
        Self { slow, done, found }
    }

    /// Close the slow block with the runtime's answer and continue after the
    /// test with the value's ref word, or the null ref for an absent key.
    pub(crate) fn finish(self, b: &mut FunctionBuilder<'_>, slow_answer: ir::Value) -> ir::Value {
        debug_assert_eq!(b.current_block(), Some(self.slow));
        b.ins().jump(self.done, &[BlockArg::Value(slow_answer)]);
        b.switch_to_block(self.done);
        b.seal_block(self.done);
        self.found
    }
}

/// The ref word of the value stored at `slot` as `word` with kind `kind`: an
/// integer, a float or a reference is named by its slot, everything else by
/// its word. This is `any_value_ref_from_storage` for a kind read at run time.
fn stored_ref_word(b: &mut FunctionBuilder<'_>, slot: ir::Value, word: ir::Value, kind: ir::Value) -> ir::Value {
    let packing = AnyValueRefPacking::current();
    let named_by_slot = [ValueKind::INT, ValueKind::FLOAT, ValueKind::REF]
        .map(|boxed| b.ins().icmp_imm_s(IntCC::Equal, kind, boxed.tag() as i64))
        .into_iter()
        .reduce(|either, is_kind| b.ins().bor(either, is_kind))
        .expect("three kinds");
    let payload = b.ins().select(named_by_slot, slot, word);
    let payload = b.ins().band_imm_u(payload, packing.payload_mask() as i64);
    let tag = b.ins().ishl_imm_u(kind, packing.tag_shift() as i64);
    b.ins().bor(payload, tag)
}

/// Convert an i8 Cranelift bool to the reserved true/false atom bit patterns.
pub(crate) fn bool_to_fz(b: &mut FunctionBuilder<'_>, cache: &mut CodegenCache, v: ir::Value) -> ir::Value {
    let true_v = cached_iconst(b, cache, TRUE_BITS);
    let false_v = cached_iconst(b, cache, FALSE_BITS);
    b.ins().select(v, true_v, false_v)
}

#[cfg(test)]
#[path = "clif_test.rs"]
mod clif_test;
