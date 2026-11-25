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
    AnyValueRefPacking, MAP_CHILD_MAP_SHIFT, MAP_COLLISION_FLAG, MAP_DATA_MAP_SHIFT, MAP_FLAT_COUNT_SHIFT,
    MAP_KIND_BYTES_OFFSET, MAP_NOT_FLAT_MASK, MAP_TRIE_FLAG, MAP_TRIE_SLOT_BITS, ValueKind,
};
use fz_runtime::process_abi::PROCESS_ATOM_KEY_HASHES_OFFSET;
use fz_runtime::term_hash::{FINALIZE_MULTIPLIERS, FINALIZE_SHIFT, SALT_INT};
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

/// A map key test whose key is one word of a kind known when compiling, made
/// where the test stands: a flat map is scanned for the key's word and a trie
/// is walked by the key's hash. A slow block is entered for a value that is
/// not a published map and for a walk that reaches a collision node. It is the
/// caller's to fill with the runtime's lookup, in as many blocks as the lookup
/// needs, and to close with `finish`.
pub(crate) struct WordKeyFind {
    done: ir::Block,
    found: ir::Value,
}

/// Where a key was found: the node's keys and its entry count, the entry's
/// index, and its kind byte. The value sits `count` words past the key.
const HIT_PARAMS: usize = 4;

impl WordKeyFind {
    /// Find the key `key_word` of `key_kind` in the map `map_ref` names. The
    /// builder is left in the slow block.
    pub(crate) fn emit(
        b: &mut FunctionBuilder<'_>,
        process: ir::Value,
        map_ref: ir::Value,
        key_word: ir::Value,
        key_kind: ValueKind,
    ) -> Self {
        let flags = MemFlagsData::trusted();
        let [header_blk, scan_blk, trie_blk, hit, miss] = std::array::from_fn(|_| b.create_block());
        let slow = b.create_block();
        let done = b.create_block();
        let found = b.append_block_param(done, types::I64);
        for _ in 0..HIT_PARAMS {
            b.append_block_param(hit, types::I64);
        }
        let key = SearchedKey {
            word: key_word,
            kind: key_kind,
            hit,
            miss,
        };

        let kind = kind_field(b, map_ref);
        let is_map = b.ins().icmp_imm_s(IntCC::Equal, kind, ValueKind::MAP.tag() as i64);
        b.ins().brif(is_map, header_blk, &[], slow, &[]);

        b.switch_to_block(header_blk);
        b.seal_block(header_blk);
        let map = address_field(b, map_ref);
        let header = b.ins().load(types::I64, flags, map, 0);
        let not_flat = b.ins().band_imm_u(header, MAP_NOT_FLAT_MASK as i64);
        b.ins().brif(not_flat, trie_blk, &[], scan_blk, &[]);

        b.switch_to_block(scan_blk);
        b.seal_block(scan_blk);
        key.scan_flat(b, map, header);

        b.switch_to_block(trie_blk);
        b.seal_block(trie_blk);
        key.walk_trie(b, process, map, header, slow);

        b.switch_to_block(hit);
        b.seal_block(hit);
        let &[keys, count, index, kind_byte] = b.block_params(hit) else {
            unreachable!("a hit has {HIT_PARAMS} params")
        };
        let values = word_at(b, keys, count);
        let found_at = word_at(b, values, index);
        let value_word = b.ins().load(types::I64, flags, found_at, 0);
        let value_kind = b.ins().band_imm_u(kind_byte, 0xF);
        let value_ref = stored_ref_word(b, found_at, value_word, value_kind);
        b.ins().jump(done, &[BlockArg::Value(value_ref)]);

        b.switch_to_block(miss);
        b.seal_block(miss);
        let packing = AnyValueRefPacking::current();
        let null = b.ins().iconst(
            types::I64,
            (u64::from(ValueKind::NULL.tag()) << packing.tag_shift()) as i64,
        );
        b.ins().jump(done, &[BlockArg::Value(null)]);

        b.switch_to_block(slow);
        b.seal_block(slow);
        Self { done, found }
    }

    /// Close the slow block with the runtime's answer and continue after the
    /// test with the value's ref word, or the null ref for an absent key.
    pub(crate) fn finish(self, b: &mut FunctionBuilder<'_>, slow_answer: ir::Value) -> ir::Value {
        b.ins().jump(self.done, &[BlockArg::Value(slow_answer)]);
        b.switch_to_block(self.done);
        b.seal_block(self.done);
        self.found
    }
}

/// The one-word key a `WordKeyFind` searches for, and the blocks a search
/// ends in.
struct SearchedKey {
    word: ir::Value,
    kind: ValueKind,
    hit: ir::Block,
    miss: ir::Block,
}

impl SearchedKey {
    /// Scan the flat map at `map`, whose first word is `header`, entry by
    /// entry for the key's word, then its kind.
    fn scan_flat(&self, b: &mut FunctionBuilder<'_>, map: ir::Value, header: ir::Value) {
        let flags = MemFlagsData::trusted();
        let [head_blk, body_blk, kind_blk, next_blk] = std::array::from_fn(|_| b.create_block());
        let index = b.append_block_param(head_blk, types::I64);
        let count = b.ins().ushr_imm_u(header, MAP_FLAT_COUNT_SHIFT);
        let (kinds, keys) = entry_columns(b, map, count);
        let zero = b.ins().iconst(types::I64, 0);
        b.ins().jump(head_blk, &[BlockArg::Value(zero)]);

        b.switch_to_block(head_blk);
        let in_map = b.ins().icmp(IntCC::UnsignedLessThan, index, count);
        b.ins().brif(in_map, body_blk, &[], self.miss, &[]);

        b.switch_to_block(body_blk);
        b.seal_block(body_blk);
        let key_slot = word_at(b, keys, index);
        let stored = b.ins().load(types::I64, flags, key_slot, 0);
        let same_word = b.ins().icmp(IntCC::Equal, stored, self.word);
        b.ins().brif(same_word, kind_blk, &[], next_blk, &[]);

        b.switch_to_block(kind_blk);
        b.seal_block(kind_blk);
        self.branch_on_kind(b, kinds, keys, count, index, next_blk);

        b.switch_to_block(next_blk);
        b.seal_block(next_blk);
        let following = b.ins().iadd_imm_s(index, 1);
        b.ins().jump(head_blk, &[BlockArg::Value(following)]);
        b.seal_block(head_blk);
    }

    /// Walk the trie whose root is at `map`, its first word `header`, by the
    /// key's hash, four bits a level, the top bits first. Slot `s` of a node
    /// holds an entry when bit `s` of its data map is set and a child when bit
    /// `s` of its child map is; entries and children are stored in the order
    /// of their bits, so where one sits is the count of set bits below it.
    fn walk_trie(
        &self,
        b: &mut FunctionBuilder<'_>,
        process: ir::Value,
        map: ir::Value,
        header: ir::Value,
        slow: ir::Block,
    ) {
        let flags = MemFlagsData::trusted();
        let [hash_blk, walk_blk, entry_blk, kind_blk, child_test_blk, child_blk] =
            std::array::from_fn(|_| b.create_block());
        let shape = b
            .ins()
            .band_imm_u(header, (MAP_NOT_FLAT_MASK | MAP_COLLISION_FLAG) as i64);
        let is_trie_node = b.ins().icmp_imm_u(IntCC::Equal, shape, MAP_TRIE_FLAG as i64);
        b.ins().brif(is_trie_node, hash_blk, &[], slow, &[]);

        b.switch_to_block(hash_blk);
        b.seal_block(hash_blk);
        let hash = self.hash(b, process);
        let [node, node_header, rest] = [(); 3].map(|_| b.append_block_param(walk_blk, types::I64));
        b.ins().jump(walk_blk, &[map, header, hash].map(BlockArg::Value));

        b.switch_to_block(walk_blk);
        let slot = b.ins().ushr_imm_u(rest, (u64::BITS - MAP_TRIE_SLOT_BITS) as i64);
        let below = b.ins().ishl_imm_u(rest, MAP_TRIE_SLOT_BITS as i64);
        let data_map_on_top = b
            .ins()
            .ishl_imm_u(node_header, (u64::BITS - MAP_CHILD_MAP_SHIFT) as i64);
        let entries = b.ins().popcnt(data_map_on_top);
        let (kinds, keys) = entry_columns(b, node, entries);
        let data_bit_at = b.ins().iadd_imm_s(slot, MAP_DATA_MAP_SHIFT as i64);
        let has_entry = header_bit(b, node_header, data_bit_at);
        b.ins().brif(has_entry, entry_blk, &[], child_test_blk, &[]);

        b.switch_to_block(entry_blk);
        b.seal_block(entry_blk);
        let index = set_bits_below(b, node_header, data_bit_at);
        let key_slot = word_at(b, keys, index);
        let stored = b.ins().load(types::I64, flags, key_slot, 0);
        let same_word = b.ins().icmp(IntCC::Equal, stored, self.word);
        b.ins().brif(same_word, kind_blk, &[], self.miss, &[]);

        b.switch_to_block(kind_blk);
        b.seal_block(kind_blk);
        self.branch_on_kind(b, kinds, keys, entries, index, self.miss);

        b.switch_to_block(child_test_blk);
        b.seal_block(child_test_blk);
        let child_bit_at = b.ins().iadd_imm_s(slot, MAP_CHILD_MAP_SHIFT as i64);
        let has_child = header_bit(b, node_header, child_bit_at);
        b.ins().brif(has_child, child_blk, &[], self.miss, &[]);

        b.switch_to_block(child_blk);
        b.seal_block(child_blk);
        // The count below the child bit takes in every data bit too: the
        // child's index plus the node's entries, its distance from the values.
        let past_values = set_bits_below(b, node_header, child_bit_at);
        let values = word_at(b, keys, entries);
        let child_word = word_at(b, values, past_values);
        let child = b.ins().load(types::I64, flags, child_word, 0);
        let child_header = b.ins().load(types::I64, flags, child, 0);
        let collision = b.ins().band_imm_u(child_header, MAP_COLLISION_FLAG as i64);
        b.ins().brif(
            collision,
            slow,
            &[],
            walk_blk,
            &[child, child_header, below].map(BlockArg::Value),
        );
        b.seal_block(walk_blk);
    }

    /// Compare the kind of entry `index` with the key's, going on to the hit
    /// or to `otherwise`.
    fn branch_on_kind(
        &self,
        b: &mut FunctionBuilder<'_>,
        kinds: ir::Value,
        keys: ir::Value,
        count: ir::Value,
        index: ir::Value,
        otherwise: ir::Block,
    ) {
        let kind_slot = b.ins().iadd(kinds, index);
        let kind_byte = b.ins().uload8(types::I64, MemFlagsData::trusted(), kind_slot, 0);
        let stored_kind = b.ins().ushr_imm_u(kind_byte, 4);
        let same_kind = b.ins().icmp_imm_s(IntCC::Equal, stored_kind, self.kind.tag() as i64);
        let at = [keys, count, index, kind_byte].map(BlockArg::Value);
        b.ins().brif(same_kind, self.hit, &at, otherwise, &[]);
    }

    /// The key's hash, as the runtime's `TermHasher` gives it: an atom's is
    /// read from the key hashes its table keeps, an integer's is its word
    /// mixed by the finalizer.
    fn hash(&self, b: &mut FunctionBuilder<'_>, process: ir::Value) -> ir::Value {
        let flags = MemFlagsData::trusted();
        match self.kind {
            ValueKind::ATOM => {
                let at = b.ins().load(types::I64, flags, process, PROCESS_ATOM_KEY_HASHES_OFFSET);
                let hashes = b.ins().load(types::I64, flags, at, 0);
                let slot = word_at(b, hashes, self.word);
                b.ins().load(types::I64, flags, slot, 0)
            }
            ValueKind::INT => {
                let mut x = b.ins().bxor_imm_u(self.word, SALT_INT as i64);
                for multiplier in FINALIZE_MULTIPLIERS {
                    let high = b.ins().ushr_imm_u(x, FINALIZE_SHIFT as i64);
                    let mixed = b.ins().bxor(x, high);
                    x = b.ins().imul_imm_u(mixed, multiplier as i64);
                }
                let high = b.ins().ushr_imm_u(x, FINALIZE_SHIFT as i64);
                b.ins().bxor(x, high)
            }
            kind => unreachable!("a one-word key is an atom or an integer, not {kind:?}"),
        }
    }
}

/// Where a map node's kind bytes and key words begin, given its entry count.
fn entry_columns(b: &mut FunctionBuilder<'_>, node: ir::Value, count: ir::Value) -> (ir::Value, ir::Value) {
    let kinds = b.ins().iadd_imm_s(node, MAP_KIND_BYTES_OFFSET);
    let rounded = b.ins().iadd_imm_s(count, 7);
    let kind_bytes = b.ins().band_imm_s(rounded, -8);
    (kinds, b.ins().iadd(kinds, kind_bytes))
}

/// The address `index` words past `base`.
fn word_at(b: &mut FunctionBuilder<'_>, base: ir::Value, index: ir::Value) -> ir::Value {
    let bytes = b.ins().ishl_imm_u(index, 3);
    b.ins().iadd(base, bytes)
}

/// Bit `at` of a trie node's header.
fn header_bit(b: &mut FunctionBuilder<'_>, header: ir::Value, at: ir::Value) -> ir::Value {
    let shifted = b.ins().ushr(header, at);
    b.ins().band_imm_u(shifted, 1)
}

/// The set bits of a trie node's header below bit `at`, down to the data map:
/// a left shift by `64 - at` drops bit `at` and every bit above it, and the
/// bits below the data map are clear. A shift amount is taken modulo 64.
fn set_bits_below(b: &mut FunctionBuilder<'_>, header: ir::Value, at: ir::Value) -> ir::Value {
    let amount = b.ins().ineg(at);
    let below = b.ins().ishl(header, amount);
    b.ins().popcnt(below)
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

/// An `I64` 0 or 1: whether the kind value `kind` is one `member` admits.
/// One bit of a constant mask is read by shifting it down by the kind.
pub(crate) fn kind_is_one_of(
    b: &mut FunctionBuilder<'_>,
    kind: ir::Value,
    member: impl Fn(ValueKind) -> bool,
) -> ir::Value {
    let mask: u64 = (0..=u8::MAX)
        .filter_map(ValueKind::new)
        .filter(|kind| member(*kind))
        .fold(0, |mask, kind| mask | 1 << kind.tag());
    let mask = b.ins().iconst(types::I64, mask as i64);
    let bit = b.ins().ushr(mask, kind);
    b.ins().band_imm_u(bit, 1)
}
