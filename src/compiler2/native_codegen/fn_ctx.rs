//! Per-function semantic codegen context.
//!
//! Cranelift's `FunctionBuilder` owns the body currently being emitted.
//! Function-local imports, however, need both the module and the function
//! body. `CodegenFn` is the fz-owned boundary for "lower one fz function":
//! semantic lowering code should ask this context for operations, while
//! runtime helper calls remain an implementation detail behind those methods.

use super::recipe::{emit_box, emit_object};
use super::type_pred::ShareClass;
use super::*;
use crate::fast_hash::HashMap;
use crate::fz_ir::Var;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataId, FuncId, Module};
use fz_runtime::any_value::{
    AnyValueRef, AnyValueRefPacking, BINARY_SHARED_MASK, CLOSURE_CAPTURES_OFFSET, CLOSURE_CODE_OFFSET,
    CLOSURE_FLAGS_CAPTURED_MASK, CLOSURE_LAYOUT_FLAGS_SHIFT, FALSE_ATOM_ID, LIST_CONS_LINK_OFFSET,
    LIST_LINK_ALIAS_MASK, NIL_ATOM_ID, STRUCT_HEADER_SCHEMA_SHIFT, STRUCT_HEADER_SHARED_MASK, SlotLayout,
    TaggedRefArch, ValueKind,
};
use fz_runtime::ir_runtime::{
    fz_closure_halt_kind_ref, fz_closure_set_capture_atom, fz_closure_set_capture_f64, fz_closure_set_capture_i64,
    fz_closure_set_capture_ref, fz_halt_implicit_atom, fz_halt_implicit_f64, fz_halt_implicit_i64,
    fz_halt_implicit_ref, fz_list_head_float_ref, fz_list_head_int_ref, fz_list_head_ref, fz_list_tail_ref,
    fz_number_ref_float_bits, fz_share_list_spine, fz_struct_copy, fz_struct_store_ref, fz_truthy_ref, fz_type_of,
    fz_unbox_atom, fz_unbox_float, fz_unbox_int,
};
use fz_runtime::process_abi::{
    PROCESS_BINARIES_SHARED_OFFSET, PROCESS_STRUCT_RETENTION_ATTEMPTS_OFFSET, PROCESS_STRUCT_RETENTION_HITS_OFFSET,
};

/// A struct or tuple that is allocated and whose fields are being stored.
pub(crate) struct NewStruct {
    pub(crate) reference: ir::Value,
    address: ir::Value,
    layout: SlotLayout,
}

/// How many captures the frame being read holds. A frame stores its raw slots
/// first and one kind byte per capture after them, so the count places the
/// kind bytes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CaptureCount {
    /// The code is compiled for one frame shape, and this is its count.
    Compiled(usize),
    /// The code reads frames of any shape: the count is in each frame's header.
    InHeader,
}

/// Per-function semantic codegen machine: the function-local import table
/// plus the `FunctionBuilder`, module, and cache bound for the body
/// currently being emitted. Every runtime-BIF operation is an inherent
/// method over `runtime_call!`; semantic lowering code drives all emission
/// through this one type.
pub(crate) struct CodegenFn<'a, 'fb, M>
where
    M: Module,
{
    imports: HashMap<FuncId, ir::FuncRef>,
    /// Memoized current-`Process*` value per block: `get_pinned_reg` reads a
    /// register that is constant for the whole function invocation, so each
    /// block that calls a process-taking BIF reads it once and reuses it.
    /// Keyed by block (not function-wide) so the value always dominates its
    /// uses without a cross-block dominance argument.
    process_by_block: HashMap<ir::Block, ir::Value>,
    pub(super) b: &'a mut FunctionBuilder<'fb>,
    pub(super) jmod: &'a mut M,
    pub(super) cache: &'a mut CodegenCache,
    /// Where an allocation this function places registers its site.
    pub(super) scope: SiteScope<'a>,
}

impl<'a, 'fb, M: Module> CodegenFn<'a, 'fb, M> {
    pub(crate) fn new(
        b: &'a mut FunctionBuilder<'fb>,
        jmod: &'a mut M,
        cache: &'a mut CodegenCache,
        scope: SiteScope<'a>,
    ) -> Self {
        Self {
            imports: HashMap::default(),
            process_by_block: HashMap::default(),
            b,
            jmod,
            cache,
            scope,
        }
    }

    pub(crate) fn func_ref(&mut self, id: FuncId) -> ir::FuncRef {
        let Self { imports, jmod, b, .. } = self;
        *imports
            .entry(id)
            .or_insert_with(|| jmod.declare_func_in_func(id, b.func))
    }

    /// Declare `id` in the current function and return its address as an i64.
    /// Routes the import through `func_ref` so shim bodies dedup their
    /// function-local imports like every other call site.
    pub(crate) fn func_addr(&mut self, id: FuncId) -> ir::Value {
        let fref = self.func_ref(id);
        self.b.ins().func_addr(types::I64, fref)
    }

    /// The current task's `Process*` — the value the scheduler placed in the
    /// pinned register at entry. It is valid anywhere in compiled code (it
    /// survives runtime-helper calls), so it is the leading argument every
    /// process-taking BIF receives, in place of a thread-local lookup. See
    /// `runtime/src/exec_ctx.rs`.
    pub(crate) fn process_arg(&mut self) -> ir::Value {
        let blk = self.b.current_block().expect("process_arg requires a current block");
        if let Some(&v) = self.process_by_block.get(&blk) {
            return v;
        }
        let v = self.b.ins().get_pinned_reg(types::I64);
        self.process_by_block.insert(blk, v);
        v
    }

    pub(crate) fn ref_tag(&mut self, value_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_type_of, [value_ref])
    }

    pub(crate) fn truthy_ref(&mut self, value_ref: ir::Value) -> ir::Value {
        runtime_condition!(self, fz_truthy_ref, [value_ref])
    }

    /// Whether `value_ref` names an object in the struct layout of schema
    /// `schema_id`. A map of either layout has a first word to read, so the
    /// header is loaded before the kind is known and the two tests are one
    /// condition.
    pub(crate) fn has_struct_layout(&mut self, value_ref: ir::Value, schema_id: u32) -> ir::Value {
        let kind = kind_field(self.b, value_ref);
        let is_struct = self
            .b
            .ins()
            .icmp_imm_s(IntCC::Equal, kind, ValueKind::STRUCT.tag() as i64);
        let object = address_field(self.b, value_ref);
        let header = self.b.ins().load(types::I64, MemFlagsData::new(), object, 0);
        let schema = self.b.ins().ushr_imm_u(header, STRUCT_HEADER_SCHEMA_SHIFT);
        let is_schema = self.b.ins().icmp_imm_s(IntCC::Equal, schema, i64::from(schema_id));
        self.b.ins().band(is_struct, is_schema)
    }

    fn copy_struct(&mut self, base_ref: ir::Value, fields: usize) -> ir::Value {
        let count = self.b.ins().iconst(types::I32, fields as i64);
        let process = self.process_arg();
        runtime_call1!(self, fz_struct_copy, [process, base_ref, count])
    }

    /// `base_ref` when its header's shared bit is clear, counted as a
    /// retention hit; otherwise `fz_struct_copy`'s copy.
    fn rewrite_unshared_struct(&mut self, base_ref: ir::Value, fields: usize) -> ir::Value {
        let reuse_blk = self.b.create_block();
        let copy_blk = self.b.create_block();
        let done_blk = self.b.create_block();
        let target = self.b.append_block_param(done_blk, types::I64);
        let object = address_field(self.b, base_ref);
        let header = self.b.ins().load(types::I64, MemFlagsData::trusted(), object, 0);
        let shared = self.b.ins().band_imm_u(header, STRUCT_HEADER_SHARED_MASK as i64);
        self.b.ins().brif(shared, copy_blk, &[], reuse_blk, &[]);

        self.b.switch_to_block(reuse_blk);
        self.b.seal_block(reuse_blk);
        self.bump_process_counter(PROCESS_STRUCT_RETENTION_ATTEMPTS_OFFSET);
        self.bump_process_counter(PROCESS_STRUCT_RETENTION_HITS_OFFSET);
        self.b.ins().jump(done_blk, &[BlockArg::Value(base_ref)]);

        self.b.switch_to_block(copy_blk);
        self.b.seal_block(copy_blk);
        let copy = self.copy_struct(base_ref, fields);
        self.b.ins().jump(done_blk, &[BlockArg::Value(copy)]);

        self.b.switch_to_block(done_blk);
        self.b.seal_block(done_blk);
        target
    }

    pub(super) fn bump_process_counter(&mut self, offset: i32) {
        let one = self.b.ins().iconst(types::I64, 1);
        self.add_process_counter(offset, one);
    }

    fn add_process_counter(&mut self, offset: i32, amount: ir::Value) {
        let process = self.process_arg();
        let count = self.b.ins().load(types::I64, MemFlagsData::trusted(), process, offset);
        let added = self.b.ins().iadd(count, amount);
        self.b.ins().store(MemFlagsData::trusted(), added, process, offset);
    }

    /// Mark `value` shared: from here on it may have a second holder, so it is
    /// never written in place again. What the compiler knows of the value
    /// decides the code: nothing for a value that holds no mark, a test and a
    /// store for a struct, tuple or binary, a test of the first cell and a
    /// spine walk for a list, and a branch on the reference's kind for a
    /// value whose kind is known only when it runs. It is `Heap::share`,
    /// written in place.
    pub(crate) fn share(&mut self, value: CodegenValue) {
        match value {
            CodegenValue::AnyRef(reference) => self.share_any(reference),
            CodegenValue::Known { kind, .. } if !kind.is_scalar() => {
                let reference = self.value_as_any_ref(value);
                self.share_kind(reference, kind);
            }
            CodegenValue::Known { .. }
            | CodegenValue::RawInt(_)
            | CodegenValue::RawF64(_)
            | CodegenValue::RawAtom(_)
            | CodegenValue::Condition(_) => {}
        }
    }

    /// Share `value`, as its type's `class` says.
    pub(crate) fn share_as(&mut self, value: CodegenValue, class: ShareClass) {
        match (value, class) {
            (_, ShareClass::Markless) => {}
            (CodegenValue::AnyRef(reference), ShareClass::Kind(kind)) => self.share_kind(reference, kind),
            _ => self.share(value),
        }
    }

    /// Share a reference whose kind is read from the reference itself.
    fn share_any(&mut self, reference: ir::Value) {
        let done = self.b.create_block();
        let kind = kind_field(self.b, reference);
        for marked_kinds in [
            &[ValueKind::STRUCT][..],
            &[ValueKind::BITSTRING, ValueKind::BINVIEW],
            &[ValueKind::LIST],
        ] {
            let this_kind = self.b.create_block();
            let next = self.b.create_block();
            let is_kind = self.kind_in(kind, marked_kinds);
            self.b.ins().brif(is_kind, this_kind, &[], next, &[]);
            self.b.switch_to_block(this_kind);
            self.b.seal_block(this_kind);
            self.share_kind(reference, marked_kinds[0]);
            self.b.ins().jump(done, &[]);
            self.b.switch_to_block(next);
            self.b.seal_block(next);
        }
        self.b.ins().jump(done, &[]);
        self.b.switch_to_block(done);
        self.b.seal_block(done);
    }

    /// Whether `kind` is one of `kinds`.
    fn kind_in(&mut self, kind: ir::Value, kinds: &[ValueKind]) -> ir::Value {
        let (first, rest) = kinds.split_first().expect("a kind");
        let mut is = self.b.ins().icmp_imm_s(IntCC::Equal, kind, first.tag() as i64);
        for other in rest {
            let is_other = self.b.ins().icmp_imm_s(IntCC::Equal, kind, other.tag() as i64);
            is = self.b.ins().bor(is, is_other);
        }
        is
    }

    /// Share a reference of a kind known while compiling. A binary's kind
    /// may name either layout: both keep the mark in their first word.
    pub(crate) fn share_kind(&mut self, reference: ir::Value, kind: ValueKind) {
        match kind {
            ValueKind::STRUCT => self.mark_first_word(reference, STRUCT_HEADER_SHARED_MASK, None),
            ValueKind::BITSTRING | ValueKind::BINVIEW => {
                self.mark_first_word(reference, BINARY_SHARED_MASK, Some(PROCESS_BINARIES_SHARED_OFFSET))
            }
            ValueKind::LIST => self.share_list(reference),
            _ => {}
        }
    }

    /// Set `mask` in the first word of the object `reference` names unless it
    /// is set already; an object already shared may be read-only program
    /// data, so it is only read. A mark this sets adds one to the process
    /// counter at `counted`.
    fn mark_first_word(&mut self, reference: ir::Value, mask: u64, counted: Option<i32>) {
        let mark = self.b.create_block();
        let done = self.b.create_block();
        let object = address_field(self.b, reference);
        let word = self.b.ins().load(types::I64, MemFlagsData::trusted(), object, 0);
        let shared = self.b.ins().band_imm_u(word, mask as i64);
        self.b.ins().brif(shared, done, &[], mark, &[]);

        self.b.switch_to_block(mark);
        self.b.seal_block(mark);
        let marked = self.b.ins().bor_imm_u(word, mask as i64);
        self.b.ins().store(MemFlagsData::trusted(), marked, object, 0);
        if let Some(offset) = counted {
            self.bump_process_counter(offset);
        }
        self.b.ins().jump(done, &[]);

        self.b.switch_to_block(done);
        self.b.seal_block(done);
    }

    /// Share a list: nothing for the empty list or for one whose first cell
    /// is marked, since a marked cell has a marked tail; otherwise the
    /// runtime walks the spine.
    fn share_list(&mut self, reference: ir::Value) {
        let check = self.b.create_block();
        let walk = self.b.create_block();
        let done = self.b.create_block();
        let cell = address_field(self.b, reference);
        self.b.ins().brif(cell, check, &[], done, &[]);

        self.b.switch_to_block(check);
        self.b.seal_block(check);
        let link = self
            .b
            .ins()
            .load(types::I64, MemFlagsData::trusted(), cell, LIST_CONS_LINK_OFFSET as i32);
        let shared = self.b.ins().band_imm_u(link, LIST_LINK_ALIAS_MASK as i64);
        self.b.ins().brif(shared, done, &[], walk, &[]);

        self.b.switch_to_block(walk);
        self.b.seal_block(walk);
        runtime_call!(self, fz_share_list_spine, [cell]);
        self.b.ins().jump(done, &[]);

        self.b.switch_to_block(done);
        self.b.seal_block(done);
    }

    /// The raw word in `slot` of the struct or tuple `object_ref` names,
    /// loaded in place. The caller's types say what kind of value the slot
    /// holds, so its kind byte is not read. The load may trap: a bad
    /// reference here is a compiler fault that must not pass silently.
    pub(crate) fn load_slot(&mut self, object_ref: ir::Value, slot: u32, ty: ir::Type) -> ir::Value {
        let object = address_field(self.b, object_ref);
        let offset = SlotLayout::slot_offset(slot as usize) as i32;
        self.b.ins().load(ty, MemFlagsData::new(), object, offset)
    }

    /// Place a struct or tuple of `fields` values and write its header.
    /// `store_field` must follow for every field before any other code runs,
    /// since nothing may read the object until then.
    pub(crate) fn alloc_struct(&mut self, schema_id: u32, fields: usize) -> NewStruct {
        let layout = SlotLayout::of(fields);
        let schema = self.b.ins().iconst(types::I32, schema_id as i64);
        let size = self.b.ins().iconst(types::I32, layout.size() as i64);
        let process = self.process_arg();
        let placed = emit_object(self, "Heap::alloc_struct_unwritten", &[process, schema, size]);
        NewStruct {
            reference: placed.reference,
            address: placed.address,
            layout,
        }
    }

    /// The struct an update of the struct `base_ref` names, which has
    /// `fields` fields, stores into: `base_ref` itself when `rewrite` permits
    /// and its header says it is not shared, otherwise an unpublished copy.
    /// The rewrite makes no runtime call. `store_field` may follow for the
    /// fields the update replaces, before any other code runs.
    pub(crate) fn reuse_or_copy_struct(
        &mut self,
        base_ref: ir::Value,
        fields: usize,
        rewrite: crate::fz_ir::RewritePermission,
    ) -> NewStruct {
        let reference = match rewrite {
            crate::fz_ir::RewritePermission::RetainOnly => self.copy_struct(base_ref, fields),
            crate::fz_ir::RewritePermission::Rewrite => self.rewrite_unshared_struct(base_ref, fields),
        };
        NewStruct {
            reference,
            address: address_field(self.b, reference),
            layout: SlotLayout::of(fields),
        }
    }

    /// Store `value` as field `index` of `object`. A value whose stored form
    /// the compiler can name is two stores in place: its raw word and its
    /// kind byte. Any other reference may be a list, which a struct shares,
    /// or a boxed scalar, so the runtime reads it and stores it.
    /// `addressed` says the value's type makes it a tuple, a map or a binary,
    /// and how a holder shares it.
    pub(crate) fn store_field(
        &mut self,
        object: &NewStruct,
        index: usize,
        value: CodegenValue,
        addressed: Option<ShareClass>,
    ) {
        let slot_offset = SlotLayout::slot_offset(index) as i32;
        let kind_offset = object.layout.kind_offset(index) as i32;
        match self.stored_form(value, addressed) {
            Some((raw, kind)) => {
                self.b
                    .ins()
                    .store(MemFlagsData::trusted(), raw, object.address, slot_offset);
                self.b
                    .ins()
                    .store(MemFlagsData::trusted(), kind, object.address, kind_offset);
            }
            None => {
                let slot_offset = self.b.ins().iconst(types::I32, slot_offset as i64);
                let kind_offset = self.b.ins().iconst(types::I32, kind_offset as i64);
                let process = self.process_arg();
                let [value_word, value_kind] = super::list_cell::stored_parts_of_ref(self.b, value.value());
                runtime_call!(
                    self,
                    fz_struct_store_ref,
                    [
                        process,
                        object.reference,
                        slot_offset,
                        kind_offset,
                        value_word,
                        value_kind
                    ]
                );
            }
        }
    }

    /// The raw word and the kind byte `value` is stored as, when both follow
    /// from what the compiler holds without reading the value.
    fn stored_form(&mut self, value: CodegenValue, addressed: Option<ShareClass>) -> Option<(ir::Value, ir::Value)> {
        let (raw, kind) = match value {
            CodegenValue::RawInt(raw) => (raw, ValueKind::INT),
            CodegenValue::RawF64(raw) => (raw, ValueKind::FLOAT),
            CodegenValue::RawAtom(raw) => (raw, ValueKind::ATOM),
            CodegenValue::Condition(flag) => (bool_to_fz(self.b, self.cache, flag), ValueKind::ATOM),
            CodegenValue::Known { payload, kind } if kind.is_scalar() => (payload, kind),
            CodegenValue::Known { kind, .. } => (self.b.ins().iconst(types::I64, 0), kind),
            CodegenValue::AnyRef(reference) => {
                let share = addressed?;
                self.share_as(value, share);
                return Some(self.addressed_form(reference));
            }
        };
        Some((raw, self.b.ins().iconst(types::I8, kind.tag() as i64)))
    }

    /// The stored form of a reference that names an object by its address:
    /// the reference without its kind, and the kind the reference carries.
    fn addressed_form(&mut self, reference: ir::Value) -> (ir::Value, ir::Value) {
        let raw = payload_field(self.b, reference);
        let kind = kind_field(self.b, reference);
        (raw, self.b.ins().ireduce(types::I8, kind))
    }

    pub(crate) fn box_int_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let process = self.process_arg();
        emit_box(self, "fz_box_int_for_any", &[process, raw])
    }

    pub(crate) fn box_float_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let process = self.process_arg();
        emit_box(self, "fz_box_float_for_any", &[process, raw])
    }

    /// An atom ref is its id under the atom tag: one `or`, no call and no
    /// address to clear, on every arch.
    pub(crate) fn box_atom_for_any(&mut self, raw: ir::Value) -> ir::Value {
        immediate_ref_word(self.b, raw, ValueKind::ATOM)
    }

    pub(crate) fn unbox_int(&mut self, value_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_unbox_int, [value_ref])
    }

    pub(crate) fn unbox_float(&mut self, value_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_unbox_float, [value_ref])
    }

    pub(crate) fn unbox_atom(&mut self, value_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_unbox_atom, [value_ref])
    }

    pub(crate) fn halt_implicit(&mut self, repr: ArgRepr, value: ir::Value) {
        let process = self.process_arg();
        match repr {
            ArgRepr::RawInt => runtime_call!(self, fz_halt_implicit_i64, [process, value]),
            ArgRepr::RawF64 => runtime_call!(self, fz_halt_implicit_f64, [process, value]),
            ArgRepr::RawAtom => runtime_call!(self, fz_halt_implicit_atom, [process, value]),
            ArgRepr::ValueRef => runtime_call!(self, fz_halt_implicit_ref, [process, value]),
            ArgRepr::Condition => unreachable!("condition halt values must be materialized"),
        };
    }

    /// The tagged ref to a read-only object the program emitted, marked as a
    /// literal so the collector and deep copy leave it where it is.
    pub(crate) fn static_object_ref(&mut self, data_id: DataId, kind: ValueKind) -> ir::Value {
        let addr = data_addr(self.jmod, data_id, self.b);
        self.literal_ref_word_from_addr(addr, kind)
    }

    /// The tagged ref to the read-only object at `addr`, marked as a literal.
    pub(crate) fn literal_ref_word_from_addr(&mut self, addr: ir::Value, kind: ValueKind) -> ir::Value {
        let ref_word = self.heap_ref_word_from_addr(addr, kind);
        self.b
            .ins()
            .bor_imm_u(ref_word, AnyValueRefPacking::current().literal_bit() as i64)
    }

    /// The program's halt continuation for a return in `repr`'s lane.
    pub(crate) fn halt_cont_ref(&mut self, locals: &LocalBodies, repr: ArgRepr) -> ir::Value {
        self.static_object_ref(locals.halt_cont_data_id(repr), ValueKind::CLOSURE)
    }

    /// Place a closure and write its header and code address. The captures
    /// are stored next, before any other code runs.
    pub(crate) fn alloc_closure(
        &mut self,
        denotation: fz_runtime::any_value::ClosureDenotationId,
        arity: ir::Value,
        captured_count: ir::Value,
        halt_kind: ir::Value,
        code_addr: ir::Value,
    ) -> ir::Value {
        let denotation = self.b.ins().iconst(types::I32, denotation.as_u32() as i64);
        let process = self.process_arg();
        let args = [process, denotation, arity, captured_count, halt_kind, code_addr];
        emit_object(self, "Heap::alloc_closure", &args).reference
    }

    pub(crate) fn list_head(&mut self, list_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_list_head_ref, [list_ref])
    }

    pub(crate) fn list_head_int(&mut self, list_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_list_head_int_ref, [list_ref])
    }

    pub(crate) fn list_head_float(&mut self, list_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_list_head_float_ref, [list_ref])
    }

    pub(crate) fn list_tail(&mut self, list_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_list_tail_ref, [list_ref])
    }

    /// The address of capture `index`'s raw slot.
    fn closure_capture_slot(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let address = address_field(self.b, closure_ref);
        let offset = self.b.ins().ishl_imm_u(index, 3);
        let slot = self.b.ins().iadd(address, offset);
        self.b.ins().iadd_imm_s(slot, CLOSURE_CAPTURES_OFFSET as i64)
    }

    pub(crate) fn closure_capture_i64(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let slot = self.closure_capture_slot(closure_ref, index);
        self.b.ins().load(types::I64, MemFlagsData::trusted(), slot, 0)
    }

    pub(crate) fn closure_capture_f64(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let slot = self.closure_capture_slot(closure_ref, index);
        self.b.ins().load(types::F64, MemFlagsData::trusted(), slot, 0)
    }

    pub(crate) fn closure_capture_atom(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        self.closure_capture_i64(closure_ref, index)
    }

    /// The address of the first kind byte, less `CLOSURE_CAPTURES_OFFSET`: the
    /// kind bytes follow the raw slots, one per capture.
    pub(crate) fn closure_kind_bytes(&mut self, address: ir::Value, count: CaptureCount) -> ir::Value {
        let offset = match count {
            CaptureCount::Compiled(count) => self.b.ins().iconst(types::I64, (count * 8) as i64),
            CaptureCount::InHeader => {
                let layout = self.b.ins().uload32(MemFlagsData::trusted(), address, 0);
                let flags_field = self.b.ins().ushr_imm_u(layout, CLOSURE_LAYOUT_FLAGS_SHIFT as i64);
                let count = self
                    .b
                    .ins()
                    .band_imm_u(flags_field, i64::from(CLOSURE_FLAGS_CAPTURED_MASK));
                self.b.ins().ishl_imm_u(count, 3)
            }
        };
        self.b.ins().iadd(address, offset)
    }

    /// A capture as a ref word: its kind byte over its raw slot. An int,
    /// float, pid or reference names the slot that holds its raw word; every
    /// other kind carries its raw word as the payload.
    pub(crate) fn closure_capture_ref(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        count: CaptureCount,
    ) -> ir::Value {
        let packing = AnyValueRefPacking::current();
        let flags = MemFlagsData::trusted();
        let address = address_field(self.b, closure_ref);
        let raw_slot = self.closure_capture_slot(closure_ref, index);
        let raw = self.b.ins().load(types::I64, flags, raw_slot, 0);
        let kinds = self.closure_kind_bytes(address, count);
        let kind_at = self.b.ins().iadd(kinds, index);
        let kind = self.b.ins().uload8(types::I64, flags, kind_at, CLOSURE_CAPTURES_OFFSET);
        let names_slot = self.kind_names_its_slot(kind);
        let payload = self.b.ins().select(names_slot, raw_slot, raw);
        let payload = self.b.ins().band_imm_u(payload, packing.payload_mask() as i64);
        let kind_bits = self.b.ins().ishl_imm_u(kind, i64::from(packing.tag_shift()));
        self.b.ins().bor(kind_bits, payload)
    }

    /// Whether a ref of this kind points at the slot that holds its raw word.
    pub(crate) fn kind_names_its_slot(&mut self, kind: ir::Value) -> ir::Value {
        let at_least_ref =
            self.b
                .ins()
                .icmp_imm_s(IntCC::UnsignedGreaterThanOrEqual, kind, i64::from(ValueKind::REF.tag()));
        let at_most_float =
            self.b
                .ins()
                .icmp_imm_s(IntCC::UnsignedLessThanOrEqual, kind, i64::from(ValueKind::FLOAT.tag()));
        self.b.ins().band(at_least_ref, at_most_float)
    }

    pub(crate) fn closure_code_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        let address = address_field(self.b, closure_ref);
        self.b
            .ins()
            .load(types::I64, MemFlagsData::trusted(), address, CLOSURE_CODE_OFFSET)
    }

    pub(crate) fn closure_halt_kind_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        runtime_call1!(self, fz_closure_halt_kind_ref, [closure_ref])
    }

    pub(crate) fn set_closure_capture_ref(
        &mut self,
        closure_ref: ir::Value,
        index: ir::Value,
        value_word: ir::Value,
        value_kind: ir::Value,
    ) {
        let process = self.process_arg();
        runtime_call!(
            self,
            fz_closure_set_capture_ref,
            [process, closure_ref, index, value_word, value_kind]
        );
    }

    pub(crate) fn set_closure_capture_i64(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let process = self.process_arg();
        runtime_call!(self, fz_closure_set_capture_i64, [process, closure_ref, index, value]);
    }

    pub(crate) fn set_closure_capture_f64(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let process = self.process_arg();
        runtime_call!(self, fz_closure_set_capture_f64, [process, closure_ref, index, value]);
    }

    pub(crate) fn set_closure_capture_atom(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let process = self.process_arg();
        runtime_call!(self, fz_closure_set_capture_atom, [process, closure_ref, index, value]);
    }

    // -- value classification reads (cache-free) --

    pub(crate) fn value_truthy(&mut self, value: CodegenValue) -> ir::Value {
        if let CodegenValue::AnyRef(value_ref) = value {
            return self.truthy_ref(value_ref);
        }
        let b = &mut *self.b;
        match value {
            CodegenValue::Condition(flag) => flag,
            CodegenValue::RawInt(_) | CodegenValue::RawF64(_) => b.ins().iconst(types::I8, 1),
            CodegenValue::RawAtom(payload) => {
                let is_false = b.ins().icmp_imm_s(IntCC::Equal, payload, FALSE_ATOM_ID as i64);
                let is_nil = b.ins().icmp_imm_s(IntCC::Equal, payload, NIL_ATOM_ID as i64);
                let falsey = b.ins().bor(is_false, is_nil);
                b.ins().bxor_imm_u(falsey, 1)
            }
            CodegenValue::Known {
                kind: ValueKind::NULL, ..
            } => b.ins().iconst(types::I8, 0),
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => {
                let is_false = b.ins().icmp_imm_s(IntCC::Equal, payload, FALSE_ATOM_ID as i64);
                let is_nil = b.ins().icmp_imm_s(IntCC::Equal, payload, NIL_ATOM_ID as i64);
                let falsey = b.ins().bor(is_false, is_nil);
                b.ins().bxor_imm_u(falsey, 1)
            }
            CodegenValue::Known { .. } => b.ins().iconst(types::I8, 1),
            CodegenValue::AnyRef(_) => unreachable!("handled above"),
        }
    }

    pub(crate) fn value_type_tag(&mut self, value: CodegenValue) -> ir::Value {
        if let CodegenValue::AnyRef(value_ref) = value {
            return self.ref_tag(value_ref);
        }
        let b = &mut *self.b;
        match value {
            CodegenValue::RawInt(_) => b.ins().iconst(types::I8, ValueKind::INT.tag() as i64),
            CodegenValue::RawF64(_) => b.ins().iconst(types::I8, ValueKind::FLOAT.tag() as i64),
            CodegenValue::RawAtom(_) => b.ins().iconst(types::I8, ValueKind::ATOM.tag() as i64),
            CodegenValue::Condition(_) => b.ins().iconst(types::I8, ValueKind::ATOM.tag() as i64),
            CodegenValue::Known { payload, kind } => known_kind_ref_tag(b, payload, kind),
            CodegenValue::AnyRef(_) => unreachable!("handled above"),
        }
    }

    pub(crate) fn value_is_tag(&mut self, value: CodegenValue, tag: ValueKind) -> ir::Value {
        let actual = self.value_type_tag(value);
        let b = &mut *self.b;
        b.ins().icmp_imm_s(IntCC::Equal, actual, tag.tag() as i64)
    }

    pub(crate) fn value_raw_int(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::RawInt(value) => value,
            CodegenValue::Known {
                payload,
                kind: ValueKind::INT,
            } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_int(value_ref),
            _ => panic!("CodegenValue is not an int"),
        }
    }

    pub(crate) fn value_raw_int_for_checked_branch(&mut self, value: CodegenValue) -> ir::Value {
        // The caller guards this block with a runtime int-tag check. Statically
        // non-int scalar bindings make the block unreachable, but Cranelift
        // still needs a well-typed i64 value while building it.
        match value {
            CodegenValue::RawInt(value) => value,
            CodegenValue::Known {
                payload,
                kind: ValueKind::INT,
            } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_int(value_ref),
            CodegenValue::RawAtom(value) | CodegenValue::Condition(value) => value,
            CodegenValue::Known { payload, .. } => payload,
            CodegenValue::RawF64(value) => self.b.ins().bitcast(types::I64, MemFlagsData::new(), value),
        }
    }

    pub(crate) fn value_raw_float(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::RawF64(value) => value,
            CodegenValue::Known {
                payload,
                kind: ValueKind::FLOAT,
            } => self.b.ins().bitcast(types::F64, MemFlagsData::new(), payload),
            CodegenValue::AnyRef(value_ref) => self.unbox_float(value_ref),
            _ => panic!("CodegenValue is not a float"),
        }
    }

    // -- ABI boxing / representation coercion (cache-free) --

    pub(crate) fn box_known_non_heap(&mut self, raw: ir::Value, kind: ValueKind) -> ir::Value {
        if kind == ValueKind::INT {
            return self.box_int_for_any(raw);
        }
        if kind == ValueKind::FLOAT {
            let raw = self.b.ins().bitcast(types::F64, MemFlagsData::new(), raw);
            return self.box_float_for_any(raw);
        }
        if kind == ValueKind::ATOM {
            return self.box_atom_for_any(raw);
        }
        if kind == ValueKind::PID {
            return immediate_ref_word(self.b, raw, ValueKind::PID);
        }
        let b = &mut *self.b;
        if kind == ValueKind::NULL {
            return b.ins().iconst(types::I64, 0);
        }
        if kind == ValueKind::LIST {
            let _ = raw;
            let word = AnyValueRef::empty_list().raw_word();
            return b.ins().iconst(types::I64, word as i64);
        }
        unreachable!("heap refs must stay as CodegenValue::AnyRef")
    }

    pub(crate) fn coerce_binding_to(&mut self, binding: CodegenValue, to: ArgRepr) -> ir::Value {
        match (binding, to) {
            (CodegenValue::Known { payload, kind }, ArgRepr::ValueRef) => self.box_known_non_heap(payload, kind),
            (
                CodegenValue::Known {
                    payload,
                    kind: ValueKind::INT,
                },
                ArgRepr::RawInt,
            ) => payload,
            (
                CodegenValue::Known {
                    payload,
                    kind: ValueKind::FLOAT,
                },
                ArgRepr::RawF64,
            ) => self.b.ins().bitcast(types::F64, MemFlagsData::new(), payload),
            (
                CodegenValue::Known {
                    payload,
                    kind: ValueKind::INT,
                },
                ArgRepr::RawF64,
            ) => self.b.ins().fcvt_from_sint(types::F64, payload),
            (
                CodegenValue::Known {
                    payload,
                    kind: ValueKind::FLOAT,
                },
                ArgRepr::RawInt,
            ) => {
                let float = self.b.ins().bitcast(types::F64, MemFlagsData::new(), payload);
                self.b.ins().fcvt_to_sint(types::I64, float)
            }
            (
                CodegenValue::Known {
                    payload,
                    kind: ValueKind::ATOM,
                },
                ArgRepr::RawAtom,
            ) => payload,
            (CodegenValue::Known { .. }, ArgRepr::RawInt | ArgRepr::RawF64 | ArgRepr::RawAtom) => {
                panic!("known scalar kind does not match requested raw ABI repr")
            }
            (CodegenValue::Known { .. }, ArgRepr::Condition) => {
                unreachable!("condition is never a callee ABI target")
            }
            (CodegenValue::AnyRef(value), ArgRepr::ValueRef) => value,
            (CodegenValue::AnyRef(value), ArgRepr::RawInt) => self.unbox_int(value),
            (CodegenValue::AnyRef(value), ArgRepr::RawF64) => self.unbox_float(value),
            (CodegenValue::AnyRef(value), ArgRepr::RawAtom) => self.unbox_atom(value),
            (CodegenValue::AnyRef(_), ArgRepr::Condition) => {
                unreachable!("condition is never a callee ABI target")
            }
            (CodegenValue::RawInt(value), ArgRepr::ValueRef) => self.box_int_for_any(value),
            (CodegenValue::RawF64(value), ArgRepr::ValueRef) => self.box_float_for_any(value),
            (CodegenValue::RawAtom(value), ArgRepr::ValueRef) => self.box_atom_for_any(value),
            (CodegenValue::Condition(value), ArgRepr::ValueRef) => {
                let atom = {
                    let b = &mut *self.b;
                    let true_v = b.ins().iconst(types::I64, TRUE_BITS);
                    let false_v = b.ins().iconst(types::I64, FALSE_BITS);
                    b.ins().select(value, true_v, false_v)
                };
                self.box_atom_for_any(atom)
            }
            (CodegenValue::Condition(value), ArgRepr::RawAtom) => bool_to_fz(self.b, self.cache, value),
            (binding, to) => {
                if binding.repr() == to {
                    binding.value()
                } else {
                    self.coerce_to(binding.value(), binding.repr(), to)
                }
            }
        }
    }

    pub(crate) fn coerce_to(&mut self, val: ir::Value, from: ArgRepr, to: ArgRepr) -> ir::Value {
        if from == to {
            return val;
        }
        match (from, to) {
            (ArgRepr::ValueRef, ArgRepr::RawInt) => self.unbox_int(val),
            (ArgRepr::ValueRef, ArgRepr::RawF64) => self.unbox_float(val),
            (ArgRepr::ValueRef, ArgRepr::RawAtom) => self.unbox_atom(val),
            (ArgRepr::RawInt, ArgRepr::ValueRef) => self.box_int_for_any(val),
            (ArgRepr::RawF64, ArgRepr::ValueRef) => self.box_float_for_any(val),
            (ArgRepr::RawAtom, ArgRepr::ValueRef) => self.box_atom_for_any(val),
            (ArgRepr::RawInt, ArgRepr::RawF64) => self.b.ins().fcvt_from_sint(types::F64, val),
            (ArgRepr::RawF64, ArgRepr::RawInt) => self.b.ins().fcvt_to_sint(types::I64, val),
            (ArgRepr::RawAtom, ArgRepr::RawInt)
            | (ArgRepr::RawAtom, ArgRepr::RawF64)
            | (ArgRepr::RawInt, ArgRepr::RawAtom)
            | (ArgRepr::RawF64, ArgRepr::RawAtom) => {
                panic!("cannot coerce atom and numeric raw ABI reprs")
            }
            (ArgRepr::Condition, _) | (_, ArgRepr::Condition) => {
                unreachable!("Condition vars are never coerced")
            }
            (ArgRepr::ValueRef, ArgRepr::ValueRef)
            | (ArgRepr::RawInt, ArgRepr::RawInt)
            | (ArgRepr::RawF64, ArgRepr::RawF64)
            | (ArgRepr::RawAtom, ArgRepr::RawAtom) => {
                unreachable!("same-repr coerce: handled by early return")
            }
        }
    }

    // -- var-keyed raw extraction (cache-free) --

    pub(crate) fn as_raw_i64(&mut self, var_env: &HashMap<u32, CodegenValue>, v: u32) -> ir::Value {
        match *var_env.get(&v).expect("unbound var") {
            CodegenValue::RawInt(value) => value,
            CodegenValue::Known { payload, .. } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_int(value_ref),
            _ => panic!("cannot read raw i64 from non-integer value"),
        }
    }

    pub(crate) fn as_raw_f64(&mut self, var_env: &HashMap<u32, CodegenValue>, v: u32) -> ir::Value {
        match *var_env.get(&v).expect("unbound var") {
            CodegenValue::RawF64(value) => value,
            CodegenValue::Known { payload, .. } => self.b.ins().bitcast(types::F64, MemFlagsData::new(), payload),
            CodegenValue::AnyRef(value_ref) => self.unbox_float(value_ref),
            _ => panic!("cannot read raw f64 from non-float value"),
        }
    }

    /// The IEEE 754 bits of the number `v` holds as an f64, an integer being
    /// converted first, whether the compiler knows its kind or only a ref names it: the raw word a float bitstring field is written from.
    pub(crate) fn as_float_word(&mut self, var_env: &HashMap<u32, CodegenValue>, v: u32) -> ir::Value {
        let binding = *var_env.get(&v).expect("unbound var");
        if let CodegenValue::AnyRef(value_ref) = binding {
            return runtime_call1!(self, fz_number_ref_float_bits, [value_ref]);
        }
        let float = self.coerce_binding_to(binding, ArgRepr::RawF64);
        self.b.ins().bitcast(types::I64, MemFlagsData::new(), float)
    }

    // -- closure capture access by usize index (cache-free) --

    fn index_const(&mut self, idx: usize) -> ir::Value {
        self.b.ins().iconst(types::I64, idx as i64)
    }

    pub(crate) fn closure_capture_i64_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_i64(closure_ref, index)
    }

    pub(crate) fn closure_capture_f64_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_f64(closure_ref, index)
    }

    pub(crate) fn closure_capture_atom_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_atom(closure_ref, index)
    }

    pub(crate) fn closure_capture_ref_at(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        count: CaptureCount,
    ) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_ref(closure_ref, index, count)
    }

    pub(crate) fn closure_capture_as_binding(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        repr: ArgRepr,
        count: CaptureCount,
    ) -> CodegenValue {
        match repr {
            ArgRepr::RawInt => CodegenValue::from_abi_value(self.closure_capture_i64_at(closure_ref, idx), repr),
            ArgRepr::RawF64 => CodegenValue::from_abi_value(self.closure_capture_f64_at(closure_ref, idx), repr),
            ArgRepr::RawAtom => CodegenValue::from_abi_value(self.closure_capture_atom_at(closure_ref, idx), repr),
            ArgRepr::ValueRef => CodegenValue::any_ref(self.closure_capture_ref_at(closure_ref, idx, count)),
            ArgRepr::Condition => unreachable!("closure captures are never condition-only"),
        }
    }

    /// The outer continuation a continuation holds as capture 0. It is always
    /// a closure, and every writer of a heap capture stores the word's payload,
    /// so its ref word is the slot under the closure tag, with no kind byte,
    /// capture count or mask to apply.
    pub(crate) fn outer_cont_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        let address = address_field(self.b, closure_ref);
        let payload = self
            .b
            .ins()
            .load(types::I64, MemFlagsData::trusted(), address, CLOSURE_CAPTURES_OFFSET);
        let tag_word = (u64::from(ValueKind::CLOSURE.tag()) << AnyValueRefPacking::current().tag_shift()) as i64;
        self.b.ins().bor_imm_u(payload, tag_word)
    }

    /// Capture `value` as the word and kind it is held as, shared since the
    /// closure now holds it too. A number held in a register is stored as is.
    pub(crate) fn store_closure_capture_value(&mut self, closure_ref: ir::Value, idx: usize, value: CodegenValue) {
        self.share(value);
        let [word, kind] = super::support::stored_parts(self, value);
        let index = self.index_const(idx);
        self.set_closure_capture_ref(closure_ref, index, word, kind);
    }

    pub(crate) fn store_closure_capture_i64(&mut self, closure_ref: ir::Value, idx: usize, value: ir::Value) {
        let index = self.index_const(idx);
        self.set_closure_capture_i64(closure_ref, index, value);
    }

    pub(crate) fn store_closure_capture_f64(&mut self, closure_ref: ir::Value, idx: usize, value: ir::Value) {
        let index = self.index_const(idx);
        self.set_closure_capture_f64(closure_ref, index, value);
    }

    pub(crate) fn store_closure_capture_atom(&mut self, closure_ref: ir::Value, idx: usize, value: ir::Value) {
        let index = self.index_const(idx);
        self.set_closure_capture_atom(closure_ref, index, value);
    }

    /// Materialize a value as an ABI `AnyValueRef` word. Cache-bearing:
    /// the `Condition` lane interns its `bool_to_fz` atom.
    pub(crate) fn value_as_any_ref(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::AnyRef(value) => value,
            CodegenValue::RawInt(value) => self.box_int_for_any(value),
            CodegenValue::RawF64(value) => self.box_float_for_any(value),
            CodegenValue::RawAtom(value) => self.box_atom_for_any(value),
            CodegenValue::Condition(value) => {
                let atom = bool_to_fz(self.b, self.cache, value);
                self.box_atom_for_any(atom)
            }
            CodegenValue::Known { payload, kind } => self.box_known_non_heap(payload, kind),
        }
    }

    pub(crate) fn heap_ref_word_from_addr(&mut self, ptr: ir::Value, kind: ValueKind) -> ir::Value {
        assert!(
            kind.is_heap() || kind.is_boxed_scalar(),
            "heap_ref_word_from_addr requires a heap or boxed scalar kind"
        );
        let ptr_payload = match TaggedRefArch::current() {
            TaggedRefArch::Arm64Tbi => ptr,
            TaggedRefArch::X86_64Canonical57 => {
                let clear_shift = i64::from(64 - AnyValueRefPacking::current().tag_shift());
                let shifted = self.b.ins().ishl_imm_u(ptr, clear_shift);
                self.b.ins().ushr_imm_u(shifted, clear_shift)
            }
        };
        let tag_word = ((kind.tag() as u64) << AnyValueRefPacking::current().tag_shift()) as i64;
        self.b.ins().bor_imm_u(ptr_payload, tag_word)
    }

    /// Materialize the var's binding as an ABI `AnyValueRef`, reusing a
    /// cached `iconst` for known raw-int constants.
    pub(crate) fn tagged_var(&mut self, var_env: &HashMap<u32, CodegenValue>, var: u32) -> ir::Value {
        match *var_env.get(&var).expect("unbound var") {
            CodegenValue::RawF64(value) => self.box_float_for_any(value),
            CodegenValue::RawAtom(value) => self.box_atom_for_any(value),
            CodegenValue::RawInt(value) => {
                let raw = if let Some(&n) = self.cache.raw_int_consts.get(&var) {
                    cached_iconst(self.b, self.cache, n)
                } else {
                    value
                };
                self.box_int_for_any(raw)
            }
            CodegenValue::Known { payload, kind } => self.box_known_non_heap(payload, kind),
            CodegenValue::AnyRef(value) => value,
            CodegenValue::Condition(value) => {
                let atom = bool_to_fz(self.b, self.cache, value);
                self.box_atom_for_any(atom)
            }
        }
    }

    pub(crate) fn value_raw_atom(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::RawAtom(raw) => raw,
            CodegenValue::Condition(flag) => bool_to_fz(self.b, self.cache, flag),
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => payload,
            CodegenValue::AnyRef(value_ref) => self.unbox_atom(value_ref),
            _ => panic!("CodegenValue is not an atom"),
        }
    }

    pub(crate) fn any_ref_for_var(&mut self, var_env: &HashMap<u32, CodegenValue>, var: u32) -> ir::Value {
        let binding = *var_env.get(&var).expect("unbound var");
        self.value_as_any_ref(binding)
    }

    /// A jump argument in the form its target parameter takes.
    pub(crate) fn goto_arg_value(&mut self, binding: CodegenValue, want: ArgRepr) -> ir::Value {
        if want == ArgRepr::ValueRef {
            self.value_as_any_ref(binding)
        } else if binding.repr() != want {
            self.coerce_binding_to(binding, want)
        } else {
            binding.value()
        }
    }

    /// Empty-list ABI word, cached per function body.
    pub(crate) fn empty_list_ref(&mut self) -> ir::Value {
        emit_empty_list_value_ref_word(self.b, self.cache)
    }

    pub(crate) fn list_tail_ref_word(&mut self, tail: ListTailBits) -> ir::Value {
        match tail {
            ListTailBits::Empty => self.empty_list_ref(),
            ListTailBits::ValueRef(value) | ListTailBits::NonEmptyValueRef(value) => value,
        }
    }

    pub(crate) fn coerce_call_args(
        &mut self,
        args: &[Var],
        callee_param_reprs: &[ArgRepr],
        var_env: &HashMap<u32, CodegenValue>,
    ) -> Vec<ir::Value> {
        let mut out = Vec::with_capacity(args.len() + 1);
        for (i, av) in args.iter().enumerate() {
            let binding = *var_env.get(&av.0).expect("unbound call arg");
            self.push_binding_as_abi_arg(&mut out, binding, callee_param_reprs[i]);
        }
        out
    }

    pub(crate) fn push_binding_as_abi_arg(&mut self, out: &mut Vec<ir::Value>, binding: CodegenValue, to: ArgRepr) {
        if to == ArgRepr::ValueRef {
            let value_ref = match binding {
                CodegenValue::RawInt(value) => self.box_int_for_any(value),
                CodegenValue::RawF64(value) => self.box_float_for_any(value),
                CodegenValue::RawAtom(value) => self.box_atom_for_any(value),
                CodegenValue::Condition(value) => {
                    let atom = bool_to_fz(self.b, self.cache, value);
                    self.box_atom_for_any(atom)
                }
                CodegenValue::AnyRef(value) => value,
                CodegenValue::Known { payload, kind } => self.box_known_non_heap(payload, kind),
            };
            out.push(value_ref);
        } else {
            out.push(self.coerce_binding_to(binding, to));
        }
    }
}
