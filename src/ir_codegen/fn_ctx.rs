//! Per-function semantic codegen context.
//!
//! Cranelift's `FunctionBuilder` owns the body currently being emitted.
//! Function-local imports, however, need both the module and the function
//! body. `CodegenFn` is the fz-owned boundary for "lower one fz function":
//! semantic lowering code should ask this context for operations, while
//! runtime helper calls remain an implementation detail behind those methods.

use super::*;
use crate::fz_ir::Var;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlags, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{FuncId, Linkage, Module};
use fz_runtime::any_value::{
    AnyValueRef, AnyValueRefPacking, FALSE_ATOM_ID, NIL_ATOM_ID, TRUE_ATOM_ID, TaggedRefArch, ValueKind,
};
use fz_runtime::heap::{FieldKind, Schema};
use std::collections::HashMap;

/// Per-function semantic codegen machine: runtime refs + the function-local
/// import table, plus the `FunctionBuilder`, module, and cache bound for the
/// body currently being emitted. Every runtime-BIF operation is an inherent
/// method built on `call`/`call1`; semantic lowering code drives all emission
/// through this one type.
pub(crate) struct CodegenFn<'a, 'env, 'fb, M>
where
    M: Module,
{
    runtime: &'env RuntimeRefs,
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
}

impl<'a, 'env, 'fb, M: Module> CodegenFn<'a, 'env, 'fb, M> {
    pub(crate) fn new(
        env: &'env CodegenEnv<'_>,
        b: &'a mut FunctionBuilder<'fb>,
        jmod: &'a mut M,
        cache: &'a mut CodegenCache,
    ) -> Self {
        Self {
            runtime: env.runtime,
            imports: HashMap::new(),
            process_by_block: HashMap::new(),
            b,
            jmod,
            cache,
        }
    }

    /// Build a semantic machine for generated runtime shim bodies, which
    /// have runtime refs but no fz `CodegenEnv`.
    pub(crate) fn for_runtime_shim(
        runtime: &'env RuntimeRefs,
        b: &'a mut FunctionBuilder<'fb>,
        jmod: &'a mut M,
        cache: &'a mut CodegenCache,
    ) -> Self {
        Self {
            runtime,
            imports: HashMap::new(),
            process_by_block: HashMap::new(),
            b,
            jmod,
            cache,
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

    fn call(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Inst {
        let fref = self.func_ref(id);
        self.b.ins().call(fref, args)
    }

    fn call1(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Value {
        let inst = self.call(id, args);
        self.b.inst_results(inst)[0]
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

    /// Call a process-taking BIF, prepending the pinned `Process*` to `args`.
    fn call1_p(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Value {
        let process = self.process_arg();
        let mut full = Vec::with_capacity(args.len() + 1);
        full.push(process);
        full.extend_from_slice(args);
        self.call1(id, &full)
    }

    /// Like `call1_p`, for a process-taking BIF with no return value.
    fn call_p(&mut self, id: FuncId, args: &[ir::Value]) -> ir::Inst {
        let process = self.process_arg();
        let mut full = Vec::with_capacity(args.len() + 1);
        full.push(process);
        full.extend_from_slice(args);
        self.call(id, &full)
    }

    /// Declare a runtime import by symbol name (idempotent) and call it. The
    /// single declare→fref→call path for the intrinsics lowered by name rather
    /// than through a `RuntimeRefs` id; the wire ABI comes from the one
    /// `runtime_import_sig` table and `func_ref` dedups the per-fn import like
    /// every other call site.
    pub(crate) fn call_named(&mut self, name: &str, args: &[ir::Value]) -> ir::Inst {
        let sig = runtime_import_sig(name);
        let id = self
            .jmod
            .declare_function(name, Linkage::Import, &sig)
            .expect("declare runtime import");
        let fref = self.func_ref(id);
        self.b.ins().call(fref, args)
    }

    pub(crate) fn ref_tag(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.runtime.type_of_id;
        self.call1(id, &[value_ref])
    }

    pub(crate) fn truthy_ref(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.runtime.truthy_ref_id;
        self.call1(id, &[value_ref])
    }

    pub(crate) fn mark_published_ref_aliased(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.runtime.mark_published_ref_aliased_id;
        self.call1_p(id, &[value_ref])
    }

    pub(crate) fn box_int_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let id = self.runtime.box_int_for_any_id;
        self.call1_p(id, &[raw])
    }

    pub(crate) fn box_float_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let id = self.runtime.box_float_for_any_id;
        self.call1_p(id, &[raw])
    }

    pub(crate) fn box_atom_for_any(&mut self, raw: ir::Value) -> ir::Value {
        let id = self.runtime.box_atom_for_any_id;
        self.call1_p(id, &[raw])
    }

    pub(crate) fn unbox_int(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.runtime.unbox_int_id;
        self.call1(id, &[value_ref])
    }

    pub(crate) fn unbox_float(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.runtime.unbox_float_id;
        self.call1(id, &[value_ref])
    }

    pub(crate) fn unbox_atom(&mut self, value_ref: ir::Value) -> ir::Value {
        let id = self.runtime.unbox_atom_id;
        self.call1(id, &[value_ref])
    }

    pub(crate) fn halt_implicit(&mut self, repr: ArgRepr, value: ir::Value) {
        let id = match repr {
            ArgRepr::RawInt => self.runtime.halt_implicit_i64_id,
            ArgRepr::RawF64 => self.runtime.halt_implicit_f64_id,
            ArgRepr::RawAtom => self.runtime.halt_implicit_atom_id,
            ArgRepr::ValueRef => self.runtime.halt_implicit_ref_id,
            ArgRepr::Condition => unreachable!("condition halt values must be materialized"),
        };
        self.call_p(id, &[value]);
    }

    pub(crate) fn alloc_frame(&mut self, schema_id: ir::Value, size: ir::Value) -> ir::Value {
        let id = self.runtime.alloc_id;
        self.call1_p(id, &[schema_id, size])
    }

    pub(crate) fn get_halt_cont(&mut self, body_addr: ir::Value, halt_kind: ir::Value) -> ir::Value {
        let id = self.runtime.get_halt_cont_id;
        self.call1_p(id, &[body_addr, halt_kind])
    }

    pub(crate) fn alloc_closure(
        &mut self,
        func_id: ir::Value,
        captured_count: ir::Value,
        halt_kind: ir::Value,
        code_addr: ir::Value,
    ) -> ir::Value {
        let id = self.runtime.alloc_closure_id;
        self.call1_p(id, &[func_id, captured_count, halt_kind, code_addr])
    }

    pub(crate) fn list_cons_with(&mut self, cons_id: FuncId, args: &[ir::Value]) -> ir::Value {
        self.call1_p(cons_id, args)
    }

    pub(crate) fn list_head(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.runtime.list_head_fallback_id;
        self.call1(id, &[list_ref])
    }

    pub(crate) fn list_head_int(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.runtime.list_head_int_ref_id;
        self.call1(id, &[list_ref])
    }

    pub(crate) fn list_head_float(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.runtime.list_head_float_ref_id;
        self.call1(id, &[list_ref])
    }

    pub(crate) fn list_tail(&mut self, list_ref: ir::Value) -> ir::Value {
        let id = self.runtime.list_tail_fallback_id;
        self.call1(id, &[list_ref])
    }

    pub(crate) fn list_reuse_or_cons_tail_ref(&mut self, source_ref: ir::Value, tail_ref: ir::Value) -> ir::Value {
        let id = self.runtime.list_reuse_or_cons_tail_ref_id;
        self.call1_p(id, &[source_ref, tail_ref])
    }

    pub(crate) fn closure_capture_i64(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.runtime.closure_get_capture_i64_id;
        self.call1(id, &[closure_ref, index])
    }

    pub(crate) fn closure_capture_f64(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.runtime.closure_get_capture_f64_id;
        self.call1(id, &[closure_ref, index])
    }

    pub(crate) fn closure_capture_atom(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.runtime.closure_get_capture_atom_id;
        self.call1(id, &[closure_ref, index])
    }

    pub(crate) fn closure_capture_ref(&mut self, closure_ref: ir::Value, index: ir::Value) -> ir::Value {
        let id = self.runtime.closure_get_capture_ref_id;
        self.call1(id, &[closure_ref, index])
    }

    pub(crate) fn closure_code_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        let id = self.runtime.closure_code_ref_id;
        self.call1(id, &[closure_ref])
    }

    pub(crate) fn closure_halt_kind_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        let id = self.runtime.closure_halt_kind_ref_id;
        self.call1(id, &[closure_ref])
    }

    pub(crate) fn set_closure_capture_ref(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let id = self.runtime.closure_set_capture_ref_id;
        self.call_p(id, &[closure_ref, index, value]);
    }

    pub(crate) fn set_closure_capture_i64(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let id = self.runtime.closure_set_capture_i64_id;
        self.call_p(id, &[closure_ref, index, value]);
    }

    pub(crate) fn set_closure_capture_f64(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let id = self.runtime.closure_set_capture_f64_id;
        self.call_p(id, &[closure_ref, index, value]);
    }

    pub(crate) fn set_closure_capture_atom(&mut self, closure_ref: ir::Value, index: ir::Value, value: ir::Value) {
        let id = self.runtime.closure_set_capture_atom_id;
        self.call_p(id, &[closure_ref, index, value]);
    }

    pub(crate) fn materialize_cont(&mut self, value: ir::Value) -> ir::Value {
        let id = self.runtime.materialize_cont_id;
        self.call1_p(id, &[value])
    }

    pub(crate) fn struct_set_field_int(&mut self, struct_bits: ir::Value, offset: ir::Value, value: ir::Value) {
        let id = self.runtime.struct_set_field_int_id;
        self.call_p(id, &[struct_bits, offset, value]);
    }

    pub(crate) fn struct_set_field_float(&mut self, struct_bits: ir::Value, offset: ir::Value, value: ir::Value) {
        let id = self.runtime.struct_set_field_float_id;
        self.call_p(id, &[struct_bits, offset, value]);
    }

    pub(crate) fn struct_set_field_atom(&mut self, struct_bits: ir::Value, offset: ir::Value, value: ir::Value) {
        let id = self.runtime.struct_set_field_atom_id;
        self.call_p(id, &[struct_bits, offset, value]);
    }

    pub(crate) fn struct_set_field_ref(&mut self, struct_bits: ir::Value, offset: ir::Value, value: ir::Value) {
        let id = self.runtime.struct_set_field_ref_id;
        self.call_p(id, &[struct_bits, offset, value]);
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
                let is_false = b.ins().icmp_imm(IntCC::Equal, payload, FALSE_ATOM_ID as i64);
                let is_nil = b.ins().icmp_imm(IntCC::Equal, payload, NIL_ATOM_ID as i64);
                let falsey = b.ins().bor(is_false, is_nil);
                b.ins().bxor_imm(falsey, 1)
            }
            CodegenValue::Known {
                kind: ValueKind::NULL, ..
            } => b.ins().iconst(types::I8, 0),
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => {
                let is_false = b.ins().icmp_imm(IntCC::Equal, payload, FALSE_ATOM_ID as i64);
                let is_nil = b.ins().icmp_imm(IntCC::Equal, payload, NIL_ATOM_ID as i64);
                let falsey = b.ins().bor(is_false, is_nil);
                b.ins().bxor_imm(falsey, 1)
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
        b.ins().icmp_imm(IntCC::Equal, actual, tag.tag() as i64)
    }

    pub(crate) fn value_atom_id_is(&mut self, value: CodegenValue, atom_id: u32) -> ir::Value {
        if let CodegenValue::AnyRef(value_ref) = value {
            // The AnyRef path interleaves block-building with an unbox BIF, so
            // each builder burst is scoped to release the borrow around the
            // `unbox_atom` call (which needs `&mut self`).
            let is_atom = self.value_is_tag(value, ValueKind::ATOM);
            let join_blk = {
                let b = &mut *self.b;
                let atom_blk = b.create_block();
                let join_blk = b.create_block();
                b.append_block_param(join_blk, types::I8);
                let false8 = b.ins().iconst(types::I8, 0);
                let no_args: Vec<BlockArg> = Vec::new();
                b.ins()
                    .brif(is_atom, atom_blk, &no_args, join_blk, &[BlockArg::Value(false8)]);
                b.switch_to_block(atom_blk);
                b.seal_block(atom_blk);
                join_blk
            };
            let atom = self.unbox_atom(value_ref);
            let b = &mut *self.b;
            let found = b.ins().icmp_imm(IntCC::Equal, atom, atom_id as i64);
            b.ins().jump(join_blk, &[BlockArg::Value(found)]);
            b.switch_to_block(join_blk);
            b.seal_block(join_blk);
            return b.block_params(join_blk)[0];
        }
        let b = &mut *self.b;
        match value {
            CodegenValue::Condition(flag) => {
                if atom_id == TRUE_ATOM_ID {
                    return flag;
                }
                if atom_id == FALSE_ATOM_ID {
                    return b.ins().bxor_imm(flag, 1);
                }
                b.ins().iconst(types::I8, 0)
            }
            CodegenValue::RawAtom(payload) => b.ins().icmp_imm(IntCC::Equal, payload, atom_id as i64),
            CodegenValue::RawInt(_) | CodegenValue::RawF64(_) => b.ins().iconst(types::I8, 0),
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => b.ins().icmp_imm(IntCC::Equal, payload, atom_id as i64),
            CodegenValue::Known { .. } => b.ins().iconst(types::I8, 0),
            CodegenValue::AnyRef(_) => unreachable!("handled above"),
        }
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

    pub(crate) fn value_raw_float(&mut self, value: CodegenValue) -> ir::Value {
        match value {
            CodegenValue::RawF64(value) => value,
            CodegenValue::Known {
                payload,
                kind: ValueKind::FLOAT,
            } => self.b.ins().bitcast(types::F64, MemFlags::new(), payload),
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
            let raw = self.b.ins().bitcast(types::F64, MemFlags::new(), raw);
            return self.box_float_for_any(raw);
        }
        if kind == ValueKind::ATOM {
            return self.box_atom_for_any(raw);
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
            ) => self.b.ins().bitcast(types::F64, MemFlags::new(), payload),
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
                let float = self.b.ins().bitcast(types::F64, MemFlags::new(), payload);
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
            CodegenValue::Known { payload, .. } => self.b.ins().bitcast(types::F64, MemFlags::new(), payload),
            CodegenValue::AnyRef(value_ref) => self.unbox_float(value_ref),
            other => tagged_to_raw_f64_unsupported(self.b, other.value()),
        }
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

    pub(crate) fn closure_capture_ref_at(&mut self, closure_ref: ir::Value, idx: usize) -> ir::Value {
        let index = self.index_const(idx);
        self.closure_capture_ref(closure_ref, index)
    }

    pub(crate) fn closure_capture_as_binding(
        &mut self,
        closure_ref: ir::Value,
        idx: usize,
        repr: ArgRepr,
    ) -> CodegenValue {
        match repr {
            ArgRepr::RawInt => CodegenValue::from_abi_value(self.closure_capture_i64_at(closure_ref, idx), repr),
            ArgRepr::RawF64 => CodegenValue::from_abi_value(self.closure_capture_f64_at(closure_ref, idx), repr),
            ArgRepr::RawAtom => CodegenValue::from_abi_value(self.closure_capture_atom_at(closure_ref, idx), repr),
            ArgRepr::ValueRef => CodegenValue::any_ref(self.closure_capture_ref_at(closure_ref, idx)),
            ArgRepr::Condition => unreachable!("closure captures are never condition-only"),
        }
    }

    pub(crate) fn outer_cont_ref(&mut self, closure_ref: ir::Value) -> ir::Value {
        self.closure_capture_ref_at(closure_ref, 0)
    }

    pub(crate) fn store_closure_capture_ref_word(&mut self, closure_ref: ir::Value, idx: usize, value: ir::Value) {
        let value = self.mark_published_ref_aliased(value);
        let index = self.index_const(idx);
        self.set_closure_capture_ref(closure_ref, index, value);
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
        assert!(kind.is_heap(), "heap_ref_word_from_addr requires a heap kind");
        let ptr_payload = match TaggedRefArch::current() {
            TaggedRefArch::Arm64Tbi => ptr,
            TaggedRefArch::X86_64Canonical57 => {
                let clear_shift = i64::from(64 - AnyValueRefPacking::current().tag_shift());
                let shifted = self.b.ins().ishl_imm(ptr, clear_shift);
                self.b.ins().ushr_imm(shifted, clear_shift)
            }
        };
        let tag_word = ((kind.tag() as u64) << AnyValueRefPacking::current().tag_shift()) as i64;
        self.b.ins().bor_imm(ptr_payload, tag_word)
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

    /// Coerce a goto block argument to the repr its target param needs,
    /// returning the rebound value when it changes and `None` when the
    /// binding already matches.
    pub(crate) fn coerce_goto_arg(&mut self, vb: CodegenValue, want: ArgRepr) -> Option<CodegenValue> {
        if want == ArgRepr::ValueRef {
            Some(CodegenValue::any_ref(self.value_as_any_ref(vb)))
        } else if vb.repr() != want {
            Some(CodegenValue::from_abi_value(self.coerce_binding_to(vb, want), want))
        } else {
            None
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

    pub(crate) fn owned_cons_reuse_source(&self, head: Var) -> Option<Var> {
        self.cache.owned_cons_reuse_sources.get(&head.0).copied()
    }

    pub(crate) fn store_frame_value_dynamic(&mut self, frame: ir::Value, field_offset: u32, value: CodegenValue) {
        let value_ref = self.value_as_any_ref(value);
        self.b
            .ins()
            .store(MemFlags::trusted(), value_ref, frame, field_offset as i32);
    }

    pub(crate) fn store_frame_word(&mut self, frame: ir::Value, field_offset: u32, value: ir::Value) {
        self.b
            .ins()
            .store(MemFlags::trusted(), value, frame, field_offset as i32);
    }

    pub(crate) fn store_bindings_into_callee_frame(
        &mut self,
        callee_schema: &Schema,
        callee_frame: ir::Value,
        args: &[CodegenValue],
        slot_base: usize,
    ) {
        for (i, binding) in args.iter().copied().enumerate() {
            let slot_idx = slot_base + i;
            let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
            match callee_schema.fields[slot_idx].kind {
                FieldKind::RawF64 => {
                    let f = self.coerce_binding_to(binding, ArgRepr::RawF64);
                    self.b.ins().store(MemFlags::trusted(), f, callee_frame, off);
                }
                FieldKind::RawI64 => {
                    let n = self.coerce_binding_to(binding, ArgRepr::RawInt);
                    self.b.ins().store(MemFlags::trusted(), n, callee_frame, off);
                }
                FieldKind::AnyValue => {
                    let value_ref = self.value_as_any_ref(binding);
                    self.b.ins().store(MemFlags::trusted(), value_ref, callee_frame, off);
                }
                FieldKind::RawBytes(_) => {
                    self.b
                        .ins()
                        .store(MemFlags::trusted(), binding.value(), callee_frame, off);
                }
            }
        }
    }

    pub(crate) fn store_typed_args_into_callee_frame(
        &mut self,
        callee_schema: &Schema,
        callee_frame: ir::Value,
        args: &[(ir::Value, ArgRepr)],
        slot_base: usize,
    ) {
        for (i, &(value, from)) in args.iter().enumerate() {
            let slot_idx = slot_base + i;
            let off = HEADER_SIZE + SLOT_BYTES * (slot_idx as i32);
            match callee_schema.fields[slot_idx].kind {
                FieldKind::RawF64 => {
                    let binding = CodegenValue::from_abi_value(value, from);
                    let f = self.coerce_binding_to(binding, ArgRepr::RawF64);
                    self.b.ins().store(MemFlags::trusted(), f, callee_frame, off);
                }
                FieldKind::RawI64 => {
                    let binding = CodegenValue::from_abi_value(value, from);
                    let n = self.coerce_binding_to(binding, ArgRepr::RawInt);
                    self.b.ins().store(MemFlags::trusted(), n, callee_frame, off);
                }
                FieldKind::AnyValue => {
                    let value_ref = match from {
                        ArgRepr::ValueRef => value,
                        ArgRepr::RawInt => self.box_int_for_any(value),
                        ArgRepr::RawF64 => self.box_float_for_any(value),
                        ArgRepr::RawAtom => self.box_atom_for_any(value),
                        ArgRepr::Condition => {
                            let atom = bool_to_fz(self.b, self.cache, value);
                            self.box_atom_for_any(atom)
                        }
                    };
                    self.b.ins().store(MemFlags::trusted(), value_ref, callee_frame, off);
                }
                FieldKind::RawBytes(_) => {
                    self.b.ins().store(MemFlags::trusted(), value, callee_frame, off);
                }
            }
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

    /// Write `value` into field `field_idx` of the struct/tuple at
    /// `struct_bits`, picking the typed setter for the value's
    /// representation. Heap refs are published before the store.
    pub(crate) fn struct_set_field(&mut self, struct_bits: ir::Value, field_idx: usize, value: CodegenValue) {
        let offset = self.b.ins().iconst(types::I32, (field_idx as i64) * SLOT_BYTES as i64);
        match value {
            CodegenValue::RawInt(raw)
            | CodegenValue::Known {
                payload: raw,
                kind: ValueKind::INT,
            } => {
                self.struct_set_field_int(struct_bits, offset, raw);
            }
            CodegenValue::RawF64(raw) => {
                self.struct_set_field_float(struct_bits, offset, raw);
            }
            CodegenValue::RawAtom(raw) => {
                self.struct_set_field_atom(struct_bits, offset, raw);
            }
            CodegenValue::Known {
                payload,
                kind: ValueKind::FLOAT,
            } => {
                let raw = self.b.ins().bitcast(types::F64, MemFlags::new(), payload);
                self.struct_set_field_float(struct_bits, offset, raw);
            }
            CodegenValue::Known {
                payload,
                kind: ValueKind::ATOM,
            } => {
                self.struct_set_field_atom(struct_bits, offset, payload);
            }
            other => {
                let value_ref = self.value_as_any_ref(other);
                let value_ref = self.mark_published_ref_aliased(value_ref);
                self.struct_set_field_ref(struct_bits, offset, value_ref);
            }
        }
    }
}

#[cfg(test)]
#[path = "fn_ctx_test.rs"]
mod fn_ctx_test;
