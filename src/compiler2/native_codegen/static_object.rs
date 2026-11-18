//! Read-only data objects a program emits once and every process shares: static
//! struct literals, static closures, halt continuations and the templates of
//! `try` handlers that capture nothing and never return.
//!
//! An object is plain bytes laid out like its heap twin, a header word first,
//! plus the addresses the linker or JIT fills in. It is 16-byte aligned so its
//! low nibble is clear (the forwarding marker owns that nibble), and it sits
//! outside every heap, so the collector and deep copy pass it by pointer.

use super::*;
use cranelift_codegen::ir::{self, InstBuilder, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use fz_runtime::any_value::{
    AnyValue, AnyValueRefPacking, ClosureDenotationId, closure_capture_set, closure_header_word, closure_size_for_count,
};
use fz_runtime::park::{ReceiveClause, ReceiveSite};
use std::mem::{offset_of, size_of};

/// An address stored into an object's bytes.
#[derive(Clone, Copy)]
pub(crate) enum StaticAddress {
    Data(DataId),
    Function(FuncId),
}

/// Define a local, read-only, 16-byte aligned object of `bytes`, with each
/// `(offset, target)` word replaced by the target's address.
pub(crate) fn define_read_only_object<M: Module>(
    jmod: &mut M,
    name: &str,
    bytes: Vec<u8>,
    addresses: &[(usize, StaticAddress)],
) -> Result<DataId, CodegenError> {
    let data_id = jmod
        .declare_data(name, Linkage::Local, /*writable=*/ false, false)
        .map_err(|e| CodegenError::new(format!("declare {}: {}", name, e)))?;
    let mut desc = DataDescription::new();
    desc.define(bytes.into_boxed_slice());
    desc.set_align(16);
    for (offset, target) in addresses {
        match *target {
            StaticAddress::Data(target) => {
                let gv = jmod.declare_data_in_data(target, &mut desc);
                // A stored address names read-only data, so it carries the literal bit.
                desc.write_data_addr(*offset as u32, gv, AnyValueRefPacking::current().literal_bit() as i64);
            }
            StaticAddress::Function(target) => {
                let fref = jmod.declare_func_in_data(target, &mut desc);
                desc.write_function_addr(*offset as u32, fref);
            }
        }
    }
    jmod.define_data(data_id, &desc)
        .map_err(|e| CodegenError::new(format!("define {}: {}", name, e)))?;
    Ok(data_id)
}

/// Define a zero-capture closure whose code pointer is `code`.
pub(crate) fn define_static_closure<M: Module>(
    jmod: &mut M,
    name: &str,
    denotation: ClosureDenotationId,
    halt_kind: u32,
    arity: u32,
    code: FuncId,
) -> Result<DataId, CodegenError> {
    let mut bytes = vec![0u8; closure_size_for_count(0)];
    let header = closure_header_word(denotation, 0, halt_kind as u16, arity as u16);
    bytes[0..8].copy_from_slice(&header.to_le_bytes());
    define_read_only_object(jmod, name, bytes, &[(8, StaticAddress::Function(code))])
}

/// Define the continuation template of a `try` handler that captures nothing
/// and never returns. A template's one fixed capture is the continuation the
/// handler returns to; this handler has none to return to, so the slot holds
/// `nil` and the whole template is constant.
pub(crate) fn define_static_handler_template<M: Module>(
    jmod: &mut M,
    name: &str,
    arity: u32,
    code: FuncId,
) -> Result<DataId, CodegenError> {
    let mut bytes = vec![0u8; closure_size_for_count(1)];
    let header = closure_header_word(ClosureDenotationId::INTERNAL, 1, 0, arity as u16);
    bytes[0..8].copy_from_slice(&header.to_le_bytes());
    // SAFETY: `bytes` is a closure of one capture whose header is written.
    unsafe { closure_capture_set(bytes.as_mut_ptr(), 0, AnyValue::nil_atom()) };
    define_read_only_object(jmod, name, bytes, &[(8, StaticAddress::Function(code))])
}

/// What a `receive` fixes at compile time, as codegen holds it.
pub(crate) struct ReceiveSiteLayout {
    pub(crate) matcher: FuncId,
    /// The `after` body's code and empty slot count.
    pub(crate) after: Option<(FuncId, u32)>,
    pub(crate) pinned_count: u32,
    /// Each clause's code, bound count and empty slot count, in source order.
    pub(crate) clauses: Vec<(FuncId, u32, u32)>,
}

/// Define a receive's `ReceiveSite` record with its clauses behind it.
pub(crate) fn define_receive_site<M: Module>(
    jmod: &mut M,
    name: &str,
    site: &ReceiveSiteLayout,
) -> Result<DataId, CodegenError> {
    let header = size_of::<ReceiveSite>();
    let clause = size_of::<ReceiveClause>();
    let mut bytes = vec![0u8; header + clause * site.clauses.len()];
    let mut addresses = vec![(offset_of!(ReceiveSite, matcher), StaticAddress::Function(site.matcher))];
    let mut put = |offset: usize, value: u32| bytes[offset..offset + 4].copy_from_slice(&value.to_le_bytes());
    put(offset_of!(ReceiveSite, clause_count), site.clauses.len() as u32);
    put(offset_of!(ReceiveSite, pinned_count), site.pinned_count);
    let bound_arity = site.clauses.iter().map(|&(_, bound, _)| bound).max().unwrap_or(0);
    put(offset_of!(ReceiveSite, bound_arity), bound_arity);
    if let Some((code, empty_slots)) = site.after {
        addresses.push((offset_of!(ReceiveSite, after_code), StaticAddress::Function(code)));
        put(offset_of!(ReceiveSite, after_empty_slots), empty_slots);
    }
    for (i, &(code, bound_count, empty_slots)) in site.clauses.iter().enumerate() {
        let at = header + i * clause;
        addresses.push((at + offset_of!(ReceiveClause, code), StaticAddress::Function(code)));
        put(at + offset_of!(ReceiveClause, bound_count), bound_count);
        put(at + offset_of!(ReceiveClause, empty_slots), empty_slots);
    }
    define_read_only_object(jmod, name, bytes, &addresses)
}

/// The address of `data_id` as an i64.
pub(crate) fn data_addr<M: Module>(jmod: &mut M, data_id: DataId, b: &mut FunctionBuilder<'_>) -> ir::Value {
    let gv = jmod.declare_data_in_func(data_id, b.func);
    b.ins().symbol_value(types::I64, gv)
}
