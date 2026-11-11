//! Read-only data objects a program emits once and every process shares: static
//! struct literals, static closures and halt continuations.
//!
//! An object is plain bytes laid out like its heap twin, a header word first,
//! plus the addresses the linker or JIT fills in. It is 16-byte aligned so its
//! low nibble is clear (the forwarding marker owns that nibble), and it sits
//! outside every heap, so the collector and deep copy pass it by pointer.

use super::*;
use cranelift_codegen::ir::{self, InstBuilder, types};
use cranelift_frontend::FunctionBuilder;
use cranelift_module::{DataDescription, DataId, FuncId, Linkage, Module};
use fz_runtime::any_value::{AnyValueRefPacking, ClosureDenotationId, closure_header_word, closure_size_for_count};

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

/// The address of `data_id` as an i64.
pub(crate) fn data_addr<M: Module>(jmod: &mut M, data_id: DataId, b: &mut FunctionBuilder<'_>) -> ir::Value {
    let gv = jmod.declare_data_in_func(data_id, b.func);
    b.ins().symbol_value(types::I64, gv)
}
