//! fz-cty.8 — constant-fold `MakeBitstring` with all-constant byte fields.
//!
//! Recognise byte-literal bitstrings — every field is an `Integer` of size 8
//! (unsigned, default endianness, unit 1) sourced from a `Const::Int` — and
//! rewrite the per-field `MakeBitstring` to a single `ConstBitstring(bytes,
//! bit_len)`. Codegen interns the byte payload as a module-private data
//! symbol and emits one allocation call, replacing the O(N) FFI fanout of
//! `fz_bs_begin` / `fz_bs_write_field` × N / `fz_bs_finalize`.
//!
//! Mixed bitstrings (any runtime field, any non-byte-integer field) are
//! left untouched — codegen keeps the per-field path for them.

use crate::ast::{BitType, Endian};
use crate::fz_ir::{BitSizeIr, Const, FnIr, Module, Prim, Stmt, Var};
use std::collections::HashMap;

pub fn fold_module(m: &mut Module) {
    for f in &mut m.fns {
        fold_fn(f);
    }
}

fn fold_fn(f: &mut FnIr) {
    // Build a per-fn map Var → i64 for vars defined by `Prim::Const(Int(_))`.
    // SSA-ish IR: each Var is defined exactly once.
    let mut int_const: HashMap<Var, i64> = HashMap::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(v, Prim::Const(Const::Int(n))) = stmt else {
                continue;
            };
            int_const.insert(*v, *n);
        }
    }
    for block in &mut f.blocks {
        for stmt in &mut block.stmts {
            let Stmt::Let(_, prim) = stmt;
            let Prim::MakeBitstring(fields) = prim else {
                continue;
            };
            if let Some((bytes, bit_len)) = try_collect_bytes(fields, &int_const) {
                *prim = Prim::ConstBitstring(bytes, bit_len);
            }
        }
    }
}

/// If every field is a byte-sized unsigned integer literal in default
/// endianness/unit, return the materialised byte vector and bit length.
fn try_collect_bytes(
    fields: &[crate::fz_ir::BitFieldIr],
    int_const: &HashMap<Var, i64>,
) -> Option<(Vec<u8>, u64)> {
    if fields.is_empty() {
        return None;
    }
    let mut bytes = Vec::with_capacity(fields.len());
    for f in fields {
        if f.ty != BitType::Integer {
            return None;
        }
        if f.signed {
            return None;
        }
        // Default unit for Integer is 1.
        if f.unit.is_some_and(|u| u != 1) {
            return None;
        }
        // Endianness must not matter at 8 bits — accept Big/Native (the
        // canonical defaults). Little also produces the same byte at width 8,
        // but stay conservative.
        if !matches!(f.endian, Endian::Big | Endian::Native) {
            return None;
        }
        // Size must be exactly 8 bits. `None` carries the default-for-Integer
        // size, which is 8 bits (see ast / bit-spec defaulting); accept that
        // case without requiring an explicit literal. An explicit literal
        // must equal 8; a runtime size-var blocks the fold.
        let bits = match &f.size {
            None => 8,
            Some(BitSizeIr::Literal(n)) => *n,
            Some(BitSizeIr::Var(_)) => return None,
        };
        if bits != 8 {
            return None;
        }
        let val = *int_const.get(&f.value)?;
        bytes.push((val as u64 & 0xff) as u8);
    }
    let bit_len = (bytes.len() as u64) * 8;
    Some((bytes, bit_len))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BitType, Endian};
    use crate::fz_ir::{
        BitFieldIr, BitSizeIr, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var,
    };

    fn byte_field(value: Var) -> BitFieldIr {
        BitFieldIr {
            value,
            ty: BitType::Integer,
            size: Some(BitSizeIr::Literal(8)),
            endian: Endian::Big,
            signed: false,
            unit: Some(1),
        }
    }

    #[test]
    fn all_constant_bytes_fold_to_const_bitstring() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let c2 = b.let_(entry, Prim::Const(Const::Int(2)));
        let c3 = b.let_(entry, Prim::Const(Const::Int(255)));
        let bs = b.let_(
            entry,
            Prim::MakeBitstring(vec![byte_field(c1), byte_field(c2), byte_field(c3)]),
        );
        b.set_terminator(entry, Term::Return(bs));
        let f = b.build();
        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        fold_module(&mut m);

        let stmt = m.fns[0]
            .block(m.fns[0].entry)
            .stmts
            .iter()
            .find_map(|s| {
                let Stmt::Let(_, p) = s;
                matches!(p, Prim::ConstBitstring(..)).then_some(p)
            })
            .expect("expected a ConstBitstring stmt");
        match stmt {
            Prim::ConstBitstring(bytes, bit_len) => {
                assert_eq!(bytes, &vec![1u8, 2, 255]);
                assert_eq!(*bit_len, 24);
            }
            _ => unreachable!(),
        }
    }

    #[test]
    fn mixed_runtime_field_blocks_fold() {
        // One field's value comes from a function parameter — not a Const.
        let mut b = FnBuilder::new(FnId(0), "main");
        let param = b.fresh_var();
        let entry = b.block(vec![param]);
        let c2 = b.let_(entry, Prim::Const(Const::Int(2)));
        let bs = b.let_(
            entry,
            Prim::MakeBitstring(vec![byte_field(param), byte_field(c2)]),
        );
        b.set_terminator(entry, Term::Return(bs));
        let f = b.build();
        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        fold_module(&mut m);

        let found_make = m.fns[0]
            .block(m.fns[0].entry)
            .stmts
            .iter()
            .any(|s| matches!(s, Stmt::Let(_, Prim::MakeBitstring(_))));
        let found_const = m.fns[0]
            .block(m.fns[0].entry)
            .stmts
            .iter()
            .any(|s| matches!(s, Stmt::Let(_, Prim::ConstBitstring(..))));
        assert!(
            found_make,
            "MakeBitstring should remain when any field is runtime"
        );
        assert!(!found_const, "no ConstBitstring should be produced");
    }

    #[test]
    fn non_byte_integer_field_blocks_fold() {
        // 16-bit field — not byte-sized → fold must skip.
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let mut f16 = byte_field(c1);
        f16.size = Some(BitSizeIr::Literal(16));
        let bs = b.let_(entry, Prim::MakeBitstring(vec![f16]));
        b.set_terminator(entry, Term::Return(bs));
        let f = b.build();
        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();

        fold_module(&mut m);

        assert!(
            m.fns[0]
                .block(m.fns[0].entry)
                .stmts
                .iter()
                .any(|s| matches!(s, Stmt::Let(_, Prim::MakeBitstring(_))))
        );
    }
}
