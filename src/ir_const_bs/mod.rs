//! fz-cty.8 / fz-q8d.2 — constant-fold `MakeBitstring` with all-constant fields.
//!
//! Recognise bitstrings whose every field is either:
//!   * an `Integer` literal (any size 1..=64, any endianness, signed or
//!     unsigned, any unit), or
//!   * a `Float` literal of size 32 or 64 bits,
//!
//! and rewrite the per-field `MakeBitstring` to a single
//! `ConstBitstring(bytes, bit_len)`. Codegen interns the byte payload as a
//! module-private data symbol and (for above-threshold payloads) emits a
//! static SharedBin in `.data` plus a single call to
//! `fz_alloc_procbin_from_static`, replacing the O(N) FFI fanout of
//! `fz_bs_begin` / `fz_bs_write_field` × N / `fz_bs_finalize`.
//!
//! Mixed bitstrings (any runtime field, runtime size, Binary / Bits / Utf,
//! out-of-range float size) are left untouched — codegen keeps the
//! per-field path for them.

use crate::ast::BitType;
use crate::fz_ir::{BitSizeIr, Const, FnIr, Module, Prim, Stmt, Var};
use fz_runtime::bitstr::{BitWriter, Endian as RtEndian, apply_endian_for_write};
use std::collections::HashMap;

pub fn fold_module(m: &mut Module) {
    for f in &mut m.fns {
        fold_fn(f);
    }
}

fn fold_fn(f: &mut FnIr) {
    // SSA-ish IR: each Var is defined exactly once. Collect Var -> constant
    // tables for Int and Float so the fold pass can look up literal values.
    let mut int_const: HashMap<Var, i64> = HashMap::new();
    let mut float_const: HashMap<Var, f64> = HashMap::new();
    for block in &f.blocks {
        for stmt in &block.stmts {
            let Stmt::Let(v, prim) = stmt;
            match prim {
                Prim::Const(Const::Int(n)) => {
                    int_const.insert(*v, *n);
                }
                Prim::Const(Const::Float(x)) => {
                    float_const.insert(*v, *x);
                }
                _ => {}
            }
        }
    }
    for block in &mut f.blocks {
        for stmt in &mut block.stmts {
            let Stmt::Let(_, prim) = stmt;
            let Prim::MakeBitstring(fields) = prim else {
                continue;
            };
            if let Some((bytes, bit_len)) = try_fold(fields, &int_const, &float_const) {
                *prim = Prim::ConstBitstring(bytes, bit_len);
            }
        }
    }
}

/// Map the AST endian enum (used by `BitFieldIr`) to the runtime's `Endian`.
fn map_endian(e: crate::ast::Endian) -> RtEndian {
    use crate::ast::Endian as A;
    match e {
        A::Big => RtEndian::Big,
        A::Little => RtEndian::Little,
        A::Native => RtEndian::Native,
    }
}

/// If every field is a statically-knowable Integer or Float literal,
/// drive a `BitWriter` at compile time and return the resulting bytes +
/// bit length. Otherwise return `None` and leave the per-field codegen
/// path in place.
fn try_fold(
    fields: &[crate::fz_ir::BitFieldIr],
    int_const: &HashMap<Var, i64>,
    float_const: &HashMap<Var, f64>,
) -> Option<(Vec<u8>, u64)> {
    if fields.is_empty() {
        return None;
    }
    let mut w = BitWriter::new();
    for f in fields {
        // Resolve total bit width. Field's `unit` defaults vary by type
        // in the AST; we treat `None` as 1 here — matches the canonical
        // default used by `fz_bs_write_field` for Integer/Float.
        let unit = f.unit.unwrap_or(1);
        let total: u32 = match (&f.size, f.ty) {
            (Some(BitSizeIr::Literal(n)), _) => n.saturating_mul(unit),
            // Float with implicit size defaults to 64.
            (None, BitType::Float) => 64u32.saturating_mul(unit),
            // Integer with implicit size defaults to 8.
            (None, BitType::Integer) => 8u32.saturating_mul(unit),
            // Other types either require runtime sources (Binary/Bits) or
            // are codepoint-encoded (Utf*) — neither is foldable.
            _ => return None,
        };
        if total == 0 || total > 64 {
            return None;
        }
        match f.ty {
            BitType::Integer => {
                let val = *int_const.get(&f.value)?;
                let raw = if total < 64 {
                    (val as u64) & ((1u64 << total) - 1)
                } else {
                    val as u64
                };
                let swapped = apply_endian_for_write(raw, total, map_endian(f.endian));
                w.write_bits(swapped, total as usize);
            }
            BitType::Float => {
                let val = *float_const.get(&f.value)?;
                let bits_repr = match total {
                    32 => (val as f32).to_bits() as u64,
                    64 => val.to_bits(),
                    _ => return None, // 16-bit / non-IEEE floats: don't fold
                };
                let swapped = apply_endian_for_write(bits_repr, total, map_endian(f.endian));
                w.write_bits(swapped, total as usize);
            }
            // Binary / Bits read from a runtime bitstring; Utf encodes
            // codepoints at runtime. Leave these to the per-field path.
            BitType::Binary | BitType::Bits | BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
                return None;
            }
        }
        let _ = f.signed; // signed Integer literals: masking + apply_endian
        // already produce the correct bit pattern, so we accept signed.
    }
    Some((w.bytes, w.bit_len as u64))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::{BitType, Endian};
    use crate::fz_ir::{
        BitFieldIr, BitSizeIr, Const, FnBuilder, FnId, ModuleBuilder, Prim, Term, Var,
    };

    fn field(
        value: Var,
        ty: BitType,
        size: Option<u32>,
        endian: Endian,
        signed: bool,
    ) -> BitFieldIr {
        BitFieldIr {
            value,
            ty,
            size: size.map(BitSizeIr::Literal),
            endian,
            signed,
            unit: Some(1),
        }
    }

    fn byte_field(value: Var) -> BitFieldIr {
        field(value, BitType::Integer, Some(8), Endian::Big, false)
    }

    /// Build a module with a single fn whose body is exactly the supplied
    /// fields wrapped in a MakeBitstring; fold and return any
    /// `ConstBitstring` produced.
    fn fold_and_find_const(
        consts: &[(Var, Const)],
        fields: Vec<BitFieldIr>,
    ) -> Option<(Vec<u8>, u64)> {
        let mut b = FnBuilder::new(FnId(0), "main");
        let entry = b.block(vec![]);
        // Declare each const with a let_; we ignore the returned Var
        // because the field-build code already encoded the Var ids the
        // caller chose. Achieve that by binding fresh Vars and rewriting
        // (simpler: emit the consts in order, then trust the Var numbers
        // to line up). FnBuilder allocates Vars sequentially.
        for (_, c) in consts {
            b.let_(entry, Prim::Const(c.clone()));
        }
        let bs = b.let_(entry, Prim::MakeBitstring(fields));
        b.set_terminator(entry, Term::Return(bs));
        let f = b.build();
        let mut mb = ModuleBuilder::new();
        mb.add_fn(f);
        let mut m = mb.build();
        fold_module(&mut m);
        m.fns[0].block(m.fns[0].entry).stmts.iter().find_map(|s| {
            let Stmt::Let(_, p) = s;
            if let Prim::ConstBitstring(bytes, bit_len) = p {
                Some((bytes.clone(), *bit_len))
            } else {
                None
            }
        })
    }

    #[test]
    fn all_byte_literals_fold() {
        let v0 = Var(0);
        let v1 = Var(1);
        let v2 = Var(2);
        let got = fold_and_find_const(
            &[
                (v0, Const::Int(1)),
                (v1, Const::Int(2)),
                (v2, Const::Int(255)),
            ],
            vec![byte_field(v0), byte_field(v1), byte_field(v2)],
        )
        .expect("expected ConstBitstring");
        assert_eq!(got.0, vec![1u8, 2, 255]);
        assert_eq!(got.1, 24);
    }

    #[test]
    fn u16_big_endian_folds() {
        let v0 = Var(0);
        let got = fold_and_find_const(
            &[(v0, Const::Int(0x1234))],
            vec![field(v0, BitType::Integer, Some(16), Endian::Big, false)],
        )
        .expect("u16 BE folds");
        assert_eq!(got.0, vec![0x12, 0x34]);
        assert_eq!(got.1, 16);
    }

    #[test]
    fn i32_little_endian_signed_folds() {
        let v0 = Var(0);
        // -2 as i32 LE = 0xFE 0xFF 0xFF 0xFF.
        let got = fold_and_find_const(
            &[(v0, Const::Int(-2))],
            vec![field(v0, BitType::Integer, Some(32), Endian::Little, true)],
        )
        .expect("i32 LE signed folds");
        assert_eq!(got.0, vec![0xFE, 0xFF, 0xFF, 0xFF]);
        assert_eq!(got.1, 32);
    }

    #[test]
    fn f64_literal_folds() {
        let v0 = Var(0);
        let got = fold_and_find_const(
            &[(v0, Const::Float(1.5))],
            vec![field(v0, BitType::Float, Some(64), Endian::Big, false)],
        )
        .expect("f64 folds");
        assert_eq!(got.0, 1.5f64.to_be_bytes().to_vec());
        assert_eq!(got.1, 64);
    }

    #[test]
    fn four_bit_unsigned_packs() {
        let v0 = Var(0);
        let v1 = Var(1);
        let got = fold_and_find_const(
            &[(v0, Const::Int(0xA)), (v1, Const::Int(0x5))],
            vec![
                field(v0, BitType::Integer, Some(4), Endian::Big, false),
                field(v1, BitType::Integer, Some(4), Endian::Big, false),
            ],
        )
        .expect("two 4-bit literals pack into one byte");
        assert_eq!(got.0, vec![0xA5]);
        assert_eq!(got.1, 8);
    }

    #[test]
    fn mixed_u16_u8_folds() {
        let v0 = Var(0);
        let v1 = Var(1);
        let got = fold_and_find_const(
            &[(v0, Const::Int(0xABCD)), (v1, Const::Int(0xEF))],
            vec![
                field(v0, BitType::Integer, Some(16), Endian::Big, false),
                field(v1, BitType::Integer, Some(8), Endian::Big, false),
            ],
        )
        .expect("u16,u8 folds");
        assert_eq!(got.0, vec![0xAB, 0xCD, 0xEF]);
        assert_eq!(got.1, 24);
    }

    #[test]
    fn float_with_unsupported_size_does_not_fold() {
        let v0 = Var(0);
        let res = fold_and_find_const(
            &[(v0, Const::Float(1.0))],
            vec![field(v0, BitType::Float, Some(16), Endian::Big, false)],
        );
        assert!(res.is_none(), "16-bit float must not fold");
    }

    #[test]
    fn binary_field_blocks_fold() {
        let v0 = Var(0);
        let res = fold_and_find_const(
            &[(v0, Const::Int(0))],
            vec![field(v0, BitType::Binary, None, Endian::Big, false)],
        );
        assert!(res.is_none());
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
        assert!(found_make);
        assert!(!found_const);
    }

    #[test]
    fn runtime_sized_field_blocks_fold() {
        let mut b = FnBuilder::new(FnId(0), "main");
        let size_var = b.fresh_var();
        let entry = b.block(vec![size_var]);
        let c1 = b.let_(entry, Prim::Const(Const::Int(1)));
        let f = BitFieldIr {
            value: c1,
            ty: BitType::Integer,
            size: Some(BitSizeIr::Var(size_var)),
            endian: Endian::Big,
            signed: false,
            unit: Some(1),
        };
        let bs = b.let_(entry, Prim::MakeBitstring(vec![f]));
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
