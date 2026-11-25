//! The fields of a construction whose bits the program text already spells.
//!
//! A field is constant when its value is a literal and its size is absent or a
//! literal, and the runtime accepts it. Its bits are computed by the runtime's
//! own encoder (`fz_runtime::construction::encode_constants`), the one
//! definition of how a field is written, so folding cannot disagree with a
//! construction that runs.
//!
//! A construction of constants alone is the literal binary it spells. Inside a
//! construction with other fields, a run of adjacent constants is one literal
//! field. A run is written as whole bytes, so it is merged only where it starts
//! on a byte boundary and the bytes end on one: the offset before a field is
//! the sum of what the fields before it add beyond whole bytes, and a field
//! whose bits are read at run time leaves the offset unknown for every field
//! after it. A run that starts mid-byte begins at its first field that starts
//! on a boundary; a run's last bits that stop mid-byte stay separate fields.

use super::construction_contract::settled_by_literal;
use crate::ast::{BitField, BitSize, BitSizeKnowledge, BitType, Expr, Spanned, bit_remainder};
use fz_runtime::construction::{ConstantField, ConstantValue, encode_constants};
use fz_runtime::ir_runtime::fz_bs_field_spec;

/// What a construction's fields come to once their constants are written out.
#[derive(Debug, PartialEq, Eq)]
pub(super) enum Folded {
    /// Every field is constant and they add up to whole bytes: the construction
    /// is this literal binary.
    Literal(Vec<u8>),
    /// The construction's pieces, in order.
    Pieces(Vec<Piece>),
}

#[derive(Debug, PartialEq, Eq)]
pub(super) enum Piece {
    /// The field at this index, built as written.
    Field(usize),
    /// The `len` fields from `first` on, written as these bytes.
    Literal { first: usize, len: usize, bytes: Vec<u8> },
}

pub(super) fn fold(fields: &[BitField<Spanned<Expr>>]) -> Folded {
    let constants: Vec<Option<ConstantField<'_>>> = fields.iter().map(constant_field).collect();
    if let Some(all) = constants.iter().copied().collect::<Option<Vec<_>>>()
        && let Ok(encoded) = encode_constants(&all)
        && encoded.bit_len % 8 == 0
    {
        return Folded::Literal(encoded.bytes);
    }
    let mut pieces = Vec::new();
    let mut offset = Some(0);
    let mut at = 0;
    while at < fields.len() {
        if offset == Some(0)
            && let Some(end) = byte_aligned_run(&constants, at)
        {
            let run: Vec<_> = constants[at..end].iter().flatten().copied().collect();
            if !is_one_literal(&fields[at..end])
                && let Ok(encoded) = encode_constants(&run)
            {
                pieces.push(Piece::Literal {
                    first: at,
                    len: end - at,
                    bytes: encoded.bytes,
                });
                at = end;
                continue;
            }
        }
        pieces.push(Piece::Field(at));
        offset = offset
            .zip(remainder(&fields[at], constants[at].as_ref()))
            .map(|(o, r)| (o + r) % 8);
        at += 1;
    }
    Folded::Pieces(pieces)
}

/// The end of the longest run of constants from `start` whose bits come to
/// whole bytes.
fn byte_aligned_run(constants: &[Option<ConstantField<'_>>], start: usize) -> Option<usize> {
    let mut bits = 0;
    let mut end = None;
    for (index, field) in constants.iter().enumerate().skip(start) {
        let Some(field) = field else { break };
        bits += bit_len(field)?;
        if bits % 8 == 0 {
            end = Some(index + 1);
        }
    }
    end
}

fn bit_len(field: &ConstantField<'_>) -> Option<u64> {
    encode_constants(&[*field]).ok().map(|encoded| encoded.bit_len)
}

/// A run of one field that is already a literal binary needs no rewriting.
fn is_one_literal(run: &[BitField<Spanned<Expr>>]) -> bool {
    matches!(run, [field] if matches!(field.value.node, Expr::Binary(_)) && field.spec.size.is_none())
}

/// The bits a field adds beyond whole bytes, when the program text says.
fn remainder(field: &BitField<Spanned<Expr>>, constant: Option<&ConstantField<'_>>) -> Option<u64> {
    if let Some(constant) = constant {
        return bit_len(constant).map(|bits| bits % 8);
    }
    let size = match &field.spec.size {
        None => BitSizeKnowledge::Absent,
        Some(BitSize::Literal(size)) => BitSizeKnowledge::Literal(*size),
        Some(BitSize::Var(_) | BitSize::Expr(_)) => BitSizeKnowledge::Runtime,
    };
    bit_remainder(field.spec.ty, size, field.spec.unit, false)
}

/// The field as the runtime's encoder takes it, when its bits are known and
/// the runtime accepts them.
fn constant_field(field: &BitField<Spanned<Expr>>) -> Option<ConstantField<'_>> {
    let spec = &field.spec;
    let size = match &spec.size {
        None => None,
        Some(BitSize::Literal(size)) => Some(u64::from(*size)),
        Some(_) => return None,
    };
    if !settled_by_literal(field) {
        return None;
    }
    let value = match (&field.value.node, spec.ty) {
        (Expr::Int(int), BitType::Integer | BitType::Utf8 | BitType::Utf16 | BitType::Utf32) => {
            ConstantValue::Word(*int as u64)
        }
        (Expr::Int(int), BitType::Float) => ConstantValue::Float(*int as f64),
        (Expr::Float(float), BitType::Float) => ConstantValue::Float(*float),
        (Expr::Binary(bytes), BitType::Binary | BitType::Bits) => ConstantValue::Bytes(bytes),
        _ => return None,
    };
    let constant = ConstantField {
        spec: fz_bs_field_spec(
            spec.ty.tag(),
            u32::from(size.is_some()),
            spec.unit.unwrap_or(spec.ty.default_unit()),
            spec.endian.tag(),
            0,
            0,
        ),
        size: size.unwrap_or(0),
        value,
    };
    encode_constants(&[constant]).ok()?;
    Some(constant)
}

#[cfg(test)]
#[path = "constant_fields_test.rs"]
mod constant_fields_test;
