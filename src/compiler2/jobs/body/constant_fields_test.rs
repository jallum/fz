//! Which constants of a construction are written out where the program is
//! compiled, and where a run of them stops.

use super::*;
use crate::ast::{BitFieldSpec, Endian, Var};
use crate::source::Span;

fn at(expr: Expr) -> Spanned<Expr> {
    Spanned::new(expr, Span::DUMMY)
}

fn spec(ty: BitType, size: Option<BitSize>) -> BitFieldSpec {
    BitFieldSpec {
        ty,
        size,
        endian: Endian::Big,
        signed: false,
        unit: None,
    }
}

fn field(value: Expr, ty: BitType, size: Option<BitSize>) -> BitField<Spanned<Expr>> {
    BitField {
        value: at(value),
        spec: spec(ty, size),
    }
}

/// `value::size`, an integer constant.
fn int(value: i64, bits: u32) -> BitField<Spanned<Expr>> {
    field(Expr::Int(value), BitType::Integer, Some(BitSize::Literal(bits)))
}

/// A byte, `value`.
fn byte(value: i64) -> BitField<Spanned<Expr>> {
    field(Expr::Int(value), BitType::Integer, None)
}

fn text(bytes: &str) -> BitField<Spanned<Expr>> {
    field(Expr::Binary(bytes.as_bytes().to_vec()), BitType::Binary, None)
}

/// A field read at run time, `x::bits`.
fn var(bits: u32) -> BitField<Spanned<Expr>> {
    field(
        Expr::Var(Var::user("x")),
        BitType::Integer,
        Some(BitSize::Literal(bits)),
    )
}

fn variable_binary() -> BitField<Spanned<Expr>> {
    field(Expr::Var(Var::user("x")), BitType::Binary, None)
}

fn run_time_size() -> BitField<Spanned<Expr>> {
    field(
        Expr::Var(Var::user("x")),
        BitType::Integer,
        Some(BitSize::Var(Var::user("n"))),
    )
}

fn literal(first: usize, len: usize, bytes: &[u8]) -> Piece {
    Piece::Literal {
        first,
        len,
        bytes: bytes.to_vec(),
    }
}

fn pieces(fields: Vec<BitField<Spanned<Expr>>>) -> Vec<Piece> {
    match fold(&fields) {
        Folded::Pieces(pieces) => pieces,
        Folded::Literal(bytes) => panic!("folded to the literal {bytes:?}"),
    }
}

#[test]
fn a_construction_of_constants_is_the_literal_it_spells() {
    assert_eq!(fold(&[byte(65)]), Folded::Literal(vec![65]));
    assert_eq!(fold(&[]), Folded::Literal(vec![]));
    assert_eq!(fold(&[text("a"), text("b")]), Folded::Literal(b"ab".to_vec()));
    assert_eq!(fold(&[int(1, 3), int(2, 5)]), Folded::Literal(vec![0x22]));
    assert_eq!(
        fold(&[
            int(0x1234, 16),
            field(Expr::Float(1.0), BitType::Float, Some(BitSize::Literal(16)))
        ]),
        Folded::Literal(vec![0x12, 0x34, 0x3c, 0x00])
    );
    assert_eq!(
        fold(&[field(Expr::Int(0x20ac), BitType::Utf8, None)]),
        Folded::Literal("\u{20ac}".as_bytes().to_vec())
    );
}

#[test]
fn constants_that_stop_mid_byte_are_not_a_literal_binary() {
    assert_eq!(pieces(vec![int(1, 3)]), [Piece::Field(0)]);
    assert_eq!(pieces(vec![int(1, 1), int(1, 1)]), [Piece::Field(0), Piece::Field(1)]);
}

#[test]
fn a_run_of_constants_between_two_variable_fields_is_one_literal_field() {
    assert_eq!(
        pieces(vec![var(8), byte(1), byte(2), byte(3), var(8)]),
        [Piece::Field(0), literal(1, 3, &[1, 2, 3]), Piece::Field(4)]
    );
    assert_eq!(
        pieces(vec![var(8), text("xy"), int(7, 16), var(8)]),
        [Piece::Field(0), literal(1, 2, &[b'x', b'y', 0, 7]), Piece::Field(3)]
    );
}

#[test]
fn a_run_ends_with_the_last_field_that_stops_on_a_byte() {
    assert_eq!(
        pieces(vec![byte(1), byte(2), int(3, 3), var(5)]),
        [literal(0, 2, &[1, 2]), Piece::Field(2), Piece::Field(3)]
    );
    assert_eq!(
        pieces(vec![var(8), int(1, 4), int(2, 4), int(3, 4)]),
        [Piece::Field(0), literal(1, 2, &[0x12]), Piece::Field(3)]
    );
}

#[test]
fn a_run_starts_at_the_first_field_that_starts_on_a_byte() {
    assert_eq!(
        pieces(vec![var(3), int(1, 5), byte(7), byte(8)]),
        [Piece::Field(0), Piece::Field(1), literal(2, 2, &[7, 8])]
    );
    assert_eq!(
        pieces(vec![int(1, 4), int(2, 4), var(8), int(3, 4), int(4, 4)]),
        [literal(0, 2, &[0x12]), Piece::Field(2), literal(3, 2, &[0x34])]
    );
    assert_eq!(
        pieces(vec![var(3), int(1, 3), int(2, 2), byte(9), var(8)]),
        [
            Piece::Field(0),
            Piece::Field(1),
            Piece::Field(2),
            literal(3, 1, &[9]),
            Piece::Field(4)
        ]
    );
}

#[test]
fn nothing_merges_after_a_field_whose_bits_are_read_at_run_time() {
    assert_eq!(
        pieces(vec![run_time_size(), byte(1), byte(2)]),
        [Piece::Field(0), Piece::Field(1), Piece::Field(2)]
    );
    assert_eq!(
        pieces(vec![byte(1), byte(2), run_time_size(), byte(3), byte(4)]),
        [
            literal(0, 2, &[1, 2]),
            Piece::Field(2),
            Piece::Field(3),
            Piece::Field(4)
        ]
    );
}

#[test]
fn a_binary_read_at_run_time_keeps_the_offset_on_a_byte() {
    assert_eq!(
        pieces(vec![variable_binary(), byte(1), byte(2)]),
        [Piece::Field(0), literal(1, 2, &[1, 2])]
    );
}

#[test]
fn a_literal_binary_alone_is_left_as_it_is_and_another_constant_alone_is_written_out() {
    assert_eq!(pieces(vec![var(8), text("ab")]), [Piece::Field(0), Piece::Field(1)]);
    assert_eq!(pieces(vec![var(8), byte(65)]), [Piece::Field(0), literal(1, 1, &[65])]);
}

#[test]
fn a_constant_the_runtime_refuses_is_left_to_raise_when_the_construction_runs() {
    let surrogate = || field(Expr::Int(0xD800), BitType::Utf8, None);
    assert_eq!(pieces(vec![surrogate()]), [Piece::Field(0)]);
    assert_eq!(
        pieces(vec![byte(1), surrogate(), byte(2), byte(3)]),
        [literal(0, 1, &[1]), Piece::Field(1), literal(2, 2, &[2, 3])]
    );
    let wrong_type = field(Expr::Float(1.5), BitType::Integer, None);
    assert_eq!(pieces(vec![wrong_type]), [Piece::Field(0)]);
}
