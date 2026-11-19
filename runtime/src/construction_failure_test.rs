use super::*;

fn segment(ty: BitType, value: Shape) -> Segment {
    Segment {
        ty,
        value,
        size: None,
        unit: if ty == BitType::Binary { 8 } else { 1 },
    }
}

fn sized(ty: BitType, value: Shape, size: Shape) -> Segment {
    Segment {
        size: Some(size),
        ..segment(ty, value)
    }
}

const ATOM: Shape = Shape::Other;

fn bits(bits: u64) -> Shape {
    Shape::Bitstring { bits }
}

#[test]
fn every_segment_keeping_its_contract_breaks_nothing() {
    let segments = [
        segment(BitType::Integer, Shape::Int(5)),
        segment(BitType::Float, Shape::Int(5)),
        segment(BitType::Binary, bits(16)),
        sized(BitType::Binary, bits(24), Shape::Int(2)),
        segment(BitType::Bits, bits(3)),
        segment(BitType::Utf8, Shape::Int(0x10FFFF)),
    ];
    assert_eq!(first_breach(&segments), None);
}

#[test]
fn a_size_an_unsized_binary_and_a_code_point_are_checked_before_any_value_is_written() {
    let unsized_atom = [segment(BitType::Integer, ATOM), segment(BitType::Binary, ATOM)];
    assert_eq!(first_breach(&unsized_atom), Some((1, Breach::NotABinary)));
    let surrogate = [
        segment(BitType::Integer, ATOM),
        segment(BitType::Utf8, Shape::Int(0xDC00)),
    ];
    assert_eq!(first_breach(&surrogate), Some((1, Breach::NotACodePoint)));
    let bad_size = [
        segment(BitType::Integer, ATOM),
        sized(BitType::Integer, Shape::Int(5), ATOM),
    ];
    assert_eq!(first_breach(&bad_size), Some((1, Breach::Size)));
}

#[test]
fn values_lengths_and_units_are_checked_in_segment_order_while_writing() {
    let short = [
        segment(BitType::Integer, ATOM),
        sized(BitType::Binary, bits(8), Shape::Int(2)),
    ];
    assert_eq!(first_breach(&short), Some((0, Breach::NotAnInteger)));
    let ragged = [segment(BitType::Integer, ATOM), segment(BitType::Binary, bits(3))];
    assert_eq!(first_breach(&ragged), Some((0, Breach::NotAnInteger)));
    assert_eq!(
        first_breach(&[sized(BitType::Binary, bits(8), Shape::Int(2))]),
        Some((0, Breach::Shorter))
    );
    assert_eq!(
        first_breach(&[segment(BitType::Binary, bits(3))]),
        Some((0, Breach::NotAUnitMultiple))
    );
}

#[test]
fn a_float_takes_an_integer_and_only_the_three_ieee_sizes() {
    assert_eq!(
        first_breach(&[segment(BitType::Float, ATOM)]),
        Some((0, Breach::NotANumber))
    );
    for size in [16, 32, 64] {
        assert_eq!(
            first_breach(&[sized(BitType::Float, Shape::Float, Shape::Int(size))]),
            None
        );
    }
    assert_eq!(
        first_breach(&[sized(BitType::Float, Shape::Float, Shape::Int(2))]),
        Some((0, Breach::FloatSize))
    );
    assert_eq!(
        first_breach(&[sized(BitType::Float, Shape::Float, Shape::Int(-1))]),
        Some((0, Breach::Size))
    );
}

#[test]
fn a_code_point_is_a_non_negative_integer_up_to_0x10ffff_outside_the_surrogates() {
    for bad in [
        Shape::Int(-1),
        Shape::Int(0xD800),
        Shape::Int(0xDFFF),
        Shape::Int(0x110000),
        ATOM,
    ] {
        assert_eq!(
            first_breach(&[segment(BitType::Utf16, bad)]),
            Some((0, Breach::NotACodePoint))
        );
    }
    for good in [0, 0xD7FF, 0xE000, 0x10FFFF] {
        assert_eq!(first_breach(&[segment(BitType::Utf32, Shape::Int(good))]), None);
    }
}

#[test]
fn the_message_counts_segments_from_one_and_reports_bits_as_binary() {
    assert_eq!(
        construction_message(1, BitType::Bits, Breach::NotABinary, ":a", "nil"),
        "construction of binary failed: segment 2 of type 'binary': expected a binary but got: :a"
    );
    assert_eq!(
        construction_message(0, BitType::Utf16, Breach::NotACodePoint, "1114112", "nil"),
        "construction of binary failed: segment 1 of type 'utf16': expected a non-negative integer encodable as \
         utf16 but got: 1114112"
    );
}
