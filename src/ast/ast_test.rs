use super::BitSizeKnowledge::{Absent, ByteSizeOf, Literal, Runtime};
use super::BitType::{Binary, Bits, Float, Integer, Utf8, Utf16, Utf32};
use super::bit_remainder;

/// Construction and matching both ask this one question of a segment: how many
/// bits does it span past a whole byte, if the program text says.
#[test]
fn a_segment_reports_the_bits_it_spans_past_whole_bytes() {
    // (type, size, unit, source is binary, remainder)
    let table = [
        (Integer, Absent, None, false, Some(0)),
        (Integer, Literal(3), None, false, Some(3)),
        (Integer, Literal(16), None, false, Some(0)),
        (Integer, Literal(2), Some(8), false, Some(0)),
        (Integer, Literal(5), Some(3), false, Some(7)),
        (Integer, Runtime, None, false, None),
        (Integer, Runtime, Some(8), false, Some(0)),
        (Float, Absent, None, false, Some(0)),
        (Float, Literal(32), None, false, Some(0)),
        (Binary, Absent, None, false, Some(0)),
        (Binary, Literal(2), None, false, Some(0)),
        (Binary, Literal(2), Some(3), false, Some(6)),
        (Binary, Runtime, None, false, Some(0)),
        (Binary, Runtime, Some(3), false, None),
        (Binary, ByteSizeOf, None, false, Some(0)),
        (Bits, Absent, None, false, None),
        (Bits, Absent, None, true, Some(0)),
        (Bits, Literal(3), None, false, Some(3)),
        (Bits, Literal(8), None, false, Some(0)),
        (Bits, Runtime, None, false, None),
        (Bits, ByteSizeOf, None, false, Some(0)),
        (Utf8, Absent, None, false, Some(0)),
        (Utf16, Absent, None, false, Some(0)),
        (Utf32, Absent, None, false, Some(0)),
    ];
    for (ty, size, unit, source_is_binary, expected) in table {
        assert_eq!(
            bit_remainder(ty, size, unit, source_is_binary),
            expected,
            "{ty:?} {size:?} unit {unit:?} source_is_binary {source_is_binary}"
        );
    }
}
