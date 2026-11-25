//! Why a binary construction failed, worded as Elixir words it.
//!
//! Compiled code tests every segment's contract before it writes a byte. When
//! the test fails it calls `Kernel.__construction_failed__/1` with each
//! segment's type, value, size and unit, which raises an `ArgumentError` whose
//! message `fz_construction_failure_message` words: it names the segment the
//! BEAM names. The BEAM builds in two passes: it first sizes the result, checking
//! every segment's size, the type of an unsized `binary` or `bits` value, and
//! every code point; it then writes the result, checking integer and float
//! values, a sized binary's length and an unsized binary's unit. The first
//! failure of the first pass that fails is the one reported.

use crate::any_value::debug::render_value;
use crate::any_value::{AnyValue, AnyValueRef};
use crate::bits::{Bin, is_bitstring_like};
use crate::bitstr::BitType;
use crate::heap::{list_head_ref, list_tail_ref};
use crate::ir_runtime::{fz_tuple_elem, fz_tuple_size};
use crate::process::Process;

/// The type Elixir's message names: `bits` is reported as `binary`.
fn reported(ty: BitType) -> &'static str {
    match ty {
        BitType::Integer => "integer",
        BitType::Float => "float",
        BitType::Binary | BitType::Bits => "binary",
        BitType::Utf8 => "utf8",
        BitType::Utf16 => "utf16",
        BitType::Utf32 => "utf32",
    }
}

fn is_bitstring(ty: BitType) -> bool {
    matches!(ty, BitType::Binary | BitType::Bits)
}

/// What a contract asks of a value: its kind, and a bitstring's length.
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum Shape {
    Int(i64),
    Float,
    Bitstring { bits: u64 },
    Other,
}

/// One segment of a failed construction.
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Segment {
    pub ty: BitType,
    pub value: Shape,
    /// `None` where the segment names no size.
    pub size: Option<Shape>,
    pub unit: u64,
}

/// Which contract term a segment broke.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Breach {
    Size,
    FloatSize,
    NotAnInteger,
    NotANumber,
    NotABinary,
    Shorter,
    NotAUnitMultiple,
    NotACodePoint,
}

/// The segment the BEAM reports, counted from 0, and what it broke; `None`
/// when every segment keeps its contract.
pub fn first_breach(segments: &[Segment]) -> Option<(usize, Breach)> {
    let pass = |check: fn(&Segment) -> Option<Breach>| {
        segments
            .iter()
            .enumerate()
            .find_map(|(index, segment)| check(segment).map(|breach| (index, breach)))
    };
    pass(sizing_breach).or_else(|| pass(writing_breach))
}

fn sizing_breach(segment: &Segment) -> Option<Breach> {
    if let Some(size) = segment.size {
        let Shape::Int(size) = size else {
            return Some(Breach::Size);
        };
        if size < 0 {
            return Some(Breach::Size);
        }
        if segment.ty == BitType::Float && !matches!(size, 16 | 32 | 64) {
            return Some(Breach::FloatSize);
        }
    }
    match segment.ty {
        ty if is_bitstring(ty) && segment.size.is_none() => {
            (!matches!(segment.value, Shape::Bitstring { .. })).then_some(Breach::NotABinary)
        }
        BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
            (!is_code_point(segment.value)).then_some(Breach::NotACodePoint)
        }
        _ => None,
    }
}

fn writing_breach(segment: &Segment) -> Option<Breach> {
    match (segment.ty, segment.value) {
        (BitType::Integer, Shape::Int(_)) => None,
        (BitType::Integer, _) => Some(Breach::NotAnInteger),
        (BitType::Float, Shape::Int(_) | Shape::Float) => None,
        (BitType::Float, _) => Some(Breach::NotANumber),
        (ty, Shape::Bitstring { bits }) if is_bitstring(ty) => match segment.size {
            Some(Shape::Int(size)) => (bits < size as u64 * segment.unit).then_some(Breach::Shorter),
            _ => (!bits.is_multiple_of(segment.unit)).then_some(Breach::NotAUnitMultiple),
        },
        (ty, _) if is_bitstring(ty) => Some(Breach::NotABinary),
        _ => None,
    }
}

fn is_code_point(value: Shape) -> bool {
    matches!(value, Shape::Int(cp) if (0..=0x10FFFF).contains(&cp) && !(0xD800..=0xDFFF).contains(&cp))
}

/// What Elixir says about the breach, after the segment's number and type.
fn complaint(ty: BitType, breach: Breach, value: &str, size: &str) -> String {
    match breach {
        Breach::Size => format!("expected a non-negative integer as size but got: {size}"),
        Breach::FloatSize => format!("expected one of the supported sizes 16, 32, or 64 but got: {size}"),
        Breach::NotAnInteger => format!("expected an integer but got: {value}"),
        Breach::NotANumber => format!("expected a float or an integer but got: {value}"),
        Breach::NotABinary => format!("expected a binary but got: {value}"),
        Breach::Shorter => format!("the value {value} is shorter than the size of the segment"),
        Breach::NotAUnitMultiple => {
            format!("the size of the value {value} is not a multiple of the unit for the segment")
        }
        Breach::NotACodePoint => {
            format!(
                "expected a non-negative integer encodable as {} but got: {value}",
                reported(ty)
            )
        }
    }
}

/// Elixir's whole message for a breach of segment `index` (counted from 0).
pub fn construction_message(index: usize, ty: BitType, breach: Breach, value: &str, size: &str) -> String {
    format!(
        "construction of binary failed: segment {} of type '{}': {}",
        index + 1,
        reported(ty),
        complaint(ty, breach, value, size)
    )
}

/// One segment as compiled code passes it: `{type, value, size, unit}`, with
/// `nil` for a size the segment does not name.
struct Passed {
    segment: Segment,
    value: AnyValue,
    size: AnyValue,
}

fn word_value(word: u64) -> AnyValue {
    AnyValueRef::from_raw_word(word)
        .and_then(AnyValue::from_ref)
        .unwrap_or_else(|error| panic!("fz_construction_failure_message: a value ref ({error:?})"))
}

fn shape(value: AnyValue) -> Shape {
    match value {
        AnyValue::Int(int) => Shape::Int(int),
        AnyValue::Float(_) => Shape::Float,
        AnyValue::HeapRef(heap) if is_bitstring_like(heap.raw_word()) => Shape::Bitstring {
            bits: unsafe { Bin::of_binary(heap.raw_word()) }.bit_len(),
        },
        _ => Shape::Other,
    }
}

fn atom_name(process: *mut Process, value: AnyValue) -> Option<String> {
    let AnyValue::Atom(id) = value else { return None };
    unsafe { &*process }.node.atom_name(id).map(|name| name.to_string())
}

fn passed(process: *mut Process, word: u64) -> Passed {
    assert_eq!(
        fz_tuple_size(process, word),
        4,
        "fz_construction_failure_message: a 4-tuple per segment"
    );
    let field = |index| word_value(fz_tuple_elem(process, word, index));
    let AnyValue::Int(tag) = field(0) else {
        panic!("fz_construction_failure_message: a segment type tag")
    };
    let ty = BitType::from_tag(tag as u32);
    let (value, size) = (field(1), field(2));
    let AnyValue::Int(unit) = field(3) else {
        panic!("fz_construction_failure_message: an integer unit")
    };
    let named_size = atom_name(process, size).as_deref() != Some("nil");
    Passed {
        segment: Segment {
            ty,
            value: shape(value),
            size: named_size.then(|| shape(size)),
            unit: unit as u64,
        },
        value,
        size,
    }
}

/// The message of the `ArgumentError` Elixir raises for a construction whose
/// segments, `{type, value, size, unit}` each, broke a contract. Compiled code
/// asks for it only when its test of the contracts failed, so a segment always
/// breaks one.
#[unsafe(no_mangle)]
#[allow(clippy::not_unsafe_ptr_arg_deref)]
pub extern "C" fn fz_construction_failure_message(process: *mut Process, segments_ref: u64) -> u64 {
    let mut passed_segments = Vec::new();
    let mut list = AnyValueRef::from_raw_word(segments_ref).expect("fz_construction_failure_message: a list ref");
    while !list.is_empty_list() {
        let head = list_head_ref(list).expect("fz_construction_failure_message: a list head");
        passed_segments.push(passed(process, head.raw_word()));
        list = list_tail_ref(list).expect("fz_construction_failure_message: a list tail");
    }
    let segments: Vec<Segment> = passed_segments.iter().map(|passed| passed.segment).collect();
    let (index, breach) = first_breach(&segments)
        .expect("fz_construction_failure_message: the compiled test failed, so a segment breaks its contract");
    let failed = &passed_segments[index];
    let message = construction_message(
        index,
        failed.segment.ty,
        breach,
        &render_value(process, failed.value),
        &render_value(process, failed.size),
    );
    let process = unsafe { &mut *process };
    process
        .alloc_bitstring(message.as_bytes(), 8 * message.len() as u64)
        .ref_word()
        .raw_word()
}

#[cfg(test)]
#[path = "construction_failure_test.rs"]
mod construction_failure_test;
