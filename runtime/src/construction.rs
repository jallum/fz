//! Building a binary from its segments: every segment is sized first, the
//! result is allocated once, and each segment is written once into it.
//!
//! A construction hands the runtime one array of [`FzBsField`] and gets the
//! binary back. `Segment` is what a field means once its value and size are
//! known; [`size_in_bits`] adds the segments up and [`fill`] writes them from
//! a [`BitSink`]'s position onward, so a result that continues an existing
//! buffer needs only a sink that starts after what the buffer holds.

use crate::bits::Bin;
use crate::bitstr::{BitSink, BitType, apply_endian_for_write, encode_utf8, encode_utf16, encode_utf32};
use crate::ir_runtime::{decode_bit_type, decode_bs_field_spec, decode_endian};
use crate::process::Process;
use std::slice::from_raw_parts;

/// One segment of a construction as the compiled code or the interpreter
/// hands it over. `spec` is the segment's `fz_bs_field_spec` (type, whether a
/// size is written, unit, endianness). `size` is the written size in units,
/// meaningful when the spec says one is present. `value` is the raw integer
/// for an integer or utf segment, the IEEE 754 bits of an f64 for a float
/// segment, and the tagged word of the bitstring for a binary or bits segment.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct FzBsField {
    pub spec: u64,
    pub size: u64,
    pub value: u64,
}

/// A segment with its value and size resolved: the bits it contributes and
/// where they come from.
enum Segment<'a> {
    /// The low `bits` bits of `word`, most significant first.
    Word { word: u64, bits: u32 },
    /// A scalar value's encoding, whole bytes.
    Encoded { bytes: [u8; 4], len: usize },
    /// The first `bits` bits of a bitstring's bytes.
    Bits { bytes: &'a [u8], bits: u64 },
}

impl Segment<'_> {
    fn of(field: &FzBsField) -> Self {
        let (ty_tag, size_present, unit, endian_tag, _, _) = decode_bs_field_spec(field.spec);
        let ty = decode_bit_type(ty_tag);
        let size = (size_present != 0).then_some(field.size);
        let unit = unit as u64;
        let endian = decode_endian(endian_tag);
        match ty {
            BitType::Integer => {
                let bits = size.unwrap_or(8) * unit;
                assert!(bits <= 64, "integer field too wide: {bits}");
                let masked = if bits < 64 {
                    field.value & ((1u64 << bits) - 1)
                } else {
                    field.value
                };
                Segment::Word {
                    word: apply_endian_for_write(masked, bits as u32, endian),
                    bits: bits as u32,
                }
            }
            BitType::Float => {
                let bits = size.unwrap_or(64) * unit;
                let value = f64::from_bits(field.value);
                let word = match bits {
                    16 => f64_to_half_bits(value) as u64,
                    32 => (value as f32).to_bits() as u64,
                    64 => value.to_bits(),
                    _ => panic!("float bit field size must be 16, 32 or 64, got {bits}"),
                };
                Segment::Word {
                    word: apply_endian_for_write(word, bits as u32, endian),
                    bits: bits as u32,
                }
            }
            BitType::Utf8 | BitType::Utf16 | BitType::Utf32 => {
                let scalar = field.value as u32;
                let encoded = match ty {
                    BitType::Utf8 => encode_utf8(scalar),
                    BitType::Utf16 => encode_utf16(scalar, endian),
                    _ => encode_utf32(scalar, endian),
                };
                let encoded =
                    encoded.expect("a construction's check passes only a Unicode scalar value to a utf segment");
                Segment::Encoded {
                    bytes: encoded.bytes,
                    len: encoded.len,
                }
            }
            BitType::Binary | BitType::Bits => {
                let source = unsafe { Bin::of_binary(field.value) };
                let source_bits = source.bit_len();
                let bits = size.map_or(source_bits, |n| n * unit);
                assert!(
                    bits <= source_bits,
                    "a construction's check passes only a bitstring as long as its segment"
                );
                // SAFETY: the source is a live bitstring and these are the bytes that hold its bits.
                let bytes = unsafe { from_raw_parts(source.ptr(), source_bits.div_ceil(8) as usize) };
                Segment::Bits { bytes, bits }
            }
        }
    }

    fn bit_len(&self) -> u64 {
        match self {
            Segment::Word { bits, .. } => *bits as u64,
            Segment::Encoded { len, .. } => *len as u64 * 8,
            Segment::Bits { bits, .. } => *bits,
        }
    }

    fn write(&self, sink: &mut BitSink<'_>) {
        match self {
            Segment::Word { word, bits } => sink.write_bits(*word, *bits),
            Segment::Encoded { bytes, len } => sink.write_bytes(&bytes[..*len]),
            Segment::Bits { bytes, bits } => sink.write_bit_range(bytes, 0, *bits),
        }
    }
}

/// The bits the segments add up to.
pub fn size_in_bits(fields: &[FzBsField]) -> u64 {
    fields.iter().map(|field| Segment::of(field).bit_len()).sum()
}

/// Write every segment, in order, from the sink's position.
pub fn fill(fields: &[FzBsField], sink: &mut BitSink<'_>) {
    for field in fields {
        Segment::of(field).write(sink);
    }
}

/// The binary the segments spell, on `process`'s heap: sized from the
/// segments, allocated once, written once.
pub fn build(process: &mut Process, fields: &[FzBsField]) -> u64 {
    let bit_len = size_in_bits(fields);
    let byte_len = bit_len.div_ceil(8) as usize;
    let value = process.alloc_bitstring_with(byte_len, bit_len, |dest| fill(fields, &mut BitSink::new(dest)));
    value.ref_word().raw_word()
}

/// The IEEE 754 binary16 bits nearest `value`, ties to even; a value past the
/// largest finite half is infinite, as the BEAM encodes it.
pub fn f64_to_half_bits(value: f64) -> u16 {
    let bits = value.to_bits();
    let sign = ((bits >> 63) as u16) << 15;
    let exponent = ((bits >> 52) & 0x7ff) as i32;
    let fraction = bits & ((1u64 << 52) - 1);
    const INFINITY: u16 = 0x7c00;
    if exponent == 0x7ff {
        return sign | if fraction == 0 { INFINITY } else { 0x7e00 };
    }
    if exponent == 0 {
        return sign;
    }
    let unbiased = exponent - 1023;
    if unbiased > 15 {
        return sign | INFINITY;
    }
    let (kept, dropped, dropped_bits) = if unbiased >= -14 {
        let kept = (((unbiased + 15) as u64) << 10) | (fraction >> 42);
        (kept, fraction & ((1u64 << 42) - 1), 42)
    } else {
        // A subnormal half counts in units of 2^-24.
        let shift = (28 - unbiased) as u32;
        if shift >= 64 {
            return sign;
        }
        let significand = (1u64 << 52) | fraction;
        (significand >> shift, significand & ((1u64 << shift) - 1), shift)
    };
    let halfway = 1u64 << (dropped_bits - 1);
    let rounded_up = dropped > halfway || (dropped == halfway && kept & 1 == 1);
    // A carry out of the fraction lands in the exponent, which is the right answer.
    sign | (kept + rounded_up as u64) as u16
}

#[cfg(test)]
#[path = "construction_test.rs"]
mod construction_test;
