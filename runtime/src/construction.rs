//! Building a binary from its segments: every segment is sized first, the
//! result is allocated once, and each segment is written once into it.
//!
//! A construction hands the runtime one array of [`FzBsField`] and gets the
//! binary back. `Segment` is what a field means once its value and size are
//! known. Each field is resolved to its segment once; [`size_in_bits`] adds the
//! segments up, and a [`BitSink`] writes each one in order. A construction that
//! starts with an unsized binary continues that binary: [`build`] appends the
//! rest to it.

use crate::bits::{Bin, BinView};
use crate::bitstr::{BitSink, BitType, Endian, apply_endian_for_write, encode_utf8, encode_utf16, encode_utf32};
use crate::ir_runtime::decode_bs_field_spec;
use crate::process::Process;
use smallvec::SmallVec;
use std::mem::MaybeUninit;
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

/// What a segment's value is, once the caller has read it: the raw word of an
/// integer, a utf code point or the IEEE 754 bits of a float, or the bytes and
/// bit length of a bitstring.
enum Operand<'a> {
    Word(u64),
    Bits { bytes: &'a [u8], bit_len: u64 },
}

impl<'a> Segment<'a> {
    /// The segment a field of a running construction describes.
    fn of(field: &FzBsField) -> Self {
        let (ty_tag, ..) = decode_bs_field_spec(field.spec);
        let operand = match BitType::from_tag(ty_tag) {
            BitType::Binary | BitType::Bits => {
                let source = unsafe { Bin::of_binary(field.value) };
                let bit_len = source.bit_len();
                // SAFETY: the source is a live bitstring and these are the bytes that hold its bits.
                let bytes = unsafe { from_raw_parts(source.ptr(), bit_len.div_ceil(8) as usize) };
                Operand::Bits { bytes, bit_len }
            }
            _ => Operand::Word(field.value),
        };
        Self::resolve(field.spec, field.size, operand).unwrap_or_else(|refusal| panic!("{refusal}"))
    }

    /// The segment `spec` describes over `operand`, or why the runtime refuses
    /// it. `size` is meaningful when the spec says one is present. This is the
    /// one definition of how a field is encoded: a running construction and the
    /// compiler's folding of constants both read it.
    fn resolve(spec: u64, size: u64, operand: Operand<'a>) -> Result<Self, String> {
        let (ty_tag, size_present, unit, endian_tag, _, _) = decode_bs_field_spec(spec);
        let ty = BitType::from_tag(ty_tag);
        let size = (size_present != 0).then_some(size);
        let unit = unit as u64;
        let endian = Endian::from_tag(endian_tag);
        match (ty, operand) {
            (BitType::Integer, Operand::Word(value)) => {
                let bits = size.unwrap_or(8) * unit;
                if bits > 64 {
                    return Err(format!("integer field too wide: {bits}"));
                }
                let masked = if bits < 64 { value & ((1u64 << bits) - 1) } else { value };
                Ok(Segment::Word {
                    word: apply_endian_for_write(masked, bits as u32, endian),
                    bits: bits as u32,
                })
            }
            (BitType::Float, Operand::Word(value)) => {
                let bits = size.unwrap_or(64) * unit;
                let value = f64::from_bits(value);
                let word = match bits {
                    16 => f64_to_half_bits(value) as u64,
                    32 => (value as f32).to_bits() as u64,
                    64 => value.to_bits(),
                    _ => return Err(format!("float bit field size must be 16, 32 or 64, got {bits}")),
                };
                Ok(Segment::Word {
                    word: apply_endian_for_write(word, bits as u32, endian),
                    bits: bits as u32,
                })
            }
            (BitType::Utf8 | BitType::Utf16 | BitType::Utf32, Operand::Word(value)) => {
                let scalar = value as u32;
                let encoded = match ty {
                    BitType::Utf8 => encode_utf8(scalar),
                    BitType::Utf16 => encode_utf16(scalar, endian),
                    _ => encode_utf32(scalar, endian),
                };
                let encoded = encoded.ok_or_else(|| format!("{scalar:#x} is not a Unicode scalar value"))?;
                Ok(Segment::Encoded {
                    bytes: encoded.bytes,
                    len: encoded.len,
                })
            }
            (BitType::Binary | BitType::Bits, Operand::Bits { bytes, bit_len }) => {
                let bits = size.map_or(bit_len, |n| n * unit);
                if bits > bit_len {
                    return Err(format!(
                        "a segment of {bits} bits is longer than its {bit_len}-bit source"
                    ));
                }
                Ok(Segment::Bits { bytes, bits })
            }
            _ => Err("a segment's operand does not suit its type".to_string()),
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

/// A construction's segments, each resolved once. Most constructions have a
/// handful of segments, which stay on the stack.
type Segments<'a> = SmallVec<[Segment<'a>; 8]>;

fn resolve(fields: &[FzBsField]) -> Segments<'_> {
    fields.iter().map(Segment::of).collect()
}

fn bits_of(segments: &[Segment<'_>]) -> u64 {
    segments.iter().map(Segment::bit_len).sum()
}

fn write_all(segments: &[Segment<'_>], sink: &mut BitSink<'_>) {
    for segment in segments {
        segment.write(sink);
    }
}

/// The bits the segments add up to.
pub fn size_in_bits(fields: &[FzBsField]) -> u64 {
    bits_of(&resolve(fields))
}

/// Write every segment, in order, from the sink's position.
#[cfg(test)]
fn fill(fields: &[FzBsField], sink: &mut BitSink<'_>) {
    write_all(&resolve(fields), sink);
}

/// A segment's value as the compiler knows it before the program runs.
#[derive(Clone, Copy, Debug)]
pub enum ConstantValue<'a> {
    /// An integer, or a utf segment's code point.
    Word(u64),
    Float(f64),
    /// The bytes of a binary or bits segment.
    Bytes(&'a [u8]),
}

/// A segment of a construction whose value and size are known when the
/// program is compiled. `spec` and `size` are what `FzBsField` carries.
#[derive(Clone, Copy, Debug)]
pub struct ConstantField<'a> {
    pub spec: u64,
    pub size: u64,
    pub value: ConstantValue<'a>,
}

/// The bits constant segments spell: whole bytes, the last of which holds the
/// final bits from its high end and is zero after them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EncodedConstants {
    pub bytes: Vec<u8>,
    pub bit_len: u64,
}

/// The bits `fields` spell, written by the same segments a running
/// construction writes. A field the runtime would refuse is an error, so a
/// caller that folds constants leaves it to the construction to raise.
pub fn encode_constants(fields: &[ConstantField<'_>]) -> Result<EncodedConstants, String> {
    let segments = fields
        .iter()
        .map(|field| {
            let operand = match field.value {
                ConstantValue::Word(word) => Operand::Word(word),
                ConstantValue::Float(value) => Operand::Word(value.to_bits()),
                ConstantValue::Bytes(bytes) => Operand::Bits {
                    bytes,
                    bit_len: bytes.len() as u64 * 8,
                },
            };
            Segment::resolve(field.spec, field.size, operand)
        })
        .collect::<Result<Segments<'_>, _>>()?;
    let bit_len = bits_of(&segments);
    let mut buffer = vec![MaybeUninit::new(0u8); bit_len.div_ceil(8) as usize];
    write_all(&segments, &mut BitSink::new(&mut buffer));
    // SAFETY: every byte was initialised to zero before the sink wrote into it.
    let bytes = buffer.into_iter().map(|byte| unsafe { byte.assume_init() }).collect();
    Ok(EncodedConstants { bytes, bit_len })
}

/// The binary the segments spell, on `process`'s heap: sized from the
/// segments, allocated once, written once. A construction that starts with an
/// unsized binary of whole bytes is an append to it, through the heap's one
/// append.
pub fn build(process: &mut Process, fields: &[FzBsField]) -> u64 {
    let segments = resolve(fields);
    if let Some(append) = Append::of(fields, &segments) {
        return append.build(process);
    }
    let bit_len = bits_of(&segments);
    let byte_len = bit_len.div_ceil(8) as usize;
    let value = process.alloc_bitstring_with(byte_len, bit_len, |dest| write_all(&segments, &mut BitSink::new(dest)));
    value.ref_word().raw_word()
}

/// A construction that continues its first segment: an unsized binary of
/// whole bytes, which is byte-aligned because it is first, followed by
/// segments that add up to whole bytes, so the result is a whole-byte binary.
struct Append<'s, 'a> {
    leading: u64,
    rest: &'s [Segment<'a>],
    rest_bytes: usize,
}

impl<'s, 'a> Append<'s, 'a> {
    /// The append `segments` make, or `None` for a construction built whole.
    fn of(fields: &[FzBsField], segments: &'s [Segment<'a>]) -> Option<Self> {
        let (leading, first) = fields.first().zip(segments.first())?;
        let rest = &segments[1..];
        let (ty_tag, size_present, unit, ..) = decode_bs_field_spec(leading.spec);
        let unsized_binary =
            BitType::from_tag(ty_tag) == BitType::Binary && size_present == 0 && unit.is_multiple_of(8);
        let Segment::Bits { bits, .. } = first else {
            return None;
        };
        let rest_bits = bits_of(rest);
        (unsized_binary && bits.is_multiple_of(8) && rest_bits.is_multiple_of(8)).then_some(Append {
            leading: leading.value,
            rest,
            rest_bytes: (rest_bits / 8) as usize,
        })
    }

    fn build(&self, process: &mut Process) -> u64 {
        extend(process, self.leading, self.rest_bytes, |dest| {
            write_all(self.rest, &mut BitSink::new(dest))
        })
    }
}

/// The binary `leading`, a live whole-byte binary, followed by `right_len`
/// bytes that `fill` writes, through the heap's one append: the leading bytes
/// stay where they are when their buffer can take the right side, and are
/// copied once otherwise.
fn extend(process: &mut Process, leading: u64, right_len: usize, fill: impl FnOnce(&mut [MaybeUninit<u8>])) -> u64 {
    let left = unsafe { Bin::of_binary(leading) }.bytes();
    let left_view = unsafe { BinView::of_binary(leading) };
    // SAFETY: `left` is the bytes of a live whole-byte binary, and a heap allocation does not move it.
    let value = unsafe { process.alloc_concatenation(left, left_view, right_len, fill) };
    value.ref_word().raw_word()
}

/// The binary `leading` followed by `right_len` bytes the caller writes, which
/// is `extend` with nothing written, and where those bytes start. Compiled code
/// appends a construction whose rest it can write itself this way, and writes
/// the rest at `rest`.
pub fn append_unfilled(process: &mut Process, leading: u64, right_len: usize) -> Appended {
    let mut rest = std::ptr::null_mut();
    let binary = extend(process, leading, right_len, |dest| rest = dest.as_mut_ptr().cast());
    Appended { binary, rest }
}

/// A binary an append made, and the first of the `right_len` bytes it left for
/// the caller to write. Two words, so both come back in registers.
#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct Appended {
    pub binary: u64,
    pub rest: *mut u8,
}

/// A whole-byte binary of `byte_len` bytes whose payload the caller writes,
/// allocated exactly as `build` allocates its result. Compiled code builds a
/// result too large to place inline this way and fills the buffer itself.
pub fn alloc_unfilled(process: &mut Process, byte_len: usize) -> u64 {
    let value = process.alloc_bitstring_with(byte_len, byte_len as u64 * 8, |_| {});
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
