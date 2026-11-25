//! The bit codec for fz bitstrings, shared by the interpreter, JIT and AOT
//! paths: `BitSink` and `BitReader` move bits and bytes, `Endian` and the
//! `apply_endian_*` and `sign_extend` helpers fix a field's byte order and
//! sign, and the UTF-8, UTF-16 and UTF-32 functions encode and decode code
//! points.

use std::mem::MaybeUninit;
use std::ptr::copy_nonoverlapping;

/// Field-type tag, matches fz's bitstring expression syntax.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BitType {
    Integer,
    Float,
    Binary,
    Bits,
    Utf8,
    Utf16,
    Utf32,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Endian {
    Big,
    Little,
    Native,
}

// ----------------------------------------------------------------------
// Bit-level sink
// ----------------------------------------------------------------------

/// A write position in a destination whose bytes are not yet written. Bits go
/// in most significant first. A byte is first written when the position
/// reaches it, so writing in order leaves every byte written, and the unused
/// low bits of a final partial byte zero.
pub struct BitSink<'a> {
    dest: &'a mut [MaybeUninit<u8>],
    pos: usize,
}

impl<'a> BitSink<'a> {
    pub fn new(dest: &'a mut [MaybeUninit<u8>]) -> Self {
        Self::starting_at(dest, 0)
    }

    /// A sink that continues after the first `bit_pos` bits, which are
    /// already written.
    pub fn starting_at(dest: &'a mut [MaybeUninit<u8>], bit_pos: usize) -> Self {
        Self { dest, pos: bit_pos }
    }

    pub fn bit_pos(&self) -> usize {
        self.pos
    }

    /// Write the low `n` bits of `value`, `n` <= 64.
    pub fn write_bits(&mut self, value: u64, n: u32) {
        let mut left = n;
        while left > 0 {
            let used = (self.pos % 8) as u32;
            let take = left.min(8 - used);
            let chunk = ((value >> (left - take)) & ((1u64 << take) - 1)) as u8;
            let slot = &mut self.dest[self.pos / 8];
            if used == 0 {
                slot.write(chunk << (8 - take));
            } else {
                // SAFETY: the byte was first written when the position entered it.
                let written = unsafe { slot.assume_init() };
                slot.write(written | (chunk << (8 - used - take)));
            }
            self.pos += take as usize;
            left -= take;
        }
    }

    pub fn write_bytes(&mut self, bytes: &[u8]) {
        if self.pos.is_multiple_of(8) {
            let at = self.pos / 8;
            // SAFETY: u8 and MaybeUninit<u8> have one layout, and the ranges are distinct objects.
            unsafe {
                copy_nonoverlapping(
                    bytes.as_ptr(),
                    self.dest[at..at + bytes.len()].as_mut_ptr().cast::<u8>(),
                    bytes.len(),
                )
            };
            self.pos += bytes.len() * 8;
        } else {
            for byte in bytes {
                self.write_bits(*byte as u64, 8);
            }
        }
    }

    /// Write the `n` bits of `source` that start at bit `start`.
    pub fn write_bit_range(&mut self, source: &[u8], start: u64, n: u64) {
        let whole = (n / 8) as usize;
        if start.is_multiple_of(8) {
            let first = (start / 8) as usize;
            self.write_bytes(&source[first..first + whole]);
        } else {
            for index in 0..whole as u64 {
                self.write_bits(read_bits_at(source, start + index * 8, 8), 8);
            }
        }
        let tail = (n % 8) as u32;
        if tail > 0 {
            self.write_bits(read_bits_at(source, start + whole as u64 * 8, tail), tail);
        }
    }
}

/// The `n` bits (at most 8) of `bytes` starting at bit `start`.
fn read_bits_at(bytes: &[u8], start: u64, n: u32) -> u64 {
    let index = (start / 8) as usize;
    let used = (start % 8) as u32;
    let two = (bytes[index] as u16) << 8 | bytes.get(index + 1).copied().unwrap_or(0) as u16;
    ((two >> (16 - used - n)) & ((1u16 << n) - 1)) as u64
}

// ----------------------------------------------------------------------
// Bit-level reader (over raw bytes)
// ----------------------------------------------------------------------

pub struct BitReader<'a> {
    pub bytes: &'a [u8],
    pub bit_len: usize,
    pub pos: usize, // current bit position
}

impl<'a> BitReader<'a> {
    pub fn remaining(&self) -> usize {
        self.bit_len - self.pos
    }

    /// Read `n` bits (≤ 64) as an unsigned integer in big-endian bit order.
    pub fn read_bits(&mut self, n: usize) -> Option<u64> {
        if self.remaining() < n {
            return None;
        }
        let mut out: u64 = 0;
        for _ in 0..n {
            let bit = self.read_bit()?;
            out = (out << 1) | (bit as u64);
        }
        Some(out)
    }

    pub fn read_bit(&mut self) -> Option<u8> {
        if self.pos >= self.bit_len {
            return None;
        }
        let byte = self.bytes[self.pos / 8];
        let bit = (byte >> (7 - (self.pos % 8))) & 1;
        self.pos += 1;
        Some(bit)
    }
}

// ----------------------------------------------------------------------
// Endianness / signedness helpers
// ----------------------------------------------------------------------

pub fn host_is_little_endian() -> bool {
    cfg!(target_endian = "little")
}

pub fn apply_endian_for_write(value: u64, total_bits: u32, endian: Endian) -> u64 {
    let n = total_bits as usize;
    if n == 0 || n > 64 {
        return value;
    }
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    if !little {
        return value;
    }
    if !n.is_multiple_of(8) {
        return value;
    }
    let bytes = n / 8;
    let mut acc = 0u64;
    for i in 0..bytes {
        let b = (value >> (i * 8)) & 0xff;
        acc |= b << ((bytes - 1 - i) * 8);
    }
    acc
}

pub fn apply_endian_for_read(value: u64, total_bits: u32, endian: Endian) -> u64 {
    apply_endian_for_write(value, total_bits, endian)
}

pub fn sign_extend(value: u64, total_bits: u32) -> i64 {
    if total_bits == 0 || total_bits >= 64 {
        return value as i64;
    }
    let mask = 1u64 << (total_bits - 1);
    if value & mask != 0 {
        let upper = !0u64 << total_bits;
        (value | upper) as i64
    } else {
        value as i64
    }
}

// ----------------------------------------------------------------------
// UTF-8 / UTF-16 / UTF-32 encoding/decoding
// ----------------------------------------------------------------------

/// A Unicode scalar value's encoding: at most four bytes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Encoded {
    pub bytes: [u8; 4],
    pub len: usize,
}

impl Encoded {
    pub fn as_slice(&self) -> &[u8] {
        &self.bytes[..self.len]
    }
}

fn is_scalar_value(cp: u32) -> bool {
    cp <= 0x10ffff && !(0xd800..=0xdfff).contains(&cp)
}

fn encoded(bytes: &[u8]) -> Encoded {
    let mut out = Encoded {
        bytes: [0; 4],
        len: bytes.len(),
    };
    out.bytes[..bytes.len()].copy_from_slice(bytes);
    out
}

pub fn encode_utf8(cp: u32) -> Option<Encoded> {
    if !is_scalar_value(cp) {
        return None;
    }
    let mut buffer = [0u8; 4];
    Some(encoded(char::from_u32(cp)?.encode_utf8(&mut buffer).as_bytes()))
}

pub fn encode_utf16(cp: u32, endian: Endian) -> Option<Encoded> {
    if !is_scalar_value(cp) {
        return None;
    }
    let mut units = [0u16; 2];
    let units = char::from_u32(cp)?.encode_utf16(&mut units);
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    let mut out = Encoded {
        bytes: [0; 4],
        len: units.len() * 2,
    };
    for (index, unit) in units.iter().enumerate() {
        let pair = if little { unit.to_le_bytes() } else { unit.to_be_bytes() };
        out.bytes[index * 2..index * 2 + 2].copy_from_slice(&pair);
    }
    Some(out)
}

pub fn encode_utf32(cp: u32, endian: Endian) -> Option<Encoded> {
    if !is_scalar_value(cp) {
        return None;
    }
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    Some(Encoded {
        bytes: if little { cp.to_le_bytes() } else { cp.to_be_bytes() },
        len: 4,
    })
}

#[cfg(test)]
#[path = "bitstr_test.rs"]
mod bitstr_test;
