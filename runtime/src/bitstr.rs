//! Bit-level primitives for fz bitstrings. JIT/interp/AOT-shared.
//!
//! The Value-aware surface (encode_field, encode_integer, match_bitstring,
//! etc.) that the AST evaluator uses lives in the fz binary's own
//! src/bitstr.rs and imports primitives from here.

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
// Bit-level writer
// ----------------------------------------------------------------------

pub struct BitWriter {
    pub bytes: Vec<u8>,
    pub bit_len: usize,
}

impl BitWriter {
    pub fn new() -> Self {
        Self {
            bytes: Vec::new(),
            bit_len: 0,
        }
    }

    /// Append `n` bits of `value`, with the high (MSB) `n` bits of `value`
    /// going first. `n` ≤ 64.
    pub fn write_bits(&mut self, value: u64, n: usize) {
        for i in 0..n {
            let bit = (value >> (n - 1 - i)) & 1;
            self.append_bit(bit as u8);
        }
    }

    pub fn append_bit(&mut self, b: u8) {
        let byte_idx = self.bit_len / 8;
        let bit_idx = 7 - (self.bit_len % 8);
        if byte_idx >= self.bytes.len() {
            self.bytes.push(0);
        }
        if b != 0 {
            self.bytes[byte_idx] |= 1 << bit_idx;
        }
        self.bit_len += 1;
    }

    pub fn write_bytes(&mut self, b: &[u8]) {
        if self.bit_len.is_multiple_of(8) {
            self.bytes.extend_from_slice(b);
            self.bit_len += b.len() * 8;
        } else {
            for byte in b {
                self.write_bits(*byte as u64, 8);
            }
        }
    }
}

impl Default for BitWriter {
    fn default() -> Self {
        Self::new()
    }
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

pub fn encode_utf8(cp: u32) -> Option<Vec<u8>> {
    if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) {
        return None;
    }
    Some(if cp < 0x80 {
        vec![cp as u8]
    } else if cp < 0x800 {
        vec![0xc0 | (cp >> 6) as u8, 0x80 | (cp & 0x3f) as u8]
    } else if cp < 0x10000 {
        vec![
            0xe0 | (cp >> 12) as u8,
            0x80 | ((cp >> 6) & 0x3f) as u8,
            0x80 | (cp & 0x3f) as u8,
        ]
    } else {
        vec![
            0xf0 | (cp >> 18) as u8,
            0x80 | ((cp >> 12) & 0x3f) as u8,
            0x80 | ((cp >> 6) & 0x3f) as u8,
            0x80 | (cp & 0x3f) as u8,
        ]
    })
}

pub fn decode_utf8(reader: &mut BitReader) -> Option<u32> {
    if !reader.pos.is_multiple_of(8) {
        return None;
    }
    let b0 = reader.read_bits(8)? as u32;
    if b0 < 0x80 {
        return Some(b0);
    }
    let (extras, mask) = if b0 & 0xe0 == 0xc0 {
        (1, 0x1f)
    } else if b0 & 0xf0 == 0xe0 {
        (2, 0x0f)
    } else if b0 & 0xf8 == 0xf0 {
        (3, 0x07)
    } else {
        return None;
    };
    let mut cp = b0 & mask;
    for _ in 0..extras {
        let b = reader.read_bits(8)? as u32;
        if b & 0xc0 != 0x80 {
            return None;
        }
        cp = (cp << 6) | (b & 0x3f);
    }
    Some(cp)
}

pub fn encode_utf16(cp: u32, endian: Endian) -> Option<Vec<u8>> {
    if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) {
        return None;
    }
    let units = if cp < 0x10000 {
        vec![cp as u16]
    } else {
        let v = cp - 0x10000;
        vec![0xd800 | (v >> 10) as u16, 0xdc00 | (v & 0x3ff) as u16]
    };
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    let mut out = Vec::with_capacity(units.len() * 2);
    for u in units {
        if little {
            out.push((u & 0xff) as u8);
            out.push((u >> 8) as u8);
        } else {
            out.push((u >> 8) as u8);
            out.push((u & 0xff) as u8);
        }
    }
    Some(out)
}

pub fn decode_utf16(reader: &mut BitReader, endian: Endian) -> Option<u32> {
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    let read_u16 = |r: &mut BitReader<'_>| -> Option<u16> {
        let lo = r.read_bits(8)? as u16;
        let hi = r.read_bits(8)? as u16;
        Some(if little { (hi << 8) | lo } else { (lo << 8) | hi })
    };
    let u1 = read_u16(reader)?;
    if !(0xd800..=0xdbff).contains(&u1) {
        return Some(u1 as u32);
    }
    let u2 = read_u16(reader)?;
    if !(0xdc00..=0xdfff).contains(&u2) {
        return None;
    }
    Some(0x10000 + (((u1 as u32 & 0x3ff) << 10) | (u2 as u32 & 0x3ff)))
}

pub fn encode_utf32(cp: u32, endian: Endian) -> Option<Vec<u8>> {
    if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) {
        return None;
    }
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    Some(if little {
        vec![
            (cp & 0xff) as u8,
            ((cp >> 8) & 0xff) as u8,
            ((cp >> 16) & 0xff) as u8,
            ((cp >> 24) & 0xff) as u8,
        ]
    } else {
        vec![
            ((cp >> 24) & 0xff) as u8,
            ((cp >> 16) & 0xff) as u8,
            ((cp >> 8) & 0xff) as u8,
            (cp & 0xff) as u8,
        ]
    })
}

pub fn decode_utf32(reader: &mut BitReader, endian: Endian) -> Option<u32> {
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    let b0 = reader.read_bits(8)? as u32;
    let b1 = reader.read_bits(8)? as u32;
    let b2 = reader.read_bits(8)? as u32;
    let b3 = reader.read_bits(8)? as u32;
    Some(if little {
        (b3 << 24) | (b2 << 16) | (b1 << 8) | b0
    } else {
        (b0 << 24) | (b1 << 16) | (b2 << 8) | b3
    })
}
