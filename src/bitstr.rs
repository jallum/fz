//! Bitstring construction and pattern matching for fz.
//!
//! Surface syntax mirrors Elixir's bitstring expressions and patterns:
//!
//!     <<x::8, len::16, payload::binary-size(len), rest::binary>>
//!
//! Internally bitstrings are packed MSB-first within each byte (network /
//! big-endian byte order). Byte-aligned results are returned as
//! `Value::Vec(FzVec::U8(_))`; non-aligned ones as `Value::BitStr(_)`.

use crate::ast::*;
use crate::value::*;
use std::rc::Rc;

// ----------------------------------------------------------------------
// Encoding (bitstring expression → Value)
// ----------------------------------------------------------------------

pub fn encode_field(value: &Value, spec: &BitFieldSpec, env: &Env, writer: &mut BitWriter) -> Result<(), String> {
    let unit = spec.resolved_unit();
    let size = resolve_size(spec, env)?;
    match spec.ty {
        BitType::Integer => encode_integer(value, spec, size, unit, writer),
        BitType::Float   => encode_float(value, spec, size, unit, writer),
        BitType::Binary  => encode_binary(value, size, unit, writer),
        BitType::Bits    => encode_bits(value, size, unit, writer),
        BitType::Utf8    => {
            let cp = codepoint(value)?;
            let bytes = encode_utf8(cp).ok_or_else(|| format!("invalid codepoint: {}", cp))?;
            writer.write_bytes(&bytes); Ok(())
        }
        BitType::Utf16   => {
            let cp = codepoint(value)?;
            let bytes = encode_utf16(cp, spec.endian).ok_or_else(|| format!("invalid codepoint: {}", cp))?;
            writer.write_bytes(&bytes); Ok(())
        }
        BitType::Utf32   => {
            let cp = codepoint(value)?;
            let bytes = encode_utf32(cp, spec.endian).ok_or_else(|| format!("invalid codepoint: {}", cp))?;
            writer.write_bytes(&bytes); Ok(())
        }
    }
}

fn resolve_size(spec: &BitFieldSpec, env: &Env) -> Result<Option<u32>, String> {
    Ok(match &spec.size {
        Some(BitSize::Literal(n)) => Some(*n),
        Some(BitSize::Var(name)) => match env.lookup(name) {
            Some(Value::Int(n)) if n >= 0 => Some(n as u32),
            Some(other) => return Err(format!("size variable `{}` must be a non-negative int, got {}", name, other)),
            None => return Err(format!("size variable `{}` not bound", name)),
        },
        None => spec.default_size(),
    })
}

fn codepoint(v: &Value) -> Result<u32, String> {
    match v {
        Value::Int(n) if *n >= 0 && *n <= 0x10ffff => Ok(*n as u32),
        _ => Err(format!("expected codepoint (0..=0x10ffff), got {}", v)),
    }
}

fn encode_integer(value: &Value, spec: &BitFieldSpec, size: Option<u32>, unit: u32, writer: &mut BitWriter) -> Result<(), String> {
    let n = match value {
        Value::Int(n) => *n,
        _ => return Err(format!("integer field expects int, got {}", value)),
    };
    let total = size.unwrap_or(8) * unit;
    if total > 64 { return Err(format!("integer field too wide: {} bits", total)); }
    let masked = if total < 64 { (n as u64) & ((1u64 << total) - 1) } else { n as u64 };
    let bswap = apply_endian_for_write(masked, total, spec.endian);
    writer.write_bits(bswap, total as usize);
    Ok(())
}

fn encode_float(value: &Value, spec: &BitFieldSpec, size: Option<u32>, unit: u32, writer: &mut BitWriter) -> Result<(), String> {
    let f = match value {
        Value::Float(f) => *f,
        Value::Int(n) => *n as f64,
        _ => return Err(format!("float field expects number, got {}", value)),
    };
    let total = size.unwrap_or(64) * unit;
    let bits = match total {
        32 => (f as f32).to_bits() as u64,
        64 => f.to_bits(),
        _  => return Err(format!("float field size must be 32 or 64, got {}", total)),
    };
    let bswap = apply_endian_for_write(bits, total, spec.endian);
    writer.write_bits(bswap, total as usize);
    Ok(())
}

fn encode_binary(value: &Value, size: Option<u32>, unit: u32, writer: &mut BitWriter) -> Result<(), String> {
    let bytes_rc = match value {
        Value::Vec(FzVec::U8(b)) => b.clone(),
        _ => return Err(format!("binary field expects byte-vector, got {}", value)),
    };
    let total_bits = match size {
        None => bytes_rc.len() * 8,
        Some(n) => (n * unit) as usize,
    };
    if total_bits > bytes_rc.len() * 8 {
        return Err(format!("binary field size {} exceeds available {} bits", total_bits, bytes_rc.len() * 8));
    }
    if total_bits % 8 == 0 && writer.bit_len % 8 == 0 {
        writer.bytes.extend_from_slice(&bytes_rc[..total_bits / 8]);
        writer.bit_len += total_bits;
    } else {
        let mut r = BitReader { bytes: &bytes_rc, bit_len: bytes_rc.len() * 8, pos: 0 };
        for _ in 0..total_bits {
            writer.append_bit(r.read_bit().unwrap());
        }
    }
    Ok(())
}

fn encode_bits(value: &Value, size: Option<u32>, unit: u32, writer: &mut BitWriter) -> Result<(), String> {
    let (bytes, bit_len) = match value {
        Value::Vec(FzVec::U8(b)) => (b.as_ref().clone(), b.len() * 8),
        Value::BitStr(bs) => (bs.bytes.clone(), bs.bit_len),
        _ => return Err(format!("bits field expects bitstring, got {}", value)),
    };
    let total_bits = match size {
        None => bit_len,
        Some(n) => (n * unit) as usize,
    };
    if total_bits > bit_len {
        return Err(format!("bits field size {} exceeds available {} bits", total_bits, bit_len));
    }
    let mut r = BitReader { bytes: &bytes, bit_len, pos: 0 };
    for _ in 0..total_bits {
        writer.append_bit(r.read_bit().unwrap());
    }
    Ok(())
}

// ----------------------------------------------------------------------
// Pattern matching (Pattern::Bitstring against a Value)
// ----------------------------------------------------------------------

pub fn match_bitstring(fields: &[BitField<crate::ast::Spanned<Pattern>>], value: &Value, env: &Env) -> bool {
    let Some(mut reader) = BitReader::from_value(value) else { return false; };
    for (i, f) in fields.iter().enumerate() {
        let unit = f.spec.resolved_unit();
        let size = match resolve_size(&f.spec, env) {
            Ok(s) => s,
            Err(_) => return false,
        };
        let is_last = i + 1 == fields.len();
        let extracted: Value = match f.spec.ty {
            BitType::Integer => {
                let total = size.unwrap_or(8) * unit;
                if total > 64 { return false; }
                let raw = match reader.read_bits(total as usize) { Some(v) => v, None => return false };
                let raw = apply_endian_for_read(raw, total, f.spec.endian);
                let n = if f.spec.signed { sign_extend(raw, total) } else { raw as i64 };
                Value::Int(n)
            }
            BitType::Float => {
                let total = size.unwrap_or(64) * unit;
                let raw = match reader.read_bits(total as usize) { Some(v) => v, None => return false };
                let raw = apply_endian_for_read(raw, total, f.spec.endian);
                let f64v = match total {
                    32 => f32::from_bits(raw as u32) as f64,
                    64 => f64::from_bits(raw),
                    _ => return false,
                };
                Value::Float(f64v)
            }
            BitType::Binary => {
                let n_bits = match size {
                    None => {
                        if !is_last { return false; }
                        reader.remaining()
                    }
                    Some(n) => (n * unit) as usize,
                };
                if n_bits % 8 != 0 { return false; }
                match reader.take_bits(n_bits) { Some(v) => v, None => return false }
            }
            BitType::Bits => {
                let n_bits = match size {
                    None => {
                        if !is_last { return false; }
                        reader.remaining()
                    }
                    Some(n) => (n * unit) as usize,
                };
                match reader.take_bits(n_bits) { Some(v) => v, None => return false }
            }
            BitType::Utf8  => match decode_utf8(&mut reader) { Some(c) => Value::Int(c as i64), None => return false },
            BitType::Utf16 => match decode_utf16(&mut reader, f.spec.endian) { Some(c) => Value::Int(c as i64), None => return false },
            BitType::Utf32 => match decode_utf32(&mut reader, f.spec.endian) { Some(c) => Value::Int(c as i64), None => return false },
        };
        if !match_pattern(&f.value.node, &extracted, env) { return false; }
    }
    reader.remaining() == 0
}

// ----------------------------------------------------------------------
// Bit-level writer
// ----------------------------------------------------------------------

pub struct BitWriter {
    pub bytes: Vec<u8>,
    pub bit_len: usize,
}

impl BitWriter {
    pub fn new() -> Self { Self { bytes: Vec::new(), bit_len: 0 } }

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
        if byte_idx >= self.bytes.len() { self.bytes.push(0); }
        if b != 0 { self.bytes[byte_idx] |= 1 << bit_idx; }
        self.bit_len += 1;
    }

    pub fn write_bytes(&mut self, b: &[u8]) {
        if self.bit_len % 8 == 0 {
            self.bytes.extend_from_slice(b);
            self.bit_len += b.len() * 8;
        } else {
            for byte in b {
                self.write_bits(*byte as u64, 8);
            }
        }
    }

    pub fn finalize(self) -> Value {
        if self.bit_len % 8 == 0 {
            Value::Vec(FzVec::U8(Rc::new(self.bytes)))
        } else {
            Value::BitStr(Rc::new(BitString { bytes: self.bytes, bit_len: self.bit_len }))
        }
    }
}

// ----------------------------------------------------------------------
// Bit-level reader (over a Value that's a binary or bitstring)
// ----------------------------------------------------------------------

pub struct BitReader<'a> {
    pub bytes: &'a [u8],
    pub bit_len: usize,
    pub pos: usize, // current bit position
}

impl<'a> BitReader<'a> {
    pub fn from_value(v: &'a Value) -> Option<BitReader<'a>> {
        match v {
            Value::Vec(FzVec::U8(rc)) => Some(BitReader {
                bytes: rc.as_slice(),
                bit_len: rc.len() * 8,
                pos: 0,
            }),
            Value::BitStr(bs) => Some(BitReader {
                bytes: bs.bytes.as_slice(),
                bit_len: bs.bit_len,
                pos: 0,
            }),
            _ => None,
        }
    }

    pub fn remaining(&self) -> usize { self.bit_len - self.pos }

    /// Read `n` bits (≤ 64) as an unsigned integer in big-endian bit order.
    pub fn read_bits(&mut self, n: usize) -> Option<u64> {
        if self.remaining() < n { return None; }
        let mut out: u64 = 0;
        for _ in 0..n {
            let bit = self.read_bit()?;
            out = (out << 1) | (bit as u64);
        }
        Some(out)
    }

    pub fn read_bit(&mut self) -> Option<u8> {
        if self.pos >= self.bit_len { return None; }
        let byte = self.bytes[self.pos / 8];
        let bit = (byte >> (7 - (self.pos % 8))) & 1;
        self.pos += 1;
        Some(bit)
    }

    /// Take `n_bits` bits as a fresh bitstring/binary value.
    pub fn take_bits(&mut self, n_bits: usize) -> Option<Value> {
        if self.remaining() < n_bits { return None; }
        let mut w = BitWriter::new();
        for _ in 0..n_bits {
            w.append_bit(self.read_bit()?);
        }
        Some(w.finalize())
    }

    pub fn take_rest(&mut self) -> Value {
        let n = self.remaining();
        self.take_bits(n).expect("remaining bits available")
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
    if n == 0 || n > 64 { return value; }
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    if !little { return value; }
    // Reverse byte order. Total bits must be a byte multiple for byte-swap to
    // be meaningful; if not, fall back to MSB-first big-endian (Elixir's
    // behavior is documented as "endianness on integers requires byte-aligned size").
    if n % 8 != 0 { return value; }
    let bytes = n / 8;
    let mut acc = 0u64;
    for i in 0..bytes {
        let b = (value >> (i * 8)) & 0xff;
        acc |= b << ((bytes - 1 - i) * 8);
    }
    acc
}

pub fn apply_endian_for_read(value: u64, total_bits: u32, endian: Endian) -> u64 {
    apply_endian_for_write(value, total_bits, endian) // same byte-swap is its own inverse
}

pub fn sign_extend(value: u64, total_bits: u32) -> i64 {
    if total_bits == 0 || total_bits >= 64 { return value as i64; }
    let mask = 1u64 << (total_bits - 1);
    if value & mask != 0 {
        // Sign bit set: sign-extend by ORing the upper bits.
        let upper = !0u64 << total_bits;
        (value | upper) as i64
    } else {
        value as i64
    }
}

// ----------------------------------------------------------------------
// UTF-8/16/32 encoding/decoding
// ----------------------------------------------------------------------

pub fn encode_utf8(cp: u32) -> Option<Vec<u8>> {
    if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) { return None; }
    Some(if cp < 0x80 {
        vec![cp as u8]
    } else if cp < 0x800 {
        vec![0xc0 | (cp >> 6) as u8, 0x80 | (cp & 0x3f) as u8]
    } else if cp < 0x10000 {
        vec![0xe0 | (cp >> 12) as u8,
             0x80 | ((cp >> 6) & 0x3f) as u8,
             0x80 | (cp & 0x3f) as u8]
    } else {
        vec![0xf0 | (cp >> 18) as u8,
             0x80 | ((cp >> 12) & 0x3f) as u8,
             0x80 | ((cp >> 6) & 0x3f) as u8,
             0x80 | (cp & 0x3f) as u8]
    })
}

pub fn decode_utf8(reader: &mut BitReader) -> Option<u32> {
    if reader.pos % 8 != 0 { return None; } // require byte alignment
    let b0 = reader.read_bits(8)? as u32;
    if b0 < 0x80 { return Some(b0); }
    let (extras, mask) = if b0 & 0xe0 == 0xc0 { (1, 0x1f) }
        else if b0 & 0xf0 == 0xe0 { (2, 0x0f) }
        else if b0 & 0xf8 == 0xf0 { (3, 0x07) }
        else { return None; };
    let mut cp = b0 & mask;
    for _ in 0..extras {
        let b = reader.read_bits(8)? as u32;
        if b & 0xc0 != 0x80 { return None; }
        cp = (cp << 6) | (b & 0x3f);
    }
    Some(cp)
}

pub fn encode_utf16(cp: u32, endian: Endian) -> Option<Vec<u8>> {
    if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) { return None; }
    let units = if cp < 0x10000 {
        vec![cp as u16]
    } else {
        let v = cp - 0x10000;
        vec![0xd800 | (v >> 10) as u16, 0xdc00 | (v & 0x3ff) as u16]
    };
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    let mut out = Vec::with_capacity(units.len() * 2);
    for u in units {
        if little { out.push((u & 0xff) as u8); out.push((u >> 8) as u8); }
        else      { out.push((u >> 8) as u8); out.push((u & 0xff) as u8); }
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
    if !(0xd800..=0xdbff).contains(&u1) { return Some(u1 as u32); }
    let u2 = read_u16(reader)?;
    if !(0xdc00..=0xdfff).contains(&u2) { return None; }
    Some(0x10000 + (((u1 as u32 & 0x3ff) << 10) | (u2 as u32 & 0x3ff)))
}

pub fn encode_utf32(cp: u32, endian: Endian) -> Option<Vec<u8>> {
    if cp > 0x10ffff || (0xd800..=0xdfff).contains(&cp) { return None; }
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    Some(if little {
        vec![(cp & 0xff) as u8, ((cp >> 8) & 0xff) as u8, ((cp >> 16) & 0xff) as u8, ((cp >> 24) & 0xff) as u8]
    } else {
        vec![((cp >> 24) & 0xff) as u8, ((cp >> 16) & 0xff) as u8, ((cp >> 8) & 0xff) as u8, (cp & 0xff) as u8]
    })
}

pub fn decode_utf32(reader: &mut BitReader, endian: Endian) -> Option<u32> {
    let little = matches!(endian, Endian::Little) || (matches!(endian, Endian::Native) && host_is_little_endian());
    let b0 = reader.read_bits(8)? as u32;
    let b1 = reader.read_bits(8)? as u32;
    let b2 = reader.read_bits(8)? as u32;
    let b3 = reader.read_bits(8)? as u32;
    Some(if little { (b3 << 24) | (b2 << 16) | (b1 << 8) | b0 }
         else      { (b0 << 24) | (b1 << 16) | (b2 << 8) | b3 })
}
