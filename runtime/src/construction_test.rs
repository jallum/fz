use super::*;
use crate::bits::Bin;
use crate::heap::SchemaRegistry;
use crate::ir_runtime::fz_bs_field_spec;
use std::cell::RefCell;
use std::rc::Rc;

const INTEGER: u32 = 0;
const FLOAT: u32 = 1;
const BINARY: u32 = 2;
const BITS: u32 = 3;
const UTF8: u32 = 4;
const UTF16: u32 = 5;
const UTF32: u32 = 6;
const BIG: u32 = 0;
const LITTLE: u32 = 1;

fn with_process<R>(f: impl FnOnce(&mut Process) -> R) -> R {
    let mut process = Box::new(Process::new(Rc::new(RefCell::new(SchemaRegistry::new()))));
    f(&mut process)
}

fn field(ty: u32, size: Option<u64>, unit: u32, endian: u32, value: u64) -> FzBsField {
    FzBsField {
        spec: fz_bs_field_spec(ty, size.is_some() as u32, unit, endian, 0, 0),
        size: size.unwrap_or(0),
        value,
    }
}

fn int(bits: u64, value: u64) -> FzBsField {
    field(INTEGER, Some(bits), 1, BIG, value)
}

fn float(bits: u64, endian: u32, value: f64) -> FzBsField {
    field(FLOAT, Some(bits), 1, endian, value.to_bits())
}

/// The result of building `fields`: its bytes and bit length.
fn built(process: &mut Process, fields: &[FzBsField]) -> (Vec<u8>, u64) {
    let word = build(process, fields);
    let bin = unsafe { Bin::of_binary(word) };
    let bytes = unsafe { from_raw_parts(bin.ptr(), bin.bit_len().div_ceil(8) as usize) };
    (bytes.to_vec(), bin.bit_len())
}

fn binary_word(process: &mut Process, bytes: &[u8], bit_len: u64) -> u64 {
    process.alloc_bitstring(bytes, bit_len).ref_word().raw_word()
}

/// Bits, one entry each, most significant first: the definition a build is held to.
fn bit_model(value: u64, n: u32) -> Vec<bool> {
    (0..n).rev().map(|shift| (value >> shift) & 1 == 1).collect()
}

fn pack(bits: &[bool]) -> (Vec<u8>, u64) {
    let mut bytes = vec![0u8; bits.len().div_ceil(8)];
    for (index, bit) in bits.iter().enumerate() {
        bytes[index / 8] |= (*bit as u8) << (7 - index % 8);
    }
    (bytes, bits.len() as u64)
}

#[test]
fn integers_of_every_width_class_land_where_their_bits_say() {
    with_process(|process| {
        let (bytes, bit_len) = built(
            process,
            &[int(3, 0b101), int(13, 0x1abc), int(8, 0xff), int(64, u64::MAX - 1)],
        );
        let mut model = bit_model(0b101, 3);
        model.extend(bit_model(0x1abc & 0x1fff, 13));
        model.extend(bit_model(0xff, 8));
        model.extend(bit_model(u64::MAX - 1, 64));
        assert_eq!((bytes, bit_len), pack(&model));
    });
}

#[test]
fn a_little_endian_integer_writes_its_low_bytes_first_and_its_high_bits_last() {
    with_process(|process| {
        let little = |bits, value| field(INTEGER, Some(bits), 1, LITTLE, value);
        assert_eq!(built(process, &[little(16, 0x1234)]), (vec![0x34, 0x12], 16));
        assert_eq!(built(process, &[little(12, 0xabc)]), (vec![0xbc, 0xa0], 12));
    });
}

#[test]
fn an_integer_with_no_size_is_one_byte_and_the_unit_scales_a_size() {
    with_process(|process| {
        assert_eq!(built(process, &[field(INTEGER, None, 1, BIG, 0x1ff)]), (vec![0xff], 8));
        assert_eq!(
            built(process, &[field(INTEGER, Some(2), 8, BIG, 0x1234)]),
            (vec![0x12, 0x34], 16)
        );
    });
}

#[test]
fn a_float_is_half_single_or_double_in_either_byte_order() {
    with_process(|process| {
        assert_eq!(built(process, &[float(16, BIG, 1.0)]), (vec![0x3c, 0x00], 16));
        assert_eq!(built(process, &[float(16, LITTLE, 1.0)]), (vec![0x00, 0x3c], 16));
        assert_eq!(built(process, &[float(32, BIG, 1.0)]), (vec![0x3f, 0x80, 0, 0], 32));
        assert_eq!(
            built(process, &[float(64, BIG, 1.0)]),
            (1.0f64.to_be_bytes().to_vec(), 64)
        );
    });
}

#[test]
fn half_precision_rounds_to_nearest_even_and_overflows_to_infinity() {
    for (value, half) in [
        (65504.0, 0x7bff),
        (65519.0, 0x7bff),
        (65520.0, 0x7c00),
        (1.0e10, 0x7c00),
        (-2.5, 0xc100),
        (1.0e-8, 0x0000),
        (6.0e-8, 0x0001),
        (3.0e-8, 0x0001),
        (6.1e-5, 0x03ff),
        (0.1, 0x2e66),
        (-0.0, 0x8000),
        (f64::INFINITY, 0x7c00),
        (f64::NEG_INFINITY, 0xfc00),
    ] {
        assert_eq!(f64_to_half_bits(value), half, "{value}");
    }
}

#[test]
fn a_utf_field_is_one_to_four_bytes_by_code_point() {
    with_process(|process| {
        let utf = |ty, endian, cp: u32| field(ty, None, 1, endian, cp as u64);
        for (cp, utf8_len) in [(0x41, 1), (0xe9, 2), (0x20ac, 3), (0x1f600, 4)] {
            let (bytes, bit_len) = built(process, &[utf(UTF8, BIG, cp)]);
            assert_eq!(bytes, char::from_u32(cp).unwrap().to_string().into_bytes());
            assert_eq!((bytes.len(), bit_len), (utf8_len, utf8_len as u64 * 8));
        }
        assert_eq!(
            built(process, &[utf(UTF16, BIG, 0x1f600)]),
            (vec![0xd8, 0x3d, 0xde, 0x00], 32)
        );
        assert_eq!(built(process, &[utf(UTF16, LITTLE, 0x20ac)]), (vec![0xac, 0x20], 16));
        assert_eq!(
            built(process, &[utf(UTF32, LITTLE, 0x20ac)]),
            (vec![0xac, 0x20, 0, 0], 32)
        );
    });
}

#[test]
fn a_binary_field_after_an_unaligned_field_is_shifted_into_place() {
    with_process(|process| {
        let source = binary_word(process, &[0xde, 0xad, 0xbe], 24);
        let (bytes, bit_len) = built(
            process,
            &[int(3, 0b110), field(BINARY, None, 8, BIG, source), int(5, 0b10101)],
        );
        let mut model = bit_model(0b110, 3);
        for byte in [0xde, 0xad, 0xbe] {
            model.extend(bit_model(byte, 8));
        }
        model.extend(bit_model(0b10101, 5));
        assert_eq!((bytes, bit_len), pack(&model));
    });
}

#[test]
fn a_bits_field_keeps_its_odd_length_and_a_sized_binary_takes_a_prefix() {
    with_process(|process| {
        let odd = binary_word(process, &[0b1011_0100], 6);
        assert_eq!(
            built(process, &[field(BITS, None, 1, BIG, odd), int(2, 0b11)]),
            (vec![0b1011_0111], 8)
        );
        let long = binary_word(process, &[1, 2, 3, 4], 32);
        assert_eq!(
            built(process, &[field(BINARY, Some(2), 8, BIG, long)]),
            (vec![1, 2], 16)
        );
    });
}

#[test]
fn results_either_side_of_the_inline_limit_hold_every_byte() {
    with_process(|process| {
        for len in [0usize, 1, 63, 64, 65, 300] {
            let payload: Vec<u8> = (0..len).map(|i| (i * 7 + 3) as u8).collect();
            let source = binary_word(process, &payload, len as u64 * 8);
            let (bytes, bit_len) = built(process, &[int(8, 0xa5), field(BINARY, None, 8, BIG, source)]);
            assert_eq!(bit_len, (len as u64 + 1) * 8);
            assert_eq!(bytes[0], 0xa5);
            assert_eq!(&bytes[1..], &payload[..], "{len} payload bytes");
        }
    });
}

#[test]
fn the_size_is_the_sum_of_the_segments_before_anything_is_written() {
    with_process(|process| {
        let source = binary_word(process, &[0; 5], 40);
        let fields = [
            int(3, 0),
            field(BINARY, None, 8, BIG, source),
            float(16, BIG, 1.0),
            field(UTF8, None, 1, BIG, 0x20ac),
        ];
        assert_eq!(size_in_bits(&fields), 3 + 40 + 16 + 24);
    });
}

#[test]
fn a_fill_that_starts_after_written_bits_continues_them() {
    let mut dest = [std::mem::MaybeUninit::<u8>::uninit(); 3];
    let mut sink = BitSink::new(&mut dest);
    sink.write_bits(0b101, 3);
    let after = sink.bit_pos();
    fill(&[int(13, 0x1fff)], &mut BitSink::starting_at(&mut dest, after));
    let written: Vec<u8> = dest[..2].iter().map(|byte| unsafe { byte.assume_init() }).collect();
    assert_eq!(written, vec![0b1011_1111, 0b1111_1111]);
}

/// A construction that starts with an unsized binary of whole bytes is an
/// append to it: appends to a buffer-backed accumulator write into the buffer
/// until it is full, so 50 appends place a buffer per doubling and not one per
/// append, and the bytes are those the segments spell.
#[test]
fn a_leading_binary_is_appended_to_in_place() {
    with_process(|process| {
        let bytes: Vec<u8> = (0..100u8).collect();
        let mut expected = bytes.clone();
        let mut acc = binary_word(process, &bytes, 800);
        let mut buffers = std::collections::BTreeSet::new();
        for step in 0..50u64 {
            acc = build(
                process,
                &[field(BINARY, None, 8, BIG, acc), int(8, step), int(16, 0xA0B0 + step)],
            );
            expected.extend_from_slice(&[step as u8, 0xA0, 0xB0 + step as u8]);
            buffers.insert(unsafe { Bin::of_binary(acc) }.ptr());
        }
        assert_eq!(buffers.len(), 2, "the accumulator moved once, when its buffer was full");
        assert_eq!(unsafe { Bin::of_binary(acc) }.bytes(), expected);
    });
}

/// An append the caller fills says where its right side goes, in the binary
/// it returns, whether the left side stayed in its buffer, was copied inline,
/// or was copied into a new buffer, so the caller needs no second look at the
/// result to write the rest.
#[test]
fn an_unfilled_append_says_where_its_rest_goes() {
    with_process(|process| {
        let right = *b"tail";
        let append_to = |process: &mut Process, leading: u64| {
            let appended = append_unfilled(process, leading, right.len());
            unsafe { std::slice::from_raw_parts_mut(appended.rest, right.len()) }.copy_from_slice(&right);
            appended.binary
        };
        let head = binary_word(process, b"head", 32);
        let inline = append_to(process, head);
        assert_eq!(unsafe { Bin::of_binary(inline) }.bytes(), b"headtail");

        let mut expected: Vec<u8> = (0..70u8).collect();
        let mut accumulator = binary_word(process, &expected, expected.len() as u64 * 8);
        for _ in 0..20 {
            accumulator = append_to(process, accumulator);
            expected.extend_from_slice(&right);
            assert_eq!(unsafe { Bin::of_binary(accumulator) }.bytes(), expected);
        }
    });
}

/// A leading binary whose value is not whole bytes, and a rest that is not
/// whole bytes, make a construction that is built whole.
#[test]
fn a_leading_bitstring_or_a_rest_that_is_not_whole_bytes_is_built_whole() {
    with_process(|process| {
        let odd = binary_word(process, &[0b1010_0000], 3);
        let (bytes, bit_len) = built(process, &[field(BINARY, None, 1, BIG, odd), int(8, 0xFF)]);
        assert_eq!((bytes, bit_len), (vec![0b1011_1111, 0b1110_0000], 11));

        let whole = binary_word(process, b"ab", 16);
        let (bytes, bit_len) = built(process, &[field(BINARY, None, 8, BIG, whole), int(4, 0xF)]);
        assert_eq!((bytes, bit_len), (vec![b'a', b'b', 0xF0], 20));
    });
}

fn constant(ty: u32, size: Option<u64>, unit: u32, endian: u32, value: ConstantValue<'_>) -> ConstantField<'_> {
    ConstantField {
        spec: fz_bs_field_spec(ty, size.is_some() as u32, unit, endian, 0, 0),
        size: size.unwrap_or(0),
        value,
    }
}

#[test]
fn constants_encode_to_what_a_running_construction_builds() {
    let word = |ty, size, endian, value| constant(ty, size, 1, endian, ConstantValue::Word(value));
    let float = |size, endian, value| constant(FLOAT, Some(size), 1, endian, ConstantValue::Float(value));
    let bytes = |ty, size| {
        constant(
            ty,
            size,
            8 * (ty == BINARY) as u32 + (ty == BITS) as u32,
            BIG,
            ConstantValue::Bytes(b"hello"),
        )
    };
    let cases: Vec<Vec<ConstantField<'_>>> = vec![
        vec![],
        vec![
            word(INTEGER, Some(3), BIG, 0b101),
            word(INTEGER, Some(13), LITTLE, 0x1abc),
        ],
        vec![word(INTEGER, None, BIG, 65)],
        vec![
            word(INTEGER, Some(64), BIG, u64::MAX - 1),
            word(INTEGER, Some(5), BIG, 9),
        ],
        vec![float(16, BIG, 0.1), float(32, LITTLE, -2.5), float(64, BIG, 1.0e300)],
        vec![
            word(UTF8, None, BIG, 0x1f600),
            word(UTF16, None, LITTLE, 0x20ac),
            word(UTF32, None, BIG, 0x41),
        ],
        vec![
            bytes(BINARY, None),
            word(INTEGER, Some(1), BIG, 1),
            bytes(BITS, Some(12)),
        ],
    ];
    with_process(|process| {
        for fields in cases {
            let runtime: Vec<FzBsField> = fields
                .iter()
                .map(|f| FzBsField {
                    spec: f.spec,
                    size: f.size,
                    value: match f.value {
                        ConstantValue::Word(word) => word,
                        ConstantValue::Float(value) => value.to_bits(),
                        ConstantValue::Bytes(b) => binary_word(process, b, b.len() as u64 * 8),
                    },
                })
                .collect();
            let (bytes, bit_len) = built(process, &runtime);
            assert_eq!(
                encode_constants(&fields),
                Ok(EncodedConstants { bytes, bit_len }),
                "{fields:?}"
            );
        }
    });
}

#[test]
fn a_constant_the_runtime_refuses_does_not_encode() {
    let word = |ty, size, value| constant(ty, size, 1, BIG, ConstantValue::Word(value));
    for refused in [
        word(UTF8, None, 0xd800),
        word(UTF16, None, 0x11_0000),
        word(UTF32, None, u64::MAX),
        word(INTEGER, Some(65), 1),
        constant(FLOAT, Some(8), 1, BIG, ConstantValue::Float(1.0)),
        constant(BINARY, Some(6), 8, BIG, ConstantValue::Bytes(b"hello")),
    ] {
        assert!(encode_constants(&[refused]).is_err(), "{refused:?}");
    }
}
