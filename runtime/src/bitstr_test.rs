use super::*;

fn written(len: usize, fill: impl FnOnce(&mut BitSink<'_>)) -> Vec<u8> {
    let mut dest = vec![MaybeUninit::<u8>::uninit(); len];
    fill(&mut BitSink::new(&mut dest));
    dest.iter().map(|byte| unsafe { byte.assume_init() }).collect()
}

#[test]
fn bits_are_written_most_significant_first_across_byte_boundaries() {
    let bytes = written(3, |sink| {
        sink.write_bits(0b1, 1);
        sink.write_bits(0x3ff, 10);
        sink.write_bits(0b0, 1);
        sink.write_bits(0b1010, 4);
        sink.write_bits(0b111, 3);
    });
    assert_eq!(bytes, vec![0b1111_1111, 0b1110_1010, 0b1110_0000]);
}

#[test]
fn a_byte_range_from_an_unaligned_start_reads_across_source_bytes() {
    let source = [0b1010_1100, 0b0101_0011, 0b1111_0000];
    let bytes = written(2, |sink| sink.write_bit_range(&source, 3, 13));
    assert_eq!(bytes, vec![0b0110_0010, 0b1001_1000]);
}

#[test]
fn an_aligned_range_copies_whole_bytes_and_the_tail_bits() {
    let source = [0xde, 0xad, 0b1011_0000];
    let bytes = written(3, |sink| sink.write_bit_range(&source, 0, 20));
    assert_eq!(bytes, vec![0xde, 0xad, 0b1011_0000]);
}

#[test]
fn a_scalar_encodes_to_the_bytes_of_its_encoding_and_a_surrogate_to_none() {
    assert_eq!(encode_utf8(0x20ac).unwrap().as_slice(), "\u{20ac}".as_bytes());
    assert_eq!(
        encode_utf16(0x1f600, Endian::Little).unwrap().as_slice(),
        &[0x3d, 0xd8, 0x00, 0xde]
    );
    assert_eq!(encode_utf32(0x41, Endian::Big).unwrap().as_slice(), &[0, 0, 0, 0x41]);
    assert_eq!(encode_utf8(0xd800), None);
    assert_eq!(encode_utf16(0x110000, Endian::Big), None);
}

#[test]
fn a_little_endian_field_is_its_low_bytes_then_the_high_bits() {
    // Elixir: <<0x1abc::13-little>> == <<0xbc, 0x1a::size(5)>>, whose bits as
    // one 13-bit big-endian word are 0xbc << 5 | 0x1a.
    assert_eq!(apply_endian_for_write(0x1abc, 13, Endian::Little), (0xbc << 5) | 0x1a);
    // <<0x1abcd::17-little>> == <<0xcd, 0xab, 1::size(1)>>
    assert_eq!(apply_endian_for_write(0x1abcd, 17, Endian::Little), (0xcdab << 1) | 1);
    // Below a byte there is nothing to swap, and a whole-byte width swaps bytes.
    assert_eq!(apply_endian_for_write(0b101, 3, Endian::Little), 0b101);
    assert_eq!(apply_endian_for_write(0x1234, 16, Endian::Little), 0x3412);
    assert_eq!(apply_endian_for_write(0x1abc, 13, Endian::Big), 0x1abc);
}

#[test]
fn reading_a_little_endian_field_undoes_writing_it_at_every_width() {
    let value = 0x7fed_cba9_8765_4321u64;
    for bits in 1..=64u32 {
        let masked = if bits == 64 {
            value
        } else {
            value & ((1u64 << bits) - 1)
        };
        for endian in [Endian::Big, Endian::Little, Endian::Native] {
            let word = apply_endian_for_write(masked, bits, endian);
            assert_eq!(
                apply_endian_for_read(word, bits, endian),
                masked,
                "{bits} bits, {endian:?}"
            );
        }
    }
}

#[test]
fn a_native_field_is_little_endian_on_a_little_endian_host() {
    assert_eq!(
        apply_endian_for_write(0x1abc, 13, Endian::Native),
        apply_endian_for_write(
            0x1abc,
            13,
            if host_is_little_endian() {
                Endian::Little
            } else {
                Endian::Big
            }
        )
    );
}

const KINDS: [BitType; 7] = [
    BitType::Integer,
    BitType::Float,
    BitType::Binary,
    BitType::Bits,
    BitType::Utf8,
    BitType::Utf16,
    BitType::Utf32,
];

#[test]
fn every_kind_survives_the_tag_the_compiled_code_carries() {
    for kind in KINDS {
        assert_eq!(BitType::from_tag(kind.tag()), kind);
    }
    let tags: Vec<u32> = KINDS.iter().map(|kind| kind.tag()).collect();
    assert_eq!(tags, vec![0, 1, 2, 3, 4, 5, 6]);
}

#[test]
fn every_byte_order_survives_the_tag_the_compiled_code_carries() {
    for endian in [Endian::Big, Endian::Little, Endian::Native] {
        assert_eq!(Endian::from_tag(endian.tag()), endian);
    }
    assert_eq!(
        [Endian::Big.tag(), Endian::Little.tag(), Endian::Native.tag()],
        [0, 1, 2]
    );
}

#[test]
#[should_panic(expected = "unknown bit type tag 7")]
fn a_kind_tag_no_kind_has_is_loud() {
    BitType::from_tag(7);
}

#[test]
#[should_panic(expected = "unknown endian tag 3")]
fn a_byte_order_tag_no_order_has_is_loud() {
    Endian::from_tag(3);
}

#[test]
fn only_binary_counts_its_size_in_bytes_by_default() {
    for kind in KINDS {
        let expected = if kind == BitType::Binary { 8 } else { 1 };
        assert_eq!(kind.default_unit(), expected, "{kind:?}");
    }
}

#[test]
fn native_order_is_the_targets_order() {
    assert!(Endian::Big.is_big());
    assert!(!Endian::Little.is_big());
    assert_eq!(Endian::Native.is_big(), cfg!(target_endian = "big"));
}
