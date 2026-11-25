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
