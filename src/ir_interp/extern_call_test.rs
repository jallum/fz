use super::{PairFF, PairFI, PairIF, PairII};
use std::mem::{align_of, size_of};

#[test]
fn c_scalar_pair_carriers_are_two_eight_byte_fields() {
    for (name, size, align) in [
        ("word/word", size_of::<PairII>(), align_of::<PairII>()),
        ("word/float", size_of::<PairIF>(), align_of::<PairIF>()),
        ("float/word", size_of::<PairFI>(), align_of::<PairFI>()),
        ("float/float", size_of::<PairFF>(), align_of::<PairFF>()),
    ] {
        assert_eq!(size, 16, "{name} C carrier size");
        assert_eq!(align, 8, "{name} C carrier alignment");
    }
}
