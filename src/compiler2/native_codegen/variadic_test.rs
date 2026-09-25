use super::*;
use std::str::FromStr;

fn lanes(lanes: &[ir::Type]) -> Vec<(ir::Value, ir::Type)> {
    lanes.iter().map(|lane| (ir::Value::from_u32(0), *lane)).collect()
}

/// Apple AArch64 reads variadic arguments from the stack, so the call has
/// to consume every integer argument register before naming them. The
/// count is what is left of x0..x7 after the fixed prefix.
#[test]
fn apple_aarch64_fills_the_integer_argument_registers() {
    let triple = Triple::from_str("aarch64-apple-darwin").expect("triple");
    assert_eq!(integer_register_padding(&triple, &lanes(&[])), 8);
    assert_eq!(integer_register_padding(&triple, &lanes(&[types::I64])), 7);
    assert_eq!(integer_register_padding(&triple, &lanes(&[types::I64, types::I64])), 6);
}

/// A fixed float parameter rides the float bank, so it leaves the integer
/// registers untouched and the padding unchanged.
#[test]
fn a_fixed_float_parameter_does_not_consume_an_integer_register() {
    let triple = Triple::from_str("aarch64-apple-darwin").expect("triple");
    assert_eq!(integer_register_padding(&triple, &lanes(&[types::F64, types::I64])), 7);
}

/// A fixed prefix long enough to spill already places its tail on the
/// stack, so the variadic values follow it with nothing added.
#[test]
fn a_long_fixed_prefix_needs_no_padding() {
    let triple = Triple::from_str("aarch64-apple-darwin").expect("triple");
    assert_eq!(integer_register_padding(&triple, &lanes(&[types::I64; 9])), 0);
}

/// Everywhere else a variadic argument is passed exactly like an ordinary
/// one, so the call is the ordinary call and nothing is added.
#[test]
fn other_targets_pass_variadic_arguments_like_ordinary_ones() {
    for target in [
        "aarch64-unknown-linux-gnu",
        "x86_64-unknown-linux-gnu",
        "x86_64-apple-darwin",
    ] {
        let triple = Triple::from_str(target).expect("triple");
        assert_eq!(integer_register_padding(&triple, &lanes(&[types::I64])), 0, "{target}");
    }
}
