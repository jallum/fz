use fz_runtime::fz_value::{FzValue, LegacyTaggedWord};

pub(crate) fn value_from_word_bits(bits: u64) -> FzValue {
    fz_runtime::process::current_process()
        .heap
        .value_from_legacy_tagged_word(LegacyTaggedWord(bits))
}

pub(crate) fn word_bits_from_value(value: FzValue) -> u64 {
    fz_runtime::fz_value::legacy_tagged_word_from_fz_value(value).0
}

pub(crate) fn int_word_bits_checked(value: i64) -> Result<u64, String> {
    let encoded = fz_runtime::fz_value::legacy_tagged_word_from_fz_value(FzValue::int(value));
    if encoded.unbox_int() == Some(value) {
        Ok(encoded.0)
    } else {
        Err(format!(
            "raw interpreter int {value} cannot be materialized as external word"
        ))
    }
}

pub(crate) fn print_value(value: FzValue) {
    fz_runtime::ir_runtime::fz_print_value(word_bits_from_value(value));
}

pub(crate) fn render_value(value: FzValue) -> String {
    fz_runtime::fz_value::debug::render(word_bits_from_value(value))
}

pub(crate) fn value_eq(a: FzValue, b: FzValue) -> bool {
    LegacyTaggedWord(fz_runtime::ir_runtime::fz_value_eq(
        word_bits_from_value(a),
        word_bits_from_value(b),
    ))
    .is_true()
}

pub(crate) fn bool_from_runtime_eq_word(bits: u64) -> bool {
    LegacyTaggedWord(bits).is_true()
}

pub(crate) fn list_pointer_from_scalar_payload(value: FzValue) -> Option<*mut u8> {
    (value.kind() == fz_runtime::fz_value::ValueKind::INT)
        .then(|| (value.raw() as i64 as u64).wrapping_shl(3) as *mut u8)
        .filter(|p| !p.is_null() && (*p as usize) >= 4096)
}
