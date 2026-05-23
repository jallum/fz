use cranelift_codegen::ir::{self, InstBuilder, condcodes::IntCC, types};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::fz_value::{FzValue, PackedValueWord};

const TAG_INT: i64 = 0b001;
const TAG_ATOM: i64 = 0b010;
const TAG_MASK: i64 = 0b111;

pub(crate) fn value_from_word_bits(bits: u64) -> FzValue {
    fz_runtime::process::current_process()
        .heap
        .value_from_packed_word(PackedValueWord(bits))
}

pub(crate) fn word_bits_from_value(value: FzValue) -> u64 {
    fz_runtime::fz_value::packed_word_from_value(value).0
}

pub(crate) fn int_word_bits_checked(value: i64) -> Result<u64, String> {
    let encoded = fz_runtime::fz_value::packed_word_from_value(FzValue::int(value));
    if encoded.unbox_int() == Some(value) {
        Ok(encoded.0)
    } else {
        Err(format!(
            "raw interpreter int {value} cannot be materialized as external word"
        ))
    }
}

pub(crate) fn int_word_bits(value: i64) -> i64 {
    fz_runtime::fz_value::packed_word_from_value(FzValue::int(value)).0 as i64
}

pub(crate) fn print_value(value: FzValue) {
    fz_runtime::ir_runtime::fz_print_value(word_bits_from_value(value));
}

pub(crate) fn render_value(value: FzValue) -> String {
    fz_runtime::fz_value::debug::render(word_bits_from_value(value))
}

pub(crate) fn value_eq(a: FzValue, b: FzValue) -> bool {
    PackedValueWord(fz_runtime::ir_runtime::fz_value_eq(
        word_bits_from_value(a),
        word_bits_from_value(b),
    ))
    .is_true()
}

pub(crate) fn bool_from_runtime_eq_word(bits: u64) -> bool {
    PackedValueWord(bits).is_true()
}

pub(crate) fn list_pointer_from_scalar_payload(value: FzValue) -> Option<*mut u8> {
    (value.kind() == fz_runtime::fz_value::ValueKind::INT)
        .then(|| (value.raw() as i64 as u64).wrapping_shl(3) as *mut u8)
        .filter(|p| !p.is_null() && (*p as usize) >= 4096)
}

pub(crate) fn pack_raw_int_for_legacy_word(
    b: &mut FunctionBuilder<'_>,
    raw: ir::Value,
) -> ir::Value {
    let shifted = b.ins().ishl_imm(raw, 3);
    b.ins().bor_imm(shifted, TAG_INT)
}

pub(crate) fn unpack_legacy_int_word(b: &mut FunctionBuilder<'_>, bits: ir::Value) -> ir::Value {
    b.ins().sshr_imm(bits, 3)
}

pub(crate) fn pack_strict_parts_for_legacy_word(
    b: &mut FunctionBuilder<'_>,
    raw: ir::Value,
    kind: ir::Value,
) -> ir::Value {
    let kind64 = b.ins().uextend(types::I64, kind);
    let heap_bits = b.ins().bor(raw, kind64);

    let int_bits = pack_raw_int_for_legacy_word(b, raw);
    let atom_shifted = b.ins().ishl_imm(raw, 3);
    let atom_bits = b.ins().bor_imm(atom_shifted, TAG_ATOM);

    let null_bits = b.ins().iconst(types::I64, 0);
    let empty_bits = b
        .ins()
        .iconst(types::I64, crate::ir_codegen::EMPTY_LIST_BITS);

    let is_null = b
        .ins()
        .icmp_imm(IntCC::Equal, kind, crate::ir_codegen::VRX_TAG_NULL);
    let is_int = b
        .ins()
        .icmp_imm(IntCC::Equal, kind, crate::ir_codegen::VRX_TAG_KIND_INT);
    let is_atom = b
        .ins()
        .icmp_imm(IntCC::Equal, kind, crate::ir_codegen::VRX_TAG_KIND_ATOM);
    let is_list = b
        .ins()
        .icmp_imm(IntCC::Equal, kind, crate::ir_codegen::VRX_TAG_LIST);
    let raw_is_zero = b.ins().icmp_imm(IntCC::Equal, raw, 0);
    let is_empty_list = b.ins().band(is_list, raw_is_zero);
    let heap_lo = b.ins().icmp_imm(
        IntCC::UnsignedGreaterThanOrEqual,
        kind,
        crate::ir_codegen::VRX_TAG_LIST,
    );
    let heap_hi = b.ins().icmp_imm(
        IntCC::UnsignedLessThanOrEqual,
        kind,
        crate::ir_codegen::VRX_TAG_RESOURCE,
    );
    let is_heap = b.ins().band(heap_lo, heap_hi);

    let mut bits = raw;
    bits = b.ins().select(is_heap, heap_bits, bits);
    bits = b.ins().select(is_empty_list, empty_bits, bits);
    bits = b.ins().select(is_atom, atom_bits, bits);
    bits = b.ins().select(is_int, int_bits, bits);
    b.ins().select(is_null, null_bits, bits)
}

pub(crate) fn unpack_legacy_word_to_strict_parts(
    b: &mut FunctionBuilder<'_>,
    value: ir::Value,
) -> (ir::Value, ir::Value) {
    let tag3 = b.ins().band_imm(value, TAG_MASK);
    let tag4 = b.ins().band_imm(value, crate::ir_codegen::VRX_TAG_MASK);
    let raw_heap = b.ins().band_imm(value, !crate::ir_codegen::VRX_TAG_MASK);
    let raw_int = b.ins().sshr_imm(value, 3);
    let raw_atom = b.ins().ushr_imm(value, 3);
    let zero64 = b.ins().iconst(types::I64, 0);

    let heap_lo = b.ins().icmp_imm(
        IntCC::UnsignedGreaterThanOrEqual,
        tag4,
        crate::ir_codegen::VRX_TAG_LIST,
    );
    let heap_hi = b.ins().icmp_imm(
        IntCC::UnsignedLessThanOrEqual,
        tag4,
        crate::ir_codegen::VRX_TAG_RESOURCE,
    );
    let heap_tag = b.ins().band(heap_lo, heap_hi);
    let heap_addr = b
        .ins()
        .icmp_imm(IntCC::UnsignedGreaterThanOrEqual, raw_heap, 4096);
    let is_heap = b.ins().band(heap_tag, heap_addr);
    let not_heap = b.ins().bxor_imm(is_heap, 1);

    let is_null = b.ins().icmp_imm(IntCC::Equal, value, 0);
    let tag3_is_int = b.ins().icmp_imm(IntCC::Equal, tag3, TAG_INT);
    let tag3_is_atom = b.ins().icmp_imm(IntCC::Equal, tag3, TAG_ATOM);
    let is_int = b.ins().band(tag3_is_int, not_heap);
    let is_atom = b.ins().band(tag3_is_atom, not_heap);
    let is_empty_list = b
        .ins()
        .icmp_imm(IntCC::Equal, value, crate::ir_codegen::EMPTY_LIST_BITS);

    let mut raw = value;
    raw = b.ins().select(is_heap, raw_heap, raw);
    raw = b.ins().select(is_empty_list, zero64, raw);
    raw = b.ins().select(is_atom, raw_atom, raw);
    raw = b.ins().select(is_int, raw_int, raw);
    raw = b.ins().select(is_null, zero64, raw);

    let kind_null = b.ins().iconst(
        types::I8,
        fz_runtime::fz_value::ValueKind::NULL.tag() as i64,
    );
    let kind_list = b.ins().iconst(
        types::I8,
        fz_runtime::fz_value::ValueKind::LIST.tag() as i64,
    );
    let kind_int = b
        .ins()
        .iconst(types::I8, fz_runtime::fz_value::ValueKind::INT.tag() as i64);
    let kind_atom = b.ins().iconst(
        types::I8,
        fz_runtime::fz_value::ValueKind::ATOM.tag() as i64,
    );
    let kind_heap = b.ins().ireduce(types::I8, tag4);

    let mut kind = kind_null;
    kind = b.ins().select(is_heap, kind_heap, kind);
    kind = b.ins().select(is_empty_list, kind_list, kind);
    kind = b.ins().select(is_atom, kind_atom, kind);
    kind = b.ins().select(is_int, kind_int, kind);
    (raw, kind)
}
