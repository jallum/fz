//! A scalar box written in place.
//!
//! An `any` slot holds an int, a float or a reference as a ref word that names
//! a one-word box on the heap. Compiled code places the box with `emit_place`
//! (one 16-byte slot, counted under the scalar-box statistics) and stores the
//! payload word the runtime's `box_any_value_ref` stores. The slot's second
//! word is padding that nothing reads: the runtime leaves it unwritten too.
//! The ref word is the box's address under the value's kind.
//!
//! A float is checked before it is placed. The runtime refuses a float that is
//! not finite (`AnyValue::float` asserts it), and a foreign function can
//! return a NaN or an infinity, so such a float must still reach that
//! assertion. The instructions test the exponent bits and send a non-finite
//! float to the runtime function, which raises; every finite float is placed
//! here.

use super::place::emit_place;
use super::recipe::constant_of;
use super::*;
use cranelift_codegen::ir::{self, BlockArg, InstBuilder, MemFlagsData, types};
use fz_runtime::any_value::ValueKind;
use fz_runtime::heap::HeapAllocKind;
use fz_runtime::ir_runtime::fz_box_float_for_any;

/// How the payload reaches the box.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BoxLane {
    Int,
    Float,
    /// A reference word. The call names its kind with a constant.
    Opaque,
}

/// A scalar box is one 16-byte slot: the payload and a padding word.
const BOX_BYTES: usize = 16;

/// The exponent field of an f64's bits, all ones for a NaN or an infinity.
const FLOAT_EXPONENT_MASK: i64 = 0x7ff0_0000_0000_0000;

/// Place a box for the payload in `args` and answer its ref word. `args[0]` is
/// the process, which `emit_place` reads from the pinned register; the payload
/// follows, and an opaque box ends with its kind as a constant.
pub(super) fn emit_scalar_box<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    lane: BoxLane,
    args: &[ir::Value],
) -> ir::Value {
    match (lane, args) {
        (BoxLane::Int, &[_process, raw]) => place_box(body, raw, ValueKind::INT),
        (BoxLane::Float, &[_process, raw]) => emit_float_box(body, raw),
        (BoxLane::Opaque, &[_process, raw, kind]) => {
            let kind = constant_of(body.b, kind)
                .and_then(|tag| ValueKind::new(u8::try_from(tag).ok()?))
                .filter(|kind| kind.is_boxed_scalar())
                .unwrap_or_else(|| panic!("an opaque box names a boxed scalar kind with a constant"));
            place_box(body, raw, kind)
        }
        _ => panic!("a {lane:?} box row got {} arguments", args.len()),
    }
}

/// Place a box holding `payload`, the word the runtime stores, and answer the
/// ref word of `kind`.
fn place_box<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    payload: ir::Value,
    kind: ValueKind,
) -> ir::Value {
    let address = emit_place(body, HeapAllocKind::ScalarBox, BOX_BYTES);
    body.b.ins().store(MemFlagsData::trusted(), payload, address, 0);
    body.heap_ref_word_from_addr(address, kind)
}

/// A finite float is placed; any other goes to the runtime function, which
/// raises.
fn emit_float_box<M: cranelift_module::Module>(body: &mut CodegenFn<'_, '_, M>, raw: ir::Value) -> ir::Value {
    let bits = body.b.ins().bitcast(types::I64, MemFlagsData::new(), raw);
    let not_bits = body.b.ins().bnot(bits);
    let exponent_has_a_zero = body.b.ins().band_imm_u(not_bits, FLOAT_EXPONENT_MASK);
    let finite = body.b.create_block();
    let refused = body.b.create_block();
    let done = body.b.create_block();
    body.b.append_block_param(done, types::I64);
    body.b.ins().brif(exponent_has_a_zero, finite, &[], refused, &[]);

    body.b.switch_to_block(refused);
    body.b.seal_block(refused);
    body.b.set_cold_block(refused);
    let process = body.process_arg();
    let call = runtime_call!(body, fz_box_float_for_any, [process, raw]);
    let from_runtime = body.sole_result(call);
    body.b.ins().jump(done, &[BlockArg::Value(from_runtime)]);

    body.b.switch_to_block(finite);
    body.b.seal_block(finite);
    let reference = place_box(body, bits, ValueKind::FLOAT);
    body.b.ins().jump(done, &[BlockArg::Value(reference)]);

    body.b.switch_to_block(done);
    body.b.seal_block(done);
    body.b.block_params(done)[0]
}
