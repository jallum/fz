//! Inline recipes: the runtime functions compiled code computes in place.
//!
//! A row of [`RECIPES`] names a runtime function by its Rust item and emits
//! Cranelift instructions that compute the answer that function computes.
//! Every place compiled code would call the function asks this table first:
//! with a row the instructions are emitted and no import is declared, without
//! one the call is emitted. Adding an intrinsic is adding one row.
//!
//! The Rust function stays the definition. The interpreter keeps calling it,
//! and the parity test in `recipe_test.rs` walks the table, comparing each
//! row's instructions with the function over inputs for its signature; a row
//! without such inputs fails the test.
//!
//! A row answers in place or it places an object. An in-place row is a pure
//! function of its arguments, and the test compares its words. An allocation
//! row takes the process as its first argument, as the runtime function does,
//! and writes the object itself: it places through `emit_place`, which calls
//! the runtime only for room, and fills the object's words. A call site asks
//! for one through [`emit_cell`], which also registers the site. The test
//! compares what an allocation row does to a heap: it runs the runtime
//! function and the instructions on two fresh heaps and compares the placed
//! object's words, the words of every object the row may share, the tip each
//! leaves and the heap's allocation statistics.
//!
//! A struct or tuple and a closure are allocation rows too, which place the
//! object and write its header (and a closure's code address) and leave its
//! fields or captures to the code that builds it. The runtime has no extern
//! for them, so their rows are named by the heap method the interpreter calls,
//! `Heap::alloc_struct_unwritten` and `Heap::alloc_closure`, and a call site
//! asks for one through [`emit_object`].
//!
//! A recipe does not validate its arguments. The Rust function panics on a
//! malformed word; the instructions read whatever the word says.
//!
//! A row answers in one of three shapes, and no others:
//!
//! - [`Emitted::Value`]: one word or float.
//! - [`Emitted::Condition`]: an `I8` the next branch uses directly. A consumer
//!   that needs the atom boolean converts it there.
//! - [`Emitted::Checked`]: a value and the `I8` condition that says it failed,
//!   in place of the C scalar pair the function returns.
//!
//! A recipe may decline an instance, as `fz_value_eq_raw_const` does for a
//! kind it has no instructions for; the call is then emitted as if the table
//! had no row.

use super::inline_object::{Placed, emit_closure, emit_struct};
use super::list_cell::{HeadLane, emit_list_cell};
use super::*;
use cranelift_codegen::ir::{
    self, BlockArg, InstBuilder, InstructionData, MemFlagsData, Opcode, ValueDef,
    condcodes::{FloatCC, IntCC},
    types,
};
use cranelift_frontend::FunctionBuilder;
use fz_runtime::any_value::{
    ClosureDenotationId, FALSE_ATOM_ID, NIL_ATOM_ID, STRUCT_HEADER_SCHEMA_SHIFT, ValueKind, closure_header_word,
};
use fz_runtime::heap::{Heap, HeapAllocKind};
use fz_runtime::ir_runtime::{
    fz_list_cons_any, fz_list_cons_atom, fz_list_cons_float, fz_list_cons_int, fz_op_abs_f, fz_op_add_ii, fz_op_eq_ff,
    fz_op_eq_ii, fz_op_gt_ff, fz_op_gt_ii, fz_op_gte_ff, fz_op_gte_ii, fz_op_identical_ii, fz_op_lt_ff, fz_op_lt_ii,
    fz_op_lte_ff, fz_op_lte_ii, fz_op_mul_ii, fz_op_neg_f, fz_op_neg_i, fz_op_neq_ff, fz_op_neq_ii,
    fz_op_not_identical_ii, fz_op_sub_ii, fz_struct_schema_id_ref, fz_truthy_ref, fz_type_of, fz_unbox_atom,
    fz_unbox_int, fz_value_eq_raw_const,
};

/// What a recipe computed, in one of the three shapes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum Emitted {
    Value(ir::Value),
    Condition(ir::Value),
    Checked { value: ir::Value, failed: ir::Value },
}

type InPlace = fn(&mut FunctionBuilder<'_>, &[ir::Value]) -> Option<Emitted>;

/// What a row emits: instructions that compute the function's answer, or the
/// object the function places.
#[derive(Clone, Copy)]
enum Emit {
    InPlace(InPlace),
    Cell(HeadLane),
    Struct,
    Closure,
}

/// One row: the runtime function's symbol, its parameter count, and the
/// instructions that compute its answer or place its object.
pub(crate) struct Recipe {
    pub(crate) symbol: &'static str,
    pub(crate) arity: usize,
    emit: Emit,
}

/// Count of the identifiers given.
macro_rules! count {
    () => { 0usize };
    ($head:ident $($rest:ident)*) => { 1usize + count!($($rest)*) };
}

/// A row. The runtime function is named by its Rust item, which must exist and
/// take as many parameters as the row names; its name is the symbol. The body
/// sees each parameter as an `ir::Value`.
macro_rules! recipe {
    ($item:ident($($param:ident),+), |$b:ident| $body:expr) => {
        Recipe {
            symbol: {
                let _: unsafe extern "C" fn($(recipe!(@lane $param)),+) -> _ = $item;
                stringify!($item)
            },
            arity: count!($($param)+),
            emit: Emit::InPlace(|$b, args| {
                let &[$($param),+] = args else {
                    panic!("recipe `{}` takes {} arguments, got {}", stringify!($item), count!($($param)+), args.len());
                };
                $body
            }),
        }
    };
    (@lane $param:ident) => {
        _
    };
}

/// An allocation row: the runtime function places a list cell whose head
/// reaches it as `$lane` says.
macro_rules! list_cell {
    ($item:ident($process:ident, $head:ident, $tail:ident), $lane:expr) => {
        Recipe {
            symbol: {
                let _: unsafe extern "C" fn(_, _, _) -> _ = $item;
                stringify!($item)
            },
            arity: 3,
            emit: Emit::Cell($lane),
        }
    };
}

/// An allocation row for an object the heap method `$definition` places: the
/// symbol is the method's path, which the `let` checks names a method. The row
/// takes the method's arguments after the process, and `$emit` says how the
/// object is written.
macro_rules! heap_object {
    ($definition:literal, $check:path, $arity:expr, $emit:expr) => {
        Recipe {
            symbol: {
                let _ = $check;
                $definition
            },
            arity: $arity,
            emit: $emit,
        }
    };
}

/// An integer comparison row: an `icmp` of the two words.
macro_rules! int_compare {
    ($item:ident, $cc:expr) => {
        recipe!($item(left, right), |b| Some(Emitted::Condition(
            b.ins().icmp($cc, left, right)
        )))
    };
}

/// A float comparison row: an `fcmp` that answers as the Rust operator does.
macro_rules! float_compare {
    ($item:ident, $cc:expr) => {
        recipe!($item(left, right), |b| Some(Emitted::Condition(
            b.ins().fcmp($cc, left, right)
        )))
    };
}

/// A checked integer row: the wrapped result and whether it overflowed.
macro_rules! overflowing {
    ($item:ident, $op:ident) => {
        recipe!($item(left, right), |b| {
            let (value, failed) = b.ins().$op(left, right);
            Some(Emitted::Checked { value, failed })
        })
    };
}

pub(crate) const RECIPES: &[Recipe] = &[
    // Helpers compiled code calls on a ref word.
    recipe!(fz_type_of(word), |b| {
        let kind = kind_field(b, word);
        Some(Emitted::Value(b.ins().ireduce(types::I8, kind)))
    }),
    recipe!(fz_truthy_ref(word), |b| Some(Emitted::Condition(truthy(b, word)))),
    recipe!(fz_unbox_int(word), |b| {
        let address = address_field(b, word);
        Some(Emitted::Value(b.ins().load(
            types::I64,
            MemFlagsData::trusted(),
            address,
            0,
        )))
    }),
    recipe!(fz_unbox_atom(word), |b| Some(Emitted::Value(address_field(b, word)))),
    recipe!(fz_struct_schema_id_ref(word), |b| {
        let address = address_field(b, word);
        let header = b.ins().load(types::I64, MemFlagsData::trusted(), address, 0);
        let schema = b.ins().ushr_imm_u(header, STRUCT_HEADER_SCHEMA_SHIFT);
        Some(Emitted::Value(b.ins().ireduce(types::I32, schema)))
    }),
    recipe!(fz_value_eq_raw_const(word, expected_kind, raw), |b| {
        let expected = ValueKind::new(u8::try_from(constant_of(b, expected_kind)?).ok()?)?;
        Some(Emitted::Condition(word_is_scalar(b, word, expected, raw)?))
    }),
    // Integer arithmetic.
    overflowing!(fz_op_add_ii, sadd_overflow),
    overflowing!(fz_op_sub_ii, ssub_overflow),
    overflowing!(fz_op_mul_ii, smul_overflow),
    recipe!(fz_op_neg_i(operand), |b| {
        let zero = b.ins().iconst(types::I64, 0);
        let (value, failed) = b.ins().ssub_overflow(zero, operand);
        Some(Emitted::Checked { value, failed })
    }),
    // Integer comparison.
    int_compare!(fz_op_lt_ii, IntCC::SignedLessThan),
    int_compare!(fz_op_lte_ii, IntCC::SignedLessThanOrEqual),
    int_compare!(fz_op_gt_ii, IntCC::SignedGreaterThan),
    int_compare!(fz_op_gte_ii, IntCC::SignedGreaterThanOrEqual),
    int_compare!(fz_op_eq_ii, IntCC::Equal),
    int_compare!(fz_op_neq_ii, IntCC::NotEqual),
    int_compare!(fz_op_identical_ii, IntCC::Equal),
    int_compare!(fz_op_not_identical_ii, IntCC::NotEqual),
    // Float comparison. `NotEqual` is Cranelift's unordered-or-not-equal and
    // the rest are ordered, which is how Rust's `!=`, `<`, `<=`, `>`, `>=` and
    // `==` treat a NaN.
    float_compare!(fz_op_lt_ff, FloatCC::LessThan),
    float_compare!(fz_op_lte_ff, FloatCC::LessThanOrEqual),
    float_compare!(fz_op_gt_ff, FloatCC::GreaterThan),
    float_compare!(fz_op_gte_ff, FloatCC::GreaterThanOrEqual),
    float_compare!(fz_op_eq_ff, FloatCC::Equal),
    float_compare!(fz_op_neq_ff, FloatCC::NotEqual),
    // Float negation and absolute value.
    recipe!(fz_op_neg_f(operand), |b| Some(Emitted::Value(b.ins().fneg(operand)))),
    recipe!(fz_op_abs_f(operand), |b| Some(Emitted::Value(b.ins().fabs(operand)))),
    // List cells.
    list_cell!(fz_list_cons_int(process, head, tail), HeadLane::Int),
    list_cell!(fz_list_cons_float(process, head, tail), HeadLane::Float),
    list_cell!(fz_list_cons_atom(process, head, tail), HeadLane::Atom),
    list_cell!(fz_list_cons_any(process, head, tail), HeadLane::Ref),
    // Structs, tuples and closures: the heap methods the interpreter calls.
    heap_object!(
        "Heap::alloc_struct_unwritten",
        Heap::alloc_struct_unwritten,
        3,
        Emit::Struct
    ),
    heap_object!("Heap::alloc_closure", Heap::alloc_closure, 6, Emit::Closure),
];

/// The row for the runtime function `symbol`, if the table has one.
pub(crate) fn recipe_for(symbol: &str) -> Option<&'static Recipe> {
    RECIPES.iter().find(|row| row.symbol == symbol)
}

/// Emit the instructions for the runtime function `symbol` applied to `args`,
/// or `None` when the table has no row for it or the row declines this
/// instance, and the call is to be emitted instead. A row that places an
/// object is not emitted here, because placing needs the body and its sites:
/// asking for one is a bug, and answered by a panic rather than a call that
/// would quietly bring the runtime path back.
pub(crate) fn emit_inline(b: &mut FunctionBuilder<'_>, symbol: &str, args: &[ir::Value]) -> Option<Emitted> {
    let row = recipe_for(symbol)?;
    assert_eq!(
        args.len(),
        row.arity,
        "recipe `{symbol}` takes {} arguments, got {}",
        row.arity,
        args.len()
    );
    match row.emit {
        Emit::InPlace(emit) => emit(b, args),
        Emit::Cell(_) | Emit::Struct | Emit::Closure => {
            panic!("`{symbol}` places an object; ask for it through `emit_cell` or `emit_object`")
        }
    }
}

/// Place the list cell the runtime function `symbol` places, applied to
/// `args` (the process, the head and the tail), and answer its ref word. The
/// site is registered in `scope`.
pub(crate) fn emit_cell<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    scope: SiteScope<'_>,
    symbol: &str,
    args: &[ir::Value],
) -> ir::Value {
    let row = recipe_for(symbol).unwrap_or_else(|| panic!("`{symbol}` has no recipe"));
    assert_eq!(
        args.len(),
        row.arity,
        "recipe `{symbol}` takes {} arguments, got {}",
        row.arity,
        args.len()
    );
    match row.emit {
        Emit::Cell(lane) => emit_list_cell(body, scope, lane, args),
        Emit::InPlace(_) => panic!("`{symbol}` computes in place; ask for it through `emit_inline`"),
        Emit::Struct | Emit::Closure => {
            panic!("`{symbol}` places a struct or closure; ask for it through `emit_object`")
        }
    }
}

/// Place the struct or closure the heap method `symbol` places, applied to
/// `args`, and write its header. The arguments after the process are
/// constants, except a closure's code address: they fix the object's size and
/// header words when the code is emitted. The site is registered in `scope`.
pub(crate) fn emit_object<M: cranelift_module::Module>(
    body: &mut CodegenFn<'_, '_, M>,
    scope: SiteScope<'_>,
    symbol: &str,
    args: &[ir::Value],
) -> Placed {
    let row = recipe_for(symbol).unwrap_or_else(|| panic!("`{symbol}` has no recipe"));
    assert_eq!(
        args.len(),
        row.arity,
        "recipe `{symbol}` takes {} arguments, got {}",
        row.arity,
        args.len()
    );
    let constant = |index: usize| {
        let word = constant_of(body.b, args[index])
            .unwrap_or_else(|| panic!("`{symbol}` needs argument {index} to be a constant"));
        word as u32
    };
    match row.emit {
        Emit::Struct => emit_struct(body, scope, constant(1), constant(2) as usize),
        Emit::Closure => {
            let count = constant(3) as usize;
            let header = closure_header_word(
                ClosureDenotationId::from_runtime_word(constant(1)),
                u16::try_from(count).expect("a capture count fits the closure header"),
                u16::try_from(constant(4)).expect("a halt kind fits the closure header"),
                u16::try_from(constant(2)).expect("an arity fits the closure header"),
            );
            emit_closure(body, scope, HeapAllocKind::Closure, header, count, args[5])
        }
        Emit::InPlace(_) | Emit::Cell(_) => panic!("`{symbol}` does not place a struct or closure"),
    }
}

/// Whether a ref word is not `false` and not `nil`: every word of another kind
/// is, and an atom is unless it is one of those two.
fn truthy(b: &mut FunctionBuilder<'_>, word: ir::Value) -> ir::Value {
    let kind = kind_field(b, word);
    let is_atom = b.ins().icmp_imm_s(IntCC::Equal, kind, i64::from(ValueKind::ATOM.tag()));
    let id = address_field(b, word);
    let is_false = b.ins().icmp_imm_s(IntCC::Equal, id, i64::from(FALSE_ATOM_ID));
    let is_nil = b.ins().icmp_imm_s(IntCC::Equal, id, i64::from(NIL_ATOM_ID));
    let falsy_id = b.ins().bor(is_false, is_nil);
    let falsy = b.ins().band(is_atom, falsy_id);
    b.ins().bxor_imm_u(falsy, 1)
}

/// Whether `word` is a ref of `kind` whose raw payload is `raw`. Only an atom and an integer have instructions: an atom's payload
/// is its address field, an integer's is the word that address names. The
/// integer is read only after its kind is known, because a word of another
/// kind has an address field that is not an address.
fn word_is_scalar(b: &mut FunctionBuilder<'_>, word: ir::Value, kind: ValueKind, raw: ir::Value) -> Option<ir::Value> {
    let same_kind = {
        let found = kind_field(b, word);
        b.ins().icmp_imm_s(IntCC::Equal, found, i64::from(kind.tag()))
    };
    let answer = match kind {
        ValueKind::ATOM => {
            let id = address_field(b, word);
            let same_id = b.ins().icmp(IntCC::Equal, id, raw);
            b.ins().band(same_kind, same_id)
        }
        ValueKind::INT => same_kind_then(b, same_kind, |b| {
            let address = address_field(b, word);
            let stored = b.ins().load(types::I64, MemFlagsData::trusted(), address, 0);
            b.ins().icmp(IntCC::Equal, stored, raw)
        }),
        _ => return None,
    };
    Some(answer)
}

/// `emit`'s `I8` answer when `condition` holds, and `0` without running `emit`
/// when it does not.
fn same_kind_then(
    b: &mut FunctionBuilder<'_>,
    condition: ir::Value,
    emit: impl FnOnce(&mut FunctionBuilder<'_>) -> ir::Value,
) -> ir::Value {
    let guarded = b.create_block();
    let join = b.create_block();
    b.append_block_param(join, types::I8);
    let no = b.ins().iconst(types::I8, 0);
    b.ins().brif(condition, guarded, &[], join, &[BlockArg::Value(no)]);
    b.switch_to_block(guarded);
    b.seal_block(guarded);
    let answer = emit(b);
    b.ins().jump(join, &[BlockArg::Value(answer)]);
    b.switch_to_block(join);
    b.seal_block(join);
    b.block_params(join)[0]
}

/// The integer `value` was made from, when an `iconst` made it.
fn constant_of(b: &FunctionBuilder<'_>, value: ir::Value) -> Option<i64> {
    let ValueDef::Result(inst, _) = b.func.dfg.value_def(value) else {
        return None;
    };
    match b.func.dfg.insts[inst] {
        InstructionData::UnaryImm {
            opcode: Opcode::Iconst,
            imm,
        } => Some(imm.bits()),
        _ => None,
    }
}

#[cfg(test)]
#[path = "recipe_test.rs"]
mod recipe_test;
