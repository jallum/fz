use super::*;
use crate::fast_hash::HashMap;
use crate::fast_hash::HashSet;
use crate::ir_codegen::backend::{Backend, JitBackend};
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};
use fz_runtime::any_value::AnyValueRefPacking;
use fz_runtime::any_value::{
    AnyValue, AnyValueRef, ClosureDenotationId, FALSE_ATOM_ID, NIL_ATOM_ID, SlotLayout, TRUE_ATOM_ID, ValueKind,
    closure_addr_from_tagged, struct_size_for_payload,
};
use fz_runtime::bits::Bin;
use fz_runtime::heap::{GcStats, Heap, HeapAllocKind, INLINE_ALLOC_LAYOUT, Schema, SchemaRegistry};
use fz_runtime::ir_runtime::*;
use fz_runtime::pinned_abi;
use fz_runtime::process::Process;
use fz_runtime::reuse_site::ReuseKind;
use fz_runtime::site_table::Site;
use std::cell::RefCell;
use std::rc::Rc;

/// What a recipe or its runtime function answered: the value word and the
/// failure word. A float is its bits, a condition is 0 or 1.
type Answer = [u64; 2];

/// The runtime function a row is proved against, called on a full input.
type Reference = Box<dyn Fn(&[u64]) -> Answer>;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Shape {
    Value,
    Condition,
    Checked,
}

impl Shape {
    fn of(emitted: Emitted) -> Self {
        match emitted {
            Emitted::Value(_) => Shape::Value,
            Emitted::Condition(_) => Shape::Condition,
            Emitted::Checked { .. } => Shape::Checked,
        }
    }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Lane {
    Word,
    Float,
}

impl Lane {
    fn ir(self) -> ir::Type {
        match self {
            Lane::Word => types::I64,
            Lane::Float => types::F64,
        }
    }
}

/// A function compiled from one recipe, entered through its lanes. A float
/// travels in the float bank, so each lane mix is its own pointer type.
enum Compiled {
    Words1(extern "C" fn(u64, *mut Answer)),
    Words2(extern "C" fn(u64, u64, *mut Answer)),
    Floats1(extern "C" fn(f64, *mut Answer)),
    Floats2(extern "C" fn(f64, f64, *mut Answer)),
}

impl Compiled {
    fn call(&self, args: &[u64]) -> Answer {
        let mut answer = [0; 2];
        let out: *mut Answer = &mut answer;
        match (self, args) {
            (Compiled::Words1(f), &[a]) => f(a, out),
            (Compiled::Words2(f), &[a, b]) => f(a, b, out),
            (Compiled::Floats1(f), &[a]) => f(f64::from_bits(a), out),
            (Compiled::Floats2(f), &[a, b]) => f(f64::from_bits(a), f64::from_bits(b), out),
            _ => panic!("{} arguments do not fit the compiled lanes", args.len()),
        }
        answer
    }
}

/// An argument the compiled body holds as an `iconst` rather than a parameter,
/// as a call site does for a kind it knows.
#[derive(Clone, Copy)]
struct ConstArg {
    index: usize,
    ty: ir::Type,
    value: i64,
}

/// A row's proof: the shape it answers in, the arguments the compiled body
/// receives, and the runtime function whose answer it must equal over every
/// input. An input holds every argument, constants included.
struct Parity {
    symbol: &'static str,
    shape: Shape,
    lanes: Vec<Lane>,
    consts: Vec<ConstArg>,
    inputs: Vec<Vec<u64>>,
    reference: Reference,
}

struct Jit {
    module: JITModule,
    next: u32,
}

impl Jit {
    fn new() -> Self {
        Jit {
            module: JITModule::new(jit_builder()),
            next: 0,
        }
    }

    /// The recipe's instructions as a function of `parity.lanes`, storing its
    /// answer through a trailing out pointer. Returns the shape the recipe
    /// answered in.
    fn compile(&mut self, parity: &Parity) -> (Compiled, Shape) {
        let mut ctx = self.module.make_context();
        let mut fbctx = FunctionBuilderContext::new();
        let mut sig = self.module.make_signature();
        sig.params
            .extend(parity.lanes.iter().map(|lane| ir::AbiParam::new(lane.ir())));
        sig.params.push(ir::AbiParam::new(types::I64));
        ctx.func.signature = sig.clone();
        let shape = {
            let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
            let entry = b.create_block();
            b.append_block_params_for_function_params(entry);
            b.switch_to_block(entry);
            b.seal_block(entry);
            let params = b.block_params(entry).to_vec();
            let (out, params) = params.split_last().expect("an out pointer");
            let mut args = Vec::new();
            let mut free = params.iter();
            for index in 0..parity.lanes.len() + parity.consts.len() {
                match parity.consts.iter().find(|c| c.index == index) {
                    Some(c) => args.push(b.ins().iconst(c.ty, c.value)),
                    None => args.push(*free.next().expect("a parameter for each free argument")),
                }
            }
            let emitted = emit_inline(&mut b, parity.symbol, &args)
                .unwrap_or_else(|| panic!("`{}` has a row that declined its test instance", parity.symbol));
            let shape = Shape::of(emitted);
            let (value, failed) = match emitted {
                Emitted::Value(value) => (value, None),
                Emitted::Condition(condition) => (condition, None),
                Emitted::Checked { value, failed } => (value, Some(failed)),
            };
            let value = word_of(&mut b, value);
            b.ins().store(MemFlagsData::trusted(), value, *out, 0);
            if let Some(failed) = failed {
                let failed = word_of(&mut b, failed);
                b.ins().store(MemFlagsData::trusted(), failed, *out, 8);
            }
            b.ins().return_(&[]);
            b.finalize(self.module.target_config());
            shape
        };
        let name = format!("recipe_parity_{}", self.next);
        self.next += 1;
        let id = self
            .module
            .declare_function(&name, Linkage::Export, &sig)
            .expect("declare the test function");
        self.module
            .define_function(id, &mut ctx)
            .expect("define the test function");
        self.module.clear_context(&mut ctx);
        self.module.finalize_definitions().expect("finalize the test function");
        let code = self.module.get_finalized_function(id);
        let compiled = unsafe {
            match parity.lanes.as_slice() {
                [Lane::Word] => {
                    Compiled::Words1(std::mem::transmute::<*const u8, extern "C" fn(u64, *mut Answer)>(code))
                }
                [Lane::Word, Lane::Word] => Compiled::Words2(std::mem::transmute::<
                    *const u8,
                    extern "C" fn(u64, u64, *mut Answer),
                >(code)),
                [Lane::Float] => {
                    Compiled::Floats1(std::mem::transmute::<*const u8, extern "C" fn(f64, *mut Answer)>(code))
                }
                [Lane::Float, Lane::Float] => Compiled::Floats2(std::mem::transmute::<
                    *const u8,
                    extern "C" fn(f64, f64, *mut Answer),
                >(code)),
                other => panic!("no entry for lanes {other:?}"),
            }
        };
        (compiled, shape)
    }
}

/// `value` widened to the 64 bits an answer holds; a float keeps its bits.
fn word_of(b: &mut FunctionBuilder<'_>, value: ir::Value) -> ir::Value {
    match b.func.dfg.value_type(value) {
        types::I64 | types::F64 => value,
        _ => b.ins().uextend(types::I64, value),
    }
}

/// The arguments the compiled body takes: an input without its constants.
fn free_args(parity: &Parity, input: &[u64]) -> Vec<u64> {
    input
        .iter()
        .enumerate()
        .filter(|(index, _)| parity.consts.iter().all(|c| c.index != *index))
        .map(|(_, word)| *word)
        .collect()
}

/// The values every word-taking row is tried on: one of each kind a ref can
/// name, and a literal-bit form of each heap kind.
struct Words {
    all: Vec<u64>,
    ints: Vec<u64>,
    atoms: Vec<u64>,
    structs: Vec<u64>,
    _heap: Heap,
}

/// Binaries in both forms, with and without the literal bit, and the
/// `(binary, bit_pos)` inputs the extent rows are tried on.
/// The heap is leaked: the inputs are addresses into it and outlive the proofs.
fn binary_extent_inputs() -> Vec<Vec<u64>> {
    let heap = Box::leak(Box::new(Heap::new(
        1 << 16,
        Rc::new(RefCell::new(SchemaRegistry::new())),
    )));
    let mut inputs = Vec::new();
    for bit_len in [0u64, 3, 8, 11, 512, 600, 1000] {
        let bytes = vec![0xa5u8; bit_len.div_ceil(8) as usize];
        let word = heap.alloc_bitstring(&bytes, bit_len).ref_word();
        for word in [word, word.literal()] {
            for bit_pos in [0, 1, 3, 8, 11, 511, 999, bit_len] {
                if bit_pos <= bit_len {
                    inputs.push(vec![word.raw_word(), bit_pos]);
                }
            }
        }
    }
    inputs
}

const OTHER_ATOM_ID: u32 = 7;

fn int_ref(heap: &mut Heap, value: i64) -> AnyValueRef {
    heap.box_any_value_ref(AnyValue::int(value))
}

fn words() -> Words {
    let mut heap = Heap::new(4096, Rc::new(RefCell::new(SchemaRegistry::new())));
    let pair = heap.register_schema(Schema::tuple_of_arity(2));
    let triple = heap.register_schema(Schema::tuple_of_arity(3));
    let record = heap.register_schema(Schema::named_struct(
        fz_runtime::module_name::ModuleName::from_segments(vec!["Point".into()]),
        ["x".to_string()],
    ));
    let ints: Vec<AnyValueRef> = INTEGERS.iter().map(|value| int_ref(&mut heap, *value)).collect();
    let atoms: Vec<AnyValueRef> = [TRUE_ATOM_ID, FALSE_ATOM_ID, NIL_ATOM_ID, OTHER_ATOM_ID]
        .iter()
        .map(|id| AnyValueRef::atom(*id))
        .collect();
    let structs: Vec<AnyValueRef> = [pair, triple, record]
        .iter()
        .map(|schema| {
            let address = heap.alloc_struct(*schema);
            AnyValueRef::from_heap_object(ValueKind::STRUCT, address).expect("a struct ref")
        })
        .collect();
    let floats: Vec<AnyValueRef> = [1.5, -0.0, 0.0]
        .iter()
        .map(|value| heap.box_any_value_ref(AnyValue::float(*value)))
        .collect();
    let cons = heap.alloc_list_cons_any(AnyValue::int(1), AnyValue::EmptyList);
    let bitstring = heap.alloc_bitstring(&[1, 2, 3], 24).ref_word();
    let mut all = Vec::new();
    all.extend([AnyValueRef::null(), AnyValueRef::empty_list(), cons, bitstring]);
    all.extend([AnyValueRef::pid(5).expect("a pid ref")]);
    all.extend(ints.iter().chain(&floats).chain(&atoms).chain(&structs));
    let literals: Vec<AnyValueRef> = [ints[1], floats[0], cons, structs[0], bitstring]
        .iter()
        .map(|word| word.literal())
        .collect();
    all.extend(literals);
    let raw = |refs: &[AnyValueRef]| refs.iter().map(|word| word.raw_word()).collect::<Vec<_>>();
    let mut ints_with_literal = raw(&ints);
    ints_with_literal.push(ints[1].literal().raw_word());
    let mut structs_with_literal = raw(&structs);
    structs_with_literal.push(structs[0].literal().raw_word());
    Words {
        all: raw(&all),
        ints: ints_with_literal,
        atoms: raw(&atoms),
        structs: structs_with_literal,
        _heap: heap,
    }
}

const INTEGERS: [i64; 9] = [0, 1, -1, 2, -2, i64::MIN, i64::MAX, 3_037_000_500, -3_037_000_500];

const FLOATS: [f64; 13] = [
    0.0,
    -0.0,
    1.5,
    -1.5,
    5e-324,
    -5e-324,
    f64::MIN_POSITIVE,
    1e300,
    -1e300,
    f64::INFINITY,
    f64::NEG_INFINITY,
    f64::NAN,
    -f64::NAN,
];

fn integer_words() -> Vec<u64> {
    INTEGERS.iter().map(|value| *value as u64).collect()
}

fn float_words() -> Vec<u64> {
    FLOATS.iter().map(|value| value.to_bits()).collect()
}

fn pairs(left: &[u64], right: &[u64]) -> Vec<Vec<u64>> {
    left.iter()
        .flat_map(|l| right.iter().map(move |r| vec![*l, *r]))
        .collect()
}

fn singles(words: &[u64]) -> Vec<Vec<u64>> {
    words.iter().map(|word| vec![*word]).collect()
}

fn value(word: u64) -> Answer {
    [word, 0]
}

fn checked(result: FzIntegerArithmeticResult) -> Answer {
    [result.result as u64, result.failed]
}

fn parity(
    symbol: &'static str,
    shape: Shape,
    lanes: &[Lane],
    inputs: Vec<Vec<u64>>,
    reference: impl Fn(&[u64]) -> Answer + 'static,
) -> Parity {
    Parity {
        symbol,
        shape,
        lanes: lanes.to_vec(),
        consts: Vec::new(),
        inputs,
        reference: Box::new(reference),
    }
}

fn integer_compare(symbol: &'static str, reference: extern "C" fn(i64, i64) -> u64) -> Parity {
    let ints = integer_words();
    parity(
        symbol,
        Shape::Condition,
        &[Lane::Word; 2],
        pairs(&ints, &ints),
        move |a| value(reference(a[0] as i64, a[1] as i64)),
    )
}

fn float_compare(symbol: &'static str, reference: extern "C" fn(f64, f64) -> u64) -> Parity {
    let floats = float_words();
    parity(
        symbol,
        Shape::Condition,
        &[Lane::Float; 2],
        pairs(&floats, &floats),
        move |a| value(reference(f64::from_bits(a[0]), f64::from_bits(a[1]))),
    )
}

fn integer_arithmetic(symbol: &'static str, reference: extern "C" fn(i64, i64) -> FzIntegerArithmeticResult) -> Parity {
    let ints = integer_words();
    parity(
        symbol,
        Shape::Checked,
        &[Lane::Word; 2],
        pairs(&ints, &ints),
        move |a| checked(reference(a[0] as i64, a[1] as i64)),
    )
}

/// A total integer row over every pair of integers.
fn integer_pair_value(symbol: &'static str, reference: extern "C" fn(i64, i64) -> i64) -> Parity {
    let ints = integer_words();
    parity(symbol, Shape::Value, &[Lane::Word; 2], pairs(&ints, &ints), move |a| {
        value(reference(a[0] as i64, a[1] as i64) as u64)
    })
}

/// A shift row over every integer and the counts around each boundary: zero,
/// the widest left shift, the first count past it, and their negatives.
fn integer_shift(symbol: &'static str, reference: extern "C" fn(i64, i64) -> FzIntegerArithmeticResult) -> Parity {
    let counts: Vec<u64> = [0, 1, 2, 62, 63, 64, 65, -1, -2, -62, -63, -64, -65, i64::MIN, i64::MAX]
        .iter()
        .map(|count: &i64| *count as u64)
        .collect();
    parity(
        symbol,
        Shape::Checked,
        &[Lane::Word; 2],
        pairs(&integer_words(), &counts),
        move |a| checked(reference(a[0] as i64, a[1] as i64)),
    )
}

/// `fz_value_eq_raw_const` for a call site that knows the constant kind.
fn eq_raw_const(kind: ValueKind, words: &Words, raws: Vec<u64>) -> Parity {
    Parity {
        symbol: "fz_value_eq_raw_const",
        shape: Shape::Condition,
        lanes: vec![Lane::Word; 2],
        consts: vec![ConstArg {
            index: 1,
            ty: types::I32,
            value: i64::from(kind.tag()),
        }],
        inputs: words
            .all
            .iter()
            .flat_map(|word| raws.iter().map(move |raw| vec![*word, u64::from(kind.tag()), *raw]))
            .collect(),
        reference: Box::new(|a| value(fz_value_eq_raw_const(a[0], a[1] as u32, a[2]))),
    }
}

/// Every row of the table, with the inputs and the runtime function that
/// prove it. A row absent here fails `every_row_is_proved_against_its_runtime_function`.
fn proofs() -> Vec<Parity> {
    let w = words();
    let binary_inputs = binary_extent_inputs();
    let ints = integer_words();
    let floats = float_words();
    let atom_ids: Vec<u64> = [TRUE_ATOM_ID, FALSE_ATOM_ID, NIL_ATOM_ID, OTHER_ATOM_ID]
        .iter()
        .map(|id| u64::from(*id))
        .chain([0, u64::MAX])
        .collect();
    vec![
        parity("fz_type_of", Shape::Value, &[Lane::Word], singles(&w.all), |a| {
            value(u64::from(fz_type_of(a[0])))
        }),
        parity("fz_truthy_ref", Shape::Condition, &[Lane::Word], singles(&w.all), |a| {
            value(u64::from(fz_truthy_ref(a[0])))
        }),
        parity("fz_unbox_int", Shape::Value, &[Lane::Word], singles(&w.ints), |a| {
            value(fz_unbox_int(a[0]) as u64)
        }),
        parity("fz_unbox_atom", Shape::Value, &[Lane::Word], singles(&w.atoms), |a| {
            value(fz_unbox_atom(a[0]))
        }),
        parity(
            "fz_struct_schema_id_ref",
            Shape::Value,
            &[Lane::Word],
            singles(&w.structs),
            |a| value(u64::from(fz_struct_schema_id_ref(a[0]))),
        ),
        parity(
            "fz_struct_is_named_ref",
            Shape::Condition,
            &[Lane::Word],
            singles(&w.structs),
            |a| value(u64::from(fz_struct_is_named_ref(a[0]))),
        ),
        parity(
            "fz_bitstring_byte_extent",
            Shape::Value,
            &[Lane::Word, Lane::Word],
            binary_inputs.clone(),
            |a| value(fz_bitstring_byte_extent(a[0], a[1]) as u64),
        ),
        parity(
            "fz_bitstring_bit_extent",
            Shape::Value,
            &[Lane::Word, Lane::Word],
            binary_inputs,
            |a| value(fz_bitstring_bit_extent(a[0], a[1]) as u64),
        ),
        eq_raw_const(ValueKind::ATOM, &w, atom_ids),
        eq_raw_const(ValueKind::INT, &w, ints.clone()),
        integer_arithmetic("fz_op_add_ii", fz_op_add_ii),
        integer_arithmetic("fz_op_sub_ii", fz_op_sub_ii),
        integer_arithmetic("fz_op_mul_ii", fz_op_mul_ii),
        parity("fz_op_neg_i", Shape::Checked, &[Lane::Word], singles(&ints), |a| {
            checked(fz_op_neg_i(a[0] as i64))
        }),
        integer_pair_value("fz_op_band_ii", fz_op_band_ii),
        integer_pair_value("fz_op_bor_ii", fz_op_bor_ii),
        integer_pair_value("fz_op_bxor_ii", fz_op_bxor_ii),
        parity("fz_op_bnot_i", Shape::Value, &[Lane::Word], singles(&ints), |a| {
            value(fz_op_bnot_i(a[0] as i64) as u64)
        }),
        integer_shift("fz_op_bsl_ii", fz_op_bsl_ii),
        integer_shift("fz_op_bsr_ii", fz_op_bsr_ii),
        integer_compare("fz_op_lt_ii", fz_op_lt_ii),
        integer_compare("fz_op_lte_ii", fz_op_lte_ii),
        integer_compare("fz_op_gt_ii", fz_op_gt_ii),
        integer_compare("fz_op_gte_ii", fz_op_gte_ii),
        integer_compare("fz_op_eq_ii", fz_op_eq_ii),
        integer_compare("fz_op_neq_ii", fz_op_neq_ii),
        integer_compare("fz_op_identical_ii", fz_op_identical_ii),
        integer_compare("fz_op_not_identical_ii", fz_op_not_identical_ii),
        float_compare("fz_op_lt_ff", fz_op_lt_ff),
        float_compare("fz_op_lte_ff", fz_op_lte_ff),
        float_compare("fz_op_gt_ff", fz_op_gt_ff),
        float_compare("fz_op_gte_ff", fz_op_gte_ff),
        float_compare("fz_op_eq_ff", fz_op_eq_ff),
        float_compare("fz_op_neq_ff", fz_op_neq_ff),
        parity("fz_op_neg_f", Shape::Value, &[Lane::Float], singles(&floats), |a| {
            value(fz_op_neg_f(f64::from_bits(a[0])).to_bits())
        }),
        parity("fz_op_abs_f", Shape::Value, &[Lane::Float], singles(&floats), |a| {
            value(fz_op_abs_f(f64::from_bits(a[0])).to_bits())
        }),
    ]
}

/// A row's instructions answer, over every input its proof lists, exactly what
/// the runtime function answers: the Rust function stays the definition.
#[test]
fn every_row_computes_what_its_runtime_function_computes() {
    let mut jit = Jit::new();
    for proof in proofs() {
        let (compiled, shape) = jit.compile(&proof);
        assert_eq!(shape, proof.shape, "`{}` answers in the wrong shape", proof.symbol);
        assert!(!proof.inputs.is_empty(), "`{}` has no inputs", proof.symbol);
        for input in &proof.inputs {
            let inline = compiled.call(&free_args(&proof, input));
            let expected = (proof.reference)(input);
            let words = |answer: Answer| match proof.shape {
                Shape::Checked => answer,
                _ => [answer[0], 0],
            };
            assert_eq!(
                words(inline),
                words(expected),
                "`{}` on {input:x?}: inline {inline:x?}, runtime {expected:x?}",
                proof.symbol
            );
        }
    }
}

/// A row cannot exist without its proof, and a proof cannot name a row that
/// does not exist.
#[test]
fn every_row_is_proved_against_its_runtime_function() {
    let proved: HashSet<&str> = proofs()
        .iter()
        .map(|proof| proof.symbol)
        .chain(cell_proofs().iter().map(|proof| proof.symbol))
        .chain(box_proofs().iter().map(|proof| proof.symbol))
        .chain(BINARY_COMPARISONS.iter().map(|(symbol, ..)| *symbol))
        .chain(ATOM_ROWS.iter().map(|(symbol, ..)| *symbol))
        .chain([SLICE_SYMBOL])
        .chain(REUSE_SYMBOLS)
        .collect();
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let proved: HashSet<&str> = proved
        .into_iter()
        .chain(object_proofs(&schemas).iter().map(|proof| proof.symbol))
        .collect();
    let rows: HashSet<&str> = RECIPES.iter().map(|row| row.symbol).collect();
    assert_eq!(rows.len(), RECIPES.len(), "a symbol has two rows");
    let unproved: Vec<_> = rows.difference(&proved).collect();
    let orphaned: Vec<_> = proved.difference(&rows).collect();
    assert!(unproved.is_empty(), "rows with no proof: {unproved:?}");
    assert!(orphaned.is_empty(), "proofs with no row: {orphaned:?}");
}

/// A row decides what it can inline from the call site. `fz_value_eq_raw_const`
/// has instructions for an atom and an integer only, and only when the kind is
/// a constant; any other instance is a call.
#[test]
fn a_row_declines_the_instance_it_has_no_instructions_for() {
    let jit = Jit::new();
    let mut ctx = jit.module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.switch_to_block(entry);
    b.seal_block(entry);
    let word = b.ins().iconst(types::I64, 0);
    let raw = b.ins().iconst(types::I64, 0);
    for kind in [ValueKind::FLOAT, ValueKind::LIST, ValueKind::STRUCT] {
        let tag = b.ins().iconst(types::I32, i64::from(kind.tag()));
        assert_eq!(
            emit_inline(&mut b, "fz_value_eq_raw_const", &[word, tag, raw]),
            None,
            "{kind:?} has no instructions"
        );
    }
    let unknown = b.ins().iadd(word, raw);
    let unknown = b.ins().ireduce(types::I32, unknown);
    assert_eq!(
        emit_inline(&mut b, "fz_value_eq_raw_const", &[word, unknown, raw]),
        None,
        "a kind that is not a constant is not inlined"
    );
    b.ins().return_(&[]);
    b.finalize(jit.module.target_config());
}

/// A symbol with no row is a call.
#[test]
fn a_symbol_without_a_row_is_a_call() {
    assert!(recipe_for("fz_op_div_ii").is_none());
}

// Allocation rows are proved on heaps. Each case builds the same objects in
// two fresh processes, runs the runtime function in one and the row's
// instructions in the other, and compares everything the run left behind.

/// What a case hands the row: its head word and, for a row that takes the
/// head's kind from a register, that kind, and the address its list tail
/// holds (0 for the empty list), and the objects the row may change by sharing
/// them.
struct CellInputs {
    head: u64,
    head_kind: u64,
    tail: u64,
    watched: Vec<*const u8>,
}

struct CellCase {
    name: &'static str,
    build: Box<dyn Fn(&mut Heap) -> CellInputs>,
}

/// How a row is handed the head's kind.
#[derive(Clone, Copy)]
enum HeadKindArg {
    /// The head is a ref word, which holds its own kind.
    InTheRef,
    /// The kind is a constant of the call site.
    Constant(ValueKind),
    /// The kind is in a register, as a case gives it.
    InARegister,
}

/// A row's proof: the runtime function it must agree with, and the heads and
/// tails it is tried on. A head's word is its stored word for a row that is
/// handed a kind and a ref word for the ref row.
struct CellProof {
    symbol: &'static str,
    head_kind: HeadKindArg,
    /// The runtime function's answer for a process, the head's word and kind,
    /// and the tail's word and kind.
    reference: fn(*mut Process, u64, u64, u64, u64) -> u64,
    cases: Vec<CellCase>,
}

impl CellProof {
    /// The kind the runtime function is handed for a case.
    fn kind_for(&self, inputs: &CellInputs) -> u64 {
        match self.head_kind {
            HeadKindArg::InTheRef => 0,
            HeadKindArg::Constant(kind) => u64::from(kind.tag()),
            HeadKindArg::InARegister => inputs.head_kind,
        }
    }
}

fn case(name: &'static str, build: impl Fn(&mut Heap) -> CellInputs + 'static) -> CellCase {
    CellCase {
        name,
        build: Box::new(build),
    }
}

/// A case whose head word is `head` and whose tail is the empty list or a
/// one-cell list.
fn scalar_cases(heads: &[(&'static str, u64)]) -> Vec<CellCase> {
    let mut cases = Vec::new();
    for &(name, head) in heads {
        cases.push(case(name, move |_| CellInputs {
            head,
            head_kind: 0,
            tail: list_storage(AnyValueRef::empty_list()),
            watched: Vec::new(),
        }));
        cases.push(case(name, move |heap| {
            let tail = heap
                .alloc_list_cons_int(9, AnyValueRef::empty_list())
                .expect("a one-cell tail");
            CellInputs {
                head,
                head_kind: 0,
                tail: list_storage(tail),
                watched: vec![list_address(tail)],
            }
        }));
    }
    cases
}

/// The word a list tail is handed over as: the address its cell has, 0 for `[]`.
fn list_storage(list: AnyValueRef) -> u64 {
    list.storage_raw().expect("a list tail address")
}

fn list_address(list: AnyValueRef) -> *const u8 {
    list.list_addr().expect("a list address") as *const u8
}

/// A list of `len` cells holding 1, 2, ..., with no cell shared.
fn int_list(heap: &mut Heap, len: i64) -> (AnyValueRef, Vec<*const u8>) {
    let mut list = AnyValueRef::empty_list();
    let mut cells = Vec::new();
    for value in (1..=len).rev() {
        list = heap.alloc_list_cons_int(value, list).expect("a cell");
        cells.push(list_address(list));
    }
    (list, cells)
}

fn ref_cases() -> Vec<CellCase> {
    let mut cases = Vec::new();
    let mut head = |name: &'static str, make: fn(&mut Heap) -> (AnyValueRef, Vec<*const u8>)| {
        cases.push(case(name, move |heap| {
            let (head, watched) = make(heap);
            CellInputs {
                head: head.raw_word(),
                head_kind: 0,
                tail: list_storage(AnyValueRef::empty_list()),
                watched,
            }
        }));
        cases.push(case(name, move |heap| {
            let (head, mut watched) = make(heap);
            let (tail, cells) = int_list(heap, 2);
            watched.extend(cells);
            CellInputs {
                head: head.raw_word(),
                head_kind: 0,
                tail: list_storage(tail),
                watched,
            }
        }));
    };
    head("an int box", |heap| (int_ref(heap, -7), Vec::new()));
    head("a float box", |heap| {
        (heap.box_any_value_ref(AnyValue::float(1.5)), Vec::new())
    });
    head("a reference box", |heap| {
        (heap.box_any_value_ref(AnyValue::Opaque(ValueKind::REF, 9)), Vec::new())
    });
    head("an atom", |_| (AnyValueRef::atom(7), Vec::new()));
    head("a pid", |_| (AnyValueRef::pid(5).expect("a pid ref"), Vec::new()));
    head("null", |_| (AnyValueRef::null(), Vec::new()));
    head("the empty list", |_| (AnyValueRef::empty_list(), Vec::new()));
    head("a bitstring", |heap| {
        let bitstring = heap.alloc_bitstring(&[1, 2, 3], 24).ref_word();
        let address = bitstring.bitstring_addr().expect("a bitstring") as *const u8;
        (bitstring, vec![address])
    });
    head("an unshared list", |heap| int_list(heap, 3));
    head("a literal list", |heap| {
        let (list, cells) = int_list(heap, 2);
        (list.literal(), cells)
    });
    head("a list shared from its second cell", |heap| {
        let (list, cells) = int_list(heap, 3);
        let second = AnyValueRef::from_heap_object(ValueKind::LIST, cells[1]).expect("a list ref");
        heap.mark_published_ref_aliased(second).expect("a shared tail");
        (list, cells)
    });
    head("a list shared whole", |heap| {
        let (list, cells) = int_list(heap, 2);
        heap.mark_published_ref_aliased(list).expect("a shared list");
        (list, cells)
    });
    head("a struct", |heap| {
        let pair = heap.register_schema(Schema::tuple_of_arity(2));
        let address = heap.alloc_struct(pair);
        (
            AnyValueRef::from_heap_object(ValueKind::STRUCT, address).expect("a struct ref"),
            vec![address as *const u8],
        )
    });
    cases
}

fn cell_proofs() -> Vec<CellProof> {
    let ints = [
        ("zero", 0),
        ("one", 1),
        ("minus one", u64::MAX),
        ("max", i64::MAX as u64),
        ("min", i64::MIN as u64),
    ];
    let floats = [1.5f64, -0.0, 0.0, 5e-324, -1e300].map(|value| ("a float", value.to_bits()));
    let atoms = [
        ("true", u64::from(TRUE_ATOM_ID)),
        ("nil", u64::from(NIL_ATOM_ID)),
        ("another", u64::from(OTHER_ATOM_ID)),
    ];
    let stored = |head_kind, cases| CellProof {
        symbol: "fz_list_cons_stored",
        head_kind,
        reference: |process, head, kind, tail, tail_kind| fz_list_cons_stored(process, head, kind, tail, tail_kind),
        cases,
    };
    vec![
        stored(HeadKindArg::Constant(ValueKind::INT), scalar_cases(&ints)),
        stored(HeadKindArg::Constant(ValueKind::FLOAT), scalar_cases(&floats)),
        stored(HeadKindArg::Constant(ValueKind::ATOM), scalar_cases(&atoms)),
        stored(HeadKindArg::InARegister, stored_cases()),
        CellProof {
            symbol: "fz_list_cons_any",
            head_kind: HeadKindArg::InTheRef,
            reference: |process, head, _kind, tail, tail_kind| fz_list_cons_any(process, head, tail, tail_kind),
            cases: ref_cases(),
        },
    ]
}

/// The ref cases with each head spelled as the stored word and kind a value
/// that travels as a pair holds.
fn stored_cases() -> Vec<CellCase> {
    ref_cases()
        .into_iter()
        .map(|CellCase { name, build }| {
            case(name, move |heap| {
                let inputs = build(heap);
                let head = AnyValueRef::from_raw_word(inputs.head).expect("a head ref");
                let pair = fz_runtime::any_value::Stored::of(AnyValue::from_ref(head).expect("a head value"));
                CellInputs {
                    head: pair.word,
                    head_kind: pair.kind,
                    ..inputs
                }
            })
        })
        .collect()
}

/// The kind a list tail travels with.
const LIST_KIND_WORD: u64 = ValueKind::LIST.tag() as u64;

/// The allocation site a table's entry is.
pub(in crate::compiler2::native_codegen) fn allocation_site(site: &Site) -> &fz_runtime::alloc_site::AllocSite {
    match site {
        Site::Alloc(site) => site,
        Site::Reuse(site) => panic!("expected an allocation site, found {site:?}"),
    }
}

/// A row compiled to a function of two words: the head's and the tail's.
struct CompiledCell {
    code: *const u8,
    /// The row's site counters, one word per site.
    counts: *const u64,
    _backend: JitBackend,
}

fn compile_cell(proof: &CellProof) -> CompiledCell {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    let words = match proof.head_kind {
        HeadKindArg::InARegister => 3,
        HeadKindArg::InTheRef | HeadKindArg::Constant(_) => 2,
    };
    sig.params = vec![ir::AbiParam::new(types::I64); words];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(SiteTable::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let params = b.block_params(entry).to_vec();
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let process = body.process_arg();
        let list_kind = body.b.ins().iconst(types::I64, i64::from(ValueKind::LIST.tag()));
        let cell = match proof.head_kind {
            HeadKindArg::InTheRef => emit_cell(&mut body, proof.symbol, &[process, params[0], params[1], list_kind]),
            HeadKindArg::Constant(kind) => {
                let kind = body.b.ins().iconst(types::I64, i64::from(kind.tag()));
                emit_cell(
                    &mut body,
                    proof.symbol,
                    &[process, params[0], kind, params[1], list_kind],
                )
            }
            HeadKindArg::InARegister => emit_cell(
                &mut body,
                proof.symbol,
                &[process, params[0], params[1], params[2], list_kind],
            ),
        };
        body.b.ins().return_(&[cell]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_cell", Linkage::Export, &sig)
        .expect("declare the cell function");
    module.define_function(id, &mut ctx).expect("define the cell function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    assert_eq!(registered.len(), 1, "one placement is one site");
    assert_eq!(allocation_site(&registered[0]).kind, HeapAllocKind::ListCons);
    assert_eq!(allocation_site(&registered[0]).bytes, 16);
    module.finalize_definitions().expect("finalize the cell function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    CompiledCell {
        code,
        counts: counts.cast(),
        _backend: backend,
    }
}

/// How full a tip is when the row runs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::compiler2::native_codegen) enum Tip {
    /// Room for the cell.
    Roomy,
    /// No room: the runtime must find some.
    Full,
}

/// Everything a run leaves that the two runs must agree on, with each address
/// replaced by the block it is in and its offset there.
#[derive(Debug, PartialEq, Eq)]
struct Left {
    result: u64,
    cell: [u64; 2],
    watched: Vec<[u64; 2]>,
    tip_used: usize,
    tip_capacity: usize,
    tip_changed: bool,
}

pub(in crate::compiler2::native_codegen) fn heap_field(process: &Process, offset: usize) -> usize {
    unsafe { *(((&process.heap as *const Heap).cast::<u8>()).add(offset) as *const usize) }
}

pub(in crate::compiler2::native_codegen) fn tip_of(process: &Process) -> (usize, usize) {
    let start = heap_field(process, INLINE_ALLOC_LAYOUT.block_start);
    (start, heap_field(process, INLINE_ALLOC_LAYOUT.block_end) - start)
}

/// A word with the address it holds replaced by `(block, offset)` when the
/// address is in one of `blocks`.
fn rebased(word: u64, blocks: [(usize, usize); 2]) -> u64 {
    let packing = AnyValueRefPacking::current();
    let address = packing.raw_address(word);
    for (index, (start, length)) in blocks.into_iter().enumerate() {
        if address >= start && address < start + length {
            return (word & !packing.address_mask()) | ((index as u64 + 1) << 40) | (address - start) as u64;
        }
    }
    word
}

fn words_at(address: *const u8) -> [u64; 2] {
    unsafe { [*address.cast::<u64>(), *address.cast::<u64>().add(1)] }
}

/// Build the case in a fresh process, bring its tip to `tip`, run `run` on it
/// and say what was left.
fn run_cell(
    case: &CellCase,
    tip: Tip,
    schemas: &Rc<RefCell<SchemaRegistry>>,
    run: impl FnOnce(*mut Process, &CellInputs) -> u64,
) -> Left {
    let mut process = Box::new(Process::new(schemas.clone()));
    let inputs = (case.build)(&mut process.heap);
    if tip == Tip::Full {
        while tip_of(&process).1 - (heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - tip_of(&process).0) >= 16 {
            process.heap.alloc(16);
        }
    }
    let before = tip_of(&process);
    let result = run(&mut *process, &inputs);
    let after = tip_of(&process);
    let blocks = [before, after];
    let address = AnyValueRefPacking::current().raw_address(result) as *const u8;
    Left {
        result: rebased(result, blocks),
        cell: words_at(address).map(|word| rebased(word, blocks)),
        watched: inputs
            .watched
            .iter()
            .map(|object| words_at(*object).map(|word| rebased(word, blocks)))
            .collect(),
        tip_used: heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - after.0,
        tip_capacity: after.1,
        tip_changed: before != after,
    }
}

/// A row, run on heaps over every case and both tip states, leaves what its
/// runtime function leaves: the cell's words, the objects it shares, the tip
/// and the statistics. The runtime function stays the definition.
#[test]
fn every_allocation_row_leaves_the_heap_its_runtime_function_leaves() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    for proof in cell_proofs() {
        let compiled = compile_cell(&proof);
        let mut runs = 0;
        for case in &proof.cases {
            for tip in [Tip::Roomy, Tip::Full] {
                let expected = run_cell(case, tip, &schemas, |process, inputs| {
                    (proof.reference)(
                        process,
                        inputs.head,
                        proof.kind_for(inputs),
                        inputs.tail,
                        LIST_KIND_WORD,
                    )
                });
                let inline = run_cell(case, tip, &schemas, |process, inputs| unsafe {
                    let answer = match proof.head_kind {
                        HeadKindArg::InARegister => {
                            pinned_abi::call3(compiled.code, process, inputs.head, inputs.head_kind, inputs.tail)
                        }
                        _ => pinned_abi::call2(compiled.code, process, inputs.head, inputs.tail),
                    };
                    answer as u64
                });
                runs += 1;
                assert_eq!(
                    inline.tip_changed,
                    tip == Tip::Full,
                    "`{}` on {} with a {tip:?} tip: the tip moved only when it had no room",
                    proof.symbol,
                    case.name
                );
                assert_eq!(
                    inline, expected,
                    "`{}` on {} with a {tip:?} tip: inline against the runtime function",
                    proof.symbol, case.name
                );
            }
        }
        let counted = unsafe { *compiled.counts };
        assert_eq!(counted, runs, "`{}` counts its site once per placement", proof.symbol);
    }
}

/// A list or struct head is shared, so the run must have marked something;
/// the harness would pass vacuously if the proofs never shared anything.
#[test]
fn the_rows_that_take_a_heap_head_are_tried_on_heads_that_must_be_shared() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    for proof in cell_proofs()
        .iter()
        .filter(|proof| matches!(proof.head_kind, HeadKindArg::InTheRef | HeadKindArg::InARegister))
    {
        let case = proof
            .cases
            .iter()
            .find(|case| case.name == "an unshared list")
            .expect("a case");
        let left = run_cell(case, Tip::Roomy, &schemas, |process, inputs| {
            (proof.reference)(
                process,
                inputs.head,
                proof.kind_for(inputs),
                inputs.tail,
                LIST_KIND_WORD,
            )
        });
        let link = left.watched[0][1];
        assert!(
            link & fz_runtime::any_value::LIST_LINK_ALIAS_MASK != 0,
            "`{}`: a list head is shared by the cell",
            proof.symbol
        );
    }
}

// Struct and closure rows are proved the same way, on the words the code
// writes: a struct's header, and a closure's header and code address. The
// slots and kind bytes that follow are written by the code that builds the
// object, and the runtime path leaves them for it too (a closure's are zeroed
// first, then overwritten).

/// How a struct or closure row is tried: the object it places.
#[derive(Clone, Copy)]
enum Object {
    Struct {
        schema: u32,
    },
    Closure {
        denotation: ClosureDenotationId,
        arity: u16,
        captures: usize,
        halt_kind: u16,
    },
}

struct ObjectCase {
    name: String,
    object: Object,
}

struct ObjectProof {
    symbol: &'static str,
    cases: Vec<ObjectCase>,
}

/// The code address every closure case is given.
const CODE_ADDRESS: u64 = 0x1234_5678_9abc;

/// Tuples of several sizes, named structs, and a size past the largest block
/// a tip steps up to, so the runtime parks the object alone.
fn struct_cases(schemas: &Rc<RefCell<SchemaRegistry>>) -> Vec<ObjectCase> {
    let register = |name: String, schema: Schema| ObjectCase {
        name,
        object: Object::Struct {
            schema: schemas.borrow_mut().register(schema),
        },
    };
    let mut cases: Vec<_> = [0, 1, 2, 3, 7, 8, 9, 16, 200]
        .into_iter()
        .map(|arity| register(format!("a {arity}-tuple"), Schema::tuple_of_arity(arity)))
        .collect();
    cases.push(register("a Range".to_owned(), Schema::range()));
    let name = fz_runtime::module_name::ModuleName::from_segments(vec!["Point".into()]);
    cases.push(register(
        "a named struct of five fields".to_owned(),
        Schema::named_struct(name, ["a", "b", "c", "d", "e"].map(String::from)),
    ));
    cases
}

/// Closures of no, one and many captures, of every halt kind, with the
/// denotations a program's closures carry and the internal one.
fn closure_cases() -> Vec<ObjectCase> {
    let closure = |captures, denotation, arity, halt_kind| ObjectCase {
        name: format!("a closure of {captures} captures, arity {arity}, halt kind {halt_kind}"),
        object: Object::Closure {
            denotation,
            arity,
            captures,
            halt_kind,
        },
    };
    let mut cases: Vec<_> = [0, 1, 2, 7, 8, 9, 100, 200]
        .into_iter()
        .map(|captures| closure(captures, ClosureDenotationId::user(5), 2, 0))
        .collect();
    for halt_kind in 1..=3 {
        cases.push(closure(3, ClosureDenotationId::user(70_000), 0, halt_kind));
    }
    cases.push(closure(1, ClosureDenotationId::INTERNAL, 1, 0));
    cases.push(closure(4, ClosureDenotationId::user(0), 255, 2));
    cases
}

fn object_proofs(schemas: &Rc<RefCell<SchemaRegistry>>) -> Vec<ObjectProof> {
    vec![
        ObjectProof {
            symbol: "Heap::alloc_struct_unwritten",
            cases: struct_cases(schemas),
        },
        ObjectProof {
            symbol: "Heap::alloc_closure",
            cases: closure_cases(),
        },
    ]
}

/// A struct or closure row compiled to a function of the code address.
struct CompiledObject {
    code: *const u8,
    counts: *const u64,
    _backend: JitBackend,
}

/// The object's size as the compiled code derives it: from the field or
/// capture count alone.
fn compiled_size(object: Object, schemas: &SchemaRegistry) -> usize {
    match object {
        Object::Struct { schema } => SlotLayout::of(schemas.get(schema).value_field_count()).size(),
        Object::Closure { captures, .. } => fz_runtime::any_value::closure_size_for_count(captures),
    }
}

fn compile_object(case: &ObjectCase, schemas: &Rc<RefCell<SchemaRegistry>>) -> CompiledObject {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    sig.params = vec![ir::AbiParam::new(types::I64)];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(SiteTable::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let code = b.block_params(entry)[0];
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let reference = match case.object {
            Object::Struct { schema } => {
                let fields = schemas.borrow().get(schema).value_field_count();
                let name = schemas.borrow().get(schema).struct_name();
                body.alloc_struct(schema, name, fields).reference
            }
            Object::Closure {
                denotation,
                arity,
                captures,
                halt_kind,
            } => {
                let arity = body.b.ins().iconst(types::I32, i64::from(arity));
                let captures = body.b.ins().iconst(types::I32, captures as i64);
                let halt_kind = body.b.ins().iconst(types::I32, i64::from(halt_kind));
                body.alloc_closure(denotation, arity, captures, halt_kind, code)
            }
        };
        body.b.ins().return_(&[reference]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_object", Linkage::Export, &sig)
        .expect("declare the object function");
    module
        .define_function(id, &mut ctx)
        .expect("define the object function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    assert_eq!(registered.len(), 1, "one placement is one site");
    let expected_kind = match case.object {
        Object::Struct { .. } => HeapAllocKind::Struct,
        Object::Closure { .. } => HeapAllocKind::Closure,
    };
    assert_eq!(allocation_site(&registered[0]).kind, expected_kind);
    assert_eq!(
        allocation_site(&registered[0]).bytes as usize,
        compiled_size(case.object, &schemas.borrow())
    );
    module.finalize_definitions().expect("finalize the object function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    CompiledObject {
        code,
        counts: counts.cast(),
        _backend: backend,
    }
}

/// Everything an object run leaves that the two runs must agree on. The
/// result word and the object's own words name addresses by the block they
/// are in and the offset there; an object parked alone is in neither block,
/// so only that fact is compared.
#[derive(Debug, PartialEq, Eq)]
struct ObjectLeft {
    result: u64,
    words: Vec<u64>,
    tip_used: usize,
    tip_capacity: usize,
    tip_changed: bool,
}

pub(in crate::compiler2::native_codegen) fn words_of(address: *const u8, count: usize) -> Vec<u64> {
    (0..count)
        .map(|index| unsafe { *address.cast::<u64>().add(index) })
        .collect()
}

/// Bring a fresh process's tip to `tip`, run `run` and say what was left.
/// `defined` is how many words from the object's start the code writes.
fn run_object(
    tip: Tip,
    defined: usize,
    schemas: &Rc<RefCell<SchemaRegistry>>,
    run: impl FnOnce(*mut Process) -> u64,
) -> ObjectLeft {
    let mut process = Box::new(Process::new(schemas.clone()));
    if tip == Tip::Full {
        while tip_of(&process).1 - (heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - tip_of(&process).0) >= 16 {
            process.heap.alloc(16);
        }
    }
    let before = tip_of(&process);
    let result = run(&mut *process);
    let after = tip_of(&process);
    let blocks = [before, after];
    let packing = AnyValueRefPacking::current();
    let address = packing.raw_address(result);
    let in_a_block = blocks
        .iter()
        .any(|(start, length)| address >= *start && address < start + length);
    let place = |word: u64| {
        if in_a_block {
            rebased(word, blocks)
        } else {
            word & !packing.address_mask()
        }
    };
    ObjectLeft {
        result: place(result),
        words: words_of(address as *const u8, defined),
        tip_used: heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - after.0,
        tip_capacity: after.1,
        tip_changed: before != after,
    }
}

/// What the runtime does to place the object: the heap method that is the
/// row's definition, then the ref word a caller holds.
fn place_in_runtime(object: Object, schemas: &SchemaRegistry, process: *mut Process) -> u64 {
    let heap = &mut unsafe { &mut *process }.heap;
    match object {
        Object::Struct { schema } => {
            let size = struct_size_for_payload(schemas.get(schema).allocation_payload_size());
            let address = heap.alloc_struct_unwritten(schemas.struct_header(schema), size);
            AnyValueRef::from_heap_object(ValueKind::STRUCT, address)
                .expect("a struct ref")
                .raw_word()
        }
        Object::Closure {
            denotation,
            arity,
            captures,
            halt_kind,
        } => {
            let bits = heap.alloc_closure(denotation, arity, captures, halt_kind, CODE_ADDRESS, &[]);
            let address = closure_addr_from_tagged(bits).expect("a closure address");
            AnyValueRef::from_heap_object(ValueKind::CLOSURE, address)
                .expect("a closure ref")
                .raw_word()
        }
    }
}

fn defined_words(object: Object) -> usize {
    match object {
        Object::Struct { .. } => 1,
        Object::Closure { .. } => 2,
    }
}

/// A struct or closure row, run on heaps over every case and both tip states,
/// writes the words its heap method writes and leaves the heap as it leaves
/// it: the tip, the object count and every statistic.
#[test]
fn every_object_row_leaves_the_heap_its_heap_method_leaves() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    for proof in object_proofs(&schemas) {
        for case in &proof.cases {
            let compiled = compile_object(case, &schemas);
            let defined = defined_words(case.object);
            let size = compiled_size(case.object, &schemas.borrow());
            for tip in [Tip::Roomy, Tip::Full] {
                let expected = run_object(tip, defined, &schemas, |process| {
                    place_in_runtime(case.object, &schemas.borrow(), process)
                });
                let inline = run_object(tip, defined, &schemas, |process| unsafe {
                    pinned_abi::call1(compiled.code, process, CODE_ADDRESS) as u64
                });
                if size <= 512 {
                    assert_eq!(
                        inline.tip_changed,
                        tip == Tip::Full,
                        "`{}` on {} with a {tip:?} tip: the tip moved only when it had no room",
                        proof.symbol,
                        case.name
                    );
                }
                assert_eq!(
                    inline, expected,
                    "`{}` on {} with a {tip:?} tip: inline against the heap method",
                    proof.symbol, case.name
                );
            }
            let counted = unsafe { *compiled.counts };
            assert_eq!(
                counted, 2,
                "`{}` on {} counts its site once per placement",
                proof.symbol, case.name
            );
        }
    }
}

/// A word every placed object must leave clear: a live object's header has
/// its low four bits free for the forwarding marker, and a new struct is
/// unshared.
#[test]
fn a_placed_header_leaves_the_forwarding_nibble_and_the_shared_bit_clear() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    for proof in object_proofs(&schemas) {
        for case in &proof.cases {
            let compiled = compile_object(case, &schemas);
            let left = run_object(Tip::Roomy, 1, &schemas, |process| unsafe {
                pinned_abi::call1(compiled.code, process, CODE_ADDRESS) as u64
            });
            assert_eq!(
                left.words[0] & 0xf,
                0,
                "`{}` on {}: forwarding nibble",
                proof.symbol,
                case.name
            );
            if matches!(case.object, Object::Struct { .. }) {
                assert_eq!(
                    left.words[0] & fz_runtime::any_value::STRUCT_HEADER_SHARED_MASK,
                    0,
                    "`{}` on {}: a new struct is unshared",
                    proof.symbol,
                    case.name
                );
            }
        }
    }
}

// Scalar box rows are proved on the one word the runtime writes, with the
// result word: the box's address under the value's kind.

/// A box row's proof: the runtime function it must agree with and the payload
/// words it is tried on. A float payload is the float's bits.
struct BoxProof {
    symbol: &'static str,
    lane: BoxLane,
    kind: ValueKind,
    reference: fn(*mut Process, u64) -> u64,
    payloads: Vec<(&'static str, u64)>,
}

fn box_proofs() -> Vec<BoxProof> {
    let ints = [
        ("zero", 0),
        ("one", 1),
        ("minus one", u64::MAX),
        ("max", i64::MAX as u64),
        ("min", i64::MIN as u64),
    ];
    let floats = [
        ("a float", 1.5f64.to_bits()),
        ("negative zero", (-0.0f64).to_bits()),
        ("zero", 0.0f64.to_bits()),
        ("a subnormal", 5e-324f64.to_bits()),
        ("the smallest normal", f64::MIN_POSITIVE.to_bits()),
        ("the largest", f64::MAX.to_bits()),
        ("a large negative", (-1e300f64).to_bits()),
    ];
    let references = [("zero", 0), ("a word", 9), ("a full word", u64::MAX)];
    vec![
        BoxProof {
            symbol: "fz_box_int_for_any",
            lane: BoxLane::Int,
            kind: ValueKind::INT,
            reference: |process, payload| fz_box_int_for_any(process, payload as i64),
            payloads: ints.to_vec(),
        },
        BoxProof {
            symbol: "fz_box_float_for_any",
            lane: BoxLane::Float,
            kind: ValueKind::FLOAT,
            reference: |process, payload| fz_box_float_for_any(process, f64::from_bits(payload)),
            payloads: floats.to_vec(),
        },
        BoxProof {
            symbol: "fz_box_opaque_for_any",
            lane: BoxLane::Opaque,
            kind: ValueKind::REF,
            reference: |process, payload| fz_box_opaque_for_any(process, payload, u64::from(ValueKind::REF.tag())),
            payloads: references.to_vec(),
        },
    ]
}

/// A box row compiled to a function of the payload word, and the runtime
/// functions its code imports.
struct CompiledBox {
    object: CompiledObject,
    imports: Vec<String>,
}

fn compile_box(proof: &BoxProof) -> CompiledBox {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    sig.params = vec![ir::AbiParam::new(types::I64)];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(SiteTable::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let payload = b.block_params(entry)[0];
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let process = body.process_arg();
        let reference = match proof.lane {
            BoxLane::Int => emit_box(&mut body, proof.symbol, &[process, payload]),
            BoxLane::Float => {
                let float = body.b.ins().bitcast(types::F64, MemFlagsData::new(), payload);
                emit_box(&mut body, proof.symbol, &[process, float])
            }
            BoxLane::Opaque => {
                let kind = body.b.ins().iconst(types::I64, i64::from(proof.kind.tag()));
                emit_box(&mut body, proof.symbol, &[process, payload, kind])
            }
        };
        body.b.ins().return_(&[reference]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_box", Linkage::Export, &sig)
        .expect("declare the box function");
    module.define_function(id, &mut ctx).expect("define the box function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    assert_eq!(registered.len(), 1, "one placement is one site");
    assert_eq!(allocation_site(&registered[0]).kind, HeapAllocKind::ScalarBox);
    assert_eq!(allocation_site(&registered[0]).bytes, 16);
    let imports = module
        .declarations()
        .get_functions()
        .filter(|(_, declaration)| declaration.linkage == Linkage::Import)
        .filter_map(|(_, declaration)| declaration.name.clone())
        .collect();
    module.finalize_definitions().expect("finalize the box function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    CompiledBox {
        object: CompiledObject {
            code,
            counts: counts.cast(),
            _backend: backend,
        },
        imports,
    }
}

/// A box row, run on heaps over every payload and both tip states, writes the
/// word its runtime function writes and leaves the heap as it leaves it: the
/// ref word, the tip, the object count and every statistic.
#[test]
fn every_box_row_leaves_the_heap_its_runtime_function_leaves() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    for proof in box_proofs() {
        let compiled = compile_box(&proof);
        for &(name, payload) in &proof.payloads {
            for tip in [Tip::Roomy, Tip::Full] {
                let expected = run_object(tip, 1, &schemas, |process| (proof.reference)(process, payload));
                let inline = run_object(tip, 1, &schemas, |process| unsafe {
                    pinned_abi::call1(compiled.object.code, process, payload) as u64
                });
                assert_eq!(
                    inline.tip_changed,
                    tip == Tip::Full,
                    "`{}` on {name} with a {tip:?} tip: the tip moved only when it had no room",
                    proof.symbol
                );
                assert_eq!(
                    inline, expected,
                    "`{}` on {name} with a {tip:?} tip: inline against the runtime function",
                    proof.symbol
                );
                assert_eq!(
                    inline.result >> AnyValueRefPacking::current().tag_shift(),
                    u64::from(proof.kind.tag()),
                    "`{}` on {name}: the ref word's kind",
                    proof.symbol
                );
            }
        }
        let counted = unsafe { *compiled.object.counts };
        assert_eq!(
            counted,
            2 * proof.payloads.len() as u64,
            "`{}` counts its site once per placement",
            proof.symbol
        );
    }
}

/// A float that is not finite is not a language value, and the runtime function
/// refuses it. The float row hands such a float to that function rather than
/// boxing it, and the int and opaque rows have no such path.
#[test]
fn only_the_float_row_can_reach_the_runtime_function_for_a_value_it_refuses() {
    for proof in box_proofs() {
        let compiled = compile_box(&proof);
        assert_eq!(
            compiled.imports.iter().any(|name| name == "fz_box_float_for_any"),
            proof.lane == BoxLane::Float,
            "`{}`: whether its code can call fz_box_float_for_any",
            proof.symbol
        );
    }
}

// List reuse rows decide between the source cell and a new one. They are
// proved on every head kind, against a tail that is the source's, another
// list or empty, with the source shared and not, with and without permission
// to rewrite, and with a tip that has room and one that has none.

const REUSE_SYMBOLS: [&str; 2] = [REUSE_REF_HEAD, "fz_list_reuse_or_cons_parts"];

/// The source cell: an int head 1 over the tail, with the tail's cells and
/// the other tail a case may hand over.
struct ReuseWorld {
    source: AnyValueRef,
    tail: AnyValueRef,
    other_tail: AnyValueRef,
    watched: Vec<*const u8>,
}

fn reuse_world(heap: &mut Heap, shared: bool) -> ReuseWorld {
    let (tail, mut watched) = int_list(heap, 2);
    let (other_tail, others) = int_list(heap, 1);
    let source = heap.alloc_list_cons_int(1, tail).expect("a source cell");
    if shared {
        heap.mark_published_ref_aliased(source).expect("a shared source");
    }
    watched.insert(0, list_address(source));
    watched.extend(others);
    ReuseWorld {
        source,
        tail,
        other_tail,
        watched,
    }
}

/// A replacement head: the ref word that names it, and the objects it may
/// have shared.
struct ReuseHead {
    name: &'static str,
    /// Whether a parts call can hand this head over as a payload and a kind.
    parts: bool,
    make: fn(&mut Heap, &ReuseWorld) -> (AnyValueRef, Vec<*const u8>),
}

fn reuse_heads() -> Vec<ReuseHead> {
    fn head(name: &'static str, make: fn(&mut Heap, &ReuseWorld) -> (AnyValueRef, Vec<*const u8>)) -> ReuseHead {
        ReuseHead {
            name,
            parts: true,
            make,
        }
    }
    vec![
        head("the source's own int", |heap, _| (int_ref(heap, 1), Vec::new())),
        head("another int", |heap, _| (int_ref(heap, 2), Vec::new())),
        head("a float", |heap, _| {
            (heap.box_any_value_ref(AnyValue::float(1.5)), Vec::new())
        }),
        head("a reference box", |heap, _| {
            (heap.box_any_value_ref(AnyValue::Opaque(ValueKind::REF, 9)), Vec::new())
        }),
        head("an atom", |_, _| (AnyValueRef::atom(7), Vec::new())),
        head("a pid", |_, _| (AnyValueRef::pid(5).expect("a pid ref"), Vec::new())),
        head("null", |_, _| (AnyValueRef::null(), Vec::new())),
        head("the empty list", |_, _| (AnyValueRef::empty_list(), Vec::new())),
        head("a bitstring", |heap, _| {
            let bitstring = heap.alloc_bitstring(&[1, 2, 3], 24).ref_word();
            let address = bitstring.bitstring_addr().expect("a bitstring") as *const u8;
            (bitstring, vec![address])
        }),
        head("an unshared list", |heap, _| int_list(heap, 3)),
        head("a list shared from its second cell", |heap, _| {
            let (list, cells) = int_list(heap, 3);
            let second = AnyValueRef::from_heap_object(ValueKind::LIST, cells[1]).expect("a list ref");
            heap.mark_published_ref_aliased(second).expect("a shared tail");
            (list, cells)
        }),
        head("a list shared whole", |heap, _| {
            let (list, cells) = int_list(heap, 2);
            heap.mark_published_ref_aliased(list).expect("a shared list");
            (list, cells)
        }),
        head("a struct", |heap, _| {
            let pair = heap.register_schema(Schema::tuple_of_arity(2));
            let address = heap.alloc_struct(pair);
            (
                AnyValueRef::from_heap_object(ValueKind::STRUCT, address).expect("a struct ref"),
                vec![address as *const u8],
            )
        }),
        head("the source cell itself", |_, world| (world.source, Vec::new())),
        ReuseHead {
            name: "a literal list",
            parts: false,
            make: |heap, _| {
                let (list, cells) = int_list(heap, 2);
                (list.literal(), cells)
            },
        },
    ]
}

#[derive(Clone, Copy, Debug)]
enum ReuseTail {
    Same,
    Other,
    Empty,
}

impl ReuseTail {
    fn word(self, world: &ReuseWorld) -> u64 {
        match self {
            Self::Same => world.tail,
            Self::Other => world.other_tail,
            Self::Empty => AnyValueRef::empty_list(),
        }
        .storage_raw()
        .expect("a list tail address")
    }
}

/// One run's inputs. A parts call carries the head's payload word and kind.
struct ReuseInputs {
    source: u64,
    head: u64,
    head_kind: ValueKind,
    tail: u64,
    watched: Vec<*const u8>,
}

fn reuse_inputs(heap: &mut Heap, head: &ReuseHead, tail: ReuseTail, shared: bool, parts: bool) -> ReuseInputs {
    let world = reuse_world(heap, shared);
    let (value, mut watched) = (head.make)(heap, &world);
    let tail_word = tail.word(&world);
    let mut all = world.watched.clone();
    all.append(&mut watched);
    ReuseInputs {
        source: world.source.raw_word(),
        head: if parts {
            value.storage_raw().expect("a head payload")
        } else {
            value.raw_word()
        },
        head_kind: value.tag(),
        tail: tail_word,
        watched: all,
    }
}

/// Everything a run leaves that the two runs must agree on.
#[derive(Debug, PartialEq, Eq)]
struct ReuseLeft {
    result: u64,
    /// Whether the answer is a cell the call placed.
    fresh: bool,
    words: Vec<[u64; 2]>,
    answer: [u64; 2],
    tip_used: usize,
    tip_capacity: usize,
    tip_changed: bool,
    retention: (u64, u64),
    binaries_shared: u64,
}

/// The program's list reuses as `(attempts, hits)`.
fn list_reuses(process: &Process) -> (u64, u64) {
    let list = process.node.retention_stats().list;
    (list.attempts(), list.hits)
}

/// The compiled row's reuse site, which owns the table's first two words:
/// `(hits, misses)`.
fn site_reuses(compiled: &CompiledCell) -> (u64, u64) {
    unsafe { (*compiled.counts, *compiled.counts.add(1)) }
}

/// What the compiled row's site counted since `before`, as `(attempts, hits)`.
fn reuses_since(compiled: &CompiledCell, before: (u64, u64)) -> (u64, u64) {
    let (hits, misses) = site_reuses(compiled);
    (hits + misses - before.0 - before.1, hits - before.0)
}

fn run_reuse(
    tip: Tip,
    schemas: &Rc<RefCell<SchemaRegistry>>,
    build: impl FnOnce(&mut Heap) -> ReuseInputs,
    run: impl FnOnce(*mut Process, &ReuseInputs) -> u64,
    retention: impl FnOnce(&Process) -> (u64, u64),
) -> ReuseLeft {
    let mut process = Box::new(Process::new(schemas.clone()));
    let inputs = build(&mut process.heap);
    if tip == Tip::Full {
        while tip_of(&process).1 - (heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - tip_of(&process).0) >= 16 {
            process.heap.alloc(16);
        }
    }
    let before = tip_of(&process);
    let result = run(&mut *process, &inputs);
    let after = tip_of(&process);
    let blocks = [before, after];
    let address = AnyValueRefPacking::current().raw_address(result) as *const u8;
    ReuseLeft {
        result: rebased(result, blocks),
        fresh: result != inputs.source,
        words: inputs
            .watched
            .iter()
            .map(|object| words_at(*object).map(|word| rebased(word, blocks)))
            .collect(),
        answer: words_at(address).map(|word| rebased(word, blocks)),
        tip_used: heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - after.0,
        tip_capacity: after.1,
        tip_changed: before != after,
        retention: retention(&process),
        binaries_shared: process.heap.binaries_shared(),
    }
}

/// A reuse row compiled to a function of the source, head and tail words,
/// with the head's kind and the permission to rewrite as constants.
fn compile_reuse(lane: ReuseLane, kind: ValueKind, rewrite: bool) -> CompiledCell {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    sig.params = vec![ir::AbiParam::new(types::I64); 3];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(SiteTable::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let params = b.block_params(entry).to_vec();
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let process = body.process_arg();
        let permission = body.b.ins().iconst(types::I64, i64::from(rewrite));
        let list_kind = body.b.ins().iconst(types::I64, i64::from(ValueKind::LIST.tag()));
        let answer = match lane {
            ReuseLane::Ref => emit_reuse(
                &mut body,
                REUSE_REF_HEAD,
                &[process, params[0], params[1], params[2], list_kind, permission],
            ),
            ReuseLane::Parts => {
                let kind = body.b.ins().iconst(types::I64, i64::from(kind.tag()));
                emit_reuse(
                    &mut body,
                    "fz_list_reuse_or_cons_parts",
                    &[process, params[0], params[1], kind, params[2], list_kind, permission],
                )
            }
        };
        body.b.ins().return_(&[answer]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_reuse", Linkage::Export, &sig)
        .expect("declare the reuse function");
    module.define_function(id, &mut ctx).expect("define the reuse function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    assert_eq!(registered.len(), 2, "one reuse site, and the placement of a new cell");
    assert!(
        matches!(&registered[0], Site::Reuse(site) if site.kind == ReuseKind::List),
        "{:?}",
        registered[0]
    );
    assert!(
        matches!(&registered[1], Site::Alloc(site) if site.kind == HeapAllocKind::ListCons && site.bytes == 16),
        "{:?}",
        registered[1]
    );
    module.finalize_definitions().expect("finalize the reuse function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    CompiledCell {
        code,
        counts: counts.cast(),
        _backend: backend,
    }
}

/// What a run of the whole matrix saw, so the proof can say it was not vacuous.
#[derive(Default)]
struct ReuseCoverage {
    hits_unchanged: u64,
    hits_rewritten: u64,
    fresh_on_alias: u64,
    fresh_without_permission: u64,
    shared_head: u64,
    head_miss: u64,
    tail_miss: u64,
}

/// A reuse row, run on heaps over every head, tail, source state, permission
/// and tip, answers the cell its runtime function answers and leaves the heap
/// as it leaves it: the cells' words, the tip, the statistics, the retention
/// counters and the binaries shared.
#[test]
fn every_list_reuse_row_leaves_the_heap_its_runtime_function_leaves() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut coverage = ReuseCoverage::default();
    for lane in [ReuseLane::Ref, ReuseLane::Parts] {
        let parts = lane == ReuseLane::Parts;
        for head in reuse_heads().iter().filter(|head| head.parts || !parts) {
            let kind = {
                let mut probe = Box::new(Process::new(schemas.clone()));
                let world = reuse_world(&mut probe.heap, false);
                (head.make)(&mut probe.heap, &world).0.tag()
            };
            for rewrite in [false, true] {
                let compiled = compile_reuse(lane, kind, rewrite);
                let mut fresh_runs = 0;
                let mut runs = 0;
                for tail in [ReuseTail::Same, ReuseTail::Other, ReuseTail::Empty] {
                    for shared in [false, true] {
                        for tip in [Tip::Roomy, Tip::Full] {
                            let build = |heap: &mut Heap| reuse_inputs(heap, head, tail, shared, parts);
                            let reference = |process: *mut Process, inputs: &ReuseInputs| match lane {
                                ReuseLane::Ref => {
                                    let head = AnyValueRef::from_raw_word(inputs.head).expect("a head ref");
                                    fz_list_reuse_or_cons_parts(
                                        process,
                                        inputs.source,
                                        head.storage_raw().expect("a head payload"),
                                        u64::from(head.tag().tag()),
                                        inputs.tail,
                                        LIST_KIND_WORD,
                                        rewrite as u64,
                                    )
                                }
                                ReuseLane::Parts => fz_list_reuse_or_cons_parts(
                                    process,
                                    inputs.source,
                                    inputs.head,
                                    u64::from(inputs.head_kind.tag()),
                                    inputs.tail,
                                    LIST_KIND_WORD,
                                    rewrite as u64,
                                ),
                            };
                            let expected = run_reuse(tip, &schemas, build, reference, list_reuses);
                            let before = site_reuses(&compiled);
                            let inline = run_reuse(
                                tip,
                                &schemas,
                                build,
                                |process, inputs| unsafe {
                                    pinned_abi::call3(compiled.code, process, inputs.source, inputs.head, inputs.tail)
                                        as u64
                                },
                                |_| reuses_since(&compiled, before),
                            );
                            let name = format!(
                                "{lane:?} on {} over {tail:?}, shared {shared}, rewrite {rewrite}, {tip:?} tip",
                                head.name
                            );
                            assert_eq!(inline, expected, "{name}: inline against the runtime function");
                            assert_eq!(
                                inline.tip_changed,
                                inline.fresh && tip == Tip::Full,
                                "{name}: the tip moves only for a new cell with no room"
                            );
                            fresh_runs += u64::from(inline.fresh);
                            runs += 1;
                            let (attempts, hits) = inline.retention;
                            assert_eq!(attempts, 1, "{name}: one attempt");
                            assert_eq!(hits, u64::from(!inline.fresh), "{name}: a hit is a reused cell");
                            coverage.note(&inline, &expected, rewrite, shared, head.name, tail);
                        }
                    }
                }
                let (hits, misses) = site_reuses(&compiled);
                assert_eq!(misses, fresh_runs, "{lane:?} counts a miss once per new cell");
                let placed = unsafe { *compiled.counts.add(2) };
                assert_eq!(
                    placed, fresh_runs,
                    "{lane:?} counts its allocation site once per new cell"
                );
                assert_eq!(hits + misses, runs, "{lane:?} counts every run once, at one counter");
            }
        }
    }
    coverage.assert_complete();
}

impl ReuseCoverage {
    fn note(
        &mut self,
        inline: &ReuseLeft,
        _expected: &ReuseLeft,
        rewrite: bool,
        shared: bool,
        head: &str,
        tail: ReuseTail,
    ) {
        let same_head = head == "the source's own int";
        let same_tail = matches!(tail, ReuseTail::Same);
        if same_head && same_tail {
            self.hits_unchanged += u64::from(!inline.fresh);
        }
        if !same_head || !same_tail {
            if !inline.fresh {
                self.hits_rewritten += 1;
            } else if rewrite && shared {
                self.fresh_on_alias += 1;
            } else if !rewrite {
                self.fresh_without_permission += 1;
            }
        }
        self.head_miss += u64::from(!same_head && same_tail);
        self.tail_miss += u64::from(same_head && !same_tail);
        self.shared_head += u64::from(matches!(head, "an unshared list" | "a struct" | "a bitstring"));
    }

    fn assert_complete(&self) {
        assert!(self.hits_unchanged > 0, "no run reused an unchanged cell");
        assert!(self.hits_rewritten > 0, "no run rewrote a cell in place");
        assert!(self.fresh_on_alias > 0, "no run replaced a shared source");
        assert!(
            self.fresh_without_permission > 0,
            "no run replaced for want of permission"
        );
        assert!(
            self.head_miss > 0 && self.tail_miss > 0,
            "a miss on the head and one on the tail"
        );
        assert!(self.shared_head > 0, "no run shared a head");
    }
}

/// One reuse bumps exactly one counter of its own site: a cell that is kept as
/// it is raises the site's hits, and a new cell raises its misses.
#[test]
fn one_inline_reuse_raises_exactly_its_sites_hit_or_miss() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let compiled = compile_reuse(ReuseLane::Ref, ValueKind::INT, true);
    let heads = reuse_heads();
    let own_int = heads
        .iter()
        .find(|head| head.name == "the source's own int")
        .expect("a head");
    let other_int = heads.iter().find(|head| head.name == "another int").expect("a head");
    let reuse = |head: &ReuseHead, tail: ReuseTail, shared: bool| {
        let before = site_reuses(&compiled);
        let left = run_reuse(
            Tip::Roomy,
            &schemas,
            |heap| reuse_inputs(heap, head, tail, shared, false),
            |process, inputs| unsafe {
                pinned_abi::call3(compiled.code, process, inputs.source, inputs.head, inputs.tail) as u64
            },
            |_| (0, 0),
        );
        let after = site_reuses(&compiled);
        (left.fresh, (after.0 - before.0, after.1 - before.1))
    };

    assert_eq!(reuse(own_int, ReuseTail::Same, false), (false, (1, 0)), "kept: one hit");
    assert_eq!(
        reuse(other_int, ReuseTail::Same, false),
        (false, (1, 0)),
        "rewritten in place: one hit"
    );
    assert_eq!(
        reuse(other_int, ReuseTail::Same, true),
        (true, (0, 1)),
        "a shared source is replaced: one miss"
    );
}

/// A head that is the source cell itself is shared before the alias bit is
/// read, so an unshared source cannot be rewritten to hold itself.
#[test]
fn a_source_that_is_its_own_new_head_is_replaced_not_rewritten() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let compiled = compile_reuse(ReuseLane::Ref, ValueKind::LIST, true);
    let heads = reuse_heads();
    let head = heads
        .iter()
        .find(|head| head.name == "the source cell itself")
        .expect("a head");
    let left = run_reuse(
        Tip::Roomy,
        &schemas,
        |heap| reuse_inputs(heap, head, ReuseTail::Same, false, false),
        |process, inputs| unsafe {
            pinned_abi::call3(compiled.code, process, inputs.source, inputs.head, inputs.tail) as u64
        },
        |_| reuses_since(&compiled, (0, 0)),
    );
    assert!(left.fresh, "the source became shared, so a new cell holds it");
    assert_eq!(left.retention, (1, 0));
}

/// A source cell a collection kept is old, and a minor collection does not look
/// inside an old cell, so a new head written into it could go unseen. The row
/// replaces it with a new cell, as its runtime function does, and counts the
/// replacement as an old target; a young unshared source is rewritten.
#[test]
fn an_old_unshared_source_is_replaced_and_counted_as_an_old_target() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let compiled = compile_reuse(ReuseLane::Parts, ValueKind::INT, true);
    let kept_source = |process: &mut Process| {
        let (tail, _) = int_list(&mut process.heap, 2);
        let mut roots = [process.heap.alloc_list_cons_int(1, tail).expect("a source cell")];
        drop(process.heap.collect(&mut roots, &mut GcStats::default()));
        roots[0]
    };
    let new_head = 9u64;
    let int_kind = u64::from(ValueKind::INT.tag());

    let mut inline = Box::new(Process::new(schemas.clone()));
    let source = kept_source(&mut inline);
    let tail = fz_list_tail_ref(source.raw_word());
    let answered = unsafe { pinned_abi::call3(compiled.code, &mut *inline, source.raw_word(), new_head, tail) as u64 };
    assert_ne!(answered, source.raw_word(), "the old cell is replaced");
    assert_eq!(inline.heap.old_targets_copied(), 1);
    assert_eq!(site_reuses(&compiled), (0, 1), "a miss, no hit");

    let mut reference = Box::new(Process::new(schemas.clone()));
    let source = kept_source(&mut reference);
    let tail = fz_list_tail_ref(source.raw_word());
    let process: *mut Process = &mut *reference;
    let answered = fz_list_reuse_or_cons_parts(process, source.raw_word(), new_head, int_kind, tail, LIST_KIND_WORD, 1);
    assert_ne!(answered, source.raw_word(), "the runtime function replaces it too");
    assert_eq!(reference.heap.old_targets_copied(), 1);

    let mut young = Box::new(Process::new(schemas));
    let (tail, _) = int_list(&mut young.heap, 2);
    let source = young.heap.alloc_list_cons_int(1, tail).expect("a source cell");
    let tail = fz_list_tail_ref(source.raw_word());
    let answered = unsafe { pinned_abi::call3(compiled.code, &mut *young, source.raw_word(), new_head, tail) as u64 };
    assert_eq!(answered, source.raw_word(), "a young unshared cell is rewritten");
    assert_eq!(young.heap.old_targets_copied(), 0);
}

// Binary comparison rows answer a condition, and call the runtime function only
// to read the bytes of two different objects. They are proved on binaries of
// every form and relation the rows distinguish.

type BinaryFunction = extern "C" fn(*mut Process, u64, u64) -> u64;

/// Each row's symbol, its runtime function, and whether a binary compared
/// with itself answers true.
const BINARY_COMPARISONS: [(&str, BinaryFunction, bool); 6] = [
    ("fz_op_eq_bb", fz_op_eq_bb, true),
    ("fz_op_neq_bb", fz_op_neq_bb, false),
    ("fz_op_lt_bb", fz_op_lt_bb, false),
    ("fz_op_lte_bb", fz_op_lte_bb, true),
    ("fz_op_gt_bb", fz_op_gt_bb, false),
    ("fz_op_gte_bb", fz_op_gte_bb, true),
];

/// A binary comparison row compiled to a function of the process and the two
/// tagged words, and the runtime functions its code imports.
struct CompiledComparison {
    code: BinaryFunction,
    imports: Vec<String>,
    /// The row left the operation to the runtime function.
    declined: bool,
    _backend: JitBackend,
}

fn compile_comparison(symbol: &str) -> CompiledComparison {
    compile_row(symbol, Operands::Words)
}

/// What a compiled row's operands are.
#[derive(Clone, Copy, PartialEq)]
enum Operands {
    /// The process and two words.
    Words,
    /// The process and two stored values whose kinds are parameters, so unknown.
    Stored,
    /// The process and two atom ids, each known by its constant kind.
    Atoms,
}

/// The row of a function of two stored values, each operand's kind the constant
/// atom kind, compiled to a function of the process and the two atom ids.
fn compile_atom_row(symbol: &str) -> CompiledComparison {
    compile_row(symbol, Operands::Atoms)
}

fn compile_row(symbol: &str, operands: Operands) -> CompiledComparison {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    sig.params = vec![ir::AbiParam::new(types::I64); if operands == Operands::Stored { 5 } else { 3 }];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(SiteTable::declare(module).expect("declare the site counters"));
    let mut declined = false;
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let mut args = b.block_params(entry).to_vec();
        if operands == Operands::Atoms {
            let kind = b.ins().iconst(types::I64, i64::from(ValueKind::ATOM.tag()));
            args = vec![args[0], args[1], kind, args[2], kind];
        }
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let word = match emit_in_body(&mut body, symbol, &args) {
            Some(Emitted::Condition(condition)) => body.b.ins().uextend(types::I64, condition),
            Some(Emitted::Value(word)) => word,
            None if operands == Operands::Stored => {
                declined = true;
                body.b.ins().iconst(types::I64, 0)
            }
            other => panic!("`{symbol}` answers a condition or a word, not {other:?}"),
        };
        body.b.ins().return_(&[word]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_comparison", Linkage::Export, &sig)
        .expect("declare the comparison function");
    module
        .define_function(id, &mut ctx)
        .expect("define the comparison function");
    let imports = module
        .declarations()
        .get_functions()
        .filter(|(_, declaration)| declaration.linkage == Linkage::Import)
        .filter_map(|(_, declaration)| declaration.name.clone())
        .collect();
    module.finalize_definitions().expect("finalize the comparison function");
    let code = unsafe { std::mem::transmute::<*const u8, BinaryFunction>(module.get_finalized_function(id)) };
    CompiledComparison {
        code,
        imports,
        declined,
        _backend: backend,
    }
}

/// Named binaries in every form the row meets: inline of each length class,
/// views over the sharing threshold (two windows of one buffer that hold the
/// same bytes, and one that differs), the literal bit, and bitstrings whose
/// last byte is partial, where one pair differs only in the padding bits.
/// The process that holds them is leaked: the words are addresses into its
/// heap, and the rows and functions take it as their first argument.
fn binary_inputs() -> (*mut Process, Vec<(&'static str, u64)>) {
    let process = Box::leak(Box::new(Process::new(Rc::new(RefCell::new(SchemaRegistry::new())))));
    let heap = &mut process.heap;
    let mut words = Vec::new();
    let mut push = |name: &'static str, word: AnyValueRef| {
        words.push((name, word.raw_word()));
        words.push((name, word.literal().raw_word()));
    };
    for (name, bytes) in [
        ("empty", &b""[..]),
        ("one byte", b"a"),
        ("same one byte", b"a"),
        ("another byte", b"b"),
        ("hello", b"hello"),
        ("hello again", b"hello"),
        ("hellp", b"hellp"),
        ("hell", b"hell"),
        ("eight bytes", b"abcdefgh"),
        ("eight bytes, last differs", b"abcdefgi"),
        ("sixty-four bytes", &[7u8; 64][..]),
        ("sixty-four bytes again", &[7u8; 64][..]),
    ] {
        push(name, heap.alloc_bitstring(bytes, bytes.len() as u64 * 8).ref_word());
    }
    let pattern: Vec<u8> = (0..400u32).map(|i| (i % 10) as u8).collect();
    let source = heap.alloc_bitstring(&pattern, pattern.len() as u64 * 8).ref_word();
    push("a 400-byte view", source);
    for (name, start, len) in [
        ("view at 10", 10u64, 100u64),
        ("view at 30, the same bytes", 30, 100),
        ("view at 31, other bytes", 31, 100),
        ("view at 30, shorter", 30, 99),
    ] {
        let window = unsafe { heap.slice(source.raw_word(), start * 8, len * 8) };
        push(name, window.ref_word());
    }
    let copy = heap.alloc_bitstring(&pattern[10..110], 800).ref_word();
    push("an inline-built copy of 100 bytes", copy);
    for (name, bytes, bit_len) in [
        ("3 bits", &[0b1010_0000u8][..], 3u64),
        ("3 bits, other padding", &[0b1011_1111], 3),
        ("3 bits, other bit", &[0b1100_0000], 3),
        ("4 bits", &[0b1010_0000], 4),
        ("11 bits", &[0xff, 0b1010_0000], 11),
        ("11 bits, other padding", &[0xff, 0b1010_1111], 11),
    ] {
        push(name, heap.alloc_bitstring(bytes, bit_len).ref_word());
    }
    (process, words)
}

/// Each comparison row answers, for every pair of binaries (a word against
/// itself included), what its runtime function answers, and that is what the
/// relation of the two binaries says: equal bytes, whatever their form, literal
/// bit or padding, are equal; the order is `Bin`'s term order, in which a
/// prefix comes before what it begins; and a binary compares with itself as
/// equal.
#[test]
fn every_binary_comparison_row_answers_what_its_runtime_function_answers() {
    let (process, words) = binary_inputs();
    for (symbol, reference, answer_when_equal) in BINARY_COMPARISONS {
        let compiled = compile_comparison(symbol);
        for (left_name, left) in &words {
            for (right_name, right) in &words {
                let inline = (compiled.code)(process, *left, *right);
                assert_eq!(
                    inline,
                    reference(process, *left, *right),
                    "`{symbol}` on {left_name} and {right_name}: inline against the runtime function"
                );
                let order = unsafe { Bin::of_binary(*left).cmp(&Bin::of_binary(*right)) };
                let expected = match symbol {
                    "fz_op_eq_bb" => order.is_eq(),
                    "fz_op_neq_bb" => order.is_ne(),
                    "fz_op_lt_bb" => order.is_lt(),
                    "fz_op_lte_bb" => order.is_le(),
                    "fz_op_gt_bb" => order.is_gt(),
                    _ => order.is_ge(),
                };
                assert_eq!(
                    inline == 1,
                    expected,
                    "`{symbol}` on {left_name} and {right_name}: the relation of the two binaries"
                );
                if left == right {
                    assert_eq!(inline == 1, answer_when_equal, "`{symbol}` of {left_name} with itself");
                }
            }
        }
    }
}

/// The relations the rows exist for are present in the inputs: the same word,
/// different lengths, equal bytes in different objects, same-length different
/// bytes, a prefix and what it begins, and bitstrings equal but for their
/// padding.
#[test]
fn the_binary_inputs_hold_every_relation_the_rows_distinguish() {
    let (_, words) = binary_inputs();
    let named = |name: &str| words.iter().find(|(n, _)| *n == name).expect("a named input").1;
    let order = |a: &str, b: &str| unsafe { Bin::of_binary(named(a)).cmp(&Bin::of_binary(named(b))) };
    assert!(order("hello", "hello again").is_eq() && named("hello") != named("hello again"));
    assert!(order("hello", "hellp").is_lt() && order("hellp", "hello").is_gt());
    assert!(order("hell", "hello").is_lt() && order("empty", "one byte").is_lt());
    assert!(order("view at 10", "view at 30, the same bytes").is_eq());
    assert!(order("view at 10", "view at 31, other bytes").is_ne());
    assert!(order("3 bits", "3 bits, other padding").is_eq() && order("3 bits", "3 bits, other bit").is_ne());
    assert!(order("11 bits", "11 bits, other padding").is_eq() && order("3 bits", "4 bits").is_lt());
    assert!(order("an inline-built copy of 100 bytes", "view at 10").is_eq());
}

/// A binary comparison row calls its own runtime function once, in a cold
/// block, and no other: only two different objects that bit lengths do not
/// settle reach it.
#[test]
fn a_binary_comparison_row_imports_only_its_bytes_comparison() {
    for (symbol, ..) in BINARY_COMPARISONS {
        let compiled = compile_comparison(symbol);
        assert_eq!(compiled.imports, [symbol], "`{symbol}` imports");
    }
}

// The atom rows compare two known atoms in place. Equality is one comparison of
// the ids; ordering compares the name prefixes and calls the runtime function
// only when the prefixes tie and the ids differ. They are proved on atoms
// interned out of name order, so the id order is never the name order, and on
// names that share their first eight bytes, that are shorter than eight bytes,
// that hold a NUL or that begin with a multi-byte character.

/// What a row answers for two atoms: its runtime function on their stored
/// words and kinds.
fn runtime_answer(symbol: &str, process: *mut Process, left: u64, right: u64) -> u64 {
    let kind = u64::from(ValueKind::ATOM.tag());
    let stored =
        |function: extern "C" fn(*mut Process, u64, u64, u64, u64) -> u64| function(process, left, kind, right, kind);
    match symbol {
        "fz_op_eq" => stored(fz_op_eq),
        "fz_op_neq" => stored(fz_op_neq),
        "fz_op_identical" => stored(fz_op_identical),
        "fz_op_not_identical" => stored(fz_op_not_identical),
        "fz_value_cmp_ref" => fz_value_cmp_ref(process, left, kind, right, kind) as u64,
        other => panic!("`{other}` is not an atom row"),
    }
}

/// What a row must answer for the relation of two names.
type AtomAnswer = fn(std::cmp::Ordering) -> u64;

/// Each atom row's symbol and what it must answer for the relation of the
/// names: a condition for the equalities, -1, 0 or 1 for the ordering.
const ATOM_ROWS: [(&str, AtomAnswer); 5] = [
    ("fz_op_eq", |o| u64::from(o.is_eq())),
    ("fz_op_neq", |o| u64::from(o.is_ne())),
    ("fz_op_identical", |o| u64::from(o.is_eq())),
    ("fz_op_not_identical", |o| u64::from(o.is_ne())),
    ("fz_value_cmp_ref", |o| o as i64 as u64),
];

/// A process whose atom table holds every name the rows distinguish, interned
/// in reverse of name order and then grown past a reallocation of the table.
/// It is leaked: compiled code reads the table through it.
fn atom_inputs() -> (*mut Process, Vec<(String, u64)>) {
    let process = Box::leak(Box::new(Process::new(Rc::new(RefCell::new(SchemaRegistry::new())))));
    let names = [
        "",
        "a",
        "a\0",
        "a\0b",
        "a\0\0",
        "ab",
        "b",
        "eight888",
        "eight888a",
        "eight888b",
        "eight889",
        "seven77",
        "z",
        "\u{e9}",
        "\u{e9}a",
        "\u{7f}",
        "false",
        "nil",
        "true",
    ];
    let mut atoms: Vec<(String, u64)> = names
        .iter()
        .rev()
        .map(|name| (name.to_string(), u64::from(process.node.intern_atom(name))))
        .collect();
    for n in 0..2_000 {
        process.node.intern_atom(&format!("padding_{n}"));
    }
    atoms.push(("runtime".to_string(), u64::from(process.node.intern_atom("runtime"))));
    (process, atoms)
}

/// Intent: each atom row answers, for every pair of atoms, what its runtime
/// function answers, and that is what the order of their names says, whatever
/// order the ids were interned in.
#[test]
fn every_atom_row_answers_what_its_runtime_function_answers() {
    let (process, atoms) = atom_inputs();
    for (symbol, expected) in ATOM_ROWS {
        let compiled = compile_atom_row(symbol);
        for (left_name, left) in &atoms {
            for (right_name, right) in &atoms {
                let inline = (compiled.code)(process, *left, *right);
                assert_eq!(
                    inline,
                    runtime_answer(symbol, process, *left, *right),
                    "`{symbol}` on {left_name:?} and {right_name:?}: inline against the runtime function"
                );
                assert_eq!(
                    inline,
                    expected(left_name.as_str().cmp(right_name.as_str())),
                    "`{symbol}` on {left_name:?} and {right_name:?}: the order of the names"
                );
            }
        }
    }
}

/// Intent: the tie symbol answers what `Node::cmp_atom_names` says of every
/// pair of different atoms, which is the order of their names.
#[test]
fn the_atom_tie_symbol_answers_what_cmp_atom_names_answers() {
    let (process, atoms) = atom_inputs();
    for (left_name, left) in &atoms {
        for (right_name, right) in &atoms {
            if left == right {
                continue;
            }
            let node = unsafe { &(*process).node };
            assert_eq!(
                fz_atom_names_cmp(process, *left, *right),
                node.cmp_atom_names(*left as u32, *right as u32) as i64,
                "{left_name:?} against {right_name:?}"
            );
            assert_eq!(
                fz_atom_names_cmp(process, *left, *right),
                left_name.as_str().cmp(right_name.as_str()) as i64,
                "{left_name:?} against {right_name:?}: the order of the names"
            );
        }
    }
}

/// Intent: an atom row declines unless both operands are the constant atom
/// kind, and the ordering row declines where no body hosts its cold call.
#[test]
fn an_atom_row_declines_without_two_constant_atom_kinds() {
    for (symbol, _) in ATOM_ROWS {
        let compiled = compile_row(symbol, Operands::Stored);
        assert!(compiled.declined, "`{symbol}` with unknown kinds is the runtime call");
    }
}

/// Intent: the equality rows import nothing and the ordering row imports only
/// its own runtime function, which only the cold tie block calls.
#[test]
fn an_atom_row_imports_only_its_own_runtime_function() {
    for (symbol, _) in ATOM_ROWS {
        let compiled = compile_atom_row(symbol);
        let expected: &[&str] = if symbol == "fz_value_cmp_ref" {
            &["fz_atom_names_cmp"]
        } else {
            &[]
        };
        assert_eq!(compiled.imports, expected, "`{symbol}` imports");
    }
}

/// The relations the rows exist for are present in the inputs: ids out of name
/// order, a tie of prefixes with different names, a name shorter than its
/// prefix, a NUL, and the same atom twice.
#[test]
fn the_atom_inputs_hold_every_relation_the_rows_distinguish() {
    let (_, atoms) = atom_inputs();
    let id = |name: &str| atoms.iter().find(|(n, _)| n == name).expect("a named input").1;
    assert!(id("z") < id("a") && "z" > "a", "ids run against the names");
    assert!(
        "eight888a" > "eight888" && id("eight888a") != id("eight888"),
        "a name that extends a name of eight bytes"
    );
    assert!(id("a\0") != id("a"), "a NUL name is not the shorter name it pads to");
}

// The binary slice row is proved on windows of every length class and
// alignment, over sources of every form. Each case is built twice in fresh
// processes, once for the runtime function and once for the instructions, and
// what the two leave must agree: the binary made (its form, bytes, bit length
// and whether it is the source), the source's header, the tip, and the
// registered placements.

const SLICE_SYMBOL: &str = "fz_bs_slice_ref";

/// A source binary the case builds on a heap: its bytes, its bit length, and
/// how it is held.
#[derive(Clone, Copy, Debug)]
enum SliceSource {
    /// An inline bitstring of `bytes` bytes holding `bits` bits.
    Inline { bytes: usize, bits: u64 },
    /// A view of a buffer of `bytes` bytes (over the sharing threshold).
    Buffer { bytes: usize },
    /// A view of a window of a larger buffer, which starts mid-buffer.
    Window { start: usize, bytes: usize },
}

fn slice_pattern(len: usize) -> Vec<u8> {
    (0..len).map(|i| (i * 7 + 3) as u8).collect()
}

impl SliceSource {
    fn bit_len(self) -> u64 {
        match self {
            SliceSource::Inline { bits, .. } => bits,
            SliceSource::Buffer { bytes } | SliceSource::Window { bytes, .. } => bytes as u64 * 8,
        }
    }

    fn build(self, heap: &mut Heap) -> u64 {
        match self {
            SliceSource::Inline { bytes, bits } => {
                let mut pattern = slice_pattern(bytes);
                if bits % 8 != 0 {
                    *pattern.last_mut().expect("a partial byte") &= !(0xff >> (bits % 8));
                }
                heap.alloc_bitstring(&pattern, bits).ref_word().raw_word()
            }
            SliceSource::Buffer { bytes } => heap
                .alloc_bitstring(&slice_pattern(bytes), bytes as u64 * 8)
                .ref_word()
                .raw_word(),
            SliceSource::Window { start, bytes } => {
                let whole = heap
                    .alloc_bitstring(&slice_pattern(start + bytes + 10), (start + bytes + 10) as u64 * 8)
                    .ref_word()
                    .raw_word();
                unsafe { heap.slice(whole, start as u64 * 8, bytes as u64 * 8) }
                    .ref_word()
                    .raw_word()
            }
        }
    }
}

#[derive(Clone, Copy, Debug)]
struct SliceCase {
    source: SliceSource,
    pos: u64,
    bit_len: u64,
}

/// Every window of every source whose bytes the source holds: whole-byte
/// windows of 0, 1, 4, 8, 63, 64 and 65 bytes, a window of 3 and of 35 bits,
/// at a byte boundary, off it, and at the source's end.
fn slice_cases() -> Vec<SliceCase> {
    let sources = [
        SliceSource::Inline { bytes: 0, bits: 0 },
        SliceSource::Inline { bytes: 1, bits: 8 },
        SliceSource::Inline { bytes: 4, bits: 32 },
        SliceSource::Inline { bytes: 8, bits: 64 },
        SliceSource::Inline { bytes: 20, bits: 160 },
        SliceSource::Inline { bytes: 20, bits: 155 },
        SliceSource::Inline { bytes: 63, bits: 504 },
        SliceSource::Inline { bytes: 64, bits: 512 },
        SliceSource::Buffer { bytes: 65 },
        SliceSource::Buffer { bytes: 200 },
        SliceSource::Window { start: 10, bytes: 150 },
    ];
    let lengths = [0u64, 8, 32, 64, 504, 512, 520, 3, 35];
    let positions = [0u64, 8, 24, 3, 11, 8 * 64];
    let mut cases = Vec::new();
    for source in sources {
        let total = source.bit_len();
        for &pos in &positions {
            for &bit_len in lengths.iter().chain(&[total.saturating_sub(pos)]) {
                if pos + bit_len <= total {
                    cases.push(SliceCase { source, pos, bit_len });
                }
            }
        }
    }
    cases
}

/// What a slice run leaves, addresses replaced by what they say.
#[derive(Debug, PartialEq, Eq)]
struct SliceLeft {
    kind: u8,
    is_source: bool,
    bit_len: u64,
    /// The bytes the binary holds, padding included for an inline object.
    bytes: Vec<u8>,
    /// The words of an inline object, which a view has none of.
    object: Vec<u64>,
    source_shared: bool,
    tip_used: usize,
    tip_changed: bool,
}

fn run_slice(tip: Tip, case: SliceCase, run: impl FnOnce(*mut Process, u64) -> u64) -> SliceLeft {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Box::new(Process::new(schemas));
    let source = case.source.build(&mut process.heap);
    if tip == Tip::Full {
        while tip_of(&process).1 - (heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - tip_of(&process).0) >= 16 {
            process.heap.alloc(16);
        }
    }
    let before = tip_of(&process);
    let result = run(&mut *process, source);
    let after = tip_of(&process);
    let used = heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - after.0;
    let packing = AnyValueRefPacking::current();
    let bin = unsafe { Bin::of_binary(result) };
    let kind = AnyValueRef::from_raw_word(result).expect("a binary ref").tag();
    let size = fz_runtime::any_value::bitstring_size_for_bit_len(bin.bit_len());
    let inline = kind == ValueKind::BITSTRING;
    let held = if inline {
        size - 8
    } else {
        (bin.bit_len() as usize).div_ceil(8)
    };
    SliceLeft {
        kind: kind.tag(),
        is_source: result == source,
        bit_len: bin.bit_len(),
        bytes: unsafe { std::slice::from_raw_parts(bin.ptr(), held) }.to_vec(),
        object: if inline {
            words_of(packing.raw_address(result) as *const u8, size / 8)
        } else {
            Vec::new()
        },
        source_shared: AnyValueRef::from_raw_word(source).expect("a ref").tag() == ValueKind::BITSTRING
            && unsafe { fz_runtime::any_value::bitstring_is_shared(packing.raw_address(source) as *const u8) },
        tip_used: used,
        tip_changed: before != after,
    }
}

/// A slice row compiled to a function of the source and the position, and of
/// the length when it is not a constant, and the placements it registered.
struct CompiledSlice {
    code: *const u8,
    counts: *const u64,
    sizes: Vec<u32>,
    imports: Vec<String>,
    _backend: JitBackend,
}

fn compile_slice(constant_len: Option<u64>) -> CompiledSlice {
    let mut backend = JitBackend::new();
    let module = backend.module_mut();
    let mut ctx = module.make_context();
    let mut fbctx = FunctionBuilderContext::new();
    let mut sig = module.make_signature();
    let params = if constant_len.is_some() { 2 } else { 3 };
    sig.params = vec![ir::AbiParam::new(types::I64); params];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(SiteTable::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let given = b.block_params(entry).to_vec();
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let process = body.process_arg();
        let bit_len = match constant_len {
            Some(bits) => body.b.ins().iconst(types::I64, bits as i64),
            None => given[2],
        };
        let sliced = emit_slice(&mut body, SLICE_SYMBOL, &[process, given[0], given[1], bit_len]);
        body.b.ins().return_(&[sliced]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_slice", Linkage::Export, &sig)
        .expect("declare the slice function");
    module.define_function(id, &mut ctx).expect("define the slice function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    let imports = module
        .declarations()
        .get_functions()
        .filter(|(_, declaration)| declaration.linkage == Linkage::Import)
        .filter_map(|(_, declaration)| declaration.name.clone())
        .collect();
    module.finalize_definitions().expect("finalize the slice function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    assert!(
        registered
            .iter()
            .all(|site| allocation_site(site).kind == HeapAllocKind::Bitstring)
    );
    CompiledSlice {
        code,
        counts: counts.cast(),
        sizes: registered.iter().map(|site| allocation_site(site).bytes).collect(),
        imports,
        _backend: backend,
    }
}

fn call_slice(compiled: &CompiledSlice, constant: bool, process: *mut Process, source: u64, case: SliceCase) -> u64 {
    unsafe {
        if constant {
            pinned_abi::call2(compiled.code, process, source, case.pos) as u64
        } else {
            pinned_abi::call3(compiled.code, process, source, case.pos, case.bit_len) as u64
        }
    }
}

/// Whether the row copies the window in place: it begins and ends on a byte
/// boundary, is at most the threshold long and is not the whole source.
fn row_copies(case: &SliceCase) -> bool {
    case.pos.is_multiple_of(8)
        && case.bit_len.is_multiple_of(8)
        && case.bit_len <= 512
        && !(case.pos == 0 && case.bit_len == case.source.bit_len())
}

fn counts_of(compiled: &CompiledSlice) -> u64 {
    (0..compiled.sizes.len())
        .map(|site| unsafe { *compiled.counts.add(site) })
        .sum()
}

/// The row places what `Heap::slice` makes, for every window, with a length
/// the code knows and one it does not, and with a tip that has room and one
/// that has none. Each copy it places is counted once at its site.
#[test]
fn the_slice_row_makes_what_the_runtime_function_makes() {
    let dynamic = compile_slice(None);
    let mut constants: HashMap<u64, CompiledSlice> = HashMap::default();
    let mut copies = 0u64;
    for case in &slice_cases() {
        let constant = constants
            .entry(case.bit_len)
            .or_insert_with(|| compile_slice(Some(case.bit_len)));
        for tip in [Tip::Roomy, Tip::Full] {
            let expected = run_slice(tip, *case, |process, source| {
                fz_bs_slice_ref(process, source, case.pos, case.bit_len)
            });
            for (compiled, is_constant) in [(&*constant, true), (&dynamic, false)] {
                let inline = run_slice(tip, *case, |process, source| {
                    call_slice(compiled, is_constant, process, source, *case)
                });
                assert_eq!(
                    inline,
                    expected,
                    "{case:?} with a {tip:?} tip, length {}: inline against the runtime function",
                    if is_constant { "known" } else { "unknown" }
                );
            }
            copies += u64::from(row_copies(case));
        }
    }
    assert!(copies > 0, "the cases must hold windows the row copies");
    let constant_counts: u64 = constants.values().map(counts_of).sum();
    assert_eq!(
        constant_counts, copies,
        "the rows of a constant length count each copy once"
    );
    assert_eq!(
        counts_of(&dynamic),
        copies,
        "the row of any length counts each copy once"
    );
}

/// A row of a constant length places one object of the size that length needs
/// and imports the runtime function for a window it does not copy; a row of any
/// length places one of five sizes. A length that is never copied places none.
#[test]
fn the_slice_row_places_the_sizes_a_copy_can_have() {
    let imports = |compiled: &CompiledSlice| {
        let mut names = compiled.imports.clone();
        names.sort();
        names
    };
    for (bits, size) in [
        (0u64, 16u32),
        (8, 16),
        (56, 16),
        (64, 32),
        (256, 48),
        (504, 80),
        (512, 80),
    ] {
        let compiled = compile_slice(Some(bits));
        assert_eq!(
            compiled.sizes,
            [size],
            "a copy of {bits} bits is placed as one object of {size} bytes"
        );
        assert_eq!(imports(&compiled), ["fz_bs_slice_ref", "fz_heap_room"]);
    }
    for bits in [520u64, 3, 35] {
        let compiled = compile_slice(Some(bits));
        assert!(
            compiled.sizes.is_empty(),
            "a window of {bits} bits is never copied in place"
        );
        assert_eq!(imports(&compiled), ["fz_bs_slice_ref"]);
    }
    let compiled = compile_slice(None);
    assert_eq!(compiled.sizes, [16, 32, 48, 64, 80]);
    assert_eq!(imports(&compiled), ["fz_bs_slice_ref", "fz_heap_room"]);
}
