use super::*;
use crate::fast_hash::HashSet;
use crate::ir_codegen::backend::{Backend, JitBackend};
use cranelift_codegen::ir::{self, InstBuilder, MemFlagsData, types};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_jit::JITModule;
use cranelift_module::{Linkage, Module};
use fz_runtime::any_value::AnyValueRefPacking;
use fz_runtime::any_value::{AnyValue, AnyValueRef, FALSE_ATOM_ID, NIL_ATOM_ID, TRUE_ATOM_ID, ValueKind};
use fz_runtime::heap::{Heap, HeapAllocKind, INLINE_ALLOC_LAYOUT, Schema, SchemaRegistry};
use fz_runtime::ir_runtime::*;
use fz_runtime::pinned_abi;
use fz_runtime::process::Process;
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

const OTHER_ATOM_ID: u32 = 7;

fn int_ref(heap: &mut Heap, value: i64) -> AnyValueRef {
    heap.box_any_value_ref(AnyValue::int(value))
}

fn words() -> Words {
    let mut heap = Heap::new(4096, Rc::new(RefCell::new(SchemaRegistry::new())));
    let pair = heap.register_schema(Schema::tuple_of_arity(2));
    let triple = heap.register_schema(Schema::tuple_of_arity(3));
    let ints: Vec<AnyValueRef> = INTEGERS.iter().map(|value| int_ref(&mut heap, *value)).collect();
    let atoms: Vec<AnyValueRef> = [TRUE_ATOM_ID, FALSE_ATOM_ID, NIL_ATOM_ID, OTHER_ATOM_ID]
        .iter()
        .map(|id| AnyValueRef::atom(*id))
        .collect();
    let structs: Vec<AnyValueRef> = [pair, triple]
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
    let cons = heap
        .alloc_list_cons_any(AnyValue::int(1), AnyValueRef::empty_list())
        .expect("a cons cell");
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
        eq_raw_const(ValueKind::ATOM, &w, atom_ids),
        eq_raw_const(ValueKind::INT, &w, ints.clone()),
        integer_arithmetic("fz_op_add_ii", fz_op_add_ii),
        integer_arithmetic("fz_op_sub_ii", fz_op_sub_ii),
        integer_arithmetic("fz_op_mul_ii", fz_op_mul_ii),
        parity("fz_op_neg_i", Shape::Checked, &[Lane::Word], singles(&ints), |a| {
            checked(fz_op_neg_i(a[0] as i64))
        }),
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

/// What a case hands the row: its head and tail words, and the objects the
/// row may change by sharing them.
struct CellInputs {
    head: u64,
    tail: u64,
    watched: Vec<*const u8>,
}

struct CellCase {
    name: &'static str,
    build: Box<dyn Fn(&mut Heap) -> CellInputs>,
}

/// A row's proof: the runtime function it must agree with, and the heads and
/// tails it is tried on. A head's word is its payload for a scalar lane and a
/// ref word for the ref lane.
struct CellProof {
    symbol: &'static str,
    lane: HeadLane,
    reference: fn(*mut Process, u64, u64) -> u64,
    cases: Vec<CellCase>,
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
            tail: AnyValueRef::empty_list().raw_word(),
            watched: Vec::new(),
        }));
        cases.push(case(name, move |heap| {
            let tail = heap
                .alloc_list_cons_int(9, AnyValueRef::empty_list())
                .expect("a one-cell tail");
            CellInputs {
                head,
                tail: tail.raw_word(),
                watched: vec![list_address(tail)],
            }
        }));
    }
    cases
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
                tail: AnyValueRef::empty_list().raw_word(),
                watched,
            }
        }));
        cases.push(case(name, move |heap| {
            let (head, mut watched) = make(heap);
            let (tail, cells) = int_list(heap, 2);
            watched.extend(cells);
            CellInputs {
                head: head.raw_word(),
                tail: tail.raw_word(),
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
    vec![
        CellProof {
            symbol: "fz_list_cons_int",
            lane: HeadLane::Int,
            reference: |process, head, tail| fz_list_cons_int(process, head as i64, tail),
            cases: scalar_cases(&ints),
        },
        CellProof {
            symbol: "fz_list_cons_float",
            lane: HeadLane::Float,
            reference: |process, head, tail| fz_list_cons_float(process, f64::from_bits(head), tail),
            cases: scalar_cases(&floats),
        },
        CellProof {
            symbol: "fz_list_cons_atom",
            lane: HeadLane::Atom,
            reference: |process, head, tail| fz_list_cons_atom(process, head, tail),
            cases: scalar_cases(&atoms),
        },
        CellProof {
            symbol: "fz_list_cons_any",
            lane: HeadLane::Ref,
            reference: |process, head, tail| fz_list_cons_any(process, head, tail),
            cases: ref_cases(),
        },
    ]
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
    sig.params = vec![ir::AbiParam::new(types::I64); 2];
    sig.returns = vec![ir::AbiParam::new(types::I64)];
    ctx.func.signature = sig.clone();
    let sites = RefCell::new(AllocSites::declare(module).expect("declare the site counters"));
    {
        let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
        let entry = b.create_block();
        b.append_block_params_for_function_params(entry);
        b.switch_to_block(entry);
        b.seal_block(entry);
        let params = b.block_params(entry).to_vec();
        let mut cache = CodegenCache::default();
        let mut body = CodegenFn::new(&mut b, module, &mut cache);
        let process = body.process_arg();
        let head = match proof.lane {
            HeadLane::Float => body.b.ins().bitcast(types::F64, MemFlagsData::new(), params[0]),
            _ => params[0],
        };
        let scope = SiteScope {
            sites: &sites,
            function: "recipe_parity",
        };
        let cell = emit_cell(&mut body, scope, proof.symbol, &[process, head, params[1]]);
        body.b.ins().return_(&[cell]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("recipe_parity_cell", Linkage::Export, &sig)
        .expect("declare the cell function");
    module.define_function(id, &mut ctx).expect("define the cell function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    assert_eq!(registered.len(), 1, "one placement is one site");
    assert_eq!(registered[0].kind, HeapAllocKind::ListCons);
    assert_eq!(registered[0].bytes, 16);
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
enum Tip {
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
    object_count: u64,
    list_cons: (u64, u64),
    total: (u64, u64),
}

fn heap_field(process: &Process, offset: usize) -> usize {
    unsafe { *(((&process.heap as *const Heap).cast::<u8>()).add(offset) as *const usize) }
}

fn tip_of(process: &Process) -> (usize, usize) {
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
    let stats = process.heap.alloc_stats_snapshot();
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
        object_count: heap_field(&process, INLINE_ALLOC_LAYOUT.alloc_count) as u64,
        list_cons: (stats.list_cons.allocs, stats.list_cons.bytes),
        total: (stats.total.allocs, stats.total.bytes),
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
                    (proof.reference)(process, inputs.head, inputs.tail)
                });
                let inline = run_cell(case, tip, &schemas, |process, inputs| unsafe {
                    pinned_abi::call2(compiled.code, process, inputs.head, inputs.tail) as u64
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
fn the_ref_row_is_tried_on_heads_that_must_be_shared() {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let proofs = cell_proofs();
    let proof = proofs
        .iter()
        .find(|proof| proof.symbol == "fz_list_cons_any")
        .expect("the ref row");
    let marked = |name: &str| {
        let case = proof.cases.iter().find(|case| case.name == name).expect("a case");
        let left = run_cell(case, Tip::Roomy, &schemas, |process, inputs| {
            (proof.reference)(process, inputs.head, inputs.tail)
        });
        let link = left.watched[0][1];
        link & fz_runtime::any_value::LIST_LINK_ALIAS_MASK != 0
    };
    assert!(marked("an unshared list"), "a list head is shared by the cell");
}
