//! The in-place construction is proved against the runtime's builder:
//! `construction::build` is the definition, so each case is built twice in
//! fresh processes, once by the runtime and once by the compiled instructions,
//! and what the two leave must agree: the binary made (its form, bytes, bit
//! length and padding), the tip, and the placements counted.

use super::recipe::recipe_test::{Tip, allocation_site, heap_field, tip_of, words_of};
use super::*;
use crate::ast::Endian;
use crate::fz_ir::Var;
use crate::ir_codegen::backend::{Backend, JitBackend};
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::Module;
use fz_runtime::any_value::{AnyValueRef, AnyValueRefPacking, ValueKind, bitstring_size_for_bit_len};
use fz_runtime::bits::Bin;
use fz_runtime::construction::{self, FzBsField};
use fz_runtime::heap::{Heap, HeapAllocKind, INLINE_ALLOC_LAYOUT, SchemaRegistry};
use fz_runtime::pinned_abi;
use fz_runtime::process::Process;
use std::cell::RefCell;
use std::rc::Rc;

/// A binary a case builds on a heap.
#[derive(Clone, Copy, Debug)]
enum Source {
    /// An inline bitstring of `bytes` bytes.
    Inline(usize),
    /// A view of a buffer of `bytes` bytes, over the sharing threshold.
    Buffer(usize),
    /// A view of a window of a larger buffer, which starts mid-buffer.
    Window { start: usize, bytes: usize },
}

fn pattern(len: usize, salt: usize) -> Vec<u8> {
    (0..len).map(|i| (i * 7 + 3 + salt) as u8).collect()
}

impl Source {
    fn bytes(self) -> usize {
        match self {
            Source::Inline(bytes) | Source::Buffer(bytes) | Source::Window { bytes, .. } => bytes,
        }
    }

    fn build(self, heap: &mut Heap, salt: usize) -> u64 {
        match self {
            Source::Inline(bytes) | Source::Buffer(bytes) => heap
                .alloc_bitstring(&pattern(bytes, salt), bytes as u64 * 8)
                .ref_word()
                .raw_word(),
            Source::Window { start, bytes } => {
                let whole = heap
                    .alloc_bitstring(&pattern(start + bytes + 10, salt), (start + bytes + 10) as u64 * 8)
                    .ref_word()
                    .raw_word();
                unsafe { heap.slice(whole, start as u64 * 8, bytes as u64 * 8) }
                    .ref_word()
                    .raw_word()
            }
        }
    }
}

/// What a field holds when the case runs.
#[derive(Clone, Copy, Debug)]
enum Input {
    Int(u64),
    Binary(Source),
    /// An unsized binary known when the code is compiled, of this many bytes.
    Literal(usize),
}

#[derive(Clone, Debug)]
struct Case {
    fields: Vec<(BitFieldIr, Input)>,
}

fn field(ty: BitType, size: Option<u32>, unit: Option<u32>, endian: Endian, index: usize) -> BitFieldIr {
    BitFieldIr {
        value: Var(index as u32),
        literal: None,
        ty,
        size: size.map(BitSizeIr::Literal),
        endian,
        signed: false,
        unit,
    }
}

const WORD: u64 = 0xA1B2_C3D4_E5F6_0718;

fn int(bits: u32, endian: Endian, index: usize, value: u64) -> (BitFieldIr, Input) {
    (
        field(BitType::Integer, Some(bits), None, endian, index),
        Input::Int(value),
    )
}

fn literal(index: usize, bytes: usize) -> (BitFieldIr, Input) {
    let mut written = field(BitType::Binary, None, None, Endian::Big, index);
    written.literal = Some(pattern(bytes, index));
    (written, Input::Literal(bytes))
}

fn binary(size: Option<u32>, index: usize, source: Source) -> (BitFieldIr, Input) {
    (
        field(BitType::Binary, size, None, Endian::Big, index),
        Input::Binary(source),
    )
}

/// Renumber the fields' values so each is its own position.
fn case(fields: Vec<(BitFieldIr, Input)>) -> Case {
    let fields = fields
        .into_iter()
        .enumerate()
        .map(|(index, (mut f, input))| {
            f.value = Var(index as u32);
            (f, input)
        })
        .collect();
    Case { fields }
}

fn cases() -> Vec<Case> {
    let mut cases = vec![case(Vec::new())];
    for endian in [Endian::Big, Endian::Little, Endian::Native] {
        for bits in [8, 16, 32, 64] {
            for value in [WORD, u64::MAX - 1, 0] {
                cases.push(case(vec![int(bits, endian, 0, value)]));
            }
        }
    }
    let mut sized_by_unit = field(BitType::Integer, Some(2), Some(8), Endian::Big, 0);
    sized_by_unit.signed = true;
    cases.push(case(vec![(sized_by_unit, Input::Int(WORD))]));
    cases.push(case(vec![(
        field(BitType::Integer, None, None, Endian::Big, 0),
        Input::Int(WORD),
    )]));
    // <<a::8, b::16, c::binary>> at every total that matters: 3, 4, 63, 64, 65, 67.
    for bytes in [0, 1, 10, 60, 61, 62, 64, 100] {
        for source in [Source::Inline(bytes.min(64)), Source::Buffer(bytes.max(65))] {
            if source.bytes() == bytes {
                cases.push(case(vec![
                    int(8, Endian::Big, 0, WORD),
                    int(16, Endian::Big, 1, WORD >> 8),
                    binary(None, 2, source),
                ]));
            }
        }
    }
    cases.push(case(vec![
        int(8, Endian::Big, 0, 7),
        int(16, Endian::Big, 1, 0x1234),
        binary(None, 2, Source::Window { start: 5, bytes: 20 }),
    ]));
    // A leading unsized binary that is inline and whose total fits inline: the
    // construction is an append that is built in place. A leading view, or a total
    // over the threshold, is the runtime's (`emit_append`).
    for source in [
        Source::Inline(0),
        Source::Inline(1),
        Source::Inline(63),
        Source::Inline(64),
    ] {
        cases.push(case(vec![binary(None, 0, source)]));
    }
    cases.push(case(vec![
        binary(None, 0, Source::Inline(30)),
        binary(None, 1, Source::Window { start: 3, bytes: 34 }),
    ]));
    cases.push(case(vec![
        binary(None, 0, Source::Inline(20)),
        int(32, Endian::Little, 1, WORD),
        binary(None, 2, Source::Inline(5)),
    ]));
    cases.push(case(vec![
        binary(Some(2), 0, Source::Inline(30)),
        binary(None, 1, Source::Window { start: 3, bytes: 34 }),
    ]));
    for source in [
        Source::Inline(0),
        Source::Inline(1),
        Source::Inline(63),
        Source::Inline(64),
        Source::Buffer(65),
        Source::Window { start: 9, bytes: 150 },
    ] {
        cases.push(case(vec![int(8, Endian::Big, 0, 5), binary(None, 1, source)]));
    }
    cases.push(case(vec![
        binary(Some(3), 0, Source::Inline(10)),
        int(8, Endian::Big, 1, 9),
        binary(Some(70), 2, Source::Buffer(100)),
    ]));
    cases.push(case(vec![
        binary(Some(0), 0, Source::Inline(4)),
        binary(Some(64), 1, Source::Window { start: 2, bytes: 90 }),
    ]));
    cases.push(case(vec![
        int(64, Endian::Big, 0, WORD),
        binary(Some(56), 1, Source::Buffer(65)),
    ]));
    // A literal is written by immediate stores of 8, 4, 2 and 1 bytes: every
    // length up to 16 after an integer, and between binaries whose total
    // crosses the sharing threshold.
    for bytes in 0..=16 {
        cases.push(case(vec![int(8, Endian::Big, 0, 5), literal(1, bytes)]));
    }
    for source in [Source::Inline(20), Source::Inline(50), Source::Buffer(65)] {
        cases.push(case(vec![
            int(16, Endian::Little, 0, WORD),
            literal(1, 15),
            binary(None, 2, source),
            literal(3, 3),
        ]));
    }
    cases
}

/// The runtime's descriptors for a case, with its binaries built on `heap`.
fn descriptors(case: &Case, heap: &mut Heap) -> Vec<FzBsField> {
    case.fields
        .iter()
        .enumerate()
        .map(|(index, (f, input))| {
            let size_present = u32::from(f.size.is_some());
            let size = match f.size {
                Some(BitSizeIr::Literal(n)) => u64::from(n),
                _ => 0,
            };
            let value = match input {
                Input::Int(word) => *word,
                Input::Binary(source) => source.build(heap, index),
                Input::Literal(bytes) => Source::Inline(*bytes).build(heap, index),
            };
            FzBsField {
                spec: descriptor_spec(f, size_present),
                size,
                value,
            }
        })
        .collect()
}

/// What a construction leaves, addresses replaced by what they say.
#[derive(Debug, PartialEq, Eq)]
struct Left {
    kind: u8,
    bit_len: u64,
    /// The bytes the binary holds, padding included for an inline object.
    bytes: Vec<u8>,
    /// The words of an inline object, which a view has none of.
    object: Vec<u64>,
    tip_used: usize,
    tip_changed: bool,
}

fn run(tip: Tip, case: &Case, make: impl FnOnce(*mut Process, &[FzBsField]) -> u64) -> Left {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Box::new(Process::new(schemas));
    let fields = descriptors(case, &mut process.heap);
    if tip == Tip::Full {
        while tip_of(&process).1 - (heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - tip_of(&process).0) >= 16 {
            process.heap.alloc(16);
        }
    }
    let before = tip_of(&process);
    let result = make(&mut *process, &fields);
    let after = tip_of(&process);
    let used = heap_field(&process, INLINE_ALLOC_LAYOUT.bump_top) - after.0;
    let packing = AnyValueRefPacking::current();
    let bin = unsafe { Bin::of_binary(result) };
    let kind = AnyValueRef::from_raw_word(result).expect("a binary ref").tag();
    let inline = kind == ValueKind::BITSTRING;
    let size = bitstring_size_for_bit_len(bin.bit_len());
    let held = if inline { size - 8 } else { bin.bit_len() as usize / 8 };
    Left {
        kind: kind.tag(),
        bit_len: bin.bit_len(),
        bytes: unsafe { std::slice::from_raw_parts(bin.ptr(), held) }.to_vec(),
        object: if inline {
            words_of(packing.raw_address(result) as *const u8, size / 8)
        } else {
            Vec::new()
        },
        tip_used: used,
        tip_changed: before != after,
    }
}

/// A case compiled to a function of the array of its values, the integers' raw
/// words and the binaries' ref words, and the placements it registered.
struct Compiled {
    code: *const u8,
    counts: *const u64,
    sizes: Vec<u32>,
    imports: Vec<String>,
    _backend: JitBackend,
}

fn compile(case: &Case) -> Compiled {
    let fields: Vec<BitFieldIr> = case.fields.iter().map(|(f, _)| f.clone()).collect();
    let segments = aligned_segments(&fields).expect("a case is whole bytes");
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
        let values = b.block_params(entry)[0];
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "construction_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let given: Vec<_> = segments
            .iter()
            .enumerate()
            .map(|(index, &segment)| {
                let word = body
                    .b
                    .ins()
                    .load(types::I64, MemFlagsData::new(), values, index as i32 * 8);
                (segment, word)
            })
            .collect();
        let built = emit_aligned_construction(&mut body, &given);
        body.b.ins().return_(&[built]);
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("construction_parity", Linkage::Export, &sig)
        .expect("declare the construction function");
    module
        .define_function(id, &mut ctx)
        .expect("define the construction function");
    let (counts_id, registered) = sites.into_inner().define(module).expect("define the site counters");
    let imports = module
        .declarations()
        .get_functions()
        .filter(|(_, declaration)| declaration.linkage == Linkage::Import)
        .filter_map(|(_, declaration)| declaration.name.clone())
        .collect();
    module
        .finalize_definitions()
        .expect("finalize the construction function");
    let code = module.get_finalized_function(id);
    let (counts, _) = module.get_finalized_data(counts_id);
    assert!(
        registered
            .iter()
            .all(|site| allocation_site(site).kind == HeapAllocKind::Bitstring)
    );
    Compiled {
        code,
        counts: counts.cast(),
        sizes: registered.iter().map(|site| allocation_site(site).bytes).collect(),
        imports,
        _backend: backend,
    }
}

fn placements(compiled: &Compiled) -> u64 {
    (0..compiled.sizes.len())
        .map(|site| unsafe { *compiled.counts.add(site) })
        .sum()
}

/// The bytes the case's result holds, from its descriptors' own sizes.
fn total_bytes_of(case: &Case) -> usize {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Box::new(Process::new(schemas));
    let fields = descriptors(case, &mut process.heap);
    construction::size_in_bits(&fields) as usize / 8
}

/// The compiled instructions make what `construction::build` makes, for every
/// case, with a tip that has room and one that has none, and place an inline
/// result at one site, once.
#[test]
fn the_inline_construction_makes_what_the_runtime_builder_makes() {
    for case in &cases() {
        let compiled = compile(case);
        let mut inline_results = 0;
        for tip in [Tip::Roomy, Tip::Full] {
            let expected = run(tip, case, |process, fields| {
                construction::build(unsafe { &mut *process }, fields)
            });
            let inline = run(tip, case, |process, fields| {
                let values: Vec<u64> = fields.iter().map(|f| f.value).collect();
                unsafe { pinned_abi::call1(compiled.code, process, values.as_ptr() as u64) as u64 }
            });
            assert_eq!(
                inline, expected,
                "{case:?} with a {tip:?} tip: inline against the runtime builder"
            );
            inline_results += u64::from(expected.kind == ValueKind::BITSTRING.tag());
        }
        assert_eq!(
            placements(&compiled),
            inline_results,
            "{case:?}: each inline result is counted once, and a shared one not at all"
        );
    }
}

/// A construction imports only what its shape can reach: the room function for
/// an inline result, the unfilled-binary function for a shared one and `memcpy`
/// for a binary whose length is not written as zero; never the builder.
#[test]
fn the_inline_construction_imports_what_its_shape_reaches() {
    for case in &cases() {
        let compiled = compile(case);
        let total = total_bytes_of(case);
        let read = |(_, input): &&(BitFieldIr, Input)| !matches!(input, Input::Literal(_));
        let unsized_binary = case
            .fields
            .iter()
            .filter(read)
            .any(|(f, _)| f.ty == BitType::Binary && f.size.is_none());
        let copies = case
            .fields
            .iter()
            .filter(read)
            .any(|(f, _)| f.ty == BitType::Binary && f.size != Some(BitSizeIr::Literal(0)));
        let mut expected = Vec::new();
        if unsized_binary || total <= 64 {
            expected.push("fz_heap_room");
        }
        if unsized_binary || total > 64 {
            expected.push("fz_bs_alloc_unfilled");
        }
        if copies {
            expected.push("memcpy");
        }
        let mut imports = compiled.imports.clone();
        imports.sort();
        expected.sort();
        assert_eq!(imports, expected, "{case:?} (total {total} bytes)");
    }
}

/// A result of a length known now is placed as one object of its size; one
/// that depends on a binary's length is placed as one of five.
#[test]
fn the_inline_construction_places_the_sizes_its_total_can_have() {
    let known = compile(&case(vec![int(8, Endian::Big, 0, 1), int(16, Endian::Big, 1, 2)]));
    assert_eq!(known.sizes, [16]);
    let known = compile(&case(vec![int(64, Endian::Big, 0, 1), int(64, Endian::Big, 1, 2)]));
    assert_eq!(known.sizes, [32]);
    let sized = compile(&case(vec![binary(Some(64), 0, Source::Inline(64))]));
    assert_eq!(sized.sizes, [80]);
    let shared = compile(&case(vec![binary(Some(65), 0, Source::Buffer(65))]));
    assert!(shared.sizes.is_empty());
    let open = compile(&case(vec![binary(None, 0, Source::Inline(3))]));
    assert_eq!(open.sizes, [16, 32, 48, 64, 80]);
}

/// A segment compiled code does not write is not aligned: a size off a byte
/// boundary, a size read at run time, `float`, `bits`, `utf` and an integer of
/// a width other than 8, 16, 32 or 64.
#[test]
fn only_whole_byte_integers_and_binaries_are_aligned() {
    let aligned = |f: BitFieldIr| aligned_segment(&f);
    let integer = |size, unit| field(BitType::Integer, size, unit, Endian::Big, 0);
    assert_eq!(
        aligned(integer(Some(16), None)),
        Some(AlignedSegment::Integer {
            bytes: 2,
            big_endian: true
        })
    );
    assert_eq!(
        aligned(integer(None, None)),
        Some(AlignedSegment::Integer {
            bytes: 1,
            big_endian: true
        })
    );
    for (size, unit) in [
        (Some(3), None),
        (Some(24), None),
        (Some(12), None),
        (Some(128), None),
        (Some(1), Some(7)),
    ] {
        assert_eq!(
            aligned(integer(size, unit)),
            None,
            "integer size {size:?} unit {unit:?}"
        );
    }
    let binary_field = |size, unit| field(BitType::Binary, size, unit, Endian::Big, 0);
    assert_eq!(
        aligned(binary_field(None, None)),
        Some(AlignedSegment::Binary { bytes: None })
    );
    assert_eq!(
        aligned(binary_field(Some(3), None)),
        Some(AlignedSegment::Binary { bytes: Some(3) })
    );
    assert_eq!(
        aligned(binary_field(Some(8), Some(1))),
        Some(AlignedSegment::Binary { bytes: Some(1) })
    );
    assert_eq!(aligned(binary_field(Some(4), Some(1))), None);
    assert_eq!(aligned(binary_field(None, Some(3))), None);
    for ty in [
        BitType::Float,
        BitType::Bits,
        BitType::Utf8,
        BitType::Utf16,
        BitType::Utf32,
    ] {
        assert_eq!(aligned(field(ty, None, None, Endian::Big, 0)), None, "{ty:?}");
    }
    let mut named = field(BitType::Integer, None, None, Endian::Big, 0);
    named.size = Some(BitSizeIr::Var(Var(1)));
    assert_eq!(aligned(named), None);
}

/// A construction that starts with an unsized binary is an append, which the
/// runtime makes in the accumulator's own buffer; every other construction of
/// whole bytes is built in place.
#[test]
fn only_a_construction_that_starts_with_an_unsized_binary_is_an_append() {
    let segments_of = |fields: Vec<(BitFieldIr, Input)>| {
        let fields: Vec<_> = fields.into_iter().map(|(f, _)| f).collect();
        aligned_segments(&fields).expect("whole bytes")
    };
    let source = Source::Inline(1);
    assert!(starts_with_unsized_binary(&segments_of(vec![
        binary(None, 0, source),
        int(8, Endian::Big, 1, 1)
    ])));
    assert!(starts_with_unsized_binary(&segments_of(vec![binary(None, 0, source)])));
    assert!(!starts_with_unsized_binary(&segments_of(vec![
        binary(Some(1), 0, source),
        binary(None, 1, source)
    ])));
    assert!(!starts_with_unsized_binary(&segments_of(vec![
        int(8, Endian::Big, 0, 1),
        binary(None, 1, source)
    ])));
    assert!(!starts_with_unsized_binary(&segments_of(Vec::new())));
}
