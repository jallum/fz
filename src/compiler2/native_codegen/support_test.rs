//! What a container stores for a value whose kind compiled code knows is what
//! it would read from the value's reference, and sharing such a value marks it
//! unless it is marked already. Each case is compiled into a one-argument
//! function and run on a process.

use super::*;
use crate::ir_codegen::backend::{Backend, JitBackend};
use cranelift_codegen::ir::condcodes::IntCC;
use cranelift_frontend::{FunctionBuilder, FunctionBuilderContext};
use cranelift_module::{Linkage, Module};
use fz_runtime::any_value::{AnyValueRefPacking, STRUCT_HEADER_SHARED_MASK};
use fz_runtime::heap::SchemaRegistry;
use fz_runtime::pinned_abi;
use fz_runtime::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, Node, Process};
use std::cell::RefCell;
use std::rc::Rc;

/// Compile `build`, which gets the function's one argument, into a function
/// returning what `build` returns, and run it on `word`.
fn run(word: u64, build: impl FnOnce(&mut CodegenFn<'_, '_, JitModuleOf>, ir::Value) -> ir::Value) -> i64 {
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
        let argument = b.block_params(entry)[0];
        let mut cache = CodegenCache::default();
        let scope = SiteScope {
            sites: &sites,
            function: "support_parity",
        };
        let mut body = CodegenFn::new(&mut b, module, &mut cache, scope);
        let result = build(&mut body, argument);
        body.b.ins().return_(&[result]);
        b.seal_all_blocks();
        b.finalize(module.target_config());
    }
    let id = module
        .declare_function("support_parity", Linkage::Export, &sig)
        .expect("declare the function");
    module.define_function(id, &mut ctx).expect("define the function");
    sites.into_inner().define(module).expect("define the site counters");
    module.finalize_definitions().expect("finalize the function");
    let code = module.get_finalized_function(id);
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    let mut process = Process::with_node(Rc::new(Node::empty()), schemas, 0, DEFAULT_REDUCTIONS_PER_QUANTUM);
    unsafe { pinned_abi::call1(code, &mut process, word) }
}

type JitModuleOf = <JitBackend as Backend>::Module;

/// A struct reference at `address`, marked as a literal when `literal`.
fn struct_ref(address: u64, literal: bool) -> u64 {
    let packing = AnyValueRefPacking::current();
    let tag = u64::from(ValueKind::STRUCT.tag()) << packing.tag_shift();
    address | tag | if literal { packing.literal_bit() } else { 0 }
}

/// One when `stored_parts` of `known` is the same word and kind as
/// `stored_parts_of_ref` of `reference`.
fn stored_parts_agree(
    body: &mut CodegenFn<'_, '_, JitModuleOf>,
    known: CodegenValue,
    reference: ir::Value,
) -> ir::Value {
    let [known_word, known_kind] = stored_parts(body, known);
    let [read_word, read_kind] = super::list_cell::stored_parts_of_ref(body.b, reference);
    let same_word = body.b.ins().icmp(IntCC::Equal, known_word, read_word);
    let same_kind = body.b.ins().icmp(IntCC::Equal, known_kind, read_kind);
    let both = body.b.ins().band(same_word, same_kind);
    body.b.ins().uextend(types::I64, both)
}

/// A static tuple's reference, held as a value of known kind, is stored as the
/// reference read at run time is: the address with its literal bit, and its kind.
#[test]
fn a_static_tuple_known_is_stored_as_its_reference_is_read() {
    let word = struct_ref(0x1000, true);
    let agree = run(word, |body, reference| {
        let known = CodegenValue::known(reference, ValueKind::STRUCT);
        stored_parts_agree(body, known, reference)
    });
    assert_eq!(agree, 1);
}

/// The empty list held as a value of known kind is stored as the empty list's
/// reference is read at run time.
#[test]
fn the_empty_list_known_is_stored_as_its_reference_is_read() {
    let agree = run(0, |body, _| {
        let empty = body.empty_list_ref();
        let known = CodegenValue::known(empty, ValueKind::LIST);
        stored_parts_agree(body, known, empty)
    });
    assert_eq!(agree, 1);
}

/// A struct of known kind that is no literal, as a heap value typed by its
/// evidence would be, is marked shared when it is shared; a literal, whose
/// header is marked already, is left as it is.
#[test]
fn sharing_a_known_struct_marks_it_unless_it_is_marked() {
    for (header, literal, expected) in [
        (0u64, false, STRUCT_HEADER_SHARED_MASK),
        (STRUCT_HEADER_SHARED_MASK, true, STRUCT_HEADER_SHARED_MASK),
    ] {
        let object = Box::new(header);
        let word = struct_ref(std::ptr::from_ref(&*object) as u64, literal);
        run(word, |body, reference| {
            body.share(CodegenValue::known(reference, ValueKind::STRUCT));
            body.b.ins().iconst(types::I64, 0)
        });
        assert_eq!(*object & STRUCT_HEADER_SHARED_MASK, expected, "literal: {literal}");
    }
}
