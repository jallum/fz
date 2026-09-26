use super::super::host_isa_with;
use super::*;
use crate::compiler2::native_codegen::runtime_call::runtime_func_ref;
use cranelift_module::{Module as ClModule, default_libcall_names};
use cranelift_object::{ObjectBuilder, ObjectModule};

/// A dispatch body asks for a helper by its Rust item, and the first ask
/// declares the symbol. Asking again reuses that declaration, so a body
/// names each helper once however many times its plan calls it.
#[test]
fn a_body_declares_each_runtime_helper_once() {
    let isa = host_isa_with(true);
    let object = ObjectBuilder::new(isa, "receive_dispatch_test", default_libcall_names())
        .expect("an object builder for the host");
    let mut module = ObjectModule::new(object);
    let mut ctx = module.make_context();
    ctx.func.signature = receive_dispatch_signature(&mut module);
    let mut fbctx = FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.append_block_params_for_function_params(entry);
    b.switch_to_block(entry);
    b.seal_block(entry);

    let mut body = DispatchBody::new(&mut b, &mut module);
    let first = runtime_func_ref!(body, fz_type_of(_));
    let again = runtime_func_ref!(body, fz_type_of(_));
    let other = runtime_func_ref!(body, fz_truthy_ref(_));
    let declared = body.b.func.dfg.ext_funcs.len();

    assert_eq!(first, again, "a second ask for one helper reuses its declaration");
    assert_ne!(first, other, "distinct helpers are distinct declarations");
    assert_eq!(declared, 2, "the body declares one symbol per helper it calls");
}

#[test]
fn dispatch_const_value_materializes_only_receive_scalar_consts() {
    let module = Module {
        atom_names: vec!["ok".to_string()],
        ..Module::default()
    };

    let cases = [
        (GroundValue::Int(-7), Some(DispatchConstValue::Int(-7))),
        (GroundValue::Float(12), Some(DispatchConstValue::Float(12))),
        (GroundValue::Atom("ok".to_string()), Some(DispatchConstValue::Atom(0))),
        (
            GroundValue::Bool(true),
            Some(DispatchConstValue::Atom(TRUE_ATOM_ID as u64)),
        ),
        (
            GroundValue::Bool(false),
            Some(DispatchConstValue::Atom(FALSE_ATOM_ID as u64)),
        ),
        (GroundValue::Nil, Some(DispatchConstValue::Atom(NIL_ATOM_ID as u64))),
        (GroundValue::Utf8Binary(b"ok".to_vec()), None),
    ];

    for (value, expected) in cases {
        let actual = dispatch_const_value(&module, &value).expect("dispatch const lowering should not fail");
        assert_eq!(
            actual, expected,
            "unexpected native receive dispatch const for {value:?}"
        );
        if let Some(actual) = actual {
            assert_ne!(
                actual.kind(),
                ValueKind::NULL,
                "native receive dispatch const materialized null"
            );
        }
    }
}
