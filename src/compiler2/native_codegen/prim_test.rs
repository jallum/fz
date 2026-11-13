use super::*;
use std::str::FromStr;

fn classify(target: &str, fields: [ExternTy; 2]) -> Result<[ir::Type; 2], CodegenError> {
    c_pair_return_types(&Triple::from_str(target).expect("valid target triple"), fields)
}

#[test]
fn x86_64_uses_each_field_natural_return_bank_on_linux_and_darwin() {
    for target in ["x86_64-unknown-linux-gnu", "x86_64-apple-darwin"] {
        assert_eq!(
            classify(target, [ExternTy::I64, ExternTy::Bool]).unwrap(),
            [types::I64, types::I64]
        );
        assert_eq!(
            classify(target, [ExternTy::I64, ExternTy::F64]).unwrap(),
            [types::I64, types::F64]
        );
        assert_eq!(
            classify(target, [ExternTy::F64, ExternTy::Bool]).unwrap(),
            [types::F64, types::I64]
        );
        assert_eq!(
            classify(target, [ExternTy::F64, ExternTy::F64]).unwrap(),
            [types::F64, types::F64]
        );
    }
}

#[test]
fn aarch64_only_uses_float_banks_for_a_float_hfa() {
    for target in ["aarch64-unknown-linux-gnu", "aarch64-apple-darwin"] {
        assert_eq!(
            classify(target, [ExternTy::F64, ExternTy::F64]).unwrap(),
            [types::F64, types::F64]
        );
        assert_eq!(
            classify(target, [ExternTy::I64, ExternTy::F64]).unwrap(),
            [types::I64, types::I64]
        );
        assert_eq!(
            classify(target, [ExternTy::F64, ExternTy::Bool]).unwrap(),
            [types::I64, types::I64]
        );
    }
}

#[test]
fn unsupported_target_abi_is_refused_before_emitting_a_call() {
    assert!(classify("x86_64-pc-windows-msvc", [ExternTy::I64, ExternTy::F64]).is_err());
    assert!(classify("x86_64-unknown-freebsd", [ExternTy::I64, ExternTy::F64]).is_err());
    assert!(classify("aarch64-pc-windows-msvc", [ExternTy::F64, ExternTy::I64]).is_err());
    assert!(classify("riscv64gc-unknown-linux-gnu", [ExternTy::I64, ExternTy::I64]).is_err());
}

/// Runs `read` against a lone variable bound to `value`, inside a function
/// that exists only to give the reader a builder.
fn read_var_as(
    value: impl FnOnce(&mut FunctionBuilder<'_>) -> CodegenValue,
    read: impl FnOnce(&mut CodegenFn<'_, '_, cranelift_object::ObjectModule>, &HashMap<u32, CodegenValue>),
) {
    use cranelift_module::{Module as _, default_libcall_names};
    let isa = super::super::host_isa_with(true);
    let object = cranelift_object::ObjectBuilder::new(isa, "lane_reader_test", default_libcall_names())
        .expect("an object builder for the host");
    let mut module = cranelift_object::ObjectModule::new(object);
    let mut ctx = module.make_context();
    let mut fbctx = cranelift_frontend::FunctionBuilderContext::new();
    let mut b = FunctionBuilder::new(&mut ctx.func, &mut fbctx);
    let entry = b.create_block();
    b.switch_to_block(entry);
    b.seal_block(entry);
    let value = value(&mut b);
    let mut cache = CodegenCache::default();
    let mut body = CodegenFn::new(&mut b, &mut module, &mut cache);
    read(&mut body, &HashMap::from([(0, value)]));
}

/// An integer read of a float-lane value refuses, and so does a float read of
/// an integer-lane value: a lane is never reinterpreted as another.
#[test]
#[should_panic(expected = "cannot read raw i64 from non-integer value")]
fn a_float_lane_value_is_refused_by_the_integer_reader() {
    read_var_as(
        |b| CodegenValue::RawF64(b.ins().f64const(1.5)),
        |body, env| {
            body.as_raw_i64(env, 0);
        },
    );
}

#[test]
#[should_panic(expected = "cannot read raw f64 from non-float value")]
fn an_integer_lane_value_is_refused_by_the_float_reader() {
    read_var_as(
        |b| CodegenValue::RawInt(b.ins().iconst(types::I64, 1)),
        |body, env| {
            body.as_raw_f64(env, 0);
        },
    );
}
