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
