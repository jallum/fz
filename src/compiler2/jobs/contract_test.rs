use super::{checked_return, worded_failure};
use crate::dispatch_matrix::pattern::LastResort;
use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};

fn failure() -> LastResort {
    LastResort::declared("Elixir.ArithmeticError".to_string(), "bad argument", None)
}

#[test]
fn a_declared_failure_checks_an_integer_or_a_float_result_of_a_c_extern() {
    for lane in [ExternTy::I64, ExternTy::F64] {
        assert_eq!(
            checked_return(ExternReturn::Scalar(lane), ExternAbi::C, failure()),
            Ok(ExternReturn::Checked(lane, failure()))
        );
    }
}

#[test]
fn a_declared_failure_needs_the_c_abi_because_only_a_c_function_returns_the_pair() {
    let refusal = checked_return(ExternReturn::Scalar(ExternTy::I64), ExternAbi::Fz, failure())
        .expect_err("an fz-ABI extern has no value-and-flag pair to return");
    assert!(refusal.starts_with("`raises:` needs the `C` ABI"), "{refusal}");
}

#[test]
fn a_declared_failure_refuses_every_result_that_is_not_an_integer_or_a_float() {
    for wire in [
        ExternReturn::Scalar(ExternTy::Bool),
        ExternReturn::Scalar(ExternTy::I32),
        ExternReturn::Scalar(ExternTy::Any),
        ExternReturn::Scalar(ExternTy::Binary),
    ] {
        let refusal = checked_return(wire.clone(), ExternAbi::C, failure())
            .expect_err("only an integer or a float can be the value of a checked return");
        assert!(refusal.contains("declared `integer` or `float`"), "{wire:?}: {refusal}");
    }
}

#[test]
fn an_unworded_failure_is_an_fz_extern_that_never_returns() {
    assert_eq!(
        worded_failure(&ExternReturn::Scalar(ExternTy::Never), ExternAbi::Fz),
        Ok(())
    );
}

#[test]
fn an_unworded_failure_refuses_a_c_extern_because_only_the_runtime_words_a_message() {
    let refusal = worded_failure(&ExternReturn::Scalar(ExternTy::Never), ExternAbi::C)
        .expect_err("a C extern declares its message");
    assert!(refusal.contains("needs the `fz` ABI"), "{refusal}");
}

#[test]
fn an_unworded_failure_refuses_a_result_because_a_returning_extern_leaves_its_caller_to_unwind() {
    for wire in [ExternReturn::Scalar(ExternTy::Any), ExternReturn::Scalar(ExternTy::I64)] {
        let refusal = worded_failure(&wire, ExternAbi::Fz).expect_err("only a `none` extern never returns");
        assert!(refusal.contains("declared `none`"), "{wire:?}: {refusal}");
    }
}
