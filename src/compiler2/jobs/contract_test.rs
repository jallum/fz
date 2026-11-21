use super::checked_return;
use crate::dispatch_matrix::pattern::LastResort;
use crate::fz_ir::{ExternAbi, ExternReturn, ExternTy};

fn failure() -> LastResort {
    LastResort::declared("Elixir.ArithmeticError".to_string(), "bad argument")
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

/// A projection is a claim about the argument's type and the integer result,
/// so a declaration that cannot carry it is refused where it is written.
#[test]
fn a_projection_needs_one_function_parameter_and_an_integer_result() {
    use super::super::super::types::Types;
    use super::projection_fits;
    use crate::function_surface::ExternProjection::ArrowArity;

    let mut types = Types::new();
    let (fun, any, int) = (types.fun_top(), types.any(), types.int());
    let integer = ExternReturn::Scalar(ExternTy::I64);
    assert_eq!(projection_fits(&mut types, ArrowArity, &[fun], &integer), Ok(()));
    for (params, ret) in [
        (vec![any], integer.clone()),
        (vec![int], integer.clone()),
        (vec![fun, fun], integer.clone()),
        (vec![fun], ExternReturn::Scalar(ExternTy::F64)),
    ] {
        let refusal = projection_fits(&mut types, ArrowArity, &params, &ret).unwrap_err();
        assert_eq!(
            refusal,
            "`projects: :arrow_arity` needs one `fun` parameter and an `integer` result"
        );
    }
}
