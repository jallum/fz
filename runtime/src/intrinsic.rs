//! Closed compiler/runtime operations. Names are used only when a declaration
//! resolves; execution consumes the identity and its exact descriptor.

use crate::any_value::ValueKind;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Domain {
    Integer,
    Float,
    Any,
    Binary,
    Callable(u16),
}

impl Domain {
    /// Exact runtime kinds admitted before an operation reads its inputs.
    /// `None` means every value is admitted, without inspecting its kind.
    pub fn runtime_kinds(self) -> Option<&'static [ValueKind]> {
        match self {
            Self::Integer => Some(&[ValueKind::INT]),
            Self::Float => Some(&[ValueKind::FLOAT]),
            Self::Any => None,
            Self::Binary => Some(&ValueKind::BINARY_REPRS),
            Self::Callable(_) => Some(&[ValueKind::CLOSURE]),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Arithmetic {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Comparison {
    Less,
    LessEqual,
    Greater,
    GreaterEqual,
    Equal,
    NotEqual,
    Identical,
    NotIdentical,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum Operation {
    Arithmetic(Arithmetic),
    Negate,
    Compare(Comparison),
    Panic,
    SelfPid,
    Send,
    Spawn,
    SpawnOpt,
    MakeRef,
    MakeResource,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Descriptor {
    pub operation: Operation,
    pub inputs: &'static [Domain],
    pub result: Option<Domain>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FaultBehavior {
    None,
    CheckedInteger,
    FiniteFloat,
    Always,
}

impl Descriptor {
    pub fn guard_admissible(self) -> bool {
        matches!(
            self.operation,
            Operation::Arithmetic(_) | Operation::Negate | Operation::Compare(_)
        )
    }

    pub fn scheduler_visible(self) -> bool {
        matches!(self.operation, Operation::Send | Operation::Spawn | Operation::SpawnOpt)
    }

    pub fn domain_fault_possible(self) -> bool {
        self.inputs.iter().any(|domain| domain.runtime_kinds().is_some())
    }

    pub fn observable(self, domain_possible: bool) -> bool {
        !self.guard_admissible() || self.fault_behavior() != FaultBehavior::None || domain_possible
    }

    pub fn fault_behavior(self) -> FaultBehavior {
        match self.operation {
            Operation::Arithmetic(_) | Operation::Negate => {
                if self.result == Some(Domain::Integer) {
                    FaultBehavior::CheckedInteger
                } else {
                    FaultBehavior::FiniteFloat
                }
            }
            Operation::Panic => FaultBehavior::Always,
            Operation::Compare(_)
            | Operation::SelfPid
            | Operation::Send
            | Operation::Spawn
            | Operation::SpawnOpt
            | Operation::MakeRef
            | Operation::MakeResource => FaultBehavior::None,
        }
    }
}

macro_rules! intrinsics {
    ($( $id:ident => ($name:literal, $op:expr, [$($input:ident $(($arity:literal))?),*], $result:expr) ),* $(,)?) => {
        #[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
        pub enum Intrinsic { $($id),* }

        impl Intrinsic {
            pub const ALL: &'static [Self] = &[$(Self::$id),*];

            pub fn resolve(name: &str) -> Option<Self> {
                match name { $($name => Some(Self::$id),)* _ => None }
            }

            pub fn descriptor(self) -> Descriptor {
                match self {
                    $(Self::$id => Descriptor {
                        operation: $op,
                        inputs: &[$(Domain::$input $(($arity))?),*],
                        result: $result,
                    }),*
                }
            }
        }
    };
}

use Arithmetic::{Add, Divide, Multiply, Remainder, Subtract};
use Comparison::{Equal, Greater, GreaterEqual, Identical, Less, LessEqual, NotEqual, NotIdentical};
use Domain::{Any, Float, Integer};
use Operation::{Arithmetic as Arith, Compare, Negate};

intrinsics! {
    NegI => ("neg_i", Negate, [Integer], Some(Integer)),
    NegF => ("neg_f", Negate, [Float], Some(Float)),
    AddII => ("add_ii", Arith(Add), [Integer, Integer], Some(Integer)),
    AddIF => ("add_if", Arith(Add), [Integer, Float], Some(Float)),
    AddFF => ("add_ff", Arith(Add), [Float, Float], Some(Float)),
    SubII => ("sub_ii", Arith(Subtract), [Integer, Integer], Some(Integer)),
    SubIF => ("sub_if", Arith(Subtract), [Integer, Float], Some(Float)),
    SubFI => ("sub_fi", Arith(Subtract), [Float, Integer], Some(Float)),
    SubFF => ("sub_ff", Arith(Subtract), [Float, Float], Some(Float)),
    MulII => ("mul_ii", Arith(Multiply), [Integer, Integer], Some(Integer)),
    MulIF => ("mul_if", Arith(Multiply), [Integer, Float], Some(Float)),
    MulFF => ("mul_ff", Arith(Multiply), [Float, Float], Some(Float)),
    DivII => ("div_ii", Arith(Divide), [Integer, Integer], Some(Integer)),
    SlashII => ("div_ii_to_float", Arith(Divide), [Integer, Integer], Some(Float)),
    DivIF => ("div_if", Arith(Divide), [Integer, Float], Some(Float)),
    DivFI => ("div_fi", Arith(Divide), [Float, Integer], Some(Float)),
    DivFF => ("div_ff", Arith(Divide), [Float, Float], Some(Float)),
    RemII => ("rem_ii", Arith(Remainder), [Integer, Integer], Some(Integer)),
    RemIF => ("rem_if", Arith(Remainder), [Integer, Float], Some(Float)),
    RemFI => ("rem_fi", Arith(Remainder), [Float, Integer], Some(Float)),
    RemFF => ("rem_ff", Arith(Remainder), [Float, Float], Some(Float)),
    LtII => ("lt_ii", Compare(Less), [Integer, Integer], Some(Any)),
    LtIF => ("lt_if", Compare(Less), [Integer, Float], Some(Any)),
    LtFI => ("lt_fi", Compare(Less), [Float, Integer], Some(Any)),
    LtFF => ("lt_ff", Compare(Less), [Float, Float], Some(Any)),
    LtBB => ("lt_bb", Compare(Less), [Binary, Binary], Some(Any)),
    LeII => ("lte_ii", Compare(LessEqual), [Integer, Integer], Some(Any)),
    LeIF => ("lte_if", Compare(LessEqual), [Integer, Float], Some(Any)),
    LeFI => ("lte_fi", Compare(LessEqual), [Float, Integer], Some(Any)),
    LeFF => ("lte_ff", Compare(LessEqual), [Float, Float], Some(Any)),
    LeBB => ("lte_bb", Compare(LessEqual), [Binary, Binary], Some(Any)),
    GtII => ("gt_ii", Compare(Greater), [Integer, Integer], Some(Any)),
    GtIF => ("gt_if", Compare(Greater), [Integer, Float], Some(Any)),
    GtFI => ("gt_fi", Compare(Greater), [Float, Integer], Some(Any)),
    GtFF => ("gt_ff", Compare(Greater), [Float, Float], Some(Any)),
    GtBB => ("gt_bb", Compare(Greater), [Binary, Binary], Some(Any)),
    GeII => ("gte_ii", Compare(GreaterEqual), [Integer, Integer], Some(Any)),
    GeIF => ("gte_if", Compare(GreaterEqual), [Integer, Float], Some(Any)),
    GeFI => ("gte_fi", Compare(GreaterEqual), [Float, Integer], Some(Any)),
    GeFF => ("gte_ff", Compare(GreaterEqual), [Float, Float], Some(Any)),
    GeBB => ("gte_bb", Compare(GreaterEqual), [Binary, Binary], Some(Any)),
    Eq => ("eq", Compare(Equal), [Any, Any], Some(Any)),
    Neq => ("neq", Compare(NotEqual), [Any, Any], Some(Any)),
    Identical => ("identical", Compare(Identical), [Any, Any], Some(Any)),
    NotIdentical => ("not_identical", Compare(NotIdentical), [Any, Any], Some(Any)),
    Panic => ("panic", Operation::Panic, [Any], None),
    SelfPid => ("self", Operation::SelfPid, [], Some(Integer)),
    Send => ("send", Operation::Send, [Integer, Any], Some(Any)),
    Spawn => ("spawn", Operation::Spawn, [Callable(0)], Some(Integer)),
    SpawnOpt => ("spawn_opt", Operation::SpawnOpt, [Callable(0), Integer], Some(Integer)),
    MakeRef => ("make_ref", Operation::MakeRef, [], Some(Integer)),
    MakeResource => ("make_resource", Operation::MakeResource, [Integer, Callable(1)], Some(Any)),
}

/// A fault is control flow, never a language value. Guard consumers preserve it
/// until the enclosing guard can reject its clause; ordinary calls fail.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
#[repr(u8)]
pub enum IntrinsicFault {
    Domain = 1,
    IntegerOverflow = 2,
    ZeroDivisor = 3,
    NonfiniteFloat = 4,
}

impl std::fmt::Display for IntrinsicFault {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(match self {
            Self::Domain => "intrinsic argument is outside its domain",
            Self::IntegerOverflow => "integer overflow",
            Self::ZeroDivisor => "division by zero",
            Self::NonfiniteFloat => "nonfinite floating point result",
        })
    }
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum NumericValue {
    Integer(i64),
    Float(f64),
}

impl NumericValue {
    fn lane(self) -> Domain {
        match self {
            Self::Integer(_) => Integer,
            Self::Float(_) => Float,
        }
    }

    fn as_float(self) -> f64 {
        match self {
            Self::Integer(value) => value as f64,
            Self::Float(value) => value,
        }
    }
}

impl Intrinsic {
    pub fn evaluate_numeric(self, args: &[NumericValue]) -> Result<NumericValue, IntrinsicFault> {
        let descriptor = self.descriptor();
        if args.len() != descriptor.inputs.len()
            || args
                .iter()
                .zip(descriptor.inputs)
                .any(|(value, lane)| value.lane() != *lane)
        {
            return Err(IntrinsicFault::Domain);
        }
        if descriptor.result == Some(Integer) {
            let result = match (descriptor.operation, args) {
                (Negate, [NumericValue::Integer(value)]) => value.checked_neg(),
                (Arith(op), [NumericValue::Integer(left), NumericValue::Integer(right)]) => {
                    if matches!(op, Divide | Remainder) && *right == 0 {
                        return Err(IntrinsicFault::ZeroDivisor);
                    }
                    match op {
                        Add => left.checked_add(*right),
                        Subtract => left.checked_sub(*right),
                        Multiply => left.checked_mul(*right),
                        Divide => left.checked_div(*right),
                        Remainder => left.checked_rem(*right),
                    }
                }
                _ => return Err(IntrinsicFault::Domain),
            };
            return result.map(NumericValue::Integer).ok_or(IntrinsicFault::IntegerOverflow);
        }
        let result = match (descriptor.operation, args) {
            (Negate, [value]) => -value.as_float(),
            (Arith(op), [left, right]) => {
                let (left, right) = (left.as_float(), right.as_float());
                if matches!(op, Divide | Remainder) && right == 0.0 {
                    return Err(IntrinsicFault::ZeroDivisor);
                }
                match op {
                    Add => left + right,
                    Subtract => left - right,
                    Multiply => left * right,
                    Divide => left / right,
                    Remainder => left % right,
                }
            }
            _ => return Err(IntrinsicFault::Domain),
        };
        if result.is_finite() {
            Ok(NumericValue::Float(result))
        } else {
            Err(IntrinsicFault::NonfiniteFloat)
        }
    }
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_intrinsic_fault(code: u64) -> ! {
    let fault = match code {
        2 => IntrinsicFault::IntegerOverflow,
        3 => IntrinsicFault::ZeroDivisor,
        4 => IntrinsicFault::NonfiniteFloat,
        _ => IntrinsicFault::Domain,
    };
    eprintln!("fz intrinsic fault: {fault}");
    std::process::abort()
}

#[cfg(test)]
mod tests {
    use super::*;
    use NumericValue::{Float as F, Integer as I};

    #[test]
    fn numeric_intrinsics_preserve_lanes_and_noncommutative_operand_order() {
        for (identity, args, expected) in [
            (Intrinsic::DivII, vec![I(7), I(2)], I(3)),
            (Intrinsic::SlashII, vec![I(7), I(2)], F(3.5)),
            (Intrinsic::SubIF, vec![I(7), F(2.5)], F(4.5)),
            (Intrinsic::SubFI, vec![F(7.5), I(2)], F(5.5)),
            (Intrinsic::RemFI, vec![F(-7.5), I(2)], F(-1.5)),
        ] {
            assert_eq!(identity.evaluate_numeric(&args), Ok(expected), "{identity:?}");
        }
        assert_eq!(
            Intrinsic::SubIF.evaluate_numeric(&[F(7.5), I(2)]),
            Err(IntrinsicFault::Domain)
        );
        assert_eq!(
            Intrinsic::NegF
                .evaluate_numeric(&[F(0.0)])
                .unwrap()
                .as_float()
                .to_bits(),
            (-0.0f64).to_bits()
        );
    }

    #[test]
    fn arithmetic_faults_never_publish_overflow_or_nonfinite_values() {
        for (identity, args, fault) in [
            (
                Intrinsic::AddII,
                vec![I(i64::MAX), I(1)],
                IntrinsicFault::IntegerOverflow,
            ),
            (
                Intrinsic::SubII,
                vec![I(i64::MIN), I(1)],
                IntrinsicFault::IntegerOverflow,
            ),
            (
                Intrinsic::MulII,
                vec![I(i64::MAX), I(2)],
                IntrinsicFault::IntegerOverflow,
            ),
            (Intrinsic::NegI, vec![I(i64::MIN)], IntrinsicFault::IntegerOverflow),
            (
                Intrinsic::DivII,
                vec![I(i64::MIN), I(-1)],
                IntrinsicFault::IntegerOverflow,
            ),
            (
                Intrinsic::RemII,
                vec![I(i64::MIN), I(-1)],
                IntrinsicFault::IntegerOverflow,
            ),
            (Intrinsic::DivII, vec![I(1), I(0)], IntrinsicFault::ZeroDivisor),
            (Intrinsic::RemII, vec![I(1), I(0)], IntrinsicFault::ZeroDivisor),
            (Intrinsic::SlashII, vec![I(1), I(0)], IntrinsicFault::ZeroDivisor),
            (Intrinsic::DivFF, vec![F(1.0), F(-0.0)], IntrinsicFault::ZeroDivisor),
            (
                Intrinsic::MulFF,
                vec![F(f64::MAX), F(2.0)],
                IntrinsicFault::NonfiniteFloat,
            ),
        ] {
            assert_eq!(identity.evaluate_numeric(&args), Err(fault), "{identity:?}");
        }
    }

    #[test]
    fn every_restricted_intrinsic_keeps_its_domain_fault_observable() {
        for identity in Intrinsic::ALL {
            let descriptor = identity.descriptor();
            if descriptor.inputs.iter().any(|lane| *lane != Domain::Any) {
                assert!(descriptor.domain_fault_possible(), "{identity:?}");
                assert!(descriptor.observable(true), "{identity:?}");
            }
        }
        assert_eq!(Intrinsic::Eq.descriptor().fault_behavior(), FaultBehavior::None);
        assert!(!Intrinsic::Eq.descriptor().observable(false));
    }

    #[test]
    fn only_pure_intrinsic_leaves_are_guard_admissible() {
        for intrinsic in Intrinsic::ALL {
            let descriptor = intrinsic.descriptor();
            let pure = matches!(descriptor.operation, Arith(_) | Negate | Compare(_));
            assert_eq!(descriptor.guard_admissible(), pure);
        }
        assert!(Intrinsic::Send.descriptor().scheduler_visible());
        assert_eq!(Intrinsic::Panic.descriptor().fault_behavior(), FaultBehavior::Always);
        assert!(
            Intrinsic::AddII.descriptor().observable(false),
            "a checked arithmetic fault is observable even when its value is unused"
        );
    }
}
