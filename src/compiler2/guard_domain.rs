//! The guard domains: what a call to a guard helper asks when some of its
//! arguments are literals.
//!
//! A helper is a type test on its own when its clauses are two plain ones, one
//! answering `true` for annotated parameters and one answering `false`
//! (`dispatch_matrix::pattern`). `Kernel.is_function/2` is not that shape: its
//! clauses read the arity argument, so it is a test only once that argument is
//! a literal. The table here says, per helper, which type a list of literal arguments
//! asks of the others. A call with no entry stays the helper, which
//! raises on a bad argument as it does everywhere else.
//!
//! The meaning of each entry is also written as the helper's clauses in
//! `lib/`, and `guard_domain_test` runs both on the same arguments.

use super::types::{Ty, Types};
use crate::ground_value::GroundValue;

/// The types a call's other arguments must have: the argument's position and
/// its type.
type Asked = Vec<(u32, Ty)>;

/// One helper's domain: for the literal arguments of a call, the type each
/// listed argument must have for the call to hold.
struct GuardDomain {
    module_atom: &'static str,
    name: &'static str,
    arity: usize,
    at: fn(&mut Types, &[Option<GroundValue>]) -> Option<Asked>,
}

const GUARD_DOMAINS: [GuardDomain; 1] = [GuardDomain {
    module_atom: "Elixir.Kernel",
    name: "is_function",
    arity: 2,
    at: is_function_at,
}];

/// What the helper `name` of the module atom `module_atom` asks of its
/// arguments at `arguments`, where a literal is `Some` and a variable `None`.
pub(super) fn guard_domain_at(
    types: &mut Types,
    module_atom: &str,
    name: &str,
    arguments: &[Option<GroundValue>],
) -> Option<Asked> {
    let domain = GUARD_DOMAINS
        .iter()
        .find(|domain| domain.module_atom == module_atom && domain.name == name && domain.arity == arguments.len())?;
    (domain.at)(types, arguments)
}

/// `is_function(f, n)` holds exactly when `f` is a function of `n` arguments,
/// the type `f :: (any, ..., any -> any)` asks. A negative or non-integer `n`
/// has no domain: the call raises.
fn is_function_at(types: &mut Types, arguments: &[Option<GroundValue>]) -> Option<Asked> {
    let [None, Some(GroundValue::Int(arity))] = arguments else {
        return None;
    };
    let any = types.any();
    let arrow = types.arrow(&vec![any; usize::try_from(*arity).ok()?], any);
    Some(vec![(0, types.runtime_type_test_envelope(arrow))])
}
