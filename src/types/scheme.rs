use crate::types::{Sigma, TypeVarId, Types};
use std::collections::HashMap;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SchemeInstantiation<T> {
    Known(T),
    Underconstrained(T),
    Invalid,
}

impl<T> SchemeInstantiation<T> {
    pub fn known(self) -> Option<T> {
        match self {
            Self::Known(ty) => Some(ty),
            Self::Underconstrained(_) | Self::Invalid => None,
        }
    }
}

pub fn instantiate_result<T: Types + ?Sized>(
    t: &mut T,
    params: &[T::Ty],
    result: &T::Ty,
    constraints: &HashMap<TypeVarId, T::Ty>,
    witnesses: &[T::Ty],
) -> SchemeInstantiation<T::Ty> {
    if params.len() != witnesses.len() {
        return SchemeInstantiation::Invalid;
    }

    let mut sigma: Sigma<T::Ty> = Sigma::new();
    for (pattern, witness) in params.iter().zip(witnesses.iter()) {
        t.collect_instantiation_subst(pattern, witness, &mut sigma);
    }

    for (var, bound) in constraints {
        let Some(actual) = sigma.get(var) else {
            return SchemeInstantiation::Underconstrained(t.instantiate(result, &sigma));
        };
        if !t.is_subtype(actual, bound) {
            return SchemeInstantiation::Invalid;
        }
    }

    for (pattern, witness) in params.iter().zip(witnesses.iter()) {
        let expected = t.instantiate(pattern, &sigma);
        if !t.has_vars(witness) && !t.is_subtype(witness, &expected) {
            return SchemeInstantiation::Invalid;
        }
    }

    let instantiated = t.instantiate(result, &sigma);
    if t.has_vars(&instantiated) {
        SchemeInstantiation::Underconstrained(instantiated)
    } else {
        SchemeInstantiation::Known(instantiated)
    }
}
