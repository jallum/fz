use super::r#match::instantiate_match_with_slots;
use super::{ResolvedSpec, ResolvedSpecSet, SchemeInstantiation};
use crate::types::{ClosureTypes, KeySlot, Ty};

pub(crate) fn declared_specs_cover_inferred_spec<T: ClosureTypes<Ty = Ty> + ?Sized>(
    t: &mut T,
    declared_specs: &ResolvedSpecSet,
    inferred_inputs: &[KeySlot],
    inferred_result: &Ty,
) -> bool {
    declared_specs.arrows.iter().any(|declared| {
        declared_arrow_covers_inferred_spec(t, declared, inferred_inputs, inferred_result)
    })
}

fn declared_arrow_covers_inferred_spec<T: ClosureTypes<Ty = Ty> + ?Sized>(
    t: &mut T,
    declared: &ResolvedSpec,
    inferred_inputs: &[KeySlot],
    inferred_result: &Ty,
) -> bool {
    match instantiate_match_with_slots(
        t,
        &declared.params,
        &declared.result,
        &declared.constraints,
        inferred_inputs,
    ) {
        SchemeInstantiation::Known(matched) => t.is_subtype(inferred_result, &matched.result),
        SchemeInstantiation::Underconstrained(_) | SchemeInstantiation::Invalid => false,
    }
}
