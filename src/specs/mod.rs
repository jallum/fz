mod r#match;
mod model;
mod select;

pub(crate) use r#match::{
    SchemeInstantiation, SchemeMatch, instantiate_match, instantiate_match_with_slots,
    resolve_closure_return,
};
pub(crate) use model::{
    ResolvedSpec, ResolvedSpecSet, ResolvedStructFieldShape, ResolvedTypeShape,
    StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep,
};
pub(crate) use select::{spec_set_correspondence_groups, unique_matching_params};

#[cfg(test)]
pub(crate) use select::{matching_result, spec_correspondence_groups};

#[cfg(test)]
mod tests;
