mod apply;
mod r#match;
mod model;
mod select;
mod validate;

pub(crate) use apply::{
    CallbackReturnDemand, CallbackReturnFact, CallbackReturnQuery, SpecApplicationOutcome,
    apply_spec_set,
};
pub(crate) use r#match::{
    SchemeInstantiation, SchemeMatch, instantiate_match, resolve_closure_return,
};
pub(crate) use model::{
    ResolvedSpec, ResolvedSpecSet, ResolvedStructFieldShape, ResolvedTypeShape,
    StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep,
};
pub(crate) use select::{spec_set_correspondence_groups, unique_matching_params};
pub(crate) use validate::declared_specs_cover_inferred_spec;

#[cfg(test)]
pub(crate) use select::{matching_result, spec_correspondence_groups};

#[cfg(test)]
mod tests;
