mod r#match;
mod model;

pub(crate) use r#match::{
    SchemeInstantiation, SchemeMatch, instantiate_match, instantiate_match_with_slots,
    resolve_closure_return,
};
pub(crate) use model::{
    ResolvedSpec, ResolvedSpecSet, ResolvedStructFieldShape, ResolvedTypeShape,
    StructuralCorrespondenceGroup, StructuralOccurrence, StructuralPathStep,
};

#[cfg(test)]
mod tests;
