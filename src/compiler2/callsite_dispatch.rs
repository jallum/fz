//! Callsite-owned dispatch helpers.
//!
//! Semantic analysis already settles every concrete target a callsite may reach.
//! This module turns a multi-target summary into a dispatch-matrix decision over
//! the callsite receiver without re-reading protocol registries or inventing a
//! synthetic callback body.

use crate::ast::{Pattern, Spanned};
use crate::dispatch_matrix::pattern::{
    PatternBodyId, PatternDispatchError, PatternDispatchPlan, PatternRow, PatternSubjectRef, SourcePatternRows,
    pattern_dispatch_from_source,
};
use crate::source::Span;

use super::semantic::{CallSiteSummary, CallTargetSummary};
use super::types::Ty;

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct CallSiteDispatch {
    pub(crate) plan: PatternDispatchPlan<Ty>,
    pub(crate) targets: Vec<CallTargetSummary>,
}

pub(crate) fn dispatch_from_callsite_summary(
    summary: &CallSiteSummary,
) -> Result<Option<CallSiteDispatch>, PatternDispatchError> {
    if summary.targets.len() <= 1 {
        return Ok(None);
    }
    let arity = summary.arity();
    let rows = summary
        .targets
        .iter()
        .enumerate()
        .map(|(index, target)| dispatch_row(target, arity, index as PatternBodyId))
        .collect::<Vec<_>>();
    let plan = pattern_dispatch_from_source(SourcePatternRows {
        input_count: arity,
        rows,
    })?;
    Ok(Some(CallSiteDispatch {
        plan,
        targets: summary.targets.clone(),
    }))
}

fn dispatch_row(target: &CallTargetSummary, arity: usize, body_id: PatternBodyId) -> PatternRow<Ty> {
    let mut patterns = Vec::with_capacity(arity);
    patterns.resize_with(arity, || Spanned::new(Pattern::Wildcard, Span::DUMMY));
    let receiver = target
        .surface_inputs
        .first()
        .copied()
        .expect("multi-target callsite dispatch requires a receiver input");
    PatternRow {
        patterns,
        preconditions: vec![(PatternSubjectRef::Input(0), receiver)],
        guard: None,
        body_id,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::{SelectedCallee, World};
    use crate::dispatch_matrix::{DispatchNode, Region, SubjectSource};
    use crate::telemetry::ConfiguredTelemetry;

    #[test]
    fn multi_target_summary_builds_receiver_type_dispatch_rows() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let list_impl = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "list_impl", 1);
        let range_impl = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "range_impl", 1);
        let any = world.types_mut().any();
        let list = world.types_mut().list(any);
        let range = world.types_mut().opaque_of("impl-target::Range");
        let summary = CallSiteSummary {
            targets: vec![
                CallTargetSummary {
                    callee: SelectedCallee::Function(list_impl),
                    surface_inputs: vec![list],
                    activation: None,
                    return_ty: None,
                },
                CallTargetSummary {
                    callee: SelectedCallee::Function(range_impl),
                    surface_inputs: vec![range],
                    activation: None,
                    return_ty: None,
                },
            ],
            return_ty: None,
        };

        let dispatch = dispatch_from_callsite_summary(&summary)
            .expect("dispatch should compile")
            .expect("multi-target summary should dispatch");

        assert_eq!(dispatch.targets, summary.targets);
        assert_eq!(dispatch.plan.input_count, 1);
        assert_eq!(
            dispatch.plan.matrix.subjects.first().map(|subject| &subject.source),
            Some(&SubjectSource::Input { ordinal: 0 }),
            "callsite dispatch should test the receiver input"
        );
        assert_eq!(
            dispatch
                .plan
                .outcomes
                .iter()
                .map(|outcome| outcome.body_id)
                .collect::<Vec<_>>(),
            vec![0, 1],
            "body ids should stay parallel to summary targets"
        );
        let type_regions = dispatch
            .plan
            .matrix
            .arms
            .iter()
            .map(|arm| {
                arm.questions
                    .iter()
                    .find_map(|question| match question.predicate.region {
                        Region::Type(ty) => Some(ty),
                        _ => None,
                    })
                    .expect("each callsite dispatch arm should type-test the receiver")
            })
            .collect::<Vec<_>>();
        assert_eq!(type_regions, vec![list, range]);
        assert!(
            matches!(
                dispatch.plan.graph.node(dispatch.plan.graph.root),
                Some(DispatchNode::Test { .. })
            ),
            "multi-target callsite dispatch should compile to a real decision graph"
        );
    }

    #[test]
    fn single_target_summary_stays_direct() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let function = world.reference_function(crate::compiler2::ModuleId::GLOBAL, "impl", 1);
        let any = world.types_mut().any();
        let summary = CallSiteSummary {
            targets: vec![CallTargetSummary {
                callee: SelectedCallee::Function(function),
                surface_inputs: vec![any],
                activation: None,
                return_ty: None,
            }],
            return_ty: None,
        };

        assert!(
            dispatch_from_callsite_summary(&summary)
                .expect("single target should not fail")
                .is_none(),
            "single-target callsites must remain ordinary direct calls"
        );
    }
}
