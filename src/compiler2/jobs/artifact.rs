//! Compiler2 artifact materialization jobs.
//!
//! This module turns a closed semantic root into one backend-owned artifact
//! snapshot. It does not ask semantic questions: every executable body, return
//! type, and selected call edge must already exist in the closed fact set.

use std::collections::HashMap;

use super::super::artifact::{MaterializedCallEdge, MaterializedExecutable, MaterializedProgram};
use super::super::body::LoweredBody;
use super::super::drive::{FactKey, JobEffects};
use super::super::identity::{ExecutableKey, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{CallSiteKey, SelectedCallee};
use super::super::world::World;
use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;

/// Materializes one closed root into a backend-owned program snapshot.
///
/// The job reads the current `SemanticClosed(root)` payload, clones only the
/// reachable lowered bodies, prunes unreachable clauses, and freezes each live
/// callsite to its selected callee executable. Missing semantic constituents
/// are fatal: materialization never reopens discovery.
pub(super) fn materialize_root(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let closed_fact = FactKey::SemanticClosed(root_id);
    let Some(closed_revision) = world.fact_revision(closed_fact.clone()) else {
        return Ok(JobEffects::wait_on(
            closed_fact,
            [super::super::Job::CheckSemanticClosure(root_id)],
        ));
    };

    let closure = world.semantic_closure(root_id);
    let reads = vec![closed_fact];
    let mut executables = HashMap::new();

    for executable in &closure.executables {
        if world.fact_revision(FactKey::Executable(executable.clone())).is_none()
            || world
                .fact_revision(FactKey::ActivationAnalyzed(executable.activation.clone()))
                .is_none()
            || world
                .fact_revision(FactKey::ReturnType(executable.activation.clone()))
                .is_none()
            || world
                .fact_revision(FactKey::LoweredBody(executable.activation.function))
                .is_none()
        {
            return Ok(wait_for_fresh_closure(root_id));
        }

        let Some(analysis) = world.activation_analysis(&executable.activation).cloned() else {
            return Ok(wait_for_fresh_closure(root_id));
        };
        let Some(return_ty) = world.activation_return(&executable.activation) else {
            return Ok(wait_for_fresh_closure(root_id));
        };
        let body = prune_lowered_body(
            world.lowered_body(executable.activation.function),
            &analysis.reachable_clauses,
        );
        let Some(call_edges) = materialize_call_edges(world, root_id, executable, &analysis.callsites)? else {
            return Ok(wait_for_fresh_closure(root_id));
        };
        executables.insert(
            executable.clone(),
            MaterializedExecutable {
                return_ty,
                body,
                call_edges,
            },
        );
    }

    let program = MaterializedProgram {
        semantic_revision: closed_revision,
        entry: closure.entry,
        executables,
    };
    let revision = world.define_materialized_program(root_id, program);
    Ok(JobEffects {
        reads,
        outputs: vec![(FactKey::MaterializedProgram(root_id), revision)],
        ..JobEffects::default()
    })
}

fn materialize_call_edges(
    world: &mut World<'_>,
    root_id: RootId,
    executable: &ExecutableKey,
    callsites: &[super::super::CallSiteId],
) -> Result<Option<HashMap<super::super::CallSiteId, MaterializedCallEdge>>, FatalError> {
    let mut call_edges = HashMap::new();
    for callsite in callsites {
        let key = CallSiteKey {
            activation: executable.activation.clone(),
            callsite: *callsite,
        };
        if world.fact_revision(FactKey::SelectedCallee(key.clone())).is_none()
            || world.fact_revision(FactKey::ReturnNeed(key.clone())).is_none()
        {
            return Ok(None);
        }
        let Some(summary) = world.callsite_summary(&key).cloned() else {
            return Ok(None);
        };
        let SelectedCallee::Function(function) = summary.callee else {
            return Err(incomplete_semantic_plan(
                world,
                root_id,
                "materialization cannot lower unresolved named call targets",
            ));
        };
        call_edges.insert(
            *callsite,
            MaterializedCallEdge {
                callee: SelectedCallee::Function(function),
                input_types: summary.input_types,
                need: summary.need,
                return_ty: summary.return_ty,
            },
        );
    }
    Ok(Some(call_edges))
}

fn prune_lowered_body(body: LoweredBody, reachable_clauses: &[u32]) -> LoweredBody {
    match body {
        LoweredBody::Extern { .. } => body,
        LoweredBody::Clauses { clauses, generated } => LoweredBody::Clauses {
            clauses: reachable_clauses
                .iter()
                .map(|clause_id| clauses[*clause_id as usize].clone())
                .collect(),
            generated,
        },
    }
}

fn incomplete_semantic_plan(world: &World<'_>, root_id: RootId, message: impl Into<String>) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 materialization for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}

fn wait_for_fresh_closure(root_id: RootId) -> JobEffects {
    JobEffects::wait_on(
        FactKey::SemanticClosed(root_id),
        [super::super::Job::CheckSemanticClosure(root_id)],
    )
}
