//! Scheduler producers for the reach facts: `StaticReach(f)` and
//! `ExecutableReach(e, chain)`.
//!
//! A reach job walks the edge facts of everything its node reaches and reads
//! each one, so a change to any edge in the cone reopens the answer and the
//! answer stands on exactly what was read. It never reads another reach:
//! nodes that reach each other each walk the same cycle and conclude the same
//! set, so no group is needed.

use crate::fast_hash::HashSet;
use std::collections::BTreeSet;
use std::rc::Rc;

use super::super::drive::{AnswerUse, FactKey, Job, JobEffects, UseCollector};
use super::super::identity::{ExecutableKey, FunctionId};
use super::super::reach::{CallChain, ReachSet, executable_successors};
use super::super::world::World;
use fz_engine::{FactUse, FatalError};

/// A walk that met facts not yet answered stops with what it read and what it
/// waits on; it runs again when one of them arrives.
fn waiting_on(uses: UseCollector) -> JobEffects {
    let (reads, waits) = uses.into_reads_waits();
    JobEffects {
        reads,
        waits: waits.into_iter().collect(),
        ..JobEffects::default()
    }
}

/// The facts `derive_static_reach` cannot start without: the function's own
/// edges. Every other edge list it needs is a read or wait the walk finds.
pub(super) fn derive_static_reach_gates(world: &World, function: FunctionId) -> Vec<FactKey> {
    let edges = FactKey::StaticCallees(function);
    if world.has_fact(&edges) {
        Vec::new()
    } else {
        vec![edges]
    }
}

/// Derives every function reachable from `function` over one or more static
/// call edges, by walking the `StaticCallees` fact of each function met.
pub(super) fn derive_static_reach(world: &mut World, function: FunctionId) -> Result<JobEffects, FatalError> {
    let mut uses = UseCollector::new(Job::DeriveStaticReach(function));
    let mut reach = BTreeSet::new();
    let mut walked = HashSet::from_iter([function]);
    let mut frontier = vec![function];
    while let Some(node) = frontier.pop() {
        if matches!(uses.answer(world, FactKey::StaticCallees(node)), AnswerUse::Wait(_)) {
            continue;
        }
        for &callee in world.static_callees(node) {
            reach.insert(callee);
            if walked.insert(callee) {
                frontier.push(callee);
            }
        }
    }
    if uses.has_waits() {
        return Ok(waiting_on(uses));
    }
    let (reads, _) = uses.into_reads_waits();
    let fact = FactKey::StaticReach(function);
    let changed = world.define_static_reach(function, Rc::new(reach));
    Ok(JobEffects {
        reads,
        outputs: vec![fact.clone()],
        changed: changed.then_some(fact).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// The facts `derive_executable_reach` cannot start without: the executable's
/// own facts, which hold its call-site targets.
pub(super) fn derive_executable_reach_gates(world: &World, executable: &ExecutableKey) -> Vec<FactKey> {
    let facts = FactKey::ExecutableFacts(executable.clone());
    if world.fact_is_settled(&facts) {
        Vec::new()
    } else {
        vec![facts]
    }
}

/// Derives every executable reachable from `executable` over one or more
/// call-site targets of `chain`, by walking the settled `ExecutableFacts` of
/// each executable met.
pub(super) fn derive_executable_reach(
    world: &mut World,
    executable: &ExecutableKey,
    chain: CallChain,
) -> Result<JobEffects, FatalError> {
    let mut uses = UseCollector::new(Job::DeriveExecutableReach(executable.clone(), chain));
    let mut reach = ReachSet::default();
    let mut walked = HashSet::from_iter([executable.clone()]);
    let mut frontier = vec![executable.clone()];
    while let Some(node) = frontier.pop() {
        let facts = FactUse::settled(FactKey::ExecutableFacts(node.clone()));
        if !world.fact_is_settled(facts.fact()) {
            uses.record_wait(facts);
            continue;
        }
        uses.record_read(facts);
        for callee in executable_successors(world, &node, chain) {
            reach.insert(callee.clone());
            if walked.insert(callee.clone()) {
                frontier.push(callee);
            }
        }
    }
    if uses.has_waits() {
        return Ok(waiting_on(uses));
    }
    let (reads, _) = uses.into_reads_waits();
    let fact = FactKey::ExecutableReach(executable.clone(), chain);
    let changed = world.define_executable_reach(executable.clone(), chain, Rc::new(reach));
    Ok(JobEffects {
        reads,
        outputs: vec![fact.clone()],
        changed: changed.then_some(fact).into_iter().collect(),
        ..JobEffects::default()
    })
}
