use std::collections::{BTreeSet, HashMap, HashSet};

use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueSource, LoweredBody, LoweredStep,
    LoweredTail, ValueId, delivered_value_joins,
};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallableDemand, CallableFlowFact, CallableSurface, ExecutableRuntimeDemand,
    RuntimeDemand, SelectedCallee, SemanticClosure, ShapeDemand,
};
use super::super::transport::{
    ActivationSymbol, BoundaryDescr, BoundaryFacts, BoundaryId, CallableDescr, CallableDirectEdge, CallableFacts,
    CallableId, CodegenLaneRepr, CodegenSeam, CodegenSeamFact, ExecutableSymbol, LaneId, ShapeDescr, ShapeId,
    TransportClass, TransportPlan, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::semantic::executable_callsite_needs;

#[derive(Debug, Clone)]
struct ExecutableContext {
    analysis: ActivationAnalysis,
    return_ty: Ty,
    body: LoweredBody,
    runtime_demand: ExecutableRuntimeDemand,
    callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
    callsite_args: HashMap<CallSiteId, Vec<CallArg>>,
    local_sources: HashMap<ValueId, TransportSource>,
    callsite_dests: HashMap<CallSiteId, ControlDestination>,
    return_sources: Vec<TransportSource>,
    resume_entries: Vec<ResumeEntry>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum TransportSource {
    ExecutableReturn,
    ExecutableInput(usize),
    LocalValue(ValueId),
    CallsiteReturn(CallSiteId),
    Join(Box<[TransportSource]>),
    TupleValue(Box<[ValueId]>),
    TupleField { source: ValueId, index: usize },
    CallableValue(LocalCallableProducer),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct LocalCallableProducer {
    function: FunctionId,
    captures: Box<[ValueId]>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct ResumeEntry {
    entry: ControlEntryId,
    value: ValueId,
    callsite: Option<CallSiteId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct CallableFactsDraft {
    resolutions: Vec<ExecutableSymbol>,
    direct_surfaces: Vec<Box<[ShapeId]>>,
    direct_edges: Vec<CallableDirectEdge>,
    boundary_ids: Vec<BoundaryId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundaryFactsDraft {
    publications: Vec<TransportPosition>,
    resolutions: Vec<ExecutableSymbol>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceShape {
    Exact(ShapeId),
    Recursive,
    Unknown,
}

/// The identity of an in-progress source projection. Two projections with the
/// same `(executable, source, demand)` are the same node of the value-flow DAG;
/// re-encountering one already on the stack is a cycle.
type CycleFrame = (ExecutableKey, TransportSource, RuntimeDemand);

/// Memo identity: a cycle frame plus the producing type, which the resolved
/// shape also depends on.
type MemoKey = (ExecutableKey, TransportSource, RuntimeDemand, Ty);

/// One projection tree's cycle stack, carrying Tarjan low-links so a completed
/// frame can tell whether it is the root of its strongly-connected component.
/// A fresh `Cycle` is built per top-level projection (exactly where the bare
/// `visiting` vector used to be), so cycle-detection scope is unchanged.
#[derive(Default)]
struct Cycle {
    stack: Vec<CycleFrame>,
    lowlinks: Vec<usize>,
}

impl Cycle {
    /// Depth of `frame` if it is currently in progress on this tree's stack.
    fn depth_of(&self, frame: &CycleFrame) -> Option<usize> {
        self.stack.iter().position(|in_progress| in_progress == frame)
    }

    /// Begin a frame; its low-link starts at its own depth.
    fn push(&mut self, frame: CycleFrame) -> usize {
        let depth = self.stack.len();
        self.stack.push(frame);
        self.lowlinks.push(depth);
        depth
    }

    /// Record a back-edge from the frame currently on top to an in-progress
    /// frame at `target_depth`, lowering the top frame's low-link.
    fn back_edge(&mut self, target_depth: usize) {
        if let Some(low) = self.lowlinks.last_mut() {
            *low = (*low).min(target_depth);
        }
    }

    /// Complete the top frame: pop it, fold its low-link into the parent
    /// (standard Tarjan propagation), and return that low-link.
    fn pop(&mut self) -> usize {
        let low = self.lowlinks.pop().expect("cycle low-link stack underflow");
        self.stack.pop();
        if let Some(parent) = self.lowlinks.last_mut() {
            *parent = (*parent).min(low);
        }
        low
    }
}

/// Plan-scoped memo of pure (publication-free) source projections, keyed by
/// `MemoKey`. The value is the resolved shape plus the fact delta this frame
/// contributes; the delta is replayed -- idempotently, since every `record_*`
/// is an additive union -- into each caller's accumulator on a hit. Only frames
/// that are their own SCC root are stored, so a cached result never depends on a
/// computation still in progress above it.
#[derive(Default)]
struct ProjectionMemo {
    entries: HashMap<MemoKey, (SourceShape, TransportFactsBuilder)>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct TransportFactsBuilder {
    callables: HashMap<CallableId, CallableFactsDraft>,
    boundaries: HashMap<BoundaryId, BoundaryFactsDraft>,
    publication_source_shapes: HashMap<TransportPosition, Vec<ShapeId>>,
    publication_source_positions: HashMap<TransportPosition, Vec<TransportPosition>>,
}

#[derive(Debug, Clone, Default, PartialEq, Eq)]
struct ShapeConstraintGraph {
    anchors: Vec<(TransportPosition, ShapeId)>,
    equalities: Vec<(
        TransportPosition,
        TransportPosition,
        &'static std::panic::Location<'static>,
    )>,
}

impl ShapeConstraintGraph {
    fn anchor(&mut self, position: TransportPosition, shape: ShapeId) {
        self.anchors.push((position, shape));
    }

    #[track_caller]
    fn equal(&mut self, left: TransportPosition, right: TransportPosition) {
        self.equalities.push((left, right, std::panic::Location::caller()));
    }

    fn has_anchor(&self, position: &TransportPosition) -> bool {
        self.anchors.iter().any(|(anchored, _)| anchored == position)
    }

    fn anchor_shape(&self, position: &TransportPosition) -> Option<ShapeId> {
        self.anchors
            .iter()
            .find_map(|(anchored, shape)| (anchored == position).then_some(*shape))
    }

    fn solve(self) -> HashMap<TransportPosition, ShapeId> {
        let mut union = PositionUnion::default();
        for (position, _) in &self.anchors {
            union.add(position.clone());
        }
        for (left, right, _) in &self.equalities {
            union.union(left.clone(), right.clone());
        }

        let mut component_shapes = HashMap::<usize, ShapeId>::new();
        for (position, shape) in &self.anchors {
            let root = union.find_existing(position);
            if let Some(existing) = component_shapes.insert(root, *shape) {
                let component = union
                    .positions()
                    .filter(|candidate| union.find_existing(candidate) == root)
                    .cloned()
                    .collect::<Vec<_>>();
                let anchors = self
                    .anchors
                    .iter()
                    .filter(|(candidate, _)| union.find_existing(candidate) == root)
                    .cloned()
                    .collect::<Vec<_>>();
                let equalities = self
                    .equalities
                    .iter()
                    .filter(|(left, right, _)| union.find_existing(left) == root || union.find_existing(right) == root)
                    .map(|(left, right, caller)| (left.clone(), right.clone(), caller.to_string()))
                    .collect::<Vec<_>>();
                assert_eq!(
                    existing, *shape,
                    "transport shape anchors disagree for connected position component: {position:?}; component={component:?}; anchors={anchors:?}; equalities={equalities:?}"
                );
            }
        }

        union
            .positions()
            .filter_map(|position| {
                let root = union.find_existing(position);
                component_shapes
                    .get(&root)
                    .copied()
                    .map(|shape| (position.clone(), shape))
            })
            .collect()
    }

    fn equivalent_positions(&self) -> HashMap<TransportPosition, Vec<TransportPosition>> {
        let mut union = PositionUnion::default();
        for (position, _) in &self.anchors {
            union.add(position.clone());
        }
        for (left, right, _) in &self.equalities {
            union.union(left.clone(), right.clone());
        }

        let mut by_root = HashMap::<usize, Vec<TransportPosition>>::new();
        for position in union.positions() {
            let root = union.find_existing(position);
            by_root.entry(root).or_default().push(position.clone());
        }

        let mut out = HashMap::new();
        for positions in by_root.values() {
            for position in positions {
                out.insert(position.clone(), positions.clone());
            }
        }
        out
    }
}

#[derive(Debug, Clone, Default)]
struct PositionUnion {
    positions: Vec<TransportPosition>,
    indexes: HashMap<TransportPosition, usize>,
    parents: Vec<usize>,
}

impl PositionUnion {
    fn add(&mut self, position: TransportPosition) -> usize {
        if let Some(index) = self.indexes.get(&position).copied() {
            return index;
        }
        let index = self.positions.len();
        self.positions.push(position.clone());
        self.indexes.insert(position, index);
        self.parents.push(index);
        index
    }

    fn union(&mut self, left: TransportPosition, right: TransportPosition) {
        let left = self.add(left);
        let right = self.add(right);
        let left_root = self.find_index(left);
        let right_root = self.find_index(right);
        if left_root != right_root {
            self.parents[right_root] = left_root;
        }
    }

    fn find_existing(&self, position: &TransportPosition) -> usize {
        let index = self
            .indexes
            .get(position)
            .copied()
            .expect("shape constraint position must be registered before solving");
        self.find_index_readonly(index)
    }

    fn find_index(&mut self, index: usize) -> usize {
        let parent = self.parents[index];
        if parent == index {
            return index;
        }
        let root = self.find_index(parent);
        self.parents[index] = root;
        root
    }

    fn find_index_readonly(&self, index: usize) -> usize {
        let mut cursor = index;
        while self.parents[cursor] != cursor {
            cursor = self.parents[cursor];
        }
        cursor
    }

    fn positions(&self) -> impl Iterator<Item = &TransportPosition> {
        self.positions.iter()
    }
}

impl TransportFactsBuilder {
    fn record_callable(
        &mut self,
        callable: CallableId,
        resolutions: Vec<ExecutableSymbol>,
        direct_surfaces: Vec<Box<[ShapeId]>>,
        direct_edges: Vec<CallableDirectEdge>,
        boundary_ids: Vec<BoundaryId>,
    ) {
        let entry = self.callables.entry(callable).or_insert_with(|| CallableFactsDraft {
            resolutions: Vec::new(),
            direct_surfaces: Vec::new(),
            direct_edges: Vec::new(),
            boundary_ids: Vec::new(),
        });
        extend_unique(&mut entry.resolutions, resolutions);
        extend_unique(&mut entry.direct_surfaces, direct_surfaces);
        extend_unique(&mut entry.direct_edges, direct_edges);
        extend_unique(&mut entry.boundary_ids, boundary_ids);
    }

    fn record_boundary(&mut self, boundary: BoundaryId, publication: TransportPosition) {
        let entry = self.boundaries.entry(boundary).or_insert_with(|| BoundaryFactsDraft {
            publications: Vec::new(),
            resolutions: Vec::new(),
        });
        if !entry.publications.contains(&publication) {
            entry.publications.push(publication);
        }
    }

    fn record_boundary_resolutions(&mut self, boundary: BoundaryId, resolutions: Vec<ExecutableSymbol>) {
        let entry = self.boundaries.entry(boundary).or_insert_with(|| BoundaryFactsDraft {
            publications: Vec::new(),
            resolutions: Vec::new(),
        });
        extend_unique(&mut entry.resolutions, resolutions);
    }

    fn record_publication_source_shapes(&mut self, publication: TransportPosition, shapes: Vec<ShapeId>) {
        let entry = self.publication_source_shapes.entry(publication).or_default();
        extend_unique(entry, shapes);
    }

    fn record_publication_source_positions(&mut self, publication: TransportPosition, sources: Vec<TransportPosition>) {
        let entry = self.publication_source_positions.entry(publication).or_default();
        extend_unique(entry, sources);
    }

    fn record_callable_shape_surface_publications(
        &mut self,
        world: &World<'_>,
        publication: TransportPosition,
        shapes: &[ShapeId],
        surface_shapes: &[Box<[ShapeId]>],
    ) {
        let boundary_ids = shapes
            .iter()
            .filter_map(|shape| match world.shape(*shape) {
                ShapeDescr::Callable(callable) => self.callables.get(callable),
                ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Tuple(_) => None,
            })
            .flat_map(|facts| facts.boundary_ids.iter().copied())
            .collect::<Vec<_>>();
        let _ = surface_shapes;
        for boundary in boundary_ids {
            self.record_boundary(boundary, publication.clone());
        }
    }

    fn expand_boundary_publications(&mut self, equivalents: &HashMap<TransportPosition, Vec<TransportPosition>>) {
        for draft in self.boundaries.values_mut() {
            let publications = draft.publications.clone();
            for publication in publications {
                if let Some(positions) = equivalents.get(&publication) {
                    for position in positions {
                        if !draft.publications.contains(position) {
                            draft.publications.push(position.clone());
                        }
                    }
                }
            }
        }
        let source_shapes = self.publication_source_shapes.clone();
        for (publication, shapes) in source_shapes {
            if let Some(positions) = equivalents.get(&publication) {
                for position in positions {
                    self.record_publication_source_shapes(position.clone(), shapes.clone());
                }
            }
        }
        let source_positions = self.publication_source_positions.clone();
        for (publication, sources) in source_positions {
            if let Some(positions) = equivalents.get(&publication) {
                for position in positions {
                    self.record_publication_source_positions(position.clone(), sources.clone());
                }
            }
        }
    }

    fn resolve_publication_source_boundaries(&mut self, world: &World<'_>) {
        let boundary_ids = self.boundaries.keys().copied().collect::<Vec<_>>();
        let mut derived = Vec::new();
        for boundary in boundary_ids {
            let Some(draft) = self.boundaries.get(&boundary) else {
                continue;
            };
            let boundary_descr = world.boundary(boundary);
            let mut resolutions = Vec::new();
            for publication in &draft.publications {
                if let Some(source_shapes) = self.publication_source_shapes.get(publication) {
                    extend_unique(
                        &mut resolutions,
                        resolution_symbols_for_callable_source_surface(
                            world,
                            self,
                            source_shapes,
                            &boundary_descr.surface_arg_shapes,
                            boundary_descr.published_return_shape,
                        ),
                    );
                }
                if let Some(source_positions) = self.publication_source_positions.get(publication) {
                    extend_unique(
                        &mut resolutions,
                        resolution_symbols_for_source_publications(
                            world,
                            self,
                            source_positions,
                            &boundary_descr.surface_arg_shapes,
                            boundary_descr.published_return_shape,
                        ),
                    );
                }
            }
            if !resolutions.is_empty() {
                derived.push((boundary, resolutions));
            }
        }
        for (boundary, resolutions) in derived {
            self.record_boundary_resolutions(boundary, resolutions);
        }
    }

    /// Fold another fact set into this one. The fact builder is an additive,
    /// idempotent monoid -- every `record_*` only ever unions entries in -- so
    /// committing a speculatively-explored subtree is `self ∪ delta`, never a
    /// structural overwrite. This is what replaces the old "snapshot the whole
    /// builder, then `*facts = staged` or drop it" rollback: a dead branch is
    /// discarded by simply not merging its delta. Taken by reference so a cached
    /// delta can be re-merged on every memo hit without being consumed.
    fn merge(&mut self, other: &TransportFactsBuilder) {
        for (callable, draft) in &other.callables {
            self.record_callable(
                *callable,
                draft.resolutions.clone(),
                draft.direct_surfaces.clone(),
                draft.direct_edges.clone(),
                draft.boundary_ids.clone(),
            );
        }
        for (boundary, draft) in &other.boundaries {
            for publication in &draft.publications {
                self.record_boundary(*boundary, publication.clone());
            }
            self.record_boundary_resolutions(*boundary, draft.resolutions.clone());
        }
        for (publication, shapes) in &other.publication_source_shapes {
            self.record_publication_source_shapes(publication.clone(), shapes.clone());
        }
        for (publication, sources) in &other.publication_source_positions {
            self.record_publication_source_positions(publication.clone(), sources.clone());
        }
    }

    fn finish(self) -> (HashMap<CallableId, CallableFacts>, HashMap<BoundaryId, BoundaryFacts>) {
        let callables = self
            .callables
            .into_iter()
            .map(|(id, mut draft)| {
                draft.resolutions.sort_by_key(executable_symbol_sort_key);
                draft
                    .direct_surfaces
                    .sort_by_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
                draft.direct_edges.sort_by_key(callable_direct_edge_sort_key);
                draft.boundary_ids.sort_by_key(|boundary| boundary.as_u32());
                (
                    id,
                    CallableFacts {
                        resolutions: draft.resolutions.into_boxed_slice(),
                        direct_surfaces: draft.direct_surfaces.into_boxed_slice(),
                        direct_edges: draft.direct_edges.into_boxed_slice(),
                        boundary_ids: draft.boundary_ids.into_boxed_slice(),
                    },
                )
            })
            .collect();
        let boundaries = self
            .boundaries
            .into_iter()
            .map(|(id, mut draft)| {
                draft.resolutions.sort_by_key(executable_symbol_sort_key);
                (
                    id,
                    BoundaryFacts {
                        publications: draft.publications.into_boxed_slice(),
                        resolutions: draft.resolutions.into_boxed_slice(),
                    },
                )
            })
            .collect();
        (callables, boundaries)
    }
}

pub(super) fn derive_transport_plan(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let closed_fact = FactKey::SemanticClosed(root_id);
    if !world.fact_is_settled(&closed_fact) {
        return Ok(JobEffects::wait_on_settled(
            closed_fact,
            [Job::SealSemanticClosure(root_id)],
        ));
    }

    let closure = world.semantic_closure(root_id);
    let mut reads = vec![closed_fact];
    let mut wait_facts = HashSet::new();
    let contexts = collect_transport_contexts(world, &closure, &closure.runtime_demands, &mut reads, &mut wait_facts);

    if !wait_facts.is_empty() {
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(wait_facts),
            follow_up: vec![Job::DeriveTransportPlan(root_id)],
            ..JobEffects::default()
        });
    }

    let mut executables = closure.executables.iter().cloned().collect::<Vec<_>>();
    executables.sort_by_key(|e| executable_sort_key(e, world.types()));

    let plan = project_transport_plan(world, &closure.entry, &executables, &contexts);

    let changed = world.define_transport_plan(root_id, plan);

    Ok(JobEffects {
        reads: settled_uses(reads),
        outputs: vec![FactKey::TransportPlan(root_id)],
        changed: changed.then_some(FactKey::TransportPlan(root_id)).into_iter().collect(),
        ..JobEffects::default()
    })
}

fn collect_transport_contexts(
    world: &mut World<'_>,
    closure: &SemanticClosure,
    runtime_demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    reads: &mut Vec<FactKey>,
    wait_facts: &mut HashSet<FactKey>,
) -> HashMap<ExecutableKey, ExecutableContext> {
    let mut contexts = HashMap::new();
    for executable in &closure.executables {
        let activation_fact = FactKey::ActivationAnalyzed(executable.activation.clone());
        if !world.fact_is_settled(&activation_fact) {
            wait_facts.insert(activation_fact);
            continue;
        }
        reads.push(activation_fact);

        let return_fact = FactKey::ReturnType(executable.activation.clone());
        if !world.fact_is_settled(&return_fact) {
            wait_facts.insert(return_fact);
            continue;
        }
        reads.push(return_fact);

        let analysis = world
            .activation_analysis(&executable.activation)
            .cloned()
            .expect("settled activation analyses should be readable");
        let return_ty = world
            .activation_return(&executable.activation)
            .unwrap_or_else(|| world.types_mut().none());
        let body = world.lowered_body(executable.activation.function);
        let runtime_demand = runtime_demands.get(executable).cloned().unwrap_or_default();
        let callsite_needs = executable_callsite_needs(&body, &analysis.reachable_clauses, executable.need);
        for callsite in &analysis.callsites {
            let fact = FactKey::CallSiteSummary(CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            });
            if !world.fact_is_settled(&fact) {
                wait_facts.insert(fact);
                continue;
            }
            reads.push(fact);
        }
        let resume_entries = collect_resume_entries(&body, &analysis);
        let mut local_sources = collect_value_sources(&body);
        for (value, semantic_index) in collect_clause_parameter_sources(&body) {
            local_sources.insert(value, TransportSource::ExecutableInput(semantic_index));
        }
        for (value, callsite) in collect_callsite_result_origins(&body) {
            local_sources.insert(value, TransportSource::CallsiteReturn(callsite));
        }
        for (value, source) in collect_delivered_value_sources(&body) {
            local_sources.insert(value, source);
        }
        contexts.insert(
            executable.clone(),
            ExecutableContext {
                callsite_args: collect_callsite_args(&body),
                callsite_dests: collect_callsite_dests(&body),
                local_sources,
                return_sources: collect_return_sources(&body, &analysis),
                resume_entries,
                analysis,
                return_ty,
                body,
                runtime_demand,
                callsite_needs,
            },
        );
    }
    contexts
}

#[cfg(test)]
pub(crate) fn transport_plan_for_runtime_demands_for_test(
    world: &mut World<'_>,
    root_id: RootId,
    runtime_demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
) -> TransportPlan {
    let closure = world.semantic_closure(root_id);
    let mut reads = Vec::new();
    let mut wait_facts = HashSet::new();
    let contexts = collect_transport_contexts(world, &closure, runtime_demands, &mut reads, &mut wait_facts);
    assert!(
        wait_facts.is_empty(),
        "transport projection test requires settled prerequisite facts: {wait_facts:?}",
    );
    let mut executables = closure.executables.iter().cloned().collect::<Vec<_>>();
    executables.sort_by_key(|e| executable_sort_key(e, world.types()));
    project_transport_plan(world, &closure.entry, &executables, &contexts)
}

/// Project one executable's intra-executable transport contribution into
/// `facts`/`shape_graph`. This is the per-executable slice of the former
/// single-pass loop, verbatim: it anchors the executable's return, value,
/// demanded-call-arg, return-payload, and resume shapes, and equates its
/// call-arg/capture/return-sharing edges. Cross-executable edges that name a
/// callee return position are still emitted here (they only name positions, not
/// solved shapes); the closure over those edges happens in the fan-in. The
/// shared `memo` is a pure cache, so isolating it per call (as
/// `derive_executable_transport` does) changes only work, never the result.
fn project_one_executable(
    world: &mut World<'_>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    shape_graph: &mut ShapeConstraintGraph,
    memo: &mut ProjectionMemo,
) {
    let symbol = executable_symbol(executable, world.types());
    let clause_params = clause_parameter_values(&context.body);

    let return_position = TransportPosition::ExecutableReturn {
        executable: symbol.clone(),
    };
    let return_shape = shape_for_source(
        world,
        contexts,
        facts,
        executable,
        context,
        context.return_ty,
        &context.runtime_demand.return_demand,
        TransportSource::ExecutableReturn,
        Some(return_position.clone()),
        memo,
    );
    shape_graph.anchor(return_position, return_shape);

    let mut values = context.analysis.value_types.iter().collect::<Vec<_>>();
    values.sort_by_key(|(value, _)| value.as_u32());
    for (&value, &ty) in values {
        if clause_params.contains(&value) {
            continue;
        }
        let demand = context
            .runtime_demand
            .value_demands
            .get(&value)
            .cloned()
            .unwrap_or_default();
        let shape = shape_for_local_value(
            world,
            contexts,
            facts,
            executable,
            context,
            value,
            ty,
            &demand,
            Some(TransportPosition::Value {
                executable: symbol.clone(),
                value,
            }),
            memo,
        );
        shape_graph.anchor(
            TransportPosition::Value {
                executable: symbol.clone(),
                value,
            },
            shape,
        );
    }

    let mut callsite_args = context.callsite_args.iter().collect::<Vec<_>>();
    callsite_args.sort_by_key(|(callsite, _)| callsite.as_u32());
    for (&callsite, args) in callsite_args {
        for (semantic_index, arg) in args.iter().enumerate() {
            let position = TransportPosition::CallArg {
                executable: symbol.clone(),
                callsite,
                semantic_index,
            };
            shape_graph.equal(
                position,
                TransportPosition::Value {
                    executable: symbol.clone(),
                    value: arg.value,
                },
            );
        }
    }
    let mut demanded_call_args = context.runtime_demand.call_arg_demands.iter().collect::<Vec<_>>();
    demanded_call_args.sort_by_key(|(callsite, _)| callsite.as_u32());
    for (&callsite, demands) in demanded_call_args {
        let actual_arity = context.callsite_args.get(&callsite).map_or(0, Vec::len);
        for (semantic_index, demand) in demands.iter().cloned().enumerate() {
            if semantic_index >= actual_arity {
                let position = TransportPosition::CallArg {
                    executable: symbol.clone(),
                    callsite,
                    semantic_index,
                };
                let ty = world.types_mut().any();
                let shape = generic_shape_from_demand(world, ty, &demand, facts, Some(position.clone()));
                shape_graph.anchor(position, shape);
            }
        }
    }

    let mut return_callsites = context
        .callsite_dests
        .iter()
        .filter_map(|(callsite, dest)| matches!(dest, ControlDestination::Return).then_some(*callsite))
        .collect::<Vec<_>>();
    return_callsites.sort_by_key(|callsite| callsite.as_u32());
    return_callsites.dedup();
    for callsite in return_callsites {
        let position = TransportPosition::ReturnPayload {
            executable: symbol.clone(),
            callsite,
        };
        if let Some(callee_return) = callsite_callee_return_position(world, contexts, executable, context, callsite) {
            shape_graph.equal(position, callee_return);
        } else {
            let shape = shape_for_source(
                world,
                contexts,
                facts,
                executable,
                context,
                context.return_ty,
                &context.runtime_demand.return_demand,
                TransportSource::CallsiteReturn(callsite),
                Some(position.clone()),
                memo,
            );
            shape_graph.anchor(position, shape);
        }
    }

    let mut entry_captures = context.runtime_demand.entry_capture_demands.iter().collect::<Vec<_>>();
    entry_captures.sort_by_key(|(entry, _)| entry.as_u32());
    for (&entry, demands) in entry_captures {
        let LoweredBody::Clauses { entries, .. } = &context.body else {
            continue;
        };
        let captures = entries
            .get(entry.as_u32() as usize)
            .map(|lowered| lowered.captures.clone())
            .unwrap_or_default();
        for (capture_index, demand) in demands.iter().cloned().enumerate() {
            let Some(&capture) = captures.get(capture_index) else {
                continue;
            };
            let _ = demand;
            shape_graph.equal(
                TransportPosition::EntryCapture {
                    executable: symbol.clone(),
                    entry,
                    capture_index,
                },
                TransportPosition::Value {
                    executable: symbol.clone(),
                    value: capture,
                },
            );
        }
    }

    for resume in &context.resume_entries {
        let position = TransportPosition::ResumePayload {
            executable: symbol.clone(),
            callsite: resume.callsite,
            entry: resume.entry,
        };
        let demand = resume_demand(context, *resume);
        // An ignored call result still arrives as the value the callee
        // returns: a shared callee delivers its whole return regardless of
        // this caller dropping it. Ignoring it must not mutate the
        // transported shape, so union the resume with the callee return
        // position instead of collapsing it to `Nothing`. The callee's own
        // return anchor already carries divergence (`Nothing` when the
        // callee never returns), so this stays correct for diverging calls.
        // Demanded resumes keep their projection, which settles direct vs.
        // first-class callable transport from the caller's use.
        let shared_return = demand
            .is_ignore()
            .then_some(resume.callsite)
            .flatten()
            .and_then(|callsite| callsite_callee_return_position(world, contexts, executable, context, callsite));
        if let Some(callee_return) = shared_return {
            shape_graph.equal(position, callee_return);
        } else {
            let shape = resume_shape(
                world,
                contexts,
                facts,
                executable,
                context,
                *resume,
                &demand,
                Some(position.clone()),
                memo,
            );
            shape_graph.anchor(position, shape);
        }
    }
}

/// Close the merged per-executable contributions into a finished plan: the
/// cross-executable tail that was always run once per root. It seeds clause
/// parameter and callable-flow equalities, runs the two solves with the input
/// merge between them, expands and resolves boundary publications, and derives
/// the codegen seam. `memo` is fresh here because every projection it needs is
/// pure; the per-executable warm cache contributes nothing to the result.
fn finish_transport_plan(
    world: &mut World<'_>,
    entry_executable: &ExecutableKey,
    executables: &[ExecutableKey],
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    mut facts: TransportFactsBuilder,
    mut shape_graph: ShapeConstraintGraph,
) -> TransportPlan {
    let entry = executable_symbol(entry_executable, world.types());
    let executable_membership = executables
        .iter()
        .map(|e| executable_symbol(e, world.types()))
        .collect::<Vec<_>>()
        .into_boxed_slice();
    let mut memo = ProjectionMemo::default();

    collect_clause_parameter_equalities(contexts, executables, &mut shape_graph, world.types());
    seed_callable_flow_capture_inputs(world, contexts, &mut facts, &mut shape_graph, &mut memo);
    seed_callable_resolution_capture_inputs(world, &facts, &mut shape_graph);
    let local_shapes = shape_graph.clone().solve();
    collect_executable_input_constraints(
        world,
        contexts,
        &mut facts,
        executables,
        &local_shapes,
        &mut shape_graph,
    );
    let equivalents = shape_graph.equivalent_positions();
    let positions = shape_graph.solve();
    facts.expand_boundary_publications(&equivalents);
    facts.resolve_publication_source_boundaries(world);

    let (callables, boundaries) = facts.finish();
    let codegen_seam_facts = derive_codegen_seam_facts(world, contexts, &positions, &boundaries);

    TransportPlan {
        entry,
        executable_membership,
        positions,
        callables,
        boundaries,
        codegen_seam_facts,
    }
}

/// Project a whole root by accumulating every executable's per-executable
/// contribution into one builder, then closing it with the cross-executable
/// tail. The per-executable slice is now [`project_one_executable`] and the
/// tail is [`finish_transport_plan`]; splitting them is the seam the
/// per-executable `ExecutableTransport` fact will publish across.
fn project_transport_plan(
    world: &mut World<'_>,
    entry_executable: &ExecutableKey,
    executables: &[ExecutableKey],
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
) -> TransportPlan {
    let mut facts = TransportFactsBuilder::default();
    let mut shape_graph = ShapeConstraintGraph::default();
    // Plan-scoped: pure source projections are reused across every position and
    // executable in this root, not just within one projection tree.
    let mut memo = ProjectionMemo::default();
    for executable in executables {
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        project_one_executable(
            world,
            executable,
            context,
            contexts,
            &mut facts,
            &mut shape_graph,
            &mut memo,
        );
    }
    finish_transport_plan(world, entry_executable, executables, contexts, facts, shape_graph)
}

fn seed_callable_flow_capture_inputs(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    shape_graph: &mut ShapeConstraintGraph,
    memo: &mut ProjectionMemo,
) {
    let mut flows = contexts
        .iter()
        .flat_map(|(executable, context)| {
            context
                .runtime_demand
                .callable_flows
                .values()
                .map(move |flow| (executable, context, flow))
        })
        .collect::<Vec<_>>();
    flows.sort_by_key(|(executable, _, flow)| {
        (
            executable.activation.function.as_u32(),
            executable.activation.arrow,
            flow.function.as_u32(),
            flow.captures.iter().map(|value| value.as_u32()).collect::<Vec<_>>(),
        )
    });
    flows.dedup_by(|left, right| left.0 == right.0 && left.2 == right.2);

    for (executable, context, flow) in flows {
        if flow.captures.is_empty() || flow.resolutions.is_empty() {
            continue;
        }
        let Some(capture_tys) = flow
            .captures
            .iter()
            .copied()
            .map(|capture| context.analysis.value_types.get(&capture).copied())
            .collect::<Option<Vec<_>>>()
        else {
            continue;
        };
        let resolution_symbols = flow
            .resolutions
            .iter()
            .map(|resolution| executable_symbol(resolution, world.types()))
            .collect::<Vec<_>>();
        for resolution in &resolution_symbols {
            if resolution.activation.function != flow.function {
                continue;
            }
            let capture_demands = capture_demands_for_resolutions(
                contexts,
                &capture_tys,
                std::slice::from_ref(resolution),
                world.types(),
            );
            let capture_shapes = flow
                .captures
                .iter()
                .copied()
                .zip(capture_tys.iter().copied().zip(capture_demands.iter()))
                .map(|(capture, (capture_ty, demand))| {
                    shape_for_local_value(
                        world, contexts, facts, executable, context, capture, capture_ty, demand, None, memo,
                    )
                })
                .collect::<Vec<_>>();
            assert!(
                resolution.activation.input.len() >= capture_shapes.len(),
                "upstream callable-flow resolution is missing capture-prefix inputs: {resolution:?}"
            );
            for (semantic_index, shape) in capture_shapes.iter().copied().enumerate() {
                shape_graph.anchor(
                    TransportPosition::ExecutableInput {
                        executable: resolution.clone(),
                        semantic_index,
                    },
                    shape,
                );
            }
        }
    }
}

fn seed_callable_resolution_capture_inputs(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    shape_graph: &mut ShapeConstraintGraph,
) {
    for (callable, draft) in &facts.callables {
        let descr = world.callable(*callable);
        for resolution in &draft.resolutions {
            if descr.function != Some(resolution.activation.function) {
                continue;
            }
            assert!(
                resolution.activation.input.len() >= descr.capture_shapes.len(),
                "upstream callable-flow resolution is missing capture-prefix inputs: {resolution:?}"
            );
            for (semantic_index, shape) in descr.capture_shapes.iter().copied().enumerate() {
                shape_graph.anchor(
                    TransportPosition::ExecutableInput {
                        executable: resolution.clone(),
                        semantic_index,
                    },
                    shape,
                );
            }
        }
    }
}

fn collect_executable_input_constraints(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executables: &[ExecutableKey],
    local_shapes: &HashMap<TransportPosition, ShapeId>,
    shape_graph: &mut ShapeConstraintGraph,
) {
    let mut anchored_function_inputs = shape_graph
        .anchors
        .iter()
        .filter_map(|(position, _)| match position {
            TransportPosition::ExecutableInput {
                executable,
                semantic_index,
            } => Some((executable.activation.function, *semantic_index)),
            _ => None,
        })
        .collect::<HashSet<_>>();
    for executable in executables {
        let symbol = executable_symbol(executable, world.types());
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        for (semantic_index, ty) in executable.activation.inputs(world.types()).into_iter().enumerate() {
            let function_input = (executable.activation.function, semantic_index);
            let demand = context
                .runtime_demand
                .input_demands
                .get(semantic_index)
                .cloned()
                .unwrap_or_default();
            let position = TransportPosition::ExecutableInput {
                executable: symbol.clone(),
                semantic_index,
            };
            let projected_callable_input_shape = if demand.is_callable()
                && let Some(incoming) = incoming_executable_input_positions(world, contexts, executable, semantic_index)
            {
                facts.record_publication_source_positions(position.clone(), incoming);
                let mut cycle = Cycle::default();
                let mut memo = ProjectionMemo::default();
                match project_executable_input_source(
                    world,
                    contexts,
                    facts,
                    executable,
                    ty,
                    &demand,
                    semantic_index,
                    Some(position.clone()),
                    &mut cycle,
                    &mut memo,
                ) {
                    SourceShape::Exact(shape) => Some(shape),
                    SourceShape::Recursive | SourceShape::Unknown => None,
                }
            } else {
                None
            };
            if executable_input_demand_requires_own_shape(&demand) && !shape_graph.has_anchor(&position) {
                let shape = projected_callable_input_shape
                    .unwrap_or_else(|| shape_for_executable_input(world, ty, &demand, facts, Some(position.clone())));
                shape_graph.anchor(position, shape);
                anchored_function_inputs.insert(function_input);
                continue;
            }
            if let Some(incoming) = incoming_executable_input_positions(world, contexts, executable, semantic_index) {
                let incoming_shapes = incoming
                    .iter()
                    .map(|call_arg| local_shapes.get(call_arg).copied())
                    .collect::<Option<Vec<_>>>();
                if let Some(incoming_shapes) = incoming_shapes {
                    let first = incoming_shapes.first().copied();
                    let anchor_shape = shape_graph.anchor_shape(&position);
                    let force_own_shape = anchored_function_inputs.contains(&function_input);
                    if first.is_some()
                        && incoming_shapes.iter().all(|shape| Some(*shape) == first)
                        && !force_own_shape
                        && anchor_shape.is_none_or(|shape| Some(shape) == first)
                    {
                        for call_arg in incoming {
                            shape_graph.equal(position.clone(), call_arg);
                        }
                    } else if anchor_shape.is_none() {
                        let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                        shape_graph.anchor(position, shape);
                        anchored_function_inputs.insert(function_input);
                    }
                } else if demand.is_ignore()
                    && incoming.len() == 1
                    && !shape_graph.has_anchor(&position)
                    && !anchored_function_inputs.contains(&function_input)
                {
                    // A single ignored incoming arg still carries alias/ownership
                    // evidence; multiple unresolved incoming args would merge
                    // distinct recursive activations before their shapes settle.
                    for call_arg in incoming {
                        shape_graph.equal(position.clone(), call_arg);
                    }
                } else if demand.is_ignore() && !shape_graph.has_anchor(&position) {
                    let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                    shape_graph.anchor(position, shape);
                    anchored_function_inputs.insert(function_input);
                } else if !shape_graph.has_anchor(&position) && !anchored_function_inputs.contains(&function_input) {
                    for call_arg in incoming {
                        shape_graph.equal(position.clone(), call_arg);
                    }
                } else if !shape_graph.has_anchor(&position) {
                    let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                    shape_graph.anchor(position, shape);
                    anchored_function_inputs.insert(function_input);
                }
            } else if !shape_graph.has_anchor(&position) {
                let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                shape_graph.anchor(position, shape);
                anchored_function_inputs.insert(function_input);
            }
        }
    }
}

fn executable_input_demand_requires_own_shape(demand: &RuntimeDemand) -> bool {
    (!matches!(demand.shape, ShapeDemand::Ignore)) || demand.callable.is_first_class()
}

fn collect_clause_parameter_equalities(
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executables: &[ExecutableKey],
    shape_graph: &mut ShapeConstraintGraph,
    types: &Types,
) {
    for executable in executables {
        let symbol = executable_symbol(executable, types);
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        let LoweredBody::Clauses { clauses, .. } = &context.body else {
            continue;
        };
        for clause in clauses {
            for (semantic_index, value) in clause.params.iter().copied().enumerate() {
                let input_position = TransportPosition::ExecutableInput {
                    executable: symbol.clone(),
                    semantic_index,
                };
                shape_graph.equal(
                    input_position,
                    TransportPosition::Value {
                        executable: symbol.clone(),
                        value,
                    },
                );
            }
        }
    }
}

fn derive_codegen_seam_facts(
    world: &World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    positions: &HashMap<TransportPosition, ShapeId>,
    boundaries: &HashMap<BoundaryId, BoundaryFacts>,
) -> Box<[CodegenSeamFact]> {
    let mut out = Vec::new();
    for (position, shape) in positions {
        for (leaf_shape, lane) in lanes_for_codegen_seam_shape(world, *shape) {
            match position {
                TransportPosition::ExecutableInput {
                    executable,
                    semantic_index,
                } => {
                    let repr = codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::FunctionEntry {
                            executable: executable.clone(),
                            semantic_index: *semantic_index,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if executable_context_for_symbol(contexts, executable, world.types())
                        .is_some_and(|context| matches!(context.body, LoweredBody::Extern { .. }))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ExternBoundary {
                                executable: executable.clone(),
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::ExecutableReturn { executable } => {
                    let repr = codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::ReturnDelivery {
                            executable: executable.clone(),
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if executable_context_for_symbol(contexts, executable, world.types())
                        .is_some_and(|context| matches!(context.body, LoweredBody::Extern { .. }))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ExternBoundary {
                                executable: executable.clone(),
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::ResumePayload { executable, entry, .. } => {
                    let repr = block_param_codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::BlockParam {
                            executable: executable.clone(),
                            entry: *entry,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if let TransportPosition::ResumePayload {
                        callsite: Some(callsite),
                        ..
                    } = position
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ContinuationEntry {
                                executable: executable.clone(),
                                callsite: *callsite,
                                entry: *entry,
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::ReturnPayload { executable, callsite } => {
                    let repr = codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::ReturnContinuation {
                            executable: executable.clone(),
                            callsite: *callsite,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                }
                TransportPosition::EntryCapture { executable, entry, .. } => {
                    let repr = block_param_codegen_repr_for_lane(world, lane);
                    out.push(CodegenSeamFact {
                        seam: CodegenSeam::BlockParam {
                            executable: executable.clone(),
                            entry: *entry,
                        },
                        shape: Some(leaf_shape),
                        lane,
                        repr,
                    });
                    if let Some(callsite) = executable_context_for_symbol(contexts, executable, world.types())
                        .and_then(|context| resume_callsite_for_entry(context, *entry))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ContinuationEntry {
                                executable: executable.clone(),
                                callsite,
                                entry: *entry,
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                TransportPosition::CallArg {
                    executable, callsite, ..
                } => {
                    let repr = codegen_repr_for_lane(world, lane);
                    if executable_context_for_symbol(contexts, executable, world.types())
                        .and_then(|context| context.callsite_dests.get(callsite))
                        .is_some_and(|dest| matches!(dest, ControlDestination::Return))
                    {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::TailCall {
                                executable: executable.clone(),
                                callsite: *callsite,
                            },
                            shape: Some(leaf_shape),
                            lane,
                            repr,
                        });
                    }
                }
                _ => {}
            }
        }
    }
    for boundary in boundaries.keys().copied() {
        let descr = world.boundary(boundary);
        // A callable-boundary lane carries the target body's own grounded repr.
        // The boxed closure-apply wrapper is the sole boxing seam: it accepts the
        // uniform `i64` closure-apply ABI from any first-class caller and unboxes
        // each lane to the body's repr before tail-calling it. Because the
        // wrapper tail-calls, it cannot rebox the return — and it does not need
        // to: the continuation that consumes the result is itself derived from
        // the body's grounded return repr (`ReturnDelivery` / `ReturnContinuation`
        // are both `codegen_repr_for_lane`). Forcing these lanes to `ValueRef`
        // therefore only desynchronizes the wrapper's declared return from the
        // body's actual return; the lanes stay grounded.
        for lane in descr
            .published_capture_lanes
            .iter()
            .chain(descr.published_arg_lanes.iter())
            .chain(descr.published_return_lanes.iter())
            .copied()
        {
            out.push(CodegenSeamFact {
                seam: CodegenSeam::CallableBoundary { boundary },
                shape: None,
                lane,
                repr: codegen_repr_for_lane(world, lane),
            });
        }
        if let Some(facts) = boundaries.get(&boundary)
            && !facts.publications.is_empty()
        {
            out.push(CodegenSeamFact {
                seam: CodegenSeam::FirstClassPublication { boundary },
                shape: None,
                lane: descr.published_value_lane,
                repr: CodegenLaneRepr::ValueRef,
            });
            for publication in facts.publications.iter() {
                match publication {
                    TransportPosition::ExecutableInput {
                        executable,
                        semantic_index,
                    } => {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::FunctionEntry {
                                executable: executable.clone(),
                                semantic_index: *semantic_index,
                            },
                            shape: None,
                            lane: descr.published_value_lane,
                            repr: CodegenLaneRepr::ValueRef,
                        });
                    }
                    TransportPosition::ResumePayload {
                        executable,
                        callsite: Some(callsite),
                        entry,
                    } => {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ContinuationEntry {
                                executable: executable.clone(),
                                callsite: *callsite,
                                entry: *entry,
                            },
                            shape: None,
                            lane: descr.published_value_lane,
                            repr: CodegenLaneRepr::ValueRef,
                        });
                    }
                    TransportPosition::ReturnPayload { executable, callsite } => {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ReturnContinuation {
                                executable: executable.clone(),
                                callsite: *callsite,
                            },
                            shape: None,
                            lane: descr.published_value_lane,
                            repr: CodegenLaneRepr::ValueRef,
                        });
                    }
                    TransportPosition::ExecutableReturn { executable } => {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::ReturnDelivery {
                                executable: executable.clone(),
                            },
                            shape: None,
                            lane: descr.published_value_lane,
                            repr: CodegenLaneRepr::ValueRef,
                        });
                    }
                    TransportPosition::ResumePayload {
                        executable,
                        callsite: None,
                        entry,
                    } => {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::BlockParam {
                                executable: executable.clone(),
                                entry: *entry,
                            },
                            shape: None,
                            lane: descr.published_value_lane,
                            repr: CodegenLaneRepr::ValueRef,
                        });
                    }
                    TransportPosition::EntryCapture { executable, entry, .. } => {
                        out.push(CodegenSeamFact {
                            seam: CodegenSeam::BlockParam {
                                executable: executable.clone(),
                                entry: *entry,
                            },
                            shape: None,
                            lane: descr.published_value_lane,
                            repr: CodegenLaneRepr::ValueRef,
                        });
                        if let Some(callsite) = executable_context_for_symbol(contexts, executable, world.types())
                            .and_then(|context| resume_callsite_for_entry(context, *entry))
                        {
                            out.push(CodegenSeamFact {
                                seam: CodegenSeam::ContinuationEntry {
                                    executable: executable.clone(),
                                    callsite,
                                    entry: *entry,
                                },
                                shape: None,
                                lane: descr.published_value_lane,
                                repr: CodegenLaneRepr::ValueRef,
                            });
                        }
                    }
                    TransportPosition::CallArg { .. } | TransportPosition::Value { .. } => {}
                }
            }
        }
    }
    out.sort_by_key(codegen_seam_fact_sort_key);
    out.into_boxed_slice()
}

/// The `ExecutableReturn` position a call result is produced from, when the
/// call settles to exactly one known callee executable. Resume payloads and
/// return payloads are callsite result positions, so they share the producer
/// return `ShapeId` instead of mutating that shape through the caller's local
/// demand.
fn callsite_callee_return_position(
    world: &World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    callsite: CallSiteId,
) -> Option<TransportPosition> {
    let summary = world.callsite_summary(&CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    })?;
    let [target] = summary.targets.as_slice() else {
        return None;
    };
    let SelectedCallee::Function(_) = target.callee else {
        return None;
    };
    let activation = target.activation.clone()?;
    let need = context
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    let callee = ExecutableKey { activation, need };
    contexts
        .contains_key(&callee)
        .then(|| TransportPosition::ExecutableReturn {
            executable: executable_symbol(&callee, world.types()),
        })
}

fn resume_callsite_for_entry(context: &ExecutableContext, entry: ControlEntryId) -> Option<CallSiteId> {
    context
        .resume_entries
        .iter()
        .find_map(|resume| (resume.entry == entry).then_some(resume.callsite).flatten())
}

fn executable_context_for_symbol<'a>(
    contexts: &'a HashMap<ExecutableKey, ExecutableContext>,
    symbol: &ExecutableSymbol,
    types: &Types,
) -> Option<&'a ExecutableContext> {
    contexts.iter().find_map(|(candidate, context)| {
        (candidate.need == symbol.need
            && candidate.activation.function == symbol.activation.function
            && candidate.activation.inputs(types).as_slice() == symbol.activation.input.as_ref())
        .then_some(context)
    })
}

fn lanes_for_codegen_seam_shape(world: &World<'_>, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Callable(callable) => world
            .callable(*callable)
            .capture_lanes
            .iter()
            .copied()
            .map(|lane| (shape, lane))
            .collect(),
        ShapeDescr::Tuple(items) => items
            .iter()
            .copied()
            .flat_map(|item| lanes_for_codegen_seam_shape(world, item))
            .collect(),
    }
}

fn raw_codegen_repr_for_lane(world: &World<'_>, lane: LaneId) -> Option<CodegenLaneRepr> {
    let ty = world.lane(lane).ty;
    if world.types().is_floating(&ty) {
        Some(CodegenLaneRepr::RawF64)
    } else if world.types().is_integer(&ty) {
        Some(CodegenLaneRepr::RawInt)
    } else if world.types().is_atom_type(&ty) {
        Some(CodegenLaneRepr::RawAtom)
    } else {
        None
    }
}

fn codegen_repr_for_lane(world: &World<'_>, lane: LaneId) -> CodegenLaneRepr {
    raw_codegen_repr_for_lane(world, lane).unwrap_or(CodegenLaneRepr::ValueRef)
}

/// Whether a shape is a single boxed value lane -- a `ValueRef`-repr return. A
/// boxed return physically accepts any concrete producer return through the
/// boxing seam, which is what lets a widened recursive activation's `any`
/// return resolve to a concretely-returning producer. Tuple and raw-scalar
/// returns are not boxed, so they keep an exact-match contract.
fn boxed_value_return(world: &World<'_>, shape: ShapeId) -> bool {
    matches!(world.shape(shape), ShapeDescr::Lane(lane) if codegen_repr_for_lane(world, *lane) == CodegenLaneRepr::ValueRef)
}

fn block_param_codegen_repr_for_lane(world: &World<'_>, lane: LaneId) -> CodegenLaneRepr {
    match raw_codegen_repr_for_lane(world, lane) {
        Some(repr @ (CodegenLaneRepr::RawInt | CodegenLaneRepr::RawAtom)) => repr,
        Some(CodegenLaneRepr::RawF64 | CodegenLaneRepr::ValueRef) | None => CodegenLaneRepr::ValueRef,
    }
}

type ExecutableSortKey = (u32, Vec<Ty>, u8, usize);
type CodegenSeamFactSortKey = (u8, ExecutableSortKey, u32, u32, usize, u32, u8);

fn empty_executable_sort_key() -> ExecutableSortKey {
    (0, Vec::new(), 0, 0)
}

fn codegen_seam_fact_sort_key(fact: &CodegenSeamFact) -> CodegenSeamFactSortKey {
    let (kind, executable, boundary, entry, index) = match &fact.seam {
        CodegenSeam::FunctionEntry {
            executable,
            semantic_index,
        } => (0, executable_symbol_sort_key(executable), 0, 0, *semantic_index),
        CodegenSeam::BlockParam { executable, entry } => {
            (1, executable_symbol_sort_key(executable), 0, entry.as_u32(), 0)
        }
        CodegenSeam::ReturnDelivery { executable } => (2, executable_symbol_sort_key(executable), 0, 0, 0),
        CodegenSeam::ContinuationEntry {
            executable,
            callsite,
            entry,
        } => (
            3,
            executable_symbol_sort_key(executable),
            0,
            entry.as_u32(),
            callsite.as_u32() as usize,
        ),
        CodegenSeam::ReturnContinuation { executable, callsite } => (
            4,
            executable_symbol_sort_key(executable),
            0,
            0,
            callsite.as_u32() as usize,
        ),
        CodegenSeam::TailCall { executable, callsite } => (
            5,
            executable_symbol_sort_key(executable),
            0,
            0,
            callsite.as_u32() as usize,
        ),
        CodegenSeam::CallableBoundary { boundary } => (6, empty_executable_sort_key(), boundary.as_u32(), 0, 0),
        CodegenSeam::ExternBoundary { executable } => (7, executable_symbol_sort_key(executable), 0, 0, 0),
        CodegenSeam::FirstClassPublication { boundary } => (8, empty_executable_sort_key(), boundary.as_u32(), 0, 0),
    };
    let repr = match fact.repr {
        CodegenLaneRepr::ValueRef => 0,
        CodegenLaneRepr::RawInt => 1,
        CodegenLaneRepr::RawF64 => 2,
        CodegenLaneRepr::RawAtom => 3,
    };
    (kind, executable, boundary, entry, index, fact.lane.as_u32(), repr)
}

fn executable_sort_key(executable: &ExecutableKey, types: &Types) -> ExecutableSortKey {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        executable.activation.inputs(types),
        need.0,
        need.1,
    )
}

fn executable_symbol(executable: &ExecutableKey, types: &Types) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            input: executable.activation.inputs(types).into_boxed_slice(),
        },
        need: executable.need,
    }
}

fn executable_symbol_sort_key(symbol: &ExecutableSymbol) -> ExecutableSortKey {
    let need = match symbol.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        symbol.activation.function.as_u32(),
        symbol.activation.input.to_vec(),
        need.0,
        need.1,
    )
}

fn callable_direct_edge_sort_key(edge: &CallableDirectEdge) -> (Vec<Ty>, ExecutableSortKey) {
    (
        edge.surface_inputs.to_vec(),
        executable_symbol_sort_key(&edge.resolution),
    )
}

fn extend_unique<T: PartialEq>(target: &mut Vec<T>, values: Vec<T>) {
    for value in values {
        if !target.contains(&value) {
            target.push(value);
        }
    }
}

fn collect_callsite_args(body: &LoweredBody) -> HashMap<CallSiteId, Vec<CallArg>> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return out;
    };
    for clause in clauses {
        collect_tail_call_args(&clause.entry, entries, &mut out);
    }
    out
}

fn collect_callsite_dests(body: &LoweredBody) -> HashMap<CallSiteId, ControlDestination> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return out;
    };
    for clause in clauses {
        collect_tail_call_dests(&clause.entry, entries, &mut out);
    }
    out
}

fn collect_tail_call_dests(
    entry_id: &ControlEntryId,
    entries: &[super::super::body::LoweredEntry],
    out: &mut HashMap<CallSiteId, ControlDestination>,
) {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::DirectCall { callsite, dest, .. } | LoweredTail::ClosureCall { callsite, dest, .. } => {
            out.insert(*callsite, dest.clone());
            if let ControlDestination::Deliver(target) = dest {
                collect_tail_call_dests(target, entries, out);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_tail_call_dests(then_entry, entries, out);
            collect_tail_call_dests(else_entry, entries, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_tail_call_dests(arm_entry, entries, out);
            }
            collect_tail_call_dests(&dispatch.miss_entry, entries, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                collect_tail_call_dests(&clause.entry, entries, out);
            }
            if let Some(after) = &receive.after {
                collect_tail_call_dests(&after.entry, entries, out);
            }
            if let ControlDestination::Deliver(target) = receive.dest {
                collect_tail_call_dests(&target, entries, out);
            }
        }
        LoweredTail::Value { dest, .. } => {
            if let ControlDestination::Deliver(target) = dest {
                collect_tail_call_dests(target, entries, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn collect_tail_call_args(
    entry_id: &ControlEntryId,
    entries: &[super::super::body::LoweredEntry],
    out: &mut HashMap<CallSiteId, Vec<CallArg>>,
) {
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::DirectCall {
            callsite, args, dest, ..
        }
        | LoweredTail::ClosureCall {
            callsite, args, dest, ..
        } => {
            out.insert(*callsite, args.clone());
            if let ControlDestination::Deliver(target) = dest {
                collect_tail_call_args(target, entries, out);
            }
        }
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_tail_call_args(then_entry, entries, out);
            collect_tail_call_args(else_entry, entries, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_tail_call_args(arm_entry, entries, out);
            }
            collect_tail_call_args(&dispatch.miss_entry, entries, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                collect_tail_call_args(&clause.entry, entries, out);
            }
            if let Some(after) = &receive.after {
                collect_tail_call_args(&after.entry, entries, out);
            }
            if let ControlDestination::Deliver(target) = receive.dest {
                collect_tail_call_args(&target, entries, out);
            }
        }
        LoweredTail::Value { dest, .. } => {
            if let ControlDestination::Deliver(target) = dest {
                collect_tail_call_args(target, entries, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn collect_callsite_result_origins(body: &LoweredBody) -> HashMap<ValueId, CallSiteId> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { entries, .. } = body else {
        return out;
    };
    for entry in entries {
        match &entry.tail {
            LoweredTail::DirectCall { value, callsite, .. } | LoweredTail::ClosureCall { value, callsite, .. } => {
                out.insert(*value, *callsite);
            }
            _ => {}
        }
    }
    out
}

fn collect_delivered_value_sources(body: &LoweredBody) -> HashMap<ValueId, TransportSource> {
    delivered_value_joins(body)
        .into_values()
        .map(|join| {
            let mut sources = join
                .sources
                .into_iter()
                .map(|source| match source {
                    DeliveredValueSource::LocalValue(value) => TransportSource::LocalValue(value),
                    DeliveredValueSource::CallsiteReturn(callsite) => TransportSource::CallsiteReturn(callsite),
                })
                .collect::<Vec<_>>();
            sources.sort_by_key(transport_source_sort_key);
            sources.dedup();
            let source = match sources.as_slice() {
                [source] => source.clone(),
                _ => TransportSource::Join(sources.into_boxed_slice()),
            };
            (join.value, source)
        })
        .collect()
}

fn transport_source_sort_key(source: &TransportSource) -> String {
    format!("{source:?}")
}

fn collect_value_sources(body: &LoweredBody) -> HashMap<ValueId, TransportSource> {
    let mut out = HashMap::new();
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return out;
    };
    for clause in clauses {
        for step in &clause.projections {
            collect_step_origin(step, &mut out);
        }
    }
    for entry in entries {
        for step in &entry.steps {
            collect_step_origin(step, &mut out);
        }
    }
    out
}

fn collect_clause_parameter_sources(body: &LoweredBody) -> Vec<(ValueId, usize)> {
    let LoweredBody::Clauses { clauses, .. } = body else {
        return Vec::new();
    };
    clauses
        .iter()
        .flat_map(|clause| {
            clause
                .params
                .iter()
                .copied()
                .enumerate()
                .map(|(semantic_index, value)| (value, semantic_index))
        })
        .collect()
}

fn collect_step_origin(step: &LoweredStep, out: &mut HashMap<ValueId, TransportSource>) {
    match step {
        LoweredStep::Tuple { value, items } => {
            out.insert(*value, TransportSource::TupleValue(items.clone().into_boxed_slice()));
        }
        LoweredStep::TupleField { value, source, index } => {
            out.insert(
                *value,
                TransportSource::TupleField {
                    source: *source,
                    index: *index,
                },
            );
        }
        LoweredStep::FunctionRef { value, function } => {
            out.insert(
                *value,
                TransportSource::CallableValue(LocalCallableProducer {
                    function: *function,
                    captures: Box::default(),
                }),
            );
        }
        LoweredStep::Lambda {
            value,
            function,
            captures,
        } => {
            out.insert(
                *value,
                TransportSource::CallableValue(LocalCallableProducer {
                    function: *function,
                    captures: captures.clone().into_boxed_slice(),
                }),
            );
        }
        _ => {}
    }
}

fn collect_return_sources(body: &LoweredBody, analysis: &ActivationAnalysis) -> Vec<TransportSource> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return Vec::new();
    };
    let reachable_clauses = analysis.reachable_clauses.iter().copied().collect::<HashSet<_>>();
    let reachable_entries = analysis.reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut out = Vec::new();
    for clause_id in reachable_clauses {
        collect_return_sources_from_entry(clauses[clause_id as usize].entry, entries, &reachable_entries, &mut out);
    }
    out
}

fn collect_return_sources_from_entry(
    entry_id: ControlEntryId,
    entries: &[super::super::body::LoweredEntry],
    reachable_entries: &HashSet<ControlEntryId>,
    out: &mut Vec<TransportSource>,
) {
    if !reachable_entries.contains(&entry_id) {
        return;
    }
    let entry = &entries[entry_id.as_u32() as usize];
    match &entry.tail {
        LoweredTail::Value {
            value,
            dest: ControlDestination::Return,
        } => out.push(TransportSource::LocalValue(*value)),
        LoweredTail::DirectCall {
            callsite,
            dest: ControlDestination::Return,
            ..
        }
        | LoweredTail::ClosureCall {
            callsite,
            dest: ControlDestination::Return,
            ..
        } => out.push(TransportSource::CallsiteReturn(*callsite)),
        LoweredTail::Value {
            dest: ControlDestination::Deliver(target),
            ..
        }
        | LoweredTail::DirectCall {
            dest: ControlDestination::Deliver(target),
            ..
        }
        | LoweredTail::ClosureCall {
            dest: ControlDestination::Deliver(target),
            ..
        } => collect_return_sources_from_entry(*target, entries, reachable_entries, out),
        LoweredTail::If {
            then_entry, else_entry, ..
        } => {
            collect_return_sources_from_entry(*then_entry, entries, reachable_entries, out);
            collect_return_sources_from_entry(*else_entry, entries, reachable_entries, out);
        }
        LoweredTail::Dispatch { dispatch, .. } => {
            for arm_entry in &dispatch.arm_entries {
                collect_return_sources_from_entry(*arm_entry, entries, reachable_entries, out);
            }
            collect_return_sources_from_entry(dispatch.miss_entry, entries, reachable_entries, out);
        }
        LoweredTail::Receive(receive) => {
            for clause in &receive.clauses {
                collect_return_sources_from_entry(clause.entry, entries, reachable_entries, out);
            }
            if let Some(after) = &receive.after {
                collect_return_sources_from_entry(after.entry, entries, reachable_entries, out);
            }
            if let ControlDestination::Deliver(target) = receive.dest {
                collect_return_sources_from_entry(target, entries, reachable_entries, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
}

fn collect_resume_entries(body: &LoweredBody, analysis: &ActivationAnalysis) -> Vec<ResumeEntry> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    let reachable_entries = analysis.reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut deliver_callsites = HashMap::new();
    for (entry_index, entry) in entries.iter().enumerate() {
        let source_entry = ControlEntryId::from_u32(entry_index as u32);
        if !reachable_entries.contains(&source_entry) {
            continue;
        }
        let callsite = match entry.tail {
            LoweredTail::DirectCall { callsite, .. } | LoweredTail::ClosureCall { callsite, .. } => Some(callsite),
            _ => None,
        };
        let dest = match &entry.tail {
            LoweredTail::DirectCall { dest, .. } | LoweredTail::ClosureCall { dest, .. } => Some(dest),
            _ => None,
        };
        if let (Some(callsite), Some(ControlDestination::Deliver(target))) = (callsite, dest) {
            deliver_callsites.insert(*target, callsite);
        }
    }
    entries
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| {
            let entry_id = ControlEntryId::from_u32(index as u32);
            if !reachable_entries.contains(&entry_id) && !deliver_callsites.contains_key(&entry_id) {
                return None;
            }
            let super::super::body::ControlEntryOrigin::DeliveredResume { value } = entry.origin else {
                return None;
            };
            Some(ResumeEntry {
                entry: entry_id,
                value,
                callsite: deliver_callsites.get(&entry_id).copied(),
            })
        })
        .collect()
}

fn clause_parameter_values(body: &LoweredBody) -> HashSet<ValueId> {
    let LoweredBody::Clauses { clauses, .. } = body else {
        return HashSet::new();
    };
    clauses
        .iter()
        .flat_map(|clause| clause.params.iter().copied())
        .collect()
}

fn shape_for_local_value(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    value: ValueId,
    ty: Ty,
    demand: &RuntimeDemand,
    publication: Option<TransportPosition>,
    memo: &mut ProjectionMemo,
) -> ShapeId {
    if let (Some(TransportSource::Join(sources)), Some(publication)) =
        (context.local_sources.get(&value), publication.clone())
    {
        let source_positions = sources
            .iter()
            .filter_map(|source| match source {
                TransportSource::LocalValue(source) => Some(TransportPosition::Value {
                    executable: executable_symbol(executable, world.types()),
                    value: *source,
                }),
                _ => None,
            })
            .collect::<Vec<_>>();
        if !source_positions.is_empty() {
            facts.record_publication_source_positions(publication, source_positions);
        }
    }
    shape_for_source(
        world,
        contexts,
        facts,
        executable,
        context,
        ty,
        demand,
        TransportSource::LocalValue(value),
        publication,
        memo,
    )
}

fn shape_for_executable_input(
    world: &mut World<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    if !demand.is_callable() {
        return generic_shape_from_demand(world, ty, demand, facts, publication);
    }
    generic_callable_shape(world, ty, &demand.callable, facts, publication)
}

fn incoming_executable_input_positions(
    world: &World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executable: &ExecutableKey,
    semantic_index: usize,
) -> Option<Vec<TransportPosition>> {
    let mut positions = Vec::new();
    for (caller, context) in contexts {
        if caller == executable {
            continue;
        }
        for (callsite, args) in &context.callsite_args {
            let key = CallSiteKey {
                activation: caller.activation.clone(),
                callsite: *callsite,
            };
            let Some(summary) = world.callsite_summary(&key) else {
                continue;
            };
            if !summary.targets.iter().any(|target| {
                target.activation.as_ref() == Some(&executable.activation)
                    && context
                        .callsite_needs
                        .get(callsite)
                        .copied()
                        .unwrap_or(ExecutableNeed::Value)
                        == executable.need
            }) {
                continue;
            }

            let capture_prefix = executable.activation.input_len(world.types()).checked_sub(args.len())?;
            if semantic_index < capture_prefix {
                return None;
            }
            let arg_index = semantic_index - capture_prefix;
            let position = TransportPosition::CallArg {
                executable: executable_symbol(caller, world.types()),
                callsite: *callsite,
                semantic_index: arg_index,
            };
            positions.push(position);
        }
    }
    (!positions.is_empty()).then_some(positions)
}

fn shape_for_source(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    source: TransportSource,
    publication: Option<TransportPosition>,
    memo: &mut ProjectionMemo,
) -> ShapeId {
    let mut delta = TransportFactsBuilder::default();
    match project_source(
        world,
        contexts,
        &mut delta,
        executable,
        context,
        ty,
        demand,
        source,
        publication.clone(),
        &mut Cycle::default(),
        memo,
    ) {
        SourceShape::Exact(shape) => {
            facts.merge(&delta);
            shape
        }
        SourceShape::Recursive | SourceShape::Unknown => {
            generic_shape_from_demand(world, ty, demand, facts, publication)
        }
    }
}

fn project_source(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    source: TransportSource,
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return SourceShape::Exact(world.intern_shape(ShapeDescr::Nothing));
    }
    let frame = (executable.clone(), source.clone(), demand.clone());
    // A frame already on this tree's stack is a genuine cycle in the current
    // computation; record the back-edge for SCC analysis and report it as
    // recursive. This takes precedence over the memo: a frame can be both cached
    // (resolved in an earlier tree) and in progress here, and the in-progress
    // occurrence must still resolve via base cases, not the cached fixpoint.
    if let Some(depth) = cycle.depth_of(&frame) {
        cycle.back_edge(depth);
        return SourceShape::Recursive;
    }
    // Publication-bearing frames are shallow, hit once, and record boundaries
    // against their publication position, so they are neither looked up nor
    // stored; only publication-free frames are pure enough to memoize.
    let memo_key: Option<MemoKey> = publication
        .is_none()
        .then(|| (frame.0.clone(), frame.1.clone(), frame.2.clone(), ty));
    if let Some(key) = memo_key.as_ref()
        && let Some((shape, delta)) = memo.entries.get(key)
    {
        facts.merge(delta);
        return *shape;
    }

    let depth = cycle.push(frame);
    // Accumulate this frame's contribution into its own delta so it can be both
    // committed upward and cached. Children write here; we union into `facts`
    // once, after the frame completes.
    let mut local = TransportFactsBuilder::default();
    let projected = match source {
        TransportSource::ExecutableReturn => project_sources(
            world,
            contexts,
            &mut local,
            executable,
            context,
            ty,
            demand,
            &context.return_sources,
            publication,
            cycle,
            memo,
        ),
        TransportSource::ExecutableInput(semantic_index) => project_executable_input_source(
            world,
            contexts,
            &mut local,
            executable,
            ty,
            demand,
            semantic_index,
            publication,
            cycle,
            memo,
        ),
        TransportSource::LocalValue(value) => match context.local_sources.get(&value).cloned() {
            Some(TransportSource::CallableValue(producer)) => project_callable_value(
                world,
                contexts,
                &mut local,
                executable,
                context,
                ty,
                demand,
                &producer,
                publication,
                context.runtime_demand.value_demands.get(&value),
                context.runtime_demand.callable_flows.get(&value),
                memo,
            ),
            Some(source) => project_source(
                world,
                contexts,
                &mut local,
                executable,
                context,
                ty,
                demand,
                source,
                publication,
                cycle,
                memo,
            ),
            None => SourceShape::Unknown,
        },
        TransportSource::CallsiteReturn(callsite) => project_callsite_return(
            world,
            contexts,
            &mut local,
            executable,
            context,
            callsite,
            demand,
            publication,
            cycle,
            memo,
        ),
        TransportSource::Join(sources) => project_sources(
            world,
            contexts,
            &mut local,
            executable,
            context,
            ty,
            demand,
            &sources,
            publication,
            cycle,
            memo,
        ),
        TransportSource::TupleValue(items) => project_tuple_value(
            world,
            contexts,
            &mut local,
            executable,
            context,
            ty,
            demand,
            &items,
            publication,
            cycle,
            memo,
        ),
        TransportSource::TupleField { source, index } => project_tuple_field(
            world,
            contexts,
            &mut local,
            executable,
            context,
            demand,
            source,
            index,
            publication,
            cycle,
            memo,
        ),
        TransportSource::CallableValue(producer) => project_callable_value(
            world,
            contexts,
            &mut local,
            executable,
            context,
            ty,
            demand,
            &producer,
            publication,
            None,
            None,
            memo,
        ),
    };
    let low = cycle.pop();
    facts.merge(&local);
    // Cache only SCC roots (`low == depth`): a frame whose subtree's back-edges
    // all target itself or its own descendants. Frames inside a larger SCC have
    // `low < depth` and stay uncached, since their result is provisional until
    // the enclosing root settles.
    if let Some(key) = memo_key
        && low == depth
    {
        memo.entries.insert(key, (projected, local));
    }
    projected
}

fn project_sources(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    sources: &[TransportSource],
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    let mut exact = Vec::new();
    let mut recursive = false;
    let mut delta = TransportFactsBuilder::default();
    for source in sources {
        match project_source(
            world,
            contexts,
            &mut delta,
            executable,
            context,
            ty,
            demand,
            source.clone(),
            publication.clone(),
            cycle,
            memo,
        ) {
            SourceShape::Exact(shape) => exact.push(shape),
            SourceShape::Recursive => recursive = true,
            SourceShape::Unknown => return SourceShape::Unknown,
        }
    }
    if exact.is_empty() {
        return if recursive {
            SourceShape::Recursive
        } else {
            SourceShape::Unknown
        };
    }
    if demand.is_callable()
        && let Some(shape) = select_callable_input_shape_for_demand(world, &mut delta, &exact, &demand.callable)
    {
        facts.merge(&delta);
        return SourceShape::Exact(shape);
    }
    if exact.windows(2).all(|pair| pair[0] == pair[1]) {
        facts.merge(&delta);
        SourceShape::Exact(exact[0])
    } else {
        if demand.is_callable() {
            if let Some(publication) = publication {
                let surface_shapes = callable_surface_shapes_for_demand(world, &mut delta, &demand.callable);
                delta.record_callable_shape_surface_publications(world, publication.clone(), &exact, &surface_shapes);
                delta.record_publication_source_shapes(publication, exact);
            }
            facts.merge(&delta);
        }
        SourceShape::Unknown
    }
}

fn project_executable_input_source(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    ty: Ty,
    demand: &RuntimeDemand,
    semantic_index: usize,
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    let mut sources = Vec::new();
    collect_call_arg_input_sources(world, contexts, executable, semantic_index, &mut sources);
    collect_callable_capture_input_sources(contexts, executable, semantic_index, &mut sources);
    if sources.is_empty() {
        return SourceShape::Unknown;
    }

    let mut delta = TransportFactsBuilder::default();
    let mut exact = Vec::new();
    let mut recursive = false;
    let mut unknown = false;
    for (source_executable, value) in sources {
        let Some(source_context) = contexts.get(&source_executable) else {
            unknown = true;
            continue;
        };
        let Some(source_ty) = source_context.analysis.value_types.get(&value).copied() else {
            unknown = true;
            continue;
        };
        let projected = project_source(
            world,
            contexts,
            &mut delta,
            &source_executable,
            source_context,
            source_ty,
            demand,
            TransportSource::LocalValue(value),
            None,
            cycle,
            memo,
        );
        match projected {
            SourceShape::Exact(shape) => exact.push(shape),
            SourceShape::Recursive => recursive = true,
            SourceShape::Unknown => unknown = true,
        }
    }
    if exact.is_empty() {
        return if recursive {
            SourceShape::Recursive
        } else {
            SourceShape::Unknown
        };
    }
    if demand.is_callable()
        && let Some(shape) = select_callable_input_shape_for_demand(world, &mut delta, &exact, &demand.callable)
    {
        if let Some(publication) = publication {
            let surface_shapes = callable_surface_shapes_for_demand(world, &mut delta, &demand.callable);
            delta.record_callable_shape_surface_publications(world, publication.clone(), &[shape], &surface_shapes);
            delta.record_publication_source_shapes(publication, vec![shape]);
        }
        facts.merge(&delta);
        return SourceShape::Exact(shape);
    }
    if demand.is_callable() {
        let source_shapes = callable_input_shapes_for_demand(world, &mut delta, &exact, &demand.callable);
        if !source_shapes.is_empty() {
            if let Some(publication) = publication.clone() {
                let surface_shapes = callable_surface_shapes_for_demand(world, &mut delta, &demand.callable);
                delta.record_callable_shape_surface_publications(
                    world,
                    publication.clone(),
                    &source_shapes,
                    &surface_shapes,
                );
                delta.record_publication_source_shapes(publication, source_shapes);
            }
            facts.merge(&delta);
            if unknown {
                return SourceShape::Unknown;
            }
        }
    }
    if unknown {
        return SourceShape::Unknown;
    }
    if exact.windows(2).all(|pair| pair[0] == pair[1]) {
        if demand.is_callable()
            && let Some(publication) = publication
        {
            let surface_shapes = callable_surface_shapes_for_demand(world, &mut delta, &demand.callable);
            delta.record_callable_shape_surface_publications(world, publication.clone(), &exact, &surface_shapes);
            delta.record_publication_source_shapes(publication, exact.clone());
        }
        facts.merge(&delta);
        SourceShape::Exact(exact[0])
    } else if exact
        .iter()
        .all(|shape| matches!(world.shape(*shape), ShapeDescr::Nothing))
    {
        SourceShape::Exact(generic_shape_from_demand(
            world,
            ty,
            &RuntimeDemand::ignore(),
            facts,
            None,
        ))
    } else {
        SourceShape::Unknown
    }
}

fn select_callable_input_shape_for_demand(
    world: &mut World<'_>,
    facts: &mut TransportFactsBuilder,
    shapes: &[ShapeId],
    demand: &CallableDemand,
) -> Option<ShapeId> {
    let selected = callable_input_shapes_for_demand(world, facts, shapes, demand);
    match selected.as_slice() {
        [shape] => Some(*shape),
        _ => None,
    }
}

fn callable_input_shapes_for_demand(
    world: &mut World<'_>,
    facts: &mut TransportFactsBuilder,
    shapes: &[ShapeId],
    demand: &CallableDemand,
) -> Vec<ShapeId> {
    if demand.resolved.is_empty() {
        return Vec::new();
    }
    let surface_shapes = callable_surface_shapes_for_demand(world, facts, demand);
    let mut selected = Vec::new();
    for shape in shapes.iter().copied() {
        if callable_input_shape_satisfies_demand(world, facts, shape, &surface_shapes) {
            extend_unique(&mut selected, vec![shape]);
        }
    }
    selected
}

fn callable_surface_shapes_for_demand(
    world: &mut World<'_>,
    facts: &mut TransportFactsBuilder,
    demand: &CallableDemand,
) -> Vec<Box<[ShapeId]>> {
    demand
        .resolved
        .iter()
        .map(|surface| surface_shape(world, surface, facts))
        .collect()
}

fn callable_input_shape_satisfies_demand(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    shape: ShapeId,
    surface_shapes: &[Box<[ShapeId]>],
) -> bool {
    let ShapeDescr::Callable(callable) = world.shape(shape) else {
        return false;
    };
    let Some(callable_facts) = facts.callables.get(callable) else {
        return false;
    };
    surface_shapes.iter().all(|surface| {
        callable_facts
            .direct_edges
            .iter()
            .any(|edge| edge.surface_arg_shapes.as_ref() == surface.as_ref())
    })
}

fn collect_call_arg_input_sources(
    world: &World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executable: &ExecutableKey,
    semantic_index: usize,
    out: &mut Vec<(ExecutableKey, ValueId)>,
) {
    for (caller, context) in contexts {
        if caller == executable {
            continue;
        }
        for (callsite, args) in &context.callsite_args {
            let Some(capture_prefix) = executable.activation.input_len(world.types()).checked_sub(args.len()) else {
                continue;
            };
            if semantic_index < capture_prefix {
                continue;
            }
            let arg_index = semantic_index - capture_prefix;
            let Some(arg) = args.get(arg_index) else {
                continue;
            };
            if context
                .callsite_needs
                .get(callsite)
                .copied()
                .unwrap_or(ExecutableNeed::Value)
                != executable.need
            {
                continue;
            }
            let key = CallSiteKey {
                activation: caller.activation.clone(),
                callsite: *callsite,
            };
            let Some(summary) = world.callsite_summary(&key) else {
                continue;
            };
            if !summary.targets.iter().any(|target| {
                target.activation.as_ref().is_some_and(|activation| {
                    activation.function == executable.activation.function
                        && activation.arrow == executable.activation.arrow
                })
            }) {
                continue;
            }
            out.push((caller.clone(), arg.value));
        }
    }
}

fn collect_callable_capture_input_sources(
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executable: &ExecutableKey,
    semantic_index: usize,
    out: &mut Vec<(ExecutableKey, ValueId)>,
) {
    for (producer_executable, context) in contexts {
        for flow in context.runtime_demand.callable_flows.values() {
            if !flow.resolutions.iter().any(|resolution| resolution == executable) {
                continue;
            }
            let Some(capture) = flow.captures.get(semantic_index).copied() else {
                continue;
            };
            out.push((producer_executable.clone(), capture));
        }
    }
}

fn project_tuple_value(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    items: &[ValueId],
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    if demand.is_callable() {
        return SourceShape::Unknown;
    }
    let ShapeDemand::TupleFields(fields) = &demand.shape else {
        return SourceShape::Unknown;
    };
    if items.len() != fields.len() {
        return SourceShape::Unknown;
    }
    let field_tys = tuple_field_tys(world, ty, fields.len());
    let mut item_shapes = Vec::with_capacity(items.len());
    for (item, (item_ty, field_demand)) in items.iter().copied().zip(field_tys.into_iter().zip(fields.iter())) {
        let mut delta = TransportFactsBuilder::default();
        let shape = match project_source(
            world,
            contexts,
            &mut delta,
            executable,
            context,
            item_ty,
            field_demand,
            TransportSource::LocalValue(item),
            publication.clone(),
            cycle,
            memo,
        ) {
            SourceShape::Exact(shape) => {
                facts.merge(&delta);
                shape
            }
            SourceShape::Recursive | SourceShape::Unknown => {
                generic_shape_from_demand(world, item_ty, field_demand, facts, None)
            }
        };
        item_shapes.push(shape);
    }
    SourceShape::Exact(world.intern_shape(ShapeDescr::Tuple(item_shapes.into_boxed_slice())))
}

fn project_tuple_field(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    demand: &RuntimeDemand,
    source: ValueId,
    index: usize,
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    let Some(parent_ty) = context.analysis.value_types.get(&source).copied() else {
        return SourceShape::Unknown;
    };
    let mut fields = vec![RuntimeDemand::ignore(); index + 1];
    fields[index] = demand.clone();
    let parent_demand = RuntimeDemand::tuple_fields(fields);
    let parent_shape = match project_source(
        world,
        contexts,
        facts,
        executable,
        context,
        parent_ty,
        &parent_demand,
        TransportSource::LocalValue(source),
        publication,
        cycle,
        memo,
    ) {
        SourceShape::Exact(shape) => shape,
        other => return other,
    };
    let ShapeDescr::Tuple(items) = world.shape(parent_shape) else {
        return SourceShape::Unknown;
    };
    items
        .get(index)
        .copied()
        .map_or(SourceShape::Unknown, SourceShape::Exact)
}

fn project_callable_value(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    ty: Ty,
    demand: &RuntimeDemand,
    producer: &LocalCallableProducer,
    publication: Option<TransportPosition>,
    precise_demand: Option<&RuntimeDemand>,
    upstream_flow: Option<&CallableFlowFact>,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    if !local_callable_transport_requested(demand, precise_demand) {
        return SourceShape::Unknown;
    }
    let Some(upstream_flow) = upstream_flow else {
        panic!("local callable producer reached transport without upstream CallableFlowFact: {producer:?}");
    };
    let Some(callable) = callable_for_producer(
        world,
        contexts,
        facts,
        executable,
        context,
        producer,
        ty,
        upstream_flow,
        publication,
        memo,
    ) else {
        return SourceShape::Unknown;
    };
    SourceShape::Exact(world.intern_shape(ShapeDescr::Callable(callable)))
}

fn project_callsite_return(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    callsite: CallSiteId,
    demand: &RuntimeDemand,
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    let key = CallSiteKey {
        activation: executable.activation.clone(),
        callsite,
    };
    let Some(summary) = world.callsite_summary(&key) else {
        return SourceShape::Unknown;
    };
    let targets = summary.targets.clone();
    let need = context
        .callsite_needs
        .get(&callsite)
        .copied()
        .unwrap_or(ExecutableNeed::Value);
    let mut shapes = Vec::new();
    let mut recursive = false;
    let mut delta = TransportFactsBuilder::default();
    for target in targets {
        match target.callee {
            SelectedCallee::ProviderBoundary(_) => return SourceShape::Unknown,
            SelectedCallee::Function(_) => {
                let Some(activation) = target.activation else {
                    return SourceShape::Unknown;
                };
                let target = ExecutableKey { activation, need };
                let Some(target_context) = contexts.get(&target) else {
                    return SourceShape::Unknown;
                };
                match project_source(
                    world,
                    contexts,
                    &mut delta,
                    &target,
                    target_context,
                    target_context.return_ty,
                    demand,
                    TransportSource::ExecutableReturn,
                    publication.clone(),
                    cycle,
                    memo,
                ) {
                    SourceShape::Exact(shape) => shapes.push(shape),
                    SourceShape::Recursive => recursive = true,
                    SourceShape::Unknown => return SourceShape::Unknown,
                }
            }
        }
    }
    if shapes.is_empty() {
        return if recursive {
            SourceShape::Recursive
        } else {
            SourceShape::Unknown
        };
    }
    if shapes.windows(2).all(|pair| pair[0] == pair[1]) {
        facts.merge(&delta);
        SourceShape::Exact(shapes[0])
    } else {
        SourceShape::Unknown
    }
}

fn callable_for_producer(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    producer: &LocalCallableProducer,
    callable_ty: Ty,
    upstream_flow: &CallableFlowFact,
    publication: Option<TransportPosition>,
    memo: &mut ProjectionMemo,
) -> Option<super::super::transport::CallableId> {
    assert_eq!(
        upstream_flow.function, producer.function,
        "upstream callable-flow fact must describe the projected producer"
    );
    assert_eq!(
        upstream_flow.captures, producer.captures,
        "upstream callable-flow captures must describe the projected producer"
    );
    let capture_tys = producer
        .captures
        .iter()
        .copied()
        .map(|capture| context.analysis.value_types.get(&capture).copied())
        .collect::<Option<Vec<_>>>()?;
    let direct_surface_demands = upstream_flow.direct_surfaces.clone();
    let boundary_surface_demands = upstream_flow.first_class_surfaces.clone();
    let resolution_symbols = upstream_flow
        .resolutions
        .iter()
        .map(|e| executable_symbol(e, world.types()))
        .collect::<Vec<_>>();
    let direct_surfaces = if direct_surface_demands.is_empty() {
        Vec::new()
    } else {
        surface_shapes(world, &direct_surface_demands, facts)
    };
    let direct_edges = callable_direct_edges(world, &upstream_flow.direct_edges, facts);
    let capture_demands = capture_demands_for_resolutions(contexts, &capture_tys, &resolution_symbols, world.types());
    let capture_shapes = producer
        .captures
        .iter()
        .copied()
        .zip(capture_tys.iter().copied().zip(capture_demands.iter()))
        .map(|(capture, (capture_ty, capture_demand))| {
            Some(shape_for_local_value(
                world,
                contexts,
                facts,
                executable,
                context,
                capture,
                capture_ty,
                capture_demand,
                None,
                memo,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let capture_lanes = capture_shapes
        .iter()
        .copied()
        .zip(capture_tys.iter().copied())
        .zip(capture_demands.iter())
        .flat_map(|((shape, capture_ty), demand)| {
            capture_lanes_for_callable_descriptor(world, shape, capture_ty, demand)
        })
        .collect::<Vec<_>>();
    let callable = world.intern_callable(CallableDescr {
        function: Some(producer.function),
        capture_shapes: capture_shapes.into_boxed_slice(),
        capture_lanes: capture_lanes.clone().into_boxed_slice(),
    });
    let boundary_ids = if !boundary_surface_demands.is_empty() {
        let surface_arg_shapes = surface_shapes(world, &boundary_surface_demands, facts);
        let boundary_resolution_symbols =
            boundary_resolution_symbols_for_flow_surfaces(upstream_flow, &boundary_surface_demands, world.types());
        let boundary_return_contracts = boundary_return_contracts_for_resolution_symbols(
            world,
            contexts,
            callable_ty,
            &boundary_surface_demands,
            &boundary_resolution_symbols,
            upstream_flow.escape && upstream_flow.direct_surfaces.is_empty(),
        );
        let boundary_return_shapes = boundary_return_shapes_for_flow_surfaces(
            world,
            contexts,
            facts,
            &boundary_resolution_symbols,
            &boundary_return_contracts.return_tys,
            memo,
        );
        publish_boundaries_for_callable(
            world,
            facts,
            callable,
            &boundary_surface_demands,
            &surface_arg_shapes,
            &capture_lanes,
            callable_ty,
            &boundary_return_contracts.return_tys,
            &boundary_return_contracts.publish,
            &boundary_return_shapes,
            &boundary_resolution_symbols,
            publication,
        )
    } else {
        Vec::new()
    };
    facts.record_callable(
        callable,
        resolution_symbols,
        direct_surfaces,
        direct_edges,
        boundary_ids,
    );
    Some(callable)
}

fn local_callable_transport_requested(demand: &RuntimeDemand, precise_demand: Option<&RuntimeDemand>) -> bool {
    precise_demand.is_some_and(RuntimeDemand::is_callable) || demand.is_callable()
}

fn capture_demands_for_resolutions(
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    capture_tys: &[Ty],
    resolutions: &[ExecutableSymbol],
    types: &Types,
) -> Vec<RuntimeDemand> {
    let mut demands = vec![RuntimeDemand::ignore(); capture_tys.len()];
    for resolution in resolutions {
        let Some((_, context)) = contexts.iter().find(|(candidate, _)| {
            candidate.need == resolution.need
                && candidate.activation.function == resolution.activation.function
                && candidate.activation.inputs(types).as_slice() == resolution.activation.input.as_ref()
        }) else {
            panic!("upstream callable-flow resolution is outside the transport root context: {resolution:?}");
        };
        assert!(
            context.runtime_demand.input_demands.len() >= capture_tys.len(),
            "upstream callable-flow resolution input demand is missing capture slots: {resolution:?}"
        );
        for (slot, demand) in demands
            .iter_mut()
            .zip(context.runtime_demand.input_demands.iter().take(capture_tys.len()))
        {
            slot.join_assign(demand);
        }
    }
    demands
}

fn surface_shapes(
    world: &mut World<'_>,
    surfaces: &BTreeSet<CallableSurface>,
    facts: &mut TransportFactsBuilder,
) -> Vec<Box<[ShapeId]>> {
    let mut rendered = surfaces
        .iter()
        .map(|surface| {
            surface
                .inputs
                .iter()
                .copied()
                .map(|ty| {
                    let demand = boundary_runtime_demand(world, ty);
                    generic_shape_from_demand(world, ty, &demand, facts, None)
                })
                .collect::<Vec<_>>()
                .into_boxed_slice()
        })
        .collect::<Vec<_>>();
    rendered.sort_by_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
    rendered
}

fn callable_direct_edges(
    world: &mut World<'_>,
    edges: &[super::super::semantic::CallableFlowEdge],
    facts: &mut TransportFactsBuilder,
) -> Vec<CallableDirectEdge> {
    edges
        .iter()
        .map(|edge| CallableDirectEdge {
            surface_inputs: edge.surface.inputs.clone().into_boxed_slice(),
            surface_arg_shapes: surface_shape(world, &edge.surface, facts),
            resolution: executable_symbol(&edge.resolution, world.types()),
        })
        .collect()
}

fn surface_shape(
    world: &mut World<'_>,
    surface: &CallableSurface,
    facts: &mut TransportFactsBuilder,
) -> Box<[ShapeId]> {
    surface
        .inputs
        .iter()
        .copied()
        .map(|ty| {
            let demand = boundary_runtime_demand(world, ty);
            generic_shape_from_demand(world, ty, &demand, facts, None)
        })
        .collect::<Vec<_>>()
        .into_boxed_slice()
}

fn generic_shape_from_demand(
    world: &mut World<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return world.intern_shape(ShapeDescr::Nothing);
    }
    if demand.is_callable() {
        return generic_callable_shape(world, ty, &demand.callable, facts, publication);
    }
    match &demand.shape {
        ShapeDemand::Ignore => world.intern_shape(ShapeDescr::Nothing),
        ShapeDemand::Whole => value_lane_shape(world, ty),
        ShapeDemand::TupleFields(fields) => {
            let items = tuple_field_tys(world, ty, fields.len())
                .into_iter()
                .zip(fields.iter())
                .map(|(field_ty, field_demand)| generic_shape_from_demand(world, field_ty, field_demand, facts, None))
                .collect::<Vec<_>>();
            world.intern_shape(ShapeDescr::Tuple(items.into_boxed_slice()))
        }
    }
}

fn generic_callable_shape(
    world: &mut World<'_>,
    ty: Ty,
    demand: &CallableDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    generic_callable_shape_with_resolutions(world, ty, demand, facts, publication)
}

fn generic_callable_shape_with_resolutions(
    world: &mut World<'_>,
    ty: Ty,
    demand: &CallableDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    let surfaces = &demand.resolved;
    assert!(
        !demand.is_first_class() || !surfaces.is_empty(),
        "generic callable transport requires upstream callable surfaces for opaque or escaped demand"
    );
    let published_surface_shapes = surface_shapes(world, surfaces, facts);
    // A boxed first-class callable's VALUE shape is a pure layout fact: the value
    // is one `ValueRef` lane (the boxed pointer), full stop. Its width is a
    // single stable fact, so every carrier — function entry, closure capture,
    // continuation capture — reads the lane straight from the shape. The
    // invocation contract (the observed surfaces) is NOT part of the value's
    // identity: it projects into the published boundaries below (and the call
    // site's argument encoding), so two boxed callables of the same value-lane
    // repr share one shape regardless of surface. Folding the invocation contract
    // into the value identity instead fragments layout-identical pointers and
    // forces out-of-band lane patching at every carrier.
    let boxed_value_lane = value_lane(world, ty);
    let callable = world.intern_callable(CallableDescr {
        function: None,
        capture_shapes: Box::default(),
        capture_lanes: Box::from([boxed_value_lane]),
    });
    let boundary_ids = if !surfaces.is_empty() {
        let return_tys = boundary_return_tys_for_callable_surfaces(world, ty, surfaces);
        let return_shapes = publication
            .as_ref()
            .and_then(|position| {
                boundary_return_shapes_for_publication_sources(world, facts, position, &published_surface_shapes)
            })
            .unwrap_or_else(|| boundary_return_shapes_for_tys(world, &return_tys, facts));
        let resolution_symbols = publication
            .as_ref()
            .map(|position| {
                facts
                    .publication_source_shapes
                    .get(position)
                    .map(|shapes| {
                        resolution_symbols_for_callable_source_surfaces(
                            world,
                            facts,
                            shapes,
                            &published_surface_shapes,
                            &return_shapes,
                        )
                    })
                    .or_else(|| {
                        facts
                            .publication_source_positions
                            .get(position)
                            .map(|source_positions| {
                                resolution_symbols_for_source_publication_surfaces(
                                    world,
                                    facts,
                                    source_positions,
                                    &published_surface_shapes,
                                    &return_shapes,
                                )
                            })
                    })
                    .unwrap_or_else(|| {
                        resolution_symbols_for_published_surfaces(
                            world,
                            facts,
                            position,
                            &published_surface_shapes,
                            &return_shapes,
                        )
                    })
            })
            .unwrap_or_else(|| vec![Vec::new(); surfaces.len()]);
        publish_boundaries_for_callable(
            world,
            facts,
            callable,
            surfaces,
            &published_surface_shapes,
            &[],
            ty,
            &return_tys,
            &vec![true; return_tys.len()],
            &return_shapes,
            &resolution_symbols,
            publication,
        )
    } else {
        Vec::new()
    };
    facts.record_callable(callable, Vec::new(), Vec::new(), Vec::new(), boundary_ids);
    world.intern_shape(ShapeDescr::Callable(callable))
}

fn resolution_symbols_for_callable_source_surfaces(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_shapes: &[ShapeId],
    surface_shapes: &[Box<[ShapeId]>],
    return_shapes: &[ShapeId],
) -> Vec<Vec<ExecutableSymbol>> {
    assert_eq!(
        surface_shapes.len(),
        return_shapes.len(),
        "callable source surface and return-shape contracts should have the same length"
    );
    surface_shapes
        .iter()
        .zip(return_shapes.iter().copied())
        .map(|(arg_shapes, return_shape)| {
            resolution_symbols_for_callable_source_surface(world, facts, source_shapes, arg_shapes, return_shape)
        })
        .collect()
}

fn resolution_symbols_for_callable_source_surface(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_shapes: &[ShapeId],
    arg_shapes: &[ShapeId],
    return_shape: ShapeId,
) -> Vec<ExecutableSymbol> {
    let mut resolutions = Vec::new();
    for shape in source_shapes {
        let ShapeDescr::Callable(callable) = world.shape(*shape) else {
            continue;
        };
        let Some(callable_facts) = facts.callables.get(callable) else {
            continue;
        };
        for edge in &callable_facts.direct_edges {
            if edge.surface_arg_shapes.as_ref() == arg_shapes {
                extend_unique(&mut resolutions, vec![edge.resolution.clone()]);
            }
        }
        for boundary in callable_facts.boundary_ids.iter().copied() {
            let boundary_descr = world.boundary(boundary);
            if boundary_descr.surface_arg_shapes.as_ref() != arg_shapes
                || boundary_descr.published_return_shape != return_shape
            {
                continue;
            }
            if let Some(boundary_facts) = facts.boundaries.get(&boundary) {
                extend_unique(&mut resolutions, boundary_facts.resolutions.clone());
            }
        }
    }
    resolutions
}

fn resolution_symbols_for_source_publication_surfaces(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_positions: &[TransportPosition],
    surface_shapes: &[Box<[ShapeId]>],
    return_shapes: &[ShapeId],
) -> Vec<Vec<ExecutableSymbol>> {
    assert_eq!(
        surface_shapes.len(),
        return_shapes.len(),
        "callable source surface and return-shape contracts should have the same length"
    );
    surface_shapes
        .iter()
        .zip(return_shapes.iter().copied())
        .map(|(arg_shapes, return_shape)| {
            resolution_symbols_for_source_publications(world, facts, source_positions, arg_shapes, return_shape)
        })
        .collect()
}

fn resolution_symbols_for_source_publications(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_positions: &[TransportPosition],
    arg_shapes: &[ShapeId],
    return_shape: ShapeId,
) -> Vec<ExecutableSymbol> {
    let mut resolutions = Vec::new();
    for source in source_positions {
        for (boundary, draft) in &facts.boundaries {
            if !draft.publications.contains(source) {
                continue;
            }
            let boundary_descr = world.boundary(*boundary);
            if boundary_descr.surface_arg_shapes.as_ref() != arg_shapes {
                continue;
            }
            // The published return shape is normally an exact part of the
            // surface contract. The one exception is a widened recursive
            // activation: it publishes the same callable with a boxed `any`
            // return where a concrete activation publishes a grounded return.
            // The boxing seam reconciles those at runtime, so a boxed value-lane
            // return on the boundary we are resolving accepts a producer that
            // returns any concrete shape. Concrete (raw / tuple) returns stay
            // strict, so genuinely distinct surfaces are not cross-resolved.
            if boundary_descr.published_return_shape != return_shape && !boxed_value_return(world, return_shape) {
                continue;
            }
            extend_unique(&mut resolutions, draft.resolutions.clone());
        }
    }
    resolutions
}

fn boundary_return_shapes_for_publication_sources(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    publication: &TransportPosition,
    surface_shapes: &[Box<[ShapeId]>],
) -> Option<Vec<ShapeId>> {
    surface_shapes
        .iter()
        .map(|arg_shapes| {
            let mut return_shapes = Vec::new();
            if let Some(source_shapes) = facts.publication_source_shapes.get(publication) {
                extend_unique(
                    &mut return_shapes,
                    boundary_return_shapes_for_callable_source_surface(world, facts, source_shapes, arg_shapes),
                );
            }
            if let Some(source_positions) = facts.publication_source_positions.get(publication) {
                extend_unique(
                    &mut return_shapes,
                    boundary_return_shapes_for_source_publications(world, facts, source_positions, arg_shapes),
                );
            }
            select_compatible_boundary_return_shape(world, &return_shapes)
        })
        .collect()
}

fn select_compatible_boundary_return_shape(world: &World<'_>, return_shapes: &[ShapeId]) -> Option<ShapeId> {
    let [first, rest @ ..] = return_shapes else {
        return None;
    };
    let first_reprs = shape_codegen_reprs(world, *first);
    rest.iter()
        .all(|shape| shape_codegen_reprs(world, *shape) == first_reprs)
        .then_some(*first)
}

fn shape_codegen_reprs(world: &World<'_>, shape: ShapeId) -> Vec<CodegenLaneRepr> {
    lanes_for_codegen_seam_shape(world, shape)
        .into_iter()
        .map(|(_, lane)| codegen_repr_for_lane(world, lane))
        .collect()
}

fn boundary_return_shapes_for_callable_source_surface(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_shapes: &[ShapeId],
    arg_shapes: &[ShapeId],
) -> Vec<ShapeId> {
    let mut return_shapes = Vec::new();
    for shape in source_shapes {
        let ShapeDescr::Callable(callable) = world.shape(*shape) else {
            continue;
        };
        let Some(callable_facts) = facts.callables.get(callable) else {
            continue;
        };
        for boundary in callable_facts.boundary_ids.iter().copied() {
            let boundary_descr = world.boundary(boundary);
            if boundary_descr.surface_arg_shapes.as_ref() == arg_shapes
                && !return_shapes.contains(&boundary_descr.published_return_shape)
            {
                return_shapes.push(boundary_descr.published_return_shape);
            }
        }
    }
    return_shapes
}

fn boundary_return_shapes_for_source_publications(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_positions: &[TransportPosition],
    arg_shapes: &[ShapeId],
) -> Vec<ShapeId> {
    let mut return_shapes = Vec::new();
    for source in source_positions {
        for (boundary, draft) in &facts.boundaries {
            if !draft.publications.contains(source) {
                continue;
            }
            let boundary_descr = world.boundary(*boundary);
            if boundary_descr.surface_arg_shapes.as_ref() == arg_shapes
                && !return_shapes.contains(&boundary_descr.published_return_shape)
            {
                return_shapes.push(boundary_descr.published_return_shape);
            }
        }
    }
    return_shapes
}

fn resolution_symbols_for_published_surfaces(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    publication: &TransportPosition,
    surface_shapes: &[Box<[ShapeId]>],
    return_shapes: &[ShapeId],
) -> Vec<Vec<ExecutableSymbol>> {
    surface_shapes
        .iter()
        .zip(return_shapes.iter().copied())
        .map(|(arg_shapes, return_shape)| {
            let mut resolutions = Vec::new();
            for (boundary, draft) in &facts.boundaries {
                if !draft.publications.contains(publication) {
                    continue;
                }
                let boundary_descr = world.boundary(*boundary);
                if boundary_descr.surface_arg_shapes.as_ref() == arg_shapes.as_ref()
                    && boundary_descr.published_return_shape == return_shape
                {
                    extend_unique(&mut resolutions, draft.resolutions.clone());
                }
            }
            resolutions
        })
        .collect()
}

fn publish_boundaries_for_callable(
    world: &mut World<'_>,
    facts: &mut TransportFactsBuilder,
    callable: CallableId,
    surfaces: &BTreeSet<CallableSurface>,
    surface_shapes: &[Box<[ShapeId]>],
    capture_lanes: &[LaneId],
    published_value_ty: Ty,
    return_tys: &[Ty],
    publish_boundary: &[bool],
    return_shapes: &[ShapeId],
    resolution_symbols: &[Vec<ExecutableSymbol>],
    publication: Option<TransportPosition>,
) -> Vec<BoundaryId> {
    assert_eq!(
        surfaces.len(),
        surface_shapes.len(),
        "boundary surface shapes must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        return_tys.len(),
        "boundary return types must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        publish_boundary.len(),
        "boundary publish flags must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        return_shapes.len(),
        "boundary return shapes must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        resolution_symbols.len(),
        "boundary resolution symbols must align with published surfaces"
    );
    let mut boundary_ids = Vec::new();
    for (((((surface, arg_shapes), return_ty), publish), return_shape), resolutions) in surfaces
        .iter()
        .zip(surface_shapes.iter())
        .zip(return_tys.iter().copied())
        .zip(publish_boundary.iter().copied())
        .zip(return_shapes.iter().copied())
        .zip(resolution_symbols.iter())
    {
        if !publish {
            continue;
        }
        let return_lanes = boundary_lanes_for_shape(world, return_shape, return_ty).into_boxed_slice();
        let published_value_lane = value_lane(world, published_value_ty);
        let arg_lanes = arg_shapes
            .iter()
            .copied()
            .zip(surface.inputs.iter().copied())
            .flat_map(|(shape, ty)| boundary_lanes_for_shape(world, shape, ty))
            .collect::<Vec<_>>();
        let boundary = world.intern_boundary(BoundaryDescr {
            callable,
            surface_arg_shapes: arg_shapes.clone(),
            published_value_lane,
            published_capture_lanes: capture_lanes.to_vec().into_boxed_slice(),
            published_arg_lanes: arg_lanes.into_boxed_slice(),
            published_return_shape: return_shape,
            published_return_lanes: return_lanes,
        });
        if let Some(position) = publication.clone() {
            facts.record_boundary(boundary, position);
        }
        facts.record_boundary_resolutions(boundary, resolutions.clone());
        boundary_ids.push(boundary);
    }
    boundary_ids
}

fn capture_lanes_for_callable_descriptor(
    world: &mut World<'_>,
    shape: ShapeId,
    ty: Ty,
    demand: &RuntimeDemand,
) -> Vec<LaneId> {
    if demand.callable.is_first_class() {
        return vec![value_lane(world, ty)];
    }
    lanes_for_codegen_seam_shape(world, shape)
        .into_iter()
        .map(|(_, lane)| lane)
        .collect()
}

fn boundary_return_shape_for_ty(world: &mut World<'_>, ret_ty: Ty, facts: &mut TransportFactsBuilder) -> ShapeId {
    if world.types().is_empty(&ret_ty) {
        return world.intern_shape(ShapeDescr::Nothing);
    }
    if let Some(fields) = exact_tuple_field_tys(world, ret_ty) {
        let field_shapes = fields
            .into_iter()
            .map(|field_ty| {
                let demand = boundary_runtime_demand(world, field_ty);
                generic_shape_from_demand(world, field_ty, &demand, facts, None)
            })
            .collect::<Vec<_>>();
        return world.intern_shape(ShapeDescr::Tuple(field_shapes.into_boxed_slice()));
    }
    let demand = boundary_runtime_demand(world, ret_ty);
    generic_shape_from_demand(world, ret_ty, &demand, facts, None)
}

fn boundary_return_shapes_for_flow_surfaces(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    resolution_symbols: &[Vec<ExecutableSymbol>],
    return_tys: &[Ty],
    memo: &mut ProjectionMemo,
) -> Vec<ShapeId> {
    assert_eq!(
        resolution_symbols.len(),
        return_tys.len(),
        "boundary return shapes must align resolution symbols with return types"
    );
    resolution_symbols
        .iter()
        .zip(return_tys.iter().copied())
        .map(|(resolutions, return_ty)| {
            let resolution = resolutions
                .first()
                .unwrap_or_else(|| panic!("upstream callable-flow surface has no executable resolution"));
            boundary_return_shape_for_resolution(world, contexts, facts, resolution, return_ty, memo)
        })
        .collect()
}

struct BoundaryReturnContracts {
    return_tys: Vec<Ty>,
    publish: Vec<bool>,
}

fn boundary_return_contracts_for_resolution_symbols(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    callable_ty: Ty,
    surfaces: &BTreeSet<CallableSurface>,
    resolution_symbols: &[Vec<ExecutableSymbol>],
    publish_empty_resolved_returns: bool,
) -> BoundaryReturnContracts {
    assert_eq!(
        surfaces.len(),
        resolution_symbols.len(),
        "boundary return types must align surfaces with resolution symbols"
    );
    let mut return_tys = Vec::with_capacity(surfaces.len());
    let mut publish = Vec::with_capacity(surfaces.len());
    for (surface, resolutions) in surfaces.iter().zip(resolution_symbols.iter()) {
        let mut resolved = None;
        for resolution in resolutions {
            let Some((_, context)) = contexts.iter().find(|(candidate, _)| {
                candidate.need == resolution.need
                    && candidate.activation.function == resolution.activation.function
                    && candidate.activation.inputs(world.types()).as_slice() == resolution.activation.input.as_ref()
            }) else {
                continue;
            };
            resolved = Some(match resolved {
                Some(current) => world.types_mut().union(current, context.return_ty),
                None => context.return_ty,
            });
        }
        let surface_return_ty = boundary_return_ty_for_surface(world, callable_ty, surface);
        let resolved_empty = resolved.is_some_and(|return_ty| world.types().is_empty(&return_ty));
        let return_ty = match resolved {
            Some(_) if resolved_empty && !world.types().is_empty(&surface_return_ty) => surface_return_ty,
            Some(return_ty) => return_ty,
            None => surface_return_ty,
        };
        return_tys.push(return_ty);
        publish.push(!resolved_empty || publish_empty_resolved_returns);
    }
    BoundaryReturnContracts { return_tys, publish }
}

fn boundary_resolution_symbols_for_flow_surfaces(
    flow: &CallableFlowFact,
    surfaces: &BTreeSet<CallableSurface>,
    types: &Types,
) -> Vec<Vec<ExecutableSymbol>> {
    surfaces
        .iter()
        .map(|surface| {
            flow.first_class_edges
                .iter()
                .filter(|edge| &edge.surface == surface)
                .map(|edge| executable_symbol(&edge.resolution, types))
                .collect::<Vec<_>>()
        })
        .collect()
}

fn boundary_return_shape_for_resolution(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    resolution: &ExecutableSymbol,
    fallback_return_ty: Ty,
    memo: &mut ProjectionMemo,
) -> ShapeId {
    let Some((executable, context)) = contexts.iter().find(|(candidate, _)| {
        candidate.need == resolution.need
            && candidate.activation.function == resolution.activation.function
            && candidate.activation.inputs(world.types()).as_slice() == resolution.activation.input.as_ref()
    }) else {
        panic!("upstream callable-flow resolution is outside the transport root context: {resolution:?}");
    };
    let demand = context.runtime_demand.return_demand.clone();
    let return_ty = if world.types().is_empty(&context.return_ty) {
        fallback_return_ty
    } else {
        context.return_ty
    };
    let shape = shape_for_source(
        world,
        contexts,
        facts,
        executable,
        context,
        return_ty,
        &demand,
        TransportSource::ExecutableReturn,
        None,
        memo,
    );
    if !demand.is_ignore() && matches!(world.shape(shape), ShapeDescr::Nothing) {
        generic_shape_from_demand(world, return_ty, &demand, facts, None)
    } else {
        shape
    }
}

fn boundary_return_tys_for_callable_surfaces(
    world: &mut World<'_>,
    callable_ty: Ty,
    surfaces: &BTreeSet<CallableSurface>,
) -> Vec<Ty> {
    surfaces
        .iter()
        .map(|surface| boundary_return_ty_for_surface(world, callable_ty, surface))
        .collect()
}

fn boundary_return_shapes_for_tys(
    world: &mut World<'_>,
    return_tys: &[Ty],
    facts: &mut TransportFactsBuilder,
) -> Vec<ShapeId> {
    return_tys
        .iter()
        .copied()
        .map(|ret_ty| boundary_return_shape_for_ty(world, ret_ty, facts))
        .collect()
}

fn boundary_return_ty_for_surface(world: &mut World<'_>, callable_ty: Ty, surface: &CallableSurface) -> Ty {
    let Some(clauses) = world.types_mut().callable_value_clauses(&callable_ty) else {
        return world.types_mut().arrow_join_return(&callable_ty);
    };
    let mut matched = None;
    for clause in clauses {
        if clause.args.len() != surface.inputs.len() {
            continue;
        }
        let overlaps =
            clause
                .args
                .iter()
                .copied()
                .zip(surface.inputs.iter().copied())
                .all(|(clause_arg, surface_arg)| {
                    let overlap = world.types_mut().intersect(clause_arg, surface_arg);
                    !world.types().is_empty(&overlap)
                });
        if !overlaps {
            continue;
        }
        matched = Some(match matched {
            Some(current) => world.types_mut().union(current, clause.ret),
            None => clause.ret,
        });
    }
    matched.unwrap_or_else(|| world.types_mut().arrow_join_return(&callable_ty))
}

fn boundary_lanes_for_shape(world: &mut World<'_>, shape: ShapeId, ty: Ty) -> Vec<LaneId> {
    match world.shape(shape).clone() {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![lane],
        ShapeDescr::Tuple(items) => {
            let field_tys = tuple_field_tys(world, ty, items.len());
            items
                .iter()
                .copied()
                .zip(field_tys)
                .flat_map(|(item, field_ty)| boundary_lanes_for_shape(world, item, field_ty))
                .collect()
        }
        ShapeDescr::Callable(_) => {
            vec![value_lane(world, ty)]
        }
    }
}

fn exact_tuple_field_tys(world: &mut World<'_>, ty: Ty) -> Option<Vec<Ty>> {
    let predicate = world.types().runtime_type_predicate(&ty);
    if predicate.tuple_arities.cofinite || predicate.tuple_arities.values.len() != 1 {
        return None;
    }
    let arity = *predicate.tuple_arities.values.iter().next()?;
    Some(tuple_field_tys(world, ty, arity))
}

fn value_lane_shape(world: &mut World<'_>, ty: Ty) -> ShapeId {
    let lane = value_lane(world, ty);
    world.intern_shape(ShapeDescr::Lane(lane))
}

fn value_lane(world: &mut World<'_>, ty: Ty) -> LaneId {
    let ty = world.types_mut().value_lane_repr(ty);
    world.intern_lane(super::super::transport::LaneDescr {
        ty,
        class: TransportClass::Value,
    })
}

fn tuple_field_tys(world: &mut World<'_>, ty: Ty, arity: usize) -> Vec<Ty> {
    let any = world.types_mut().any();
    let mut fields = world.types_mut().tuple_projections(&ty, arity);
    if fields.len() < arity {
        fields.resize(arity, any);
    } else if fields.len() > arity {
        fields.truncate(arity);
    }
    fields
}

fn boundary_runtime_demand(world: &mut World<'_>, ty: Ty) -> RuntimeDemand {
    let Some(clauses) = world.types_mut().callable_clauses(&ty) else {
        if let Some(fields) = exact_tuple_field_tys(world, ty) {
            return RuntimeDemand::tuple_fields(
                fields
                    .into_iter()
                    .map(|field_ty| boundary_runtime_demand(world, field_ty))
                    .collect(),
            );
        }
        return RuntimeDemand::whole();
    };
    RuntimeDemand::callable(CallableDemand {
        resolved: clauses
            .into_iter()
            .map(|clause| CallableSurface::new(clause.args, world.types_mut()))
            .collect::<BTreeSet<_>>(),
        opaque: false,
        escape: true,
    })
}

fn resume_demand(context: &ExecutableContext, resume: ResumeEntry) -> RuntimeDemand {
    context
        .runtime_demand
        .value_demands
        .get(&resume.value)
        .cloned()
        .unwrap_or_default()
}

fn resume_shape(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    resume: ResumeEntry,
    demand: &RuntimeDemand,
    publication: Option<TransportPosition>,
    memo: &mut ProjectionMemo,
) -> ShapeId {
    let value_ty = context
        .analysis
        .value_types
        .get(&resume.value)
        .copied()
        .unwrap_or_else(|| world.types_mut().any());
    shape_for_source(
        world,
        contexts,
        facts,
        executable,
        context,
        value_ty,
        demand,
        resume
            .callsite
            .map(TransportSource::CallsiteReturn)
            .unwrap_or(TransportSource::LocalValue(resume.value)),
        publication,
        memo,
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::telemetry::ConfiguredTelemetry;

    fn intern_test_shape(world: &mut World<'_>) -> ShapeId {
        let ty = world.types_mut().any();
        value_lane_shape(world, ty)
    }

    fn lane_for_shape(world: &World<'_>, shape: ShapeId) -> LaneId {
        let ShapeDescr::Lane(lane) = world.shape(shape) else {
            panic!("test shape should be one lane")
        };
        *lane
    }

    fn test_positions(world: &mut World<'_>) -> (TransportPosition, TransportPosition) {
        world.submit_code(None, "fn main(x), do: x".to_string());
        let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
        let ty = world.types_mut().any();
        let function = world.root_entry(root).function;
        let executable = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                input: vec![ty].into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        };
        (
            TransportPosition::Value {
                executable: executable.clone(),
                value: ValueId::from_u32(1),
            },
            TransportPosition::Value {
                executable,
                value: ValueId::from_u32(2),
            },
        )
    }

    #[test]
    fn shape_constraint_graph_solves_independent_of_insertion_order() {
        let tel = ConfiguredTelemetry::new();
        let mut left_world = World::new(&tel);
        let (left_a, left_b) = test_positions(&mut left_world);
        let left_shape = intern_test_shape(&mut left_world);
        let mut left = ShapeConstraintGraph::default();
        left.anchor(left_a.clone(), left_shape);
        left.equal(left_a.clone(), left_b.clone());
        let left_solved = left.solve();

        let tel = ConfiguredTelemetry::new();
        let mut right_world = World::new(&tel);
        let (right_a, right_b) = test_positions(&mut right_world);
        let right_shape = intern_test_shape(&mut right_world);
        let mut right = ShapeConstraintGraph::default();
        right.equal(right_b.clone(), right_a.clone());
        right.anchor(right_b.clone(), right_shape);
        let right_solved = right.solve();

        assert_eq!(left_solved.get(&left_a), Some(&left_shape));
        assert_eq!(left_solved.get(&left_b), Some(&left_shape));
        assert_eq!(right_solved.get(&right_a), Some(&right_shape));
        assert_eq!(right_solved.get(&right_b), Some(&right_shape));
    }

    #[test]
    #[should_panic(expected = "transport shape anchors disagree")]
    fn shape_constraint_graph_rejects_conflicting_anchors() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let (a, b) = test_positions(&mut world);
        let left_shape = world.intern_shape(ShapeDescr::Nothing);
        let right_shape = intern_test_shape(&mut world);
        assert_ne!(left_shape, right_shape);

        let mut graph = ShapeConstraintGraph::default();
        graph.anchor(a.clone(), left_shape);
        graph.equal(a, b.clone());
        graph.anchor(b, right_shape);
        let _ = graph.solve();
    }

    #[test]
    fn codegen_seam_sort_key_distinguishes_executable_symbol_identity() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        world.submit_code(None, "fn main(x), do: x".to_string());
        let root = world.submit_root(None, "main".to_string(), 1, ExecutableNeed::Value);
        let function = world.root_entry(root).function;
        let int = world.types_mut().int();
        let any = world.types_mut().any();
        let shape = value_lane_shape(&mut world, int);
        let lane = lane_for_shape(&world, shape);

        let value_symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                input: vec![int].into_boxed_slice(),
            },
            need: ExecutableNeed::Value,
        };
        let tuple_symbol = ExecutableSymbol {
            activation: ActivationSymbol {
                function,
                input: vec![any].into_boxed_slice(),
            },
            need: ExecutableNeed::TupleFields(1),
        };
        let value_fact = CodegenSeamFact {
            seam: CodegenSeam::ReturnDelivery {
                executable: value_symbol,
            },
            shape: Some(shape),
            lane,
            repr: CodegenLaneRepr::ValueRef,
        };
        let tuple_fact = CodegenSeamFact {
            seam: CodegenSeam::ReturnDelivery {
                executable: tuple_symbol,
            },
            shape: Some(shape),
            lane,
            repr: CodegenLaneRepr::ValueRef,
        };

        assert_ne!(
            codegen_seam_fact_sort_key(&value_fact),
            codegen_seam_fact_sort_key(&tuple_fact),
            "codegen seam fact ordering must be stable for multiple activations/needs of the same function"
        );
    }
}
