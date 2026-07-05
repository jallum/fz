use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::super::artifact::MaterializedExecutable;
use super::super::body::{
    CallArg, CallInputMode, CallSiteId, ControlDestination, ControlEntryId, DeliveredValueSource, LoweredBody,
    LoweredStep, LoweredTail, ValueId, body_consumed_values, callsite_call_args, callsite_call_dests,
    callsite_input_modes, delivered_value_joins,
};
use super::super::drive::FactKey;
use super::super::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::pull::{
    IncomingInputSource, InputSlot, ProductKey, ProductValue, PullOutcome, PullSession, PullWait,
    SolvedTransportClosure, SolvedTransportComponent, TransportComponentInventory, TransportShapeFact,
};
use super::super::semantic::{
    ActivationAnalysis, CallSiteKey, CallableDemand, CallableFlowFact, CallableSurface, ExecutableRuntimeDemand,
    RuntimeDemand, SelectedCallee, ShapeDemand,
};
use super::super::transport::{
    ActivationSymbol, BoundaryDescr, BoundaryFacts, BoundaryId, CallableDescr, CallableDirectEdge, CallableFacts,
    CallableId, CodegenLaneRepr, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportClass, TransportPosition,
};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::semantic::executable_callsite_needs;
use crate::telemetry::opaque_debug;
use crate::{measurements, metadata};

#[derive(Debug, Clone)]
struct ExecutableContext {
    analysis: ActivationAnalysis,
    return_ty: Ty,
    body: LoweredBody,
    original_entry_ids: Vec<ControlEntryId>,
    runtime_demand: ExecutableRuntimeDemand,
    callsite_needs: HashMap<CallSiteId, ExecutableNeed>,
    callsite_args: HashMap<CallSiteId, Vec<CallArg>>,
    callsite_modes: HashMap<CallSiteId, CallInputMode>,
    local_sources: HashMap<ValueId, TransportSource>,
    callsite_dests: HashMap<CallSiteId, ControlDestination>,
    return_sources: Vec<TransportSource>,
    resume_entries: Vec<ResumeEntry>,
}

/// Key into the forward incoming-input-source index: a callee executable and
/// the semantic input position fed.
type IncomingInputKey = (ExecutableKey, usize);

/// The per-root context set plus the forward index of incoming input sources it
/// induces. The index is the push inverse of the former backward whole-closure
/// scans (`collect_call_arg_input_sources`/`collect_callable_capture_input_sources`):
/// rather than an executable scanning every other executable to discover who
/// feeds its inputs, each producer's outgoing call-arg and callable-capture
/// edges are pushed once into the fed callee's slot when the contexts are
/// assembled. `project_executable_input_source` reads its callee's slot instead
/// of scanning. Deref exposes the underlying context map unchanged, so callee
/// lookups (`get`, `iter`, ...) read through.
#[derive(Debug, Default)]
struct TransportContexts {
    by_executable: HashMap<ExecutableKey, ExecutableContext>,
    incoming_input_sources: HashMap<IncomingInputKey, Vec<(ExecutableKey, ValueId)>>,
    /// When `Some`, every projection lookup that dereferences a neighbor's
    /// context records that neighbor's key here. `derive_executable_transport`
    /// runs a throwaway recording projection against the full-closure context
    /// set, then narrows the contexts/reads to exactly the recorded keys -- so
    /// the per-executable transport job subscribes to ONLY the facts its
    /// projection actually reads, never the blanket closure. `None` (the
    /// fan-in/shadow path) makes every accessor a plain lookup.
    accessed: RefCell<Option<HashSet<ExecutableKey>>>,
}

impl std::ops::Deref for TransportContexts {
    type Target = HashMap<ExecutableKey, ExecutableContext>;

    fn deref(&self) -> &Self::Target {
        &self.by_executable
    }
}

impl TransportContexts {
    /// Record `key` as accessed when recording is enabled. A no-op otherwise.
    fn record_access(&self, key: &ExecutableKey) {
        if let Some(accessed) = self.accessed.borrow_mut().as_mut() {
            accessed.insert(key.clone());
        }
    }

    /// A neighbor's context, recording it as accessed. Projection dereferences
    /// neighbors only through this, so the recorded set is exactly the cone.
    fn context_for(&self, key: &ExecutableKey) -> Option<&ExecutableContext> {
        self.record_access(key);
        self.by_executable.get(key)
    }

    /// Whether a neighbor's context is present, recording it as accessed.
    fn contains_context(&self, key: &ExecutableKey) -> bool {
        self.record_access(key);
        self.by_executable.contains_key(key)
    }

    /// The first context whose executable matches `symbol`'s dispatch identity,
    /// recording the matched key as accessed.
    fn context_for_symbol(
        &self,
        symbol: &ExecutableSymbol,
        types: &Types,
    ) -> Option<(&ExecutableKey, &ExecutableContext)> {
        let found = self.by_executable.iter().find(|(candidate, _)| {
            candidate.need == symbol.need
                && candidate.activation.function == symbol.activation.function
                && candidate.activation.inputs(types).as_slice() == symbol.activation.input.as_ref()
        });
        if let Some((key, _)) = found {
            self.record_access(key);
        }
        found
    }

    /// The values feeding `callee`'s `semantic_index` input as `(producer,
    /// value)` pairs, in a deterministic order (producer sort key, then value).
    /// Records each producer as accessed: projection projects each through its
    /// own context, so the producers belong to the cone.
    fn incoming_inputs(&self, callee: &ExecutableKey, semantic_index: usize) -> &[(ExecutableKey, ValueId)] {
        let sources = self
            .incoming_input_sources
            .get(&(callee.clone(), semantic_index))
            .map_or(&[][..], Vec::as_slice);
        for (producer, _) in sources {
            self.record_access(producer);
        }
        sources
    }
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

    /// Build the position union-find from the anchors and equality edges. The
    /// shape solve and the equivalence grouping are both views over this one
    /// structure, so callers that need both build it once.
    fn build_union(&self) -> PositionUnion {
        let mut union = PositionUnion::default();
        for (position, _) in &self.anchors {
            union.add(position.clone());
        }
        for (left, right, _) in &self.equalities {
            union.union(left.clone(), right.clone());
        }
        union
    }

    /// Each component root's shape, asserting that every anchor in a component
    /// agrees -- the flat agree-or-panic meet.
    fn component_shapes(&self, union: &PositionUnion) -> HashMap<usize, ShapeId> {
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
        component_shapes
    }

    #[cfg(test)]
    fn positions_for(
        union: &PositionUnion,
        component_shapes: &HashMap<usize, ShapeId>,
    ) -> HashMap<TransportPosition, ShapeId> {
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

    fn equivalents_for(union: &PositionUnion) -> HashMap<TransportPosition, Vec<TransportPosition>> {
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

    #[cfg(test)]
    fn solve(&self) -> HashMap<TransportPosition, ShapeId> {
        let union = self.build_union();
        let component_shapes = self.component_shapes(&union);
        Self::positions_for(&union, &component_shapes)
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
            // The boundary we are filling resolutions for is anchored to a
            // specific callable identity (`BoundaryDescr::callable`), which for a
            // first-class closure carries the captured-value shapes that
            // distinguish, say, a reducer that closed over `gt2` from one that
            // closed over `even`. Source boundaries are matched by *layout*
            // (`surface_arg_shapes` + `published_return_shape`) so two distinct
            // captures of the same lambda surface look identical here. Anchoring
            // the collection to the target callable keeps a concrete boundary
            // from absorbing a sibling capture's resolutions; a generic
            // (`function: None`) dispatch boundary still pools every concrete
            // producer that flows through it.
            let target_callable = boundary_descr.callable;
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
                            target_callable,
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
                            target_callable,
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
                draft.resolutions.sort_by_cached_key(executable_symbol_sort_key);
                draft
                    .direct_surfaces
                    .sort_by_cached_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
                draft.direct_edges.sort_by_cached_key(callable_direct_edge_sort_key);
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
                draft.resolutions.sort_by_cached_key(executable_symbol_sort_key);
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

pub(crate) fn produce_transport_shape_product(
    world: &mut World<'_>,
    session: &mut PullSession,
    position: &TransportPosition,
) -> PullOutcome {
    let executable = executable_key_for_transport_position(session.root(), position, world.types_mut());
    displace_covering_solve_if_stale(world, session, &executable);
    if let Some(fact) = session.transport_shape_fact(position) {
        return PullOutcome::Produced(ProductValue::TransportShape(fact.clone()));
    }
    if session.transport_component(position).is_none() {
        return PullOutcome::Waiting(vec![PullWait::Product(ProductKey::TransportComponent(
            position.clone(),
        ))]);
    }
    let closure = session.transport_closure_id_covering(&executable).unwrap_or_else(|| {
        panic!(
            "transport shape queried for {position:?} owned by {executable:?} with a materialized \
             component but no covering closure -- produce_transport_component_product must establish \
             the cover before materialize_transport_component runs"
        )
    });
    session.record_absent_transport_shape_for(&executable, position.clone(), closure);
    PullOutcome::Produced(ProductValue::TransportShape(TransportShapeFact::AbsentForClosure(
        closure,
    )))
}

fn emit_transport_component_produced(world: &World<'_>, component: &TransportComponentInventory) {
    world.tel().execute(
        &["fz", "compiler2", "pull", "transport_component", "produced"],
        &measurements! {
            component_size: component.positions.len() as u64,
        },
        &metadata! {
            representative: opaque_debug(&component.representative),
        },
    );
}

/// Fires exactly when an executable's transport component is freshly
/// materialized from a covering solve -- i.e. this pull was NOT served from
/// the session's `transport_components` product cache (the early-return
/// branch in `produce_transport_component_product` above never reaches this
/// point). This is the product-path replacement for the legacy
/// `executable_transport.derived` signal: "this executable's transport was
/// (re)projected on this drive," observable without forcing any extra
/// recomputation -- it rides the materialize path that already runs.
fn emit_transport_component_materialized(
    world: &World<'_>,
    executable: &ExecutableKey,
    component: &TransportComponentInventory,
) {
    world.tel().execute(
        &["fz", "compiler2", "executable_transport", "projected"],
        &measurements! {
            component_size: component.positions.len() as u64,
        },
        &metadata! {
            executable: opaque_debug(executable),
        },
    );
}

fn emit_transport_closure_solved(world: &World<'_>, closure: &SolvedTransportClosure) {
    world.tel().execute(
        &["fz", "compiler2", "pull", "transport_component", "closure_solved"],
        &measurements! {
            executables: closure.executables.len(),
            components: closure.components.len(),
            positions: closure.component_of.len(),
        },
        &metadata! {},
    );
}

pub(crate) fn produce_transport_component_product(
    world: &mut World<'_>,
    session: &mut PullSession,
    position: &TransportPosition,
) -> PullOutcome {
    let executable = executable_key_for_transport_position(session.root(), position, world.types_mut());
    displace_covering_solve_if_stale(world, session, &executable);
    if let Some(component) = session.transport_component(position).cloned() {
        emit_transport_component_produced(world, &component);
        return PullOutcome::Produced(ProductValue::TransportComponent(component));
    }
    if !session.transport_closure_covers(&executable)
        && let Err(waits) = solve_transport_closure(world, session, &executable)
    {
        return PullOutcome::Waiting(waits);
    }
    let component = materialize_transport_component(world, session, &executable, position);
    emit_transport_component_produced(world, &component);
    emit_transport_component_materialized(world, &executable, &component);
    PullOutcome::Produced(ProductValue::TransportComponent(component))
}

/// Materialize `position`'s component from the covering solve into the
/// session's product-visible inventories: every member's shape is recorded and
/// the pulled position's inventory carries the component's canonical
/// representative and full membership. A position the covering solve never
/// constrained is proven unconstrained by that same solve -- it gets a
/// singleton component, never a re-solve.
fn materialize_transport_component(
    world: &mut World<'_>,
    session: &mut PullSession,
    executable: &ExecutableKey,
    position: &TransportPosition,
) -> TransportComponentInventory {
    let Some(solved) = session.solved_transport_component(executable, position).cloned() else {
        let component = TransportComponentInventory {
            representative: position.clone(),
            positions: vec![position.clone()],
        };
        session.record_transport_component(position.clone(), component.clone());
        return component;
    };
    if let Some(shape) = solved.shape {
        for member in &solved.positions {
            let member_executable = executable_key_for_transport_position(session.root(), member, world.types_mut());
            session.record_transport_shape_for(&member_executable, member.clone(), shape);
        }
    }
    let component = TransportComponentInventory {
        representative: solved.representative,
        positions: solved.positions,
    };
    session.record_transport_component(position.clone(), component.clone());
    component
}

/// Read-time freshness gate for the WORLD facts a recorded solve consumed.
/// Session products push their movement into the session
/// (`record_settled_runtime_demand`, `record_call_edge`, the materialization
/// epoch gate), but world facts have no push channel -- so before a recorded
/// solve answers a pull, its revision snapshot is compared against the
/// world's current revisions, and any moved fact displaces the whole
/// covering solve (the full invalidation walk over the consult ledger). The
/// same validated-at-read discipline `DemandFactsCache` applies to
/// demand-cone facts.
fn displace_covering_solve_if_stale(world: &World<'_>, session: &mut PullSession, executable: &ExecutableKey) {
    let stale = session
        .covering_solve_consumed_revisions(executable)
        .is_some_and(|snapshot| {
            snapshot
                .iter()
                .any(|(fact, revision)| world.fact_revision(fact).unwrap_or(0) != *revision)
        });
    if stale {
        session.displace_transport_closure_for(executable);
    }
}

/// The consulted-facts ledger ONE closure solve accumulates, then registers
/// into the session on completion. Two channels, matched to how each fact
/// kind retracts:
///
///  - `executables`: owners of SESSION-product reads (RuntimeDemand values,
///    IncomingInputSlot values). Installed as `SolvedTransportClosure::
///    consulted` and cross-registered against the closure's membership by
///    `record_solved_transport_closure` so the session-side push events
///    (`record_settled_runtime_demand`, `record_call_edge`) reach every
///    member through `invalidate_transport_products`' walk.
///  - `fact_revisions`: WORLD-fact reads at the revision consumed
///    (first-read-wins; 0 = read before first publication, so a later
///    publication mismatches -- "not yet published" is a distinct state, not
///    an absent entry). World facts have no push into the session; the
///    snapshot is validated whenever the recorded solve answers a pull
///    (`displace_covering_solve_if_stale`).
#[derive(Default)]
struct ClosureConsultLedger {
    executables: HashSet<ExecutableKey>,
    fact_revisions: HashMap<FactKey, u64>,
}

impl ClosureConsultLedger {
    fn consult_executable(&mut self, executable: &ExecutableKey) {
        self.executables.insert(executable.clone());
    }

    fn consult_fact(&mut self, world: &World<'_>, fact: FactKey) {
        let revision = world.fact_revision(&fact).unwrap_or(0);
        self.fact_revisions.entry(fact).or_insert(revision);
    }
}

/// Solve the shape-constraint graph for the settled executable closure seeded
/// at `executable` ONCE, and record the complete result -- every connected
/// component plus all callable and boundary facts -- into the session. Any
/// later component pull for any position of any covered executable
/// materializes from this record; the solve never repeats until a transport
/// invalidation (an epoch event) clears the recorded solves.
fn solve_transport_closure(
    world: &mut World<'_>,
    session: &mut PullSession,
    executable: &ExecutableKey,
) -> Result<(), Vec<PullWait>> {
    let demand = match session.memo().runtime_demand(executable).cloned() {
        Some(demand) => demand,
        None => {
            return Err(vec![PullWait::Product(ProductKey::RuntimeDemand(executable.clone()))]);
        }
    };

    let mut runtime_demands = HashMap::from([(executable.clone(), demand)]);
    let mut executables = HashSet::from([executable.clone()]);
    // THE CONSULTED-FACTS LEDGER (see `ClosureConsultLedger`). Every fact
    // this solve reads is recorded AT THE READ SITE -- session-product reads
    // register their owning executable, world-fact reads snapshot their
    // revision -- and on completion both channels are installed with the
    // closure (`SolvedTransportClosure::consulted` +
    // `SolvedTransportClosure::consumed_fact_revisions`). The discovery graph
    // and the retraction graph are thereby the SAME graph by construction:
    // any movement of any consulted fact displaces every member this solve
    // produced, so wait-emission order is unconstrained -- completeness never
    // depends on which wait the driver services first.
    //
    // MAINTENANCE OBLIGATION: any fact read added to this solve (here, the
    // expansion helpers, `collect_transport_contexts`,
    // `install_produced_incoming_inputs`, or the projection phase) that can
    // influence closure membership or recorded shapes MUST be recorded in
    // this ledger at the read site -- `consult_executable` for a session
    // product, `consult_fact` for a world fact -- or be exempted here with a
    // stated reason. Current exemptions:
    //  - `world.types()` / `world.shape()` / `world.lane()`: interned
    //    identities are append-only and immutable -- an id never changes
    //    meaning, so there is nothing to retract.
    //  - the `OutgoingInputEdges` presence probe in
    //    `outgoing_input_edge_waits`: a scheduling gate only; the product's
    //    DATA reaches this solve exclusively through the ledgered
    //    `IncomingInputSlot` reads (its production `record_call_edge`s into
    //    the session inventory those slots serve).
    //  - the projection phase's direct `world.callsite_summary` reads: keyed
    //    by (member activation, callsite) pairs drawn from the member's
    //    lowered body, the same key set `collect_transport_contexts` already
    //    snapshots from the member's settled `analysis.callsites` -- covered
    //    by subsumption, no second snapshot.
    //  - `session.materialized_executables` bodies: session products whose
    //    movement pushes through `record_materialized_executable`'s epoch
    //    gate, rooted at the owning member itself (a ledgered executable).
    //  - `session.transport_closure_id_covering` (read by the shape
    //    producer, not this solve): the session's own solve record, displaced
    //    together with the closure it names.
    let mut ledger = ClosureConsultLedger::default();
    while let Some(next) =
        expand_transport_product_executables(world, session, &executables, &runtime_demands, &mut ledger)
    {
        let mut wait_products = Vec::new();
        let mut changed = false;
        for executable in next {
            if executables.insert(executable.clone()) {
                changed = true;
            }
            if let std::collections::hash_map::Entry::Vacant(entry) = runtime_demands.entry(executable.clone()) {
                if let Some(demand) = session.memo().runtime_demand(&executable).cloned() {
                    entry.insert(demand);
                } else {
                    wait_products.push(PullWait::Product(ProductKey::RuntimeDemand(executable)));
                }
            }
        }
        if !wait_products.is_empty() {
            return Err(wait_products);
        }

        let outgoing_waits = outgoing_input_edge_waits(session, &executables);
        if !outgoing_waits.is_empty() {
            return Err(outgoing_waits);
        }

        let incoming = expand_transport_product_incoming_producers(world, session, &executables, &mut ledger)?;
        let mut wait_products = Vec::new();
        for executable in incoming {
            if executables.insert(executable.clone()) {
                changed = true;
            }
            if let std::collections::hash_map::Entry::Vacant(entry) = runtime_demands.entry(executable.clone()) {
                if let Some(demand) = session.memo().runtime_demand(&executable).cloned() {
                    entry.insert(demand);
                } else {
                    wait_products.push(PullWait::Product(ProductKey::RuntimeDemand(executable)));
                }
            }
        }
        if !wait_products.is_empty() {
            return Err(wait_products);
        }
        if !changed {
            break;
        }
    }
    let outgoing_waits = outgoing_input_edge_waits(session, &executables);
    if !outgoing_waits.is_empty() {
        return Err(outgoing_waits);
    }

    let mut reads = Vec::new();
    let mut wait_facts = HashSet::new();
    let mut contexts = collect_transport_contexts(
        world,
        &executables,
        &runtime_demands,
        session.materialized_executables(),
        &mut reads,
        &mut wait_facts,
        &mut ledger,
    );
    if !wait_facts.is_empty() {
        return Err(wait_facts
            .into_iter()
            .map(|fact| PullWait::Fact(super::super::facts::FactUse::settled(fact)))
            .collect());
    }

    install_produced_incoming_inputs(world, session, &mut contexts, &mut ledger)?;
    let mut facts = TransportFactsBuilder::default();
    let mut shape_graph = ShapeConstraintGraph::default();
    let mut memo = ProjectionMemo::default();
    // Canonical visitation over the COMPLETED closure: order is a property of
    // the container (a BTreeMap keyed by the schedule-free structural render),
    // with each key computed once per member -- never a comparison-time sort
    // over an in-flight set. Distinct executables whose renders collide all
    // keep their slot (the value is a bucket, not a single member).
    let ordered = {
        let mut by_key: BTreeMap<ExecutableSortKey, Vec<ExecutableKey>> = BTreeMap::new();
        for executable in &executables {
            by_key
                .entry(executable_sort_key(executable, world.types()))
                .or_default()
                .push(executable.clone());
        }
        by_key.into_values().flatten().collect::<Vec<_>>()
    };
    for executable in &ordered {
        let Some(context) = contexts.get(executable).cloned() else {
            continue;
        };
        project_one_executable(
            world,
            executable,
            &context,
            &contexts,
            &mut facts,
            &mut shape_graph,
            &mut memo,
        );
    }
    collect_clause_parameter_equalities(&contexts, &ordered, &mut shape_graph, world.types());
    seed_callable_capture_inputs(world, &contexts, &mut facts, &mut shape_graph, &mut memo);
    collect_executable_input_constraints(world, &contexts, &mut facts, &ordered, &mut shape_graph);

    let union = shape_graph.build_union();
    let component_shapes = shape_graph.component_shapes(&union);
    let equivalents = ShapeConstraintGraph::equivalents_for(&union);
    facts.expand_boundary_publications(&equivalents);
    facts.resolve_publication_source_boundaries(world);
    let (callables, boundaries) = facts.finish();
    for (callable, facts) in callables {
        session.record_callable_facts(callable, facts);
    }
    for (boundary, facts) in boundaries {
        session.record_boundary_facts(boundary, facts);
    }

    let mut closure = solved_closure_from_union(executables, &union, &component_shapes, world.types());
    closure.consumed_fact_revisions = ledger.fact_revisions;
    closure.consulted = ledger.executables;
    emit_transport_closure_solved(world, &closure);
    session.record_solved_transport_closure(closure);
    Ok(())
}

/// Fold the solved union into per-component records: member positions, the
/// component's agreed shape, and the canonical representative -- a running min
/// under the structural position order, never a sort.
fn solved_closure_from_union(
    executables: HashSet<ExecutableKey>,
    union: &PositionUnion,
    component_shapes: &HashMap<usize, ShapeId>,
    types: &Types,
) -> SolvedTransportClosure {
    let mut closure = SolvedTransportClosure {
        executables,
        ..Default::default()
    };
    let mut index_of_root: HashMap<usize, usize> = HashMap::new();
    let mut representative_keys: Vec<TransportPositionSortKey> = Vec::new();
    for position in union.positions() {
        let root = union.find_existing(position);
        let key = transport_position_sort_key(position, types);
        let index = match index_of_root.entry(root) {
            std::collections::hash_map::Entry::Occupied(entry) => {
                let index = *entry.get();
                if key < representative_keys[index] {
                    representative_keys[index] = key;
                    closure.components[index].representative = position.clone();
                }
                index
            }
            std::collections::hash_map::Entry::Vacant(entry) => {
                closure.components.push(SolvedTransportComponent {
                    representative: position.clone(),
                    positions: Vec::new(),
                    shape: component_shapes.get(&root).copied(),
                });
                representative_keys.push(key);
                *entry.insert(closure.components.len() - 1)
            }
        };
        closure.components[index].positions.push(position.clone());
        closure.component_of.insert(position.clone(), index);
    }
    closure
}

fn expand_transport_product_executables(
    world: &World<'_>,
    session: &PullSession,
    executables: &HashSet<ExecutableKey>,
    runtime_demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    ledger: &mut ClosureConsultLedger,
) -> Option<Vec<ExecutableKey>> {
    let mut next = Vec::new();
    for executable in executables {
        let demand = runtime_demands
            .get(executable)
            .or_else(|| session.memo().runtime_demand(executable))?;
        // The RuntimeDemand read above is a session product (callable_flows
        // feeds membership); its owner joins the executables channel. The
        // world-fact reads below each snapshot their revision: the activation
        // analysis (callsites and reachable_clauses feed membership), the
        // lowered body (via `executable_callsite_needs` it decides the `need`
        // component of the member keys pushed -- membership identity, not
        // just shapes), and each CallSiteSummary (targets feed membership).
        // A read added here MUST join the ledger the same way (see the
        // obligation in `solve_transport_closure`).
        ledger.consult_executable(executable);
        for flow in demand.callable_flows.values() {
            for resolution in &flow.resolutions {
                push_executable_unique(&mut next, resolution.clone());
            }
        }
        ledger.consult_fact(world, FactKey::ActivationAnalyzed(executable.activation.clone()));
        let analysis = world.activation_analysis(&executable.activation)?;
        ledger.consult_fact(world, FactKey::LoweredBody(executable.activation.function));
        let body = world.lowered_body(executable.activation.function);
        let callsite_needs = executable_callsite_needs(&body, &analysis.reachable_clauses, executable.need);
        for callsite in &analysis.callsites {
            let key = CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            };
            ledger.consult_fact(world, FactKey::CallSiteSummary(key.clone()));
            let summary = world.callsite_summary(&key)?;
            let need = callsite_needs.get(callsite).copied().unwrap_or(ExecutableNeed::Value);
            for target in &summary.targets {
                let Some(activation) = target.activation.clone() else {
                    continue;
                };
                push_executable_unique(&mut next, ExecutableKey { activation, need });
            }
        }
    }
    Some(next)
}

// The `OutgoingInputEdges` probe is a scheduling gate, not a data read: it
// only tests presence to emit waits, and the product's data reaches the solve
// exclusively through the ledger-covered `IncomingInputSlot` reads. Exempt
// from the consulted-facts ledger for that reason.
fn outgoing_input_edge_waits(session: &PullSession, executables: &HashSet<ExecutableKey>) -> Vec<PullWait> {
    executables
        .iter()
        .filter_map(|executable| {
            let key = ProductKey::OutgoingInputEdges(executable.clone());
            session.memo().get(&key).is_none().then_some(PullWait::Product(key))
        })
        .collect()
}

fn expand_transport_product_incoming_producers(
    world: &World<'_>,
    session: &PullSession,
    executables: &HashSet<ExecutableKey>,
    ledger: &mut ClosureConsultLedger,
) -> Result<Vec<ExecutableKey>, Vec<PullWait>> {
    let mut next = Vec::new();
    let mut waits = Vec::new();
    for executable in executables {
        for semantic_index in 0..executable.activation.input_len(world.types()) {
            let slot = InputSlot {
                executable: executable.clone(),
                semantic_index,
            };
            let key = ProductKey::IncomingInputSlot(slot);
            let Some(value) = session.memo().get(&key) else {
                waits.push(PullWait::Product(key));
                continue;
            };
            // The read IncomingInputSlot is a session product owned by
            // `executable`: a later change to its producer set
            // (`record_call_edge`) must reach this closure, so its owner
            // joins the executables channel.
            ledger.consult_executable(executable);
            let ProductValue::IncomingInputSlot(sources) = value else {
                panic!("incoming input slot product produced unexpected value {value:?}");
            };
            for source in sources.iter() {
                push_executable_unique(&mut next, source.producer.clone());
            }
        }
    }
    if waits.is_empty() { Ok(next) } else { Err(waits) }
}

fn push_executable_unique(target: &mut Vec<ExecutableKey>, executable: ExecutableKey) {
    if !target.contains(&executable) {
        target.push(executable);
    }
}

fn install_produced_incoming_inputs(
    world: &World<'_>,
    session: &PullSession,
    contexts: &mut TransportContexts,
    ledger: &mut ClosureConsultLedger,
) -> Result<(), Vec<PullWait>> {
    let mut waits = Vec::new();
    let mut installed = Vec::new();
    for executable in contexts.by_executable.keys() {
        let input_len = executable.activation.input_len(world.types());
        for semantic_index in 0..input_len {
            let slot = InputSlot {
                executable: executable.clone(),
                semantic_index,
            };
            let key = ProductKey::IncomingInputSlot(slot);
            let Some(value) = session.memo().get(&key) else {
                waits.push(PullWait::Product(key));
                continue;
            };
            // The consumed IncomingInputSlot values feed the recorded shapes,
            // so the slot-owning member joins the executables channel here too.
            ledger.consult_executable(executable);
            let ProductValue::IncomingInputSlot(slot_sources) = value else {
                panic!("incoming input slot product produced unexpected value {value:?}");
            };
            let sources = incoming_slot_source_pairs(slot_sources);
            if !sources.is_empty() {
                installed.push(((executable.clone(), semantic_index), sources));
            }
        }
    }
    if !waits.is_empty() {
        return Err(waits);
    }
    contexts.incoming_input_sources.extend(installed);
    Ok(())
}

fn incoming_slot_source_pairs(sources: &[IncomingInputSource]) -> Vec<(ExecutableKey, ValueId)> {
    sources
        .iter()
        .map(|source| (source.producer.clone(), source.value))
        .collect()
}

fn executable_key_for_transport_position(
    root: RootId,
    position: &TransportPosition,
    types: &mut Types,
) -> ExecutableKey {
    let symbol = position.executable();
    ExecutableKey {
        activation: ActivationKey::from_inputs(root, symbol.activation.function, &symbol.activation.input, types),
        need: symbol.need,
    }
}

fn collect_transport_contexts(
    world: &mut World<'_>,
    executables: &HashSet<ExecutableKey>,
    runtime_demands: &HashMap<ExecutableKey, ExecutableRuntimeDemand>,
    materialized_executables: &HashMap<ExecutableKey, MaterializedExecutable>,
    reads: &mut Vec<FactKey>,
    wait_facts: &mut HashSet<FactKey>,
    ledger: &mut ClosureConsultLedger,
) -> TransportContexts {
    let mut contexts = HashMap::new();
    for executable in executables {
        // EVERY fact read in this member's block is keyed by `executable`.
        // Session products (the runtime-demand snapshot, a materialized body)
        // register the member in the executables channel; world facts (the
        // settled activation analysis, return type, per-callsite summaries,
        // and the lowered-body fallback) each snapshot their revision. A read
        // keyed by a different executable MUST record its own owner (see the
        // ledger obligation in `solve_transport_closure`).
        ledger.consult_executable(executable);
        let activation_fact = FactKey::ActivationAnalyzed(executable.activation.clone());
        if !world.fact_is_settled(&activation_fact) {
            wait_facts.insert(activation_fact);
            continue;
        }
        ledger.consult_fact(world, activation_fact.clone());
        reads.push(activation_fact);

        let return_fact = FactKey::ReturnType(executable.activation.clone());
        if !world.fact_is_settled(&return_fact) {
            wait_facts.insert(return_fact);
            continue;
        }
        ledger.consult_fact(world, return_fact.clone());
        reads.push(return_fact);

        let analysis = world
            .activation_analysis(&executable.activation)
            .cloned()
            .expect("settled activation analyses should be readable");
        let return_ty = world
            .activation_return(&executable.activation)
            .unwrap_or_else(|| world.types_mut().none());
        let materialized = materialized_executables.get(executable);
        let uses_materialized_body = materialized.is_some();
        if !uses_materialized_body {
            ledger.consult_fact(world, FactKey::LoweredBody(executable.activation.function));
        }
        let (body, original_entry_ids) = materialized
            .map(|materialized| (materialized.body.clone(), materialized.original_entry_ids.clone()))
            .unwrap_or_else(|| (world.lowered_body(executable.activation.function), Vec::new()));
        let runtime_demand = runtime_demands.get(executable).cloned().unwrap_or_default();
        let reachable_clauses = if uses_materialized_body {
            local_clause_ids(&body)
        } else {
            analysis.reachable_clauses.clone()
        };
        let reachable_entries = if uses_materialized_body {
            local_entry_ids(&body)
        } else {
            analysis.reachable_entries.clone()
        };
        let callsite_needs = executable_callsite_needs(&body, &reachable_clauses, executable.need);
        for callsite in &analysis.callsites {
            let fact = FactKey::CallSiteSummary(CallSiteKey {
                activation: executable.activation.clone(),
                callsite: *callsite,
            });
            if !world.fact_is_settled(&fact) {
                wait_facts.insert(fact);
                continue;
            }
            ledger.consult_fact(world, fact.clone());
            reads.push(fact);
        }
        let resume_entries = collect_resume_entries(&body, &analysis, &original_entry_ids);
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
                callsite_args: callsite_call_args(&body),
                callsite_modes: callsite_input_modes(&body),
                callsite_dests: callsite_call_dests(&body),
                local_sources,
                return_sources: collect_return_sources(&body, &reachable_clauses, &reachable_entries),
                resume_entries,
                analysis,
                return_ty,
                body,
                original_entry_ids,
                runtime_demand,
                callsite_needs,
            },
        );
    }
    // The incoming-input-source index is filled by the caller: production reads
    // it from the contributed `InputSources` facts (each producer pushes its
    // outgoing edges); the shadow test builds it in-process from injected
    // demands. Leaving it empty here keeps the two sources out of this pass.
    TransportContexts {
        by_executable: contexts,
        incoming_input_sources: HashMap::new(),
        accessed: RefCell::new(None),
    }
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
    contexts: &TransportContexts,
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

    let value_demands = effective_value_demands(world, executable, context, contexts);
    let mut values = context.analysis.value_types.iter().collect::<Vec<_>>();
    values.sort_by_key(|(value, _)| value.as_u32());
    for (&value, &ty) in values {
        if clause_params.contains(&value) {
            continue;
        }
        let demand = value_demands.get(&value).cloned().unwrap_or_default();
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

    if let LoweredBody::Clauses { entries, .. } = &context.body {
        for (entry_index, entry) in entries.iter().enumerate() {
            let entry_id = original_entry_id(context, entry_index);
            for (capture_index, capture) in entry.captures.iter().copied().enumerate() {
                shape_graph.equal(
                    TransportPosition::EntryCapture {
                        executable: symbol.clone(),
                        entry: entry_id,
                        capture_index,
                    },
                    TransportPosition::Value {
                        executable: symbol.clone(),
                        value: capture,
                    },
                );
            }
        }
    }

    let consumed_values = body_consumed_values(&context.body);
    for resume in &context.resume_entries {
        let position = TransportPosition::ResumePayload {
            executable: symbol.clone(),
            callsite: resume.callsite,
            entry: resume.entry,
        };
        let demand = resume_demand(context, *resume);
        let is_consumed = consumed_values.contains(&resume.value);
        // The physical shape of a delivered call result is owned by the
        // PRODUCER: the callee's settled `ExecutableReturn` ABI. We source the
        // resume STRUCTURE from that producer ABI in two cases:
        //
        //  - DESTINATION-PASSING (`ExecutableNeed::TupleFields`): the callee
        //    physically writes every field into the caller frame, so a field
        //    this caller ignores is never erased to `Nothing`. Reliably
        //    ABI-derivable from the callsite need.
        //  - CONSUMED by-value: the body actually reads the delivered value, so
        //    its structure must survive. Consumption is read from the static
        //    lowered body (`body_consumed_values`), NOT from `demand.is_ignore()`
        //    -- the value-demand fixpoint transiently UNDER-reports a consumed
        //    delivered result (e.g. a tail-recursion accumulator), and sourcing
        //    structure from that oscillating demand is exactly the defect that
        //    dropped a delivered field.
        //
        // A GENUINELY-DISCARDED by-value return (read nowhere, not
        // destination-passing -- e.g. an `Enum.each` element call) is left on the
        // demand-driven path, where its `ignore` demand keeps the zero-width
        // continuation the runtime needs instead of fabricating a value.
        //
        // A CALLABLE return keeps the demand-driven projection regardless, which
        // settles direct vs. first-class callable transport from THIS caller's
        // use -- the boundary selection the rest of the callable-boundary suite
        // asserts. A callable return carries the empty data shape, so the two
        // axes never overlap.
        let destination_passing = resume
            .callsite
            .and_then(|callsite| context.callsite_needs.get(&callsite))
            .is_some_and(|need| matches!(need, ExecutableNeed::TupleFields(_)));
        let producer_return = (!demand.is_callable() && (destination_passing || is_consumed))
            .then_some(resume.callsite)
            .flatten()
            .and_then(|callsite| callsite_callee_return_position(world, contexts, executable, context, callsite));
        if let Some(callee_return) = producer_return {
            shape_graph.equal(position, callee_return);
        } else {
            // No single producer ABI to source from (callable dispatch,
            // multi-target, or a diverging callee), or a genuinely-discarded
            // by-value return. A discarded return keeps its demand-driven shape
            // (zero-width when ignored). A CONSUMED return whose value-demand
            // still under-reports as `ignore` is floored to `Whole`, so its
            // delivered value materializes as a real (boxed) shape rather than
            // collapsing to `Nothing` -- this is monotone: the floor only raises
            // an `ignore` toward `Whole`, and consumption is a stable body fact.
            let effective_demand = if is_consumed && demand.is_ignore() {
                RuntimeDemand::whole()
            } else {
                demand.clone()
            };
            let shape = resume_shape(
                world,
                contexts,
                facts,
                executable,
                context,
                *resume,
                &effective_demand,
                Some(position.clone()),
                memo,
            );
            shape_graph.anchor(position, shape);
        }
    }
}

/// Anchor every callable resolution's capture-prefix inputs to the closure's
/// construction layout. This is the SOLE seeder of capture-input shapes: a
/// closure value has one physical capture layout, owned by the value and derived
/// once from its construction (the joined demand over all the flow's
/// resolutions), so two observers of the same closure cannot disagree about its
/// shape. (The former second pass that re-derived capture shapes from the
/// canonical interned descr was redundant with this and is gone.)
fn seed_callable_capture_inputs(
    world: &mut World<'_>,
    contexts: &TransportContexts,
    facts: &mut TransportFactsBuilder,
    shape_graph: &mut ShapeConstraintGraph,
    memo: &mut ProjectionMemo,
) {
    // Keyed by (executable, capture-producing value) -- `callable_flows` is
    // already a `HashMap<ValueId, CallableFlowFact>` per executable, so that
    // pair is a structural identity with no collisions to arbitrate: unlike a
    // display-string or partial-field sort key feeding a dedup, this ordering
    // can never merge two DIFFERENT flows or need a tie-break between them.
    // The `BTreeMap` gives deterministic visitation order (both `contexts` and
    // `callable_flows` are hash-order today) without a per-comparison sort.
    let flows: BTreeMap<(ExecutableKey, ValueId), (&ExecutableKey, &ExecutableContext, &CallableFlowFact)> = contexts
        .iter()
        .flat_map(|(executable, context)| {
            context
                .runtime_demand
                .callable_flows
                .iter()
                .map(move |(value, flow)| ((executable.clone(), *value), (executable, context, flow)))
        })
        .collect();
    let flows = flows.into_values().collect::<Vec<_>>();

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
            .filter(|resolution| resolution.activation.function == flow.function)
            .collect::<Vec<_>>();
        if resolution_symbols.is_empty() {
            continue;
        }
        // A capture's shape is the closure's CONSTRUCTION layout: the capture is
        // physically present in the record for every activation of the closure,
        // regardless of which specialized activation happens to read it. So the
        // demand joins across ALL of the flow's resolutions (a present-but-unused
        // capture on one specialization joins with its use on another), never
        // per single resolution -- a per-activation demand bottoms to `Ignore`
        // for the arm that ignores the capture and would anchor `Nothing`,
        // fragmenting a layout-identical closure (fz-f98.3,
        // [[feedback_shapeid_is_pure_layout]]). The joined shape is then anchored
        // identically for every resolution.
        let capture_demands =
            capture_demands_for_resolutions(contexts, &capture_tys, &resolution_symbols, world.types());
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
        for resolution in &resolution_symbols {
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

fn effective_value_demands(
    world: &World<'_>,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    contexts: &TransportContexts,
) -> HashMap<ValueId, RuntimeDemand> {
    let mut demands = context.runtime_demand.value_demands.clone();
    for (callsite, arg_demands) in &context.runtime_demand.call_arg_demands {
        let Some(args) = context.callsite_args.get(callsite) else {
            continue;
        };
        for (arg, demand) in args.iter().zip(arg_demands.iter()) {
            demands
                .entry(arg.value)
                .and_modify(|existing| existing.join_assign(demand))
                .or_insert_with(|| demand.clone());
        }
    }
    for (callsite, args) in &context.callsite_args {
        let Some(mode) = context.callsite_modes.get(callsite).copied() else {
            continue;
        };
        let key = CallSiteKey {
            activation: executable.activation.clone(),
            callsite: *callsite,
        };
        let Some(summary) = world.callsite_summary(&key) else {
            continue;
        };
        let need = context
            .callsite_needs
            .get(callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        for target in &summary.targets {
            let Some(activation) = target.activation.as_ref() else {
                continue;
            };
            let callee = ExecutableKey {
                activation: activation.clone(),
                need,
            };
            let Some(callee_context) = contexts.context_for(&callee) else {
                continue;
            };
            for (arg_index, arg) in args.iter().enumerate() {
                let Some(semantic_index) =
                    mode.semantic_index(callee.activation.input_len(world.types()), args.len(), arg_index)
                else {
                    continue;
                };
                let Some(demand) = callee_context.runtime_demand.input_demands.get(semantic_index) else {
                    continue;
                };
                demands
                    .entry(arg.value)
                    .and_modify(|existing| existing.join_assign(demand))
                    .or_insert_with(|| demand.clone());
            }
        }
    }
    demands
}

fn collect_executable_input_constraints(
    world: &mut World<'_>,
    contexts: &TransportContexts,
    facts: &mut TransportFactsBuilder,
    executables: &[ExecutableKey],
    shape_graph: &mut ShapeConstraintGraph,
) {
    for executable in executables {
        let symbol = executable_symbol(executable, world.types());
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        // The KEY inputs are the dispatch identity carried by `symbol`; after the
        // addressed-alpha convergence collapse they may be address vars
        // (`list(a1_e)`, surface vars) that carry no layout. LAYOUT is derived from
        // the PRECISE EVIDENCE — the un-collapsed `ActivationInputs` fact — so a
        // slot's ShapeId anchors on its real ground type (`list(int)`, the concrete
        // callable) rather than the address var. KEY ≠ EVIDENCE, applied at the
        // transport seam (fz-f98.14.10.2). When the fact is absent (no body
        // evidence yet) the key inputs are the only available layout source.
        let layout_inputs = world
            .activation_inputs(&executable.activation)
            .unwrap_or_else(|| executable.activation.inputs(world.types()));
        for (semantic_index, ty) in layout_inputs.into_iter().enumerate() {
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
            let incoming = incoming_executable_input_positions(world, contexts, executable, semantic_index);
            let projected_callable_input_shape = if demand.is_callable()
                && let Some(incoming) = incoming.as_ref()
            {
                facts.record_publication_source_positions(position.clone(), incoming.clone());
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
                continue;
            }
            if let Some(incoming) = incoming {
                let incoming_shapes = incoming
                    .iter()
                    .map(|source| shape_graph.anchor_shape(source))
                    .collect::<Option<Vec<_>>>();
                if let Some(incoming_shapes) = incoming_shapes {
                    // Every incoming shape has settled: union with the call args
                    // only when they all agree (and agree with any existing anchor),
                    // which is layout-preserving. Distinct incoming shapes fall
                    // through and anchor this slot's own shape instead, so
                    // layout-distinct sibling callables never fuse into one
                    // component.
                    let first = incoming_shapes.first().copied();
                    let anchor_shape = shape_graph.anchor_shape(&position);
                    if first.is_some()
                        && incoming_shapes.iter().all(|shape| Some(*shape) == first)
                        && anchor_shape.is_none_or(|shape| Some(shape) == first)
                    {
                        for call_arg in incoming {
                            shape_graph.equal(position.clone(), call_arg);
                        }
                    } else if anchor_shape.is_none() {
                        let shape = projected_callable_input_shape.unwrap_or_else(|| {
                            shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()))
                        });
                        shape_graph.anchor(position, shape);
                    }
                } else if demand.is_ignore() && incoming.len() == 1 && !shape_graph.has_anchor(&position) {
                    // A single ignored incoming arg still carries alias/ownership
                    // evidence; multiple unresolved incoming args would merge
                    // distinct recursive activations before their shapes settle.
                    for call_arg in incoming {
                        shape_graph.equal(position.clone(), call_arg);
                    }
                } else if demand.is_ignore() && !shape_graph.has_anchor(&position) {
                    let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                    shape_graph.anchor(position, shape);
                } else if !shape_graph.has_anchor(&position)
                    && demand.callable.resolved.len() <= 1
                    && incoming.len() == 1
                {
                    // The incoming shapes have not all settled (this input's own
                    // shape was not projectable), so the layout-preserving "incoming
                    // agree" gate above cannot fire. Union with the incoming call arg
                    // only when a SINGLE incoming source converges here at a slot
                    // carrying at most one resolved surface: one source cannot fuse
                    // layout-distinct callables, so a recursive self-call still
                    // carries its source layout (fz-go4.1). With two or more
                    // unsettled incoming sources — the take/drop/split WRAPPER that
                    // sees several layout-distinct reducers before their shapes
                    // settle — unioning would merge distinct capture shapes into one
                    // anchor component and trip the agree-or-panic meet, so it
                    // anchors its own shape instead. A joined opaque value is
                    // first-class and unions through the agree gate above.
                    for call_arg in incoming {
                        shape_graph.equal(position.clone(), call_arg);
                    }
                } else if !shape_graph.has_anchor(&position) {
                    let shape = projected_callable_input_shape.unwrap_or_else(|| {
                        shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()))
                    });
                    shape_graph.anchor(position, shape);
                }
            } else if !shape_graph.has_anchor(&position) {
                let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                shape_graph.anchor(position, shape);
            }
        }
    }
}

fn executable_input_demand_requires_own_shape(demand: &RuntimeDemand) -> bool {
    (!matches!(demand.shape, ShapeDemand::Ignore)) || demand.callable.is_first_class()
}

fn collect_clause_parameter_equalities(
    contexts: &TransportContexts,
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

/// The `ExecutableReturn` position a call result is produced from, when the
/// call settles to exactly one known callee executable. Resume payloads and
/// return payloads are callsite result positions, so they share the producer
/// return `ShapeId` instead of mutating that shape through the caller's local
/// demand.
fn callsite_callee_return_position(
    world: &World<'_>,
    contexts: &TransportContexts,
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
        .contains_context(&callee)
        .then(|| TransportPosition::ExecutableReturn {
            executable: executable_symbol(&callee, world.types()),
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

// The EXECUTABLE VISITATION key (`executable_sort_key`) is a CANONICAL STRUCTURAL
// render of its input types (`Vec<String>`), not the raw interned `Ty(u32)` ids.
// The upstream type fixpoint mints `Ty` ids in process-hash-dependent order, so a
// raw-id key would sort same-function specializations differently per run — and
// that visitation order drives the non-monotone anchor/union gate in
// `collect_executable_input_constraints`, which is the schedule-dependent source
// of the transport.rs shape-anchor panic. A structural render is a pure function
// of input STRUCTURE: total, deterministic, and interning-order-free. The key is
// computed ONCE per closure member at the completed-closure boundary (a BTreeMap
// insert in `solve_transport_closure`), never re-rendered per comparison.
//
// The COMPONENT REPRESENTATIVE key (`transport_position_sort_key`) extends the
// same structural render to positions; the representative is the running MIN
// under this order while the solved union is folded into components.
//
// The fact-OUTPUT keys below (`executable_symbol_sort_key` etc.) stay raw-`Ty`
// keyed: they order published resolution/codegen-seam lists, not the union
// ladder, and within one plan the `Ty` ids are stable — re-keying them on the
// structural render reorders which resolution a boundary picks for its return
// lane, which is a layout regression, not a determinism fix.
type ExecutableSortKey = (u32, Vec<String>, u8, usize);
type ExecutableSymbolSortKey = (u32, Vec<Ty>, u8, usize);
type TransportPositionSortKey = (u8, u32, Vec<String>, u8, usize, u64, u64, usize);

/// Canonical structural render of an input type vector — the schedule-free
/// projection used as the executable visitation secondary sort key.
fn input_structure_key(inputs: &[Ty], types: &Types) -> Vec<String> {
    inputs.iter().map(|ty| types.display(ty)).collect()
}

fn executable_sort_key(executable: &ExecutableKey, types: &Types) -> ExecutableSortKey {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        input_structure_key(&executable.activation.inputs(types), types),
        need.0,
        need.1,
    )
}

/// Canonical structural order over transport positions: position kind, then
/// the owning executable's structural render, then the position's body-local
/// ids. Schedule-free for the same reason `executable_sort_key` is.
fn transport_position_sort_key(position: &TransportPosition, types: &Types) -> TransportPositionSortKey {
    let executable = position.executable();
    let (rank, first, second, index) = match position {
        TransportPosition::ExecutableInput { semantic_index, .. } => (0, 0, 0, *semantic_index),
        TransportPosition::ExecutableReturn { .. } => (1, 0, 0, 0),
        TransportPosition::ResumePayload { callsite, entry, .. } => (
            2,
            callsite.map_or(0, |callsite| u64::from(callsite.as_u32()) + 1),
            u64::from(entry.as_u32()),
            0,
        ),
        TransportPosition::ReturnPayload { callsite, .. } => (3, u64::from(callsite.as_u32()), 0, 0),
        TransportPosition::CallArg {
            callsite,
            semantic_index,
            ..
        } => (4, u64::from(callsite.as_u32()), 0, *semantic_index),
        TransportPosition::EntryCapture {
            entry, capture_index, ..
        } => (5, u64::from(entry.as_u32()), 0, *capture_index),
        TransportPosition::Value { value, .. } => (6, u64::from(value.as_u32()), 0, 0),
    };
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        rank,
        executable.activation.function.as_u32(),
        input_structure_key(&executable.activation.input, types),
        need.0,
        need.1,
        first,
        second,
        index,
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

fn executable_symbol_sort_key(symbol: &ExecutableSymbol) -> ExecutableSymbolSortKey {
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

fn callable_direct_edge_sort_key(edge: &CallableDirectEdge) -> (Vec<Ty>, ExecutableSymbolSortKey) {
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
            sources.sort_by_key(delivered_value_source_sort_key);
            sources.dedup();
            let source = match sources.as_slice() {
                [source] => source.clone(),
                _ => TransportSource::Join(sources.into_boxed_slice()),
            };
            (join.value, source)
        })
        .collect()
}

/// Canonical structural order over the two `TransportSource` variants this
/// function ever constructs (`LocalValue`/`CallsiteReturn`, straight from
/// `DeliveredValueSource`). Sorting on this -- not on the `Debug` render --
/// makes `TransportSource::Join` identity a pure function of the source SET:
/// the same set of local values/callsite returns always canonicalizes to the
/// same slice regardless of which order the join discovered them in, so two
/// joins over the same set always compare equal and hash equal. The variant
/// tag plus its raw id is exactly the structural content a `Debug` string
/// would have spelled out, without allocating one per comparison.
fn delivered_value_source_sort_key(source: &TransportSource) -> (u8, u32) {
    match source {
        TransportSource::LocalValue(value) => (0, value.as_u32()),
        TransportSource::CallsiteReturn(callsite) => (1, callsite.as_u32()),
        other => unreachable!(
            "collect_delivered_value_sources only ever constructs LocalValue/CallsiteReturn sources, found {other:?}"
        ),
    }
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

fn local_clause_ids(body: &LoweredBody) -> Vec<u32> {
    let LoweredBody::Clauses { clauses, .. } = body else {
        return Vec::new();
    };
    (0..clauses.len() as u32).collect()
}

fn local_entry_ids(body: &LoweredBody) -> Vec<ControlEntryId> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    (0..entries.len() as u32).map(ControlEntryId::from_u32).collect()
}

fn collect_return_sources(
    body: &LoweredBody,
    reachable_clauses: &[u32],
    reachable_entries: &[ControlEntryId],
) -> Vec<TransportSource> {
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return Vec::new();
    };
    let reachable_entries = reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut out = Vec::new();
    for clause_id in reachable_clauses.iter().copied() {
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

fn collect_resume_entries(
    body: &LoweredBody,
    analysis: &ActivationAnalysis,
    original_entry_ids: &[ControlEntryId],
) -> Vec<ResumeEntry> {
    let LoweredBody::Clauses { entries, .. } = body else {
        return Vec::new();
    };
    let reachable_entries = analysis.reachable_entries.iter().copied().collect::<HashSet<_>>();
    let mut deliver_callsites = HashMap::new();
    for (entry_index, entry) in entries.iter().enumerate() {
        let source_entry = original_entry_id_from(original_entry_ids, entry_index);
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
            let target = original_entry_id_from(original_entry_ids, target.as_u32() as usize);
            deliver_callsites.insert(target, callsite);
        }
    }
    entries
        .iter()
        .enumerate()
        .filter_map(|(index, entry)| {
            let entry_id = original_entry_id_from(original_entry_ids, index);
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

fn original_entry_id(context: &ExecutableContext, entry_index: usize) -> ControlEntryId {
    original_entry_id_from(&context.original_entry_ids, entry_index)
}

fn original_entry_id_from(original_entry_ids: &[ControlEntryId], entry_index: usize) -> ControlEntryId {
    original_entry_ids
        .get(entry_index)
        .copied()
        .unwrap_or_else(|| ControlEntryId::from_u32(entry_index as u32))
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
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
    executable: &ExecutableKey,
    semantic_index: usize,
) -> Option<Vec<TransportPosition>> {
    let positions = contexts
        .incoming_inputs(executable, semantic_index)
        .iter()
        .map(|(producer, value)| TransportPosition::Value {
            executable: executable_symbol(producer, world.types()),
            value: *value,
        })
        .collect::<Vec<_>>();
    (!positions.is_empty()).then_some(positions)
}

fn shape_for_source(
    world: &mut World<'_>,
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    ty: Ty,
    demand: &RuntimeDemand,
    semantic_index: usize,
    publication: Option<TransportPosition>,
    cycle: &mut Cycle,
    memo: &mut ProjectionMemo,
) -> SourceShape {
    let sources = contexts.incoming_inputs(executable, semantic_index);
    if sources.is_empty() {
        return SourceShape::Unknown;
    }

    let mut delta = TransportFactsBuilder::default();
    let mut exact = Vec::new();
    let mut recursive = false;
    let mut unknown = false;
    for (source_executable, value) in sources {
        let Some(source_context) = contexts.context_for(source_executable) else {
            unknown = true;
            continue;
        };
        let Some(source_ty) = source_context.analysis.value_types.get(value).copied() else {
            unknown = true;
            continue;
        };
        let projected = project_source(
            world,
            contexts,
            &mut delta,
            source_executable,
            source_context,
            source_ty,
            demand,
            TransportSource::LocalValue(*value),
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

fn project_tuple_value(
    world: &mut World<'_>,
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
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
        return SourceShape::Unknown;
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
    contexts: &TransportContexts,
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
                let Some(target_context) = contexts.context_for(&target) else {
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
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
    capture_tys: &[Ty],
    resolutions: &[ExecutableSymbol],
    types: &Types,
) -> Vec<RuntimeDemand> {
    let mut demands = vec![RuntimeDemand::ignore(); capture_tys.len()];
    for resolution in resolutions {
        let Some((_, context)) = contexts.context_for_symbol(resolution, types) else {
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
    rendered.sort_by_cached_key(|surface| surface.iter().map(|shape| shape.as_u32()).collect::<Vec<_>>());
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
                            callable,
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
                                    callable,
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

/// A source boundary's resolutions belong on a target boundary only when the
/// two share callable identity. Boundaries are matched by *layout* elsewhere
/// (surface arg shapes + return shape), so two first-class closures that close
/// over different captures of the same lambda surface (e.g. a reducer over
/// `gt2` vs `even`) look identical by layout but are interned as distinct
/// `CallableId`s carrying distinct capture shapes. A concrete (`function: Some`)
/// target therefore admits a source only when their interned callables agree; a
/// generic (`function: None`) dispatch target still pools every concrete
/// producer that flows through it, because that boundary's whole job is to
/// dispatch the union.
fn source_callable_admitted_by_target(world: &World<'_>, source: CallableId, target: CallableId) -> bool {
    if source == target {
        return true;
    }
    let target_descr = world.callable(target);
    let source_descr = world.callable(source);
    // A generic dispatch boundary on either side pools the union: a generic
    // target collects every concrete producer, and a concrete target can be fed
    // by an upstream generic carrier it was specialized from.
    target_descr.function.is_none() || source_descr.function.is_none()
}

fn resolution_symbols_for_callable_source_surfaces(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_shapes: &[ShapeId],
    surface_shapes: &[Box<[ShapeId]>],
    return_shapes: &[ShapeId],
    target_callable: CallableId,
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
            resolution_symbols_for_callable_source_surface(
                world,
                facts,
                source_shapes,
                arg_shapes,
                return_shape,
                target_callable,
            )
        })
        .collect()
}

fn resolution_symbols_for_callable_source_surface(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_shapes: &[ShapeId],
    arg_shapes: &[ShapeId],
    return_shape: ShapeId,
    target_callable: CallableId,
) -> Vec<ExecutableSymbol> {
    let mut resolutions = Vec::new();
    for shape in source_shapes {
        let ShapeDescr::Callable(callable) = world.shape(*shape) else {
            continue;
        };
        if !source_callable_admitted_by_target(world, *callable, target_callable) {
            continue;
        }
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
    target_callable: CallableId,
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
            resolution_symbols_for_source_publications(
                world,
                facts,
                source_positions,
                arg_shapes,
                return_shape,
                target_callable,
            )
        })
        .collect()
}

fn resolution_symbols_for_source_publications(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    source_positions: &[TransportPosition],
    arg_shapes: &[ShapeId],
    return_shape: ShapeId,
    target_callable: CallableId,
) -> Vec<ExecutableSymbol> {
    let mut resolutions = Vec::new();
    for source in source_positions {
        for (boundary, draft) in &facts.boundaries {
            if !draft.publications.contains(source) {
                continue;
            }
            let boundary_descr = world.boundary(*boundary);
            if !source_callable_admitted_by_target(world, boundary_descr.callable, target_callable) {
                continue;
            }
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
    contexts: &TransportContexts,
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
    contexts: &TransportContexts,
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
            let Some((_, context)) = contexts.context_for_symbol(resolution, world.types()) else {
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
    contexts: &TransportContexts,
    facts: &mut TransportFactsBuilder,
    resolution: &ExecutableSymbol,
    fallback_return_ty: Ty,
    memo: &mut ProjectionMemo,
) -> ShapeId {
    let Some((executable, context)) = contexts.context_for_symbol(resolution, world.types()) else {
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
    contexts: &TransportContexts,
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

    fn fake_executable(world: &mut World<'_>, root: u32, function: u32, inputs: &[Ty]) -> ExecutableKey {
        let activation = ActivationKey::from_inputs(
            RootId::for_test(root),
            FunctionId::for_test(function),
            inputs,
            world.types_mut(),
        );
        ExecutableKey {
            activation,
            need: ExecutableNeed::Value,
        }
    }

    #[test]
    fn executable_key_for_transport_position_roundtrips_recursive_union_key() {
        // The reconstruction site re-mints an ExecutableKey from a transport
        // position's symbol via `from_inputs`. For a RECURSIVE activation whose
        // input is a tuple union, the key arrow is the convergence-collapsed
        // evidence (the recursive branch of `World::canonical_activation_key`).
        // That collapsed arrow MUST already be canonically addressed so the
        // reconstruction recovers the SAME key; otherwise the transport cone
        // never anchors the input and native lowering reports an omitted semantic
        // input (fz-go4.18.3.2.1). This guards the actual site where the defect
        // lived, so a future change to symbol minting cannot silently reintroduce
        // it.
        use crate::compiler2::keying::DispatchDemand;
        use crate::types::TypeVarId;
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let root = RootId::for_test(7);
        let function = FunctionId::for_test(185);

        // Evidence input: {:cont, {[T], int}} | {:halt, {[T], int}} — the reducer
        // continuation union whose shared list element triggered the defect.
        let t = world.types_mut();
        let elem = t.type_var(TypeVarId(0));
        let inner = {
            let list = t.list(elem);
            let int = t.int();
            t.tuple(&[list, int])
        };
        let cont = {
            let tag = t.atom_lit("cont");
            t.tuple(&[tag, inner])
        };
        let halt = {
            let tag = t.atom_lit("halt");
            t.tuple(&[tag, inner])
        };
        let union = t.union(cont, halt);

        // Mint the recursive dispatch key as `canonical_activation_key` does:
        // address the evidence, then collapse non-dispatch subtrees. The tag
        // (field 0) dispatches; the payload (field 1) is ignored and collapses.
        let base = ActivationKey::from_inputs(root, function, &[union], t);
        let mut fields = std::collections::BTreeMap::new();
        fields.insert(0, DispatchDemand::Whole);
        let arrow = t.convergence_collapse(base.arrow, &[DispatchDemand::TupleFields(fields)]);
        let key = ExecutableKey {
            activation: ActivationKey { arrow, ..base },
            need: ExecutableNeed::Value,
        };

        // Production symbol mint, then the reconstruction site under test.
        let symbol = executable_symbol(&key, t);
        let position = TransportPosition::ExecutableInput {
            executable: symbol,
            semantic_index: 0,
        };
        let reconstructed = executable_key_for_transport_position(root, &position, t);

        assert_eq!(
            reconstructed, key,
            "reconstructing a recursive tuple-union executable key must recover the minted key"
        );
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
    fn incoming_input_positions_are_derived_from_slot_sources() {
        let tel = ConfiguredTelemetry::new();
        let mut world = World::new(&tel);
        let int = world.types_mut().int();
        let producer = fake_executable(&mut world, 81, 82, &[]);
        let callee = fake_executable(&mut world, 81, 83, &[int]);
        let value = ValueId::from_u32(9);
        let mut contexts = TransportContexts::default();
        contexts
            .incoming_input_sources
            .insert((callee.clone(), 0), vec![(producer.clone(), value)]);

        let positions = incoming_executable_input_positions(&world, &contexts, &callee, 0)
            .expect("slot source should produce one incoming input position");

        assert_eq!(
            positions,
            vec![TransportPosition::Value {
                executable: executable_symbol(&producer, world.types()),
                value,
            }],
            "input source positions should come from the produced slot source, not from scanning caller contexts"
        );
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
}
