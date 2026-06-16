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
    RuntimeDemand, SelectedCallee,
};
use super::super::transport::{
    ActivationSymbol, BoundaryDescr, BoundaryFacts, BoundaryId, CallableDescr, CallableFacts, CallableId,
    CodegenLaneRepr, CodegenSeam, CodegenSeamFact, ExecutableSymbol, LaneId, ShapeDescr, ShapeId, TransportClass,
    TransportPlan, TransportPosition,
};
use super::super::types::Ty;
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

#[derive(Debug, Clone, PartialEq, Eq)]
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

#[derive(Debug, Clone, PartialEq, Eq)]
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
    boundary_ids: Vec<BoundaryId>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
struct BoundaryFactsDraft {
    publications: Vec<TransportPosition>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SourceShape {
    Exact(ShapeId),
    Recursive,
    Unknown,
}

#[derive(Debug, Clone, Default)]
struct TransportFactsBuilder {
    callables: HashMap<CallableId, CallableFactsDraft>,
    boundaries: HashMap<BoundaryId, BoundaryFactsDraft>,
}

#[derive(Debug, Clone, Default)]
struct ShapeConstraintGraph {
    anchors: Vec<(TransportPosition, ShapeId)>,
    equalities: Vec<(TransportPosition, TransportPosition)>,
}

impl ShapeConstraintGraph {
    fn anchor(&mut self, position: TransportPosition, shape: ShapeId) {
        self.anchors.push((position, shape));
    }

    fn equal(&mut self, left: TransportPosition, right: TransportPosition) {
        self.equalities.push((left, right));
    }

    fn has_anchor(&self, position: &TransportPosition) -> bool {
        self.anchors.iter().any(|(anchored, _)| anchored == position)
    }

    fn solve(self) -> HashMap<TransportPosition, ShapeId> {
        let mut union = PositionUnion::default();
        for (position, _) in &self.anchors {
            union.add(position.clone());
        }
        for (left, right) in &self.equalities {
            union.union(left.clone(), right.clone());
        }

        let mut component_shapes = HashMap::<usize, ShapeId>::new();
        for (position, shape) in &self.anchors {
            let root = union.find_existing(position);
            if let Some(existing) = component_shapes.insert(root, *shape) {
                assert_eq!(
                    existing, *shape,
                    "transport shape anchors disagree for connected position component: {position:?}"
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
        for (left, right) in &self.equalities {
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
        boundary_ids: Vec<BoundaryId>,
    ) {
        let entry = self.callables.entry(callable).or_insert_with(|| CallableFactsDraft {
            resolutions: Vec::new(),
            direct_surfaces: Vec::new(),
            boundary_ids: Vec::new(),
        });
        extend_unique(&mut entry.resolutions, resolutions);
        extend_unique(&mut entry.direct_surfaces, direct_surfaces);
        extend_unique(&mut entry.boundary_ids, boundary_ids);
    }

    fn record_boundary(&mut self, boundary: BoundaryId, publication: TransportPosition) {
        let entry = self.boundaries.entry(boundary).or_insert_with(|| BoundaryFactsDraft {
            publications: Vec::new(),
        });
        if !entry.publications.contains(&publication) {
            entry.publications.push(publication);
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
                draft.boundary_ids.sort_by_key(|boundary| boundary.as_u32());
                (
                    id,
                    CallableFacts {
                        resolutions: draft.resolutions.into_boxed_slice(),
                        direct_surfaces: draft.direct_surfaces.into_boxed_slice(),
                        boundary_ids: draft.boundary_ids.into_boxed_slice(),
                    },
                )
            })
            .collect();
        let boundaries = self
            .boundaries
            .into_iter()
            .map(|(id, draft)| {
                (
                    id,
                    BoundaryFacts {
                        publications: draft.publications.into_boxed_slice(),
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
        let runtime_demand = closure.runtime_demands.get(executable).cloned().unwrap_or_default();
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

    if !wait_facts.is_empty() {
        return Ok(JobEffects {
            reads: settled_uses(reads),
            waits: settled_uses(wait_facts),
            follow_up: vec![Job::DeriveTransportPlan(root_id)],
            ..JobEffects::default()
        });
    }

    let mut executables = closure.executables.into_iter().collect::<Vec<_>>();
    executables.sort_by_key(executable_sort_key);

    let entry = executable_symbol(&closure.entry);
    let executable_membership = executables
        .iter()
        .map(executable_symbol)
        .collect::<Vec<_>>()
        .into_boxed_slice();

    let mut facts = TransportFactsBuilder::default();
    let mut shape_graph = ShapeConstraintGraph::default();
    for executable in &executables {
        let symbol = executable_symbol(executable);
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        let clause_params = clause_parameter_values(&context.body);

        let return_position = TransportPosition::ExecutableReturn {
            executable: symbol.clone(),
        };
        let return_shape = shape_for_source(
            world,
            &contexts,
            &mut facts,
            executable,
            context,
            context.return_ty,
            &context.runtime_demand.return_demand,
            TransportSource::ExecutableReturn,
            Some(return_position.clone()),
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
                &contexts,
                &mut facts,
                executable,
                context,
                value,
                ty,
                &demand,
                Some(TransportPosition::Value {
                    executable: symbol.clone(),
                    value,
                }),
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
                    let shape = generic_shape_from_demand(world, ty, &demand, &mut facts, Some(position.clone()));
                    shape_graph.anchor(position, shape);
                }
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
                .and_then(|callsite| resume_callee_return_position(world, &contexts, executable, context, callsite));
            if let Some(callee_return) = shared_return {
                shape_graph.equal(position, callee_return);
            } else {
                let shape = resume_shape(
                    world,
                    &contexts,
                    &mut facts,
                    executable,
                    context,
                    *resume,
                    &demand,
                    Some(position.clone()),
                );
                shape_graph.anchor(position, shape);
            }
        }
    }

    collect_clause_parameter_equalities(&contexts, &executables, &mut shape_graph);
    seed_callable_resolution_capture_inputs(world, &facts, &mut shape_graph);
    let local_shapes = shape_graph.clone().solve();
    collect_executable_input_constraints(
        world,
        &contexts,
        &mut facts,
        &executables,
        &local_shapes,
        &mut shape_graph,
    );
    let equivalents = shape_graph.equivalent_positions();
    let positions = shape_graph.solve();
    facts.expand_boundary_publications(&equivalents);

    let (callables, boundaries) = facts.finish();
    let codegen_seam_facts = derive_codegen_seam_facts(world, &contexts, &positions, &callables, &boundaries);

    let changed = world.define_transport_plan(
        root_id,
        TransportPlan {
            entry,
            executable_membership,
            positions,
            callables,
            boundaries,
            codegen_seam_facts,
        },
    );

    Ok(JobEffects {
        reads: settled_uses(reads),
        outputs: vec![FactKey::TransportPlan(root_id)],
        changed: changed.then_some(FactKey::TransportPlan(root_id)).into_iter().collect(),
        ..JobEffects::default()
    })
}

fn seed_callable_resolution_capture_inputs(
    world: &World<'_>,
    facts: &TransportFactsBuilder,
    shape_graph: &mut ShapeConstraintGraph,
) {
    for (callable, draft) in &facts.callables {
        let descr = world.transport().interners().callable(*callable);
        for resolution in &draft.resolutions {
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
    for executable in executables {
        let symbol = executable_symbol(executable);
        let context = contexts
            .get(executable)
            .expect("transport derivation requires one context per settled executable");
        for (semantic_index, ty) in executable.activation.input.iter().copied().enumerate() {
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
            if executable_input_demand_requires_own_shape(&demand) && !shape_graph.has_anchor(&position) {
                let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                shape_graph.anchor(position, shape);
                continue;
            }
            if let Some(incoming) = incoming_executable_input_positions(world, contexts, executable, semantic_index) {
                let incoming_shapes = incoming
                    .iter()
                    .map(|call_arg| local_shapes.get(call_arg).copied())
                    .collect::<Option<Vec<_>>>();
                if let Some(incoming_shapes) = incoming_shapes {
                    let first = incoming_shapes.first().copied();
                    if first.is_some() && incoming_shapes.iter().all(|shape| Some(*shape) == first) {
                        for call_arg in incoming {
                            shape_graph.equal(position.clone(), call_arg);
                        }
                    } else if !shape_graph.has_anchor(&position) {
                        let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                        shape_graph.anchor(position, shape);
                    }
                } else {
                    for call_arg in incoming {
                        shape_graph.equal(position.clone(), call_arg);
                    }
                }
            } else if !shape_graph.has_anchor(&position) {
                let shape = shape_for_executable_input(world, ty, &demand, facts, Some(position.clone()));
                shape_graph.anchor(position, shape);
            }
        }
    }
}

fn executable_input_demand_requires_own_shape(demand: &RuntimeDemand) -> bool {
    match demand {
        RuntimeDemand::Ignore => false,
        RuntimeDemand::Value | RuntimeDemand::TupleFields(_) => true,
        RuntimeDemand::Callable(callable) => callable.opaque || callable.escape,
    }
}

fn collect_clause_parameter_equalities(
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    executables: &[ExecutableKey],
    shape_graph: &mut ShapeConstraintGraph,
) {
    for executable in executables {
        let symbol = executable_symbol(executable);
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
    callables: &HashMap<CallableId, CallableFacts>,
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
                    if executable_context_for_symbol(contexts, executable)
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
                    if executable_context_for_symbol(contexts, executable)
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
                    if let Some(callsite) = executable_context_for_symbol(contexts, executable)
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
                    if executable_context_for_symbol(contexts, executable)
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
        let descr = world.transport().interners().boundary(boundary);
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
                repr: CodegenLaneRepr::ValueRef,
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
                    TransportPosition::ResumePayload {
                        executable,
                        callsite: None,
                        entry,
                    }
                    | TransportPosition::EntryCapture { executable, entry, .. } => {
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
                    TransportPosition::ExecutableReturn { .. }
                    | TransportPosition::CallArg { .. }
                    | TransportPosition::Value { .. } => {}
                }
            }
        }
    }
    for (callable, facts) in callables {
        let descr = world.transport().interners().callable(*callable);
        for (semantic_index, lane) in callable_function_entry_publication_lanes(world, descr) {
            for executable in facts.resolutions.iter() {
                out.push(CodegenSeamFact {
                    seam: CodegenSeam::FunctionEntry {
                        executable: executable.clone(),
                        semantic_index,
                    },
                    shape: None,
                    lane,
                    repr: CodegenLaneRepr::ValueRef,
                });
            }
        }
    }
    out.sort_by_key(codegen_seam_fact_sort_key);
    out.into_boxed_slice()
}

fn callable_function_entry_publication_lanes(world: &World<'_>, descr: &CallableDescr) -> Vec<(usize, LaneId)> {
    let mut lane_index = 0;
    let mut lanes = Vec::new();
    for (semantic_index, shape) in descr.capture_shapes.iter().copied().enumerate() {
        let structural_width = lanes_for_codegen_seam_shape(world, shape).len();
        if structural_width == 0 && lane_index < descr.capture_lanes.len() {
            lanes.push((semantic_index, descr.capture_lanes[lane_index]));
            lane_index += 1;
        } else {
            lane_index += structural_width;
        }
    }
    lanes
}

/// The `ExecutableReturn` position a call resume is delivered from, when the
/// call settles to exactly one known callee executable. A delivered resume and
/// the producing return are the same runtime value, so they share one
/// `ShapeId`: the resume position is unioned with the callee return position
/// rather than re-projected through the caller's (possibly `Ignore`) demand. A
/// caller that ignores or narrows the result settles that locally; it never
/// mutates the transported return shape.
fn resume_callee_return_position(
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
            executable: executable_symbol(&callee),
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
) -> Option<&'a ExecutableContext> {
    contexts.iter().find_map(|(candidate, context)| {
        (candidate.need == symbol.need
            && candidate.activation.function == symbol.activation.function
            && candidate.activation.input.as_slice() == symbol.activation.input.as_ref())
        .then_some(context)
    })
}

fn lanes_for_codegen_seam_shape(world: &World<'_>, shape: ShapeId) -> Vec<(ShapeId, LaneId)> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => Vec::new(),
        ShapeDescr::Lane(lane) => vec![(shape, *lane)],
        ShapeDescr::Callable(callable) => world
            .transport()
            .interners()
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
    let ty = world.transport().interners().lane(lane).ty;
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
        CodegenSeam::TailCall { executable, callsite } => (
            4,
            executable_symbol_sort_key(executable),
            0,
            0,
            callsite.as_u32() as usize,
        ),
        CodegenSeam::CallableBoundary { boundary } => (5, empty_executable_sort_key(), boundary.as_u32(), 0, 0),
        CodegenSeam::ExternBoundary { executable } => (6, executable_symbol_sort_key(executable), 0, 0, 0),
        CodegenSeam::FirstClassPublication { boundary } => (7, empty_executable_sort_key(), boundary.as_u32(), 0, 0),
    };
    let repr = match fact.repr {
        CodegenLaneRepr::ValueRef => 0,
        CodegenLaneRepr::RawInt => 1,
        CodegenLaneRepr::RawF64 => 2,
        CodegenLaneRepr::RawAtom => 3,
    };
    (kind, executable, boundary, entry, index, fact.lane.as_u32(), repr)
}

fn executable_sort_key(executable: &ExecutableKey) -> ExecutableSortKey {
    let need = match executable.need {
        ExecutableNeed::Value => (0, 0),
        ExecutableNeed::TupleFields(arity) => (1, arity),
    };
    (
        executable.activation.function.as_u32(),
        executable.activation.input.clone(),
        need.0,
        need.1,
    )
}

fn executable_symbol(executable: &ExecutableKey) -> ExecutableSymbol {
    ExecutableSymbol {
        activation: ActivationSymbol {
            function: executable.activation.function,
            input: executable.activation.input.clone().into_boxed_slice(),
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
    for entry in entries {
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
            if !reachable_entries.contains(&entry_id) {
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
) -> ShapeId {
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
    )
}

fn shape_for_executable_input(
    world: &mut World<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    let RuntimeDemand::Callable(callable) = demand else {
        return generic_shape_from_demand(world, ty, demand, facts, publication);
    };
    let surfaces = callable.resolved.clone();
    generic_callable_shape(world, ty, callable, &surfaces, facts, publication)
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
                target.activation.as_ref().is_some_and(|activation| {
                    activation.function == executable.activation.function
                        && activation.input == executable.activation.input
                        && context
                            .callsite_needs
                            .get(callsite)
                            .copied()
                            .unwrap_or(ExecutableNeed::Value)
                            == executable.need
                })
            }) {
                continue;
            }

            let capture_prefix = executable.activation.input.len().checked_sub(args.len())?;
            if semantic_index < capture_prefix {
                return None;
            }
            let arg_index = semantic_index - capture_prefix;
            let position = TransportPosition::CallArg {
                executable: executable_symbol(caller),
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
) -> ShapeId {
    let mut staged = facts.clone();
    match project_source(
        world,
        contexts,
        &mut staged,
        executable,
        context,
        ty,
        demand,
        source,
        publication.clone(),
        &mut Vec::new(),
    ) {
        SourceShape::Exact(shape) => {
            *facts = staged;
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
    visiting: &mut Vec<(ExecutableKey, TransportSource, RuntimeDemand)>,
) -> SourceShape {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return SourceShape::Exact(world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing));
    }
    let frame = (executable.clone(), source.clone(), demand.clone());
    if visiting.contains(&frame) {
        return SourceShape::Recursive;
    }
    visiting.push(frame);
    let projected = match source {
        TransportSource::ExecutableReturn => project_sources(
            world,
            contexts,
            facts,
            executable,
            context,
            ty,
            demand,
            &context.return_sources,
            publication,
            visiting,
        ),
        TransportSource::ExecutableInput(semantic_index) => {
            project_executable_input_source(world, contexts, facts, executable, ty, demand, semantic_index, visiting)
        }
        TransportSource::LocalValue(value) => match context.local_sources.get(&value).cloned() {
            Some(TransportSource::CallableValue(producer)) => project_callable_value(
                world,
                contexts,
                facts,
                executable,
                context,
                ty,
                demand,
                &producer,
                publication,
                context.runtime_demand.value_demands.get(&value),
                context.runtime_demand.callable_flows.get(&value),
            ),
            Some(source) => project_source(
                world,
                contexts,
                facts,
                executable,
                context,
                ty,
                demand,
                source,
                publication,
                visiting,
            ),
            None => SourceShape::Unknown,
        },
        TransportSource::CallsiteReturn(callsite) => {
            project_callsite_return(world, contexts, facts, executable, context, callsite, demand, visiting)
        }
        TransportSource::Join(sources) => project_sources(
            world,
            contexts,
            facts,
            executable,
            context,
            ty,
            demand,
            &sources,
            publication,
            visiting,
        ),
        TransportSource::TupleValue(items) => project_tuple_value(
            world, contexts, facts, executable, context, ty, demand, &items, visiting,
        ),
        TransportSource::TupleField { source, index } => project_tuple_field(
            world, contexts, facts, executable, context, demand, source, index, visiting,
        ),
        TransportSource::CallableValue(producer) => project_callable_value(
            world,
            contexts,
            facts,
            executable,
            context,
            ty,
            demand,
            &producer,
            publication,
            None,
            None,
        ),
    };
    visiting.pop();
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
    visiting: &mut Vec<(ExecutableKey, TransportSource, RuntimeDemand)>,
) -> SourceShape {
    let mut exact = Vec::new();
    let mut recursive = false;
    let mut staged = facts.clone();
    for source in sources {
        match project_source(
            world,
            contexts,
            &mut staged,
            executable,
            context,
            ty,
            demand,
            source.clone(),
            publication.clone(),
            visiting,
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
    if exact.windows(2).all(|pair| pair[0] == pair[1]) {
        *facts = staged;
        SourceShape::Exact(exact[0])
    } else {
        if matches!(demand, RuntimeDemand::Callable(callable) if callable.opaque || callable.escape) {
            *facts = staged;
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
    visiting: &mut Vec<(ExecutableKey, TransportSource, RuntimeDemand)>,
) -> SourceShape {
    let mut sources = Vec::new();
    collect_call_arg_input_sources(world, contexts, executable, semantic_index, &mut sources);
    collect_callable_capture_input_sources(contexts, executable, semantic_index, &mut sources);
    if sources.is_empty() {
        return SourceShape::Unknown;
    }

    let mut staged = facts.clone();
    let mut exact = Vec::new();
    let mut recursive = false;
    for (source_executable, value) in sources {
        let Some(source_context) = contexts.get(&source_executable) else {
            return SourceShape::Unknown;
        };
        let Some(source_ty) = source_context.analysis.value_types.get(&value).copied() else {
            return SourceShape::Unknown;
        };
        match project_source(
            world,
            contexts,
            &mut staged,
            &source_executable,
            source_context,
            source_ty,
            demand,
            TransportSource::LocalValue(value),
            None,
            visiting,
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
    if exact.windows(2).all(|pair| pair[0] == pair[1]) {
        *facts = staged;
        SourceShape::Exact(exact[0])
    } else if exact
        .iter()
        .all(|shape| matches!(world.transport().interners().shape(*shape), ShapeDescr::Nothing))
    {
        SourceShape::Exact(generic_shape_from_demand(
            world,
            ty,
            &RuntimeDemand::Ignore,
            facts,
            None,
        ))
    } else {
        SourceShape::Unknown
    }
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
            let Some(capture_prefix) = executable.activation.input.len().checked_sub(args.len()) else {
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
                        && activation.input == executable.activation.input
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
    visiting: &mut Vec<(ExecutableKey, TransportSource, RuntimeDemand)>,
) -> SourceShape {
    let RuntimeDemand::TupleFields(fields) = demand else {
        return SourceShape::Unknown;
    };
    if items.len() != fields.len() {
        return SourceShape::Unknown;
    }
    let field_tys = tuple_field_tys(world, ty, fields.len());
    let mut item_shapes = Vec::with_capacity(items.len());
    for (item, (item_ty, field_demand)) in items.iter().copied().zip(field_tys.into_iter().zip(fields.iter())) {
        let mut staged = facts.clone();
        let shape = match project_source(
            world,
            contexts,
            &mut staged,
            executable,
            context,
            item_ty,
            field_demand,
            TransportSource::LocalValue(item),
            None,
            visiting,
        ) {
            SourceShape::Exact(shape) => {
                *facts = staged;
                shape
            }
            SourceShape::Recursive | SourceShape::Unknown => {
                generic_shape_from_demand(world, item_ty, field_demand, facts, None)
            }
        };
        item_shapes.push(shape);
    }
    SourceShape::Exact(
        world
            .transport_mut()
            .interners_mut()
            .intern_shape(ShapeDescr::Tuple(item_shapes.into_boxed_slice())),
    )
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
    visiting: &mut Vec<(ExecutableKey, TransportSource, RuntimeDemand)>,
) -> SourceShape {
    let Some(parent_ty) = context.analysis.value_types.get(&source).copied() else {
        return SourceShape::Unknown;
    };
    let mut fields = vec![RuntimeDemand::Ignore; index + 1];
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
        None,
        visiting,
    ) {
        SourceShape::Exact(shape) => shape,
        other => return other,
    };
    let ShapeDescr::Tuple(items) = world.transport().interners().shape(parent_shape) else {
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
    ) else {
        return SourceShape::Unknown;
    };
    SourceShape::Exact(
        world
            .transport_mut()
            .interners_mut()
            .intern_shape(ShapeDescr::Callable(callable)),
    )
}

fn project_callsite_return(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    executable: &ExecutableKey,
    context: &ExecutableContext,
    callsite: CallSiteId,
    demand: &RuntimeDemand,
    visiting: &mut Vec<(ExecutableKey, TransportSource, RuntimeDemand)>,
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
    let mut staged = facts.clone();
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
                    &mut staged,
                    &target,
                    target_context,
                    target_context.return_ty,
                    demand,
                    TransportSource::ExecutableReturn,
                    None,
                    visiting,
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
        *facts = staged;
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
        .map(executable_symbol)
        .collect::<Vec<_>>();
    let direct_surfaces = if direct_surface_demands.is_empty() {
        Vec::new()
    } else {
        surface_shapes(world, &direct_surface_demands, facts)
    };
    let capture_demands = capture_demands_for_resolutions(contexts, &capture_tys, &resolution_symbols);
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
    let callable = world.transport_mut().interners_mut().intern_callable(CallableDescr {
        function: Some(producer.function),
        capture_shapes: capture_shapes.into_boxed_slice(),
        capture_lanes: capture_lanes.clone().into_boxed_slice(),
        contract_surfaces: Box::default(),
    });
    let boundary_ids = if !boundary_surface_demands.is_empty() {
        let surface_arg_shapes = surface_shapes(world, &boundary_surface_demands, facts);
        let boundary_return_shapes = boundary_return_shapes_for_flow_surfaces(
            world,
            contexts,
            facts,
            upstream_flow,
            &capture_tys,
            &boundary_surface_demands,
        );
        publish_boundaries_for_callable(
            world,
            facts,
            callable,
            &boundary_surface_demands,
            &surface_arg_shapes,
            &capture_lanes,
            callable_ty,
            &boundary_return_shapes,
            publication,
        )
    } else {
        Vec::new()
    };
    facts.record_callable(callable, resolution_symbols, direct_surfaces, boundary_ids);
    Some(callable)
}

fn local_callable_transport_requested(demand: &RuntimeDemand, precise_demand: Option<&RuntimeDemand>) -> bool {
    matches!(precise_demand, Some(RuntimeDemand::Callable(_))) || matches!(demand, RuntimeDemand::Callable(_))
}

fn capture_demands_for_resolutions(
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    capture_tys: &[Ty],
    resolutions: &[ExecutableSymbol],
) -> Vec<RuntimeDemand> {
    let mut demands = vec![RuntimeDemand::Ignore; capture_tys.len()];
    for resolution in resolutions {
        let Some((_, context)) = contexts.iter().find(|(candidate, _)| {
            candidate.need == resolution.need
                && candidate.activation.function == resolution.activation.function
                && candidate.activation.input.as_slice() == resolution.activation.input.as_ref()
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

fn generic_shape_from_demand(
    world: &mut World<'_>,
    ty: Ty,
    demand: &RuntimeDemand,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    if demand.is_ignore() || world.types().is_empty(&ty) {
        return world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing);
    }
    match demand {
        RuntimeDemand::Ignore => world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing),
        RuntimeDemand::Value => value_lane_shape(world, ty),
        RuntimeDemand::TupleFields(fields) => {
            let items = tuple_field_tys(world, ty, fields.len())
                .into_iter()
                .zip(fields.iter())
                .map(|(field_ty, field_demand)| generic_shape_from_demand(world, field_ty, field_demand, facts, None))
                .collect::<Vec<_>>();
            world
                .transport_mut()
                .interners_mut()
                .intern_shape(ShapeDescr::Tuple(items.into_boxed_slice()))
        }
        RuntimeDemand::Callable(callable) => {
            let surfaces = callable.resolved.clone();
            generic_callable_shape(world, ty, callable, &surfaces, facts, publication)
        }
    }
}

fn generic_callable_shape(
    world: &mut World<'_>,
    ty: Ty,
    demand: &CallableDemand,
    surfaces: &BTreeSet<CallableSurface>,
    facts: &mut TransportFactsBuilder,
    publication: Option<TransportPosition>,
) -> ShapeId {
    assert!(
        !(demand.opaque || demand.escape) || !surfaces.is_empty(),
        "generic callable transport requires upstream callable surfaces for opaque or escaped demand"
    );
    let published_surface_shapes = surface_shapes(world, surfaces, facts);
    let callable = world.transport_mut().interners_mut().intern_callable(CallableDescr {
        function: None,
        capture_shapes: Box::default(),
        capture_lanes: Box::default(),
        contract_surfaces: published_surface_shapes.clone().into_boxed_slice(),
    });
    let boundary_ids = if !surfaces.is_empty() {
        let return_shapes = boundary_return_shapes_for_callable_surfaces(world, ty, surfaces, facts);
        publish_boundaries_for_callable(
            world,
            facts,
            callable,
            surfaces,
            &published_surface_shapes,
            &[],
            ty,
            &return_shapes,
            publication,
        )
    } else {
        Vec::new()
    };
    facts.record_callable(callable, Vec::new(), Vec::new(), boundary_ids);
    world
        .transport_mut()
        .interners_mut()
        .intern_shape(ShapeDescr::Callable(callable))
}

fn publish_boundaries_for_callable(
    world: &mut World<'_>,
    facts: &mut TransportFactsBuilder,
    callable: CallableId,
    surfaces: &BTreeSet<CallableSurface>,
    surface_shapes: &[Box<[ShapeId]>],
    capture_lanes: &[LaneId],
    callable_ty: Ty,
    return_shapes: &[ShapeId],
    publication: Option<TransportPosition>,
) -> Vec<BoundaryId> {
    assert_eq!(
        surfaces.len(),
        surface_shapes.len(),
        "boundary surface shapes must align with published surfaces"
    );
    assert_eq!(
        surfaces.len(),
        return_shapes.len(),
        "boundary return shapes must align with published surfaces"
    );
    let mut boundary_ids = Vec::new();
    for ((surface, arg_shapes), return_shape) in surfaces
        .iter()
        .zip(surface_shapes.iter())
        .zip(return_shapes.iter().copied())
    {
        let return_ty = boundary_return_ty_for_surface(world, callable_ty, surface);
        let return_lanes = boundary_lanes_for_shape(world, return_shape, return_ty).into_boxed_slice();
        let published_value_lane = value_lane(world, callable_ty);
        let arg_lanes = arg_shapes
            .iter()
            .copied()
            .zip(surface.inputs.iter().copied())
            .flat_map(|(shape, ty)| boundary_lanes_for_shape(world, shape, ty))
            .collect::<Vec<_>>();
        let boundary = world.transport_mut().interners_mut().intern_boundary(BoundaryDescr {
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
    if matches!(demand, RuntimeDemand::Callable(callable) if callable.opaque || callable.escape) {
        return vec![value_lane(world, ty)];
    }
    lanes_for_codegen_seam_shape(world, shape)
        .into_iter()
        .map(|(_, lane)| lane)
        .collect()
}

fn boundary_return_shape_for_ty(world: &mut World<'_>, ret_ty: Ty, facts: &mut TransportFactsBuilder) -> ShapeId {
    if world.types().is_empty(&ret_ty) {
        return world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing);
    }
    if let Some(fields) = exact_tuple_field_tys(world, ret_ty) {
        let field_shapes = fields
            .into_iter()
            .map(|field_ty| {
                let demand = boundary_runtime_demand(world, field_ty);
                generic_shape_from_demand(world, field_ty, &demand, facts, None)
            })
            .collect::<Vec<_>>();
        return world
            .transport_mut()
            .interners_mut()
            .intern_shape(ShapeDescr::Tuple(field_shapes.into_boxed_slice()));
    }
    let demand = boundary_runtime_demand(world, ret_ty);
    generic_shape_from_demand(world, ret_ty, &demand, facts, None)
}

fn boundary_return_shapes_for_flow_surfaces(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    flow: &CallableFlowFact,
    capture_tys: &[Ty],
    surfaces: &BTreeSet<CallableSurface>,
) -> Vec<ShapeId> {
    surfaces
        .iter()
        .map(|surface| {
            let mut inputs = capture_tys.to_vec();
            inputs.extend(surface.inputs.iter().copied());
            let resolution = flow
                .resolutions
                .iter()
                .find(|resolution| {
                    resolution.activation.function == flow.function
                        && resolution.activation.input.as_slice() == inputs.as_slice()
                })
                .map(executable_symbol)
                .unwrap_or_else(|| {
                    panic!("upstream callable-flow surface has no matching executable resolution: {surface:?}")
                });
            boundary_return_shape_for_resolution(world, contexts, facts, &resolution)
        })
        .collect()
}

fn boundary_return_shape_for_resolution(
    world: &mut World<'_>,
    contexts: &HashMap<ExecutableKey, ExecutableContext>,
    facts: &mut TransportFactsBuilder,
    resolution: &ExecutableSymbol,
) -> ShapeId {
    let Some((executable, context)) = contexts.iter().find(|(candidate, _)| {
        candidate.need == resolution.need
            && candidate.activation.function == resolution.activation.function
            && candidate.activation.input.as_slice() == resolution.activation.input.as_ref()
    }) else {
        panic!("upstream callable-flow resolution is outside the transport root context: {resolution:?}");
    };
    let demand = context.runtime_demand.return_demand.clone();
    shape_for_source(
        world,
        contexts,
        facts,
        executable,
        context,
        context.return_ty,
        &demand,
        TransportSource::ExecutableReturn,
        None,
    )
}

fn boundary_return_shapes_for_callable_surfaces(
    world: &mut World<'_>,
    callable_ty: Ty,
    surfaces: &BTreeSet<CallableSurface>,
    facts: &mut TransportFactsBuilder,
) -> Vec<ShapeId> {
    surfaces
        .iter()
        .map(|surface| boundary_return_shape_for_surface(world, callable_ty, surface, facts))
        .collect()
}

fn boundary_return_shape_for_surface(
    world: &mut World<'_>,
    callable_ty: Ty,
    surface: &CallableSurface,
    facts: &mut TransportFactsBuilder,
) -> ShapeId {
    let ret_ty = boundary_return_ty_for_surface(world, callable_ty, surface);
    boundary_return_shape_for_ty(world, ret_ty, facts)
}

fn boundary_return_ty_for_surface(world: &mut World<'_>, callable_ty: Ty, surface: &CallableSurface) -> Ty {
    let Some(clauses) = world.types_mut().callable_clauses(&callable_ty) else {
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
    match world.transport().interners().shape(shape).clone() {
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
    world
        .transport_mut()
        .interners_mut()
        .intern_shape(ShapeDescr::Lane(lane))
}

fn value_lane(world: &mut World<'_>, ty: Ty) -> LaneId {
    world
        .transport_mut()
        .interners_mut()
        .intern_lane(super::super::transport::LaneDescr {
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
        return RuntimeDemand::Value;
    };
    RuntimeDemand::callable(CallableDemand {
        resolved: clauses
            .into_iter()
            .map(|clause| CallableSurface::new(clause.args))
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
        let ShapeDescr::Lane(lane) = world.transport().interners().shape(shape) else {
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
        let left_shape = world.transport_mut().interners_mut().intern_shape(ShapeDescr::Nothing);
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
