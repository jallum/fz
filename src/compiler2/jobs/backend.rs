//! Compiler2 backend-lowering jobs.
//!
//! This module turns one emission-ready closed root into one backend-owned
//! program. The result keeps function/clause structure, but every callsite now
//! points at settled executable inventory, every callable boundary carries its
//! required callable-entry inventory, and every extern callsite carries its
//! concrete wire classes.

use std::collections::HashSet;

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::dispatch_matrix::{ComparisonValue, DispatchConst, DispatchNode, ProjectionKind, Region, SubjectSource};

use super::super::artifact::{
    BackendBlock, BackendBody, BackendCallArg, BackendCallableEntry, BackendClause, BackendExecutable, BackendProgram,
    BackendStep,
};
use super::super::body::{CallArg, CallSiteId, LoweredBlock, LoweredBody, LoweredClause, LoweredStep};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::facts::FactValue;
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::scheduler::FatalError;
use super::super::types::Ty;
use super::super::world::World;

/// Lowers one emission-ready closed root into the shared backend handoff.
///
/// The backend artifact consumes only `EmissionReadyProgram(root)` plus the
/// world-owned type store. It does not reopen semantic closure, planner state,
/// or backend-specific discovery.
pub(super) fn lower_backend_program(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let emission_ready_fact = FactKey::EmissionReadyProgram(root_id);
    let Some(emission_ready_revision) = world.fact_revision(emission_ready_fact.clone()) else {
        return Ok(JobEffects::wait_on(
            emission_ready_fact,
            [Job::DeriveEmissionReady(root_id)],
        ));
    };

    let emission_ready = world.emission_ready_program(root_id);
    let mut lowerer = BackendLowerer::new(world, root_id, &emission_ready);
    let executables = emission_ready
        .executables
        .iter()
        .map(|executable| lowerer.lower_executable(executable))
        .collect::<Result<Vec<_>, _>>()?;
    let callable_entries = emission_ready
        .callable_entries
        .iter()
        .map(|entry| BackendCallableEntry {
            target: entry.target,
            capture_count: entry.capture_count,
        })
        .collect();
    let program = BackendProgram {
        emission_ready_revision,
        entry: emission_ready.entry,
        atom_names: collect_backend_atom_names(lowerer.world, &executables),
        executables,
        callable_entries,
    };
    let revision = world.define_backend_program(root_id, program);
    Ok(JobEffects {
        reads: vec![emission_ready_fact],
        outputs: vec![(FactKey::BackendProgram(root_id), FactValue::presence(revision))],
        ..JobEffects::default()
    })
}

struct BackendLowerer<'a, 'tel> {
    world: &'a mut World<'tel>,
    root_id: RootId,
    program: &'a super::super::artifact::EmissionReadyProgram,
}

impl<'a, 'tel> BackendLowerer<'a, 'tel> {
    fn new(
        world: &'a mut World<'tel>,
        root_id: RootId,
        program: &'a super::super::artifact::EmissionReadyProgram,
    ) -> Self {
        Self {
            world,
            root_id,
            program,
        }
    }

    fn lower_executable(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
    ) -> Result<BackendExecutable, FatalError> {
        Ok(BackendExecutable {
            key: executable.key.clone(),
            entry_dispatch: executable.entry_dispatch.clone(),
            return_ty: executable.return_ty,
            return_abi: executable.return_abi.clone(),
            param_reprs: executable.param_reprs.clone(),
            value_types: executable.value_types.clone(),
            value_reprs: executable.value_reprs.clone(),
            effects: executable.effects,
            body: self.lower_body(executable)?,
        })
    }

    fn lower_body(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
    ) -> Result<BackendBody, FatalError> {
        match &executable.body {
            LoweredBody::Extern { signature } => Ok(BackendBody::Extern {
                signature: signature.clone(),
            }),
            LoweredBody::Clauses { clauses, generated } => Ok(BackendBody::Clauses {
                clauses: clauses
                    .iter()
                    .map(|clause| self.lower_clause(executable, clause))
                    .collect::<Result<Vec<_>, _>>()?,
                generated: generated.clone(),
            }),
        }
    }

    fn lower_clause(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        clause: &LoweredClause,
    ) -> Result<BackendClause, FatalError> {
        Ok(BackendClause {
            span: clause.span,
            params: clause.params.clone(),
            projections: clause
                .projections
                .iter()
                .map(|step| self.lower_step(executable, step))
                .collect::<Result<Vec<_>, _>>()?,
            body: self.lower_block(executable, &clause.body)?,
        })
    }

    fn lower_block(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        block: &LoweredBlock,
    ) -> Result<BackendBlock, FatalError> {
        Ok(BackendBlock {
            span: block.span,
            steps: block
                .steps
                .iter()
                .map(|step| self.lower_step(executable, step))
                .collect::<Result<Vec<_>, _>>()?,
            result: block.result,
        })
    }

    fn lower_step(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        step: &LoweredStep,
    ) -> Result<BackendStep, FatalError> {
        Ok(match step {
            LoweredStep::Const { value, literal } => BackendStep::Const {
                value: *value,
                literal: literal.clone(),
            },
            LoweredStep::Tuple { value, items } => BackendStep::Tuple {
                value: *value,
                items: items.clone(),
            },
            LoweredStep::List { value, items, tail } => BackendStep::List {
                value: *value,
                items: items.clone(),
                tail: *tail,
            },
            LoweredStep::FunctionRef { value, function } => BackendStep::FunctionRef {
                value: *value,
                function: *function,
            },
            LoweredStep::NamedFunctionRef { value, name, arity } => BackendStep::NamedFunctionRef {
                value: *value,
                name: name.clone(),
                arity: *arity,
            },
            LoweredStep::DirectCall {
                value, callsite, args, ..
            } => {
                let edge = call_edge(executable, *callsite).ok_or_else(|| {
                    incomplete_backend_program(
                        self.world,
                        self.root_id,
                        format!("missing settled direct-call edge for callsite {}", callsite.as_u32()),
                    )
                })?;
                BackendStep::DirectCall {
                    value: *value,
                    callsite: *callsite,
                    callee: edge.callee,
                    args: self.lower_call_args(executable, *callsite, None, args)?,
                    extern_marshals: edge.extern_marshals.clone(),
                }
            }
            LoweredStep::ClosureCall {
                value,
                callsite,
                callee,
                args,
            } => {
                let edge = call_edge(executable, *callsite).ok_or_else(|| {
                    incomplete_backend_program(
                        self.world,
                        self.root_id,
                        format!("missing settled closure-call edge for callsite {}", callsite.as_u32()),
                    )
                })?;
                BackendStep::ClosureCall {
                    value: *value,
                    callsite: *callsite,
                    callee: *callee,
                    target: edge.callee,
                    args: self.lower_call_args(executable, *callsite, Some(*callee), args)?,
                }
            }
            LoweredStep::Lambda {
                value,
                function,
                captures,
            } => BackendStep::Lambda {
                value: *value,
                function: *function,
                captures: captures.clone(),
            },
            LoweredStep::BinaryOp { value, op, left, right } => BackendStep::BinaryOp {
                value: *value,
                op: *op,
                left: *left,
                right: *right,
            },
            LoweredStep::UnaryOp { value, op, input } => BackendStep::UnaryOp {
                value: *value,
                op: *op,
                input: *input,
            },
            LoweredStep::MapIndex { value, base, key } => BackendStep::MapIndex {
                value: *value,
                base: *base,
                key: *key,
            },
            LoweredStep::If {
                value,
                cond,
                then_block,
                else_block,
            } => BackendStep::If {
                value: *value,
                cond: *cond,
                then_block: self.lower_block(executable, then_block)?,
                else_block: self.lower_block(executable, else_block)?,
            },
            LoweredStep::AssertLiteral { source, literal } => BackendStep::AssertLiteral {
                source: *source,
                literal: literal.clone(),
            },
            LoweredStep::AssertTuple { source, arity } => BackendStep::AssertTuple {
                source: *source,
                arity: *arity,
            },
            LoweredStep::TupleField { value, source, index } => BackendStep::TupleField {
                value: *value,
                source: *source,
                index: *index,
            },
            LoweredStep::AssertEmptyList { source } => BackendStep::AssertEmptyList { source: *source },
            LoweredStep::AssertSame { source, value } => BackendStep::AssertSame {
                source: *source,
                value: *value,
            },
            LoweredStep::SplitList { source, head, tail } => BackendStep::SplitList {
                source: *source,
                head: *head,
                tail: *tail,
            },
        })
    }

    fn lower_call_args(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        callsite: CallSiteId,
        closure_callee: Option<super::super::body::ValueId>,
        args: &[CallArg],
    ) -> Result<Vec<BackendCallArg>, FatalError> {
        args.iter()
            .enumerate()
            .map(|(arg_index, arg)| {
                let arg_ty = executable
                    .value_types
                    .get(&arg.value)
                    .copied()
                    .expect("emission-ready executables should carry settled types for every call argument value");
                let callable_entries = match self.resolve_callable_entries_for_type(arg_ty)? {
                    CallableResolution::NotCallable => {
                        if self.boundary_expects_callable(executable, callsite, closure_callee, arg_index) {
                            return Err(incomplete_backend_program(
                                self.world,
                                self.root_id,
                                format!(
                                    "callable boundary at callsite {} expects a resolved callable entry for arg {}",
                                    callsite.as_u32(),
                                    arg_index
                                ),
                            ));
                        }
                        Vec::new()
                    }
                    CallableResolution::Opaque => {
                        return Err(incomplete_backend_program(
                            self.world,
                            self.root_id,
                            format!(
                                "callable boundary at callsite {} carries an opaque callable arg {}",
                                callsite.as_u32(),
                                arg_index
                            ),
                        ));
                    }
                    CallableResolution::Resolved(entries) => entries,
                };
                Ok(BackendCallArg {
                    value: arg.value,
                    callable_entries,
                })
            })
            .collect()
    }

    fn boundary_expects_callable(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        callsite: CallSiteId,
        closure_callee: Option<super::super::body::ValueId>,
        arg_index: usize,
    ) -> bool {
        let Some(edge) = call_edge(executable, callsite) else {
            return false;
        };
        let offset = closure_callee
            .and_then(|callee| executable.value_types.get(&callee))
            .and_then(|callee_ty| self.world.types().closure_lit_parts(callee_ty))
            .map_or(0, |parts| parts.captures.len());
        let Some(expected_ty) = self.program.executables[edge.callee]
            .key
            .activation
            .input
            .get(offset + arg_index)
        else {
            return false;
        };
        self.world.types_mut().callable_clauses(expected_ty).is_some()
    }

    fn resolve_callable_entries_for_type(&mut self, ty: Ty) -> Result<CallableResolution, FatalError> {
        let Some(clauses) = self.world.types_mut().callable_clauses(&ty) else {
            return Ok(CallableResolution::NotCallable);
        };
        if clauses.is_empty() {
            return Ok(CallableResolution::NotCallable);
        }

        let mut entries = Vec::new();
        for clause in clauses {
            let Some(closure) = clause.closure else {
                return Ok(CallableResolution::Opaque);
            };
            let function = FunctionId::from_u32(closure.target.0);
            let capture_count = closure.captures.len();
            let fixed_arity = clause.args.len();
            let variadic = self.world.function_variadic(function);
            let mut matched = false;
            for (index, _entry) in self.program.callable_entries.iter().enumerate().filter(|(_, entry)| {
                let executable = &self.program.executables[entry.target];
                executable.key.activation.function == function
                    && executable.key.need == ExecutableNeed::Value
                    && has_capture_prefix(&executable.key.activation.input, &closure.captures)
                    && callable_entry_arity_matches(&executable.key, capture_count, fixed_arity, variadic)
            }) {
                matched = true;
                entries.push(index);
            }
            if !matched {
                return Err(incomplete_backend_program(
                    self.world,
                    self.root_id,
                    format!(
                        "callable entry target {} with {} capture(s) and arity {} is missing from backend inventory",
                        function.as_u32(),
                        capture_count,
                        fixed_arity
                    ),
                ));
            }
        }
        entries.sort_unstable();
        entries.dedup();
        Ok(CallableResolution::Resolved(entries))
    }
}

fn call_edge(
    executable: &super::super::artifact::EmissionReadyExecutable,
    callsite: CallSiteId,
) -> Option<&super::super::artifact::EmissionReadyCallEdge> {
    executable.call_edges.iter().find(|edge| edge.callsite == callsite)
}

fn has_capture_prefix(input: &[Ty], captures: &[Ty]) -> bool {
    input.starts_with(captures)
}

fn callable_entry_arity_matches(
    target: &ExecutableKey,
    capture_count: usize,
    fixed_arity: usize,
    variadic: bool,
) -> bool {
    let actual_arity = target.activation.input.len().saturating_sub(capture_count);
    if variadic {
        actual_arity >= fixed_arity
    } else {
        actual_arity == fixed_arity
    }
}

enum CallableResolution {
    NotCallable,
    Opaque,
    Resolved(Vec<usize>),
}

fn collect_backend_atom_names(world: &mut World<'_>, executables: &[BackendExecutable]) -> Vec<String> {
    let mut seen = HashSet::new();
    let mut atoms = Vec::new();
    for name in ["nil", "true", "false"] {
        push_atom(&mut seen, &mut atoms, name);
    }
    for executable in executables {
        collect_executable_atoms(world, executable, &mut seen, &mut atoms);
    }
    atoms
}

fn collect_executable_atoms(
    world: &mut World<'_>,
    executable: &BackendExecutable,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    match &executable.body {
        BackendBody::Extern { .. } => {}
        BackendBody::Clauses { clauses, .. } => {
            if let Some(dispatch) = &executable.entry_dispatch {
                collect_dispatch_atoms(world, dispatch.plan(), seen, atoms);
            }
            for clause in clauses {
                collect_step_atoms(world, &clause.projections, seen, atoms);
                collect_block_atoms(world, &clause.body, seen, atoms);
            }
        }
    }
}

fn collect_block_atoms(
    world: &mut World<'_>,
    block: &BackendBlock,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    collect_step_atoms(world, &block.steps, seen, atoms);
}

fn collect_step_atoms(
    world: &mut World<'_>,
    steps: &[BackendStep],
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    for step in steps {
        match step {
            BackendStep::Const { literal, .. } | BackendStep::AssertLiteral { literal, .. } => {
                collect_literal_atoms(literal, seen, atoms);
            }
            BackendStep::If {
                then_block, else_block, ..
            } => {
                collect_block_atoms(world, then_block, seen, atoms);
                collect_block_atoms(world, else_block, seen, atoms);
            }
            BackendStep::Tuple { .. }
            | BackendStep::List { .. }
            | BackendStep::FunctionRef { .. }
            | BackendStep::NamedFunctionRef { .. }
            | BackendStep::DirectCall { .. }
            | BackendStep::ClosureCall { .. }
            | BackendStep::Lambda { .. }
            | BackendStep::BinaryOp { .. }
            | BackendStep::UnaryOp { .. }
            | BackendStep::MapIndex { .. }
            | BackendStep::AssertTuple { .. }
            | BackendStep::TupleField { .. }
            | BackendStep::AssertEmptyList { .. }
            | BackendStep::AssertSame { .. }
            | BackendStep::SplitList { .. } => {}
        }
    }
}

fn collect_literal_atoms(literal: &super::super::body::Literal, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    if let super::super::body::Literal::Atom(name) = literal {
        push_atom(seen, atoms, name);
    }
}

fn collect_dispatch_atoms(
    world: &mut World<'_>,
    plan: &PatternDispatchPlan<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    for prepared in &plan.prepared_keys {
        collect_dispatch_const_atoms(prepared, seen, atoms);
    }
    for subject in &plan.matrix.subjects {
        match &subject.source {
            SubjectSource::Input { .. } => {}
            SubjectSource::Projection(projection) => {
                if let ProjectionKind::MapValue { key } = &projection.kind {
                    collect_dispatch_const_atoms(key, seen, atoms);
                }
            }
        }
    }
    for guard in &plan.guards {
        collect_guard_atoms(world, guard, seen, atoms);
    }
    collect_dispatch_graph_atoms(world, plan, plan.graph.root, seen, atoms);
}

fn collect_dispatch_graph_atoms(
    world: &mut World<'_>,
    plan: &PatternDispatchPlan<Ty>,
    node_id: crate::dispatch_matrix::GraphNodeId,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    let Some(node) = plan.graph.node(node_id) else {
        return;
    };
    match node {
        DispatchNode::Fail | DispatchNode::Outcome { .. } => {}
        DispatchNode::Test {
            predicate,
            on_match,
            on_miss,
        } => {
            collect_region_atoms(world, &predicate.region, seen, atoms);
            collect_dispatch_graph_atoms(world, plan, on_match.target, seen, atoms);
            collect_dispatch_graph_atoms(world, plan, on_miss.target, seen, atoms);
        }
    }
}

fn collect_region_atoms(
    world: &mut World<'_>,
    region: &Region<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    match region {
        Region::Equal(ComparisonValue::Const(value)) | Region::MapKeyPresent { key: value } => {
            collect_dispatch_const_atoms(value, seen, atoms);
        }
        Region::Type(ty) => {
            for atom in world.types().atom_literals(ty) {
                push_atom(seen, atoms, &atom);
            }
        }
        Region::Equal(ComparisonValue::Pinned(_))
        | Region::TupleArity(_)
        | Region::List(_)
        | Region::MapKind
        | Region::Bitstring(_)
        | Region::Guard(_)
        | Region::Any
        | Region::Never => {}
    }
}

fn collect_guard_atoms(
    world: &mut World<'_>,
    expr: &PatternGuardExpr<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    match expr {
        PatternGuardExpr::Const(value) => collect_dispatch_const_atoms(value, seen, atoms),
        PatternGuardExpr::Unary { expr, .. } => collect_guard_atoms(world, expr, seen, atoms),
        PatternGuardExpr::Binary { lhs, rhs, .. } => {
            collect_guard_atoms(world, lhs, seen, atoms);
            collect_guard_atoms(world, rhs, seen, atoms);
        }
        PatternGuardExpr::Dispatch { inputs, dispatch } => {
            for input in inputs {
                collect_guard_atoms(world, input, seen, atoms);
            }
            collect_guard_dispatch_atoms(world, dispatch, seen, atoms);
        }
        PatternGuardExpr::Subject(_) | PatternGuardExpr::Pinned(_) => {}
    }
}

fn collect_guard_dispatch_atoms(
    world: &mut World<'_>,
    dispatch: &PatternGuardDispatch<Ty>,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    collect_dispatch_atoms(world, &dispatch.plan, seen, atoms);
    for body in &dispatch.bodies {
        collect_guard_atoms(world, body, seen, atoms);
    }
}

fn collect_dispatch_const_atoms(value: &DispatchConst, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    if let DispatchConst::AtomName(name) = value {
        push_atom(seen, atoms, name);
    }
}

fn push_atom(seen: &mut HashSet<String>, atoms: &mut Vec<String>, name: &str) {
    if seen.insert(name.to_string()) {
        atoms.push(name.to_string());
    }
}

fn incomplete_backend_program(world: &World<'_>, root_id: RootId, message: impl Into<String>) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 backend lowering for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
