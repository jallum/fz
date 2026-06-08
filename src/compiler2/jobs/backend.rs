//! Compiler2 backend-lowering jobs.
//!
//! This module turns one emission-ready closed root into one backend-owned
//! program. The result keeps function/clause structure, but every callsite now
//! points at settled executable inventory, every callable boundary carries its
//! required callable-entry inventory, and every extern callsite carries its
//! concrete wire classes.

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;

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

    let reads = vec![emission_ready_fact];
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
        executables,
        callable_entries,
    };
    let revision = world.define_backend_program(root_id, program);
    Ok(JobEffects {
        reads,
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
