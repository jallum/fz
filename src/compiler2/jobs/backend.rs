//! Compiler2 backend-lowering jobs.
//!
//! This module turns one emission-ready closed root into one backend-owned
//! program. The result keeps function/clause structure, but every callsite now
//! points at settled executable inventory, every callable boundary carries its
//! required callable-entry inventory, and every extern callsite carries its
//! concrete wire classes.

use std::collections::{HashMap, HashSet};

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr};
use crate::dispatch_matrix::{ComparisonValue, DispatchConst, DispatchNode, ProjectionKind, Region, SubjectSource};

use super::super::artifact::{
    AbiValueRepr, BackendBody, BackendCallArg, BackendCallableEntry, BackendClause, BackendEntry, BackendEntryOrigin,
    BackendExecutable, BackendProgram, BackendStep, BackendTail, ReturnAbi,
};
use super::super::body::{
    CallArg, CallSiteId, ControlDestination, ControlEntryOrigin, LoweredBody, LoweredClause, LoweredEntry, LoweredStep,
    LoweredTail, ValueId,
};
use super::super::drive::{FactKey, Job, JobEffects};
use super::super::identity::{ExecutableKey, ExecutableNeed, RootId, function_id_of_closure_target};
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
            param_reprs: entry.param_reprs.clone(),
            return_ty: entry.return_ty,
            return_abi: entry.return_abi.clone(),
        })
        .collect();
    let program = BackendProgram {
        emission_ready_revision,
        entry: emission_ready.entry,
        atom_names: collect_backend_atom_names(lowerer.world, &executables),
        struct_schemas: lowerer.world.struct_schemas(),
        executables,
        callable_entries,
    };
    let backend_fact = FactKey::BackendProgram(root_id);
    let revision = world.define_backend_program(root_id, program);
    let changed = world.fact_would_change(backend_fact.clone(), revision);
    Ok(JobEffects {
        reads: vec![emission_ready_fact],
        outputs: vec![(backend_fact, revision)],
        follow_up: changed
            .then_some(Job::LowerNativeProgram(root_id))
            .into_iter()
            .collect(),
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
            LoweredBody::Clauses {
                clauses,
                entries,
                generated,
            } => {
                let resume_abis =
                    entry_input_abis(self.world, self.root_id, self.program, executable, entries, clauses)?;
                Ok(BackendBody::Clauses {
                    clauses: clauses
                        .iter()
                        .map(|clause| self.lower_clause(executable, clause))
                        .collect::<Result<Vec<_>, _>>()?,
                    entries: entries
                        .iter()
                        .enumerate()
                        .map(|(index, entry)| self.lower_entry(executable, index, entry, &resume_abis))
                        .collect::<Result<Vec<_>, _>>()?,
                    generated: generated.clone(),
                })
            }
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
            entry: clause.entry,
        })
    }

    fn lower_entry(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        entry_index: usize,
        entry: &LoweredEntry,
        resume_abis: &[Option<ReturnAbi>],
    ) -> Result<BackendEntry, FatalError> {
        Ok(BackendEntry {
            span: entry.span,
            origin: lower_entry_origin(entry_index, entry, resume_abis),
            params: entry.params.clone(),
            captures: entry.captures.clone(),
            steps: entry
                .steps
                .iter()
                .map(|step| self.lower_step(executable, step))
                .collect::<Result<Vec<_>, _>>()?,
            tail: self.lower_tail(executable, &entry.tail)?,
        })
    }

    fn lower_step(
        &mut self,
        _executable: &super::super::artifact::EmissionReadyExecutable,
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
            LoweredStep::Map { value, entries } => BackendStep::Map {
                value: *value,
                entries: entries.clone(),
            },
            LoweredStep::MapUpdate { value, base, entries } => BackendStep::MapUpdate {
                value: *value,
                base: *base,
                entries: entries.clone(),
            },
            LoweredStep::Struct { value, module, fields } => BackendStep::Struct {
                value: *value,
                module_name: self
                    .world
                    .module_name(*module)
                    .unwrap_or_else(|| panic!("struct module {} should have a name", module.as_u32()))
                    .to_string(),
                fields: fields.clone(),
            },
            LoweredStep::Bitstring { value, fields } => BackendStep::Bitstring {
                value: *value,
                fields: fields.clone(),
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
            LoweredStep::FieldAccess { value, base, field } => BackendStep::FieldAccess {
                value: *value,
                base: *base,
                field: field.clone(),
            },
            LoweredStep::AssertLiteral { source, literal } => BackendStep::AssertLiteral {
                source: *source,
                literal: literal.clone(),
            },
            LoweredStep::AssertStruct { source, module } => BackendStep::AssertStruct {
                source: *source,
                module_name: self
                    .world
                    .module_name(*module)
                    .unwrap_or_else(|| panic!("struct module {} should have a name", module.as_u32()))
                    .to_string(),
            },
            LoweredStep::RequireMapValue { value, source, key } => BackendStep::RequireMapValue {
                value: *value,
                source: *source,
                key: key.clone(),
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
            LoweredStep::BitstringInit { reader, source } => BackendStep::BitstringInit {
                reader: *reader,
                source: *source,
            },
            LoweredStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                is_last,
            } => BackendStep::BitstringRead {
                ok: *ok,
                value: *value,
                next_reader: *next_reader,
                reader: *reader,
                spec: spec.clone(),
                is_last: *is_last,
            },
            LoweredStep::AssertBitstringDone { reader } => BackendStep::AssertBitstringDone { reader: *reader },
        })
    }

    fn lower_tail(
        &mut self,
        executable: &super::super::artifact::EmissionReadyExecutable,
        tail: &LoweredTail,
    ) -> Result<BackendTail, FatalError> {
        Ok(match tail {
            LoweredTail::Value { value, dest } => BackendTail::Value {
                value: *value,
                dest: dest.clone(),
            },
            LoweredTail::DirectCall {
                value,
                callsite,
                args,
                dest,
                ..
            } => {
                let edge = call_edge(executable, *callsite).ok_or_else(|| {
                    incomplete_backend_program(
                        self.world,
                        self.root_id,
                        format!("missing settled direct-call edge for callsite {}", callsite.as_u32()),
                    )
                })?;
                BackendTail::DirectCall {
                    value: *value,
                    callsite: *callsite,
                    callee: edge.callee,
                    args: self.lower_call_args(executable, *callsite, None, args)?,
                    dest: dest.clone(),
                    extern_marshals: edge.extern_marshals.clone(),
                }
            }
            LoweredTail::ClosureCall {
                value,
                callsite,
                callee,
                args,
                dest,
            } => {
                let edge = call_edge(executable, *callsite).ok_or_else(|| {
                    incomplete_backend_program(
                        self.world,
                        self.root_id,
                        format!("missing settled closure-call edge for callsite {}", callsite.as_u32()),
                    )
                })?;
                BackendTail::ClosureCall {
                    value: *value,
                    callsite: *callsite,
                    callee: *callee,
                    target: edge.callee,
                    args: self.lower_call_args(executable, *callsite, Some(*callee), args)?,
                    dest: dest.clone(),
                }
            }
            LoweredTail::If {
                cond,
                then_entry,
                else_entry,
            } => BackendTail::If {
                cond: *cond,
                then_entry: *then_entry,
                else_entry: *else_entry,
            },
            LoweredTail::Dispatch {
                inputs,
                bindings,
                dispatch,
            } => BackendTail::Dispatch {
                inputs: inputs.clone(),
                bindings: bindings.clone(),
                dispatch: dispatch.clone(),
            },
            LoweredTail::Receive(receive) => BackendTail::Receive(Box::new(super::super::artifact::BackendReceive {
                bindings: receive.bindings.clone(),
                dispatch: receive.dispatch.clone(),
                clauses: receive.clauses.clone(),
                after: receive.after.clone(),
            })),
            LoweredTail::Halt { atom } => BackendTail::Halt { atom: atom.clone() },
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
        let Some(clauses) = self.world.types_mut().callable_value_clauses(&ty) else {
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
            let function = function_id_of_closure_target(closure.target);
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

fn lower_entry_origin(
    entry_index: usize,
    entry: &LoweredEntry,
    resume_abis: &[Option<ReturnAbi>],
) -> BackendEntryOrigin {
    match entry.origin {
        ControlEntryOrigin::Clause => BackendEntryOrigin::Clause,
        ControlEntryOrigin::Branch => BackendEntryOrigin::Branch,
        ControlEntryOrigin::Receive => BackendEntryOrigin::Receive,
        ControlEntryOrigin::CallResume { value } => BackendEntryOrigin::CallResume {
            value,
            return_abi: resume_abis[entry_index]
                .clone()
                .unwrap_or_else(|| panic!("resume entry {entry_index} should have a settled input ABI: {entry:?}")),
        },
        ControlEntryOrigin::LocalResume { value } => BackendEntryOrigin::LocalResume { value },
    }
}

fn entry_input_abis(
    world: &mut World<'_>,
    root_id: RootId,
    program: &super::super::artifact::EmissionReadyProgram,
    executable: &super::super::artifact::EmissionReadyExecutable,
    entries: &[LoweredEntry],
    clauses: &[LoweredClause],
) -> Result<Vec<Option<ReturnAbi>>, FatalError> {
    let mut needs = vec![None; entries.len()];
    for clause in clauses {
        let _ = collect_entry_input_need(
            world,
            executable,
            entries,
            clause.entry,
            executable.return_abi.clone(),
            &mut needs,
        );
    }
    let mut out = vec![None; entries.len()];
    for (index, entry) in entries.iter().enumerate() {
        if let ControlEntryOrigin::CallResume { value } = entry.origin
            && let Some(need) = needs[index]
        {
            out[index] = Some(return_abi_for_resume_input(world, executable, value, need));
        }
    }
    for entry in entries {
        publish_entry_input_abis(world, root_id, program, executable, entries, entry, &needs, &mut out)?;
    }
    for (index, entry) in entries.iter().enumerate() {
        if let ControlEntryOrigin::CallResume { value } = entry.origin
            && out[index].is_none()
        {
            out[index] = Some(return_abi_for_resume_input(
                world,
                executable,
                value,
                ExecutableNeed::Value,
            ));
        }
    }
    Ok(out)
}

fn collect_entry_input_need(
    world: &mut World<'_>,
    executable: &super::super::artifact::EmissionReadyExecutable,
    entries: &[LoweredEntry],
    entry_id: super::super::body::ControlEntryId,
    outgoing_need: ReturnAbi,
    out: &mut [Option<ExecutableNeed>],
) -> ExecutableNeed {
    let entry = &entries[entry_id.as_u32() as usize];
    let mut tuple_demands = HashMap::new();
    let mut used_values = HashSet::new();
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            used_values.insert(*value);
            if let ExecutableNeed::TupleFields(arity) =
                destination_need(world, executable, entries, dest, outgoing_need.clone(), out)
            {
                tuple_demands.insert(*value, arity);
            }
        }
        LoweredTail::DirectCall { args, dest, .. } => {
            for arg in args {
                used_values.insert(arg.value);
            }
            let _ = destination_need(world, executable, entries, dest, outgoing_need.clone(), out);
        }
        LoweredTail::ClosureCall { callee, args, dest, .. } => {
            used_values.insert(*callee);
            for arg in args {
                used_values.insert(arg.value);
            }
            let _ = destination_need(world, executable, entries, dest, outgoing_need.clone(), out);
        }
        LoweredTail::If {
            cond,
            then_entry,
            else_entry,
            ..
        } => {
            used_values.insert(*cond);
            let _ = collect_entry_input_need(world, executable, entries, *then_entry, outgoing_need.clone(), out);
            let _ = collect_entry_input_need(world, executable, entries, *else_entry, outgoing_need, out);
        }
        LoweredTail::Dispatch {
            inputs,
            bindings,
            dispatch,
        } => {
            used_values.extend(inputs.iter().copied());
            used_values.extend(bindings.pinned.iter().copied());
            used_values.extend(bindings.prepared.iter().copied());
            for arm_entry in &dispatch.arm_entries {
                let _ = collect_entry_input_need(world, executable, entries, *arm_entry, outgoing_need.clone(), out);
            }
            let _ = collect_entry_input_need(world, executable, entries, dispatch.miss_entry, outgoing_need, out);
        }
        LoweredTail::Receive(receive) => {
            let bindings = &receive.bindings;
            used_values.extend(bindings.pinned.iter().copied());
            used_values.extend(bindings.prepared.iter().copied());
            for clause in &receive.clauses {
                let _ = collect_entry_input_need(world, executable, entries, clause.entry, outgoing_need.clone(), out);
            }
            if let Some(after) = &receive.after {
                used_values.insert(after.timeout);
                let _ = collect_entry_input_need(world, executable, entries, after.entry, outgoing_need, out);
            }
        }
        LoweredTail::Halt { .. } => {}
    }
    for step in entry.steps.iter().rev() {
        collect_step_reads(step, &mut used_values);
        match step {
            LoweredStep::AssertTuple { source, arity } => {
                tuple_demands.insert(*source, *arity);
            }
            LoweredStep::Const { value, .. }
            | LoweredStep::Tuple { value, .. }
            | LoweredStep::List { value, .. }
            | LoweredStep::Map { value, .. }
            | LoweredStep::MapUpdate { value, .. }
            | LoweredStep::Struct { value, .. }
            | LoweredStep::Bitstring { value, .. }
            | LoweredStep::FunctionRef { value, .. }
            | LoweredStep::NamedFunctionRef { value, .. }
            | LoweredStep::Lambda { value, .. }
            | LoweredStep::BinaryOp { value, .. }
            | LoweredStep::UnaryOp { value, .. }
            | LoweredStep::MapIndex { value, .. }
            | LoweredStep::FieldAccess { value, .. }
            | LoweredStep::RequireMapValue { value, .. }
            | LoweredStep::TupleField { value, .. } => {
                tuple_demands.remove(value);
            }
            LoweredStep::SplitList { head, tail, .. } => {
                tuple_demands.remove(head);
                tuple_demands.remove(tail);
            }
            LoweredStep::BitstringInit { reader, .. } => {
                tuple_demands.remove(reader);
            }
            LoweredStep::BitstringRead {
                ok, value, next_reader, ..
            } => {
                tuple_demands.remove(ok);
                tuple_demands.remove(value);
                tuple_demands.remove(next_reader);
            }
            LoweredStep::AssertLiteral { .. }
            | LoweredStep::AssertStruct { .. }
            | LoweredStep::AssertEmptyList { .. }
            | LoweredStep::AssertSame { .. }
            | LoweredStep::AssertBitstringDone { .. } => {}
        }
    }
    let input_need = entry.origin.input_value().and_then(|value| {
        tuple_demands
            .remove(&value)
            .map(ExecutableNeed::TupleFields)
            .or_else(|| used_values.contains(&value).then_some(ExecutableNeed::Value))
    });
    if matches!(entry.origin, ControlEntryOrigin::CallResume { .. }) {
        out[entry_id.as_u32() as usize] = input_need;
    }
    input_need.unwrap_or(ExecutableNeed::Value)
}

fn collect_step_reads(step: &LoweredStep, out: &mut HashSet<ValueId>) {
    match step {
        LoweredStep::Const { .. } | LoweredStep::FunctionRef { .. } | LoweredStep::NamedFunctionRef { .. } => {}
        LoweredStep::Tuple { items, .. } => out.extend(items.iter().copied()),
        LoweredStep::List { items, tail, .. } => {
            out.extend(items.iter().copied());
            if let Some(tail) = tail {
                out.insert(*tail);
            }
        }
        LoweredStep::Map { entries, .. } => {
            for (key, value) in entries {
                out.insert(*key);
                out.insert(*value);
            }
        }
        LoweredStep::MapUpdate { base, entries, .. } => {
            out.insert(*base);
            for (key, value) in entries {
                out.insert(*key);
                out.insert(*value);
            }
        }
        LoweredStep::Struct { fields, .. } => out.extend(fields.iter().map(|(_, value)| *value)),
        LoweredStep::Bitstring { fields, .. } => {
            for field in fields {
                out.insert(field.value);
                if let Some(super::super::body::LoweredBitSize::Value(size)) = &field.spec.size {
                    out.insert(*size);
                }
            }
        }
        LoweredStep::Lambda { captures, .. } => out.extend(captures.iter().copied()),
        LoweredStep::BinaryOp { left, right, .. } => {
            out.insert(*left);
            out.insert(*right);
        }
        LoweredStep::UnaryOp { input, .. } => {
            out.insert(*input);
        }
        LoweredStep::MapIndex { base, key, .. } => {
            out.insert(*base);
            out.insert(*key);
        }
        LoweredStep::FieldAccess { base, .. } | LoweredStep::AssertStruct { source: base, .. } => {
            out.insert(*base);
        }
        LoweredStep::RequireMapValue { source, .. } => {
            out.insert(*source);
        }
        LoweredStep::AssertLiteral { source, .. }
        | LoweredStep::AssertTuple { source, .. }
        | LoweredStep::AssertEmptyList { source } => {
            out.insert(*source);
        }
        LoweredStep::TupleField { source, .. } => {
            out.insert(*source);
        }
        LoweredStep::AssertSame { source, value } => {
            out.insert(*source);
            out.insert(*value);
        }
        LoweredStep::SplitList { source, .. } => {
            out.insert(*source);
        }
        LoweredStep::BitstringInit { source, .. } | LoweredStep::AssertBitstringDone { reader: source } => {
            out.insert(*source);
        }
        LoweredStep::BitstringRead { reader, spec, .. } => {
            out.insert(*reader);
            if let Some(super::super::body::LoweredBitSize::Value(size)) = &spec.size {
                out.insert(*size);
            }
        }
    }
}

fn destination_need(
    world: &mut World<'_>,
    executable: &super::super::artifact::EmissionReadyExecutable,
    entries: &[LoweredEntry],
    dest: &ControlDestination,
    outgoing_need: ReturnAbi,
    out: &mut [Option<ExecutableNeed>],
) -> ExecutableNeed {
    match dest {
        ControlDestination::Return => match outgoing_need {
            ReturnAbi::Value(_) => ExecutableNeed::Value,
            ReturnAbi::TupleFields(ref reprs) => ExecutableNeed::TupleFields(reprs.len()),
        },
        ControlDestination::Deliver(entry_id) => {
            collect_entry_input_need(world, executable, entries, *entry_id, outgoing_need, out)
        }
    }
}

fn publish_entry_input_abis(
    world: &mut World<'_>,
    root_id: RootId,
    program: &super::super::artifact::EmissionReadyProgram,
    executable: &super::super::artifact::EmissionReadyExecutable,
    entries: &[LoweredEntry],
    entry: &LoweredEntry,
    needs: &[Option<ExecutableNeed>],
    out: &mut [Option<ReturnAbi>],
) -> Result<(), FatalError> {
    match &entry.tail {
        LoweredTail::Value { value, dest } => {
            if let ControlDestination::Deliver(target) = dest
                && matches!(
                    entries[target.as_u32() as usize].origin,
                    ControlEntryOrigin::CallResume { .. }
                )
            {
                let need = needs[target.as_u32() as usize].unwrap_or(ExecutableNeed::Value);
                let abi = return_abi_for_resume_input(world, executable, *value, need);
                merge_resume_abi(world, root_id, *target, abi, out)?;
            }
        }
        LoweredTail::DirectCall { callsite, dest, .. } | LoweredTail::ClosureCall { callsite, dest, .. } => {
            if let ControlDestination::Deliver(target) = dest
                && matches!(
                    entries[target.as_u32() as usize].origin,
                    ControlEntryOrigin::CallResume { .. }
                )
            {
                let edge = call_edge(executable, *callsite).ok_or_else(|| {
                    incomplete_backend_program(
                        world,
                        root_id,
                        format!(
                            "missing settled call edge while deriving resume ABI for callsite {}",
                            callsite.as_u32()
                        ),
                    )
                })?;
                let abi = program.executables[edge.callee].return_abi.clone();
                merge_resume_abi(world, root_id, *target, abi, out)?;
            }
        }
        LoweredTail::If { .. } | LoweredTail::Dispatch { .. } | LoweredTail::Receive(_) | LoweredTail::Halt { .. } => {}
    }
    Ok(())
}

fn merge_resume_abi(
    world: &World<'_>,
    root_id: RootId,
    entry_id: super::super::body::ControlEntryId,
    abi: ReturnAbi,
    out: &mut [Option<ReturnAbi>],
) -> Result<(), FatalError> {
    let slot = &mut out[entry_id.as_u32() as usize];
    match slot {
        Some(existing) if *existing != abi => Err(incomplete_backend_program(
            world,
            root_id,
            format!(
                "resume entry {} received conflicting input ABIs: {:?} vs {:?}",
                entry_id.as_u32(),
                existing,
                abi
            ),
        )),
        Some(_) => Ok(()),
        None => {
            *slot = Some(abi);
            Ok(())
        }
    }
}

fn return_abi_for_resume_input(
    world: &mut World<'_>,
    executable: &super::super::artifact::EmissionReadyExecutable,
    value: ValueId,
    need: ExecutableNeed,
) -> ReturnAbi {
    match need {
        ExecutableNeed::Value => ReturnAbi::Value(
            executable
                .value_reprs
                .get(&value)
                .copied()
                .unwrap_or_else(|| backend_value_repr(world, executable.value_types[&value])),
        ),
        ExecutableNeed::TupleFields(arity) => {
            let field_tys = world
                .types_mut()
                .tuple_projections(&executable.value_types[&value], arity);
            let reprs = field_tys
                .into_iter()
                .map(|ty| backend_value_repr(world, ty))
                .collect::<Vec<_>>();
            ReturnAbi::TupleFields(reprs)
        }
    }
}

fn backend_value_repr(world: &mut World<'_>, ty: Ty) -> AbiValueRepr {
    if world.types().is_floating(&ty) {
        return AbiValueRepr::RawF64;
    }
    if world.types().is_integer(&ty) {
        return AbiValueRepr::RawInt;
    }
    let atom = world.types_mut().atom();
    if world.types().is_subtype(&ty, &atom) {
        AbiValueRepr::RawAtom
    } else {
        AbiValueRepr::ValueRef
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
        BackendBody::Clauses { clauses, entries, .. } => {
            if let Some(dispatch) = &executable.entry_dispatch {
                collect_dispatch_atoms(world, dispatch.plan(), seen, atoms);
            }
            for clause in clauses {
                collect_step_atoms(world, &clause.projections, seen, atoms);
            }
            for entry in entries {
                collect_entry_atoms(world, entry, seen, atoms);
            }
        }
    }
}

fn collect_entry_atoms(
    world: &mut World<'_>,
    entry: &BackendEntry,
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    collect_step_atoms(world, &entry.steps, seen, atoms);
    collect_tail_atoms(world, &entry.tail, seen, atoms);
}

fn collect_step_atoms(
    _world: &mut World<'_>,
    steps: &[BackendStep],
    seen: &mut HashSet<String>,
    atoms: &mut Vec<String>,
) {
    for step in steps {
        match step {
            BackendStep::Const { literal, .. } | BackendStep::AssertLiteral { literal, .. } => {
                collect_literal_atoms(literal, seen, atoms);
            }
            BackendStep::FieldAccess { field, .. } => {
                if seen.insert(field.clone()) {
                    atoms.push(field.clone());
                }
            }
            BackendStep::RequireMapValue { key, .. } => {
                collect_literal_atoms(key, seen, atoms);
            }
            BackendStep::Tuple { .. }
            | BackendStep::List { .. }
            | BackendStep::Map { .. }
            | BackendStep::MapUpdate { .. }
            | BackendStep::Struct { .. }
            | BackendStep::Bitstring { .. }
            | BackendStep::FunctionRef { .. }
            | BackendStep::NamedFunctionRef { .. }
            | BackendStep::Lambda { .. }
            | BackendStep::BinaryOp { .. }
            | BackendStep::UnaryOp { .. }
            | BackendStep::MapIndex { .. }
            | BackendStep::AssertStruct { .. }
            | BackendStep::AssertTuple { .. }
            | BackendStep::TupleField { .. }
            | BackendStep::AssertEmptyList { .. }
            | BackendStep::AssertSame { .. }
            | BackendStep::SplitList { .. }
            | BackendStep::BitstringInit { .. }
            | BackendStep::BitstringRead { .. }
            | BackendStep::AssertBitstringDone { .. } => {}
        }
    }
}

fn collect_tail_atoms(world: &mut World<'_>, tail: &BackendTail, seen: &mut HashSet<String>, atoms: &mut Vec<String>) {
    match tail {
        BackendTail::Dispatch { dispatch, .. } => collect_dispatch_atoms(world, &dispatch.plan, seen, atoms),
        BackendTail::Receive(receive) => collect_dispatch_atoms(world, &receive.dispatch, seen, atoms),
        BackendTail::Halt { atom } => push_atom(seen, atoms, atom),
        BackendTail::Value { .. }
        | BackendTail::DirectCall { .. }
        | BackendTail::ClosureCall { .. }
        | BackendTail::If { .. } => {}
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
