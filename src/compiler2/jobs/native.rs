//! Compiler2 native-handoff lowering.
//!
//! This job turns one closed `BackendProgram(root)` into one CPS/native
//! handoff. The result is still Compiler2-owned: direct executable entries,
//! clause helpers, continuations, settled callable-boundary facts, and extern
//! marshal facts are all derived once here instead of being rediscovered by
//! shared codegen.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use crate::compiler::source::Span;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr, prepared_key_name};
use crate::dispatch_matrix::{
    ComparisonValue, DispatchConst, DispatchNode, GraphNodeId, ListRegion, Region, SubjectId,
};
use crate::fz_ir::{
    BinOp as IrBinOp, BitSizeIr, BlockId, BranchOrigin, CallsiteIdent, Const, Cont, DirectCallTarget, ExternArg,
    ExternDecl, ExternId, ExternMarshalSite, ExternTy, FnBuilder, FnCategory, FnId, InitTokenId, ModuleBuilder, Prim,
    ReceiveAfter, ReceiveClause, Term, UnOp as IrUnOp, Var,
};
use crate::runtime_type_predicate::RuntimeTypePredicate;
use crate::type_expr::ResolvedSpecDecl;
use crate::types::Types as LegacyTypes;

use super::super::artifact::{
    AbiValueRepr, BackendBody, BackendClause, BackendEntry, BackendEntryOrigin, BackendExecutable, BackendProgram,
    BackendStep, BackendTail, CallReturnFlow, CallTarget, EffectSummary, NativeBody, NativeBodyOrigin,
    NativeCallableBoundary, NativeCallableBoundaryId, NativeEntryAbi, NativeProgram,
    ReusableConsCapture as BackendReusableConsCapture,
};
use super::super::body::{ControlDestination, ControlEntryId, Literal, LoweredExtern, ValueId};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{FunctionId, RootId};
use super::super::scheduler::FatalError;
use super::super::semantic::{RuntimeDemand, ShapeDemand};
use super::super::transport::{
    BoundaryId, CallableId, CodegenLaneRepr, CodegenSeam, LaneId, ShapeDescr, ShapeId, TransportPosition,
    TransportValue,
};
use super::super::types::Ty;
use super::super::world::World;

fn legacy_extern_ty<T>(types: &mut T, ty: ExternTy) -> crate::types::Ty
where
    T: LegacyTypes<Ty = crate::types::Ty>,
{
    match ty {
        ExternTy::Unit => types.nil(),
        ExternTy::Never => types.none(),
        ExternTy::I64 => types.int(),
        ExternTy::F64 => types.float(),
        ExternTy::Any | ExternTy::Binary | ExternTy::CString => types.any(),
    }
}

fn legacy_extern_contract<T>(types: &mut T, signature: &LoweredExtern) -> ResolvedSpecDecl<crate::types::Ty>
where
    T: LegacyTypes<Ty = crate::types::Ty>,
{
    let params = signature
        .params
        .iter()
        .copied()
        .map(|ty| legacy_extern_ty(types, ty))
        .collect::<Vec<_>>();
    let result = legacy_extern_ty(types, signature.ret);
    ResolvedSpecDecl {
        params,
        result,
        constraints: HashMap::new(),
    }
}

/// Lowers one backend program into the Compiler2-owned native handoff.
///
/// The native handoff consumes only `BackendProgram(root)` plus compiler-owned
/// stores. It introduces CPS/native bodies and side facts, but it does not
/// reopen semantic closure, type inference, or planner discovery.
pub(super) fn lower_native_program(world: &mut World<'_>, root_id: RootId) -> Result<JobEffects, FatalError> {
    let backend_fact = FactKey::BackendProgram(root_id);
    if !world.has_fact(&backend_fact) {
        return Ok(JobEffects::wait_on_settled(
            backend_fact,
            [Job::LowerBackendProgram(root_id)],
        ));
    }

    let backend = world.backend_program(root_id);
    let stats = reusable_cons_telemetry_counts(&backend);
    let program = NativeLowerer::new(world, root_id, &backend)?.lower()?;
    let changed = world.define_native_program(root_id, program);
    world.tel().execute(
        &["fz", "compiler2", "native_program", "reusable_cons"],
        &crate::measurements! {
            root_id: root_id.as_u32() as u64,
            birth_count: stats.birth_count,
            transport_count: stats.transport_count,
        },
        &crate::metadata! {},
    );
    Ok(JobEffects {
        reads: settled_uses([backend_fact]),
        outputs: vec![FactKey::NativeProgram(root_id)],
        changed: changed.then_some(FactKey::NativeProgram(root_id)).into_iter().collect(),
        ..JobEffects::default()
    })
}

struct ReusableConsTelemetryCounts {
    birth_count: u64,
    transport_count: u64,
}

fn reusable_cons_telemetry_counts(program: &BackendProgram) -> ReusableConsTelemetryCounts {
    let mut birth_count = 0_u64;
    let mut transport_count = 0_u64;
    for executable in &program.executables {
        let BackendBody::Clauses { clauses, entries, .. } = &executable.body else {
            continue;
        };
        for clause in clauses {
            birth_count += count_reusable_cons_births(&clause.projections);
        }
        for entry in entries {
            birth_count += count_reusable_cons_births(&entry.steps);
            transport_count += entry.reusable_cons_captures.len() as u64;
        }
    }
    ReusableConsTelemetryCounts {
        birth_count,
        transport_count,
    }
}

fn count_reusable_cons_births(steps: &[BackendStep]) -> u64 {
    steps
        .iter()
        .filter(|step| matches!(step, BackendStep::SplitList { .. }))
        .count() as u64
}

struct NativeLowerer<'a, 'tel> {
    world: &'a mut World<'tel>,
    root_id: RootId,
    program: &'a BackendProgram,
    module: ModuleBuilder,
    atom_ids: HashMap<String, u32>,
    executable_fns: Vec<FnId>,
    callable_identity_fns: HashMap<(FunctionId, usize), FnId>,
    callable_boundaries: Vec<NativeCallableBoundary>,
    extern_ids: HashMap<usize, ExternId>,
    extern_marshals: HashMap<usize, Vec<ExternTy>>,
    extern_decls: Vec<ExternDecl>,
    native_bodies: Vec<NativeBody>,
    return_continuation_count: u32,
}

impl<'a, 'tel> NativeLowerer<'a, 'tel> {
    fn new(world: &'a mut World<'tel>, root_id: RootId, program: &'a BackendProgram) -> Result<Self, FatalError> {
        let mut atom_ids = HashMap::new();
        for (index, atom) in program.atom_names.iter().enumerate() {
            atom_ids.insert(atom.clone(), index as u32);
        }
        for atom in ["function_clause", "match_error"] {
            if !atom_ids.contains_key(atom) {
                let next = atom_ids.len() as u32;
                atom_ids.insert(atom.to_string(), next);
            }
        }

        let mut module = ModuleBuilder::new();
        let executable_fns = program
            .executables
            .iter()
            .map(|_| module.fresh_fn_id())
            .collect::<Vec<_>>();

        let mut callable_identity_fns = HashMap::new();
        for (function, capture_count) in collect_callable_identity_needs(program) {
            callable_identity_fns
                .entry((function, capture_count))
                .or_insert_with(|| module.fresh_fn_id());
        }
        for entry in &program.callable_entries {
            let function = program.executables[entry.target].key.activation.function;
            callable_identity_fns
                .entry((function, entry.capture_count))
                .or_insert_with(|| module.fresh_fn_id());
        }

        let extern_marshals = collect_extern_marshals(world, root_id, program)?;
        let mut legacy_types = crate::types::new();
        let mut extern_ids = HashMap::new();
        let mut extern_decls = Vec::new();
        for (index, executable) in program.executables.iter().enumerate() {
            let BackendBody::Extern { signature } = &executable.body else {
                continue;
            };
            let id = ExternId(extern_decls.len() as u32);
            extern_ids.insert(index, id);
            let semantic_contract = legacy_extern_contract(&mut legacy_types, signature);
            extern_decls.push(ExternDecl {
                id,
                fz_name: world.function_ref(executable.key.activation.function).name.clone(),
                symbol: signature.symbol.clone(),
                params: signature.params.clone(),
                variadic: signature.variadic,
                ret: signature.ret,
                ret_descr: semantic_contract.result.clone(),
                semantic_contract,
            });
        }

        let callable_boundaries = program
            .callable_entries
            .iter()
            .enumerate()
            .map(|(index, entry)| {
                let executable = &program.executables[entry.target];
                let function = executable.key.activation.function;
                let identity_fn = *callable_identity_fns
                    .get(&(function, entry.capture_count))
                    .expect("callable identity should be predeclared");
                NativeCallableBoundary {
                    id: NativeCallableBoundaryId(index as u32),
                    boundary: entry.boundary,
                    identity_fn,
                    target_fn: executable_fns[entry.target],
                    target: executable.key.clone(),
                    capture_count: entry.capture_count,
                    capture_reprs: entry.capture_reprs.clone(),
                    arg_reprs: entry.arg_reprs.clone(),
                    return_ty: entry.return_ty,
                    return_shape: entry.return_shape,
                    return_lanes: entry.return_lanes.clone(),
                    return_reprs: callable_boundary_reprs(program, entry.boundary, &entry.return_lanes),
                    return_tuple_arity: match world.transport().interners().shape(entry.return_shape) {
                        ShapeDescr::Tuple(fields) => Some(fields.len()),
                        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => None,
                    },
                }
            })
            .collect();

        Ok(Self {
            world,
            root_id,
            program,
            module,
            atom_ids,
            executable_fns,
            callable_identity_fns,
            callable_boundaries,
            extern_ids,
            extern_marshals,
            extern_decls,
            native_bodies: Vec::new(),
            return_continuation_count: 0,
        })
    }

    fn lower(mut self) -> Result<NativeProgram, FatalError> {
        for (index, executable) in self.program.executables.iter().enumerate() {
            match &executable.body {
                BackendBody::Extern { signature } => self.lower_extern_executable(index, executable, signature)?,
                BackendBody::Clauses { clauses, entries, .. } => {
                    let entry_fns = entry_fn_ids(&mut self.module, entries);
                    if executable.entry_dispatch.is_some() {
                        self.lower_clause_dispatch_executable(index, executable, clauses, entries, &entry_fns)?;
                    } else {
                        let [clause] = clauses.as_slice() else {
                            return Err(incomplete_native_program(
                                self.world,
                                self.root_id,
                                format!(
                                    "backend executable {} has {} clauses but no settled entry dispatch",
                                    index,
                                    clauses.len()
                                ),
                            ));
                        };
                        self.lower_clause_body_fn(
                            self.executable_fns[index],
                            executable,
                            &format!(
                                "{}__e{}",
                                self.world.function_ref(executable.key.activation.function).name,
                                index
                            ),
                            FnCategory::User,
                            NativeBodyOrigin::Executable(executable.key.clone()),
                            entries,
                            &entry_fns,
                            clause,
                        )?;
                    }
                    self.lower_entry_helpers(index, executable, entries, &entry_fns)?;
                }
            }
        }

        let entry = *self
            .executable_fns
            .get(self.program.entry)
            .expect("native entry executable should exist");
        let mut module = self.module.build();
        annotate_back_edges(&mut module);
        module.atom_names = atom_names(&self.atom_ids);
        module.externs = self.extern_decls;
        module.extern_idx = module
            .externs
            .iter()
            .enumerate()
            .map(|(index, decl)| (decl.id, index))
            .collect();
        module.struct_schemas = self.program.struct_schemas.clone();
        Ok(NativeProgram {
            backend_revision: self.program.emission_ready_revision,
            entry,
            module,
            bodies: self.native_bodies,
            callable_boundaries: self.callable_boundaries,
        })
    }

    fn lower_extern_executable(
        &mut self,
        index: usize,
        executable: &BackendExecutable,
        signature: &LoweredExtern,
    ) -> Result<(), FatalError> {
        let fn_id = self.executable_fns[index];
        let name = format!(
            "{}__e{}",
            self.world.function_ref(executable.key.activation.function).name,
            index
        );
        let (return_reprs, return_tuple_arity) =
            native_return_contract(self.world, self.program, &executable.transport.return_position);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::Prelude,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.param_reprs.clone(),
            executable.return_ty,
            executable.transport.return_position.clone(),
            return_reprs,
            return_tuple_arity,
            executable.effects,
        );
        let params = ctx.entry_params(executable.key.activation.input.as_slice());
        let mut extern_args = Vec::with_capacity(params.len());
        for (arg_index, param) in params.iter().copied().enumerate() {
            let arg = if arg_index < signature.params.len() {
                ExternArg::fixed(param, signature.params[arg_index])
            } else {
                ExternArg::auto(param)
            };
            extern_args.push(arg);
        }
        let extern_id = *self
            .extern_ids
            .get(&index)
            .expect("extern executable should have a declared ExternId");
        let marshal_plan = self.extern_marshals.get(&index).cloned().unwrap_or_default();
        let callsite = ctx.fresh_callsite();
        let (value, stmt_idx) = ctx.emit_let(Prim::Extern(callsite, extern_id, extern_args));
        for (arg_index, marshal) in marshal_plan.iter().copied().enumerate() {
            ctx.extern_marshals.insert(
                ExternMarshalSite {
                    block: ctx.current_block,
                    stmt_idx,
                    arg_idx: arg_index,
                },
                marshal,
            );
        }
        let result = if matches!(signature.ret, ExternTy::Unit | ExternTy::Never) {
            let (nil, _) = ctx.emit_let(Prim::Const(Const::Nil));
            let _ = value;
            nil
        } else {
            value
        };
        ctx.set_term(Term::Return(result));
        self.finish_native_fn(ctx);
        Ok(())
    }

    fn lower_clause_dispatch_executable(
        &mut self,
        index: usize,
        executable: &BackendExecutable,
        clauses: &[BackendClause],
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
    ) -> Result<(), FatalError> {
        let helper_ids = clauses.iter().map(|_| self.module.fresh_fn_id()).collect::<Vec<_>>();
        let fn_id = self.executable_fns[index];
        let name = format!(
            "{}__e{}",
            self.world.function_ref(executable.key.activation.function).name,
            index
        );
        let (return_reprs, return_tuple_arity) =
            native_return_contract(self.world, self.program, &executable.transport.return_position);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::User,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.param_reprs.clone(),
            executable.return_ty,
            executable.transport.return_position.clone(),
            return_reprs,
            return_tuple_arity,
            executable.effects,
        );
        let entry_tys = executable_input_tys(self.world, self.program, executable);
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let semantic_inputs = bind_executable_inputs(self.world, self.program, executable, &mut ctx, &entry_vars)?;
        let dispatch = executable
            .entry_dispatch
            .as_ref()
            .expect("clause dispatch lowering requires a settled entry dispatch");
        let required_inputs = dispatch.required_input_ordinals();
        let inputs = semantic_inputs
            .iter()
            .enumerate()
            .map(
                |(semantic_index, value)| match (required_inputs.contains(&semantic_index), value) {
                    (true, Some(value)) => self.materialize_native_value(
                        &mut ctx,
                        executable.key.activation.input.get(semantic_index).copied(),
                        value,
                    ),
                    (true, None) => Err(incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!(
                            "native clause dispatch required omitted semantic input {} for executable {}",
                            semantic_index,
                            executable.key.activation.function.as_u32(),
                        ),
                    )),
                    (false, _) => Ok(ctx.emit_let(Prim::Const(Const::Nil)).0),
                },
            )
            .collect::<Result<Vec<_>, _>>()?;
        let mut state = DispatchState::new(inputs, entry_vars, Vec::new());
        self.lower_dispatch_node(
            &mut ctx,
            executable,
            dispatch,
            dispatch.plan().graph.root,
            &helper_ids,
            &mut state,
        )?;
        self.finish_native_fn(ctx);

        for (clause_index, (clause, helper_id)) in clauses.iter().zip(helper_ids.iter().copied()).enumerate() {
            self.lower_clause_body_fn(
                helper_id,
                executable,
                &format!(
                    "{}__clause_{}",
                    self.world.function_ref(executable.key.activation.function).name,
                    clause_index
                ),
                FnCategory::MultiClauseCont,
                NativeBodyOrigin::Clause {
                    owner: executable.key.clone(),
                    index: clause_index as u32,
                },
                entries,
                entry_fns,
                clause,
            )?;
        }
        Ok(())
    }

    fn lower_clause_body_fn(
        &mut self,
        fn_id: FnId,
        executable: &BackendExecutable,
        name: &str,
        category: FnCategory,
        origin: NativeBodyOrigin,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        clause: &BackendClause,
    ) -> Result<(), FatalError> {
        let (return_reprs, return_tuple_arity) =
            native_return_contract(self.world, self.program, &executable.transport.return_position);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            name,
            category,
            origin,
            NativeEntryAbi::Direct,
            executable.param_reprs.clone(),
            executable.return_ty,
            executable.transport.return_position.clone(),
            return_reprs,
            return_tuple_arity,
            executable.effects,
        );
        let mut env = ValueEnv::default();
        let entry_tys = executable_input_tys(self.world, self.program, executable);
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let semantic_inputs = bind_executable_inputs(self.world, self.program, executable, &mut ctx, &entry_vars)?;
        for (value, bound) in clause.params.iter().copied().zip(semantic_inputs) {
            if let Some(bound) = bound {
                bind_local_value(&mut ctx, executable, &mut env, value, bound);
            }
        }
        self.lower_entry_steps(&mut ctx, executable, &mut env, &clause.projections)?;
        self.lower_entry_from_id(&mut ctx, executable, entries, entry_fns, clause.entry, env)?;
        self.finish_native_fn(ctx);
        Ok(())
    }

    fn finish_native_fn(&mut self, ctx: NativeFnCtx) {
        let (fn_ir, body) = ctx.finish();
        let body = NativeBody {
            block_param_reprs: native_block_param_reprs(self.world, &fn_ir, &body.value_types),
            ..body
        };
        self.module.add_fn(fn_ir);
        self.native_bodies.push(body);
    }

    fn lower_entry_helpers(
        &mut self,
        executable_index: usize,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
    ) -> Result<(), FatalError> {
        for (entry_index, entry) in entries.iter().enumerate() {
            if matches!(entry.origin, BackendEntryOrigin::Clause) {
                continue;
            }
            self.lower_entry_fn(
                executable_index,
                executable,
                entries,
                entry_fns,
                ControlEntryId::from_u32(entry_index as u32),
            )?;
        }
        Ok(())
    }

    fn lower_entry_fn(
        &mut self,
        executable_index: usize,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        entry_id: ControlEntryId,
    ) -> Result<(), FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let fn_id = *entry_fns
            .get(&entry_id)
            .expect("non-clause entry should have a predeclared helper fn");
        let base_name = format!(
            "{}__e{}",
            self.world.function_ref(executable.key.activation.function).name,
            executable_index
        );
        let (entry_name, entry_category) = match &entry.origin {
            BackendEntryOrigin::Clause => return Err(FatalError),
            BackendEntryOrigin::Branch => (
                format!("{base_name}__branch_{}", entry_id.as_u32()),
                FnCategory::ControlFlowCont,
            ),
            BackendEntryOrigin::ReceiveOutcome => (
                format!("{base_name}__receive_{}", entry_id.as_u32()),
                FnCategory::CpsCont,
            ),
            BackendEntryOrigin::DeliveredResume { .. } => (
                format!("{base_name}__resume_{}", entry_id.as_u32()),
                FnCategory::CpsCont,
            ),
        };
        let (entry_tys, param_reprs, entry_abi) =
            self.entry_signature(executable, entry, entry.reusable_cons_captures.as_slice());
        let (return_reprs, return_tuple_arity) =
            native_return_contract(self.world, self.program, &executable.transport.return_position);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &entry_name,
            entry_category,
            NativeBodyOrigin::Continuation {
                owner: self.executable_fns[executable_index],
                index: entry_id.as_u32(),
            },
            entry_abi,
            param_reprs,
            executable.return_ty,
            executable.transport.return_position.clone(),
            return_reprs,
            return_tuple_arity,
            executable.effects,
        );
        let mut env = ValueEnv::default();
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let mut capture_offset = self.bind_entry_input(&mut ctx, executable, entry, &entry_vars, &mut env)?;
        self.mark_delivered_entry_semantics(&mut ctx, executable, entry, &entry_vars[..capture_offset])?;
        for (value, position) in entry.captures.iter().copied().zip(entry.capture_positions.iter()) {
            let shape = position_shape(self.program, position);
            let bound = decode_runtime_value(self.world, &mut ctx, &entry_vars, shape, &mut capture_offset).map_err(|_| {
                incomplete_native_program(
                    self.world,
                    self.root_id,
                    format!(
                        "native entry {:?} failed to decode capture {} at position {:?} with shape {:?}; offset={} params={}",
                        ctx.origin,
                        value.as_u32(),
                        position,
                        self.world.transport().interners().shape(shape),
                        capture_offset,
                        entry_vars.len()
                    ),
                )
            })?;
            bind_local_value(&mut ctx, executable, &mut env, value, bound);
        }
        for (capture, physical_var) in entry
            .reusable_cons_captures
            .iter()
            .copied()
            .zip(entry_vars.iter().copied().skip(capture_offset))
        {
            self.bind_runtime_value(&mut ctx, executable, &mut env, capture.source, physical_var);
            let semantic_var = self.env_runtime_var(&mut ctx, executable, &env, capture.head);
            ctx.builder.record_reusable_cons_cell(semantic_var, physical_var);
        }
        self.lower_entry_steps(&mut ctx, executable, &mut env, &entry.steps)?;
        self.lower_entry_tail(&mut ctx, executable, entries, entry_fns, &env, &entry.tail)?;
        self.finish_native_fn(ctx);
        Ok(())
    }

    fn lower_entry_from_id(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        entry_id: ControlEntryId,
        mut env: ValueEnv,
    ) -> Result<(), FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        self.lower_entry_steps(ctx, executable, &mut env, &entry.steps)?;
        self.lower_entry_tail(ctx, executable, entries, entry_fns, &env, &entry.tail)
    }

    fn lower_entry_steps(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &mut ValueEnv,
        steps: &[BackendStep],
    ) -> Result<(), FatalError> {
        for step in steps {
            match step {
                BackendStep::Omitted { value } => {
                    bind_local_value(ctx, executable, env, *value, NativeBoundValue::Absent);
                }
                BackendStep::Const { value, literal } => {
                    let var = lower_backend_literal(ctx, &self.atom_ids, literal)?;
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::Tuple { value, items } => {
                    if let Some(shape) = maybe_value_shape(self.program, executable, *value)
                        && let ShapeDescr::Tuple(fields) = self.world.transport().interners().shape(shape).clone()
                    {
                        if fields.len() != items.len() {
                            return Err(FatalError);
                        }
                        let mut lanes = Vec::new();
                        for (item, field_shape) in items.iter().copied().zip(fields) {
                            self.encode_env_value_for_shape(ctx, executable, env, item, field_shape, &mut lanes)?;
                        }
                        bind_local_value(
                            ctx,
                            executable,
                            env,
                            *value,
                            NativeBoundValue::Transport { shape, lanes },
                        );
                    } else {
                        let fields = self.env_runtime_vars(ctx, executable, env, items);
                        let (var, _) = ctx.emit_let(Prim::MakeTuple(fields));
                        self.bind_runtime_value(ctx, executable, env, *value, var);
                    }
                }
                BackendStep::List { value, items, tail } => {
                    let vars = self.env_runtime_vars(ctx, executable, env, items);
                    let tail = tail.map(|tail| self.env_runtime_var(ctx, executable, env, tail));
                    let (var, _) = ctx.emit_let(Prim::MakeList(vars, tail));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::Map { value, entries } => {
                    let token = ctx.fresh_token();
                    let (map, _) = ctx.emit_let(Prim::DestMapBegin {
                        token,
                        base: None,
                        extra: entries.len(),
                    });
                    let mut token = token;
                    for (key, item) in entries {
                        let next = ctx.fresh_token();
                        let key = self.env_runtime_var(ctx, executable, env, *key);
                        let value = self.env_runtime_var(ctx, executable, env, *item);
                        let _ = ctx.emit_let(Prim::DestMapPut {
                            map,
                            token,
                            key,
                            value,
                            next,
                        });
                        token = next;
                    }
                    let (var, _) = ctx.emit_let(Prim::DestMapFreeze { map, token });
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::MapUpdate { value, base, entries } => {
                    let base = self.env_runtime_var(ctx, executable, env, *base);
                    let token = ctx.fresh_token();
                    let (map, _) = ctx.emit_let(Prim::DestMapBegin {
                        token,
                        base: Some(base),
                        extra: entries.len(),
                    });
                    let mut token = token;
                    for (key, item) in entries {
                        let next = ctx.fresh_token();
                        let key = self.env_runtime_var(ctx, executable, env, *key);
                        let value = self.env_runtime_var(ctx, executable, env, *item);
                        let _ = ctx.emit_let(Prim::DestMapPut {
                            map,
                            token,
                            key,
                            value,
                            next,
                        });
                        token = next;
                    }
                    let (var, _) = ctx.emit_let(Prim::DestMapFreeze { map, token });
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::Struct {
                    value,
                    module_name,
                    fields,
                } => {
                    let mut lowered = Vec::with_capacity(fields.len());
                    for (field, item) in fields {
                        lowered.push((field.clone(), self.env_runtime_var(ctx, executable, env, *item)));
                    }
                    let (var, _) = ctx.emit_let(Prim::MakeStruct {
                        module: module_name.clone(),
                        fields: lowered,
                    });
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::Bitstring { value, fields } => {
                    let mut lowered = Vec::with_capacity(fields.len());
                    for field in fields {
                        lowered.push(crate::fz_ir::BitFieldIr {
                            value: self.env_runtime_var(ctx, executable, env, field.value),
                            ty: field.spec.ty,
                            size: lower_bit_size_ir(self.world, &field.spec.size, env)?,
                            endian: field.spec.endian,
                            signed: field.spec.signed,
                            unit: field.spec.unit,
                        });
                    }
                    let (var, _) = ctx.emit_let(Prim::MakeBitstring(lowered));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::FunctionRef { value, function: _ } => {
                    let shape = value_shape(self.program, executable, *value);
                    if matches!(self.world.transport().interners().shape(shape), ShapeDescr::Nothing) {
                        // The transport plan settled this reference to Nothing: it is
                        // never demanded as a runtime callable (passed only to an
                        // ignoring boundary or discarded), so it carries no lanes.
                        // Honor that proof and construct nothing.
                        bind_local_value(ctx, executable, env, *value, NativeBoundValue::Absent);
                    } else {
                        callable_id_for_shape(self.world, shape)?;
                        bind_local_value(
                            ctx,
                            executable,
                            env,
                            *value,
                            NativeBoundValue::Transport {
                                shape,
                                lanes: Vec::new(),
                            },
                        );
                    }
                }
                BackendStep::Lambda {
                    value,
                    function: _,
                    captures,
                } => {
                    let shape = value_shape(self.program, executable, *value);
                    if matches!(self.world.transport().interners().shape(shape), ShapeDescr::Nothing) {
                        // A settled-Nothing constructed callable is never demanded at
                        // runtime, so its captures carry nothing. Honor the transport
                        // plan's proof and construct nothing.
                        bind_local_value(ctx, executable, env, *value, NativeBoundValue::Absent);
                        continue;
                    }
                    let callable = callable_id_for_shape(self.world, shape)?;
                    let callable_descr = self.world.transport().interners().callable(callable).clone();
                    let capture_shapes = callable_descr.capture_shapes.to_vec();
                    if capture_shapes.len() != captures.len() {
                        return Err(incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native direct callable capture count did not match transport callable descriptor",
                        ));
                    }
                    let mut capture_lanes = Vec::new();
                    let mut descriptor_lane_index = 0;
                    for (capture, shape) in captures.iter().copied().zip(capture_shapes) {
                        let structural_width = self.world.transport().interners().shape_width(shape);
                        if structural_width == 0 && descriptor_lane_index < callable_descr.capture_lanes.len() {
                            let lane = callable_descr.capture_lanes[descriptor_lane_index];
                            descriptor_lane_index += 1;
                            let local = env_local_value(env, capture)?;
                            let ty = self.world.transport().interners().lane(lane).ty;
                            capture_lanes.push(self.materialize_native_value(ctx, Some(ty), &local)?);
                        } else {
                            self.encode_env_value_for_shape(ctx, executable, env, capture, shape, &mut capture_lanes)?;
                            descriptor_lane_index += structural_width;
                        }
                    }
                    if descriptor_lane_index != callable_descr.capture_lanes.len() {
                        return Err(incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native lambda capture lowering did not consume the callable descriptor capture lanes",
                        ));
                    }
                    bind_local_value(
                        ctx,
                        executable,
                        env,
                        *value,
                        NativeBoundValue::Transport {
                            shape,
                            lanes: capture_lanes,
                        },
                    );
                }
                BackendStep::BinaryOp { value, op, left, right } => {
                    let left = self.env_runtime_var(ctx, executable, env, *left);
                    let right = self.env_runtime_var(ctx, executable, env, *right);
                    let (var, _) = ctx.emit_let(Prim::BinOp(lower_binop(*op), left, right));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::UnaryOp { value, op, input } => {
                    let input = self.env_runtime_var(ctx, executable, env, *input);
                    let (var, _) = ctx.emit_let(Prim::UnOp(lower_unop(*op), input));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::MapIndex { value, base, key } => {
                    let base = self.env_runtime_var(ctx, executable, env, *base);
                    let key = self.env_runtime_var(ctx, executable, env, *key);
                    let (var, _) = ctx.emit_let(Prim::MapGet(base, key));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::FieldAccess { value, base, field } => {
                    let base = self.env_runtime_var(ctx, executable, env, *base);
                    let (var, _) = ctx.emit_let(Prim::StructField(base, field.clone()));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::AssertLiteral { source, literal } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let expected = lower_backend_literal(ctx, &self.atom_ids, literal)?;
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, source, expected));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::AssertStruct { source, module_name } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let predicate =
                        RuntimeTypePredicate::named_struct(module_name.rsplit('.').next().unwrap_or(module_name));
                    let (matches, _) = ctx.emit_let(Prim::RuntimeTypeTest(source, Box::new(predicate)));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::RequireMapValue { value, source, key } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let key = lower_backend_literal(ctx, &self.atom_ids, key)?;
                    let (var, _) = ctx.emit_let(Prim::MatcherMapGet(source, key));
                    let (is_miss, _) = ctx.emit_let(Prim::IsMatcherMapMiss(var));
                    let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, is_miss, false_v));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::AssertTuple { source, arity } => {
                    let realized = env_local_value(env, *source)?;
                    if self.transport_tuple_arity(&realized) == Some(*arity) {
                        continue;
                    }
                    let source = self.materialize_native_value(ctx, None, &realized)?;
                    let tuple_ty = RuntimeTypePredicate::tuple_arity(*arity);
                    let (matches, _) = ctx.emit_let(Prim::RuntimeTypeTest(source, Box::new(tuple_ty)));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::TupleField { value, source, index } => {
                    let realized = env_local_value(env, *source)?;
                    if let Some(field) = self.transport_tuple_field(&realized, *index)? {
                        bind_local_value(ctx, executable, env, *value, field);
                    } else {
                        let tuple = self.materialize_native_value(ctx, None, &realized)?;
                        let (var, _) = ctx.emit_let(Prim::TupleField(tuple, *index as u32));
                        bind_local_value(ctx, executable, env, *value, NativeBoundValue::Runtime(var));
                    }
                }
                BackendStep::AssertEmptyList { source } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let (matches, _) = ctx.emit_let(Prim::IsEmptyList(source));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::AssertSame { source, value } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let value = self.env_runtime_var(ctx, executable, env, *value);
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, source, value));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::SplitList { source, head, tail } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let (head_var, _) = ctx.emit_let(Prim::ListHead(source));
                    self.bind_runtime_value(ctx, executable, env, *head, head_var);
                    ctx.builder.record_reusable_cons_cell(head_var, source);
                    let (tail_var, _) = ctx.emit_let(Prim::ListTail(source));
                    self.bind_runtime_value(ctx, executable, env, *tail, tail_var);
                }
                BackendStep::BitstringInit { reader, source } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let (var, _) = ctx.emit_let(Prim::BitReaderInit(source));
                    self.bind_runtime_value(ctx, executable, env, *reader, var);
                }
                BackendStep::BitstringRead {
                    ok,
                    value,
                    next_reader,
                    reader,
                    spec,
                    is_last,
                } => {
                    let reader = self.env_runtime_var(ctx, executable, env, *reader);
                    let (result, _) = ctx.emit_let(Prim::BitReadField {
                        reader,
                        ty: spec.ty,
                        size: lower_bit_size_ir(self.world, &spec.size, env)?,
                        endian: spec.endian,
                        signed: spec.signed,
                        unit: spec.unit,
                        is_last: *is_last,
                    });
                    let (ok_var, _) = ctx.emit_let(Prim::TupleField(result, 0));
                    self.bind_runtime_value(ctx, executable, env, *ok, ok_var);
                    let (value_var, _) = ctx.emit_let(Prim::TupleField(result, 1));
                    self.bind_runtime_value(ctx, executable, env, *value, value_var);
                    let (reader_var, _) = ctx.emit_let(Prim::TupleField(result, 2));
                    self.bind_runtime_value(ctx, executable, env, *next_reader, reader_var);
                }
                BackendStep::AssertBitstringDone { reader } => {
                    let reader = self.env_runtime_var(ctx, executable, env, *reader);
                    let (done, _) = ctx.emit_let(Prim::BitReaderDone(reader));
                    ctx.assert_truthy(done, self.atom_id("match_error"));
                }
            }
        }
        Ok(())
    }

    fn lower_entry_tail(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        env: &ValueEnv,
        tail: &BackendTail,
    ) -> Result<(), FatalError> {
        match tail {
            BackendTail::Value { value, dest } => {
                self.lower_value_destination(ctx, executable, entries, entry_fns, env, *value, dest)
            }
            BackendTail::DirectCall {
                callee,
                args,
                dest,
                return_flow,
                ..
            } => {
                let (callee, call_args) = match callee {
                    CallTarget::Local(callee) => {
                        let callee_executable = &self.program.executables[*callee];
                        let mut lanes = Vec::new();
                        let input_bindings = executable_input_bindings(self.program, callee_executable);
                        for (arg, binding) in args.iter().zip(input_bindings.iter()) {
                            let local = env_local_value(env, arg.value)?;
                            if binding.publication_lanes.is_empty() {
                                self.encode_runtime_value(
                                    ctx,
                                    callee_executable,
                                    Some(arg.value),
                                    &local,
                                    binding.shape,
                                    &mut lanes,
                                )?;
                            } else {
                                lanes.push(self.materialize_native_value_for_publication(
                                    ctx,
                                    executable.value_types.get(&arg.value).copied(),
                                    &local,
                                    &binding.position,
                                )?);
                            }
                        }
                        (DirectCallTarget::Local(self.executable_fns[*callee]), lanes)
                    }
                    CallTarget::ProviderBoundary(function) => (
                        DirectCallTarget::ProviderBoundary(self.world.function_mfa(*function)),
                        self.env_runtime_vars(
                            ctx,
                            executable,
                            env,
                            &args.iter().map(|arg| arg.value).collect::<Vec<_>>(),
                        ),
                    ),
                };
                match dest {
                    ControlDestination::Return => match return_flow {
                        CallReturnFlow::Tail { .. } => {
                            ctx.set_term(Term::TailCall {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                callee,
                                args: call_args,
                                is_back_edge: false,
                            });
                            Ok(())
                        }
                        CallReturnFlow::Continue { payload, .. } => {
                            let continuation = self.return_lane_continuation_for_payload(ctx, executable, payload)?;
                            ctx.set_term(Term::Call {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                callee,
                                args: call_args,
                                continuation,
                            });
                            Ok(())
                        }
                        CallReturnFlow::Deliver { .. } => Err(incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native direct call with Return destination carried Deliver return-flow",
                        )),
                    },
                    ControlDestination::Deliver(entry_id) => {
                        let continuation =
                            self.entry_continuation(ctx, executable, entries, entry_fns, *entry_id, env)?;
                        ctx.set_term(Term::Call {
                            ident: CallsiteIdent::from_source(Span::DUMMY),
                            callee,
                            args: call_args,
                            continuation,
                        });
                        Ok(())
                    }
                }
            }
            BackendTail::ClosureCall {
                callee,
                target,
                args,
                dest,
                return_flow,
                ..
            } => {
                let callee_value = env_local_value(env, *callee)?;
                if let Some(capture_lanes) = self.direct_callable_lanes(&callee_value)? {
                    let target = target.ok_or_else(|| {
                        incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native direct-only closure call did not settle an exact local target",
                        )
                    })?;
                    let callee_executable = &self.program.executables[target];
                    let mut call_args = capture_lanes;
                    let input_shapes = executable_input_shapes(self.program, callee_executable);
                    let arg_inputs_start = input_shapes.len().checked_sub(args.len()).ok_or(FatalError)?;
                    for (arg, (_, shape)) in args.iter().zip(input_shapes.iter().copied().skip(arg_inputs_start)) {
                        let local = env_local_value(env, arg.value)?;
                        self.encode_runtime_value(
                            ctx,
                            callee_executable,
                            Some(arg.value),
                            &local,
                            shape,
                            &mut call_args,
                        )?;
                    }
                    let callee = DirectCallTarget::Local(self.executable_fns[target]);
                    match dest {
                        ControlDestination::Return => match return_flow.as_ref().ok_or_else(|| {
                            incomplete_native_program(
                                self.world,
                                self.root_id,
                                "native direct closure call with Return destination is missing return-flow facts",
                            )
                        })? {
                            CallReturnFlow::Tail { .. } => {
                                ctx.set_term(Term::TailCall {
                                    ident: CallsiteIdent::from_source(Span::DUMMY),
                                    callee,
                                    args: call_args,
                                    is_back_edge: false,
                                });
                                Ok(())
                            }
                            CallReturnFlow::Continue { payload, .. } => {
                                let continuation =
                                    self.return_lane_continuation_for_payload(ctx, executable, payload)?;
                                ctx.set_term(Term::Call {
                                    ident: CallsiteIdent::from_source(Span::DUMMY),
                                    callee,
                                    args: call_args,
                                    continuation,
                                });
                                Ok(())
                            }
                            CallReturnFlow::Deliver { .. } => Err(incomplete_native_program(
                                self.world,
                                self.root_id,
                                "native direct closure call with Return destination carried Deliver return-flow",
                            )),
                        },
                        ControlDestination::Deliver(entry_id) => {
                            let continuation =
                                self.entry_continuation(ctx, executable, entries, entry_fns, *entry_id, env)?;
                            ctx.set_term(Term::Call {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                callee,
                                args: call_args,
                                continuation,
                            });
                            Ok(())
                        }
                    }
                } else {
                    let closure = self.materialize_native_value(ctx, None, &callee_value)?;
                    let call_args = self.env_runtime_vars(
                        ctx,
                        executable,
                        env,
                        &args.iter().map(|arg| arg.value).collect::<Vec<_>>(),
                    );
                    let direct_target = target.map(|target| self.executable_fns[target]);
                    match dest {
                        ControlDestination::Return => {
                            if let Some(CallReturnFlow::Continue { payload, .. }) = return_flow.as_ref() {
                                let continuation =
                                    self.return_lane_continuation_for_payload(ctx, executable, payload)?;
                                ctx.set_term(Term::CallClosure {
                                    ident: CallsiteIdent::from_source(Span::DUMMY),
                                    closure,
                                    direct_target,
                                    args: call_args,
                                    continuation,
                                });
                                return Ok(());
                            }
                            ctx.set_term(Term::TailCallClosure {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                closure,
                                direct_target,
                                args: call_args,
                            });
                            Ok(())
                        }
                        ControlDestination::Deliver(entry_id) => {
                            let continuation =
                                self.entry_continuation(ctx, executable, entries, entry_fns, *entry_id, env)?;
                            ctx.set_term(Term::CallClosure {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                closure,
                                direct_target,
                                args: call_args,
                                continuation,
                            });
                            Ok(())
                        }
                    }
                }
            }
            BackendTail::If {
                cond,
                then_entry,
                else_entry,
            } => {
                let cond = self.env_runtime_var(ctx, executable, env, *cond);
                let then_b = ctx.builder.block(vec![]);
                let else_b = ctx.builder.block(vec![]);
                ctx.set_term(Term::If {
                    cond,
                    then_b,
                    else_b,
                    origin: BranchOrigin::User,
                });
                ctx.current_block = then_b;
                let then_args = self.entry_capture_args(ctx, executable, entries, *then_entry, env)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(
                        *entry_fns.get(then_entry).expect("branch entry should have a helper fn"),
                    ),
                    args: then_args,
                    is_back_edge: false,
                });
                ctx.current_block = else_b;
                let else_args = self.entry_capture_args(ctx, executable, entries, *else_entry, env)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(
                        *entry_fns.get(else_entry).expect("branch entry should have a helper fn"),
                    ),
                    args: else_args,
                    is_back_edge: false,
                });
                Ok(())
            }
            BackendTail::Dispatch {
                inputs,
                bindings,
                dispatch,
            } => {
                let input_vars = self.env_runtime_vars(ctx, executable, env, inputs);
                let pinned_vars = self.env_runtime_vars(ctx, executable, env, &bindings.pinned);
                let forwarded_vars =
                    self.control_dispatch_forwarded_args(ctx, executable, entries, &dispatch.arm_entries, env)?;
                let mut state = DispatchState::new(input_vars, forwarded_vars, pinned_vars);
                self.lower_control_dispatch_node(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    &dispatch.plan,
                    &dispatch.arm_entries,
                    dispatch.miss_entry,
                    dispatch.plan.graph.root,
                    &mut state,
                )
            }
            BackendTail::Receive(receive) => {
                let bindings = &receive.bindings;
                let dispatch = &receive.dispatch;
                let clauses = &receive.clauses;
                let after = receive.after.as_ref();
                let captures = self.receive_capture_vars(ctx, executable, entries, clauses, after, env)?;
                let clauses = clauses
                    .iter()
                    .map(|clause| {
                        Ok(ReceiveClause {
                            ident: CallsiteIdent::from_source(clause.span),
                            bound_names: clause.bound_names.clone(),
                            guard: None,
                            body: *entry_fns
                                .get(&clause.entry)
                                .expect("receive clause entry should have a helper fn"),
                            span: clause.span,
                        })
                    })
                    .collect::<Result<Vec<_>, FatalError>>()?;
                let after = after
                    .map(|after| {
                        Ok(ReceiveAfter {
                            ident: CallsiteIdent::from_source(after.span),
                            timeout: self.env_runtime_var(ctx, executable, env, after.timeout),
                            body: *entry_fns
                                .get(&after.entry)
                                .expect("receive after entry should have a helper fn"),
                            span: after.span,
                        })
                    })
                    .transpose()?;
                let pinned = self.receive_pinned_vars(ctx, executable, env, bindings, dispatch)?;
                let dispatch = {
                    let types = self.world.types();
                    dispatch.map_type_handle(&mut |ty| types.runtime_type_predicate(ty))
                };
                ctx.set_term(Term::ReceiveMatched {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    clauses,
                    dispatch: Arc::new(dispatch),
                    after,
                    pinned,
                    captures,
                });
                Ok(())
            }
            BackendTail::Halt { atom } => {
                ctx.halt_with_atom(self.atom_id(atom));
                Ok(())
            }
        }
    }

    fn lower_value_destination(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        env: &ValueEnv,
        value_id: ValueId,
        dest: &ControlDestination,
    ) -> Result<(), FatalError> {
        match dest {
            ControlDestination::Return => {
                let lanes = self.return_lane_vars(ctx, executable, env, value_id)?;
                ctx.set_term(Term::ReturnLanes(lanes));
                Ok(())
            }
            ControlDestination::Deliver(entry_id) => {
                let args = self.entry_call_args_from_value(ctx, executable, entries, *entry_id, env, value_id)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(
                        *entry_fns.get(entry_id).expect("resume entry should have a helper fn"),
                    ),
                    args,
                    is_back_edge: false,
                });
                Ok(())
            }
        }
    }

    fn return_lane_vars(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        value_id: ValueId,
    ) -> Result<Vec<Var>, FatalError> {
        let mut lanes = Vec::new();
        let return_shape = position_shape(self.program, &executable.transport.return_position);
        self.encode_env_value_for_shape(ctx, executable, env, value_id, return_shape, &mut lanes)?;
        Ok(lanes)
    }

    fn entry_signature(
        &mut self,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        reusable_cons_captures: &[BackendReusableConsCapture],
    ) -> (Vec<Ty>, Vec<AbiValueRepr>, NativeEntryAbi) {
        let mut param_tys = entry
            .params
            .iter()
            .map(|value| {
                executable
                    .value_types
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any())
            })
            .collect::<Vec<_>>();
        let capture_shapes = entry
            .capture_positions
            .iter()
            .map(|position| position_shape(self.program, position))
            .collect::<Vec<_>>();
        let capture_lane_tys = capture_shapes
            .iter()
            .copied()
            .flat_map(|shape| shape_lane_tys(self.world, shape))
            .collect::<Vec<_>>();
        let capture_lane_reprs = entry_capture_reprs(self.world, self.program, entry);
        let physical_capture_tys = reusable_cons_captures
            .iter()
            .map(|capture| {
                executable
                    .value_types
                    .get(&capture.source)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any())
            })
            .collect::<Vec<_>>();
        match entry.origin.clone() {
            BackendEntryOrigin::Clause => panic!("clause entries are lowered through their owning clause"),
            BackendEntryOrigin::Branch => {
                let mut param_reprs = param_tys
                    .iter()
                    .copied()
                    .map(|ty| abi_value_repr(self.world, ty))
                    .collect::<Vec<_>>();
                param_reprs.extend(capture_lane_reprs.iter().copied());
                param_reprs.extend(
                    physical_capture_tys
                        .iter()
                        .copied()
                        .map(|ty| abi_value_repr(self.world, ty)),
                );
                param_tys.extend(capture_lane_tys.iter().copied());
                let mut entry_tys = param_tys;
                entry_tys.extend(physical_capture_tys);
                (entry_tys, param_reprs, NativeEntryAbi::Direct)
            }
            BackendEntryOrigin::ReceiveOutcome => {
                let mut param_reprs = param_tys
                    .iter()
                    .copied()
                    .map(|ty| abi_value_repr(self.world, ty))
                    .collect::<Vec<_>>();
                param_reprs.extend(capture_lane_reprs.iter().copied());
                param_tys.extend(capture_lane_tys.iter().copied());
                (param_tys, param_reprs, NativeEntryAbi::Continuation { extra_params: 0 })
            }
            BackendEntryOrigin::DeliveredResume { value: _, position } => {
                let (mut entry_tys, mut param_reprs) = continuation_result_entry(self.world, self.program, &position);
                let extra_params = param_reprs.len();
                entry_tys.extend(param_tys.iter().copied());
                param_reprs.extend(param_tys.iter().copied().map(|ty| abi_value_repr(self.world, ty)));
                entry_tys.extend(capture_lane_tys.iter().copied());
                param_reprs.extend(capture_lane_reprs.iter().copied());
                entry_tys.extend(physical_capture_tys.iter().copied());
                param_reprs.extend(
                    physical_capture_tys
                        .iter()
                        .copied()
                        .map(|ty| abi_value_repr(self.world, ty)),
                );
                (entry_tys, param_reprs, NativeEntryAbi::Continuation { extra_params })
            }
        }
    }

    fn bind_entry_input(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        entry_vars: &[Var],
        env: &mut ValueEnv,
    ) -> Result<usize, FatalError> {
        match &entry.origin {
            BackendEntryOrigin::Clause => Ok(0),
            BackendEntryOrigin::Branch => {
                for (value, var) in entry.params.iter().copied().zip(entry_vars.iter().copied()) {
                    self.bind_runtime_value(ctx, executable, env, value, var);
                }
                Ok(entry.params.len())
            }
            BackendEntryOrigin::ReceiveOutcome => {
                for (value, var) in entry.params.iter().copied().zip(entry_vars.iter().copied()) {
                    self.bind_runtime_value(ctx, executable, env, value, var);
                }
                Ok(entry.params.len())
            }
            BackendEntryOrigin::DeliveredResume { value, position } => {
                if self.resume_payload_is_runtime_absent(position) {
                    bind_local_value(ctx, executable, env, *value, NativeBoundValue::Absent);
                    return Ok(0);
                }
                let shape = position_shape(self.program, position);
                let mut lane_index = 0;
                let publication_lanes =
                    position_publication_lanes(self.program, |seam| continuation_seam_matches(position, seam));
                let bound = decode_runtime_value_with_width(
                    entry_vars,
                    shape,
                    position_width(self.world, shape, &publication_lanes),
                    !publication_lanes.is_empty(),
                    self.world,
                    ctx,
                    &mut lane_index,
                )?;
                bind_local_value(ctx, executable, env, *value, bound);
                Ok(lane_index)
            }
        }
    }

    fn mark_delivered_entry_semantics(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        input_vars: &[Var],
    ) -> Result<(), FatalError> {
        let BackendEntryOrigin::DeliveredResume { value, position } = &entry.origin else {
            return Ok(());
        };
        let shape = position_shape(self.program, position);
        let publication_lanes =
            position_publication_lanes(self.program, |seam| continuation_seam_matches(position, seam));
        let mut lane_index = 0;
        if !publication_lanes.is_empty() {
            let ignore = RuntimeDemand::ignore();
            let demand = executable.runtime_demand.value_demands.get(value).unwrap_or(&ignore);
            mark_ignored_publication_lanes(&mut ctx.builder, input_vars, demand, &mut lane_index)?;
        } else if let Some(demand) = executable.runtime_demand.value_demands.get(value) {
            mark_ignored_lanes_for_demand(self.world, &mut ctx.builder, input_vars, shape, demand, &mut lane_index)?;
        } else {
            mark_all_runtime_lanes_ignored(self.world, &mut ctx.builder, input_vars, shape, &mut lane_index)?;
        }
        if lane_index != input_vars.len() {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "delivered resume value {} semantic demand consumed {} lanes but entry exposes {}",
                    value.as_u32(),
                    lane_index,
                    input_vars.len()
                ),
            ));
        }
        Ok(())
    }

    fn entry_continuation(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        entry_id: ControlEntryId,
        env: &ValueEnv,
    ) -> Result<Cont, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        if entry.origin.input_value().is_none() {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "native call continuation targeted entry {} without an input value: origin={:?} params={} captures={}",
                    entry_id.as_u32(),
                    entry.origin,
                    entry.params.len(),
                    entry.captures.len(),
                ),
            ));
        }
        Ok(Cont {
            fn_id: *entry_fns.get(&entry_id).expect("resume entry should have a helper fn"),
            captured: self.entry_capture_args(ctx, executable, entries, entry_id, env)?,
        })
    }

    fn return_lane_continuation_for_payload(
        &mut self,
        ctx: &NativeFnCtx,
        executable: &BackendExecutable,
        payload: &TransportPosition,
    ) -> Result<Cont, FatalError> {
        let (param_tys, payload_reprs) = return_payload_entry(self.world, self.program, payload);
        if param_tys.len() != payload_reprs.len() {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "native return-lane continuation for {:?} expected {} payload lane types, got {} reprs",
                    payload,
                    param_tys.len(),
                    payload_reprs.len()
                ),
            ));
        }

        let fn_id = self.module.fresh_fn_id();
        let index = self.return_continuation_count;
        self.return_continuation_count += 1;
        let name = format!("return_lanes__{}_{}", ctx.fn_id.0, index);
        let mut cont_ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::CpsCont,
            NativeBodyOrigin::Continuation {
                owner: ctx.fn_id,
                index,
            },
            NativeEntryAbi::Continuation {
                extra_params: payload_reprs.len(),
            },
            payload_reprs,
            executable.return_ty,
            executable.transport.return_position.clone(),
            ctx.return_reprs.clone(),
            ctx.return_tuple_arity,
            executable.effects,
        );
        let lanes = cont_ctx.entry_params(param_tys.as_slice());
        cont_ctx.set_term(Term::ReturnLanes(lanes));
        self.finish_native_fn(cont_ctx);
        Ok(Cont {
            fn_id,
            captured: Vec::new(),
        })
    }

    fn entry_capture_args(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_id: ControlEntryId,
        env: &ValueEnv,
    ) -> Result<Vec<Var>, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let mut args = Vec::new();
        for (value, position) in entry.captures.iter().copied().zip(entry.capture_positions.iter()) {
            let local = env_local_value(env, value)?;
            let shape = position_shape(self.program, position);
            self.encode_runtime_value(ctx, executable, Some(value), &local, shape, &mut args)?;
        }
        for capture in &entry.reusable_cons_captures {
            args.push(self.env_runtime_var(ctx, executable, env, capture.source));
        }
        Ok(args)
    }

    fn resume_payload_is_runtime_absent(&self, position: &TransportPosition) -> bool {
        let shape = position_shape(self.program, position);
        matches!(self.world.transport().interners().shape(shape), ShapeDescr::Nothing)
    }

    fn receive_pinned_vars(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        bindings: &super::super::body::DispatchBindings,
        dispatch: &PatternDispatchPlan<Ty>,
    ) -> Result<Vec<(String, Var)>, FatalError> {
        let mut pinned = Vec::new();
        for (index, value_id) in bindings.pinned.iter().copied().enumerate() {
            let Some(pin) = dispatch.pinned.get(index) else {
                return Err(incomplete_native_program(
                    self.world,
                    self.root_id,
                    format!("receive pinned binding {} is out of bounds", index),
                ));
            };
            if pin.input.is_none() {
                let var = self.env_runtime_var(ctx, executable, env, value_id);
                pinned.push((pin.name.clone(), var));
            }
        }
        for (index, value_id) in bindings.prepared.iter().copied().enumerate() {
            let var = self.env_runtime_var(ctx, executable, env, value_id);
            pinned.push((prepared_key_name(index), var));
        }
        Ok(pinned)
    }

    fn receive_capture_vars(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        clauses: &[super::super::body::ReceiveClause],
        after: Option<&super::super::body::ReceiveAfter>,
        env: &ValueEnv,
    ) -> Result<Vec<Var>, FatalError> {
        let mut iter = clauses
            .iter()
            .map(|clause| clause.entry)
            .chain(after.iter().map(|after| after.entry));
        let capture_ids = iter
            .next()
            .map(|entry_id| entries[entry_id.as_u32() as usize].captures.clone())
            .unwrap_or_default();
        for entry_id in iter {
            let entry_captures = &entries[entry_id.as_u32() as usize].captures;
            if *entry_captures != capture_ids {
                return Err(incomplete_native_program(
                    self.world,
                    self.root_id,
                    "receive entries did not settle on one shared capture layout",
                ));
            }
        }
        let entry = entries
            .get(
                clauses
                    .first()
                    .map(|clause| clause.entry.as_u32() as usize)
                    .or_else(|| after.map(|after| after.entry.as_u32() as usize))
                    .unwrap_or(0),
            )
            .ok_or(FatalError)?;
        let mut args = Vec::new();
        for (value, position) in capture_ids.into_iter().zip(entry.capture_positions.iter()) {
            let local = env_local_value(env, value)?;
            let shape = position_shape(self.program, position);
            self.encode_runtime_value(ctx, executable, Some(value), &local, shape, &mut args)?;
        }
        Ok(args)
    }

    fn entry_call_args_from_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_id: ControlEntryId,
        env: &ValueEnv,
        value_id: ValueId,
    ) -> Result<Vec<Var>, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let mut args = match &entry.origin {
            BackendEntryOrigin::Clause | BackendEntryOrigin::Branch | BackendEntryOrigin::ReceiveOutcome => Vec::new(),
            BackendEntryOrigin::DeliveredResume { position, .. } => {
                let mut lanes = Vec::new();
                let publication_lanes =
                    position_publication_lanes(self.program, |seam| continuation_seam_matches(position, seam));
                if publication_lanes.is_empty() {
                    let shape = position_shape(self.program, position);
                    self.encode_env_value_for_shape(ctx, executable, env, value_id, shape, &mut lanes)?;
                } else {
                    let local = env_local_value(env, value_id)?;
                    lanes.push(self.materialize_native_value_for_publication(
                        ctx,
                        executable.value_types.get(&value_id).copied(),
                        &local,
                        position,
                    )?);
                }
                lanes
            }
        };
        args.extend(self.entry_capture_args(ctx, executable, entries, entry_id, env)?);
        Ok(args)
    }

    fn lower_dispatch_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        dispatch: &crate::compiler2::ExecutableDispatch,
        node_id: GraphNodeId,
        helper_ids: &[FnId],
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = dispatch.plan().graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!("dispatch graph node {:?} is out of bounds", node_id),
            ));
        };
        match node {
            DispatchNode::Fail => {
                ctx.halt_with_atom(self.atom_id("function_clause"));
                Ok(())
            }
            DispatchNode::Outcome { outcome, .. } => {
                let body_id = dispatch
                    .plan()
                    .outcome(outcome)
                    .map(|entry| entry.body_id)
                    .ok_or_else(|| {
                        incomplete_native_program(
                            self.world,
                            self.root_id,
                            format!("dispatch outcome {:?} is out of bounds", outcome),
                        )
                    })?;
                let Some(clause_index) = dispatch.clause_index(body_id) else {
                    ctx.halt_with_atom(self.atom_id("function_clause"));
                    return Ok(());
                };
                let args = state.forwarded_args.clone();
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(helper_ids[clause_index]),
                    args,
                    is_back_edge: false,
                });
                Ok(())
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let cond = self.lower_dispatch_region(
                    ctx,
                    executable,
                    dispatch.plan(),
                    predicate.subject,
                    &predicate.region,
                    state,
                )?;
                let then_b = ctx.builder.block(vec![]);
                let else_b = ctx.builder.block(vec![]);
                ctx.set_term(Term::If {
                    cond,
                    then_b,
                    else_b,
                    origin: BranchOrigin::ClauseDispatch,
                });
                let mut match_state = state.clone();
                ctx.current_block = then_b;
                self.lower_dispatch_node(ctx, executable, dispatch, on_match.target, helper_ids, &mut match_state)?;
                ctx.current_block = else_b;
                self.lower_dispatch_node(ctx, executable, dispatch, on_miss.target, helper_ids, state)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_control_dispatch_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &HashMap<ControlEntryId, FnId>,
        env: &ValueEnv,
        plan: &PatternDispatchPlan<Ty>,
        arm_entries: &[ControlEntryId],
        miss_entry: ControlEntryId,
        node_id: GraphNodeId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = plan.graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!("local dispatch graph node {:?} is out of bounds", node_id),
            ));
        };
        match node {
            DispatchNode::Fail => {
                let args = self.entry_capture_args(ctx, executable, entries, miss_entry, env)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(
                        *entry_fns
                            .get(&miss_entry)
                            .expect("local dispatch miss entry should have a helper fn"),
                    ),
                    args,
                    is_back_edge: false,
                });
                Ok(())
            }
            DispatchNode::Outcome { outcome, .. } => {
                let Some(body_id) = plan.outcome(outcome).map(|outcome| outcome.body_id) else {
                    let args = self.entry_capture_args(ctx, executable, entries, miss_entry, env)?;
                    ctx.set_term(Term::TailCall {
                        ident: CallsiteIdent::from_source(Span::DUMMY),
                        callee: DirectCallTarget::Local(
                            *entry_fns
                                .get(&miss_entry)
                                .expect("local dispatch miss entry should have a helper fn"),
                        ),
                        args,
                        is_back_edge: false,
                    });
                    return Ok(());
                };
                let arm_entry = *arm_entries.get(body_id as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!("local dispatch arm {} is out of bounds", body_id),
                    )
                })?;
                let args = self.control_dispatch_entry_args(ctx, executable, entries, arm_entry, env, state)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(
                        *entry_fns
                            .get(&arm_entry)
                            .expect("local dispatch arm entry should have a helper fn"),
                    ),
                    args,
                    is_back_edge: false,
                });
                Ok(())
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let cond =
                    self.lower_dispatch_region(ctx, executable, plan, predicate.subject, &predicate.region, state)?;
                let then_b = ctx.builder.block(vec![]);
                let else_b = ctx.builder.block(vec![]);
                ctx.set_term(Term::If {
                    cond,
                    then_b,
                    else_b,
                    origin: BranchOrigin::User,
                });
                let mut match_state = state.clone();
                ctx.current_block = then_b;
                self.lower_control_dispatch_node(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    plan,
                    arm_entries,
                    miss_entry,
                    on_match.target,
                    &mut match_state,
                )?;
                ctx.current_block = else_b;
                self.lower_control_dispatch_node(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    plan,
                    arm_entries,
                    miss_entry,
                    on_miss.target,
                    state,
                )
            }
        }
    }

    fn control_dispatch_forwarded_args(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        arm_entries: &[ControlEntryId],
        env: &ValueEnv,
    ) -> Result<Vec<Var>, FatalError> {
        let Some(first_entry) = arm_entries.first().map(|entry_id| &entries[entry_id.as_u32() as usize]) else {
            return Ok(Vec::new());
        };
        let params = first_entry.params.clone();
        for entry_id in arm_entries.iter().copied().skip(1) {
            let entry = &entries[entry_id.as_u32() as usize];
            if entry.params != params {
                return Err(incomplete_native_program(
                    self.world,
                    self.root_id,
                    format!(
                        "local dispatch arm entries disagree on forwarded params: entry {} has {:?}, expected {:?}",
                        entry_id.as_u32(),
                        entry.params,
                        params
                    ),
                ));
            }
        }
        Ok(self.env_runtime_vars(ctx, executable, env, &params))
    }

    fn control_dispatch_entry_args(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_id: ControlEntryId,
        env: &ValueEnv,
        state: &DispatchState,
    ) -> Result<Vec<Var>, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let param_count = entry.params.len();
        let mut args = state
            .forwarded_args
            .get(..param_count)
            .ok_or_else(|| {
                incomplete_native_program(
                    self.world,
                    self.root_id,
                    format!(
                        "local dispatch arm entry {} needs {} forwarded params but dispatch carries {}",
                        entry_id.as_u32(),
                        param_count,
                        state.forwarded_args.len()
                    ),
                )
            })?
            .to_vec();
        args.extend(self.entry_capture_args(ctx, executable, entries, entry_id, env)?);
        Ok(args)
    }

    fn lower_dispatch_region(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        plan: &PatternDispatchPlan<Ty>,
        subject: SubjectId,
        region: &Region<Ty>,
        state: &mut DispatchState,
    ) -> Result<Var, FatalError> {
        Ok(match region {
            Region::Any => {
                let (var, _) = ctx.emit_let(Prim::Const(Const::True));
                var
            }
            Region::Never => {
                let (var, _) = ctx.emit_let(Prim::Const(Const::False));
                var
            }
            Region::Type(ty) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let predicate = self.world.types().runtime_type_predicate(ty);
                let (var, _) = ctx.emit_let(Prim::RuntimeTypeTest(subject, Box::new(predicate)));
                var
            }
            Region::Equal(ComparisonValue::Const(DispatchConst::EmptyList)) | Region::List(ListRegion::Empty) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let (var, _) = ctx.emit_let(Prim::IsEmptyList(subject));
                var
            }
            Region::List(ListRegion::Cons) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let (var, _) = ctx.emit_let(Prim::IsListCons(subject));
                var
            }
            Region::TupleArity(arity) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let tuple_ty = RuntimeTypePredicate::tuple_arity(*arity as usize);
                let (var, _) = ctx.emit_let(Prim::RuntimeTypeTest(subject, Box::new(tuple_ty)));
                var
            }
            Region::MapKind => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let (var, _) = ctx.emit_let(Prim::RuntimeTypeTest(
                    subject,
                    Box::new(RuntimeTypePredicate::map_kind()),
                ));
                var
            }
            Region::MapKeyPresent { key } => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let key = lower_dispatch_const(ctx, &self.atom_ids, key)?;
                let (value, _) = ctx.emit_let(Prim::MatcherMapGet(subject, key));
                let (is_miss, _) = ctx.emit_let(Prim::IsMatcherMapMiss(value));
                let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, is_miss, false_v));
                var
            }
            Region::Equal(ComparisonValue::Const(value)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let expected = lower_dispatch_const(ctx, &self.atom_ids, value)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, subject, expected));
                var
            }
            Region::Guard(guard) => {
                let expr = plan.guards.get(guard.0 as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!("dispatch guard {:?} is out of bounds", guard),
                    )
                })?;
                self.lower_guard_expr(ctx, executable, plan, state, expr)?
            }
            Region::Equal(ComparisonValue::Pinned(pinned)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let pinned = self.dispatch_pinned_var(plan, state, *pinned)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, subject, pinned));
                var
            }
            Region::Bitstring(_) => {
                return Err(incomplete_native_program(
                    self.world,
                    self.root_id,
                    "native entry-dispatch lowering does not support bitstring tests yet",
                ));
            }
        })
    }

    fn lower_guard_expr(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        expr: &PatternGuardExpr<Ty>,
    ) -> Result<Var, FatalError> {
        Ok(match expr {
            PatternGuardExpr::Const(value) => lower_dispatch_const(ctx, &self.atom_ids, value)?,
            PatternGuardExpr::Subject(subject) => self.dispatch_subject_var(ctx, plan, state, *subject)?,
            PatternGuardExpr::Unary { op, expr } => {
                let input = self.lower_guard_expr(ctx, executable, plan, state, expr)?;
                let (var, _) = ctx.emit_let(Prim::UnOp(
                    match op {
                        crate::dispatch_matrix::pattern::PatternGuardUnaryOp::Not => IrUnOp::Not,
                        crate::dispatch_matrix::pattern::PatternGuardUnaryOp::Neg => IrUnOp::Neg,
                    },
                    input,
                ));
                var
            }
            PatternGuardExpr::Binary { op, lhs, rhs } => {
                let lhs = self.lower_guard_expr(ctx, executable, plan, state, lhs)?;
                let rhs = self.lower_guard_expr(ctx, executable, plan, state, rhs)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(lower_guard_binop(*op), lhs, rhs));
                var
            }
            PatternGuardExpr::Dispatch { .. } => {
                if let PatternGuardExpr::Dispatch { inputs, dispatch } = expr {
                    self.lower_guard_dispatch(ctx, executable, plan, state, inputs, dispatch)?
                } else {
                    unreachable!("dispatch arm must have matched");
                }
            }
            PatternGuardExpr::Pinned(pinned) => self.dispatch_pinned_var(plan, state, *pinned)?,
        })
    }

    fn lower_guard_dispatch(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        parent_plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        inputs: &[PatternGuardExpr<Ty>],
        dispatch: &crate::dispatch_matrix::pattern::PatternGuardDispatch<Ty>,
    ) -> Result<Var, FatalError> {
        let input_vars = inputs
            .iter()
            .map(|input| self.lower_guard_expr(ctx, executable, parent_plan, state, input))
            .collect::<Result<Vec<_>, _>>()?;
        let done_value = ctx.builder.fresh_var();
        let done_b = ctx.builder.block(vec![done_value]);
        let fail_b = ctx.builder.block(vec![]);
        let mut dispatch_state = DispatchState::new(input_vars, Vec::new(), Vec::new());
        self.lower_guard_dispatch_node(
            ctx,
            executable,
            &dispatch.plan,
            &dispatch.bodies,
            dispatch.plan.graph.root,
            done_b,
            fail_b,
            &mut dispatch_state,
        )?;
        ctx.current_block = fail_b;
        let (false_value, _) = ctx.emit_let(Prim::Const(Const::False));
        ctx.set_term(Term::Goto(done_b, vec![false_value]));
        ctx.current_block = done_b;
        Ok(done_value)
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_guard_dispatch_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        plan: &PatternDispatchPlan<Ty>,
        bodies: &[PatternGuardExpr<Ty>],
        node_id: GraphNodeId,
        done_b: BlockId,
        fail_b: BlockId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = plan.graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!("guard dispatch graph node {:?} is out of bounds", node_id),
            ));
        };
        match node {
            DispatchNode::Fail => {
                ctx.set_term(Term::Goto(fail_b, vec![]));
                Ok(())
            }
            DispatchNode::Outcome { outcome, .. } => {
                let outcome = plan.outcome(outcome).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!("guard dispatch outcome {:?} is out of bounds", outcome),
                    )
                })?;
                let body = bodies.get(outcome.body_id as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!("guard dispatch body {} is out of bounds", outcome.body_id),
                    )
                })?;
                let value = self.lower_guard_expr(ctx, executable, plan, state, body)?;
                ctx.set_term(Term::Goto(done_b, vec![value]));
                Ok(())
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let cond =
                    self.lower_dispatch_region(ctx, executable, plan, predicate.subject, &predicate.region, state)?;
                let then_b = ctx.builder.block(vec![]);
                let else_b = ctx.builder.block(vec![]);
                ctx.set_term(Term::If {
                    cond,
                    then_b,
                    else_b,
                    origin: BranchOrigin::ClauseDispatch,
                });
                let mut match_state = state.clone();
                ctx.current_block = then_b;
                self.lower_guard_dispatch_node(
                    ctx,
                    executable,
                    plan,
                    bodies,
                    on_match.target,
                    done_b,
                    fail_b,
                    &mut match_state,
                )?;
                ctx.current_block = else_b;
                self.lower_guard_dispatch_node(ctx, executable, plan, bodies, on_miss.target, done_b, fail_b, state)
            }
        }
    }

    fn dispatch_subject_var(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        subject: SubjectId,
    ) -> Result<Var, FatalError> {
        if let Some(var) = state.values.get(&subject).copied() {
            return Ok(var);
        }
        let Some(subject_data) = plan.matrix.subjects.get(subject.0 as usize) else {
            return Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!("dispatch subject {:?} is out of bounds", subject),
            ));
        };
        let var = match &subject_data.source {
            crate::dispatch_matrix::SubjectSource::Input { ordinal } => {
                state.dispatch_inputs.get(*ordinal as usize).copied().ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!("dispatch input {} has no native entry param", ordinal),
                    )
                })?
            }
            crate::dispatch_matrix::SubjectSource::Projection(projection) => match &projection.kind {
                crate::dispatch_matrix::ProjectionKind::TupleField(index) => {
                    let tuple = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let (var, _) = ctx.emit_let(Prim::TupleField(tuple, *index));
                    var
                }
                crate::dispatch_matrix::ProjectionKind::ListHead => {
                    let list = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let (var, _) = ctx.emit_let(Prim::ListHead(list));
                    var
                }
                crate::dispatch_matrix::ProjectionKind::ListTail => {
                    let list = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let (var, _) = ctx.emit_let(Prim::ListTail(list));
                    var
                }
                crate::dispatch_matrix::ProjectionKind::MapValue { key } => {
                    let map = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let key = lower_dispatch_const(ctx, &self.atom_ids, key)?;
                    let (var, _) = ctx.emit_let(Prim::MapGet(map, key));
                    var
                }
                crate::dispatch_matrix::ProjectionKind::BitstringField(index) => {
                    return Err(incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!("native dispatch does not support bitstring field projection {}", index),
                    ));
                }
            },
        };
        state.values.insert(subject, var);
        Ok(var)
    }

    fn dispatch_pinned_var(
        &mut self,
        plan: &PatternDispatchPlan<Ty>,
        state: &DispatchState,
        pinned: crate::dispatch_matrix::PinnedValueId,
    ) -> Result<Var, FatalError> {
        let pin = plan.pinned.get(pinned.0 as usize).ok_or_else(|| {
            incomplete_native_program(
                self.world,
                self.root_id,
                format!("dispatch pinned {:?} is out of bounds", pinned),
            )
        })?;
        if let Some(input) = pin.input {
            return state.dispatch_inputs.get(input as usize).copied().ok_or_else(|| {
                incomplete_native_program(
                    self.world,
                    self.root_id,
                    format!("dispatch pinned input {} is out of bounds", input),
                )
            });
        }
        state.pinned.get(pinned.0 as usize).copied().ok_or_else(|| {
            incomplete_native_program(
                self.world,
                self.root_id,
                format!("dispatch pinned capture {:?} is out of bounds", pinned),
            )
        })
    }

    fn atom_id(&self, name: &str) -> u32 {
        *self.atom_ids.get(name).expect("required atom should be interned")
    }

    fn callable_identity(&self, function: FunctionId, capture_count: usize) -> FnId {
        *self
            .callable_identity_fns
            .get(&(function, capture_count))
            .unwrap_or_else(|| panic!("callable identity for {function:?}/{capture_count}"))
    }

    /// Select the callable boundary for a rematerialized callable value from
    /// transport facts. Publication positions name the exact boundary when the
    /// value crosses a first-class seam; otherwise the value's `CallableId`
    /// fact must already identify one concrete native boundary.
    fn settled_callable_boundary(
        &self,
        callable: CallableId,
        function: FunctionId,
        capture_count: usize,
    ) -> Result<NativeCallableBoundaryId, FatalError> {
        let plan = self.world.transport().plans().get(self.root_id);
        let boundary_ids: Vec<BoundaryId> = match plan.and_then(|plan| plan.callables.get(&callable)) {
            Some(facts) => facts.boundary_ids.to_vec(),
            None => {
                return Err(incomplete_native_program(
                    self.world,
                    self.root_id,
                    format!(
                        "native callable materialization for {function:?}/{capture_count} has no transport callable facts for {callable:?}",
                    ),
                ));
            }
        };
        let matched = self
            .callable_boundaries
            .iter()
            .filter(|boundary| {
                let Some(boundary_facts) = plan.and_then(|plan| plan.boundaries.get(&boundary.boundary)) else {
                    return false;
                };
                boundary_ids.contains(&boundary.boundary)
                    && boundary_facts.resolutions.iter().any(|resolution| {
                        resolution.need == boundary.target.need
                            && resolution.activation.function == boundary.target.activation.function
                            && resolution.activation.input.as_ref() == boundary.target.activation.input.as_slice()
                    })
                    && boundary.target.activation.function == function
                    && boundary.capture_count == capture_count
            })
            .map(NativeCallableBoundary::id)
            .collect::<Vec<_>>();
        match matched.as_slice() {
            [boundary] => Ok(*boundary),
            [] => Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "native callable materialization for {function:?}/{capture_count} found no published boundary among CallableId fact boundaries {boundary_ids:?}",
                ),
            )),
            _ => Err(incomplete_native_program(
                self.world,
                self.root_id,
                // A callable published at multiple surfaces names several
                // boundary contracts; selecting which one a materialized value
                // carries is surface disambiguation, owned by the escaped/
                // static-singleton path in fz-hwn.19.5, and unreachable here.
                format!(
                    "native callable materialization for {function:?}/{capture_count} matched multiple published boundaries {matched:?} from CallableId fact {boundary_ids:?}",
                ),
            )),
        }
    }

    fn native_boundary_for_transport_boundary(
        &self,
        boundary: BoundaryId,
        function: FunctionId,
        capture_count: usize,
    ) -> Result<Option<NativeCallableBoundaryId>, FatalError> {
        let matched = self
            .callable_boundaries
            .iter()
            .filter(|candidate| {
                candidate.boundary == boundary
                    && candidate.target.activation.function == function
                    && candidate.capture_count == capture_count
            })
            .map(NativeCallableBoundary::id)
            .collect::<Vec<_>>();
        match matched.as_slice() {
            [boundary] => Ok(Some(*boundary)),
            [] => Ok(None),
            _ => Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "native callable materialization for {function:?}/{capture_count} matched multiple native boundaries {matched:?} for published transport boundary {boundary:?}",
                ),
            )),
        }
    }

    fn first_class_publication_boundary(
        &mut self,
        position: &TransportPosition,
        function: FunctionId,
        capture_count: usize,
    ) -> Result<Option<NativeCallableBoundaryId>, FatalError> {
        let published = self
            .program
            .transport
            .publication_boundaries
            .iter()
            .filter_map(|(candidate, boundary)| (candidate == position).then_some(*boundary))
            .collect::<Vec<_>>();
        match published.as_slice() {
            [] => Ok(None),
            [boundary] => self.native_boundary_for_transport_boundary(*boundary, function, capture_count),
            _ => Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!("transport position {position:?} is published by multiple callable boundaries {published:?}"),
            )),
        }
    }

    fn env_runtime_var(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        value_id: ValueId,
    ) -> Var {
        let value = env.cloned_value(value_id).unwrap_or_else(|| {
            panic!(
                "native lowering invariant failed: backend value {:?} in executable {:?} must be bound before runtime use",
                value_id, executable.key
            )
        });
        let ty = executable.value_types.get(&value_id).copied();
        self.materialize_native_value(ctx, ty, &value).unwrap_or_else(|_| {
            panic!(
                "native lowering invariant failed: backend value {:?} in executable {:?} must be runtime-materializable",
                value_id, executable.key
            )
        })
    }

    fn env_runtime_vars(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        values: &[ValueId],
    ) -> Vec<Var> {
        values
            .iter()
            .map(|value| self.env_runtime_var(ctx, executable, env, *value))
            .collect()
    }

    /// Bind a single native `Var` as a scalar value, recording its settled
    /// representation lane so downstream seams read it back uniformly.
    fn bind_runtime_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &mut ValueEnv,
        value: ValueId,
        var: Var,
    ) {
        bind_local_value(ctx, executable, env, value, NativeBoundValue::Runtime(var));
    }

    /// Collapse a cached native value into one runtime `Var`.
    ///
    /// Transport shape is deliberately not consulted here. Shape-specific lane
    /// projection happens in `encode_runtime_value` from the seam's shape.
    fn materialize_native_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        ty: Option<Ty>,
        value: &NativeBoundValue,
    ) -> Result<Var, FatalError> {
        self.materialize_native_value_with_boundary(ctx, ty, value, None)
    }

    fn materialize_native_value_for_publication(
        &mut self,
        ctx: &mut NativeFnCtx,
        ty: Option<Ty>,
        value: &NativeBoundValue,
        position: &TransportPosition,
    ) -> Result<Var, FatalError> {
        let boundary = match value {
            NativeBoundValue::Transport { shape, lanes } => match self.world.transport().interners().shape(*shape) {
                ShapeDescr::Callable(callable) => {
                    let descr = self.world.transport().interners().callable(*callable);
                    if lanes.len() == descr.capture_lanes.len()
                        && let Some(function) = descr.function
                    {
                        self.first_class_publication_boundary(position, function, descr.capture_lanes.len())?
                    } else {
                        None
                    }
                }
                ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Tuple(_) => None,
            },
            NativeBoundValue::Absent | NativeBoundValue::Runtime(_) => None,
        };
        self.materialize_native_value_with_boundary(ctx, ty, value, boundary)
    }

    fn materialize_native_value_with_boundary(
        &mut self,
        ctx: &mut NativeFnCtx,
        ty: Option<Ty>,
        value: &NativeBoundValue,
        boundary: Option<NativeCallableBoundaryId>,
    ) -> Result<Var, FatalError> {
        let var = match value {
            NativeBoundValue::Absent => return Err(FatalError),
            NativeBoundValue::Runtime(var) => *var,
            NativeBoundValue::Transport { shape, lanes } => {
                self.materialize_transport_value(ctx, *shape, lanes, boundary)?
            }
        };
        if let Some(ty) = ty {
            ctx.value_types.insert(var, ty);
        }
        Ok(var)
    }

    fn materialize_transport_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        shape: ShapeId,
        lanes: &[Var],
        boundary: Option<NativeCallableBoundaryId>,
    ) -> Result<Var, FatalError> {
        match self.world.transport().interners().shape(shape).clone() {
            ShapeDescr::Nothing => Err(FatalError),
            ShapeDescr::Lane(_) => lanes.first().copied().ok_or(FatalError),
            ShapeDescr::Tuple(fields) => {
                let mut vars = Vec::with_capacity(fields.len());
                for field in self.transport_field_views(shape, lanes, &fields)? {
                    vars.push(self.materialize_native_value(ctx, None, &field)?);
                }
                Ok(ctx.emit_let(Prim::MakeTuple(vars)).0)
            }
            ShapeDescr::Callable(callable) => {
                let descr = self.world.transport().interners().callable(callable);
                if descr.function.is_none() && lanes.len() == 1 {
                    return Ok(lanes[0]);
                }
                if lanes.len() != descr.capture_lanes.len() {
                    return Err(FatalError);
                }
                let function = descr.function.ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!(
                            "native attempted to rematerialize generic callable shape {:?} in {:?}; first-class callable values must come from transport publication lanes",
                            shape, ctx.origin,
                        ),
                    )
                })?;
                let capture_count = descr.capture_lanes.len();
                let identity = self.callable_identity(function, capture_count);
                let boundary = match boundary {
                    Some(boundary) => boundary,
                    None => self.settled_callable_boundary(callable, function, capture_count)?,
                };
                let prim = if lanes.is_empty() {
                    Prim::MakeFnRef(ctx.fresh_callsite(), identity)
                } else {
                    Prim::MakeClosure(ctx.fresh_callsite(), identity, lanes.to_vec())
                };
                let (var, _) = ctx.emit_let(prim);
                ctx.callable_value_boundaries.insert(var, boundary);
                Ok(var)
            }
        }
    }

    fn transport_tuple_arity(&self, value: &NativeBoundValue) -> Option<usize> {
        let NativeBoundValue::Transport { shape, .. } = value else {
            return None;
        };
        match self.world.transport().interners().shape(*shape) {
            ShapeDescr::Tuple(fields) => Some(fields.len()),
            ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => None,
        }
    }

    fn transport_tuple_field(
        &self,
        value: &NativeBoundValue,
        index: usize,
    ) -> Result<Option<NativeBoundValue>, FatalError> {
        let NativeBoundValue::Transport { shape, lanes } = value else {
            return Ok(None);
        };
        let ShapeDescr::Tuple(fields) = self.world.transport().interners().shape(*shape).clone() else {
            return Ok(None);
        };
        Ok(Some(
            self.transport_field_views(*shape, lanes, &fields)?
                .get(index)
                .cloned()
                .ok_or(FatalError)?,
        ))
    }

    fn direct_callable_lanes(&self, value: &NativeBoundValue) -> Result<Option<Vec<Var>>, FatalError> {
        let NativeBoundValue::Transport { shape, lanes } = value else {
            return Ok(None);
        };
        let ShapeDescr::Callable(callable) = self.world.transport().interners().shape(*shape) else {
            return Ok(None);
        };
        let descr = self.world.transport().interners().callable(*callable);
        if descr.function.is_none() {
            return Ok(None);
        }
        if lanes.len() != descr.capture_lanes.len() {
            return Err(FatalError);
        }
        Ok(Some(lanes.clone()))
    }

    fn tuple_field_values_for_shape(
        &mut self,
        ctx: &mut NativeFnCtx,
        value: &NativeBoundValue,
        shape: ShapeId,
        fields: &[ShapeId],
    ) -> Result<Vec<NativeBoundValue>, FatalError> {
        if let NativeBoundValue::Transport {
            shape: value_shape,
            lanes,
        } = value
            && *value_shape == shape
        {
            return self.transport_field_views(shape, lanes, fields);
        }
        let tuple = self.materialize_native_value(ctx, None, value)?;
        Ok(fields
            .iter()
            .enumerate()
            .map(|(index, _)| {
                let (var, _) = ctx.emit_let(Prim::TupleField(tuple, index as u32));
                NativeBoundValue::Runtime(var)
            })
            .collect())
    }

    fn transport_field_views(
        &self,
        shape: ShapeId,
        lanes: &[Var],
        fields: &[ShapeId],
    ) -> Result<Vec<NativeBoundValue>, FatalError> {
        if lanes.len() != self.world.transport().interners().shape_width(shape) {
            return Err(FatalError);
        }
        let mut offset = 0_usize;
        let mut values = Vec::with_capacity(fields.len());
        for field in fields.iter().copied() {
            let width = self.world.transport().interners().shape_width(field);
            let end = offset.checked_add(width).ok_or(FatalError)?;
            let field_lanes = lanes.get(offset..end).ok_or(FatalError)?.to_vec();
            let value = match self.world.transport().interners().shape(field) {
                ShapeDescr::Nothing => NativeBoundValue::Absent,
                ShapeDescr::Lane(_) => NativeBoundValue::Runtime(*field_lanes.first().ok_or(FatalError)?),
                ShapeDescr::Tuple(_) | ShapeDescr::Callable(_) => NativeBoundValue::Transport {
                    shape: field,
                    lanes: field_lanes,
                },
            };
            values.push(value);
            offset = end;
        }
        Ok(values)
    }

    fn encode_runtime_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value_id: Option<ValueId>,
        value: &NativeBoundValue,
        shape: ShapeId,
        lanes: &mut Vec<Var>,
    ) -> Result<(), FatalError> {
        if let NativeBoundValue::Transport {
            shape: value_shape,
            lanes: value_lanes,
        } = value
            && *value_shape == shape
        {
            lanes.extend(value_lanes.iter().copied());
            return Ok(());
        }
        match self.world.transport().interners().shape(shape).clone() {
            ShapeDescr::Nothing => Ok(()),
            ShapeDescr::Lane(lane) => {
                let ty = value_id
                    .and_then(|value_id| executable.value_types.get(&value_id).copied())
                    .unwrap_or_else(|| self.world.transport().interners().lane(lane).ty);
                lanes.push(self.materialize_native_value(ctx, Some(ty), value)?);
                Ok(())
            }
            ShapeDescr::Tuple(fields) => {
                let tuple_fields = self.tuple_field_values_for_shape(ctx, value, shape, &fields)?;
                for (field, field_shape) in tuple_fields.iter().zip(fields.iter().copied()) {
                    self.encode_runtime_value(ctx, executable, None, field, field_shape, lanes)?;
                }
                Ok(())
            }
            ShapeDescr::Callable(callable) => Err(incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "native attempted to encode callable shape {:?} ({:?}) for value {:?} from {:?}; callable values must be supplied by matching transport lanes or a published value seam",
                    shape,
                    self.world.transport().interners().callable(callable),
                    value_id,
                    value,
                ),
            )),
        }
    }

    fn encode_env_value_for_shape(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        value_id: ValueId,
        shape: ShapeId,
        lanes: &mut Vec<Var>,
    ) -> Result<(), FatalError> {
        if matches!(self.world.transport().interners().shape(shape), ShapeDescr::Nothing) {
            return Ok(());
        }
        let local = env
            .cloned_value(value_id)
            .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
        self.encode_runtime_value(ctx, executable, Some(value_id), &local, shape, lanes)
    }
}

fn entry_fn_ids(module: &mut ModuleBuilder, entries: &[BackendEntry]) -> HashMap<ControlEntryId, FnId> {
    let mut out = HashMap::new();
    for (index, entry) in entries.iter().enumerate() {
        if matches!(entry.origin, BackendEntryOrigin::Clause) {
            continue;
        }
        out.insert(ControlEntryId::from_u32(index as u32), module.fresh_fn_id());
    }
    out
}

fn annotate_back_edges(module: &mut crate::fz_ir::Module) {
    // The SCC graph must carry EVERY static control successor, not just
    // TailCall edges: a recursion cycle threaded through a Call continuation
    // (caller -Call-> kernel, whose return chains into a resume fn that
    // TailCalls the entry) is invisible to a TailCall-only graph, and its
    // closing tail call would never be marked — a frame-flat loop that spends
    // no reductions. Closure callees have no static target at this level and
    // are conservatively absent; their continuations still contribute.
    let mut graph: HashMap<FnId, HashSet<FnId>> = HashMap::new();
    for function in &module.fns {
        let entry = graph.entry(function.id).or_default();
        for block in &function.blocks {
            match &block.terminator {
                Term::TailCall { callee, .. } => {
                    if let Some(callee) = callee.local_fn_id() {
                        entry.insert(callee);
                    }
                }
                Term::Call {
                    callee, continuation, ..
                } => {
                    if let Some(callee) = callee.local_fn_id() {
                        entry.insert(callee);
                    }
                    entry.insert(continuation.fn_id);
                }
                Term::CallClosure { continuation, .. } => {
                    entry.insert(continuation.fn_id);
                }
                Term::ReceiveMatched { clauses, after, .. } => {
                    for clause in clauses {
                        entry.insert(clause.body);
                        if let Some(guard) = clause.guard {
                            entry.insert(guard);
                        }
                    }
                    if let Some(after) = after {
                        entry.insert(after.body);
                    }
                }
                Term::TailCallClosure { .. }
                | Term::Goto(..)
                | Term::If { .. }
                | Term::Return(_)
                | Term::ReturnLanes(_)
                | Term::Halt(_) => {}
            }
        }
    }

    let scc_of = {
        let mut index_counter = 0usize;
        let mut stack = Vec::new();
        let mut on_stack = HashSet::new();
        let mut index = HashMap::new();
        let mut lowlink = HashMap::new();
        let mut scc_of = HashMap::new();
        let mut scc_count = 0usize;
        let all_fns = module.fns.iter().map(|function| function.id).collect::<Vec<_>>();

        fn strongconnect(
            function: FnId,
            graph: &HashMap<FnId, HashSet<FnId>>,
            index_counter: &mut usize,
            stack: &mut Vec<FnId>,
            on_stack: &mut HashSet<FnId>,
            index: &mut HashMap<FnId, usize>,
            lowlink: &mut HashMap<FnId, usize>,
            scc_of: &mut HashMap<FnId, usize>,
            scc_count: &mut usize,
        ) {
            let function_index = *index_counter;
            index.insert(function, function_index);
            lowlink.insert(function, function_index);
            *index_counter += 1;
            stack.push(function);
            on_stack.insert(function);

            if let Some(neighbors) = graph.get(&function) {
                for neighbor in neighbors.iter().copied().collect::<Vec<_>>() {
                    if !index.contains_key(&neighbor) {
                        strongconnect(
                            neighbor,
                            graph,
                            index_counter,
                            stack,
                            on_stack,
                            index,
                            lowlink,
                            scc_of,
                            scc_count,
                        );
                        let neighbor_lowlink = lowlink[&neighbor];
                        let function_lowlink = lowlink.get_mut(&function).expect("function lowlink");
                        if neighbor_lowlink < *function_lowlink {
                            *function_lowlink = neighbor_lowlink;
                        }
                    } else if on_stack.contains(&neighbor) {
                        let neighbor_index = index[&neighbor];
                        let function_lowlink = lowlink.get_mut(&function).expect("function lowlink");
                        if neighbor_index < *function_lowlink {
                            *function_lowlink = neighbor_index;
                        }
                    }
                }
            }

            if lowlink[&function] == index[&function] {
                let scc_id = *scc_count;
                *scc_count += 1;
                loop {
                    let member = stack.pop().expect("SCC stack member");
                    on_stack.remove(&member);
                    scc_of.insert(member, scc_id);
                    if member == function {
                        break;
                    }
                }
            }
        }

        for function in &all_fns {
            if !index.contains_key(function) {
                strongconnect(
                    *function,
                    &graph,
                    &mut index_counter,
                    &mut stack,
                    &mut on_stack,
                    &mut index,
                    &mut lowlink,
                    &mut scc_of,
                    &mut scc_count,
                );
            }
        }
        scc_of
    };

    for function in &mut module.fns {
        let caller_scc = scc_of.get(&function.id).copied().unwrap_or(usize::MAX);
        for block in &mut function.blocks {
            if let Term::TailCall {
                callee, is_back_edge, ..
            } = &mut block.terminator
            {
                let Some(callee) = callee.local_fn_id() else {
                    continue;
                };
                let callee_scc = scc_of.get(&callee).copied().unwrap_or(usize::MAX);
                if callee_scc == caller_scc {
                    *is_back_edge = true;
                }
            }
        }
    }
}

/// Native lowering cache for already-emitted IR artifacts.
///
/// Shape and lane layout stay in `TransportPlan`; this cache only remembers
/// whether a semantic value is already materialized as one runtime var, is a
/// direct callable represented by its transport callable id plus capture lanes,
/// or has no transported value.
type NativeBoundValue = TransportValue<Var>;

#[derive(Default, Clone)]
struct ValueEnv {
    values: HashMap<ValueId, NativeBoundValue>,
}

impl ValueEnv {
    fn insert(&mut self, value: ValueId, bound: NativeBoundValue) {
        self.values.insert(value, bound);
    }

    fn value(&self, value: ValueId) -> Option<&NativeBoundValue> {
        self.values.get(&value)
    }

    fn cloned_value(&self, value: ValueId) -> Option<NativeBoundValue> {
        self.value(value).cloned()
    }

    fn runtime_var(&self, value: ValueId) -> Option<Var> {
        self.value(value).and_then(TransportValue::runtime_lane)
    }
}

fn shape_lane_tys(world: &World<'_>, shape: ShapeId) -> Vec<Ty> {
    world
        .transport()
        .interners()
        .shape_lane_ids(shape)
        .into_iter()
        .map(|lane| world.transport().interners().lane(lane).ty)
        .collect()
}

fn position_shape(program: &BackendProgram, position: &TransportPosition) -> ShapeId {
    program
        .transport
        .position_shapes
        .iter()
        .find_map(|(candidate, shape)| (candidate == position).then_some(*shape))
        .unwrap_or_else(|| panic!("backend transport handoff should publish shape for {position:?}"))
}

fn native_return_contract(
    world: &World<'_>,
    program: &BackendProgram,
    position: &TransportPosition,
) -> (Vec<AbiValueRepr>, Option<usize>) {
    let shape = position_shape(program, position);
    let reprs = seam_reprs_for_position_shape(world, program, position, shape, |seam| {
        matches!(
            (position, seam),
            (
                TransportPosition::ExecutableReturn { executable: position_executable },
                CodegenSeam::ReturnDelivery { executable: seam_executable }
            ) if position_executable == seam_executable
        )
    });
    let tuple_arity = match world.transport().interners().shape(shape) {
        ShapeDescr::Tuple(fields) => Some(fields.len()),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => None,
    };
    (reprs, tuple_arity)
}

fn native_block_param_reprs(
    world: &mut World<'_>,
    fn_ir: &crate::fz_ir::FnIr,
    value_types: &HashMap<Var, Ty>,
) -> HashMap<Var, AbiValueRepr> {
    let mut reprs = HashMap::new();
    for block in &fn_ir.blocks {
        for param in &block.params {
            let ty = value_types
                .get(param)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            reprs.insert(*param, block_param_abi_value_repr(world, ty));
        }
    }
    reprs
}

fn continuation_result_entry(
    world: &World<'_>,
    program: &BackendProgram,
    position: &TransportPosition,
) -> (Vec<Ty>, Vec<AbiValueRepr>) {
    let shape = position_shape(program, position);
    let seam_matches = |seam: &CodegenSeam| continuation_seam_matches(position, seam);
    let publication_lanes = position_publication_lanes(program, seam_matches);
    if !publication_lanes.is_empty() {
        let tys = publication_lanes
            .iter()
            .copied()
            .map(|lane| world.transport().interners().lane(lane).ty)
            .collect();
        let reprs = publication_lanes
            .iter()
            .copied()
            .map(|lane| seam_repr_for_lane(program, &seam_matches, None, lane))
            .collect();
        return (tys, reprs);
    }
    let reprs = seam_reprs_for_position_shape(world, program, position, shape, seam_matches);
    (shape_lane_tys(world, shape), reprs)
}

fn return_payload_entry(
    world: &World<'_>,
    program: &BackendProgram,
    position: &TransportPosition,
) -> (Vec<Ty>, Vec<AbiValueRepr>) {
    let shape = position_shape(program, position);
    let seam_matches = |seam: &CodegenSeam| return_payload_seam_matches(position, seam);
    let publication_lanes = position_publication_lanes(program, seam_matches);
    if !publication_lanes.is_empty() {
        let tys = publication_lanes
            .iter()
            .copied()
            .map(|lane| world.transport().interners().lane(lane).ty)
            .collect();
        let reprs = publication_lanes
            .iter()
            .copied()
            .map(|lane| seam_repr_for_lane(program, &seam_matches, None, lane))
            .collect();
        return (tys, reprs);
    }
    let reprs = seam_reprs_for_position_shape(world, program, position, shape, seam_matches);
    (shape_lane_tys(world, shape), reprs)
}

fn continuation_seam_matches(position: &TransportPosition, seam: &CodegenSeam) -> bool {
    matches!(
        (position, seam),
        (
            TransportPosition::ResumePayload {
                executable: position_executable,
                callsite: Some(position_callsite),
                entry: position_entry,
            },
            CodegenSeam::ContinuationEntry {
                executable: seam_executable,
                callsite: seam_callsite,
                entry: seam_entry,
            }
        ) if position_executable == seam_executable
            && position_callsite == seam_callsite
            && position_entry == seam_entry
    ) || matches!(
        (position, seam),
        (
            TransportPosition::ResumePayload {
                executable: position_executable,
                callsite: None,
                entry: position_entry,
            },
            CodegenSeam::BlockParam {
                executable: seam_executable,
                entry: seam_entry,
            }
        ) if position_executable == seam_executable && position_entry == seam_entry
    )
}

fn return_payload_seam_matches(position: &TransportPosition, seam: &CodegenSeam) -> bool {
    matches!(
        (position, seam),
        (
            TransportPosition::ReturnPayload {
                executable: position_executable,
                callsite: position_callsite,
            },
            CodegenSeam::ReturnContinuation {
                executable: seam_executable,
                callsite: seam_callsite,
            }
        ) if position_executable == seam_executable && position_callsite == seam_callsite
    )
}

fn seam_reprs_for_position_shape(
    world: &World<'_>,
    program: &BackendProgram,
    _position: &TransportPosition,
    shape: ShapeId,
    seam_matches: impl Fn(&CodegenSeam) -> bool,
) -> Vec<AbiValueRepr> {
    world
        .transport()
        .interners()
        .shape_leaf_lanes(shape)
        .into_iter()
        .map(|(leaf_shape, lane)| seam_repr_for_lane(program, &seam_matches, Some(leaf_shape), lane))
        .collect()
}

fn callable_boundary_reprs(
    program: &BackendProgram,
    boundary: super::super::transport::BoundaryId,
    lanes: &[LaneId],
) -> Vec<AbiValueRepr> {
    lanes
        .iter()
        .copied()
        .map(|lane| {
            seam_repr_for_lane(
                program,
                &|seam| matches!(seam, CodegenSeam::CallableBoundary { boundary: candidate } if *candidate == boundary),
                None,
                lane,
            )
        })
        .collect()
}

fn function_entry_publication_lanes(
    program: &BackendProgram,
    executable: &super::super::transport::ExecutableSymbol,
    semantic_index: usize,
) -> Vec<LaneId> {
    position_publication_lanes(program, |seam| {
        matches!(
            seam,
            CodegenSeam::FunctionEntry {
                executable: candidate,
                semantic_index: candidate_index,
            } if candidate == executable && *candidate_index == semantic_index
        )
    })
}

fn position_publication_lanes(program: &BackendProgram, seam_matches: impl Fn(&CodegenSeam) -> bool) -> Vec<LaneId> {
    program
        .transport
        .codegen_seam_facts
        .iter()
        .filter(|fact| fact.shape.is_none() && seam_matches(&fact.seam))
        .map(|fact| fact.lane)
        .collect()
}

fn position_width(world: &World<'_>, shape: ShapeId, publication_lanes: &[LaneId]) -> usize {
    if publication_lanes.is_empty() {
        world.transport().interners().shape_width(shape)
    } else {
        publication_lanes.len()
    }
}

fn entry_capture_reprs(world: &World<'_>, program: &BackendProgram, entry: &BackendEntry) -> Vec<AbiValueRepr> {
    entry
        .capture_positions
        .iter()
        .flat_map(|position| {
            let shape = position_shape(program, position);
            seam_reprs_for_position_shape(world, program, position, shape, |seam| {
                entry_capture_seam_matches(entry, position, seam)
            })
        })
        .collect()
}

fn entry_capture_seam_matches(entry: &BackendEntry, position: &TransportPosition, seam: &CodegenSeam) -> bool {
    let TransportPosition::EntryCapture {
        executable,
        entry: captured_entry,
        ..
    } = position
    else {
        return false;
    };
    if let BackendEntryOrigin::DeliveredResume {
        position: TransportPosition::ResumePayload {
            callsite: Some(callsite),
            ..
        },
        ..
    } = &entry.origin
    {
        return matches!(
            seam,
            CodegenSeam::ContinuationEntry {
                executable: seam_executable,
                callsite: seam_callsite,
                entry: seam_entry,
            } if seam_executable == executable && seam_callsite == callsite && seam_entry == captured_entry
        );
    }
    matches!(
        seam,
        CodegenSeam::BlockParam {
            executable: seam_executable,
            entry: seam_entry,
        } if seam_executable == executable && seam_entry == captured_entry
    )
}

fn seam_repr_for_lane(
    program: &BackendProgram,
    seam_matches: &impl Fn(&CodegenSeam) -> bool,
    shape: Option<ShapeId>,
    lane: LaneId,
) -> AbiValueRepr {
    let fact = program
        .transport
        .codegen_seam_facts
        .iter()
        .find(|fact| seam_matches(&fact.seam) && fact.shape == shape && fact.lane == lane)
        .unwrap_or_else(|| panic!("backend transport handoff should publish seam fact for {shape:?} {lane:?}"));
    abi_repr_from_codegen(fact.repr)
}

fn abi_repr_from_codegen(repr: CodegenLaneRepr) -> AbiValueRepr {
    match repr {
        CodegenLaneRepr::ValueRef => AbiValueRepr::ValueRef,
        CodegenLaneRepr::RawInt => AbiValueRepr::RawInt,
        CodegenLaneRepr::RawF64 => AbiValueRepr::RawF64,
        CodegenLaneRepr::RawAtom => AbiValueRepr::RawAtom,
    }
}

#[derive(Clone)]
struct DispatchState {
    dispatch_inputs: Vec<Var>,
    forwarded_args: Vec<Var>,
    pinned: Vec<Var>,
    values: HashMap<SubjectId, Var>,
}

impl DispatchState {
    fn new(dispatch_inputs: Vec<Var>, forwarded_args: Vec<Var>, pinned: Vec<Var>) -> Self {
        Self {
            dispatch_inputs,
            forwarded_args,
            pinned,
            values: HashMap::new(),
        }
    }
}

struct NativeFnCtx {
    fn_id: FnId,
    builder: FnBuilder,
    current_block: BlockId,
    stmt_counts: HashMap<BlockId, usize>,
    value_types: HashMap<Var, Ty>,
    callable_value_boundaries: HashMap<Var, NativeCallableBoundaryId>,
    extern_marshals: HashMap<ExternMarshalSite, ExternTy>,
    failure_blocks: HashMap<u32, BlockId>,
    origin: NativeBodyOrigin,
    entry_abi: NativeEntryAbi,
    param_reprs: Vec<AbiValueRepr>,
    return_ty: Ty,
    return_position: TransportPosition,
    return_reprs: Vec<AbiValueRepr>,
    return_tuple_arity: Option<usize>,
    effects: EffectSummary,
    next_token: u32,
}

impl NativeFnCtx {
    fn new(
        fn_id: FnId,
        name: &str,
        category: FnCategory,
        origin: NativeBodyOrigin,
        entry_abi: NativeEntryAbi,
        param_reprs: Vec<AbiValueRepr>,
        return_ty: Ty,
        return_position: TransportPosition,
        return_reprs: Vec<AbiValueRepr>,
        return_tuple_arity: Option<usize>,
        effects: EffectSummary,
    ) -> Self {
        let builder = FnBuilder::new(fn_id, name.to_string()).with_category(category);
        Self {
            fn_id,
            builder,
            current_block: BlockId(0),
            stmt_counts: HashMap::new(),
            value_types: HashMap::new(),
            callable_value_boundaries: HashMap::new(),
            extern_marshals: HashMap::new(),
            failure_blocks: HashMap::new(),
            origin,
            entry_abi,
            param_reprs,
            return_ty,
            return_position,
            return_reprs,
            return_tuple_arity,
            effects,
            next_token: 0,
        }
    }

    fn entry_params(&mut self, tys: &[Ty]) -> Vec<Var> {
        let params = tys.iter().map(|_| self.builder.fresh_var()).collect::<Vec<_>>();
        self.current_block = self.builder.block(params.clone());
        for (param, ty) in params.iter().copied().zip(tys.iter().copied()) {
            self.value_types.insert(param, ty);
        }
        params
    }

    fn emit_let(&mut self, prim: Prim) -> (Var, usize) {
        let stmt_idx = self.stmt_counts.entry(self.current_block).or_insert(0);
        let idx = *stmt_idx;
        *stmt_idx += 1;
        let var = self.builder.let_(self.current_block, prim);
        (var, idx)
    }

    fn fresh_callsite(&self) -> CallsiteIdent {
        CallsiteIdent::from_source(Span::DUMMY)
    }

    fn fresh_token(&mut self) -> InitTokenId {
        let token = InitTokenId(self.next_token);
        self.next_token += 1;
        token
    }

    fn set_term(&mut self, term: Term) {
        self.builder.set_terminator(self.current_block, term);
    }

    fn halt_with_atom(&mut self, atom: u32) {
        let (reason, _) = self.emit_let(Prim::Const(Const::Atom(atom)));
        self.set_term(Term::Halt(reason));
    }

    fn assert_truthy(&mut self, cond: Var, fail_atom: u32) {
        let pass = self.builder.block(Vec::new());
        let fail = if let Some(fail) = self.failure_blocks.get(&fail_atom).copied() {
            fail
        } else {
            let saved = self.current_block;
            let fail = self.builder.block(Vec::new());
            self.current_block = fail;
            let (reason, _) = self.emit_let(Prim::Const(Const::Atom(fail_atom)));
            self.set_term(Term::Halt(reason));
            self.current_block = saved;
            self.failure_blocks.insert(fail_atom, fail);
            fail
        };
        self.set_term(Term::If {
            cond,
            then_b: pass,
            else_b: fail,
            origin: BranchOrigin::PatternBind,
        });
        self.current_block = pass;
    }

    fn finish(self) -> (crate::fz_ir::FnIr, NativeBody) {
        let fn_ir = self.builder.build();
        let body = NativeBody {
            fn_id: self.fn_id,
            origin: self.origin,
            entry_abi: self.entry_abi,
            param_reprs: self.param_reprs,
            return_ty: self.return_ty,
            return_position: self.return_position,
            return_reprs: self.return_reprs,
            return_tuple_arity: self.return_tuple_arity,
            block_param_reprs: HashMap::new(),
            value_types: self.value_types,
            callable_value_boundaries: self.callable_value_boundaries,
            extern_marshals: self.extern_marshals,
            effects: self.effects,
        };
        (fn_ir, body)
    }
}

fn env_local_value(env: &ValueEnv, value: ValueId) -> Result<NativeBoundValue, FatalError> {
    env.cloned_value(value).ok_or(FatalError)
}

fn executable_input_tys(world: &World<'_>, program: &BackendProgram, executable: &BackendExecutable) -> Vec<Ty> {
    executable_input_bindings(program, executable)
        .into_iter()
        .flat_map(|binding| {
            if binding.publication_lanes.is_empty() {
                shape_lane_tys(world, binding.shape)
            } else {
                binding
                    .publication_lanes
                    .into_iter()
                    .map(|lane| world.transport().interners().lane(lane).ty)
                    .collect()
            }
        })
        .collect()
}

fn bind_executable_inputs(
    world: &World<'_>,
    program: &BackendProgram,
    executable: &BackendExecutable,
    ctx: &mut NativeFnCtx,
    params: &[Var],
) -> Result<Vec<Option<NativeBoundValue>>, FatalError> {
    let semantic_arity = executable.key.activation.input.len();
    let mut bound = vec![None; semantic_arity];
    let mut lane_index = 0;
    for binding in executable_input_bindings(program, executable) {
        bound[binding.semantic_index] = Some(decode_runtime_value_with_width(
            params,
            binding.shape,
            binding.width(world),
            !binding.publication_lanes.is_empty(),
            world,
            ctx,
            &mut lane_index,
        )?);
    }
    if lane_index != params.len() {
        return Err(FatalError);
    }
    Ok(bound)
}

#[derive(Clone)]
struct ExecutableInputBinding {
    position: TransportPosition,
    semantic_index: usize,
    shape: ShapeId,
    publication_lanes: Vec<LaneId>,
}

impl ExecutableInputBinding {
    fn width(&self, world: &World<'_>) -> usize {
        if self.publication_lanes.is_empty() {
            world.transport().interners().shape_width(self.shape)
        } else {
            self.publication_lanes.len()
        }
    }
}

fn executable_input_bindings(program: &BackendProgram, executable: &BackendExecutable) -> Vec<ExecutableInputBinding> {
    let mut inputs = executable
        .transport
        .input_positions
        .iter()
        .filter_map(|position| {
            let TransportPosition::ExecutableInput {
                executable,
                semantic_index,
            } = position
            else {
                return None;
            };
            Some(ExecutableInputBinding {
                position: position.clone(),
                semantic_index: *semantic_index,
                shape: position_shape(program, position),
                publication_lanes: function_entry_publication_lanes(program, executable, *semantic_index),
            })
        })
        .collect::<Vec<_>>();
    inputs.sort_by_key(|binding| binding.semantic_index);
    inputs.dedup_by_key(|binding| binding.semantic_index);
    inputs
}

fn executable_input_shapes(program: &BackendProgram, executable: &BackendExecutable) -> Vec<(usize, ShapeId)> {
    executable_input_bindings(program, executable)
        .into_iter()
        .map(|binding| (binding.semantic_index, binding.shape))
        .collect()
}

fn value_shape(program: &BackendProgram, executable: &BackendExecutable, value: ValueId) -> ShapeId {
    maybe_value_shape(program, executable, value)
        .unwrap_or_else(|| panic!("backend transport handoff should publish value position for {value:?}"))
}

fn maybe_value_shape(program: &BackendProgram, executable: &BackendExecutable, value: ValueId) -> Option<ShapeId> {
    let position = executable.transport.value_positions.iter().find(
        |position| matches!(position, TransportPosition::Value { value: candidate, .. } if *candidate == value),
    )?;
    Some(position_shape(program, position))
}

/// Decode one value from a transport seam. The seam shape is consumed here and
/// not stored in the native value cache.
fn decode_runtime_value(
    world: &World<'_>,
    ctx: &mut NativeFnCtx,
    params: &[Var],
    shape: ShapeId,
    lane_index: &mut usize,
) -> Result<NativeBoundValue, FatalError> {
    decode_runtime_value_with_width(
        params,
        shape,
        world.transport().interners().shape_width(shape),
        false,
        world,
        ctx,
        lane_index,
    )
}

fn decode_runtime_value_with_width(
    params: &[Var],
    shape: ShapeId,
    width: usize,
    published_value: bool,
    world: &World<'_>,
    ctx: &mut NativeFnCtx,
    lane_index: &mut usize,
) -> Result<NativeBoundValue, FatalError> {
    let end = lane_index.checked_add(width).ok_or(FatalError)?;
    let lanes = params.get(*lane_index..end).ok_or(FatalError)?.to_vec();
    *lane_index = end;
    if published_value {
        if lanes.is_empty() {
            return Err(FatalError);
        }
        return Ok(NativeBoundValue::Transport { shape, lanes });
    }
    decode_native_value_from_lanes(world, ctx, shape, lanes)
}

fn decode_native_value_from_lanes(
    world: &World<'_>,
    _ctx: &mut NativeFnCtx,
    shape: ShapeId,
    lanes: Vec<Var>,
) -> Result<NativeBoundValue, FatalError> {
    if lanes.len() != world.transport().interners().shape_width(shape) {
        return Err(FatalError);
    }
    Ok(match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => NativeBoundValue::Absent,
        ShapeDescr::Lane(_) => NativeBoundValue::Runtime(*lanes.first().ok_or(FatalError)?),
        ShapeDescr::Tuple(_) | ShapeDescr::Callable(_) => NativeBoundValue::Transport { shape, lanes },
    })
}

fn callable_id_for_shape(world: &World<'_>, shape: ShapeId) -> Result<CallableId, FatalError> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Callable(callable) => Ok(*callable),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Tuple(_) => Err(FatalError),
    }
}

fn bind_local_value(
    ctx: &mut NativeFnCtx,
    executable: &BackendExecutable,
    env: &mut ValueEnv,
    value: ValueId,
    bound: NativeBoundValue,
) {
    if let Some(var) = bound.runtime_lane()
        && let Some(ty) = executable.value_types.get(&value).copied()
    {
        ctx.value_types.insert(var, ty);
    }
    env.insert(value, bound);
}

fn collect_callable_identity_needs(program: &BackendProgram) -> Vec<(FunctionId, usize)> {
    let mut seen = HashSet::new();
    let mut out = Vec::new();
    for entry in &program.callable_entries {
        let function = program.executables[entry.target].key.activation.function;
        if seen.insert((function, entry.capture_count)) {
            out.push((function, entry.capture_count));
        }
    }
    for executable in &program.executables {
        match &executable.body {
            BackendBody::Extern { .. } => {}
            BackendBody::Clauses { clauses, entries, .. } => {
                for clause in clauses {
                    collect_callable_identity_needs_in_steps(&clause.projections, &mut seen, &mut out);
                }
                for entry in entries {
                    collect_callable_identity_needs_in_steps(&entry.steps, &mut seen, &mut out);
                }
            }
        }
    }
    out
}

fn collect_callable_identity_needs_in_steps(
    steps: &[BackendStep],
    seen: &mut HashSet<(FunctionId, usize)>,
    out: &mut Vec<(FunctionId, usize)>,
) {
    for step in steps {
        match step {
            BackendStep::FunctionRef { function, .. } => {
                if seen.insert((*function, 0)) {
                    out.push((*function, 0));
                }
            }
            BackendStep::Lambda { function, captures, .. } => {
                let key = (*function, captures.len());
                if seen.insert(key) {
                    out.push(key);
                }
            }
            _ => {}
        }
    }
}

fn collect_extern_marshals(
    world: &World<'_>,
    root_id: RootId,
    program: &BackendProgram,
) -> Result<HashMap<usize, Vec<ExternTy>>, FatalError> {
    let mut out = HashMap::new();
    for executable in &program.executables {
        if let BackendBody::Clauses { clauses, entries, .. } = &executable.body {
            for clause in clauses {
                collect_extern_marshals_in_steps(world, root_id, program, &clause.projections, &mut out)?;
            }
            for entry in entries {
                collect_extern_marshals_in_tail(world, root_id, program, &entry.tail, &mut out)?;
            }
        }
    }
    Ok(out)
}

fn collect_extern_marshals_in_steps(
    _world: &World<'_>,
    _root_id: RootId,
    _program: &BackendProgram,
    _steps: &[BackendStep],
    _out: &mut HashMap<usize, Vec<ExternTy>>,
) -> Result<(), FatalError> {
    Ok(())
}

fn collect_extern_marshals_in_tail(
    world: &World<'_>,
    root_id: RootId,
    program: &BackendProgram,
    tail: &BackendTail,
    out: &mut HashMap<usize, Vec<ExternTy>>,
) -> Result<(), FatalError> {
    if let BackendTail::DirectCall {
        callee,
        extern_marshals,
        ..
    } = tail
        && let CallTarget::Local(callee) = callee
        && matches!(program.executables[*callee].body, BackendBody::Extern { .. })
    {
        let signature = match &program.executables[*callee].body {
            BackendBody::Extern { signature } => signature,
            BackendBody::Clauses { .. } => unreachable!(),
        };
        let marshals = extern_marshals.clone().unwrap_or_else(|| signature.params.clone());
        match out.get(callee) {
            Some(existing) if existing != &marshals => {
                return Err(incomplete_native_program(
                    world,
                    root_id,
                    format!(
                        "extern executable {} has conflicting marshal plans: {:?} vs {:?}",
                        callee, existing, marshals
                    ),
                ));
            }
            Some(_) => {}
            None => {
                out.insert(*callee, marshals);
            }
        }
    }
    Ok(())
}

fn lower_backend_literal(
    ctx: &mut NativeFnCtx,
    atom_ids: &HashMap<String, u32>,
    literal: &Literal,
) -> Result<Var, FatalError> {
    Ok(match literal {
        Literal::Int(value) => ctx.emit_let(Prim::Const(Const::Int(*value))).0,
        Literal::Float(value) => ctx.emit_let(Prim::Const(Const::Float(*value))).0,
        Literal::Atom(name) => {
            ctx.emit_let(Prim::Const(Const::Atom(*atom_ids.get(name).ok_or(FatalError)?)))
                .0
        }
        Literal::Bool(true) => ctx.emit_let(Prim::Const(Const::True)).0,
        Literal::Bool(false) => ctx.emit_let(Prim::Const(Const::False)).0,
        Literal::Nil => ctx.emit_let(Prim::Const(Const::Nil)).0,
        Literal::Binary(bytes) => {
            ctx.emit_let(Prim::ConstBitstring(bytes.clone(), (bytes.len() * 8) as u64))
                .0
        }
    })
}

fn lower_dispatch_const(
    ctx: &mut NativeFnCtx,
    atom_ids: &HashMap<String, u32>,
    value: &DispatchConst,
) -> Result<Var, FatalError> {
    Ok(match value {
        DispatchConst::Int(value) => ctx.emit_let(Prim::Const(Const::Int(*value))).0,
        DispatchConst::FloatBits(bits) => ctx.emit_let(Prim::Const(Const::Float(f64::from_bits(*bits)))).0,
        DispatchConst::AtomName(name) => {
            let atom = *atom_ids.get(name).ok_or(FatalError)?;
            ctx.emit_let(Prim::Const(Const::Atom(atom))).0
        }
        DispatchConst::Bool(true) => ctx.emit_let(Prim::Const(Const::True)).0,
        DispatchConst::Bool(false) => ctx.emit_let(Prim::Const(Const::False)).0,
        DispatchConst::Nil => ctx.emit_let(Prim::Const(Const::Nil)).0,
        DispatchConst::Utf8Binary(bytes) => {
            ctx.emit_let(Prim::ConstBitstring(bytes.clone(), (bytes.len() * 8) as u64))
                .0
        }
        DispatchConst::EmptyList => {
            return Err(FatalError);
        }
    })
}

fn lower_binop(op: crate::ast::BinOp) -> IrBinOp {
    match op {
        crate::ast::BinOp::Add => IrBinOp::Add,
        crate::ast::BinOp::Sub => IrBinOp::Sub,
        crate::ast::BinOp::Mul => IrBinOp::Mul,
        crate::ast::BinOp::Div => IrBinOp::Div,
        crate::ast::BinOp::Rem => IrBinOp::Mod,
        crate::ast::BinOp::Eq => IrBinOp::Eq,
        crate::ast::BinOp::Neq => IrBinOp::Neq,
        crate::ast::BinOp::Lt => IrBinOp::Lt,
        crate::ast::BinOp::LtEq => IrBinOp::Le,
        crate::ast::BinOp::Gt => IrBinOp::Gt,
        crate::ast::BinOp::GtEq => IrBinOp::Ge,
        crate::ast::BinOp::And => IrBinOp::And,
        crate::ast::BinOp::Or => IrBinOp::Or,
        other => panic!("unsupported backend binop in native lowering: {other:?}"),
    }
}

fn lower_guard_binop(op: crate::dispatch_matrix::pattern::PatternGuardBinOp) -> IrBinOp {
    match op {
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Add => IrBinOp::Add,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Sub => IrBinOp::Sub,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Mul => IrBinOp::Mul,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Div => IrBinOp::Div,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Rem => IrBinOp::Mod,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Eq => IrBinOp::Eq,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Neq => IrBinOp::Neq,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Lt => IrBinOp::Lt,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::LtEq => IrBinOp::Le,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Gt => IrBinOp::Gt,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::GtEq => IrBinOp::Ge,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::And => IrBinOp::And,
        crate::dispatch_matrix::pattern::PatternGuardBinOp::Or => IrBinOp::Or,
    }
}

fn lower_unop(op: crate::ast::UnOp) -> IrUnOp {
    match op {
        crate::ast::UnOp::Neg => IrUnOp::Neg,
        crate::ast::UnOp::Not => IrUnOp::Not,
    }
}

fn atom_names(atom_ids: &HashMap<String, u32>) -> Vec<String> {
    let mut out = vec![String::new(); atom_ids.len()];
    for (name, id) in atom_ids {
        out[*id as usize] = name.clone();
    }
    out
}

fn lower_bit_size_ir(
    _world: &World<'_>,
    size: &Option<super::super::body::LoweredBitSize>,
    env: &ValueEnv,
) -> Result<Option<BitSizeIr>, FatalError> {
    Ok(match size {
        None => None,
        Some(super::super::body::LoweredBitSize::Literal(value)) => Some(BitSizeIr::Literal(*value)),
        Some(super::super::body::LoweredBitSize::Value(value)) => {
            Some(BitSizeIr::Var(env.runtime_var(*value).ok_or(FatalError)?))
        }
    })
}

fn abi_value_repr(world: &mut World<'_>, ty: Ty) -> AbiValueRepr {
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

fn block_param_abi_value_repr(world: &mut World<'_>, ty: Ty) -> AbiValueRepr {
    match abi_value_repr(world, ty) {
        repr @ (AbiValueRepr::RawInt | AbiValueRepr::RawAtom) => repr,
        AbiValueRepr::RawF64 | AbiValueRepr::ValueRef => AbiValueRepr::ValueRef,
    }
}

fn mark_ignored_lanes_for_demand(
    world: &World<'_>,
    builder: &mut FnBuilder,
    vars: &[Var],
    shape: ShapeId,
    demand: &RuntimeDemand,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => Ok(()),
        ShapeDescr::Lane(_) => {
            let var = next_runtime_lane(vars, lane_index)?;
            if demand.is_ignore() {
                builder.mark_param_ignored(var);
            }
            Ok(())
        }
        ShapeDescr::Tuple(fields) => {
            if demand.is_callable() {
                return skip_runtime_lanes(world, vars, shape, lane_index);
            }
            match &demand.shape {
                ShapeDemand::Ignore => {
                    for field in fields.iter().copied() {
                        mark_all_runtime_lanes_ignored(world, builder, vars, field, lane_index)?;
                    }
                    Ok(())
                }
                ShapeDemand::TupleFields(demands) => {
                    if demands.len() > fields.len() {
                        return Err(FatalError);
                    }
                    for (index, field) in fields.iter().copied().enumerate() {
                        if let Some(field_demand) = demands.get(index) {
                            mark_ignored_lanes_for_demand(world, builder, vars, field, field_demand, lane_index)?;
                        } else {
                            mark_all_runtime_lanes_ignored(world, builder, vars, field, lane_index)?;
                        }
                    }
                    Ok(())
                }
                ShapeDemand::Whole => skip_runtime_lanes(world, vars, shape, lane_index),
            }
        }
        ShapeDescr::Callable(callable) => {
            let capture_lanes = world.transport().interners().callable(*callable).capture_lanes.len();
            if demand.is_ignore() {
                for _ in 0..capture_lanes {
                    let var = next_runtime_lane(vars, lane_index)?;
                    builder.mark_param_ignored(var);
                }
                Ok(())
            } else {
                skip_runtime_lanes(world, vars, shape, lane_index)
            }
        }
    }
}

fn mark_ignored_publication_lanes(
    builder: &mut FnBuilder,
    vars: &[Var],
    demand: &RuntimeDemand,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    for _ in 0..vars.len() {
        let var = next_runtime_lane(vars, lane_index)?;
        if demand.is_ignore() {
            builder.mark_param_ignored(var);
        }
    }
    Ok(())
}

fn mark_all_runtime_lanes_ignored(
    world: &World<'_>,
    builder: &mut FnBuilder,
    vars: &[Var],
    shape: ShapeId,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => Ok(()),
        ShapeDescr::Lane(_) => {
            let var = next_runtime_lane(vars, lane_index)?;
            builder.mark_param_ignored(var);
            Ok(())
        }
        ShapeDescr::Tuple(fields) => {
            for field in fields.iter().copied() {
                mark_all_runtime_lanes_ignored(world, builder, vars, field, lane_index)?;
            }
            Ok(())
        }
        ShapeDescr::Callable(callable) => {
            for _ in 0..world.transport().interners().callable(*callable).capture_lanes.len() {
                let var = next_runtime_lane(vars, lane_index)?;
                builder.mark_param_ignored(var);
            }
            Ok(())
        }
    }
}

fn skip_runtime_lanes(
    world: &World<'_>,
    vars: &[Var],
    shape: ShapeId,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    match world.transport().interners().shape(shape) {
        ShapeDescr::Nothing => Ok(()),
        ShapeDescr::Lane(_) => {
            next_runtime_lane(vars, lane_index)?;
            Ok(())
        }
        ShapeDescr::Tuple(fields) => {
            for field in fields.iter().copied() {
                skip_runtime_lanes(world, vars, field, lane_index)?;
            }
            Ok(())
        }
        ShapeDescr::Callable(callable) => {
            for _ in 0..world.transport().interners().callable(*callable).capture_lanes.len() {
                next_runtime_lane(vars, lane_index)?;
            }
            Ok(())
        }
    }
}

fn next_runtime_lane(vars: &[Var], lane_index: &mut usize) -> Result<Var, FatalError> {
    let var = vars.get(*lane_index).copied().ok_or(FatalError)?;
    *lane_index += 1;
    Ok(var)
}

fn missing_backend_value(_root_id: RootId, _value: ValueId) -> FatalError {
    FatalError
}

fn incomplete_native_program(world: &World<'_>, root_id: RootId, message: impl Into<String>) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 native lowering for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(world.tel(), None, std::slice::from_ref(&diagnostic));
    FatalError
}
