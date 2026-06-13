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
    BackendStep, BackendTail, CallTarget, EffectSummary, NativeBody, NativeBodyOrigin, NativeCallableBoundary,
    NativeCallableBoundaryId, NativeEntryAbi, NativeProgram, ReturnAbi,
};
use super::super::body::{ControlDestination, ControlEntryId, Literal, LoweredExtern, ValueId};
use super::super::drive::{FactKey, Job, JobEffects, settled_uses};
use super::super::identity::{FunctionId, RootId};
use super::super::scheduler::FatalError;
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
    let program = NativeLowerer::new(world, root_id, &backend)?.lower()?;
    let changed = world.define_native_program(root_id, program);
    Ok(JobEffects {
        reads: settled_uses([backend_fact]),
        outputs: vec![FactKey::NativeProgram(root_id)],
        changed: changed.then_some(FactKey::NativeProgram(root_id)).into_iter().collect(),
        ..JobEffects::default()
    })
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
                    identity_fn,
                    target_fn: executable_fns[entry.target],
                    target: executable.key.clone(),
                    capture_count: entry.capture_count,
                    capture_reprs: entry.capture_reprs.clone(),
                    arg_reprs: entry.arg_reprs.clone(),
                    return_ty: entry.return_ty,
                    return_abi: entry.return_abi.clone(),
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
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::Prelude,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.param_reprs.clone(),
            executable.return_ty,
            executable.return_abi.clone(),
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
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::User,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.param_reprs.clone(),
            executable.return_ty,
            executable.return_abi.clone(),
            executable.effects,
        );
        let inputs = ctx.entry_params(executable.key.activation.input.as_slice());
        let mut state = DispatchState::new(inputs, Vec::new());
        let dispatch = executable
            .entry_dispatch
            .as_ref()
            .expect("clause dispatch lowering requires a settled entry dispatch");
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
        let mut ctx = NativeFnCtx::new(
            fn_id,
            name,
            category,
            origin,
            NativeEntryAbi::Direct,
            executable.param_reprs.clone(),
            executable.return_ty,
            executable.return_abi.clone(),
            executable.effects,
        );
        let mut env = ValueEnv::default();
        let entry_tys = clause
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
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        for (value, var) in clause.params.iter().copied().zip(entry_vars) {
            env.insert(value, var);
        }
        self.lower_entry_steps(&mut ctx, executable, &mut env, &clause.projections)?;
        self.lower_entry_from_id(&mut ctx, executable, entries, entry_fns, clause.entry, env)?;
        self.finish_native_fn(ctx);
        Ok(())
    }

    fn finish_native_fn(&mut self, ctx: NativeFnCtx) {
        let (fn_ir, body) = ctx.finish();
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
        let (entry_tys, param_reprs, entry_abi) = self.entry_signature(executable, entry);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &entry_name(&base_name, entry_id, &entry.origin),
            entry_category(&entry.origin),
            NativeBodyOrigin::Continuation {
                owner: self.executable_fns[executable_index],
                index: entry_id.as_u32(),
            },
            entry_abi,
            param_reprs,
            executable.return_ty,
            executable.return_abi.clone(),
            executable.effects,
        );
        let mut env = ValueEnv::default();
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let capture_offset = self.bind_entry_input(&mut ctx, executable, entry, &entry_vars, &mut env)?;
        for (value, var) in entry
            .captures
            .iter()
            .copied()
            .zip(entry_vars.iter().copied().skip(capture_offset))
        {
            env.insert(value, var);
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
                BackendStep::Const { value, literal } => {
                    let var = lower_backend_literal(ctx, &self.atom_ids, literal)?;
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::Tuple { value, items } => {
                    let vars = env.vars(items).ok_or_else(|| {
                        incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native tuple build referenced an unbound value",
                        )
                    })?;
                    let (var, _) = ctx.emit_let(Prim::MakeTuple(vars));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::List { value, items, tail } => {
                    let vars = env.vars(items).ok_or_else(|| {
                        incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native list build referenced an unbound value",
                        )
                    })?;
                    let tail = tail.and_then(|tail| env.var(tail));
                    let (var, _) = ctx.emit_let(Prim::MakeList(vars, tail));
                    bind_backend_value(ctx, executable, env, *value, var);
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
                        let key = env.var(*key).ok_or_else(|| missing_backend_value(self.root_id, *key))?;
                        let value = env
                            .var(*item)
                            .ok_or_else(|| missing_backend_value(self.root_id, *item))?;
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
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::MapUpdate { value, base, entries } => {
                    let base = env
                        .var(*base)
                        .ok_or_else(|| missing_backend_value(self.root_id, *base))?;
                    let token = ctx.fresh_token();
                    let (map, _) = ctx.emit_let(Prim::DestMapBegin {
                        token,
                        base: Some(base),
                        extra: entries.len(),
                    });
                    let mut token = token;
                    for (key, item) in entries {
                        let next = ctx.fresh_token();
                        let key = env.var(*key).ok_or_else(|| missing_backend_value(self.root_id, *key))?;
                        let value = env
                            .var(*item)
                            .ok_or_else(|| missing_backend_value(self.root_id, *item))?;
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
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::Struct {
                    value,
                    module_name,
                    fields,
                } => {
                    let mut lowered = Vec::with_capacity(fields.len());
                    for (field, item) in fields {
                        lowered.push((
                            field.clone(),
                            env.var(*item)
                                .ok_or_else(|| missing_backend_value(self.root_id, *item))?,
                        ));
                    }
                    let (var, _) = ctx.emit_let(Prim::MakeStruct {
                        module: module_name.clone(),
                        fields: lowered,
                    });
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::Bitstring { value, fields } => {
                    let mut lowered = Vec::with_capacity(fields.len());
                    for field in fields {
                        lowered.push(crate::fz_ir::BitFieldIr {
                            value: env
                                .var(field.value)
                                .ok_or_else(|| missing_backend_value(self.root_id, field.value))?,
                            ty: field.spec.ty,
                            size: lower_bit_size_ir(&field.spec.size, env)?,
                            endian: field.spec.endian,
                            signed: field.spec.signed,
                            unit: field.spec.unit,
                        });
                    }
                    let (var, _) = ctx.emit_let(Prim::MakeBitstring(lowered));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::FunctionRef { value, function } => {
                    let identity = self.callable_identity(*function, 0);
                    let (var, _) = ctx.emit_let(Prim::MakeFnRef(ctx.fresh_callsite(), identity));
                    if let Some(boundary) = self.settled_callable_boundary(ctx, *function, &[])? {
                        ctx.callable_value_boundaries.insert(var, boundary);
                    }
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::Lambda {
                    value,
                    function,
                    captures,
                } => {
                    let capture_vars = env.vars(captures).ok_or_else(|| {
                        incomplete_native_program(
                            self.world,
                            self.root_id,
                            "native closure build referenced an unbound capture",
                        )
                    })?;
                    let capture_count = captures.len();
                    let identity = self.callable_identity(*function, capture_count);
                    let boundary = self.settled_callable_boundary(ctx, *function, &capture_vars)?;
                    let prim = if capture_vars.is_empty() {
                        Prim::MakeFnRef(ctx.fresh_callsite(), identity)
                    } else {
                        Prim::MakeClosure(ctx.fresh_callsite(), identity, capture_vars)
                    };
                    let (var, _) = ctx.emit_let(prim);
                    if let Some(boundary) = boundary {
                        ctx.callable_value_boundaries.insert(var, boundary);
                    }
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::BinaryOp { value, op, left, right } => {
                    let left = env
                        .var(*left)
                        .ok_or_else(|| missing_backend_value(self.root_id, *left))?;
                    let right = env
                        .var(*right)
                        .ok_or_else(|| missing_backend_value(self.root_id, *right))?;
                    let (var, _) = ctx.emit_let(Prim::BinOp(lower_binop(*op), left, right));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::UnaryOp { value, op, input } => {
                    let input = env
                        .var(*input)
                        .ok_or_else(|| missing_backend_value(self.root_id, *input))?;
                    let (var, _) = ctx.emit_let(Prim::UnOp(lower_unop(*op), input));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::MapIndex { value, base, key } => {
                    let base = env
                        .var(*base)
                        .ok_or_else(|| missing_backend_value(self.root_id, *base))?;
                    let key = env.var(*key).ok_or_else(|| missing_backend_value(self.root_id, *key))?;
                    let (var, _) = ctx.emit_let(Prim::MapGet(base, key));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::FieldAccess { value, base, field } => {
                    let base = env
                        .var(*base)
                        .ok_or_else(|| missing_backend_value(self.root_id, *base))?;
                    let (var, _) = ctx.emit_let(Prim::StructField(base, field.clone()));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::AssertLiteral { source, literal } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let expected = lower_backend_literal(ctx, &self.atom_ids, literal)?;
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, source, expected));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::AssertStruct { source, module_name } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let predicate =
                        RuntimeTypePredicate::named_struct(module_name.rsplit('.').next().unwrap_or(module_name));
                    let (matches, _) = ctx.emit_let(Prim::RuntimeTypeTest(source, Box::new(predicate)));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::RequireMapValue { value, source, key } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let key = lower_backend_literal(ctx, &self.atom_ids, key)?;
                    let (var, _) = ctx.emit_let(Prim::MatcherMapGet(source, key));
                    let (is_miss, _) = ctx.emit_let(Prim::IsMatcherMapMiss(var));
                    let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, is_miss, false_v));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::AssertTuple { source, arity } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let tuple_ty = RuntimeTypePredicate::tuple_arity(*arity);
                    let (matches, _) = ctx.emit_let(Prim::RuntimeTypeTest(source, Box::new(tuple_ty)));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::TupleField { value, source, index } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let (var, _) = ctx.emit_let(Prim::TupleField(source, *index as u32));
                    bind_backend_value(ctx, executable, env, *value, var);
                }
                BackendStep::AssertEmptyList { source } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let (matches, _) = ctx.emit_let(Prim::IsEmptyList(source));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::AssertSame { source, value } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let value = env
                        .var(*value)
                        .ok_or_else(|| missing_backend_value(self.root_id, *value))?;
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, source, value));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::SplitList { source, head, tail } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let (head_var, _) = ctx.emit_let(Prim::ListHead(source));
                    bind_backend_value(ctx, executable, env, *head, head_var);
                    let (tail_var, _) = ctx.emit_let(Prim::ListTail(source));
                    bind_backend_value(ctx, executable, env, *tail, tail_var);
                }
                BackendStep::BitstringInit { reader, source } => {
                    let source = env
                        .var(*source)
                        .ok_or_else(|| missing_backend_value(self.root_id, *source))?;
                    let (var, _) = ctx.emit_let(Prim::BitReaderInit(source));
                    bind_backend_value(ctx, executable, env, *reader, var);
                }
                BackendStep::BitstringRead {
                    ok,
                    value,
                    next_reader,
                    reader,
                    spec,
                    is_last,
                } => {
                    let reader = env
                        .var(*reader)
                        .ok_or_else(|| missing_backend_value(self.root_id, *reader))?;
                    let (result, _) = ctx.emit_let(Prim::BitReadField {
                        reader,
                        ty: spec.ty,
                        size: lower_bit_size_ir(&spec.size, env)?,
                        endian: spec.endian,
                        signed: spec.signed,
                        unit: spec.unit,
                        is_last: *is_last,
                    });
                    let (ok_var, _) = ctx.emit_let(Prim::TupleField(result, 0));
                    bind_backend_value(ctx, executable, env, *ok, ok_var);
                    let (value_var, _) = ctx.emit_let(Prim::TupleField(result, 1));
                    bind_backend_value(ctx, executable, env, *value, value_var);
                    let (reader_var, _) = ctx.emit_let(Prim::TupleField(result, 2));
                    bind_backend_value(ctx, executable, env, *next_reader, reader_var);
                }
                BackendStep::AssertBitstringDone { reader } => {
                    let reader = env
                        .var(*reader)
                        .ok_or_else(|| missing_backend_value(self.root_id, *reader))?;
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
                let result = env
                    .var(*value)
                    .ok_or_else(|| missing_backend_value(self.root_id, *value))?;
                self.lower_value_destination(ctx, executable, entries, entry_fns, env, *value, result, dest)
            }
            BackendTail::DirectCall { callee, args, dest, .. } => {
                let call_args = env.call_args(args).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        "native direct call referenced an unbound argument",
                    )
                })?;
                let callee = match callee {
                    CallTarget::Local(callee) => DirectCallTarget::Local(self.executable_fns[*callee]),
                    CallTarget::ProviderBoundary(function) => {
                        DirectCallTarget::ProviderBoundary(self.world.function_mfa(*function))
                    }
                };
                match dest {
                    ControlDestination::Return => {
                        ctx.set_term(Term::TailCall {
                            ident: CallsiteIdent::from_source(Span::DUMMY),
                            callee,
                            args: call_args,
                            is_back_edge: false,
                        });
                        Ok(())
                    }
                    ControlDestination::Deliver(entry_id) => {
                        let continuation = self.entry_continuation(entries, entry_fns, *entry_id, env)?;
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
                ..
            } => {
                let closure = env
                    .var(*callee)
                    .ok_or_else(|| missing_backend_value(self.root_id, *callee))?;
                let call_args = env.call_args(args).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        "native closure call referenced an unbound argument",
                    )
                })?;
                let direct_target = target.map(|target| self.executable_fns[target]);
                match dest {
                    ControlDestination::Return => {
                        ctx.set_term(Term::TailCallClosure {
                            ident: CallsiteIdent::from_source(Span::DUMMY),
                            closure,
                            direct_target,
                            args: call_args,
                        });
                        Ok(())
                    }
                    ControlDestination::Deliver(entry_id) => {
                        let continuation = self.entry_continuation(entries, entry_fns, *entry_id, env)?;
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
            BackendTail::If {
                cond,
                then_entry,
                else_entry,
            } => {
                let cond = env
                    .var(*cond)
                    .ok_or_else(|| missing_backend_value(self.root_id, *cond))?;
                let then_b = ctx.builder.block(vec![]);
                let else_b = ctx.builder.block(vec![]);
                ctx.set_term(Term::If {
                    cond,
                    then_b,
                    else_b,
                    origin: BranchOrigin::User,
                });
                ctx.current_block = then_b;
                let then_args = self.entry_capture_args(entries, *then_entry, env)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(
                        *entry_fns.get(then_entry).expect("branch entry should have a helper fn"),
                    ),
                    args: then_args,
                    is_back_edge: false,
                });
                ctx.current_block = else_b;
                let else_args = self.entry_capture_args(entries, *else_entry, env)?;
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
                let input_vars = env.vars(inputs).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        "native local dispatch referenced an unbound input value",
                    )
                })?;
                let pinned_vars = env.vars(&bindings.pinned).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        "native local dispatch referenced an unbound pinned value",
                    )
                })?;
                let mut state = DispatchState::new(input_vars, pinned_vars);
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
                let captures = self.receive_capture_vars(entries, clauses, after, env)?;
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
                            timeout: env.var(after.timeout).ok_or_else(|| {
                                incomplete_native_program(
                                    self.world,
                                    self.root_id,
                                    "native receive referenced an unbound after timeout",
                                )
                            })?,
                            body: *entry_fns
                                .get(&after.entry)
                                .expect("receive after entry should have a helper fn"),
                            span: after.span,
                        })
                    })
                    .transpose()?;
                let pinned = self.receive_pinned_vars(env, bindings, dispatch)?;
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
        value_var: Var,
        dest: &ControlDestination,
    ) -> Result<(), FatalError> {
        match dest {
            ControlDestination::Return => {
                ctx.set_term(Term::Return(value_var));
                Ok(())
            }
            ControlDestination::Deliver(entry_id) => {
                let args =
                    self.entry_call_args_from_value(ctx, executable, entries, *entry_id, env, value_id, value_var)?;
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

    fn entry_signature(
        &mut self,
        executable: &BackendExecutable,
        entry: &BackendEntry,
    ) -> (Vec<Ty>, Vec<AbiValueRepr>, NativeEntryAbi) {
        let mut capture_tys = Vec::with_capacity(entry.params.len() + entry.captures.len());
        for value in entry.params.iter().chain(entry.captures.iter()) {
            let ty = executable
                .value_types
                .get(value)
                .copied()
                .unwrap_or_else(|| self.world.types_mut().any());
            capture_tys.push(ty);
        }
        match entry.origin.clone() {
            BackendEntryOrigin::Clause => panic!("clause entries are lowered through their owning clause"),
            BackendEntryOrigin::Branch => {
                let param_reprs = capture_tys
                    .iter()
                    .copied()
                    .map(|ty| abi_value_repr(self.world, ty))
                    .collect::<Vec<_>>();
                (capture_tys, param_reprs, NativeEntryAbi::Direct)
            }
            BackendEntryOrigin::Receive => {
                let param_reprs = capture_tys
                    .iter()
                    .copied()
                    .map(|ty| abi_value_repr(self.world, ty))
                    .collect::<Vec<_>>();
                (
                    capture_tys,
                    param_reprs,
                    NativeEntryAbi::Continuation { extra_params: 0 },
                )
            }
            BackendEntryOrigin::CallResume { value, return_abi } => {
                let result_ty = executable
                    .value_types
                    .get(&value)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any());
                let (mut entry_tys, mut param_reprs) = continuation_result_entry(self.world, result_ty, &return_abi);
                let extra_params = param_reprs.len();
                entry_tys.extend(capture_tys.iter().copied());
                param_reprs.extend(capture_tys.iter().copied().map(|ty| abi_value_repr(self.world, ty)));
                (entry_tys, param_reprs, NativeEntryAbi::Continuation { extra_params })
            }
            BackendEntryOrigin::LocalResume { value } => {
                let result_ty = executable
                    .value_types
                    .get(&value)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any());
                let mut entry_tys = vec![result_ty];
                let mut param_reprs = vec![abi_value_repr(self.world, result_ty)];
                entry_tys.extend(capture_tys.iter().copied());
                param_reprs.extend(capture_tys.iter().copied().map(|ty| abi_value_repr(self.world, ty)));
                (entry_tys, param_reprs, NativeEntryAbi::Direct)
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
                    bind_backend_value(ctx, executable, env, value, var);
                }
                Ok(entry.params.len())
            }
            BackendEntryOrigin::Receive => {
                for (value, var) in entry.params.iter().copied().zip(entry_vars.iter().copied()) {
                    bind_backend_value(ctx, executable, env, value, var);
                }
                Ok(entry.params.len())
            }
            BackendEntryOrigin::CallResume { value, return_abi } => match return_abi {
                ReturnAbi::Value(_) => {
                    let var = *entry_vars
                        .first()
                        .expect("value continuation should have one entry param");
                    bind_backend_value(ctx, executable, env, *value, var);
                    Ok(1)
                }
                ReturnAbi::TupleFields(reprs) => {
                    let tuple_fields = entry_vars.iter().copied().take(reprs.len()).collect::<Vec<_>>();
                    let (result_var, _) = ctx.emit_let(Prim::MakeTuple(tuple_fields));
                    bind_backend_value(ctx, executable, env, *value, result_var);
                    Ok(reprs.len())
                }
            },
            BackendEntryOrigin::LocalResume { value } => {
                let var = *entry_vars
                    .first()
                    .expect("local resume should receive its delivered value as the first entry param");
                bind_backend_value(ctx, executable, env, *value, var);
                Ok(1)
            }
        }
    }

    fn entry_continuation(
        &mut self,
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
                    "native call continuation targeted entry {} without an input value",
                    entry_id.as_u32()
                ),
            ));
        }
        Ok(Cont {
            fn_id: *entry_fns.get(&entry_id).expect("resume entry should have a helper fn"),
            captured: self.entry_capture_args(entries, entry_id, env)?,
        })
    }

    fn entry_capture_args(
        &mut self,
        entries: &[BackendEntry],
        entry_id: ControlEntryId,
        env: &ValueEnv,
    ) -> Result<Vec<Var>, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        env.capture_args(&entry.captures).ok_or_else(|| {
            incomplete_native_program(
                self.world,
                self.root_id,
                format!(
                    "native lowering could not resolve captures for entry {}",
                    entry_id.as_u32()
                ),
            )
        })
    }

    fn receive_pinned_vars(
        &mut self,
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
                let var = env.var(value_id).ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        "native receive referenced an unbound pinned value",
                    )
                })?;
                pinned.push((pin.name.clone(), var));
            }
        }
        for (index, value_id) in bindings.prepared.iter().copied().enumerate() {
            let var = env.var(value_id).ok_or_else(|| {
                incomplete_native_program(
                    self.world,
                    self.root_id,
                    "native receive referenced an unbound prepared dispatch value",
                )
            })?;
            pinned.push((prepared_key_name(index), var));
        }
        Ok(pinned)
    }

    fn receive_capture_vars(
        &mut self,
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
        env.capture_args(&capture_ids).ok_or_else(|| {
            incomplete_native_program(
                self.world,
                self.root_id,
                "native receive could not resolve capture values",
            )
        })
    }

    fn entry_call_args_from_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_id: ControlEntryId,
        env: &ValueEnv,
        value_id: ValueId,
        value_var: Var,
    ) -> Result<Vec<Var>, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let mut args = match &entry.origin {
            BackendEntryOrigin::Clause | BackendEntryOrigin::Branch | BackendEntryOrigin::Receive => Vec::new(),
            BackendEntryOrigin::CallResume { return_abi, .. } => {
                self.delivered_args_for_abi(ctx, executable, value_id, value_var, return_abi)?
            }
            BackendEntryOrigin::LocalResume { .. } => vec![value_var],
        };
        args.extend(self.entry_capture_args(entries, entry_id, env)?);
        Ok(args)
    }

    fn delivered_args_for_abi(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value_id: ValueId,
        value_var: Var,
        return_abi: &ReturnAbi,
    ) -> Result<Vec<Var>, FatalError> {
        match return_abi {
            ReturnAbi::Value(_) => Ok(vec![value_var]),
            ReturnAbi::TupleFields(reprs) => {
                let tuple_ty = executable
                    .value_types
                    .get(&value_id)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any());
                let field_tys = self.world.types_mut().tuple_projections(&tuple_ty, reprs.len());
                let mut out = Vec::with_capacity(reprs.len());
                for (index, field_ty) in field_tys.into_iter().enumerate() {
                    let (field_var, _) = ctx.emit_let(Prim::TupleField(value_var, index as u32));
                    ctx.value_types.insert(field_var, field_ty);
                    out.push(field_var);
                }
                Ok(out)
            }
        }
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
                let args = state.inputs.clone();
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
                let args = self.entry_capture_args(entries, miss_entry, env)?;
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
                    let args = self.entry_capture_args(entries, miss_entry, env)?;
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
                let args = self.entry_capture_args(entries, arm_entry, env)?;
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
        let mut dispatch_state = DispatchState::new(input_vars, Vec::new());
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
                state.inputs.get(*ordinal as usize).copied().ok_or_else(|| {
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
            return state.inputs.get(input as usize).copied().ok_or_else(|| {
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

    fn settled_callable_boundary(
        &mut self,
        ctx: &NativeFnCtx,
        function: FunctionId,
        captures: &[Var],
    ) -> Result<Option<NativeCallableBoundaryId>, FatalError> {
        let capture_tys = captures
            .iter()
            .map(|capture| {
                ctx.value_types.get(capture).copied().ok_or_else(|| {
                    incomplete_native_program(
                        self.world,
                        self.root_id,
                        format!(
                            "native closure build referenced capture {:?} without a settled type",
                            capture
                        ),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        select_settled_callable_boundary(
            self.world.types_mut(),
            &self.callable_boundaries,
            function,
            &capture_tys,
        )
        .map_err(|message| incomplete_native_program(self.world, self.root_id, message))
    }
}

fn callable_abi_strictly_more_specific(
    lhs_args: &[AbiValueRepr],
    lhs_return: &ReturnAbi,
    rhs_args: &[AbiValueRepr],
    rhs_return: &ReturnAbi,
) -> bool {
    if lhs_args.len() != rhs_args.len() {
        return false;
    }
    let mut saw_stricter_lane = false;
    for (lhs, rhs) in lhs_args.iter().copied().zip(rhs_args.iter().copied()) {
        match (lhs, rhs) {
            (AbiValueRepr::ValueRef, AbiValueRepr::ValueRef) => {}
            (AbiValueRepr::ValueRef, _) => return false,
            (_, AbiValueRepr::ValueRef) => saw_stricter_lane = true,
            _ if lhs == rhs => {}
            _ => return false,
        }
    }
    match (lhs_return, rhs_return) {
        (ReturnAbi::Value(AbiValueRepr::ValueRef), ReturnAbi::Value(AbiValueRepr::ValueRef)) => saw_stricter_lane,
        (ReturnAbi::Value(AbiValueRepr::ValueRef), ReturnAbi::Value(_)) => false,
        (ReturnAbi::Value(_), ReturnAbi::Value(AbiValueRepr::ValueRef)) => true,
        (ReturnAbi::Value(lhs), ReturnAbi::Value(rhs)) => lhs == rhs && saw_stricter_lane,
        (ReturnAbi::TupleFields(lhs), ReturnAbi::TupleFields(rhs)) => lhs == rhs && saw_stricter_lane,
        (ReturnAbi::Value(_), ReturnAbi::TupleFields(_)) | (ReturnAbi::TupleFields(_), ReturnAbi::Value(_)) => false,
    }
}

fn select_settled_callable_boundary(
    types: &mut crate::compiler2::types::Types,
    boundaries: &[NativeCallableBoundary],
    function: FunctionId,
    capture_tys: &[Ty],
) -> Result<Option<NativeCallableBoundaryId>, String> {
    let mut query = Vec::with_capacity(capture_tys.len());
    for ty in capture_tys {
        let erased = types.erase_closure_identity(ty);
        query.push(types.alpha_normalize_vars(&erased));
    }

    let mut covers = boundaries
        .iter()
        .filter(|boundary| {
            boundary.target.activation.function == function && boundary.capture_count == capture_tys.len()
        })
        .filter_map(|boundary| {
            let capture_inputs = boundary
                .target
                .activation
                .input
                .iter()
                .copied()
                .take(boundary.capture_count)
                .map(|ty| {
                    let erased = types.erase_closure_identity(&ty);
                    types.alpha_normalize_vars(&erased)
                })
                .collect::<Vec<_>>();
            let capture_key = crate::types::key_slots_from_tys(capture_inputs);
            let mut sigma = HashMap::new();
            query
                .iter()
                .zip(capture_key.iter())
                .all(|(query_ty, key_slot)| match key_slot {
                    None => true,
                    Some(key_ty) => types.key_subsumes_with(query_ty, key_ty, &mut sigma),
                })
                .then_some((boundary.id(), capture_key, &boundary.arg_reprs, &boundary.return_abi))
        })
        .collect::<Vec<_>>();
    if covers.is_empty() {
        return Ok(None);
    }

    let min_var_count = covers
        .iter()
        .map(|(_, capture_key, _, _)| crate::types::key_slot_var_count(types, capture_key))
        .min()
        .unwrap_or(0);
    covers.retain(|(_, capture_key, _, _)| crate::types::key_slot_var_count(types, capture_key) == min_var_count);
    covers.sort_by_key(|(boundary_id, _, _, _)| boundary_id.as_u32());

    let maximal = covers
        .iter()
        .filter(|&(candidate_id, _, candidate_args, candidate_return)| {
            !covers.iter().any(|(other_id, _, other_args, other_return)| {
                other_id != candidate_id
                    && callable_abi_strictly_more_specific(candidate_args, candidate_return, other_args, other_return)
            })
        })
        .cloned()
        .collect::<Vec<_>>();
    match maximal.as_slice() {
        [] => Ok(None),
        [(boundary_id, _, _, _)] => Ok(Some(*boundary_id)),
        _ => Err(format!(
            "ambiguous callable boundaries for {:?}/{} captures: candidates {:?}",
            function,
            capture_tys.len(),
            maximal
                .iter()
                .map(|(boundary_id, _, _, _)| boundary_id.as_u32())
                .collect::<Vec<_>>()
        )),
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

fn entry_name(base: &str, entry_id: ControlEntryId, origin: &BackendEntryOrigin) -> String {
    match origin {
        BackendEntryOrigin::Clause => panic!("clause entries are named by their owning clause"),
        BackendEntryOrigin::Branch => format!("{base}__branch_{}", entry_id.as_u32()),
        BackendEntryOrigin::Receive => format!("{base}__receive_{}", entry_id.as_u32()),
        BackendEntryOrigin::CallResume { .. } | BackendEntryOrigin::LocalResume { .. } => {
            format!("{base}__resume_{}", entry_id.as_u32())
        }
    }
}

fn entry_category(origin: &BackendEntryOrigin) -> FnCategory {
    match origin {
        BackendEntryOrigin::Clause => panic!("clause entries are named by their owning clause"),
        BackendEntryOrigin::Branch => FnCategory::ControlFlowCont,
        BackendEntryOrigin::Receive => FnCategory::CpsCont,
        BackendEntryOrigin::CallResume { .. } => FnCategory::CpsCont,
        BackendEntryOrigin::LocalResume { .. } => FnCategory::ControlFlowCont,
    }
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
                Term::TailCallClosure { .. } | Term::Goto(..) | Term::If { .. } | Term::Return(_) | Term::Halt(_) => {}
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

#[derive(Default, Clone)]
struct ValueEnv {
    vars: HashMap<ValueId, Var>,
}

impl ValueEnv {
    fn insert(&mut self, value: ValueId, var: Var) {
        self.vars.insert(value, var);
    }

    fn var(&self, value: ValueId) -> Option<Var> {
        self.vars.get(&value).copied()
    }

    fn vars(&self, values: &[ValueId]) -> Option<Vec<Var>> {
        values.iter().map(|value| self.var(*value)).collect()
    }

    fn call_args(&self, args: &[crate::compiler2::BackendCallArg]) -> Option<Vec<Var>> {
        args.iter().map(|arg| self.var(arg.value)).collect()
    }

    fn capture_args(&self, captured: &[ValueId]) -> Option<Vec<Var>> {
        captured.iter().map(|value| self.var(*value)).collect()
    }
}

#[derive(Clone)]
struct DispatchState {
    inputs: Vec<Var>,
    pinned: Vec<Var>,
    values: HashMap<SubjectId, Var>,
}

impl DispatchState {
    fn new(inputs: Vec<Var>, pinned: Vec<Var>) -> Self {
        Self {
            inputs,
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
    return_abi: ReturnAbi,
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
        return_abi: ReturnAbi,
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
            return_abi,
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
            return_abi: self.return_abi,
            value_types: self.value_types,
            callable_value_boundaries: self.callable_value_boundaries,
            extern_marshals: self.extern_marshals,
            effects: self.effects,
        };
        (fn_ir, body)
    }
}

fn bind_backend_value(
    ctx: &mut NativeFnCtx,
    executable: &BackendExecutable,
    env: &mut ValueEnv,
    value: ValueId,
    var: Var,
) {
    env.insert(value, var);
    if let Some(ty) = executable.value_types.get(&value).copied() {
        ctx.value_types.insert(var, ty);
    }
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
    size: &Option<super::super::body::LoweredBitSize>,
    env: &ValueEnv,
) -> Result<Option<BitSizeIr>, FatalError> {
    Ok(match size {
        None => None,
        Some(super::super::body::LoweredBitSize::Literal(value)) => Some(BitSizeIr::Literal(*value)),
        Some(super::super::body::LoweredBitSize::Value(value)) => {
            Some(BitSizeIr::Var(env.var(*value).ok_or(FatalError)?))
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

fn continuation_result_entry(
    world: &mut World<'_>,
    result_ty: Ty,
    result_abi: &ReturnAbi,
) -> (Vec<Ty>, Vec<AbiValueRepr>) {
    match result_abi {
        ReturnAbi::Value(repr) => (vec![result_ty], vec![*repr]),
        ReturnAbi::TupleFields(reprs) => (
            world.types_mut().tuple_projections(&result_ty, reprs.len()),
            reprs.clone(),
        ),
    }
}

fn missing_backend_value(root_id: RootId, value: ValueId) -> FatalError {
    panic!(
        "native lowering referenced unbound value {} for root {}",
        value.as_u32(),
        root_id.as_u32()
    )
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
