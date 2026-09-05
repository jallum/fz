//! Compiler2 native-handoff lowering.
//!
//! This product producer turns one closed `BackendProgram(root)` into one
//! CPS/native handoff. The result is still Compiler2-owned: direct executable
//! entries, clause helpers, continuations, settled callable-boundary facts,
//! and extern marshal facts are all derived once here instead of being
//! rediscovered by shared codegen.

use super::super::identity::ExecutableKey;
use super::super::transport::TransportPosition;

use std::collections::{HashMap, HashSet, VecDeque};
use std::rc::Rc;
use std::sync::Arc;

use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::diag::driver::emit_through;
use crate::dispatch_matrix::pattern::{PatternDispatchPlan, PatternGuardExpr, prepared_key_name};
use crate::dispatch_matrix::{ComparisonValue, DispatchNode, GraphNodeId, ListRegion, Region, SubjectId};
use crate::fz_ir::{
    BinOp as IrBinOp, BitSizeIr, BlockId, BranchOrigin, CallsiteIdent, Const, Cont, DirectCallTarget, ExternArg,
    ExternDecl, ExternId, ExternMarshalSite, ExternTy, FnBuilder, FnCategory, FnId, InitTokenId, ModuleBuilder, Prim,
    ReceiveAfter, ReceiveClause, Term, UnOp as IrUnOp, Var,
};
use crate::ground_value::GroundValue;
use crate::runtime_type_predicate::{CallableShape, RuntimeTypePredicate};
use crate::source::Span;
use crate::telemetry::TelemetryExt as _;

use super::super::artifact::{
    AbiValueRepr, BackendBody, BackendCallableReturn, BackendClause, BackendEntry, BackendEntryCapture,
    BackendEntryOrigin, BackendExecutable, BackendProgram, BackendReturnFlow, BackendStep, BackendTail, CallEdge,
    CallTarget, DispatchCallEdge, EffectSummary, NativeBody, NativeBodyOrigin, NativeCallableBoundary,
    NativeCallableBoundaryId, NativeConstructionMember, NativeEntryAbi, NativeExecutableEntry, NativeProgram,
    ReusableConsCapture, required_dispatch_input_ordinals,
};
use super::super::body::{ControlDestination, ControlEntryId, LoweredExtern, ValueId};
use super::super::identity::RootId;
use super::super::pull::{ProductKey, ProductReadContext, ProductValue, PullOutcome};
use super::super::scheduler::FatalError;
use super::super::semantic::{RuntimeDemand, ShapeDemand};
use super::super::transport::{CallableId, ShapeDescr, ShapeId, TransportLayout};
use super::super::types::{ClosureTarget, Ty, Types};
use super::super::world::World;

const UNREACHABLE_CONTROL_ATOM: &str = "compiler2_unreachable_control";

pub(crate) fn produce_native_program(
    world: &mut World,
    telemetry: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    root_id: RootId,
) -> PullOutcome {
    let backend_key = ProductKey::RootBackendProduct(root_id);
    let backend = match context.read_product(telemetry, backend_key.clone(), world.types()) {
        Some(ProductValue::RootBackendProduct(backend)) => Rc::clone(backend),
        Some(value) => panic!("root backend content produced unexpected value {value:?}"),
        None => return PullOutcome::wait_on_product(backend_key),
    };
    match NativeLowerer::new(world, telemetry, root_id, &backend).and_then(NativeLowerer::lower) {
        Ok(program) => {
            emit_reusable_cons(telemetry, &root_id, &backend);
            PullOutcome::Produced(ProductValue::NativeProgram(Rc::new(program)))
        }
        Err(_) => PullOutcome::Failed(super::super::pull::ProductFailure::NativeLowering),
    }
}

fn callable_return_reprs(form: BackendCallableReturn) -> Vec<AbiValueRepr> {
    match form {
        BackendCallableReturn::Diverges | BackendCallableReturn::Absent => Vec::new(),
        BackendCallableReturn::ValueRef => vec![AbiValueRepr::ValueRef],
    }
}

/// Lowers one backend program into the Compiler2-owned native handoff.
///
/// The native handoff consumes only `BackendProgram(root)` plus compiler-owned
/// stores. It introduces CPS/native bodies and side facts, but it does not
/// reopen semantic closure, type inference, or planner discovery.
fn emit_reusable_cons(tel: &impl crate::telemetry::Telemetry, root: &RootId, program: &BackendProgram) {
    tel.raw_event2(&["fz", "compiler2", "native_program", "reusable_cons"], root, program);
}

struct NativeLowerer<'a, 'tel, T: crate::telemetry::Telemetry> {
    world: &'a mut World,
    telemetry: &'tel T,
    root_id: RootId,
    program: &'a BackendProgram,
    module: ModuleBuilder,
    atom_ids: HashMap<String, u32>,
    executable_fns: Vec<FnId>,
    construction_identity_fns: HashMap<TransportPosition, FnId>,
    callable_boundaries: Vec<NativeCallableBoundary>,
    extern_ids: HashMap<usize, ExternId>,
    extern_marshals: HashMap<usize, Vec<ExternTy>>,
    extern_decls: Vec<ExternDecl>,
    native_bodies: Vec<NativeBody>,
    return_continuation_count: u32,
}

impl<'a, 'tel, T: crate::telemetry::Telemetry> NativeLowerer<'a, 'tel, T> {
    /// The construction words that mint `callable`: one per boundary over that
    /// layout. Each boundary stamps its own `identity_fn` into the values it
    /// makes, so this is the whole set a value of that layout can carry -- and
    /// the set whose capture representations a reader must agree with.
    fn constructions_minting(&self, callable: CallableId) -> Box<[FnId]> {
        self.callable_boundaries
            .iter()
            .filter(|boundary| boundary.callable == callable)
            .map(|boundary| boundary.identity_fn)
            .collect()
    }

    fn new(
        world: &'a mut World,
        telemetry: &'tel T,
        root_id: RootId,
        program: &'a BackendProgram,
    ) -> Result<Self, FatalError> {
        let mut atom_ids = HashMap::new();
        for (index, atom) in program.atom_names.iter().enumerate() {
            atom_ids.insert(atom.as_ref().clone(), index as u32);
        }
        for atom in ["function_clause", "match_error"] {
            if !atom_ids.contains_key(atom) {
                let next = atom_ids.len() as u32;
                atom_ids.insert(atom.to_string(), next);
            }
        }

        let mut module = ModuleBuilder::new();
        let executable_fns = program
            .executables()
            .iter()
            .map(|_| module.fresh_fn_id())
            .collect::<Vec<_>>();

        let construction_identity_fns = program
            .construction_wrappers()
            .iter()
            .map(|wrapper| (wrapper.identity.clone(), module.fresh_fn_id()))
            .collect::<HashMap<_, _>>();
        let construction_wrapper_fns = program
            .construction_wrappers()
            .iter()
            .map(|wrapper| (wrapper.identity.clone(), module.fresh_fn_id()))
            .collect::<HashMap<_, _>>();

        let extern_marshals = collect_extern_marshals(world, telemetry, root_id, program)?;
        let mut extern_ids = HashMap::new();
        let mut extern_decls = Vec::new();
        for (index, executable) in program.executables().iter().enumerate() {
            let BackendBody::Extern { signature } = &executable.body else {
                continue;
            };
            let id = ExternId(extern_decls.len() as u32);
            extern_ids.insert(index, id);
            extern_decls.push(ExternDecl {
                id,
                fz_name: world.function_ref(executable.key.activation.function).name.clone(),
                symbol: signature.symbol.clone(),
                params: signature.params.clone(),
                variadic: signature.variadic,
                ret: signature.ret,
            });
        }

        let mut callable_boundaries = Vec::with_capacity(program.construction_wrappers().len());
        for (index, wrapper) in program.construction_wrappers().iter().enumerate() {
            let identity_fn = *construction_identity_fns
                .get(&wrapper.identity)
                .expect("construction identity should be predeclared");
            let wrapper_fn = *construction_wrapper_fns
                .get(&wrapper.identity)
                .expect("construction wrapper should be predeclared");
            let members = wrapper
                .members
                .iter()
                .map(|member| NativeConstructionMember {
                    boundary: member.boundary,
                    target_fn: executable_fns[program
                        .executable_index(&member.target, world.types())
                        .expect("construction target belongs to program")],
                    target: member.target.clone(),
                    surface_inputs: member.surface_inputs.clone(),
                    capture_semantic_inputs: member.capture_semantic_inputs.clone(),
                    surface_semantic_inputs: member.surface_semantic_inputs.clone(),
                    target_inputs: member.target_inputs.clone(),
                    target_return: member.target_return.clone(),
                })
                .collect::<Box<[_]>>();
            let task_halt_repr = if wrapper.call_arity != 0 {
                None
            } else {
                match members.as_ref() {
                    [] => None,
                    [member] if member.target_return.diverges => None,
                    [member] => member.target_return.layout.reprs.first().copied(),
                    _ => {
                        return Err(incomplete_native_program(
                            telemetry,
                            root_id,
                            format!(
                                "zero-argument callable construction {:?} has {} members",
                                wrapper.identity,
                                members.len(),
                            ),
                        ));
                    }
                }
            };
            let callable = world.callable(wrapper.callable);
            let shape = callable.function.map(|function| CallableShape {
                target: ClosureTarget(function.as_u32()),
                captures: callable
                    .capture_tys
                    .iter()
                    .map(|ty| world.types().runtime_type_predicate(ty))
                    .collect(),
            });
            callable_boundaries.push(NativeCallableBoundary {
                id: NativeCallableBoundaryId(index as u32),
                identity_fn,
                callable: wrapper.callable,
                shape,
                wrapper_fn,
                captures: wrapper.captures.clone(),
                capture_reprs: native_construction_capture_reprs(wrapper),
                call_arity: wrapper.call_arity,
                return_form: wrapper.return_form,
                task_halt_repr,
                members,
                selection: wrapper.selection.clone(),
            });
        }

        Ok(Self {
            world,
            telemetry,
            root_id,
            program,
            module,
            atom_ids,
            executable_fns,
            construction_identity_fns,
            callable_boundaries,
            extern_ids,
            extern_marshals,
            extern_decls,
            native_bodies: Vec::new(),
            return_continuation_count: 0,
        })
    }

    fn lower(mut self) -> Result<NativeProgram, FatalError> {
        for (index, executable) in self.program.executables().iter().enumerate() {
            let lowered = (|| -> Result<(), FatalError> {
                match &executable.body {
                    BackendBody::Extern { signature } => self.lower_extern_executable(index, executable, signature),
                    BackendBody::Clauses { clauses, entries, .. } => {
                        let mut entry_fns = EntryFns::default();
                        if executable.abi.materialized.entry_dispatch.is_some() {
                            self.lower_clause_dispatch_executable(index, executable, clauses, entries, &mut entry_fns)?;
                        } else {
                            let [clause] = clauses.as_slice() else {
                                return Err(incomplete_native_program(
                                    self.telemetry,
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
                                &mut entry_fns,
                                clause,
                            )?;
                        }
                        while let Some((entry, fn_id)) = entry_fns.pending.pop_front() {
                            self.lower_entry_fn(index, executable, entries, &mut entry_fns, entry, fn_id)?;
                        }
                        Ok(())
                    }
                }
            })();
            lowered.map_err(|_| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native executable lowering failed for index {index}, key {:?}",
                        executable.key
                    ),
                )
            })?;
        }
        for boundary in self.callable_boundaries.clone() {
            self.lower_callable_construction_wrapper(&boundary).map_err(|_| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native callable wrapper lowering failed for construction {}",
                        boundary.id.as_u32()
                    ),
                )
            })?;
        }

        let entry = *self
            .executable_fns
            .get(
                self.program
                    .executable_index(self.program.entry(), self.world.types())
                    .expect("native entry belongs to program"),
            )
            .expect("native entry executable should exist");
        let executable_entries = self
            .program
            .executables()
            .iter()
            .zip(&self.executable_fns)
            .map(|(executable, fn_id)| NativeExecutableEntry {
                key: executable.key.clone(),
                fn_id: *fn_id,
            })
            .collect();
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
        module.struct_schemas = self
            .program
            .struct_schemas
            .entries()
            .map(|(name, fields)| (name.as_ref().clone(), fields.as_ref().clone()))
            .collect();
        let mut program = NativeProgram {
            entry,
            module,
            executable_entries,
            bodies: self.native_bodies,
            callable_boundaries: self.callable_boundaries,
        };
        #[cfg(test)]
        self.telemetry.raw_event2(
            &["fz", "compiler2", "native_program", "before_sharing"],
            &self.root_id,
            &program,
        );
        program.deduplicate_equivalent_sibling_graphs();
        Ok(program)
    }

    fn lower_callable_construction_wrapper(&mut self, boundary: &NativeCallableBoundary) -> Result<(), FatalError> {
        let all_members_diverge = boundary.members.iter().all(|member| member.target_return.diverges);
        if matches!(boundary.return_form, BackendCallableReturn::Diverges) != all_members_diverge {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} return form disagrees with its member return contracts",
                    boundary.id.as_u32()
                ),
            ));
        }
        let mut ctx = NativeFnCtx::new(
            boundary.wrapper_fn,
            &format!("callable_wrapper_{}", boundary.id.as_u32()),
            FnCategory::User,
            NativeBodyOrigin::CallableWrapper {
                identity: boundary.id.as_u32(),
            },
            NativeEntryAbi::Direct,
            boundary
                .capture_reprs
                .iter()
                .copied()
                .chain(std::iter::repeat_n(AbiValueRepr::ValueRef, boundary.call_arity))
                .collect(),
            self.world.types_mut().any(),
            callable_return_reprs(boundary.return_form),
            None,
            EffectSummary::default(),
        );
        let mut param_tys = boundary
            .captures
            .iter()
            .flat_map(|capture| capture.layout.tys.iter().copied())
            .collect::<Vec<_>>();
        param_tys.extend(std::iter::repeat_n(self.world.types_mut().any(), boundary.call_arity));
        let params = ctx.entry_params(&param_tys);
        let captures = params[..boundary.capture_reprs.len()].to_vec();
        let args = params[boundary.capture_reprs.len()..].to_vec();
        match &boundary.selection {
            Some(selection) => {
                if selection.input_count != args.len() {
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "callable construction {} dispatch expects {} inputs but exposes {} call arguments",
                            boundary.id.as_u32(),
                            selection.input_count,
                            args.len(),
                        ),
                    ));
                }
                let mut state = DispatchState::new(args.clone(), Vec::new(), Vec::new());
                self.lower_callable_construction_wrapper_dispatch_node(
                    &mut ctx,
                    boundary,
                    selection,
                    selection.graph.root,
                    &captures,
                    &args,
                    &mut state,
                )?;
            }
            None if boundary.members.len() == 1 => {
                self.lower_callable_construction_wrapper_member(&mut ctx, boundary, 0, &captures, &args)?;
            }
            None if boundary.members.is_empty() => {
                ctx.halt_with_atom(self.atom_id("function_clause"));
            }
            None => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "callable construction {:?} has {} members without a selection plan",
                        boundary.id.as_u32(),
                        boundary.members.len(),
                    ),
                ));
            }
        }
        self.finish_native_fn(ctx);
        Ok(())
    }

    fn lower_callable_construction_wrapper_dispatch_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        boundary: &NativeCallableBoundary,
        plan: &PatternDispatchPlan<Ty>,
        node_id: GraphNodeId,
        captures: &[Var],
        args: &[Var],
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = plan.graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} dispatch graph node {:?} is out of bounds",
                    boundary.id.as_u32(),
                    node_id,
                ),
            ));
        };
        match node {
            DispatchNode::Fail => {
                ctx.halt_with_atom(self.atom_id("function_clause"));
                Ok(())
            }
            DispatchNode::Outcome { outcome, .. } => {
                let body_id = plan
                    .outcome(outcome)
                    .ok_or_else(|| {
                        incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            format!(
                                "callable construction {} dispatch outcome {:?} is out of bounds",
                                boundary.id.as_u32(),
                                outcome,
                            ),
                        )
                    })?
                    .body_id;
                self.lower_callable_construction_wrapper_member(ctx, boundary, body_id as usize, captures, args)
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let cond = self.lower_dispatch_region(ctx, plan, predicate.subject, &predicate.region, state)?;
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
                self.lower_callable_construction_wrapper_dispatch_node(
                    ctx,
                    boundary,
                    plan,
                    on_match.target,
                    captures,
                    args,
                    &mut match_state,
                )?;
                ctx.current_block = else_b;
                self.lower_callable_construction_wrapper_dispatch_node(
                    ctx,
                    boundary,
                    plan,
                    on_miss.target,
                    captures,
                    args,
                    state,
                )
            }
        }
    }

    fn lower_callable_construction_wrapper_member(
        &mut self,
        ctx: &mut NativeFnCtx,
        boundary: &NativeCallableBoundary,
        member_index: usize,
        captures: &[Var],
        args: &[Var],
    ) -> Result<(), FatalError> {
        let member = boundary.members.get(member_index).ok_or(FatalError)?;
        let target_index = self
            .program
            .executable_index(&member.target, self.world.types())
            .ok_or(FatalError)?;
        let target = &self.program.executables()[target_index];
        let mut values = vec![
            None;
            member
                .target_inputs
                .iter()
                .map(|input| input.semantic_index)
                .max()
                .map_or(0, |index| index + 1)
        ];
        let mut capture_cursor = 0;
        for (capture_index, capture) in boundary.captures.iter().enumerate() {
            let input = *member.capture_semantic_inputs.get(capture_index).ok_or(FatalError)?;
            let repr_count = capture.layout.reprs.len();
            if repr_count == 0 {
                continue;
            }
            let lanes = captures
                .get(capture_cursor..capture_cursor + repr_count)
                .ok_or(FatalError)?
                .to_vec();
            values[input] = Some(if capture.layout.reprs.as_ref() == [AbiValueRepr::ValueRef] {
                NativeBoundValue::Runtime(lanes[0])
            } else {
                NativeBoundValue::Transport {
                    shape: capture.layout.structural,
                    lanes,
                }
            });
            capture_cursor += repr_count;
        }
        if capture_cursor != captures.len() {
            return Err(FatalError);
        }
        if member.surface_semantic_inputs.len() != args.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} member {:?} publishes {} surface semantic inputs for {} wrapper call lanes",
                    boundary.id.as_u32(),
                    member.target,
                    member.surface_semantic_inputs.len(),
                    args.len(),
                ),
            ));
        }
        for (surface_index, semantic_index) in member.surface_semantic_inputs.iter().copied().enumerate() {
            if member
                .target_inputs
                .iter()
                .find(|input| input.semantic_index == semantic_index)
                .is_some_and(|input| !input.layout.reprs.is_empty())
            {
                values[semantic_index] = Some(NativeBoundValue::Runtime(args[surface_index]));
            }
        }
        if member
            .target_inputs
            .iter()
            .any(|input| values[input.semantic_index].is_none() && !input.layout.reprs.is_empty())
        {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} could not assign its published capture and surface lanes to member {:?}: captures={}, surface_inputs={:?}, target_inputs={:?}, assigned={:?}",
                    boundary.id.as_u32(),
                    member.target,
                    captures.len(),
                    member.surface_semantic_inputs,
                    member.target_inputs,
                    values.iter().map(Option::is_some).collect::<Vec<_>>(),
                ),
            ));
        }
        let input_reprs = member
            .target_inputs
            .iter()
            .flat_map(|input| input.layout.reprs.iter().copied())
            .collect::<Vec<_>>();
        if input_reprs.as_slice() != target.abi.param_reprs.as_slice() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} target {:?} input ABI {:?} disagrees with declared ABI {:?}",
                    boundary.id.as_u32(),
                    member.target,
                    input_reprs,
                    target.abi.param_reprs,
                ),
            ));
        }
        let mut target_args = Vec::new();
        for input in &member.target_inputs {
            if input.layout.reprs.is_empty() {
                continue;
            }
            if let Some(value) = &values[input.semantic_index] {
                if input.layout.reprs.as_ref() == [AbiValueRepr::ValueRef] {
                    target_args.push(self.materialize_native_value(ctx, None, value)?);
                } else {
                    self.encode_runtime_value(ctx, target, None, value, input.layout.structural, &mut target_args)?;
                }
            }
        }
        if target_args.len() != input_reprs.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} emitted {} ABI arguments for target {:?}, which declares {}",
                    boundary.id.as_u32(),
                    target_args.len(),
                    member.target,
                    input_reprs.len(),
                ),
            ));
        }
        if member.target_return.diverges {
            Self::emit_native_no_return_call(ctx, DirectCallTarget::Local(member.target_fn), target_args);
            return Ok(());
        }
        let continuation = self.callable_wrapper_return_continuation(ctx, boundary, member)?;
        ctx.set_term(Term::Call {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee: DirectCallTarget::Local(member.target_fn),
            args: target_args,
            continuation,
        });
        Ok(())
    }

    fn callable_wrapper_return_continuation(
        &mut self,
        owner: &NativeFnCtx,
        boundary: &NativeCallableBoundary,
        member: &NativeConstructionMember,
    ) -> Result<Cont, FatalError> {
        let param_tys = member.target_return.layout.tys.to_vec();
        let fn_id = self.module.fresh_fn_id();
        let index = self.return_continuation_count;
        self.return_continuation_count += 1;
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &format!("callable_wrapper_return_{}_{}", owner.fn_id.0, index),
            FnCategory::CpsCont,
            NativeBodyOrigin::Continuation { owner: owner.fn_id },
            NativeEntryAbi::Continuation {
                extra_params: member.target_return.layout.reprs.len(),
            },
            member.target_return.layout.reprs.to_vec(),
            self.world.types_mut().any(),
            if member.target_return.layout.reprs.is_empty() {
                Vec::new()
            } else {
                callable_return_reprs(boundary.return_form)
            },
            None,
            EffectSummary::default(),
        );
        let params = ctx.entry_params(&param_tys);
        if params.len() != member.target_return.layout.reprs.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} return adapter exposes {} typed lanes for {} published return lane(s)",
                    boundary.id.as_u32(),
                    params.len(),
                    member.target_return.layout.reprs.len(),
                ),
            ));
        }
        let return_lanes = if member.target_return.layout.reprs.is_empty() {
            Vec::new()
        } else {
            let mut lane_index = 0;
            let value = self.decode_runtime_value_for_layout(&member.target_return.layout, &params, &mut lane_index)?;
            if lane_index != params.len() {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "callable construction {} consumed {} of {} target return lanes",
                        boundary.id.as_u32(),
                        lane_index,
                        params.len(),
                    ),
                ));
            }
            vec![self.materialize_native_value(&mut ctx, None, &value)?]
        };
        ctx.set_term(Term::ReturnLanes(return_lanes));
        self.finish_native_fn(ctx);
        Ok(Cont {
            fn_id,
            captured: Vec::new(),
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
        let (return_reprs, return_tuple_arity) = native_return_contract(self.world, &executable.abi.return_layout);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::Prelude,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.abi.param_reprs.clone(),
            executable.abi.materialized.return_ty,
            return_reprs,
            return_tuple_arity,
            executable.abi.effects,
        );
        let activation_inputs = executable.key.activation.inputs(self.world.types());
        let params = ctx.entry_params(activation_inputs.as_slice());
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
        entry_fns: &mut EntryFns,
    ) -> Result<(), FatalError> {
        let helper_ids = clauses.iter().map(|_| self.module.fresh_fn_id()).collect::<Vec<_>>();
        let fn_id = self.executable_fns[index];
        let name = format!(
            "{}__e{}",
            self.world.function_ref(executable.key.activation.function).name,
            index
        );
        let (return_reprs, return_tuple_arity) = native_return_contract(self.world, &executable.abi.return_layout);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::User,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.abi.param_reprs.clone(),
            executable.abi.materialized.return_ty,
            return_reprs,
            return_tuple_arity,
            executable.abi.effects,
        );
        let entry_tys = executable_input_tys(executable);
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let semantic_inputs = self.bind_executable_inputs(executable, &entry_vars)?;
        let dispatch = executable
            .abi
            .materialized
            .entry_dispatch
            .as_ref()
            .expect("clause dispatch lowering requires a settled entry dispatch");
        let required_inputs = dispatch.required_input_ordinals();
        let activation_inputs = executable.key.activation.inputs(self.world.types());
        let inputs = semantic_inputs
            .iter()
            .enumerate()
            .map(
                |(semantic_index, value)| match (required_inputs.contains(&semantic_index), value) {
                    (true, Some(value)) => {
                        self.materialize_native_value(&mut ctx, activation_inputs.get(semantic_index).copied(), value)
                    }
                    (true, None) => Err(incomplete_native_program(
                        self.telemetry,
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
        self.lower_dispatch_node(&mut ctx, dispatch, dispatch.plan().graph.root, &helper_ids, &mut state)?;
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
        entry_fns: &mut EntryFns,
        clause: &BackendClause,
    ) -> Result<(), FatalError> {
        let (return_reprs, return_tuple_arity) = native_return_contract(self.world, &executable.abi.return_layout);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            name,
            category,
            origin,
            NativeEntryAbi::Direct,
            executable.abi.param_reprs.clone(),
            executable.abi.materialized.return_ty,
            return_reprs,
            return_tuple_arity,
            executable.abi.effects,
        );
        let mut env = ValueEnv::default();
        let entry_tys = executable_input_tys(executable);
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let semantic_inputs = self.bind_executable_inputs(executable, &entry_vars)?;
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

    fn lower_entry_fn(
        &mut self,
        executable_index: usize,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        entry_id: ControlEntryId,
        fn_id: FnId,
    ) -> Result<(), FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
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
        let (return_reprs, return_tuple_arity) = native_return_contract(self.world, &executable.abi.return_layout);
        let mut ctx = NativeFnCtx::new(
            fn_id,
            &entry_name,
            entry_category,
            NativeBodyOrigin::Continuation {
                owner: self.executable_fns[executable_index],
            },
            entry_abi,
            param_reprs,
            executable.abi.materialized.return_ty,
            return_reprs,
            return_tuple_arity,
            executable.abi.effects,
        );
        let mut env = ValueEnv::default();
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let mut capture_offset = self.bind_entry_input(&mut ctx, executable, entry, &entry_vars, &mut env)?;
        self.mark_delivered_entry_semantics(&mut ctx, executable, entry, &entry_vars[..capture_offset])?;
        self.bind_entry_captures(&mut ctx, executable, entry, &entry_vars, &mut capture_offset, &mut env)?;
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
        entry_fns: &mut EntryFns,
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
                    let var = lower_backend_literal(ctx, &self.atom_ids, self.world.types_mut(), literal)?;
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::Tuple { value, items } => {
                    if let Some(layout) = executable.abi.value_layouts.get(value)
                        && let shape = layout.structural
                        && let ShapeDescr::Tuple(fields) = self.world.shape(shape).clone()
                    {
                        if fields.len() != items.len() {
                            return Err(FatalError);
                        }
                        if matches!(layout.carrier, super::super::pull::TransportCarrier::ValueRef(_)) {
                            let vars = self.env_runtime_vars(ctx, executable, env, items);
                            let (var, _) = ctx.emit_let(Prim::MakeTuple(vars));
                            self.bind_runtime_value(ctx, executable, env, *value, var);
                        } else {
                            let mut lanes = Vec::new();
                            for (item, field_layout) in items.iter().copied().zip(fields) {
                                self.encode_env_value_for_layout(ctx, executable, env, item, field_layout, &mut lanes)?;
                            }
                            bind_local_value(
                                ctx,
                                executable,
                                env,
                                *value,
                                NativeBoundValue::Transport { shape, lanes },
                            );
                        }
                    } else {
                        let fields = self.env_runtime_vars(ctx, executable, env, items);
                        let (var, _) = ctx.emit_let(Prim::MakeTuple(fields));
                        self.bind_runtime_value(ctx, executable, env, *value, var);
                    }
                }
                BackendStep::List { value, items, tail } => {
                    let vars = self.env_runtime_vars(ctx, executable, env, items);
                    let tail = self.list_tail_runtime_var(ctx, executable, env, *tail)?;
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
                BackendStep::FunctionRef {
                    value,
                    function: _,
                    construction,
                } => {
                    // A reference the transport plan settled to `Nothing` never
                    // reaches here: backend lowering already omits it
                    // (`construction_step_or_omitted`), so every surviving
                    // `FunctionRef` carries lanes.
                    let shape = value_shape(executable, *value);
                    if let Some(identity) = construction {
                        let boundary = self.native_callable_boundary_for_construction(identity)?;
                        let var = self.emit_callable_construction(ctx, boundary, Vec::new());
                        self.bind_runtime_value(ctx, executable, env, *value, var);
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
                    construction,
                } => {
                    // As with `FunctionRef`, a settled-`Nothing` closure is omitted
                    // by backend lowering, so every surviving `Lambda` really is
                    // constructed and its captures really are demanded.
                    let shape = value_shape(executable, *value);
                    let callable_boundary = construction
                        .as_ref()
                        .map(|identity| self.native_callable_boundary_for_construction(identity))
                        .transpose()?;
                    if let Some(boundary) = callable_boundary {
                        let mut capture_lanes = Vec::new();
                        let capture_layouts = self.callable_boundaries[boundary.as_u32() as usize]
                            .captures
                            .iter()
                            .map(|slot| slot.layout.clone())
                            .collect::<Vec<_>>();
                        if capture_layouts.len() != captures.len() {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                "native callable construction capture inventory disagrees with its lambda producer",
                            ));
                        }
                        for (capture, layout) in captures.iter().copied().zip(capture_layouts) {
                            let local = env_local_value(env, capture)?;
                            self.encode_runtime_value_for_layout(
                                ctx,
                                executable,
                                Some(capture),
                                &local,
                                &layout,
                                &mut capture_lanes,
                            )?;
                        }
                        let var = self.emit_callable_construction(ctx, boundary, capture_lanes);
                        self.bind_runtime_value(ctx, executable, env, *value, var);
                    } else {
                        let callable = callable_id_for_shape(self.world, shape)?;
                        let callable_descr = self.world.callable(callable).clone();
                        let capture_layouts = callable_descr.capture_layouts.to_vec();
                        if capture_layouts.len() != captures.len() {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                "native direct callable capture count did not match transport callable descriptor",
                            ));
                        }
                        let mut capture_lanes = Vec::new();
                        for (capture, layout) in captures.iter().copied().zip(capture_layouts) {
                            self.encode_env_value_for_layout(
                                ctx,
                                executable,
                                env,
                                capture,
                                layout,
                                &mut capture_lanes,
                            )?;
                        }
                        if capture_lanes.len() != self.world.shape_width(shape) {
                            return Err(incomplete_native_program(
                                self.telemetry,
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
                    let expected = lower_backend_literal(ctx, &self.atom_ids, self.world.types_mut(), literal)?;
                    let (matches, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, source, expected));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::AssertStruct { source, module_name } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let predicate = RuntimeTypePredicate::named_struct(module_name);
                    let (matches, _) = ctx.emit_let(Prim::RuntimeTypeTest(source, Box::new(predicate)));
                    ctx.assert_truthy(matches, self.atom_id("match_error"));
                }
                BackendStep::RequireMapValue { value, source, key } => {
                    let source = self.env_runtime_var(ctx, executable, env, *source);
                    let key = lower_backend_literal(ctx, &self.atom_ids, self.world.types_mut(), key)?;
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
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        tail: &BackendTail,
    ) -> Result<(), FatalError> {
        match tail {
            BackendTail::Value { value, dest } => {
                self.lower_value_destination(ctx, executable, entries, entry_fns, env, *value, dest)
            }
            BackendTail::DirectCall { target, args, dest, .. } => match target {
                CallEdge::Direct(direct) => self.lower_direct_call_tail(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    &direct.callee,
                    args,
                    dest,
                    &direct.return_flow,
                ),
                CallEdge::Dispatch(dispatch) => {
                    self.lower_dispatch_call_tail(ctx, executable, entries, entry_fns, env, dispatch, args, dest)
                }
                CallEdge::Indirect { .. } => Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "native direct call materialized as an indirect closure edge; Indirect is closure-call-only",
                )),
            },
            BackendTail::ClosureCall {
                callee,
                target,
                args,
                dest,
                return_flow,
                ..
            } => {
                let callee_value = env.cloned_value(*callee);
                let direct_capture_lanes = self.direct_closure_capture_lanes(
                    executable,
                    *callee,
                    callee_value.as_ref(),
                    target.as_ref(),
                    args.len(),
                )?;
                let direct_call = if let Some(capture_lanes) = direct_capture_lanes {
                    let target = target.as_ref().ok_or_else(|| {
                        incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            "native direct-only closure call did not settle an exact local target",
                        )
                    })?;
                    let target = self
                        .program
                        .executable_index(target, self.world.types())
                        .ok_or(FatalError)?;
                    let callee_executable = &self.program.executables()[target];
                    let mut call_args = capture_lanes;
                    let mut direct_ok = true;
                    let capture_inputs_end = callee_executable
                        .key
                        .activation
                        .input_len(self.world.types())
                        .checked_sub(args.len())
                        .ok_or(FatalError)?;
                    for (surface_index, arg) in args.iter().enumerate() {
                        let semantic_index = capture_inputs_end + surface_index;
                        let Some(target_input) = callee_executable
                            .abi
                            .semantic_inputs
                            .iter()
                            .find(|input| input.semantic_index == semantic_index)
                        else {
                            continue;
                        };
                        if target_input.layout.reprs.is_empty() {
                            continue;
                        }
                        let local = env_local_value(env, arg.value)?;
                        if matches!(
                            target_input.layout.carrier,
                            super::super::pull::TransportCarrier::ValueRef(_)
                        ) {
                            self.encode_runtime_value_for_layout(
                                ctx,
                                callee_executable,
                                Some(arg.value),
                                &local,
                                &target_input.layout,
                                &mut call_args,
                            )?;
                        } else {
                            if !self.closure_fast_path_arg_is_structural(&local, target_input.layout.structural) {
                                direct_ok = false;
                                break;
                            }
                            self.encode_runtime_value(
                                ctx,
                                callee_executable,
                                Some(arg.value),
                                &local,
                                target_input.layout.structural,
                                &mut call_args,
                            )?;
                        }
                    }
                    if call_args.len() != callee_executable.abi.param_reprs.len() {
                        direct_ok = false;
                    }
                    if !return_flow.as_ref().is_some_and(|flow| match flow {
                        BackendReturnFlow::NoReturn | BackendReturnFlow::Tail => true,
                        BackendReturnFlow::Continue { source } | BackendReturnFlow::Deliver { source, .. } => {
                            source.as_ref() == &callee_executable.abi.return_layout
                        }
                    }) {
                        direct_ok = false;
                    }
                    direct_ok.then_some((target, call_args))
                } else {
                    None
                };
                if let Some((target, call_args)) = direct_call {
                    let callee = DirectCallTarget::Local(self.executable_fns[target]);
                    let return_flow = return_flow.as_ref().ok_or_else(|| {
                        incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            "native direct closure call is missing return-flow facts",
                        )
                    })?;
                    self.emit_native_direct_call_tail(
                        ctx,
                        executable,
                        entries,
                        entry_fns,
                        env,
                        callee,
                        call_args,
                        dest,
                        return_flow,
                    )
                } else {
                    let callee_value = callee_value.as_ref().ok_or_else(|| {
                        incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            "native indirect closure call has no runtime callee value",
                        )
                    })?;
                    let closure = self.materialize_native_value(ctx, None, callee_value)?;
                    let call_args = self.env_runtime_vars(
                        ctx,
                        executable,
                        env,
                        &args.iter().map(|arg| arg.value).collect::<Vec<_>>(),
                    );
                    match (return_flow.as_ref(), dest) {
                        (Some(BackendReturnFlow::Continue { source }), ControlDestination::Return) => {
                            let continuation =
                                self.return_lane_continuation_for_source_payload(ctx, executable, source)?;
                            ctx.set_term(Term::CallClosure {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                closure,
                                args: call_args,
                                continuation,
                            });
                            Ok(())
                        }
                        (Some(BackendReturnFlow::Deliver { source, entry }), ControlDestination::Deliver(entry_id)) => {
                            if entry != entry_id {
                                return Err(incomplete_native_program(
                                    self.telemetry,
                                    self.root_id,
                                    "native indirect closure call delivered return-flow targets another entry",
                                ));
                            }
                            let continuation = self.deliver_entry_continuation_for_source(
                                ctx, executable, entries, entry_fns, *entry_id, env, source,
                            )?;
                            ctx.set_term(Term::CallClosure {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                closure,
                                args: call_args,
                                continuation,
                            });
                            Ok(())
                        }
                        (Some(BackendReturnFlow::NoReturn), _)
                        | (Some(BackendReturnFlow::Tail), ControlDestination::Return)
                        | (None, ControlDestination::Return)
                        | (Some(BackendReturnFlow::Deliver { .. }), ControlDestination::Return) => {
                            ctx.set_term(Term::TailCallClosure {
                                ident: CallsiteIdent::from_source(Span::DUMMY),
                                closure,
                                args: call_args,
                            });
                            Ok(())
                        }
                        (None, ControlDestination::Deliver(_))
                        | (Some(BackendReturnFlow::Tail), ControlDestination::Deliver(_))
                        | (Some(BackendReturnFlow::Continue { .. }), ControlDestination::Deliver(_)) => {
                            Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                "native indirect closure call with Deliver destination is missing delivered return-flow",
                            ))
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
                    callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, *then_entry)),
                    args: then_args,
                    is_back_edge: false,
                });
                ctx.current_block = else_b;
                let else_args = self.entry_capture_args(ctx, executable, entries, *else_entry, env)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, *else_entry)),
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
                            body: entry_fns.reference(&mut self.module, clause.entry),
                            span: clause.span,
                        })
                    })
                    .collect::<Result<Vec<_>, FatalError>>()?;
                let after = after
                    .map(|after| {
                        Ok(ReceiveAfter {
                            ident: CallsiteIdent::from_source(after.span),
                            timeout: self.env_runtime_var(ctx, executable, env, after.timeout),
                            body: entry_fns.reference(&mut self.module, after.entry),
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

    #[allow(clippy::too_many_arguments)]
    fn lower_direct_call_tail(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        callee: &CallTarget<ExecutableKey>,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
        return_flow: &BackendReturnFlow,
    ) -> Result<(), FatalError> {
        let (callee, call_args) = self.native_direct_call_target_and_args(ctx, executable, env, callee, args)?;
        self.emit_native_direct_call_tail(
            ctx,
            executable,
            entries,
            entry_fns,
            env,
            callee,
            call_args,
            dest,
            return_flow,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_dispatch_call_tail(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        dispatch: &DispatchCallEdge<ExecutableKey, BackendReturnFlow>,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
    ) -> Result<(), FatalError> {
        let input_ids = args.iter().map(|arg| arg.value).collect::<Vec<_>>();
        let required_inputs = required_dispatch_input_ordinals(&dispatch.plan);
        let input_vars = input_ids
            .iter()
            .enumerate()
            .map(|(index, value)| {
                if required_inputs.contains(&index) {
                    self.env_runtime_var(ctx, executable, env, *value)
                } else {
                    ctx.emit_let(Prim::Const(Const::Nil)).0
                }
            })
            .collect();
        let mut state = DispatchState::new(input_vars, Vec::new(), Vec::new());
        self.lower_dispatch_call_node(
            ctx,
            executable,
            entries,
            entry_fns,
            env,
            dispatch,
            args,
            dest,
            dispatch.plan.graph.root,
            &mut state,
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_dispatch_call_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        dispatch: &DispatchCallEdge<ExecutableKey, BackendReturnFlow>,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
        node_id: GraphNodeId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = dispatch.plan.graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("call dispatch graph node {:?} is out of bounds", node_id),
            ));
        };
        match node {
            DispatchNode::Fail => {
                ctx.halt_with_atom(self.atom_id(UNREACHABLE_CONTROL_ATOM));
                Ok(())
            }
            DispatchNode::Outcome { outcome, .. } => {
                let Some(body_id) = dispatch.plan.outcome(outcome).map(|outcome| outcome.body_id) else {
                    ctx.halt_with_atom(self.atom_id(UNREACHABLE_CONTROL_ATOM));
                    return Ok(());
                };
                let Some(arm) = dispatch.arms.iter().find(|arm| arm.body_id == body_id) else {
                    ctx.halt_with_atom(self.atom_id(UNREACHABLE_CONTROL_ATOM));
                    return Ok(());
                };
                let (callee, call_args) =
                    self.native_direct_call_target_and_args(ctx, executable, env, &arm.callee, args)?;
                self.emit_native_direct_call_tail(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    callee,
                    call_args,
                    dest,
                    &arm.return_flow,
                )
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let cond =
                    self.lower_dispatch_region(ctx, &dispatch.plan, predicate.subject, &predicate.region, state)?;
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
                self.lower_dispatch_call_node(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    dispatch,
                    args,
                    dest,
                    on_match.target,
                    &mut match_state,
                )?;
                ctx.current_block = else_b;
                self.lower_dispatch_call_node(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    dispatch,
                    args,
                    dest,
                    on_miss.target,
                    state,
                )
            }
        }
    }

    fn native_direct_call_target_and_args(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        callee: &CallTarget<ExecutableKey>,
        args: &[super::super::artifact::BackendCallArg],
    ) -> Result<(DirectCallTarget, Vec<Var>), FatalError> {
        match callee {
            CallTarget::Local(callee) => {
                let callee = self
                    .program
                    .executable_index(callee, self.world.types())
                    .ok_or(FatalError)?;
                let callee_executable = &self.program.executables()[callee];
                let mut lanes = Vec::new();
                for (semantic_index, arg) in args.iter().enumerate() {
                    let Some(target_input) = callee_executable
                        .abi
                        .semantic_inputs
                        .iter()
                        .find(|input| input.semantic_index == semantic_index)
                    else {
                        continue;
                    };
                    if target_input.layout.reprs.is_empty() {
                        continue;
                    }
                    let local = env_local_value(env, arg.value)?;
                    if !matches!(
                        target_input.layout.carrier,
                        super::super::pull::TransportCarrier::ValueRef(_)
                    ) {
                        self.encode_runtime_value_for_layout(
                            ctx,
                            executable,
                            Some(arg.value),
                            &local,
                            &target_input.layout,
                            &mut lanes,
                        )?;
                    } else {
                        let value = self.materialize_native_value(
                            ctx,
                            executable.abi.materialized.value_types.get(&arg.value).copied(),
                            &local,
                        )?;
                        lanes.push(value);
                    }
                }
                if lanes.len() != callee_executable.abi.param_reprs.len() {
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "native direct call emitted {} arguments for target {:?}, which declares {}",
                            lanes.len(),
                            callee_executable.key,
                            callee_executable.abi.param_reprs.len(),
                        ),
                    ));
                }
                Ok((DirectCallTarget::Local(self.executable_fns[callee]), lanes))
            }
            CallTarget::ProviderBoundary(function) => Ok((
                DirectCallTarget::ProviderBoundary(self.world.function_mfa(*function)),
                self.env_runtime_vars(
                    ctx,
                    executable,
                    env,
                    &args.iter().map(|arg| arg.value).collect::<Vec<_>>(),
                ),
            )),
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn emit_native_direct_call_tail(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        callee: DirectCallTarget,
        call_args: Vec<Var>,
        dest: &ControlDestination,
        return_flow: &BackendReturnFlow,
    ) -> Result<(), FatalError> {
        if matches!(return_flow, BackendReturnFlow::NoReturn) {
            Self::emit_native_no_return_call(ctx, callee, call_args);
            return Ok(());
        }
        match dest {
            ControlDestination::Return => match return_flow {
                BackendReturnFlow::NoReturn => unreachable!(),
                BackendReturnFlow::Tail => {
                    ctx.set_term(Term::TailCall {
                        ident: CallsiteIdent::from_source(Span::DUMMY),
                        callee,
                        args: call_args,
                        is_back_edge: false,
                    });
                    Ok(())
                }
                BackendReturnFlow::Continue { source } => {
                    let continuation = self.return_lane_continuation_for_source_payload(ctx, executable, source)?;
                    ctx.set_term(Term::Call {
                        ident: CallsiteIdent::from_source(Span::DUMMY),
                        callee,
                        args: call_args,
                        continuation,
                    });
                    Ok(())
                }
                BackendReturnFlow::Deliver { .. } => Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "native direct call with Return destination carried Deliver return-flow",
                )),
            },
            ControlDestination::Deliver(entry_id) => {
                let continuation = self.delivered_call_continuation(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    *entry_id,
                    env,
                    Some(return_flow),
                )?;
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

    fn emit_native_no_return_call(ctx: &mut NativeFnCtx, callee: DirectCallTarget, args: Vec<Var>) {
        ctx.set_term(Term::TailCall {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee,
            args,
            is_back_edge: false,
        });
    }

    fn lower_value_destination(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
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
                    callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, *entry_id)),
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
        if executable.abi.return_layout.layout.reprs.is_empty() {
            return Ok(Vec::new());
        }
        let mut lanes = Vec::new();
        let local = env
            .cloned_value(value_id)
            .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
        self.encode_runtime_value_for_layout(
            ctx,
            executable,
            Some(value_id),
            &local,
            &executable.abi.return_layout.layout,
            &mut lanes,
        )?;
        Ok(lanes)
    }

    fn entry_signature(
        &mut self,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        reusable_cons_captures: &[ReusableConsCapture],
    ) -> (Vec<Ty>, Vec<AbiValueRepr>, NativeEntryAbi) {
        let mut param_tys = entry
            .params
            .iter()
            .map(|value| {
                executable
                    .abi
                    .materialized
                    .value_types
                    .get(value)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any())
            })
            .collect::<Vec<_>>();
        let capture_lane_tys = entry
            .captures
            .iter()
            .flat_map(|capture| capture.layout.tys.iter().copied())
            .collect::<Vec<_>>();
        let capture_lane_reprs = entry
            .captures
            .iter()
            .flat_map(|capture| capture.layout.reprs.iter().copied())
            .collect::<Vec<_>>();
        let physical_capture_tys = reusable_cons_captures
            .iter()
            .map(|capture| {
                executable
                    .abi
                    .materialized
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
            BackendEntryOrigin::DeliveredResume { value: _, layout } => {
                let (mut entry_tys, mut param_reprs) = (layout.layout.tys.to_vec(), layout.layout.reprs.to_vec());
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
            BackendEntryOrigin::DeliveredResume { value, layout } => {
                if matches!(layout.layout.carrier, super::super::pull::TransportCarrier::Absent)
                    && matches!(self.world.shape(layout.layout.structural), ShapeDescr::Nothing)
                {
                    bind_local_value(ctx, executable, env, *value, NativeBoundValue::Absent);
                    return Ok(0);
                }
                let mut lane_index = 0;
                let bound = self.decode_runtime_value_for_layout(&layout.layout, entry_vars, &mut lane_index)?;
                bind_local_value(ctx, executable, env, *value, bound);
                Ok(lane_index)
            }
        }
    }

    fn bind_entry_captures(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        entry_vars: &[Var],
        capture_offset: &mut usize,
        env: &mut ValueEnv,
    ) -> Result<(), FatalError> {
        for capture in &entry.captures {
            if capture.layout.reprs.is_empty() {
                bind_local_value(ctx, executable, env, capture.value, NativeBoundValue::Absent);
                continue;
            }
            let bound = self
                .decode_runtime_value_for_layout(&capture.layout, entry_vars, capture_offset)
                .map_err(|_| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "native entry {:?} failed to decode capture {} with shape {:?}; offset={} params={}",
                            ctx.origin,
                            capture.value.as_u32(),
                            self.world.shape(capture.layout.structural),
                            *capture_offset,
                            entry_vars.len()
                        ),
                    )
                })?;
            bind_local_value(ctx, executable, env, capture.value, bound);
        }
        for capture in entry.reusable_cons_captures.iter().copied() {
            let physical_var = *entry_vars.get(*capture_offset).ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native entry {:?} missing reusable cons capture param at offset {} of {}",
                        ctx.origin,
                        *capture_offset,
                        entry_vars.len()
                    ),
                )
            })?;
            self.bind_runtime_value(ctx, executable, env, capture.source, physical_var);
            let semantic_var = self.env_runtime_var(ctx, executable, env, capture.head);
            ctx.builder.record_reusable_cons_cell(semantic_var, physical_var);
            *capture_offset += 1;
        }
        Ok(())
    }

    fn mark_delivered_entry_semantics(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        input_vars: &[Var],
    ) -> Result<(), FatalError> {
        let BackendEntryOrigin::DeliveredResume { value, layout } = &entry.origin else {
            return Ok(());
        };
        if input_vars.is_empty() {
            return Ok(());
        }
        let shape = layout.layout.structural;
        let mut lane_index = 0;
        if matches!(layout.layout.carrier, super::super::pull::TransportCarrier::ValueRef(_)) {
            let ignore = RuntimeDemand::ignore();
            let demand = executable
                .abi
                .materialized
                .runtime_demand
                .value_demands
                .get(value)
                .unwrap_or(&ignore);
            mark_ignored_carrier_lane(&mut ctx.builder, input_vars, demand, &mut lane_index)?;
        } else if let Some(demand) = executable.abi.materialized.runtime_demand.value_demands.get(value) {
            mark_ignored_lanes_for_demand(self.world, &mut ctx.builder, input_vars, shape, demand, &mut lane_index)?;
        } else {
            mark_all_layout_lanes_ignored(
                self.world,
                &mut ctx.builder,
                input_vars,
                TransportLayout::structural(shape),
                &mut lane_index,
            )?;
        }
        if lane_index != input_vars.len() {
            return Err(incomplete_native_program(
                self.telemetry,
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

    fn delivered_call_continuation(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        entry_id: ControlEntryId,
        env: &ValueEnv,
        return_flow: Option<&BackendReturnFlow>,
    ) -> Result<Cont, FatalError> {
        let Some(BackendReturnFlow::Deliver { source, entry }) = return_flow else {
            return self.entry_continuation(ctx, executable, entries, entry_fns, entry_id, env);
        };
        if *entry != entry_id {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native delivered call targeted entry {} but return-flow targets {}",
                    entry_id.as_u32(),
                    entry.as_u32()
                ),
            ));
        }
        self.deliver_entry_continuation_for_source(ctx, executable, entries, entry_fns, entry_id, env, source)
    }

    fn entry_continuation(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        entry_id: ControlEntryId,
        env: &ValueEnv,
    ) -> Result<Cont, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        if entry.origin.input_value().is_none() {
            return Err(incomplete_native_program(
                self.telemetry,
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
            fn_id: entry_fns.reference(&mut self.module, entry_id),
            captured: self.entry_capture_args(ctx, executable, entries, entry_id, env)?,
        })
    }

    fn return_lane_continuation_for_source_payload(
        &mut self,
        ctx: &NativeFnCtx,
        executable: &BackendExecutable,
        source_return: &super::super::artifact::BackendReturnLayout,
    ) -> Result<Cont, FatalError> {
        let param_tys = source_return.layout.tys.to_vec();
        let source_reprs = source_return.layout.reprs.to_vec();
        if param_tys.len() != source_reprs.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native return-lane continuation from {:?} expected {} source lane types, got {} reprs",
                    source_return,
                    param_tys.len(),
                    source_reprs.len()
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
            NativeBodyOrigin::Continuation { owner: ctx.fn_id },
            NativeEntryAbi::Continuation {
                extra_params: source_reprs.len(),
            },
            source_reprs,
            executable.abi.materialized.return_ty,
            ctx.return_reprs.clone(),
            ctx.return_tuple_arity,
            executable.abi.effects,
        );
        let params = cont_ctx.entry_params(param_tys.as_slice());
        let mut lane_index = 0;
        let source_value = self.decode_runtime_value_for_layout(&source_return.layout, &params, &mut lane_index)?;
        if lane_index != params.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native return-lane continuation from {:?} consumed {} source lanes, but received {}",
                    source_return,
                    lane_index,
                    params.len()
                ),
            ));
        }
        let mut return_lanes = Vec::new();
        self.encode_runtime_value_for_layout(
            &mut cont_ctx,
            executable,
            None,
            &source_value,
            &executable.abi.return_layout.layout,
            &mut return_lanes,
        )?;
        cont_ctx.set_term(Term::ReturnLanes(return_lanes));
        self.finish_native_fn(cont_ctx);
        Ok(Cont {
            fn_id,
            captured: Vec::new(),
        })
    }

    fn deliver_entry_continuation_for_source(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        entry_id: ControlEntryId,
        env: &ValueEnv,
        source: &super::super::artifact::BackendReturnLayout,
    ) -> Result<Cont, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let Some(value) = entry.origin.input_value() else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native delivered adapter targeted entry {} without an input value",
                    entry_id.as_u32()
                ),
            ));
        };

        let (source_tys, source_reprs) = (source.layout.tys.to_vec(), source.layout.reprs.to_vec());
        if source_tys.len() != source_reprs.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native delivered adapter for {:?} expected {} source lane types, got {} reprs",
                    source,
                    source_tys.len(),
                    source_reprs.len()
                ),
            ));
        }
        let extra_params = source_reprs.len();
        let source_is_absent = source_reprs.is_empty();

        let capture_lane_tys = entry
            .captures
            .iter()
            .flat_map(|capture| capture.layout.tys.iter().copied())
            .collect::<Vec<_>>();
        let capture_lane_reprs = entry
            .captures
            .iter()
            .flat_map(|capture| capture.layout.reprs.iter().copied())
            .collect::<Vec<_>>();
        let physical_capture_tys = entry
            .reusable_cons_captures
            .iter()
            .map(|capture| {
                executable
                    .abi
                    .materialized
                    .value_types
                    .get(&capture.source)
                    .copied()
                    .unwrap_or_else(|| self.world.types_mut().any())
            })
            .collect::<Vec<_>>();

        let mut param_tys = source_tys;
        let mut param_reprs = source_reprs;
        param_tys.extend(capture_lane_tys.iter().copied());
        param_reprs.extend(capture_lane_reprs.iter().copied());
        param_tys.extend(physical_capture_tys.iter().copied());
        param_reprs.extend(
            physical_capture_tys
                .iter()
                .copied()
                .map(|ty| abi_value_repr(self.world, ty)),
        );

        let fn_id = self.module.fresh_fn_id();
        let index = self.return_continuation_count;
        self.return_continuation_count += 1;
        let name = format!("deliver_lanes__{}_{}", ctx.fn_id.0, index);
        let mut cont_ctx = NativeFnCtx::new(
            fn_id,
            &name,
            FnCategory::CpsCont,
            NativeBodyOrigin::Continuation { owner: ctx.fn_id },
            NativeEntryAbi::Continuation { extra_params },
            param_reprs,
            executable.abi.materialized.return_ty,
            ctx.return_reprs.clone(),
            ctx.return_tuple_arity,
            executable.abi.effects,
        );
        let entry_vars = cont_ctx.entry_params(param_tys.as_slice());
        let mut source_lane_index = 0;
        let delivered = self.decode_runtime_value_for_layout(&source.layout, &entry_vars, &mut source_lane_index)?;
        let mut adapter_env = ValueEnv::default();
        bind_local_value(&mut cont_ctx, executable, &mut adapter_env, value, delivered);
        let mut lane_index = extra_params;
        self.bind_entry_captures(
            &mut cont_ctx,
            executable,
            entry,
            &entry_vars,
            &mut lane_index,
            &mut adapter_env,
        )?;
        if lane_index != entry_vars.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native delivered adapter for entry {} consumed {} params but exposes {}",
                    entry_id.as_u32(),
                    lane_index,
                    entry_vars.len()
                ),
            ));
        }
        let args = if source_is_absent {
            self.entry_capture_args(&mut cont_ctx, executable, entries, entry_id, &adapter_env)?
        } else {
            self.entry_call_args_from_value(&mut cont_ctx, executable, entries, entry_id, &adapter_env, value)?
        };
        cont_ctx.set_term(Term::TailCall {
            ident: CallsiteIdent::from_source(Span::DUMMY),
            callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, entry_id)),
            args,
            is_back_edge: false,
        });
        self.finish_native_fn(cont_ctx);

        Ok(Cont {
            fn_id,
            captured: self.entry_capture_args(ctx, executable, entries, entry_id, env)?,
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
        for capture in &entry.captures {
            if capture.layout.reprs.is_empty() {
                continue;
            }
            let local = env_local_value(env, capture.value)?;
            self.encode_runtime_value_for_layout(
                ctx,
                executable,
                Some(capture.value),
                &local,
                &capture.layout,
                &mut args,
            )?;
        }
        for capture in &entry.reusable_cons_captures {
            args.push(self.env_runtime_var(ctx, executable, env, capture.source));
        }
        Ok(args)
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
                    self.telemetry,
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
            if entry_captures.len() != capture_ids.len()
                || entry_captures
                    .iter()
                    .zip(&capture_ids)
                    .any(|(left, right)| !same_entry_capture_contract(left, right))
            {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "receive entries did not settle on one shared capture layout",
                ));
            }
        }
        let mut args = Vec::new();
        for capture in capture_ids {
            if capture.layout.reprs.is_empty() {
                continue;
            }
            let local = env_local_value(env, capture.value)?;
            self.encode_runtime_value_for_layout(
                ctx,
                executable,
                Some(capture.value),
                &local,
                &capture.layout,
                &mut args,
            )?;
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
            BackendEntryOrigin::DeliveredResume { layout, .. } => {
                let mut lanes = Vec::new();
                let local = env
                    .cloned_value(value_id)
                    .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
                self.encode_runtime_value_for_layout(
                    ctx,
                    executable,
                    Some(value_id),
                    &local,
                    &layout.layout,
                    &mut lanes,
                )?;
                lanes
            }
        };
        args.extend(self.entry_capture_args(ctx, executable, entries, entry_id, env)?);
        Ok(args)
    }

    fn bind_executable_inputs(
        &mut self,
        executable: &BackendExecutable,
        params: &[Var],
    ) -> Result<Vec<Option<NativeBoundValue>>, FatalError> {
        let semantic_arity = executable.key.activation.input_len(self.world.types());
        let mut bound = vec![None; semantic_arity];
        let mut lane_index = 0;
        for input in executable
            .abi
            .semantic_inputs
            .iter()
            .filter(|input| !input.layout.reprs.is_empty())
        {
            let value = self.decode_runtime_value_for_layout(&input.layout, params, &mut lane_index)?;
            bound[input.semantic_index] = Some(value);
        }
        if lane_index != params.len() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native executable {:?} decoded {} of {} published input lane(s)",
                    executable.key,
                    lane_index,
                    params.len(),
                ),
            ));
        }
        Ok(bound)
    }

    fn decode_runtime_value_for_layout(
        &mut self,
        layout: &super::super::artifact::BackendValueLayout,
        params: &[Var],
        lane_index: &mut usize,
    ) -> Result<NativeBoundValue, FatalError> {
        self.decode_runtime_value(
            TransportLayout {
                structural: layout.structural,
                carrier: layout.carrier,
            },
            params,
            lane_index,
        )
    }

    fn decode_runtime_value(
        &mut self,
        layout: TransportLayout,
        params: &[Var],
        lane_index: &mut usize,
    ) -> Result<NativeBoundValue, FatalError> {
        if layout.carrier.is_value_ref() {
            return Ok(NativeBoundValue::Runtime(next_runtime_lane(params, lane_index)?));
        }
        let shape = layout.structural;
        match self.world.shape(shape).clone() {
            ShapeDescr::Nothing => Ok(NativeBoundValue::Absent),
            ShapeDescr::Lane(_) => Ok(NativeBoundValue::Runtime(next_runtime_lane(params, lane_index)?)),
            ShapeDescr::Callable(_) | ShapeDescr::Tuple(_) => {
                let width = self.world.shape_width(shape);
                let end = lane_index.checked_add(width).ok_or(FatalError)?;
                let lanes = params.get(*lane_index..end).ok_or(FatalError)?.to_vec();
                *lane_index = end;
                Ok(NativeBoundValue::Transport { shape, lanes })
            }
        }
    }

    fn lower_dispatch_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        dispatch: &crate::compiler2::ExecutableDispatch,
        node_id: GraphNodeId,
        helper_ids: &[FnId],
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = dispatch.plan().graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.telemetry,
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
                            self.telemetry,
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
                let cond =
                    self.lower_dispatch_region(ctx, dispatch.plan(), predicate.subject, &predicate.region, state)?;
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
                self.lower_dispatch_node(ctx, dispatch, on_match.target, helper_ids, &mut match_state)?;
                ctx.current_block = else_b;
                self.lower_dispatch_node(ctx, dispatch, on_miss.target, helper_ids, state)
            }
        }
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_control_dispatch_node(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        plan: &PatternDispatchPlan<Ty>,
        arm_entries: &[ControlEntryId],
        miss_entry: ControlEntryId,
        node_id: GraphNodeId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = plan.graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("local dispatch graph node {:?} is out of bounds", node_id),
            ));
        };
        match node {
            DispatchNode::Fail => {
                let args = self.entry_capture_args(ctx, executable, entries, miss_entry, env)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, miss_entry)),
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
                        callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, miss_entry)),
                        args,
                        is_back_edge: false,
                    });
                    return Ok(());
                };
                let arm_entry = *arm_entries.get(body_id as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("local dispatch arm {} is out of bounds", body_id),
                    )
                })?;
                let args = self.control_dispatch_entry_args(ctx, executable, entries, arm_entry, env, state)?;
                ctx.set_term(Term::TailCall {
                    ident: CallsiteIdent::from_source(Span::DUMMY),
                    callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, arm_entry)),
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
                let cond = self.lower_dispatch_region(ctx, plan, predicate.subject, &predicate.region, state)?;
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
                    self.telemetry,
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
                    self.telemetry,
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
        plan: &PatternDispatchPlan<Ty>,
        subject: SubjectId,
        region: &Region<Ty>,
        state: &mut DispatchState,
    ) -> Result<Var, FatalError> {
        Ok(match region {
            Region::Type(ty) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let predicate = self.world.types().runtime_type_predicate(ty);
                let (var, _) = ctx.emit_let(Prim::RuntimeTypeTest(subject, Box::new(predicate)));
                var
            }
            Region::List(ListRegion::Empty) => {
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
                let key = lower_dispatch_const(ctx, &self.atom_ids, self.world.types_mut(), key)?;
                let (value, _) = ctx.emit_let(Prim::MatcherMapGet(subject, key));
                let (is_miss, _) = ctx.emit_let(Prim::IsMatcherMapMiss(value));
                let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, is_miss, false_v));
                var
            }
            Region::Equal(ComparisonValue::Const(value)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let expected = lower_dispatch_const(ctx, &self.atom_ids, self.world.types_mut(), value)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, subject, expected));
                var
            }
            Region::Guard(guard) => {
                let expr = plan.guards.get(guard.0 as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("dispatch guard {:?} is out of bounds", guard),
                    )
                })?;
                self.lower_guard_expr(ctx, plan, state, expr)?
            }
            Region::Equal(ComparisonValue::Pinned(pinned)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let pinned = self.dispatch_pinned_var(plan, state, *pinned)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Eq, subject, pinned));
                var
            }
            Region::Bitstring(_) => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "native entry-dispatch lowering does not support bitstring tests yet",
                ));
            }
        })
    }

    fn lower_guard_expr(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        expr: &PatternGuardExpr<Ty>,
    ) -> Result<Var, FatalError> {
        Ok(match expr {
            PatternGuardExpr::Const(value) => lower_dispatch_const(ctx, &self.atom_ids, self.world.types_mut(), value)?,
            PatternGuardExpr::Subject(subject) => self.dispatch_subject_var(ctx, plan, state, *subject)?,
            PatternGuardExpr::Unary { op, expr } => {
                let input = self.lower_guard_expr(ctx, plan, state, expr)?;
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
                let lhs = self.lower_guard_expr(ctx, plan, state, lhs)?;
                let rhs = self.lower_guard_expr(ctx, plan, state, rhs)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(lower_guard_binop(*op), lhs, rhs));
                var
            }
            PatternGuardExpr::Dispatch { .. } => {
                if let PatternGuardExpr::Dispatch { inputs, dispatch } = expr {
                    self.lower_guard_dispatch(ctx, plan, state, inputs, dispatch)?
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
        parent_plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        inputs: &[PatternGuardExpr<Ty>],
        dispatch: &crate::dispatch_matrix::pattern::PatternGuardDispatch<Ty>,
    ) -> Result<Var, FatalError> {
        let input_vars = inputs
            .iter()
            .map(|input| self.lower_guard_expr(ctx, parent_plan, state, input))
            .collect::<Result<Vec<_>, _>>()?;
        let done_value = ctx.builder.fresh_var();
        let done_b = ctx.builder.block(vec![done_value]);
        let fail_b = ctx.builder.block(vec![]);
        let mut dispatch_state = DispatchState::new(input_vars, Vec::new(), Vec::new());
        self.lower_guard_dispatch_node(
            ctx,
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
        plan: &PatternDispatchPlan<Ty>,
        bodies: &[PatternGuardExpr<Ty>],
        node_id: GraphNodeId,
        done_b: BlockId,
        fail_b: BlockId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let Some(node) = plan.graph.node(node_id).cloned() else {
            return Err(incomplete_native_program(
                self.telemetry,
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
                        self.telemetry,
                        self.root_id,
                        format!("guard dispatch outcome {:?} is out of bounds", outcome),
                    )
                })?;
                let body = bodies.get(outcome.body_id as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("guard dispatch body {} is out of bounds", outcome.body_id),
                    )
                })?;
                let value = self.lower_guard_expr(ctx, plan, state, body)?;
                ctx.set_term(Term::Goto(done_b, vec![value]));
                Ok(())
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let cond = self.lower_dispatch_region(ctx, plan, predicate.subject, &predicate.region, state)?;
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
                self.lower_guard_dispatch_node(ctx, plan, bodies, on_match.target, done_b, fail_b, &mut match_state)?;
                ctx.current_block = else_b;
                self.lower_guard_dispatch_node(ctx, plan, bodies, on_miss.target, done_b, fail_b, state)
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
                self.telemetry,
                self.root_id,
                format!("dispatch subject {:?} is out of bounds", subject),
            ));
        };
        let var = match &subject_data.source {
            crate::dispatch_matrix::SubjectSource::Input { ordinal } => {
                state.dispatch_inputs.get(*ordinal as usize).copied().ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
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
                    let key = lower_dispatch_const(ctx, &self.atom_ids, self.world.types_mut(), key)?;
                    let (var, _) = ctx.emit_let(Prim::MapGet(map, key));
                    var
                }
                crate::dispatch_matrix::ProjectionKind::BitstringField(index) => {
                    return Err(incomplete_native_program(
                        self.telemetry,
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
                self.telemetry,
                self.root_id,
                format!("dispatch pinned {:?} is out of bounds", pinned),
            )
        })?;
        if let Some(input) = pin.input {
            return state.dispatch_inputs.get(input as usize).copied().ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!("dispatch pinned input {} is out of bounds", input),
                )
            });
        }
        state.pinned.get(pinned.0 as usize).copied().ok_or_else(|| {
            incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("dispatch pinned capture {:?} is out of bounds", pinned),
            )
        })
    }

    fn atom_id(&self, name: &str) -> u32 {
        *self.atom_ids.get(name).expect("required atom should be interned")
    }

    fn native_callable_boundary_for_construction(
        &self,
        identity: &TransportPosition,
    ) -> Result<NativeCallableBoundaryId, FatalError> {
        let identity_fn = self.construction_identity_fns.get(identity).ok_or_else(|| {
            incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("native callable construction names unknown construction identity {identity:?}"),
            )
        })?;
        self.callable_boundaries
            .iter()
            .find(|boundary| boundary.identity_fn == *identity_fn)
            .map(NativeCallableBoundary::id)
            .ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!("native callable construction {identity:?} has no materialized native boundary"),
                )
            })
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
        let ty = executable.abi.materialized.value_types.get(&value_id).copied();
        self.materialize_native_value(ctx, ty, &value).unwrap_or_else(|error| {
            // fz-hwn.27.5 — name the predicate at the failure site. A bare-variable
            // (value-template) value has no runtime representation, so it binds
            // `Absent` and cannot be materialized. When that is the cause, this is
            // the fz-hwn.23 phantom: a value-template activation reached the
            // backend. `is_value_template` is the discriminator; the cure is
            // grounding/pruning the activation before lowering (fz-hwn.27.8).
            if ty.is_some_and(|ty| self.world.types().is_value_template(&ty)) {
                let shown = ty.map(|ty| self.world.types().display(&ty)).unwrap_or_default();
                panic!(
                    "native lowering invariant failed: backend value {:?} in executable {:?} is a \
                     value-template ({shown}) — a value-template activation reached the backend and \
                     cannot be materialized (fz-hwn.23; predicate is_value_template)",
                    value_id, executable.key,
                )
            }
            panic!(
                "native lowering invariant failed: backend value {:?} in executable {:?} must be runtime-materializable; value={value:?}; error={error:?}",
                value_id, executable.key,
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

    fn list_tail_runtime_var(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        tail: Option<ValueId>,
    ) -> Result<Option<Var>, FatalError> {
        let Some(tail) = tail else {
            return Ok(None);
        };
        if matches!(env.value(tail), Some(NativeBoundValue::Absent)) && self.value_is_exact_empty_list(executable, tail)
        {
            return Ok(None);
        }
        Ok(Some(self.env_runtime_var(ctx, executable, env, tail)))
    }

    fn value_is_exact_empty_list(&mut self, executable: &BackendExecutable, value: ValueId) -> bool {
        let Some(ty) = executable.abi.materialized.value_types.get(&value).copied() else {
            return false;
        };
        self.ty_is_exact_empty_list(ty)
    }

    fn ty_is_exact_empty_list(&mut self, ty: Ty) -> bool {
        let empty = self.world.types_mut().empty_list();
        self.world.types().is_equivalent(&ty, &empty)
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
        let var = match value {
            NativeBoundValue::Absent if ty.is_some_and(|ty| self.ty_is_exact_empty_list(ty)) => {
                ctx.emit_let(Prim::MakeList(Vec::new(), None)).0
            }
            NativeBoundValue::Absent => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native attempted to materialize absent value as runtime value with ty {ty:?} in {:?}",
                        ctx.origin
                    ),
                ));
            }
            NativeBoundValue::Runtime(var) => *var,
            NativeBoundValue::Transport { shape, lanes } => self.materialize_transport_value(ctx, *shape, lanes)?,
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
    ) -> Result<Var, FatalError> {
        match self.world.shape(shape).clone() {
            ShapeDescr::Nothing => Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native attempted to materialize nothing-shaped transport value {shape:?} in {:?}",
                    ctx.origin
                ),
            )),
            ShapeDescr::Lane(_) => lanes.first().copied().ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native lane-shaped transport value {shape:?} has no runtime lane while materializing in {:?}",
                        ctx.origin,
                    ),
                )
            }),
            ShapeDescr::Tuple(fields) => {
                let mut vars = Vec::with_capacity(fields.len());
                for field in self.transport_field_views(shape, lanes, &fields)? {
                    vars.push(self.materialize_native_value(ctx, None, &field)?);
                }
                Ok(ctx.emit_let(Prim::MakeTuple(vars)).0)
            }
            ShapeDescr::Callable(callable) => {
                let descr = self.world.callable(callable);
                if descr.function.is_none() && lanes.len() == 1 {
                    return Ok(lanes[0]);
                }
                let capture_lanes = self.world.shape_width(shape);
                if lanes.len() != capture_lanes {
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "native callable transport value {shape:?} has {} lanes, but callable {callable:?} expects {} capture lanes in {:?}",
                            lanes.len(),
                            capture_lanes,
                            ctx.origin,
                        ),
                    ));
                }
                if descr.function.is_none() {
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "native attempted to rematerialize generic callable shape {:?} in {:?}; first-class callable values must come from transport publication lanes",
                            shape, ctx.origin,
                        ),
                    ));
                }
                Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native attempted to materialize direct-only callable {callable:?} in {:?}",
                        ctx.origin
                    ),
                ))
            }
        }
    }

    fn emit_callable_construction(
        &self,
        ctx: &mut NativeFnCtx,
        boundary: NativeCallableBoundaryId,
        captures: Vec<Var>,
    ) -> Var {
        let identity = self.callable_boundaries[boundary.as_u32() as usize].identity_fn;
        let prim = if captures.is_empty() {
            Prim::MakeFnRef(ctx.fresh_callsite(), identity)
        } else {
            Prim::MakeClosure(ctx.fresh_callsite(), identity, captures)
        };
        ctx.emit_let(prim).0
    }

    fn transport_tuple_arity(&self, value: &NativeBoundValue) -> Option<usize> {
        let NativeBoundValue::Transport { shape, .. } = value else {
            return None;
        };
        match self.world.shape(*shape) {
            ShapeDescr::Tuple(fields) => Some(fields.len()),
            ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => None,
        }
    }

    fn transport_tuple_field(
        &self,
        value: &NativeBoundValue,
        index: usize,
    ) -> Result<Option<NativeBoundValue>, FatalError> {
        let NativeBoundValue::Transport { shape, lanes, .. } = value else {
            return Ok(None);
        };
        let ShapeDescr::Tuple(fields) = self.world.shape(*shape).clone() else {
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
        let ShapeDescr::Callable(callable) = self.world.shape(*shape) else {
            return Ok(None);
        };
        let descr = self.world.callable(*callable);
        if descr.function.is_none() {
            return Ok(None);
        }
        if lanes.len() != self.world.shape_width(*shape) {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native direct callable transport value {shape:?} has {} lanes, but callable {callable:?} expects {} capture lanes",
                    lanes.len(),
                    self.world.shape_width(*shape),
                ),
            ));
        }
        Ok(Some(lanes.clone()))
    }

    fn direct_closure_capture_lanes(
        &self,
        caller: &BackendExecutable,
        callee: ValueId,
        value: Option<&NativeBoundValue>,
        target: Option<&ExecutableKey>,
        surface_arity: usize,
    ) -> Result<Option<Vec<Var>>, FatalError> {
        let mut absent = true;
        if let Some(value) = value {
            if let Some(lanes) = self.direct_callable_lanes(value)? {
                return Ok(Some(lanes));
            }
            absent = matches!(value, NativeBoundValue::Absent);
        }
        let Some(target) = target else {
            return Ok(None);
        };
        let target = self
            .program
            .executable_index(target, self.world.types())
            .ok_or(FatalError)?;
        let executable = &self.program.executables()[target];
        let capture_inputs_end = executable
            .key
            .activation
            .input_len(self.world.types())
            .checked_sub(surface_arity)
            .ok_or(FatalError)?;
        if executable
            .abi
            .semantic_inputs
            .iter()
            .any(|input| input.semantic_index < capture_inputs_end && !input.layout.reprs.is_empty())
        {
            if !absent {
                return Ok(None);
            }
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native closure call owner={:?} callee={callee:?} bound={value:?} resolves to target={:?} with absent physical identity, but capture input range 0..{capture_inputs_end} has exact layouts {:?}",
                    caller.key,
                    executable.key,
                    executable
                        .abi
                        .semantic_inputs
                        .iter()
                        .filter(|input| input.semantic_index < capture_inputs_end)
                        .collect::<Vec<_>>(),
                ),
            ));
        }
        Ok(Some(Vec::new()))
    }

    fn closure_fast_path_arg_is_structural(&self, value: &NativeBoundValue, shape: ShapeId) -> bool {
        if !self.world.shape_contains_callable(shape) {
            return true;
        }
        matches!(
            value,
            NativeBoundValue::Transport {
                shape: value_shape,
                ..
            } if *value_shape == shape
        )
    }

    fn tuple_field_values_for_encoding(
        &mut self,
        ctx: &mut NativeFnCtx,
        value: &NativeBoundValue,
        fields: &[TransportLayout],
    ) -> Result<Vec<NativeBoundValue>, FatalError> {
        if let NativeBoundValue::Transport {
            shape: value_shape,
            lanes,
            ..
        } = value
            && let ShapeDescr::Tuple(source_fields) = self.world.shape(*value_shape)
            && source_fields.len() == fields.len()
        {
            return self.transport_field_views(*value_shape, lanes, source_fields);
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
        fields: &[TransportLayout],
    ) -> Result<Vec<NativeBoundValue>, FatalError> {
        if lanes.len() != self.world.shape_width(shape) {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native transport tuple view for {shape:?} has {} lanes, but shape width is {}",
                    lanes.len(),
                    self.world.shape_width(shape),
                ),
            ));
        }
        let mut offset = 0_usize;
        let mut values = Vec::with_capacity(fields.len());
        for field in fields.iter().copied() {
            let width = self.world.layout_width(field);
            let end = offset.checked_add(width).ok_or(FatalError)?;
            let field_lanes = lanes.get(offset..end).ok_or(FatalError)?.to_vec();
            let value = if field.carrier.is_value_ref() {
                NativeBoundValue::Runtime(*field_lanes.first().ok_or(FatalError)?)
            } else {
                match self.world.shape(field.structural) {
                    ShapeDescr::Nothing => NativeBoundValue::Absent,
                    ShapeDescr::Lane(_) => NativeBoundValue::Runtime(*field_lanes.first().ok_or(FatalError)?),
                    ShapeDescr::Tuple(_) | ShapeDescr::Callable(_) => NativeBoundValue::Transport {
                        shape: field.structural,
                        lanes: field_lanes,
                    },
                }
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
            ..
        } = value
            && *value_shape == shape
        {
            lanes.extend(value_lanes.iter().copied());
            return Ok(());
        }
        match self.world.shape(shape).clone() {
            ShapeDescr::Nothing => Ok(()),
            ShapeDescr::Lane(lane) => {
                let ty = value_id
                    .and_then(|value_id| executable.abi.materialized.value_types.get(&value_id).copied())
                    .unwrap_or_else(|| self.world.lane(lane).ty);
                lanes.push(self.materialize_native_value(ctx, Some(ty), value)?);
                Ok(())
            }
            ShapeDescr::Tuple(fields) => {
                let tuple_fields = self.tuple_field_values_for_encoding(ctx, value, &fields)?;
                for (field, field_layout) in tuple_fields.iter().zip(fields.iter().copied()) {
                    self.encode_transport_layout(ctx, executable, None, field, field_layout, lanes)?;
                }
                Ok(())
            }
            ShapeDescr::Callable(callable) => {
                let descr = self.world.callable(callable);
                let descriptor_lanes = self.world.shape_lane_ids(shape);
                if descr.function.is_none()
                    && let [lane] = descriptor_lanes.as_slice()
                {
                    let ty = self.world.lane(*lane).ty;
                    lanes.push(self.materialize_native_value(ctx, Some(ty), value)?);
                    return Ok(());
                }
                if let NativeBoundValue::Runtime(var) = value {
                    // A whole closure standing where a callable's captures are
                    // wanted as lanes. The callee grounded the callable from
                    // its own key and asks for the parts; the caller reached it
                    // through a dispatch that proved the identity but carries
                    // the value boxed, so the parts come back out of the box
                    // here (fz-kdt.125). Zero capture lanes is the elided case
                    // and never reaches this encoder.
                    let Some(function) = descr.function else {
                        return Err(incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            format!(
                                "native cannot project captures out of a callable that names no function in {:?}",
                                ctx.origin
                            ),
                        ));
                    };
                    let constructions = self.constructions_minting(callable);
                    if constructions.is_empty() {
                        return Err(incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            format!(
                                "native cannot project captures out of callable {callable:?} for function {}: no construction mints it in {:?}",
                                function.as_u32(),
                                ctx.origin,
                            ),
                        ));
                    }
                    for index in 0..descriptor_lanes.len() {
                        let (capture, _) = ctx.emit_let(Prim::ClosureCapture {
                            closure: *var,
                            constructions: constructions.clone(),
                            index: index as u32,
                        });
                        lanes.push(capture);
                    }
                    return Ok(());
                }
                Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native attempted to encode callable shape {:?} ({:?}) for value {:?} from {:?} in {:?}; callable values must be supplied by matching transport lanes or a published value seam",
                        shape, descr, value_id, value, ctx.origin,
                    ),
                ))
            }
        }
    }

    fn encode_env_value_for_layout(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        value_id: ValueId,
        layout: TransportLayout,
        lanes: &mut Vec<Var>,
    ) -> Result<(), FatalError> {
        if self.world.layout_width(layout) == 0 {
            return Ok(());
        }
        let local = env
            .cloned_value(value_id)
            .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
        self.encode_transport_layout(ctx, executable, Some(value_id), &local, layout, lanes)
    }

    fn encode_runtime_value_for_layout(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value_id: Option<ValueId>,
        value: &NativeBoundValue,
        layout: &super::super::artifact::BackendValueLayout,
        lanes: &mut Vec<Var>,
    ) -> Result<(), FatalError> {
        self.encode_transport_layout(
            ctx,
            executable,
            value_id,
            value,
            TransportLayout {
                structural: layout.structural,
                carrier: layout.carrier,
            },
            lanes,
        )
    }

    fn encode_transport_layout(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value_id: Option<ValueId>,
        value: &NativeBoundValue,
        layout: TransportLayout,
        lanes: &mut Vec<Var>,
    ) -> Result<(), FatalError> {
        if layout.carrier.is_value_ref() {
            lanes.push(self.materialize_native_value(
                ctx,
                value_id.and_then(|value_id| executable.abi.materialized.value_types.get(&value_id).copied()),
                value,
            )?);
            return Ok(());
        }
        let shape = layout.structural;
        match self.world.shape(shape).clone() {
            ShapeDescr::Tuple(fields) => {
                let tuple_fields = self.tuple_field_values_for_encoding(ctx, value, &fields)?;
                for (field, field_layout) in tuple_fields.iter().zip(fields.iter().copied()) {
                    self.encode_transport_layout(ctx, executable, None, field, field_layout, lanes)?;
                }
                Ok(())
            }
            ShapeDescr::Callable(_) => self.encode_runtime_value(ctx, executable, value_id, value, shape, lanes),
            ShapeDescr::Nothing | ShapeDescr::Lane(_) => {
                self.encode_runtime_value(ctx, executable, value_id, value, shape, lanes)
            }
        }
    }
}

fn same_entry_capture_contract(left: &BackendEntryCapture, right: &BackendEntryCapture) -> bool {
    left.value == right.value && left.layout == right.layout
}

#[derive(Default)]
struct EntryFns {
    ids: HashMap<ControlEntryId, FnId>,
    pending: VecDeque<(ControlEntryId, FnId)>,
}

impl EntryFns {
    fn reference(&mut self, module: &mut ModuleBuilder, entry: ControlEntryId) -> FnId {
        *self.ids.entry(entry).or_insert_with(|| {
            let fn_id = module.fresh_fn_id();
            self.pending.push_back((entry, fn_id));
            fn_id
        })
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

#[derive(Debug, Clone)]
enum NativeBoundValue {
    Absent,
    Runtime(Var),
    Transport { shape: ShapeId, lanes: Vec<Var> },
}

impl NativeBoundValue {
    fn runtime_lane(&self) -> Option<Var> {
        match self {
            Self::Runtime(var) => Some(*var),
            Self::Absent | Self::Transport { .. } => None,
        }
    }
}

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
        self.value(value).and_then(NativeBoundValue::runtime_lane)
    }
}

fn native_return_contract(
    world: &World,
    layout: &super::super::artifact::BackendReturnLayout,
) -> (Vec<AbiValueRepr>, Option<usize>) {
    let tuple_arity = match world.shape(layout.layout.structural) {
        ShapeDescr::Tuple(fields) => Some(fields.len()),
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Callable(_) => None,
    };
    (layout.layout.reprs.to_vec(), tuple_arity)
}

fn native_construction_capture_reprs(
    wrapper: &super::super::artifact::BackendConstructionWrapper,
) -> Box<[AbiValueRepr]> {
    wrapper
        .captures
        .iter()
        .flat_map(|capture| capture.layout.reprs.iter().copied())
        .collect()
}

fn native_block_param_reprs(
    world: &mut World,
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
    extern_marshals: HashMap<ExternMarshalSite, ExternTy>,
    failure_blocks: HashMap<u32, BlockId>,
    origin: NativeBodyOrigin,
    entry_abi: NativeEntryAbi,
    param_reprs: Vec<AbiValueRepr>,
    return_ty: Ty,
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
            extern_marshals: HashMap::new(),
            failure_blocks: HashMap::new(),
            origin,
            entry_abi,
            param_reprs,
            return_ty,
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
            return_reprs: self.return_reprs,
            return_tuple_arity: self.return_tuple_arity,
            block_param_reprs: HashMap::new(),
            value_types: self.value_types,
            extern_marshals: self.extern_marshals,
            effects: self.effects,
        };
        (fn_ir, body)
    }
}

fn env_local_value(env: &ValueEnv, value: ValueId) -> Result<NativeBoundValue, FatalError> {
    env.cloned_value(value).ok_or(FatalError)
}

fn executable_input_tys(executable: &BackendExecutable) -> Vec<Ty> {
    executable
        .abi
        .semantic_inputs
        .iter()
        .flat_map(|input| input.layout.tys.iter().copied())
        .collect()
}

fn value_shape(executable: &BackendExecutable, value: ValueId) -> ShapeId {
    executable
        .abi
        .value_layouts
        .get(&value)
        .map(|layout| layout.structural)
        .unwrap_or_else(|| panic!("backend executable should publish a layout for {value:?}"))
}

fn callable_id_for_shape(world: &World, shape: ShapeId) -> Result<CallableId, FatalError> {
    match world.shape(shape) {
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
        && let Some(ty) = executable.abi.materialized.value_types.get(&value).copied()
    {
        ctx.value_types.insert(var, ty);
    }
    env.insert(value, bound);
}

fn collect_extern_marshals(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    program: &BackendProgram,
) -> Result<HashMap<usize, Vec<ExternTy>>, FatalError> {
    let mut out = HashMap::new();
    for executable in program.executables() {
        if let BackendBody::Clauses { clauses, entries, .. } = &executable.body {
            for clause in clauses {
                collect_extern_marshals_in_steps(world, root_id, program, &clause.projections, &mut out)?;
            }
            for entry in entries {
                collect_extern_marshals_in_tail(world, tel, root_id, program, &entry.tail, &mut out)?;
            }
        }
    }
    Ok(out)
}

fn collect_extern_marshals_in_steps(
    _world: &World,
    _root_id: RootId,
    _program: &BackendProgram,
    _steps: &[BackendStep],
    _out: &mut HashMap<usize, Vec<ExternTy>>,
) -> Result<(), FatalError> {
    Ok(())
}

fn collect_extern_marshals_in_tail(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    program: &BackendProgram,
    tail: &BackendTail,
    out: &mut HashMap<usize, Vec<ExternTy>>,
) -> Result<(), FatalError> {
    if let BackendTail::DirectCall { target, .. } = tail {
        match target {
            CallEdge::Direct(direct) => {
                collect_extern_marshals_for_call_target(
                    world,
                    tel,
                    root_id,
                    program,
                    &direct.callee,
                    direct.extern_marshals.as_ref(),
                    out,
                )?;
            }
            CallEdge::Dispatch(dispatch) => {
                for arm in &dispatch.arms {
                    collect_extern_marshals_for_call_target(
                        world,
                        tel,
                        root_id,
                        program,
                        &arm.callee,
                        arm.extern_marshals.as_ref(),
                        out,
                    )?;
                }
            }
            // Indirect is closure-call-only (never a DirectCall edge); no
            // local callee to collect extern marshals for.
            CallEdge::Indirect { .. } => {}
        }
    }
    Ok(())
}

fn collect_extern_marshals_for_call_target(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    program: &BackendProgram,
    callee: &CallTarget<ExecutableKey>,
    extern_marshals: Option<&Vec<ExternTy>>,
    out: &mut HashMap<usize, Vec<ExternTy>>,
) -> Result<(), FatalError> {
    if let CallTarget::Local(key) = callee
        && let Some(callee) = program.executable_index(key, world.types())
        && matches!(program.executables()[callee].body, BackendBody::Extern { .. })
    {
        let signature = match &program.executables()[callee].body {
            BackendBody::Extern { signature } => signature,
            BackendBody::Clauses { .. } => unreachable!(),
        };
        let marshals = extern_marshals.cloned().unwrap_or_else(|| signature.params.clone());
        match out.get(&callee) {
            Some(existing) if existing != &marshals => {
                return Err(incomplete_native_program(
                    tel,
                    root_id,
                    format!(
                        "extern executable {} has conflicting marshal plans: {:?} vs {:?}",
                        callee, existing, marshals
                    ),
                ));
            }
            Some(_) => {}
            None => {
                out.insert(callee, marshals);
            }
        }
    }
    Ok(())
}

/// Lower a compile-time literal to a fresh `Var` holding its `Prim::Const`.
///
/// This `Var` never flows through type inference (it has no `ValueId`), so
/// without registering its `Ty` here, every downstream codegen fast path
/// gated on `value_types` (equality, ordering, arithmetic dispatch) sees it
/// as untyped `any()` and falls back to the generic boxed slow path — e.g.
/// comparing a pattern-match tag against a literal atom like `:cont` boxed
/// the tag into a heap scalar on every check instead of taking the raw-atom
/// `icmp` fast path. Registering the literal's known type here is what lets
/// those fast paths recognize it.
fn lower_backend_literal(
    ctx: &mut NativeFnCtx,
    atom_ids: &HashMap<String, u32>,
    types: &mut Types,
    literal: &GroundValue,
) -> Result<Var, FatalError> {
    use crate::ground_value::BodyLiteral;
    let (var, ty) = match literal
        .as_body_literal()
        .expect("lower_backend_literal only ever sees a lowered-body literal")
    {
        BodyLiteral::Int(value) => (ctx.emit_let(Prim::Const(Const::Int(value))).0, types.int()),
        BodyLiteral::Float(bits) => (
            ctx.emit_let(Prim::Const(Const::Float(f64::from_bits(bits)))).0,
            types.float(),
        ),
        BodyLiteral::Atom(name) => (
            ctx.emit_let(Prim::Const(Const::Atom(*atom_ids.get(name).ok_or(FatalError)?)))
                .0,
            types.atom(),
        ),
        BodyLiteral::Bool(value) => (
            ctx.emit_let(Prim::Const(if value { Const::True } else { Const::False }))
                .0,
            types.bool(),
        ),
        BodyLiteral::Nil => (ctx.emit_let(Prim::Const(Const::Nil)).0, types.nil()),
        BodyLiteral::Binary(bytes) => {
            return Ok(ctx
                .emit_let(Prim::ConstBitstring(bytes.to_vec(), (bytes.len() * 8) as u64))
                .0);
        }
    };
    ctx.value_types.insert(var, ty);
    Ok(var)
}

/// Lower a dispatch-matrix clause-selector constant (the compile-time value
/// a multi-clause function's argument is tested against, e.g. the `:cont`
/// in a `{:cont, acc}` clause head) to a fresh `Var`.
///
/// See `lower_backend_literal`'s doc comment: this `Var` has no `ValueId`
/// and so never appears in type inference's `value_types`. Registering its
/// `Ty` here is what lets `lower_eq_binop`'s same-kind fast paths recognize
/// it instead of falling back to the generic boxed `fz_value_eq_ref` path —
/// this is the exact site responsible for boxing the `{:cont, acc}` /
/// `{:halt, acc}` tag on every `Enum.reduce` step.
fn lower_dispatch_const(
    ctx: &mut NativeFnCtx,
    atom_ids: &HashMap<String, u32>,
    types: &mut Types,
    value: &GroundValue,
) -> Result<Var, FatalError> {
    use crate::ground_value::DispatchShape;
    let (var, ty) = match value
        .as_dispatch_shape()
        .expect("lower_dispatch_const only ever sees a dispatch-matrix const")
    {
        DispatchShape::Int(value) => (ctx.emit_let(Prim::Const(Const::Int(value))).0, types.int()),
        DispatchShape::Float(bits) => (
            ctx.emit_let(Prim::Const(Const::Float(f64::from_bits(bits)))).0,
            types.float(),
        ),
        DispatchShape::Atom(name) => {
            let atom = *atom_ids.get(name).ok_or(FatalError)?;
            (ctx.emit_let(Prim::Const(Const::Atom(atom))).0, types.atom())
        }
        DispatchShape::Bool(value) => (
            ctx.emit_let(Prim::Const(if value { Const::True } else { Const::False }))
                .0,
            types.bool(),
        ),
        DispatchShape::Nil => (ctx.emit_let(Prim::Const(Const::Nil)).0, types.nil()),
        DispatchShape::Utf8Binary(bytes) => {
            return Ok(ctx
                .emit_let(Prim::ConstBitstring(bytes.to_vec(), (bytes.len() * 8) as u64))
                .0);
        }
    };
    ctx.value_types.insert(var, ty);
    Ok(var)
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
    _world: &World,
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

fn abi_value_repr(world: &mut World, ty: Ty) -> AbiValueRepr {
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

fn block_param_abi_value_repr(world: &mut World, ty: Ty) -> AbiValueRepr {
    match abi_value_repr(world, ty) {
        repr @ (AbiValueRepr::RawInt | AbiValueRepr::RawAtom) => repr,
        AbiValueRepr::RawF64 | AbiValueRepr::ValueRef => AbiValueRepr::ValueRef,
    }
}

fn mark_ignored_lanes_for_demand(
    world: &World,
    builder: &mut FnBuilder,
    vars: &[Var],
    shape: ShapeId,
    demand: &RuntimeDemand,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    match world.shape(shape) {
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
                        mark_all_layout_lanes_ignored(world, builder, vars, field, lane_index)?;
                    }
                    Ok(())
                }
                ShapeDemand::TupleFields(demands) => {
                    if demands.len() > fields.len() {
                        return Err(FatalError);
                    }
                    for (index, field) in fields.iter().copied().enumerate() {
                        if let Some(field_demand) = demands.get(index) {
                            mark_ignored_layout_lanes_for_demand(
                                world,
                                builder,
                                vars,
                                field,
                                field_demand,
                                lane_index,
                            )?;
                        } else {
                            mark_all_layout_lanes_ignored(world, builder, vars, field, lane_index)?;
                        }
                    }
                    Ok(())
                }
                ShapeDemand::Whole => skip_runtime_lanes(world, vars, shape, lane_index),
            }
        }
        ShapeDescr::Callable(_callable) => {
            let capture_lanes = world.shape_width(shape);
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

fn mark_ignored_layout_lanes_for_demand(
    world: &World,
    builder: &mut FnBuilder,
    vars: &[Var],
    layout: TransportLayout,
    demand: &RuntimeDemand,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    if layout.carrier.is_value_ref() {
        return mark_ignored_carrier_lane(builder, vars, demand, lane_index);
    }
    mark_ignored_lanes_for_demand(world, builder, vars, layout.structural, demand, lane_index)
}

fn mark_ignored_carrier_lane(
    builder: &mut FnBuilder,
    vars: &[Var],
    demand: &RuntimeDemand,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    let var = next_runtime_lane(vars, lane_index)?;
    if demand.is_ignore() {
        builder.mark_param_ignored(var);
    }
    Ok(())
}

fn mark_all_layout_lanes_ignored(
    world: &World,
    builder: &mut FnBuilder,
    vars: &[Var],
    layout: TransportLayout,
    lane_index: &mut usize,
) -> Result<(), FatalError> {
    for var in take_runtime_lanes(vars, lane_index, world.layout_width(layout))? {
        builder.mark_param_ignored(*var);
    }
    Ok(())
}

fn skip_runtime_lanes(world: &World, vars: &[Var], shape: ShapeId, lane_index: &mut usize) -> Result<(), FatalError> {
    take_runtime_lanes(vars, lane_index, world.shape_width(shape)).map(|_| ())
}

fn take_runtime_lanes<'a>(vars: &'a [Var], lane_index: &mut usize, width: usize) -> Result<&'a [Var], FatalError> {
    let end = lane_index.checked_add(width).ok_or(FatalError)?;
    let lanes = vars.get(*lane_index..end).ok_or(FatalError)?;
    *lane_index = end;
    Ok(lanes)
}

fn next_runtime_lane(vars: &[Var], lane_index: &mut usize) -> Result<Var, FatalError> {
    let var = vars.get(*lane_index).copied().ok_or(FatalError)?;
    *lane_index += 1;
    Ok(var)
}

fn missing_backend_value(_root_id: RootId, _value: ValueId) -> FatalError {
    FatalError
}

fn incomplete_native_program(
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    message: impl Into<String>,
) -> FatalError {
    let message = message.into();
    let diagnostic = Diagnostic::error(
        codes::ARTIFACT_INCOMPLETE_SEMANTIC_PLAN,
        format!("compiler2 native lowering for root {}: {}", root_id.as_u32(), message),
        Span::DUMMY,
    );
    emit_through(tel, std::slice::from_ref(&diagnostic));
    FatalError
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::compiler2::identity::{ActivationKey, ExecutableKey, ExecutableNeed, FunctionId};
    use crate::compiler2::pull::TransportCarrier;
    use crate::compiler2::transport::{LaneDescr, TransportClass};
    use crate::telemetry::sink::NullTelemetry;

    #[test]
    fn entry_function_references_schedule_each_recursive_helper_once() {
        let mut module = ModuleBuilder::new();
        let mut entries = EntryFns::default();
        let first = ControlEntryId::from_u32(7);
        let second = ControlEntryId::from_u32(2);
        assert!(entries.pending.is_empty());
        let first_fn = entries.reference(&mut module, first);
        assert_eq!(entries.pending.pop_front(), Some((first, first_fn)));
        let second_fn = entries.reference(&mut module, second);
        assert_eq!(entries.reference(&mut module, first), first_fn);
        assert_eq!(entries.pending.pop_front(), Some((second, second_fn)));
        assert_eq!(entries.reference(&mut module, second), second_fn);
        assert_eq!(entries.reference(&mut module, first), first_fn);
        assert!(
            entries.pending.is_empty(),
            "self and mutual references reuse emitted helpers"
        );
        assert_ne!(first_fn, second_fn);
    }

    fn empty_backend_program() -> BackendProgram {
        BackendProgram::empty_for_test()
    }

    fn test_executable(key: ExecutableKey, return_ty: Ty, nothing: ShapeId) -> BackendExecutable {
        BackendExecutable::for_test(key, return_ty, nothing)
    }

    fn encode_for_layout<T: crate::telemetry::Telemetry>(
        lowerer: &mut NativeLowerer<'_, '_, T>,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value: &NativeBoundValue,
        shape: ShapeId,
    ) -> Result<Vec<Var>, FatalError> {
        encode_with_layout(lowerer, ctx, executable, value, TransportLayout::structural(shape))
    }

    fn encode_with_layout<T: crate::telemetry::Telemetry>(
        lowerer: &mut NativeLowerer<'_, '_, T>,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value: &NativeBoundValue,
        layout: TransportLayout,
    ) -> Result<Vec<Var>, FatalError> {
        let mut encoded = Vec::new();
        lowerer.encode_transport_layout(ctx, executable, None, value, layout, &mut encoded)?;
        Ok(encoded)
    }

    fn defining_prim(function: &crate::fz_ir::FnIr, value: Var) -> Option<&Prim> {
        function
            .blocks
            .iter()
            .flat_map(|block| &block.stmts)
            .find_map(|statement| {
                let crate::fz_ir::Stmt::Let(defined, prim) = statement;
                (*defined == value).then_some(prim)
            })
    }

    fn tuple_shape(world: &mut World, fields: &[ShapeId]) -> ShapeId {
        world.intern_shape(ShapeDescr::Tuple(
            fields
                .iter()
                .copied()
                .map(TransportLayout::structural)
                .collect::<Vec<_>>()
                .into_boxed_slice(),
        ))
    }

    #[test]
    fn tuple_encoding_reprojects_same_arity_partial_transport_by_position() {
        let mut world = World::new();
        let int = world.types_mut().int();
        let inner_tuple_ty = world.types_mut().tuple(&[int, int, int]);
        let outer_tuple_ty = world.types_mut().tuple(&[int, inner_tuple_ty]);
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let lane = world.intern_lane(LaneDescr {
            ty: int,
            class: TransportClass::Value,
        });
        let scalar = world.intern_shape(ShapeDescr::Lane(lane));
        let inner_tuple_lane = world.intern_lane(LaneDescr {
            ty: inner_tuple_ty,
            class: TransportClass::Value,
        });
        let inner_tuple_value = world.intern_shape(ShapeDescr::Lane(inner_tuple_lane));
        let outer_tuple_lane = world.intern_lane(LaneDescr {
            ty: outer_tuple_ty,
            class: TransportClass::Value,
        });
        let source_inner = tuple_shape(&mut world, &[scalar, scalar, scalar]);
        let source = tuple_shape(&mut world, &[nothing, source_inner]);
        let destination = tuple_shape(&mut world, &[nothing, inner_tuple_value]);
        let selective_inner = tuple_shape(&mut world, &[nothing, scalar, nothing]);
        let selective_destination = tuple_shape(&mut world, &[nothing, selective_inner]);
        let source_with_present_discard = tuple_shape(&mut world, &[scalar, source_inner]);
        let required_absent_destination = tuple_shape(&mut world, &[scalar, nothing]);
        let arity_mismatch_destination = tuple_shape(&mut world, &[scalar]);
        let root = RootId::for_test(0);
        let function = FunctionId::for_test(0);
        let activation = ActivationKey::from_inputs(root, function, &[], world.types_mut());
        let key = ExecutableKey {
            activation,
            need: ExecutableNeed::Value,
        };
        let executable = test_executable(key.clone(), int, nothing);
        let program = empty_backend_program();
        let telemetry = NullTelemetry;
        let mut lowerer = NativeLowerer::new(&mut world, &telemetry, root, &program).expect("test native lowerer");
        let mut ctx = NativeFnCtx::new(
            FnId(0),
            "tuple_reprojection",
            FnCategory::User,
            NativeBodyOrigin::Executable(key),
            NativeEntryAbi::Direct,
            Vec::new(),
            int,
            vec![AbiValueRepr::ValueRef],
            None,
            EffectSummary::default(),
        );
        let params = ctx.entry_params(&[int, int, int]);
        let value = NativeBoundValue::Transport {
            shape: source,
            lanes: params.clone(),
        };
        let encoded = encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, destination)
            .expect("the destination erases the absent field before encoding the required inner tuple");

        assert_eq!(encoded.len(), 1);

        let selectively_encoded = encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, selective_destination)
            .expect("a second consumer should independently select one nested source field");
        assert_eq!(selectively_encoded, vec![params[1]]);

        let (present_tag, _) = ctx.emit_let(Prim::Const(Const::Int(99)));
        let value_with_present_discard = NativeBoundValue::Transport {
            shape: source_with_present_discard,
            lanes: std::iter::once(present_tag).chain(params.iter().copied()).collect(),
        };
        let present_discarded = encode_for_layout(
            &mut lowerer,
            &mut ctx,
            &executable,
            &value_with_present_discard,
            destination,
        )
        .expect("destination Nothing should discard a present source field");
        assert_eq!(present_discarded.len(), 1);

        let whole_carrier = encode_with_layout(
            &mut lowerer,
            &mut ctx,
            &executable,
            &value_with_present_discard,
            TransportLayout {
                structural: source_with_present_discard,
                carrier: TransportCarrier::ValueRef(outer_tuple_lane),
            },
        )
        .expect("a whole tuple should satisfy an outer ValueRef carrier");
        assert_eq!(whole_carrier.len(), 1);
        assert!(
            encode_with_layout(
                &mut lowerer,
                &mut ctx,
                &executable,
                &value,
                TransportLayout {
                    structural: destination,
                    carrier: TransportCarrier::ValueRef(outer_tuple_lane),
                },
            )
            .is_err(),
            "same-arity reprojection must not bypass an outer ValueRef obligation",
        );

        assert!(
            encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, required_absent_destination,).is_err(),
            "a required destination field cannot be invented from an absent source field",
        );
        assert!(
            encode_for_layout(&mut lowerer, &mut ctx, &executable, &value, arity_mismatch_destination,).is_err(),
            "arity-mismatched tuples retain outer materialization behavior",
        );
        assert!(
            lowerer
                .encode_runtime_value(&mut ctx, &executable, None, &value, scalar, &mut Vec::new())
                .is_err(),
            "non-tuple destinations retain outer materialization behavior",
        );

        let mut identical = Vec::new();
        lowerer
            .encode_runtime_value(&mut ctx, &executable, None, &value, source, &mut identical)
            .expect("an identical layout keeps the direct lane-copy path");
        assert_eq!(identical, params);

        ctx.set_term(Term::Halt(encoded[0]));
        let (function, body) = ctx.finish();
        assert_eq!(body.value_types.get(&encoded[0]), Some(&inner_tuple_ty));
        assert_eq!(body.value_types.get(&present_discarded[0]), Some(&inner_tuple_ty));
        assert!(
            matches!(defining_prim(&function, encoded[0]), Some(Prim::MakeTuple(items)) if items == &params),
            "the absent-tag consumer should build only the required inner tuple",
        );
        assert!(
            matches!(defining_prim(&function, present_discarded[0]), Some(Prim::MakeTuple(items)) if items == &params),
            "the present-tag consumer should discard the tag before building the inner tuple",
        );
        assert!(
            matches!(defining_prim(&function, whole_carrier[0]), Some(Prim::MakeTuple(items)) if items.len() == 2 && items[0] == present_tag),
            "the explicit whole carrier should build one outer tuple value",
        );
        assert!(
            function
                .blocks
                .iter()
                .flat_map(|block| &block.stmts)
                .all(|statement| { !matches!(statement, crate::fz_ir::Stmt::Let(_, Prim::TupleField(_, _))) })
        );
    }
}
