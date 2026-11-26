//! Compiler2 native-handoff lowering.
//!
//! This product producer turns one closed `BackendProgram(root)` into one
//! CPS/native handoff. The result is still Compiler2-owned: direct executable
//! entries, clause helpers, continuations, settled callable-boundary facts,
//! and extern marshal facts are all derived once here instead of being
//! rediscovered by shared codegen.

use super::super::drive::emit_job_diagnostic;
use super::super::identity::{ExecutableKey, FunctionId};
use super::super::transport::TransportPosition;
use crate::compiler2::ValueMap;
use crate::literal_term::LiteralTerm;

use crate::fast_hash::{HashMap, HashSet};

use std::collections::VecDeque;
use std::rc::Rc;
use std::sync::Arc;

use crate::ast::BitType;
use crate::diag::Diagnostic;
use crate::diag::codes;
use crate::dispatch_matrix::joins::{ArrivalState, DispatchJoins, DispatchLeaf};
use crate::dispatch_matrix::pattern::{
    FieldTerm, GuardExtern, LastResort, PatternDispatchPlan, PatternGuardBinOp, PatternGuardExpr, PatternGuardUnaryOp,
    RaisedField, ReasonTerm, guard_body_subjects,
};
use crate::dispatch_matrix::{ComparisonValue, DispatchNode, GraphNodeId, ListRegion, Region, SubjectId};
use crate::fz_ir::{
    BinOp as IrBinOp, BitMatchField, BitSizeIr, BlockId, BranchOrigin, CallsiteIdent, Const, Cont, DestMapSeed,
    DirectCallTarget, ExternAbi, ExternArg, ExternDecl, ExternId, ExternMarshalSite, ExternReturn, ExternTy,
    FieldSizeIr, FnBuilder, FnCategory, FnId, ModuleAtoms, ModuleBuilder, Prim, ReceiveAfter, ReceiveClause, SlotStore,
    Term, UnOp as IrUnOp, Var,
};
use crate::ground_value::GroundValue;
use crate::runtime_type_predicate::{CallableShape, RuntimeTypePredicate, TuplePositions};
use crate::source::Span;
use crate::telemetry::TelemetryExt as _;
use fz_runtime::any_value::ValueKind;
use fz_runtime::module_name::STRUCT_MODULE_FIELD;

use super::super::artifact::{
    AbiValueRepr, BackendBody, BackendClause, BackendEntry, BackendEntryCapture, BackendEntryOrigin, BackendExecutable,
    BackendProgram, BackendReturnFlow, BackendStep, BackendTail, BackendValueLayout, CallEdge, CallTarget,
    ClosureCallEdge, DispatchCallEdge, EffectSummary, EntryTransfer, NativeBody, NativeBodyOrigin,
    NativeCallableBoundary, NativeCallableBoundaryId, NativeConstructionMember, NativeEntryAbi, NativeExecutableEntry,
    NativeProgram,
};
use super::super::body::{ControlDestination, ControlEntryId, DispatchBindings, LoweredExtern, ValueId};
use super::super::dispatch_reachability::project_subject;
use super::super::identity::RootId;
use super::super::pull::{ProductKey, ProductReadContext, ProductValue, PullOutcome};
use super::super::semantic::{RuntimeDemand, ShapeDemand, UndefinedFunction};
use super::super::transport::{BoundValue, CallableId, ShapeDescr, ShapeId, TransportLayout};
use super::super::types::{ClosureTarget, Ty, Types};
use super::super::world::World;
use super::frame_free::{self, FrameFree};
use fz_engine::FatalError;

pub(crate) fn produce_native_program(
    world: &mut World,
    telemetry: &impl crate::telemetry::Telemetry,
    context: &mut ProductReadContext<'_>,
    root_id: RootId,
) -> PullOutcome {
    let backend_key = ProductKey::RootBackendProduct(root_id);
    let backend = match context.read_product(telemetry, &backend_key, world.types()) {
        Some(ProductValue::RootBackendProduct(backend)) => Rc::clone(backend),
        Some(value) => panic!("root backend content produced unexpected value {value:?}"),
        None => return PullOutcome::wait_on_product(backend_key),
    };
    match NativeLowerer::new(world, telemetry, root_id, &backend).and_then(NativeLowerer::lower) {
        Ok(program) => {
            emit_list_retention(telemetry, &root_id, &backend);
            PullOutcome::Produced(ProductValue::NativeProgram(Rc::new(program)))
        }
        Err(_) => PullOutcome::Failed,
    }
}

fn emit_list_retention(tel: &impl crate::telemetry::Telemetry, root: &RootId, program: &BackendProgram) {
    tel.raw_event2(&["fz", "compiler2", "native_program", "list_retention"], root, program);
}

/// What an entry dispatch does with the clause an outcome selects.
type EnterClause<'e, 'a, 'tel, T> = dyn FnMut(&mut NativeLowerer<'a, 'tel, T>, &mut NativeFnCtx, usize, &mut DispatchState) -> Result<(), FatalError>
    + 'e;

struct NativeLowerer<'a, 'tel, T: crate::telemetry::Telemetry> {
    world: &'a mut World,
    telemetry: &'tel T,
    root_id: RootId,
    program: &'a BackendProgram,
    module: ModuleBuilder,
    atoms: ModuleAtoms,
    executable_fns: Vec<FnId>,
    /// Which executables a call calls as machine functions.
    frame_free: FrameFree,
    /// The machine function of each frame-free executable that has a body of
    /// clauses: the one place its body is lowered. The executable's own
    /// function, which a continuation reaches it by, calls it.
    machine_fns: Vec<Option<FnId>>,
    construction_identity_fns: HashMap<TransportPosition, FnId>,
    callable_boundaries: Vec<NativeCallableBoundary>,
    extern_ids: HashMap<usize, ExternId>,
    extern_marshals: HashMap<usize, Vec<ExternTy>>,
    extern_decls: Vec<ExternDecl>,
    /// The externs guards call. A guard names its extern directly, with no
    /// executable behind it, so each is declared the first time one is lowered.
    guard_extern_ids: HashMap<(ExternAbi, String), ExternId>,
    native_bodies: Vec<NativeBody>,
    return_continuation_count: u32,
}

impl<'a, 'tel, T: crate::telemetry::Telemetry> NativeLowerer<'a, 'tel, T> {
    fn new(
        world: &'a mut World,
        telemetry: &'tel T,
        root_id: RootId,
        program: &'a BackendProgram,
    ) -> Result<Self, FatalError> {
        let atoms = ModuleAtoms::from_names(program.atom_names.iter().cloned());
        let mut module = ModuleBuilder::new();
        let executable_fns = program
            .executables()
            .iter()
            .map(|_| module.fresh_fn_id())
            .collect::<Vec<_>>();
        let frame_free = FrameFree::of(program, world.types());
        let machine_fns = program
            .executables()
            .iter()
            .enumerate()
            .map(|(index, executable)| {
                (matches!(executable.body, BackendBody::Clauses { .. }) && frame_free.executable(index))
                    .then(|| module.fresh_fn_id())
            })
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
        let mut extern_ids = HashMap::default();
        let mut extern_decls = Vec::new();
        for (index, executable) in program.executables().iter().enumerate() {
            let BackendBody::Extern { signature } = &executable.body else {
                continue;
            };
            let id = ExternId(extern_decls.len() as u32);
            extern_ids.insert(index, id);
            extern_decls.push(ExternDecl {
                id,
                symbol: signature.symbol.clone(),
                params: ExternTy::wire_classes(&signature.params),
                variadic: signature.variadic,
                ret: signature.ret.clone(),
                abi: signature.abi,
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
                    // The host binds the wrapper, so the halt kind is the lane the
                    // wrapper hands back, not the lane its member returns behind it.
                    [_] => wrapper
                        .return_form
                        .return_reprs()
                        .and_then(|reprs| reprs.first().copied()),
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
                captures: wrapper
                    .captures
                    .iter()
                    .map(|capture| world.types().runtime_type_predicate(&capture.ty))
                    .collect(),
            });
            let capture_reprs = wrapper
                .captures
                .iter()
                .map(|capture| AbiValueRepr::for_ty(world, capture.ty))
                .collect();
            callable_boundaries.push(NativeCallableBoundary {
                id: NativeCallableBoundaryId(index as u32),
                denotation: wrapper.denotation,
                source_origin: std::sync::Arc::clone(&wrapper.source_origin),
                identity_fn,
                callable: wrapper.callable,
                shape,
                wrapper_fn,
                captures: wrapper.captures.clone(),
                capture_reprs,
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
            atoms,
            executable_fns,
            frame_free,
            machine_fns,
            construction_identity_fns,
            callable_boundaries,
            extern_ids,
            extern_marshals,
            extern_decls,
            guard_extern_ids: HashMap::default(),
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
                        let mut entry_fns =
                            EntryFns::for_executable(entries, clauses, |tail| self.continues_in_caller(tail));
                        match self.machine_fns[index] {
                            Some(machine) => {
                                self.lower_machine_fn(index, machine, executable, clauses, entries, &mut entry_fns)?;
                                self.lower_machine_entry(index, machine, executable)
                            }
                            None => {
                                let name = self.executable_fn_name(index, executable);
                                let fn_id = self.executable_fns[index];
                                let direct = NativeEntryAbi::Direct;
                                self.lower_executable_head(
                                    fn_id,
                                    &name,
                                    direct,
                                    executable,
                                    clauses,
                                    entries,
                                    &mut entry_fns,
                                )?;
                                while let Some((entry, fn_id)) = entry_fns.pending.pop_front() {
                                    self.lower_entry_fn(
                                        index,
                                        executable,
                                        entries,
                                        &mut entry_fns,
                                        entry,
                                        fn_id,
                                        None,
                                    )?;
                                }
                                Ok(())
                            }
                        }
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
        module.atoms = self.atoms;
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
        let any = self.world.types_mut().any();
        for refused in super::super::native_body_frame::frame_bodies(&mut program, any) {
            self.telemetry.raw_event2(
                &["fz", "compiler2", "native_program", "frame_refused"],
                &self.root_id,
                &refused,
            );
        }
        Ok(program)
    }

    fn lower_callable_construction_wrapper(&mut self, boundary: &NativeCallableBoundary) -> Result<(), FatalError> {
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
            // A wrapper over members that all diverge never reaches a
            // return, so it declares no return lanes.
            boundary.return_form.return_reprs().unwrap_or_default().into_vec(),
            EffectSummary::default(),
        );
        let any = self.world.types_mut().any();
        let params = ctx.entry_params(
            boundary
                .captures
                .iter()
                .map(|capture| &capture.ty)
                .chain(std::iter::repeat_n(&any, boundary.call_arity)),
        );
        let (captures, args) = params.split_at(boundary.capture_reprs.len());
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
                let word_args = args.iter().copied().map(NativeBoundValue::Runtime).collect::<Vec<_>>();
                let bindings = self.lower_argument_bindings(&mut ctx, selection, &word_args)?;
                let mut state = DispatchState::new(word_args, Vec::new(), bindings);
                self.lower_dispatch_graph(
                    &mut ctx,
                    selection,
                    BranchOrigin::ClauseDispatch,
                    &mut state,
                    &mut |lowerer, ctx, leaf, _state| match leaf {
                        DispatchLeaf::Fail => {
                            ctx.set_term(Term::Unreachable);
                            Ok(())
                        }
                        DispatchLeaf::Outcome(outcome) => {
                            let body_id = selection
                                .outcome(outcome)
                                .ok_or_else(|| {
                                    incomplete_native_program(
                                        lowerer.telemetry,
                                        lowerer.root_id,
                                        format!(
                                            "callable construction {} dispatch outcome {:?} is out of bounds",
                                            boundary.id.as_u32(),
                                            outcome,
                                        ),
                                    )
                                })?
                                .body_id;
                            lowerer.lower_callable_construction_wrapper_member(
                                ctx,
                                boundary,
                                body_id as usize,
                                captures,
                                args,
                            )
                        }
                    },
                )?;
            }
            None if boundary.members.len() == 1 => {
                self.lower_callable_construction_wrapper_member(&mut ctx, boundary, 0, captures, args)?;
            }
            None if boundary.members.is_empty() => {
                ctx.set_term(Term::Unreachable);
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
        if captures.len() != boundary.captures.len() {
            return Err(FatalError);
        }
        for (capture_index, capture) in captures.iter().copied().enumerate() {
            let input = *member.capture_semantic_inputs.get(capture_index).ok_or(FatalError)?;
            if let Some(slot) = values.get_mut(input) {
                *slot = Some(NativeBoundValue::Runtime(capture));
            }
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
        let input_reprs = || {
            member
                .target_inputs
                .iter()
                .flat_map(|input| input.layout.reprs.iter().copied())
        };
        if !input_reprs().eq(target.abi.param_reprs.iter().copied()) {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} target {:?} input ABI {:?} disagrees with declared ABI {:?}",
                    boundary.id.as_u32(),
                    member.target,
                    input_reprs().collect::<Vec<_>>(),
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
                self.encode_runtime_value_for_layout(ctx, target, None, value, &input.layout, &mut target_args)?;
            }
        }
        if target_args.len() != input_reprs().count() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "callable construction {} emitted {} ABI arguments for target {:?}, which declares {}",
                    boundary.id.as_u32(),
                    target_args.len(),
                    member.target,
                    input_reprs().count(),
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
                boundary
                    .return_form
                    .return_reprs()
                    .expect("a wrapper reached through a returning member returns")
                    .into_vec()
            },
            EffectSummary::default(),
        );
        let params = ctx.entry_params(member.target_return.layout.tys.iter());
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

    /// An extern is a function with one typed clause. When the call's types
    /// leave that clause something to ask, the executable runs the entry
    /// dispatch and its one outcome tail-calls the function that makes the
    /// call; otherwise the executable is that function.
    fn lower_extern_executable(
        &mut self,
        index: usize,
        executable: &BackendExecutable,
        signature: &LoweredExtern,
    ) -> Result<(), FatalError> {
        let name = format!(
            "{}__e{}",
            self.world
                .function_ref(executable.key.activation.function)
                .display_name(),
            index
        );
        let return_reprs = executable.abi.return_layout.layout.reprs.to_vec();
        let mut ctx = NativeFnCtx::new(
            self.executable_fns[index],
            &name,
            FnCategory::Prelude,
            NativeBodyOrigin::Executable(executable.key.clone()),
            NativeEntryAbi::Direct,
            executable.abi.param_reprs.clone(),
            executable.abi.materialized.return_ty,
            return_reprs,
            executable.abi.effects,
        );
        let entry_tys = executable_input_tys(executable);
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        if let Some(result) = self.lower_extern_here(&mut ctx, index, executable, signature, &entry_vars)? {
            ctx.set_term(Term::Return(result));
        }
        self.finish_native_fn(ctx);
        Ok(())
    }

    /// Calls extern executable `index` on `entry_vars` where control is, after
    /// its dispatch when it has one, and answers the extern's result in the
    /// block where the call succeeded. A dispatch with no outcome answers
    /// nothing.
    fn lower_extern_here(
        &mut self,
        ctx: &mut NativeFnCtx,
        index: usize,
        executable: &BackendExecutable,
        signature: &LoweredExtern,
        entry_vars: &[Var],
    ) -> Result<Option<Var>, FatalError> {
        if !executable.asks_anything_of_inputs() {
            return self.emit_extern_call(ctx, index, signature, entry_vars).map(Some);
        }
        let entry_tys = executable_input_tys(executable);
        let mut call_block = None;
        self.lower_executable_entry_dispatch(ctx, executable, entry_vars, [], &mut |_, ctx, _clause, state| {
            let block = call_block
                .get_or_insert_with(|| {
                    let lanes = ctx.typed_params(entry_tys.iter());
                    (ctx.builder.block(lanes.clone()), lanes)
                })
                .0;
            ctx.set_term(Term::Goto(block, state.forwarded_args.clone()));
            Ok(())
        })?;
        let Some((block, lanes)) = call_block else {
            return Ok(None);
        };
        ctx.current_block = block;
        self.emit_extern_call(ctx, index, signature, &lanes).map(Some)
    }

    /// Calls extern executable `index` on `params`. A declared failure raises
    /// from here, so control goes on in the block where the call succeeded,
    /// and the result is the call's value.
    fn emit_extern_call(
        &mut self,
        ctx: &mut NativeFnCtx,
        index: usize,
        signature: &LoweredExtern,
        params: &[Var],
    ) -> Result<Var, FatalError> {
        let extern_args = self.extern_arguments(ctx, index, signature, params)?;
        let extern_id = *self
            .extern_ids
            .get(&index)
            .expect("extern executable should have a declared ExternId");
        let marshal_plan = self.extern_marshals.get(&index).map_or(&[][..], Vec::as_slice);
        let callsite = ctx.fresh_callsite();
        let prim = Prim::Extern(callsite, extern_id, extern_args);
        if let ExternReturn::Checked(_, failure) = &signature.ret {
            let (values, stmt_idx) = ctx.emit_let_many(2, prim);
            register_extern_marshals(ctx, stmt_idx, marshal_plan);
            let (value, failed) = (values[0], values[1]);
            let raise_b = ctx.builder.block(vec![]);
            let value_b = ctx.builder.block(vec![]);
            ctx.set_term(Term::If {
                cond: failed,
                then_b: raise_b,
                else_b: value_b,
                origin: BranchOrigin::ClauseDispatch,
            });
            ctx.current_block = raise_b;
            self.emit_raise(ctx, failure, None)?;
            ctx.current_block = value_b;
            return Ok(value);
        }
        let (value, stmt_idx) = ctx.emit_let(prim);
        register_extern_marshals(ctx, stmt_idx, marshal_plan);
        if matches!(signature.ret, ExternReturn::Scalar(ExternTy::Unit | ExternTy::Never)) {
            return Ok(ctx.emit_let(Prim::Const(Const::Nil)).0);
        }
        Ok(value)
    }

    /// The extern arguments for the lanes its executable received. A
    /// `binary_cursor` parameter is the source and position of a cursor, or a
    /// whole binary at position 0, so the binary itself is never made; every
    /// other input is its one lane, marshalled as its wire type says.
    fn extern_arguments(
        &mut self,
        ctx: &mut NativeFnCtx,
        index: usize,
        signature: &LoweredExtern,
        lanes: &[Var],
    ) -> Result<Vec<ExternArg>, FatalError> {
        let program = self.program;
        let inputs = &program.executables()[index].abi.semantic_inputs;
        let mut remaining = lanes.iter().copied();
        let mut arguments = Vec::with_capacity(inputs.len());
        for input in inputs.iter() {
            let width = input.layout.reprs.len();
            let own = remaining.by_ref().take(width).collect::<Vec<_>>();
            let wire = signature.params.get(input.semantic_index).copied();
            match (wire, own.as_slice()) {
                (Some(ExternTy::BinaryCursor), [source, position]) => {
                    arguments.push(ExternArg::fixed(*source, ExternTy::Any));
                    arguments.push(ExternArg::fixed(*position, ExternTy::I64));
                }
                (Some(ExternTy::BinaryCursor), [whole]) => {
                    let from_the_start = ctx.emit_let(Prim::Const(Const::Int(0))).0;
                    arguments.push(ExternArg::fixed(*whole, ExternTy::Any));
                    arguments.push(ExternArg::fixed(from_the_start, ExternTy::I64));
                }
                (Some(wire), [word]) => arguments.push(ExternArg::fixed(*word, wire)),
                (None, [word]) => arguments.push(ExternArg::auto(*word)),
                _ => {
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "extern `{}` argument {} arrives in {width} lanes, which its wire type does not read",
                            signature.symbol, input.semantic_index
                        ),
                    ));
                }
            }
        }
        Ok(arguments)
    }

    /// Lowers the executable's own function: its dispatch, when it has one,
    /// and each clause body the dispatch enters, as blocks of that function.
    fn lower_executable_head(
        &mut self,
        fn_id: FnId,
        name: &str,
        entry_abi: NativeEntryAbi,
        executable: &BackendExecutable,
        clauses: &[BackendClause],
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
    ) -> Result<(), FatalError> {
        let mut ctx = self.executable_ctx(fn_id, name, entry_abi, executable);
        let entry_vars = ctx.entry_params(executable_input_tys(executable).as_slice());
        self.lower_clauses_here(&mut ctx, executable, clauses, entries, &entry_vars)?;
        self.finish_entry_lowering_fn(ctx, executable, entries, entry_fns)
    }

    /// Lowers frame-free executable `index` as machine function `machine`: its
    /// dispatch and every entry its clauses reach are blocks of it, and its
    /// returns hand the result lanes to its caller in registers.
    fn lower_machine_fn(
        &mut self,
        index: usize,
        machine: FnId,
        executable: &BackendExecutable,
        clauses: &[BackendClause],
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
    ) -> Result<(), FatalError> {
        let name = format!("{}__machine", self.executable_fn_name(index, executable));
        self.lower_executable_head(
            machine,
            &name,
            NativeEntryAbi::Machine,
            executable,
            clauses,
            entries,
            entry_fns,
        )?;
        assert!(
            entry_fns.ids.is_empty(),
            "a frame-free executable {:?} reached an entry that needs a function of its own",
            executable.key
        );
        Ok(())
    }

    /// Lowers the function a continuation reaches frame-free executable
    /// `index` by: it calls `machine` and returns what it returns.
    fn lower_machine_entry(
        &mut self,
        index: usize,
        machine: FnId,
        executable: &BackendExecutable,
    ) -> Result<(), FatalError> {
        let name = self.executable_fn_name(index, executable);
        let mut ctx = self.executable_ctx(self.executable_fns[index], &name, NativeEntryAbi::Direct, executable);
        let entry_vars = ctx.entry_params(executable_input_tys(executable).as_slice());
        let lanes = ctx.emit_machine_call(machine, entry_vars, &executable.abi.return_layout.layout.tys);
        ctx.set_term(Term::ReturnLanes(lanes));
        self.finish_native_fn(ctx);
        Ok(())
    }

    fn executable_fn_name(&self, index: usize, executable: &BackendExecutable) -> String {
        format!(
            "{}__e{}",
            self.world
                .function_ref(executable.key.activation.function)
                .display_name(),
            index
        )
    }

    /// The context for lowering a function that runs `executable`'s body.
    fn executable_ctx(
        &self,
        fn_id: FnId,
        name: &str,
        entry_abi: NativeEntryAbi,
        executable: &BackendExecutable,
    ) -> NativeFnCtx {
        NativeFnCtx::new(
            fn_id,
            name,
            FnCategory::User,
            NativeBodyOrigin::Executable(executable.key.clone()),
            entry_abi,
            executable.abi.param_reprs.clone(),
            executable.abi.materialized.return_ty,
            executable.abi.return_layout.layout.reprs.to_vec(),
            executable.abi.effects,
        )
    }

    /// Lowers an executable's entry dispatch where control is: each clause it
    /// selects is entered as a block, handed the values the dispatch read.
    fn lower_clauses_here(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        clauses: &[BackendClause],
        entries: &[BackendEntry],
        entry_vars: &[Var],
    ) -> Result<(), FatalError> {
        if executable.abi.materialized.entry_dispatch.is_none() {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "backend executable {:?} has {} clauses but no settled entry dispatch",
                    executable.key,
                    clauses.len()
                ),
            ));
        }
        let handed = clauses
            .iter()
            .flat_map(|clause| clause.arguments.iter().map(|argument| argument.subject));
        self.lower_executable_entry_dispatch(
            ctx,
            executable,
            entry_vars,
            handed,
            &mut |lowerer, ctx, clause, state| lowerer.enter_clause(ctx, executable, entries, &clauses[clause], state),
        )
    }

    /// Emits the executable's entry dispatch into `ctx`: each outcome is
    /// handed to `enter_clause` with the clause it selects, and a miss raises
    /// the plan's arm of last resort.
    fn lower_executable_entry_dispatch(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entry_vars: &[Var],
        handed: impl IntoIterator<Item = SubjectId>,
        enter_clause: &mut EnterClause<'_, 'a, 'tel, T>,
    ) -> Result<(), FatalError> {
        let semantic_inputs = self.bind_executable_inputs(executable, entry_vars)?;
        let dispatch = executable
            .abi
            .materialized
            .entry_dispatch
            .as_ref()
            .expect("clause dispatch lowering requires a settled entry dispatch");
        let inputs = semantic_inputs
            .into_iter()
            .enumerate()
            .map(
                |(semantic_index, value)| match (dispatch.plan().required_input(semantic_index), value) {
                    // Dispatch reads an input in whatever form it arrived in: a
                    // tuple delivered as lanes is questioned lane-wise. An
                    // input nothing reads was never delivered.
                    (_, Some(value)) => Ok(value),
                    (true, None) => Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "native clause dispatch required omitted semantic input {} for executable {}",
                            semantic_index,
                            executable.key.activation.function.as_u32(),
                        ),
                    )),
                    (false, None) => Ok(NativeBoundValue::Absent),
                },
            )
            .collect::<Result<Vec<_>, _>>()?;
        let bindings = self.lower_argument_bindings(ctx, dispatch.plan(), &inputs)?;
        let roots = executable.key.activation.inputs(self.world.types()).to_vec();
        let mut state = DispatchState::new(inputs, entry_vars.to_vec(), bindings)
            .proven(roots)
            .reading(handed);
        self.lower_dispatch_graph(
            ctx,
            dispatch.plan(),
            BranchOrigin::ClauseDispatch,
            &mut state,
            &mut |lowerer, ctx, leaf, state| match leaf {
                DispatchLeaf::Fail => lowerer.raise_last_resort(ctx, dispatch.plan(), state),
                DispatchLeaf::Outcome(outcome) => {
                    let Some(clause_index) = dispatch.clause_index(outcome) else {
                        ctx.set_term(Term::Unreachable);
                        return Ok(());
                    };
                    enter_clause(lowerer, ctx, clause_index, state)
                }
            },
        )
    }

    /// Enters the block of the clause an outcome selected. The block receives
    /// the executable's input lanes, and after them the value of each subject
    /// its arguments name in the layout its parameter arrives in, exactly as a
    /// `case` arm is handed its subjects.
    fn enter_clause(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        clause: &BackendClause,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        let entry = &entries[clause.entry.as_u32() as usize];
        self.check_outcome_arguments_follow_parameters(entry, &clause.arguments)?;
        let plan = executable
            .abi
            .materialized
            .entry_dispatch
            .as_ref()
            .expect("a clause is entered by the entry dispatch")
            .plan();
        let mut args = state.forwarded_args.clone();
        args.extend(self.encode_outcome_arguments(ctx, executable, plan, state, &clause.arguments)?);
        let mut tys = executable_input_tys(executable);
        tys.extend(self.entry_signature(executable, entry).0);
        let block = ctx.entry_block(clause.entry, &tys);
        ctx.set_term(Term::Goto(block, args));
        Ok(())
    }

    /// Lowers a clause body where control already is: its parameters are the
    /// executable's inputs, and the arguments its entry dispatch handed
    /// follow them.
    fn lower_clause_body_here(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        clause: &BackendClause,
        entry_vars: &[Var],
    ) -> Result<(), FatalError> {
        let (input_vars, argument_vars) = entry_vars.split_at(executable_input_tys(executable).len());
        let mut env = ValueEnv::default();
        let semantic_inputs = self.bind_executable_inputs(executable, input_vars)?;
        for (value, bound) in clause.params.iter().copied().zip(semantic_inputs) {
            if let Some(bound) = bound {
                bind_local_value(ctx, executable, &mut env, value, bound);
            }
        }
        self.lower_entry_here(ctx, executable, entries, entry_fns, clause.entry, argument_vars, env)?;
        Ok(())
    }

    /// Finishes a function that lowers entries: every entry and clause body it
    /// reached as a block is lowered into it first.
    fn finish_entry_lowering_fn(
        &mut self,
        mut ctx: NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
    ) -> Result<(), FatalError> {
        self.lower_entry_blocks(&mut ctx, executable, entries, entry_fns)?;
        self.finish_native_fn(ctx);
        Ok(())
    }

    /// Lowers every entry and clause body of `executable` that control has
    /// reached as a block of this function and that is not lowered yet.
    fn lower_entry_blocks(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
    ) -> Result<(), FatalError> {
        while let Some((entry_id, block, entry_vars)) = ctx.pending_entries.pop_front() {
            ctx.current_block = block;
            match clause_entered_at(executable, entry_id) {
                Some(clause) => {
                    self.lower_clause_body_here(ctx, executable, entries, entry_fns, clause, &entry_vars)?
                }
                None => {
                    self.lower_entry_here(
                        ctx,
                        executable,
                        entries,
                        entry_fns,
                        entry_id,
                        &entry_vars,
                        ValueEnv::default(),
                    )?;
                }
            }
        }
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
        outcome: Option<&super::super::body::OutcomeEdge>,
    ) -> Result<Vec<(SubjectId, Var)>, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let base_name = format!(
            "{}__e{}",
            self.world
                .function_ref(executable.key.activation.function)
                .display_name(),
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
            BackendEntryOrigin::Handler => (
                format!("{base_name}__handler_{}", entry_id.as_u32()),
                FnCategory::CpsCont,
            ),
            BackendEntryOrigin::DeliveredResume { .. } => (
                format!("{base_name}__resume_{}", entry_id.as_u32()),
                FnCategory::CpsCont,
            ),
        };
        let (entry_tys, param_reprs, entry_abi) = self.entry_signature(executable, entry);
        let return_reprs = executable.abi.return_layout.layout.reprs.to_vec();
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
            executable.abi.effects,
        );
        let entry_vars = ctx.entry_params(entry_tys.as_slice());
        let arguments = self.receive_clause_arguments(executable, entry, outcome, &entry_vars)?;
        let input_lanes = self.lower_entry_here(
            &mut ctx,
            executable,
            entries,
            entry_fns,
            entry_id,
            &entry_vars,
            ValueEnv::default(),
        )?;
        self.mark_entry_function_params(&mut ctx, executable, entry, &entry_vars, input_lanes)?;
        self.finish_entry_lowering_fn(ctx, executable, entries, entry_fns)?;
        Ok(arguments)
    }

    /// The subject each receive outcome argument binds, with the lane that
    /// carries it. The matcher fills one lane per subject, so each argument's
    /// parameter must have a one-lane layout.
    fn receive_clause_arguments(
        &mut self,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        outcome: Option<&super::super::body::OutcomeEdge>,
        entry_vars: &[Var],
    ) -> Result<Vec<(SubjectId, Var)>, FatalError> {
        let Some(edge) = outcome else {
            return Ok(Vec::new());
        };
        self.check_outcome_arguments_follow_parameters(entry, &edge.arguments)?;
        let mut lane_index = 0;
        let mut arguments = Vec::with_capacity(edge.arguments.len());
        for argument in &edge.arguments {
            let lanes = entry_param_layout(executable, argument.parameter).reprs.len();
            if lanes != 1 {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "receive outcome parameter {:?} travels in {lanes} lanes; the matcher fills one",
                        argument.parameter
                    ),
                ));
            }
            arguments.push((argument.subject, entry_vars[lane_index]));
            lane_index += lanes;
        }
        Ok(arguments)
    }

    /// An outcome hands its arguments in the order the target entry's
    /// parameters are laid out, so the lanes it passes line up with the lanes
    /// the entry reads.
    /// The lanes an outcome hands its target entry: each argument's subject
    /// in the layout its parameter declares. A parameter of no lanes is handed
    /// nothing, so its subject is never read.
    fn encode_outcome_arguments(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        arguments: &[super::super::body::OutcomeArgument],
    ) -> Result<Vec<Var>, FatalError> {
        let mut args = Vec::new();
        for argument in arguments {
            let layout = entry_param_layout(executable, argument.parameter);
            if self.world.layout_width(TransportLayout {
                structural: layout.structural,
                carrier: layout.carrier,
            }) == 0
            {
                continue;
            }
            let subject = self.dispatch_subject_value(ctx, plan, state, argument.subject)?.clone();
            self.encode_runtime_value_for_layout(
                ctx,
                executable,
                Some(argument.parameter),
                &subject,
                layout,
                &mut args,
            )?;
        }
        Ok(args)
    }

    fn check_outcome_arguments_follow_parameters(
        &self,
        entry: &BackendEntry,
        arguments: &[super::super::body::OutcomeArgument],
    ) -> Result<(), FatalError> {
        let in_order = arguments
            .iter()
            .map(|argument| argument.parameter)
            .eq(entry.params.iter().copied());
        if in_order {
            return Ok(());
        }
        Err(incomplete_native_program(
            self.telemetry,
            self.root_id,
            format!(
                "outcome arguments {:?} are not the parameters {:?} of the entry they target, in order",
                arguments.iter().map(|argument| argument.parameter).collect::<Vec<_>>(),
                entry.params
            ),
        ))
    }

    /// Lowers an entry where control already is: binds what it is entered
    /// with, then its steps and tail. Answers how many of `entry_vars` carry
    /// the entry's input.
    #[allow(clippy::too_many_arguments)]
    fn lower_entry_here(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        entry_id: ControlEntryId,
        entry_vars: &[Var],
        mut env: ValueEnv,
    ) -> Result<usize, FatalError> {
        let entry = &entries[entry_id.as_u32() as usize];
        let input_lanes = self.bind_entry_input(ctx, executable, entry, entry_vars, &mut env)?;
        let mut capture_offset = input_lanes;
        self.bind_entry_captures(ctx, executable, entry, entry_vars, &mut capture_offset, &mut env)?;
        self.lower_entry_steps(ctx, executable, &mut env, &entry.steps)?;
        self.lower_entry_tail(ctx, executable, entries, entry_fns, &env, &entry.tail)?;
        Ok(input_lanes)
    }

    /// Hands control to an entry: a block of this function when only this
    /// function's direct transfers reach it, otherwise a tail call to its own
    /// function.
    fn transfer_to_entry(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        entry_id: ControlEntryId,
        args: Vec<Var>,
    ) {
        let term = if entry_fns.is_block(entry_id) {
            let entry = &entries[entry_id.as_u32() as usize];
            let (entry_tys, _, _) = self.entry_signature(executable, entry);
            Term::Goto(ctx.entry_block(entry_id, &entry_tys), args)
        } else {
            Term::TailCall {
                ident: CallsiteIdent::from_source(Span::DUMMY),
                callee: DirectCallTarget::Local(entry_fns.reference(&mut self.module, entry_id)),
                args,
                is_back_edge: false,
            }
        };
        ctx.set_term(term);
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
                    let layout = executable.abi.value_layouts.get(value).map(|layout| TransportLayout {
                        structural: layout.structural,
                        carrier: layout.carrier,
                    });
                    let bound = self.literal_bound(ctx, executable, literal, layout)?;
                    bind_local_value(ctx, executable, env, *value, bound);
                }
                BackendStep::Tuple { value, items } => {
                    share_native_values(
                        ctx,
                        env,
                        items
                            .iter()
                            .filter(|item| item.mode == crate::fz_ir::OwnershipMode::Share)
                            .map(|item| item.value),
                    );
                    let item_values = || items.iter().map(|item| item.value);
                    if let Some(layout) = executable.abi.value_layouts.get(value)
                        && let shape = layout.structural
                        && self.world.tuple_arity(shape).is_some()
                    {
                        if self.world.tuple_arity(shape) != Some(items.len()) {
                            return Err(FatalError);
                        }
                        if matches!(layout.carrier, super::super::pull::TransportCarrier::ValueRef(_)) {
                            let vars = self.env_runtime_vars(ctx, executable, env, item_values());
                            let (var, _) = ctx.emit_let(Prim::MakeTuple(vars));
                            self.bind_runtime_value(ctx, executable, env, *value, var);
                        } else {
                            let mut lanes = Vec::new();
                            for (index, item) in item_values().enumerate() {
                                let field_layout = self.field_layout(shape, index);
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
                        let fields = self.env_runtime_vars(ctx, executable, env, item_values());
                        let (var, _) = ctx.emit_let(Prim::MakeTuple(fields));
                        self.bind_runtime_value(ctx, executable, env, *value, var);
                    }
                }
                BackendStep::List {
                    value,
                    items,
                    tail,
                    retention,
                } => {
                    let vars = self.env_runtime_vars(ctx, executable, env, items.iter().copied());
                    let tail = self.list_tail_runtime_var(ctx, executable, env, *tail)?;
                    let retention = retention.map(|retention| crate::fz_ir::ListRetention {
                        source: self.env_runtime_var(ctx, executable, env, retention.source),
                        permission: retention.permission,
                    });
                    let (var, _) = ctx.emit_let(Prim::MakeList(vars, tail, retention));
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::Map {
                    value,
                    entries,
                    in_key_order,
                } => {
                    let (mut map, _) = ctx.emit_let(Prim::DestMapBegin(DestMapSeed::Capacity(entries.len())));
                    for (key, item) in entries {
                        let key = self.env_runtime_var(ctx, executable, env, *key);
                        let value = self.env_runtime_var(ctx, executable, env, *item);
                        map = ctx.emit_map_put(map, key, value);
                    }
                    let (var, _) = ctx.emit_let(if *in_key_order {
                        Prim::DestMapPublish(map)
                    } else {
                        Prim::DestMapFreeze(map)
                    });
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::MapUpdate {
                    value,
                    ok,
                    base,
                    entries,
                } => {
                    let base = self.env_runtime_var(ctx, executable, env, *base);
                    let (mut map, _) = ctx.emit_let(Prim::DestMapBegin(DestMapSeed::Update(base)));
                    for (key, item) in entries {
                        let key = self.env_runtime_var(ctx, executable, env, *key);
                        let value = self.env_runtime_var(ctx, executable, env, *item);
                        map = ctx.emit_map_put(map, key, value);
                    }
                    let (var, _) = ctx.emit_let(Prim::DestMapFreeze(map));
                    let (missed, _) = ctx.emit_let(Prim::IsMapMiss(var));
                    let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
                    let (ok_var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, missed, false_v));
                    self.bind_runtime_value(ctx, executable, env, *ok, ok_var);
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::StructUpdate {
                    value,
                    ok,
                    base,
                    module,
                    arity,
                    stores,
                    rewrite,
                } => {
                    let base = self.env_runtime_var(ctx, executable, env, *base);
                    let stores = stores
                        .iter()
                        .map(|store| SlotStore {
                            slot: store.slot,
                            key: self.env_runtime_var(ctx, executable, env, store.key),
                            value: self.env_runtime_var(ctx, executable, env, store.value),
                        })
                        .collect();
                    let (var, _) = ctx.emit_let(Prim::StructWith {
                        base,
                        module: module.clone(),
                        arity: *arity,
                        stores,
                        rewrite: *rewrite,
                    });
                    let (ok_var, _) = ctx.emit_let(Prim::Const(Const::True));
                    self.bind_runtime_value(ctx, executable, env, *ok, ok_var);
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
                            literal: field.literal.clone(),
                            value: self.env_runtime_var(ctx, executable, env, field.value),
                            ty: field.spec.ty,
                            size: lower_field_size_ir(&field.spec.size, env)?,
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
                    // (`step_or_omitted_when_absent`), so every surviving
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
                    share_native_values(ctx, env, captures.iter().copied());
                    // As with `FunctionRef`, a settled-`Nothing` closure is omitted
                    // by backend lowering, so every surviving `Lambda` really is
                    // constructed and its captures really are demanded.
                    let shape = value_shape(executable, *value);
                    let callable_boundary = construction
                        .as_ref()
                        .map(|identity| self.native_callable_boundary_for_construction(identity))
                        .transpose()?;
                    if let Some(boundary) = callable_boundary {
                        if self.callable_boundaries[boundary.as_u32() as usize].captures.len() != captures.len() {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                "native callable construction capture inventory disagrees with its lambda producer",
                            ));
                        }
                        let mut capture_values = Vec::with_capacity(captures.len());
                        for (index, capture) in captures.iter().copied().enumerate() {
                            let ty = self.callable_boundaries[boundary.as_u32() as usize].captures[index].ty;
                            let local = env_local_value(env, capture)?;
                            capture_values.push(self.materialize_native_value(ctx, Some(ty), local)?);
                        }
                        let var = self.emit_callable_construction(ctx, boundary, capture_values);
                        self.bind_runtime_value(ctx, executable, env, *value, var);
                    } else {
                        let callable = callable_id_for_shape(self.world, shape)?;
                        if self.world.callable(callable).capture_layouts.len() != captures.len() {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                "native direct callable capture count did not match transport callable descriptor",
                            ));
                        }
                        let mut capture_lanes = Vec::new();
                        for (index, capture) in captures.iter().copied().enumerate() {
                            let layout = self.field_layout(shape, index);
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
                    let prim = if field == STRUCT_MODULE_FIELD {
                        Prim::StructModule(base)
                    } else {
                        Prim::StructField(base, field.clone())
                    };
                    let (var, _) = ctx.emit_let(prim);
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::StructSlot {
                    value,
                    base,
                    module,
                    slot,
                    field,
                } => {
                    let base = self.env_runtime_var(ctx, executable, env, *base);
                    let (var, _) = ctx.emit_let(Prim::StructSlot {
                        base,
                        module: module.clone(),
                        slot: *slot,
                        field: field.clone(),
                    });
                    self.bind_runtime_value(ctx, executable, env, *value, var);
                }
                BackendStep::PopHandler => {
                    ctx.emit_let(Prim::PopHandler);
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
        if let BackendTail::DirectCall { args, .. } | BackendTail::ClosureCall { args, .. } = tail {
            share_native_values(
                ctx,
                env,
                args.iter()
                    .filter(|arg| arg.ownership == crate::fz_ir::OwnershipMode::Share)
                    .map(|arg| arg.value),
            );
        }
        match tail {
            BackendTail::Value { value, dest } => {
                self.lower_value_destination(ctx, executable, entries, entry_fns, env, *value, dest)
            }
            BackendTail::DirectCall {
                target,
                selector,
                args,
                dest,
                ..
            } => match target {
                CallEdge::Direct(direct) => self.lower_direct_call_tail(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    &direct.callee,
                    *selector,
                    args,
                    dest,
                    &direct.return_flow,
                    self.call_continues_here(ctx, target, dest),
                ),
                CallEdge::Dispatch(dispatch) => self.lower_dispatch_call_tail(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    dispatch,
                    *selector,
                    args,
                    dest,
                    self.call_continues_here(ctx, target, dest),
                ),
                CallEdge::Indirect { .. } => Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "native direct call materialized as an indirect closure edge; Indirect is closure-call-only",
                )),
            },
            BackendTail::ClosureCall {
                callee,
                edge,
                args,
                dest,
                return_flow,
                ..
            } => {
                let callee_value = env.value(*callee);
                // The recorded call form carries the decision the artifact
                // layer made. Native emits what that answer promised; it does
                // not re-decide, and it does not re-derive where the target's
                // captures end.
                let direct_call = match edge {
                    ClosureCallEdge::Direct { target, capture_count } => {
                        let capture_inputs_end = *capture_count;
                        let capture_lanes = self.direct_closure_capture_lanes(
                            ctx,
                            executable,
                            *callee,
                            callee_value,
                            target,
                            capture_inputs_end,
                        )?;
                        let target = self
                            .program
                            .executable_index(target, self.world.types())
                            .ok_or(FatalError)?;
                        let callee_executable = &self.program.executables()[target];
                        let mut call_args = capture_lanes;
                        let target_inputs = callee_executable.key.activation.input_len(self.world.types());
                        if target_inputs != capture_inputs_end + args.len() {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                format!(
                                    "native direct closure call owner={:?} target={:?} takes {target_inputs} input(s), but the call form names {capture_inputs_end} capture(s) and passes {} argument(s)",
                                    executable.key,
                                    callee_executable.key,
                                    args.len(),
                                ),
                            ));
                        }
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
                                    local,
                                    &target_input.layout,
                                    &mut call_args,
                                )?;
                            } else {
                                self.encode_runtime_value(
                                    ctx,
                                    callee_executable,
                                    Some(arg.value),
                                    local,
                                    target_input.layout.structural,
                                    &mut call_args,
                                )?;
                            }
                        }
                        if call_args.len() != callee_executable.abi.param_reprs.len() {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                format!(
                                    "native direct closure call owner={:?} target={:?} encoded {} argument lane(s) for {} parameter(s)",
                                    executable.key,
                                    callee_executable.key,
                                    call_args.len(),
                                    callee_executable.abi.param_reprs.len(),
                                ),
                            ));
                        }
                        if !return_flow.as_ref().is_some_and(|flow| match flow {
                            BackendReturnFlow::NoReturn | BackendReturnFlow::Tail => true,
                            BackendReturnFlow::Continue { source } | BackendReturnFlow::Deliver { source, .. } => {
                                source.as_ref() == &callee_executable.abi.return_layout
                            }
                        }) {
                            return Err(incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                format!(
                                    "native direct closure call owner={:?} target={:?} reads a return flow {:?} the target does not publish",
                                    executable.key, callee_executable.key, return_flow,
                                ),
                            ));
                        }
                        Some((target, call_args))
                    }
                    // A seam call goes through the callee value's own boundary,
                    // and a dead call reaches nothing: both lower to the
                    // indirect term below, whose return flow says which.
                    ClosureCallEdge::Seam | ClosureCallEdge::Dead => None,
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
                    let callee_value = callee_value.ok_or_else(|| {
                        incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            "native indirect closure call has no runtime callee value",
                        )
                    })?;
                    let closure = self.materialize_native_value(ctx, None, callee_value)?;
                    let call_args = self.env_runtime_vars(ctx, executable, env, args.iter().map(|arg| arg.value));
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
                self.transfer_to_entry(ctx, executable, entries, entry_fns, *then_entry, then_args);
                ctx.current_block = else_b;
                let else_args = self.entry_capture_args(ctx, executable, entries, *else_entry, env)?;
                self.transfer_to_entry(ctx, executable, entries, entry_fns, *else_entry, else_args);
                Ok(())
            }
            BackendTail::Dispatch {
                inputs,
                bindings,
                dispatch,
            } => {
                // A decision reads an input in whatever form it is bound in: a
                // tuple held as lanes is questioned lane-wise, and an input it
                // never reads was never bound.
                let input_values = inputs
                    .iter()
                    .map(|input| env.value(*input).cloned().unwrap_or(NativeBoundValue::Absent))
                    .collect();
                let pinned_vars = self.env_runtime_vars(ctx, executable, env, bindings.pinned.iter().copied());
                let prepared = self.env_runtime_vars(ctx, executable, env, bindings.prepared.iter().copied());
                let mut state = DispatchState::new(
                    input_values,
                    Vec::new(),
                    DispatchBindings {
                        pinned: pinned_vars,
                        prepared,
                    },
                )
                .proven(
                    inputs
                        .iter()
                        .map(|input| {
                            let proven = executable.abi.materialized.value_types.get(input).copied();
                            proven.unwrap_or_else(|| self.world.types_mut().any())
                        })
                        .collect(),
                )
                .reading(dispatch.argument_subjects());
                self.lower_dispatch_graph(
                    ctx,
                    &dispatch.plan,
                    BranchOrigin::User,
                    &mut state,
                    &mut |lowerer, ctx, leaf, state| {
                        lowerer.lower_control_dispatch_leaf(
                            ctx,
                            executable,
                            entries,
                            entry_fns,
                            env,
                            &dispatch.plan,
                            &dispatch.outcomes,
                            dispatch.miss_entry,
                            leaf,
                            state,
                        )
                    },
                )
            }
            BackendTail::Try { body, handler } => {
                let executable_index = self
                    .program
                    .executable_index(&executable.key, self.world.types())
                    .expect("owning executable");
                let handler_fn = self.module.fresh_fn_id();
                assert!(
                    entry_fns.ids.insert(*handler, handler_fn).is_none(),
                    "one try owns its handler entry"
                );
                self.lower_entry_fn(
                    executable_index,
                    executable,
                    entries,
                    entry_fns,
                    *handler,
                    handler_fn,
                    None,
                )?;
                let captures = self.entry_capture_args(ctx, executable, entries, *handler, env)?;
                let body_block = ctx.builder.block(vec![]);
                ctx.set_term(Term::Try {
                    handler: handler_fn,
                    captures,
                    body: body_block,
                });
                ctx.current_block = body_block;
                let body_args = self.entry_capture_args(ctx, executable, entries, *body, env)?;
                self.transfer_to_entry(ctx, executable, entries, entry_fns, *body, body_args);
                Ok(())
            }
            BackendTail::Receive(receive) => {
                let bindings = &receive.bindings;
                let dispatch = &receive.dispatch;
                let outcomes = &receive.outcomes;
                let after = receive.after.as_ref();
                let captures = self.receive_capture_vars(ctx, executable, entries, outcomes, after, env)?;
                let executable_index = self
                    .program
                    .executable_index(&executable.key, self.world.types())
                    .expect("owning executable");
                let clauses = outcomes
                    .iter()
                    .map(|edge| {
                        let body = self.module.fresh_fn_id();
                        assert!(
                            entry_fns.ids.insert(edge.target, body).is_none(),
                            "one receive outcome owns its target"
                        );
                        let arguments = self.lower_entry_fn(
                            executable_index,
                            executable,
                            entries,
                            entry_fns,
                            edge.target,
                            body,
                            Some(edge),
                        )?;
                        let span = entries[edge.target.as_u32() as usize].span;
                        Ok(ReceiveClause {
                            ident: CallsiteIdent::from_source(span),
                            arguments,
                            guard: None,
                            body,
                            span,
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
                let pinned = bindings
                    .pinned
                    .iter()
                    .chain(&bindings.prepared)
                    .map(|value| self.env_runtime_var(ctx, executable, env, *value))
                    .collect();
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
            BackendTail::Unreachable => {
                ctx.set_term(Term::Unreachable);
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
        selector: Option<ValueId>,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
        return_flow: &BackendReturnFlow,
        in_place: bool,
    ) -> Result<(), FatalError> {
        if let CallTarget::Undefined(undefined) = callee {
            return self.raise_undefined_function(ctx, executable, env, undefined, selector);
        }
        if in_place && (ctx.returns_here() || !matches!(return_flow, BackendReturnFlow::NoReturn)) {
            let CallTarget::Local(callee) = callee else {
                unreachable!("only a local callee is a machine call")
            };
            let callee = self
                .program
                .executable_index(callee, self.world.types())
                .ok_or(FatalError)?;
            return self.lower_machine_call(
                ctx,
                executable,
                entries,
                entry_fns,
                env,
                callee,
                args,
                dest,
                return_flow,
            );
        }
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

    /// Whether a tail is a call that continues in this function, so that the
    /// entry it delivers to is reached by a direct transfer.
    fn continues_in_caller(&self, tail: &BackendTail) -> bool {
        let BackendTail::DirectCall { target, dest, .. } = tail else {
            return false;
        };
        frame_free::delivered_call_continues_here(target, dest, &mut |callee| self.callee_is_frame_free(callee))
    }

    /// Whether this call is a machine call: a delivered call whose callees are
    /// all frame-free, or, inside a machine function, a tail call, whose
    /// callees are then frame-free by that function's own rule.
    fn call_continues_here(
        &self,
        ctx: &NativeFnCtx,
        target: &CallEdge<ExecutableKey, BackendReturnFlow>,
        dest: &ControlDestination,
    ) -> bool {
        let frame_free = &mut |callee: &CallTarget<ExecutableKey>| self.callee_is_frame_free(callee);
        match dest {
            ControlDestination::Deliver(_) => frame_free::delivered_call_continues_here(target, dest, frame_free),
            ControlDestination::Return if ctx.returns_here() => {
                assert!(
                    frame_free::tail_call_continues_here(target, frame_free),
                    "a body that returns here tail-calls only frame-free callees"
                );
                true
            }
            ControlDestination::Return => false,
        }
    }

    fn callee_is_frame_free(&self, callee: &CallTarget<ExecutableKey>) -> bool {
        self.frame_free.callee(self.program, self.world.types(), callee)
    }

    /// Calls frame-free executable `callee` on the call's lanes. An extern is
    /// called where control is; any other body is a machine function, called
    /// and returned from, or tail-called when the call returns the callee's
    /// value as the caller's own.
    #[allow(clippy::too_many_arguments)]
    fn lower_machine_call(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        callee: usize,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
        return_flow: &BackendReturnFlow,
    ) -> Result<(), FatalError> {
        let program = self.program;
        let callee_executable = &program.executables()[callee];
        let lanes = self.call_lanes(ctx, executable, env, callee, args)?;
        let layout = &callee_executable.abi.return_layout.layout;
        let returned = match &callee_executable.body {
            BackendBody::Extern { signature } => {
                let Some(result) = self.lower_extern_call_here(ctx, callee, callee_executable, signature, lanes)?
                else {
                    return Ok(());
                };
                if layout.reprs.is_empty() {
                    Vec::new()
                } else {
                    vec![result]
                }
            }
            BackendBody::Clauses { .. } if self.frame_free.copied_in_caller(callee) => {
                return self.lower_call_copied(ctx, executable, entries, entry_fns, env, callee, lanes, dest);
            }
            BackendBody::Clauses { .. } => {
                let machine = self.machine_fns[callee].expect("a frame-free executable of clauses has a machine fn");
                if matches!(dest, ControlDestination::Return)
                    && matches!(return_flow, BackendReturnFlow::Tail)
                    && ctx.is_machine()
                    && !ctx.returns_to_join()
                {
                    ctx.set_term(Term::TailCall {
                        ident: ctx.fresh_callsite(),
                        callee: DirectCallTarget::Local(machine),
                        args: lanes,
                        is_back_edge: false,
                    });
                    return Ok(());
                }
                ctx.emit_machine_call(machine, lanes, &layout.tys)
            }
        };
        if matches!(return_flow, BackendReturnFlow::NoReturn) {
            ctx.set_term(Term::Unreachable);
            return Ok(());
        }
        match dest {
            ControlDestination::Return => {
                ctx.return_lanes(returned);
                Ok(())
            }
            ControlDestination::Deliver(resume) => {
                self.resume_with_returned(ctx, executable, entries, entry_fns, env, *resume, layout, &returned)
            }
        }
    }

    /// Lowers frame-free executable `callee`, whose copied size is within the
    /// limit, as blocks of this function on the call's `lanes`. Its returns go
    /// where this body's own go when the call is in tail position, and
    /// otherwise meet in one block, which goes on in the entry the call
    /// delivers to.
    #[allow(clippy::too_many_arguments)]
    fn lower_call_copied(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        callee: usize,
        lanes: Vec<Var>,
        dest: &ControlDestination,
    ) -> Result<(), FatalError> {
        let program = self.program;
        let callee_executable = &program.executables()[callee];
        let BackendBody::Clauses {
            clauses,
            entries: callee_entries,
            ..
        } = &callee_executable.body
        else {
            unreachable!("only an executable of clauses is copied; an extern is called where control is")
        };
        let inputs = ctx.typed_params(executable_input_tys(callee_executable).iter());
        let head = ctx.builder.block(inputs.clone());
        ctx.set_term(Term::Goto(head, lanes));
        ctx.current_block = head;
        let layout = &callee_executable.abi.return_layout.layout;
        let returns = match dest {
            ControlDestination::Deliver(_) => Returns::to_join(&layout.tys),
            ControlDestination::Return => std::mem::take(&mut ctx.returns),
        };
        let caller_scope = ctx.enter_scope(returns);
        let mut callee_fns = EntryFns::for_executable(callee_entries, clauses, |tail| self.continues_in_caller(tail));
        self.lower_clauses_here(ctx, callee_executable, clauses, callee_entries, &inputs)?;
        self.lower_entry_blocks(ctx, callee_executable, callee_entries, &mut callee_fns)?;
        assert!(
            callee_fns.ids.is_empty(),
            "a copied executable {:?} reached an entry that needs a function of its own",
            callee_executable.key
        );
        let callee_scope = ctx.leave_scope(caller_scope);
        let ControlDestination::Deliver(resume) = dest else {
            ctx.returns = callee_scope.returns;
            return Ok(());
        };
        let Some((join, returned)) = callee_scope.returns.joined() else {
            return Ok(());
        };
        ctx.current_block = join;
        self.resume_with_returned(ctx, executable, entries, entry_fns, env, *resume, layout, &returned)
    }

    /// Calls extern executable `callee` on `lanes` where control is, and
    /// answers the lanes it returns, or nothing when no call is reached.
    fn lower_extern_call_here(
        &mut self,
        ctx: &mut NativeFnCtx,
        callee: usize,
        callee_executable: &BackendExecutable,
        signature: &LoweredExtern,
        lanes: Vec<Var>,
    ) -> Result<Option<Var>, FatalError> {
        let inputs = ctx.typed_params(executable_input_tys(callee_executable).iter());
        let head = ctx.builder.block(inputs.clone());
        ctx.set_term(Term::Goto(head, lanes));
        ctx.current_block = head;
        self.lower_extern_here(ctx, callee, callee_executable, signature, &inputs)
    }

    /// Goes on in the entry `resume` with the value a call returned in
    /// `returned`, the lanes of `layout`.
    #[allow(clippy::too_many_arguments)]
    fn resume_with_returned(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        resume: ControlEntryId,
        layout: &BackendValueLayout,
        returned: &[Var],
    ) -> Result<(), FatalError> {
        let input = entries[resume.as_u32() as usize]
            .origin
            .input_value()
            .ok_or(FatalError)?;
        let delivered = self.decode_runtime_value_for_layout(layout, returned, &mut 0)?;
        let mut resumed = env.clone();
        bind_local_value(ctx, executable, &mut resumed, input, delivered);
        let resume_args = self.entry_call_args_from_value(ctx, executable, entries, resume, &resumed, input)?;
        self.transfer_to_entry(ctx, executable, entries, entry_fns, resume, resume_args);
        Ok(())
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
        selector: Option<ValueId>,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
        in_place: bool,
    ) -> Result<(), FatalError> {
        let word_inputs = selector
            .into_iter()
            .chain(args.iter().map(|arg| arg.value))
            .enumerate()
            .map(|(index, value)| {
                NativeBoundValue::Runtime(if dispatch.plan.required_input(index) {
                    self.env_runtime_var(ctx, executable, env, value)
                } else {
                    ctx.emit_let(Prim::Const(Const::Nil)).0
                })
            })
            .collect::<Vec<_>>();
        let bindings = self.lower_argument_bindings(ctx, &dispatch.plan, &word_inputs)?;
        let mut state = DispatchState::new(word_inputs, Vec::new(), bindings);
        let origin = BranchOrigin::User;
        self.lower_dispatch_graph(
            ctx,
            &dispatch.plan,
            origin,
            &mut state,
            &mut |lowerer, ctx, leaf, state| {
                lowerer.lower_dispatch_call_leaf(
                    ctx, executable, entries, entry_fns, env, dispatch, selector, args, dest, in_place, leaf, state,
                )
            },
        )
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_dispatch_call_leaf(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        dispatch: &DispatchCallEdge<ExecutableKey, BackendReturnFlow>,
        selector: Option<ValueId>,
        args: &[super::super::artifact::BackendCallArg],
        dest: &ControlDestination,
        in_place: bool,
        leaf: DispatchLeaf,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        match leaf {
            DispatchLeaf::Fail if dispatch.plan.last_resort.is_some() => {
                self.raise_last_resort(ctx, &dispatch.plan, state)
            }
            DispatchLeaf::Fail => {
                ctx.set_term(Term::Unreachable);
                Ok(())
            }
            DispatchLeaf::Outcome(outcome) => {
                let Some(arm) = dispatch.arm(outcome) else {
                    ctx.set_term(Term::Unreachable);
                    return Ok(());
                };
                self.lower_direct_call_tail(
                    ctx,
                    executable,
                    entries,
                    entry_fns,
                    env,
                    &arm.callee,
                    selector,
                    args,
                    dest,
                    &arm.return_flow,
                    in_place,
                )
            }
        }
    }

    /// The lanes executable `callee` receives for a call's `args`, each
    /// encoded to the layout the callee declares for its input.
    fn call_lanes(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        callee: usize,
        args: &[super::super::artifact::BackendCallArg],
    ) -> Result<Vec<Var>, FatalError> {
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
                    local,
                    &target_input.layout,
                    &mut lanes,
                )?;
            } else {
                let value = self.materialize_native_value(
                    ctx,
                    executable.abi.materialized.value_types.get(&arg.value).copied(),
                    local,
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
        Ok(lanes)
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
                let lanes = self.call_lanes(ctx, executable, env, callee, args)?;
                Ok((DirectCallTarget::Local(self.executable_fns[callee]), lanes))
            }
            CallTarget::ProviderBoundary(function) => Ok((
                DirectCallTarget::ProviderBoundary(self.world.function_mfa(*function)),
                self.env_runtime_vars(ctx, executable, env, args.iter().map(|arg| arg.value)),
            )),
            CallTarget::Undefined(undefined) => Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "a call that finds no `{}/{}` raises; it has no target to pass arguments to",
                    undefined.function, undefined.arity
                ),
            )),
        }
    }

    /// Ends the block raising for a call on the module value `selector` that
    /// found no function.
    fn raise_undefined_function(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        env: &ValueEnv,
        undefined: &UndefinedFunction,
        selector: Option<ValueId>,
    ) -> Result<(), FatalError> {
        let Some(selector) = selector else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "a call that finds no `{}/{}` has no module value to show",
                    undefined.function, undefined.arity
                ),
            ));
        };
        let receiver = self.env_runtime_var(ctx, executable, env, selector);
        let mut atom = |name: &str| ctx.emit_let(Prim::Const(Const::Atom(self.atom_id(name)))).0;
        let function = atom(&undefined.function);
        let modules = undefined.modules_without.iter().map(|module| atom(module)).collect();
        let (modules_without, _) = ctx.emit_let(Prim::MakeList(modules, None, None));
        ctx.set_term(Term::RaiseUndefined {
            receiver,
            function,
            arity: undefined.arity,
            modules_without,
        });
        Ok(())
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
                ctx.return_lanes(lanes);
                Ok(())
            }
            ControlDestination::Deliver(entry_id) => {
                let args = self.entry_call_args_from_value(ctx, executable, entries, *entry_id, env, value_id)?;
                self.transfer_to_entry(ctx, executable, entries, entry_fns, *entry_id, args);
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
            .value(value_id)
            .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
        self.encode_runtime_value_for_layout(
            ctx,
            executable,
            Some(value_id),
            local,
            &executable.abi.return_layout.layout,
            &mut lanes,
        )?;
        Ok(lanes)
    }

    fn entry_signature(
        &mut self,
        executable: &BackendExecutable,
        entry: &BackendEntry,
    ) -> (Vec<Ty>, Vec<AbiValueRepr>, NativeEntryAbi) {
        match &entry.origin {
            BackendEntryOrigin::Clause
            | BackendEntryOrigin::Branch
            | BackendEntryOrigin::ReceiveOutcome
            | BackendEntryOrigin::Handler => {
                let (mut tys, mut reprs) = (Vec::new(), Vec::new());
                for value in &entry.params {
                    let layout = entry_param_layout(executable, *value);
                    tys.extend(layout.tys.iter().copied());
                    reprs.extend(layout.reprs.iter().copied());
                }
                self.append_entry_capture_lanes(executable, entry, &mut tys, &mut reprs);
                let abi = match &entry.origin {
                    BackendEntryOrigin::Clause | BackendEntryOrigin::Branch => NativeEntryAbi::Direct,
                    _ => NativeEntryAbi::Continuation { extra_params: 0 },
                };
                (tys, reprs, abi)
            }
            BackendEntryOrigin::DeliveredResume { value: _, layout } => {
                assert!(
                    entry.params.is_empty(),
                    "a resume entry is entered with its delivered value alone"
                );
                let (mut tys, mut reprs) = (layout.layout.tys.to_vec(), layout.layout.reprs.to_vec());
                let extra_params = reprs.len();
                self.append_entry_capture_lanes(executable, entry, &mut tys, &mut reprs);
                (tys, reprs, NativeEntryAbi::Continuation { extra_params })
            }
        }
    }

    /// Appends the lanes an entry receives for its captures: the lanes of each
    /// lane-form capture, then one lane per physical capture.
    fn append_entry_capture_lanes(
        &mut self,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        tys: &mut Vec<Ty>,
        reprs: &mut Vec<AbiValueRepr>,
    ) {
        for capture in &entry.captures {
            tys.extend(capture.layout.tys.iter().copied());
            reprs.extend(capture.layout.reprs.iter().copied());
        }
        for capture in &entry.physical_captures {
            let ty = executable
                .abi
                .materialized
                .value_types
                .get(capture)
                .copied()
                .unwrap_or_else(|| self.world.types_mut().any());
            tys.push(ty);
            reprs.push(AbiValueRepr::for_ty(self.world, ty));
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
            BackendEntryOrigin::Clause
            | BackendEntryOrigin::Branch
            | BackendEntryOrigin::ReceiveOutcome
            | BackendEntryOrigin::Handler => {
                let mut lane_index = 0;
                for value in entry.params.iter().copied() {
                    let layout = entry_param_layout(executable, value);
                    let bound = self.decode_runtime_value_for_layout(layout, entry_vars, &mut lane_index)?;
                    bind_local_value(ctx, executable, env, value, bound);
                }
                Ok(lane_index)
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
        for capture in entry.physical_captures.iter().copied() {
            let physical_var = *entry_vars.get(*capture_offset).ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native entry {:?} missing retained list cell capture param at offset {} of {}",
                        ctx.origin,
                        *capture_offset,
                        entry_vars.len()
                    ),
                )
            })?;
            self.bind_runtime_value(ctx, executable, env, capture, physical_var);
            *capture_offset += 1;
        }
        Ok(())
    }

    /// Records what an entry function's parameters carry beyond its source
    /// values: the physical capabilities it is handed, and which lanes of a
    /// delivered value it never reads. A block of another function has no
    /// parameters of its own to describe.
    fn mark_entry_function_params(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entry: &BackendEntry,
        entry_vars: &[Var],
        input_lanes: usize,
    ) -> Result<(), FatalError> {
        if matches!(
            entry.origin,
            BackendEntryOrigin::Branch | BackendEntryOrigin::ReceiveOutcome
        ) {
            let mut lane_index = 0;
            for value in &entry.params {
                let lanes = entry_param_layout(executable, *value).reprs.len();
                if entry.physical_params.contains(value) {
                    for var in &entry_vars[lane_index..lane_index + lanes] {
                        ctx.builder.record_physical_entry_param(*var);
                    }
                }
                lane_index += lanes;
            }
        }
        self.mark_delivered_entry_semantics(ctx, executable, entry, &entry_vars[..input_lanes])?;
        // The signature carries physical captures as its trailing parameters.
        let physical_start = entry_vars.len() - entry.physical_captures.len();
        for var in &entry_vars[physical_start..] {
            ctx.builder.record_physical_entry_param(*var);
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
        let param_tys = &source_return.layout.tys;
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
            executable.abi.effects,
        );
        let params = cont_ctx.entry_params(param_tys.iter());
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

        // A source that already has the entry's layout needs no adapter: the
        // entry is the continuation, and the call builds one frame, not two.
        if let BackendEntryOrigin::DeliveredResume { layout, .. } = &entry.origin
            && layout.layout == source.layout
        {
            return self.entry_continuation(ctx, executable, entries, entry_fns, entry_id, env);
        }

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

        let mut param_tys = source_tys;
        let mut param_reprs = source_reprs;
        self.append_entry_capture_lanes(executable, entry, &mut param_tys, &mut param_reprs);

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
                local,
                &capture.layout,
                &mut args,
            )?;
        }
        for capture in &entry.physical_captures {
            args.push(self.env_runtime_var(ctx, executable, env, *capture));
        }
        Ok(args)
    }

    fn receive_capture_vars(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        outcomes: &[super::super::body::OutcomeEdge],
        after: Option<&super::super::body::ReceiveAfter>,
        env: &ValueEnv,
    ) -> Result<Vec<Var>, FatalError> {
        let mut iter = outcomes
            .iter()
            .map(|edge| edge.target)
            .chain(after.iter().map(|after| after.entry));
        let (capture_ids, physical_captures) = iter
            .next()
            .map(|entry_id| {
                let entry = &entries[entry_id.as_u32() as usize];
                (entry.captures.as_slice(), entry.physical_captures.as_slice())
            })
            .unwrap_or_default();
        for entry_id in iter {
            let entry_captures = &entries[entry_id.as_u32() as usize].captures;
            if entries[entry_id.as_u32() as usize].physical_captures != physical_captures
                || entry_captures.len() != capture_ids.len()
                || entry_captures
                    .iter()
                    .zip(capture_ids)
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
                local,
                &capture.layout,
                &mut args,
            )?;
        }
        args.extend(
            physical_captures
                .iter()
                .map(|capture| self.env_runtime_var(ctx, executable, env, *capture)),
        );
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
            BackendEntryOrigin::Clause
            | BackendEntryOrigin::Branch
            | BackendEntryOrigin::ReceiveOutcome
            | BackendEntryOrigin::Handler => Vec::new(),
            BackendEntryOrigin::DeliveredResume { layout, .. } => {
                let mut lanes = Vec::new();
                let local = env
                    .value(value_id)
                    .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
                self.encode_runtime_value_for_layout(
                    ctx,
                    executable,
                    Some(value_id),
                    local,
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
        for input in &executable.abi.semantic_inputs {
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
        match self.world.shape(shape) {
            ShapeDescr::Nothing => Ok(NativeBoundValue::Absent),
            ShapeDescr::Lane(_) => Ok(NativeBoundValue::Runtime(next_runtime_lane(params, lane_index)?)),
            ShapeDescr::Callable(_) | ShapeDescr::Tuple(_) | ShapeDescr::Cursor { .. } => {
                let width = self.world.shape_width(shape);
                let end = lane_index.checked_add(width).ok_or(FatalError)?;
                let lanes = params.get(*lane_index..end).ok_or(FatalError)?.to_vec();
                *lane_index = end;
                Ok(NativeBoundValue::Transport { shape, lanes })
            }
        }
    }

    /// A decision's last resort: the plan's exception, raised through the one
    /// panic route, or the raise a handler was delivered, continued. A message
    /// that shows the subject reads the plan's first input; a re-raise reads
    /// its first three, the kind, the value and the reason.
    fn raise_last_resort(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &DispatchState,
    ) -> Result<(), FatalError> {
        let Some(last_resort) = &plan.last_resort else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("a dispatch with no last resort reached its fail in {:?}", ctx.origin),
            ));
        };
        if matches!(last_resort, LastResort::Reraise) {
            let kind = state.dispatch_inputs.first().ok_or(FatalError)?;
            let kind = self.materialize_native_value(ctx, None, kind)?;
            let value = state.dispatch_inputs.get(1).ok_or(FatalError)?;
            let value = self.materialize_native_value(ctx, None, value)?;
            let reason = state.dispatch_inputs.get(2).ok_or(FatalError)?;
            let reason = self.materialize_native_value(ctx, None, reason)?;
            ctx.set_term(Term::Reraise { kind, value, reason });
            return Ok(());
        }
        if matches!(last_resort, LastResort::Raise) {
            let value = state.dispatch_inputs.first().ok_or(FatalError)?;
            let value = self.materialize_native_value(ctx, None, value)?;
            let reason = state.dispatch_inputs.get(1).ok_or(FatalError)?;
            let reason = self.materialize_native_value(ctx, None, reason)?;
            ctx.set_term(Term::Raise {
                value,
                reason: Some(reason),
            });
            return Ok(());
        }
        let subject = match last_resort.consumed_inputs() {
            0 => None,
            _ => {
                let input = state.dispatch_inputs.first().ok_or(FatalError)?;
                Some(self.materialize_native_value(ctx, None, input)?)
            }
        };
        self.emit_raise(ctx, last_resort, subject)
    }

    /// Ends the block raising the struct `failure` builds: each field its
    /// exception declares, holding what the failure sets or the field's
    /// default, with `subject` as the value of a field that carries the plan's
    /// subject.
    fn emit_raise(
        &mut self,
        ctx: &mut NativeFnCtx,
        failure: &LastResort,
        subject: Option<Var>,
    ) -> Result<(), FatalError> {
        let program = self.program;
        let raised = failure.exception().and_then(|exception| {
            let module = fz_runtime::module_name::ModuleName::from_atom_name(exception)?;
            let declared = program.schema(&module)?;
            let defaults = program.struct_defaults(&module)?;
            Some((module, failure.struct_fields(declared, defaults)))
        });
        let (module, fields) = match raised {
            Some((module, Ok(fields))) => (module, fields),
            Some((_, Err(reason))) => return Err(incomplete_native_program(self.telemetry, self.root_id, reason)),
            None => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!("a failure raises {failure:?}, whose struct the program lacks"),
                ));
            }
        };
        let fields = fields
            .into_iter()
            .map(|(name, held)| {
                let value = match held {
                    RaisedField::Subject => subject.expect("a field that carries the subject has one to carry"),
                    RaisedField::Literal(term) => self.literal_var(ctx, term),
                };
                (name.to_string(), value)
            })
            .collect();
        let (value, _) = ctx.emit_let(Prim::MakeStruct { module, fields });
        let reason = failure.reason().map(|reason| self.reason_var(ctx, reason, subject));
        ctx.set_term(Term::Raise { value, reason });
        Ok(())
    }

    /// The Erlang reason a failure declares, built as the value a `catch`
    /// binds, with `subject` where the reason holds the plan's subject.
    fn reason_var(&mut self, ctx: &mut NativeFnCtx, reason: &ReasonTerm, subject: Option<Var>) -> Var {
        match reason {
            ReasonTerm::Atom(name) => self.ground_var(ctx, &GroundValue::Atom(name.to_string())),
            ReasonTerm::Tuple(elements) => {
                let elements = elements
                    .iter()
                    .map(|element| match element {
                        FieldTerm::Subject => subject.expect("a reason that carries the subject has one to carry"),
                        FieldTerm::Literal(term) => self.literal_var(ctx, term),
                    })
                    .collect();
                ctx.emit_let(Prim::MakeTuple(elements)).0
            }
        }
    }

    /// `term` as `layout` carries it. A tuple whose layout spreads its fields
    /// over lanes is encoded field by field, as a tuple step is, so no tuple
    /// is built only to be taken apart; every other term is built whole.
    fn literal_bound(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        term: &LiteralTerm,
        layout: Option<TransportLayout>,
    ) -> Result<NativeBoundValue, FatalError> {
        let spread = layout.filter(|layout| {
            self.world.tuple_arity(layout.structural).is_some()
                && !matches!(layout.carrier, super::super::pull::TransportCarrier::ValueRef(_))
        });
        let (LiteralTerm::Tuple(items), Some(layout)) = (term, spread) else {
            return Ok(NativeBoundValue::Runtime(self.literal_var(ctx, term)));
        };
        let shape = layout.structural;
        if self.world.tuple_arity(shape) != Some(items.len()) {
            return Err(FatalError);
        }
        let mut lanes = Vec::new();
        for (index, item) in items.iter().enumerate() {
            let field_layout = self.field_layout(shape, index);
            if self.world.layout_width(field_layout) == 0 {
                continue;
            }
            let item = self.literal_bound(ctx, executable, item, Some(field_layout))?;
            self.encode_transport_layout(ctx, executable, None, &item, field_layout, &mut lanes)?;
        }
        Ok(NativeBoundValue::Transport { shape, lanes })
    }

    /// Builds `term` and answers the value it is.
    fn literal_var(&mut self, ctx: &mut NativeFnCtx, term: &LiteralTerm) -> Var {
        let prim = match term {
            LiteralTerm::Ground(value) => return self.ground_var(ctx, value),
            LiteralTerm::Function { .. } => unreachable!("neither a constant nor a raised field holds a function"),
            LiteralTerm::List(items) => {
                let items = items.iter().map(|item| self.literal_var(ctx, item)).collect();
                Prim::MakeList(items, None, None)
            }
            LiteralTerm::Tuple(items) => {
                let items = items.iter().map(|item| self.literal_var(ctx, item)).collect();
                Prim::MakeTuple(items)
            }
            LiteralTerm::Map(entries) => {
                let in_key_order = LiteralTerm::entries_in_key_order(entries);
                let written = in_key_order.clone().unwrap_or_else(|| entries.iter().collect());
                let (mut map, _) = ctx.emit_let(Prim::DestMapBegin(DestMapSeed::Capacity(written.len())));
                for (key, value) in written {
                    let (key, value) = (self.literal_var(ctx, key), self.literal_var(ctx, value));
                    map = ctx.emit_map_put(map, key, value);
                }
                match in_key_order {
                    Some(_) => Prim::DestMapPublish(map),
                    None => Prim::DestMapFreeze(map),
                }
            }
        };
        ctx.emit_let(prim).0
    }

    /// The constant that is `value`. Its known type travels with it: a later
    /// comparison against a raw atom or int then takes the fast path that
    /// needs no boxed scalar.
    fn ground_var(&mut self, ctx: &mut NativeFnCtx, value: &GroundValue) -> Var {
        let (prim, ty) = match value {
            GroundValue::Int(value) => (Const::Int(*value), self.world.types_mut().int()),
            GroundValue::Float(bits) => (Const::Float(f64::from_bits(*bits)), self.world.types_mut().float()),
            GroundValue::Atom(name) => (Const::Atom(self.atom_id(name)), self.world.types_mut().atom()),
            GroundValue::Bool(true) => (Const::True, self.world.types_mut().bool()),
            GroundValue::Bool(false) => (Const::False, self.world.types_mut().bool()),
            GroundValue::Nil => (Const::Nil, self.world.types_mut().nil()),
            GroundValue::Binary(bytes) | GroundValue::Utf8Binary(bytes) => {
                return ctx
                    .emit_let(Prim::ConstBitstring(bytes.clone(), 8 * bytes.len() as u64))
                    .0;
            }
        };
        let var = ctx.emit_let(Prim::Const(prim)).0;
        ctx.value_types.insert(var, ty);
        var
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_control_dispatch_leaf(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        entries: &[BackendEntry],
        entry_fns: &mut EntryFns,
        env: &ValueEnv,
        plan: &PatternDispatchPlan<Ty>,
        outcomes: &[super::super::body::OutcomeEdge],
        miss_entry: Option<ControlEntryId>,
        leaf: DispatchLeaf,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        match leaf {
            DispatchLeaf::Fail => {
                let Some(miss_entry) = miss_entry else {
                    return self.raise_last_resort(ctx, plan, state);
                };
                let args = self.entry_capture_args(ctx, executable, entries, miss_entry, env)?;
                self.transfer_to_entry(ctx, executable, entries, entry_fns, miss_entry, args);
                Ok(())
            }
            DispatchLeaf::Outcome(outcome) => {
                let edge = outcomes
                    .get(outcome.0 as usize)
                    .expect("every native dispatch outcome has an edge");
                let arm_entry = edge.target;
                self.check_outcome_arguments_follow_parameters(&entries[arm_entry.as_u32() as usize], &edge.arguments)?;
                let mut args = self.encode_outcome_arguments(ctx, executable, plan, state, &edge.arguments)?;
                args.extend(self.entry_capture_args(ctx, executable, entries, arm_entry, env)?);
                self.transfer_to_entry(ctx, executable, entries, entry_fns, arm_entry, args);
                Ok(())
            }
        }
    }

    /// Lowers a dispatch graph, each node once.
    ///
    /// The root is lowered from the current block. An edge into a join records
    /// what it holds and jumps to the join's block; after the root, each
    /// join is lowered in its block, from the largest id down, holding what
    /// every arrival holds. A fail or an outcome is lowered by `lower_leaf`.
    fn lower_dispatch_graph<L>(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        origin: BranchOrigin,
        state: &mut DispatchState,
        lower_leaf: &mut L,
    ) -> Result<(), FatalError>
    where
        L: FnMut(&mut Self, &mut NativeFnCtx, DispatchLeaf, &mut DispatchState) -> Result<(), FatalError>,
    {
        let mut walk = DispatchWalk {
            plan,
            origin,
            lower_leaf,
            joins: DispatchJoins::default(),
        };
        self.lower_dispatch_node(ctx, &mut walk, plan.graph.root, state)?;
        while let Some(join) = walk.joins.next() {
            ctx.current_block = join.block;
            let mut state = join.state;
            self.lower_dispatch_node(ctx, &mut walk, join.node, &mut state)?;
        }
        Ok(())
    }

    fn lower_dispatch_node<L>(
        &mut self,
        ctx: &mut NativeFnCtx,
        walk: &mut DispatchWalk<'_, L>,
        node_id: GraphNodeId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError>
    where
        L: FnMut(&mut Self, &mut NativeFnCtx, DispatchLeaf, &mut DispatchState) -> Result<(), FatalError>,
    {
        let Some(node) = walk.plan.graph.node(node_id) else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("dispatch graph node {:?} is out of bounds", node_id),
            ));
        };
        match node {
            DispatchNode::Fail => (walk.lower_leaf)(self, ctx, DispatchLeaf::Fail, state),
            DispatchNode::Outcome { outcome, .. } => {
                (walk.lower_leaf)(self, ctx, DispatchLeaf::Outcome(*outcome), state)
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => self.lower_dispatch_test(ctx, walk, predicate, on_match, on_miss, state),
        }
    }

    /// The block of the first field not fitting and the state it arrives with.
    /// `state` becomes the state of every other way to miss, which is past a
    /// first field that fit and was read: what `matched` learned of it.
    fn unfit_arrival(unfit: Unfit, state: &mut DispatchState, matched: &DispatchState) -> (BlockId, DispatchState) {
        let mut arrival = state.clone();
        arrival.fit_answers.insert(unfit.question, false);
        state.fit_answers.insert(unfit.question, true);
        state.field_reads.clone_from(&matched.field_reads);
        (unfit.block, arrival)
    }

    /// The node an arrival holding `state` reaches from `target`: a test whose
    /// first question the arrival has already answered no is passed over by
    /// its miss edge, so it is not a way into the node that asks it.
    fn first_unsettled(
        &self,
        plan: &PatternDispatchPlan<Ty>,
        mut target: GraphNodeId,
        state: &DispatchState,
    ) -> GraphNodeId {
        while let Some(DispatchNode::Test { predicate, on_miss, .. }) = plan.graph.node(target) {
            let unfit = self
                .first_fit_question(plan, state, predicate)
                .is_some_and(|question| state.fit_answers.get(&question) == Some(&false));
            if !unfit {
                break;
            }
            target = on_miss.target;
        }
        target
    }

    /// Follows an edge: into a join it jumps, otherwise the target is lowered
    /// where the edge stands.
    fn lower_dispatch_edge<L>(
        &mut self,
        ctx: &mut NativeFnCtx,
        walk: &mut DispatchWalk<'_, L>,
        target: GraphNodeId,
        state: &mut DispatchState,
    ) -> Result<(), FatalError>
    where
        L: FnMut(&mut Self, &mut NativeFnCtx, DispatchLeaf, &mut DispatchState) -> Result<(), FatalError>,
    {
        let target = self.first_unsettled(walk.plan, target, state);
        let joined = walk
            .joins
            .arrive(&walk.plan.graph, target, state, || ctx.builder.block(vec![]));
        match joined {
            Some(block) => {
                ctx.set_term(Term::Goto(block, vec![]));
                Ok(())
            }
            None => self.lower_dispatch_node(ctx, walk, target, state),
        }
    }

    /// Lower one dispatch test: ask its question, then follow the edge the
    /// answer selects.
    ///
    /// A question settled statically produces no branch at all -- the surviving
    /// edge is followed straight from the block the test would have branched
    /// from -- so the five dispatch graphs share this one shape.
    fn lower_dispatch_test<L>(
        &mut self,
        ctx: &mut NativeFnCtx,
        walk: &mut DispatchWalk<'_, L>,
        predicate: &crate::dispatch_matrix::RegionPredicate<Ty>,
        on_match: &crate::dispatch_matrix::DispatchEdge<Ty>,
        on_miss: &crate::dispatch_matrix::DispatchEdge<Ty>,
        state: &mut DispatchState,
    ) -> Result<(), FatalError>
    where
        L: FnMut(&mut Self, &mut NativeFnCtx, DispatchLeaf, &mut DispatchState) -> Result<(), FatalError>,
    {
        let plan = walk.plan;
        if let Region::Bitstring(shape) = &predicate.region {
            let reads_bytes = self.reads_bytes_by_address(plan, state, shape);
            self.read_bitstring_subject(ctx, plan, state, predicate.subject, reads_bytes)?;
        }
        let mut match_state = state.clone();
        let outcome = self.lower_dispatch_region(
            ctx,
            plan,
            predicate.subject,
            &predicate.region,
            &on_match.evidence,
            &mut match_state,
        )?;
        match outcome {
            RegionOutcome::Answer(DispatchAnswer::Static(true)) => {
                self.lower_dispatch_edge(ctx, walk, on_match.target, &mut match_state)
            }
            RegionOutcome::Answer(DispatchAnswer::Static(false)) => {
                self.lower_dispatch_edge(ctx, walk, on_miss.target, state)
            }
            RegionOutcome::Answer(DispatchAnswer::Runtime(cond)) => {
                let then_b = ctx.builder.block(vec![]);
                let else_b = ctx.builder.block(vec![]);
                ctx.set_term(Term::If {
                    cond,
                    then_b,
                    else_b,
                    origin: walk.origin,
                });
                ctx.current_block = then_b;
                self.lower_dispatch_edge(ctx, walk, on_match.target, &mut match_state)?;
                ctx.current_block = else_b;
                self.lower_dispatch_edge(ctx, walk, on_miss.target, state)
            }
            RegionOutcome::Matched { missed, unfit } => {
                let unfit_arrival = unfit.map(|unfit| Self::unfit_arrival(unfit, state, &match_state));
                self.lower_dispatch_edge(ctx, walk, on_match.target, &mut match_state)?;
                if let Some((block, mut unfit_state)) = unfit_arrival {
                    ctx.current_block = block;
                    self.lower_dispatch_edge(ctx, walk, on_miss.target, &mut unfit_state)?;
                }
                ctx.current_block = missed;
                self.lower_dispatch_edge(ctx, walk, on_miss.target, state)
            }
        }
    }

    /// The answer a variable's scalar type gives a predicate, when the
    /// predicate admits all of that scalar kind or none of it. A variable of
    /// type `int` is an integer wherever it is held, so the question needs no
    /// test and the successor it rules out is never lowered.
    fn scalar_lane_answer(&mut self, ctx: &NativeFnCtx, var: Var, predicate: &RuntimeTypePredicate) -> Option<bool> {
        let ty = ctx.value_types.get(&var).copied()?;
        let kind = match AbiValueRepr::for_ty(self.world, ty) {
            AbiValueRepr::RawInt => ValueKind::INT,
            AbiValueRepr::RawF64 => ValueKind::FLOAT,
            AbiValueRepr::RawAtom => ValueKind::ATOM,
            AbiValueRepr::ValueRef | AbiValueRepr::Stored => return None,
        };
        predicate.settled_for_scalar_lane(kind)
    }

    /// Whether a value held in this form can be a list. A tuple held as lanes
    /// cannot, and a variable whose type has no list in it cannot, so a list
    /// question of either is settled without reading it as a list.
    fn value_may_be_list(&mut self, ctx: &NativeFnCtx, value: &NativeBoundValue) -> bool {
        match value {
            NativeBoundValue::Transport { .. } => false,
            NativeBoundValue::Absent => true,
            NativeBoundValue::Runtime(var) => match ctx.value_types.get(var).copied() {
                Some(ty) => self.world.types().runtime_type_predicate(&ty).admits_a_list(),
                None => true,
            },
        }
    }

    /// Ask a type test of a value in whatever form it is held.
    ///
    /// A whole value answers with one `RuntimeTypeTest`. A tuple held as lanes
    /// has no value to read a schema off, so it asks the predicate what it
    /// wants of a tuple of that arity and puts one question to each position
    /// instead -- the same decomposition the boxed matcher and the boxed
    /// emitter make, one level in, against lanes already in hand. A binary
    /// held as a cursor is a bitstring and is asked by its length alone.
    ///
    /// A position carries runtime demand and so keeps a lane, which is why the
    /// absent arm below is unreachable rather than a case to answer.
    fn lane_form_type_test(
        &mut self,
        ctx: &mut NativeFnCtx,
        value: &NativeBoundValue,
        predicate: &RuntimeTypePredicate,
    ) -> Result<DispatchAnswer, FatalError> {
        let (shape, lanes) = match value {
            NativeBoundValue::Runtime(var) => {
                if let Some(admitted) = self.scalar_lane_answer(ctx, *var, predicate) {
                    return Ok(DispatchAnswer::Static(admitted));
                }
                let (flag, _) = ctx.emit_let(Prim::RuntimeTypeTest(*var, Box::new(predicate.clone())));
                return Ok(DispatchAnswer::Runtime(flag));
            }
            NativeBoundValue::Absent => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!("native type test has no value to ask in {:?}", ctx.origin),
                ));
            }
            NativeBoundValue::Transport { shape, lanes } => (*shape, lanes),
        };
        if matches!(self.world.shape(shape), ShapeDescr::Cursor { .. }) {
            return self.cursor_type_test(ctx, lanes, predicate);
        }
        let Some(arity) = self.world.tuple_arity(shape) else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("native type test cannot read lane-form {shape:?} in {:?}", ctx.origin),
            ));
        };
        let positions = match predicate.tuple_positions(arity) {
            TuplePositions::Never => return Ok(DispatchAnswer::Static(false)),
            TuplePositions::Always => return Ok(DispatchAnswer::Static(true)),
            TuplePositions::AnyOf(shapes) => shapes,
        };
        let views = self.transport_field_views(shape, lanes)?;
        let mut admitted = DispatchAnswer::Static(false);
        for shape in positions {
            let mut matched = DispatchAnswer::Static(true);
            for (position, view) in shape.iter().zip(&views) {
                let answer = self.lane_form_type_test(ctx, view, position)?;
                matched = matched.and(ctx, answer);
            }
            admitted = admitted.or(ctx, matched);
        }
        Ok(admitted)
    }

    /// Ask a type test of a binary that travels as a cursor: its source and a
    /// bit position. A cursor stands for the bitstring that remains from the
    /// position, so a predicate asks of it only whether it admits a bitstring
    /// whose length is whole bytes, partial, or either. Only the first of the
    /// two needs the lanes, and it needs the one question a `binary` rest field
    /// already asks -- do the remaining bits fill whole bytes -- which no
    /// suffix is built to answer.
    fn cursor_type_test(
        &mut self,
        ctx: &mut NativeFnCtx,
        lanes: &[Var],
        predicate: &RuntimeTypePredicate,
    ) -> Result<DispatchAnswer, FatalError> {
        let admitted = predicate.bitstrings;
        if !admitted.asks_length() {
            return Ok(DispatchAnswer::Static(!admitted.is_none()));
        }
        let &[source, position] = lanes else {
            return Err(FatalError);
        };
        let (bit_len, _) = ctx.emit_let(Prim::BinaryBitLen(source));
        let int = self.world.types_mut().int();
        ctx.value_types.insert(bit_len, int);
        let rest = BitMatchField {
            ty: BitType::Binary,
            size: None,
            endian: crate::ast::Endian::Big,
            signed: false,
            unit: None,
            is_last: true,
        };
        let (whole_bytes, _) = ctx.emit_let(Prim::BitFieldFits {
            pos: position,
            bit_len,
            field: rest,
        });
        let bool_ty = self.world.types_mut().bool();
        ctx.value_types.insert(whole_bytes, bool_ty);
        if admitted.whole_bytes {
            return Ok(DispatchAnswer::Runtime(whole_bytes));
        }
        let (partial_byte, _) = ctx.emit_let(Prim::UnOp(IrUnOp::Not, whole_bytes));
        ctx.value_types.insert(partial_byte, bool_ty);
        Ok(DispatchAnswer::Runtime(partial_byte))
    }

    /// Answer one region question about one subject.
    fn lower_dispatch_region(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        subject: SubjectId,
        region: &Region<Ty>,
        evidence: &crate::dispatch_matrix::EdgeEvidence<Ty>,
        state: &mut DispatchState,
    ) -> Result<RegionOutcome, FatalError> {
        Ok(RegionOutcome::Answer(DispatchAnswer::Runtime(match region {
            Region::Type(ty) => {
                // The value is asked in the form it is held: a tuple delivered
                // as lanes is decided per position, without one being built.
                let value = self.dispatch_subject_value(ctx, plan, state, subject)?;
                let predicate = self.world.types().runtime_type_predicate(ty);
                return self
                    .lane_form_type_test(ctx, value, &predicate)
                    .map(RegionOutcome::Answer);
            }
            Region::List(list) => {
                let value = self.dispatch_subject_value(ctx, plan, state, subject)?;
                if !self.value_may_be_list(ctx, value) {
                    return Ok(RegionOutcome::Answer(DispatchAnswer::Static(false)));
                }
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let question = match list {
                    ListRegion::Empty => Prim::IsEmptyList(subject),
                    ListRegion::Cons => Prim::IsListCons(subject),
                };
                let (var, _) = ctx.emit_let(question);
                var
            }
            Region::TupleArity(arity) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let tuple_ty = RuntimeTypePredicate::tuple_arity(*arity as usize);
                let (var, _) = ctx.emit_let(Prim::RuntimeTypeTest(subject, Box::new(tuple_ty)));
                var
            }
            Region::Arity(arity) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let callable = RuntimeTypePredicate::callable_arity(*arity as usize);
                let (var, _) = ctx.emit_let(Prim::RuntimeTypeTest(subject, Box::new(callable)));
                var
            }
            Region::MapSize(size) => self.lower_property_is(ctx, plan, state, subject, "fz_map_size_of", *size)?,
            Region::ByteSize(size) => {
                self.lower_property_is(ctx, plan, state, subject, "fz_bitstring_byte_size_of", *size)?
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
                let map_var = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let key_var = self.dispatch_key_var(ctx, plan, state, key)?;
                let (value, _) = ctx.emit_let(Prim::MatcherMapGet(map_var, key_var));
                for result in &evidence.projections {
                    if let crate::dispatch_matrix::SubjectSource::Projection(projection) = plan.subject(*result)
                        && projection.source == subject
                        && matches!(&projection.kind, crate::dispatch_matrix::ProjectionKind::MapValue { key: projection_key } if projection_key == key)
                    {
                        state.values.insert(*result, NativeBoundValue::Runtime(value));
                    }
                }
                let (is_miss, _) = ctx.emit_let(Prim::IsMapMiss(value));
                let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, is_miss, false_v));
                var
            }
            Region::Equal(ComparisonValue::Const(value)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let expected = lower_dispatch_const(ctx, &self.atoms, self.world.types_mut(), value)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, subject, expected));
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
                self.lower_guard_answer(ctx, plan, state, expr)?
            }
            Region::Equal(ComparisonValue::Pinned(pinned)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let pinned = self.dispatch_pinned_var(state, *pinned)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, subject, pinned));
                var
            }
            Region::Equal(ComparisonValue::Subject(earlier)) => {
                let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
                let earlier = self.dispatch_subject_var(ctx, plan, state, *earlier)?;
                let (var, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, subject, earlier));
                var
            }
            Region::Bitstring(shape) => return self.lower_bitstring_region(ctx, plan, subject, shape, state),
        })))
    }

    /// Whether the property `reader` answers for the subject is `size`. The
    /// reader is a runtime function that answers -1 for a value with no such
    /// property, so it is asked of any value, and no size matches that answer.
    fn lower_property_is(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        subject: SubjectId,
        reader: &str,
        size: u32,
    ) -> Result<Var, FatalError> {
        let subject = self.dispatch_subject_var(ctx, plan, state, subject)?;
        let reader = GuardExtern::new(
            ExternAbi::Fz,
            reader,
            &[ExternTy::Any],
            ExternReturn::Scalar(ExternTy::I64),
            false,
        )
        .expect("a property reader takes one reference word and answers an integer");
        let extern_id = self.guard_extern_id(&reader);
        let callsite = ctx.fresh_callsite();
        let (property, _) = ctx.emit_let(Prim::Extern(
            callsite,
            extern_id,
            vec![ExternArg::fixed(subject, ExternTy::Any)],
        ));
        let int = self.world.types_mut().int();
        ctx.value_types.insert(property, int);
        let (expected, _) = ctx.emit_let(Prim::Const(Const::Int(i64::from(size))));
        let (is_size, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, property, expected));
        Ok(is_size)
    }

    /// A guard's truth. A call inside it that fails the guard (a helper that
    /// matches nothing, or an extern that aborts) leaves through one block and
    /// answers false, however deep in the expression it was made.
    fn lower_guard_answer(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        expr: &PatternGuardExpr<Ty>,
    ) -> Result<Var, FatalError> {
        let mut fail = None;
        let value = self.lower_guard_expr(ctx, plan, state, expr, &mut fail)?;
        let Some(fail_b) = fail else {
            return Ok(value);
        };
        let answer = ctx.builder.fresh_var();
        let done_b = ctx.builder.block(vec![answer]);
        ctx.set_term(Term::Goto(done_b, vec![value]));
        ctx.current_block = fail_b;
        let (false_value, _) = ctx.emit_let(Prim::Const(Const::False));
        ctx.set_term(Term::Goto(done_b, vec![false_value]));
        ctx.current_block = done_b;
        Ok(answer)
    }

    fn lower_guard_expr(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        expr: &PatternGuardExpr<Ty>,
        fail: &mut Option<BlockId>,
    ) -> Result<Var, FatalError> {
        Ok(match expr {
            PatternGuardExpr::Const(value) => lower_dispatch_const(ctx, &self.atoms, self.world.types_mut(), value)?,
            PatternGuardExpr::EmptyList => {
                let empty = ctx.emit_let(Prim::MakeList(Vec::new(), None, None)).0;
                let ty = self.world.types_mut().empty_list();
                ctx.value_types.insert(empty, ty);
                empty
            }
            PatternGuardExpr::Subject(subject) => self.dispatch_subject_var(ctx, plan, state, *subject)?,
            PatternGuardExpr::Unary {
                op: PatternGuardUnaryOp::Not,
                expr,
            } => {
                let input = self.lower_guard_boolean(ctx, plan, state, expr, fail)?;
                self.emit_guard_boolean(ctx, Prim::UnOp(IrUnOp::Not, input))
            }
            PatternGuardExpr::Binary {
                op: op @ (PatternGuardBinOp::And | PatternGuardBinOp::Or),
                lhs,
                rhs,
            } => self.lower_guard_short_circuit(ctx, plan, state, *op, lhs, rhs, fail)?,
            PatternGuardExpr::Binary { op, lhs, rhs } => {
                let lhs = self.lower_guard_expr(ctx, plan, state, lhs, fail)?;
                let rhs = self.lower_guard_expr(ctx, plan, state, rhs, fail)?;
                self.emit_guard_boolean(ctx, Prim::BinOp(lower_guard_binop(*op), lhs, rhs))
            }
            PatternGuardExpr::Dispatch {
                inputs,
                prepared,
                dispatch,
            } => self.lower_guard_dispatch(ctx, plan, state, inputs, prepared, dispatch, fail)?,
            PatternGuardExpr::Fails => Self::fail_guard(ctx, fail),
            PatternGuardExpr::Extern { extern_fn, args } => {
                self.lower_guard_extern(ctx, plan, state, extern_fn, args, fail)?
            }
            PatternGuardExpr::Pinned(pinned) => self.dispatch_pinned_var(state, *pinned)?,
        })
    }

    /// A guard step whose answer is a boolean whatever its operands are: a
    /// comparison or a `not`. Recording that lets an enclosing `and`, `or` or
    /// `not` take the answer without testing it.
    fn emit_guard_boolean(&mut self, ctx: &mut NativeFnCtx, prim: Prim) -> Var {
        let (answer, _) = ctx.emit_let(prim);
        self.record_guard_boolean(ctx, answer);
        answer
    }

    fn record_guard_boolean(&mut self, ctx: &mut NativeFnCtx, answer: Var) {
        let boolean = self.world.types_mut().bool();
        ctx.value_types.insert(answer, boolean);
    }

    /// An operand of `and`, `or` or `not`. In a guard an error fails the
    /// guard, and a non-boolean operand is an error, so one the type does not
    /// already prove a boolean is tested and leaves through the failure block.
    fn lower_guard_boolean(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        expr: &PatternGuardExpr<Ty>,
        fail: &mut Option<BlockId>,
    ) -> Result<Var, FatalError> {
        let value = self.lower_guard_expr(ctx, plan, state, expr, fail)?;
        let proven = ctx.value_types.get(&value).copied().is_some_and(|ty| {
            let boolean = self.world.types_mut().bool();
            self.world.types().is_subtype(&ty, &boolean)
        });
        if proven {
            return Ok(value);
        }
        let (true_v, _) = ctx.emit_let(Prim::Const(Const::True));
        let (false_v, _) = ctx.emit_let(Prim::Const(Const::False));
        let (is_true, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, value, true_v));
        let (is_false, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, value, false_v));
        let (is_boolean, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Or, is_true, is_false));
        let boolean_b = ctx.builder.block(vec![]);
        let fail_b = *fail.get_or_insert_with(|| ctx.builder.block(vec![]));
        ctx.set_term(Term::If {
            cond: is_boolean,
            then_b: boolean_b,
            else_b: fail_b,
            origin: BranchOrigin::ClauseDispatch,
        });
        ctx.current_block = boolean_b;
        Ok(value)
    }

    /// `and` / `or` evaluate their right side only when the left leaves it
    /// open, so a right side that fails the guard is never reached when the
    /// left has already decided.
    #[allow(clippy::too_many_arguments)]
    fn lower_guard_short_circuit(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        op: PatternGuardBinOp,
        lhs: &PatternGuardExpr<Ty>,
        rhs: &PatternGuardExpr<Ty>,
        fail: &mut Option<BlockId>,
    ) -> Result<Var, FatalError> {
        let lhs = self.lower_guard_boolean(ctx, plan, state, lhs, fail)?;
        let answer = ctx.builder.fresh_var();
        let done_b = ctx.builder.block(vec![answer]);
        let rhs_b = ctx.builder.block(vec![]);
        let decided_b = ctx.builder.block(vec![]);
        let decided_when_truthy = match op {
            PatternGuardBinOp::And => false,
            PatternGuardBinOp::Or => true,
            _ => unreachable!("only `and` and `or` short-circuit"),
        };
        let (then_b, else_b) = if decided_when_truthy {
            (decided_b, rhs_b)
        } else {
            (rhs_b, decided_b)
        };
        ctx.set_term(Term::If {
            cond: lhs,
            then_b,
            else_b,
            origin: BranchOrigin::ClauseDispatch,
        });
        ctx.current_block = decided_b;
        let (decided, _) = ctx.emit_let(Prim::Const(if decided_when_truthy {
            Const::True
        } else {
            Const::False
        }));
        ctx.set_term(Term::Goto(done_b, vec![decided]));
        ctx.current_block = rhs_b;
        // What the right side builds exists only on the path that reaches it.
        let rhs = self.lower_guard_boolean(ctx, plan, &mut state.clone(), rhs, fail)?;
        ctx.set_term(Term::Goto(done_b, vec![rhs]));
        ctx.current_block = done_b;
        self.record_guard_boolean(ctx, answer);
        Ok(answer)
    }

    /// A call to an extern.
    fn lower_guard_extern(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        extern_fn: &GuardExtern,
        args: &[PatternGuardExpr<Ty>],
        fail: &mut Option<BlockId>,
    ) -> Result<Var, FatalError> {
        let mut extern_args = Vec::with_capacity(args.len());
        for (arg, ty) in args.iter().zip(&extern_fn.params) {
            let var = self.lower_guard_expr(ctx, plan, state, arg, fail)?;
            if *ty == ExternTy::BinaryCursor {
                // A guard holds the binary whole: its view starts at 0.
                let from_the_start = ctx.emit_let(Prim::Const(Const::Int(0))).0;
                extern_args.push(ExternArg::fixed(var, ExternTy::Any));
                extern_args.push(ExternArg::fixed(from_the_start, ExternTy::I64));
            } else {
                extern_args.push(ExternArg::fixed(var, *ty));
            }
        }
        let extern_id = self.guard_extern_id(extern_fn);
        let callsite = ctx.fresh_callsite();
        let prim = Prim::Extern(callsite, extern_id, extern_args);
        let (var, lane) = match &extern_fn.ret {
            ExternReturn::Checked(lane, _) => {
                let (values, _) = ctx.emit_let_many(2, prim);
                let ok_b = ctx.builder.block(vec![]);
                let fail_b = *fail.get_or_insert_with(|| ctx.builder.block(vec![]));
                ctx.set_term(Term::If {
                    cond: values[1],
                    then_b: fail_b,
                    else_b: ok_b,
                    origin: BranchOrigin::ClauseDispatch,
                });
                ctx.current_block = ok_b;
                (values[0], *lane)
            }
            ExternReturn::Scalar(lane) => (ctx.emit_let(prim).0, *lane),
        };
        match lane {
            ExternTy::I64 => {
                let int = self.world.types_mut().int();
                ctx.value_types.insert(var, int);
            }
            ExternTy::F64 => {
                let float = self.world.types_mut().float();
                ctx.value_types.insert(var, float);
            }
            ExternTy::Bool => {
                let boolean = self.world.types_mut().bool();
                ctx.value_types.insert(var, boolean);
            }
            ExternTy::Opaque(kind) => {
                let opaque = match kind {
                    ValueKind::PID => self.world.types_mut().pid(),
                    ValueKind::REF => self.world.types_mut().reference(),
                    other => unreachable!("an opaque extern lane is a pid or a reference, not {other:?}"),
                };
                ctx.value_types.insert(var, opaque);
            }
            _ => {}
        }
        Ok(var)
    }

    fn leave_guard_dispatch(ctx: &mut NativeFnCtx, fail: &mut Option<BlockId>) {
        let fail_b = *fail.get_or_insert_with(|| ctx.builder.block(vec![]));
        ctx.set_term(Term::Goto(fail_b, vec![]));
    }

    /// Leaves the guard through its failure block. What follows in the
    /// expression is unreachable, and goes on in a block nothing enters.
    fn fail_guard(ctx: &mut NativeFnCtx, fail: &mut Option<BlockId>) -> Var {
        let fail_b = *fail.get_or_insert_with(|| ctx.builder.block(vec![]));
        ctx.set_term(Term::Goto(fail_b, vec![]));
        ctx.current_block = ctx.builder.block(vec![]);
        ctx.emit_let(Prim::Const(Const::False)).0
    }

    fn guard_extern_id(&mut self, extern_fn: &GuardExtern) -> ExternId {
        let key = (extern_fn.abi, extern_fn.symbol.clone());
        if let Some(id) = self.guard_extern_ids.get(&key) {
            return *id;
        }
        let id = ExternId(self.extern_decls.len() as u32);
        self.extern_decls.push(ExternDecl {
            id,
            symbol: extern_fn.symbol.clone(),
            params: ExternTy::wire_classes(&extern_fn.params),
            variadic: false,
            ret: extern_fn.ret.clone(),
            abi: extern_fn.abi,
        });
        self.guard_extern_ids.insert(key, id);
        id
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_guard_dispatch(
        &mut self,
        ctx: &mut NativeFnCtx,
        parent_plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        inputs: &[PatternGuardExpr<Ty>],
        prepared_keys: &[crate::dispatch_matrix::PreparedKeyId],
        dispatch: &crate::dispatch_matrix::pattern::PatternGuardDispatch<Ty>,
        fail: &mut Option<BlockId>,
    ) -> Result<Var, FatalError> {
        let input_vars = inputs
            .iter()
            .map(|input| self.lower_guard_expr(ctx, parent_plan, state, input, fail))
            .collect::<Result<Vec<_>, _>>()?;
        let done_value = ctx.builder.fresh_var();
        let done_b = ctx.builder.block(vec![done_value]);
        let prepared = prepared_keys
            .iter()
            .map(|id| {
                state.bindings.prepared.get(id.0 as usize).copied().ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("guard prepared operand {:?} is missing from its caller", id),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut dispatch_state = DispatchState::resolved(
            input_vars,
            Vec::new(),
            DispatchBindings {
                pinned: Vec::new(),
                prepared,
            },
        )
        .reading(guard_body_subjects(&dispatch.bodies));
        let mut answers = Vec::new();
        self.lower_dispatch_graph(
            ctx,
            &dispatch.plan,
            BranchOrigin::ClauseDispatch,
            &mut dispatch_state,
            &mut |lowerer, ctx, leaf, state| {
                lowerer.lower_guard_dispatch_leaf(
                    ctx,
                    &dispatch.plan,
                    &dispatch.bodies,
                    leaf,
                    done_b,
                    &mut answers,
                    fail,
                    state,
                )
            },
        )?;
        if let Some(ty) = self.join_type(ctx, &answers) {
            ctx.value_types.insert(done_value, ty);
        }
        ctx.current_block = done_b;
        Ok(done_value)
    }

    /// The type the join of a guard dispatch's bodies holds: the union of what
    /// each body answered. The join takes the lane that type has, so bodies that
    /// all answer an integer meet in a raw integer and the guard that reads it
    /// never sees a box. One body of unknown type leaves the join untyped.
    fn join_type(&mut self, ctx: &NativeFnCtx, answers: &[Var]) -> Option<Ty> {
        let mut tys = answers.iter().map(|answer| ctx.value_types.get(answer).copied());
        let first = tys.next()??;
        tys.try_fold(first, |joined, ty| Some(self.world.types_mut().union(joined, ty?)))
    }

    #[allow(clippy::too_many_arguments)]
    fn lower_guard_dispatch_leaf(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        bodies: &[PatternGuardExpr<Ty>],
        leaf: DispatchLeaf,
        done_b: BlockId,
        answers: &mut Vec<Var>,
        fail: &mut Option<BlockId>,
        state: &mut DispatchState,
    ) -> Result<(), FatalError> {
        match leaf {
            DispatchLeaf::Fail => {
                Self::leave_guard_dispatch(ctx, fail);
                Ok(())
            }
            DispatchLeaf::Outcome(outcome) => {
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
                if matches!(body, PatternGuardExpr::Fails) {
                    // A body that fails the guard answers nothing to the join.
                    Self::leave_guard_dispatch(ctx, fail);
                    return Ok(());
                }
                let value = self.lower_guard_expr(ctx, plan, state, body, fail)?;
                answers.push(value);
                ctx.set_term(Term::Goto(done_b, vec![value]));
                Ok(())
            }
        }
    }

    /// Clause selection on a bitstring pattern.
    ///
    /// The interpreter answers this in `Dispatch::read_bitstring` and the
    /// receive matcher answers it in `emit_bitstring_test`; this is the entry
    /// dispatch's answer, and it is why `case <<len, rest :: binary>> -> ...`
    /// used to run on the interpreter and refuse to lower natively.
    ///
    /// Unlike the binding path — which reads fields the dispatch has already
    /// proven present — a failed read has to fall through rather than abort. A
    /// read has no miss to report: it is only made once `BitFieldFits` says the
    /// field is there. Hence short-circuit control flow: every failure edge
    /// goes to one block, and the region ends in the block where everything
    /// matched, with no yes or no value in between. The position is an
    /// integer the region carries from field to field.
    ///
    /// A field is built (`BitReadField`) only when something reads its value:
    /// a later question, a later field's `size(len)`, or the winning outcome
    /// (`DispatchState::outcome_reads`). Every other field is only checked to
    /// fit, so a clause whose body re-reads its own fields allocates nothing
    /// here. A built field is recorded in `state.values` under its own
    /// subject, which is what lets `dispatch_subject_var` resolve a
    /// bitstring-field projection instead of reporting it unsupported.
    fn lower_bitstring_region(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        subject: SubjectId,
        shape: &crate::dispatch_matrix::BitstringShape,
        state: &mut DispatchState,
    ) -> Result<RegionOutcome, FatalError> {
        let reads_bytes = self.reads_bytes_by_address(plan, state, shape);
        let (subject_var, cursor_position, facts) =
            self.read_bitstring_subject(ctx, plan, state, subject, reads_bytes)?;
        let bit_len = facts.bit_len;
        let fail_b = ctx.builder.block(vec![]);
        let int = self.world.types_mut().int();

        let (mut pos, mut start) = match cursor_position {
            Some(position) => (position, FieldStart::PastCursor(Some(0))),
            None => {
                let (zero, _) = ctx.emit_let(Prim::Const(Const::Int(0)));
                ctx.value_types.insert(zero, int);
                (zero, FieldStart::Fixed(0))
            }
        };
        let field_count = shape.fields.len();
        let mut unfit = None;
        for (index, field_subject) in shape.fields.iter().enumerate() {
            let extraction = plan.bitstring_extraction(*field_subject);
            let spec = &extraction.spec;
            let field = BitMatchField {
                ty: spec.runtime_kind(),
                size: self.lower_dispatch_bit_size(ctx, plan, state, spec, fail_b)?,
                endian: spec.endian,
                signed: spec.signed,
                unit: spec.unit,
                is_last: extraction.is_last,
            };
            if cursor_position.is_none() && index == 0 && Self::fit_ignores_length(&field) {
                self.require_binary(ctx, pos, bit_len, fail_b);
            }
            let question = match (index, cursor_position) {
                (0, Some(position)) => FitQuestion::of(subject_var, position, &extraction.spec),
                _ => None,
            };
            let utf8_end = if question.is_some_and(|question| state.fit_answers.get(&question) == Some(&true)) {
                None
            } else {
                let (fits, utf8_end) = self.emit_bit_fits(ctx, subject_var, pos, bit_len, &field);
                let next_b = ctx.builder.block(vec![]);
                let else_b = match question {
                    Some(question) => {
                        let block = ctx.builder.block(vec![]);
                        unfit = Some(Unfit { block, question });
                        block
                    }
                    None => fail_b,
                };
                ctx.set_term(Term::If {
                    cond: fits,
                    then_b: next_b,
                    else_b,
                    origin: BranchOrigin::ClauseDispatch,
                });
                ctx.current_block = next_b;
                utf8_end
            };
            if let Some(question) = question {
                state.fit_answers.insert(question, true);
            }
            let consumed = plan.graph.asks(*field_subject) || state.outcome_reads.contains(field_subject);
            let value = if !consumed {
                None
            } else if self.is_rest_read(&field) {
                Some(NativeBoundValue::Transport {
                    shape: self.world.binary_cursor_shape(),
                    lanes: vec![subject_var, pos],
                })
            } else {
                let read = match question.and_then(|question| state.field_read(question, &field)) {
                    Some(read) => read,
                    None => {
                        let read = self.emit_bit_read(ctx, facts.base, subject_var, pos, start, &field)?;
                        if let Some(question) = question {
                            state.field_reads.push(FieldRead::of(question, &field, read));
                        }
                        read
                    }
                };
                Some(NativeBoundValue::Runtime(read))
            };
            // The last field has no successor unless the pattern must also end
            // there; a field that reads to the end of the binary ends at its end.
            let reads_to_end = field.size.is_none() && matches!(field.ty, BitType::Binary | BitType::Bits);
            if reads_to_end {
                pos = bit_len;
                start = FieldStart::Unknown;
            } else if let Some(end) = utf8_end {
                pos = end;
                start = start.advanced_by(None);
            } else if index + 1 < field_count || shape.require_done {
                pos = self.emit_bit_next(ctx, subject_var, pos, field.clone());
                start = start.advanced_by(field.static_bits());
            }
            // A later field's `size(len)` reads this one, and the read happens
            // in this block, so it is available for the rest of the loop.
            if let Some(value) = value {
                state.values.insert(*field_subject, value);
            }
        }

        if shape.require_done {
            let (exhausted, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Identical, pos, bit_len));
            let bool_ty = self.world.types_mut().bool();
            ctx.value_types.insert(exhausted, bool_ty);
            let matched_b = ctx.builder.block(vec![]);
            ctx.set_term(Term::If {
                cond: exhausted,
                then_b: matched_b,
                else_b: fail_b,
                origin: BranchOrigin::ClauseDispatch,
            });
            ctx.current_block = matched_b;
        }

        Ok(RegionOutcome::Matched { missed: fail_b, unfit })
    }

    /// Whether `field` is the rest of a binary: a `binary` or `bits` field with
    /// no size, which reads to the end.
    fn is_rest_read(&self, field: &BitMatchField) -> bool {
        field.is_last && field.size.is_none() && matches!(field.ty, BitType::Binary | BitType::Bits)
    }

    /// What a bitstring test needs of its subject: the binary, the position of
    /// a cursor, and what the dispatch asks of the binary before any field. The
    /// first test of a binary reads its length and, when a clause of the test
    /// reads bytes by address, selects its base; every later test of the same
    /// binary finds both in `state.binary_facts`. A cursor's source is a binary
    /// by construction and is read without asking its kind; any other subject's
    /// read answers a negative length when the subject is not a binary.
    fn read_bitstring_subject(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        subject: SubjectId,
        reads_bytes: bool,
    ) -> Result<(Var, Option<Var>, BinaryFacts), FatalError> {
        let (source, cursor_position) = self.dispatch_bit_source(ctx, plan, state, subject)?;
        let int = self.world.types_mut().int();
        let mut facts = match state.binary_facts.get(&source) {
            Some(facts) => *facts,
            None => {
                let prim = match cursor_position {
                    Some(_) => Prim::BinaryBitLen(source),
                    None => Prim::BitstringBitLen(source),
                };
                let (bit_len, _) = ctx.emit_let(prim);
                ctx.value_types.insert(bit_len, int);
                BinaryFacts { bit_len, base: None }
            }
        };
        if reads_bytes && facts.base.is_none() {
            let (base, _) = ctx.emit_let(Prim::BitstringBase(source));
            ctx.value_types.insert(base, int);
            facts.base = Some(base);
        }
        state.binary_facts.insert(source, facts);
        Ok((source, cursor_position, facts))
    }

    /// Whether some field of `shape` that the dispatch builds is a whole-byte
    /// integer, which is read by a load from the binary's address.
    fn reads_bytes_by_address(
        &self,
        plan: &PatternDispatchPlan<Ty>,
        state: &DispatchState,
        shape: &crate::dispatch_matrix::BitstringShape,
    ) -> bool {
        shape.fields.iter().any(|field_subject| {
            let spec = &plan.bitstring_extraction(*field_subject).spec;
            literal_bit_field(spec).is_some_and(|field| {
                field.whole_byte_integer_width().is_some()
                    && (plan.graph.asks(*field_subject) || state.outcome_reads.contains(field_subject))
            })
        })
    }

    /// The question of whether the first field of `predicate`'s bitstring test
    /// fits, when the subject is a cursor already in hand and the field's width
    /// is a literal. Nothing is emitted to ask it.
    fn first_fit_question(
        &self,
        plan: &PatternDispatchPlan<Ty>,
        state: &DispatchState,
        predicate: &crate::dispatch_matrix::RegionPredicate<Ty>,
    ) -> Option<FitQuestion> {
        let Region::Bitstring(shape) = &predicate.region else {
            return None;
        };
        let first = plan.bitstring_extraction(*shape.fields.first()?);
        let subject = plan.graph.subjects.get(predicate.subject.0 as usize)?;
        let held = state.values.get(&predicate.subject).or_else(|| match subject.source {
            crate::dispatch_matrix::SubjectSource::Input { ordinal } => state.dispatch_inputs.get(ordinal as usize),
            _ => None,
        })?;
        let NativeBoundValue::Transport { shape: cursor, lanes } = held else {
            return None;
        };
        let [source, position] = lanes.as_slice() else {
            return None;
        };
        matches!(self.world.shape(*cursor), ShapeDescr::Cursor { .. }).then_some(())?;
        FitQuestion::of(*source, *position, &first.spec)
    }

    /// The binary a bitstring region reads and the position it starts at: the
    /// source and position of a cursor, or the whole binary the subject is.
    fn dispatch_bit_source(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        subject: SubjectId,
    ) -> Result<(Var, Option<Var>), FatalError> {
        if let NativeBoundValue::Transport { shape, lanes } = self.dispatch_subject_value(ctx, plan, state, subject)?
            && matches!(self.world.shape(*shape), ShapeDescr::Cursor { .. })
            && let [source, position] = lanes.as_slice()
        {
            return Ok((*source, Some(*position)));
        }
        Ok((self.dispatch_subject_var(ctx, plan, state, subject)?, None))
    }

    /// The value of `field` at bit `pos` of `source`, which the caller has seen
    /// fit. An integer field is a raw integer.
    ///
    /// `start` is what the program text says of where the field starts. A
    /// whole-byte integer field that starts a whole number of bytes from the
    /// first bit, or from a cursor's position, is a load from the binary's
    /// address; every other field is read by the runtime.
    fn emit_bit_read(
        &mut self,
        ctx: &mut NativeFnCtx,
        base: Option<Var>,
        source: Var,
        pos: Var,
        start: FieldStart,
        field: &BitMatchField,
    ) -> Result<Var, FatalError> {
        let base_of_subject = || {
            base.ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "a bitstring field is read by address but its subject's base was not selected".to_string(),
                )
            })
        };
        let prim = match (start, field.whole_byte_integer_width()) {
            (FieldStart::Fixed(at), Some(bytes)) if at % 8 == 0 => Prim::BitReadByteInt {
                base: base_of_subject()?,
                byte_offset: (at / 8) as u32,
                bytes,
            },
            (FieldStart::PastCursor(Some(offset)), Some(bytes)) if offset % 8 == 0 => Prim::BitReadByteIntAt {
                base: base_of_subject()?,
                pos,
                bytes,
            },
            _ => Prim::BitReadField {
                source,
                pos,
                field: field.clone(),
            },
        };
        let (value, _) = ctx.emit_let(prim);
        if field.ty.reads_as_integer() {
            let int = self.world.types_mut().int();
            ctx.value_types.insert(value, int);
        }
        Ok(value)
    }

    /// Whether `field` fits at `pos`, and for a field whose width the binary's
    /// bytes decide, where it ends: the one question the runtime answers for
    /// both, so the position is never asked for twice.
    fn emit_bit_fits(
        &mut self,
        ctx: &mut NativeFnCtx,
        source: Var,
        pos: Var,
        bit_len: Var,
        field: &BitMatchField,
    ) -> (Var, Option<Var>) {
        let int = self.world.types_mut().int();
        let bool_ty = self.world.types_mut().bool();
        if field.ty != BitType::Utf8 {
            let (fits, _) = ctx.emit_let(Prim::BitFieldFits {
                pos,
                bit_len,
                field: field.clone(),
            });
            ctx.value_types.insert(fits, bool_ty);
            return (fits, None);
        }
        let (end, _) = ctx.emit_let(Prim::BitFieldEnd {
            source,
            pos,
            field: field.clone(),
        });
        ctx.value_types.insert(end, int);
        let (zero, _) = ctx.emit_let(Prim::Const(Const::Int(0)));
        ctx.value_types.insert(zero, int);
        let (fits, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Ge, end, zero));
        ctx.value_types.insert(fits, bool_ty);
        (fits, Some(end))
    }

    /// Whether a field's fit asks nothing of the binary's length: a bare
    /// `bits` rest, and a field the runtime reads. At the start of a subject
    /// that may not be a binary, only `require_binary` keeps such a field from
    /// fitting a value that is not one.
    fn fit_ignores_length(field: &BitMatchField) -> bool {
        matches!(field.ty, BitType::Utf8 | BitType::Utf16 | BitType::Utf32)
            || (field.ty == BitType::Bits && field.size.is_none())
    }

    /// Leave for `miss` unless `pos` is within the binary. A value that is not
    /// a binary has length -1, which no position is within.
    fn require_binary(&mut self, ctx: &mut NativeFnCtx, pos: Var, bit_len: Var, miss: BlockId) {
        let (within, _) = ctx.emit_let(Prim::BinOp(IrBinOp::Ge, bit_len, pos));
        let bool_ty = self.world.types_mut().bool();
        ctx.value_types.insert(within, bool_ty);
        let next_b = ctx.builder.block(vec![]);
        ctx.set_term(Term::If {
            cond: within,
            then_b: next_b,
            else_b: miss,
            origin: BranchOrigin::ClauseDispatch,
        });
        ctx.current_block = next_b;
    }

    /// The position after a sized `field` that starts at `pos`.
    fn emit_bit_next(&mut self, ctx: &mut NativeFnCtx, source: Var, pos: Var, field: BitMatchField) -> Var {
        let prim = match field.ty {
            BitType::Utf8 => Prim::BitFieldEnd { source, pos, field },
            _ => Prim::BitFieldNext { pos, field },
        };
        let (next, _) = ctx.emit_let(prim);
        let int = self.world.types_mut().int();
        ctx.value_types.insert(next, int);
        next
    }

    /// A field's size is a literal, or an earlier field this same test already
    /// extracted — `<<len, payload :: binary-size(len)>>`.
    fn lower_dispatch_bit_size(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        field: &crate::dispatch_matrix::BitstringFieldShape,
        miss: BlockId,
    ) -> Result<Option<BitSizeIr>, FatalError> {
        use crate::dispatch_matrix::BitstringFieldSize;
        Ok(match &field.size {
            None => None,
            Some(BitstringFieldSize::Literal(bits)) => Some(BitSizeIr::Literal(*bits)),
            Some(BitstringFieldSize::Binding(subject)) => {
                Some(BitSizeIr::Var(self.dispatch_subject_var(ctx, plan, state, *subject)?))
            }
            // A size bound before the pattern began arrives as a PIN, the same
            // way a pinned value does.
            Some(BitstringFieldSize::Pinned(pinned)) => Some(BitSizeIr::Var(self.dispatch_pinned_var(state, *pinned)?)),
            Some(BitstringFieldSize::PinnedByteSize(pinned)) => {
                Some(BitSizeIr::ByteSizeOf(self.dispatch_pinned_var(state, *pinned)?))
            }
            // A size written as an expression is a guard's value; a guard that
            // fails leaves through the bitstring's own miss block.
            Some(BitstringFieldSize::Guard(guard)) => {
                let expr = plan.guards.get(guard.0 as usize).ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("bitstring size guard {:?} is out of bounds", guard),
                    )
                })?;
                let mut fail = Some(miss);
                Some(BitSizeIr::Var(
                    self.lower_guard_expr(ctx, plan, state, expr, &mut fail)?,
                ))
            }
        })
    }

    /// The one runtime word a subject denotes.
    ///
    /// A tuple's arity, its field projections and a type test all read a subject
    /// in the lane form its caller delivered. What is left are the questions
    /// that want the whole value and cannot be decomposed: a pinned equality, a
    /// guard, and the map, list and bitstring regions. Those build the value
    /// here, at the question that asks for it, and keep it for the rest of this
    /// branch.
    fn dispatch_subject_var(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        subject: SubjectId,
    ) -> Result<Var, FatalError> {
        let var = match self.dispatch_subject_value(ctx, plan, state, subject)? {
            NativeBoundValue::Runtime(var) => return Ok(*var),
            NativeBoundValue::Absent => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!("dispatch subject {subject:?} carries no runtime value"),
                ));
            }
            NativeBoundValue::Transport { shape, lanes } => {
                let (shape, lanes) = (*shape, lanes.clone());
                let var = self.materialize_transport_value(ctx, shape, &lanes)?;
                // A cursor stays a cursor, so a later bit question still reads
                // from its position; the binary built for it is remembered per
                // block by `make_cursor_whole`.
                if matches!(self.world.shape(shape), ShapeDescr::Cursor { .. }) {
                    return Ok(var);
                }
                var
            }
        };
        state.values.insert(subject, NativeBoundValue::Runtime(var));
        Ok(var)
    }

    /// What a subject holds, in whatever form it already has.
    ///
    /// A tuple field of a lane-form subject is a view over lanes the entry
    /// already holds, so it costs nothing. Every other projection reads through
    /// a runtime value and emits the prim that does so.
    fn dispatch_subject_value<'s>(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &'s mut DispatchState,
        subject: SubjectId,
    ) -> Result<&'s NativeBoundValue, FatalError> {
        self.bind_dispatch_subject(ctx, plan, state, subject)?;
        Ok(&state.values[&subject])
    }

    /// Records the subject's value in `state.values` unless it is already
    /// there.
    fn bind_dispatch_subject(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &mut DispatchState,
        subject: SubjectId,
    ) -> Result<(), FatalError> {
        if state.values.contains_key(&subject) {
            return Ok(());
        }
        let Some(subject_data) = plan.graph.subjects.get(subject.0 as usize) else {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("dispatch subject {:?} is out of bounds", subject),
            ));
        };
        let value = match &subject_data.source {
            crate::dispatch_matrix::SubjectSource::Input { ordinal } => {
                state.dispatch_inputs.get(*ordinal as usize).cloned().ok_or_else(|| {
                    incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("dispatch input {} has no native entry param", ordinal),
                    )
                })?
            }
            crate::dispatch_matrix::SubjectSource::Projection(projection) => match &projection.kind {
                crate::dispatch_matrix::ProjectionKind::TupleField(index) => {
                    let source = self.dispatch_subject_value(ctx, plan, state, projection.source)?;
                    match self.transport_tuple_field(source, *index as usize)? {
                        Some(field) => field,
                        None => {
                            let tuple = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                            let (var, _) = ctx.emit_let(Prim::TupleField(tuple, *index));
                            NativeBoundValue::Runtime(var)
                        }
                    }
                }
                crate::dispatch_matrix::ProjectionKind::StructField(field) => {
                    let record = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let (var, _) = ctx.emit_let(Prim::StructField(record, field.clone()));
                    NativeBoundValue::Runtime(var)
                }
                crate::dispatch_matrix::ProjectionKind::ListHead => {
                    let list = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let (var, _) = ctx.emit_let(Prim::ListHead(list));
                    NativeBoundValue::Runtime(var)
                }
                crate::dispatch_matrix::ProjectionKind::ListTail => {
                    let list = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let (var, _) = ctx.emit_let(Prim::ListTail(list));
                    NativeBoundValue::Runtime(var)
                }
                crate::dispatch_matrix::ProjectionKind::MapValue { key } => {
                    let map = self.dispatch_subject_var(ctx, plan, state, projection.source)?;
                    let key = self.dispatch_key_var(ctx, plan, state, key)?;
                    let (var, _) = ctx.emit_let(Prim::MapGet(map, key));
                    NativeBoundValue::Runtime(var)
                }
                crate::dispatch_matrix::ProjectionKind::BitstringField(index) => {
                    // `lower_bitstring_region` records every field it extracts
                    // under its own subject, and the lookup at the top of this
                    // function returns it. Arriving here means the projection
                    // was asked for without the test that binds it having run.
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!("bitstring field projection {index:?} was read before its pattern test bound it"),
                    ));
                }
            },
        };
        self.record_projected_type(ctx, plan, state, subject, &value);
        state.values.insert(subject, value);
        Ok(())
    }

    /// A list head a dispatch reads carries the type its plan's inputs prove
    /// for it, so the compare or arithmetic that consumes it sees what the
    /// dispatch already knows. A cell is projected only on a cons edge, so the
    /// head exists. The types come from the plan's inputs and not from the
    /// edges' refinements, so only a projection whose source is a list is
    /// typed: a struct field read through the same types asks a tag the inputs
    /// do not prove, and a head of `none` proves nothing for the value that is
    /// there.
    fn record_projected_type(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &DispatchState,
        subject: SubjectId,
        value: &NativeBoundValue,
    ) {
        let (NativeBoundValue::Runtime(var), crate::dispatch_matrix::SubjectSource::Projection(projection)) =
            (value, &plan.subject(subject))
        else {
            return;
        };
        if !matches!(projection.kind, crate::dispatch_matrix::ProjectionKind::ListHead) {
            return;
        }
        let ty = project_subject(self.world.types_mut(), plan, &state.roots, &[], subject);
        if ty == self.world.types_mut().none() {
            return;
        }
        ctx.value_types.entry(*var).or_insert(ty);
    }

    fn dispatch_pinned_var(
        &mut self,
        state: &DispatchState,
        pinned: crate::dispatch_matrix::PinnedValueId,
    ) -> Result<Var, FatalError> {
        state.bindings.pinned.get(pinned.0 as usize).copied().ok_or_else(|| {
            incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("dispatch pinned operand {:?} is out of bounds", pinned),
            )
        })
    }

    /// The operands a plan whose inputs are its arguments needs. Every pin such
    /// a plan carries was bound before its patterns began and arrives as one of
    /// those arguments; a pin without one is an undefined name the entry
    /// planner already refused, so reaching here means the plan never went
    /// through it. A pin is compared whole, so its operand is one runtime word.
    fn lower_argument_bindings(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        inputs: &[NativeBoundValue],
    ) -> Result<DispatchBindings<Var>, FatalError> {
        let prepared = plan
            .prepared_keys
            .iter()
            .map(|key| lower_dispatch_const(ctx, &self.atoms, self.world.types_mut(), key))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(DispatchBindings {
            pinned: plan
                .pinned
                .iter()
                .map(|pin| {
                    pin.input
                        .and_then(|input| inputs.get(input as usize))
                        .and_then(NativeBoundValue::runtime_word)
                        .ok_or_else(|| {
                            incomplete_native_program(
                                self.telemetry,
                                self.root_id,
                                format!("dispatch pin `{}` has no runtime argument operand", pin.name),
                            )
                        })
                })
                .collect::<Result<Vec<_>, _>>()?,
            prepared,
        })
    }

    fn dispatch_key_var(
        &mut self,
        ctx: &mut NativeFnCtx,
        plan: &PatternDispatchPlan<Ty>,
        state: &DispatchState,
        key: &ComparisonValue,
    ) -> Result<Var, FatalError> {
        let key = match key {
            ComparisonValue::Pinned(pinned) => return self.dispatch_pinned_var(state, *pinned),
            ComparisonValue::Const(key) => key,
            ComparisonValue::Subject(_) => {
                return Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    "a map key question compares against an earlier subject".to_string(),
                ));
            }
        };
        if let Some(id) = plan.prepared_key_id(key) {
            return state.bindings.prepared.get(id.0 as usize).copied().ok_or_else(|| {
                incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!("dispatch prepared operand {:?} is missing from its owning plan", id),
                )
            });
        }
        lower_dispatch_const(ctx, &self.atoms, self.world.types_mut(), key)
    }

    fn atom_id(&self, name: &str) -> u32 {
        self.atoms.id_of(name).expect("required atom should be interned")
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
        let value = env.value(value_id).unwrap_or_else(|| {
            panic!(
                "native lowering invariant failed: backend value {:?} in executable {:?} must be bound before runtime use",
                value_id, executable.key
            )
        });
        let ty = executable.abi.materialized.value_types.get(&value_id).copied();
        self.materialize_native_value(ctx, ty, value).unwrap_or_else(|error| {
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
        values: impl IntoIterator<Item = ValueId>,
    ) -> Vec<Var> {
        values
            .into_iter()
            .map(|value| self.env_runtime_var(ctx, executable, env, value))
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
                ctx.emit_let(Prim::MakeList(Vec::new(), None, None)).0
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
            ctx.value_types.entry(var).or_insert(ty);
        }
        Ok(var)
    }

    /// The two lanes a value travels in when its layout is a cursor: a cursor
    /// passed on as is, or a whole binary, which is a cursor at position zero.
    fn cursor_lanes(&mut self, ctx: &mut NativeFnCtx, value: &NativeBoundValue) -> Result<(Var, Var), FatalError> {
        match value {
            NativeBoundValue::Transport { shape, lanes }
                if matches!(self.world.shape(*shape), ShapeDescr::Cursor { .. }) =>
            {
                match lanes.as_slice() {
                    [source, position] => Ok((*source, *position)),
                    _ => Err(FatalError),
                }
            }
            NativeBoundValue::Runtime(source) => {
                let int = self.world.types_mut().int();
                let (position, _) = ctx.emit_let(Prim::Const(Const::Int(0)));
                ctx.value_types.insert(position, int);
                Ok((*source, position))
            }
            NativeBoundValue::Absent | NativeBoundValue::Transport { .. } => Err(FatalError),
        }
    }

    /// The bitstring a cursor stands for: the source when the position is zero,
    /// otherwise the suffix stub the runtime allocates. A cursor made whole in
    /// this block is not made again in it.
    fn make_cursor_whole(&mut self, ctx: &mut NativeFnCtx, source: Var, position: Var) -> Var {
        if let Some((block, whole)) = ctx.whole_cursors.get(&(source, position))
            && *block == ctx.current_block
        {
            return *whole;
        }
        let rest = BitMatchField {
            ty: BitType::Bits,
            size: None,
            endian: crate::ast::Endian::Big,
            signed: false,
            unit: None,
            is_last: true,
        };
        let (whole, _) = ctx.emit_let(Prim::BitReadField {
            source,
            pos: position,
            field: rest,
        });
        if let Some(ty) = ctx.value_types.get(&source).copied() {
            ctx.value_types.insert(whole, ty);
        }
        ctx.whole_cursors.insert((source, position), (ctx.current_block, whole));
        whole
    }

    fn materialize_transport_value(
        &mut self,
        ctx: &mut NativeFnCtx,
        shape: ShapeId,
        lanes: &[Var],
    ) -> Result<Var, FatalError> {
        match self.world.shape(shape) {
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
            ShapeDescr::Cursor { .. } => {
                let [source, position] = lanes else {
                    return Err(incomplete_native_program(
                        self.telemetry,
                        self.root_id,
                        format!(
                            "native cursor {shape:?} has {} lanes, not two, in {:?}",
                            lanes.len(),
                            ctx.origin
                        ),
                    ));
                };
                Ok(self.make_cursor_whole(ctx, *source, *position))
            }
            ShapeDescr::Tuple(fields) => {
                let mut vars = Vec::with_capacity(fields.len());
                for field in self.transport_field_views(shape, lanes)? {
                    vars.push(self.materialize_native_value(ctx, None, &field)?);
                }
                Ok(ctx.emit_let(Prim::MakeTuple(vars)).0)
            }
            ShapeDescr::Callable(callable) => {
                let descr = self.world.callable(*callable);
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

    fn transport_tuple_field(
        &self,
        value: &NativeBoundValue,
        index: usize,
    ) -> Result<Option<NativeBoundValue>, FatalError> {
        let NativeBoundValue::Transport { shape, lanes, .. } = value else {
            return Ok(None);
        };
        if self.world.tuple_arity(*shape).is_none() {
            return Ok(None);
        }
        let field = self
            .transport_field_spans(*shape, lanes)?
            .nth(index)
            .ok_or(FatalError)?;
        Ok(Some(self.transport_field_view(lanes, field)?))
    }

    fn direct_callable_captures(
        &self,
        value: &NativeBoundValue,
    ) -> Result<Option<(FunctionId, Vec<NativeBoundValue>)>, FatalError> {
        let NativeBoundValue::Transport { shape, lanes } = value else {
            return Ok(None);
        };
        let ShapeDescr::Callable(callable) = self.world.shape(*shape) else {
            return Ok(None);
        };
        let descr = self.world.callable(*callable);
        let Some(function) = descr.function else {
            return Ok(None);
        };
        Ok(Some((function, self.transport_field_views(*shape, lanes)?)))
    }

    /// The capture lanes a direct closure call hands its target.
    ///
    /// Whether the call IS direct, and how many captures it promised to hand
    /// over, were decided when the edge was minted, so this only emits what
    /// that answer promised. A callee value that turns out not to carry those
    /// captures is a broken plan, not a reason to call through the seam
    /// instead.
    fn direct_closure_capture_lanes(
        &mut self,
        ctx: &mut NativeFnCtx,
        caller: &BackendExecutable,
        callee: ValueId,
        value: Option<&NativeBoundValue>,
        target: &ExecutableKey,
        capture_inputs_end: usize,
    ) -> Result<Vec<Var>, FatalError> {
        let target = self
            .program
            .executable_index(target, self.world.types())
            .ok_or(FatalError)?;
        let executable = Rc::clone(&self.program.executables()[target]);
        if let Some(value) = value
            && let Some((function, captures)) = self.direct_callable_captures(value)?
        {
            if function != executable.key.activation.function || captures.len() != capture_inputs_end {
                return Err(FatalError);
            }
            let mut lanes = Vec::new();
            for input in executable
                .abi
                .semantic_inputs
                .iter()
                .filter(|input| input.semantic_index < capture_inputs_end)
            {
                let capture = captures.get(input.semantic_index).ok_or(FatalError)?;
                self.encode_runtime_value_for_layout(ctx, caller, None, capture, &input.layout, &mut lanes)?;
            }
            return Ok(lanes);
        }
        if executable
            .abi
            .semantic_inputs
            .iter()
            .any(|input| input.semantic_index < capture_inputs_end && !input.layout.reprs.is_empty())
        {
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
        Ok(Vec::new())
    }

    /// Encodes each field of a tuple value into its layout's lanes. Field
    /// layouts are read by index because encoding needs `&mut self` between
    /// fields.
    fn encode_tuple_fields(
        &mut self,
        ctx: &mut NativeFnCtx,
        executable: &BackendExecutable,
        value: &NativeBoundValue,
        shape: ShapeId,
        arity: usize,
        lanes: &mut Vec<Var>,
    ) -> Result<(), FatalError> {
        let tuple_fields = self.tuple_field_values_for_encoding(ctx, value, arity)?;
        for (index, field) in tuple_fields.iter().enumerate() {
            let field_layout = self.field_layout(shape, index);
            self.encode_transport_layout(ctx, executable, None, field, field_layout, lanes)?;
        }
        Ok(())
    }

    /// The layout of one field of a tuple or the capture of a callable. Shapes
    /// are interned and never change, so a caller that must call `&mut self`
    /// between fields reads each layout when it needs it.
    fn field_layout(&self, shape: ShapeId, index: usize) -> TransportLayout {
        self.world.field_layouts(shape).expect("a composite shape has fields")[index]
    }

    fn tuple_field_values_for_encoding(
        &mut self,
        ctx: &mut NativeFnCtx,
        value: &NativeBoundValue,
        arity: usize,
    ) -> Result<Vec<NativeBoundValue>, FatalError> {
        if let NativeBoundValue::Transport {
            shape: value_shape,
            lanes,
            ..
        } = value
            && self.world.tuple_arity(*value_shape) == Some(arity)
        {
            return self.transport_field_views(*value_shape, lanes);
        }
        let tuple = self.materialize_native_value(ctx, None, value)?;
        Ok((0..arity)
            .map(|index| {
                let (var, _) = ctx.emit_let(Prim::TupleField(tuple, index as u32));
                NativeBoundValue::Runtime(var)
            })
            .collect())
    }

    /// Every field of a lane-form value: a tuple's fields, or a callable's
    /// captures, which occupy their lanes the same way.
    fn transport_field_views(&self, shape: ShapeId, lanes: &[Var]) -> Result<Vec<NativeBoundValue>, FatalError> {
        self.transport_field_spans(shape, lanes)?
            .map(|field| self.transport_field_view(lanes, field))
            .collect()
    }

    /// The fields of a lane-form value with the lane span each occupies,
    /// after checking that the lanes are exactly the shape's width.
    fn transport_field_spans(
        &self,
        shape: ShapeId,
        lanes: &[Var],
    ) -> Result<impl Iterator<Item = (TransportLayout, std::ops::Range<usize>)> + '_, FatalError> {
        if lanes.len() != self.world.shape_width(shape) {
            return Err(incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!(
                    "native transport field view for {shape:?} has {} lanes, but shape width is {}",
                    lanes.len(),
                    self.world.shape_width(shape),
                ),
            ));
        }
        self.world.field_spans(shape).ok_or_else(|| {
            incomplete_native_program(
                self.telemetry,
                self.root_id,
                format!("native transport field view for {shape:?}, which has no fields"),
            )
        })
    }

    /// One field of a lane-form value: a runtime word, nothing, or the lane
    /// slice of a nested tuple or callable.
    fn transport_field_view(
        &self,
        lanes: &[Var],
        (field, span): (TransportLayout, std::ops::Range<usize>),
    ) -> Result<NativeBoundValue, FatalError> {
        let field_lanes = lanes.get(span).ok_or(FatalError)?;
        let first_lane = || field_lanes.first().copied().ok_or(FatalError);
        if field.carrier.is_value_ref() {
            return Ok(NativeBoundValue::Runtime(first_lane()?));
        }
        Ok(match self.world.shape(field.structural) {
            ShapeDescr::Nothing => NativeBoundValue::Absent,
            ShapeDescr::Lane(_) => NativeBoundValue::Runtime(first_lane()?),
            ShapeDescr::Tuple(_) | ShapeDescr::Callable(_) | ShapeDescr::Cursor { .. } => NativeBoundValue::Transport {
                shape: field.structural,
                lanes: field_lanes.to_vec(),
            },
        })
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
        match self.world.shape(shape) {
            ShapeDescr::Nothing => Ok(()),
            ShapeDescr::Lane(lane) => {
                let ty = value_id
                    .and_then(|value_id| executable.abi.materialized.value_types.get(&value_id).copied())
                    .unwrap_or_else(|| self.world.lane(*lane).ty);
                lanes.push(self.materialize_native_value(ctx, Some(ty), value)?);
                Ok(())
            }
            ShapeDescr::Cursor { .. } => {
                let (source, position) = self.cursor_lanes(ctx, value)?;
                lanes.extend([source, position]);
                Ok(())
            }
            ShapeDescr::Tuple(fields) => {
                let arity = fields.len();
                self.encode_tuple_fields(ctx, executable, value, shape, arity, lanes)
            }
            ShapeDescr::Callable(callable) => {
                let (function_id, capture_count) = {
                    let descr = self.world.callable(*callable);
                    (descr.function, descr.capture_layouts.len())
                };
                let descriptor_lanes = self.world.shape_lane_ids(shape);
                if function_id.is_none()
                    && let [lane] = descriptor_lanes.as_slice()
                {
                    let ty = self.world.lane(*lane).ty;
                    lanes.push(self.materialize_native_value(ctx, Some(ty), value)?);
                    return Ok(());
                }
                if let Some((function, captures)) = self.direct_callable_captures(value)? {
                    if function_id != Some(function) || captures.len() != capture_count {
                        return Err(FatalError);
                    }
                    for (index, capture) in captures.iter().enumerate() {
                        let layout = self.field_layout(shape, index);
                        self.encode_transport_layout(ctx, executable, None, capture, layout, lanes)?;
                    }
                    return Ok(());
                }
                if let NativeBoundValue::Runtime(var) = value {
                    if function_id.is_none() {
                        return Err(incomplete_native_program(
                            self.telemetry,
                            self.root_id,
                            format!(
                                "native cannot project captures out of a callable that names no function in {:?}",
                                ctx.origin
                            ),
                        ));
                    }
                    for index in 0..capture_count {
                        let layout = self.field_layout(shape, index);
                        if self.world.layout_width(layout) == 0 {
                            continue;
                        }
                        let (capture, _) = ctx.emit_let(Prim::ClosureCapture {
                            closure: *var,
                            index: index as u32,
                        });
                        self.encode_transport_layout(
                            ctx,
                            executable,
                            None,
                            &NativeBoundValue::Runtime(capture),
                            layout,
                            lanes,
                        )?;
                    }
                    return Ok(());
                }
                Err(incomplete_native_program(
                    self.telemetry,
                    self.root_id,
                    format!(
                        "native attempted to encode callable shape {:?} ({:?}) for value {:?} from {:?} in {:?}; callable values must be supplied by matching transport lanes or a published value seam",
                        shape,
                        self.world.callable(*callable),
                        value_id,
                        value,
                        ctx.origin,
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
            .value(value_id)
            .ok_or_else(|| missing_backend_value(self.root_id, value_id))?;
        self.encode_transport_layout(ctx, executable, Some(value_id), local, layout, lanes)
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
        match self.world.shape(shape) {
            ShapeDescr::Tuple(fields) => {
                let arity = fields.len();
                self.encode_tuple_fields(ctx, executable, value, shape, arity, lanes)
            }
            ShapeDescr::Callable(_) => self.encode_runtime_value(ctx, executable, value_id, value, shape, lanes),
            ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Cursor { .. } => {
                self.encode_runtime_value(ctx, executable, value_id, value, shape, lanes)
            }
        }
    }
}

/// The clause whose body is the entry, when the entry is a clause body.
fn clause_entered_at(executable: &BackendExecutable, entry: ControlEntryId) -> Option<&BackendClause> {
    let BackendBody::Clauses { clauses, .. } = &executable.body else {
        return None;
    };
    clauses.iter().find(|clause| clause.entry == entry)
}

/// The layout an entry's parameter arrives in. Every parameter a decision, a
/// receive or a raise hands has one, so a missing layout is a defect upstream.
fn entry_param_layout(executable: &BackendExecutable, value: ValueId) -> &BackendValueLayout {
    executable
        .abi
        .value_layouts
        .get(&value)
        .unwrap_or_else(|| panic!("entry parameter {value:?} has no layout"))
}

fn same_entry_capture_contract(left: &BackendEntryCapture, right: &BackendEntryCapture) -> bool {
    left.value == right.value && left.layout == right.layout
}

/// A delivered call that is the extern behind its callee.
/// How one executable's entries become native code. Something outside a
/// function can arrive in it by a call from elsewhere, by a call's return, or
/// from the runtime. An entry that only its own function's direct transfers
/// reach is a block of that function; every other entry is a function of its
/// own, emitted once.
#[derive(Default)]
struct EntryFns {
    ids: HashMap<ControlEntryId, FnId>,
    pending: VecDeque<(ControlEntryId, FnId)>,
    blocks: HashSet<ControlEntryId>,
}

/// The machine function an entry belongs to.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Home {
    /// The executable's own function: its dispatch and its clause bodies.
    Executable,
    /// The function the named entry begins.
    Entry(ControlEntryId),
}

/// Each entry's incoming transfers, and the homes decided so far.
struct EntryHomes {
    incoming: HashMap<ControlEntryId, Vec<(ControlEntryId, EntryTransfer)>>,
    homes: HashMap<ControlEntryId, Home>,
    deciding: HashSet<ControlEntryId>,
}

impl EntryHomes {
    fn new(entries: &[BackendEntry], clauses: &[BackendClause], continues_here: impl Fn(&BackendTail) -> bool) -> Self {
        let mut incoming: HashMap<ControlEntryId, Vec<(ControlEntryId, EntryTransfer)>> = HashMap::default();
        for (source, entry) in entries.iter().enumerate() {
            let source = ControlEntryId::from_u32(source as u32);
            let continues = continues_here(&entry.tail);
            for (target, transfer) in entry.tail.transfers() {
                let transfer = match transfer {
                    EntryTransfer::CallReturn if continues => EntryTransfer::Direct,
                    other => other,
                };
                incoming.entry(target).or_default().push((source, transfer));
            }
        }
        let homes = clauses.iter().map(|clause| (clause.entry, Home::Executable)).collect();
        Self {
            incoming,
            homes,
            deciding: HashSet::default(),
        }
    }

    /// A function of its own unless every transfer that arrives is a direct
    /// transfer from one and the same function, which then holds it as a block.
    fn home(&mut self, entry: ControlEntryId) -> Home {
        if let Some(home) = self.homes.get(&entry) {
            return *home;
        }
        assert!(
            self.deciding.insert(entry),
            "entry {entry:?} is reached from itself by direct transfers alone; only a self tail call may close a loop"
        );
        let arrivals = self.incoming.get(&entry).cloned().unwrap_or_default();
        let origins: Vec<Option<Home>> = arrivals
            .iter()
            .map(|(source, transfer)| match transfer {
                EntryTransfer::Direct => Some(self.home(*source)),
                EntryTransfer::CallReturn | EntryTransfer::Runtime => None,
            })
            .collect();
        let home = match origins.split_first() {
            Some((Some(first), rest)) if rest.iter().all(|other| *other == Some(*first)) => *first,
            _ => Home::Entry(entry),
        };
        self.deciding.remove(&entry);
        self.homes.insert(entry, home);
        home
    }
}

impl EntryFns {
    /// `continues_here` says which tails are calls lowered in this function
    /// instead of returning to it: their resume entry is reached by a direct
    /// transfer like any other.
    fn for_executable(
        entries: &[BackendEntry],
        clauses: &[BackendClause],
        continues_here: impl Fn(&BackendTail) -> bool,
    ) -> Self {
        let mut homes = EntryHomes::new(entries, clauses, continues_here);
        let blocks = (0..entries.len() as u32)
            .map(ControlEntryId::from_u32)
            .filter(|entry| homes.home(*entry) != Home::Entry(*entry))
            .collect();
        Self {
            blocks,
            ..Self::default()
        }
    }

    fn is_block(&self, entry: ControlEntryId) -> bool {
        self.blocks.contains(&entry)
    }

    fn reference(&mut self, module: &mut ModuleBuilder, entry: ControlEntryId) -> FnId {
        assert!(
            !self.is_block(entry),
            "entry {entry:?} is a block of the function that reaches it, never a function of its own"
        );
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
    let mut graph: HashMap<FnId, HashSet<FnId>> = HashMap::default();
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
                Term::Try { handler, .. } => {
                    entry.insert(*handler);
                }
                Term::TailCallClosure { .. }
                | Term::Goto(..)
                | Term::If { .. }
                | Term::Return(_)
                | Term::ReturnLanes(_)
                | Term::Raise { .. }
                | Term::Reraise { .. }
                | Term::RaiseUndefined { .. }
                | Term::Unreachable => {}
            }
        }
    }

    let scc_of = {
        let mut index_counter = 0usize;
        let mut stack = Vec::new();
        let mut on_stack = HashSet::default();
        let mut index = HashMap::default();
        let mut lowlink = HashMap::default();
        let mut scc_of = HashMap::default();
        let mut scc_count = 0usize;

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
                for neighbor in neighbors.iter().copied() {
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

        for function in module.fns.iter().map(|function| &function.id) {
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

type NativeBoundValue = BoundValue<Var>;

/// One lowering of a dispatch graph: the plan, how a leaf is lowered, and the
/// joins reached and not yet lowered.
struct DispatchWalk<'w, L> {
    plan: &'w PatternDispatchPlan<Ty>,
    origin: BranchOrigin,
    lower_leaf: &'w mut L,
    joins: DispatchJoins<BlockId, DispatchState>,
}

/// Share the variables that carry `values`, each once: a value passed or
/// stored in more than one place gains its second holder once, and a mark,
/// once set, is never cleared.
fn share_native_values(ctx: &mut NativeFnCtx, env: &ValueEnv, values: impl IntoIterator<Item = ValueId>) {
    let mut shared = HashSet::default();
    for value in values {
        let vars = match env.value(value) {
            Some(NativeBoundValue::Runtime(var)) => std::slice::from_ref(var),
            Some(NativeBoundValue::Transport { lanes, .. }) => lanes.as_slice(),
            Some(NativeBoundValue::Absent) | None => &[],
        };
        for var in vars {
            if shared.insert(*var) {
                ctx.emit_let(Prim::Share(*var));
            }
        }
    }
}

#[derive(Default, Clone)]
struct ValueEnv {
    values: ValueMap<NativeBoundValue>,
}

impl ValueEnv {
    fn insert(&mut self, value: ValueId, bound: NativeBoundValue) {
        self.values.insert(value, bound);
    }

    fn value(&self, value: ValueId) -> Option<&NativeBoundValue> {
        self.values.get(&value)
    }

    fn runtime_var(&self, value: ValueId) -> Option<Var> {
        self.value(value).and_then(NativeBoundValue::runtime_word)
    }
}

fn native_block_param_reprs(
    world: &mut World,
    fn_ir: &crate::fz_ir::FnIr,
    value_types: &HashMap<Var, Ty>,
) -> HashMap<Var, AbiValueRepr> {
    let mut reprs = HashMap::default();
    for block in &fn_ir.blocks {
        for param in &block.params {
            let ty = value_types
                .get(param)
                .copied()
                .unwrap_or_else(|| world.types_mut().any());
            reprs.insert(*param, AbiValueRepr::for_ty(world, ty));
        }
    }
    reprs
}

/// What a region question answered.
///
/// A question a subject's transport form already settles has no runtime cost
/// and no branch: only the surviving child is lowered.
#[derive(Clone, Copy)]
enum DispatchAnswer {
    Static(bool),
    Runtime(Var),
}

/// What a region question left behind.
enum RegionOutcome {
    /// A yes or no, for the caller to branch on.
    Answer(DispatchAnswer),
    /// The question has already branched: control is in the block where it
    /// matched, and every way it can miss leads to `missed`, except that the
    /// first field not fitting leads to `unfit` when the question of that fit
    /// is one a later clause may ask again. What it extracted is defined where
    /// it matched, so it needs no join to reach the matched side.
    Matched { missed: BlockId, unfit: Option<Unfit> },
}

impl DispatchAnswer {
    /// Both answers, with the settled side folded away rather than emitted as a
    /// constant to combine against.
    fn and(self, ctx: &mut NativeFnCtx, other: Self) -> Self {
        match (self, other) {
            (Self::Static(false), _) | (_, Self::Static(false)) => Self::Static(false),
            (Self::Static(true), answer) | (answer, Self::Static(true)) => answer,
            (Self::Runtime(left), Self::Runtime(right)) => {
                Self::Runtime(ctx.emit_let(Prim::BinOp(IrBinOp::And, left, right)).0)
            }
        }
    }

    /// Either answer, folded the same way.
    fn or(self, ctx: &mut NativeFnCtx, other: Self) -> Self {
        match (self, other) {
            (Self::Static(true), _) | (_, Self::Static(true)) => Self::Static(true),
            (Self::Static(false), answer) | (answer, Self::Static(false)) => answer,
            (Self::Runtime(left), Self::Runtime(right)) => {
                Self::Runtime(ctx.emit_let(Prim::BinOp(IrBinOp::Or, left, right)).0)
            }
        }
    }
}

#[derive(Clone)]
struct DispatchState {
    dispatch_inputs: Vec<NativeBoundValue>,
    forwarded_args: Vec<Var>,
    bindings: DispatchBindings<Var>,
    /// What the plan's inputs are proven to be; an input without one is `any`.
    roots: Vec<Ty>,
    values: HashMap<SubjectId, NativeBoundValue>,
    /// The subjects the winning outcome reads, beyond what the decision asks.
    /// A bitstring field outside both is checked for fit and never built.
    outcome_reads: Vec<SubjectId>,
    /// What the dispatch has learned of each binary a bitstring test has read,
    /// by the variable that holds the binary. The reads sit in the block where
    /// the first test begins, which dominates every clause that tests the same
    /// binary after it, so the next clause reuses them rather than asking again.
    binary_facts: HashMap<Var, BinaryFacts>,
    /// The fit questions this arrival has already answered, whether the answer
    /// was yes or no. Both answers are facts of the arrival: a later clause
    /// that begins with the same question needs no test when the answer was
    /// yes, and is not reached at all when it was no.
    fit_answers: HashMap<FitQuestion, bool>,
    /// The first field of a bitstring test, read where it fits, by the question
    /// of its fitting: a later clause that begins with the same field takes
    /// the value rather than reading it again.
    field_reads: Vec<FieldRead>,
}

/// Whether a field of a known width fits where a cursor stands: the binary the
/// cursor reads, the position it stands at, and the width in bits.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
struct FitQuestion {
    source: Var,
    position: Var,
    bits: u64,
}

impl FitQuestion {
    /// The question of `spec`'s field fitting at `position` of `source`, when
    /// the field's width is known without running the program.
    fn of(source: Var, position: Var, spec: &crate::dispatch_matrix::BitstringFieldShape) -> Option<Self> {
        let bits = literal_bit_field(spec)?.static_bits()?;
        Some(Self { source, position, bits })
    }
}

/// `spec` as a field to match, when its size is absent or a literal.
fn literal_bit_field(spec: &crate::dispatch_matrix::BitstringFieldShape) -> Option<BitMatchField> {
    use crate::dispatch_matrix::BitstringFieldSize;
    let size = match &spec.size {
        None => None,
        Some(BitstringFieldSize::Literal(bits)) => Some(BitSizeIr::Literal(*bits)),
        Some(_) => return None,
    };
    Some(BitMatchField {
        ty: spec.runtime_kind(),
        size,
        endian: spec.endian,
        signed: spec.signed,
        unit: spec.unit,
        is_last: false,
    })
}

/// A field read where it fits: what the bits are read as, and the variable
/// that holds the value. The width is the question's; the size a pattern
/// spells for it, or leaves to the type's default, does not change the value.
#[derive(Clone, Copy, Debug, PartialEq)]
struct FieldRead {
    question: FitQuestion,
    ty: BitType,
    endian: crate::ast::Endian,
    signed: bool,
    var: Var,
}

impl FieldRead {
    fn of(question: FitQuestion, field: &BitMatchField, var: Var) -> Self {
        Self {
            question,
            ty: field.ty,
            endian: field.endian,
            signed: field.signed,
            var,
        }
    }

    fn is_of(&self, question: FitQuestion, field: &BitMatchField) -> bool {
        self.question == question && self.ty == field.ty && self.endian == field.endian && self.signed == field.signed
    }
}

/// The path out of a bitstring test when its first field does not fit,
/// together with the question that failed.
struct Unfit {
    block: BlockId,
    question: FitQuestion,
}

/// What a bitstring test asks of its binary before any field: how many bits it
/// has, which is -1 for a value that is not a binary, and, once a clause reads
/// bytes by address, where those bytes start. The address names bytes the
/// process's heap may move, and the heap moves only when the scheduler
/// collects at the end of a quantum. A dispatch is `Goto` and `If` blocks with
/// no call, so the address is good for every clause of one dispatch, whatever
/// its guards and field reads allocate.
#[derive(Clone, Copy, PartialEq)]
struct BinaryFacts {
    bit_len: Var,
    base: Option<Var>,
}

/// A join keeps the cached values and binary facts every arrival holds. A
/// cached variable was made in a block that dominates the arrival it was
/// cached on, so one every arrival holds dominates the join. Nothing else in
/// a state varies between arrivals.
impl ArrivalState for DispatchState {
    fn meet(arrivals: Vec<Self>) -> Self {
        let mut arrivals = arrivals.into_iter();
        let mut met = arrivals.next().expect("a join is reached by an arrival");
        for other in arrivals {
            met.values
                .retain(|subject, value| other.values.get(subject) == Some(value));
            met.binary_facts
                .retain(|binary, facts| other.binary_facts.get(binary) == Some(facts));
            met.fit_answers
                .retain(|question, answer| other.fit_answers.get(question) == Some(answer));
            met.field_reads.retain(|read| other.field_reads.contains(read));
        }
        met
    }
}

impl DispatchState {
    fn new(dispatch_inputs: Vec<NativeBoundValue>, forwarded_args: Vec<Var>, bindings: DispatchBindings<Var>) -> Self {
        Self {
            dispatch_inputs,
            forwarded_args,
            bindings,
            roots: Vec::new(),
            values: HashMap::default(),
            outcome_reads: Vec::new(),
            binary_facts: HashMap::default(),
            fit_answers: HashMap::default(),
            field_reads: Vec::new(),
        }
    }

    fn field_read(&self, question: FitQuestion, field: &BitMatchField) -> Option<Var> {
        self.field_reads
            .iter()
            .find(|read| read.is_of(question, field))
            .map(|read| read.var)
    }

    fn proven(mut self, roots: Vec<Ty>) -> Self {
        self.roots = roots;
        self
    }

    fn reading(mut self, subjects: impl IntoIterator<Item = SubjectId>) -> Self {
        self.outcome_reads.extend(subjects);
        self
    }

    /// A state whose dispatch inputs are each already one runtime word,
    /// rather than a value still in lane form.
    fn resolved(dispatch_inputs: Vec<Var>, forwarded_args: Vec<Var>, bindings: DispatchBindings<Var>) -> Self {
        Self::new(
            dispatch_inputs.into_iter().map(NativeBoundValue::Runtime).collect(),
            forwarded_args,
            bindings,
        )
    }
}

/// The entries of one executable copied into the function being built, and
/// where its returns go.
struct EntryScope {
    blocks: HashMap<ControlEntryId, BlockId>,
    pending: VecDeque<(ControlEntryId, BlockId, Vec<Var>)>,
    returns: Returns,
}

#[derive(Default)]
enum Returns {
    /// The body is the function's own: a return leaves the function.
    #[default]
    FromFunction,
    /// The body is copied into its caller: a return jumps to the block where
    /// its returns meet, which takes the lanes of its return layout and is
    /// made by the first return.
    ToJoin {
        tys: Vec<Ty>,
        join: Option<(BlockId, Vec<Var>)>,
    },
}

impl Returns {
    fn to_join(tys: &[Ty]) -> Self {
        Self::ToJoin {
            tys: tys.to_vec(),
            join: None,
        }
    }

    /// The block the returns met in and its parameters, when any return was
    /// lowered.
    fn joined(self) -> Option<(BlockId, Vec<Var>)> {
        match self {
            Self::ToJoin { join, .. } => join,
            Self::FromFunction => unreachable!("only a body copied into its caller has a meeting block"),
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
    origin: NativeBodyOrigin,
    entry_abi: NativeEntryAbi,
    param_reprs: Vec<AbiValueRepr>,
    return_ty: Ty,
    return_reprs: Vec<AbiValueRepr>,
    effects: EffectSummary,
    /// The block each entry reached as a block of this function has.
    entry_blocks: HashMap<ControlEntryId, BlockId>,
    /// Entries reached as blocks and not yet lowered, with their block and
    /// the parameters the block binds.
    pending_entries: VecDeque<(ControlEntryId, BlockId, Vec<Var>)>,
    /// Where the returns of the body being lowered go.
    returns: Returns,
    /// The whole binary a cursor was made into, with the block that made it:
    /// the same cursor asked again in that block is not made again.
    whole_cursors: HashMap<(Var, Var), (BlockId, Var)>,
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
        effects: EffectSummary,
    ) -> Self {
        let builder = FnBuilder::new(fn_id, name.to_string()).with_category(category);
        Self {
            fn_id,
            builder,
            current_block: BlockId(0),
            stmt_counts: HashMap::default(),
            value_types: HashMap::default(),
            extern_marshals: HashMap::default(),
            origin,
            entry_abi,
            param_reprs,
            return_ty,
            return_reprs,
            effects,
            entry_blocks: HashMap::default(),
            pending_entries: VecDeque::default(),
            returns: Returns::FromFunction,
            whole_cursors: HashMap::default(),
        }
    }

    /// The block an entry is lowered into within this function, created the
    /// first time control reaches it.
    fn entry_block(&mut self, entry: ControlEntryId, tys: &[Ty]) -> BlockId {
        if let Some(block) = self.entry_blocks.get(&entry) {
            return *block;
        }
        let params = self.typed_params(tys);
        let block = self.builder.block(params.clone());
        self.entry_blocks.insert(entry, block);
        self.pending_entries.push_back((entry, block, params));
        block
    }

    /// Whether this function is a machine function, which returns its result
    /// lanes to its caller in registers.
    fn is_machine(&self) -> bool {
        matches!(self.entry_abi, NativeEntryAbi::Machine)
    }

    /// Whether the body being lowered returns where control is: a machine
    /// function, or a body copied into its caller.
    fn returns_here(&self) -> bool {
        self.is_machine() || self.returns_to_join()
    }

    fn returns_to_join(&self) -> bool {
        matches!(self.returns, Returns::ToJoin { .. })
    }

    /// Lowers another executable's entries into this function from here on,
    /// its returns going where `returns` says. Answers the scope it replaces.
    fn enter_scope(&mut self, returns: Returns) -> EntryScope {
        EntryScope {
            blocks: std::mem::take(&mut self.entry_blocks),
            pending: std::mem::take(&mut self.pending_entries),
            returns: std::mem::replace(&mut self.returns, returns),
        }
    }

    /// Goes back to lowering `outer`'s entries, answering the scope left.
    fn leave_scope(&mut self, outer: EntryScope) -> EntryScope {
        assert!(
            self.pending_entries.is_empty(),
            "an executable copied into its caller leaves no entry unlowered"
        );
        EntryScope {
            blocks: std::mem::replace(&mut self.entry_blocks, outer.blocks),
            pending: std::mem::replace(&mut self.pending_entries, outer.pending),
            returns: std::mem::replace(&mut self.returns, outer.returns),
        }
    }

    /// Ends the block returning `lanes`: from this function, or, in a body
    /// copied into its caller, by a jump to the block where its returns meet.
    fn return_lanes(&mut self, lanes: Vec<Var>) {
        let Returns::ToJoin { tys, join } = &self.returns else {
            self.set_term(Term::ReturnLanes(lanes));
            return;
        };
        assert_eq!(
            tys.len(),
            lanes.len(),
            "a return in a body copied into its caller carries the lanes of its return layout"
        );
        let block = match join {
            Some((block, _)) => *block,
            None => {
                let tys = tys.clone();
                let params = self.typed_params(tys.iter());
                let block = self.builder.block(params.clone());
                let Returns::ToJoin { join, .. } = &mut self.returns else {
                    unreachable!()
                };
                *join = Some((block, params));
                block
            }
        };
        self.set_term(Term::Goto(block, lanes));
    }

    /// Calls machine function `callee` on `args` and answers the lanes it
    /// returns, of types `result_tys`.
    fn emit_machine_call(&mut self, callee: FnId, args: Vec<Var>, result_tys: &[Ty]) -> Vec<Var> {
        let (lanes, _) = self.emit_let_many(result_tys.len(), Prim::MachineCall(callee, args));
        for (lane, ty) in lanes.iter().zip(result_tys) {
            self.value_types.insert(*lane, *ty);
        }
        lanes
    }

    fn entry_params<'t>(&mut self, tys: impl IntoIterator<Item = &'t Ty>) -> Vec<Var> {
        let params = self.typed_params(tys);
        self.current_block = self.builder.block(params.clone());
        params
    }

    fn typed_params<'t>(&mut self, tys: impl IntoIterator<Item = &'t Ty>) -> Vec<Var> {
        tys.into_iter()
            .map(|ty| {
                let param = self.builder.fresh_var();
                self.value_types.insert(param, *ty);
                param
            })
            .collect()
    }

    fn emit_let(&mut self, prim: Prim) -> (Var, usize) {
        let stmt_idx = self.stmt_counts.entry(self.current_block).or_insert(0);
        let idx = *stmt_idx;
        *stmt_idx += 1;
        let var = self.builder.let_(self.current_block, prim);
        (var, idx)
    }

    fn emit_let_many(&mut self, arity: usize, prim: Prim) -> (Vec<Var>, usize) {
        let stmt_idx = self.stmt_counts.entry(self.current_block).or_insert(0);
        let idx = *stmt_idx;
        *stmt_idx += 1;
        let vars = self.builder.let_many(self.current_block, arity, prim);
        (vars, idx)
    }

    fn fresh_callsite(&self) -> CallsiteIdent {
        CallsiteIdent::from_source(Span::DUMMY)
    }

    /// Put one entry in the map destination `map`; the answer is the
    /// destination the next put or the freeze takes.
    fn emit_map_put(&mut self, map: Var, key: Var, value: Var) -> Var {
        self.emit_let(Prim::DestMapPut { map, key, value }).0
    }

    fn set_term(&mut self, term: Term) {
        self.builder.set_terminator(self.current_block, term);
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
            block_param_reprs: HashMap::default(),
            value_types: self.value_types,
            extern_marshals: self.extern_marshals,
            effects: self.effects,
            frame: None,
        };
        (fn_ir, body)
    }
}

fn env_local_value(env: &ValueEnv, value: ValueId) -> Result<&NativeBoundValue, FatalError> {
    env.value(value).ok_or(FatalError)
}

fn executable_input_tys(executable: &BackendExecutable) -> Vec<Ty> {
    executable
        .abi
        .semantic_inputs
        .iter()
        .flat_map(|input| input.layout.tys.iter().copied())
        .collect()
}

/// What the program text says of where a bitstring field starts.
#[derive(Debug, Clone, Copy)]
enum FieldStart {
    /// This many bits from the first bit of the binary.
    Fixed(u64),
    /// Past the position of a cursor, by this many bits when the text says.
    PastCursor(Option<u64>),
    /// Somewhere only the running program knows.
    Unknown,
}

impl FieldStart {
    /// The start of the field after one that spans `extent` bits, when the
    /// text says how many.
    fn advanced_by(self, extent: Option<u64>) -> Self {
        match (self, extent) {
            (Self::Fixed(at), Some(extent)) => Self::Fixed(at + extent),
            (Self::PastCursor(Some(offset)), Some(extent)) => Self::PastCursor(Some(offset + extent)),
            (Self::PastCursor(_), _) => Self::PastCursor(None),
            (Self::Fixed(_) | Self::Unknown, _) => Self::Unknown,
        }
    }
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
        ShapeDescr::Nothing | ShapeDescr::Lane(_) | ShapeDescr::Tuple(_) | ShapeDescr::Cursor { .. } => Err(FatalError),
    }
}

fn bind_local_value(
    ctx: &mut NativeFnCtx,
    executable: &BackendExecutable,
    env: &mut ValueEnv,
    value: ValueId,
    bound: NativeBoundValue,
) {
    if let Some(var) = bound.runtime_word()
        && let Some(ty) = executable.abi.materialized.value_types.get(&value).copied()
    {
        ctx.value_types.insert(var, ty);
    }
    env.insert(value, bound);
}

/// Records, for the extern call at statement `stmt_idx` of the current block,
/// the wire type each of its arguments crosses in.
fn register_extern_marshals(ctx: &mut NativeFnCtx, stmt_idx: usize, marshal_plan: &[ExternTy]) {
    for (arg_idx, marshal) in marshal_plan.iter().copied().enumerate() {
        ctx.extern_marshals.insert(
            ExternMarshalSite {
                block: ctx.current_block,
                stmt_idx,
                arg_idx,
            },
            marshal,
        );
    }
}

fn collect_extern_marshals(
    world: &World,
    tel: &impl crate::telemetry::Telemetry,
    root_id: RootId,
    program: &BackendProgram,
) -> Result<HashMap<usize, Vec<ExternTy>>, FatalError> {
    let mut out = HashMap::default();
    for executable in program.executables() {
        if let BackendBody::Clauses { entries, .. } = &executable.body {
            for entry in entries {
                collect_extern_marshals_in_tail(world, tel, root_id, program, &entry.tail, &mut out)?;
            }
        }
    }
    Ok(out)
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
        let marshals = extern_marshals.unwrap_or(&signature.params);
        match out.get(&callee) {
            Some(existing) if existing != marshals => {
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
                out.insert(callee, marshals.clone());
            }
        }
    }
    Ok(())
}

/// Lower a dispatch-matrix clause-selector constant (the compile-time value
/// a multi-clause function's argument is tested against, e.g. the `:cont`
/// in a `{:cont, acc}` clause head) to a fresh `Var`.
///
/// As in `ground_var`: this `Var` has no `ValueId`
/// and so never appears in type inference's `value_types`. Registering its
/// `Ty` here is what lets `lower_eq_binop`'s same-kind fast paths recognize
/// it instead of falling back to the generic boxed `fz_value_eq_ref` path —
/// this is the exact site responsible for boxing the `{:cont, acc}` /
/// `{:halt, acc}` tag on every `Enum.reduce` step.
fn lower_dispatch_const(
    ctx: &mut NativeFnCtx,
    atoms: &ModuleAtoms,
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
            let atom = atoms.id_of(name).ok_or(FatalError)?;
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
        crate::ast::BinOp::Eq => IrBinOp::Eq,
        crate::ast::BinOp::Neq => IrBinOp::Neq,
        crate::ast::BinOp::Lt => IrBinOp::Lt,
        crate::ast::BinOp::LtEq => IrBinOp::Le,
        crate::ast::BinOp::Gt => IrBinOp::Gt,
        crate::ast::BinOp::GtEq => IrBinOp::Ge,
        other => panic!("unsupported backend binop in native lowering: {other:?}"),
    }
}

fn lower_guard_binop(op: crate::dispatch_matrix::pattern::PatternGuardBinOp) -> IrBinOp {
    match op {
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
        crate::ast::UnOp::Not => panic!("lowering should route `not` through a case"),
    }
}

fn lower_field_size_ir(
    size: &Option<super::super::body::LoweredBitSize>,
    env: &ValueEnv,
) -> Result<Option<FieldSizeIr>, FatalError> {
    Ok(match size {
        None => None,
        Some(super::super::body::LoweredBitSize::Literal(value)) => Some(FieldSizeIr::Literal(*value)),
        Some(super::super::body::LoweredBitSize::Value(value)) => {
            Some(FieldSizeIr::Var(env.runtime_var(*value).ok_or(FatalError)?))
        }
    })
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
                ShapeDemand::TupleFields(_) => {
                    let field_demands = demand
                        .shape
                        .field_prefix(fields.len())
                        .expect("a field demand reads as a field prefix");
                    for (field, field_demand) in fields.iter().copied().zip(field_demands) {
                        mark_ignored_layout_lanes_for_demand(world, builder, vars, field, &field_demand, lane_index)?;
                    }
                    Ok(())
                }
                ShapeDemand::Whole | ShapeDemand::Matched => skip_runtime_lanes(world, vars, shape, lane_index),
            }
        }
        ShapeDescr::Cursor { .. } => skip_runtime_lanes(world, vars, shape, lane_index),
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
    emit_job_diagnostic(tel, diagnostic)
}

#[cfg(test)]
#[path = "native_test.rs"]
mod native_test;
