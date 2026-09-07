//! The canonical external form of a compiled artifact.
//!
//! Two builds mean the same thing when this rendering of them is byte-equal.
//! That is a different question from the two the existing determinism tests
//! ask, and the three do not subsume one another:
//!
//! - the CANONICAL FORM measures the ARTIFACT — it survives renumbering, so it
//!   is the only comparand that holds across processes, versions, or a build
//!   cache;
//! - raw `PartialEq` on `BackendProgram` measures the BOOKKEEPING — sound only
//!   for two compiles of one input in one process, where different ids imply a
//!   different work order;
//! - job order measures the CAUSE — the work sequence whose drift renumbers the
//!   arena in the first place.
//!
//! Comparison-only. Nothing on a production path consumes this, and it never
//! replaces `PartialEq` on `BackendProgram` (that equality is load-bearing for
//! incremental invalidation).
//!
//! Three rules make the rendering id-free:
//!
//! - INTERNED ids (`Ty`, `ShapeId`, `LaneId`, `CallableId`, `BoundaryId`,
//!   `FunctionId`, `CodeId`) are expanded to what they describe;
//! - PROGRAM-WIDE positions (the executable and construction-wrapper vectors)
//!   are re-sorted on an id-free key, and every reference to them is remapped
//!   through that order — in the RENDERING only, never by renumbering the real
//!   structures;
//! - BODY-LOCAL ids (`ValueId`, `CallSiteId`) are sparse after pruning, so they
//!   are re-densified by first appearance in the body walk. A value the body
//!   never mentions has no identity worth naming and renders as `v?`.
//!
//! `{:?}` appears only on field-free enums, where it is the variant name and
//! nothing else. It is never used on a container: `HashMap`'s Debug order is
//! per-instance `RandomState` order, so a form derived from it would differ run
//! to run even between equal structs.

use super::transport::TransportPosition;
use std::collections::HashMap;
use std::sync::Arc;

use crate::dispatch_matrix::pattern::{
    PatternDispatchOutcome, PatternDispatchPlan, PatternGuardDispatch, PatternGuardExpr, PatternPinnedInput,
    PatternSubjectRef,
};
use crate::dispatch_matrix::{
    BitstringFieldShape, BitstringFieldSize, BitstringShape, ComparisonValue, DispatchArm, DispatchEdge, DispatchGraph,
    DispatchMatrix, DispatchNode, EdgeEvidence, EdgeProjection, GroundValue, ProjectionKind, Proof, Region,
    RegionPredicate, RegionQuestion, Subject, SubjectSource,
};
use crate::source::Span;
use crate::type_expr::ResolvedSpecDecl;

use super::artifact::{
    AbiValueRepr, BackendBody, BackendCallArg, BackendClause, BackendConstructionCapture,
    BackendConstructionMemberAdapter, BackendConstructionWrapper, BackendEntry, BackendEntryCapture,
    BackendEntryOrigin, BackendExecutable, BackendProgram, BackendReceive, BackendReturnFlow, BackendReturnLayout,
    BackendSemanticInputLayout, BackendStep, BackendTail, BackendValueLayout, CallEdge, CallTarget, EffectSummary,
    ExecutableDispatch,
};
use super::body::{
    CallSiteId, ControlDestination, ControlDispatch, ControlEntryId, DispatchBindings, LoweredBitField,
    LoweredBitFieldSpec, LoweredBitSize, LoweredExtern, ReceiveAfter, ReceiveClause, ReusableConsCapture, ValueId,
};
use super::identity::{ActivationKey, ExecutableKey, FunctionId};
use super::semantic::{
    CallableDemand, CallableFlowEdge, CallableFlowFact, CallableSurface, CallableTarget, ExecutableRuntimeDemand,
    RuntimeDemand, ShapeDemand,
};
use super::transport::{BoundaryId, CallableId, LaneId, ShapeDescr, ShapeId, TransportCarrier, TransportLayout};
#[cfg(test)]
use super::types::{ClosureSurfacePos, decode_closure_surface_var};
use super::types::{Ty, TyCanon, TypeVarId};
use super::world::World;

/// The canonical external form of one root's `BackendProgram`.
pub(crate) fn canon_backend_program(world: &World, program: &BackendProgram) -> String {
    let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
    ProgramCanon::new(world, TyCanon::new(&labels)).render(program)
}

#[cfg(test)]
pub(crate) fn canon_runtime_demand_fact(
    world: &World,
    executable: &ExecutableKey,
    demand: &ExecutableRuntimeDemand,
) -> String {
    let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
    let mut canon = ProgramCanon::new(world, TyCanon::new(&labels));
    let mut out = vec![canon.executable_key(executable)];
    out.extend(canon.runtime_demand(demand));
    out.join("\n")
}

#[cfg(test)]
pub(crate) fn canon_executable_key(world: &World, executable: &ExecutableKey) -> String {
    let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
    ProgramCanon::new(world, TyCanon::new(&labels)).executable_key(executable)
}
/// Canonical display numbers indexed by consumer-local wrapper ordinal.
/// Both projections name the same immutable wrappers; neither is their typed
/// construction identity. Tests use this to match interpreter runtime labels
/// against canonical dump labels.
#[cfg(test)]
pub(crate) fn canonical_wrapper_numbers(world: &World, program: &BackendProgram) -> Vec<usize> {
    let labels = |fn_id| function_label(world, FunctionId::from_fn_id(fn_id));
    let mut canon = ProgramCanon::new(world, TyCanon::new(&labels));
    inverse(&canon.wrapper_order(program))
}

/// A function's stable label: `Module.name/arity`.
///
/// Generated lambdas are minted with a name that embeds their OWNER's raw
/// `FunctionId` (`#lambda:{owner}:{start}-{end}`, see
/// `FunctionTable::reference_generated`), which is a mint-order index and so
/// cannot appear in a canonical rendering. The owner is resolved to its own
/// label instead, which also keeps the result injective: the generated key is
/// exactly (owner, span, arity), and all three survive here.
pub(crate) fn function_label(world: &World, function: FunctionId) -> String {
    let reference = world.function_ref(function);
    let (name, arity) = (reference.name.clone(), reference.arity);
    let module = world.module_name(reference.module).unwrap_or_default().to_string();
    match parse_generated_name(&name) {
        Some((owner, start, end)) => format!("{}#lambda@{start}-{end}/{arity}", function_label(world, owner)),
        None if module.is_empty() => format!("{name}/{arity}"),
        None => format!("{module}.{name}/{arity}"),
    }
}

#[cfg(test)]
fn stable_closure_alpha_label(world: &World, id: TypeVarId) -> Option<String> {
    let (fn_id, position) = decode_closure_surface_var(id)?;
    let function = FunctionId::from_fn_id(fn_id);
    let arity = world.try_function_ref(function)?.arity;
    let slot = match position {
        ClosureSurfacePos::Arg(position) if (position as usize) < arity => format!("arg{position}"),
        ClosureSurfacePos::Ret => "return".to_string(),
        ClosureSurfacePos::Arg(_) => return None,
    };
    Some(format!("closure({}:{slot})", function_label(world, function)))
}

fn parse_generated_name(name: &str) -> Option<(FunctionId, u32, u32)> {
    let rest = name.strip_prefix("#lambda:")?;
    let (owner, span) = rest.split_once(':')?;
    let (start, end) = span.split_once('-')?;
    Some((
        FunctionId::from_fn_id(crate::fz_ir::FnId(owner.parse().ok()?)),
        start.parse().ok()?,
        end.parse().ok()?,
    ))
}

/// An indented line sink. Every renderer below appends whole lines, so the
/// output has no place for an unordered container to leak in as a `{:?}` blob.
#[derive(Default)]
struct Out {
    buf: String,
    depth: usize,
}

impl Out {
    fn put(&mut self, text: &str) {
        for _ in 0..self.depth {
            self.buf.push_str("  ");
        }
        self.buf.push_str(text);
        self.buf.push('\n');
    }

    fn enter(&mut self, text: &str) {
        self.put(text);
        self.depth += 1;
    }

    fn exit(&mut self) {
        self.depth -= 1;
    }

    fn section(&mut self, title: &str, lines: Vec<String>) {
        if lines.is_empty() {
            return;
        }
        self.enter(title);
        for line in lines {
            self.put(&line);
        }
        self.exit();
    }
}

/// Body-local names. `ValueId`/`CallSiteId` survive pruning without being
/// renumbered (`prune_lowered_body` reindexes entries only), so their raw
/// values are sparse and carry no meaning. Names are handed out at first
/// appearance in the body walk, which is the one traversal order the artifact
/// itself fixes.
#[derive(Clone, Default)]
struct Names {
    values: HashMap<ValueId, usize>,
    callsites: HashMap<CallSiteId, usize>,
}

impl Names {
    fn value(&mut self, value: ValueId) -> String {
        let next = self.values.len();
        format!("v{}", *self.values.entry(value).or_insert(next))
    }

    /// A value the body never mentions has no position to be named by. Its
    /// content still renders, so nothing is lost — only an identity that was
    /// never referenced.
    fn known_value(&self, value: ValueId) -> Option<String> {
        self.values.get(&value).map(|index| format!("v{index}"))
    }

    fn callsite(&mut self, callsite: CallSiteId) -> String {
        let next = self.callsites.len();
        format!("cs{}", *self.callsites.entry(callsite).or_insert(next))
    }

    fn known_callsite(&self, callsite: CallSiteId) -> Option<String> {
        self.callsites.get(&callsite).map(|index| format!("cs{index}"))
    }
}

struct ProgramCanon<'a> {
    world: &'a World,
    tyc: TyCanon<'a>,
    executables: HashMap<ExecutableKey, usize>,
    wrappers: HashMap<TransportPosition, usize>,
    names: Names,
    shapes: HashMap<ShapeId, Arc<str>>,
    callables: HashMap<CallableId, Arc<str>>,
    boundaries: HashMap<BoundaryId, Arc<str>>,
    #[cfg(test)]
    strict_formula_names: bool,
}

impl<'a> ProgramCanon<'a> {
    fn new(world: &'a World, tyc: TyCanon<'a>) -> Self {
        Self {
            world,
            tyc,
            executables: HashMap::new(),
            wrappers: HashMap::new(),
            names: Names::default(),
            shapes: HashMap::new(),
            callables: HashMap::new(),
            boundaries: HashMap::new(),
            #[cfg(test)]
            strict_formula_names: false,
        }
    }

    fn formula_sort_key(&self, render: impl FnOnce(&mut ProgramCanon<'_>) -> String) -> String {
        let labels = |fn_id| function_label(self.world, FunctionId::from_fn_id(fn_id));
        #[cfg(test)]
        let tyc = TyCanon::alpha_normalized(&labels);
        #[cfg(not(test))]
        let tyc = TyCanon::new(&labels);
        let mut canon = ProgramCanon::new(self.world, tyc);
        canon.names = self.names.clone();
        #[cfg(test)]
        {
            canon.strict_formula_names = self.strict_formula_names;
        }
        render(&mut canon)
    }

    // ------------------------------------------------------------------
    // Program
    // ------------------------------------------------------------------

    fn render(&mut self, program: &BackendProgram) -> String {
        let executable_order = self.executable_order(program);
        let wrapper_order = self.wrapper_order(program);
        self.executables = executable_order
            .iter()
            .enumerate()
            .map(|(canonical, old)| (program.executables()[*old].key.clone(), canonical))
            .collect();
        self.wrappers = wrapper_order
            .iter()
            .enumerate()
            .map(|(canonical, old)| (program.construction_wrappers()[*old].identity.clone(), canonical))
            .collect();

        let mut out = Out::default();
        out.enter("backend_program");
        out.put(&format!("entry {}", self.executable_ref(program.entry())));
        // The atom table's ORDER is an allocation artifact: nothing in the
        // artifact names an atom by its index (steps carry `GroundValue::Atom`
        // with the name), so only the set is meaningful.
        let mut atoms: Vec<String> = program.atom_names.iter().map(|name| format!(":{name}")).collect();
        atoms.sort();
        out.section("atoms", atoms);
        if !program.struct_schemas.is_empty() {
            out.enter("struct_schemas");
            for (name, fields) in program.struct_schemas.entries() {
                out.put(&format!("{name} [{}]", fields.join(", ")));
            }
            out.exit();
        }
        for (canonical, old) in executable_order.iter().enumerate() {
            self.executable(&mut out, canonical, &program.executables()[*old]);
        }
        for (canonical, old) in wrapper_order.iter().enumerate() {
            self.wrapper(&mut out, canonical, &program.construction_wrappers()[*old]);
        }
        out.exit();
        out.buf
    }

    /// Canonical position to old position for the executable vector.
    ///
    /// The canonical order is the id-free key an executable already has — its
    /// function, its input types, and what is demanded of it — with an equally
    /// id-free shallow signature behind it so the order stays total if the
    /// interner ever hands one activation two identities (fz-kdt.48).
    ///
    /// Two executables that render the SAME key tie, and `sort` breaks a tie on
    /// published position — so this rendering is only as id-free as the
    /// published order behind it. That order is the central typed
    /// `SemanticOrd<Types>` relation for `ExecutableKey`, which compares the
    /// addressed activation arrow structurally and never consults rendering or
    /// raw interner ids.
    fn executable_order(&mut self, program: &BackendProgram) -> Vec<usize> {
        let mut keys: Vec<(String, usize)> = program
            .executables()
            .iter()
            .enumerate()
            .map(|(index, executable)| {
                let key = format!(
                    "{}|{}|{:?}|{}",
                    self.executable_key(&executable.key),
                    self.ty(executable.abi.materialized.return_ty),
                    executable.abi.param_reprs,
                    effects_text(executable.abi.effects)
                );
                (key, index)
            })
            .collect();
        keys.sort();
        keys.into_iter().map(|(_, index)| index).collect()
    }

    /// Canonical position to old position for the construction-wrapper vector.
    ///
    /// Wrappers tie far more readily than executables — two specializations of
    /// one callable publish wrappers that render byte-identically — so the
    /// published-order fallback is load-bearing here rather than theoretical.
    /// It is the central typed `SemanticOrd<Types>` relation for
    /// `TransportPosition`, shared by publication and packaging.
    fn wrapper_order(&mut self, program: &BackendProgram) -> Vec<usize> {
        let mut keys: Vec<(String, usize)> = program
            .construction_wrappers()
            .iter()
            .enumerate()
            .map(|(index, wrapper)| {
                let members: Vec<String> = wrapper
                    .members
                    .iter()
                    .map(|member| self.boundary(member.boundary).to_string())
                    .collect();
                let key = format!(
                    "{}|{}|{:?}|{}",
                    self.callable(wrapper.callable),
                    wrapper.call_arity,
                    wrapper.return_form,
                    members.join(";")
                );
                (key, index)
            })
            .collect();
        keys.sort();
        keys.into_iter().map(|(_, index)| index).collect()
    }

    fn executable_ref(&self, old: &ExecutableKey) -> String {
        match self.executables.get(old) {
            Some(canonical) => format!("x{canonical}"),
            None => "x?".to_string(),
        }
    }

    fn wrapper_ref(&self, identity: &TransportPosition) -> String {
        match self.wrappers.get(identity) {
            Some(canonical) => format!("w{canonical}"),
            None => "w?".to_string(),
        }
    }

    // ------------------------------------------------------------------
    // Executable
    // ------------------------------------------------------------------

    fn executable(&mut self, out: &mut Out, index: usize, executable: &BackendExecutable) {
        self.names = Names::default();
        // The body is rendered FIRST so value and callsite names are handed out
        // in body-walk order; the sections that only reference them follow.
        let body = self.body(&executable.body);
        let demand = self.runtime_demand(&executable.abi.materialized.runtime_demand);
        let values = self.value_table(executable);
        let dispatch = executable
            .abi
            .materialized
            .entry_dispatch
            .as_ref()
            .map(|dispatch| self.entry_dispatch(dispatch));

        out.enter(&format!("executable x{index}"));
        out.put(&format!("key {}", self.executable_key(&executable.key)));
        out.put(&format!("return {}", self.ty(executable.abi.materialized.return_ty)));
        out.put(&format!("param_reprs [{}]", reprs_text(&executable.abi.param_reprs)));
        out.put(&format!("effects {}", effects_text(executable.abi.effects)));
        out.section(
            "semantic_inputs",
            executable
                .abi
                .semantic_inputs
                .iter()
                .map(|input| self.semantic_input(input))
                .collect(),
        );
        out.put(&format!(
            "return_layout {}",
            self.return_layout(&executable.abi.return_layout)
        ));
        if let Some(dispatch) = dispatch {
            out.section("entry_dispatch", dispatch);
        }
        out.section("values", values);
        out.section("runtime_demand", demand);
        out.section("body", body);
        out.exit();
    }

    fn executable_key(&mut self, key: &ExecutableKey) -> String {
        format!("{} need={:?}", self.activation_key(&key.activation), key.need)
    }

    fn activation_key(&mut self, activation: &ActivationKey) -> String {
        let inputs: Vec<String> = activation
            .inputs(self.world.types())
            .iter()
            .map(|ty| self.ty(*ty))
            .collect();
        format!(
            "{}[{}]",
            function_label(self.world, activation.function),
            inputs.join(", ")
        )
    }

    fn value_table(&mut self, executable: &BackendExecutable) -> Vec<String> {
        let mut keys: Vec<&ValueId> = executable
            .abi
            .materialized
            .value_types
            .keys()
            .chain(executable.abi.value_layouts.keys())
            .collect();
        keys.sort();
        keys.dedup();
        let mut rows: Vec<(Option<usize>, String)> = Vec::with_capacity(keys.len());
        for value in keys {
            let ty = executable
                .abi
                .materialized
                .value_types
                .get(value)
                .map(|ty| self.ty(*ty))
                .unwrap_or_else(|| "-".to_string());
            let layout = executable
                .abi
                .value_layouts
                .get(value)
                .map(|layout| self.layout(layout))
                .unwrap_or_else(|| "-".to_string());
            let name = self.names.known_value(*value);
            rows.push((
                name.as_ref().map(|_| self.names.values[value]),
                format!("{} : {ty} / {layout}", name.unwrap_or_else(|| "v?".to_string())),
            ));
        }
        // Named values keep the body's order; unnamed ones are unreferenced, so
        // only their content can order them.
        rows.sort_by(|left, right| left.0.cmp(&right.0).then_with(|| left.1.cmp(&right.1)));
        rows.into_iter().map(|(_, line)| line).collect()
    }
}

// ----------------------------------------------------------------------
// Layouts and transport descriptors
// ----------------------------------------------------------------------

impl ProgramCanon<'_> {
    fn ty(&mut self, ty: Ty) -> String {
        #[cfg(test)]
        for id in self.world.types().free_var_ids(&ty) {
            if let Some(name) = stable_closure_alpha_label(self.world, id) {
                self.tyc.name_structural_alpha(id, name);
            }
        }
        self.tyc.render(self.world.types(), ty).to_string()
    }

    fn semantic_input(&mut self, input: &BackendSemanticInputLayout) -> String {
        format!("{} {}", input.semantic_index, self.layout(&input.layout))
    }

    fn return_layout(&mut self, layout: &BackendReturnLayout) -> String {
        let diverges = if layout.diverges { " diverges" } else { "" };
        format!("{}{diverges}", self.layout(&layout.layout))
    }

    fn layout(&mut self, layout: &BackendValueLayout) -> String {
        let tys: Vec<String> = layout.tys.iter().map(|ty| self.ty(*ty)).collect();
        let carrier = match layout.carrier {
            TransportCarrier::Absent => "Absent".to_string(),
            TransportCarrier::ValueRef(lane) => format!("ValueRef({})", self.lane(lane)),
        };
        format!(
            "{} carrier={} tys=[{}] reprs=[{}]",
            self.shape(layout.structural),
            carrier,
            tys.join(", "),
            reprs_text(&layout.reprs)
        )
    }

    /// A transport id names a row in a `World`-owned interner, so it is
    /// expanded to the descriptor behind it. The descriptor tables are
    /// append-only, so the expansion is a finite tree; it is memoized because
    /// one shape is referenced from many layouts.
    fn shape(&mut self, id: ShapeId) -> Arc<str> {
        if let Some(hit) = self.shapes.get(&id) {
            return Arc::clone(hit);
        }
        let text: Arc<str> = match self.world.shape(id).clone() {
            ShapeDescr::Nothing => "nothing".to_string(),
            ShapeDescr::Lane(lane) => format!("lane({})", self.lane(lane)),
            ShapeDescr::Tuple(fields) => {
                let fields: Vec<String> = fields.iter().map(|field| self.transport_layout(*field)).collect();
                format!("shape{{{}}}", fields.join(", "))
            }
            ShapeDescr::Callable(callable) => format!("callable({})", self.callable(callable)),
        }
        .into();
        self.shapes.insert(id, Arc::clone(&text));
        text
    }

    fn lane(&mut self, id: LaneId) -> String {
        let descr = self.world.lane(id).clone();
        format!("{:?}:{}", descr.class, self.ty(descr.ty))
    }

    fn transport_layout(&mut self, layout: TransportLayout) -> String {
        let structural = self.shape(layout.structural);
        match layout.carrier {
            TransportCarrier::Absent => structural.to_string(),
            TransportCarrier::ValueRef(lane) => format!("{structural}+value_ref({})", self.lane(lane)),
        }
    }

    fn callable(&mut self, id: CallableId) -> Arc<str> {
        if let Some(hit) = self.callables.get(&id) {
            return Arc::clone(hit);
        }
        let descr = self.world.callable(id).clone();
        let function = descr
            .function
            .map(|function| function_label(self.world, function))
            .unwrap_or_else(|| "<unknown>".to_string());
        let tys: Vec<String> = descr.capture_tys.iter().map(|ty| self.ty(*ty)).collect();
        let layouts: Vec<String> = descr
            .capture_layouts
            .iter()
            .map(|layout| self.transport_layout(*layout))
            .collect();
        let text: Arc<str> = format!(
            "{function}/{} captures=[{}] layouts=[{}]",
            descr.arity,
            tys.join(", "),
            layouts.join(", ")
        )
        .into();
        self.callables.insert(id, Arc::clone(&text));
        text
    }

    fn boundary(&mut self, id: BoundaryId) -> Arc<str> {
        if let Some(hit) = self.boundaries.get(&id) {
            return Arc::clone(hit);
        }
        let descr = self.world.boundary(id).clone();
        let args: Vec<String> = descr
            .surface_arg_layouts
            .iter()
            .map(|layout| self.transport_layout(*layout))
            .collect();
        let text: Arc<str> = format!(
            "boundary({}) args=[{}] value_lane={}",
            self.callable(descr.callable),
            args.join(", "),
            self.lane(descr.published_value_lane),
        )
        .into();
        self.boundaries.insert(id, Arc::clone(&text));
        text
    }
}

// ----------------------------------------------------------------------
// Runtime demand
// ----------------------------------------------------------------------

impl ProgramCanon<'_> {
    fn runtime_demand(&mut self, demand: &ExecutableRuntimeDemand) -> Vec<String> {
        let mut out = Out::default();
        let activation_inputs = self.callable_activation_inputs(&demand.callable_activation_inputs);
        out.section("callable_activation_inputs", activation_inputs);
        out.put(&format!("return {}", self.demand(&demand.return_demand)));
        for (index, input) in demand.input_demands.iter().enumerate() {
            out.put(&format!("input {index} {}", self.demand(input)));
        }
        let values = self.keyed_by_value(&demand.value_demands, |canon, value| canon.demand(value));
        out.section("values", values);
        let captures = self.keyed_by_entry(&demand.entry_capture_demands, |canon, demands| {
            demands
                .iter()
                .map(|demand| canon.demand(demand))
                .collect::<Vec<_>>()
                .join(", ")
        });
        out.section("entry_captures", captures);
        let args = self.keyed_by_callsite(&demand.call_arg_demands, |canon, demands| {
            demands
                .iter()
                .map(|demand| canon.demand(demand))
                .collect::<Vec<_>>()
                .join(", ")
        });
        out.section("call_args", args);
        let flows = self.keyed_by_value(&demand.callable_flows, |canon, flow| canon.callable_flow(flow));
        out.section("callable_flows", flows);
        lines(out)
    }

    fn demand(&mut self, demand: &RuntimeDemand) -> String {
        format!(
            "{} {}",
            self.shape_demand(&demand.shape),
            self.callable_demand(&demand.callable)
        )
    }

    fn shape_demand(&mut self, demand: &ShapeDemand) -> String {
        match demand {
            ShapeDemand::Ignore => "ignore".to_string(),
            ShapeDemand::Whole => "whole".to_string(),
            ShapeDemand::TupleFields(fields) => {
                let fields: Vec<String> = fields.iter().map(|field| self.demand(field)).collect();
                format!("fields({})", fields.join(", "))
            }
        }
    }

    /// `CallableDemand`'s two sets are `BTreeSet`s ordered by raw `Ty`, so their
    /// iteration order tracks the arena rather than the program. They are
    /// ordered on an entry-local alpha-normalized form before the shared alpha
    /// environment renders them.
    fn callable_demand(&mut self, demand: &CallableDemand) -> String {
        let mut ordered_resolved = demand.resolved.iter().collect::<Vec<_>>();
        ordered_resolved.sort_by_cached_key(|surface| self.formula_sort_key(|local| local.callable_surface(surface)));
        let mut resolved = ordered_resolved
            .into_iter()
            .map(|surface| self.callable_surface(surface))
            .collect::<Vec<_>>();
        resolved.sort();
        let mut ordered_targets = demand.targets.iter().collect::<Vec<_>>();
        ordered_targets.sort_by_cached_key(|target| self.formula_sort_key(|local| local.callable_target(target)));
        let mut targets = ordered_targets
            .into_iter()
            .map(|target| self.callable_target(target))
            .collect::<Vec<_>>();
        targets.sort();
        format!(
            "callable(resolved=[{}] targets=[{}] opaque={} escape={})",
            resolved.join("; "),
            targets.join("; "),
            demand.opaque,
            demand.escape
        )
    }

    fn callable_surface(&mut self, surface: &CallableSurface) -> String {
        let inputs: Vec<String> = surface.inputs.iter().map(|ty| self.ty(*ty)).collect();
        format!("({})", inputs.join(", "))
    }

    fn callable_activation_input(&mut self, input: &super::semantic::CallableActivationInput) -> String {
        let captures = input.captures.iter().map(|ty| self.ty(*ty)).collect::<Vec<_>>();
        format!(
            "captures=[{}] surface={} own_surface_calls={:?}",
            captures.join(", "),
            self.callable_surface(&input.surface),
            input.capture_called_with_own_surface
        )
    }

    fn callable_activation_inputs(&mut self, inputs: &[super::semantic::CallableActivationInput]) -> Vec<String> {
        let mut ordered = inputs.iter().collect::<Vec<_>>();
        ordered.sort_by_cached_key(|input| self.formula_sort_key(|local| local.callable_activation_input(input)));
        let mut inputs = ordered
            .into_iter()
            .map(|input| self.callable_activation_input(input))
            .collect::<Vec<_>>();
        inputs.sort();
        inputs
    }

    fn callable_target(&mut self, target: &CallableTarget) -> String {
        let inputs: Vec<String> = target.activation_inputs.iter().map(|ty| self.ty(*ty)).collect();
        format!(
            "{}->{}({}) need={:?}",
            self.callable_surface(&target.surface),
            self.activation_key(&target.activation),
            inputs.join(", "),
            target.need
        )
    }

    fn callable_flow(&mut self, flow: &CallableFlowFact) -> String {
        // Named only, never naming: the body walk is the one place a value
        // earns a name, and this fact is read long after that walk is over.
        let captures: Vec<String> = flow.captures.iter().map(|value| self.value_ref(*value)).collect();
        let mut direct_surfaces = flow.direct_surfaces.iter().collect::<Vec<_>>();
        direct_surfaces.sort_by_cached_key(|surface| self.formula_sort_key(|local| local.callable_surface(surface)));
        let mut direct = direct_surfaces
            .into_iter()
            .map(|surface| self.callable_surface(surface))
            .collect::<Vec<_>>();
        direct.sort();
        let mut first_class_surfaces = flow.first_class_surfaces.iter().collect::<Vec<_>>();
        first_class_surfaces
            .sort_by_cached_key(|surface| self.formula_sort_key(|local| local.callable_surface(surface)));
        let mut first_class = first_class_surfaces
            .into_iter()
            .map(|surface| self.callable_surface(surface))
            .collect::<Vec<_>>();
        first_class.sort();
        let direct_edges: Vec<String> = flow.direct_edges.iter().map(|e| self.callable_flow_edge(e)).collect();
        let first_class_edges: Vec<String> = flow
            .first_class_edges
            .iter()
            .map(|e| self.callable_flow_edge(e))
            .collect();
        let resolutions: Vec<String> = flow.resolutions.iter().map(|key| self.executable_key(key)).collect();
        format!(
            "{} captures=[{}] direct=[{}] first_class=[{}] direct_edges=[{}] first_class_edges=[{}] \
             opaque={} escape={} resolutions=[{}]",
            function_label(self.world, flow.function),
            captures.join(", "),
            direct.join("; "),
            first_class.join("; "),
            direct_edges.join("; "),
            first_class_edges.join("; "),
            flow.opaque,
            flow.escape,
            resolutions.join("; ")
        )
    }

    fn value_ref(&self, value: ValueId) -> String {
        if let Some(name) = self.names.known_value(value) {
            return name;
        }
        #[cfg(test)]
        assert!(
            !self.strict_formula_names,
            "formula canon missing body-local value {value:?}"
        );
        "v?".to_string()
    }

    fn callable_flow_edge(&mut self, edge: &CallableFlowEdge) -> String {
        let boundary = edge
            .boundary_input_demands
            .iter()
            .map(|demand| {
                demand
                    .as_ref()
                    .map(|demand| self.demand(demand))
                    .unwrap_or_else(|| "none".to_string())
            })
            .collect::<Vec<_>>();
        format!(
            "{}->{} captures={:?} surface={:?} boundary=[{}]",
            self.callable_surface(&edge.surface),
            self.executable_key(&edge.resolution),
            edge.capture_semantic_inputs,
            edge.surface_semantic_inputs,
            boundary.join(", ")
        )
    }

    /// A `HashMap` keyed by a body-local id, rendered in the order the body
    /// named its keys. Entries for values the body never mentions have no
    /// position, so they are ordered by their content instead.
    fn keyed_by_value<V>(&mut self, map: &HashMap<ValueId, V>, render: fn(&mut Self, &V) -> String) -> Vec<String> {
        let mut keys: Vec<&ValueId> = map.keys().collect();
        keys.sort_by_key(|key| (self.names.values.get(key).copied().unwrap_or(usize::MAX), key.as_u32()));
        let mut rows: Vec<(Option<usize>, String)> = Vec::with_capacity(keys.len());
        for key in keys {
            let value = render(self, &map[key]);
            let named = self.names.known_value(*key);
            #[cfg(test)]
            assert!(
                named.is_some() || !self.strict_formula_names,
                "formula canon missing body-local value {key:?}"
            );
            rows.push((
                named.as_ref().map(|_| self.names.values[key]),
                format!("{} {value}", named.unwrap_or_else(|| "v?".to_string())),
            ));
        }
        ordered(rows)
    }

    fn keyed_by_callsite<V>(
        &mut self,
        map: &HashMap<CallSiteId, V>,
        render: fn(&mut Self, &V) -> String,
    ) -> Vec<String> {
        let mut keys: Vec<&CallSiteId> = map.keys().collect();
        keys.sort_by_key(|key| {
            (
                self.names.callsites.get(key).copied().unwrap_or(usize::MAX),
                key.as_u32(),
                key.span().start,
            )
        });
        let mut rows: Vec<(Option<usize>, String)> = Vec::with_capacity(keys.len());
        for key in keys {
            let value = render(self, &map[key]);
            let named = self.names.known_callsite(*key);
            #[cfg(test)]
            assert!(
                named.is_some() || !self.strict_formula_names,
                "formula canon missing body-local callsite {key:?}"
            );
            rows.push((
                named.as_ref().map(|_| self.names.callsites[key]),
                format!("{} {value}", named.unwrap_or_else(|| "cs?".to_string())),
            ));
        }
        ordered(rows)
    }

    /// `ControlEntryId` is already a dense DFS index into the body's `entries`
    /// vector, so it needs no remapping — only a stable iteration order.
    fn keyed_by_entry<V>(
        &mut self,
        map: &HashMap<ControlEntryId, V>,
        render: fn(&mut Self, &V) -> String,
    ) -> Vec<String> {
        let mut keys: Vec<&ControlEntryId> = map.keys().collect();
        keys.sort_by_key(|key| key.as_u32());
        keys.iter()
            .map(|key| {
                let value = render(self, &map[*key]);
                format!("e{} {value}", key.as_u32())
            })
            .collect()
    }
}

// ----------------------------------------------------------------------
// Body
// ----------------------------------------------------------------------

impl ProgramCanon<'_> {
    fn body(&mut self, body: &BackendBody) -> Vec<String> {
        let mut out = Out::default();
        match body {
            BackendBody::Extern { signature } => self.lowered_extern(&mut out, signature),
            BackendBody::Clauses {
                clauses,
                entries,
                generated,
            } => {
                for (index, clause) in clauses.iter().enumerate() {
                    self.clause(&mut out, index, clause);
                }
                for (index, entry) in entries.iter().enumerate() {
                    self.entry(&mut out, index, entry);
                }
                out.section(
                    "generated",
                    generated
                        .iter()
                        .map(|function| function_label(self.world, *function))
                        .collect(),
                );
            }
        }
        lines(out)
    }

    fn lowered_extern(&mut self, out: &mut Out, signature: &LoweredExtern) {
        out.enter(&format!("extern {} {}", signature.abi, signature.symbol));
        out.put(&format!(
            "params {:?} variadic={}",
            signature.params, signature.variadic
        ));
        out.put(&format!("ret {:?} {}", signature.ret, self.ty(signature.return_ty)));
        out.put(&format!("contract {}", self.spec_decl(&signature.semantic_contract)));
        out.exit();
    }

    /// `constraints` is a `HashMap<TypeVarId, Ty>`, so it is rendered as sorted
    /// rows. A var renders through the arrow language's own naming — a
    /// structural address where it has one — never as its raw id.
    fn spec_decl(&mut self, decl: &ResolvedSpecDecl<Ty>) -> String {
        let params: Vec<String> = decl.params.iter().map(|ty| self.ty(*ty)).collect();
        let result = self.ty(decl.result);
        let constraints: Vec<(TypeVarId, Ty)> = decl.constraints.iter().map(|(var, ty)| (*var, *ty)).collect();
        let mut bound: Vec<String> = constraints
            .into_iter()
            .map(|(var, ty)| {
                let name = self.tyc.var(self.world.types(), var);
                format!("{name}={}", self.ty(ty))
            })
            .collect();
        bound.sort();
        format!("({}) -> {result} where [{}]", params.join(", "), bound.join(", "))
    }

    fn clause(&mut self, out: &mut Out, index: usize, clause: &BackendClause) {
        out.enter(&format!("clause {index} {}", self.span(clause.span)));
        let params: Vec<String> = clause.params.iter().map(|v| self.names.value(*v)).collect();
        out.put(&format!("params [{}]", params.join(", ")));
        for step in &clause.projections {
            let text = self.step(step);
            out.put(&text);
        }
        out.put(&format!("entry e{}", clause.entry.as_u32()));
        out.exit();
    }

    fn entry(&mut self, out: &mut Out, index: usize, entry: &BackendEntry) {
        out.enter(&format!("entry e{index} {}", self.span(entry.span)));
        let origin = self.entry_origin(&entry.origin);
        out.put(&format!("origin {origin}"));
        let params: Vec<String> = entry.params.iter().map(|v| self.names.value(*v)).collect();
        out.put(&format!("params [{}]", params.join(", ")));
        let captures: Vec<String> = entry
            .captures
            .iter()
            .map(|capture| self.entry_capture(capture))
            .collect();
        out.section("captures", captures);
        let reused: Vec<String> = entry
            .reusable_cons_captures
            .iter()
            .map(|reuse| self.reusable_cons(reuse))
            .collect();
        out.section("reusable_cons", reused);
        for step in &entry.steps {
            let text = self.step(step);
            out.put(&text);
        }
        self.tail(out, &entry.tail);
        out.exit();
    }

    fn entry_origin(&mut self, origin: &BackendEntryOrigin) -> String {
        match origin {
            BackendEntryOrigin::Clause => "clause".to_string(),
            BackendEntryOrigin::Branch => "branch".to_string(),
            BackendEntryOrigin::ReceiveOutcome => "receive_outcome".to_string(),
            BackendEntryOrigin::DeliveredResume { value, layout } => {
                let name = self.names.value(*value);
                format!("delivered_resume {name} {}", self.return_layout(layout))
            }
        }
    }

    fn entry_capture(&mut self, capture: &BackendEntryCapture) -> String {
        let name = self.names.value(capture.value);
        format!("{name} {}", self.layout(&capture.layout))
    }

    fn reusable_cons(&mut self, reuse: &ReusableConsCapture) -> String {
        let head = self.names.value(reuse.head);
        let source = self.names.value(reuse.source);
        format!("head={head} source={source}")
    }

    fn step(&mut self, step: &BackendStep) -> String {
        match step {
            BackendStep::Omitted { value } => format!("omitted {}", self.names.value(*value)),
            BackendStep::Const { value, literal } => {
                format!("{} = const {}", self.names.value(*value), ground(literal))
            }
            BackendStep::Tuple { value, items } => {
                format!("{} = tuple [{}]", self.names.value(*value), self.value_list(items))
            }
            BackendStep::List { value, items, tail } => {
                let head = self.names.value(*value);
                let items = self.value_list(items);
                let tail = tail.map(|t| self.names.value(t)).unwrap_or_else(|| "[]".to_string());
                format!("{head} = list [{items}] tail={tail}")
            }
            BackendStep::Map { value, entries } => {
                format!("{} = map {}", self.names.value(*value), self.value_pairs(entries))
            }
            BackendStep::MapUpdate { value, base, entries } => {
                let name = self.names.value(*value);
                let base = self.names.value(*base);
                format!("{name} = map_update {base} {}", self.value_pairs(entries))
            }
            BackendStep::Struct {
                value,
                module_name,
                fields,
            } => {
                let name = self.names.value(*value);
                let fields: Vec<String> = fields
                    .iter()
                    .map(|(field, value)| format!("{field}: {}", self.names.value(*value)))
                    .collect();
                format!("{name} = struct %{module_name}{{{}}}", fields.join(", "))
            }
            BackendStep::Bitstring { value, fields } => {
                let name = self.names.value(*value);
                let fields: Vec<String> = fields.iter().map(|field| self.bit_field(field)).collect();
                format!("{name} = bitstring <<{}>>", fields.join(", "))
            }
            BackendStep::FunctionRef {
                value,
                function,
                construction,
            } => {
                let name = self.names.value(*value);
                format!(
                    "{name} = function_ref {} {}",
                    function_label(self.world, *function),
                    self.construction(construction.as_ref())
                )
            }
            BackendStep::Lambda {
                value,
                function,
                captures,
                construction,
            } => {
                let name = self.names.value(*value);
                let label = function_label(self.world, *function);
                format!(
                    "{name} = lambda {label} captures=[{}] {}",
                    self.value_list(captures),
                    self.construction(construction.as_ref())
                )
            }
            BackendStep::BinaryOp { value, op, left, right } => {
                let name = self.names.value(*value);
                let left = self.names.value(*left);
                let right = self.names.value(*right);
                format!("{name} = {left} {op:?} {right}")
            }
            BackendStep::UnaryOp { value, op, input } => {
                let name = self.names.value(*value);
                let input = self.names.value(*input);
                format!("{name} = {op:?} {input}")
            }
            BackendStep::MapIndex { value, base, key } => {
                let name = self.names.value(*value);
                let base = self.names.value(*base);
                let key = self.names.value(*key);
                format!("{name} = map_index {base}[{key}]")
            }
            BackendStep::FieldAccess { value, base, field } => {
                let name = self.names.value(*value);
                let base = self.names.value(*base);
                format!("{name} = field {base}.{field}")
            }
            BackendStep::AssertLiteral { source, literal } => {
                format!("assert_literal {} {}", self.names.value(*source), ground(literal))
            }
            BackendStep::AssertStruct { source, module_name } => {
                format!("assert_struct {} %{module_name}", self.names.value(*source))
            }
            BackendStep::RequireMapValue { value, source, key } => {
                let name = self.names.value(*value);
                let source = self.names.value(*source);
                format!("{name} = require_map_value {source}[{}]", ground(key))
            }
            BackendStep::AssertTuple { source, arity } => {
                format!("assert_tuple {} arity={arity}", self.names.value(*source))
            }
            BackendStep::TupleField { value, source, index } => {
                let name = self.names.value(*value);
                let source = self.names.value(*source);
                format!("{name} = tuple_field {source}.{index}")
            }
            BackendStep::AssertEmptyList { source } => {
                format!("assert_empty_list {}", self.names.value(*source))
            }
            BackendStep::AssertSame { source, value } => {
                let source = self.names.value(*source);
                let value = self.names.value(*value);
                format!("assert_same {source} {value}")
            }
            BackendStep::SplitList { source, head, tail } => {
                let source = self.names.value(*source);
                let head = self.names.value(*head);
                let tail = self.names.value(*tail);
                format!("split_list {source} -> head={head} tail={tail}")
            }
            BackendStep::BitstringInit { reader, source } => {
                let reader = self.names.value(*reader);
                let source = self.names.value(*source);
                format!("{reader} = bitstring_init {source}")
            }
            BackendStep::BitstringRead {
                ok,
                value,
                next_reader,
                reader,
                spec,
                is_last,
            } => {
                let ok = self.names.value(*ok);
                let value = self.names.value(*value);
                let next_reader = self.names.value(*next_reader);
                let reader = self.names.value(*reader);
                let spec = self.bit_spec(spec);
                format!("{ok}, {value}, {next_reader} = bitstring_read {reader} {spec} last={is_last}")
            }
            BackendStep::AssertBitstringDone { reader } => {
                format!("assert_bitstring_done {}", self.names.value(*reader))
            }
        }
    }

    fn value_list(&mut self, values: &[ValueId]) -> String {
        values
            .iter()
            .map(|value| self.names.value(*value))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn value_pairs(&mut self, entries: &[(ValueId, ValueId)]) -> String {
        let pairs: Vec<String> = entries
            .iter()
            .map(|(key, value)| {
                let key = self.names.value(*key);
                format!("{key} => {}", self.names.value(*value))
            })
            .collect();
        format!("%{{{}}}", pairs.join(", "))
    }

    fn construction(&mut self, construction: Option<&TransportPosition>) -> String {
        match construction {
            None => "construction=-".to_string(),
            Some(identity) => format!("construction={}", self.wrapper_ref(identity)),
        }
    }

    fn bit_field(&mut self, field: &LoweredBitField) -> String {
        let value = self.names.value(field.value);
        format!("{value}{}", self.bit_spec(&field.spec))
    }

    fn bit_spec(&mut self, spec: &LoweredBitFieldSpec) -> String {
        let size = match &spec.size {
            None => "-".to_string(),
            Some(LoweredBitSize::Literal(bits)) => bits.to_string(),
            Some(LoweredBitSize::Value(value)) => self.names.value(*value),
        };
        format!(
            "::{:?}/size={size}/{:?}/signed={}/unit={:?}",
            spec.ty, spec.endian, spec.signed, spec.unit
        )
    }
}

// ----------------------------------------------------------------------
// Tails and call edges
// ----------------------------------------------------------------------

impl ProgramCanon<'_> {
    fn tail(&mut self, out: &mut Out, tail: &BackendTail) {
        match tail {
            BackendTail::Value { value, dest } => {
                let value = self.names.value(*value);
                out.put(&format!("tail value {value} {}", destination(dest)));
            }
            BackendTail::DirectCall {
                value,
                callsite,
                target,
                args,
                dest,
            } => {
                let value = self.names.value(*value);
                let callsite = self.names.callsite(*callsite);
                let args = self.call_args(args);
                out.enter(&format!(
                    "tail direct_call {value} {callsite} args=[{args}] {}",
                    destination(dest)
                ));
                self.call_edge(out, target);
                out.exit();
            }
            BackendTail::ClosureCall {
                value,
                callsite,
                callee,
                target,
                args,
                dest,
                return_flow,
            } => {
                let value = self.names.value(*value);
                let callsite = self.names.callsite(*callsite);
                let callee = self.names.value(*callee);
                let args = self.call_args(args);
                let target = target
                    .as_ref()
                    .map(|target| self.executable_ref(target))
                    .unwrap_or_else(|| "-".to_string());
                out.enter(&format!(
                    "tail closure_call {value} {callsite} callee={callee} target={target} args=[{args}] {}",
                    destination(dest)
                ));
                if let Some(flow) = return_flow {
                    let flow = self.return_flow(flow);
                    out.put(&format!("return_flow {flow}"));
                }
                out.exit();
            }
            BackendTail::If {
                cond,
                then_entry,
                else_entry,
            } => {
                let cond = self.names.value(*cond);
                out.put(&format!(
                    "tail if {cond} then=e{} else=e{}",
                    then_entry.as_u32(),
                    else_entry.as_u32()
                ));
            }
            BackendTail::Dispatch {
                inputs,
                bindings,
                dispatch,
            } => {
                let inputs = self.value_list(inputs);
                out.enter(&format!("tail dispatch inputs=[{inputs}]"));
                let bindings = self.bindings(bindings);
                out.put(&format!("bindings {bindings}"));
                self.control_dispatch(out, dispatch);
                out.exit();
            }
            BackendTail::Receive(receive) => {
                out.enter("tail receive");
                self.receive(out, receive);
                out.exit();
            }
            BackendTail::Halt { atom } => out.put(&format!("tail halt :{atom}")),
        }
    }

    fn call_args(&mut self, args: &[BackendCallArg]) -> String {
        args.iter()
            .map(|arg| self.names.value(arg.value))
            .collect::<Vec<_>>()
            .join(", ")
    }

    fn bindings(&mut self, bindings: &DispatchBindings) -> String {
        let pinned = self.value_list(&bindings.pinned);
        let prepared = self.value_list(&bindings.prepared);
        format!("pinned=[{pinned}] prepared=[{prepared}]")
    }

    fn control_dispatch(&mut self, out: &mut Out, dispatch: &ControlDispatch) {
        let arms: Vec<String> = dispatch
            .arm_entries
            .iter()
            .map(|entry| format!("e{}", entry.as_u32()))
            .collect();
        out.put(&format!(
            "arms [{}] miss=e{}",
            arms.join(", "),
            dispatch.miss_entry.as_u32()
        ));
        let plan = self.plan(&dispatch.plan);
        out.section("plan", plan);
    }

    fn receive(&mut self, out: &mut Out, receive: &BackendReceive) {
        let bindings = self.bindings(&receive.bindings);
        out.put(&format!("bindings {bindings}"));
        let clauses: Vec<String> = receive
            .clauses
            .iter()
            .map(|clause| self.receive_clause(clause))
            .collect();
        out.section("clauses", clauses);
        if let Some(after) = &receive.after {
            let after = self.receive_after(after);
            out.put(&format!("after {after}"));
        }
        out.put(&format!("dest {}", destination(&receive.dest)));
        let plan = self.plan(&receive.dispatch);
        out.section("plan", plan);
    }

    fn receive_clause(&mut self, clause: &ReceiveClause) -> String {
        format!(
            "{} e{} bound=[{}]",
            self.span(clause.span),
            clause.entry.as_u32(),
            clause.bound_names.join(", ")
        )
    }

    fn receive_after(&mut self, after: &ReceiveAfter) -> String {
        let timeout = self.names.value(after.timeout);
        format!("{} timeout={timeout} e{}", self.span(after.span), after.entry.as_u32())
    }

    fn call_edge(&mut self, out: &mut Out, edge: &CallEdge<ExecutableKey, BackendReturnFlow>) {
        match edge {
            CallEdge::Direct(direct) => {
                let callee = self.call_target(&direct.callee);
                let flow = self.return_flow(&direct.return_flow);
                out.put(&format!(
                    "direct callee={callee} return_flow={flow} marshals={:?}",
                    direct.extern_marshals
                ));
            }
            CallEdge::Dispatch(dispatch) => {
                out.enter(&format!("dispatch miss={:?}", dispatch.miss));
                for arm in &dispatch.arms {
                    let callee = self.call_target(&arm.callee);
                    let flow = self.return_flow(&arm.return_flow);
                    out.put(&format!(
                        "arm body={} callee={callee} return_flow={flow} marshals={:?}",
                        arm.body_id, arm.extern_marshals
                    ));
                }
                let plan = self.plan(&dispatch.plan);
                out.section("plan", plan);
                out.exit();
            }
            CallEdge::Indirect(flow) => {
                let flow = self.return_flow(flow);
                out.put(&format!("indirect return_flow={flow}"));
            }
        }
    }

    fn call_target(&mut self, target: &CallTarget<ExecutableKey>) -> String {
        match target {
            CallTarget::Local(index) => self.executable_ref(index),
            CallTarget::ProviderBoundary(function) => {
                format!("provider:{}", function_label(self.world, *function))
            }
        }
    }

    fn return_flow(&mut self, flow: &BackendReturnFlow) -> String {
        match flow {
            BackendReturnFlow::NoReturn => "no_return".to_string(),
            BackendReturnFlow::Tail => "tail".to_string(),
            BackendReturnFlow::Continue { source } => format!("continue({})", self.return_layout(source)),
            BackendReturnFlow::Deliver { source, entry } => {
                format!("deliver({}) e{}", self.return_layout(source), entry.as_u32())
            }
        }
    }

    fn span(&self, span: Span) -> String {
        if span.is_dummy() {
            return "<generated>".to_string();
        }
        let code = super::code::CodeId::from_source(span.code_id);
        let name = self.world.code_name(code).unwrap_or("<anonymous>");
        format!("@{name}:{}-{}", span.start, span.end)
    }
}

// ----------------------------------------------------------------------
// Construction wrappers
// ----------------------------------------------------------------------

impl ProgramCanon<'_> {
    fn wrapper(&mut self, out: &mut Out, index: usize, wrapper: &BackendConstructionWrapper) {
        out.enter(&format!("wrapper w{index}"));
        out.put(&format!("callable {}", self.callable(wrapper.callable)));
        out.put(&format!(
            "call_arity {} return_form {:?}",
            wrapper.call_arity, wrapper.return_form
        ));
        let captures: Vec<String> = wrapper
            .captures
            .iter()
            .map(|capture| self.construction_capture(capture))
            .collect();
        out.section("captures", captures);
        let members: Vec<String> = wrapper
            .members
            .iter()
            .map(|member| self.member_adapter(member))
            .collect();
        out.section("members", members);
        if let Some(selection) = &wrapper.selection {
            let plan = self.plan(selection);
            out.section("selection", plan);
        }
        out.exit();
    }

    fn construction_capture(&mut self, capture: &BackendConstructionCapture) -> String {
        self.layout(&capture.layout)
    }

    fn member_adapter(&mut self, member: &BackendConstructionMemberAdapter) -> String {
        let inputs: Vec<String> = member.surface_inputs.iter().map(|ty| self.ty(*ty)).collect();
        let shapes: Vec<String> = member
            .surface_arg_shapes
            .iter()
            .map(|shape| self.shape(*shape).to_string())
            .collect();
        let target_inputs: Vec<String> = member
            .target_inputs
            .iter()
            .map(|input| self.semantic_input(input))
            .collect();
        format!(
            "{} target={} inputs=[{}] shapes=[{}] captures={:?} surface={:?} target_inputs=[{}] return={}",
            self.boundary(member.boundary),
            self.executable_ref(&member.target),
            inputs.join(", "),
            shapes.join(", "),
            member.capture_semantic_inputs,
            member.surface_semantic_inputs,
            target_inputs.join("; "),
            self.return_layout(&member.target_return)
        )
    }

    fn entry_dispatch(&mut self, dispatch: &ExecutableDispatch) -> Vec<String> {
        let mut out = Out::default();
        let clauses: Vec<String> = dispatch.clause_ids().iter().map(u32::to_string).collect();
        out.put(&format!("clause_ids [{}]", clauses.join(", ")));
        let plan = self.plan(dispatch.plan());
        out.section("plan", plan);
        lines(out)
    }
}

// ----------------------------------------------------------------------
// Pattern dispatch plans
// ----------------------------------------------------------------------

/// Every id inside a plan (`SubjectId`, `OutcomeId`, `GraphNodeId`, `ArmId`,
/// `GuardId`, `PinnedValueId`) is already a dense index into one of the plan's
/// own vectors, so it is rendered positionally and needs no remapping. The only
/// interned handle a plan carries is the `Ty` in a `Region::Type`.
impl ProgramCanon<'_> {
    fn plan(&mut self, plan: &PatternDispatchPlan<Ty>) -> Vec<String> {
        let mut out = Out::default();
        out.put(&format!("inputs {}", plan.input_count));
        let subjects: Vec<String> = plan
            .subjects
            .iter()
            .enumerate()
            .map(|(index, subject)| {
                let rendered = subject.as_ref().map(subject_ref).unwrap_or_else(|| "-".to_string());
                format!("s{index} {rendered}")
            })
            .collect();
        out.section("subjects", subjects);
        self.matrix(&mut out, &plan.matrix);
        self.graph(&mut out, &plan.graph);
        let outcomes: Vec<String> = plan.outcomes.iter().map(|outcome| self.plan_outcome(outcome)).collect();
        out.section("outcomes", outcomes);
        for (index, guard) in plan.guards.iter().enumerate() {
            let guard = self.guard(guard);
            out.section(&format!("guard g{index}"), guard);
        }
        let pinned: Vec<String> = plan
            .pinned
            .iter()
            .enumerate()
            .map(|(index, pinned)| self.pinned_input(index, pinned))
            .collect();
        out.section("pinned", pinned);
        out.section(
            "prepared_keys",
            plan.prepared_keys.iter().map(ground).collect::<Vec<_>>(),
        );
        // Keyed by a dense `SubjectId`, so the map's own iteration order is
        // `RandomState` order and nothing else; the subject index restores it.
        let mut bindings: Vec<(u32, String)> = plan
            .bitstring_direct_bindings
            .iter()
            .map(|(subject, names)| (subject.0, format!("s{} [{}]", subject.0, names.join(", "))))
            .collect();
        bindings.sort();
        out.section(
            "bitstring_direct_bindings",
            bindings.into_iter().map(|(_, line)| line).collect(),
        );
        lines(out)
    }

    fn matrix(&mut self, out: &mut Out, matrix: &DispatchMatrix<Ty>) {
        out.enter("matrix");
        let subjects: Vec<String> = matrix.subjects.iter().map(subject).collect();
        out.section("subjects", subjects);
        let outcomes: Vec<String> = matrix
            .outcomes
            .iter()
            .map(|outcome| format!("o{} {:?}", outcome.id.0, outcome.multiplicity))
            .collect();
        out.section("outcomes", outcomes);
        for arm in &matrix.arms {
            self.arm(out, arm);
        }
        out.exit();
    }

    fn arm(&mut self, out: &mut Out, arm: &DispatchArm<Ty>) {
        out.enter(&format!("arm a{} -> o{}", arm.id.0, arm.outcome.0));
        for question in &arm.questions {
            self.question(out, question);
        }
        let evidence = self.evidence(&arm.evidence);
        out.put(&format!("evidence {evidence}"));
        out.exit();
    }

    fn question(&mut self, out: &mut Out, question: &RegionQuestion<Ty>) {
        let predicate = self.predicate(&question.predicate);
        out.enter(&format!("question {predicate}"));
        let matched = self.evidence(&question.match_evidence);
        out.put(&format!("match {matched}"));
        let missed = self.evidence(&question.miss_evidence);
        out.put(&format!("miss {missed}"));
        out.exit();
    }

    fn graph(&mut self, out: &mut Out, graph: &DispatchGraph<Ty>) {
        out.enter(&format!("graph root=n{}", graph.root.0));
        for (index, node) in graph.nodes.iter().enumerate() {
            let node = self.node(node);
            out.put(&format!("n{index} {node}"));
        }
        out.exit();
    }

    fn node(&mut self, node: &DispatchNode<Ty>) -> String {
        match node {
            DispatchNode::Fail => "fail".to_string(),
            DispatchNode::Outcome { outcome, evidence } => {
                format!("outcome o{} {}", outcome.0, self.evidence(evidence))
            }
            DispatchNode::Test {
                predicate,
                on_match,
                on_miss,
            } => {
                let predicate = self.predicate(predicate);
                let matched = self.edge(on_match);
                let missed = self.edge(on_miss);
                format!("test {predicate} match={matched} miss={missed}")
            }
        }
    }

    fn edge(&mut self, edge: &DispatchEdge<Ty>) -> String {
        format!("n{} {}", edge.target.0, self.evidence(&edge.evidence))
    }

    fn evidence(&mut self, evidence: &EdgeEvidence<Ty>) -> String {
        let proofs: Vec<String> = evidence.proofs.iter().map(|proof| self.proof(proof)).collect();
        let projections: Vec<String> = evidence.projections.iter().map(projection).collect();
        format!(
            "proofs=[{}] projections=[{}]",
            proofs.join("; "),
            projections.join("; ")
        )
    }

    fn proof(&mut self, proof: &Proof<Ty>) -> String {
        format!("{:?} {}", proof.sense, self.predicate(&proof.predicate))
    }

    fn predicate(&mut self, predicate: &RegionPredicate<Ty>) -> String {
        format!("s{} {}", predicate.subject.0, self.region(&predicate.region))
    }

    fn region(&mut self, region: &Region<Ty>) -> String {
        match region {
            Region::Type(ty) => format!("type({})", self.ty(*ty)),
            Region::Equal(value) => format!("equal({})", comparison(value)),
            Region::TupleArity(arity) => format!("tuple_arity({arity})"),
            Region::List(list) => format!("list({list:?})"),
            Region::MapKind => "map_kind".to_string(),
            Region::MapKeyPresent { key } => format!("map_key({})", ground(key)),
            Region::Bitstring(shape) => format!("bitstring({})", bitstring_shape(shape)),
            Region::Guard(guard) => format!("guard(g{})", guard.0),
        }
    }

    fn plan_outcome(&mut self, outcome: &PatternDispatchOutcome) -> String {
        let bindings: Vec<String> = outcome
            .bindings
            .iter()
            .map(|binding| format!("{}=s{} {}", binding.name, binding.source.0, self.span(binding.span)))
            .collect();
        format!(
            "o{} body={} {} bindings=[{}]",
            outcome.outcome.0,
            outcome.body_id,
            self.span(outcome.span),
            bindings.join(", ")
        )
    }

    fn pinned_input(&mut self, index: usize, pinned: &PatternPinnedInput) -> String {
        let input = pinned
            .input
            .map(|input| input.to_string())
            .unwrap_or_else(|| "-".to_string());
        format!("p{index} {} input={input} {}", pinned.name, self.span(pinned.span))
    }

    fn guard(&mut self, expr: &PatternGuardExpr<Ty>) -> Vec<String> {
        let mut out = Out::default();
        self.guard_expr(&mut out, expr);
        lines(out)
    }

    fn guard_expr(&mut self, out: &mut Out, expr: &PatternGuardExpr<Ty>) {
        match expr {
            PatternGuardExpr::Const(value) => out.put(&format!("const {}", ground(value))),
            PatternGuardExpr::Subject(subject) => out.put(&format!("subject s{}", subject.0)),
            PatternGuardExpr::Pinned(pinned) => out.put(&format!("pinned p{}", pinned.0)),
            PatternGuardExpr::Unary { op, expr } => {
                out.enter(&format!("unary {op:?}"));
                self.guard_expr(out, expr);
                out.exit();
            }
            PatternGuardExpr::Binary { op, lhs, rhs } => {
                out.enter(&format!("binary {op:?}"));
                self.guard_expr(out, lhs);
                self.guard_expr(out, rhs);
                out.exit();
            }
            PatternGuardExpr::Dispatch { inputs, dispatch } => {
                out.enter("guard_dispatch");
                for input in inputs {
                    self.guard_expr(out, input);
                }
                self.guard_dispatch(out, dispatch);
                out.exit();
            }
        }
    }

    fn guard_dispatch(&mut self, out: &mut Out, dispatch: &PatternGuardDispatch<Ty>) {
        let plan = self.plan(&dispatch.plan);
        out.section("plan", plan);
        for (index, body) in dispatch.bodies.iter().enumerate() {
            let body = self.guard(body);
            out.section(&format!("body {index}"), body);
        }
    }
}

// ----------------------------------------------------------------------
// Id-free leaves
// ----------------------------------------------------------------------

fn subject(subject: &Subject) -> String {
    let source = match &subject.source {
        SubjectSource::Input { ordinal } => format!("input {ordinal}"),
        SubjectSource::Projection(projection) => {
            format!("project s{} {}", projection.source.0, projection_kind(&projection.kind))
        }
    };
    format!("s{} {source}", subject.id.0)
}

fn subject_ref(reference: &PatternSubjectRef) -> String {
    match reference {
        PatternSubjectRef::Input(ordinal) => format!("input({ordinal})"),
        PatternSubjectRef::TupleField { tuple, index } => format!("field({}, {index})", subject_ref(tuple)),
        PatternSubjectRef::ListHead(list) => format!("head({})", subject_ref(list)),
        PatternSubjectRef::ListTail(list) => format!("tail({})", subject_ref(list)),
        PatternSubjectRef::MapValue { map, key } => format!("map_value({}, {})", subject_ref(map), ground(key)),
        PatternSubjectRef::BitstringField { bitstring, index } => {
            format!("bit_field({}, {index})", subject_ref(bitstring))
        }
    }
}

fn projection(projection: &EdgeProjection) -> String {
    format!(
        "s{} {} -> s{}",
        projection.source.0,
        projection_kind(&projection.kind),
        projection.result.0
    )
}

fn projection_kind(kind: &ProjectionKind) -> String {
    match kind {
        ProjectionKind::TupleField(index) => format!("field({index})"),
        ProjectionKind::ListHead => "head".to_string(),
        ProjectionKind::ListTail => "tail".to_string(),
        ProjectionKind::MapValue { key } => format!("map_value({})", ground(key)),
        ProjectionKind::BitstringField(index) => format!("bit_field({index})"),
    }
}

fn comparison(value: &ComparisonValue) -> String {
    match value {
        ComparisonValue::Const(value) => ground(value),
        ComparisonValue::Pinned(pinned) => format!("p{}", pinned.0),
    }
}

fn bitstring_shape(shape: &BitstringShape) -> String {
    let fields: Vec<String> = shape.fields.iter().map(bitstring_field).collect();
    format!("<<{}>> done={}", fields.join(", "), shape.require_done)
}

fn bitstring_field(field: &BitstringFieldShape) -> String {
    let size = match &field.size {
        None => "-".to_string(),
        Some(BitstringFieldSize::Literal(bits)) => bits.to_string(),
        Some(BitstringFieldSize::Binding(subject)) => format!("s{}", subject.0),
        Some(BitstringFieldSize::BindingName(name)) => name.clone(),
    };
    format!(
        "{:?}/size={size}/{:?}/signed={}/unit={:?}",
        field.kind, field.endian, field.signed, field.unit
    )
}

/// A ground literal, rendered exactly. A float is rendered by its BITS: the
/// carrier stores bits (`GroundValue::Float(u64)`), and a decimal rendering
/// would fold values the artifact keeps apart.
fn ground(value: &GroundValue) -> String {
    match value {
        GroundValue::Int(value) => value.to_string(),
        GroundValue::Float(bits) => format!("float#{bits:016x}"),
        GroundValue::Atom(name) => format!(":{name}"),
        GroundValue::Bool(value) => value.to_string(),
        GroundValue::Nil => "nil".to_string(),
        GroundValue::Binary(bytes) => format!("bin#{}", hex(bytes)),
        GroundValue::Utf8Binary(bytes) => format!("utf8#{}", hex(bytes)),
    }
}

fn hex(bytes: &[u8]) -> String {
    bytes.iter().map(|byte| format!("{byte:02x}")).collect()
}

fn destination(dest: &ControlDestination) -> String {
    match dest {
        ControlDestination::Return => "-> return".to_string(),
        ControlDestination::Deliver(entry) => format!("-> deliver e{}", entry.as_u32()),
    }
}

fn effects_text(effects: EffectSummary) -> String {
    let flags = [
        (effects.allocates, "allocates"),
        (effects.observable, "observable"),
        (effects.reads_allocation_stats, "reads_allocation_stats"),
        (effects.scheduler_visible, "scheduler_visible"),
        (effects.halts, "halts"),
        (effects.calls_opaque, "calls_opaque"),
    ];
    let set: Vec<&str> = flags.iter().filter(|(on, _)| *on).map(|(_, name)| *name).collect();
    if set.is_empty() { "-".to_string() } else { set.join(",") }
}

fn reprs_text(reprs: &[AbiValueRepr]) -> String {
    reprs
        .iter()
        .map(|repr| format!("{repr:?}"))
        .collect::<Vec<_>>()
        .join(", ")
}

fn lines(out: Out) -> Vec<String> {
    out.buf.lines().map(str::to_string).collect()
}

/// Rows a body position named, in that order, then the rows it did not, in
/// content order.
fn ordered(mut rows: Vec<(Option<usize>, String)>) -> Vec<String> {
    rows.sort_by(|left, right| {
        left.0
            .is_none()
            .cmp(&right.0.is_none())
            .then_with(|| left.0.cmp(&right.0))
            .then_with(|| left.1.cmp(&right.1))
    });
    rows.into_iter().map(|(_, line)| line).collect()
}

#[cfg(test)]
fn inverse(order: &[usize]) -> Vec<usize> {
    let mut inverse = vec![0; order.len()];
    for (canonical, old) in order.iter().enumerate() {
        inverse[*old] = canonical;
    }
    inverse
}

#[cfg(test)]
mod carrier_canon_tests {
    use super::*;

    fn render_root_carrier_with_dummy_lanes(dummy_lanes: usize) -> String {
        let mut world = World::new();
        let int = world.types_mut().int();
        let atom = world.types_mut().atom();
        for _ in 0..dummy_lanes {
            world.intern_lane(crate::compiler2::transport::LaneDescr {
                ty: atom,
                class: crate::compiler2::transport::TransportClass::Value,
            });
        }
        let carrier = world.intern_lane(crate::compiler2::transport::LaneDescr {
            ty: int,
            class: crate::compiler2::transport::TransportClass::Value,
        });
        let nothing = world.intern_shape(ShapeDescr::Nothing);
        let layout = BackendValueLayout {
            structural: nothing,
            carrier: TransportCarrier::ValueRef(carrier),
            tys: Box::new([int]),
            reprs: Box::new([AbiValueRepr::ValueRef]),
        };
        let labels = |fn_id| function_label(&world, FunctionId::from_fn_id(fn_id));
        ProgramCanon::new(&world, TyCanon::new(&labels)).layout(&layout)
    }

    #[test]
    fn root_carrier_canon_uses_the_lane_type_not_its_mint_order() {
        assert_eq!(
            render_root_carrier_with_dummy_lanes(0),
            render_root_carrier_with_dummy_lanes(1)
        );
    }
}
