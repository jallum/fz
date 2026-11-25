//! The executable-scoped transport facts: `TransportInterface(e)` and
//! `TransportBody(e)`.
//!
//! An executable's interface is the layout of each of its inputs and of its
//! return: the positions another executable can read. Its body is the layout
//! of every other position it owns, which nothing outside it reads.
//!
//! A job computes the positions it owns inline, each from the executable's own
//! facts and from the positions it aliases, memoized for the run. A position
//! of another executable is always an input or a return, and is one read of
//! that executable's interface fact; a read of an interface that has not
//! settled waits for it. A body reads its own inputs and return the same way,
//! from its own settled interface. The interfaces wait on each other only
//! along the return edges that survive the cut (`cut_in_component_returns`)
//! and along the inputs of the callable targets a callable demand names.

use std::rc::Rc;

use crate::fast_hash::{HashMap, HashSet};

use super::super::artifact::TransportLayouts;
use super::super::body::CallSiteId;
use super::super::drive::{FactKey, Job, JobEffects, UseCollector};
use super::super::executable_facts::ExecutableFacts;
use super::super::identity::{ExecutableKey, ExecutableNeed, FunctionId, RootId};
use super::super::pull::TransportLayout;
use super::super::reach::CallChain;
use super::super::semantic::{ExecutableRuntimeDemand, RuntimeDemand};
use super::super::transport::{ExecutableSymbol, ShapeDescr, TransportPosition};
use super::super::types::{Ty, Types};
use super::super::world::World;
use super::transport::{
    DirectClosureTarget, RecipeLayout, TransportRecipe, assemble_local_callable, bottom_transport_layout,
    callable_capture_demands, callable_capture_tys, contract_transport_layout, cut_transport_layout,
    entry_capture_value, evaluate_transport_recipe, executable_key_for_transport_position, local_callable_construction,
    origin_transport_recipe, position_demand, position_requires_value_ref, position_ty, resume_payload_origin,
    return_edge_is_cut, with_value_ref_carrier,
};
use fz_engine::{FactUse, FatalError, SemanticOrd};

/// The transport fact a job derives.
#[derive(Clone, Copy, PartialEq, Eq)]
enum LayoutFact {
    Interface,
    Body,
}

impl LayoutFact {
    fn job(self, executable: &ExecutableKey) -> Job {
        match self {
            Self::Interface => Job::DeriveTransportInterface(executable.clone()),
            Self::Body => Job::DeriveTransportBody(executable.clone()),
        }
    }

    fn members(self, inputs: &LayoutInputs) -> Vec<TransportPosition> {
        match self {
            Self::Interface => inputs.interface_positions(),
            Self::Body => inputs.body_positions(),
        }
    }
}

/// The facts an interface job cannot start without.
pub(super) fn derive_transport_interface_gates(world: &World, executable: &ExecutableKey) -> Vec<FactKey> {
    layout_gates(world, executable, LayoutFact::Interface)
}

/// The facts a body job cannot start without.
pub(super) fn derive_transport_body_gates(world: &World, executable: &ExecutableKey) -> Vec<FactKey> {
    layout_gates(world, executable, LayoutFact::Body)
}

/// The executable's own facts and the demand on its inputs and return (and,
/// for a body, its own interface), then, once those have settled, everything
/// its positions will read from outside it: the reaches its cuts ask, and the
/// interfaces of the callees the cuts keep.
///
/// All of it is nameable from the facts alone: the walk follows each
/// position's recipe through the positions the executable owns, asks each cut
/// of the reach that decides it, and names a foreign input or return only
/// once its edge is known to survive. A job that discovered these while
/// running would stop at its first run to wait on the reaches, again to wait on
/// the interfaces they cleared, and run a third time to conclude; started
/// behind its gates it runs once. A foreign read the walk cannot foresee --
/// through a closure call or the captures of a callable -- is still a wait the
/// run records.
fn layout_gates(world: &World, executable: &ExecutableKey, which: LayoutFact) -> Vec<FactKey> {
    let mut prefix = vec![
        FactKey::ExecutableFacts(executable.clone()),
        FactKey::RuntimeDemand(executable.clone()),
    ];
    if which == LayoutFact::Body {
        prefix.push(FactKey::TransportInterface(executable.clone()));
    }
    prefix.retain(|fact| !world.fact_is_settled(fact));
    if !prefix.is_empty() {
        return prefix;
    }
    let inputs = LayoutInputs::settled(world, executable);
    NamingWalk::new(world, &inputs, which).gates()
}

/// The walk that names what a job will read from outside its executable.
struct NamingWalk<'w> {
    world: &'w World,
    inputs: &'w LayoutInputs,
    which: LayoutFact,
    frontier: Vec<TransportPosition>,
    seen: HashSet<TransportPosition>,
    gates: Vec<FactKey>,
}

impl<'w> NamingWalk<'w> {
    fn new(world: &'w World, inputs: &'w LayoutInputs, which: LayoutFact) -> Self {
        Self {
            world,
            inputs,
            which,
            frontier: which.members(inputs),
            seen: HashSet::default(),
            gates: Vec::new(),
        }
    }

    fn gates(mut self) -> Vec<FactKey> {
        while let Some(position) = self.frontier.pop() {
            if self.seen.insert(position.clone()) {
                self.visit(&position);
            }
        }
        self.gates
    }

    fn name(&mut self, fact: FactKey) {
        if !self.world.fact_is_settled(&fact) && !self.gates.contains(&fact) {
            self.gates.push(fact);
        }
    }

    fn visit(&mut self, position: &TransportPosition) {
        let (world, inputs) = (self.world, self.inputs);
        let mut recipe = inputs.position_recipe(world, position);
        if !inputs.asks_the_cut(world, position, &recipe) {
            return;
        }
        let mut blocked = false;
        cut_recipe(
            inputs.owner(),
            inputs.root(),
            world.types(),
            &mut recipe,
            &mut blocked,
            &mut |from, chain| match reaches_owner(world, &inputs.executable, &from, chain) {
                Ok(on_cycle) => Some(on_cycle),
                Err(unsettled) => {
                    self.name(unsettled);
                    None
                }
            },
        );
        if blocked {
            return;
        }
        let mut children = Vec::new();
        recipe_positions(&recipe, &mut children);
        for child in children {
            self.follow(child);
        }
    }

    /// A position of this executable is walked in turn, except the inputs and
    /// return a body reads from its own settled interface; a position of
    /// another executable is its interface.
    fn follow(&mut self, child: TransportPosition) {
        let inputs = self.inputs;
        if child.executable() != &inputs.symbol {
            if is_interface_position(&child) {
                let owner = executable_key_for_transport_position(inputs.root(), &child);
                self.name(FactKey::TransportInterface(owner));
            }
        } else if self.which == LayoutFact::Interface || !is_interface_position(&child) {
            self.frontier.push(child);
        }
    }
}

/// Whether the executable `from` reaches `owner` over the edges `chain`
/// names, or the reach fact that has not settled.
fn reaches_owner(
    world: &World,
    owner: &ExecutableKey,
    from: &ExecutableKey,
    chain: CallChain,
) -> Result<bool, FactKey> {
    if from == owner {
        return Ok(true);
    }
    let reach = FactKey::ExecutableReach(from.clone(), chain);
    if !world.fact_is_settled(&reach) {
        return Err(reach);
    }
    let reached = world
        .executable_reach(from, chain)
        .expect("a settled reach fact is defined");
    Ok(reached.contains(owner))
}

/// The positions a recipe may read. A grounded closure call names its callee
/// and its grounded return recipe together: which of the two the evaluation
/// takes depends on the callee's evaluated layout, which a gate cannot compute
/// without evaluating the callee's position a second time. The gate is
/// therefore a superset, and an executable that keeps the extra gate waits on
/// an interface the run would read next to settle the same position.
fn recipe_positions(recipe: &TransportRecipe, out: &mut Vec<TransportPosition>) {
    match recipe {
        TransportRecipe::Alias(position) => out.push(position.clone()),
        TransportRecipe::ClosureCallReturn { callee, grounded } => {
            out.push(callee.clone());
            if let Some(grounded) = grounded {
                recipe_positions(&grounded.return_recipe, out);
            }
        }
        TransportRecipe::Alternatives(children) | TransportRecipe::Tuple(children) => {
            children.iter().for_each(|child| recipe_positions(child, out));
        }
        TransportRecipe::Projection { source, .. } => recipe_positions(source, out),
        TransportRecipe::Terminal | TransportRecipe::PublicCallableReturn | TransportRecipe::CutEdge => {}
    }
}

fn is_interface_position(position: &TransportPosition) -> bool {
    matches!(
        position,
        TransportPosition::ExecutableInput { .. } | TransportPosition::ExecutableReturn { .. }
    )
}

pub(super) fn derive_transport_interface(
    world: &mut World,
    executable: &ExecutableKey,
) -> Result<JobEffects, FatalError> {
    derive_layouts(
        world,
        executable,
        LayoutFact::Interface,
        FactKey::TransportInterface(executable.clone()),
        World::define_transport_interface,
    )
}

pub(super) fn derive_transport_body(world: &mut World, executable: &ExecutableKey) -> Result<JobEffects, FatalError> {
    derive_layouts(
        world,
        executable,
        LayoutFact::Body,
        FactKey::TransportBody(executable.clone()),
        World::define_transport_body,
    )
}

fn derive_layouts(
    world: &mut World,
    executable: &ExecutableKey,
    which: LayoutFact,
    fact: FactKey,
    define: impl FnOnce(&mut World, ExecutableKey, Rc<TransportLayouts>) -> bool,
) -> Result<JobEffects, FatalError> {
    let inputs = LayoutInputs::settled(world, executable);
    let mut layouts = ExecutableLayouts::new(&inputs, which);
    let mut positions = which.members(&inputs);
    positions.sort_by(|left, right| left.semantic_cmp(right, world.types()));
    let mut answers = Vec::with_capacity(positions.len());
    let mut unanswered = 0;
    for position in positions {
        match layouts.read(world, &position) {
            Some(layout) => answers.push((position, layout)),
            None => unanswered += 1,
        }
    }
    let (reads, waits) = layouts.uses.into_reads_waits();
    if !waits.is_empty() {
        return Ok(JobEffects {
            reads,
            waits: waits.into_iter().collect(),
            ..JobEffects::default()
        });
    }
    assert_eq!(
        unanswered, 0,
        "{executable:?}: a position with no layout stands on a fact the job waits for"
    );
    let changed = define(world, executable.clone(), Rc::new(answers.into_iter().collect()));
    Ok(JobEffects {
        reads,
        outputs: vec![fact.clone()],
        changed: changed.then_some(fact).into_iter().collect(),
        ..JobEffects::default()
    })
}

/// The fact that holds the layout at `position`: its executable's interface
/// for an input or its return, its body for any other position.
pub(crate) fn layout_fact(executable: &ExecutableKey, position: &TransportPosition) -> FactKey {
    if is_interface_position(position) {
        FactKey::TransportInterface(executable.clone())
    } else {
        FactKey::TransportBody(executable.clone())
    }
}

/// The layouts a transport fact holds, once it has been derived.
pub(crate) fn fact_layouts<'w>(world: &'w World, fact: &FactKey) -> Option<&'w Rc<TransportLayouts>> {
    match fact {
        FactKey::TransportInterface(executable) => world.transport_interface(executable),
        FactKey::TransportBody(executable) => world.transport_body(executable),
        other => unreachable!("{other:?} holds no transport layouts"),
    }
}

/// An executable and the settled facts its positions are derived from.
struct LayoutInputs {
    executable: ExecutableKey,
    symbol: ExecutableSymbol,
    facts: Rc<ExecutableFacts>,
    runtime: Rc<ExecutableRuntimeDemand>,
}

impl LayoutInputs {
    /// The facts and demand a transport job's gates guarantee are settled.
    fn settled(world: &World, executable: &ExecutableKey) -> Self {
        Self {
            executable: executable.clone(),
            symbol: ExecutableSymbol::new(executable),
            facts: Rc::clone(
                world
                    .executable_facts(executable)
                    .expect("a transport job starts once its executable facts have settled"),
            ),
            runtime: Rc::clone(
                world
                    .runtime_demand(executable)
                    .expect("a transport job starts once its runtime demand has settled"),
            ),
        }
    }

    fn root(&self) -> RootId {
        self.executable.activation.root
    }

    fn owner(&self) -> FunctionId {
        self.executable.activation.function
    }

    fn interface_positions(&self) -> Vec<TransportPosition> {
        let inputs = (0..self.runtime.input_demands.len()).map(|semantic_index| TransportPosition::ExecutableInput {
            executable: self.symbol.clone(),
            semantic_index,
        });
        inputs
            .chain([TransportPosition::ExecutableReturn {
                executable: self.symbol.clone(),
            }])
            .collect()
    }

    fn body_positions(&self) -> Vec<TransportPosition> {
        super::artifact::body_transport_positions(&self.executable, &self.facts, &self.runtime)
    }

    /// Where the layout at `position` comes from: the positions it aliases, or
    /// nothing when it is stated outright.
    fn position_recipe(&self, world: &World, position: &TransportPosition) -> TransportRecipe {
        let facts = &self.facts;
        let symbol = &self.symbol;
        match position {
            TransportPosition::ExecutableInput { .. } => TransportRecipe::Terminal,
            TransportPosition::ExecutableReturn { .. } => TransportRecipe::Alternatives(
                facts
                    .return_origins()
                    .iter()
                    .map(|origin| origin_transport_recipe(symbol, facts, origin))
                    .collect(),
            ),
            TransportPosition::Value { value, .. } => match facts.value_origin(*value) {
                Some(_) if local_callable_construction(facts, &self.runtime, position).is_some() => {
                    TransportRecipe::Terminal
                }
                Some(origin) => origin_transport_recipe(symbol, facts, origin),
                None => TransportRecipe::Terminal,
            },
            TransportPosition::CallArg {
                callsite,
                semantic_index,
                ..
            } => self.call_arg_recipe(world, *callsite, *semantic_index),
            TransportPosition::ReturnPayload { callsite, .. } => origin_transport_recipe(
                symbol,
                facts,
                &facts
                    .callsite_return_origin(*callsite)
                    .expect("every return payload must have a normalized callsite origin"),
            ),
            TransportPosition::EntryCapture {
                entry, capture_index, ..
            } => entry_capture_value(facts, *entry, *capture_index).map_or(TransportRecipe::Terminal, |capture| {
                TransportRecipe::Alias(TransportPosition::Value {
                    executable: symbol.clone(),
                    value: capture,
                })
            }),
            TransportPosition::ResumePayload { entry, .. } => {
                origin_transport_recipe(symbol, facts, resume_payload_origin(facts, *entry))
            }
        }
    }

    /// Whether deriving the layout at `position` runs its recipe through the
    /// cut: a return with no type yet and a position nothing is demanded of
    /// are bottom without it.
    fn asks_the_cut(&self, world: &World, position: &TransportPosition, recipe: &TransportRecipe) -> bool {
        let typed = !matches!(
            position,
            TransportPosition::ExecutableReturn { .. } | TransportPosition::ReturnPayload { .. }
        ) || world.activation_return(&self.executable.activation).is_some();
        typed && !demands_nothing(&position_demand(&self.facts, &self.runtime, position), recipe)
    }

    /// An argument's layout is whichever input of its call's targets receives it.
    fn call_arg_recipe(&self, world: &World, callsite: CallSiteId, semantic_index: usize) -> TransportRecipe {
        let facts = &self.facts;
        if facts
            .body()
            .call_args(callsite)
            .and_then(|args| args.get(semantic_index))
            .is_none()
        {
            return TransportRecipe::Terminal;
        }
        let args_len = facts.body().call_args(callsite).map_or(0, <[_]>::len);
        let mode = facts.body().call_input_mode(callsite);
        let need = facts
            .callsite_needs()
            .get(&callsite)
            .copied()
            .unwrap_or(ExecutableNeed::Value);
        let (Some(mode), Some(summary)) = (mode, facts.callsites().get(&callsite)) else {
            return TransportRecipe::Terminal;
        };
        let inputs = summary
            .targets
            .iter()
            .filter_map(|target| target.activation.as_ref())
            .filter_map(|activation| {
                let target_index =
                    mode.semantic_index(activation.input_len(world.types()), args_len, semantic_index)?;
                Some(TransportRecipe::Alias(TransportPosition::ExecutableInput {
                    executable: ExecutableSymbol::new(&ExecutableKey {
                        activation: activation.clone(),
                        need,
                    }),
                    semantic_index: target_index,
                }))
            })
            .collect::<Vec<_>>();
        if inputs.is_empty() {
            TransportRecipe::Terminal
        } else {
            TransportRecipe::Alternatives(inputs)
        }
    }
}

/// A position's place in a run: being computed, or computed -- `None` when it
/// stands on a fact that has not settled.
enum Slot {
    Computing,
    Done(Option<TransportLayout>),
}

/// The positions of one executable, computed on demand and remembered for the
/// run, and every fact the computation stood on.
pub(super) struct ExecutableLayouts<'i> {
    inputs: &'i LayoutInputs,
    which: LayoutFact,
    uses: UseCollector,
    read: HashSet<FactKey>,
    interfaces: HashMap<ExecutableKey, Rc<TransportLayouts>>,
    slots: HashMap<TransportPosition, Slot>,
}

impl<'i> ExecutableLayouts<'i> {
    fn new(inputs: &'i LayoutInputs, which: LayoutFact) -> Self {
        let mut layouts = Self {
            inputs,
            which,
            uses: UseCollector::new(which.job(&inputs.executable)),
            read: HashSet::default(),
            interfaces: HashMap::default(),
            slots: HashMap::default(),
        };
        layouts.record_read(FactKey::ExecutableFacts(inputs.executable.clone()));
        layouts.record_read(FactKey::RuntimeDemand(inputs.executable.clone()));
        layouts
    }

    fn record_read(&mut self, fact: FactKey) {
        if self.read.insert(fact.clone()) {
            self.uses.record_read(FactUse::settled(fact));
        }
    }

    /// Whether `fact` has settled; if not, the run waits for it.
    fn settled(&mut self, world: &World, fact: FactKey) -> bool {
        if !world.fact_is_settled(&fact) {
            self.uses.record_wait(FactUse::settled(fact));
            return false;
        }
        self.record_read(fact);
        true
    }

    /// The runtime demand of another executable, or `None` while it is unsettled.
    fn read_runtime_demand(
        &mut self,
        world: &World,
        executable: &ExecutableKey,
    ) -> Option<Rc<ExecutableRuntimeDemand>> {
        self.settled(world, FactKey::RuntimeDemand(executable.clone()))
            .then(|| {
                Rc::clone(
                    world
                        .runtime_demand(executable)
                        .expect("settled runtime demand should have a value"),
                )
            })
    }

    /// The layout at `position`, or `None` while a fact it stands on has not
    /// settled -- the wait is already recorded.
    pub(super) fn read(&mut self, world: &mut World, position: &TransportPosition) -> Option<TransportLayout> {
        let own = position.executable() == &self.inputs.symbol;
        if !own || (self.which == LayoutFact::Body && is_interface_position(position)) {
            return self.read_interface(world, position);
        }
        match self.slots.get(position) {
            Some(Slot::Done(layout)) => return *layout,
            Some(Slot::Computing) => panic!(
                "transport position {position:?} reads itself: the positions of one executable follow its acyclic \
                 def-use, and the inputs of a closure are built before the closure"
            ),
            None => {}
        }
        self.slots.insert(position.clone(), Slot::Computing);
        let layout = self.evaluate(world, position);
        self.slots.insert(position.clone(), Slot::Done(layout));
        layout
    }

    /// An input or a return, read from its executable's interface fact -- the
    /// body's own, once settled, or another executable's.
    fn read_interface(&mut self, world: &World, position: &TransportPosition) -> Option<TransportLayout> {
        assert!(
            is_interface_position(position),
            "only an executable's inputs and return are read from its interface: {position:?}"
        );
        let key = executable_key_for_transport_position(self.inputs.root(), position);
        if !self.interfaces.contains_key(&key) {
            if !self.settled(world, FactKey::TransportInterface(key.clone())) {
                return None;
            }
            let interface = Rc::clone(
                world
                    .transport_interface(&key)
                    .expect("a settled transport interface has a value"),
            );
            self.interfaces.insert(key.clone(), interface);
        }
        let layout = self.interfaces[&key]
            .layout_at(position)
            .unwrap_or_else(|| panic!("the interface of {key:?} publishes {position:?}"));
        Some(layout)
    }

    /// Whether the fact a position's type stands on has settled.
    fn position_fact_settled(&mut self, world: &World, position: &TransportPosition) -> bool {
        let activation = self.inputs.executable.activation.clone();
        match position {
            TransportPosition::ExecutableInput { .. } => self.settled(world, FactKey::ActivationInputs(activation)),
            TransportPosition::ExecutableReturn { .. } | TransportPosition::ReturnPayload { .. } => {
                self.settled(world, FactKey::ReturnType(activation))
            }
            _ => true,
        }
    }

    fn evaluate(&mut self, world: &mut World, position: &TransportPosition) -> Option<TransportLayout> {
        let inputs = self.inputs;
        if !self.position_fact_settled(world, position) {
            return None;
        }
        let demand = position_demand(&inputs.facts, &inputs.runtime, position);
        let Some(ty) = position_ty(world, &inputs.executable, &inputs.facts, position) else {
            return Some(untyped_layout(world, position));
        };
        if local_callable_construction(&inputs.facts, &inputs.runtime, position).is_some() {
            return self.local_callable_layout(world, position, &demand);
        }
        let mut recipe = inputs.position_recipe(world, position);
        if demands_nothing(&demand, &recipe) {
            return Some(bottom_transport_layout(world));
        }
        let names_in_component_direct_return = self.cut_in_component_returns(world, &mut recipe)?;
        // A CALLABLE return is exempt: a callable's form is not a lane contract but
        // the row its own demand names, which `exact_direct_callable_layout`
        // derives from facts alone and every view of the convention reaches the
        // same way. There is no type contract to state for a clause set.
        let cycle_return = names_in_component_direct_return
            && matches!(position, TransportPosition::ExecutableReturn { .. })
            && !demand.is_callable();
        let layout = match evaluate_transport_recipe(world, self, &recipe, ty, &demand, position) {
            RecipeLayout::Waiting => return None,
            // A return whose recipe names an in-component DIRECT return publishes
            // the CONTRACT, however much its own arms saw. The cut falls on one
            // side of the cycle only, so the members do not all read each other:
            // a form drawn from what one member happened to see cannot bind the
            // rest, and the caller that returns this value derives its payload
            // from the contract too. Deriving the same way is what leaves one
            // recursive chain on one form -- and a call whose three ends name
            // one form is a TAIL call.
            //
            // The arms are still read: they are this position's dependencies
            // whether or not they decide it.
            _ if cycle_return => contract_transport_layout(world, ty, &demand),
            RecipeLayout::Exact(layout) => layout,
            RecipeLayout::Cut(evidence) => cut_transport_layout(world, ty, &demand, &evidence),
        };
        Some(self.carried_as_value_ref(world, position, ty, layout))
    }

    /// The layout, widened to carry a whole value where the position's wire
    /// demands it.
    fn carried_as_value_ref(
        &self,
        world: &mut World,
        position: &TransportPosition,
        ty: Ty,
        layout: TransportLayout,
    ) -> TransportLayout {
        let inputs = self.inputs;
        if position_requires_value_ref(world, &inputs.executable, inputs.facts.extern_wire(), position, layout) {
            with_value_ref_carrier(world, ty, layout)
        } else {
            layout
        }
    }

    /// The layout of a callable built here: the function it closes over beside
    /// the layouts of the captures it carries.
    fn local_callable_layout(
        &mut self,
        world: &mut World,
        position: &TransportPosition,
        demand: &RuntimeDemand,
    ) -> Option<TransportLayout> {
        let inputs = self.inputs;
        let (value, producer, flow) = local_callable_construction(&inputs.facts, &inputs.runtime, position)
            .expect("a callable value with a flow is built here");
        let captures = callable_capture_tys(world, &inputs.facts, producer);
        let demands = callable_capture_demands(flow, captures.len(), |resolution| {
            self.read_runtime_demand(world, resolution)
        });
        let mut layouts = Vec::with_capacity(producer.captures.len());
        let mut ready = demands.is_some();
        for capture in producer.captures.iter().copied() {
            let capture = TransportPosition::Value {
                executable: inputs.symbol.clone(),
                value: capture,
            };
            match self.read(world, &capture) {
                Some(layout) => layouts.push(layout),
                None => ready = false,
            }
        }
        if !ready {
            return None;
        }
        let callable_ty = inputs
            .facts
            .analysis()
            .value_types
            .get(&value)
            .copied()
            .unwrap_or_else(|| world.types_mut().any());
        let demands = demands.expect("ready captures have settled demands");
        Some(assemble_local_callable(
            world,
            producer,
            callable_ty,
            &captures,
            &demands,
            layouts,
            demand,
        ))
    }

    /// Whether the executable `from` calls reaches `owner` over the edges
    /// `chain` names. `None` while that reach has not settled.
    fn on_cycle(&mut self, world: &World, from: ExecutableKey, chain: CallChain) -> Option<bool> {
        match reaches_owner(world, &self.inputs.executable, &from, chain) {
            Ok(on_cycle) => {
                if from != self.inputs.executable {
                    self.record_read(FactKey::ExecutableReach(from, chain));
                }
                Some(on_cycle)
            }
            Err(unsettled) => {
                self.uses.record_wait(FactUse::settled(unsettled));
                None
            }
        }
    }

    /// Cuts the recursion out of a recipe before it is evaluated, so evaluation
    /// is a function of settled facts and of interfaces that can settle without
    /// it, and answers whether the recipe named an in-cycle return AT ALL -- cut
    /// or kept. `None` while a reach it asks has not settled; every reach the
    /// recipe asks is waited on at once.
    ///
    /// Every cycle in the position graph runs through some executable return: a
    /// body's own positions follow its acyclic def-use, so leaving a body means
    /// naming a callee's return. There are two kinds of such edge and each is cut
    /// on its own terms.
    ///
    /// A DIRECT call's edge is tested by exact reach: does the callee executable
    /// reach the owner through settled `ExecutableFacts` call-site targets,
    /// skipping edges whose origin is a `ClosureCallReturn` (`CallChain::Direct`)?
    /// Both ends on one cycle are mutually reachable this way -- and the edges of
    /// one cycle cannot all climb, so at least one names a callee whose function
    /// does not rise in the typed-origin order. Cutting exactly those leaves the
    /// surviving in-cycle edges strictly climbing, and an edge off any cycle can
    /// close nothing because reach from its callee back to the owner fails.
    ///
    /// A GROUNDED CLOSURE call's edge reaches its callee through a value, so it
    /// carries no `ClosureCallReturn` origin to skip: a closure built outside a
    /// recursion and threaded back through it would otherwise leave the cycle
    /// whole. Asking the one-way reach question with every edge included keeps
    /// the argument above true for this edge too.
    ///
    /// Both tests read only settled `ExecutableFacts`, so the same edges are cut
    /// in every run. What keeps one recursive chain on one form is not the
    /// surviving edges -- they run one way round the cycle only -- but the
    /// contract every return on the cycle publishes: the answer this returns
    /// says which returns those are.
    fn cut_in_component_returns(&mut self, world: &World, recipe: &mut TransportRecipe) -> Option<bool> {
        let inputs = self.inputs;
        let mut blocked = false;
        let names_cycle = cut_recipe(
            inputs.owner(),
            inputs.root(),
            world.types(),
            recipe,
            &mut blocked,
            &mut |from, chain| self.on_cycle(world, from, chain),
        );
        (!blocked).then_some(names_cycle)
    }
}

/// The layout of a position that has no type to derive one from: a return whose
/// activation has no return type yet is bottom, and so is an entry capture the
/// entry does not have.
fn untyped_layout(world: &mut World, position: &TransportPosition) -> TransportLayout {
    match position {
        TransportPosition::EntryCapture { .. } => TransportLayout::structural(world.intern_shape(ShapeDescr::Nothing)),
        _ => bottom_transport_layout(world),
    }
}

/// Applies the cut to `recipe`, asking `on_cycle` whether the executable a
/// recipe names reaches `owner` over a chain, and answers whether the recipe
/// named an in-cycle return at all. `on_cycle` answers `None` while that reach
/// has not settled, which marks the walk `blocked`.
fn cut_recipe(
    owner: FunctionId,
    root: RootId,
    types: &Types,
    recipe: &mut TransportRecipe,
    blocked: &mut bool,
    on_cycle: &mut impl FnMut(ExecutableKey, CallChain) -> Option<bool>,
) -> bool {
    match recipe {
        TransportRecipe::Alias(child @ TransportPosition::ExecutableReturn { .. }) => {
            let (names_cycle, cut) = direct_return_edge(owner, root, types, child, blocked, on_cycle);
            if cut {
                *recipe = TransportRecipe::CutEdge;
            }
            names_cycle
        }
        TransportRecipe::Alternatives(children) | TransportRecipe::Tuple(children) => {
            let mut names_cycle = false;
            for child in children {
                names_cycle |= cut_recipe(owner, root, types, child, blocked, on_cycle);
            }
            names_cycle
        }
        TransportRecipe::Projection { source: tuple, .. } => cut_recipe(owner, root, types, tuple, blocked, on_cycle),
        TransportRecipe::ClosureCallReturn {
            grounded: Some(grounded),
            ..
        } => {
            cut_grounded_return(root, grounded, blocked, on_cycle);
            false
        }
        TransportRecipe::ClosureCallReturn { grounded: None, .. }
        | TransportRecipe::Terminal
        | TransportRecipe::PublicCallableReturn
        | TransportRecipe::CutEdge
        | TransportRecipe::Alias(_) => false,
    }
}

/// A direct call's return edge: whether it names an in-cycle return, and
/// whether it is the side the typed-origin order cuts.
fn direct_return_edge(
    owner: FunctionId,
    root: RootId,
    types: &Types,
    callee: &TransportPosition,
    blocked: &mut bool,
    on_cycle: &mut impl FnMut(ExecutableKey, CallChain) -> Option<bool>,
) -> (bool, bool) {
    let function = callee.executable().activation.function;
    match on_cycle(executable_key_for_transport_position(root, callee), CallChain::Direct) {
        Some(on_cycle) => (on_cycle, on_cycle && return_edge_is_cut(types, function, owner)),
        None => {
            *blocked = true;
            (false, false)
        }
    }
}

/// A closure call's grounded return edge.
///
/// A closure call reaches its callee through a VALUE, so the static graph
/// carries no edge for it: a closure built outside a recursion and threaded
/// back through it leaves caller and lambda in DIFFERENT components, and the
/// licence of the direct edge -- keep a cross-component edge, because no static
/// path returns -- is void. Ask the returning question directly instead. If the
/// target cannot reach this function statically then adding this edge leaves
/// the condensation a DAG and the grounding is safe to keep, which is what
/// preserves one authority for an exact-carrier closure call.
///
/// This edge deliberately does NOT count as naming a cycle: a data-returning
/// cycle carried only by closure edges keeps its evidence form instead of the
/// contract. The edge is indirect through the boxed apply seam, so no
/// direct-call tail is at stake.
fn cut_grounded_return(
    root: RootId,
    grounded: &mut DirectClosureTarget,
    blocked: &mut bool,
    on_cycle: &mut impl FnMut(ExecutableKey, CallChain) -> Option<bool>,
) {
    let TransportRecipe::Alias(child) = &grounded.return_recipe else {
        return;
    };
    match on_cycle(executable_key_for_transport_position(root, child), CallChain::All) {
        Some(true) => grounded.return_recipe = TransportRecipe::CutEdge,
        Some(false) => {}
        None => *blocked = true,
    }
}

/// Whether a position nothing is demanded of has no layout to derive from its
/// recipe. A closure call still derives one: its callee decides the lanes.
fn demands_nothing(demand: &RuntimeDemand, recipe: &TransportRecipe) -> bool {
    demand.is_ignore() && !matches!(recipe, TransportRecipe::ClosureCallReturn { .. })
}

#[cfg(test)]
#[path = "transport_layouts_test.rs"]
mod transport_layouts_test;
