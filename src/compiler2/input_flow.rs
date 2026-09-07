//! Typed, function-local input provenance extraction.
//!
//! The retained relation normalizes SSA routes to semantic endpoints. It is
//! deliberately separate from cross-function demand solving.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use super::body::{
    CallInputMode, CallSiteId, ControlDestination, LoweredBody, LoweredMapKey, LoweredStep, LoweredTail, ValueId,
};
use super::identity::FunctionId;
use super::keying::{
    CallableInputUse, DirectCallFlow, DispatchDemand, InputBinding, InputFlow, InputFlowOrigin, InputFlowRelation,
    InputFlowSink, InputMapKey, InputPathStep, InputPosition, InputPullback, MapSelector,
};
use super::world::World;

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub(super) struct ValueLineage {
    pub(super) origin: InputFlowOrigin,
    pub(super) destination: Box<[InputPathStep]>,
    pub(super) pullback: InputPullback,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) enum ValueTransfer {
    Origin(InputFlowOrigin),
    Resolved(ValueLineage),
    Identity(ValueId),
    WholeDependency(ValueId),
    Project { value: ValueId, path: Box<[InputPathStep]> },
    Embed { value: ValueId, path: Box<[InputPathStep]> },
    EmbedWholeDependency { value: ValueId, path: Box<[InputPathStep]> },
}

pub(super) fn extract_input_flow_relation(
    world: &World,
    function: FunctionId,
    local_dispatch: Box<[DispatchDemand]>,
) -> InputFlowRelation {
    let body = world.lowered_body_ref(function);
    let LoweredBody::Clauses { clauses, entries, .. } = body else {
        return InputFlowRelation {
            local_dispatch,
            ..InputFlowRelation::default()
        };
    };
    let input_count = world.function_arity(function);
    let mut definitions: HashMap<ValueId, Vec<ValueTransfer>> = HashMap::new();
    let mut local_aliases = vec![HashMap::new(); entries.len()];
    let mut clause_aliases = vec![Vec::new(); entries.len()];

    for clause in clauses {
        for (input, value) in clause.params.iter().copied().enumerate().take(input_count) {
            definitions
                .entry(value)
                .or_default()
                .push(ValueTransfer::Origin(InputFlowOrigin::Input(InputPosition::root(
                    input,
                ))));
        }
        let mut aliases = HashMap::new();
        for step in &clause.projections {
            collect_value_transfers(step, &mut definitions, &mut aliases);
        }
        clause_aliases[clause.entry.as_u32() as usize].push(alias_pairs(&aliases));
    }
    for (index, entry) in entries.iter().enumerate() {
        for step in &entry.steps {
            collect_value_transfers(step, &mut definitions, &mut local_aliases[index]);
        }
    }
    for entry in entries {
        if let LoweredTail::DirectCall { value, callsite, .. } | LoweredTail::ClosureCall { value, callsite, .. } =
            entry.tail
        {
            definitions
                .entry(value)
                .or_default()
                .push(ValueTransfer::Origin(InputFlowOrigin::CallResult {
                    callsite,
                    path: Box::default(),
                }));
        }
    }
    let (aliases_by_entry, control_order) = propagated_aliases(entries, &local_aliases, &clause_aliases);
    for producer in control_order {
        let aliases = &aliases_by_entry[producer];
        super::body::visit_control_transitions(&entries[producer].tail, |transition| {
            let target = transition.entry.as_u32() as usize;
            let super::body::ControlEntryOrigin::DeliveredResume { value: delivered } = entries[target].origin else {
                return;
            };
            let lineages = match transition.delivered {
                Some(super::body::DeliveredValueSource::LocalValue(value)) => resolve_value_lineage(
                    value,
                    &definitions,
                    Some(aliases),
                    &mut HashMap::new(),
                    &mut HashSet::new(),
                ),
                Some(super::body::DeliveredValueSource::CallsiteReturn(callsite)) => BTreeSet::from([ValueLineage {
                    origin: InputFlowOrigin::CallResult {
                        callsite,
                        path: Box::default(),
                    },
                    destination: Box::default(),
                    pullback: InputPullback::Structural,
                }]),
                None => return,
            };
            let transfers = definitions.entry(delivered).or_default();
            for lineage in lineages {
                if !transfers
                    .iter()
                    .any(|transfer| transfer == &ValueTransfer::Resolved(lineage.clone()))
                {
                    transfers.push(ValueTransfer::Resolved(lineage));
                }
            }
        });
    }
    let mut flows = BTreeSet::new();
    let mut direct_calls = BTreeMap::new();
    for (index, entry) in entries.iter().enumerate() {
        let aliases = Some(&aliases_by_entry[index]);
        let mut memo = HashMap::new();
        match &entry.tail {
            LoweredTail::Value {
                value,
                dest: ControlDestination::Return,
            } => record_value_sink(
                *value,
                InputFlowSink::FunctionReturn,
                &definitions,
                aliases,
                &mut memo,
                &mut flows,
            ),
            LoweredTail::DirectCall {
                callsite,
                callee,
                args,
                dest: ControlDestination::Return,
                ..
            } => {
                flows.insert(InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite: *callsite,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                });
                record_direct_call(
                    world,
                    *callsite,
                    *callee,
                    args,
                    &definitions,
                    aliases,
                    &mut memo,
                    &mut direct_calls,
                );
            }
            LoweredTail::DirectCall {
                callsite, callee, args, ..
            } => record_direct_call(
                world,
                *callsite,
                *callee,
                args,
                &definitions,
                aliases,
                &mut memo,
                &mut direct_calls,
            ),
            LoweredTail::ClosureCall {
                callsite, callee, dest, ..
            } => {
                if *dest == ControlDestination::Return {
                    flows.insert(InputFlow {
                        origin: InputFlowOrigin::CallResult {
                            callsite: *callsite,
                            path: Box::default(),
                        },
                        sink: InputFlowSink::FunctionReturn(Box::default()),
                        pullback: InputPullback::Structural,
                    });
                }
                record_value_sink(
                    *callee,
                    |path| InputFlowSink::CallableUse {
                        site: CallableInputUse::ClosureCall(*callsite),
                        path,
                    },
                    &definitions,
                    aliases,
                    &mut memo,
                    &mut flows,
                );
            }
            LoweredTail::Value { .. }
            | LoweredTail::If { .. }
            | LoweredTail::Dispatch { .. }
            | LoweredTail::Receive(_)
            | LoweredTail::Halt { .. } => {}
        }
        for step in &entry.steps {
            record_callable_sink(step, &definitions, aliases, &mut memo, &mut flows);
        }
    }
    for clause in clauses {
        let aliases = Some(&aliases_by_entry[clause.entry.as_u32() as usize]);
        let mut memo = HashMap::new();
        for step in &clause.projections {
            record_callable_sink(step, &definitions, aliases, &mut memo, &mut flows);
        }
    }

    InputFlowRelation {
        local_dispatch,
        direct_calls,
        flows,
    }
}

type AliasMap = HashMap<ValueId, BTreeSet<ValueId>>;
type AliasPairs = BTreeSet<(ValueId, ValueId)>;

fn propagated_aliases(
    entries: &[super::body::LoweredEntry],
    local: &[AliasMap],
    clause: &[Vec<AliasPairs>],
) -> (Vec<AliasMap>, Vec<usize>) {
    let mut successors = vec![BTreeSet::new(); entries.len()];
    let mut predecessors = vec![BTreeSet::new(); entries.len()];
    for (source, entry) in entries.iter().enumerate() {
        super::body::visit_control_transitions(&entry.tail, |transition| {
            let target = transition.entry.as_u32() as usize;
            assert!(
                target < entries.len(),
                "lowered control transition must name an entry in its body"
            );
            successors[source].insert(target);
            predecessors[target].insert(source);
        });
    }

    let local = local.iter().map(alias_pairs).collect::<Vec<_>>();
    let mut outgoing = vec![AliasPairs::new(); entries.len()];
    let mut order = Vec::with_capacity(entries.len());
    let mut completed = vec![false; entries.len()];
    let mut ready = predecessors
        .iter()
        .enumerate()
        .filter_map(|(entry, predecessors)| predecessors.is_empty().then_some(entry))
        .collect::<BTreeSet<_>>();
    while let Some(entry) = ready.pop_first() {
        let mut incoming = predecessors[entry]
            .iter()
            .map(|predecessor| &outgoing[*predecessor])
            .chain(clause[entry].iter());
        let mut facts = incoming.next().cloned().unwrap_or_default();
        for contribution in incoming {
            facts.retain(|pair| contribution.contains(pair));
        }
        facts.extend(local[entry].iter().copied());
        outgoing[entry] = close_alias_pairs(&facts);
        order.push(entry);
        completed[entry] = true;
        for successor in &successors[entry] {
            if predecessors[*successor]
                .iter()
                .all(|predecessor| completed[*predecessor])
            {
                ready.insert(*successor);
            }
        }
    }
    assert_eq!(
        order.len(),
        entries.len(),
        "lowered local control graph must be acyclic",
    );
    (outgoing.iter().map(aliases_from_pairs).collect(), order)
}

fn alias_pairs(aliases: &AliasMap) -> AliasPairs {
    let pairs = aliases
        .iter()
        .flat_map(|(left, rights)| rights.iter().map(move |right| ordered_pair(*left, *right)))
        .collect();
    close_alias_pairs(&pairs)
}

fn close_alias_pairs(pairs: &AliasPairs) -> AliasPairs {
    let aliases = aliases_from_pairs(pairs);
    let mut closed = AliasPairs::new();
    let mut visited = BTreeSet::new();
    for value in aliases.keys().copied() {
        if visited.contains(&value) {
            continue;
        }
        let component = alias_component(value, Some(&aliases));
        visited.extend(component.iter().copied());
        for (index, left) in component.iter().copied().enumerate() {
            for right in component.iter().copied().skip(index + 1) {
                closed.insert((left, right));
            }
        }
    }
    closed
}

fn aliases_from_pairs(pairs: &AliasPairs) -> AliasMap {
    let mut aliases = AliasMap::new();
    for (left, right) in pairs {
        aliases.entry(*left).or_default().insert(*right);
        aliases.entry(*right).or_default().insert(*left);
    }
    aliases
}

fn ordered_pair(left: ValueId, right: ValueId) -> (ValueId, ValueId) {
    if left <= right { (left, right) } else { (right, left) }
}

fn record_callable_sink(
    step: &LoweredStep,
    definitions: &HashMap<ValueId, Vec<ValueTransfer>>,
    aliases: Option<&HashMap<ValueId, BTreeSet<ValueId>>>,
    memo: &mut HashMap<ValueId, BTreeSet<ValueLineage>>,
    flows: &mut BTreeSet<InputFlow>,
) {
    let LoweredStep::Lambda { function, captures, .. } = step else {
        return;
    };
    for (capture, value) in captures.iter().copied().enumerate() {
        record_value_sink(
            value,
            |path| InputFlowSink::CallableUse {
                site: CallableInputUse::LambdaCapture {
                    function: *function,
                    capture,
                },
                path,
            },
            definitions,
            aliases,
            memo,
            flows,
        );
    }
}

fn record_direct_call(
    world: &World,
    callsite: CallSiteId,
    callee: FunctionId,
    args: &[super::body::CallArg],
    definitions: &HashMap<ValueId, Vec<ValueTransfer>>,
    aliases: Option<&HashMap<ValueId, BTreeSet<ValueId>>>,
    memo: &mut HashMap<ValueId, BTreeSet<ValueLineage>>,
    direct_calls: &mut BTreeMap<CallSiteId, DirectCallFlow>,
) {
    let callee_inputs = world.function_arity(callee);
    let mut inputs = vec![BTreeSet::new(); callee_inputs];
    for (arg_index, arg) in args.iter().enumerate() {
        let Some(input) = CallInputMode::Direct.semantic_index(callee_inputs, args.len(), arg_index) else {
            continue;
        };
        for lineage in resolve_value_lineage(arg.value, definitions, aliases, memo, &mut HashSet::new()) {
            inputs[input].insert(InputBinding {
                origin: lineage.origin,
                path: lineage.destination,
                pullback: lineage.pullback,
            });
        }
    }
    let replaced = direct_calls.insert(
        callsite,
        DirectCallFlow {
            callee,
            inputs: inputs.into_boxed_slice(),
        },
    );
    assert!(replaced.is_none(), "CallSiteId must be unique within one body");
}

fn record_value_sink(
    value: ValueId,
    sink: impl Fn(Box<[InputPathStep]>) -> InputFlowSink,
    definitions: &HashMap<ValueId, Vec<ValueTransfer>>,
    aliases: Option<&HashMap<ValueId, BTreeSet<ValueId>>>,
    memo: &mut HashMap<ValueId, BTreeSet<ValueLineage>>,
    flows: &mut BTreeSet<InputFlow>,
) {
    for lineage in resolve_value_lineage(value, definitions, aliases, memo, &mut HashSet::new()) {
        flows.insert(InputFlow {
            origin: lineage.origin,
            sink: sink(lineage.destination),
            pullback: lineage.pullback,
        });
    }
}

pub(super) fn collect_value_transfers(
    step: &LoweredStep,
    definitions: &mut HashMap<ValueId, Vec<ValueTransfer>>,
    aliases: &mut HashMap<ValueId, BTreeSet<ValueId>>,
) {
    let mut define = |value, transfers| {
        definitions.entry(value).or_default().extend(transfers);
    };
    match step {
        LoweredStep::Tuple { value, items } => define(
            *value,
            items
                .iter()
                .copied()
                .enumerate()
                .map(|(index, value)| ValueTransfer::Embed {
                    value,
                    path: vec![InputPathStep::TupleField(index as u32)].into_boxed_slice(),
                })
                .collect(),
        ),
        LoweredStep::List { value, items, tail } => {
            let mut transfers = items
                .iter()
                .copied()
                .enumerate()
                .map(|(index, value)| ValueTransfer::Embed {
                    value,
                    path: std::iter::repeat_n(InputPathStep::ListTail, index)
                        .chain(std::iter::once(InputPathStep::ListHead))
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                })
                .collect::<Vec<_>>();
            transfers.extend(tail.iter().copied().map(|value| {
                ValueTransfer::Embed {
                    value,
                    path: std::iter::repeat_n(InputPathStep::ListTail, items.len())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                }
            }));
            define(*value, transfers);
        }
        LoweredStep::Map { value, entries } => define(*value, map_entry_transfers(entries)),
        LoweredStep::MapUpdate { value, base, entries } => {
            let mut excluded = entries
                .iter()
                .filter_map(|(key, _)| key.literal.as_ref().map(InputMapKey::from_ground))
                .collect::<Vec<_>>();
            excluded.sort_unstable();
            excluded.dedup();
            let mut transfers = vec![ValueTransfer::Embed {
                value: *base,
                path: vec![InputPathStep::MapRemainder(excluded.into_boxed_slice())].into_boxed_slice(),
            }];
            transfers.extend(map_entry_transfers(entries));
            define(*value, transfers);
        }
        LoweredStep::Struct { value, fields, .. } => define(
            *value,
            fields
                .iter()
                .map(|(field, value)| ValueTransfer::Embed {
                    value: *value,
                    path: vec![InputPathStep::MapValue(MapSelector::Known(InputMapKey::Atom(
                        field.clone(),
                    )))]
                    .into_boxed_slice(),
                })
                .collect(),
        ),
        LoweredStep::Bitstring { value, fields } => define(
            *value,
            fields
                .iter()
                .enumerate()
                .map(|(index, field)| ValueTransfer::Embed {
                    value: field.value,
                    path: vec![InputPathStep::BitstringField(super::keying::BitstringSelector::Known(
                        index as u32,
                    ))]
                    .into_boxed_slice(),
                })
                .collect(),
        ),
        LoweredStep::Lambda { .. } => {}
        LoweredStep::MapIndex { value, base, key } => define(
            *value,
            std::iter::once(ValueTransfer::Project {
                value: *base,
                path: vec![InputPathStep::MapValue(map_selector(key))].into_boxed_slice(),
            })
            .chain(
                key.literal
                    .is_none()
                    .then_some(ValueTransfer::WholeDependency(key.value)),
            )
            .collect(),
        ),
        LoweredStep::FieldAccess { value, base, field } => define(
            *value,
            vec![ValueTransfer::Project {
                value: *base,
                path: vec![InputPathStep::MapValue(MapSelector::Known(InputMapKey::Atom(
                    field.clone(),
                )))]
                .into_boxed_slice(),
            }],
        ),
        LoweredStep::RequireMapValue { value, source, key } => define(
            *value,
            vec![ValueTransfer::Project {
                value: *source,
                path: vec![InputPathStep::MapValue(MapSelector::Known(InputMapKey::from_ground(
                    key,
                )))]
                .into_boxed_slice(),
            }],
        ),
        LoweredStep::TupleField { value, source, index } => define(
            *value,
            vec![ValueTransfer::Project {
                value: *source,
                path: vec![InputPathStep::TupleField(*index as u32)].into_boxed_slice(),
            }],
        ),
        LoweredStep::SplitList { source, head, tail } => {
            define(
                *head,
                vec![ValueTransfer::Project {
                    value: *source,
                    path: vec![InputPathStep::ListHead].into_boxed_slice(),
                }],
            );
            define(
                *tail,
                vec![ValueTransfer::Project {
                    value: *source,
                    path: vec![InputPathStep::ListTail].into_boxed_slice(),
                }],
            );
        }
        LoweredStep::BitstringInit { reader, source } => {
            define(*reader, vec![ValueTransfer::Identity(*source)]);
        }
        LoweredStep::BitstringRead {
            value,
            next_reader,
            reader,
            ..
        } => {
            define(
                *value,
                vec![ValueTransfer::Project {
                    value: *reader,
                    path: vec![InputPathStep::BitstringField(super::keying::BitstringSelector::Dynamic)]
                        .into_boxed_slice(),
                }],
            );
            define(*next_reader, vec![ValueTransfer::Identity(*reader)]);
        }
        LoweredStep::AssertSame { source, value } => {
            aliases.entry(*source).or_default().insert(*value);
            aliases.entry(*value).or_default().insert(*source);
        }
        LoweredStep::Const { .. }
        | LoweredStep::FunctionRef { .. }
        | LoweredStep::BinaryOp { .. }
        | LoweredStep::UnaryOp { .. }
        | LoweredStep::AssertLiteral { .. }
        | LoweredStep::AssertStruct { .. }
        | LoweredStep::AssertTuple { .. }
        | LoweredStep::AssertEmptyList { .. }
        | LoweredStep::AssertBitstringDone { .. } => {}
    }
}

pub(super) fn map_entry_transfers(entries: &[(LoweredMapKey, ValueId)]) -> Vec<ValueTransfer> {
    let mut transfers = Vec::new();
    let mut later_known = BTreeSet::new();
    for (key, value) in entries.iter().rev() {
        let selector = key
            .literal
            .as_ref()
            .map(InputMapKey::from_ground)
            .map(MapSelector::Known)
            .unwrap_or_else(|| {
                if later_known.is_empty() {
                    MapSelector::Dynamic
                } else {
                    MapSelector::dynamic_excluding(later_known.iter().cloned().collect())
                }
            });
        if let MapSelector::Known(known) = &selector
            && !later_known.insert(known.clone())
        {
            continue;
        }
        if matches!(selector, MapSelector::Dynamic | MapSelector::DynamicExcept(_)) {
            transfers.push(ValueTransfer::EmbedWholeDependency {
                value: key.value,
                path: vec![InputPathStep::MapKey(selector.clone())].into_boxed_slice(),
            });
        }
        transfers.push(ValueTransfer::Embed {
            value: *value,
            path: vec![InputPathStep::MapValue(selector)].into_boxed_slice(),
        });
    }
    transfers.reverse();
    transfers
}

fn map_selector(key: &LoweredMapKey) -> MapSelector {
    key.literal
        .as_ref()
        .map(InputMapKey::from_ground)
        .map(MapSelector::Known)
        .unwrap_or(MapSelector::Dynamic)
}

fn resolve_value_lineage(
    value: ValueId,
    definitions: &HashMap<ValueId, Vec<ValueTransfer>>,
    aliases: Option<&HashMap<ValueId, BTreeSet<ValueId>>>,
    memo: &mut HashMap<ValueId, BTreeSet<ValueLineage>>,
    visiting: &mut HashSet<ValueId>,
) -> BTreeSet<ValueLineage> {
    if let Some(known) = memo.get(&value) {
        return known.clone();
    }
    let component = alias_component(value, aliases);
    if component.iter().any(|member| visiting.contains(member)) {
        return BTreeSet::new();
    }
    visiting.extend(component.iter().copied());
    let mut lineages = BTreeSet::new();
    for transfer in component
        .iter()
        .flat_map(|member| definitions.get(member).into_iter().flatten())
    {
        match transfer {
            ValueTransfer::Origin(origin) => {
                lineages.insert(ValueLineage {
                    origin: origin.clone(),
                    destination: Box::default(),
                    pullback: InputPullback::Structural,
                });
            }
            ValueTransfer::Resolved(lineage) => {
                lineages.insert(lineage.clone());
            }
            ValueTransfer::Identity(source) => {
                lineages.extend(resolve_value_lineage(*source, definitions, aliases, memo, visiting));
            }
            ValueTransfer::WholeDependency(source) => {
                lineages.extend(
                    resolve_value_lineage(*source, definitions, aliases, memo, visiting)
                        .into_iter()
                        .map(|mut lineage| {
                            lineage.destination = Box::default();
                            lineage.pullback = InputPullback::WholeOrigin;
                            lineage
                        }),
                );
            }
            ValueTransfer::Embed { value: source, path } => {
                for lineage in resolve_value_lineage(*source, definitions, aliases, memo, visiting) {
                    if let Some(lineage) = embed_lineage(lineage, path) {
                        lineages.insert(lineage);
                    }
                }
            }
            ValueTransfer::EmbedWholeDependency { value: source, path } => {
                for mut lineage in resolve_value_lineage(*source, definitions, aliases, memo, visiting) {
                    lineage.destination = Box::default();
                    lineage.pullback = InputPullback::WholeOrigin;
                    if let Some(lineage) = embed_lineage(lineage, path) {
                        lineages.insert(lineage);
                    }
                }
            }
            ValueTransfer::Project { value: source, path } => {
                lineages.extend(
                    resolve_value_lineage(*source, definitions, aliases, memo, visiting)
                        .into_iter()
                        .filter_map(|lineage| project_lineage(lineage, path)),
                );
            }
        }
    }
    for member in component {
        visiting.remove(&member);
        memo.insert(member, lineages.clone());
    }
    lineages
}

fn alias_component(value: ValueId, aliases: Option<&HashMap<ValueId, BTreeSet<ValueId>>>) -> BTreeSet<ValueId> {
    let mut component = BTreeSet::from([value]);
    let mut frontier = vec![value];
    while let Some(member) = frontier.pop() {
        for alias in aliases
            .and_then(|aliases| aliases.get(&member))
            .into_iter()
            .flatten()
            .copied()
        {
            if component.insert(alias) {
                frontier.push(alias);
            }
        }
    }
    component
}

fn project_lineage(mut lineage: ValueLineage, projection: &[InputPathStep]) -> Option<ValueLineage> {
    let (origin_suffix, destination) = compose_paths(&lineage.destination, projection)?;
    if lineage.pullback == InputPullback::Structural {
        append_origin_path(&mut lineage.origin, &origin_suffix);
    }
    lineage.destination = destination;
    Some(lineage)
}

pub(super) fn embed_lineage(mut lineage: ValueLineage, path: &[InputPathStep]) -> Option<ValueLineage> {
    let [InputPathStep::MapRemainder(excluded)] = path else {
        lineage.destination = path
            .iter()
            .cloned()
            .chain(lineage.destination.iter().cloned())
            .collect::<Vec<_>>()
            .into_boxed_slice();
        return Some(lineage);
    };
    let Some((head, tail)) = lineage.destination.split_first() else {
        lineage.destination = path.to_vec().into_boxed_slice();
        return Some(lineage);
    };
    match head {
        InputPathStep::MapValue(MapSelector::Known(key)) if excluded.contains(key) => None,
        InputPathStep::MapValue(selector) | InputPathStep::MapKey(selector) => {
            let selector = exclude_map_keys(selector, excluded);
            let head = match head {
                InputPathStep::MapValue(_) => InputPathStep::MapValue(selector),
                InputPathStep::MapKey(_) => InputPathStep::MapKey(selector),
                _ => unreachable!(),
            };
            lineage.destination = std::iter::once(head)
                .chain(tail.iter().cloned())
                .collect::<Vec<_>>()
                .into_boxed_slice();
            Some(lineage)
        }
        InputPathStep::MapRemainder(inner) => {
            let mut combined = excluded.iter().chain(inner.iter()).cloned().collect::<Vec<_>>();
            combined.sort_unstable();
            combined.dedup();
            lineage.destination = std::iter::once(InputPathStep::MapRemainder(combined.into_boxed_slice()))
                .chain(tail.iter().cloned())
                .collect::<Vec<_>>()
                .into_boxed_slice();
            Some(lineage)
        }
        _ => {
            lineage.destination = path
                .iter()
                .cloned()
                .chain(lineage.destination.iter().cloned())
                .collect::<Vec<_>>()
                .into_boxed_slice();
            Some(lineage)
        }
    }
}

fn exclude_map_keys(selector: &MapSelector, excluded: &[InputMapKey]) -> MapSelector {
    match selector {
        MapSelector::Known(key) => MapSelector::Known(key.clone()),
        MapSelector::Dynamic | MapSelector::DynamicExcept(_) => {
            let mut combined = match selector {
                MapSelector::Dynamic => Vec::new(),
                MapSelector::DynamicExcept(existing) => existing.to_vec(),
                MapSelector::Known(_) => unreachable!(),
            };
            combined.extend_from_slice(excluded);
            MapSelector::dynamic_excluding(combined)
        }
    }
}

fn append_origin_path(origin: &mut InputFlowOrigin, suffix: &[InputPathStep]) {
    let path = match origin {
        InputFlowOrigin::Input(position) => &mut position.path,
        InputFlowOrigin::CallResult { path, .. } => path,
    };
    *path = path
        .iter()
        .cloned()
        .chain(suffix.iter().cloned())
        .collect::<Vec<_>>()
        .into_boxed_slice();
}

/// Returns the path suffix each side contributes when two semantic positions
/// intersect. Exactly one suffix is nonempty for ordinary prefix composition;
/// typed dynamic selectors and map remainders intersect at their shared step.
pub(super) type PathResiduals = (Box<[InputPathStep]>, Box<[InputPathStep]>);

pub(super) fn compose_paths(left: &[InputPathStep], right: &[InputPathStep]) -> Option<PathResiduals> {
    let common = left.len().min(right.len());
    for (index, (left_step, right_step)) in left.iter().zip(right).take(common).enumerate() {
        match (left_step, right_step) {
            (InputPathStep::MapRemainder(excluded), InputPathStep::MapValue(selector))
                if !matches!(selector, MapSelector::Known(_)) =>
            {
                return Some((
                    std::iter::once(InputPathStep::MapValue(exclude_map_keys(selector, excluded)))
                        .chain(right[index + 1..].iter().cloned())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    left[index + 1..].to_vec().into_boxed_slice(),
                ));
            }
            (InputPathStep::MapValue(selector), InputPathStep::MapRemainder(excluded))
                if !matches!(selector, MapSelector::Known(_)) =>
            {
                return Some((
                    right[index + 1..].to_vec().into_boxed_slice(),
                    std::iter::once(InputPathStep::MapValue(exclude_map_keys(selector, excluded)))
                        .chain(left[index + 1..].iter().cloned())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                ));
            }
            _ => {}
        }
        if left_step == right_step || path_steps_intersect(left_step, right_step) {
            continue;
        }
        match (left_step, right_step) {
            (InputPathStep::MapRemainder(excluded), InputPathStep::MapValue(MapSelector::Known(key)))
                if !excluded.contains(key) =>
            {
                return Some((
                    std::iter::once(right_step.clone())
                        .chain(right[index + 1..].iter().cloned())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    left[index + 1..].to_vec().into_boxed_slice(),
                ));
            }
            (InputPathStep::MapValue(MapSelector::Known(key)), InputPathStep::MapRemainder(excluded))
                if !excluded.contains(key) =>
            {
                return Some((
                    right[index + 1..].to_vec().into_boxed_slice(),
                    std::iter::once(left_step.clone())
                        .chain(left[index + 1..].iter().cloned())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                ));
            }
            (InputPathStep::MapRemainder(left_excluded), InputPathStep::MapRemainder(right_excluded)) => {
                let mut excluded = left_excluded
                    .iter()
                    .chain(right_excluded.iter())
                    .cloned()
                    .collect::<Vec<_>>();
                excluded.sort_unstable();
                excluded.dedup();
                return Some((
                    std::iter::once(InputPathStep::MapRemainder(excluded.into_boxed_slice()))
                        .chain(right[index + 1..].iter().cloned())
                        .collect::<Vec<_>>()
                        .into_boxed_slice(),
                    left[index + 1..].to_vec().into_boxed_slice(),
                ));
            }
            _ => return None,
        }
    }
    Some((
        right[common..].to_vec().into_boxed_slice(),
        left[common..].to_vec().into_boxed_slice(),
    ))
}

fn path_steps_intersect(left: &InputPathStep, right: &InputPathStep) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (InputPathStep::MapValue(left), InputPathStep::MapValue(right))
        | (InputPathStep::MapKey(left), InputPathStep::MapKey(right))
        | (InputPathStep::MapKey(left), InputPathStep::MapValue(right))
        | (InputPathStep::MapValue(left), InputPathStep::MapKey(right))
            if map_selectors_intersect(left, right) =>
        {
            true
        }
        (
            InputPathStep::BitstringField(super::keying::BitstringSelector::Dynamic),
            InputPathStep::BitstringField(_),
        )
        | (
            InputPathStep::BitstringField(_),
            InputPathStep::BitstringField(super::keying::BitstringSelector::Dynamic),
        ) => true,
        (InputPathStep::MapRemainder(_), InputPathStep::MapValue(selector))
        | (InputPathStep::MapValue(selector), InputPathStep::MapRemainder(_))
            if !matches!(selector, MapSelector::Known(_)) =>
        {
            true
        }
        _ => false,
    }
}

fn map_selectors_intersect(left: &MapSelector, right: &MapSelector) -> bool {
    match (left, right) {
        (MapSelector::Known(left), MapSelector::Known(right)) => left == right,
        (MapSelector::Known(key), MapSelector::DynamicExcept(excluded))
        | (MapSelector::DynamicExcept(excluded), MapSelector::Known(key)) => !excluded.contains(key),
        (MapSelector::Known(_), MapSelector::Dynamic)
        | (MapSelector::Dynamic, MapSelector::Known(_))
        | (MapSelector::Dynamic, MapSelector::Dynamic)
        | (MapSelector::Dynamic, MapSelector::DynamicExcept(_))
        | (MapSelector::DynamicExcept(_), MapSelector::Dynamic)
        | (MapSelector::DynamicExcept(_), MapSelector::DynamicExcept(_)) => true,
    }
}

#[cfg(test)]
mod tests {
    use super::super::body::{
        CallArg, ControlDestination, ControlEntryId, ControlEntryOrigin, LoweredClause, LoweredEntry,
    };
    use super::super::world::World;
    use super::*;
    use crate::ground_value::GroundValue;
    use crate::source::Span;

    fn value(raw: u32) -> ValueId {
        ValueId::from_u32(raw)
    }

    fn lineages(steps: &[LoweredStep], output: ValueId) -> BTreeSet<ValueLineage> {
        let mut definitions = (0..4)
            .map(|input| {
                (
                    value(input as u32),
                    vec![ValueTransfer::Origin(InputFlowOrigin::Input(InputPosition::root(
                        input,
                    )))],
                )
            })
            .collect::<HashMap<_, _>>();
        let mut aliases = HashMap::new();
        for step in steps {
            collect_value_transfers(step, &mut definitions, &mut aliases);
        }
        resolve_value_lineage(
            output,
            &definitions,
            Some(&aliases),
            &mut HashMap::new(),
            &mut HashSet::new(),
        )
    }

    fn input_lineage(input: usize, path: Vec<InputPathStep>) -> ValueLineage {
        ValueLineage {
            origin: InputFlowOrigin::Input(InputPosition {
                input,
                path: path.into_boxed_slice(),
            }),
            destination: Box::default(),
            pullback: InputPullback::Structural,
        }
    }

    fn dependency_lineage(input: usize, destination: Vec<InputPathStep>) -> ValueLineage {
        ValueLineage {
            origin: InputFlowOrigin::Input(InputPosition::root(input)),
            destination: destination.into_boxed_slice(),
            pullback: InputPullback::WholeOrigin,
        }
    }

    fn entry(origin: ControlEntryOrigin, steps: Vec<LoweredStep>, tail: LoweredTail) -> LoweredEntry {
        LoweredEntry {
            span: Span::DUMMY,
            origin,
            params: Vec::new(),
            captures: Vec::new(),
            reusable_cons_captures: Vec::new(),
            steps,
            tail,
        }
    }

    #[test]
    fn reconstruction_and_projection_share_one_typed_path_algebra() {
        let list = value(10);
        let head = value(11);
        let tail = value(12);
        assert_eq!(
            lineages(
                &[
                    LoweredStep::List {
                        value: list,
                        items: vec![value(0)],
                        tail: Some(value(1)),
                    },
                    LoweredStep::SplitList {
                        source: list,
                        head,
                        tail,
                    },
                ],
                head,
            ),
            BTreeSet::from([input_lineage(0, Vec::new())]),
        );
        assert_eq!(
            lineages(
                &[
                    LoweredStep::List {
                        value: list,
                        items: vec![value(0)],
                        tail: Some(value(1)),
                    },
                    LoweredStep::SplitList {
                        source: list,
                        head,
                        tail,
                    },
                ],
                tail,
            ),
            BTreeSet::from([input_lineage(1, Vec::new())]),
        );

        let key = LoweredMapKey {
            value: value(3),
            literal: None,
        };
        let indexed = value(13);
        assert_eq!(
            lineages(
                &[LoweredStep::MapIndex {
                    value: indexed,
                    base: value(0),
                    key,
                }],
                indexed,
            ),
            BTreeSet::from([
                input_lineage(0, vec![InputPathStep::MapValue(MapSelector::Dynamic)]),
                dependency_lineage(3, Vec::new()),
            ]),
        );

        let indexed_field = value(18);
        assert_eq!(
            lineages(
                &[
                    LoweredStep::MapIndex {
                        value: indexed,
                        base: value(0),
                        key: LoweredMapKey {
                            value: value(3),
                            literal: None,
                        },
                    },
                    LoweredStep::TupleField {
                        value: indexed_field,
                        source: indexed,
                        index: 0,
                    },
                ],
                indexed_field,
            ),
            BTreeSet::from([
                input_lineage(
                    0,
                    vec![
                        InputPathStep::MapValue(MapSelector::Dynamic),
                        InputPathStep::TupleField(0)
                    ],
                ),
                dependency_lineage(3, Vec::new()),
            ]),
        );

        let reconstructed_key = value(20);
        let reconstructed_index = value(21);
        let reconstructed_field = value(22);
        assert_eq!(
            lineages(
                &[
                    LoweredStep::Tuple {
                        value: reconstructed_key,
                        items: vec![value(0), value(1)],
                    },
                    LoweredStep::MapIndex {
                        value: reconstructed_index,
                        base: value(2),
                        key: LoweredMapKey {
                            value: reconstructed_key,
                            literal: None,
                        },
                    },
                    LoweredStep::TupleField {
                        value: reconstructed_field,
                        source: reconstructed_index,
                        index: 0,
                    },
                ],
                reconstructed_field,
            ),
            BTreeSet::from([
                dependency_lineage(0, Vec::new()),
                dependency_lineage(1, Vec::new()),
                input_lineage(
                    2,
                    vec![
                        InputPathStep::MapValue(MapSelector::Dynamic),
                        InputPathStep::TupleField(0)
                    ],
                ),
            ]),
        );

        let constructed = value(19);
        assert_eq!(
            lineages(
                &[LoweredStep::Map {
                    value: constructed,
                    entries: vec![(
                        LoweredMapKey {
                            value: value(2),
                            literal: None,
                        },
                        value(1),
                    )],
                }],
                constructed,
            ),
            BTreeSet::from([
                dependency_lineage(2, vec![InputPathStep::MapKey(MapSelector::Dynamic)]),
                ValueLineage {
                    origin: InputFlowOrigin::Input(InputPosition::root(1)),
                    destination: vec![InputPathStep::MapValue(MapSelector::Dynamic)].into_boxed_slice(),
                    pullback: InputPullback::Structural,
                },
            ]),
        );

        let reconstructed_map_key = value(23);
        let constructed_with_reconstructed_key = value(24);
        assert_eq!(
            lineages(
                &[
                    LoweredStep::Tuple {
                        value: reconstructed_map_key,
                        items: vec![value(0), value(1)],
                    },
                    LoweredStep::Map {
                        value: constructed_with_reconstructed_key,
                        entries: vec![(
                            LoweredMapKey {
                                value: reconstructed_map_key,
                                literal: None,
                            },
                            value(2),
                        )],
                    },
                ],
                constructed_with_reconstructed_key,
            ),
            BTreeSet::from([
                dependency_lineage(0, vec![InputPathStep::MapKey(MapSelector::Dynamic)]),
                dependency_lineage(1, vec![InputPathStep::MapKey(MapSelector::Dynamic)]),
                ValueLineage {
                    origin: InputFlowOrigin::Input(InputPosition::root(2)),
                    destination: vec![InputPathStep::MapValue(MapSelector::Dynamic)].into_boxed_slice(),
                    pullback: InputPullback::Structural,
                },
            ]),
        );

        let field = value(14);
        let required = value(15);
        let atom = InputMapKey::Atom("name".to_string());
        for step in [
            LoweredStep::FieldAccess {
                value: field,
                base: value(0),
                field: "name".to_string(),
            },
            LoweredStep::RequireMapValue {
                value: required,
                source: value(0),
                key: GroundValue::Atom("name".to_string()),
            },
        ] {
            let output = match &step {
                LoweredStep::FieldAccess { value, .. } | LoweredStep::RequireMapValue { value, .. } => *value,
                _ => unreachable!(),
            };
            assert_eq!(
                lineages(&[step], output),
                BTreeSet::from([input_lineage(
                    0,
                    vec![InputPathStep::MapValue(MapSelector::Known(atom.clone()))],
                )]),
            );
        }

        let structured = value(16);
        let projected = value(17);
        assert_eq!(
            lineages(
                &[
                    LoweredStep::Struct {
                        value: structured,
                        module: super::super::identity::ModuleId::for_test(9),
                        fields: vec![("name".to_string(), value(2))],
                    },
                    LoweredStep::FieldAccess {
                        value: projected,
                        base: structured,
                        field: "name".to_string(),
                    },
                ],
                projected,
            ),
            BTreeSet::from([input_lineage(2, Vec::new())]),
        );
    }

    #[test]
    fn every_literal_map_key_keeps_exact_lookup_and_last_writer_identity() {
        assert_ne!(
            InputMapKey::from_ground(&GroundValue::Float(0.0_f64.to_bits())),
            InputMapKey::from_ground(&GroundValue::Float((-0.0_f64).to_bits())),
        );
        let map = value(10);
        let indexed = value(11);
        let key = |literal: GroundValue| LoweredMapKey {
            value: value(3),
            literal: Some(literal),
        };

        for (written, lookup, other) in [
            (GroundValue::Int(1), GroundValue::Int(1), GroundValue::Int(2)),
            (
                GroundValue::Float(1.5_f64.to_bits()),
                GroundValue::Float(1.5_f64.to_bits()),
                GroundValue::Float(2.5_f64.to_bits()),
            ),
            (
                GroundValue::Atom("a".to_string()),
                GroundValue::Atom("a".to_string()),
                GroundValue::Atom("b".to_string()),
            ),
            (
                GroundValue::Atom("true".to_string()),
                GroundValue::Bool(true),
                GroundValue::Bool(false),
            ),
            (
                GroundValue::Atom("nil".to_string()),
                GroundValue::Nil,
                GroundValue::Atom("other".to_string()),
            ),
            (
                GroundValue::Binary(b"a".to_vec()),
                GroundValue::Utf8Binary(b"a".to_vec()),
                GroundValue::Binary(b"b".to_vec()),
            ),
        ] {
            for steps in [
                vec![
                    LoweredStep::Map {
                        value: map,
                        entries: vec![(key(written.clone()), value(0)), (key(other.clone()), value(1))],
                    },
                    LoweredStep::MapIndex {
                        value: indexed,
                        base: map,
                        key: key(lookup.clone()),
                    },
                ],
                vec![
                    LoweredStep::MapUpdate {
                        value: map,
                        base: value(2),
                        entries: vec![(key(written.clone()), value(0))],
                    },
                    LoweredStep::MapIndex {
                        value: indexed,
                        base: map,
                        key: key(lookup.clone()),
                    },
                ],
                vec![
                    LoweredStep::Map {
                        value: map,
                        entries: vec![(key(written.clone()), value(1)), (key(lookup.clone()), value(0))],
                    },
                    LoweredStep::MapIndex {
                        value: indexed,
                        base: map,
                        key: key(lookup.clone()),
                    },
                ],
            ] {
                assert_eq!(
                    lineages(&steps, indexed),
                    BTreeSet::from([input_lineage(0, Vec::new())])
                );
            }
        }
    }

    #[test]
    fn path_intersection_preserves_residuals_and_rejects_disjoint_selectors() {
        let atom = InputMapKey::Atom("a".to_string());
        let other = InputMapKey::Atom("b".to_string());
        let dynamic = InputPathStep::MapValue(MapSelector::Dynamic);
        let known = InputPathStep::MapValue(MapSelector::Known(atom.clone()));
        let except = InputPathStep::MapValue(MapSelector::DynamicExcept(vec![atom.clone()].into_boxed_slice()));
        let known_other = InputPathStep::MapValue(MapSelector::Known(other.clone()));
        assert_eq!(MapSelector::dynamic_excluding(Vec::new()), MapSelector::Dynamic);
        let cases = [
            (
                vec![InputPathStep::TupleField(0)],
                vec![InputPathStep::TupleField(0), InputPathStep::ListHead],
                Some((vec![InputPathStep::ListHead], Vec::new())),
            ),
            (
                vec![InputPathStep::TupleField(0), InputPathStep::ListHead],
                vec![InputPathStep::TupleField(0)],
                Some((Vec::new(), vec![InputPathStep::ListHead])),
            ),
            (
                vec![InputPathStep::TupleField(0)],
                vec![InputPathStep::TupleField(1)],
                None,
            ),
            (vec![InputPathStep::ListHead], vec![InputPathStep::ListTail], None),
            (vec![dynamic], vec![known.clone()], Some((Vec::new(), Vec::new()))),
            (vec![except.clone()], vec![known], None),
            (vec![except], vec![known_other.clone()], Some((Vec::new(), Vec::new()))),
            (
                vec![InputPathStep::MapRemainder(vec![atom.clone()].into_boxed_slice())],
                vec![InputPathStep::MapValue(MapSelector::Dynamic)],
                Some((
                    vec![InputPathStep::MapValue(MapSelector::dynamic_excluding(vec![
                        atom.clone(),
                    ]))],
                    Vec::new(),
                )),
            ),
            (
                vec![InputPathStep::MapRemainder(vec![atom.clone()].into_boxed_slice())],
                vec![InputPathStep::MapValue(MapSelector::Known(other.clone()))],
                Some((vec![known_other], Vec::new())),
            ),
            (
                vec![InputPathStep::MapRemainder(vec![atom.clone()].into_boxed_slice())],
                vec![InputPathStep::MapRemainder(vec![other.clone()].into_boxed_slice())],
                Some((
                    vec![InputPathStep::MapRemainder(vec![atom, other].into_boxed_slice())],
                    Vec::new(),
                )),
            ),
            (
                vec![InputPathStep::BitstringField(
                    super::super::keying::BitstringSelector::Dynamic,
                )],
                vec![InputPathStep::BitstringField(
                    super::super::keying::BitstringSelector::Known(1),
                )],
                Some((Vec::new(), Vec::new())),
            ),
            (
                vec![InputPathStep::BitstringField(
                    super::super::keying::BitstringSelector::Known(1),
                )],
                vec![InputPathStep::BitstringField(
                    super::super::keying::BitstringSelector::Known(2),
                )],
                None,
            ),
        ];
        for (left, right, expected) in cases {
            assert_eq!(
                compose_paths(&left, &right),
                expected.map(|(right, left)| (right.into_boxed_slice(), left.into_boxed_slice())),
            );
        }
    }

    #[test]
    fn extraction_normalizes_direct_result_reconstruction_and_callable_endpoints() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::identity::ModuleId::GLOBAL, "caller", 2);
        let callee = world.reference_function(super::super::identity::ModuleId::GLOBAL, "callee", 2);
        let lambda = world.reference_function(super::super::identity::ModuleId::GLOBAL, "lambda", 1);
        let callsite = CallSiteId::from_u32(7);
        let rebuilt = value(10);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: vec![value(0), value(1)],
                    projections: Vec::new(),
                    entry: ControlEntryId::from_u32(0),
                }],
                entries: vec![entry(
                    ControlEntryOrigin::Clause,
                    vec![
                        LoweredStep::Tuple {
                            value: rebuilt,
                            items: vec![value(1), value(0)],
                        },
                        LoweredStep::Lambda {
                            value: value(11),
                            function: lambda,
                            captures: vec![value(1)],
                        },
                    ],
                    LoweredTail::DirectCall {
                        value: value(12),
                        callsite,
                        callee,
                        args: vec![
                            CallArg {
                                value: rebuilt,
                                ascription: None,
                            },
                            CallArg {
                                value: value(0),
                                ascription: None,
                            },
                        ],
                        dest: ControlDestination::Return,
                    },
                )],
                generated: Vec::new(),
            },
        );
        let relation = extract_input_flow_relation(&world, caller, vec![DispatchDemand::Ignore; 2].into_boxed_slice());
        assert_eq!(
            relation.direct_calls,
            BTreeMap::from([(
                callsite,
                DirectCallFlow {
                    callee,
                    inputs: vec![
                        BTreeSet::from([
                            InputBinding {
                                origin: InputFlowOrigin::Input(InputPosition::root(0)),
                                path: vec![InputPathStep::TupleField(1)].into_boxed_slice(),
                                pullback: InputPullback::Structural,
                            },
                            InputBinding {
                                origin: InputFlowOrigin::Input(InputPosition::root(1)),
                                path: vec![InputPathStep::TupleField(0)].into_boxed_slice(),
                                pullback: InputPullback::Structural,
                            },
                        ]),
                        BTreeSet::from([InputBinding {
                            origin: InputFlowOrigin::Input(InputPosition::root(0)),
                            path: Box::default(),
                            pullback: InputPullback::Structural,
                        }]),
                    ]
                    .into_boxed_slice(),
                },
            )]),
        );
        let expected_flows = BTreeSet::from([
            InputFlow {
                origin: InputFlowOrigin::CallResult {
                    callsite,
                    path: Box::default(),
                },
                sink: InputFlowSink::FunctionReturn(Box::default()),
                pullback: InputPullback::Structural,
            },
            InputFlow {
                origin: InputFlowOrigin::Input(InputPosition::root(1)),
                sink: InputFlowSink::CallableUse {
                    site: CallableInputUse::LambdaCapture {
                        function: lambda,
                        capture: 0,
                    },
                    path: Box::default(),
                },
                pullback: InputPullback::Structural,
            },
        ]);
        assert_eq!(
            relation.local_dispatch.as_ref(),
            [DispatchDemand::Ignore, DispatchDemand::Ignore]
        );
        assert_eq!(relation.flows, expected_flows);
    }

    #[test]
    fn delivery_links_only_the_exact_used_call_result_despite_child_first_entries() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::identity::ModuleId::GLOBAL, "deliver", 1);
        let callee = world.reference_function(super::super::identity::ModuleId::GLOBAL, "produce", 1);
        let callsite = CallSiteId::from_u32(8);
        let resume = ControlEntryId::from_u32(0);
        let body = |used| LoweredBody::Clauses {
            clauses: vec![LoweredClause {
                span: Span::DUMMY,
                params: vec![value(0)],
                projections: Vec::new(),
                entry: ControlEntryId::from_u32(1),
            }],
            entries: vec![
                entry(
                    ControlEntryOrigin::DeliveredResume { value: value(9) },
                    Vec::new(),
                    if used {
                        LoweredTail::Value {
                            value: value(9),
                            dest: ControlDestination::Return,
                        }
                    } else {
                        LoweredTail::Halt {
                            atom: "discarded".to_string(),
                        }
                    },
                ),
                entry(
                    ControlEntryOrigin::Clause,
                    Vec::new(),
                    LoweredTail::DirectCall {
                        value: value(10),
                        callsite,
                        callee,
                        args: vec![CallArg {
                            value: value(0),
                            ascription: None,
                        }],
                        dest: ControlDestination::Deliver(resume),
                    },
                ),
            ],
            generated: Vec::new(),
        };
        world.define_lowered_body(caller, body(true));
        let used = extract_input_flow_relation(&world, caller, Box::from([DispatchDemand::Ignore]));
        let result = InputFlow {
            origin: InputFlowOrigin::CallResult {
                callsite,
                path: Box::default(),
            },
            sink: InputFlowSink::FunctionReturn(Box::default()),
            pullback: InputPullback::Structural,
        };
        assert!(used.flows.contains(&result));
        world.define_lowered_body(caller, body(false));
        let discarded = extract_input_flow_relation(&world, caller, Box::from([DispatchDemand::Ignore]));
        assert!(!discarded.flows.contains(&result));
    }

    #[test]
    fn branch_deliveries_resolve_predecessor_aliases_without_cross_arm_leakage() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::identity::ModuleId::GLOBAL, "merge", 4);
        let callee = world.reference_function(super::super::identity::ModuleId::GLOBAL, "consume", 3);
        let lambda_left = world.reference_function(super::super::identity::ModuleId::GLOBAL, "left_capture", 1);
        let lambda_right = world.reference_function(super::super::identity::ModuleId::GLOBAL, "right_capture", 1);
        let callsite = CallSiteId::from_u32(20);
        let resume = ControlEntryId::from_u32(0);
        let left = ControlEntryId::from_u32(1);
        let right = ControlEntryId::from_u32(2);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: vec![value(0), value(1), value(2), value(3)],
                    projections: Vec::new(),
                    entry: ControlEntryId::from_u32(3),
                }],
                entries: vec![
                    entry(
                        ControlEntryOrigin::DeliveredResume { value: value(20) },
                        vec![
                            LoweredStep::Lambda {
                                value: value(21),
                                function: lambda_left,
                                captures: vec![value(1)],
                            },
                            LoweredStep::Lambda {
                                value: value(22),
                                function: lambda_right,
                                captures: vec![value(2)],
                            },
                        ],
                        LoweredTail::DirectCall {
                            value: value(23),
                            callsite,
                            callee,
                            args: [value(20), value(1), value(2)]
                                .into_iter()
                                .map(|value| CallArg {
                                    value,
                                    ascription: None,
                                })
                                .collect(),
                            dest: ControlDestination::Return,
                        },
                    ),
                    entry(
                        ControlEntryOrigin::Branch,
                        vec![LoweredStep::AssertSame {
                            source: value(0),
                            value: value(1),
                        }],
                        LoweredTail::Value {
                            value: value(1),
                            dest: ControlDestination::Deliver(resume),
                        },
                    ),
                    entry(
                        ControlEntryOrigin::Branch,
                        vec![LoweredStep::AssertSame {
                            source: value(0),
                            value: value(2),
                        }],
                        LoweredTail::Value {
                            value: value(2),
                            dest: ControlDestination::Deliver(resume),
                        },
                    ),
                    entry(
                        ControlEntryOrigin::Clause,
                        Vec::new(),
                        LoweredTail::If {
                            cond: value(3),
                            then_entry: left,
                            else_entry: right,
                        },
                    ),
                ],
                generated: Vec::new(),
            },
        );

        let relation = extract_input_flow_relation(&world, caller, vec![DispatchDemand::Ignore; 4].into_boxed_slice());
        let origins = |input: usize| {
            relation.direct_calls[&callsite].inputs[input]
                .iter()
                .filter_map(|binding| match &binding.origin {
                    InputFlowOrigin::Input(position) => Some(position.input),
                    InputFlowOrigin::CallResult { .. } => None,
                })
                .collect::<BTreeSet<_>>()
        };
        assert_eq!(origins(0), BTreeSet::from([0, 1, 2]));
        assert_eq!(origins(1), BTreeSet::from([1]));
        assert_eq!(origins(2), BTreeSet::from([2]));
        for (function, expected) in [(lambda_left, 1), (lambda_right, 2)] {
            let actual = relation
                .flows
                .iter()
                .filter_map(|flow| match (&flow.origin, &flow.sink) {
                    (
                        InputFlowOrigin::Input(position),
                        InputFlowSink::CallableUse {
                            site: CallableInputUse::LambdaCapture { function: found, .. },
                            ..
                        },
                    ) if *found == function => Some(position.input),
                    _ => None,
                })
                .collect::<BTreeSet<_>>();
            assert_eq!(actual, BTreeSet::from([expected]));
        }
    }

    #[test]
    fn closure_call_records_callable_identity_and_return_without_inventing_input_flow() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::identity::ModuleId::GLOBAL, "invoke", 1);
        let callsite = CallSiteId::from_u32(12);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: vec![value(0)],
                    projections: Vec::new(),
                    entry: ControlEntryId::from_u32(0),
                }],
                entries: vec![entry(
                    ControlEntryOrigin::Clause,
                    Vec::new(),
                    LoweredTail::ClosureCall {
                        value: value(1),
                        callsite,
                        callee: value(0),
                        args: Vec::new(),
                        dest: ControlDestination::Return,
                    },
                )],
                generated: Vec::new(),
            },
        );
        let relation = extract_input_flow_relation(&world, caller, Box::from([DispatchDemand::Ignore]));
        assert!(relation.direct_calls.is_empty());
        assert_eq!(
            relation.flows,
            BTreeSet::from([
                InputFlow {
                    origin: InputFlowOrigin::Input(InputPosition::root(0)),
                    sink: InputFlowSink::CallableUse {
                        site: CallableInputUse::ClosureCall(callsite),
                        path: Box::default(),
                    },
                    pullback: InputPullback::Structural,
                },
                InputFlow {
                    origin: InputFlowOrigin::CallResult {
                        callsite,
                        path: Box::default(),
                    },
                    sink: InputFlowSink::FunctionReturn(Box::default()),
                    pullback: InputPullback::Structural,
                },
            ]),
        );
    }

    #[test]
    fn direct_call_records_zero_constant_and_mixed_inputs_without_synthetic_edges() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::identity::ModuleId::GLOBAL, "calls", 1);
        let zero = world.reference_function(super::super::identity::ModuleId::GLOBAL, "zero", 0);
        let constant = world.reference_function(super::super::identity::ModuleId::GLOBAL, "constant", 1);
        let mixed = world.reference_function(super::super::identity::ModuleId::GLOBAL, "mixed", 2);
        let zero_site = CallSiteId::from_u32(20);
        let constant_site = CallSiteId::from_u32(21);
        let mixed_site = CallSiteId::from_u32(22);
        let resume = ControlEntryId::from_u32(0);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: vec![value(0)],
                    projections: Vec::new(),
                    entry: ControlEntryId::from_u32(3),
                }],
                entries: vec![
                    entry(
                        ControlEntryOrigin::DeliveredResume { value: value(30) },
                        Vec::new(),
                        LoweredTail::DirectCall {
                            value: value(31),
                            callsite: constant_site,
                            callee: constant,
                            args: vec![CallArg {
                                value: value(9),
                                ascription: None,
                            }],
                            dest: ControlDestination::Return,
                        },
                    ),
                    entry(
                        ControlEntryOrigin::DeliveredResume { value: value(32) },
                        vec![
                            LoweredStep::Const {
                                value: value(9),
                                literal: GroundValue::Atom("local".to_string()),
                            },
                            LoweredStep::TupleField {
                                value: value(8),
                                source: value(0),
                                index: 1,
                            },
                        ],
                        LoweredTail::DirectCall {
                            value: value(33),
                            callsite: mixed_site,
                            callee: mixed,
                            args: vec![
                                CallArg {
                                    value: value(9),
                                    ascription: None,
                                },
                                CallArg {
                                    value: value(8),
                                    ascription: None,
                                },
                            ],
                            dest: ControlDestination::Deliver(resume),
                        },
                    ),
                    entry(
                        ControlEntryOrigin::DeliveredResume { value: value(34) },
                        Vec::new(),
                        LoweredTail::DirectCall {
                            value: value(35),
                            callsite: zero_site,
                            callee: zero,
                            args: Vec::new(),
                            dest: ControlDestination::Deliver(ControlEntryId::from_u32(1)),
                        },
                    ),
                    entry(
                        ControlEntryOrigin::Clause,
                        Vec::new(),
                        LoweredTail::Value {
                            value: value(0),
                            dest: ControlDestination::Deliver(ControlEntryId::from_u32(2)),
                        },
                    ),
                ],
                generated: Vec::new(),
            },
        );
        let relation = extract_input_flow_relation(&world, caller, Box::from([DispatchDemand::Ignore]));
        assert_eq!(relation.direct_calls[&zero_site].inputs.len(), 0);
        assert_eq!(relation.direct_calls[&constant_site].inputs.as_ref(), [BTreeSet::new()]);
        assert_eq!(
            relation.direct_calls[&mixed_site].inputs.as_ref(),
            [
                BTreeSet::new(),
                BTreeSet::from([InputBinding {
                    origin: InputFlowOrigin::Input(InputPosition {
                        input: 0,
                        path: vec![InputPathStep::TupleField(1)].into_boxed_slice(),
                    }),
                    path: Box::default(),
                    pullback: InputPullback::Structural,
                }]),
            ],
        );
    }

    #[test]
    fn direct_call_keeps_every_origin_of_a_reconstructed_dynamic_map_key() {
        let mut world = World::new();
        let caller = world.reference_function(super::super::identity::ModuleId::GLOBAL, "construct", 3);
        let callee = world.reference_function(super::super::identity::ModuleId::GLOBAL, "consume_map", 1);
        let callsite = CallSiteId::from_u32(40);
        let key = value(10);
        let map = value(11);
        world.define_lowered_body(
            caller,
            LoweredBody::Clauses {
                clauses: vec![LoweredClause {
                    span: Span::DUMMY,
                    params: vec![value(0), value(1), value(2)],
                    projections: Vec::new(),
                    entry: ControlEntryId::from_u32(0),
                }],
                entries: vec![entry(
                    ControlEntryOrigin::Clause,
                    vec![
                        LoweredStep::Tuple {
                            value: key,
                            items: vec![value(0), value(1)],
                        },
                        LoweredStep::Map {
                            value: map,
                            entries: vec![(
                                LoweredMapKey {
                                    value: key,
                                    literal: None,
                                },
                                value(2),
                            )],
                        },
                    ],
                    LoweredTail::DirectCall {
                        value: value(12),
                        callsite,
                        callee,
                        args: vec![CallArg {
                            value: map,
                            ascription: None,
                        }],
                        dest: ControlDestination::Return,
                    },
                )],
                generated: Vec::new(),
            },
        );

        let relation = extract_input_flow_relation(&world, caller, vec![DispatchDemand::Ignore; 3].into_boxed_slice());

        assert_eq!(
            relation.direct_calls[&callsite].inputs.as_ref(),
            [BTreeSet::from([
                InputBinding {
                    origin: InputFlowOrigin::Input(InputPosition::root(0)),
                    path: vec![InputPathStep::MapKey(MapSelector::Dynamic)].into_boxed_slice(),
                    pullback: InputPullback::WholeOrigin,
                },
                InputBinding {
                    origin: InputFlowOrigin::Input(InputPosition::root(1)),
                    path: vec![InputPathStep::MapKey(MapSelector::Dynamic)].into_boxed_slice(),
                    pullback: InputPullback::WholeOrigin,
                },
                InputBinding {
                    origin: InputFlowOrigin::Input(InputPosition::root(2)),
                    path: vec![InputPathStep::MapValue(MapSelector::Dynamic)].into_boxed_slice(),
                    pullback: InputPullback::Structural,
                },
            ])],
        );
    }

    #[test]
    fn extern_relation_retains_its_arity_sized_local_dispatch_mask() {
        let mut world = World::new();
        let function = world.reference_function(super::super::identity::ModuleId::GLOBAL, "extern_two", 2);
        let any = world.types_mut().any();
        world.define_lowered_body(
            function,
            LoweredBody::Extern {
                signature: super::super::body::LoweredExtern {
                    abi: "C".to_string(),
                    symbol: "extern_two".to_string(),
                    params: vec![crate::fz_ir::ExternTy::Any; 2],
                    variadic: false,
                    ret: crate::fz_ir::ExternTy::Any,
                    return_ty: any,
                    semantic_contract: crate::type_expr::ResolvedSpecDecl {
                        params: vec![any; 2],
                        result: any,
                        constraints: HashMap::new(),
                    },
                },
            },
        );
        let local_dispatch = vec![DispatchDemand::Ignore, DispatchDemand::Whole].into_boxed_slice();

        assert_eq!(
            extract_input_flow_relation(&world, function, local_dispatch.clone()),
            InputFlowRelation {
                local_dispatch,
                ..InputFlowRelation::default()
            },
        );
    }
}
