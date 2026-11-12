//! Which values of a body can share storage with a given value.
//!
//! Ownership asks, for each tuple item, whether any value used later could
//! overlap it. Asked of every later value, the answer costs a walk of the
//! origin chains per pair and the body's cost grows with the square of its
//! literals. Two values whose storage roots are disjoint cannot overlap, so
//! the index records each value's roots once and lets an item meet only the
//! values that share one.

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use super::{child_entries, construction_children, origin_source_path};
use crate::compiler2::body::{ControlEntryId, LoweredBody, LoweredStep, SubjectOriginRoot, ValueId, step_used_values};
use crate::compiler2::executable_facts::TransportOrigin;

/// Every storage root a value can be compared through. A value whose
/// provenance cannot be bounded is open: any comparison with it stays
/// conservative.
#[derive(Debug, Clone, Default)]
struct Footprint {
    roots: HashSet<SubjectOriginRoot>,
    open: bool,
}

type Origins = HashMap<ValueId, TransportOrigin>;

/// The footprints of every value a body uses, and the values that use each
/// root. Built once from the body and never changed.
pub(super) struct StorageRootIndex {
    footprints: HashMap<ValueId, Rc<Footprint>>,
    sites: HashMap<ValueId, Vec<(u32, u32)>>,
    users: HashMap<SubjectOriginRoot, Vec<ValueId>>,
    open_users: Vec<ValueId>,
}

impl StorageRootIndex {
    pub(super) fn new(body: &LoweredBody, origins: &Origins) -> Self {
        let LoweredBody::Clauses { entries, tables, .. } = body;
        let mut sites: HashMap<ValueId, Vec<(u32, u32)>> = HashMap::new();
        for entry in 0..entries.len() as u32 {
            for (step, value) in tables.entry_use_sites(ControlEntryId::from_u32(entry)) {
                sites.entry(*value).or_default().push((entry, *step));
            }
        }
        let mut footprints = Footprints::default();
        let mut users: HashMap<SubjectOriginRoot, Vec<ValueId>> = HashMap::new();
        let mut open_users = Vec::new();
        for &value in sites.keys() {
            let footprint = footprints.of(body, origins, value);
            if footprint.open {
                open_users.push(value);
            }
            for root in &footprint.roots {
                users.entry(*root).or_default().push(value);
            }
        }
        Self {
            footprints: footprints.known,
            sites,
            users,
            open_users,
        }
    }

    /// The values used after `later` that can share storage with `item`, or
    /// `None` when `item` is open and every later use must be asked.
    pub(super) fn competitors_after(&self, item: ValueId, later: &LaterUses<'_>) -> Option<Vec<ValueId>> {
        let footprint = &self.footprints[&item];
        if footprint.open {
            return None;
        }
        let sharing = footprint
            .roots
            .iter()
            .flat_map(|root| self.users.get(root).into_iter().flatten());
        let candidates = self.open_users.iter().chain(sharing).copied().collect::<HashSet<_>>();
        Some(
            candidates
                .into_iter()
                .filter(|value| self.used_after(*value, later))
                .collect(),
        )
    }

    fn used_after(&self, value: ValueId, later: &LaterUses<'_>) -> bool {
        self.sites
            .get(&value)
            .is_some_and(|sites| sites.iter().any(|&(entry, step)| later.contains(entry, step)))
    }
}

/// What can still happen after a step: the rest of its entry, and every entry
/// the entry reaches, which runs in full.
pub(super) struct LaterUses<'a> {
    entry: u32,
    step: u32,
    reached: &'a HashSet<u32>,
}

impl<'a> LaterUses<'a> {
    pub(super) fn after(entry: usize, step: usize, reached: &'a HashSet<u32>) -> Self {
        Self {
            entry: entry as u32,
            step: step as u32,
            reached,
        }
    }

    pub(super) fn entry(&self) -> usize {
        self.entry as usize
    }

    pub(super) fn step(&self) -> usize {
        self.step as usize
    }

    /// The sources whose ownership the list steps in this region retain.
    pub(super) fn retained_sources<'b>(&'b self, body: &'b LoweredBody) -> impl Iterator<Item = ValueId> + 'b {
        let LoweredBody::Clauses { tables, .. } = body;
        let rest = tables.entry_retentions_from(ControlEntryId::from_u32(self.entry), self.step + 1);
        let reached = self
            .reached
            .iter()
            .flat_map(|entry| tables.entry_retentions_from(ControlEntryId::from_u32(*entry), 0));
        rest.chain(reached)
    }

    fn contains(&self, entry: u32, step: u32) -> bool {
        if entry == self.entry {
            step > self.step
        } else {
            self.reached.contains(&entry)
        }
    }
}

/// The entries reachable from `entry` through its tail, not counting `entry`
/// itself.
pub(super) fn entries_reached_from(body: &LoweredBody, entry: usize) -> HashSet<u32> {
    let LoweredBody::Clauses { entries, .. } = body;
    let mut reached = HashSet::new();
    let mut pending = child_entries(&entries[entry].tail);
    while let Some(block) = pending.pop() {
        if block.as_u32() as usize != entry && reached.insert(block.as_u32()) {
            pending.extend(child_entries(&entries[block.as_u32() as usize].tail));
        }
    }
    reached
}

/// Footprints memoised as they are first needed. A value met again while its
/// own footprint is being computed is part of a cycle and makes the footprint
/// open.
#[derive(Default)]
struct Footprints {
    known: HashMap<ValueId, Rc<Footprint>>,
    in_progress: HashSet<ValueId>,
}

impl Footprints {
    fn of(&mut self, body: &LoweredBody, origins: &Origins, value: ValueId) -> Rc<Footprint> {
        if let Some(known) = self.known.get(&value) {
            return known.clone();
        }
        if !self.in_progress.insert(value) {
            return Rc::new(Footprint {
                roots: HashSet::new(),
                open: true,
            });
        }
        let mut footprint = Footprint {
            roots: HashSet::from([SubjectOriginRoot::Value(value)]),
            open: false,
        };
        let mut reaches = Vec::new();
        add_own_root(&mut footprint, body, origins, value);
        if let Some(origin) = origins.get(&value) {
            origin_reaches(body, origin, &mut reaches, &mut footprint);
        }
        reaches.extend(construction_children(body, origins, value));
        definition_reaches(body, origins, value, &mut reaches, &mut footprint);
        for reached in reaches {
            let reached = self.of(body, origins, reached);
            footprint.open |= reached.open;
            footprint.roots.extend(reached.roots.iter().copied());
        }
        self.in_progress.remove(&value);
        let footprint = Rc::new(footprint);
        self.known.insert(value, footprint.clone());
        footprint
    }
}

fn add_own_root(footprint: &mut Footprint, body: &LoweredBody, origins: &Origins, value: ValueId) {
    match origin_source_path(body, origins, &TransportOrigin::LocalValue(value)) {
        Some((root, _)) => {
            footprint.roots.insert(root);
        }
        None => footprint.open = true,
    }
}

/// The values a step's definition draws on. A value with neither an origin
/// nor a definition is unknown and so open.
fn definition_reaches(
    body: &LoweredBody,
    origins: &Origins,
    value: ValueId,
    reaches: &mut Vec<ValueId>,
    footprint: &mut Footprint,
) {
    let Some(step) = body.value_definition(value) else {
        footprint.open |= !origins.contains_key(&value);
        return;
    };
    step_used_values(step, reaches);
    if let LoweredStep::List {
        retention: Some(retention),
        ..
    } = step
    {
        reaches.push(retention.source);
        add_own_root(footprint, body, origins, retention.source);
    }
}

fn origin_reaches(body: &LoweredBody, origin: &TransportOrigin, reaches: &mut Vec<ValueId>, footprint: &mut Footprint) {
    match origin {
        TransportOrigin::LocalValue(value) | TransportOrigin::Projection { source: value, .. } => reaches.push(*value),
        TransportOrigin::OutcomeSubject { owner, subject } => match body.dispatch_subject_origin(*owner, *subject).0 {
            SubjectOriginRoot::Value(value) => reaches.push(value),
            root @ SubjectOriginRoot::MailboxMessage(_) => {
                footprint.roots.insert(root);
            }
        },
        TransportOrigin::Join(alternatives) => {
            for alternative in alternatives.iter() {
                origin_reaches(body, alternative, reaches, footprint);
            }
        }
        TransportOrigin::TupleValue(items) => reaches.extend(items.iter().copied()),
        TransportOrigin::CallableValue(producer) => reaches.extend(producer.captures.iter().copied()),
        TransportOrigin::ExecutableInput(_)
        | TransportOrigin::CallsiteReturn(_)
        | TransportOrigin::ClosureCallReturn { .. } => {}
    }
}
