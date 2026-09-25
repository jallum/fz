//! Rooted demand is a witness over the memo's committed membership edges.

use super::*;

mod dirty;
use dirty::DirtyWitness;

#[derive(Debug)]
pub(super) struct RootedProducts {
    seed: ProductKey,
    parents: HashMap<ProductKey, Option<ProductKey>>,
    children: HashMap<ProductKey, HashSet<ProductKey>>,
    pub(super) dirty: DirtyWitness,
    pub(super) changes: HashSet<ProductKey>,
    #[cfg(test)]
    last_detached: usize,
}

impl RootedProducts {
    fn mark_dirty(&mut self, key: &ProductKey) -> bool {
        self.dirty.insert(key.clone(), &self.parents)
    }

    fn visit_dirty(&self, mut blocked: impl FnMut(&ProductKey) -> bool) -> ProductValidation {
        let (mut cursor, visits) = self.dirty.first(&self.seed);
        let mut work = ProductValidation {
            witness_visits: visits,
            ..ProductValidation::default()
        };
        while let Some(key) = cursor {
            let blocked = self.dirty.contains(&key) && blocked(&key);
            cursor = self.dirty.next(&key, !blocked, &self.parents);
            work.witness_visits += u64::from(cursor.is_some());
        }
        self.collect_maintenance(&mut work);
        work
    }

    pub(super) fn collect_maintenance(&self, work: &mut ProductValidation) {
        let (updates, rewinds) = self.dirty.take_maintenance();
        work.witness_updates += updates;
        work.cursor_rewinds += rewinds;
    }

    fn new(seed: ProductKey) -> Self {
        Self {
            seed,
            parents: HashMap::new(),
            children: HashMap::new(),
            dirty: DirtyWitness::default(),
            changes: HashSet::new(),
            #[cfg(test)]
            last_detached: 0,
        }
    }

    fn attach(
        &mut self,
        memo: &ProductMemo,
        key: ProductKey,
        parent: Option<ProductKey>,
        types: &super::super::types::Types,
    ) -> HashSet<ProductKey> {
        let mut pending = vec![(key, parent)];
        let mut added = HashSet::new();
        while let Some((key, parent)) = pending.pop() {
            if self.parents.contains_key(&key) {
                continue;
            }
            if let Some(parent) = &parent {
                self.children.entry(parent.clone()).or_default().insert(key.clone());
            }
            self.parents.insert(key.clone(), parent);
            self.dirty.insert(key.clone(), &self.parents);
            self.changes.insert(key.clone());
            added.insert(key.clone());
            let mut children = memo.membership(&key).into_iter().flatten().collect::<Vec<_>>();
            children.sort_by(|left, right| right.semantic_cmp(left, types));
            pending.extend(children.into_iter().map(|child| (child.clone(), Some(key.clone()))));
        }
        added
    }

    fn below(&self, key: &ProductKey, ancestor: &ProductKey, work: &mut ProductValidation) -> bool {
        let mut cursor = Some(key);
        while let Some(key) = cursor {
            work.reparent_proof_nodes += 1;
            if key == ancestor {
                return true;
            }
            cursor = self.parents.get(key).and_then(Option::as_ref);
        }
        false
    }

    fn reparent(&mut self, key: &ProductKey, parent: ProductKey) {
        let previous = self.parents.get_mut(key).expect("only a reached member is reparented");
        if let Some(previous) = previous.replace(parent.clone()) {
            self.children
                .get_mut(&previous)
                .expect("witness child index")
                .remove(key);
            self.dirty.reparent(key, &previous, &parent, &self.parents);
        }
        self.children.entry(parent).or_default().insert(key.clone());
    }

    fn remove_edge(
        &mut self,
        memo: &ProductMemo,
        parent: &ProductKey,
        key: &ProductKey,
        types: &super::super::types::Types,
        reparented: &mut Vec<ProductKey>,
        work: &mut ProductValidation,
    ) -> HashSet<ProductKey> {
        if self.parents.get(key) != Some(&Some(parent.clone())) {
            return HashSet::new();
        }
        let mut leaf = None;
        if let Some(alternate) = memo
            .membership_readers
            .get(key)
            .into_iter()
            .flatten()
            .filter(|candidate| {
                work.reparent_candidates += 1;
                if *candidate == key || !self.parents.contains_key(*candidate) {
                    return false;
                }
                let leaf = *leaf.get_or_insert_with(|| {
                    work.reparent_proof_nodes += 1;
                    self.children.get(key).is_none_or(HashSet::is_empty)
                });
                leaf || !self.below(candidate, key, work)
            })
            .min_by(|left, right| left.semantic_cmp(right, types))
        {
            self.reparent(key, alternate.clone());
            reparented.push(key.clone());
            return HashSet::new();
        }
        let mut detached = HashMap::new();
        let mut pending = vec![key.clone()];
        while let Some(member) = pending.pop() {
            if detached
                .insert(
                    member.clone(),
                    (self.changes.contains(&member), self.dirty.contains(&member)),
                )
                .is_none()
            {
                pending.extend(self.children.remove(&member).into_iter().flatten());
            }
        }
        #[cfg(test)]
        {
            self.last_detached += detached.len();
        }
        self.children
            .get_mut(parent)
            .expect("removed witness has a parent")
            .remove(key);
        for member in detached.keys() {
            self.dirty.remove(member, &self.parents);
        }
        for member in detached.keys() {
            self.parents.remove(member);
        }
        let entrance_candidates = Cell::new(0);
        let mut entrances = detached
            .keys()
            .flat_map(|member| {
                memo.membership_readers
                    .get(member)
                    .into_iter()
                    .flatten()
                    .filter(|parent| {
                        entrance_candidates.set(entrance_candidates.get() + 1);
                        self.parents.contains_key(*parent)
                    })
                    .map(|parent| (member.clone(), parent.clone()))
            })
            .collect::<Vec<_>>();
        work.reparent_candidates += entrance_candidates.get();
        entrances.sort_by(|(left, parent), (right, next_parent)| {
            left.semantic_cmp(right, types)
                .then_with(|| parent.semantic_cmp(next_parent, types))
        });
        let mut touched = HashSet::new();
        for (member, parent) in entrances {
            if self.parents.contains_key(&member) {
                continue;
            }
            touched.extend(self.attach(memo, member.clone(), Some(parent), types));
            reparented.push(member);
        }
        for (member, (was_changed, was_dirty)) in detached {
            if self.parents.contains_key(&member) {
                // Restoration changes a proof, not a contribution.
                if !was_changed {
                    self.changes.remove(&member);
                }
                if !was_dirty {
                    self.dirty.remove(&member, &self.parents);
                }
                touched.remove(&member);
                continue;
            }
            self.changes.insert(member.clone());
            touched.insert(member);
        }
        touched
    }

    fn replace_edges(
        &mut self,
        memo: &ProductMemo,
        owner: &ProductKey,
        previous: &HashSet<ProductKey>,
        types: &super::super::types::Types,
        work: &mut ProductValidation,
    ) -> (HashSet<ProductKey>, Vec<ProductKey>) {
        #[cfg(test)]
        {
            self.last_detached = 0;
        }
        let next = memo
            .membership(owner)
            .expect("a successful member has committed dependencies");
        // New entry paths exist before obsolete support is repaired.
        let mut touched = HashSet::new();
        let mut reparented = Vec::new();
        let mut added = next.difference(previous).collect::<Vec<_>>();
        let mut removed = previous.difference(next).collect::<Vec<_>>();
        added.sort_by(|left, right| left.semantic_cmp(right, types));
        removed.sort_by(|left, right| left.semantic_cmp(right, types));
        for child in added {
            touched.extend(self.attach(memo, child.clone(), Some(owner.clone()), types));
        }
        for child in removed {
            touched.extend(self.remove_edge(memo, owner, child, types, &mut reparented, work));
        }
        (touched, reparented)
    }
}

impl ProductMemo {
    pub(super) fn begin_wait_frame_admissions(&mut self, reader: &ProductKey) {
        if let Some((_, request)) = self.live_rooted_wait_frame(reader) {
            let seed = self.rooted[reader].seed.clone();
            self.expose_waiting_branch(reader, request, seed, false);
        }
    }

    fn live_rooted_wait_frame(&self, reader: &ProductKey) -> Option<(usize, ProductRequestId)> {
        let pending = self.pending_dependencies.get(reader)?;
        let read = pending.dependencies.rooted_read?;
        (!read.delivered && read.controls_delivered).then_some((pending.waiting_frame?, pending.request))
    }

    fn expose_waiting_branch(
        &mut self,
        reader: &ProductKey,
        request: ProductRequestId,
        branch: ProductKey,
        reparented: bool,
    ) {
        let Some((position, current)) = self.live_rooted_wait_frame(reader) else {
            return;
        };
        if current != request {
            return;
        }
        let rooted = &self.rooted[reader];
        if !rooted.dirty.contains(&branch) && rooted.dirty.children(&branch).next().is_none() {
            return;
        }
        self.wait_frame_exposures.push(WaitFrameExposure {
            reader: reader.clone(),
            request,
            position,
            branch,
            reparented,
        });
    }

    pub(super) fn next_wait_frame_admission(
        &mut self,
        work: &mut ProductValidation,
    ) -> Option<(usize, ProductRequestId, ProductKey)> {
        while let Some(effect) = self.wait_frame_exposures.pop() {
            let WaitFrameExposure {
                reader,
                request,
                position,
                branch,
                reparented,
            } = effect;
            if self.live_rooted_wait_frame(&reader) != Some((position, request)) {
                continue;
            }
            let rooted = &self.rooted[&reader];
            if reparented {
                let mut parent = rooted.parents.get(&branch).and_then(Option::as_ref);
                let mut blocked = false;
                while let Some(key) = parent {
                    work.witness_visits += 1;
                    if rooted.dirty.contains(key) {
                        blocked = true;
                        break;
                    }
                    if rooted.dirty.on_clear_active_prefix(key) {
                        break;
                    }
                    parent = rooted.parents.get(key).and_then(Option::as_ref);
                }
                if blocked {
                    continue;
                }
            }
            work.witness_visits += 1;
            let current = self.get(&branch).is_some()
                && !self.has_unsettled_inputs(&branch)
                && self.rooted.get(&branch).is_none_or(|root| root.dirty.is_empty());
            let rooted = self.rooted.get_mut(&reader).expect("live waiting witness");
            if rooted.dirty.contains(&branch) && !current {
                let admitted = rooted.dirty.admit(&branch, request);
                rooted.collect_maintenance(work);
                if admitted {
                    return Some((position, request, branch));
                }
                continue;
            }
            for child in rooted.dirty.children(&branch) {
                self.wait_frame_exposures.push(WaitFrameExposure {
                    reader: reader.clone(),
                    request,
                    position,
                    branch: child.clone(),
                    reparented: false,
                });
            }
            rooted.dirty.remove(&branch, &rooted.parents);
            rooted.collect_maintenance(work);
        }
        None
    }

    pub(super) fn admit_wait_frame_product(
        &mut self,
        reader: &ProductKey,
        request: ProductRequestId,
        product: &ProductKey,
    ) {
        if self
            .live_rooted_wait_frame(reader)
            .is_some_and(|(_, origin)| origin == request)
        {
            self.rooted
                .get_mut(reader)
                .expect("live waiting witness")
                .dirty
                .admit(product, request);
        }
    }

    pub(super) fn release_wait_frame_product(
        &mut self,
        reader: &ProductKey,
        request: ProductRequestId,
        product: &ProductKey,
    ) {
        if let Some(rooted) = self.rooted.get_mut(reader) {
            rooted.dirty.release(product, request);
        }
    }

    pub(super) fn retire_rooted(&mut self, reader: &ProductKey) -> ProductValidation {
        let mut work = ProductValidation::default();
        let Some(mut rooted) = self.rooted.remove(reader) else {
            return work;
        };
        rooted.dirty.clear();
        rooted.collect_maintenance(&mut work);
        for member in rooted.parents.keys() {
            let readers = self.rooted_readers.get_mut(member).expect("registered member");
            readers.remove(reader);
            if readers.is_empty() {
                self.rooted_readers.remove(member);
            }
        }
        work
    }

    pub(super) fn rooted_member_dirty(&mut self, member: &ProductKey, work: &mut ProductValidation) -> Vec<ProductKey> {
        let readers = self.rooted_readers.get(member).cloned().unwrap_or_default();
        readers
            .into_iter()
            .filter(|reader| {
                work.mutation_edges += 1;
                let rooted = self.rooted.get_mut(reader).expect("registered root");
                let changed = rooted.mark_dirty(member);
                rooted.collect_maintenance(work);
                changed
            })
            .collect()
    }

    pub(super) fn rooted_member_refresh(
        &mut self,
        member: &ProductKey,
        work: &mut ProductValidation,
    ) -> Vec<ProductKey> {
        if self.has_unsettled_inputs(member) {
            return Vec::new();
        }
        let readers = self.rooted_readers.get(member).cloned().unwrap_or_default();
        readers
            .into_iter()
            .filter(|reader| {
                work.mutation_edges += 1;
                let rooted = self.rooted.get_mut(reader).expect("registered root");
                let waiting = rooted.dirty.waiting(member);
                let changed = rooted.dirty.remove(member, &rooted.parents)
                    && rooted.dirty.is_empty()
                    && rooted.changes.is_empty();
                rooted.collect_maintenance(work);
                if let Some(request) = waiting {
                    self.expose_waiting_branch(reader, request, member.clone(), false);
                }
                changed
            })
            .collect()
    }

    pub(super) fn rooted_stale_dependency(
        &mut self,
        tel: &impl Telemetry,
        reader: &ProductKey,
        visiting: &mut ProductValidationWalk,
        types: &super::super::types::Types,
        complete: bool,
    ) -> Option<ProductKey> {
        let rooted = self.rooted.get(reader)?;
        let (mut cursor, visits) = rooted.dirty.first(&rooted.seed);
        visiting.work.witness_visits += visits;
        let mut outcome = None;
        while let Some(member) = cursor {
            if self.get(&member).is_none() {
                outcome = Some(member);
                break;
            }
            if complete {
                if let Some(stale) = self.stale_dependency_inner(tel, &member, visiting, types, true) {
                    outcome = Some(stale);
                    break;
                }
                let rooted = &self.rooted[reader];
                cursor = rooted.dirty.next(&member, true, &rooted.parents);
                visiting.work.witness_visits += u64::from(cursor.is_some());
            } else {
                let mut member_walk = ProductValidationWalk::default();
                let stale = self.stale_dependency_inner(tel, &member, &mut member_walk, types, true);
                visiting
                    .work
                    .include(self.finish_validation(tel, member_walk, stale.is_none(), Some(reader), types));
                if stale.is_some() {
                    outcome = stale;
                    break;
                }
                let rooted = self.rooted.get_mut(reader).expect("registered validation owner");
                rooted.dirty.remove(&member, &rooted.parents);
                let (next, visits) = rooted.dirty.first(&rooted.seed);
                cursor = next;
                visiting.work.witness_visits += visits;
            }
        }
        let (updates, rewinds) = self.rooted[reader].dirty.take_maintenance();
        visiting.work.witness_updates += updates;
        visiting.work.cursor_rewinds += rewinds;
        outcome
    }

    fn membership(&self, key: &ProductKey) -> Option<&HashSet<ProductKey>> {
        self.produced
            .get(key)
            .or_else(|| self.displaced.get(key))
            .map(|entry| &entry.membership)
    }

    pub(super) fn register_rooted(
        &mut self,
        reader: ProductKey,
        seed: ProductKey,
        types: &super::super::types::Types,
    ) -> ProductValidation {
        let mut work = ProductValidation::default();
        if self.rooted.get(&reader).is_some_and(|rooted| rooted.seed == seed) {
            return work;
        }
        let mut rooted = RootedProducts::new(seed.clone());
        let _ = rooted.attach(self, seed, None, types);
        if let Some(mut previous) = self.rooted.remove(&reader) {
            for member in previous.parents.keys() {
                let readers = self.rooted_readers.get_mut(member).expect("registered member");
                readers.remove(&reader);
                if readers.is_empty() {
                    self.rooted_readers.remove(member);
                }
                if rooted.parents.contains_key(member) {
                    if !previous.changes.contains(member) {
                        rooted.changes.remove(member);
                    }
                    if !previous.dirty.contains(member) {
                        rooted.dirty.remove(member, &rooted.parents);
                    }
                } else {
                    rooted.changes.insert(member.clone());
                }
            }
            previous.dirty.clear();
            previous.collect_maintenance(&mut work);
            rooted.changes.extend(
                previous
                    .changes
                    .into_iter()
                    .filter(|member| !rooted.parents.contains_key(member)),
            );
        }
        for member in rooted.parents.keys() {
            self.rooted_readers
                .entry(member.clone())
                .or_default()
                .insert(reader.clone());
        }
        self.rooted.insert(reader, rooted);
        work
    }

    pub(super) fn replace_membership_readers(&mut self, owner: &ProductKey, previous: &HashSet<ProductKey>) {
        let next = self.membership(owner).expect("committed membership");
        let removed = previous.difference(next).cloned().collect::<Vec<_>>();
        let added = next.difference(previous).cloned().collect::<Vec<_>>();
        for child in removed {
            let readers = self
                .membership_readers
                .get_mut(&child)
                .expect("committed reverse membership");
            readers.remove(owner);
            if readers.is_empty() {
                self.membership_readers.remove(&child);
            }
        }
        for child in added {
            self.membership_readers.entry(child).or_default().insert(owner.clone());
        }
    }

    pub(super) fn committed_rooted_member(
        &mut self,
        tel: &impl Telemetry,
        owner: &ProductKey,
        previous: &HashSet<ProductKey>,
        changed: bool,
        types: &super::super::types::Types,
    ) -> Vec<(ReaderMutation, ProductKey)> {
        let readers = self.rooted_readers.get(owner).cloned().unwrap_or_default();
        let mut invalidated = Vec::new();
        for reader in readers {
            let mut rooted = self.rooted.remove(&reader).expect("registered root reader");
            let mut work = ProductValidation::default();
            let (touched, reparented) = rooted.replace_edges(self, owner, previous, types, &mut work);
            let waiting = rooted.dirty.waiting(owner);
            rooted.dirty.remove(owner, &rooted.parents);
            if changed {
                rooted.changes.insert(owner.clone());
            }
            for member in &touched {
                if rooted.parents.contains_key(member) {
                    self.rooted_readers
                        .entry(member.clone())
                        .or_default()
                        .insert(reader.clone());
                } else if let Some(readers) = self.rooted_readers.get_mut(member) {
                    readers.remove(&reader);
                    if readers.is_empty() {
                        self.rooted_readers.remove(member);
                    }
                }
            }
            if (changed || !touched.is_empty())
                && !self
                    .pending_dependencies
                    .get(&reader)
                    .is_some_and(|pending| pending.dependencies.rooted_read.is_some_and(|read| !read.delivered))
            {
                invalidated.push((ReaderMutation::Invalidate, reader.clone()));
            } else if rooted.dirty.is_empty() {
                invalidated.push((ReaderMutation::Refresh, reader.clone()));
            }
            rooted.collect_maintenance(&mut work);
            work.report(tel, owner);
            self.rooted.insert(reader.clone(), rooted);
            if let Some(request) = waiting {
                self.expose_waiting_branch(&reader, request, owner.clone(), false);
            }
            if let Some((_, request)) = self.live_rooted_wait_frame(&reader) {
                for branch in reparented {
                    self.expose_waiting_branch(&reader, request, branch, true);
                }
            }
        }
        invalidated
    }
}

impl ProductReadContext<'_> {
    pub(crate) fn include_product(&mut self, key: ProductKey) {
        self.dependencies.membership.insert(key);
    }

    pub(crate) fn read_rooted_products(
        &mut self,
        tel: &impl super::Telemetry,
        reader: ProductKey,
        seed: ProductKey,
        types: &super::super::types::Types,
    ) -> Result<Vec<(ProductKey, Option<ProductValue>)>, Vec<PullWait>> {
        assert!(
            self.session.memo.contains_in_progress(&reader),
            "a rooted observation belongs to its current formula"
        );
        assert!(
            self.dependencies.rooted_read.is_none(),
            "a formula observes one rooted membership witness"
        );
        self.dependencies.rooted_read = Some(RootedRead {
            position: self.dependencies.products.len(),
            delivered: false,
            controls_delivered: self.product_reads_delivered,
        });
        let mut waits = Vec::new();
        let mut walk = ProductValidationWalk::default();
        walk.work
            .include(self.session.memo.register_rooted(reader.clone(), seed, types));
        let work = self.session.memo.rooted[&reader].visit_dirty(|member| {
            if self.session.memo.get(member).is_none() {
                waits.push(PullWait::Product(member.clone()));
                return true;
            }
            if self.session.memo.has_unsettled_inputs(member)
                || self
                    .session
                    .memo
                    .rooted
                    .get(member)
                    .is_some_and(|rooted| !rooted.dirty.is_empty())
            {
                waits.push(PullWait::Product(member.clone()));
                true
            } else {
                false
            }
        });
        walk.work.include(work);
        let result = if waits.is_empty() {
            self.session
                .memo
                .rooted
                .get_mut(&reader)
                .expect("registered root")
                .dirty
                .clear();
            let mut changes = self.session.memo.rooted[&reader]
                .changes
                .iter()
                .cloned()
                .collect::<Vec<_>>();
            sort_product_keys(&mut changes, types);
            Ok(changes
                .into_iter()
                .map(|key| {
                    let value = self.session.memo.rooted[&reader]
                        .parents
                        .contains_key(&key)
                        .then(|| self.session.memo.get(&key).expect("ready rooted member").clone());
                    (key, value)
                })
                .collect())
        } else {
            Err(waits)
        };
        self.session.memo.rooted[&reader].collect_maintenance(&mut walk.work);
        self.session
            .memo
            .finish_validation(tel, walk, result.is_ok(), None, types)
            .report(tel, &reader);
        self.dependencies
            .rooted_read
            .as_mut()
            .expect("current rooted observation")
            .delivered = result.is_ok();
        result
    }

    pub(crate) fn previous_product(&self, key: &ProductKey) -> Option<&ProductValue> {
        self.session
            .memo
            .produced
            .get(key)
            .or_else(|| self.session.memo.displaced.get(key))
            .map(|entry| &entry.value)
    }
}

#[cfg(test)]
mod lifecycle_test;
#[cfg(test)]
#[path = "rooted_test.rs"]
mod rooted_test;
