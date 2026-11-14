//! Groups: jobs whose answers conclude together.
//!
//! A recursive answer is found by a climb: each job in the cycle re-runs as
//! the others' answers grow, until nothing moves. Between two steps of the
//! climb no member is queued, so "no publisher is queued" is true at every
//! rung, and a reader outside the cycle that took that for conclusion would
//! read, and pay for, every rung it happened to see.
//!
//! A group names the jobs of one such climb. It forms when a reader meets the
//! answer of a producer that is itself waiting, through standing waits, on the
//! reader: the two are partners, and with them every job on the wait path
//! between them. It is open from formation and whenever a member is queued; it
//! closes when a member's completion leaves none queued or waiting. A reader
//! inside the group asks only whether a fact is locally settled. A reader
//! outside it hears a member's fact concluded only once the group is closed.

use std::hash::Hash;

use crate::fast_hash::{HashMap, HashSet};
use crate::waits::StandingWaits;

pub(crate) type GroupId = u64;

#[derive(Debug)]
struct Group<J> {
    members: Vec<J>,
}

/// The groups of one scheduler. A job belongs to at most one group, by run
/// identity: every answer a job owns is the group's answer.
#[derive(Debug)]
pub(crate) struct Groups<J> {
    of: HashMap<J, GroupId>,
    groups: HashMap<GroupId, Group<J>>,
    /// The groups still deriving. Mostly empty, so asking whether any
    /// publisher is withheld costs nothing between climbs.
    open: HashSet<GroupId>,
    next: GroupId,
}

impl<J> Default for Groups<J> {
    fn default() -> Self {
        Self {
            of: HashMap::default(),
            groups: HashMap::default(),
            open: HashSet::default(),
            next: 0,
        }
    }
}

impl<J: Clone + Eq + Hash> Groups<J> {
    /// The group `job` belongs to.
    pub(crate) fn group_of(&self, job: &J) -> Option<GroupId> {
        self.of.get(job).copied()
    }

    /// Whether `publisher`'s group is open and `reader`, when there is one,
    /// is not in it: the publisher's answer is still being derived, and not by
    /// the reader's own climb.
    pub(crate) fn withholds_from(&self, publisher: &J, reader: Option<&J>) -> bool {
        !self.open.is_empty()
            && self
                .of
                .get(publisher)
                .is_some_and(|id| self.open.contains(id) && reader.is_none_or(|reader| self.of.get(reader) != Some(id)))
    }

    /// Every member of `job`'s group, or `job` alone when it has none.
    pub(crate) fn members_or_self<'a>(&'a self, job: &'a J) -> &'a [J] {
        self.of
            .get(job)
            .and_then(|id| self.groups.get(id))
            .map_or_else(|| std::slice::from_ref(job), |group| group.members.as_slice())
    }

    /// Whether `job` belongs to a group that is still open.
    pub(crate) fn is_in_open_group(&self, job: &J) -> bool {
        !self.open.is_empty() && self.of.get(job).is_some_and(|id| self.open.contains(id))
    }

    /// Opens `job`'s group, if it has one: a member was queued, so the group
    /// is deriving again.
    pub(crate) fn reopen(&mut self, job: &J) {
        if let Some(&id) = self.of.get(job) {
            self.open.insert(id);
        }
    }

    /// Puts every job of `jobs` in one open group, merging each group any of
    /// them already belongs to.
    pub(crate) fn join(&mut self, jobs: impl IntoIterator<Item = J>) {
        let mut target: Option<GroupId> = None;
        let mut loose = Vec::new();
        for job in jobs {
            match (self.of.get(&job).copied(), target) {
                (None, _) => loose.push(job),
                (Some(id), None) => target = Some(id),
                (Some(id), Some(into)) if id != into => self.merge(id, into),
                (Some(_), Some(_)) => {}
            }
        }
        let target = target.unwrap_or_else(|| {
            let id = self.next;
            self.next += 1;
            self.groups.insert(id, Group { members: Vec::new() });
            id
        });
        let group = self.groups.get_mut(&target).expect("a joined group is live");
        for job in loose {
            if self.of.insert(job.clone(), target).is_none() {
                group.members.push(job);
            }
        }
        self.open.insert(target);
    }

    fn merge(&mut self, from: GroupId, into: GroupId) {
        self.open.remove(&from);
        let moved = self.groups.remove(&from).expect("a merged group is live").members;
        for job in &moved {
            self.of.insert(job.clone(), into);
        }
        self.groups
            .get_mut(&into)
            .expect("a merge target is live")
            .members
            .extend(moved);
    }

    /// Closes `job`'s group when none of its members is active, returning its
    /// id. `None` when `job` has no group, it is already closed, or a member
    /// is still active.
    pub(crate) fn close_if_idle(&mut self, job: &J, is_active: impl Fn(&J) -> bool) -> Option<GroupId> {
        let id = *self.of.get(job)?;
        if !self.open.contains(&id) {
            return None;
        }
        if is_active(job) || self.groups.get(&id)?.members.iter().any(is_active) {
            return None;
        }
        self.open.remove(&id);
        Some(id)
    }

    /// The jobs on a wait path from any of `starts` to `to`, `to` excluded:
    /// the job that waits on `to` and, back through the waits, the job each
    /// was reached from. A job waiting on a group it is not in reaches every
    /// member of that group as one node; a wait inside a group reaches only
    /// its producer.
    pub(crate) fn wait_path<'a, F: Eq + Hash + 'a>(
        &'a self,
        starts: &'a [J],
        to: &J,
        waits_for: impl Fn(&J) -> &'a StandingWaits<F, J>,
    ) -> Option<Vec<J>> {
        let mut pending: Vec<(&'a J, Option<usize>)> = starts.iter().map(|start| (start, None)).collect();
        let mut expanded: Vec<(&'a J, Option<usize>)> = Vec::new();
        let mut seen: HashSet<&'a J> = HashSet::default();
        while let Some((job, via)) = pending.pop() {
            let waits = waits_for(job);
            if waits.is_empty() || !seen.insert(job) {
                continue;
            }
            let at = expanded.len();
            expanded.push((job, via));
            let job_group = self.of.get(job);
            for producer in waits.producers() {
                let producer_group = self.of.get(producer);
                let entered = match producer_group {
                    Some(group) if Some(group) != job_group => self.members(group),
                    _ => std::slice::from_ref(producer),
                };
                for next in entered {
                    if next == to {
                        return Some(path_to_start(&expanded, at));
                    }
                    pending.push((next, Some(at)));
                }
            }
        }
        None
    }

    fn members(&self, group: &GroupId) -> &[J] {
        self.groups.get(group).map_or(&[], |group| group.members.as_slice())
    }
}

/// The jobs from `expanded[at]` back to the start it was reached from.
fn path_to_start<J: Clone>(expanded: &[(&J, Option<usize>)], mut at: usize) -> Vec<J> {
    let mut path = Vec::new();
    loop {
        let (job, via) = expanded[at];
        path.push(job.clone());
        match via {
            Some(previous) => at = previous,
            None => return path,
        }
    }
}

#[cfg(test)]
#[path = "groups_test.rs"]
mod groups_test;
