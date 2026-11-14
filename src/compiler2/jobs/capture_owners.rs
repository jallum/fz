//! Which entry owns each capture's transport layout.
//!
//! A body with N non-tail calls is cut into N resume entries, and each holds
//! every value still live after its call. An entry reached from exactly one
//! other entry receives those values from it, at the same type and layout, so
//! the entry where a value first appears is the one place that decides how the
//! value travels.

use super::super::body::{CaptureOwner, ControlEntryId, LoweredEntry};
use super::body::child_entries;

/// How the entries of a body reach one entry.
#[derive(Clone, Copy)]
enum Reach {
    Nowhere,
    FromEntry(usize),
    FromSeveral,
}

impl Reach {
    fn noted_from(self, entry: usize) -> Self {
        match self {
            Self::Nowhere => Self::FromEntry(entry),
            Self::FromEntry(existing) if existing == entry => self,
            Self::FromEntry(_) | Self::FromSeveral => Self::FromSeveral,
        }
    }

    fn sole_parent(self) -> Option<usize> {
        match self {
            Self::FromEntry(parent) => Some(parent),
            Self::Nowhere | Self::FromSeveral => None,
        }
    }
}

/// Records on every entry the owner of each of its captures. `clause_entries`
/// are entered from outside the body, so they never inherit.
pub(super) fn record_capture_owners(
    entries: &mut [LoweredEntry],
    clause_entries: impl Iterator<Item = ControlEntryId>,
) {
    let parents = sole_parents(entries, clause_entries);
    for entry in entries.iter_mut() {
        entry.capture_owners.clear();
    }
    for index in 0..entries.len() {
        record_owners_after_parent(entries, &parents, index);
    }
}

fn sole_parents(entries: &[LoweredEntry], clause_entries: impl Iterator<Item = ControlEntryId>) -> Vec<Option<usize>> {
    let mut reach = vec![Reach::Nowhere; entries.len()];
    for entry in clause_entries {
        reach[entry.as_u32() as usize] = Reach::FromSeveral;
    }
    for (index, entry) in entries.iter().enumerate() {
        for child in child_entries(&entry.tail) {
            let child = child.as_u32() as usize;
            reach[child] = reach[child].noted_from(index);
        }
    }
    reach.into_iter().map(Reach::sole_parent).collect()
}

/// An entry whose owners are as many as its captures is already recorded.
fn record_owners_after_parent(entries: &mut [LoweredEntry], parents: &[Option<usize>], index: usize) {
    if entries[index].capture_owners.len() == entries[index].captures.len() {
        return;
    }
    if let Some(parent) = parents[index] {
        record_owners_after_parent(entries, parents, parent);
    }
    let owners = owners_of(entries, parents[index], index);
    entries[index].capture_owners = owners;
}

fn owners_of(entries: &[LoweredEntry], parent: Option<usize>, index: usize) -> Vec<CaptureOwner> {
    let parent = parent.map(|parent| &entries[parent]);
    entries[index]
        .captures
        .iter()
        .enumerate()
        .map(|(capture_index, value)| {
            parent
                .and_then(|parent| {
                    let held = parent
                        .captures
                        .binary_search_by_key(&value.as_u32(), |held| held.as_u32());
                    held.ok().map(|at| parent.capture_owners[at])
                })
                .unwrap_or(CaptureOwner {
                    entry: ControlEntryId::from_u32(index as u32),
                    index: capture_index,
                })
        })
        .collect()
}

#[cfg(test)]
#[path = "capture_owners_test.rs"]
mod capture_owners_test;
