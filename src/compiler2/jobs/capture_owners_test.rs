use super::*;
use crate::compiler2::ValueId;
use crate::compiler2::body::{ControlDestination, ControlEntryOrigin, LoweredTail};
use crate::source::Span;

fn id(index: u32) -> ControlEntryId {
    ControlEntryId::from_u32(index)
}

fn holding(captures: &[u32], tail: LoweredTail) -> LoweredEntry {
    LoweredEntry {
        span: Span::DUMMY,
        origin: ControlEntryOrigin::Branch,
        params: Vec::new(),
        captures: captures.iter().map(|value| ValueId::from_u32(*value)).collect(),
        capture_owners: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps: Vec::new(),
        tail,
    }
}

fn delivering_to(entry: u32) -> LoweredTail {
    LoweredTail::Value {
        value: ValueId::from_u32(99),
        dest: ControlDestination::Deliver(id(entry)),
    }
}

fn returning() -> LoweredTail {
    LoweredTail::Value {
        value: ValueId::from_u32(99),
        dest: ControlDestination::Return,
    }
}

fn owner(entry: u32, index: usize) -> CaptureOwner {
    CaptureOwner {
        entry: id(entry),
        index,
    }
}

fn owners_after(mut entries: Vec<LoweredEntry>, clause_entries: &[u32]) -> Vec<Vec<CaptureOwner>> {
    record_capture_owners(&mut entries, clause_entries.iter().map(|entry| id(*entry)));
    entries.into_iter().map(|entry| entry.capture_owners).collect()
}

/// A value an entry receives from the only entry that reaches it keeps the
/// first holder as its owner; a value that entry defines itself is its own.
#[test]
fn an_entry_reached_from_one_entry_names_that_entrys_capture_as_owner() {
    let owners = owners_after(
        vec![holding(&[1, 2], delivering_to(1)), holding(&[2, 3], returning())],
        &[0],
    );
    assert_eq!(
        owners,
        vec![vec![owner(0, 0), owner(0, 1)], vec![owner(0, 1), owner(1, 1)]]
    );
}

/// Ownership passes down a chain of entries, whichever order they are stored in.
#[test]
fn ownership_passes_down_a_chain_from_the_first_holder_whatever_the_storage_order() {
    let owners = owners_after(
        vec![
            holding(&[2], returning()),
            holding(&[1, 2], delivering_to(0)),
            holding(&[1, 2], delivering_to(1)),
        ],
        &[2],
    );
    assert_eq!(
        owners,
        vec![
            vec![owner(2, 1)],
            vec![owner(2, 0), owner(2, 1)],
            vec![owner(2, 0), owner(2, 1)]
        ]
    );
}

/// Two entries that reach one entry each hold the value in their own frame, so
/// the entry they reach owns what it captures.
#[test]
fn an_entry_reached_from_two_entries_owns_every_capture() {
    let branch = LoweredTail::If {
        cond: ValueId::from_u32(0),
        then_entry: id(1),
        else_entry: id(2),
    };
    let owners = owners_after(
        vec![
            holding(&[1], branch),
            holding(&[1], delivering_to(3)),
            holding(&[1], delivering_to(3)),
            holding(&[1], returning()),
        ],
        &[0],
    );
    assert_eq!(owners[3], vec![owner(3, 0)]);
    assert_eq!(owners[1], vec![owner(0, 0)]);
}

/// An entry the body is entered at has a caller outside the body, so it owns
/// its captures even when one entry also reaches it.
#[test]
fn a_clause_entry_owns_every_capture() {
    let owners = owners_after(
        vec![holding(&[1], delivering_to(1)), holding(&[1], returning())],
        &[0, 1],
    );
    assert_eq!(owners, vec![vec![owner(0, 0)], vec![owner(1, 0)]]);
}
