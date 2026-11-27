use super::*;
use crate::heap::pool_outstanding_blocks;
use crate::process::{DEFAULT_REDUCTIONS_PER_QUANTUM, ProcessState};

struct Fixture {
    node: Rc<Node>,
    schemas: Rc<RefCell<SchemaRegistry>>,
}

impl Fixture {
    fn new() -> Self {
        Self {
            node: Rc::new(Node::empty()),
            schemas: Rc::new(RefCell::new(SchemaRegistry::new())),
        }
    }

    fn spawn(&self, table: &mut ProcTable) -> PidId {
        let process = table
            .spawn(
                Rc::clone(&self.node),
                Rc::clone(&self.schemas),
                DEFAULT_REDUCTIONS_PER_QUANTUM,
            )
            .expect("the table has room");
        unsafe { (*process).pid }
    }
}

/// Intent: a pid names the process the table minted it for, and the first
/// process of a fresh table is main.
#[test]
fn spawned_processes_are_found_by_their_pids() {
    let fixture = Fixture::new();
    let mut table = ProcTable::new();

    let first = fixture.spawn(&mut table);
    let second = fixture.spawn(&mut table);

    assert_eq!(first, FIRST_PID);
    assert_ne!(first, second);
    assert_eq!(table.get(first).map(|p| p.pid), Some(first));
    assert_eq!(table.get(second).map(|p| p.pid), Some(second));
    assert_eq!(table.live(), 2);
}

/// Intent: a pid that never named a process finds nothing: not pid 0, whose
/// slot is never used, not a slot past the array and not a free slot.
#[test]
fn an_unknown_pid_finds_nothing() {
    let fixture = Fixture::new();
    let mut table = ProcTable::new();
    fixture.spawn(&mut table);

    assert!(table.get(0).is_none());
    assert!(table.get(FIRST_PID + 1).is_none(), "a free slot");
    assert!(table.get(u32::MAX).is_none(), "a slot past the array");
    assert!(ProcTable::new().get(FIRST_PID).is_none(), "an empty table");
}

/// Intent: the pid of an exited process stays dead after its slot is reused:
/// the successor in the slot is a different pid and the old one finds nothing.
#[test]
fn a_stale_pid_finds_nothing_after_its_slot_is_reused() {
    let fixture = Fixture::new();
    let mut table = ProcTable::new();
    let dead = fixture.spawn(&mut table);
    table.retire(dead);
    assert!(table.get(dead).is_none(), "an exited process is gone at once");

    let successor = loop {
        let pid = fixture.spawn(&mut table);
        if pid_slot(pid) == pid_slot(dead) {
            break pid;
        }
    };

    assert_ne!(successor, dead);
    assert_eq!(pid_generation(successor), pid_generation(dead) + 1);
    assert!(table.get(dead).is_none(), "the stale pid does not name the successor");
    assert!(table.get(successor).is_some());
}

/// Intent: the table doubles when every slot is in use and no process moves,
/// so a pointer handed to compiled code stays good.
#[test]
fn doubling_keeps_every_process_where_it_was() {
    let fixture = Fixture::new();
    let mut table = ProcTable::new();
    let mut seen = Vec::new();
    for _ in 0..200 {
        let pid = fixture.spawn(&mut table);
        seen.push((pid, table.get_ptr(pid).unwrap()));
    }

    assert!(table.slot_count() >= 201, "the array doubled past the first 8 slots");
    assert_eq!(table.slot_count(), 256);
    for (pid, address) in seen {
        assert_eq!(table.get_ptr(pid), Some(address));
    }
}

/// Intent: when a slot's generation passes its last value it wraps to 0, so
/// the slot's very first pid names the occupant again. The wrap is the defined
/// limit of a pid's protection, not a fault.
#[test]
fn a_generation_wraps_to_zero() {
    assert_eq!(pid_generation(successor(7 | (4094 << SLOT_BITS))), 4095);
    assert_eq!(successor(7 | (4095 << SLOT_BITS)), 7);

    let fixture = Fixture::new();
    let mut table = ProcTable::new();
    let first = fixture.spawn(&mut table);
    let mut occupant = first;
    for _ in 0..(1usize << GENERATION_BITS) {
        table.retire(occupant);
        occupant = loop {
            let pid = fixture.spawn(&mut table);
            if pid_slot(pid) == pid_slot(first) {
                break pid;
            }
            table.retire(pid);
        };
    }
    assert_eq!(
        occupant, first,
        "after 4096 exits the slot's generation is back at its first"
    );
    assert!(table.get(first).is_some());
}

/// Intent: an exit frees the slot with its shell, and the next spawn takes
/// that shell instead of allocating one, handing it back as a fresh process.
#[test]
fn a_spawn_reuses_the_shell_of_an_exited_process() {
    let fixture = Fixture::new();
    let mut table = ProcTable::new();
    let old = fixture.spawn(&mut table);
    let shell = table.get_ptr(old).unwrap();
    {
        let process = table.get_mut(old).unwrap();
        process.state = ProcessState::Exited;
        process.halt_value = 9;
        process.parks = 4;
        process.handlers.push_interpreter();
    }
    table.retire(old);
    assert_eq!(table.free_shells(), 1);
    assert_eq!(table.live(), 0);

    let new = fixture.spawn(&mut table);

    assert_eq!(table.get_ptr(new), Some(shell), "the same shell");
    assert_eq!(table.free_shells(), 0);
    let process = table.get(new).unwrap();
    assert_eq!(process.state, ProcessState::New);
    assert_eq!((process.halt_value, process.parks), (0, 0));
    assert_eq!(process.handlers.depth(), 0, "no handler of the last life survives");
    assert!(process.mailbox.is_empty());
    assert_eq!(process.delivery.borrow().queued_gifts().count(), 0);
}

/// Intent: an exit gives every block of the process back to the pool while the
/// shell stays, so a program of short-lived processes holds blocks only for
/// the ones alive.
#[test]
fn an_exit_returns_the_heap_blocks_and_keeps_the_shell() {
    let fixture = Fixture::new();
    let before = pool_outstanding_blocks();
    let mut table = ProcTable::new();
    let pid = fixture.spawn(&mut table);
    assert_eq!(pool_outstanding_blocks(), before + 1);

    table.retire(pid);

    assert_eq!(pool_outstanding_blocks(), before);
    assert_eq!(table.free_shells(), 1);
    drop(table);
    assert_eq!(pool_outstanding_blocks(), before);
}

/// Intent: a table with every slot in use says so by name instead of reusing
/// a live slot.
#[test]
fn a_full_table_refuses_a_spawn() {
    let fixture = Fixture::new();
    let mut table = ProcTable::new();
    table.slots = vec![std::ptr::null_mut(); MAX_SLOTS];

    let refused = table.spawn(Rc::clone(&fixture.node), Rc::clone(&fixture.schemas), 1);

    assert_eq!(refused.err(), Some(TableFull));
    assert!(TableFull.to_string().contains("full"));
}

/// Intent: a process on loan keeps its whole heap through its exit and goes
/// back to its lender.
#[test]
fn a_process_on_loan_is_not_cleaned_at_exit() {
    let fixture = Fixture::new();
    let process = Box::new(Process::with_node(
        Rc::clone(&fixture.node),
        Rc::clone(&fixture.schemas),
        0,
        DEFAULT_REDUCTIONS_PER_QUANTUM,
    ));
    let mut table = ProcTable::new();
    let pid = table.lend(process).unwrap();
    assert_eq!(pid, FIRST_PID);
    let before = pool_outstanding_blocks();

    table.retire(pid);

    assert_eq!(pool_outstanding_blocks(), before, "its blocks are still its own");
    assert_eq!(table.free_shells(), 0);
    let returned = table.take(pid).expect("the lender takes it back");
    assert_eq!(returned.pid, pid);
    assert!(table.get(pid).is_none());
}
