//! The process table: where every live process of one scheduler lives, and
//! what a pid means.
//!
//! The table is an array of pointers to processes indexed by slot, as Erlang's
//! `erl_ptab` is. Each process is allocated on its own, so a process never
//! moves when the array doubles, and a raw `*mut Process` handed to compiled
//! code stays valid for the process's whole life.
//!
//! A pid packs a slot and a generation into one `u32`: the low
//! [`SLOT_BITS`] name the slot, the high [`GENERATION_BITS`] count how many
//! processes have left it. Twenty bits of slot allow 2^20 live processes,
//! Erlang's default limit; the twelve left over for the generation make a stale
//! pid collide with a live one only after 4096 exits from one slot, and the
//! free slots are reused oldest first so those exits are spread across the
//! whole table. Slot 0 is never used, so no process has pid 0 and the first
//! process of a fresh table is [`FIRST_PID`]. The generation wraps; that is
//! defined, not an error.
//!
//! A lookup is a mask, a load and a compare of the whole pid against the one
//! the process in the slot carries. A pid whose process has exited, or that
//! never named one, finds nothing.
//!
//! An exited process is cleaned while its heap is hot ([`Process::vacate`]),
//! its slot is freed with the next generation, and its shell goes on a list the
//! next spawn takes from, so a spawn allocates only when that list is empty.

use crate::heap::SchemaRegistry;
use crate::process::{Node, PidId, Process};
use std::cell::RefCell;
use std::collections::VecDeque;
use std::fmt;
use std::rc::Rc;

/// Bits of a pid that name its slot.
pub const SLOT_BITS: u32 = 20;
/// Bits of a pid that count how many processes have left its slot.
pub const GENERATION_BITS: u32 = 32 - SLOT_BITS;
pub const SLOT_MASK: u32 = (1 << SLOT_BITS) - 1;
/// The most slots a table holds, slot 0 included.
pub const MAX_SLOTS: usize = 1 << SLOT_BITS;
/// The pid of the first process a fresh table holds.
pub const FIRST_PID: PidId = 1;
/// The slots of a table's first array.
const FIRST_SLOTS: usize = 8;

/// The slot a pid names.
pub const fn pid_slot(pid: PidId) -> usize {
    (pid & SLOT_MASK) as usize
}

/// How many processes had left the pid's slot when it was minted.
pub const fn pid_generation(pid: PidId) -> u32 {
    pid >> SLOT_BITS
}

/// The pid of the process that takes the slot of `pid` after its occupant
/// leaves. The generation wraps.
const fn successor(pid: PidId) -> PidId {
    (pid & SLOT_MASK) | (pid_generation(pid).wrapping_add(1) << SLOT_BITS)
}

/// The table has every slot in use.
#[derive(Debug, PartialEq, Eq)]
pub struct TableFull;

impl fmt::Display for TableFull {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "the process table is full: {} processes are alive", MAX_SLOTS - 1)
    }
}

/// The live processes of one scheduler, by slot, and the shells of the ones
/// that have exited.
pub struct ProcTable {
    /// The process in each slot; null for a free slot.
    slots: Vec<*mut Process>,
    /// The pid the next process in each free slot gets, oldest first.
    free_pids: VecDeque<PidId>,
    /// Shells of exited processes, vacated; the most recent last.
    free_shells: Vec<*mut Process>,
    /// The one process the table holds on loan, which exits do not clean.
    lent: Option<PidId>,
    live: usize,
}

impl Default for ProcTable {
    fn default() -> Self {
        Self::new()
    }
}

impl ProcTable {
    pub fn new() -> Self {
        Self {
            slots: Vec::new(),
            free_pids: VecDeque::new(),
            free_shells: Vec::new(),
            lent: None,
            live: 0,
        }
    }

    /// How many processes are alive.
    pub fn live(&self) -> usize {
        self.live
    }

    /// How many slots the table has.
    pub fn slot_count(&self) -> usize {
        self.slots.len()
    }

    /// How many exited processes' shells wait for a spawn.
    pub fn free_shells(&self) -> usize {
        self.free_shells.len()
    }

    /// Start a process: it takes the oldest free slot and, when one waits, an
    /// exited process's shell.
    pub fn spawn(
        &mut self,
        node: Rc<Node>,
        schemas: Rc<RefCell<SchemaRegistry>>,
        reductions_per_quantum: i32,
    ) -> Result<*mut Process, TableFull> {
        let pid = self.take_pid()?;
        let process = match self.free_shells.pop() {
            Some(shell) => {
                // SAFETY: a free shell is a vacated process this table owns.
                unsafe { (*shell).reuse(node, schemas, pid, reductions_per_quantum) };
                shell
            }
            None => Box::into_raw(Box::new(Process::with_node(node, schemas, pid, reductions_per_quantum))),
        };
        Ok(self.place(pid, process))
    }

    /// Hold `process` on loan under a pid of its own. Its exit does not clean
    /// it: the lender takes it back with [`ProcTable::take`].
    pub fn lend(&mut self, mut process: Box<Process>) -> Result<PidId, TableFull> {
        let pid = self.take_pid()?;
        process.pid = pid;
        self.lent = Some(pid);
        self.place(pid, Box::into_raw(process));
        Ok(pid)
    }

    /// Give the process of `pid` back to its owner, whole. Its slot is freed.
    pub fn take(&mut self, pid: PidId) -> Option<Box<Process>> {
        let process = self.get_ptr(pid)?;
        self.free_slot(pid);
        if self.lent == Some(pid) {
            self.lent = None;
        }
        // SAFETY: every slot holds a pointer from `Box::into_raw`, and the slot no longer does.
        Some(unsafe { Box::from_raw(process) })
    }

    /// The process `pid` names, or `None` when it has exited or never was.
    pub fn get_ptr(&self, pid: PidId) -> Option<*mut Process> {
        let process = *self.slots.get(pid_slot(pid))?;
        // SAFETY: a non-null slot holds a live process.
        (!process.is_null() && unsafe { (*process).pid } == pid).then_some(process)
    }

    pub fn get(&self, pid: PidId) -> Option<&Process> {
        // SAFETY: a process in a slot is alive, and `&self` stops the table freeing it.
        self.get_ptr(pid).map(|process| unsafe { &*process })
    }

    pub fn get_mut(&mut self, pid: PidId) -> Option<&mut Process> {
        // SAFETY: a process in a slot is alive, and `&mut self` is the only way to reach it here.
        self.get_ptr(pid).map(|process| unsafe { &mut *process })
    }

    /// The process `pid` names has exited: clean it while its heap is hot,
    /// free its slot for the next generation and keep its shell for the next
    /// spawn. The process on loan is left whole for its lender.
    pub fn retire(&mut self, pid: PidId) {
        let Some(process) = self.get_ptr(pid) else {
            return;
        };
        if self.lent == Some(pid) {
            return;
        }
        // SAFETY: the pid named this process, so it is alive.
        unsafe { (*process).vacate() };
        self.free_slot(pid);
        self.free_shells.push(process);
    }

    fn take_pid(&mut self) -> Result<PidId, TableFull> {
        if self.free_pids.is_empty() {
            self.double()?;
        }
        self.free_pids.pop_front().ok_or(TableFull)
    }

    /// Double the array. The new slots are free with generation 0; slot 0 is
    /// never offered.
    fn double(&mut self) -> Result<(), TableFull> {
        let old = self.slots.len();
        let new = (old * 2).clamp(FIRST_SLOTS, MAX_SLOTS);
        if new == old {
            return Err(TableFull);
        }
        self.slots.resize(new, std::ptr::null_mut());
        self.free_pids.extend((old.max(1)..new).map(|slot| slot as PidId));
        Ok(())
    }

    fn place(&mut self, pid: PidId, process: *mut Process) -> *mut Process {
        self.slots[pid_slot(pid)] = process;
        self.live += 1;
        process
    }

    fn free_slot(&mut self, pid: PidId) {
        self.slots[pid_slot(pid)] = std::ptr::null_mut();
        self.free_pids.push_back(successor(pid));
        self.live -= 1;
    }
}

impl Drop for ProcTable {
    /// Drop every process still alive and every shell that waits.
    fn drop(&mut self) {
        for process in self.slots.drain(..).chain(self.free_shells.drain(..)) {
            if !process.is_null() {
                // SAFETY: every pointer the table holds came from `Box::into_raw` and is held once.
                drop(unsafe { Box::from_raw(process) });
            }
        }
    }
}

#[cfg(test)]
#[path = "proc_table_test.rs"]
mod proc_table_test;
