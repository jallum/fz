//! The runtime events a scheduler reports and the one writer that renders them.
//!
//! The scheduling core raises each event through [`crate::sched_core::Scheduler::observe`],
//! so every scheduler is asked about every event and says what it does with it.
//! [`write_line`] is the single rendering of an event as a JSONL line; a host
//! that keeps a telemetry bus raises the matching typed raw event, and any sink
//! that writes the line calls the same function.

use crate::heap::{pool_outstanding_blocks, pool_total_cached_blocks};
use crate::process::{Collection, Process};
use crate::sched::{ProbeOutcome, SendProbe};
use std::fmt::Write as _;
use std::time::Duration;

/// The boundary between compiling a program and running it.
pub const EXECUTION_READY: [&str; 3] = ["fz", "runtime", "execution_ready"];
/// One per task exit; carries the pid and the live `Process`.
pub const PROCESS_EXITED: [&str; 3] = ["fz", "runtime", "process_exited"];
/// One each time the scheduling core sleeps for a pending timer; carries the
/// `Duration` it is about to wait.
pub const SCHEDULER_SLEPT: [&str; 3] = ["fz", "runtime", "scheduler_slept"];
/// One per cross-process send; carries the `SendProbe` the sender's probe made.
pub const SEND_PROBE: [&str; 4] = ["fz", "runtime", "send", "probe"];
/// One per heap collection a scheduler boundary performs; carries the
/// `Collection`.
pub const GC: [&str; 3] = ["fz", "runtime", "gc"];
/// One per run, after every process has been torn down; carries the `RunEnded`
/// pool census.
pub const RUN_ENDED: [&str; 3] = ["fz", "runtime", "run_ended"];

/// One per raise, before the runtime decides where it goes; carries the `Raise`.
pub const RAISE: [&str; 3] = ["fz", "runtime", "raise"];

/// One raise as the runtime saw it: its kind (`error` for `raise`/`panic`),
/// the exception's name (empty for a value that is not an exception), and how
/// many handlers were on the stack. Depth zero is an uncaught raise. The stack
/// bytes are the machine stack between the quantum's entry and the raise.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Raise {
    pub kind: String,
    pub exception: String,
    pub handler_depth: usize,
    pub stack_bytes: usize,
}

impl Raise {
    /// Build the record from the raise hook's borrowed arguments.
    ///
    /// # Safety
    /// `kind`/`name` must point at `kind_len`/`name_len` readable bytes.
    pub unsafe fn from_hook_args(
        kind: *const u8,
        kind_len: usize,
        name: *const u8,
        name_len: usize,
        depth: usize,
        stack_bytes: usize,
    ) -> Self {
        let text = |ptr, len| String::from_utf8_lossy(unsafe { std::slice::from_raw_parts(ptr, len) }).into_owned();
        Self {
            kind: text(kind, kind_len),
            exception: text(name, name_len),
            handler_depth: depth,
            stack_bytes,
        }
    }
}

/// What the block pool holds once a run has torn down every process.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RunEnded {
    /// Blocks handed out and not returned when the run began.
    pub pool_outstanding_before_run: usize,
    /// The same count once every process has been torn down. Equal to
    /// `pool_outstanding_before_run` means the run returned every block it took.
    pub pool_outstanding_after_run: usize,
    /// Blocks resting in the pool's free lists.
    pub pool_cached_blocks: usize,
}

impl RunEnded {
    /// The census now, against the outstanding count sampled when the run began.
    pub fn sample(pool_outstanding_before_run: usize) -> Self {
        Self {
            pool_outstanding_before_run,
            pool_outstanding_after_run: pool_outstanding_blocks(),
            pool_cached_blocks: pool_total_cached_blocks(),
        }
    }
}

/// One thing a scheduler reports about a run.
#[derive(Clone, Copy)]
pub enum RuntimeEvent<'a> {
    ExecutionReady,
    ProcessExited(&'a Process),
    SchedulerSlept(Duration),
    SendProbe(&'a SendProbe),
    Raise(&'a Raise),
    Gc(&'a Collection),
    RunEnded(RunEnded),
}

impl RuntimeEvent<'_> {
    pub fn name(&self) -> &'static [&'static str] {
        match self {
            RuntimeEvent::ExecutionReady => &EXECUTION_READY,
            RuntimeEvent::ProcessExited(_) => &PROCESS_EXITED,
            RuntimeEvent::SchedulerSlept(_) => &SCHEDULER_SLEPT,
            RuntimeEvent::SendProbe(_) => &SEND_PROBE,
            RuntimeEvent::Raise(_) => &RAISE,
            RuntimeEvent::Gc(_) => &GC,
            RuntimeEvent::RunEnded(_) => &RUN_ENDED,
        }
    }
}

/// Append `event` to `out` as one JSON object (no trailing newline): the
/// envelope every telemetry line shares, then the event's metadata.
pub fn write_line(out: &mut String, time_ns: u64, span_id: u64, parent_span_id: u64, event: &RuntimeEvent<'_>) {
    out.push_str("{\"name\":[");
    for (position, segment) in event.name().iter().enumerate() {
        if position > 0 {
            out.push(',');
        }
        write!(out, "\"{segment}\"").unwrap();
    }
    write!(
        out,
        "],\"time_ns\":{time_ns},\"kind\":\"event\",\"span_id\":{span_id},\"parent_span_id\":{parent_span_id},\"measurements\":{{}},\"metadata\":{{"
    )
    .unwrap();
    write_metadata(out, event);
    out.push_str("}}");
}

fn write_metadata(out: &mut String, event: &RuntimeEvent<'_>) {
    match event {
        RuntimeEvent::ExecutionReady => {}
        RuntimeEvent::ProcessExited(process) => write_process_exited(out, process),
        RuntimeEvent::SchedulerSlept(wait) => {
            let wait_ns = wait.as_nanos().min(u64::MAX as u128);
            write!(out, "\"wait_ns\":{wait_ns}").unwrap();
        }
        RuntimeEvent::SendProbe(probe) => {
            let outcome = match probe.outcome {
                ProbeOutcome::Hit => "hit",
                ProbeOutcome::Miss => "miss",
            };
            write!(
                out,
                "\"outcome\":\"{outcome}\",\"receiver\":{},\"reductions\":{},\"gift_bytes\":{},\"gift_blocks\":{}",
                probe.receiver, probe.reductions, probe.gift_bytes, probe.gift_blocks
            )
            .unwrap();
        }
        RuntimeEvent::Raise(raise) => {
            write!(
                out,
                "\"kind\":\"{}\",\"exception\":\"{}\",\"handler_depth\":{},\"stack_bytes\":{}",
                raise.kind, raise.exception, raise.handler_depth, raise.stack_bytes
            )
            .unwrap();
        }
        RuntimeEvent::Gc(collection) => {
            let stats = &collection.stats;
            write!(
                out,
                "\"pid\":{},\"boundary\":\"{}\",\"copied_bytes\":{},\"live_bytes\":{},\"from_space_capacity_bytes\":{},\"blocks_released\":{},\"blocks_after\":{}",
                collection.pid,
                collection.boundary.as_str(),
                stats.copied_bytes,
                stats.live_bytes,
                stats.from_space_capacity_bytes,
                stats.blocks_released,
                stats.blocks_after
            )
            .unwrap();
        }
        RuntimeEvent::RunEnded(ended) => {
            write!(
                out,
                "\"pool_outstanding_before_run\":{},\"pool_outstanding_after_run\":{},\"pool_cached_blocks\":{}",
                ended.pool_outstanding_before_run, ended.pool_outstanding_after_run, ended.pool_cached_blocks
            )
            .unwrap();
        }
    }
}

/// The process is nested as an opaque value, the shape every host sink gives a
/// live runtime object it cannot render field by field.
fn write_process_exited(out: &mut String, process: &Process) {
    write!(
        out,
        "\"pid\":{},\"process\":{{\"opaque_type\":\"{}\",\"live_count\":{},\"bytes_used\":{},\"list_retention_attempts\":{},\"list_retention_hits\":{},\"raises_delivered\":{},\"reduction_yields\":{},\"dtors_dispatched\":{},\"halt_value\":{},\"failed\":{}}}",
        process.pid,
        std::any::type_name::<Process>(),
        process.heap.live_count(),
        process.heap.bytes_used(),
        process.list_retention_attempts,
        process.list_retention_hits,
        process.raises_delivered,
        process.reduction_yields,
        process.dtors_dispatched,
        process.halt_value,
        process.failed
    )
    .unwrap();
}

#[cfg(test)]
#[path = "telemetry_test.rs"]
mod telemetry_test;
