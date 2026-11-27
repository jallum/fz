//! Which executables need no frame of their own, so that a call to one is a
//! machine call: the callee runs on the machine stack and returns its result
//! in registers.
//!
//! A machine function needs a frame only when something outside it can arrive
//! in it while it is live: a call's return, or the runtime. A process leaves
//! native code to yield, which happens only at a tail call inside a call cycle;
//! to park, which happens only at a `receive`; and at the end of its quantum.
//! A raise is no such arrival: every function returns to the quantum entry,
//! which runs the handler. So an executable is frame-free when none of its
//! entries reaches a `receive`, a `try` (whose handler the runtime enters), a
//! closure call (whose target is not known), a call it cannot see into, or a
//! call into a cycle, and every executable it calls is frame-free too, including
//! one it calls and never returns from. Being in no cycle also bounds its work
//! by its code, so it spends no reduction.

use super::super::artifact::{BackendBody, BackendProgram, BackendReturnFlow, BackendTail, CallEdge, CallTarget};
use super::super::body::ControlDestination;
use super::super::identity::ExecutableKey;
use super::super::types::Types;

/// For each executable of a program, in program order, whether it is
/// frame-free.
pub(super) struct FrameFree {
    answers: Vec<bool>,
    copied_sizes: Vec<usize>,
}

/// The most blocks a frame-free callee may add to a caller that copies it: a
/// forwarder, a small helper and a few-clause function over helpers are within
/// it, a function with many clauses that call helpers of their own is not. Every copy is at
/// most this big, so a caller's code is bounded by its own calls, not by the
/// depth of what they call.
pub(super) const COPY_LIMIT: usize = 32;

impl FrameFree {
    pub(super) fn of(program: &BackendProgram, types: &Types) -> Self {
        let count = program.executables().len();
        let mut answers = Answers {
            program,
            types,
            states: vec![State::Unasked; count],
            copied_sizes: vec![usize::MAX; count],
        };
        let frame_free = (0..count).map(|index| answers.frame_free(index)).collect();
        Self {
            answers: frame_free,
            copied_sizes: answers.copied_sizes,
        }
    }

    /// Whether executable `index` is frame-free.
    pub(super) fn executable(&self, index: usize) -> bool {
        self.answers[index]
    }

    /// Whether a delivered call to frame-free executable `index` is copied
    /// into its caller: its copied size is within [`COPY_LIMIT`].
    pub(super) fn copied_in_caller(&self, index: usize) -> bool {
        self.answers[index] && self.copied_sizes[index] <= COPY_LIMIT
    }

    /// Whether a call to `callee` is a machine call.
    pub(super) fn callee(&self, program: &BackendProgram, types: &Types, callee: &CallTarget<ExecutableKey>) -> bool {
        callee_is_frame_free(program, types, callee, &mut |index| self.answers[index])
    }
}

/// Whether a call that delivers its value to an entry of the caller continues
/// in the caller's function: every callee it can reach is frame-free, raises
/// because nothing defines it, or never returns, so that no frame waits for it.
pub(super) fn delivered_call_continues_here(
    target: &CallEdge<ExecutableKey, BackendReturnFlow>,
    dest: &ControlDestination,
    callee_frame_free: &mut impl FnMut(&CallTarget<ExecutableKey>) -> bool,
) -> bool {
    if !matches!(dest, ControlDestination::Deliver(_)) {
        return false;
    }
    let mut continues = |callee: &CallTarget<ExecutableKey>, flow: &BackendReturnFlow| match flow {
        BackendReturnFlow::NoReturn => true,
        BackendReturnFlow::Deliver { .. } => callee_frame_free(callee),
        BackendReturnFlow::Tail | BackendReturnFlow::Continue { .. } => false,
    };
    match target {
        CallEdge::Direct(direct) => continues(&direct.callee, &direct.return_flow),
        CallEdge::Dispatch(dispatch) => dispatch.arms.iter().all(|arm| continues(&arm.callee, &arm.return_flow)),
        CallEdge::Indirect(_) => false,
    }
}

/// Whether a tail call that returns its callee's value as its own is a machine
/// tail call, inside a body that is a machine function: every callee it can
/// reach is frame-free, raises because nothing defines it, or never returns.
pub(super) fn tail_call_continues_here(
    target: &CallEdge<ExecutableKey, BackendReturnFlow>,
    callee_frame_free: &mut impl FnMut(&CallTarget<ExecutableKey>) -> bool,
) -> bool {
    let mut continues = |callee: &CallTarget<ExecutableKey>, flow: &BackendReturnFlow| match flow {
        BackendReturnFlow::NoReturn => true,
        BackendReturnFlow::Tail => callee_frame_free(callee),
        BackendReturnFlow::Deliver { .. } | BackendReturnFlow::Continue { .. } => false,
    };
    match target {
        CallEdge::Direct(direct) => continues(&direct.callee, &direct.return_flow),
        CallEdge::Dispatch(dispatch) => dispatch.arms.iter().all(|arm| continues(&arm.callee, &arm.return_flow)),
        CallEdge::Indirect(_) => false,
    }
}

/// Whether every callee an edge can reach that never returns is itself
/// frame-free. A machine function cannot hand a call to a function that
/// suspends, since such a callee may end the quantum with nothing above it to
/// resume.
fn no_return_callees_are_frame_free(
    target: &CallEdge<ExecutableKey, BackendReturnFlow>,
    callee_frame_free: &mut impl FnMut(&CallTarget<ExecutableKey>) -> bool,
) -> bool {
    let mut frame_free = |callee: &CallTarget<ExecutableKey>, flow: &BackendReturnFlow| {
        !matches!(flow, BackendReturnFlow::NoReturn) || callee_frame_free(callee)
    };
    match target {
        CallEdge::Direct(direct) => frame_free(&direct.callee, &direct.return_flow),
        CallEdge::Dispatch(dispatch) => dispatch
            .arms
            .iter()
            .all(|arm| frame_free(&arm.callee, &arm.return_flow)),
        CallEdge::Indirect(_) => false,
    }
}

fn callee_is_frame_free(
    program: &BackendProgram,
    types: &Types,
    callee: &CallTarget<ExecutableKey>,
    executable_frame_free: &mut impl FnMut(usize) -> bool,
) -> bool {
    match callee {
        CallTarget::Local(key) => program.executable_index(key, types).is_some_and(executable_frame_free),
        CallTarget::Undefined(_) => true,
        CallTarget::ProviderBoundary(_) => false,
    }
}

#[derive(Clone, Copy)]
enum State {
    Unasked,
    Deciding,
    Answered(bool),
}

struct Answers<'p> {
    program: &'p BackendProgram,
    types: &'p Types,
    states: Vec<State>,
    /// For each frame-free executable answered, the blocks a caller that
    /// copies it holds: its own, and those of the callees it copies in turn.
    copied_sizes: Vec<usize>,
}

impl Answers<'_> {
    /// An executable met again while its own answer is being decided is in a
    /// call cycle, and so is every executable on the way back to it.
    fn frame_free(&mut self, index: usize) -> bool {
        match self.states[index] {
            State::Answered(answer) => return answer,
            State::Deciding => return false,
            State::Unasked => {}
        }
        self.states[index] = State::Deciding;
        let program = self.program;
        let answer = match &program.executables()[index].body {
            BackendBody::Extern { .. } => true,
            BackendBody::Clauses { entries, .. } => entries.iter().all(|entry| self.tail_needs_no_frame(&entry.tail)),
        };
        self.states[index] = State::Answered(answer);
        if answer {
            self.copied_sizes[index] = self.copied_size(index);
        }
        answer
    }

    /// The blocks of executable `index`, a frame-free one, with those of each
    /// callee that is small enough to be copied into it; a callee that is not
    /// is one call. A forwarder, whose whole body is a call it returns, adds no
    /// blocks of its own: it costs what its callee does.
    fn copied_size(&self, index: usize) -> usize {
        let program = self.program;
        let executable = &program.executables()[index];
        let BackendBody::Clauses { entries, .. } = &executable.body else {
            return 1;
        };
        let callee_cost = |callee: usize| match self.copied_sizes[callee] {
            size if size <= COPY_LIMIT => size,
            _ => 1,
        };
        if let Some(callee) = self.forwarded_callee(index) {
            return callee_cost(callee);
        }
        let callees: usize = entries
            .iter()
            .flat_map(|entry| self.callee_indices(&entry.tail))
            .map(callee_cost)
            .sum();
        1 + entries.len() + callees
    }

    /// The executable that `index` only forwards to: its body is one entry with no
    /// steps that returns a direct call of a local callee.
    fn forwarded_callee(&self, index: usize) -> Option<usize> {
        let executable = &self.program.executables()[index];
        let BackendBody::Clauses { entries, .. } = &executable.body else {
            return None;
        };
        let [entry] = entries.as_slice() else {
            return None;
        };
        if !entry.steps.is_empty() {
            return None;
        }
        let BackendTail::DirectCall {
            target: CallEdge::Direct(_),
            dest: ControlDestination::Return,
            ..
        } = &entry.tail
        else {
            return None;
        };
        self.callee_indices(&entry.tail).first().copied()
    }

    fn callee_indices(&self, tail: &BackendTail) -> Vec<usize> {
        let BackendTail::DirectCall { target, .. } = tail else {
            return Vec::new();
        };
        let local = |callee: &CallTarget<ExecutableKey>| match callee {
            CallTarget::Local(key) => self.program.executable_index(key, self.types),
            CallTarget::Undefined(_) | CallTarget::ProviderBoundary(_) => None,
        };
        match target {
            CallEdge::Direct(direct) => local(&direct.callee).into_iter().collect(),
            CallEdge::Dispatch(dispatch) => dispatch.arms.iter().filter_map(|arm| local(&arm.callee)).collect(),
            CallEdge::Indirect(_) => Vec::new(),
        }
    }

    fn tail_needs_no_frame(&mut self, tail: &BackendTail) -> bool {
        let (program, types) = (self.program, self.types);
        let mut callee_frame_free = |callee: &CallTarget<ExecutableKey>| {
            callee_is_frame_free(program, types, callee, &mut |index| self.frame_free(index))
        };
        match tail {
            BackendTail::Value { .. } | BackendTail::If { .. } | BackendTail::Dispatch { .. } => true,
            BackendTail::Unreachable => true,
            BackendTail::ClosureCall { .. } | BackendTail::Receive(_) | BackendTail::Try { .. } => false,
            BackendTail::DirectCall { target, dest, .. } => {
                let continues = match dest {
                    ControlDestination::Deliver(_) => {
                        delivered_call_continues_here(target, dest, &mut callee_frame_free)
                    }
                    ControlDestination::Return => tail_call_continues_here(target, &mut callee_frame_free),
                };
                continues && no_return_callees_are_frame_free(target, &mut callee_frame_free)
            }
        }
    }
}
