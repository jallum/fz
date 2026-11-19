//! Which executables need no frame of their own, so that a call to one can be
//! lowered as blocks of its caller.
//!
//! A machine function needs a frame only when something outside it can arrive
//! in it while it is live: a call's return, or the runtime. A process leaves
//! native code to yield, which happens only at a tail call inside a call cycle;
//! to park, which happens only at a `receive`; and at the end of its quantum.
//! A raise is no such arrival: every function returns to the quantum entry,
//! which runs the handler. So an executable is frame-free when none of its
//! entries reaches a `receive`, a `try` (whose handler the runtime enters), a
//! closure call (whose target is not known), a call it cannot see into, or a
//! call into a cycle, and every executable it calls is frame-free too. Being in
//! no cycle also bounds its work by its code, so it spends no reduction.

use super::super::artifact::{BackendBody, BackendProgram, BackendReturnFlow, BackendTail, CallEdge, CallTarget};
use super::super::body::ControlDestination;
use super::super::identity::ExecutableKey;
use super::super::types::Types;

/// For each executable of a program, in program order, whether it is
/// frame-free.
pub(super) struct FrameFree(Vec<bool>);

impl FrameFree {
    pub(super) fn of(program: &BackendProgram, types: &Types) -> Self {
        let mut answers = Answers {
            program,
            types,
            states: vec![State::Unasked; program.executables().len()],
        };
        Self(
            (0..program.executables().len())
                .map(|index| answers.frame_free(index))
                .collect(),
        )
    }

    /// Whether a call to `callee` can be lowered in its caller.
    pub(super) fn callee(&self, program: &BackendProgram, types: &Types, callee: &CallTarget<ExecutableKey>) -> bool {
        callee_is_frame_free(program, types, callee, &mut |index| self.0[index])
    }
}

/// Whether a call that delivers its value to an entry of the caller continues
/// in the caller's function: every callee it can reach is frame-free, raises
/// because nothing defines it, or never returns.
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

/// Whether a tail call that returns its callee's value as its own lowers in
/// place inside a body that is itself lowered in place: every callee it can
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
        answer
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
            BackendTail::DirectCall { target, dest, .. } => match dest {
                ControlDestination::Deliver(_) => delivered_call_continues_here(target, dest, &mut callee_frame_free),
                ControlDestination::Return => tail_call_continues_here(target, &mut callee_frame_free),
            },
        }
    }
}
