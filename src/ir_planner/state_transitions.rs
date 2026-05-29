use crate::fz_ir::{Cont, FnId, Module, Term, Var};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResumeStateUpdate {
    pub target: FnId,
    pub args: Vec<ResumeStateArg>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResumeStateArg {
    Result,
    Capture { index: usize, var: Var },
    Local(Var),
}

/// Recognize the immediate resume target of a continuation, even when the
/// target is not the caller. Source function clauses lower into helper bodies,
/// so the reducer call may live in `fn_clause_*` while the resume target is the
/// source recursive function. Later loopification can compare the target to the
/// surrounding recursive family.
pub fn continuation_resume_state_update(
    module: &Module,
    continuation: &Cont,
) -> Option<ResumeStateUpdate> {
    let cont_fn = module.fn_by_id(continuation.fn_id);
    let params = &cont_fn.block(cont_fn.entry).params;
    let result = *params.first()?;
    let entry = cont_fn.block(cont_fn.entry);
    let Term::TailCall { callee, args, .. } = &entry.terminator else {
        return None;
    };
    Some(ResumeStateUpdate {
        target: *callee,
        args: resume_args(params, &continuation.captured, result, args),
    })
}

fn resume_args(params: &[Var], captures: &[Var], result: Var, args: &[Var]) -> Vec<ResumeStateArg> {
    args.iter()
        .map(|arg| resume_arg(params, captures, result, *arg))
        .collect()
}

fn resume_arg(params: &[Var], captures: &[Var], result: Var, arg: Var) -> ResumeStateArg {
    if arg == result {
        return ResumeStateArg::Result;
    }
    if let Some(param_idx) = params.iter().position(|param| *param == arg) {
        if let Some(capture_idx) = param_idx.checked_sub(1) {
            if let Some(captured) = captures.get(capture_idx) {
                return ResumeStateArg::Capture {
                    index: capture_idx,
                    var: *captured,
                };
            }
        }
    }
    ResumeStateArg::Local(arg)
}
