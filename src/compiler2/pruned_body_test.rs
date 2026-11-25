use super::*;
use crate::compiler2::FunctionId;
use crate::compiler2::body::{DirectCallee, LoweredEntry, LoweredTail};

/// Pruning leaves holes in a body's call-site numbers; the pruned body answers
/// `None` for the call site it dropped and the right arguments for the rest.
#[test]
fn a_pruned_body_answers_only_for_the_call_sites_it_kept() {
    use crate::compiler2::body::{CallArg, CallSiteId, ControlEntryId, ControlEntryOrigin, LoweredClause, ValueId};
    use crate::fz_ir::OwnershipMode;
    let entry = |tail| LoweredEntry {
        span: crate::source::Span::DUMMY,
        origin: ControlEntryOrigin::Clause,
        params: Vec::new(),
        captures: Vec::new(),
        capture_owners: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps: Vec::new(),
        tail,
    };
    let call = |callsite: u32, arg: u32| LoweredTail::DirectCall {
        value: ValueId::from_u32(10 + callsite),
        callsite: CallSiteId::from_u32(callsite),
        callee: DirectCallee::Function(FunctionId::from_coordinate(0)),
        args: vec![CallArg {
            value: ValueId::from_u32(arg),
            ascription: None,
            ownership: OwnershipMode::Share,
        }],
        dest: ControlDestination::Return,
    };
    let (root, dropped, kept) = (
        ControlEntryId::from_u32(0),
        ControlEntryId::from_u32(1),
        ControlEntryId::from_u32(2),
    );
    let body = LoweredBody::clauses(
        vec![LoweredClause {
            span: crate::source::Span::DUMMY,
            params: Vec::new(),
            arguments: Box::default(),
            entry: root,
        }],
        vec![
            entry(LoweredTail::If {
                cond: ValueId::from_u32(0),
                then_entry: dropped,
                else_entry: kept,
            }),
            entry(call(0, 1)),
            entry(call(1, 2)),
        ],
        Vec::new(),
    );

    let pruned = prune_lowered_body(&body, &[0], &[root, kept]).body;

    assert_eq!(pruned.call_args(CallSiteId::from_u32(0)), None);
    assert_eq!(pruned.call_input_mode(CallSiteId::from_u32(0)), None);
    let args = pruned.call_args(CallSiteId::from_u32(1)).expect("the kept call site");
    assert_eq!(args.len(), 1);
    assert_eq!(args[0].value, ValueId::from_u32(2));
}
