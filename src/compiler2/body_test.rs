use super::*;
use crate::fz_ir::OwnershipMode;

fn entry(tail: LoweredTail) -> LoweredEntry {
    LoweredEntry {
        span: Span::DUMMY,
        origin: ControlEntryOrigin::Clause,
        params: Vec::new(),
        captures: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps: Vec::new(),
        tail,
    }
}

fn arg(value: u32) -> CallArg {
    CallArg {
        value: ValueId::from_u32(value),
        ascription: None,
        ownership: OwnershipMode::Share,
    }
}

fn direct(callsite: u32, args: Vec<CallArg>) -> LoweredEntry {
    entry(LoweredTail::DirectCall {
        value: ValueId::from_u32(100 + callsite),
        callsite: CallSiteId::from_u32(callsite),
        callee: DirectCallee::Function(FunctionId::from_coordinate(0)),
        args,
        dest: ControlDestination::Return,
    })
}

fn closure(callsite: u32, args: Vec<CallArg>) -> LoweredEntry {
    entry(LoweredTail::ClosureCall {
        value: ValueId::from_u32(100 + callsite),
        callsite: CallSiteId::from_u32(callsite),
        callee: ValueId::from_u32(7),
        args,
        dest: ControlDestination::Return,
    })
}

fn body_of(entries: Vec<LoweredEntry>) -> LoweredBody {
    LoweredBody::clauses(Vec::new(), entries, Vec::new())
}

/// A call site's arguments and input mode are each read from
/// the one entry whose tail makes that call, whatever order the entries hold.
#[test]
fn a_call_sites_facts_come_from_the_entry_that_makes_the_call() {
    let body = body_of(vec![
        closure(1, vec![arg(3), arg(4)]),
        entry(LoweredTail::Unreachable),
        direct(0, vec![arg(5)]),
    ]);
    let (zero, one) = (CallSiteId::from_u32(0), CallSiteId::from_u32(1));

    assert_eq!(body.call_args(zero), Some(&[arg(5)][..]));
    assert_eq!(body.call_args(one), Some(&[arg(3), arg(4)][..]));
    assert_eq!(body.call_input_mode(zero), Some(CallInputMode::Direct));
    assert_eq!(body.call_input_mode(one), Some(CallInputMode::Closure));
}

/// `calls` names every call of the body once, with its arguments.
#[test]
fn calls_lists_every_call_with_its_arguments() {
    let body = body_of(vec![
        direct(0, vec![arg(1)]),
        entry(LoweredTail::Unreachable),
        closure(1, Vec::new()),
    ]);
    let calls = body.calls().collect::<Vec<_>>();
    assert_eq!(
        calls,
        vec![
            (CallSiteId::from_u32(0), &[arg(1)][..]),
            (CallSiteId::from_u32(1), &[][..]),
        ]
    );
}

/// A call-site number the body does not make -- a hole between numbers, or one
/// past the last -- answers `None` everywhere rather than naming another call.
#[test]
fn a_call_site_the_body_does_not_make_has_no_facts() {
    let body = body_of(vec![direct(0, vec![arg(1)]), direct(2, vec![arg(2)])]);
    for absent in [1, 3, 99] {
        let callsite = CallSiteId::from_u32(absent);
        assert_eq!(body.call_args(callsite), None);
        assert_eq!(body.call_input_mode(callsite), None);
    }
    assert_eq!(body.call_args(CallSiteId::from_u32(2)), Some(&[arg(2)][..]));
}

/// Two entries naming one call site would make every answer ambiguous, so
/// building such a body is refused in every build profile.
#[test]
#[should_panic(expected = "named by two entries")]
fn a_body_whose_entries_name_one_call_site_twice_is_refused() {
    body_of(vec![direct(0, vec![arg(1)]), closure(0, vec![arg(2)])]);
}
