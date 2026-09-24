use super::*;
use crate::ast::{Pattern, Spanned};
use crate::dispatch_matrix::pattern::{PatternRow, SourcePatternRows, pattern_dispatch_from_source};
use crate::fz_ir::OwnershipMode;

fn value(raw: u32) -> ValueId {
    ValueId::from_u32(raw)
}

fn entry_id(raw: u32) -> ControlEntryId {
    ControlEntryId::from_u32(raw)
}

fn entry(steps: Vec<LoweredStep>, tail: LoweredTail) -> LoweredEntry {
    LoweredEntry {
        span: Span::DUMMY,
        origin: ControlEntryOrigin::Clause,
        params: Vec::new(),
        captures: Vec::new(),
        physical_captures: Vec::new(),
        physical_params: Vec::new(),
        steps,
        tail,
    }
}

fn closure_call(callee: u32, callsite: u32, result: u32, args: &[u32], dest: ControlDestination) -> LoweredTail {
    LoweredTail::ClosureCall {
        value: value(result),
        callsite: CallSiteId::from_u32(callsite),
        callee: value(callee),
        args: args
            .iter()
            .map(|arg| CallArg {
                value: value(*arg),
                ascription: None,
                ownership: OwnershipMode::Share,
            })
            .collect(),
        dest,
    }
}

#[test]
fn definition_sites_distinguish_projections_entries_and_multiple_outputs() {
    let body = LoweredBody::clauses(
        vec![LoweredClause {
            span: Span::DUMMY,
            params: vec![value(0)],
            projections: vec![LoweredStep::SplitList {
                source: value(0),
                head: value(1),
                tail: value(2),
            }],
            entry: entry_id(0),
        }],
        vec![entry(
            vec![
                LoweredStep::Const {
                    value: value(3),
                    literal: GroundValue::Int(10),
                },
                LoweredStep::AssertSame {
                    source: value(1),
                    value: value(3),
                },
            ],
            LoweredTail::Value {
                value: value(3),
                dest: ControlDestination::Return,
            },
        )],
        Vec::new(),
    );
    let projection = StepSite::Projection { clause: 0, index: 0 };
    let construction = StepSite::Entry {
        entry: entry_id(0),
        index: 0,
    };
    assert_eq!(
        body.value_definition_site(value(0)),
        None,
        "parameters arrive without a defining step"
    );
    for (output, site) in [(1, projection), (2, projection), (3, construction)] {
        assert_eq!(body.value_definition_site(value(output)), Some(site));
        assert!(std::ptr::eq(
            body.step_at(site),
            body.value_definition(value(output)).unwrap()
        ));
    }
    let assertion = body.step_at(StepSite::Entry {
        entry: entry_id(0),
        index: 1,
    });
    assert_eq!(
        step_defined_values(assertion).count(),
        0,
        "an equality assertion must not redefine its operand"
    );
    let mut operands = Vec::new();
    step_used_values(assertion, &mut operands);
    assert_eq!(operands, [value(1), value(3)]);
}

#[test]
fn ordered_operands_keep_repeated_captures_and_each_closure_callee() {
    let lambda = LoweredStep::Lambda {
        value: value(4),
        function: FunctionId::from_coordinate(0),
        captures: vec![value(1), value(0), value(1)],
    };
    let mut operands = Vec::new();
    step_used_values(&lambda, &mut operands);
    assert_eq!(operands, [value(1), value(0), value(1)]);

    // Two calls of f keep distinct callsites and results, even with the same args.
    // Substituting g changes the callee operand, not the argument coordinates.
    let calls = [
        closure_call(4, 0, 6, &[2, 1, 2], ControlDestination::Deliver(entry_id(1))),
        closure_call(4, 1, 7, &[2, 1, 2], ControlDestination::Deliver(entry_id(2))),
        closure_call(5, 2, 8, &[2, 1, 2], ControlDestination::Return),
    ];
    for (call, callee) in calls.iter().zip([4, 4, 5]) {
        operands.clear();
        tail_used_values(call, &mut operands);
        assert_eq!(operands, [value(callee), value(2), value(1), value(2)]);
    }
    assert_ne!(calls[0], calls[1]);
    assert_eq!(calls[0].child_entries(), [entry_id(1)]);
    assert_eq!(calls[1].child_entries(), [entry_id(2)]);
    assert!(calls[2].child_entries().is_empty());
}

#[test]
fn control_successors_keep_outcomes_misses_and_timeouts_in_source_order() {
    let plan = Rc::new(
        pattern_dispatch_from_source(SourcePatternRows::<Ty>::lexical(
            1,
            [10, 20]
                .into_iter()
                .enumerate()
                .map(|(index, literal)| PatternRow {
                    patterns: vec![Spanned::dummy(Pattern::Int(literal))],
                    preconditions: Vec::new(),
                    guard: None,
                    body_id: index as u32,
                })
                .collect(),
        ))
        .unwrap(),
    );
    let outcomes = [1, 2]
        .into_iter()
        .map(|raw| OutcomeEdge {
            target: entry_id(raw),
            arguments: Box::new([]),
        })
        .collect::<Vec<_>>();
    let dispatch = LoweredTail::Dispatch {
        inputs: vec![value(0)],
        bindings: DispatchBindings::default(),
        dispatch: Box::new(ControlDispatch::new(Rc::clone(&plan), outcomes.clone(), entry_id(3))),
    };
    assert_eq!(dispatch.child_entries(), [entry_id(1), entry_id(2), entry_id(3)]);
    let mut receive = LoweredReceive {
        bindings: DispatchBindings::default(),
        outcomes,
        after: Some(ReceiveAfter {
            span: Span::DUMMY,
            timeout: value(0),
            entry: entry_id(3),
        }),
        dest: ControlDestination::Deliver(entry_id(4)),
        dispatch: plan,
    };
    assert_eq!(
        LoweredTail::Receive(Box::new(receive.clone())).child_entries(),
        [entry_id(1), entry_id(2), entry_id(3)]
    );
    receive.after = None;
    assert_eq!(
        LoweredTail::Receive(Box::new(receive)).child_entries(),
        [entry_id(1), entry_id(2)]
    );
    assert_eq!(
        LoweredTail::If {
            cond: value(0),
            then_entry: entry_id(1),
            else_entry: entry_id(1)
        }
        .child_entries(),
        [entry_id(1), entry_id(1)],
        "source edges are retained even when both target the same entry"
    );
    for dest in [ControlDestination::Return, ControlDestination::Deliver(entry_id(4))] {
        let expected = match dest {
            ControlDestination::Return => vec![],
            ControlDestination::Deliver(id) => vec![id],
        };
        assert_eq!(
            LoweredTail::Value {
                value: value(0),
                dest: dest.clone()
            }
            .child_entries(),
            expected
        );
        assert_eq!(
            LoweredTail::DirectCall {
                value: value(1),
                callsite: CallSiteId::from_u32(0),
                callee: FunctionId::from_coordinate(0),
                args: vec![],
                dest,
            }
            .child_entries(),
            expected
        );
    }
    assert!(LoweredTail::Halt { atom: "done".into() }.child_entries().is_empty());
}
