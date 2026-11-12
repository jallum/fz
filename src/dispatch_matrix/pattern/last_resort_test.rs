use super::LastResort;

#[test]
fn a_function_head_miss_names_the_function_it_missed() {
    let raised = LastResort::function_clause("M.f/1");
    assert_eq!(raised.exception(), Some("Elixir.FunctionClauseError"));
    assert_eq!(raised.message(), Some("no function clause matching in M.f/1"));
    assert_eq!(
        raised.consumed_inputs(),
        0,
        "Elixir's message names the function, not its arguments"
    );
}

#[test]
fn the_decisions_that_show_their_subject_lead_with_elixirs_words() {
    let showing = [
        (
            LastResort::match_error(),
            "Elixir.MatchError",
            "no match of right hand side value:",
        ),
        (
            LastResort::case_clause(),
            "Elixir.CaseClauseError",
            "no case clause matching:",
        ),
        (
            LastResort::with_clause(),
            "Elixir.WithClauseError",
            "no with clause matching:",
        ),
        (
            LastResort::try_clause(),
            "Elixir.TryClauseError",
            "no try clause matching:",
        ),
        (
            LastResort::bad_boolean("or"),
            "Elixir.BadBooleanError",
            "expected a boolean on left-side of \"or\", got:",
        ),
    ];
    for (raised, exception, lead) in showing {
        assert_eq!(raised.exception(), Some(exception));
        assert_eq!(raised.message(), Some(lead));
        assert_eq!(raised.consumed_inputs(), 1, "{exception} shows the value that missed");
    }
}

#[test]
fn the_decisions_with_nothing_to_show_carry_their_whole_message() {
    let cond = LastResort::cond_clause();
    assert_eq!(cond.exception(), Some("Elixir.CondClauseError"));
    assert_eq!(cond.message(), Some("no cond clause evaluated to a truthy value"));
    assert_eq!(cond.consumed_inputs(), 0);

    let not = LastResort::argument_error();
    assert_eq!(not.exception(), Some("Elixir.ArgumentError"));
    assert_eq!(not.message(), Some("argument error"));
    assert_eq!(not.consumed_inputs(), 0);
}

#[test]
fn a_handlers_last_resort_continues_the_raise_it_was_delivered() {
    let reraise = LastResort::reraise();
    assert_eq!(reraise, LastResort::Reraise);
    assert_eq!(
        reraise.consumed_inputs(),
        2,
        "the kind and the value are what it continues with"
    );
    assert_eq!(LastResort::case_clause().consumed_inputs(), 1);
    assert_eq!(LastResort::cond_clause().consumed_inputs(), 0);
}
