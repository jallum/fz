use super::LastResort;

#[test]
fn a_function_head_miss_names_the_function_it_missed() {
    let raised = LastResort::function_clause("M.f/1");
    assert_eq!(raised.exception, "Elixir.FunctionClauseError");
    assert_eq!(raised.message, "no function clause matching in M.f/1");
    assert!(
        !raised.shows_subject,
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
            LastResort::bad_boolean("or"),
            "Elixir.BadBooleanError",
            "expected a boolean on left-side of \"or\", got:",
        ),
    ];
    for (raised, exception, lead) in showing {
        assert_eq!(raised.exception, exception);
        assert_eq!(raised.message, lead);
        assert!(raised.shows_subject, "{exception} shows the value that missed");
    }
}

#[test]
fn the_decisions_with_nothing_to_show_carry_their_whole_message() {
    let cond = LastResort::cond_clause();
    assert_eq!(cond.exception, "Elixir.CondClauseError");
    assert_eq!(cond.message, "no cond clause evaluated to a truthy value");
    assert!(!cond.shows_subject);

    let not = LastResort::argument_error();
    assert_eq!(not.exception, "Elixir.ArgumentError");
    assert_eq!(not.message, "argument error");
    assert!(!not.shows_subject);
}
