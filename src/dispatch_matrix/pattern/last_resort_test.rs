use super::{FieldTerm, LastResort};

fn fields(raised: &LastResort) -> Vec<(&'static str, FieldTerm)> {
    match raised {
        LastResort::Exception { fields, .. } => fields.clone(),
        LastResort::Reraise => panic!("a re-raise builds no exception"),
    }
}

fn atom(name: &'static str) -> FieldTerm {
    FieldTerm::Atom(name.into())
}

#[test]
fn a_function_head_miss_carries_the_function_it_missed_and_none_of_its_arguments() {
    let raised = LastResort::function_clause(Some("Elixir.M".to_string()), "f".to_string(), 1);
    assert_eq!(raised.exception(), Some("Elixir.FunctionClauseError"));
    assert_eq!(
        fields(&raised),
        vec![
            ("module", atom("Elixir.M")),
            ("function", atom("f")),
            ("arity", FieldTerm::Int(1)),
            ("kind", atom("nil")),
            ("args", atom("nil")),
            ("clauses", atom("nil")),
        ],
        "every field of Elixir's struct is present, so a handler can read any of them"
    );
    assert_eq!(raised.consumed_inputs(), 0, "Elixir's message names the function only");
}

#[test]
fn a_function_outside_any_module_has_no_module_to_carry() {
    let raised = LastResort::function_clause(None, "main".to_string(), 0);
    assert_eq!(fields(&raised)[0], ("module", atom("nil")));
}

#[test]
fn the_decisions_about_one_value_carry_it_as_their_term() {
    let about_the_subject = [
        (LastResort::match_error(), "Elixir.MatchError"),
        (LastResort::case_clause(), "Elixir.CaseClauseError"),
        (LastResort::with_clause(), "Elixir.WithClauseError"),
        (LastResort::try_clause(), "Elixir.TryClauseError"),
    ];
    for (raised, exception) in about_the_subject {
        assert_eq!(raised.exception(), Some(exception));
        assert_eq!(fields(&raised), vec![("term", FieldTerm::Subject)]);
        assert_eq!(raised.consumed_inputs(), 1, "{exception} carries the value that missed");
    }
}

#[test]
fn a_boolean_operator_carries_its_left_side_and_its_own_name() {
    let raised = LastResort::bad_boolean("or");
    assert_eq!(raised.exception(), Some("Elixir.BadBooleanError"));
    assert_eq!(
        fields(&raised),
        vec![("term", FieldTerm::Subject), ("operator", atom("or"))]
    );
    assert_eq!(raised.consumed_inputs(), 1);
}

#[test]
fn a_cond_with_no_truthy_condition_has_nothing_to_carry() {
    let cond = LastResort::cond_clause();
    assert_eq!(cond.exception(), Some("Elixir.CondClauseError"));
    assert_eq!(fields(&cond), vec![]);
    assert_eq!(cond.consumed_inputs(), 0);
}

#[test]
fn an_exception_that_is_declared_with_its_words_carries_them_as_its_message() {
    let not = LastResort::argument_error();
    assert_eq!(not.exception(), Some("Elixir.ArgumentError"));
    assert_eq!(
        fields(&not),
        vec![("message", FieldTerm::Text("argument error".to_string()))]
    );
    assert_eq!(not.consumed_inputs(), 0);
    assert_eq!(
        LastResort::declared("Elixir.ArgumentError".to_string(), "argument error".to_string()),
        not
    );
}

#[test]
fn a_handlers_last_resort_continues_the_raise_it_was_delivered() {
    let reraise = LastResort::reraise();
    assert_eq!(reraise, LastResort::Reraise);
    assert_eq!(reraise.exception(), None);
    assert_eq!(
        reraise.consumed_inputs(),
        2,
        "the kind and the value are what it continues with"
    );
}

#[test]
fn a_protocol_miss_carries_the_protocol_and_the_value_that_missed() {
    let raised = LastResort::protocol_undefined("Elixir.String.Chars".to_string());
    assert_eq!(raised.exception(), Some("Elixir.Protocol.UndefinedError"));
    assert_eq!(
        fields(&raised),
        vec![
            ("protocol", atom("Elixir.String.Chars")),
            ("value", FieldTerm::Subject),
            ("message", atom("nil")),
            ("description", FieldTerm::Text(String::new())),
        ]
    );
    assert_eq!(raised.consumed_inputs(), 1);
}

#[test]
fn the_atoms_of_a_last_resort_are_its_module_its_keys_and_its_atom_values() {
    let raised = LastResort::bad_boolean("or");
    assert_eq!(
        raised.atoms().collect::<Vec<_>>(),
        ["Elixir.BadBooleanError", "term", "operator", "or"],
        "a backend interns exactly what the exception is built from"
    );
    assert_eq!(LastResort::reraise().atoms().count(), 0);
}
