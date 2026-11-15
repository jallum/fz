use super::{FieldTerm, LastResort, RaisedField};
use crate::ground_value::GroundValue;
use crate::literal_term::LiteralTerm;

fn fields(raised: &LastResort) -> Vec<(&str, FieldTerm)> {
    match raised {
        LastResort::Exception { fields, .. } => fields
            .iter()
            .map(|(name, term)| (name.as_ref(), term.clone()))
            .collect(),
        LastResort::Reraise => panic!("a re-raise builds no exception"),
    }
}

fn atom(name: &'static str) -> FieldTerm {
    FieldTerm::atom(name)
}

const NIL: LiteralTerm = LiteralTerm::Ground(GroundValue::Nil);

/// The fields the library's exception `module` declares, in order, each
/// with its default as the source writes it, read from the module's
/// `defexception` under `lib/exceptions`.
fn library_declaration(module: &str) -> Vec<(String, Option<String>)> {
    let sources = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("lib/exceptions");
    let opening = format!("defmodule {module} do");
    for entry in std::fs::read_dir(sources).expect("the library's exception sources") {
        let text = std::fs::read_to_string(entry.expect("a source file").path()).expect("a readable source");
        let Some(start) = text.find(&opening) else {
            continue;
        };
        let line = text[start..]
            .lines()
            .find_map(|line| line.trim().strip_prefix("defexception "))
            .unwrap_or_else(|| panic!("{module} declares an exception"));
        return line
            .trim_matches(|bracket| bracket == '[' || bracket == ']')
            .split(", ")
            .filter(|field| !field.is_empty())
            .map(|field| match field.strip_prefix(':') {
                Some(name) => (name.to_string(), None),
                None => {
                    let (name, default) = field.split_once(": ").expect("a field with a default");
                    (name.to_string(), Some(default.to_string()))
                }
            })
            .collect();
    }
    panic!("the library declares no exception {module}");
}

#[test]
fn every_failure_the_compiler_raises_sets_only_fields_its_exception_declares() {
    let built_in = [
        LastResort::function_clause(Some("Elixir.M".to_string()), "f".to_string(), 1),
        LastResort::match_error(),
        LastResort::protocol_undefined("Elixir.String.Chars".to_string()),
        LastResort::case_clause(),
        LastResort::cond_clause(),
        LastResort::with_clause(),
        LastResort::try_clause(),
        LastResort::bad_boolean("and"),
        LastResort::argument_error(),
    ];
    for raised in built_in {
        let exception = raised.exception().expect("each raises an exception");
        let module = exception.strip_prefix("Elixir.").expect("a module's atom");
        let declared: Vec<String> = library_declaration(module).into_iter().map(|(name, _)| name).collect();
        let defaults = vec![NIL; declared.len()];
        let fields = raised.struct_fields(&declared, &defaults);
        assert_eq!(
            fields.map(|fields| fields.len()),
            Ok(declared.len()),
            "{module} is raised as the struct lib/exceptions declares"
        );
    }
}

#[test]
fn a_field_a_failure_does_not_set_holds_the_default_its_exception_declares() {
    let declared = ["protocol", "value", "message", "description"].map(str::to_string);
    let empty = LiteralTerm::Ground(GroundValue::Binary(Vec::new()));
    let defaults = [NIL, NIL, NIL, empty.clone()];
    let raised = LastResort::protocol_undefined("Elixir.String.Chars".to_string());
    let protocol = LiteralTerm::Ground(GroundValue::Atom("Elixir.String.Chars".to_string()));
    assert_eq!(
        raised.struct_fields(&declared, &defaults),
        Ok(vec![
            ("protocol", RaisedField::Literal(&protocol)),
            ("value", RaisedField::Subject),
            ("message", RaisedField::Literal(&NIL)),
            ("description", RaisedField::Literal(&empty)),
        ]),
        "the struct has every declared field, in the order the module declares them"
    );
}

#[test]
fn a_failure_that_sets_a_field_its_exception_lacks_has_no_struct_to_raise() {
    let declared = ["term".to_string()];
    assert_eq!(
        LastResort::bad_boolean("or").struct_fields(&declared, &[NIL]),
        Err("exception `Elixir.BadBooleanError` declares no field `operator`".to_string()),
        "the mismatch is named, not raised as a struct missing a field"
    );
}

#[test]
fn the_words_an_exception_declares_are_its_default_not_a_copy_the_compiler_keeps() {
    let message = library_declaration("ArgumentError");
    assert_eq!(
        message,
        vec![("message".to_string(), Some("\"argument error\"".to_string()))],
        "ArgumentError words itself"
    );
    assert_eq!(fields(&LastResort::argument_error()), vec![]);
}

#[test]
fn a_function_head_miss_carries_the_function_it_missed_and_none_of_its_arguments() {
    let raised = LastResort::function_clause(Some("Elixir.M".to_string()), "f".to_string(), 1);
    assert_eq!(raised.exception(), Some("Elixir.FunctionClauseError"));
    assert_eq!(
        fields(&raised),
        vec![
            ("function", atom("f")),
            ("arity", FieldTerm::Literal(LiteralTerm::Ground(GroundValue::Int(1)))),
            ("module", atom("Elixir.M")),
        ],
        "the fields about the arguments keep the default their module declares"
    );
    assert_eq!(raised.consumed_inputs(), 0, "Elixir's message names the function only");
}

#[test]
fn a_function_outside_any_module_has_no_module_to_carry() {
    let raised = LastResort::function_clause(None, "main".to_string(), 0);
    assert!(
        fields(&raised).iter().all(|(name, _)| *name != "module"),
        "the module field keeps its default"
    );
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
        vec![("protocol", atom("Elixir.String.Chars")), ("value", FieldTerm::Subject)]
    );
    assert_eq!(raised.consumed_inputs(), 1);
}

#[test]
fn the_atoms_of_a_last_resort_are_the_atoms_its_fields_write() {
    let raised = LastResort::bad_boolean("or");
    assert_eq!(
        raised.atoms().collect::<Vec<_>>(),
        ["or"],
        "the struct's module and field names are its schema's, not atoms the code writes"
    );
    assert_eq!(LastResort::reraise().atoms().count(), 0);
}
