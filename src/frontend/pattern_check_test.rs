use super::*;
use crate::compiler::source::SourceMap;
use crate::frontend::resolve::flatten_modules;
use crate::parser::Parser;
use crate::parser::lexer::Lexer;
use crate::telemetry::Telemetry;

fn parse(src: &str, tel: &dyn Telemetry) -> Program {
    let mut sm = SourceMap::new();
    let fid = sm.add_code(Some("test.fz"), src);
    let toks = Lexer::with_code_id_and_source_name(src, fid, "<test>")
        .tokenize(tel)
        .unwrap();
    let prog = Parser::new(toks).parse_program(tel).unwrap();
    let mut ct = crate::types::new();
    flatten_modules(&mut ct, prog, tel).unwrap()
}

// PICKED: wildcard clause makes subsequent specific clauses unreachable
#[test]
fn detects_unreachable_after_wildcard_in_multi_clause_fn() {
    let prog = parse(
        "fn classify(_), do: :any\n\
         fn classify(0), do: :zero\n\
         fn main(), do: classify(7)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let diags = check_program(&mut crate::types::new(), &prog, None, None);
    assert!(
        diags.iter().any(|d| d.code == codes::TYPE_UNREACHABLE_ARM),
        "expected unreachable-arm diag, got {:?}",
        diags.iter().map(|d| d.code).collect::<Vec<_>>()
    );
}

// PICKED: wildcard arm in case makes subsequent arms unreachable
#[test]
fn detects_unreachable_after_wildcard_in_case() {
    let prog = parse(
        "fn f(v) do\n\
           case v do\n\
             _ -> :any\n\
             0 -> :zero\n\
           end\n\
         end\n\
         fn main(), do: f(7)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let diags = check_program(&mut crate::types::new(), &prog, None, None);
    assert!(diags.iter().any(|d| d.code == codes::TYPE_UNREACHABLE_ARM));
}

// PICKED: specific clause before wildcard is reachable, no spurious warning
#[test]
fn no_warning_when_specific_then_wildcard() {
    let prog = parse(
        "fn classify(0), do: :zero\n\
         fn classify(_), do: :other\n\
         fn main(), do: classify(7)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let diags = check_program(&mut crate::types::new(), &prog, None, None);
    assert!(
        diags.is_empty(),
        "should not warn when specific-then-wildcard: {:?}",
        diags.iter().map(|d| d.message.clone()).collect::<Vec<_>>()
    );
}

// PICKED: fn with only literal clauses and no wildcard is inexhaustive
#[test]
fn detects_inexhaustive_multi_clause_fn() {
    let prog = parse(
        "fn classify(0), do: :zero\n\
         fn classify(1), do: :one\n\
         fn main(), do: classify(7)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let diags = check_program(&mut crate::types::new(), &prog, None, None);
    assert!(
        diags.iter().any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE),
        "expected no-matching-clause diag, got {:?}",
        diags.iter().map(|d| d.code).collect::<Vec<_>>()
    );
}

// PICKED: case with only literal arms and no wildcard is inexhaustive
#[test]
fn detects_inexhaustive_case() {
    let prog = parse(
        "fn f(v) do\n\
           case v do\n\
             0 -> :zero\n\
             1 -> :one\n\
           end\n\
         end\n\
         fn main(), do: f(7)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let diags = check_program(&mut crate::types::new(), &prog, None, None);
    assert!(diags.iter().any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE));
}

// PICKED: wildcard clause makes pattern set exhaustive, no warning
#[test]
fn no_inexhaustive_with_wildcard() {
    let prog = parse(
        "fn classify(0), do: :zero\n\
         fn classify(_), do: :other\n\
         fn main(), do: classify(7)",
        &crate::telemetry::ConfiguredTelemetry::new(),
    );
    let diags = check_program(&mut crate::types::new(), &prog, None, None);
    assert!(!diags.iter().any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE));
}
