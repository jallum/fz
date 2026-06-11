use super::parse_quoted_program;
use crate::telemetry::ConfiguredTelemetry;

fn parse_ok_fixture(path: &str, source: &str) {
    let tel = ConfiguredTelemetry::new();
    parse_quoted_program(path, source, &tel).unwrap_or_else(|error| panic!("{path} should parse like Elixir: {error}"));
}

fn parse_err_fixture(path: &str, source: &str, expected: &str) {
    let tel = ConfiguredTelemetry::new();
    let error = parse_quoted_program(path, source, &tel)
        .err()
        .unwrap_or_else(|| panic!("{path} should currently fail until its fixture is enabled"));
    assert!(
        error.msg.contains(expected),
        "{path} should mention `{expected}`; got `{}`",
        error.msg
    );
}

macro_rules! ok_test {
    ($name:ident, $fixture:literal) => {
        #[test]
        fn $name() {
            parse_ok_fixture($fixture, include_str!(concat!("../../fixtures2/", $fixture)));
        }
    };
}

macro_rules! err_test {
    ($name:ident, $fixture:literal, $expected:literal) => {
        #[test]
        fn $name() {
            parse_err_fixture(
                $fixture,
                include_str!(concat!("../../fixtures2/", $fixture)),
                $expected,
            );
        }
    };
}

ok_test!(elixir_parser_range_do_blocks, "00532_elixir_parser_range_do_blocks.fz");
ok_test!(elixir_parser_range_no_parens, "00533_elixir_parser_range_no_parens.fz");
err_test!(
    elixir_invalid_keyword_list_tuple_one,
    "00534_elixir_invalid_keyword_list_tuple_one.fz",
    "unexpected keyword list inside tuple"
);
err_test!(
    elixir_invalid_keyword_list_tuple_two,
    "00535_elixir_invalid_keyword_list_tuple_two.fz",
    "unexpected keyword list inside tuple"
);
err_test!(
    elixir_invalid_keyword_list_bitstring,
    "00536_elixir_invalid_keyword_list_bitstring.fz",
    "unexpected keyword list inside bitstring"
);
err_test!(
    elixir_expression_after_keyword_list_noparens_call,
    "00537_elixir_expression_after_keyword_list_noparens_call.fz",
    "unexpected expression after keyword list"
);
err_test!(
    elixir_expression_after_keyword_list_paren_call,
    "00538_elixir_expression_after_keyword_list_paren_call.fz",
    "unexpected expression after keyword list"
);
err_test!(
    elixir_expression_after_keyword_list_list_literal,
    "00539_elixir_expression_after_keyword_list_list_literal.fz",
    "unexpected expression after keyword list"
);
err_test!(
    elixir_expression_after_keyword_list_map_literal,
    "00540_elixir_expression_after_keyword_list_map_literal.fz",
    "unexpected expression after keyword list"
);
ok_test!(elixir_keyword_list_literals, "00541_elixir_keyword_list_literals.fz");
ok_test!(
    elixir_keyword_list_do_operand,
    "00542_elixir_keyword_list_do_operand.fz"
);
ok_test!(elixir_last_arg_keyword_list, "00543_elixir_last_arg_keyword_list.fz");
err_test!(
    elixir_keyword_missing_space_ident,
    "00544_elixir_keyword_missing_space_ident.fz",
    "keyword argument must be followed by space after: foo:"
);
err_test!(
    elixir_keyword_missing_space_unary_plus,
    "00545_elixir_keyword_missing_space_unary_plus.fz",
    "keyword argument must be followed by space after: foo:"
);
err_test!(
    elixir_keyword_missing_space_unary_plus_int,
    "00546_elixir_keyword_missing_space_unary_plus_int.fz",
    "keyword argument must be followed by space after: foo:"
);
