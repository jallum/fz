use super::{CodeId, CodeMap};

#[test]
fn compiler2_code_text_is_total_for_defined_code() {
    let mut code = CodeMap::new();
    let code_id = code.define(Some("main.fz".to_string()), "fn main(), do: 42\n".to_string());

    assert_eq!(code.text(code_id), "fn main(), do: 42\n");
}

#[test]
#[should_panic(expected = "code ids should have source text")]
fn compiler2_code_text_panics_for_unknown_code_id() {
    let code = CodeMap::new();

    let _ = code.text(CodeId::ZERO);
}
