use super::*;

#[test]
fn binary_display_keeps_textual_utf8_quoted() {
    let value = Value::Binary(Rc::from(&b"hello"[..]));
    assert_eq!(format!("{}", value), "\"hello\"");
}

#[test]
fn binary_display_uses_byte_list_for_control_bytes() {
    let value = Value::Binary(Rc::from(&[1_u8, 2, 65][..]));
    assert_eq!(format!("{}", value), "<<1, 2, 65>>");
}
