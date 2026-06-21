use std::cell::RefCell;

pub(crate) const HEADER_SIZE: i32 = 16;
pub(crate) const SLOT_BYTES: i32 = 8;

thread_local! {
    static IR_TEXT_RECORD: RefCell<Option<Vec<(String, String)>>> = const { RefCell::new(None) };
}

pub fn ir_text_record_enable() {
    IR_TEXT_RECORD.with(|c| *c.borrow_mut() = Some(Vec::new()));
}

pub fn ir_text_record_enabled() -> bool {
    IR_TEXT_RECORD.with(|c| c.borrow().is_some())
}

pub fn ir_text_record_take() -> Vec<(String, String)> {
    IR_TEXT_RECORD.with(|c| c.borrow_mut().take().unwrap_or_default())
}
