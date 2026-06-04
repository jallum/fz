use super::*;
use crate::heap::SchemaRegistry;
use std::cell::RefCell;
use std::rc::Rc;

fn process() -> Process {
    let schemas = Rc::new(RefCell::new(SchemaRegistry::new()));
    Process::new(schemas)
}

#[test]
fn reductions_remaining_offset_matches_process_layout() {
    let process = process();
    let base = (&process as *const Process).addr();
    let field = (&process.reductions_remaining as *const i32).addr();

    assert_eq!(PROCESS_REDUCTIONS_REMAINING_OFFSET, (field - base) as i32);
}

#[test]
fn yield_reasons_offset_matches_process_layout() {
    let process = process();
    let base = (&process as *const Process).addr();
    let field = (&process.yield_reasons as *const u8).addr();

    assert_eq!(PROCESS_YIELD_REASONS_OFFSET, (field - base) as i32);
}
