//! Runtime-owned `Process` layout constants for generated code.
//!
//! Keep this module narrow: compiled code may only import offsets that are
//! intentionally part of the runtime/codegen ABI.

use crate::process::Process;
use std::mem::offset_of;

pub const PROCESS_REDUCTIONS_REMAINING_OFFSET: i32 = offset_of!(Process, reductions_remaining) as i32;
pub const PROCESS_YIELD_REASONS_OFFSET: i32 = offset_of!(Process, yield_reasons) as i32;

#[cfg(test)]
mod tests {
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
}
