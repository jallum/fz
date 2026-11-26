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

#[test]
fn unwinding_offset_matches_process_layout() {
    let process = process();
    let base = (&process as *const Process).addr();
    let field = (&process.unwinding as *const bool).addr();

    assert_eq!(PROCESS_UNWINDING_OFFSET, (field - base) as i32);
}

#[test]
fn heap_offset_matches_process_layout() {
    let process = process();
    let base = (&process as *const Process).addr();
    let field = (&process.heap as *const crate::heap::Heap).addr();

    assert_eq!(PROCESS_HEAP_OFFSET, (field - base) as i32);
}

#[test]
fn compiled_code_reads_an_atoms_key_hash_through_the_process_while_the_table_grows() {
    let process = process();
    let first = process.node.intern_atom("first");
    let words = (&process as *const Process).cast::<u8>();
    let key_hash = |id: u32| unsafe {
        let at = words
            .add(PROCESS_ATOM_KEY_HASHES_OFFSET as usize)
            .cast::<*const *const u64>()
            .read();
        at.read().add(id as usize).read()
    };
    assert_eq!(key_hash(first), crate::term_hash::atom_key_hash("first"));

    let grown: Vec<u32> = (0..10_000)
        .map(|n| process.node.intern_atom(&format!("grown_{n}")))
        .collect();
    assert_eq!(key_hash(first), crate::term_hash::atom_key_hash("first"));
    assert_eq!(key_hash(grown[9_999]), crate::term_hash::atom_key_hash("grown_9999"));
}
