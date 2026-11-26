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
fn failed_offset_matches_process_layout() {
    let process = process();
    let base = (&process as *const Process).addr();
    let field = (&process.failed as *const bool).addr();

    assert_eq!(PROCESS_FAILED_OFFSET, (field - base) as i32);
}

#[test]
fn delivered_offset_matches_process_layout() {
    let process = process();
    let base = (&process as *const Process).addr();
    let field = (&process.delivered as *const Option<crate::process::ClosureRef>).addr();

    assert_eq!(PROCESS_DELIVERED_OFFSET, (field - base) as i32);
    assert_eq!(std::mem::size_of::<Option<crate::process::ClosureRef>>(), 8);
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

/// Intent: compiled code orders two atoms by reading their name prefixes
/// through the process, and a prefix read that way orders as the names do
/// whenever two prefixes differ, however the table has grown since.
#[test]
fn compiled_code_reads_an_atoms_name_prefix_through_the_process_while_the_table_grows() {
    let process = process();
    let words = (&process as *const Process).cast::<u8>();
    let prefix = |id: u32| unsafe {
        let at = words
            .add(PROCESS_ATOM_NAME_PREFIXES_OFFSET as usize)
            .cast::<*const *const u64>()
            .read();
        at.read().add(id as usize).read()
    };
    let names = ["", "a", "a\0", "a\0b", "ab", "eight888", "eight888a", "zebra", "é"];
    let ids: Vec<u32> = names.iter().rev().map(|name| process.node.intern_atom(name)).collect();
    let grown: Vec<u32> = (0..10_000)
        .map(|n| process.node.intern_atom(&format!("grown_{n}")))
        .collect();
    let named: Vec<(&str, u32)> = names.iter().rev().copied().zip(ids).collect();
    assert_eq!(prefix(grown[9_999]), u64::from_be_bytes(*b"grown_99"));
    for (left_name, left) in &named {
        for (right_name, right) in &named {
            let (a, b) = (prefix(*left), prefix(*right));
            if a != b {
                assert_eq!(a.cmp(&b), left_name.cmp(right_name), "{left_name:?} vs {right_name:?}");
            }
        }
    }
    let zebra = named.iter().find(|(name, _)| *name == "zebra").expect("interned").1;
    assert_eq!(prefix(zebra), u64::from_be_bytes(*b"zebra\0\0\0"));
}
