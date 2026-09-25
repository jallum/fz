use std::rc::Rc;

use fz_runtime::any_value::{AnyValueRef, ValueKind};

use super::is_remote_dot_callee;
use crate::compiler2::{QuotedSourceHeap, QuotedSourceMetadata};
use crate::source::SourceMap;

#[test]
fn remote_callee_probe_propagates_an_invalid_atom_payload() {
    let heap = Rc::new(QuotedSourceHeap::new());
    let builder = heap.builder();
    let unknown_atom_id = u64::MAX;
    let unknown_atom = AnyValueRef::from_scalar_slot(ValueKind::ATOM, &unknown_atom_id)
        .expect("stack scalar is a valid temporary atom carrier");
    let encoded = builder
        .ast_node(unknown_atom, &QuotedSourceMetadata::default(), builder.empty_list())
        .expect("builder copies the scalar into its owned heap");
    let root = builder.root(encoded).expect("quoted source root");
    let node = root
        .cursor()
        .ast_node(&SourceMap::new())
        .expect("structural read")
        .expect("AST node");

    let error = is_remote_dot_callee(&node).expect_err("remote callee probe must propagate invalid atom");
    assert!(error.to_string().contains("unknown atom id"), "{error}");
}
