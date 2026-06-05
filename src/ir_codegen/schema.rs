use super::*;
use fz_runtime::heap::{FieldDescriptor, FieldKind, FieldKind::AnyValue, Schema};

/// Build a [cont_ptr, ...entry_params] frame schema. The cont_ptr slot is
/// always `AnyValue`; the param slots are described by `param_kinds`.
pub(crate) fn build_frame_schema(name: &str, param_kinds: &[FieldKind]) -> Schema {
    let n_fields = 1 + param_kinds.len();
    let mut fields = Vec::with_capacity(n_fields);
    fields.push(FieldDescriptor {
        offset: 0,
        kind: AnyValue,
        name: None,
    });
    for (i, k) in param_kinds.iter().enumerate() {
        fields.push(FieldDescriptor {
            offset: ((i + 1) * SLOT_BYTES as usize) as u32,
            kind: k.clone(),
            name: None,
        });
    }
    Schema {
        name: format!("Frame_{}", name),
        size: HEADER_SIZE as u32 + (n_fields as u32) * SLOT_BYTES as u32,
        fields,
    }
}
