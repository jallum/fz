use crate::fz_ir::{ExternId, ExternTy};
use std::collections::HashMap;

/// Name → ExternId index, built during the zeroth lowering pass.
pub struct ExternTable {
    map: HashMap<String, ExternId>,
}

impl ExternTable {
    pub fn new() -> Self {
        Self { map: HashMap::new() }
    }
    pub(crate) fn insert(&mut self, name: String, id: ExternId) {
        self.map.insert(name, id);
    }
    pub fn lookup(&self, name: &str) -> Option<ExternId> {
        self.map.get(name).copied()
    }
}

/// Map a single token identifier to an `ExternTy`. Used when resolving the
/// return-type annotation in an `extern "C" fn` declaration.
/// fz-y3k — split an extern's fz-visible name into the C symbol it resolves
/// to. A `lib::name` prefix is fz-side documentation/namespacing only; the
/// linker sees just the bare suffix. fz-axu — externs declared inside a
/// `defmodule Foo do ... end` get auto-qualified by the resolver to
/// `Foo.name` (with a `.`), which is also fz-side decoration; strip
/// either separator to recover the C symbol. Single-segment names
/// round-trip.
pub(crate) fn extern_symbol_from_name(fz_name: &str) -> &str {
    if let Some((_, sym)) = fz_name.rsplit_once("::") {
        return sym;
    }
    if let Some((_, sym)) = fz_name.rsplit_once('.') {
        return sym;
    }
    fz_name
}

pub(crate) fn extern_ty_from_name(name: &str) -> Option<ExternTy> {
    match name {
        "any" | "atom" | "bool" => Some(ExternTy::Any),
        "integer" => Some(ExternTy::I64),
        "float" => Some(ExternTy::F64),
        "nil" => Some(ExternTy::Unit),
        "never" => Some(ExternTy::Never),
        // fz-0cv — binary marshal classes; one fz binary arg → one
        // `*const u8` C arg. See [[fz-9ss]] for the runtime helpers.
        "binary" => Some(ExternTy::Binary),
        "cstring" => Some(ExternTy::CString),
        _ => None,
    }
}
