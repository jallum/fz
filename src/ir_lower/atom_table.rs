use std::collections::HashMap;

/// Atom interner: maps atom names to stable u32 ids.
/// Per-CompiledModule atom table built during AST → IR lowering.
///
/// fz-ul4.19.6 policy (atom-table cross-process semantics):
/// - Atom ids are assigned here, per Module. All Processes that run from
///   the same CompiledModule see the same atom ids (atoms are embedded as
///   u32 literals in compiled code; the ids ARE the atoms at runtime).
/// - Two CompiledModules built from different source produce independent
///   atom-id spaces. Cross-module sends (a future feature) would require
///   atom-id translation; not needed for v1.
pub struct AtomTable {
    map: HashMap<String, u32>,
}

impl Default for AtomTable {
    fn default() -> Self {
        Self::new()
    }
}

impl AtomTable {
    /// fz-yan.1 — reserve compile-time atom IDs for `nil`, `true`,
    /// `false`. These three are language keywords that desugar to
    /// atom literals (post-fz-yan); reserving them at construction
    /// time gives every module the same well-known IDs:
    ///
    ///   nil   → atom id 0  → NIL_ATOM_ID   (runtime/codegen NIL_BITS)
    ///   true  → atom id 1  → TRUE_ATOM_ID  (runtime/codegen TRUE_BITS)
    ///   false → atom id 2  → FALSE_ATOM_ID (runtime/codegen FALSE_BITS)
    ///
    /// User-source atoms (and runtime-reserved ones like
    /// `match_error` / `function_clause`) get ids ≥ 3.
    pub fn new() -> Self {
        let mut t = Self {
            map: HashMap::new(),
        };
        // Order matters: nil=0, true=1, false=2.
        let nil = t.intern("nil");
        let tr = t.intern("true");
        let fa = t.intern("false");
        debug_assert_eq!(nil, fz_runtime::fz_value::NIL_ATOM_ID);
        debug_assert_eq!(tr, fz_runtime::fz_value::TRUE_ATOM_ID);
        debug_assert_eq!(fa, fz_runtime::fz_value::FALSE_ATOM_ID);
        t
    }

    pub fn intern(&mut self, name: &str) -> u32 {
        if let Some(&id) = self.map.get(name) {
            return id;
        }
        let id = self.map.len() as u32;
        self.map.insert(name.to_string(), id);
        id
    }

    /// Return atom names in id order: id N -> names[N].
    pub fn names(&self) -> Vec<String> {
        let mut out = vec![String::new(); self.map.len()];
        for (k, &id) in &self.map {
            out[id as usize] = k.clone();
        }
        out
    }
}
