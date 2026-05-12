//! fz-ul4.23.10 — runtime staticlib for fz code (JIT, interp, AOT).
//!
//! Owns the per-task substrate that every execution path shares:
//! FzValue tagged-pointer rep (`fz_value`), per-task heap (`heap`),
//! Process struct + TLS (`process`), bit-level encoders (`bitstr`),
//! and the JIT/AOT extern "C" FFI surface (`ir_runtime`). AOT-compiled
//! binaries link against this crate as a staticlib; the fz binary
//! links against it as an rlib.
//!
//! Pre-23.10 history: this crate held only the atom table + `.12`-era
//! print helpers. The substrate has been lifted out of the binary
//! (src/*.rs → runtime/src/*.rs) so the linker can resolve every fz_*
//! symbol from one place. Two surfaces:

pub mod aot_shim;
pub mod bitstr;
pub mod fz_value;
pub mod heap;
pub mod ir_runtime;
pub mod process;
pub mod scheduler_hooks;

use std::sync::Mutex;

// ---------------------------------------------------------------------------
// Atom table
// ---------------------------------------------------------------------------

struct AtomTable {
    names: Vec<String>,
}

impl AtomTable {
    const fn new() -> Self {
        Self { names: Vec::new() }
    }
}

static ATOMS: Mutex<AtomTable> = Mutex::new(AtomTable::new());

/// Intern an atom name, returning a stable u32 id. Same name → same id for
/// the lifetime of the process.
///
/// Linear-scan lookup — fine for this tier; .14 or beyond can swap in a
/// hashmap if atom interning becomes a hotspot.
pub fn intern(name: &str) -> u32 {
    let mut t = ATOMS.lock().unwrap();
    if let Some(idx) = t.names.iter().position(|n| n == name) {
        return idx as u32;
    }
    let id = t.names.len() as u32;
    t.names.push(name.to_string());
    id
}

/// Resolve an atom id back to its name. Returns `None` if the id is unknown
/// (which should never happen for ids minted via `intern`).
pub fn name_of(id: u32) -> Option<String> {
    let t = ATOMS.lock().unwrap();
    t.names.get(id as usize).cloned()
}

/// Reset the atom table. Test-only — production code should never call this.
#[doc(hidden)]
pub fn _reset_atoms() {
    let mut t = ATOMS.lock().unwrap();
    t.names.clear();
}

// ---------------------------------------------------------------------------
// C-ABI builtins called from compiled fz code
// ---------------------------------------------------------------------------

// fz-ul4.27.7 (VR.5b): typed print helpers. The JIT routes Prim::Builtin::Print
// to these directly when ir_typer narrows the arg, skipping the boxing
// round-trip through `fz_print_value`. Rendering matches `fz_value::debug::render`
// for the corresponding tag — same byte-for-byte output as the polymorphic
// path. Each helper also pushes to `TEST_CAPTURE` so cargo-test assertions
// work the same way regardless of which entry point the JIT picked.

fn emit_print_line(s: String) {
    println!("{}", s);
    crate::ir_runtime::TEST_CAPTURE.with(|c| c.borrow_mut().push(s));
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_i64(n: i64) {
    emit_print_line(n.to_string());
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_f64(x: f64) {
    let s = if x.is_finite() && x.fract() == 0.0 {
        format!("{:.1}", x)
    } else {
        format!("{}", x)
    };
    emit_print_line(s);
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_bool(b: u8) {
    emit_print_line(if b != 0 { "true".to_string() } else { "false".to_string() });
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_atom(id: u32) {
    let s = match name_of(id) {
        Some(n) => format!(":{}", n),
        None => format!(":<atom#{}>", id),
    };
    emit_print_line(s);
}

#[unsafe(no_mangle)]
pub extern "C" fn fz_print_nil() {
    emit_print_line("nil".to_string());
}

/// Aborts with `msg` printed to stderr. `msg_ptr`/`msg_len` describe a UTF-8
/// byte slice; the compiler emits these from a string literal embedded in
/// the binary. Used for case no-match, integer overflow guards (.12.5), etc.
///
/// # Safety
/// `msg_ptr` must point to `msg_len` valid UTF-8 bytes.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_panic(msg_ptr: *const u8, msg_len: usize) -> ! {
    let bytes = unsafe { std::slice::from_raw_parts(msg_ptr, msg_len) };
    let s = std::str::from_utf8(bytes).unwrap_or("<panic message: invalid utf-8>");
    eprintln!("fz panic: {}", s);
    std::process::abort();
}

/// Register a compile-time-interned atom at runtime startup. AOT-compiled
/// binaries call this once per atom from a constructor before main() runs,
/// so the runtime's id↔name mapping matches the compiler's. The compiler
/// emits one call per atom in interning order; this asserts the id matches
/// what the compiler chose, panicking if the table has been touched first.
#[unsafe(no_mangle)]
pub unsafe extern "C" fn fz_register_atom(
    expected_id: u32,
    name_ptr: *const u8,
    name_len: usize,
) {
    let bytes = unsafe { std::slice::from_raw_parts(name_ptr, name_len) };
    let name = std::str::from_utf8(bytes).expect("fz_register_atom: name not utf-8");
    let id = intern(name);
    if id != expected_id {
        eprintln!(
            "fz_register_atom: expected id {} for {:?}, got {} — atom table out of sync",
            expected_id, name, id
        );
        std::process::abort();
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;
    use std::sync::Mutex;

    // Atom tests touch global state. Serialize them so they don't interfere.
    static GUARD: Mutex<()> = Mutex::new(());

    #[test]
    fn intern_assigns_stable_ids() {
        let _g = GUARD.lock().unwrap();
        _reset_atoms();
        let a = intern("alpha");
        let b = intern("beta");
        let a2 = intern("alpha");
        assert_eq!(a, a2);
        assert_ne!(a, b);
    }

    #[test]
    fn name_of_round_trips() {
        let _g = GUARD.lock().unwrap();
        _reset_atoms();
        let id = intern("hello");
        assert_eq!(name_of(id).as_deref(), Some("hello"));
    }

    #[test]
    fn name_of_unknown_id_is_none() {
        let _g = GUARD.lock().unwrap();
        _reset_atoms();
        assert!(name_of(99_999).is_none());
    }

    #[test]
    fn register_atom_succeeds_when_id_matches() {
        let _g = GUARD.lock().unwrap();
        _reset_atoms();
        let name = b"first";
        unsafe { fz_register_atom(0, name.as_ptr(), name.len()) };
        assert_eq!(name_of(0).as_deref(), Some("first"));
    }
}
