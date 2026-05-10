//! fz-ul4.12.3 — AOT driver: source → standalone executable.
//!
//! Pipeline: parse → type → monomorphize (typer Descr → codegen LowerTy) →
//! lower each fn → ObjectModule → object file → cc + fz-runtime staticlib →
//! binary.
//!
//! Standalone per the .12 scope decision: any feature outside the in-scope
//! subset (heap types, multi-clause, closures, etc.) is a compile-time
//! error, named with the source location. The runtime is the fz-runtime
//! staticlib; no interpreter is shipped in the binary.

use crate::ast::*;
use crate::codegen::{lower_fn, AtomInterner, FnSig, LowerError, LowerResult, LowerTy};
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::typer::Typer;
use crate::types::*;
use cranelift_codegen::ir::{self, AbiParam, ExternalName, InstBuilder, Signature, UserExternalName, UserFuncName};
use cranelift_codegen::isa::CallConv;
use cranelift_codegen::settings::{self, Configurable};
use cranelift_codegen::Context;
use cranelift_module::{DataDescription, FuncId, Linkage, Module};
use cranelift_object::{ObjectBuilder, ObjectModule};
use std::collections::HashMap;
use std::path::Path;
use std::process::Command;
use std::sync::Arc;

// ---------------------------------------------------------------------------
// Typer Descr → codegen LowerTy
// ---------------------------------------------------------------------------

/// Map a typer descriptor to a unique LowerTy. Returns `None` for descriptors
/// outside the .12 in-scope subset (unions across kinds, heap types, `any`,
/// imprecise singletons, etc.).
pub fn derive_lowerty(d: &Descr) -> Option<LowerTy> {
    if d.is_empty() {
        return None;
    }

    // Reject anything outside scalar+tuple before classifying.
    let any_list = !d.lists.is_empty();
    let any_func = !d.funcs.is_empty();
    let any_map = !d.maps.is_empty();
    let any_str = !d.strs.is_none();
    let basic_other = (d.basic.raw()
        & !(BasicBits::NIL.raw() | BasicBits::BOOL.raw()))
        != 0;
    if any_list || any_func || any_map || any_str || basic_other {
        return None;
    }

    let has_nil = d.basic.contains_all(BasicBits::NIL);
    let has_bool = d.basic.contains_all(BasicBits::BOOL);
    let has_int = !d.ints.is_none();
    let has_float = !d.floats.is_none();
    let has_atom = !d.atoms.is_none();
    let has_tuple = !d.tuples.is_empty();

    // Exactly one axis populated.
    let count = [has_nil, has_bool, has_int, has_float, has_atom, has_tuple]
        .iter()
        .filter(|b| **b)
        .count();
    if count != 1 {
        return None;
    }

    if has_nil { return Some(LowerTy::Nil); }
    if has_bool { return Some(LowerTy::Bool); }
    if has_int { return Some(LowerTy::I64); }
    if has_float { return Some(LowerTy::F64); }
    if has_atom { return Some(LowerTy::Atom); }

    // Tuple: must be a single positive shape with no negatives, all-scalar
    // components recursively reducible.
    if d.tuples.len() == 1 {
        let conj = &d.tuples[0];
        if conj.neg.is_empty() && conj.pos.len() == 1 {
            let elems: Option<Vec<LowerTy>> =
                conj.pos[0].elems.iter().map(derive_lowerty).collect();
            return elems.map(LowerTy::Tuple);
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Monomorphization
// ---------------------------------------------------------------------------

#[derive(Clone)]
pub struct MonoFn {
    pub name: String,
    pub sig: FnSig,
    pub def: FnDef,
}

/// Walk every user fn and derive a LowerTy signature from the typer's
/// inferred arrow type. Errors if any fn falls outside the in-scope subset.
pub fn monomorphize(prog: &Program, typer: &Typer) -> Result<Vec<MonoFn>, Vec<String>> {
    let mut out = Vec::new();
    let mut errs = Vec::new();
    for item in &prog.items {
        let Item::Fn(def) = &**item else { continue };
        if def.is_macro {
            continue;
        }
        let arrow = match typer.globals.get(&def.name) {
            Some(t) => t,
            None => {
                errs.push(format!("{}: typer has no entry", def.name));
                continue;
            }
        };
        let (params, ret) = match extract_simple_arrow(arrow) {
            Some(p) => p,
            None => {
                errs.push(format!(
                    "{}: type {} is not a single monomorphic arrow in the .12 scalar+tuple subset",
                    def.name, format_descr_short(arrow)
                ));
                continue;
            }
        };
        out.push(MonoFn {
            name: def.name.clone(),
            sig: FnSig { params, ret },
            def: def.clone(),
        });
    }
    if !errs.is_empty() {
        return Err(errs);
    }
    Ok(out)
}

pub fn extract_simple_arrow(d: &Descr) -> Option<(Vec<LowerTy>, LowerTy)> {
    // Expect one DNF func conjunction with no negatives. Multi-clause fns
    // produce an intersection of arrows (one positive per clause); we accept
    // them if all positives reduce to the same LowerTy signature.
    if d.funcs.len() != 1 {
        return None;
    }
    let conj = &d.funcs[0];
    if !conj.neg.is_empty() || conj.pos.is_empty() {
        return None;
    }
    let mut sig: Option<(Vec<LowerTy>, LowerTy)> = None;
    for arrow in &conj.pos {
        let params: Vec<LowerTy> = arrow.args.iter().map(derive_lowerty).collect::<Option<_>>()?;
        let ret = derive_lowerty(&arrow.ret)?;
        match &sig {
            None => sig = Some((params, ret)),
            Some((p0, r0)) => {
                if p0 != &params || r0 != &ret {
                    return None;
                }
            }
        }
    }
    sig
}

fn format_descr_short(d: &Descr) -> String {
    // Best-effort short formatter; types.rs has its own Display.
    format!("{}", d)
}

// ---------------------------------------------------------------------------
// Build pipeline
// ---------------------------------------------------------------------------

/// Names of runtime C-ABI symbols the compiler can reference.
const RUNTIME_SYMBOLS: &[(&str, &[LowerTy], Option<LowerTy>)] = &[
    ("fz_print_i64", &[LowerTy::I64], None),
    ("fz_print_f64", &[LowerTy::F64], None),
    ("fz_print_bool", &[LowerTy::Bool], None),
    ("fz_print_atom", &[LowerTy::Atom], None),
    ("fz_print_nil", &[], None),
];

fn runtime_sig(params: &[LowerTy], ret: Option<LowerTy>) -> FnSig {
    FnSig {
        params: params.to_vec(),
        ret: ret.unwrap_or(LowerTy::Nil),
    }
}

fn host_isa() -> Arc<dyn cranelift_codegen::isa::TargetIsa> {
    let mut flag_builder = settings::builder();
    flag_builder.set("opt_level", "speed").unwrap();
    flag_builder.set("is_pic", "true").unwrap();
    let isa_builder = cranelift_native::builder().expect("host ISA");
    isa_builder
        .finish(settings::Flags::new(flag_builder))
        .expect("isa finish")
}

#[derive(Debug)]
pub struct BuildError(pub String);

impl std::fmt::Display for BuildError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "fz build: {}", self.0)
    }
}
impl std::error::Error for BuildError {}

impl From<String> for BuildError { fn from(s: String) -> Self { Self(s) } }

/// Build an executable from `src_path` to `out_path`. Returns an error if
/// any step fails (parse, type, monomorphize, codegen, link).
pub fn build(src_path: &Path, out_path: &Path) -> Result<(), BuildError> {
    let src = std::fs::read_to_string(src_path)
        .map_err(|e| BuildError(format!("reading {}: {}", src_path.display(), e)))?;
    let toks = Lexer::new(&src)
        .tokenize()
        .map_err(|e| BuildError(format!("{}", e)))?;
    let prog = Parser::new(toks)
        .parse_program()
        .map_err(|e| BuildError(format!("{}", e)))?;
    let mut typer = Typer::new();
    typer.type_program(&prog);
    if !typer.errors.is_empty() {
        return Err(BuildError(format!(
            "type errors:\n  {}",
            typer.errors.join("\n  ")
        )));
    }
    let monos = monomorphize(&prog, &typer)
        .map_err(|errs| BuildError(format!("not in .12 scope:\n  {}", errs.join("\n  "))))?;

    // Locate user main.
    let main_mono = monos
        .iter()
        .find(|m| m.name == "main" && m.sig.params.is_empty())
        .ok_or_else(|| {
            BuildError("no `fn main()` defined (AOT requires a zero-arg main)".into())
        })?
        .clone();

    let isa = host_isa();
    let obj_builder = ObjectBuilder::new(
        isa,
        out_path
            .file_stem()
            .map(|s| s.to_string_lossy().into_owned())
            .unwrap_or_else(|| "fz_obj".into()),
        cranelift_module::default_libcall_names(),
    )
    .map_err(|e| BuildError(format!("ObjectBuilder: {}", e)))?;
    let mut module = ObjectModule::new(obj_builder);

    // Declare runtime symbols.
    let mut runtime_ids: HashMap<&'static str, FuncId> = HashMap::new();
    for (sym, params, ret) in RUNTIME_SYMBOLS {
        let sig = runtime_sig(params, ret.clone());
        let cl_sig = sig.to_cranelift(CallConv::SystemV);
        let id = module
            .declare_function(sym, Linkage::Import, &cl_sig)
            .map_err(|e| BuildError(format!("declare {}: {}", sym, e)))?;
        runtime_ids.insert(sym, id);
    }
    // fz_register_atom signature: (u32, *const u8, usize) -> ()
    let reg_sig = {
        let mut s = Signature::new(CallConv::SystemV);
        s.params.push(AbiParam::new(ir::types::I32));
        s.params.push(AbiParam::new(ir::types::I64));
        s.params.push(AbiParam::new(ir::types::I64));
        s
    };
    let reg_id = module
        .declare_function("fz_register_atom", Linkage::Import, &reg_sig)
        .map_err(|e| BuildError(format!("declare fz_register_atom: {}", e)))?;

    // Declare each user fn (rename `main` → `fz_user_main` to free `main`
    // for the C entry-point shim).
    let mut user_ids: HashMap<String, FuncId> = HashMap::new();
    for m in &monos {
        let sym = if m.name == "main" { "fz_user_main".to_string() } else { m.name.clone() };
        let cl_sig = m.sig.to_cranelift(CallConv::SystemV);
        let id = module
            .declare_function(&sym, Linkage::Export, &cl_sig)
            .map_err(|e| BuildError(format!("declare {}: {}", sym, e)))?;
        user_ids.insert(m.name.clone(), id);
    }

    // Lower and define each user fn.
    let callee_sigs: HashMap<String, FnSig> = monos
        .iter()
        .map(|m| (m.name.clone(), m.sig.clone()))
        .collect();
    let mut atoms = AtomInterner::default();
    for m in &monos {
        let r = lower_fn(&m.def, &m.sig, &callee_sigs, &mut atoms)
            .map_err(|e: LowerError| BuildError(format!("{}: {}", m.name, e)))?;
        let LowerResult { mut func, callee_imports, builtin_imports } = r;
        rewrite_user_names(&mut func, &callee_imports, &builtin_imports, &user_ids, &runtime_ids)?;
        let mut ctx = Context::for_function(func);
        let user_id = user_ids[&m.name];
        module
            .define_function(user_id, &mut ctx)
            .map_err(|e| BuildError(format!("{}: {}", m.name, e)))?;
    }

    // Emit one data object per interned atom name (UTF-8 bytes, no NUL).
    let atom_data_ids = emit_atom_data(&mut module, &atoms.names)?;

    // Emit `main` C entry-point shim.
    emit_c_main_shim(
        &mut module,
        &main_mono,
        &user_ids,
        &runtime_ids,
        reg_id,
        &atom_data_ids,
        &atoms.names,
    )?;

    // Finish module → object bytes → write .o → link.
    let obj_product = module.finish();
    let obj_bytes = obj_product
        .emit()
        .map_err(|e| BuildError(format!("emit: {}", e)))?;
    let obj_path = out_path.with_extension("o");
    std::fs::write(&obj_path, &obj_bytes)
        .map_err(|e| BuildError(format!("write {}: {}", obj_path.display(), e)))?;

    // Invoke cc to link with the runtime staticlib.
    link(&obj_path, out_path)?;
    Ok(())
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

fn rewrite_user_names(
    func: &mut ir::Function,
    callee_imports: &[String],
    builtin_imports: &[&'static str],
    user_ids: &HashMap<String, FuncId>,
    runtime_ids: &HashMap<&'static str, FuncId>,
) -> Result<(), BuildError> {
    let entries: Vec<(ir::UserExternalNameRef, UserExternalName)> = func
        .params
        .user_named_funcs()
        .iter()
        .map(|(r, n)| (r, n.clone()))
        .collect();
    for (r, name) in entries {
        let new_id = match name.namespace {
            0 => {
                let callee = &callee_imports[name.index as usize];
                // `main` was renamed to `fz_user_main` at declaration time;
                // self-recursion through "main" goes to the same FuncId.
                let id = user_ids.get(callee).ok_or_else(|| {
                    BuildError(format!("internal: callee {} not declared", callee))
                })?;
                id.as_u32()
            }
            1 => {
                let sym = builtin_imports[name.index as usize];
                let id = runtime_ids
                    .get(sym)
                    .ok_or_else(|| BuildError(format!("internal: runtime {} not declared", sym)))?;
                id.as_u32()
            }
            _ => return Err(BuildError(format!("unknown namespace {}", name.namespace))),
        };
        func.params
            .reset_user_func_name(r, UserExternalName { namespace: 0, index: new_id });
    }
    Ok(())
}

fn emit_atom_data(
    module: &mut ObjectModule,
    names: &[String],
) -> Result<Vec<cranelift_module::DataId>, BuildError> {
    let mut out = Vec::with_capacity(names.len());
    for (i, n) in names.iter().enumerate() {
        let mut data = DataDescription::new();
        data.define(n.as_bytes().to_vec().into_boxed_slice());
        let id = module
            .declare_data(&format!("fz_atom_{}", i), Linkage::Local, false, false)
            .map_err(|e| BuildError(format!("declare atom data {}: {}", i, e)))?;
        module
            .define_data(id, &data)
            .map_err(|e| BuildError(format!("define atom data {}: {}", i, e)))?;
        out.push(id);
    }
    Ok(out)
}

fn emit_c_main_shim(
    module: &mut ObjectModule,
    main_mono: &MonoFn,
    user_ids: &HashMap<String, FuncId>,
    _runtime_ids: &HashMap<&'static str, FuncId>,
    reg_id: FuncId,
    atom_data_ids: &[cranelift_module::DataId],
    atom_names: &[String],
) -> Result<(), BuildError> {
    // C-ABI: int main(int argc, char** argv).
    let mut sig = Signature::new(CallConv::SystemV);
    sig.params.push(AbiParam::new(ir::types::I32));
    sig.params.push(AbiParam::new(ir::types::I64));
    sig.returns.push(AbiParam::new(ir::types::I32));
    let main_id = module
        .declare_function("main", Linkage::Export, &sig)
        .map_err(|e| BuildError(format!("declare main: {}", e)))?;

    let mut func = ir::Function::with_name_signature(UserFuncName::user(0, main_id.as_u32()), sig);
    let mut fbctx = cranelift_frontend::FunctionBuilderContext::new();
    let mut builder = cranelift_frontend::FunctionBuilder::new(&mut func, &mut fbctx);

    let entry = builder.create_block();
    builder.append_block_params_for_function_params(entry);
    builder.switch_to_block(entry);
    builder.seal_block(entry);

    // Register atoms in id order.
    let reg_fr = module.declare_func_in_func(reg_id, builder.func);
    for (i, name) in atom_names.iter().enumerate() {
        let data_gv = module.declare_data_in_func(atom_data_ids[i], builder.func);
        let ptr = builder.ins().symbol_value(ir::types::I64, data_gv);
        let id_v = builder.ins().iconst(ir::types::I32, i as i64);
        let len_v = builder.ins().iconst(ir::types::I64, name.len() as i64);
        builder.ins().call(reg_fr, &[id_v, ptr, len_v]);
    }

    // Call user main (`fz_user_main`).
    let user_main_id = user_ids[&main_mono.name];
    let user_main_fr = module.declare_func_in_func(user_main_id, builder.func);
    let inst = builder.ins().call(user_main_fr, &[]);
    let _ = builder.inst_results(inst); // discard whatever main returns

    // return 0
    let zero = builder.ins().iconst(ir::types::I32, 0);
    builder.ins().return_(&[zero]);

    builder.finalize();
    let mut ctx = Context::for_function(func);
    module
        .define_function(main_id, &mut ctx)
        .map_err(|e| BuildError(format!("define main: {}", e)))?;
    Ok(())
}

fn link(obj_path: &Path, out_path: &Path) -> Result<(), BuildError> {
    let runtime_lib = locate_runtime_staticlib()
        .ok_or_else(|| BuildError("could not locate libfz_runtime.a — run `cargo build` first".into()))?;
    let cc = std::env::var("CC").unwrap_or_else(|_| "cc".into());
    let mut cmd = Command::new(&cc);
    cmd.arg(obj_path).arg(&runtime_lib).arg("-o").arg(out_path);
    if cfg!(target_os = "macos") {
        // Quiet macOS linker warnings about no version min specified.
        cmd.arg("-Wl,-no_warn_duplicate_libraries");
    }
    let out = cmd
        .output()
        .map_err(|e| BuildError(format!("invoke {}: {}", cc, e)))?;
    if !out.status.success() {
        return Err(BuildError(format!(
            "linker failed (status {}):\nstdout: {}\nstderr: {}",
            out.status,
            String::from_utf8_lossy(&out.stdout),
            String::from_utf8_lossy(&out.stderr)
        )));
    }
    Ok(())
}

fn locate_runtime_staticlib() -> Option<std::path::PathBuf> {
    // 1) FZ_RUNTIME_LIB env override.
    if let Ok(p) = std::env::var("FZ_RUNTIME_LIB") {
        let pb = std::path::PathBuf::from(p);
        if pb.exists() {
            return Some(pb);
        }
    }
    // 2) Look in `<cargo manifest>/target/{debug,release}` (test/`cargo run`).
    if let Ok(base) = std::env::var("CARGO_MANIFEST_DIR") {
        for profile in &["debug", "release"] {
            let p = std::path::Path::new(&base)
                .join("target")
                .join(profile)
                .join("libfz_runtime.a");
            if p.exists() {
                return Some(p);
            }
        }
    }
    // 3) Look next to the running executable (e.g. target/debug/fz alongside
    //    target/debug/libfz_runtime.a).
    if let Ok(exe) = std::env::current_exe() {
        if let Some(dir) = exe.parent() {
            let p = dir.join("libfz_runtime.a");
            if p.exists() {
                return Some(p);
            }
            // Test binaries live in target/debug/deps/; staticlib is one up.
            if let Some(parent) = dir.parent() {
                let p = parent.join("libfz_runtime.a");
                if p.exists() {
                    return Some(p);
                }
            }
        }
    }
    None
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lowerty_for_scalars() {
        assert_eq!(derive_lowerty(&Descr::int()), Some(LowerTy::I64));
        assert_eq!(derive_lowerty(&Descr::float()), Some(LowerTy::F64));
        assert_eq!(derive_lowerty(&Descr::bool_t()), Some(LowerTy::Bool));
        assert_eq!(derive_lowerty(&Descr::atom_top()), Some(LowerTy::Atom));
        assert_eq!(derive_lowerty(&Descr::atom_lit("x")), Some(LowerTy::Atom));
        assert_eq!(derive_lowerty(&Descr::nil()), Some(LowerTy::Nil));
        assert_eq!(derive_lowerty(&Descr::int_lit(7)), Some(LowerTy::I64));
    }

    #[test]
    fn lowerty_rejects_unions_across_kinds() {
        let d = Descr::int().union(&Descr::nil());
        assert_eq!(derive_lowerty(&d), None);
    }

    #[test]
    fn lowerty_rejects_heap_types() {
        assert_eq!(derive_lowerty(&Descr::list_of(Descr::int())), None);
        assert_eq!(derive_lowerty(&Descr::str_t()), None);
        assert_eq!(derive_lowerty(&Descr::map_top()), None);
    }

    #[test]
    fn lowerty_for_tuple_of_scalars() {
        let d = Descr::tuple_of([Descr::int(), Descr::bool_t()]);
        assert_eq!(
            derive_lowerty(&d),
            Some(LowerTy::Tuple(vec![LowerTy::I64, LowerTy::Bool]))
        );
    }

    #[test]
    fn lowerty_rejects_tuple_with_heap_component() {
        let d = Descr::tuple_of([Descr::int(), Descr::str_t()]);
        assert_eq!(derive_lowerty(&d), None);
    }

    #[test]
    fn end_to_end_aot_runs_binary() {
        // Skip if libfz_runtime.a hasn't been built yet.
        if locate_runtime_staticlib().is_none() {
            eprintln!("skip: libfz_runtime.a not present");
            return;
        }

        let dir = std::env::temp_dir().join(format!("fz-aot-test-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = dir.join("hello.fz");
        std::fs::write(
            &src,
            r#"
fn main() do
  print(40 + 2)
  print(:ok)
  print(true)
  print(nil)
end
"#,
        )
        .unwrap();
        let bin = dir.join("hello");
        build(&src, &bin).expect("build");

        let out = Command::new(&bin).output().expect("run");
        assert!(out.status.success(), "binary exit: {}", out.status);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.contains("42"), "stdout missing '42': {}", stdout);
        assert!(stdout.contains(":ok"), "stdout missing ':ok': {}", stdout);
    }


    #[test]
    fn end_to_end_aot_multi_clause_runs() {
        if locate_runtime_staticlib().is_none() {
            eprintln!("skip: libfz_runtime.a not present");
            return;
        }
        let dir = std::env::temp_dir().join(format!("fz-aot-multi-{}", std::process::id()));
        std::fs::create_dir_all(&dir).unwrap();
        let src = dir.join("multi.fz");
        std::fs::write(
            &src,
            r#"
fn classify(0), do: :zero
fn classify(n) when n > 0, do: :positive
fn classify(_), do: :negative

fn fact(0), do: 1
fn fact(n), do: n * fact(n - 1)

fn main() do
  print(classify(0))
  print(classify(7))
  print(classify(-3))
  print(fact(5))
end
"#,
        )
        .unwrap();
        let bin = dir.join("multi");
        build(&src, &bin).expect("build");

        let out = Command::new(&bin).output().expect("run");
        assert!(out.status.success(), "binary exit: {}", out.status);
        let stdout = String::from_utf8_lossy(&out.stdout);
        assert!(stdout.contains(":zero"), "stdout missing :zero: {}", stdout);
        assert!(stdout.contains(":positive"), "stdout missing :positive: {}", stdout);
        assert!(stdout.contains(":negative"), "stdout missing :negative: {}", stdout);
        assert!(stdout.contains("120"), "stdout missing 120: {}", stdout);
    }

    #[test]
    fn rejects_heap_typed_fn_at_aot() {
        let src = "fn make() do [1, 2, 3] end\nfn main() do print(make()) end";
        let toks = Lexer::new(src).tokenize().unwrap();
        let prog = Parser::new(toks).parse_program().unwrap();
        let mut t = Typer::new();
        t.type_program(&prog);
        let res = monomorphize(&prog, &t);
        assert!(res.is_err());
    }
}
