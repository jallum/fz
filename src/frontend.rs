use crate::ast::Program;
use crate::diag::{Diagnostic, Diagnostics, SourceMap};
use crate::fz_ir::Module;
use crate::ir_typer::ModuleTypes;
use crate::lexer::Lexer;
use crate::macros;
use crate::parser::Parser;
use crate::pattern_matrix::SubjectDomain;
use crate::resolve;
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types};
use std::collections::HashSet;

pub struct FrontendOk {
    pub sm: SourceMap,
    pub _prog: Program,
    pub module: Module,
    pub module_types: ModuleTypes,
    pub diagnostics: Diagnostics,
}

pub struct FrontendErr {
    pub sm: SourceMap,
    pub diagnostics: Diagnostics,
}

pub type FrontendResult = Result<FrontendOk, FrontendErr>;

fn fail(sm: SourceMap, d: Diagnostic) -> FrontendErr {
    FrontendErr {
        sm,
        diagnostics: Diagnostics::from_one(d),
    }
}

pub fn check_patterns<T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes>(
    t: &mut T,
    prog: &Program,
    module: &Module,
    module_types: &crate::ir_typer::ModuleTypes,
) -> Diagnostics {
    let mut reduced = module.clone();
    let _ = crate::ir_reducer::reduce_module(t, &mut reduced);
    let reachable = crate::ir_callgraph::reachable_fns(t, &reduced);
    let survivors: HashSet<(String, usize)> = reachable
        .iter()
        .filter_map(|fid| {
            let &idx = reduced.fn_idx.get(fid)?;
            let f = &reduced.fns[idx];
            let arity = f.block(f.entry).params.len();
            Some((f.name.clone(), arity))
        })
        .collect();
    let domains = fn_subject_domains(t, module, module_types);
    Diagnostics::from_vec(crate::pattern_check::check_program(
        t,
        prog,
        Some(&survivors),
        Some(&domains),
    ))
}

fn fn_subject_domains<T: Types<Ty = crate::types::Ty>>(
    t: &mut T,
    module: &Module,
    module_types: &crate::ir_typer::ModuleTypes,
) -> std::collections::HashMap<(String, usize), Vec<SubjectDomain>> {
    let any = t.any();
    let list_any = t.list(any);
    let mut by_fn: std::collections::HashMap<(String, usize), Vec<bool>> =
        std::collections::HashMap::new();
    for (fid, key) in module_types.specs.keys() {
        let Some(&idx) = module.fn_idx.get(fid) else {
            continue;
        };
        let name = module.fns[idx].name.clone();
        let arity = key.len();
        let entry = by_fn
            .entry((name, arity))
            .or_insert_with(|| vec![true; key.len()]);
        for (i, ty) in key.iter().enumerate() {
            entry[i] &= match ty {
                Some(ty) => t.is_subtype(ty, &list_any),
                None => false,
            };
        }
    }
    by_fn
        .into_iter()
        .map(|(name_arity, positions)| {
            (
                name_arity,
                positions
                    .into_iter()
                    .map(|is_list| {
                        if is_list {
                            SubjectDomain::List
                        } else {
                            SubjectDomain::Any
                        }
                    })
                    .collect(),
            )
        })
        .collect()
}

pub fn check_frontend<T>(
    t: &mut T,
    prog: &Program,
    module: &Module,
    tel: &dyn crate::telemetry::Telemetry,
) -> (Diagnostics, ModuleTypes)
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mt = crate::ir_typer::type_module(t, module, tel);
    let mut diags = Diagnostics::from_vec(crate::spec_check::validate_specs(t, prog, module, &mt));
    diags.extend(check_patterns(t, prog, module, &mt));
    tel.execute(
        &["fz", "frontend", "checked"],
        &crate::measurements! { diagnostics: diags.len() },
        &crate::metadata! {
            module_path: module.module_path().to_owned(),
            program: crate::telemetry::value::opaque(prog),
            module: crate::telemetry::value::opaque(module),
            module_types: crate::telemetry::value::opaque(&mt),
        },
    );
    (diags, mt)
}

#[cfg(test)]
pub fn compile_source(src: String, source_name: String) -> FrontendResult {
    let mut t = crate::types::ConcreteTypes;
    compile_source_with_types(&mut t, src, source_name, &crate::telemetry::NullTelemetry)
}

pub fn compile_source_with_types<T>(
    t: &mut T,
    src: String,
    source_name: String,
    tel: &dyn crate::telemetry::Telemetry,
) -> FrontendResult
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name, src.clone());
    let toks = match Lexer::with_file(&src, file_id).tokenize_with_telemetry(tel) {
        Ok(toks) => toks,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    let prog = match Parser::new(toks).parse_program_with_telemetry(tel) {
        Ok(prog) => prog,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    tel.event(
        &["fz", "frontend", "parsed"],
        crate::metadata! {
            items: prog.items.len(),
            program: crate::telemetry::value::opaque(&prog),
        },
    );
    let mut prog = match resolve::flatten_modules(t, prog) {
        Ok(prog) => prog,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    tel.event(
        &["fz", "frontend", "resolved"],
        crate::metadata! {
            items: prog.items.len(),
            program: crate::telemetry::value::opaque(&prog),
        },
    );
    if let Err(e) = macros::expand_program(&mut prog) {
        return Err(fail(sm, e.to_diagnostic()));
    }
    tel.event(
        &["fz", "frontend", "macro_expanded"],
        crate::metadata! {
            items: prog.items.len(),
            program: crate::telemetry::value::opaque(&prog),
        },
    );
    let module = match crate::ir_lower::lower_program(t, &prog) {
        Ok(module) => module,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    tel.event(
        &["fz", "frontend", "lowered"],
        crate::metadata! {
            module_path: module.module_path().to_owned(),
            fns: module.fns.len(),
            module: crate::telemetry::value::opaque(&module),
        },
    );
    let (diagnostics, module_types) = check_frontend(t, &prog, &module, tel);
    Ok(FrontendOk {
        sm,
        _prog: prog,
        module,
        module_types,
        diagnostics,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::codes;
    use crate::telemetry::{ConfiguredTelemetry, Handler};
    use std::cell::RefCell;
    use std::rc::Rc;

    #[test]
    fn returns_warning_diagnostics_without_rendering() {
        let src = "\
fn classify(0), do: :zero
fn classify(1), do: :one
fn main(), do: classify(7)
";
        let out = match compile_source(src.to_string(), "test.fz".to_string()) {
            Ok(out) => out,
            Err(_) => panic!("frontend ok"),
        };
        assert!(
            out.diagnostics
                .as_slice()
                .iter()
                .any(|d| d.code == codes::TYPE_NO_MATCHING_CLAUSE)
        );
    }

    #[test]
    fn returns_error_diagnostics_without_rendering() {
        let err = match compile_source("fn main( do\n".to_string(), "bad.fz".to_string()) {
            Ok(_) => panic!("frontend should fail"),
            Err(err) => err,
        };
        assert!(
            err.diagnostics
                .as_slice()
                .iter()
                .any(|d| d.severity == crate::diag::diagnostic::Severity::Error)
        );
    }

    #[derive(Default)]
    struct StructuralFacts {
        parser_items: usize,
        parsed_items: usize,
        lowered_fns: usize,
        typed_specs: usize,
        checked_diagnostics: usize,
    }

    struct StructuralHandler(Rc<RefCell<StructuralFacts>>);

    impl Handler for StructuralHandler {
        fn handle(&self, ev: &crate::telemetry::Event<'_, '_, '_>) {
            match ev.name {
                ["fz", "parser", "items_built"] => {
                    let count = match ev.measurements.get("count") {
                        Some(crate::telemetry::Value::U64(n)) => *n as usize,
                        _ => 0,
                    };
                    self.0.borrow_mut().parser_items = count;
                }
                ["fz", "frontend", "parsed"] => {
                    if let Some(program) = ev
                        .metadata
                        .get("program")
                        .and_then(|v| v.downcast_ref::<crate::ast::Program>())
                    {
                        self.0.borrow_mut().parsed_items = program.items.len();
                    }
                }
                ["fz", "frontend", "lowered"] => {
                    if let Some(module) = ev
                        .metadata
                        .get("module")
                        .and_then(|v| v.downcast_ref::<crate::fz_ir::Module>())
                    {
                        self.0.borrow_mut().lowered_fns = module.fns.len();
                    }
                }
                ["fz", "typer", "typed"] => {
                    if let Some(module_types) = ev
                        .metadata
                        .get("module_types")
                        .and_then(|v| v.downcast_ref::<crate::ir_typer::ModuleTypes>())
                    {
                        self.0.borrow_mut().typed_specs = module_types.specs.len();
                    }
                }
                ["fz", "frontend", "checked"] => {
                    let diagnostics = match ev.measurements.get("diagnostics") {
                        Some(crate::telemetry::Value::U64(n)) => *n as usize,
                        _ => 0,
                    };
                    self.0.borrow_mut().checked_diagnostics = diagnostics;
                }
                _ => {}
            }
        }
    }

    #[test]
    fn structural_telemetry_exposes_compiler_artifacts_to_handlers() {
        let tel = ConfiguredTelemetry::new();
        let facts = Rc::new(RefCell::new(StructuralFacts::default()));
        tel.attach(&["fz"], Box::new(StructuralHandler(facts.clone())));

        let src = "fn id(x), do: x\nfn main(), do: id(1)\n";
        let mut t = crate::types::ConcreteTypes;
        let out =
            match compile_source_with_types(&mut t, src.to_string(), "test.fz".to_string(), &tel) {
                Ok(out) => out,
                Err(_) => panic!("frontend ok"),
            };

        let facts = facts.borrow();
        assert_eq!(facts.parser_items, 2);
        assert_eq!(facts.parsed_items, 2);
        assert_eq!(facts.lowered_fns, out.module.fns.len());
        assert_eq!(facts.typed_specs, out.module_types.specs.len());
        assert_eq!(facts.checked_diagnostics, out.diagnostics.len());
    }
}
