use crate::ast::Program;
use crate::diag::{Diagnostic, Diagnostics, SourceMap};
use crate::fz_ir::Module;
use crate::lexer::Lexer;
use crate::macros;
use crate::parser::Parser;
use crate::pattern_matrix::SubjectDomain;
use crate::resolve;
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types};
use std::collections::HashSet;

pub struct FrontendOk {
    pub sm: SourceMap,
    #[allow(dead_code)]
    pub prog: Program,
    pub module: Module,
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
            entry[i] &= t.is_subtype(ty, &list_any);
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

pub fn check_frontend<T>(t: &mut T, prog: &Program, module: &Module) -> Diagnostics
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mt = crate::ir_typer::type_module(t, module, &crate::telemetry::NullTelemetry);
    let mut diags = Diagnostics::from_vec(crate::spec_check::validate_specs(t, prog, module, &mt));
    diags.extend(check_patterns(t, prog, module, &mt));
    diags
}

#[cfg(test)]
pub fn compile_source(src: String, source_name: String) -> FrontendResult {
    let mut t = crate::types::ConcreteTypes;
    compile_source_with_types(&mut t, src, source_name)
}

pub fn compile_source_with_types<T>(t: &mut T, src: String, source_name: String) -> FrontendResult
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut sm = SourceMap::new();
    let file_id = sm.add_file(source_name, src.clone());
    let toks = match Lexer::with_file(&src, file_id).tokenize() {
        Ok(toks) => toks,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    let prog = match Parser::new(toks).parse_program() {
        Ok(prog) => prog,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    let mut prog = match resolve::flatten_modules(t, prog) {
        Ok(prog) => prog,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    if let Err(e) = macros::expand_program(&mut prog) {
        return Err(fail(sm, e.to_diagnostic()));
    }
    let module = match crate::ir_lower::lower_program(t, &prog) {
        Ok(module) => module,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    let diagnostics = check_frontend(t, &prog, &module);
    Ok(FrontendOk {
        sm,
        prog,
        module,
        diagnostics,
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::diag::codes;

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
        assert!(err.diagnostics.has_errors());
    }
}
