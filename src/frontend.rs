use crate::ast::{Expr, FnClause, FnDef, Pattern, Program, Spanned};
use crate::diag::{Diagnostic, Diagnostics, SourceMap};
use crate::fz_ir::{FnId, Module};
use crate::ir_planner::ModulePlan;
use crate::lexer::Lexer;
use crate::macros;
use crate::parser::Parser;
use crate::pattern_matrix::SubjectDomain;
use crate::resolve::{self, InterfaceTable};
use crate::types::{ClosureTypes, LiteralTypes, RenderTypes, Types};
use std::collections::HashSet;

pub struct FrontendOk {
    pub sm: SourceMap,
    pub _prog: Program,
    pub module: Module,
    pub module_plan: ModulePlan,
    pub diagnostics: Diagnostics,
}

pub struct FrontendErr {
    pub sm: SourceMap,
    pub diagnostics: Diagnostics,
}

pub type FrontendResult = Result<FrontendOk, FrontendErr>;

pub(crate) struct ReplEntryOk {
    pub frontend: FrontendOk,
    pub entry_fn: FnId,
    pub input_frame: Vec<String>,
    pub output_frame: Vec<String>,
    pub entry_item: std::rc::Rc<crate::ast::Item>,
}

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
    module_plan: &crate::ir_planner::ModulePlan,
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
    let domains = fn_subject_domains(t, module, module_plan);
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
    module_plan: &crate::ir_planner::ModulePlan,
) -> std::collections::HashMap<(String, usize), Vec<SubjectDomain>> {
    let any = t.any();
    let list_any = t.list(any);
    let mut by_fn: std::collections::HashMap<(String, usize), Vec<bool>> =
        std::collections::HashMap::new();
    for spec_key in module_plan.specs.keys() {
        let Some(&idx) = module.fn_idx.get(&spec_key.fn_id) else {
            continue;
        };
        let name = module.fns[idx].name.clone();
        let arity = spec_key.input.len();
        let entry = by_fn
            .entry((name, arity))
            .or_insert_with(|| vec![true; spec_key.input.len()]);
        for (i, ty) in spec_key.input.iter().enumerate() {
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
) -> (Diagnostics, ModulePlan)
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut mt = crate::ir_planner::plan_module(t, module, tel);
    let mut diags = Diagnostics::from_vec(crate::spec_check::validate_specs(t, prog, module, &mt));
    diags.extend(check_patterns(t, prog, module, &mt));
    diags.extend(Diagnostics::from_vec(
        crate::ir_extern_marshal::resolve_module_types(t, module, &mut mt),
    ));
    tel.execute(
        &["fz", "frontend", "checked"],
        &crate::measurements! { diagnostics: diags.len() },
        &crate::metadata! {
            module_path: module.module_path().to_owned(),
            program: crate::telemetry::value::opaque(prog),
            module: crate::telemetry::value::opaque(module),
            module_plan: crate::telemetry::value::opaque(&mt),
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
    compile_source_with_interface_table(t, src, source_name, InterfaceTable::new(), tel)
}

pub fn compile_source_with_interface_table<T>(
    t: &mut T,
    src: String,
    source_name: String,
    interface_table: InterfaceTable,
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
    compile_program_with_interface_table(t, prog, sm, interface_table, tel)
}

pub(crate) fn compile_program_with_types<T>(
    t: &mut T,
    prog: Program,
    sm: SourceMap,
    tel: &dyn crate::telemetry::Telemetry,
) -> FrontendResult
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    compile_program_with_interface_table(t, prog, sm, InterfaceTable::new(), tel)
}

pub(crate) fn compile_program_with_interface_table<T>(
    t: &mut T,
    prog: Program,
    sm: SourceMap,
    interface_table: InterfaceTable,
    tel: &dyn crate::telemetry::Telemetry,
) -> FrontendResult
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let mut prog = match resolve::flatten_modules_with_interface_table(t, prog, interface_table) {
        Ok(prog) => prog,
        Err(e) => return Err(fail(sm, e.to_diagnostic())),
    };
    tel.event(
        &["fz", "frontend", "resolved"],
        crate::metadata! {
            items: prog.items.len(),
            module_interfaces: prog.module_interfaces.len(),
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
    let module = match crate::ir_lower::lower_program_with_telemetry(t, &prog, tel) {
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
    let (diagnostics, module_plan) = check_frontend(t, &prog, &module, tel);
    Ok(FrontendOk {
        sm,
        _prog: prog,
        module,
        module_plan,
        diagnostics,
    })
}

pub(crate) fn compile_repl_expr_with_types<T>(
    t: &mut T,
    mut prog: Program,
    expr: Spanned<Expr>,
    input_frame: Vec<String>,
    entry_name: String,
    sm: SourceMap,
    tel: &dyn crate::telemetry::Telemetry,
) -> Result<ReplEntryOk, FrontendErr>
where
    T: Types<Ty = crate::types::Ty> + ClosureTypes + LiteralTypes + RenderTypes,
{
    let output_frame = crate::ir_lower::repl_output_frame_names(&input_frame, &expr);
    let entry_item = std::rc::Rc::new(crate::ast::Item::Fn(repl_entry_fn_def(
        &entry_name,
        &input_frame,
        &output_frame,
        expr,
    )));
    prog.items.push(entry_item.clone());
    let frontend = compile_program_with_types(t, prog, sm, tel)?;
    let Some(entry_fn) = frontend.module.fn_by_name(&entry_name).map(|f| f.id) else {
        return Err(fail(
            frontend.sm,
            Diagnostic::error(
                crate::diag::codes::LOWER_UNSUPPORTED,
                format!("repl entry `{}` not lowered", entry_name),
                crate::diag::Span::DUMMY,
            ),
        ));
    };
    Ok(ReplEntryOk {
        frontend,
        entry_fn,
        input_frame,
        output_frame,
        entry_item,
    })
}

fn repl_entry_fn_def(
    entry_name: &str,
    input_frame: &[String],
    output_frame: &[String],
    expr: Spanned<Expr>,
) -> FnDef {
    let display_name = "__repl_display".to_string();
    let display_expr = Spanned::new(Expr::Var(display_name.clone()), expr.span);
    let bind_display = Spanned::new(
        Expr::Match(
            Spanned::new(Pattern::Var(display_name.clone()), expr.span),
            Box::new(expr),
        ),
        display_expr.span,
    );
    let mut returns = vec![display_expr];
    returns.extend(
        output_frame
            .iter()
            .map(|name| Spanned::dummy(Expr::Var(name.clone()))),
    );
    let body = Spanned::new(
        Expr::Block(vec![bind_display, Spanned::dummy(Expr::Tuple(returns))]),
        crate::diag::Span::DUMMY,
    );
    let params = input_frame
        .iter()
        .map(|name| Spanned::dummy(Pattern::Var(name.clone())))
        .collect::<Vec<_>>();
    FnDef {
        name: entry_name.to_string(),
        name_span: crate::diag::Span::DUMMY,
        clauses: vec![FnClause {
            param_annotations: vec![None; params.len()],
            params,
            guard: None,
            body,
            span: crate::diag::Span::DUMMY,
        }],
        is_macro: false,
        variadic: false,
        extern_abi: None,
        extern_params: vec![],
        extern_ret_tokens: crate::ast::TypeExprBody(vec![]),
        attrs: vec![],
        span: crate::diag::Span::DUMMY,
    }
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
                ["fz", "planner", "planned"] => {
                    if let Some(module_plan) = ev
                        .metadata
                        .get("module_plan")
                        .and_then(|v| v.downcast_ref::<crate::ir_planner::ModulePlan>())
                    {
                        self.0.borrow_mut().typed_specs = module_plan.specs.len();
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
        assert_eq!(facts.typed_specs, out.module_plan.specs.len());
        assert_eq!(facts.checked_diagnostics, out.diagnostics.len());
    }

    fn parse_with_source_map(src: &str, source_name: &str) -> (Program, SourceMap) {
        let mut sm = SourceMap::new();
        let file_id = sm.add_file(source_name.to_string(), src.to_string());
        let toks = Lexer::with_file(src, file_id).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        (prog, sm)
    }

    fn parse_expr_with_source_map(src: &str, source_name: &str) -> (Spanned<Expr>, SourceMap) {
        let mut sm = SourceMap::new();
        let file_id = sm.add_file(source_name.to_string(), src.to_string());
        let toks = Lexer::with_file(src, file_id).tokenize().expect("lex");
        let expr = Parser::new(toks).parse_expr_eof().expect("parse expr");
        (expr, sm)
    }

    #[test]
    fn compile_program_with_types_compiles_parsed_program() {
        let src = "fn id(x), do: x\nfn main(), do: id(41)\n";
        let (prog, sm) = parse_with_source_map(src, "parsed.fz");
        let mut t = crate::types::ConcreteTypes;
        let out =
            match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::NullTelemetry) {
                Ok(out) => out,
                Err(_) => panic!("compile parsed program"),
            };
        assert!(out.module.fn_by_name("main").is_some());
    }

    #[test]
    fn compile_program_with_types_matches_source_pipeline() {
        let src = "fn add(a, b), do: a + b\nfn main(), do: add(20, 22)\n";
        let source_out = match compile_source(src.to_string(), "source.fz".to_string()) {
            Ok(out) => out,
            Err(_) => panic!("compile source program"),
        };
        let (prog, sm) = parse_with_source_map(src, "source.fz");
        let mut t = crate::types::ConcreteTypes;
        let parsed_out =
            match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::NullTelemetry) {
                Ok(out) => out,
                Err(_) => panic!("compile parsed program"),
            };
        assert_eq!(parsed_out.module.fns.len(), source_out.module.fns.len());
        assert!(parsed_out.module.fn_by_name("main").is_some());
        assert_eq!(parsed_out.diagnostics.len(), source_out.diagnostics.len());
    }

    #[test]
    fn compile_program_with_types_preserves_diagnostics() {
        let src = "fn main(), do: missing + 1\n";
        let (prog, sm) = parse_with_source_map(src, "bad-parsed.fz");
        let mut t = crate::types::ConcreteTypes;
        let err =
            match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::NullTelemetry) {
                Ok(_) => panic!("unbound name should fail lowering"),
                Err(err) => err,
            };
        assert!(
            err.diagnostics
                .as_slice()
                .iter()
                .any(|d| d.severity == crate::diag::diagnostic::Severity::Error)
        );
    }

    #[test]
    fn compile_source_accepts_loaded_interfaces_without_provider_body() {
        let mut t = crate::types::ConcreteTypes;
        let math = crate::module_identity::ModuleName::from_segments(vec!["Math".to_string()]);
        let mut interfaces = InterfaceTable::new();
        interfaces.insert(
            math.clone(),
            crate::module_interface::ModuleInterface {
                name: math,
                abi_version: crate::module_interface::FZ_INTERFACE_ABI_VERSION,
                imports: Vec::new(),
                exports: vec![crate::module_interface::InterfaceFn {
                    name: "add".to_string(),
                    arity: 2,
                    spec: Some(crate::module_interface::InterfaceSpec {
                        params: vec!["Ident(\"integer\")".to_string(); 2],
                        result: "Ident(\"integer\")".to_string(),
                    }),
                    name_span: crate::diag::Span::DUMMY,
                }],
                types: Vec::new(),
                docs: None,
                fingerprint_inputs: Vec::new(),
            },
        );
        let src = r#"
defmodule User do
  import Math, only: [add: 2]
  @spec run(integer, integer) :: integer
  fn run(x, y), do: x + y
end
"#;

        let out = match compile_source_with_interface_table(
            &mut t,
            src.to_string(),
            "consumer.fz".to_string(),
            interfaces,
            &crate::telemetry::NullTelemetry,
        ) {
            Ok(out) => out,
            Err(_) => panic!("frontend ok"),
        };

        assert!(out.module.fn_by_name("User.run").is_some());
        assert!(out.module.fn_by_name("Math.add").is_none());
    }

    #[test]
    fn compile_program_with_types_preserves_macro_expansion() {
        let src = r#"
defmacro inc(x) do
  quote do: unquote(x) + 1
end

fn main(), do: inc(41)
"#;
        let source_out = match compile_source(src.to_string(), "macro-source.fz".to_string()) {
            Ok(out) => out,
            Err(_) => panic!("compile source program"),
        };
        let (prog, sm) = parse_with_source_map(src, "macro-source.fz");
        let mut t = crate::types::ConcreteTypes;
        let parsed_out =
            match compile_program_with_types(&mut t, prog, sm, &crate::telemetry::NullTelemetry) {
                Ok(out) => out,
                Err(_) => panic!("compile parsed program"),
            };
        assert_eq!(parsed_out.module.fns.len(), source_out.module.fns.len());
        assert!(parsed_out.module.fn_by_name("main").is_some());
    }

    #[test]
    fn compile_repl_expr_returns_entry_and_frame_layout_for_plain_expression() {
        let (expr, sm) = parse_expr_with_source_map("x + 1", "repl.fz");
        let mut t = crate::types::ConcreteTypes;
        let out = match compile_repl_expr_with_types(
            &mut t,
            Program::default(),
            expr,
            vec!["x".to_string()],
            "__repl_eval_0".to_string(),
            sm,
            &crate::telemetry::NullTelemetry,
        ) {
            Ok(out) => out,
            Err(_) => panic!("compile repl expression"),
        };
        let entry = out
            .frontend
            .module
            .fn_by_name("__repl_eval_0")
            .expect("repl entry");
        assert_eq!(out.entry_fn, entry.id);
        assert_eq!(out.input_frame, vec!["x"]);
        assert_eq!(out.output_frame, vec!["x"]);
        assert_eq!(entry.category, crate::fz_ir::FnCategory::ReplEntry);
    }

    #[test]
    fn compile_repl_expr_extends_frame_for_simple_and_destructuring_bindings() {
        let cases = [
            ("x = 41", Vec::<String>::new(), vec!["x".to_string()]),
            (
                "{a, b} = {1, 2}",
                vec!["z".to_string()],
                vec!["z".to_string(), "a".to_string(), "b".to_string()],
            ),
            ("x = 42", vec!["x".to_string()], vec!["x".to_string()]),
        ];
        for (src, input, expected_output) in cases {
            let (expr, sm) = parse_expr_with_source_map(src, "repl.fz");
            let mut t = crate::types::ConcreteTypes;
            let out = match compile_repl_expr_with_types(
                &mut t,
                Program::default(),
                expr,
                input.clone(),
                "__repl_eval_0".to_string(),
                sm,
                &crate::telemetry::NullTelemetry,
            ) {
                Ok(out) => out,
                Err(_) => panic!("compile repl expression `{}`", src),
            };
            assert_eq!(out.input_frame, input);
            assert_eq!(out.output_frame, expected_output);
        }
    }

    #[test]
    fn compile_repl_expr_lowers_match_failure_path() {
        let (expr, sm) = parse_expr_with_source_map("{:ok, y} = {:error, 2}", "repl.fz");
        let mut t = crate::types::ConcreteTypes;
        let out = match compile_repl_expr_with_types(
            &mut t,
            Program::default(),
            expr,
            vec![],
            "__repl_eval_0".to_string(),
            sm,
            &crate::telemetry::NullTelemetry,
        ) {
            Ok(out) => out,
            Err(_) => panic!("compile repl expression"),
        };
        let entry = out
            .frontend
            .module
            .fn_by_name("__repl_eval_0")
            .expect("repl entry");
        let has_halt = entry
            .blocks
            .iter()
            .any(|block| matches!(block.terminator, crate::fz_ir::Term::Halt(_)));
        assert!(has_halt, "match failure path should lower to Halt");
        assert_eq!(out.output_frame, vec!["y"]);
    }
}
