//! fz-ul4.15 — read-eval-print loop.
//!
//! Each line is parsed first as a fn definition (top-level `fn`/`defmacro`),
//! falling back to an expression. Expressions lower to IR evaluator entries
//! that run on a persistent `ReplRuntime`, so `x = 42` on one line and
//! `x + 1` on the next both work through the same runtime path as spawned
//! processes and receives.
//!
//! Interactive editing is owned by `ReplLineEditor`. `ReplComposer` classifies
//! submitted editor buffers as commands, diagnostics, or complete source chunks.
//!
//! `:quit` / `:q` / Ctrl-D exits.
//!
//! fz-i67.1 / fz-elu.9 — `run_script` drives whole-file scripts through
//! `ReplSession`, lowering to IR and executing `main/0` on `IrInterpRuntime`.
//! No banner/prompts are emitted and expression results are not echoed. Only
//! program-side `dbg()` reaches stdout, so a fixture's REPL-leg output is
//! exact-comparable to the other legs' golden.

use crate::ast::{Expr, FnDef, Item, Program, Spanned};
use crate::compiler::source::SourceMap;
use crate::compiler::{Compiler, World as CompilerWorld};
use crate::diag::diagnostic::Severity;
use crate::diag::style::ColorMode;
use crate::diag::{Diagnostic, render_one_to_string};
use crate::exec::eval::{CompileTimeEvaluator, format_spec_text};
use crate::exec::value::{Closure, Value};
use crate::frontend::macros::expand_with;
use crate::frontend::resolve::flatten_modules;
use crate::frontend::{FrontendOk, compile_repl_expr_with_types};
use crate::fz_ir::{FnId, Module};
use crate::ir_interp::{AnyValue, IrInterpRuntime};
use crate::ir_planner::ModulePlan;
use crate::modules::pipeline::{CompileMode, PipelineError};
use crate::notify_fixture_execution_start;
use crate::parser::Parser;
use crate::parser::lexer::{Lexer, Tok};
use crate::telemetry::{ConfiguredTelemetry, DiagRenderer, Telemetry};
use crate::types::{DefaultTypes, RenderTypes, Ty, Types};
use rustyline::completion::Completer;
use rustyline::error::ReadlineError;
use rustyline::highlight::Highlighter;
use rustyline::hint::Hinter;
use rustyline::history::DefaultHistory;
use rustyline::validate::{ValidationContext, ValidationResult, Validator};
use rustyline::{Editor, Helper};
use std::cell::RefCell;
use std::collections::BTreeMap;
use std::io::{self, Write};
use std::path::Path;
use std::rc::Rc;

pub fn run() -> io::Result<()> {
    let tel = Rc::new(ConfiguredTelemetry::new());
    let mut session = ReplSession::new();
    let mut composer = ReplComposer::new(tel.clone());
    let mut editor = RustylineReplLineEditor::new(tel.clone())?;

    println!("fz repl — :q to quit");
    loop {
        let line = match editor.read_line("fz> ")? {
            ReplLine::Line(line) => line,
            ReplLine::Eof => {
                println!();
                break;
            }
            ReplLine::Interrupted => continue,
        };

        match composer.submit_buffer(&line) {
            ReplComposerEvent::Quit => break,
            ReplComposerEvent::Empty => {}
            ReplComposerEvent::DocQuery(q) => println!("{}", session.lookup_doc(&q)),
            ReplComposerEvent::Diagnostic(msg) => eprintln!("{}", msg),
            ReplComposerEvent::Complete(src) => {
                editor.add_history_entry(&src)?;
                match session.eval_chunk(&src, tel.as_ref()) {
                    ReplChunkOutcome::Ok(None) => {}
                    ReplChunkOutcome::Ok(Some(value)) => {
                        if !value.is_nil() {
                            println!("{}", session.render_value(value));
                        }
                    }
                    ReplChunkOutcome::Err(msg) => eprintln!("{}", msg),
                }
            }
        }
    }
    Ok(())
}

#[derive(Debug, Eq, PartialEq)]
enum ReplLine {
    Line(String),
    Eof,
    Interrupted,
}

trait ReplLineEditor {
    fn read_line(&mut self, prompt: &str) -> io::Result<ReplLine>;
    fn add_history_entry(&mut self, line: &str) -> io::Result<()>;
}

struct RustylineReplLineEditor {
    editor: Editor<ReplEditorHelper, DefaultHistory>,
}

impl RustylineReplLineEditor {
    fn new(tel: Rc<dyn Telemetry>) -> io::Result<Self> {
        let mut editor = Editor::<ReplEditorHelper, DefaultHistory>::new().map_err(rustyline_to_io_error)?;
        editor.set_helper(Some(ReplEditorHelper { tel }));
        Ok(Self { editor })
    }
}

impl ReplLineEditor for RustylineReplLineEditor {
    fn read_line(&mut self, prompt: &str) -> io::Result<ReplLine> {
        match self.editor.readline(prompt) {
            Ok(line) => Ok(ReplLine::Line(line)),
            Err(ReadlineError::Eof) => Ok(ReplLine::Eof),
            Err(ReadlineError::Interrupted) => Ok(ReplLine::Interrupted),
            Err(err) => Err(rustyline_to_io_error(err)),
        }
    }

    fn add_history_entry(&mut self, line: &str) -> io::Result<()> {
        self.editor
            .add_history_entry(line)
            .map(|_| ())
            .map_err(rustyline_to_io_error)
    }
}

fn rustyline_to_io_error(err: ReadlineError) -> io::Error {
    io::Error::other(err)
}

struct ReplEditorHelper {
    tel: Rc<dyn Telemetry>,
}

impl ReplEditorHelper {
    fn validation_result_for(input: &str, tel: &dyn Telemetry) -> ValidationResult {
        if ReplComposer::is_immediate_input(input) {
            return ValidationResult::Valid(None);
        }
        match ReplWorld::parse_source_chunk(input, tel) {
            Err(ReplWorldParse::Incomplete) => ValidationResult::Incomplete,
            Ok(_) | Err(ReplWorldParse::Err(_)) => ValidationResult::Valid(None),
        }
    }
}

impl Completer for ReplEditorHelper {
    type Candidate = String;
}

impl Hinter for ReplEditorHelper {
    type Hint = String;
}

impl Highlighter for ReplEditorHelper {}

impl Validator for ReplEditorHelper {
    fn validate(&self, ctx: &mut ValidationContext<'_>) -> rustyline::Result<ValidationResult> {
        Ok(Self::validation_result_for(ctx.input(), self.tel.as_ref()))
    }
}

impl Helper for ReplEditorHelper {}

/// Compile a file's contents, then call `main/0` through `ReplRuntime` if
/// defined. Only program-side `dbg()` writes to stdout; diagnostics use the
/// caller's telemetry bus.
pub fn run_script(path: &Path, tel: &dyn Telemetry) -> io::Result<()> {
    let src = std::fs::read_to_string(path)?;
    let source_name = path.display().to_string();
    let (diagnostics, handler_id) = attach_repl_diagnostic_renderer(tel);
    let result = ReplSession::new().run_script_str(&src, source_name, tel, &diagnostics);
    assert!(
        tel.detach(handler_id),
        "temporary repl diagnostic renderer should detach"
    );
    result
}

/// Underlying driver shared by `run_script` and tests. Returns Err on
/// parse/eval errors so callers can decide the exit code; on success the
/// only output is whatever the program's own `dbg()` calls produced.
#[cfg(test)]
pub fn run_script_str(src: &str) -> io::Result<()> {
    let (tel, diagnostics) = repl_diagnostic_telemetry();
    ReplSession::new().run_script_str(src, "<repl-script>".to_string(), &tel, &diagnostics)
}

pub(crate) struct ReplSession {
    world: ReplWorld,
    frame: ReplFrame,
    runtime: Option<ReplRuntime>,
    next_eval: usize,
}

#[derive(Debug, Eq, PartialEq)]
enum ReplComposerEvent {
    Quit,
    DocQuery(String),
    Empty,
    Complete(String),
    Diagnostic(String),
}

struct ReplComposer {
    tel: Rc<dyn Telemetry>,
}

impl ReplComposer {
    fn new(tel: Rc<dyn Telemetry>) -> Self {
        Self { tel }
    }

    fn submit_buffer(&mut self, buffer: &str) -> ReplComposerEvent {
        let trimmed = buffer.trim();
        if Self::is_quit(trimmed) {
            return ReplComposerEvent::Quit;
        }
        if trimmed.is_empty() {
            return ReplComposerEvent::Empty;
        }
        if let Some(query) = trimmed.strip_prefix('?') {
            return ReplComposerEvent::DocQuery(query.trim().to_string());
        }

        match ReplWorld::parse_source_chunk(buffer, self.tel.as_ref()) {
            Ok(_) => ReplComposerEvent::Complete(buffer.to_string()),
            Err(ReplWorldParse::Incomplete) => ReplComposerEvent::Diagnostic("incomplete repl input".to_string()),
            Err(ReplWorldParse::Err(msg)) => ReplComposerEvent::Diagnostic(msg),
        }
    }

    fn is_immediate_input(input: &str) -> bool {
        let trimmed = input.trim();
        trimmed.is_empty() || Self::is_quit(trimmed) || trimmed.starts_with('?')
    }

    fn is_quit(trimmed: &str) -> bool {
        trimmed == ":q" || trimmed == ":quit"
    }
}

impl ReplSession {
    pub(crate) fn new() -> Self {
        Self {
            world: ReplWorld::new(),
            frame: ReplFrame::new(),
            runtime: None,
            next_eval: 0,
        }
    }

    fn run_script_str(
        &mut self,
        src: &str,
        source_name: String,
        tel: &dyn Telemetry,
        diagnostics: &Rc<RefCell<Vec<u8>>>,
    ) -> io::Result<()> {
        self.world
            .compiler
            .prepare_execution_graph_from_source(
                &mut self.world.compiler_world,
                src.to_string(),
                source_name,
                tel,
                CompileMode::Normal,
            )
            .map_err(|err| pipeline_error_to_io_error(err, diagnostics))?;

        let Some(main) = self.world.compiler_world.linked_module().fn_by_name("main") else {
            return Ok(());
        };
        if !main.block(main.entry).params.is_empty() {
            return Ok(());
        }

        notify_fixture_execution_start();
        let module = self.world.compiler_world.linked_module().clone();
        let module_plan = self.world.compiler_world.linked_module_plan().clone();
        let main_id = main.id;
        ReplRuntime::run_script_main(self.world.types(), &module, module_plan, main_id, tel)
    }

    pub(crate) fn eval_chunk(&mut self, src: &str, tel: &dyn Telemetry) -> ReplChunkOutcome {
        match self.world.parse_chunk(src, tel) {
            Ok(ReplWorldChunk::Items(prog)) => match self.world.apply_items(src, prog, tel) {
                Ok(_module) => ReplChunkOutcome::Ok(None),
                Err(e) => ReplChunkOutcome::Err(e),
            },
            Ok(ReplWorldChunk::Expr { expr, sm }) => self.eval_expr_chunk(src, expr, sm, tel),
            Err(ReplWorldParse::Incomplete) => {
                ReplChunkOutcome::Err("incomplete repl input must be composed before execution".to_string())
            }
            Err(ReplWorldParse::Err(msg)) => ReplChunkOutcome::Err(msg),
        }
    }

    fn eval_expr_chunk(
        &mut self,
        _src: &str,
        expr: Spanned<Expr>,
        sm: SourceMap,
        tel: &dyn Telemetry,
    ) -> ReplChunkOutcome {
        let eval_name = format!("__repl_eval_{}", self.next_eval);
        let compiled = match self
            .world
            .compile_repl_expr(expr, self.frame.names(), eval_name, sm, tel)
        {
            Ok(compiled) => compiled,
            Err(e) => return ReplChunkOutcome::Err(e.to_string()),
        };
        let runtime = self.runtime.get_or_insert_with(|| ReplRuntime::new(&compiled.module));
        let args = match self.frame.values_for(&compiled.input_frame) {
            Ok(args) => args,
            Err(e) => return ReplChunkOutcome::Err(e),
        };
        let value = match runtime.eval_entry(
            self.world.types(),
            &compiled.module,
            compiled.module_plan,
            compiled.fn_id,
            args,
            tel,
        ) {
            Ok(value) => value,
            Err(e) => return ReplChunkOutcome::Err(e),
        };
        let fields = match runtime.read_tuple_fields(value, compiled.output_frame.len() + 1) {
            Ok(fields) => fields,
            Err(e) => {
                let rendered = runtime.render_value(value).unwrap_or(e);
                return ReplChunkOutcome::Err(format!("repl expression did not return frame tuple: {}", rendered));
            }
        };
        let Some((display, frame_values)) = fields.split_first() else {
            return ReplChunkOutcome::Err("repl expression returned empty frame tuple".to_string());
        };
        if let Err(e) = self.frame.replace(compiled.output_frame, frame_values) {
            return ReplChunkOutcome::Err(e);
        }
        self.world.commit_repl_entry(compiled.entry_program);
        self.next_eval += 1;
        ReplChunkOutcome::Ok(Some(*display))
    }

    fn lookup_doc(&self, name: &str) -> String {
        self.world.lookup_doc(name)
    }

    fn render_value(&self, value: AnyValue) -> String {
        self.runtime
            .as_ref()
            .and_then(|runtime| runtime.render_value(value).ok())
            .unwrap_or_else(|| value.render(std::ptr::null_mut()))
    }
}

struct ReplRuntime {
    interp: IrInterpRuntime,
    evaluator_pid: u32,
    current_module: Module,
}

impl ReplRuntime {
    fn new(module: &Module) -> Self {
        Self {
            interp: IrInterpRuntime::fresh_with_root(module),
            evaluator_pid: 1,
            current_module: module.clone(),
        }
    }

    fn run_script_main(
        t: &mut DefaultTypes,
        module: &Module,
        module_plan: ModulePlan,
        main_id: FnId,
        tel: &dyn Telemetry,
    ) -> io::Result<()> {
        let mut runtime = Self::new(module);
        let completions = runtime
            .enqueue_and_drive(t, module, module_plan, main_id, vec![], /*keepalive=*/ false, tel)
            .map_err(io::Error::other)?;
        if completions.iter().any(|(pid, _)| *pid == runtime.evaluator_pid) {
            Ok(())
        } else {
            Err(io::Error::other("script main/0 blocked with idle runtime"))
        }
    }

    fn eval_entry(
        &mut self,
        t: &mut DefaultTypes,
        module: &Module,
        module_plan: ModulePlan,
        fn_id: FnId,
        args: Vec<AnyValue>,
        tel: &dyn Telemetry,
    ) -> Result<AnyValue, String> {
        let completions = self.enqueue_and_drive(t, module, module_plan, fn_id, args, /*keepalive=*/ true, tel)?;
        completions
            .into_iter()
            .rev()
            .find_map(|(pid, value)| (pid == self.evaluator_pid).then_some(value))
            .ok_or_else(|| "repl expression blocked".to_string())
    }

    fn enqueue_and_drive(
        &mut self,
        t: &mut DefaultTypes,
        module: &Module,
        module_plan: ModulePlan,
        fn_id: FnId,
        args: Vec<AnyValue>,
        keepalive: bool,
        tel: &dyn Telemetry,
    ) -> Result<Vec<(u32, AnyValue)>, String> {
        self.current_module = module.clone();
        self.interp
            .enqueue_entry_with_plan(t, module, module_plan, self.evaluator_pid, fn_id, args)?;
        let keepalive_pid = keepalive.then_some(self.evaluator_pid);
        self.interp.drive_until_idle(t, tel, keepalive_pid)
    }

    fn read_tuple_fields(&self, value: AnyValue, arity: usize) -> Result<Vec<AnyValue>, String> {
        self.interp.read_tuple_fields(self.evaluator_pid, value, arity)
    }

    fn render_value(&self, value: AnyValue) -> Result<String, String> {
        self.interp.render_value(self.evaluator_pid, value)
    }
}

struct ReplFrame {
    values: BTreeMap<String, AnyValue>,
}

impl ReplFrame {
    fn new() -> Self {
        Self {
            values: BTreeMap::new(),
        }
    }

    fn names(&self) -> Vec<String> {
        self.values.keys().cloned().collect()
    }

    fn values_for(&self, names: &[String]) -> Result<Vec<AnyValue>, String> {
        names
            .iter()
            .map(|name| {
                self.values
                    .get(name)
                    .copied()
                    .ok_or_else(|| format!("repl frame missing input `{}`", name))
            })
            .collect()
    }

    fn replace(&mut self, names: Vec<String>, values: &[AnyValue]) -> Result<(), String> {
        if names.len() != values.len() {
            return Err(format!(
                "repl frame expected {} values, got {}",
                names.len(),
                values.len()
            ));
        }
        self.values = names.into_iter().zip(values.iter().copied()).collect();
        Ok(())
    }
}

struct ReplWorld {
    compiler: Compiler,
    compiler_world: CompilerWorld,
    compile_time: CompileTimeEvaluator,
    item_chunks: Vec<ReplItemChunk>,
    eval_chunks: Vec<Program>,
}

struct ReplItemChunk {
    prog: Program,
    fns: Vec<(String, usize)>,
}

struct ReplCompiledEntry {
    module: Module,
    module_plan: ModulePlan,
    fn_id: FnId,
    input_frame: Vec<String>,
    output_frame: Vec<String>,
    entry_program: Program,
}

enum ReplWorldChunk {
    Items(Program),
    Expr { expr: Spanned<Expr>, sm: SourceMap },
}

#[derive(Debug)]
enum ReplWorldParse {
    Incomplete,
    Err(String),
}

impl ReplWorld {
    fn new() -> Self {
        Self {
            compiler: Compiler::new(),
            compiler_world: CompilerWorld::new(),
            compile_time: CompileTimeEvaluator::new(),
            item_chunks: Vec::new(),
            eval_chunks: Vec::new(),
        }
    }

    fn types(&mut self) -> &mut DefaultTypes {
        self.compiler_world.types()
    }

    fn parse_chunk(&self, src: &str, tel: &dyn Telemetry) -> Result<ReplWorldChunk, ReplWorldParse> {
        Self::parse_source_chunk(src, tel)
    }

    fn parse_source_chunk(src: &str, tel: &dyn Telemetry) -> Result<ReplWorldChunk, ReplWorldParse> {
        let mut sm = SourceMap::new();
        let code_id = sm.add_code(Some("<repl-chunk>".to_string()), src.to_string());
        let toks = Lexer::with_code_id_and_source_name(src, code_id, "<repl-chunk>")
            .tokenize(tel)
            .map_err(|e| ReplWorldParse::Err(format!("{}", e)))?;
        let starts_with_item = toks
            .iter()
            .map(|t| &t.tok)
            .find(|t| !matches!(t, Tok::Newline | Tok::Semi))
            .map(|t| {
                matches!(
                    t,
                    Tok::At | Tok::Fn | Tok::Extern | Tok::Defmacro | Tok::Defmodule | Tok::Alias | Tok::Import
                )
            })
            .unwrap_or(false);

        if starts_with_item {
            let mut p = Parser::new(toks);
            return match p.parse_program(tel) {
                Ok(prog) => Ok(ReplWorldChunk::Items(prog)),
                Err(e) if e.is_incomplete() => Err(ReplWorldParse::Incomplete),
                Err(e) => Err(ReplWorldParse::Err(format!("{}", e))),
            };
        }

        let mut p = Parser::new(toks);
        match p.parse_expr_eof() {
            Ok(expr) => Ok(ReplWorldChunk::Expr { expr, sm }),
            Err(e) if e.is_incomplete() => Err(ReplWorldParse::Incomplete),
            Err(e) => Err(ReplWorldParse::Err(format!("{}", e))),
        }
    }

    fn apply_items(&mut self, _src: &str, prog: Program, tel: &dyn Telemetry) -> Result<Module, String> {
        let fns = item_fn_shapes(&prog);
        self.load_docs_and_macros(prog.clone(), tel)?;
        self.item_chunks.retain(|existing| {
            !existing.fns.iter().any(|(old_name, old_arity)| {
                fns.iter()
                    .any(|(new_name, new_arity)| old_name == new_name && old_arity != new_arity)
            })
        });
        self.item_chunks.push(ReplItemChunk { prog, fns });
        match self.compile_session_module(tel) {
            Ok(module) => Ok(module),
            Err(e) => Err(e.to_string()),
        }
    }

    fn compile_repl_expr(
        &mut self,
        expr: Spanned<Expr>,
        input_frame: Vec<String>,
        entry_name: String,
        sm: SourceMap,
        tel: &dyn Telemetry,
    ) -> io::Result<ReplCompiledEntry> {
        let prog = self.session_program();
        let out = match compile_repl_expr_with_types(self.types(), prog, expr, input_frame, entry_name.clone(), sm, tel)
        {
            Ok(out) => out,
            Err(err) => {
                return Err(diagnostics_to_io_error(&err.sm, err.diagnostics.as_slice()));
            }
        };
        if out
            .frontend
            .diagnostics
            .as_slice()
            .iter()
            .any(|d| d.severity == Severity::Error)
        {
            return Err(diagnostics_to_io_error(
                &out.frontend.sm,
                out.frontend.diagnostics.as_slice(),
            ));
        }
        prepare_repl_frontend(&mut self.compiler, &mut self.compiler_world, out.frontend, tel)?;
        let Some(entry_fn) = self
            .compiler_world
            .linked_module()
            .fn_by_name(&entry_name)
            .map(|f| f.id)
        else {
            return Err(io::Error::other(format!("repl entry `{}` not lowered", entry_name)));
        };
        let mut entry_program = Program::default();
        entry_program.items.push(out.entry_item);
        Ok(ReplCompiledEntry {
            module: self.compiler_world.linked_module().clone(),
            module_plan: self.compiler_world.linked_module_plan().clone(),
            fn_id: entry_fn,
            input_frame: out.input_frame,
            output_frame: out.output_frame,
            entry_program,
        })
    }

    fn commit_repl_entry(&mut self, entry_program: Program) {
        self.eval_chunks.push(entry_program);
    }

    fn lookup_doc(&self, name: &str) -> String {
        lookup_doc(&self.compile_time, name)
    }

    fn compile_session_module(&mut self, tel: &dyn Telemetry) -> io::Result<Module> {
        let prog = self.session_program();
        compile_parsed_program_module(&mut self.compiler, &mut self.compiler_world, prog, tel)
    }

    fn session_program(&self) -> Program {
        let mut prog = Program::default();
        for item in &self.item_chunks {
            append_items_grouping_fn_clauses(&mut prog, item.prog.items.iter().cloned());
        }
        for eval in &self.eval_chunks {
            prog.items.extend(eval.items.iter().cloned());
        }
        prog
    }

    fn load_docs_and_macros(&mut self, prog: Program, tel: &dyn Telemetry) -> Result<(), String> {
        let mut prog = flatten_modules(self.types(), prog, tel).map_err(|e| format!("module: {}", e))?;
        for (path, doc) in &prog.module_docs {
            self.compile_time
                .module_docs
                .borrow_mut()
                .insert(path.clone(), doc.clone());
        }
        let compile_time = &self.compile_time;
        let compiler_world = &mut self.compiler_world;
        if let Err(e) = load_items_filtered(compiler_world.types(), compile_time, &prog, /*macros=*/ true) {
            return Err(format!("load macros: {}", e));
        }
        let live = compile_time.macro_names.borrow().clone();
        if let Err(e) = expand_with(&mut prog, compile_time, &live) {
            return Err(format!("macro: {}", e));
        }
        if let Err(e) = load_items_filtered(compiler_world.types(), compile_time, &prog, /*macros=*/ false) {
            return Err(format!("load fns: {}", e));
        }
        Ok(())
    }
}

pub(crate) enum ReplChunkOutcome {
    Ok(Option<AnyValue>),
    Err(String),
}

fn compile_parsed_program_module(
    compiler: &mut Compiler,
    world: &mut CompilerWorld,
    prog: Program,
    tel: &dyn Telemetry,
) -> io::Result<Module> {
    let frontend = match compiler.compile_program(world, prog, SourceMap::new(), tel) {
        Ok(ok) => ok,
        Err(err) => {
            return Err(diagnostics_to_io_error(&err.sm, err.diagnostics.as_slice()));
        }
    };
    if frontend
        .diagnostics
        .as_slice()
        .iter()
        .any(|d| d.severity == Severity::Error)
    {
        return Err(diagnostics_to_io_error(&frontend.sm, frontend.diagnostics.as_slice()));
    }
    prepare_repl_frontend(compiler, world, frontend, tel)?;
    Ok(world.linked_module().clone())
}

fn prepare_repl_frontend(
    compiler: &mut Compiler,
    world: &mut CompilerWorld,
    frontend: FrontendOk,
    tel: &dyn Telemetry,
) -> io::Result<()> {
    let diagnostics = Rc::new(RefCell::new(Vec::new()));
    compiler
        .prepare_execution_graph_from_frontend(world, frontend, tel, CompileMode::Normal)
        .map_err(|err| pipeline_error_to_io_error(err, &diagnostics))
}

#[cfg(test)]
fn repl_diagnostic_telemetry() -> (ConfiguredTelemetry, Rc<RefCell<Vec<u8>>>) {
    let tel = ConfiguredTelemetry::new();
    let (diagnostics, _handler_id) = attach_repl_diagnostic_renderer(&tel);
    (tel, diagnostics)
}

fn attach_repl_diagnostic_renderer(tel: &dyn Telemetry) -> (Rc<RefCell<Vec<u8>>>, crate::telemetry::HandlerId) {
    let diagnostics = Rc::new(RefCell::new(Vec::new()));
    let handler_id = tel.attach(
        &["fz", "diag"],
        Box::new(DiagRenderer::new_to_writer(
            Rc::new(RefCell::new(SourceMap::new())),
            ReplDiagnosticWriter(diagnostics.clone()),
            ColorMode::Never,
        )),
    );
    (diagnostics, handler_id)
}

struct ReplDiagnosticWriter(Rc<RefCell<Vec<u8>>>);

impl Write for ReplDiagnosticWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.0.borrow_mut().extend_from_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

fn item_fn_shapes(prog: &Program) -> Vec<(String, usize)> {
    prog.items
        .iter()
        .filter_map(|item| match &**item {
            Item::Fn(def) => Some((
                def.name.clone(),
                def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0),
            )),
            _ => None,
        })
        .collect()
}

fn append_items_grouping_fn_clauses<I>(prog: &mut Program, items: I)
where
    I: IntoIterator<Item = Rc<Item>>,
{
    for item in items {
        let Item::Fn(new_def) = item.as_ref() else {
            prog.items.push(item);
            continue;
        };
        let new_arity = fn_def_arity(new_def);
        let existing = prog.items.iter_mut().find_map(|existing| {
            let Item::Fn(existing_def) = existing.as_ref() else {
                return None;
            };
            (existing_def.name == new_def.name
                && fn_def_arity(existing_def) == new_arity
                && existing_def.is_macro == new_def.is_macro
                && existing_def.extern_abi == new_def.extern_abi)
                .then_some(existing)
        });
        let Some(existing) = existing else {
            prog.items.push(item);
            continue;
        };
        let Item::Fn(existing_def) = existing.as_ref() else {
            unreachable!("existing fn item changed during grouping");
        };
        let mut merged = existing_def.clone();
        merged.span = merged.span.merge(new_def.span);
        merged.clauses.extend(new_def.clauses.iter().cloned());
        if merged.attrs.is_empty() {
            merged.attrs = new_def.attrs.clone();
        }
        *existing = Rc::new(Item::Fn(merged));
    }
}

fn fn_def_arity(def: &FnDef) -> usize {
    def.clauses.first().map(|clause| clause.params.len()).unwrap_or(0)
}

fn diagnostics_to_io_error(sm: &SourceMap, diags: &[Diagnostic]) -> io::Error {
    let rendered = diags
        .iter()
        .map(|d| render_one_to_string(sm, d))
        .collect::<Vec<_>>()
        .join("");
    io::Error::other(rendered)
}

fn pipeline_error_to_io_error(err: PipelineError, diagnostics: &Rc<RefCell<Vec<u8>>>) -> io::Error {
    let rendered = diagnostics.borrow();
    if !rendered.is_empty() {
        return io::Error::other(String::from_utf8_lossy(&rendered).into_owned());
    }
    drop(rendered);
    match err {
        PipelineError::Link(err) => io::Error::other(err.to_string()),
        err => io::Error::other(err.to_string()),
    }
}

/// `which == true` loads only macros; `which == false` loads only non-macros.
/// Splitting the two phases lets the REPL register macros before running
/// expansion on fn bodies that may call them.
fn load_items_filtered<T>(
    t: &mut T,
    interp: &CompileTimeEvaluator,
    prog: &Program,
    macros_only: bool,
) -> Result<(), String>
where
    T: Types<Ty = Ty> + RenderTypes,
{
    for item in &prog.items {
        match &**item {
            Item::Module(_)
            | Item::Struct(_)
            | Item::Protocol(_)
            | Item::ProtocolImpl(_)
            | Item::Alias { .. }
            | Item::Import { .. }
            | Item::MacroCall { .. } => {
                continue;
            } // flattened away upstream
            Item::Fn(def) => {
                if macros_only != def.is_macro {
                    continue;
                }
                if def.is_macro {
                    interp.macro_names.borrow_mut().insert(def.name.clone());
                    interp.macro_def_spans.borrow_mut().insert(def.name.clone(), def.span);
                }
                // If a closure already exists under this name *and* the new
                // clauses match arity, append. Otherwise replace. Matches
                // user expectation: typing several `fn foo(...)` lines in
                // sequence builds up a multi-clause fn.
                let existing = interp.globals.lookup(&def.name);
                let mut clauses = def.clauses.clone();
                let mut doc = def.doc().map(String::from);
                let mut spec_text = format_spec_text(t, def, prog);
                if let Some(Value::Closure(c)) = existing {
                    let same_arity =
                        c.clauses.first().map(|cl| cl.params.len()) == clauses.first().map(|cl| cl.params.len());
                    if same_arity && c.name.as_deref() == Some(def.name.as_str()) {
                        let mut combined = c.clauses.clone();
                        combined.append(&mut clauses);
                        clauses = combined;
                        // Preserve prior doc / spec_text if the new def didn't carry one.
                        if doc.is_none() {
                            doc = c.doc.clone();
                        }
                        if spec_text.is_none() {
                            spec_text = c.spec_text.clone();
                        }
                    }
                }
                let closure = Value::Closure(Rc::new(Closure {
                    name: Some(def.name.clone()),
                    clauses,
                    env: interp.globals.clone(),
                    doc,
                    spec_text,
                }));
                interp.globals.bind(&def.name, closure);
            }
        }
    }
    Ok(())
}

/// Resolve a `?<name>` REPL query against loaded fns and modules. Tries
/// fns first (so `?M.add` finds the closure), then falls back to a
/// moduledoc lookup (so `?M` finds the module).
///
/// fz-ul4.31.6 — renders `@spec` declaration alongside the `@doc` text
/// when both are present.
fn lookup_doc(interp: &CompileTimeEvaluator, name: &str) -> String {
    if name.is_empty() {
        return "usage: ?<fn-or-module-name>".to_string();
    }
    if let Some(Value::Closure(c)) = interp.globals.lookup(name) {
        let mut out = String::new();
        if let Some(s) = &c.spec_text {
            for line in s.lines() {
                if !out.is_empty() {
                    out.push('\n');
                }
                out.push_str("@spec: ");
                out.push_str(line);
            }
        }
        if let Some(d) = &c.doc {
            if !out.is_empty() {
                out.push('\n');
            }
            out.push_str("@doc:  ");
            out.push_str(d);
        }
        if out.is_empty() {
            return format!("{}: no documentation", name);
        }
        return out;
    }
    if let Some(d) = interp.module_docs.borrow().get(name) {
        return d.clone();
    }
    format!("{}: not found", name)
}

#[cfg(test)]
#[path = "repl_test.rs"]
mod repl_test;
