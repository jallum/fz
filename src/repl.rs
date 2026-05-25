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
//! program-side `print()` reaches stdout, so a fixture's REPL-leg output is
//! exact-comparable to the other legs' golden.

use crate::ast::{Item, Program};
use crate::eval::CompileTimeEvaluator;
use crate::lexer::Lexer;
use crate::parser::Parser;
use crate::value::Value;
use std::collections::BTreeMap;
use std::io;
use std::path::Path;

pub fn run() -> io::Result<()> {
    let mut session = ReplSession::new();
    let mut composer = ReplComposer::new();
    let mut editor = RustylineReplLineEditor::new()?;

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
                match session.eval_chunk(&src) {
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
    editor: rustyline::Editor<ReplEditorHelper, rustyline::history::DefaultHistory>,
}

impl RustylineReplLineEditor {
    fn new() -> io::Result<Self> {
        let mut editor =
            rustyline::Editor::<ReplEditorHelper, rustyline::history::DefaultHistory>::new()
                .map_err(rustyline_to_io_error)?;
        editor.set_helper(Some(ReplEditorHelper));
        Ok(Self { editor })
    }
}

impl ReplLineEditor for RustylineReplLineEditor {
    fn read_line(&mut self, prompt: &str) -> io::Result<ReplLine> {
        match self.editor.readline(prompt) {
            Ok(line) => Ok(ReplLine::Line(line)),
            Err(rustyline::error::ReadlineError::Eof) => Ok(ReplLine::Eof),
            Err(rustyline::error::ReadlineError::Interrupted) => Ok(ReplLine::Interrupted),
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

fn rustyline_to_io_error(err: rustyline::error::ReadlineError) -> io::Error {
    io::Error::other(err)
}

struct ReplEditorHelper;

impl ReplEditorHelper {
    fn validation_result_for(input: &str) -> rustyline::validate::ValidationResult {
        use rustyline::validate::ValidationResult;

        if ReplComposer::is_immediate_input(input) {
            return ValidationResult::Valid(None);
        }
        match ReplWorld::parse_source_chunk(input) {
            Err(ReplWorldParse::Incomplete) => ValidationResult::Incomplete,
            Ok(_) | Err(ReplWorldParse::Err(_)) => ValidationResult::Valid(None),
        }
    }
}

impl rustyline::completion::Completer for ReplEditorHelper {
    type Candidate = String;
}

impl rustyline::hint::Hinter for ReplEditorHelper {
    type Hint = String;
}

impl rustyline::highlight::Highlighter for ReplEditorHelper {}

impl rustyline::validate::Validator for ReplEditorHelper {
    fn validate(
        &self,
        ctx: &mut rustyline::validate::ValidationContext<'_>,
    ) -> rustyline::Result<rustyline::validate::ValidationResult> {
        Ok(Self::validation_result_for(ctx.input()))
    }
}

impl rustyline::Helper for ReplEditorHelper {}

/// fz-i67.1 — non-interactive driver: compile a file's contents, then call
/// `main/0` through `ReplRuntime` if defined. Only program-side `print()`
/// writes to stdout.
pub fn run_script(path: &Path) -> io::Result<()> {
    let src = std::fs::read_to_string(path)?;
    let source_name = path.display().to_string();
    ReplSession::new().run_script_str(&src, source_name)
}

/// Underlying driver shared by `run_script` and tests. Returns Err on
/// parse/eval errors so callers can decide the exit code; on success the
/// only output is whatever the program's own `print()` calls produced.
#[cfg(test)]
pub fn run_script_str(src: &str) -> io::Result<()> {
    ReplSession::new().run_script_str(src, "<repl-script>".to_string())
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

#[derive(Default)]
struct ReplComposer;

impl ReplComposer {
    fn new() -> Self {
        Self
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

        match ReplWorld::parse_source_chunk(buffer) {
            Ok(_) => ReplComposerEvent::Complete(buffer.to_string()),
            Err(ReplWorldParse::Incomplete) => {
                ReplComposerEvent::Diagnostic("incomplete repl input".to_string())
            }
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

    pub(crate) fn run_script_str(&mut self, src: &str, source_name: String) -> io::Result<()> {
        let mut t = crate::types::ConcreteTypes;
        let frontend = match crate::frontend::compile_source_with_types(
            &mut t,
            src.to_string(),
            source_name,
            &crate::telemetry::NullTelemetry,
        ) {
            Ok(ok) => ok,
            Err(err) => {
                return Err(diagnostics_to_io_error(&err.sm, err.diagnostics.as_slice()));
            }
        };
        if frontend
            .diagnostics
            .as_slice()
            .iter()
            .any(|d| d.severity == crate::diag::diagnostic::Severity::Error)
        {
            return Err(diagnostics_to_io_error(
                &frontend.sm,
                frontend.diagnostics.as_slice(),
            ));
        }

        let Some(main) = frontend.module.fn_by_name("main") else {
            return Ok(());
        };
        if !main.block(main.entry).params.is_empty() {
            return Ok(());
        }

        ReplRuntime::run_script_main(&frontend.module, main.id)
    }

    pub(crate) fn eval_chunk(&mut self, src: &str) -> ReplChunkOutcome {
        match self.world.parse_chunk(src) {
            Ok(ReplWorldChunk::Items(prog)) => match self.world.apply_items(src, prog) {
                Ok(_module) => ReplChunkOutcome::Ok(None),
                Err(e) => ReplChunkOutcome::Err(e),
            },
            Ok(ReplWorldChunk::Expr { expr, sm }) => self.eval_expr_chunk(src, expr, sm),
            Err(ReplWorldParse::Incomplete) => ReplChunkOutcome::Err(
                "incomplete repl input must be composed before execution".to_string(),
            ),
            Err(ReplWorldParse::Err(msg)) => ReplChunkOutcome::Err(msg),
        }
    }

    fn eval_expr_chunk(
        &mut self,
        _src: &str,
        expr: crate::ast::Spanned<crate::ast::Expr>,
        sm: crate::diag::SourceMap,
    ) -> ReplChunkOutcome {
        let eval_name = format!("__repl_eval_{}", self.next_eval);
        let compiled = match self
            .world
            .compile_repl_expr(expr, self.frame.names(), eval_name, sm)
        {
            Ok(compiled) => compiled,
            Err(e) => return ReplChunkOutcome::Err(e.to_string()),
        };
        let runtime = self
            .runtime
            .get_or_insert_with(|| ReplRuntime::new(&compiled.module));
        let args = match self.frame.values_for(&compiled.input_frame) {
            Ok(args) => args,
            Err(e) => return ReplChunkOutcome::Err(e),
        };
        let value = match runtime.eval_entry(&compiled.module, compiled.fn_id, args) {
            Ok(value) => value,
            Err(e) => return ReplChunkOutcome::Err(e),
        };
        let fields = match runtime.read_tuple_fields(value, compiled.output_frame.len() + 1) {
            Ok(fields) => fields,
            Err(e) => {
                let rendered = runtime.render_value(value).unwrap_or(e);
                return ReplChunkOutcome::Err(format!(
                    "repl expression did not return frame tuple: {}",
                    rendered
                ));
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

    fn render_value(&self, value: crate::ir_interp::AnyValue) -> String {
        self.runtime
            .as_ref()
            .and_then(|runtime| runtime.render_value(value).ok())
            .unwrap_or_else(|| value.render())
    }
}

struct ReplRuntime {
    interp: crate::ir_interp::IrInterpRuntime,
    evaluator_pid: u32,
    current_module: crate::fz_ir::Module,
}

impl ReplRuntime {
    fn new(module: &crate::fz_ir::Module) -> Self {
        Self {
            interp: crate::ir_interp::IrInterpRuntime::fresh_with_root(module),
            evaluator_pid: 1,
            current_module: module.clone(),
        }
    }

    fn run_script_main(
        module: &crate::fz_ir::Module,
        main_id: crate::fz_ir::FnId,
    ) -> io::Result<()> {
        let mut runtime = Self::new(module);
        let completions = runtime
            .enqueue_and_drive(module, main_id, vec![], /*keepalive=*/ false)
            .map_err(io::Error::other)?;
        if completions
            .iter()
            .any(|(pid, _)| *pid == runtime.evaluator_pid)
        {
            Ok(())
        } else {
            Err(io::Error::other("script main/0 blocked with idle runtime"))
        }
    }

    fn eval_entry(
        &mut self,
        module: &crate::fz_ir::Module,
        fn_id: crate::fz_ir::FnId,
        args: Vec<crate::ir_interp::AnyValue>,
    ) -> Result<crate::ir_interp::AnyValue, String> {
        let completions = self.enqueue_and_drive(module, fn_id, args, /*keepalive=*/ true)?;
        completions
            .into_iter()
            .rev()
            .find_map(|(pid, value)| (pid == self.evaluator_pid).then_some(value))
            .ok_or_else(|| "repl expression blocked".to_string())
    }

    fn enqueue_and_drive(
        &mut self,
        module: &crate::fz_ir::Module,
        fn_id: crate::fz_ir::FnId,
        args: Vec<crate::ir_interp::AnyValue>,
        keepalive: bool,
    ) -> Result<Vec<(u32, crate::ir_interp::AnyValue)>, String> {
        self.current_module = module.clone();
        self.interp
            .enqueue_entry(module, self.evaluator_pid, fn_id, args)?;
        let keepalive_pid = keepalive.then_some(self.evaluator_pid);
        self.interp
            .drive_until_idle(&crate::telemetry::NullTelemetry, keepalive_pid)
    }

    fn read_tuple_fields(
        &self,
        value: crate::ir_interp::AnyValue,
        arity: usize,
    ) -> Result<Vec<crate::ir_interp::AnyValue>, String> {
        self.interp
            .read_tuple_fields(self.evaluator_pid, value, arity)
    }

    fn render_value(&self, value: crate::ir_interp::AnyValue) -> Result<String, String> {
        self.interp.render_value(self.evaluator_pid, value)
    }
}

struct ReplFrame {
    values: BTreeMap<String, crate::ir_interp::AnyValue>,
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

    fn values_for(&self, names: &[String]) -> Result<Vec<crate::ir_interp::AnyValue>, String> {
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

    fn replace(
        &mut self,
        names: Vec<String>,
        values: &[crate::ir_interp::AnyValue],
    ) -> Result<(), String> {
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
    compile_time: CompileTimeEvaluator,
    item_chunks: Vec<ReplItemChunk>,
    eval_chunks: Vec<Program>,
}

struct ReplItemChunk {
    prog: Program,
    fns: Vec<(String, usize)>,
}

struct ReplCompiledEntry {
    module: crate::fz_ir::Module,
    fn_id: crate::fz_ir::FnId,
    input_frame: Vec<String>,
    output_frame: Vec<String>,
    entry_program: Program,
}

enum ReplWorldChunk {
    Items(Program),
    Expr {
        expr: crate::ast::Spanned<crate::ast::Expr>,
        sm: crate::diag::SourceMap,
    },
}

#[derive(Debug)]
enum ReplWorldParse {
    Incomplete,
    Err(String),
}

impl ReplWorld {
    fn new() -> Self {
        Self {
            compile_time: CompileTimeEvaluator::new(),
            item_chunks: Vec::new(),
            eval_chunks: Vec::new(),
        }
    }

    fn parse_chunk(&self, src: &str) -> Result<ReplWorldChunk, ReplWorldParse> {
        Self::parse_source_chunk(src)
    }

    fn parse_source_chunk(src: &str) -> Result<ReplWorldChunk, ReplWorldParse> {
        let mut sm = crate::diag::SourceMap::new();
        let file_id = sm.add_file("<repl-chunk>".to_string(), src.to_string());
        let toks = Lexer::with_file(src, file_id)
            .tokenize()
            .map_err(|e| ReplWorldParse::Err(format!("{}", e)))?;
        let starts_with_item = toks
            .iter()
            .map(|t| &t.tok)
            .find(|t| !matches!(t, crate::lexer::Tok::Newline | crate::lexer::Tok::Semi))
            .map(|t| {
                matches!(
                    t,
                    crate::lexer::Tok::At
                        | crate::lexer::Tok::Fn
                        | crate::lexer::Tok::Extern
                        | crate::lexer::Tok::Defmacro
                        | crate::lexer::Tok::Defmodule
                )
            })
            .unwrap_or(false);

        if starts_with_item {
            let mut p = Parser::new(toks);
            return match p.parse_program() {
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

    fn apply_items(&mut self, _src: &str, prog: Program) -> Result<crate::fz_ir::Module, String> {
        let fns = item_fn_shapes(&prog);
        self.load_docs_and_macros(prog.clone())?;
        self.item_chunks.retain(|existing| {
            !existing.fns.iter().any(|(old_name, old_arity)| {
                fns.iter()
                    .any(|(new_name, new_arity)| old_name == new_name && old_arity != new_arity)
            })
        });
        self.item_chunks.push(ReplItemChunk { prog, fns });
        match self.compile_session_module() {
            Ok(module) => Ok(module),
            Err(e) => Err(e.to_string()),
        }
    }

    fn compile_repl_expr(
        &self,
        expr: crate::ast::Spanned<crate::ast::Expr>,
        input_frame: Vec<String>,
        entry_name: String,
        sm: crate::diag::SourceMap,
    ) -> io::Result<ReplCompiledEntry> {
        let mut t = crate::types::ConcreteTypes;
        let out = match crate::frontend::compile_repl_expr_with_types(
            &mut t,
            self.session_program(),
            expr,
            input_frame,
            entry_name,
            sm,
            &crate::telemetry::NullTelemetry,
        ) {
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
            .any(|d| d.severity == crate::diag::diagnostic::Severity::Error)
        {
            return Err(diagnostics_to_io_error(
                &out.frontend.sm,
                out.frontend.diagnostics.as_slice(),
            ));
        }
        let mut entry_program = Program::default();
        entry_program.items.push(out.entry_item);
        Ok(ReplCompiledEntry {
            module: out.frontend.module,
            fn_id: out.entry_fn,
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

    fn compile_session_module(&self) -> io::Result<crate::fz_ir::Module> {
        compile_parsed_program_module(self.session_program())
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

    fn load_docs_and_macros(&mut self, prog: Program) -> Result<(), String> {
        let mut ct = crate::types::ConcreteTypes;
        let mut prog =
            crate::resolve::flatten_modules(&mut ct, prog).map_err(|e| format!("module: {}", e))?;
        for (path, doc) in &prog.module_docs {
            self.compile_time
                .module_docs
                .borrow_mut()
                .insert(path.clone(), doc.clone());
        }
        if let Err(e) = load_items_filtered(&self.compile_time, &prog, /*macros=*/ true) {
            return Err(format!("load macros: {}", e));
        }
        let live = self.compile_time.macro_names.borrow().clone();
        if let Err(e) = crate::macros::expand_with(&mut prog, &self.compile_time, &live) {
            return Err(format!("macro: {}", e));
        }
        if let Err(e) = load_items_filtered(&self.compile_time, &prog, /*macros=*/ false) {
            return Err(format!("load fns: {}", e));
        }
        Ok(())
    }
}

pub(crate) enum ReplChunkOutcome {
    Ok(Option<crate::ir_interp::AnyValue>),
    Err(String),
}

fn compile_parsed_program_module(prog: Program) -> io::Result<crate::fz_ir::Module> {
    let mut t = crate::types::ConcreteTypes;
    let frontend = match crate::frontend::compile_program_with_types(
        &mut t,
        prog,
        crate::diag::SourceMap::new(),
        &crate::telemetry::NullTelemetry,
    ) {
        Ok(ok) => ok,
        Err(err) => {
            return Err(diagnostics_to_io_error(&err.sm, err.diagnostics.as_slice()));
        }
    };
    if frontend
        .diagnostics
        .as_slice()
        .iter()
        .any(|d| d.severity == crate::diag::diagnostic::Severity::Error)
    {
        return Err(diagnostics_to_io_error(
            &frontend.sm,
            frontend.diagnostics.as_slice(),
        ));
    }
    Ok(frontend.module)
}

fn item_fn_shapes(prog: &Program) -> Vec<(String, usize)> {
    prog.items
        .iter()
        .filter_map(|item| match &**item {
            Item::Fn(def) => Some((
                def.name.clone(),
                def.clauses
                    .first()
                    .map(|clause| clause.params.len())
                    .unwrap_or(0),
            )),
            _ => None,
        })
        .collect()
}

fn append_items_grouping_fn_clauses<I>(prog: &mut Program, items: I)
where
    I: IntoIterator<Item = std::rc::Rc<Item>>,
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
        *existing = std::rc::Rc::new(Item::Fn(merged));
    }
}

fn fn_def_arity(def: &crate::ast::FnDef) -> usize {
    def.clauses
        .first()
        .map(|clause| clause.params.len())
        .unwrap_or(0)
}

fn diagnostics_to_io_error(
    sm: &crate::diag::SourceMap,
    diags: &[crate::diag::Diagnostic],
) -> io::Error {
    let rendered = diags
        .iter()
        .map(|d| crate::diag::render_one_to_string(sm, d))
        .collect::<Vec<_>>()
        .join("");
    io::Error::other(rendered)
}

/// `which == true` loads only macros; `which == false` loads only non-macros.
/// Splitting the two phases lets the REPL register macros before running
/// expansion on fn bodies that may call them.
fn load_items_filtered(
    interp: &CompileTimeEvaluator,
    prog: &Program,
    macros_only: bool,
) -> Result<(), String> {
    use std::rc::Rc;
    for item in &prog.items {
        match &**item {
            Item::Module(_) | Item::Alias { .. } | Item::Import { .. } | Item::MacroCall { .. } => {
                continue;
            } // flattened away upstream
            Item::Fn(def) => {
                if macros_only != def.is_macro {
                    continue;
                }
                if def.is_macro {
                    interp.macro_names.borrow_mut().insert(def.name.clone());
                    interp
                        .macro_def_spans
                        .borrow_mut()
                        .insert(def.name.clone(), def.span);
                }
                // If a closure already exists under this name *and* the new
                // clauses match arity, append. Otherwise replace. Matches
                // user expectation: typing several `fn foo(...)` lines in
                // sequence builds up a multi-clause fn.
                let existing = interp.globals.lookup(&def.name);
                let mut clauses = def.clauses.clone();
                let mut doc = def.doc().map(String::from);
                let mut spec_text = crate::eval::format_spec_text(def, prog);
                if let Some(Value::Closure(c)) = existing {
                    let same_arity = c.clauses.first().map(|cl| cl.params.len())
                        == clauses.first().map(|cl| cl.params.len());
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
                let closure = Value::Closure(Rc::new(crate::value::Closure {
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
            out.push_str("@spec: ");
            out.push_str(s);
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
mod tests {
    use super::*;
    use std::collections::VecDeque;

    struct FakeLineEditor {
        lines: VecDeque<ReplLine>,
        history: Vec<String>,
    }

    impl FakeLineEditor {
        fn new(lines: impl IntoIterator<Item = ReplLine>) -> Self {
            Self {
                lines: lines.into_iter().collect(),
                history: Vec::new(),
            }
        }
    }

    impl ReplLineEditor for FakeLineEditor {
        fn read_line(&mut self, _prompt: &str) -> io::Result<ReplLine> {
            Ok(self.lines.pop_front().unwrap_or(ReplLine::Eof))
        }

        fn add_history_entry(&mut self, line: &str) -> io::Result<()> {
            self.history.push(line.to_string());
            Ok(())
        }
    }

    fn load_program_test(interp: &CompileTimeEvaluator, prog: &Program) -> Result<(), String> {
        load_items_filtered(interp, prog, false)?;
        load_items_filtered(interp, prog, true)?;
        Ok(())
    }

    /// Drive the same session path as the REPL but capture rendered eval
    /// results in a vec rather than printing.
    fn drive(lines: &[&str]) -> Vec<Result<String, String>> {
        let mut session = ReplSession::new();
        let mut composer = ReplComposer::new();
        let mut out: Vec<Result<String, String>> = Vec::new();
        for line in lines {
            match composer.submit_buffer(line) {
                ReplComposerEvent::Empty => {}
                ReplComposerEvent::Quit => break,
                ReplComposerEvent::DocQuery(q) => out.push(Ok(session.lookup_doc(&q))),
                ReplComposerEvent::Diagnostic(msg) => out.push(Err(msg)),
                ReplComposerEvent::Complete(src) => match session.eval_chunk(&src) {
                    ReplChunkOutcome::Ok(Some(value)) => {
                        out.push(Ok(session.render_value(value)));
                    }
                    ReplChunkOutcome::Ok(None) => {
                        out.push(Ok("nil".to_string()));
                    }
                    ReplChunkOutcome::Err(msg) => {
                        out.push(Err(msg));
                    }
                },
            }
        }
        out
    }

    #[test]
    fn evaluates_simple_expression() {
        let r = drive(&["1 + 2"]);
        assert_eq!(r.len(), 1);
        assert_eq!(r[0].as_deref(), Ok("3"));
    }

    #[test]
    fn drive_uses_composer_for_blank_docs_quit_and_parse_errors() {
        let r = drive(&["", "?missing", "1 2", "3", ":q", "4"]);
        assert_eq!(r.len(), 3);
        assert_eq!(r[0].as_deref(), Ok("missing: not found"));
        assert!(
            matches!(&r[1], Err(msg) if msg.contains("trailing tokens")),
            "{:?}",
            r[1]
        );
        assert_eq!(r[2].as_deref(), Ok("3"));
    }

    #[test]
    fn repl_round_trip_int_float_and_mixed_list_display() {
        let r = drive(&["42", "3.14", "[1, 2.5, :a]"]);
        assert_eq!(r[0].as_deref(), Ok("42"));
        assert_eq!(r[1].as_deref(), Ok("3.14"));
        assert_eq!(r[2].as_deref(), Ok("[1, 2.5, :a]"));
    }

    #[test]
    fn run_script_str_accepts_utf8_smart_constructors() {
        let src = r#"
fn main() do
  good = <<104, 105>>
  bad = <<0xff, 0xff>>
  assert(Utf8.valid?(good))
  assert_neq(Utf8.valid?(bad), true)
  assert_eq(Utf8.from_bytes(good), {:ok, "hi"})
  assert_eq(Utf8.from_bytes(bad), {:error, :invalid_utf8})
end
"#;
        run_script_str(src).expect("Utf8 helpers should run through script REPL");
    }

    fn eval_session_i64(session: &mut ReplSession, src: &str) -> Option<i64> {
        match session.eval_chunk(src) {
            ReplChunkOutcome::Ok(Some(value)) => value.as_i64(),
            ReplChunkOutcome::Err(err) => panic!("expected value from `{}`; got err: {}", src, err),
            other => panic!(
                "expected value from `{}`; got {:?}",
                src,
                outcome_name(&other)
            ),
        }
    }

    fn eval_session_render(session: &mut ReplSession, src: &str) -> String {
        match session.eval_chunk(src) {
            ReplChunkOutcome::Ok(Some(value)) => session.render_value(value),
            ReplChunkOutcome::Err(err) => panic!("expected value from `{}`; got err: {}", src, err),
            other => panic!(
                "expected value from `{}`; got {:?}",
                src,
                outcome_name(&other)
            ),
        }
    }

    fn outcome_name(outcome: &ReplChunkOutcome) -> &'static str {
        match outcome {
            ReplChunkOutcome::Ok(Some(_)) => "value",
            ReplChunkOutcome::Ok(None) => "ok",
            ReplChunkOutcome::Err(_) => "err",
        }
    }

    #[test]
    fn repl_line_editor_trait_accepts_fake_editor() {
        let mut editor = FakeLineEditor::new([ReplLine::Line("1 + 2".to_string())]);
        assert_eq!(
            editor.read_line("fz> ").expect("read fake line"),
            ReplLine::Line("1 + 2".to_string())
        );
        editor.add_history_entry("1 + 2").expect("record history");
        assert_eq!(editor.history, vec!["1 + 2"]);
        assert_eq!(editor.read_line("fz> ").expect("read eof"), ReplLine::Eof);
    }

    #[test]
    fn line_editor_validator_continues_only_parser_incomplete_input() {
        assert!(matches!(
            ReplEditorHelper::validation_result_for("do\n  1"),
            rustyline::validate::ValidationResult::Incomplete
        ));
        assert!(matches!(
            ReplEditorHelper::validation_result_for("do\n  1\nend"),
            rustyline::validate::ValidationResult::Valid(None)
        ));
        assert!(matches!(
            ReplEditorHelper::validation_result_for("1 2"),
            rustyline::validate::ValidationResult::Valid(None)
        ));
        assert!(matches!(
            ReplEditorHelper::validation_result_for(":q"),
            rustyline::validate::ValidationResult::Valid(None)
        ));
        assert!(matches!(
            ReplEditorHelper::validation_result_for("   "),
            rustyline::validate::ValidationResult::Valid(None)
        ));
    }

    #[test]
    fn composer_ignores_blank_input() {
        let mut composer = ReplComposer::new();
        assert_eq!(composer.submit_buffer("   "), ReplComposerEvent::Empty);
    }

    #[test]
    fn composer_recognizes_quit_command() {
        let mut composer = ReplComposer::new();
        assert_eq!(composer.submit_buffer(":q"), ReplComposerEvent::Quit);
        assert_eq!(composer.submit_buffer(":quit"), ReplComposerEvent::Quit);
    }

    #[test]
    fn composer_recognizes_docs_query() {
        let mut composer = ReplComposer::new();
        assert_eq!(
            composer.submit_buffer("? Enum.map"),
            ReplComposerEvent::DocQuery("Enum.map".to_string())
        );
    }

    #[test]
    fn composer_accepts_complete_multiline_item_chunks_from_editor() {
        let mut composer = ReplComposer::new();
        assert_eq!(
            composer.submit_buffer(
                r#"@doc "adds one"
fn add1(n), do: n + 1"#
            ),
            ReplComposerEvent::Complete(
                r#"@doc "adds one"
fn add1(n), do: n + 1"#
                    .to_string()
            )
        );
    }

    #[test]
    fn composer_accepts_complete_multiline_expression_chunks_from_editor() {
        let mut composer = ReplComposer::new();
        assert_eq!(
            composer.submit_buffer("do\n  1 + 2\nend"),
            ReplComposerEvent::Complete("do\n  1 + 2\nend".to_string())
        );
    }

    #[test]
    fn composer_keeps_blank_lines_inside_submitted_editor_buffer() {
        let mut composer = ReplComposer::new();
        assert_eq!(
            composer.submit_buffer("do\n\n  1\nend"),
            ReplComposerEvent::Complete("do\n\n  1\nend".to_string())
        );
    }

    #[test]
    fn composer_reports_invalid_input_without_retaining_state() {
        let mut composer = ReplComposer::new();
        assert!(matches!(
            composer.submit_buffer("1 2"),
            ReplComposerEvent::Diagnostic(_)
        ));
        assert_eq!(
            composer.submit_buffer("3"),
            ReplComposerEvent::Complete("3".to_string())
        );
    }

    #[test]
    fn composer_accepts_whitespace_heavy_chunks() {
        let mut composer = ReplComposer::new();
        assert_eq!(
            composer.submit_buffer("   fn id(n), do: n   "),
            ReplComposerEvent::Complete("   fn id(n), do: n   ".to_string())
        );
    }

    #[test]
    fn parser_classifies_incomplete_without_error_text() {
        let toks = Lexer::new("1 +").tokenize().expect("lex");
        let err = Parser::new(toks).parse_expr_eof().unwrap_err();
        assert!(err.is_incomplete(), "{err}");
    }

    #[test]
    fn repl_world_classifies_eof_shaped_item_input_as_incomplete() {
        let err = match ReplWorld::new().parse_chunk(
            r#"
@doc "adds one"
"#,
        ) {
            Ok(_) => panic!("expected incomplete input"),
            Err(err) => err,
        };
        assert!(matches!(err, ReplWorldParse::Incomplete), "{err:?}");
    }

    #[test]
    fn session_rejects_incomplete_execution_input() {
        let mut session = ReplSession::new();
        match session.eval_chunk("do\n  1") {
            ReplChunkOutcome::Err(msg) => assert!(
                msg.contains("must be composed"),
                "expected composition boundary error, got: {}",
                msg
            ),
            other => panic!(
                "expected composition boundary error, got {:?}",
                outcome_name(&other)
            ),
        }
    }

    #[test]
    fn repl_world_classifies_invalid_syntax_as_non_incomplete_error() {
        let err = match ReplWorld::new().parse_chunk("1 2") {
            Ok(_) => panic!("expected invalid input"),
            Err(err) => err,
        };
        assert!(
            matches!(&err, ReplWorldParse::Err(msg) if msg.contains("trailing tokens")),
            "{err:?}"
        );
    }

    #[test]
    fn repl_session_binds_variable_across_chunks() {
        let mut session = ReplSession::new();
        assert_eq!(eval_session_i64(&mut session, "x = 41"), Some(41));
        assert_eq!(eval_session_i64(&mut session, "x + 1"), Some(42));
    }

    #[test]
    fn repl_session_expression_display_does_not_mutate_frame() {
        let mut session = ReplSession::new();
        assert_eq!(eval_session_i64(&mut session, "x = 10"), Some(10));
        assert_eq!(eval_session_i64(&mut session, "x + 5"), Some(15));
        assert_eq!(eval_session_i64(&mut session, "x"), Some(10));
    }

    #[test]
    fn repl_session_destructuring_binding_persists_across_chunks() {
        let mut session = ReplSession::new();
        assert_eq!(
            eval_session_render(&mut session, "{a, b} = {1, 2}"),
            "{1, 2}"
        );
        assert_eq!(eval_session_i64(&mut session, "a + b"), Some(3));
    }

    #[test]
    fn repl_expression_chunks_do_not_depend_on_generated_wrapper_source() {
        let source = std::fs::read_to_string(file!()).expect("read repl source");
        let old_wrapper_shape = ["fn ", "{}({})", " do"].concat();
        assert!(
            !source.contains(&old_wrapper_shape),
            "REPL expression chunks must be compiler-owned entries, not formatted fn source"
        );
        let old_compile_call = ["compile", "_eval", "(&eval", "_source)"].concat();
        assert!(
            !source.contains(&old_compile_call),
            "REPL expression chunks must compile semantic chunk data, not generated eval strings"
        );
    }

    #[test]
    fn repl_frame_abi_is_not_inferred_by_host_pattern_walkers() {
        let source = std::fs::read_to_string(file!()).expect("read repl source");
        let old_frame_walker = ["fn ", "bound", "_names", "("].concat();
        assert!(
            !source.contains(&old_frame_walker),
            "frame ABI shape must come from compiler-owned lowered locals"
        );
        let old_pattern_walker = ["fn ", "collect", "_pattern", "_names", "("].concat();
        assert!(
            !source.contains(&old_pattern_walker),
            "REPL host must not walk patterns to decide frame updates"
        );
    }

    #[test]
    fn repl_diagnostics_are_anchored_to_user_source_not_wrapper_text() {
        let mut session = ReplSession::new();
        match session.eval_chunk("missing_name + 1") {
            ReplChunkOutcome::Err(err) => {
                assert!(
                    !err.contains("__repl_eval"),
                    "diagnostic leaked compiler entry name: {}",
                    err
                );
                assert!(
                    err.contains("missing_name"),
                    "diagnostic should name the user source binding: {}",
                    err
                );
            }
            other => panic!("expected diagnostic, got {:?}", outcome_name(&other)),
        }
    }

    #[test]
    fn repl_accepts_whitespace_heavy_multiline_expression_chunks() {
        let mut session = ReplSession::new();
        let src = "\n\n  x\n    =\n      41\n";
        assert_eq!(eval_session_i64(&mut session, src), Some(41));
        assert_eq!(eval_session_i64(&mut session, "x + 1"), Some(42));
    }

    #[test]
    fn repl_session_match_failure_uses_lowered_runtime_semantics() {
        let mut session = ReplSession::new();
        assert_eq!(eval_session_i64(&mut session, "x = 1"), Some(1));
        match session.eval_chunk("{:ok, y} = {:error, 2}") {
            ReplChunkOutcome::Err(err) => assert!(
                err.contains("match") || err.contains("clause"),
                "expected match failure diagnostic, got: {}",
                err
            ),
            other => panic!("expected match failure, got {:?}", outcome_name(&other)),
        }
        assert_eq!(eval_session_i64(&mut session, "x"), Some(1));
    }

    #[test]
    fn repl_session_top_level_definition_is_callable() {
        let mut session = ReplSession::new();
        assert!(matches!(
            session.eval_chunk("fn add1(n), do: n + 1"),
            ReplChunkOutcome::Ok(None)
        ));
        assert_eq!(eval_session_i64(&mut session, "add1(41)"), Some(42));
    }

    #[test]
    fn repl_session_accepts_top_level_extern_declaration() {
        let mut session = ReplSession::new();
        assert!(matches!(
            session.eval_chunk(r#"extern "C" fn libc::open(cstring, cstring) :: integer"#),
            ReplChunkOutcome::Ok(None)
        ));
    }

    #[test]
    fn repl_session_spawned_child_blocks_across_chunks_and_resumes() {
        let mut session = ReplSession::new();
        assert_eq!(eval_session_i64(&mut session, "parent = self()"), Some(1));
        assert_eq!(
            eval_session_i64(&mut session, "spawn(fn () -> send(parent, receive()))"),
            Some(2),
        );
        assert_eq!(eval_session_i64(&mut session, "send(2, 42)"), Some(42));
        assert_eq!(eval_session_i64(&mut session, "receive()"), Some(42));
    }

    #[test]
    fn repl_session_blocked_child_survives_later_code_generation() {
        let mut session = ReplSession::new();
        assert_eq!(eval_session_i64(&mut session, "parent = self()"), Some(1));
        assert_eq!(
            eval_session_i64(&mut session, "spawn(fn () -> send(parent, receive()))"),
            Some(2),
        );
        assert!(matches!(
            session.eval_chunk("fn id(n), do: n"),
            ReplChunkOutcome::Ok(None)
        ));
        assert_eq!(eval_session_i64(&mut session, "id(42)"), Some(42));
        assert_eq!(eval_session_i64(&mut session, "send(2, 7)"), Some(7));
        assert_eq!(eval_session_i64(&mut session, "receive()"), Some(7));
    }

    #[test]
    fn repl_round_trip_send_receive_self() {
        let r = drive(&["send(self(), [1, 2.5, :a])", "receive()"]);
        assert_eq!(r[1].as_deref(), Ok("[1, 2.5, :a]"));
    }

    #[test]
    fn repl_spawned_send_round_trips_through_receive_matcher() {
        let r = drive(&[
            "parent = self()",
            "spawn(fn () -> send(parent, [1, 2.5, :a]))",
            r#"receive do
                 [1, 2.5, :a] -> :ok
               after
                 0 -> :miss
               end"#,
        ]);
        assert_eq!(r[2].as_deref(), Ok(":ok"));
    }

    #[test]
    fn repl_spawn2_accepts_ignored_heap_hint() {
        let r = drive(&[
            "parent = self()",
            "spawn(fn () -> send(parent, 42), 4096)",
            "receive()",
        ]);
        assert_eq!(r[2].as_deref(), Ok("42"));
    }

    #[test]
    fn binds_variable_across_inputs() {
        let r = drive(&["x = 7", "x + 35"]);
        assert_eq!(r.len(), 2);
        assert_eq!(r[1].as_deref(), Ok("42"));
    }

    #[test]
    fn appends_clauses_to_existing_fn() {
        let r = drive(&[
            "fn fact(0), do: 1",
            "fn fact(n), do: n * fact(n - 1)",
            "fact(6)",
        ]);
        assert!(r[2].as_deref() == Ok("720"), "expected 720, got {:?}", r[2]);
    }

    #[test]
    fn accepts_multiline_do_end_from_editor_buffer() {
        let r = drive(&[
            "fn double_plus(x) do\n  y = x + 1\n  y * 2\nend",
            "double_plus(20)",
        ]);
        let last = r.last().unwrap();
        assert_eq!(last.as_deref(), Ok("42"), "got {:?}", last);
    }

    /// Drive a full program (lex → parse → flatten → load) and return the
    /// interp so doc-lookup tests can inspect post-load state. Mirrors what
    /// the REPL does for an item-level input, but in one shot.
    fn load(src: &str) -> CompileTimeEvaluator {
        let interp = CompileTimeEvaluator::new();
        let toks = Lexer::new(src).tokenize().expect("lex");
        let prog = Parser::new(toks).parse_program().expect("parse");
        let mut ct = crate::types::ConcreteTypes;
        let prog = crate::resolve::flatten_modules(&mut ct, prog).expect("resolve");
        for (path, doc) in &prog.module_docs {
            interp
                .module_docs
                .borrow_mut()
                .insert(path.clone(), doc.clone());
        }
        load_program_test(&interp, &prog).expect("load");
        interp
    }

    fn apply_world_item(world: &mut ReplWorld, src: &str) {
        match world.parse_chunk(src).expect("parse world chunk") {
            ReplWorldChunk::Items(prog) => {
                world.apply_items(src, prog).expect("apply world items");
            }
            ReplWorldChunk::Expr { .. } => panic!("expected item chunk"),
        }
    }

    fn parse_world_expr(
        src: &str,
    ) -> (
        crate::ast::Spanned<crate::ast::Expr>,
        crate::diag::SourceMap,
    ) {
        match ReplWorld::new()
            .parse_chunk(src)
            .expect("parse world chunk")
        {
            ReplWorldChunk::Expr { expr, sm } => (expr, sm),
            ReplWorldChunk::Items(_) => panic!("expected expression chunk"),
        }
    }

    #[test]
    fn repl_world_owns_docs_lookup() {
        let mut world = ReplWorld::new();
        apply_world_item(
            &mut world,
            r#"
defmodule M do
  @moduledoc "the M module"
  @doc "adds two"
  fn add(a, b), do: a + b
end
"#,
        );
        assert_eq!(world.lookup_doc("M"), "the M module");
        assert_eq!(world.lookup_doc("M.add"), "@doc:  adds two");
    }

    #[test]
    fn repl_world_compiles_accumulated_item_clauses() {
        let mut world = ReplWorld::new();
        apply_world_item(&mut world, "fn fact(0), do: 1");
        apply_world_item(&mut world, "fn fact(n), do: n * fact(n - 1)");
        let (expr, sm) = parse_world_expr("fact(5)");
        let module = world
            .compile_repl_expr(expr, vec![], "__repl_eval_0".to_string(), sm)
            .expect("compile accumulated clauses");
        assert!(module.module.fn_by_name("__repl_eval_0").is_some());
    }

    #[test]
    fn repl_world_compiles_eval_chunks_with_accumulated_macros() {
        let mut world = ReplWorld::new();
        apply_world_item(
            &mut world,
            r#"
defmacro inc(x) do
  quote do: unquote(x) + 1
end
"#,
        );
        let (expr, sm) = parse_world_expr("inc(41)");
        let module = world
            .compile_repl_expr(expr, vec![], "__repl_eval_0".to_string(), sm)
            .expect("compile macro-using eval chunk");
        assert!(module.module.fn_by_name("__repl_eval_0").is_some());
    }

    #[test]
    fn doc_query_finds_module_fn_doc() {
        let interp = load(
            r#"
defmodule M do
  @doc "adds two"
  fn add(a, b), do: a + b
end
"#,
        );
        assert_eq!(lookup_doc(&interp, "M.add"), "@doc:  adds two");
    }

    #[test]
    fn doc_query_finds_moduledoc() {
        let interp = load(
            r#"
defmodule M do
  @moduledoc "the M module"
  fn add(a, b), do: a + b
end
"#,
        );
        assert_eq!(lookup_doc(&interp, "M"), "the M module");
    }

    #[test]
    fn doc_query_surfaces_spec_when_declared() {
        // .31.6 — `?<name>` renders @spec alongside @doc when both are
        // declared.
        let interp = load(
            r#"
defmodule M do
  @doc "adds one"
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#,
        );
        let out = lookup_doc(&interp, "M.add1");
        assert!(
            out.contains("@spec"),
            "should render @spec line; got: {}",
            out
        );
        assert!(
            out.contains("@doc"),
            "should render @doc line; got: {}",
            out
        );
        // Type display renders integer as `int` (the lattice's name).
        assert!(
            out.contains("(int) -> int"),
            "should render declared types; got: {}",
            out
        );
    }

    #[test]
    fn doc_query_surfaces_spec_without_doc() {
        // .31.6 — @spec alone still surfaces in `?<name>`.
        let interp = load(
            r#"
defmodule M do
  @spec add1(integer) :: integer
  fn add1(n), do: n + 1
end
"#,
        );
        let out = lookup_doc(&interp, "M.add1");
        assert!(
            out.contains("@spec"),
            "should render @spec line; got: {}",
            out
        );
        assert!(
            !out.contains("no documentation"),
            "@spec alone counts as documentation; got: {}",
            out
        );
    }

    #[test]
    fn doc_query_missing_doc_reports_so() {
        let interp = load("fn plain(x), do: x");
        assert_eq!(lookup_doc(&interp, "plain"), "plain: no documentation");
    }

    #[test]
    fn doc_query_unknown_name_reports_not_found() {
        let interp = load("fn plain(x), do: x");
        assert_eq!(lookup_doc(&interp, "nope"), "nope: not found");
    }

    #[test]
    fn doc_query_empty_shows_usage() {
        let interp = CompileTimeEvaluator::new();
        assert!(lookup_doc(&interp, "").starts_with("usage:"));
    }

    // ===== fz-i67.1 — run_script_str =====

    #[test]
    fn run_script_str_accepts_program_with_main() {
        // Defines main/0; run_script_str should call it. (We can't capture
        // stdout from a unit test without subprocessing; the matrix leg in
        // fz-i67.2 covers the stdout side. Here we just verify the driver
        // completes without error.)
        let src = "fn add1(n) do n + 1 end\nfn main() do print(add1(41)) end\n";
        run_script_str(src).expect("script with main should succeed");
    }

    #[test]
    fn run_script_str_uses_scheduler_backed_relay() {
        let src = std::fs::read_to_string("fixtures/relay/input.fz").expect("read relay fixture");
        run_script_str(&src).expect("relay should run through ir_interp-backed ReplSession");
    }

    #[test]
    fn run_script_str_accepts_program_without_main() {
        // No main/0 defined → driver finishes without calling anything.
        let src = "fn add1(n) do n + 1 end\n";
        run_script_str(src).expect("script without main should succeed");
    }

    #[test]
    fn run_script_str_accepts_multi_line_forms() {
        let src = "fn double(x) do\n  x * 2\nend\nfn main() do print(double(21)) end\n";
        run_script_str(src).expect("multi-line fn body should parse and run");
    }

    #[test]
    fn run_script_str_accepts_top_level_spec_with_fn() {
        let src = "@spec add1(integer) :: integer\nfn add1(n), do: n + 1\nfn main() do print(add1(41)) end\n";
        run_script_str(src).expect("top-level @spec should attach to following fn");
    }

    #[test]
    fn run_script_str_reports_parse_error() {
        // A syntactically broken input should surface as Err — the matrix
        // leg will translate that into a nonzero exit code.
        let src = "fn main() do print(\n"; // unterminated
        let err = run_script_str(src).expect_err("unterminated input should fail");
        let msg = err.to_string();
        assert!(
            msg.contains("parse/expected-token"),
            "expected a parser diagnostic, got: {}",
            msg
        );
    }

    #[test]
    fn redefines_fn_with_different_arity() {
        let r = drive(&["fn f(x), do: x + 1", "fn f(x, y), do: x + y", "f(10, 20)"]);
        // Different arity → replace, not append. f/2 should resolve.
        assert_eq!(r[2].as_deref(), Ok("30"), "got {:?}", r[2]);
    }
}
