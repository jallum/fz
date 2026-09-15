mod aot_link;
mod ast;
pub mod compiler2;
mod diag;
mod dispatch_matrix;
mod exec;
mod execution_ready;
mod extern_contract;
mod finite_set;
mod function_surface;
mod fz_ir;
pub mod ground_value;
mod ir_codegen;
mod ir_dce;
mod ir_interp;
mod modules;
mod parser;
mod runtime_type_predicate;
mod source;
mod telemetry;
mod type_expr;
pub mod types;

pub use function_surface::FunctionSurface;
/// Causal replay over a public telemetry log (fz-kdt.34.6). Re-exported at the
/// crate root because it reads the public ARTIFACT, not the compiler: the
/// integration tests and a future `fz2 trace-diff` consume a log file.
pub use telemetry::causal;
pub use telemetry::sink::NullTelemetry;
