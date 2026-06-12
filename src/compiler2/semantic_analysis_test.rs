use std::cell::RefCell;
use std::rc::Rc;

use super::{
    CallSiteKey, CallSiteSummary, CodeSubmission, Compiler2, DriveOutcome, ExecutableNeed, FactKey, FunctionId,
    FunctionRef, Job, RootSubmission, SelectedCallee,
};
use crate::telemetry::Value;
use crate::telemetry::handler::{Event, EventKind, Handler};

type FunctionDefs = Rc<RefCell<Vec<FunctionDef>>>;
type CallsiteDefs = Rc<RefCell<Vec<CallsiteDef>>>;

#[derive(Debug, Clone)]
struct FunctionDef {
    id: FunctionId,
    name: String,
    arity: u64,
}

#[derive(Debug, Clone)]
struct CallsiteDef {
    key: CallSiteKey,
    summary: CallSiteSummary,
}

struct FunctionCapture {
    defs: FunctionDefs,
}

struct CallsiteCapture {
    defs: CallsiteDefs,
}

impl FunctionCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(FunctionCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn id(&self, name: &str, arity: u64) -> FunctionId {
        self.defs
            .borrow()
            .iter()
            .rev()
            .find(|def| def.name == name && def.arity == arity)
            .map(|def| def.id)
            .unwrap_or_else(|| panic!("function definition for {name}/{arity}"))
    }
}

impl CallsiteCapture {
    fn new() -> Self {
        Self {
            defs: Rc::new(RefCell::new(Vec::new())),
        }
    }

    fn handler(&self) -> Box<dyn Handler> {
        Box::new(CallsiteCaptureHandler {
            defs: self.defs.clone(),
        })
    }

    fn all(&self) -> Vec<CallsiteDef> {
        self.defs.borrow().clone()
    }
}

struct FunctionCaptureHandler {
    defs: FunctionDefs,
}

struct CallsiteCaptureHandler {
    defs: CallsiteDefs,
}

impl Handler for FunctionCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.kind != EventKind::Event
            || !matches!(
                event.name,
                ["fz", "compiler2", "function", "defined"] | ["fz", "compiler2", "function", "source", "noted"]
            )
        {
            return;
        }
        let Some(id) = event
            .metadata
            .get("function_id")
            .and_then(|value| value.downcast_ref::<FunctionId>())
            .copied()
        else {
            return;
        };
        let Some(function_ref) = event
            .metadata
            .get("function_ref")
            .and_then(|value| value.downcast_ref::<FunctionRef>())
        else {
            return;
        };
        let Some(Value::U64(arity)) = event.measurements.get("arity") else {
            return;
        };
        self.defs.borrow_mut().push(FunctionDef {
            id,
            name: function_ref.name.clone(),
            arity: *arity,
        });
    }
}

impl Handler for CallsiteCaptureHandler {
    fn handle(&self, event: &Event<'_, '_, '_>) {
        if event.name != ["fz", "compiler2", "callsite", "defined"] || event.kind != EventKind::Event {
            return;
        }
        let Some(key) = event
            .metadata
            .get("callsite")
            .and_then(|value| value.downcast_ref::<CallSiteKey>())
        else {
            return;
        };
        let Some(summary) = event
            .metadata
            .get("summary")
            .and_then(|value| value.downcast_ref::<CallSiteSummary>())
        else {
            return;
        };
        self.defs.borrow_mut().push(CallsiteDef {
            key: key.clone(),
            summary: summary.clone(),
        });
    }
}

fn assert_resolved(outcome: DriveOutcome<Job, FactKey>, message: &str) {
    assert!(matches!(outcome, DriveOutcome::Resolved), "{message}: {outcome:?}");
}

fn summary_has_function(summary: &CallSiteSummary, function: FunctionId) -> bool {
    summary
        .targets
        .iter()
        .any(|target| target.callee == SelectedCallee::Function(function))
}

#[test]
fn compiler2_semantic_analysis_does_not_reach_continuation_after_never_return() {
    let tel = crate::telemetry::ConfiguredTelemetry::new();
    let functions = FunctionCapture::new();
    tel.attach(&["fz", "compiler2", "function"], functions.handler());
    let callsites = CallsiteCapture::new();
    tel.attach(&["fz", "compiler2", "callsite", "defined"], callsites.handler());

    let mut compiler = Compiler2::new(&tel);
    compiler.submit_code(CodeSubmission {
        name: Some("never_continuation.fz".to_string()),
        text: r#"
fn main() do
  panic("stop")
  |> dbg()
end
"#
        .to_string(),
    });
    let root_id = compiler.submit_root(RootSubmission {
        module_name: None,
        name: "main".to_string(),
        arity: 0,
        need: ExecutableNeed::Value,
    });

    assert_resolved(
        compiler.drive(),
        "a never-returning call should not keep its pipe continuation semantically live",
    );

    let main = functions.id("main", 0);
    let panic = functions.id("panic", 1);
    let dbg = functions.id("dbg", 1);
    let main_calls = callsites
        .all()
        .into_iter()
        .filter(|record| record.key.activation.root == root_id && record.key.activation.function == main)
        .collect::<Vec<_>>();

    assert!(
        main_calls
            .iter()
            .any(|record| summary_has_function(&record.summary, panic)),
        "main/0 should still publish the never-returning panic/1 edge",
    );
    assert!(
        main_calls
            .iter()
            .all(|record| !summary_has_function(&record.summary, dbg)),
        "main/0 should not publish a dbg/1 edge for a continuation that cannot receive a value",
    );
}
