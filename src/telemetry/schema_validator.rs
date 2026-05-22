//! Schema-validation handler (fz-ndf.14).
//!
//! `SchemaValidator` is a `Handler` that asserts at runtime that every emitted
//! event is declared in at least one registered `Spec`. In debug builds the
//! assertions fire as panics; in release builds the handler compiles to a
//! no-op via `debug_assert!` so there is no overhead.
//!
//! Attach during driver startup (before any events fire) to catch wiring bugs
//! early. Not intended for production binaries — the overhead of the linear
//! scan is acceptable in tests and local dev, not in release.
//!
//! Validation rules:
//! - Only `EventKind::Event` events are validated; span lifecycle events
//!   (SpanStart/Stop/Exception) are not required to appear in a Spec.
//! - Every event name must appear in at least one registered `Spec`.
//! - Every measurement key must be declared in the matched `EventDecl`.
//! - Every metadata key must be declared in the matched `EventDecl`.
//! - Key type checking is intentionally absent in v1: `KeySpec::ty` exists
//!   for documentation and future tooling; asserting on it would require
//!   mapping `Value` variants to `KeyType` and adds friction for callers
//!   using `KeyType::Any`. Add it when a concrete need arises.

use super::handler::{Event, EventKind, Handler};
use super::spec::Spec;

pub struct SchemaValidator {
    specs: Vec<&'static Spec>,
}

impl SchemaValidator {
    /// Create a validator that checks events against the given specs.
    pub fn new(specs: Vec<&'static Spec>) -> Self {
        Self { specs }
    }
}

impl Handler for SchemaValidator {
    fn handle(&self, ev: &Event<'_>) {
        if ev.kind != EventKind::Event {
            return;
        }

        let decl = self.specs.iter().find_map(|spec| spec.find(ev.name));

        debug_assert!(
            decl.is_some(),
            "telemetry: unknown event {:?}; add it to a Spec and register that Spec with SchemaValidator",
            ev.name,
        );

        if let Some(decl) = decl {
            for (key, _) in ev.measurements.iter() {
                let known = decl.measurements.iter().any(|ks| ks.name == *key);
                debug_assert!(
                    known,
                    "telemetry: measurement key {:?} not declared for event {:?}",
                    key, ev.name,
                );
            }
            for (key, _) in ev.metadata.iter() {
                let known = decl.metadata.iter().any(|ks| ks.name == *key);
                debug_assert!(
                    known,
                    "telemetry: metadata key {:?} not declared for event {:?}",
                    key, ev.name,
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::telemetry::spec::{EventDecl, KeySpec, KeyType, Level};
    use crate::telemetry::{ConfiguredTelemetry, Measurements, Metadata, Telemetry as _};

    // Minimal spec for test events.
    const COUNT_KEY: KeySpec = KeySpec::new("count", KeyType::Uint, "item count");
    const LABEL_KEY: KeySpec = KeySpec::new("label", KeyType::Str, "descriptive label");

    const TEST_EVENT: EventDecl = EventDecl::new(
        &["fz", "test", "done"],
        Level::Info,
        "Test event.",
        &[COUNT_KEY],
        &[LABEL_KEY],
    );

    const TEST_SPEC: Spec = Spec::new("test", "Test spec.", &[TEST_EVENT]);

    fn validator_with_test_spec() -> SchemaValidator {
        SchemaValidator::new(vec![&TEST_SPEC])
    }

    #[test]
    fn clean_known_event_is_silent() {
        let tel = ConfiguredTelemetry::new();
        tel.attach(&[], Box::new(validator_with_test_spec()));

        // A fully-declared event with correct keys must not panic.
        tel.execute(
            &["fz", "test", "done"],
            &crate::measurements! { count: 3usize },
            &crate::metadata! { label: "ok" },
        );
    }

    #[test]
    fn empty_payload_on_known_event_is_silent() {
        let tel = ConfiguredTelemetry::new();
        tel.attach(&[], Box::new(validator_with_test_spec()));
        // Not providing optional keys is fine — the check is "no undeclared
        // keys", not "all declared keys must be present".
        tel.execute(
            &["fz", "test", "done"],
            &Measurements::new(),
            &Metadata::new(),
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "unknown event")]
    fn unknown_event_name_panics_in_debug() {
        let tel = ConfiguredTelemetry::new();
        tel.attach(&[], Box::new(validator_with_test_spec()));
        tel.execute(
            &["fz", "test", "ghost"],
            &Measurements::new(),
            &Metadata::new(),
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "measurement key")]
    fn undeclared_measurement_key_panics_in_debug() {
        let tel = ConfiguredTelemetry::new();
        tel.attach(&[], Box::new(validator_with_test_spec()));
        tel.execute(
            &["fz", "test", "done"],
            &crate::measurements! { surprise: 99usize },
            &Metadata::new(),
        );
    }

    #[test]
    #[cfg(debug_assertions)]
    #[should_panic(expected = "metadata key")]
    fn undeclared_metadata_key_panics_in_debug() {
        let tel = ConfiguredTelemetry::new();
        tel.attach(&[], Box::new(validator_with_test_spec()));
        tel.execute(
            &["fz", "test", "done"],
            &Measurements::new(),
            &crate::metadata! { mystery: "oops" },
        );
    }

    #[test]
    fn span_events_are_not_validated() {
        use crate::telemetry::TelemetryExt;

        // A span name not in any spec must NOT panic — span events bypass
        // validation.
        let tel = ConfiguredTelemetry::new();
        tel.attach(&[], Box::new(SchemaValidator::new(vec![])));
        let _span = tel.span(&["fz", "no_spec", "span"], Metadata::new());
        drop(_span);
    }

    #[test]
    fn multiple_specs_all_consulted() {
        const OTHER_EVENT: EventDecl = EventDecl::new(
            &["fz", "other", "thing"],
            Level::Debug,
            "Another event.",
            &[],
            &[],
        );
        const OTHER_SPEC: Spec = Spec::new("other", "Other spec.", &[OTHER_EVENT]);

        let tel = ConfiguredTelemetry::new();
        tel.attach(
            &[],
            Box::new(SchemaValidator::new(vec![&TEST_SPEC, &OTHER_SPEC])),
        );
        // Both specs' events must be accepted without panic.
        tel.execute(
            &["fz", "test", "done"],
            &Measurements::new(),
            &Metadata::new(),
        );
        tel.execute(
            &["fz", "other", "thing"],
            &Measurements::new(),
            &Metadata::new(),
        );
    }
}
