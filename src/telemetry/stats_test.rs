use super::*;
use crate::telemetry::{ConfiguredTelemetry, Metadata, Telemetry as _};

#[test]
fn counts_events_by_name() {
    let tel = ConfiguredTelemetry::new();
    let stats = StatsHandler::new();
    tel.attach(&[], stats.handler());

    tel.emit(&["fz", "lexer", "pass"]);
    tel.emit(&["fz", "lexer", "pass"]);
    tel.emit(&["fz", "parse", "done"]);

    let counts = stats.counts();
    assert_eq!(counts.get("fz.lexer.pass"), Some(&2));
    assert_eq!(counts.get("fz.parse.done"), Some(&1));
    assert_eq!(stats.total(), 3);
}

#[test]
fn span_events_not_counted() {
    use crate::telemetry::TelemetryExt;

    let tel = ConfiguredTelemetry::new();
    let stats = StatsHandler::new();
    tel.attach(&[], stats.handler());

    let _span = tel.span(&["fz", "test", "span"], Metadata::new());
    drop(_span);

    tel.emit(&["fz", "test", "event"]);

    let counts = stats.counts();
    assert_eq!(counts.get("fz.test.event"), Some(&1), "event should be counted");
    assert_eq!(counts.get("fz.test.span"), None, "span events must not appear");
    assert_eq!(stats.total(), 1);
}

#[test]
fn empty_bus_has_empty_counts() {
    let stats = StatsHandler::new();
    assert!(stats.counts().is_empty());
    assert_eq!(stats.total(), 0);
}

#[test]
fn sorted_alphabetically() {
    let tel = ConfiguredTelemetry::new();
    let stats = StatsHandler::new();
    tel.attach(&[], stats.handler());

    tel.emit(&["z", "last"]);
    tel.emit(&["a", "first"]);
    tel.emit(&["m", "middle"]);

    let keys: Vec<_> = stats.counts().into_keys().collect();
    assert_eq!(keys, vec!["a.first", "m.middle", "z.last"]);
}
