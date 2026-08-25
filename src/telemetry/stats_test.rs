use super::*;
use crate::telemetry::{ConfiguredTelemetry, Metadata, RawSpanStop1 as _, TelemetryExt as _};

#[test]
fn counts_events_by_name() {
    let tel = ConfiguredTelemetry::new();
    let stats = StatsHandler::new();
    stats.install(&tel);

    tel.event_lazy(&["fz", "lexer", "pass"], Metadata::new);
    tel.event_lazy(&["fz", "lexer", "pass"], Metadata::new);
    tel.event_lazy(&["fz", "parse", "done"], Metadata::new);

    let counts = stats.counts();
    assert_eq!(counts.get("fz.lexer.pass"), Some(&2));
    assert_eq!(counts.get("fz.parse.done"), Some(&1));
    assert_eq!(stats.total(), 3);
}

#[test]
fn raw_lifecycle_counts_events_starts_stops_and_exceptions() {
    let tel = ConfiguredTelemetry::new();
    let stats = StatsHandler::new();
    stats.install(&tel);

    let value = 1_u64;
    tel.raw_event1(&["fz", "test", "event"], &value);
    tel.raw_span1_1::<u64, u64>(&["fz", "test", "span"], &value)
        .stop1(&value);
    tel.raw_span1_1::<u64, u64>(&["fz", "test", "failed"], &value)
        .exception();

    let counts = stats.counts();
    assert_eq!(counts.get("fz.test.event"), Some(&1));
    assert_eq!(counts.get("fz.test.span.start"), Some(&1));
    assert_eq!(counts.get("fz.test.span.stop"), Some(&1));
    assert_eq!(counts.get("fz.test.failed.start"), Some(&1));
    assert_eq!(counts.get("fz.test.failed.exception"), Some(&1));
    assert_eq!(stats.total(), 5);
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
    stats.install(&tel);

    tel.event_lazy(&["z", "last"], Metadata::new);
    tel.event_lazy(&["a", "first"], Metadata::new);
    tel.event_lazy(&["m", "middle"], Metadata::new);

    let keys: Vec<_> = stats.counts().into_keys().collect();
    assert_eq!(keys, vec!["a.first", "m.middle", "z.last"]);
}
