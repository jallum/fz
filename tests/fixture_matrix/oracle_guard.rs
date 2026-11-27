//! Guards on `ORACLE=regen`: a golden is written only from an oracle that
//! answers the same way twice, and only for a fixture the caller named.

use super::*;

/// The one output Elixir printed twice, or the failure naming the fixture and
/// both outputs when the two runs differ.
pub(super) fn require_one_answer(fixture: &FixtureCase, first: String, second: String) -> Result<String, String> {
    if first == second {
        return Ok(first);
    }
    Err(format!(
        "{}: the Elixir oracle answered twice differently, so no golden is written; \
         normalize what Elixir leaves unordered (`inspect(x, custom_options: [sort_maps: true])`, `Enum.sort`)\n\
         --- first run\n{first}--- second run\n{second}",
        fixture.display_path().display()
    ))
}

/// `ORACLE=regen` rewrites goldens, so it must name the fixture it rewrites.
pub(super) fn require_named_fixture_for_regen(mode: OracleMode, only: Option<&str>) -> Result<(), String> {
    if matches!(mode, OracleMode::Regen) && only.is_none() {
        return Err(
            "`ORACLE=regen` rewrites goldens from Elixir's output and needs `ORACLE_FIXTURE=<stem>` \
                    naming the fixture to regenerate"
                .to_string(),
        );
    }
    Ok(())
}
