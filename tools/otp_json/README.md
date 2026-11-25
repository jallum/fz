# OTP json.erl on fz

`fixtures/01860_otp_json_erl_runs_unchanged.fz` contains `OtpJSON`, a line-for-line port of OTP 28.3 (stdlib-7.2) `json.erl` into Elixir syntax, followed by a deterministic corpus. It is an `oracle: self` fixture: Elixir runs the file and owns `expected.txt`, and the fixture matrix runs the same file on interp, run and build.

The port keeps every function, clause, argument and variable name of `json.erl`. It keeps the improper-list stacks and iodata, `throw`/`catch`, the guard macros, the 8-byte fast path, and the real BIFs. The only changes are the ones Elixir syntax forces, and each one carries a `# erl:` comment quoting the original line. Where fz cannot run the port, the gap is a ticket under fz-mue, never a change to the port.

- `difftest.exs` compares the port against OTP's `:json` on the BEAM, case by case and outcome by outcome: 113,386 cases. Run it from the repository root with `elixir tools/otp_json/difftest.exs`. It loads the port from the fixture.
- `gen_guards.py` prints the `defguardp` block of `json.hrl` in Elixir form. The long `===` chains in the port are its output.

The corpus prints every outcome for small groups, and a count plus a digest for large ones. To see every outcome, run `elixir <fixture> full` or `fz2 run <fixture> full`, then diff the two outputs.

The corpus holds no call whose argument lies outside the callee's `@spec`. fz refuses such a call at compile time (`error[spec/violation]`), where the BEAM compiles it and raises at run time, so a corpus that made those calls could not compile on fz. The misuse cases live in two places: `difftest.exs` still runs them against `:json` on the BEAM, and fixtures `01861` to `01866` each hold small copies of the specced port functions and one out-of-spec call, and pin the `spec/violation` diagnostic on interp, run and build. The kinds are a binary to `encode_integer/1`, a list to `encode_binary/1`, an atom to `decode/1` and to `decode/3`, and an atom as the encoder of `encode/2` and `format/2`.
