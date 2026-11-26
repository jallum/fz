Each `<ticket>.moves` file here is one change's movement of the distiller's
compile ceilings in `tests/distill_telemetry_test.rs`. A part's ceiling is its
`CEILINGS` base plus every file's delta for that part.

A file holds lines of `<part> <signed delta>`, the part named as in `CEILINGS`,
and `#` lines saying why the spend moved:

    # Enum.reduce over a list folds the list directly; rise accepted by the user
    largest drive requests +663
    derivations +430

A delta is the change's measured figure minus the ceiling it was measured
against. A rise is accepted by the user before its file lands; a fall needs no
one's acceptance. Two changes in flight add two files and never edit the same
line. Folding sums every file into `CEILINGS` and deletes the files.
