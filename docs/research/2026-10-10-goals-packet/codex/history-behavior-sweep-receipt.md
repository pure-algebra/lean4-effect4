# History proof behavior sweep

Both affected external comparisons pass at `70f6d1c7b`.
The proof goals remain open where their receipts name them.

## Command

`make check-truth check-host-protocol`

The command exits with status zero.
The exact output is `HistoryBehaviorSweep.log` in this folder.
The command regenerates its inputs and leaves the tracked tree unchanged.

## Evidence and scope

The truth comparison checks 81 programs and retains 10 signed divergences.
The keyed host comparison checks 57 runs and 52 admitted printed programs.
The scenario comparison performs 72 scripts in 267 actual rc.112 runs.
It retains 13 scripts without a host run and 44 red controls.
The host protocol tests pass: 56 tests and 487 assertions.

The scenario report retains incomplete timeout observations for timers and forms.
Those limits remain in the measured output; this receipt claims no wider timeout comparison.
These finite comparisons prove no universal scenario assertion.
They introduce no new proof axiom and discharge no planned goal.

## Deferred checks

This sweep runs the two affected behavior gates after the shared histories land.
It does not run the whole battery, whole-tree axiom gate, policies or document ratchets.
