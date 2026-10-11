# First-exit typing and target readers receipt

The source typing proofs and generated TypeScript readers include the first-exit action.
This slice depends on `6aba81de`.
The backend observer and declarative proof bridge remain in their assigned slices.

## Placement and reach

The checker agreement serves initial-algebras-folds, R14, at every signature as required by R1.
The signature extension serves R2.
The annotation and replacement proofs serve initial-algebras-folds, R14.
The generated target readers serve translation-simulation, R10.
The source position registry records the new entrant field as the same external hook as first-success entrants.
The static placement predicate serves scope-lifetime-finalization, R11.
Its runtime interpretation remains a separate obligation.
The consumers are source admission, typed printing and the first-exit timeout form.

## Checks

- The focused source proof builds pass for `Closed`, `Restrict`, `ExpandFix` and `Placement`, 310 Lake jobs.
- Those builds also check the changed checker, signature, annotation, replacement and splice dependencies.
- `Typing.Splice` adjusts its two numbered statement-list cases after the source constructor is appended.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Sources`: passes, three Lake jobs.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/FirstExitTypingAudit.lean`: passes.
- The audit walks 2554 declarations within `[propext, Quot.sound]`, with zero goals and zero declarations modulo goals.
- `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only ts`: passes.
- `node_modules/.bin/tsgo --noEmit -p tsconfig.json`: passes from `ts/eff`.
- The compiler reports `7.0.0-dev.20260629.1`.
- `bun test ./ingest/test/first-exit.test.ts ./ingest/test/printer.test.ts ./test/read.test.ts`: 162 pass, zero fail, 382 assertions.

These tests are finite source-reader checks.
They establish no target execution or machine observation claim.
The coordinator owns the outside behaviour gates.
