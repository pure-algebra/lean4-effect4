# Seat APP brief: `apps/todo/`, the to-do on SQLite, each run checked by Lean (2026-10-13)

Status: brief (history, not authority). Coordinator: the main session. Branch `seat/app`,
worktree `~/Dev/lean4-effect4-app`, base: the coordinator's head when the worktree was made.

## The one goal

Slice V4 of decisions row 378 (16) and (15): a real application at `apps/todo/`. It runs the
to-do's emitted Effect service against SQLite and records each request. Lean then decides each
recorded run's checks, so the to-do's proved claims hold of that run where the checks pass. Read
the lowering note's §6 (`docs/research/2026-10-13-lowering-vertical-slice/README.md`), then seat
SVC's receipt (`docs/research/2026-10-13-seat-svc-receipt.md`, E4): E4 already does this against
a scripted host.

## What to land, in order

1. **The application.** `apps/todo/` holds:
   - the emitted service, written by Lean (`harness/truth/service/EmitTodo.lean`, reused or moved,
     never copied);
   - `SqliteTodoRepo`, a layer that provides `TodoRepo` over `bun:sqlite` (Bun's built-in
     module, so nothing is installed). A failure of SQLite is the row's declared error;
   - a small front: a Bun HTTP server or a command line, one request per entry (`add`, `list`,
     `complete`, `remove`);
   - a recorder that writes one record per request: the entry, its arguments, each host call's row
     and request, the completion, and the exit. Reuse the keyed lane's recorder
     (`harness/truth/session/keyed-recorder.ts`); write no second one.
2. **The checker.** Lean reads a session's records and decides, per request, the five checks of
   the note's §6.1, with the model's state threaded across requests for `agrees`. E4's
   `service-checks` (`harness/truth/session/Keyed.lean`) holds most of this logic. Move what both
   need into one module, and make `Keyed.lean` and the new checker use it. A second copy is a
   defect.
3. **A run and its controls.** From an empty database, a script of requests, checked by Lean:
   every check passes. Red controls: an adapter that forgets a write fails `agrees`, as the
   `forgetful` reactor does today. An adapter whose insert ignores the title fails `conforms`.
4. **The gate.** SQLite is an outside implementation, so the run is a behaviour gate. Prefer to
   extend `make check-host-protocol` over a new target. If a new target is clearer, add one line
   to the `Makefile` and say why in the receipt. Add no wrapper script.

## Placement (AGENTS.md, Trust)

The checker decides premises and states no theorem: each decision is graded `validated` in the
claim record (`Test/Dogfood/Application.lean`). Its consumers are `conforms_sat` and
`agrees_hostRun` (`src/Effect4/Laws/Program/Validated.lean`). Not established: anything of a run
that no check read; SQLite's behaviour beyond the recorded completions; concurrency between
requests.

## Rules

- Reuse first. The receipt lists what you reused. A duplicate is a defect.
- Seat READ owns `src/Effect4/Codegen/{Read,Classes,Types}.lean`,
  `src/Effect4/Laws/Api/ModuleReadable.lean` and `ts/eff/read.ts`. Seat IMPOSE owns
  `src/Effect4/Program/Authoring.lean`, `src/Effect4/Program/Authoring/Application.lean`,
  `src/Effect4/Codegen/Print.lean`, `Test/Dogfood/Scenario/Todo.lean`,
  `src/Effect4/Library/Ref/`, `src/Effect4/Laws/Library/Ref/` and
  `src/Effect4/Laws/Program/Block.lean`. Do not edit them. IMPOSE will change the to-do so that
  `list` reads through a cache; your app writes its service from Lean at each run, so it follows.
  Never edit `lakefile.toml` or `docs/core/decisions.md`.
- Root imports (`src/Effect4.lean`, `src/Effect4/Laws.lean`, `Test/All.lean`) only by appending
  at the end.
- Build only through `~/Dev/lean4-effect4/scratch/lean-slot.sh lake build <Module>`. Never a bare
  `lake build`, never `lake build Test`.
- TypeScript: run bun only as `bun --no-install`. Import packages only by directory from the
  linked `harness/truth/node_modules` or `ts/eff/node_modules`, and print the effect version. tsgo
  7 is the one compiler. No downloads; `bun:sqlite` is built in.
- Proofs, where any: aesop and its banks; `simp only [...]`; no `simp_all`, `first`, `try`. Audit
  touched Lean modules with `#axiom_audit` at `[propext, Quot.sound]`.
- Commit on `seat/app` by named paths, each item as it works. Never push. Never `2>/dev/null`.

## The receipt

`docs/research/2026-10-13-seat-app-receipt.md` (force-added): the one thing to know before
merging, base and head, changed files, commands and results, the versions (effect, bun, tsgo,
SQLite), open obligations, and whether any evidence is bounded or host-only.
