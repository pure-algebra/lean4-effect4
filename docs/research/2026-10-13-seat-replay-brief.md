# Seat brief: one checked replay route (seat REPLAY)

Status: brief (history, not authority). 2026-10-13. Obligation O7 of
`docs/research/2026-10-13-authoring-obligations/README.md`.

**The one thing to know first.** Row 373 (8) rules it: `Typed.replay` replays the session's
journal, checked at each call's instance (row 98). The raw `Api.replay` stays as a named test
entry, and `replayAdmitted` goes. Today `Typed.replay` (`src/Effect4/Api.lean`) replays raw
decisions, so it applies a host answer that no check admits. Seat LIVE landed the session face
today (`Live.open`, `Live.start`, `Live.feed`, `Live.view`; `src/Effect4/Run/Live.lean`), with
`Live.journal_replays` and `session_eq_ref` at `Live` (`src/Effect4/Laws/Api/Live.lean`).

## Read first

- Decisions rows 98, 323 (8), 326 and 373 (points 1, 2 and 8); `docs/core/host-boundary.md` §4.6.
- Seat LIVE's receipt (`docs/research/2026-10-13-seat-live-receipt.md`), its DM5 to DM7 list.
- Seat BACKLOG's deep dive (`docs/research/2026-10-13-backlog-deep-dive/README.md`): its host
  session section, its §6.1 placement of `replay-at-call-instance`, and its question 3.
- The tree: `Api.replay`, `replayChecked`, `replayAdmitted` and `Typed.replay` in
  `src/Effect4/Api.lean`; `Runner.replay` (`src/Effect4/Api/Runner.lean`); `Live.feed`.

## What to build, in order

1. **The route.** `Typed.replay` takes a session header and a `Runner.Command` journal, and replays
   it through `Live.feed`, with both budgets and phases that can refuse. A host answer is applied
   only after the session admits it at the call's instance.
2. **The law.** Place `replay-at-call-instance` first (the deep dive's §6.1 gives its fields): a
   replayed run's applied answers fit their call's checked instance, on rows whose answer column
   allocates nothing. Prove it from the session's admission laws (`preflight_success_prepared_fits`,
   `instance_prepared_success`) and `Live.journal_replays`; state nothing that they already state.
3. **The callers move.** Every caller of `replayAdmitted` moves to `Typed.replay`, then
   `replayAdmitted` goes. `Api.replay` stays, named a test entry in its docstring.

## Rules from the last landings

1. **Reuse, never a second mechanism.** The replay is `Live.feed` folded over the journal, not a
   new loop. A law already proved is applied, not restated.
2. **Every reader of a changed definition builds.** List each reader with `git grep` and build them
   all before a commit. Seat LIVE missed `HostTimeoutApplication`, and the merge found it.
3. **No new gate**, ratchet or pinned count (row 375). Battery lines are readers and controls
   (row 301). One red control: a journal whose answer misfits its call's instance is refused.
4. **Run the behaviour gate the change reaches**: `make check-host-protocol`, through the slot.

## Boundaries

- Worktree: reuse seat LIVE's, `~/Dev/lean4-effect4-live` (its build products are of this cone):
  `git -C ~/Dev/lean4-effect4-live switch -c seat/replay refactor/phase1-phase3`.
- Edit `src/Effect4/Api.lean`, `src/Effect4/Api/**`, `src/Effect4/Run/**`, `src/Effect4/Laws/Api/**`,
  `src/Effect4/Laws/Run/**`, `Test/**` and the root imports at their end. Propose registry claims
  and an `api-surface.md` edit in the receipt. Never edit `lakefile.toml`, `docs/core/**`,
  `tools/ProofGraph/Registry.lean`, `src/Effect4/Laws/Program/**` or `tools/Tools/View/`.
- Run every `lake` and `make` through `/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh`,
  narrow. Commit by named paths on `seat/replay`. Never push or merge. Stop under 8 GiB free.
- Stop at a question of meaning or at about six hours. The receipt
  `docs/research/2026-10-13-seat-replay-receipt.md` (force-added) names first the one thing to know
  before merging, then the base and head, the files, the commands and results, the axiom output
  (`#axiom_audit`), the placement, and what row 99 (typed answers on data rows) now needs.
