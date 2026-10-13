# Seat brief: the host session's face, slices DM1 to DM4 (seat LIVE)

Status: brief (history, not authority). 2026-10-13. The coordinator dispatches it when a code
slot frees.

**The one thing to know first.** Decisions row 326 ruled the session's face, the deep module
`Live` with `open`, `start`, `feed` and `view`, and the session note planned it in seven slices
(`docs/research/2026-10-07-session-api-design.md`, commit `030eefa40`). Only DM5 landed
(`5c01db4a3`). Row 373 (1) puts DM1 to DM4 first in the non-visual backlog: MCP's runs, a run
view with host replies, and editing beside running all wait on it.

## Read first

- The session note, whole; decisions rows 326, 333 (3) and 373 (points 1, 2, 5, 8 and 12).
- Seat BACKLOG's deep dive `docs/research/2026-10-13-backlog-deep-dive/README.md`: the host
  session's sections, the ranked list's first slice, and §6.1's placement of `view_funded`.
- The tree as it stands: `Run` (`src/Effect4/Run/`), `src/Effect4/Api/HostSession.lean`
  (`Session`, `submit`, `applyReply`, `retire`, `Refusal`), the events in
  `Test/Dogfood/Scenario.lean` (`Sel`, `Move`), and the laws `session_eq_ref`
  (`src/Effect4/Laws/Api/SessionRef.lean`) and `reply_commute`
  (`src/Effect4/Laws/Api/HostSession.lean`).

## What to build, in order

1. **DM1.** The session's events move into the library; the test module imports them.
2. **DM2.** `Live`, with `Live.open` and `Live.start`, over the existing `Run`; no second
   representation of a session (the representation rules in `AGENTS.md`).
3. **DM3.** One `View` with each call's checked instance (the live call view, row 373 (12);
   HC-1 folds into it), and the header's `profile` renamed `binding` with its codec (row 326 (4)).
4. **DM4.** `applyReply` keeps a `funded` bit for an applied step that ran out of fuel, and
   `view_funded` states that the view's flag agrees with `Run.funded`. Place it first (the five
   things of `AGENTS.md`, "Trust"); the deep dive's §6.1 gives its fields.

Each slice lands as its own commit after a narrow build and `#axiom_audit` of the modules it
touches. DM3 moves codec ordinals and DM4 changes `applyReply`, which about seven laws unfold:
re-prove them in place, never weaken them. Run the behaviour gates the change reaches
(`make check-host-protocol` at least; `AGENTS.md`, "Working").

## Boundaries

- Worktree: `git -C ~/Dev/lean4-effect4 worktree add ~/Dev/lean4-effect4-live -b seat/live
  refactor/phase1-phase3`, then `cp -c -R ~/Dev/lean4-effect4/.lake ~/Dev/lean4-effect4-live/.lake`.
  Never copy `docs/research`.
- Edit `src/Effect4/Api/**`, `src/Effect4/Run/**`, `src/Effect4/Laws/Api/**`, `Test/**` and the root
  imports at their end. Never edit `lakefile.toml`, `docs/core/decisions.md` or `tools/Tools/View/`.
- Build with `LEAN_NUM_THREADS=2`, one `lake` at a time, narrow. Commit by named paths on
  `seat/live`. Never push or merge. Stop under 8 GiB free.
- Stop at a question of meaning or at about six hours. The receipt
  `docs/research/2026-10-13-seat-live-receipt.md` (force-added) names first the one thing to know
  before merging, then the base and head, the files, the commands and results, the axiom output,
  each placement, and what DM5 to DM7 still need.
