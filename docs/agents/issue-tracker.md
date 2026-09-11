# Issue tracker: this repo's own registers and research notes

There is no external tracker. Work is tracked where the estate already tracks it, and the
engineering skills adapt to that; nothing new is created for them.

| what | where | who writes |
| --- | --- | --- |
| open design questions | `docs/DESIGN-ISSUES.md`, rows `DI-nn`; status open → recommended → ruled → basis | the owner rules; an agent proposes in a research note and cites the row id, and once the owner has ratified, writes the row and the tracked place it cites in the same commit |
| settled decisions | `docs/DESIGN-BASIS.md`, rows `DB-nn` | the owner |
| frozen contracts and falsifiers | `Test/contracts/*.contract.md` | a slice, landed by the coordinator |
| declaration-changing counterexamples | `Test/Counterexamples/REGISTER.md` | a slice |
| history: plans, scouts, grills, receipts | `docs/research/<date>-<slug>.md` (gitignored, synced between machines directly) | anyone; a dated note is the deliverable of a scout or a grill |
| truth | the Lean model under `src/Effect4/` and `Effect4.Laws`, the algebra in the `effects` package, the history above, and a little of the lineage in `~/Dev/foldlab` | the build and the axiom gate |

## Conventions

- A ruling is not made until it is written into a tracked file (the register's first rule).
  A research note proposes; the owner ratifies; the register records, in the same commit as
  the tracked place the row cites.
- Rows are cited by id, never by line. Ids are never reused.
- An agent does not edit `docs/DESIGN-ISSUES.md` or `docs/DESIGN-BASIS.md` on its own
  initiative. After the owner's ratification it writes the ruling into the row and the tracked
  place itself (owner correction, 2026-09-11).

## When a skill says "publish to the issue tracker"

Write a dated research note under `docs/research/`. If the content is a decision the owner
has made, say which `DI` or `DB` row it belongs to so the owner can write it in.

## When a skill says "fetch the relevant ticket"

Read the `DI` row by id, the research note by path, or the wayfinder ticket by number.

## Wayfinding operations

Used by `/wayfinder`. One map per effort, kept inside the effort's own research note; no
separate tracker files, no labels, no board.

- **Map**: a `## Wayfinder map` section in the effort's goal note. It stands in for the
  `wayfinder:map` label. Current effort: `docs/research/2026-09-10-fractal-cas-architecture.md`
  §8, with the unified system of `2026-09-10-program-as-schema.md` as the larger goal.
- **Child ticket**: a `### T-nn <title>` subsection under `## Tickets` in the same note,
  numbered from `T-01`. Its first line carries `Type:` (`research` / `prototype` / `grilling`
  / `task`, standing in for `wayfinder:<type>`), `Status:` (`open` / `claimed (<seat>,
  <date>)` / `resolved (<date>)` / `out of scope`) and `Blocked by:` (ticket numbers, a `DI`
  row id, or `none`). The body is the question; the answer is appended under it on
  resolution.
- **Frontier**: the tickets that are open, unblocked and unclaimed, taken in number order.
- **Claim**: set `Status: claimed (<seat>, <date>)` before any work.
- **Resolve**: append the answer under the ticket, set `Status: resolved (<date>)`, and add
  one line to the map's "Decisions so far". If the answer is a ruling, it is proposed to
  the owner by `DI` row id and written into the row once ratified.
- **Blocking**: the `Blocked by:` line. There is no native dependency view, so the ticket
  list in the note is the visual.
- **Research tickets** may be resolved by a subagent that writes its findings to
  `docs/research/<date>-wayfinder-<slug>.md` and links the note from the ticket.
