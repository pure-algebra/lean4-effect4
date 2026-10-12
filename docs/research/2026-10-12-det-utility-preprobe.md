# Pre-probe: what the schedule-independence work (DET) is worth to the project (2026-10-12)

Status: research note (history, not authority). A read-only pre-probe for the owner's grill.
Base `c7504d691` on `refactor/phase1-phase3`. No `lake` ran. Sources: the
[schedule independence note](2026-10-10-schedule-independence/README.md) and its `brief.md`;
Codex's packet [deterministic-fragment-review](2026-10-10-deterministic-fragment-review/README.md)
(`acf7cf413`), with its `REVIEW.md` and `PROOF-DAG.md`; the held commit `d064ab3b2` on branch
`land/backlog-1012`; `docs/core/system-map.md`; `docs/DESIGN-BASIS.md` DB-03; `AGENTS.md`.

## Know this first

- **No gate or theorem needs a schedule-independence result today.** The truth lane compares one
  schedule row by row: `flushAllState` transcribes `Scheduler.ts`'s FIFO order, and 43 of its 93
  programs name a fork (a substring count over `harness/truth/corpus.json`). The OCaml route drives three engines from one tape (`ocaml/engine/e4_diff.mli`).
  Both use route 1, a fixed tape.
- **It is off the M5 → M7 spine.** Codex's `PROOF-DAG.md` says that schedule independence
  "neither replaces that chain nor follows from it".
- **AGENTS.md names two routes to determinism, and only the first is used.** Route 1, a fixed
  decision tape, carries `run_eq_ref`, `run_eq_meaning`, `replay_unique` and `Beh`. Route 2, "a
  fragment with no decision source", has no stated predicate or theorem. `Straight`
  (`src/Effect4/Program/Fragment.lean`) refuses forks and yields, which is near it.
- **My held commit `d064ab3b2` has four faults that Codex's review named before I wrote it.**
  - DET-OW-02: `decisionStep` is the raw decision relation. A fire on an absent owner, a
    `yieldVerdict` and `installMiddleware` are always enabled (`stepDecisionState`,
    `src/Effect4/Machine/Fibers.lean`). So no live machine is `Terminal`, and
    `complete_unique` never applies to it. The connector `replayEval_of_run` is true, but it
    unlocks nothing.
  - DET-OW-03: the battery's `explore` calls a machine with nothing armed `complete`. A machine
    that waits on a promise or a host answer is also unarmed and not finished.
  - DET-OW-04: the battery observes the root's exit and the reference heap. The machine's own
    observation, `obs` (`src/Effect4/Laws/Machine/Behaviour.lean`), holds every fiber's exit
    and the whole store.
  - DET-OW-01 is met: `extends_all`, `complete_unique` and `bounded` keep the `Equivalence R`
    premise.
- **Codex proposes a different second step.** Its proposal is a syntactic fragment over
  `Api.Typed` with exact `obs`, not the brief's DET-3, which is a name quotient over the whole
  machine. The fragment is a finite parallel phase:
  - workers with private cells, shared read-only cells, or shared additions that return unit;
  - the parent joins every worker before it reads a shared cell.

  Its probe accepts 7 author programs and refuses 17. Each accepted program's explored tapes
  (2 fire tapes, and 255 with up to two preemptions) end at one `obs`. Those are finite checks.

## The utility, against the project's goal

The goal (`docs/core/system-map.md` §1): Effect's runtime reified in Lean as a general model with
defined semantics, typed programs as data, and an agent that authors them.

| What DET would give | Who uses it | Today |
| --- | --- | --- |
| A located answer to an author's question "does this result depend on the schedule?", on `Api.Typed` | the authoring line: the session tool, MCP, R14's live loop | no consumer; Codex's D4 is editor feedback |
| A canonical run that stands for every schedule, on the fragment | the truth lane and the OCaml route, if a scheduler stops being FIFO (4.0.1, or domains) | inference: a latent consumer; FIFO is transcribed today |
| Completion with no fairness premise, on the fragment (`fire-tapes-bounded`) | R12-c, `fair-scheduling` | R12-c waits on a ruling; the claim is `.absent` |
| A third determinism route in AGENTS.md and DB-03 | every determinism claim on a concurrent program | none is stated |

The cost, from Codex's estimates (planning, not measured):

- D0: correct the note and land the generic theorem with controls, 0.5 to 1 day;
- D1: the fragment checker with located refusals, 1 to 2 days;
- D2: the store laws and the final-observation proof, 3 to 5 days;
- D3: the work measure and the canonical-driver connector, 2 to 3 days.

The brief's DET-3 needs three lemmas that are not built: `names-equivariant`, which its note
calls the largest, `trace-write-only` and `armed-order-irrelevant`. The store's name laws
(`src/Effect4/Laws/Store/Names.lean`) cover `Store.Val` only.

## Recommendations for the grill

1. **The third route** (meaning). Admit schedule independence as a route, but only for a named
   observation and a named fragment. Full meaning stays relational. Write it in DB-03 and
   AGENTS.md when a theorem first needs it, not before.
2. **The observation** (meaning). Exact `obs` for the first fragment, with names allocated in
   program order. The name quotient waits. Two reasons:
   - allocation counts differ between schedules, and that is no permutation (DET-OW-05);
   - `getId` shows a fiber id as a number.
3. **The route of the proof** (representation). Codex's syntactic fragment over `Api.Typed`, not
   the whole-machine quotient. It needs no name quotient, it gives an author a located refusal,
   and it adds no language.
4. **The order** (domain). Now: D0, which repairs `d064ab3b2` by the review (an enabled-fire
   relation, `finished` apart from unarmed, `obs`). Merge it, and split `keys-once` out. D1 to D3
   wait until the authoring line (MCP, R14) asks for the analysis. The spine and the SVG port
   come first.

## Placement and limits

- Concept: `reactive-scheduling`. The requirement is R12; DET-1's tag places
  `replayEval_of_run` there. No registry claim is proved by it on the machine.
- Evidence kinds: Codex's counts are its probe's finite checks. The consumer table is read from
  sources; the latent consumers are inference.
- Not established: any machine theorem of schedule independence; Codex's day estimates.

## The owner's rulings (2026-10-12)

Every recommendation was taken; decisions row 361 records them. The third route holds for a named
observation on a named fragment and enters DB-03 with its first theorem. The observation is
exact `obs`. The proof route is Codex's checked fragment over `Api.Typed`. D0 lands now; D1 to D3
wait for the authoring line.
