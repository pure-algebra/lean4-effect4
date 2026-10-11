# Scenario goal landings

The first landing adds the common proof frame. It closes no original application goal yet.
Every original scenario proposition remains unchanged.
The timeout race still needs repair before its retry proposition can hold.

## Branch and commits

Base: `b74ebab6f2b3f39f0c60d04b25014488b274f197`.
Branch: `codex/last-planned-goals`.
The commit containing this receipt records the first landing.
No commit is pushed.

## L0: the common run frame

Changed files:

- `src/Effect4/Laws/Run/Frame.lean`
- `Test/Dogfood/Scenario/Frame.lean`
- `docs/research/2026-10-10-goals-packet/PLAN.md`
- `docs/research/2026-10-10-goals-packet/codex/AuditFrame.lean`
- This receipt.

The proposed claim `run-history` belongs to `host-session-protocol`, with role compatibility and requirement R13.
`Run.reached_history` is its pointer.
`Run.Keeps` owns row preservation with an explicit permission predicate.
`Run.Allowed` follows that predicate at intermediate runs.
The funded adapter and the unrestricted adapter use that same law.
`Run.HistoryOf` uses the existing `Machine.Lift.Admitted` history and the exact reply admission.
Its empty-table instance excludes every direct answer.
`Accepted.host_request` establishes that an accepted answer names a parked host call.
`HistoryOf.reachable` supplies the weaker raw reachability when a consumer needs it.

The scenario adapters serve the thirteen application goals over scripts.
These laws transfer an invariant supplied by their caller.
They establish no progress, resource liveness or outside runtime behavior.

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Run.Tape Effect4.Laws.Program.Guard.Core ProofGraph.AxiomAudit Test.Dogfood.Scenario` | Pass, 1025 jobs |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Run.Frame Test.Dogfood.Scenario.Frame` | Pass, 1020 jobs |
| `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AuditFrame.lean` | Pass |

```text
#axiom_audit: 107 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

A fixture proves that a raw direct-answer row keeps the machine unchanged.
The packet's machine-level cleanup counterexample therefore requires no change to the scenario proposition.
The earlier fixture build failed on namespace references. The saved correction passes the repeated build and audit.

## Deferred gates and obligations

Root import closure and semantics registration wait for the structure integration pass.
No executable definition changes in L0, so L0 reaches no outside behavior gate.
No whole battery, whole-tree audit, ratchet or documentation sweep runs during these landings.
All fourteen original scenario obligations remain open after L0.
The machine lane's finite comparison chooses the next proof structure and proves no application invariant.

## Proposed decisions

Preserve the cleanup proposition and use admitted machine histories in its proof.
Preserve stale reply provenance, the routing budget, every unauthorized script and every job count.
Repair the timeout form while retaining the original retry proposition and its counterexample evidence.
Use shared command laws with program assertions at every command boundary.
The plan records these recommendations. It changes no decision register.

## L4: Atomic structure

The original three store clauses now use the shared history and two explicit obligations.
They remain proved modulo those obligations. They are not completed claims.
The capacity clause uses `Program.HeapSites.heap_sites_keep`.
The count and committed-state clauses use `Atomic.Store.shop_stages`.
The cleanup clause remains its original planned goal.
Their propositions, source program, scripts and observations remain byte-identical.
A comparison against the base commit verifies that extraction.

Changed files:

- `src/Effect4/Laws/Program/HeapSites.lean`
- `Test/Dogfood/Scenario/Atomic/Model.lean`
- `Test/Dogfood/Scenario/Atomic/Store.lean`
- `Test/Dogfood/Scenario/Atomic.lean`
- `docs/research/2026-10-10-goals-packet/codex/AuditAtomic.lean`
- The plan and this receipt.

The write-site census and the request-stage observation algebra compile from the retained probe.
They use `Run.ControlHistory` and `Author.build_retains`; no second history or author-build law remains.
The plan records both obligations' placement, scope, consumers and exclusions.

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Atomic` passes with 1033 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AuditAtomic.lean` passes.

```text
#axiom_audit: 464 declarations within [propext, Quot.sound], 4 of them modulo planned goals; 3 planned goals
```

The first integration build found a missing binder-table import and a namespace collision.
Both are repaired before the passing build.
The unchanged scenario gate rejects planned subgoals beneath proved clauses.
An exact expected-error guard retains that rejection until the final gate repair.
The guard fails if the diagnostic changes; the proof declarations still compile and undergo the axiom audit.
The final pass must admit a goal only when a named clause reaches it.

## L1, L2, L3 and L5 integration

The universal Workers and QueueWorkers elaboration equations retain every job count.
`Author.build_retains` identifies the built program and table.
`Program.Placement` classifies source paths; `Scenario.Programs` proves the actual acquisition sites.
The symbolic lane's audit reports 99 declarations, no modulo declarations and no planned goals.
Its receipt is `docs/research/2026-10-10-goals-packet/codex/symbolic-programs-receipt.md`.

`Run.Journal` proves key uniqueness and retirement clauses for every program.
The original reply-value provenance clause remains separate.
The command law modules compile exact transitions for arbitrary fibers at a synchronous store operation.
They establish neither source provenance nor a whole-run application invariant.

The original `Workers.releases_once` now consumes `Workers.Assertions.history` and its concrete log reading.
Its proposition remains unchanged, including all budgets and all scripts.
The source assertions consume the actual acquisition sites and their universal placement proofs.
The three remaining goals are registration preservation, release debit preservation and log debit preservation.
Middleware and yield edits are proved leaves; admitted histories retain the original command boundaries.

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers` passes with 1039 jobs.
`LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/AuditWorkers.lean` passes.

```text
#axiom_audit: 151 declarations within [propext, Quot.sound], 4 of them modulo planned goals; 3 planned goals
```

The original Workers gate rejection is retained under an exact expected-error guard, as Atomic's is.
Its final repair must follow a named clause to each planned subgoal.
The original theorem is still modulo its three goals.

## Owner ruling and timeout evidence

The owner approves retry admission by the timeout form's completed outcome.
The four-attempt bound remains. The original host-reply premise is withdrawn for the retry clause.
This ruling is recorded here because the task forbids editing `docs/core/decisions.md`.
The final register proposal must quote the same ruling.
The old proposition and its Lean refutation remain retained evidence.

`codex/timeout-contract-decision.md` states the exact proposed observation and its evidence limits.
`RaceFirstYield.ts` and `RaceFirstYield.output.json` reproduce the issue on the pinned Effect runtime.
The four runs cover success and nonretryable failure, each with and without a forced yield.
Both yielded runs start a second attempt; both controls end after one.
The probe passes strict tsgo `7.0.0-dev.20260629.1` checking and runs under Bun.
It uses the real race and retry implementations, with a controlled callback timer.
It does not measure a physical clock or the exponential delay.
The waiting topology's cancellation defect remains separate from this contract amendment.

## Queue clause assembly

The four original queue clauses now consume the shared command assertions directly.
The assertion module repeats none of the original clause statements.
`jobs_step` serves held-job bounds, job accounting, and settled queue contents.
`rest_step` also serves accounting and settled contents.
`cleanup_step` serves cleanup counts.
All three remain planned goals.

`LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.QueueWorkers` passes with 1050 jobs.
The old scenario gate rejects these transitive goals, as expected.
A temporary exact diagnostic guard records that rejection until the planned gate repair.
`lake env lean docs/research/2026-10-10-goals-packet/codex/QueueAssertions.lean` passes.
Its audit reports 345 declarations, five modulo declarations, and three planned goals.
The audit checks the four supporting modules at `[propext, Quot.sound]`.
