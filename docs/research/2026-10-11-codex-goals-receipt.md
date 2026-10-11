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
