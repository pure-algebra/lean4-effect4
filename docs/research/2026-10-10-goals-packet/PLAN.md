# The final scenario goals

The implementation starts at `b74ebab6f2b3f39f0c60d04b25014488b274f197`.
The working branch is `codex/last-planned-goals`.
This plan records proposals and checked evidence. It records no owner ruling.

## Finishing criteria

Each original scenario proposition has a proof, or a retained counterexample with an explicit unresolved decision.
No proved claim depends on a planned goal.
Every helper serves a named scenario clause or registered property.
Every landing passes its narrow build and `#axiom_audit`.
The final gate pass checks every changed behavior and repairs affected imports and reports.
No work is pushed.

## Theory and ownership

The run frame belongs to `host-session-protocol`, requirement R13.
The proposed claim `run-history` has role compatibility and points to `Run.reached_history`.
Its module is `src/Effect4/Laws/Run/Frame.lean`.
`Run.Keeps.reached` and its row induction serve that claim and the session key ledger.
`HistoryOf` uses `Machine.Lift.Admitted` over the existing machine.
It retains reply admission at the program's call table.
A control history has no direct answers. Arbitrary script rows still pass session admission.
These laws carry supplied invariants. They establish no progress or host implementation claim.
The consumers are the thirteen scenario clauses over scripts, under R4 through R13.

The central machine work follows `docs/core/semantics.md` concept 4.
Its proof technique uses trace invariants and interference checks, as the Owicki and Gries connection describes.
`Machine.Lift` already owns induction through commands, decisions and histories.
`Book` already owns transfer between the frame and reference machines.
A new law must use those owners and give its consumer.

## Landing order

The Workers comparison selects shared command laws and program-specific assertions at every command boundary.

| Landing | Modules and result | Narrow build and audit |
| --- | --- | --- |
| L0 | `Effect4.Laws.Run.Frame`, shared scenario adapter, one frame for all families | Build both modules, audit both |
| L1 | `Effect4.Laws.Api.AuthorBuild`, `Test.Dogfood.Scenario.Programs`, symbolic crew equations | Build both modules, audit both |
| L2 | `Effect4.Laws.Run.Journal`, session key uniqueness and tape ending | Build Journal and its scenario reader, audit both |
| L3 | General machine step laws selected by the Workers comparison | Build new law modules and actual consumers, audit each |
| L4 | Store write discipline and Atomic invariant | Build the support module and Atomic, audit each |
| L5 | Workers control positions and release accounting | Build the support module and Workers, audit each |
| L6 | Queue wrapper segments and one crew invariant | Build Queue law and support modules, then QueueWorkers, audit each |
| L7 | Correct timeout race and one fetch invariant | Build P1HttpCache, support modules and Timeout, audit each |
| L8 | Routing segment proof and call provenance | Build Routing support and Routing, audit each |
| L9 | Gate repair and generated proof graph | Run only the checks reached by the landed changes |

```mermaid
flowchart TD
  F[L0 run frame] --> J[L2 session ledger]
  P[L1 symbolic programs] --> C[L3 machine laws]
  F --> C
  C --> A[L4 Atomic]
  C --> W[L5 Workers]
  C --> Q[L6 QueueWorkers]
  P --> W
  P --> Q
  J --> Q
  J --> T[L7 Timeout]
  C --> T
  J --> R[L8 Routing]
  A --> G[L9 gate repair]
  W --> G
  Q --> G
  T --> G
  R --> G
  subgraph parallel[Independent proof lanes]
    P
    J
    R
  end
```

## Decisions and evidence

| Question | Recommendation | Current evidence |
| --- | --- | --- |
| Timeout race | Repair the form to settle on an entrant's exit. Preserve the retry proposition. | The agent checks the retained counterexample against vendored rc.112. |
| Cleanup premise | Preserve the existing proposition. Use session-admitted history in its proof. | The scenario already passes every raw row through session admission. |
| Stale reply provenance | Preserve clause four. Prove provenance separately from key uniqueness. | `ending_of_tape` does not imply the original clause. |
| Routing budget | Preserve the current budget unless a checked necessity requires a ruling. | The larger generic sufficient bound alone proves no necessity. |
| Unauthorized scripts | Preserve every script. | A restriction would weaken the proposition. |
| Symbolic job count | Preserve every job count. | The symbolic-program lane checks and replaces the stalled probe. |
| Shared machine structure | Reuse command induction and prove program-specific assertions at every command boundary. | Both Workers probes compile. Cuts and forced yields defeat the ordinary resting table. |

## Deferred gates

No behavior gate runs before the major proof structures land.
Pure law modules change no executable behavior.
Root import closure, semantics regeneration and scenario control repairs follow their structure landings.
A timeout form change reaches `check-truth`, `check-target`, `check-compiler`, `check-native` and `check-ocaml`.
The receipt records each actual command and result.
The whole battery and whole-tree axiom gate remain owner-triggered sweeps.

## Current checked evidence

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Run.Tape Effect4.Laws.Program.Guard.Core ProofGraph.AxiomAudit Test.Dogfood.Scenario` passes.
The build reports 1025 jobs.
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Run.Frame Test.Dogfood.Scenario.Frame` passes with 1020 jobs.
`AuditFrame.lean` audits 107 declarations within `[propext, Quot.sound]`, with no planned goals or dependencies on goals.
The fixture checks that a direct answer as a raw session row keeps the machine unchanged.

The machine lane compiles both Workers probes at one job.
A fuel cut leaves a non-resting state.
A forced yield leaves a resting state with a delayed entry.
The selected route combines shared command laws with assertions at every command boundary.
A table restricted to ordinary resting states cannot cover the existing propositions.
This finite probe selects proof structure. It proves no scenario invariant.

## Atomic proof placement

`Program.HeapSites.heap_sites_keep` states the proposed `cell-invariant-from-write-sites` claim.
Its concept is `store-typing`, its role is soundness, and its requirement is R4.
The write-site premise covers each `perform` at its source address and binder level.
Its reach is every control history of a built program, with any compile budget.
It establishes no progress, multi-cell relation or outside runtime behavior.
Its consumer is the original `Atomic.bounded` proposition.

`Atomic.Store.shop_stages` is a step of the `atomic` claim, under `store-typing` and R4.
Its consumers are the original `Atomic.counted` and `Atomic.committed` propositions.
The premise is a successful build of the shop and a control history.
The stage assignment relates request outcomes and the stores; it establishes no progress.
Its existence remains a planned obligation until code-position and store preservation are proved.
The extracted program, scripts, observations and original propositions remain unchanged.

## Worker release placement

`Workers.Assertions` serves the original `Workers.releases_once` clause, under `scope-lifetime-finalization` and R11.
Its source facts hold for every job count and identify the two acquisition paths.
It counts registrations, release starts and log writes separately.
Its reach includes every budget, script, yield and interruption admitted by the session.
It proves no progress or release order.
The original clause follows from three preservation goals through the shared history law.
The general release proof needs custody across scope entries, active close code and the registration continuation.
The scope's `close_twice` law alone cannot supply that custody.

## Source position cautions

The packet's suggested raw-point level invariant needs a name-specific statement.
`EffName.gen` keeps the generator root path while its environment advances with a separate program counter.
The relevant source address includes that counter; the raw point alone does not locate the active statement.
`PointTyped` retains source typing but does not assert unique dynamic use of a source site.
The existing typed capstones do not supply native source ownership for table-aware, variable-budget histories.
