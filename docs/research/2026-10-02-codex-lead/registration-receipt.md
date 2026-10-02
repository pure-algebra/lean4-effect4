# Registration completion receipt

Before integrating: this closes the unchanged `M6Ledger.step_registrationDone` goal. It does
not close launch, loop, deliver, either M6 capstone, or M7. No production machine definition,
`ConfigTyped` clause or theorem hypothesis changed. M6 has 5 open of 20; M7 has 4 open.

Base: `4c219956e9fa952a34bb37cb5f89ab0ce657f74c`, independent `codex/proofs-lead` worktree.
The commit containing this receipt is the slice head. No push.

## Theory and proof graph

Concept 4, reactive scheduling, requires local configuration preservation before induction on
executions. The exact question is `StepPreserves root rootTy (.registrationDone race yielding)`;
the consumer is the existing M6 decision/reachability assembly, followed by M7. This is the
same invariant method documented with Lynch–Vaandrager §6 in `docs/core/semantics.md` §2.4.5.
The frame/protocol analogy there guides decomposition; it does not assert an Iris model or
global exclusive ownership of internal tokens.

The actual machine has three outcomes. A buffered accepted answer installs the typed settle
program. A deferred interruption installs the cancellation frame and queues a loop. Otherwise
the host becomes idle with a pending record at its race key. All three retain typing at the
same world, satisfying the existing existential later-world goal.

The third outcome changes a pending lookup. The ordinary `ObsView` forbids that, so the new
`ObsViewOff` permits it at exactly one key. Row 134(d)'s stored and queued observer exclusion
ensures no countdown reads the changed record. The proof retains the token's declared type;
it does not change it to `unit` to make the park work.

Every new theorem has a concrete consumer:

| Theorems | Consumer |
| --- | --- |
| `pendingWeakerOff_single`, `obsViewOff_rupdate` | the ordinary-park branch and `configTyped_rupdate_park` |
| `countdownAt_off`, `storedObserverOk_off`, `observerCommandOk_off` | observer obligations in the fiber/queue transports |
| `enrollRaceOk_off`, `fiberTyped_transport_off`, `queueOk_transport_off` | `configTyped_rupdate_park` |
| `externalRequestR_of_marker` | registration's exclusion of a new external request |
| `raceCancelThenFail_typed`, `stackAccepts_raceFinalizer` | the deferred-interrupt branch |
| `configTyped_rupdate_park` | the ordinary-park branch of `registrationDone_preserves` |
| `registrationDone_preserves` | exact `#obligation_proved M6Ledger.step_registrationDone` |

The selected proof view includes the command witness, park builder, countdown transport and
cancellation-frame witness, alongside the ledger goal. Actual statement/body references remain
distinct from authored prerequisites. The report is a selected view, not a complete proof census.

## Verification

Commands ran in the independent worktree through
`/private/tmp/codex-lead-2026-10-02/run.py`, with one compiler lane, `LEAN_NUM_THREADS=1`,
explicit Lean `-j1 -M6144 -DwarningAsError=true` for isolated files, and bounded durations.
Saved command JSON and complete logs are beside that runner.

- Claude supplied a source-only candidate. It compiled after two explicit `(g := g)` arguments
  at existing helper calls; no proposition changed (`registration-03`, exit 0, 5.657 seconds).
- `lake --no-cache build Effect4.Laws.Program.Typed.Commands.Registration` passed
  (`registration-build`, 18.872 seconds).
- Every one of the 13 production theorems had its transitive dependencies inspected with
  `#print axioms` (`registration-axioms`, exit 0, 7.792 seconds). All lie within
  `[propext, Quot.sound]`; one uses no axioms and the marker fact uses only `propext`.
- The concrete battery passed (`registration-controls-02`, 1.973 seconds); all 17 theorem
  dependency reports lie within the same ceiling. It rejects the historical CE-028 machine
  for every world/queue using `SchedulerState.raceObservers`, then proves the positive input
  after removing only its countdown. `result_typed` applies the general command theorem;
  separate equations pin the actual void park, cleared registration flag and historical
  collision's raw behavior. These equations are finite controls, not a reachability proof.
- `lake --no-cache build Effect4.Laws Test.Program.RegistrationColumn` passed
  (`registration-integration-02`, 10.042 seconds). The prior attempt caught the final ledger
  reporter's missing import of the new witness. Advancing Observe's import from Race to
  Registration and lowering its ceiling from 6 to 5 repaired that integration boundary;
  no Observe proof changed.
- The existing seven semantics producer/fixture targets prepared successfully
  (`registration-report-prep`, 14.528 seconds). Report and architecture generation results
  are retained in the completion record beside the runner.
- `python3 scripts/check-semantics.py --generate generated` passed
  (`registration-report`, 100.864 seconds), verifying 1,226 imported artifact hashes against
  their saved traces. The selected report has 9 features, 149 declarations and 771 edges;
  the registration goal is `proved` with its unchanged statement. Its actual proof-reference
  edges include the park builder and cancellation-frame witness, and the command witness
  connects to the goal. M6 is measured as 15 proved / 5 wanted.
- The architecture producer and its `--check` passed (`registration-architecture`,
  24.998 seconds; `registration-architecture-check`, 20.409 seconds). The existing one
  import-direction warning remains displayed and is not claimed repaired. `git diff --check`
  and independent output-hash, selected-status and source-identity comparisons passed.

Final formatting removed one extra blank line at the end of the new battery. Its saved module
built again (`registration-battery-final`, 3.301 seconds); all 35 named generation inputs stayed
byte-identical. The architecture's source-line count was regenerated and checked again
(`registration-architecture-final` / `registration-architecture-final-check`). The completion
record retains final saved file hashes; no semantic or proof statement changed in this cleanup.

The temporary drafts' earlier failed elaborations are retained as diagnostics; their `sorryAx`
error recovery is not accepted evidence. The final checked sources contain no proof holes.
The exact baseline Assembly diff removes only the old placeholder; other reviewed machine,
guard, validity, Race and Bookkeeping source hashes remain unchanged.

## Scope and remaining work

Production scope is the new Registration module, its Laws import, the Assembly placeholder,
and Observe's report import/ceiling. The battery is imported by `Test/All.lean`; CE-028's row
retains its historical refutation and links the current controls. STATE, semantics prose,
the selected proof graph, generated report/architecture, plan and this receipt document the slice.

The report refresh does not rerun the unchanged TypeScript decoder suite or the broad generator
sweep. The earlier full semantics check remains historical; this slice records fresh generation
and source/artifact verification separately. No target/host test, speedup, progress, fairness,
global unique-sender property or complete machine safety is claimed.

Independent launch investigation found a different checked counterexample at this base: a
queued enrollment can name a not-yet-allocated child. Evidence is under
`/private/tmp/codex-lead-2026-10-02/launch-audit/`. This slice changes no enrollment contract;
the frozen launch goal remains open. Its narrow row 134(e) clarification is a separate slice.
