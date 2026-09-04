# Retiring the old fiber machines (W3, 2026-09-04)

Status: plan, executed the same day in three mechanical pieces (A library, C records, B
batteries and coverage). Predecessors: the reification spine (`dd1bc93`, the Deep machine as
the witnessed model for the fiber rows) and the second pass of clauses (`f89524e`, 134 of 135
census rows green through `Effect4/Deep/Clauses.lean` and `Witnesses.lean`).

## Why now

Every fiber, interrupt, fork, scope-close and scheduler row of the runtime census is
witnessed by the reference machine. The two older machines it replaces —
`Effect4/Concurrency/Scheduler.lean` (the relational scheduler over a fiber map, with its
decision tape) and the controller calculus of `Effect4/Concurrency/Supervision.lean`
(`Globals`, `Fiber`, `forkUnsafe`, `WaitState` replay, `raceStep` replay) — survive only
through three projections (`RunFiber.toCore`, `RunFiber.toSup`, `RunMachine.toSched`), one
bridge definition (`Event.toTrace` in `Target/TypeScript/Simulation.lean`), eight batteries
and 235 witness citations in the coverage join. The user's ruling for this phase: keep what is
proven correct, remove what Deep directly replaces. The projections were the plan's reuse
route; with every row re-witnessed on the machine itself they carry nothing.

## What stays: the vocabulary

Deep, its stores, the fork-flow compile and the Layer model use these names and nothing else
from the old modules. They stay, in `Effect4/Concurrency/Supervision.lean` and
`Effect4/Concurrency/Fiber.lean`, with their receipts:

| kept | used by |
| --- | --- |
| `Effect4.FiberId` (`Fiber.lean`) | everything |
| `Supervision.MaskMode`, `ForkOptions`, `ObserverMode`, `ScopeMode` | `Deep.Fibers`, `Stores`, `ForkFlow`, `Layer`, `Clauses`, `Witnesses` |
| `Supervision.RaceAllState`, `RaceAllState.initial`, `raceComplete` (and `WaitState`, `WaitState.pending`, which `raceComplete`'s `cleanup` field and `after_accepted` arm need) | `Deep.Fibers` (`raceAll`, `fireObserver`), `Clauses` |
| `Supervision.interruptCause` | `Deep.Fibers` (`interruptRecord`), `Clauses`, `Witnesses` |
| receipts: `MaskMode.cases_receipt`, `ObserverMode.cases_receipt`, `ScopeMode.cases_receipt`, `interruptCause_eq`, `RaceAllState.initial_eq`, `raceComplete_unknown`, `_after_accepted`, `_success`, `_failure_last`, `_failure_pending` | coverage rows `fork.unsafe`, `fork.await`, `fork.join`, `fork.in`, `fork.fiber-run-in`, `fork.interrupt`, `interrupt.accumulate`, `fork.race-all` |

## What goes

* `Effect4/Concurrency/Scheduler.lean` (whole), `Effect4/Concurrency/Interrupt.lean` (whole:
  `InterruptMask`, `CleanupState`, `InterruptBoundary` served only `FiberState` and the
  projections), `FiberStatus` and `FiberState` from `Fiber.lean`, everything in
  `Supervision.lean` outside the table above.
* `RunFiber.status`, `mask`, `cleanup`, `toCore`, `subscriptions`, `toSup`,
  `RunMachine.toSched` in `Deep/Fibers.lean`; `Witnesses.statusOf` and the "two projections
  compute" section (`toSched_computes`, `toSup_computes`, `toSup_records_the_interrupt`);
  `ForkFlow.maskedOf` reads `frame.interruptible` directly.
* `Event.toTrace` in `Target/TypeScript/Simulation.lean` and its two checks in
  `Effect4Test/Target/TypeScript/SimulationContract.lean`.
* Batteries: `Effect4Test/Concurrency/{FiberAssurance,FiberAxiomReport,FiberRepresentativeContract,FiberSupervisionAxiomReport,FiberSupervisionContract}.lean`,
  `Effect4Test/Counterexamples/Concurrency/{FiberRepresentative,FiberSupervision,RaceRepresentative}.lean`;
  their imports in `Effect4Test.lean`; the `Effect4TestConcurrency` lib; the
  `FiberAssurance` entry of `auditImplementationModules` in `AxiomGate.lean`.
* Coverage join: the 222 `Effect4.Supervision.*` citations outside the kept receipts and the
  13 root-namespace scheduler theorems (`cleanup_*`, `*_exists`, `join_agreement`,
  `double_join_agreement`, `step_deterministic`, `fixedTape_deterministic`,
  `masked_interrupt_defers`, `unmask_delivers_pending`), with their snapshot blocks. Every
  affected row keeps at least one Deep or frame witness and its coverage.
* Records: `docs/SUPERVISION-DAG.md`, `docs/SUPERVISION-IMPLEMENTATION.md`,
  `docs/FIBER-DAG.md`, `test/contracts/fiber-representative.contract.md`,
  `test/contracts/fiber-supervision.contract.md`, `test/counterexamples/concurrency/ATTACKS.md`,
  `scripts/{check,generate,test}-fiber-assurance*.sh`, `scripts/check-fiber-supervision-host.sh`,
  `generated/fiber-assurance.tsv`; register rows `E4-CONC-CE-001`–`026` with a history note;
  the 27 `Effect4.Supervision.*` rows of `PORT-MANIFEST.md` reduced to the kept vocabulary.
  `harness/fiber-supervision/` stays: its `host-pin.json` is the live-stack contract's
  package authority.

## Not touched

Frozen contracts that mention the old modules in prose (`cause-exit`, `frames`,
`live-stack`), the research notes, `docs/EFFECTS-SPLIT-PLAN.md`'s history table. The
`owned` disposition keeps its rows (a Lean-owned model, now Deep). `op.Failure` stays partial
(the stack-frame annotation needs a `StackTrace` service key).

## Pieces

* **A (library, builds `Effect4`)**: the trims above in `Effect4/`, `Effect4.lean`,
  `Effect4Test/Target/TypeScript/SimulationContract.lean`.
* **C (records, no build)**: the deletions and edits under `docs/`, `test/`, `scripts/`,
  `generated/`, `PORT-MANIFEST.md`, `docs/ARCHITECTURE.md`.
* **B (after A; builds `Effect4Test.Audit.RuntimeCoverage`, then `Effect4 Effect4TestGreen`)**:
  the battery deletions, `Effect4Test.lean`, `lakefile.toml`, `AxiomGate.lean`, and the
  coverage strip (scripted, then the fallout).
