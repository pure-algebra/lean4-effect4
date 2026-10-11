# The last planned goals: a packet for Codex

The library rests on no planned goal. Fourteen goals remain, and each is a property of one of the
five example applications in `Test/Dogfood/Scenario/`. This packet plans their proofs. Four probe
seats wrote one folder each, with a note and a `Probe.lean` that proves each goal modulo the
lemmas it names. The coordinator's summary below orders the work.

## The fourteen goals

Thirteen goals say "under every script": `∀ moves, P (observe (Scenario.play (opened b) moves))`
(`Test/Dogfood/Scenario.lean`). A move plays rows of `Command` on `Effect4.Run`
(`src/Effect4/Run/Basic.lean`), and `Move.row` plays any raw row. So each goal is an invariant of
runs under every command, joined to facts about one program's code. The fourteenth,
`infrastructure_escapes`, fixes one script.

| Family | Goals | Requirement | Folder |
| --- | --- | --- | --- |
| Release at most once | `Workers.releases_once`, `QueueWorkers.releases_once`, `Atomic.cleans_once`, `Timeout.cleanup_keeps` | R11 | [release-once](release-once/README.md) |
| Store invariants | `bounded`, `counted`, `committed` (Atomic) | R4 | [store-invariants](store-invariants/README.md) |
| The queue under a run | `held_within_fed`, `fed_accounted`, `queue_settled` (QueueWorkers) | R10, R12 | [queue-run](queue-run/README.md) |
| Host protocol and handlers | `stale_never_applies`, `retries_declared` (Timeout), `unauthorized_calls_nothing`, `infrastructure_escapes` (Routing) | R5, R6, R10 | [host-protocol](host-protocol/README.md) |

## What the probes found

Each family's `Probe.lean` compiles and proves its goals modulo named planned goals, within
`[propext, Quot.sound]`. Codex orders the landing ([the prompt](CODEX-PROMPT.md)). The seats'
hour estimates are discarded: the owner expects most goals to land within hours.

- **Two goals are false as stated.**
  - `retries_declared` (Timeout): `retries_declared_refuted` (`host-protocol/Probe.lean`) proves
    its negation by the kernel. The form `timeoutForm` (`Test/Dogfood/P1HttpCache.lean`) races
    two forked awaits, so the timer can win after the attempt has finished. rc.112's
    `raceAllFirst` settles the race at the body's own exit. The seat recommends repairing the
    form.
  - `cleanup_keeps` (Timeout): one direct answer to the root's join lets attempt 2 count while
    attempt 1 is never cleaned. The goal holds on runs whose decisions a run can make
    (`RunReachable`, `release-once/Probe.lean`).
- **One frame, four spellings.** Every family wrote the same frame: a run property that every
  row keeps (`RunKeeps`, `RowKeeps`, `MachineKeeps` with `RunReachable`, `scenario_keeps`).
  Unify it first.
- **One large shared law.** The goals over forked programs need a step law of the frame machine
  for many fibers: each fiber's position in its own code. The seats name it three ways: control
  linearity (`once_placed_*`, release-once), fiber-local positions (G2, store-invariants), and a
  stage table of every fiber (`crew_invariant`, queue-run). It is one law.
- **Smaller general laws.** A cell invariant from its write sites (`heap_sites_keep`, G1); R11
  per registration (`release_starts_le_registrations`, `finalizer_starts_le_pushes`); a join law;
  the session's keys once (`Ledger`, `session_keys_once`, proved); `ending_of_tape` (proved).
- **Cheap now.** `stale_never_applies` clauses 1 to 3 are proved for every program, and clause 4
  restated as `ending_of_tape` is proved. `bounded` rests on `heap_sites_keep` alone.
  `infrastructure_escapes` rests on `escape_session`, a budget fact of one funded run.
- **A trap.** The crew's elaboration at a symbolic job count does not reduce: a generated binder
  name takes its digits from `toString` of the scope's length, and `whnf` folds `Nat.mod` only on
  closed arguments. A repair is drafted and not verified (`queue-run/scratch/StuckFix.lean`).

## Beyond the fourteen goals: the open parts

`generated/semantics.md` lists 87 open parts that no planned goal states. The coordinator sorted
them by what they wait on. A part that feeds a goal above is the goal's work.

### They feed the fourteen goals

- R11: release at most once per registration over a whole run (DB-07); exactly once in close
  order with a completed-cleanup receipt (DB-07, DI-65).
- R10 to R12: `queue-expansion-agrees`, `waiting-request-obligation-preserved` and
  `wait-registration-no-gap` (proposed claims).
- R10: a behaviour law of a handler form (DI-89); `infrastructure_escapes` is the one for
  `catchTag` on one program.
- R6: the retirement edge and reply admission at the application, as far as
  `stale_never_applies` reads them.

### Proposed claims that need no ruling

Each is worded in the registry and stands alone. They are the next goals to state.

- Modules: `pool-profile-preserved`, `semaphore-accounting-preserved`, `pool-expansion-agrees`,
  `semaphore-expansion-agrees`, `partitioned-semaphore-expansion-agrees`,
  `stream-array-run-agrees`, `synchronized-ref-expansion-agrees`,
  `pubsub-single-expansion-agrees`, `posted-wake-profile-agrees`, `pool-lease-return`,
  `pool-close-waits`, `semaphore-protected-permit`, `pool-wake-selection`,
  `atomic-attempt-isolation`, `atomic-attempt-agreement`.
- Scheduling: `driver-continuation-split`, `driver-suspension-keeps-typed`,
  `embedded-budget-sufficient`, `posted-task-decision-preserves`.
- The host: `expansion-keeps-call`, `replay-at-call-instance`, `clock-unit-compatibility`.
- Sketches and the checker: `column-graduality`, `marking-agrees`, `checker-monotone`,
  `posted-body-entry-typed`.

### Structural parts, not yet triaged

These are the large ones. Each needs a statement before it can be a goal.

- R2 C2: the host meaning outside `StraightRows` and `LoopedDataRows`, so for programs that fork,
  open a scope, are interrupted, use services or call definitions. This is the largest gap for
  agents' programs.
- R2 C4, C5, C7 and C8: the protocol typing for `TypedProg`, the world projection, the
  representation (row 115), and each form.
- R1: program admission at declared services, and the faces pinned to the built-in signature.
- R5: `lower_refines_build` (row 147); reference keys, Config and minted keys at a runtime bridge.
- R8: K2 past the readable domain; the TypeScript face beyond finite checks; the profile as data.
- R10: a composed module's law, `Agrees profile module expansion` (row 79, DI-89), and DI-39's six
  rows.
- R11: state retained at a frontier; the carrying fact of a region.
- R12: stability with a named progress observation; divergence by compatible prefixes; posted-wake
  progress under fairness premises.
- R13: the service half of the signature as a recorded input.

### They wait on a ruling (13)

Rows 82 (twice: typed behaviour values, code-valued services), 97 (handle declarations), 98 to
100 (the typed replay route), 108 (numbers), 117 (the frame contract), 118 (structured service
carriers), 124 (recursive types) and 28 (verified lowering); DI-89's D9 and DB-07's D8; R12-c
(liveness on infinite tapes).

### They need a definition (6)

The host as a relation between calls and answers (R6); and for sketches, a renumbering map, an
admission with a located refusal, the expected type of an analysing rule, the gap as a leaf of
`Ty`, and a data hole that takes a reply.

### They come after other work (5)

Equality at records (row 126); the public typed guarantee for programs using host services
(row 99); the fiber identity carrier (DI-81); and Config route B, twice (rows 51 and 83).
