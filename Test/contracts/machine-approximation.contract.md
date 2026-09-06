# Machine approximation contract packet

Status: FROZEN / GREEN, authored and landed 2026-09-05. The module landed with its battery
and its report; every theorem below is proved, and the four rows are SEEDED.

Implementation fence (one new module; no existing module changes beyond the root import
lists): `src/Effect4/Machine/Approximation.lean`.

Lean battery: `Test/Machine/Runtime/ApproximationContract.lean`.

Axiom report: `Test/Machine/Runtime/ApproximationAxiomReport.lean`.

Counterexamples: `E4-APPROX-CE-001` through `E4-APPROX-CE-004` in
`Test/Counterexamples/REGISTER.md`; witnesses are guards in the battery.

Review: `docs/research/2026-09-05-effects-papers-review.md` §3 G2; the landing note is
`docs/research/2026-09-05-fuel-laws.md`. The shape mirrors the archived Flow module
`git:c407ab7:Effect4/Semantics/Approximation.lean`; nothing of it is copied, the machine is
another one.

Machine under contract: `src/Effect4/Machine/Fibers.lean` — `drive`, `stepDecision` with
`fire`, `flushAll`, `flushRoot`, and `replayEval`.

## Claim boundary

This packet freezes four bounded facts about the Lean loop and refuses two by name.

1. `drive` is the machine half of a loop that keeps its residual commands (`driveState`), and
   that loop splits: fuel `a + b` is fuel `a`, then fuel `b` on what fuel `a` left. A loop whose
   commands were exhausted, or which halted, never changes with more fuel.
2. The trace of a machine only grows through every helper `drive` reaches, through `drive`,
   through each decision and through `replayEval`. No interp hook returns a machine, so no
   choice an interp makes can shrink a trace.
3. On one loop, fuel is monotone: more fuel extends the trace. The decisions that run one
   loop or none (`evaluate`, `answerAsync`, `interruptFrom`, `yieldVerdict`,
   `installMiddleware`) inherit it.
4. A preorder on replay results (`frontier m` below whatever extends `m.trace`; `finished`
   and `stuck` below themselves), a decidable sufficiency predicate on a tape, stability under
   it, monotonicity under it, the frontier and stuck halves of monotonicity on a one-decision
   tape, and a bounded search for the least sufficient fuel whose answer does not depend on
   the bound.

Refused by name:

* `APPROX-FB-REFRESH` — fuel is not monotone across a fuel refresh: `fire` gives every task
  the full fuel, `flushAll` and `flushRoot` every round, `replayEval` every decision. A loop
  cut short is followed by the next unit of work on the half-done machine, and its events
  land where the finished loop's would have. Rows `E4-APPROX-CE-003` and `E4-APPROX-CE-004`.
  Across a refresh, monotonicity is stated only under `Suffices`, where it is stability.
* `APPROX-FB-FINISHED` — `finished` at an insufficient fuel is not proved terminal. Every
  fiber has exited, but a residual `Cmd.drainDue` may change the store through
  `interp.dueResumes`. `replay_stable` carries `Suffices`, not the outcome. Row
  `E4-APPROX-CE-002`.

Not here: the `fuelFor` allotment for `Eff` programs (the review's fourth theorem); any
statement about rc.112; anything called a bisimulation. These are theorems about the Lean
loop.

## ENSURES

Every theorem is at `propext`/`Quot.sound`.

The loop with its residue:

1. `driveStep`, one non-stuck command of `drive`, arm for arm; `driveState`, the loop keeping
   the commands it did not run: fuel `0` keeps everything, no command leaves nothing, a stuck
   machine keeps its commands.
2. `drive_succ_cons`, `drive_zero`, `drive_nil`, `drive_stuck`, `driveState_zero`,
   `driveState_nil`, `driveState_succ_cons`, `driveState_stuck`.
3. `drive_eq_driveState : drive interp n m c = (driveState interp n m c).1`.
4. `driveState_add : driveState interp (a + b) m c = driveState interp b (driveState interp a m c).1 (driveState interp a m c).2`;
   `drive_add` the same on `drive`.
5. `drive_stable_of_done : (driveState interp n m c).2 = [] → ∀ k, drive interp (n + k) m c = drive interp n m c`;
   `drive_stable_of_stuck`, `driveState_done_add`, `driveState_settled_add`,
   `drive_stable_of_settled`, with `settled r := r.2.isEmpty || r.1.stuck.isSome`.

The trace only grows:

6. `RunMachine.Extends m m' := m.trace <+: m'.trace`, reflexive, transitive, and
   `Extends.exists` in the review's form `∃ ev, m'.trace = m.trace ++ ev`.
7. The trace of `emit`, `update`, `modify`, `halt`, `updateRace`, `arm`, `disarm`.
8. `RunMachine.Grows m e := Extends m e.1` and one lemma per helper: `spawn_grows`,
   `start_grows`, `interruptEach_grows`, `countdownPark_grows`, `linkScope_grows`,
   `launchEntrant_grows`, `injectYield_extends`, `fireObserver_grows`,
   `fireObserver_fold_grows`, `exitFiber_grows`, `finishFrame_extends`, `stepFrame_extends`,
   `finalizerOr_extends`, `interruptThenJoin_extends`, `withFiber_extends`,
   `evaluatePrim_extends`, `iteration_extends`, `settle_grows`, `driveStep_grows`.
9. `drive_extends`, `fire_extends`, `flushAll_extends`, `flushRoot_extends`,
   `stepDecision_extends`, `replayEval_extends` (on `ReplayResult.machine`), each with its
   `_trace_extends` form `∃ ev, … = m.trace ++ ev`.
10. `drive_trace_mono : n ≤ n' → Extends (drive interp n m c) (drive interp n' m c)`.

The order:

11. `ReplayResult.le`, `ReplayResult.terminal`, `le_refl`, `le_trans`, `le_antisymm_terminal`,
    `frontier_le`; `replayEval_nil_machine`.

The receipts:

12. `taskCmds`, `fireStep`, `fireState`; `fire_eq_fireState`; `fireTasks_false`,
    `fireTasks_stable`, `fireState_stable`, `fire_stable`.
13. `flushAllState`, `flushAll_eq_flushAllState`, `flushAllState_stable`, `flushAll_stable`;
    `flushRootState`, `flushRoot_eq_flushRootState`, `flushRootState_stable`,
    `flushRoot_stable` (two indices: the fuel and the rounds).
14. `stepDecisionState` with `stepDecision_eq_state`, `stepDecisionState_stable`,
    `stepDecision_stable`.

The laws over `replayEval`:

15. `Suffices interp fuel tape m : Bool` — the replay itself with the receipts; a stuck
    machine ends the replay and needs nothing.
16. `replay_stable : Suffices interp n tape m = true → ∀ k, replayEval interp (n + k) tape m = replayEval interp n tape m`.
17. `Suffices_mono`, `Suffices_of_le`.
18. `replay_obs_mono_of_suffices : n ≤ n' → Suffices interp n tape m = true → le (replayEval interp n tape m) (replayEval interp n' tape m)`.
19. `SingleLoop`; `stepDecision_trace_mono`; `stepDecision_stuck_stable`;
    `replay_frontier_mono_single`, `replay_stuck_mono_single`.
20. `leastUpTo` with `_none`, `_sound`, `_le`, `_least`, `_isSome`, `_bound_mono`;
    `leastSufficient` with the same six; `replay_colimit`; `replay_colimit_eq_of_sufficient`.

## Algebra and dependency spine

```text
drive (n+1) m (c :: rest)   = if stuck then m else drive n (driveStep m c rest).1 (driveStep m c rest).2
driveState (a + b) m c      = driveState b (driveState a m c).1 (driveState a m c).2
drive (n + k) m c           = drive n m c                          when (driveState n m c).2 = []
trace (drive n m c)         = trace m ++ ev                        for some ev
trace (drive n m c)         <+: trace (drive n' m c)               when n ≤ n'
replayEval (n + k) tape m   = replayEval n tape m                  when Suffices n tape m
leastSufficient tape m b    = some f  ⇒  Suffices f, ¬ Suffices g (g < f), same f under b' ≥ b
```

Dependencies: `Effect4.Machine.Fibers` (the machine), `Effect4.Machine.Clauses`
(`interruptEach_cons`, `fire_unknown`, `fire_eq`, `flushAll_idle`, `flushAll_round`),
`List.IsPrefix` from core. No Mathlib; the bounded search is written by hand.

## Counterexample rows

| ID | Status | Attacked statement | Witness | Forced repair |
| --- | --- | --- | --- | --- |
| `E4-APPROX-CE-001` | SEEDED | The loop is stable in fuel without a side condition | `pBindSync` under `evaluate`: fuel `1` records one event and leaves two commands, fuel `2` records two | `drive_stable_of_done` carries `(driveState …).2 = []` |
| `E4-APPROX-CE-002` | SEEDED | The outcome `finished` means the fuel sufficed | `pSucceed` at fuel `3` is `finished` with `[drainDue, drainDue]` unrun and `Suffices … 3 = false`; `pYieldNow` under `[evaluate, flush]` is `finished` from `5` and sufficient from `7` | `replay_stable` carries `Suffices`, not the outcome (`APPROX-FB-FINISHED`) |
| `E4-APPROX-CE-003` | SEEDED | The fuel chain is monotone along a tape | `pBindSync` under `[evaluate, interruptFrom none ∅ root]`: the traces at fuel `1` and `2` are not prefixes of each other | monotonicity is stated on one loop (`stepDecision_trace_mono`) and along a tape under `Suffices` (`APPROX-FB-REFRESH`) |
| `E4-APPROX-CE-004` | SEEDED | `fire` is monotone in fuel | two `start` tasks on the root's dispatcher fired at fuel `1` and `2`: the traces are not prefixes of each other, since the second task runs after the first was cut short | `fireState`'s receipt is false at both; `fire_stable` carries it |

## Falsifiers

Each row is a pair of guards in the battery: the witness as stated and the statement the
repair makes true. A change that lets a row's attacked statement hold must change both
guards. A change to `drive` that makes fuel exhaustion sticky (a frontier marker, as the
archived Flow runner had) would turn rows `003` and `004` green and is the one repair this
packet would welcome; it is not made here.
