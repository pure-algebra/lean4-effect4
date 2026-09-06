import Effect4.Machine.Fibers
import Effect4.Machine.Clauses

/-!
# Machine.Approximation — the fuel laws over the live fiber machine (G2)

Review: `docs/research/2026-09-05-effects-papers-review.md` §3 G2. Packet:
`Test/contracts/machine-approximation.contract.md`. Batteries:
`Test/Machine/Runtime/ApproximationContract.lean` (the guards and the rows `E4-APPROX-CE-001`
to `E4-APPROX-CE-004`) and `Test/Machine/Runtime/ApproximationAxiomReport.lean`. The name
mirrors the archived Flow module (`git:c407ab7:Effect4/Semantics/Approximation.lean`); the
machine under it is `src/Effect4/Machine/Fibers.lean`, whose loop `drive` spends one fuel per
command and returns silently when the fuel is gone.

What is proved:

* **The loop with its residue.** `driveStep` is one non-stuck command of `drive`;
  `driveState` is `drive` returning the commands it did not run. `drive_eq_driveState` says
  `drive` is its first component. The splitting law `driveState_add` says fuel `a + b` is
  fuel `a` and then fuel `b` on what was left, and `drive_add` is the same on `drive`. A run
  whose commands were exhausted never changes with more fuel (`drive_stable_of_done`), nor
  does a run that halted (`drive_stable_of_stuck`).
* **The trace only grows.** `RunMachine.Extends m m'` is "`m'.trace` is `m.trace` followed by
  something". Every helper the loop reaches keeps it (`spawn`, `start`, `launchEntrant`,
  `linkScope`, `interruptEach`, `countdownPark`, `injectYield`, `evaluatePrim` with its
  `withFiber`, `finalizerOr`, `stepFrame`, `finishFrame`, `interruptThenJoin` arms,
  `iteration`, `fireObserver`, `exitFiber`, `settle`), and so do `driveStep`, `drive`,
  `stepDecision.fire`, `stepDecision.flushAll`, `stepDecision.flushRoot`, `stepDecision`,
  and `replayEval` on the machine inside its result. No interp hook returns a machine; the
  hooks return stores, so nothing an interp chooses can shrink a trace.
* **Fuel is monotone on one loop.** `drive_trace_mono`: more fuel on the same commands
  extends the trace. `stepDecision_trace_mono` lifts it to the decisions that run one loop
  (`evaluate`, `answerAsync`, `interruptFrom`) and the two that run none.
* **The order and the three laws over `replayEval`.** `ReplayResult.le`: a `frontier m` is
  below every result whose trace extends `m.trace`; `finished` and `stuck` are below
  themselves only. Reflexive, transitive, antisymmetric on terminal results. Then the
  receipts `fireState`, `flushAllState`, `flushRootState`, `stepDecisionState` and the
  decidable predicate `Suffices interp fuel tape m` ("every loop a decision ran exhausted its
  commands, every `flush` stopped with nothing armed before its rounds ran out"), with
  `replay_stable` (under `Suffices`, every larger fuel replays to the same result),
  `Suffices_mono` (a sufficient fuel stays sufficient), `replay_obs_mono_of_suffices`, the
  frontier and stuck halves of monotonicity on a one-decision tape
  (`replay_frontier_mono_single`, `replay_stuck_mono_single`), and the bounded search
  `leastSufficient` with `replay_colimit`: the fuel it finds is sufficient, every smaller
  fuel is not, the result does not move once one sufficient fuel is under the bound
  (`leastSufficient_bound_mono`, `replay_colimit_eq_of_sufficient`).

What is deliberately not said, each named so it is a refusal and not an omission:

* `APPROX-FB-REFRESH` — fuel is *not* monotone across a fuel refresh. `fire` runs one loop
  per task at the full fuel, `flushAll` and `flushRoot` one `fire` per round, and
  `replayEval` one decision after another: a loop cut short is followed by the next unit of
  work on the half-done machine, so its events land where the finished loop's events would
  have. `E4-APPROX-CE-003` (two decisions) and `E4-APPROX-CE-004` (two tasks) refute the
  trace-prefix law there. Monotonicity across a refresh is stated only under `Suffices`,
  where it is stability.
* `APPROX-FB-FINISHED` — `ReplayResult.finished` at an insufficient fuel is not proved
  terminal. Every fiber has exited, but the residual commands may still change the store
  (`Cmd.drainDue` through `interp.dueResumes`, which an interp chooses). Nothing here says
  they do not; `replay_stable` carries `Suffices`, not the outcome (`E4-APPROX-CE-002`).
* The `fuelFor` allotment of `Eff` programs (the review's fourth theorem) is not here.
* Nothing here is a bisimulation, and nothing here is a statement about rc.112: these are
  theorems about the Lean loop.
-/

set_option autoImplicit false

-- The `DecidableEq` section variables are what the machine's definitions take; a law about a
-- definition that does not need them is stated in the same section anyway.
set_option linter.unusedSectionVars false

namespace Effect4.Machine

universe u v w

open Effect4

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-! ## The loop with its residue

`drive` (`Fibers.lean`) is tail recursive: every arm either returns the machine or runs one
command and goes on with one fuel less. `driveStep` is that one command, on a machine that
is not stuck; `driveState` is the loop keeping the commands it did not run. -/

/-- One command of `drive` on a machine that is not stuck: the machine it leaves and the
commands still to run (`Fibers.lean`, `drive`, arm for arm). -/
def driveStep (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St) :
    Cmd ν σ β ε δ ι α → List (Cmd ν σ β ε δ ι α) →
      RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)
  | Cmd.evaluate id, rest =>
    match m.fiber? id with
    | none => (m, rest)
    | some f =>
      if f.exit.isSome || f.running then (m, rest)
      else
        let f := { f with running := true, currentOpCount := 0, parked := Parked.notParked }
        ((m.update f).emit [RunEvent.started id], Cmd.loop id false :: rest)
  | Cmd.loop id yielding, rest =>
    match m.fiber? id with
    | none => (m, rest)
    | some f => settle id rest (iteration interp m f yielding)
  | Cmd.deliver id yielding, rest =>
    match m.fiber? id with
    | none => (m, rest)
    | some f => settle id rest (evaluatePrim interp m f yielding)
  | Cmd.resume id token answer, rest =>
    match m.fiber? id with
    | none => (m, rest)
    | some t =>
      match t.parked with
      | Parked.withGuard parkedToken =>
        if parkedToken = token then
          let t := { t with
            parked := Parked.notParked
            pending := t.pending.filter fun p => p.token ≠ token
            frame := { t.frame with current := answer } }
          ((m.update t).emit [RunEvent.resumedWith id token answer], Cmd.evaluate id :: rest)
        else (m, rest)
      | Parked.notParked => (m, rest)
  | Cmd.launch raceId, rest =>
    match m.race? raceId with
    | none => (m, rest)
    | some race =>
      match race.programs with
      | [] => (m, rest)
      | program :: more =>
        if race.state.accepted.isSome then (m, rest)
        else
          match m.fiber? race.host with
          | none => (m, rest)
          | some host =>
            let (m, child) := launchEntrant interp raceId m host program
            let m := m.updateRace { race with
              programs := more
              state := { race.state with live := race.state.live ++ [child] } }
            (m.emit [RunEvent.raceLaunched raceId child],
              Cmd.evaluate child :: Cmd.launch raceId :: rest)
  | Cmd.link mode scope key target interruptor extra, rest =>
    let (m, nested) := linkScope interp m mode scope key target interruptor extra
    (m, nested ++ rest)
  | Cmd.finish id exit, rest =>
    match m.fiber? id with
    | none => (m, rest)
    | some f =>
      let (m, f, parked, nested) := exitFiber interp m { f with running := false } exit
      (m.update f, nested ++ (if parked then [] else [Cmd.drainDue]) ++ rest)
  | Cmd.drainDue, rest =>
    let (due, state) := interp.dueResumes m.state
    ({ m with state := state }, (due.map fun d => Cmd.resume d.1 d.2.1 d.2.2) ++ rest)

/-- `drive` keeping the commands it did not run: fuel `0` runs nothing, no command leaves
nothing, a stuck machine keeps its commands, and otherwise one command costs one fuel. -/
def driveState (interp : RunInterp ν σ β ε δ ι α χ St) :
    Nat → RunMachine ν σ β ε δ ι α χ St → List (Cmd ν σ β ε δ ι α) →
      RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)
  | 0, m, cmds => (m, cmds)
  | _ + 1, m, [] => (m, [])
  | fuel + 1, m, cmd :: rest =>
    if m.stuck.isSome then (m, cmd :: rest)
    else driveState interp fuel (driveStep interp m cmd rest).1 (driveStep interp m cmd rest).2

/-- One fuel of `drive` on a command is `driveStep`, unless the machine is stuck. -/
theorem drive_succ_cons (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmd : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)) :
    drive interp (fuel + 1) m (cmd :: rest) =
      if m.stuck.isSome then m
      else drive interp fuel (driveStep interp m cmd rest).1 (driveStep interp m cmd rest).2 := by
  cases hs : m.stuck.isSome
  · cases cmd <;> simp only [drive, driveStep, hs, Bool.false_eq_true, if_false] <;>
      (repeat' split) <;> first | rfl | simp_all
  · cases cmd <;> simp [drive, hs]

theorem drive_zero (interp : RunInterp ν σ β ε δ ι α χ St) (m : RunMachine ν σ β ε δ ι α χ St)
    (cmds : List (Cmd ν σ β ε δ ι α)) : drive interp 0 m cmds = m := rfl

theorem drive_nil (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) : drive interp fuel m [] = m := by
  cases fuel <;> rfl

theorem drive_stuck (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : m.stuck.isSome = true) : drive interp fuel m cmds = m := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases cmds with
    | nil => rfl
    | cons cmd rest => rw [drive_succ_cons, if_pos h]

theorem driveState_zero (interp : RunInterp ν σ β ε δ ι α χ St)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) :
    driveState interp 0 m cmds = (m, cmds) := rfl

theorem driveState_nil (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) : driveState interp fuel m [] = (m, []) := by
  cases fuel <;> rfl

theorem driveState_succ_cons (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmd : Cmd ν σ β ε δ ι α) (rest : List (Cmd ν σ β ε δ ι α)) :
    driveState interp (fuel + 1) m (cmd :: rest) =
      if m.stuck.isSome then (m, cmd :: rest)
      else driveState interp fuel (driveStep interp m cmd rest).1 (driveStep interp m cmd rest).2 :=
  rfl

/-- A stuck machine keeps its commands, whatever the fuel. -/
theorem driveState_stuck (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : m.stuck.isSome = true) : driveState interp fuel m cmds = (m, cmds) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases cmds with
    | nil => rfl
    | cons cmd rest => rw [driveState_succ_cons, if_pos h]

/-- `drive` is the machine half of `driveState`. -/
theorem drive_eq_driveState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) :
    drive interp fuel m cmds = (driveState interp fuel m cmds).1 := by
  induction fuel generalizing m cmds with
  | zero => rfl
  | succ fuel ih =>
    cases cmds with
    | nil => rfl
    | cons cmd rest =>
      rw [drive_succ_cons, driveState_succ_cons]
      cases hs : m.stuck.isSome
      · simp only [Bool.false_eq_true, if_false]
        exact ih _ _
      · rfl

/-- The splitting law: fuel `a + b` is fuel `a`, then fuel `b` on what fuel `a` left. The
corner cases compose because fuel `0` leaves everything, no command leaves nothing, and a
stuck machine leaves its commands. -/
theorem driveState_add (interp : RunInterp ν σ β ε δ ι α χ St) (a b : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) :
    driveState interp (a + b) m cmds =
      driveState interp b (driveState interp a m cmds).1 (driveState interp a m cmds).2 := by
  induction a generalizing m cmds with
  | zero => simp only [Nat.zero_add, driveState_zero]
  | succ a ih =>
    rw [Nat.succ_add]
    cases cmds with
    | nil => simp only [driveState_nil]
    | cons cmd rest =>
      rw [driveState_succ_cons, driveState_succ_cons]
      cases hs : m.stuck.isSome
      · simp only [Bool.false_eq_true, if_false]
        exact ih _ _
      · simp only [if_true, driveState_stuck interp b m (cmd :: rest) hs]

/-- The splitting law on `drive`. -/
theorem drive_add (interp : RunInterp ν σ β ε δ ι α χ St) (a b : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) :
    drive interp (a + b) m cmds =
      drive interp b (driveState interp a m cmds).1 (driveState interp a m cmds).2 := by
  rw [drive_eq_driveState, drive_eq_driveState, driveState_add]

/-- A run whose commands were exhausted never changes with more fuel: the compatibility law
on the loop. -/
theorem drive_stable_of_done (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : (driveState interp fuel m cmds).2 = []) :
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds := by
  intro k
  rw [drive_add, h, drive_nil, drive_eq_driveState]

/-- Nor does a run that halted. -/
theorem drive_stable_of_stuck (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : (driveState interp fuel m cmds).1.stuck.isSome = true) :
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds := by
  intro k
  rw [drive_add, drive_stuck _ _ _ _ h, drive_eq_driveState]

/-- Exhausted commands stay exhausted, and the machine stays. -/
theorem driveState_done_add (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : (driveState interp fuel m cmds).2 = []) :
    ∀ k, driveState interp (fuel + k) m cmds = ((driveState interp fuel m cmds).1, []) := by
  intro k
  rw [driveState_add, h, driveState_nil]

/-! ## The trace only grows

`RunMachine.emit` is the one writer of `trace` (`Fibers.lean:456`); every other machine
operation is a `{ m with … }` that leaves it alone. The invariant is stated as a list prefix
and proved helper by helper, from the leaves up to `replayEval`. -/

namespace RunMachine

/-- `m'` recorded everything `m` had, in order, and then some. -/
def Extends (m m' : RunMachine ν σ β ε δ ι α χ St) : Prop := m.trace <+: m'.trace

theorem Extends.refl (m : RunMachine ν σ β ε δ ι α χ St) : Extends m m := List.prefix_rfl

theorem Extends.trans {a b c : RunMachine ν σ β ε δ ι α χ St} (h₁ : Extends a b) (h₂ : Extends b c) :
    Extends a c := List.IsPrefix.trans h₁ h₂

/-- The form the review states: the later trace is the earlier one followed by some events. -/
theorem Extends.exists {a b : RunMachine ν σ β ε δ ι α χ St} (h : Extends a b) :
    ∃ ev, b.trace = a.trace ++ ev :=
  let ⟨ev, hev⟩ := h
  ⟨ev, hev.symm⟩

theorem emit_trace (m : RunMachine ν σ β ε δ ι α χ St) (ev : List (RunEvent ν σ β ε δ ι α χ)) :
    (m.emit ev).trace = m.trace ++ ev := rfl

theorem update_trace (m : RunMachine ν σ β ε δ ι α χ St) (f : RunFiber ν σ β ε δ ι α χ) :
    (m.update f).trace = m.trace := rfl

theorem modify_trace (m : RunMachine ν σ β ε δ ι α χ St) (id : FiberId)
    (k : RunFiber ν σ β ε δ ι α χ → RunFiber ν σ β ε δ ι α χ) : (m.modify id k).trace = m.trace := by
  unfold modify
  split <;> rfl

theorem halt_trace (m : RunMachine ν σ β ε δ ι α χ St) (why : Stuck) :
    (m.halt why).trace = m.trace := rfl

theorem updateRace_trace (m : RunMachine ν σ β ε δ ι α χ St) (r : Race ν σ β ε δ ι α) :
    (m.updateRace r).trace = m.trace := rfl

theorem arm_trace (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    (m.arm owner).trace = m.trace := rfl

theorem disarm_trace (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    (m.disarm owner).trace = m.trace := rfl

/-- A machine-first tuple whose machine extends `m`: the shape every helper that returns a
machine beside other things has, so a hop through it is one lemma. -/
def Grows (m : RunMachine ν σ β ε δ ι α χ St) {R : Type w} (e : RunMachine ν σ β ε δ ι α χ St × R) :
    Prop := Extends m e.1

theorem Grows.refl (m : RunMachine ν σ β ε δ ι α χ St) {R : Type w} (r : R) : Grows m (m, r) :=
  Extends.refl m

end RunMachine

open RunMachine

/-! ### The tactic

A leaf is `Extends m X` with `X` built from some machine `m₁` by `emit`, `update`, `modify`,
`halt`, `updateRace`, `arm`, `disarm` and `{ … with … }`, where `m₁` is `m` itself or the
first component of a helper's result. `trace_leaf` computes `X.trace` down to `m₁.trace ++ …`
and, when `m₁` is not `m`, leaves `Extends m m₁`; `trace_chain with hop` then hops through
the helper with the lemma `hop` supplies and goes on. The hop list grows down the file, so
that every name it mentions exists where it is used. -/

macro "trace_leaf" : tactic =>
  `(tactic| (
    try simp only [RunMachine.Extends, RunMachine.emit_trace, RunMachine.update_trace,
      RunMachine.modify_trace, RunMachine.halt_trace, RunMachine.updateRace_trace,
      RunMachine.arm_trace, RunMachine.disarm_trace, List.append_assoc]
    first
      | exact List.prefix_rfl
      | exact List.prefix_append _ _
      | refine List.IsPrefix.trans ?_ (List.prefix_append _ _)
      | skip))

syntax "trace_chain" " with " tactic : tactic

macro_rules
  | `(tactic| trace_chain with $hop) => `(tactic| (
      trace_leaf
      first
        | done
        | exact RunMachine.Extends.refl _
        | (apply RunMachine.Extends.trans
           rotate_left 1
           $hop:tactic
           trace_chain with $hop)))

/-! ### The leaves -/

theorem spawn_grows {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {parent : RunFiber ν σ β ε δ ι α χ} {program : Prim ν σ β ε δ ι α}
    {options : Supervision.ForkOptions} : Grows m (spawn interp m parent program options) := by
  unfold Grows spawn
  trace_leaf

theorem start_grows {m : RunMachine ν σ β ε δ ι α χ St} {parent : RunFiber ν σ β ε δ ι α χ}
    {child : FiberId} {immediately : Bool} : Grows m (start m parent child immediately) := by
  unfold Grows start
  split <;> trace_leaf

theorem interruptEach_grows {interp : RunInterp ν σ β ε δ ι α χ St} {who : FiberId}
    {extra : ReasonAnnotations α} {targets : List FiberId}
    {acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)} :
    Grows acc.1 (interruptEach interp who extra targets acc) := by
  induction targets generalizing acc with
  | nil => exact Grows.refl _ _
  | cons t ts ih =>
    rw [interruptEach_cons]
    refine Extends.trans ?_ ih
    split <;> trace_leaf

theorem countdownPark_grows {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {targets : List FiberId}
    {resumeWith : Resume ν} {failFast : Bool} :
    Grows m (countdownPark interp m f targets resumeWith failFast) := by
  unfold Grows countdownPark
  try dsimp only
  (repeat' split) <;> trace_leaf

theorem linkScope_grows {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {mode : Supervision.ScopeMode} {scope key : Nat} {target : FiberId}
    {interruptor : Option FiberId} {extra : ReasonAnnotations α} :
    Grows m (linkScope interp m mode scope key target interruptor extra) := by
  unfold Grows linkScope
  try dsimp only
  (repeat' split) <;> trace_leaf

/-- The hops through the leaves. -/
macro "hops_leaf" : tactic => `(tactic| first
  | exact spawn_grows
  | exact start_grows
  | exact interruptEach_grows
  | exact countdownPark_grows
  | exact linkScope_grows)

theorem launchEntrant_grows {interp : RunInterp ν σ β ε δ ι α χ St} {raceId : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {host : RunFiber ν σ β ε δ ι α χ}
    {program : Prim ν σ β ε δ ι α} : Grows m (launchEntrant interp raceId m host program) := by
  unfold Grows launchEntrant
  try dsimp only
  trace_chain with hops_leaf

/-- `injectYield` emits or answers nothing. -/
theorem injectYield_extends {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {yielding : Bool} {it : Iter ν σ β ε δ ι α χ St} (h : injectYield m f yielding = some it) :
    Extends m it.machine := by
  unfold injectYield at h
  split at h
  · cases h
    trace_leaf
  · cases h

/-! ### The exit path -/

theorem fireObserver_grows {interp : RunInterp ν σ β ε δ ι α χ St} {id : FiberId}
    {exit : Exit β ε δ ι α} {acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)}
    {observer : Observer} : Grows acc.1 (fireObserver interp id exit acc observer) := by
  unfold Grows fireObserver
  try dsimp only
  (repeat' split) <;> trace_chain with hops_leaf

theorem fireObserver_fold_grows {interp : RunInterp ν σ β ε δ ι α χ St} {id : FiberId}
    {exit : Exit β ε δ ι α} {observers : List Observer}
    {acc : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)} :
    Grows acc.1 (observers.foldl (fireObserver interp id exit) acc) := by
  induction observers generalizing acc with
  | nil => exact Grows.refl _ _
  | cons o os ih =>
    rw [List.foldl_cons]
    exact Extends.trans fireObserver_grows ih

/-- The hops through the leaves and the observer fold. -/
macro "hops_observers" : tactic => `(tactic| first
  | hops_leaf
  | exact fireObserver_fold_grows)

theorem exitFiber_grows {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {exit : Exit β ε δ ι α} :
    Grows m (exitFiber interp m f exit) := by
  unfold Grows exitFiber
  try dsimp only
  (repeat' split) <;> trace_chain with hops_observers

/-- The hops through everything a command reaches. -/
macro "hops_cmd" : tactic => `(tactic| first
  | hops_observers
  | exact launchEntrant_grows
  | exact exitFiber_grows)

/-! ### `evaluatePrim` and its arms -/

theorem finishFrame_extends {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {yielding : Bool} {next : FrameStep ν σ β ε δ ι α} {events : List (FrameEvent ν σ β ε δ ι α)}
    {nested : List (Cmd ν σ β ε δ ι α)} :
    Extends m (evaluatePrim.finishFrame m f yielding next events nested).machine := by
  unfold evaluatePrim.finishFrame
  try dsimp only
  split <;> trace_leaf

theorem stepFrame_extends {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    Extends m (evaluatePrim.stepFrame interp m f yielding).machine := by
  unfold evaluatePrim.stepFrame
  try dsimp only
  exact finishFrame_extends

theorem finalizerOr_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {exit : Exit β ε δ ι α} :
    Extends m (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  try dsimp only
  (repeat' split) <;> first | trace_leaf; done | exact stepFrame_extends

theorem interruptThenJoin_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {target : FiberId} {interruptor : Option FiberId} :
    Extends m (evaluatePrim.interruptThenJoin interp m f yielding target interruptor).machine := by
  unfold evaluatePrim.interruptThenJoin
  try dsimp only
  (repeat' split) <;> trace_chain with hops_leaf

theorem withFiber_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {action : WithFiberAction ν σ β ε δ ι α χ} :
    Extends m (evaluatePrim.withFiber interp m f yielding action).machine := by
  unfold evaluatePrim.withFiber
  try dsimp only
  (repeat' split) <;> first
    | exact interruptThenJoin_extends
    | trace_chain with hops_leaf

theorem evaluatePrim_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    Extends m (evaluatePrim interp m f yielding).machine := by
  unfold evaluatePrim
  try dsimp only
  (repeat' split) <;> first
    | exact withFiber_extends
    | exact stepFrame_extends
    | exact finalizerOr_extends
    | trace_leaf; done

theorem iteration_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    Extends m (iteration interp m f yielding).machine := by
  unfold iteration
  try dsimp only
  split
  · next it h => exact injectYield_extends h
  · exact evaluatePrim_extends

/-! ### The loop -/

theorem settle_grows {id : FiberId} {rest : List (Cmd ν σ β ε δ ι α)} {it : Iter ν σ β ε δ ι α χ St} :
    Grows it.machine (settle id rest it) := by
  unfold Grows settle
  (repeat' split) <;> trace_leaf

theorem driveStep_grows {interp : RunInterp ν σ β ε δ ι α χ St} {m : RunMachine ν σ β ε δ ι α χ St}
    {cmd : Cmd ν σ β ε δ ι α} {rest : List (Cmd ν σ β ε δ ι α)} :
    Grows m (driveStep interp m cmd rest) := by
  unfold Grows
  cases cmd <;> simp only [driveStep] <;> (repeat' split) <;> first
    | exact Extends.trans iteration_extends settle_grows
    | exact Extends.trans evaluatePrim_extends settle_grows
    | trace_chain with hops_cmd

/-- The loop keeps the trace: `drive_trace_extends` is the review's form of it. -/
theorem drive_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {cmds : List (Cmd ν σ β ε δ ι α)} :
    Extends m (drive interp fuel m cmds) := by
  induction fuel generalizing m cmds with
  | zero => exact Extends.refl _
  | succ fuel ih =>
    cases cmds with
    | nil => rw [drive_nil]; exact Extends.refl _
    | cons cmd rest =>
      rw [drive_succ_cons]
      split
      · exact Extends.refl _
      · exact Extends.trans driveStep_grows ih

theorem drive_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) :
    ∃ ev, (drive interp fuel m cmds).trace = m.trace ++ ev :=
  drive_extends.exists

/-- The hops through everything a decision reaches. -/
macro "hops_loop" : tactic => `(tactic| first
  | hops_cmd
  | exact drive_extends)

/-! ### The decisions -/

theorem fire_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {owner : FiberId} :
    Extends m (stepDecision.fire interp fuel m owner) := by
  unfold stepDecision.fire
  try dsimp only
  split
  · exact Extends.refl _
  · next o _ =>
    generalize (o.dispatcher.drain).1 = tasks
    refine Extends.trans (b := (m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner)
      (by trace_leaf) ?_
    generalize (m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner = m₀
    induction tasks generalizing m₀ with
    | nil => exact Extends.refl _
    | cons task tasks ih =>
      rw [List.foldl_cons]
      refine Extends.trans ?_ (ih _)
      cases task <;> trace_chain with hops_loop

theorem fire_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    ∃ ev, (stepDecision.fire interp fuel m owner).trace = m.trace ++ ev :=
  fire_extends.exists

theorem flushAll_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel rounds : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} :
    Extends m (stepDecision.flushAll interp fuel rounds m) := by
  induction rounds generalizing m with
  | zero => exact Extends.refl _
  | succ rounds ih =>
    unfold stepDecision.flushAll
    split
    · exact Extends.refl _
    · split
      · exact Extends.refl _
      · exact Extends.trans fire_extends ih

theorem flushAll_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) :
    ∃ ev, (stepDecision.flushAll interp fuel rounds m).trace = m.trace ++ ev :=
  flushAll_extends.exists

theorem flushRoot_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat} {root : FiberId}
    {rounds : Nat} {m : RunMachine ν σ β ε δ ι α χ St} :
    Extends m (stepDecision.flushRoot interp fuel root rounds m) := by
  induction rounds generalizing m with
  | zero => exact Extends.refl _
  | succ rounds ih =>
    unfold stepDecision.flushRoot
    split
    · exact Extends.refl _
    · split
      · exact Extends.refl _
      · exact Extends.trans fire_extends ih

theorem flushRoot_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (root : FiberId) (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St) :
    ∃ ev, (stepDecision.flushRoot interp fuel root rounds m).trace = m.trace ++ ev :=
  flushRoot_extends.exists

theorem stepDecision_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {decision : RunDecision ν σ β ε δ ι α} :
    Extends m (stepDecision interp fuel m decision) := by
  cases decision <;> simp only [stepDecision] <;> (repeat' split) <;> first
    | exact fire_extends
    | exact flushAll_extends
    | trace_chain with hops_loop

theorem stepDecision_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α) :
    ∃ ev, (stepDecision interp fuel m decision).trace = m.trace ++ ev :=
  stepDecision_extends.exists

/-- The machine inside a replay result. -/
def ReplayResult.machine : ReplayResult ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St
  | ReplayResult.finished m => m
  | ReplayResult.frontier m => m
  | ReplayResult.stuck _ m => m

theorem replayEval_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {tape : List (RunDecision ν σ β ε δ ι α)} {m : RunMachine ν σ β ε δ ι α χ St} :
    Extends m (replayEval interp fuel tape m).machine := by
  induction tape generalizing m with
  | nil =>
    unfold replayEval
    (repeat' split) <;> exact Extends.refl _
  | cons decision tape ih =>
    unfold replayEval
    split
    · exact Extends.refl _
    · exact Extends.trans stepDecision_extends ih

theorem replayEval_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) :
    ∃ ev, (replayEval interp fuel tape m).machine.trace = m.trace ++ ev :=
  replayEval_extends.exists

/-! ### Fuel is monotone on one loop -/

/-- More fuel on the same commands extends the trace: the splitting law and the growth of
the trace together. -/
theorem drive_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat} (h : n ≤ n')
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)) :
    Extends (drive interp n m cmds) (drive interp n' m cmds) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [drive_add, drive_eq_driveState interp n]
  exact drive_extends

/-! ## The order on replay results -/

namespace ReplayResult

/-- A `frontier m` is below every result whose trace extends `m.trace`; a `finished` and a
`stuck` result are below themselves only. -/
def le (a b : ReplayResult ν σ β ε δ ι α χ St) : Prop :=
  match a with
  | frontier m => m.trace <+: b.machine.trace
  | finished m => b = finished m
  | stuck why m => b = stuck why m

/-- A result more fuel is not meant to refine. -/
def terminal : ReplayResult ν σ β ε δ ι α χ St → Bool
  | frontier _ => false
  | finished _ => true
  | stuck _ _ => true

theorem le_refl (a : ReplayResult ν σ β ε δ ι α χ St) : le a a := by
  cases a with
  | frontier m => exact List.prefix_rfl
  | finished m => rfl
  | stuck why m => rfl

theorem le_trans {a b c : ReplayResult ν σ β ε δ ι α χ St} (h₁ : le a b) (h₂ : le b c) : le a c := by
  cases a with
  | frontier m =>
    cases b with
    | frontier m' => exact List.IsPrefix.trans h₁ h₂
    | finished m' => unfold le at h₂; subst h₂; exact h₁
    | stuck why m' => unfold le at h₂; subst h₂; exact h₁
  | finished m => unfold le at h₁; subst h₁; exact h₂
  | stuck why m => unfold le at h₁; subst h₁; exact h₂

/-- Antisymmetry on terminal results; two frontiers with the same trace may still differ
elsewhere, so the order is a preorder on frontiers. -/
theorem le_antisymm_terminal {a b : ReplayResult ν σ β ε δ ι α χ St} (ht : a.terminal = true)
    (h₁ : le a b) (_ : le b a) : a = b := by
  cases a with
  | frontier m => cases ht
  | finished m => exact h₁.symm
  | stuck why m => exact h₁.symm

/-- A frontier is below anything that extends it. -/
theorem frontier_le {m : RunMachine ν σ β ε δ ι α χ St} {b : ReplayResult ν σ β ε δ ι α χ St}
    (h : Extends m b.machine) : le (frontier m) b := h

end ReplayResult

/-- The empty tape classifies the machine and keeps it. -/
theorem replayEval_nil_machine (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) : (replayEval interp fuel [] m).machine = m := by
  unfold replayEval
  (repeat' split) <;> rfl

/-! ## The receipts: what a decision ran, and whether its fuel sufficed

`settled` is "the commands were exhausted or the machine halted": a halted loop keeps its
commands (`driveState_stuck`), so exhaustion alone would call a stuck run insufficient. -/

/-- The loop stopped for a reason other than fuel. -/
def settled (r : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) : Bool :=
  r.2.isEmpty || r.1.stuck.isSome

/-- A settled loop is the loop at every larger fuel, commands included. -/
theorem driveState_settled_add (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : settled (driveState interp fuel m cmds) = true) :
    ∀ k, driveState interp (fuel + k) m cmds = driveState interp fuel m cmds := by
  intro k
  unfold settled at h
  rw [driveState_add]
  rcases Bool.or_eq_true_iff.mp h with hdone | hstuck
  · have h2 := List.isEmpty_iff.mp hdone
    rw [h2, driveState_nil]
    exact Prod.ext rfl h2.symm
  · exact driveState_stuck interp k _ _ hstuck

theorem drive_stable_of_settled (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α))
    (h : settled (driveState interp fuel m cmds) = true) :
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds := by
  intro k
  rw [drive_eq_driveState, drive_eq_driveState, driveState_settled_add interp fuel m cmds h k]

/-- The commands a task runs (`stepDecision.fire`, `Fibers.lean`). -/
def taskCmds : Task ν σ β ε δ ι α → List (Cmd ν σ β ε δ ι α)
  | Task.start child => [Cmd.evaluate child, Cmd.drainDue]
  | Task.resume target token answer => [Cmd.resume target token answer, Cmd.drainDue]

/-- One task of `fire`, with the receipt so far. -/
def fireStep (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (owner : FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St × Bool) (task : Task ν σ β ε δ ι α) :
    RunMachine ν σ β ε δ ι α χ St × Bool :=
  let r := driveState interp fuel (acc.1.emit [RunEvent.ranTask owner task]) (taskCmds task)
  (r.1, acc.2 && settled r)

/-- `fire` with its receipt: did every task's loop settle? -/
def fireState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) : RunMachine ν σ β ε δ ι α χ St × Bool :=
  match m.fiber? owner with
  | none => (m, true)
  | some o =>
    (o.dispatcher.drain).1.foldl (fireStep interp fuel owner)
      ((m.update { o with dispatcher := (o.dispatcher.drain).2 }).disarm owner, true)

theorem fireTasks_eq (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (owner : FiberId)
    (tasks : List (Task ν σ β ε δ ι α)) (m₀ : RunMachine ν σ β ε δ ι α χ St) (b : Bool) :
    tasks.foldl (fun m task =>
        let m := m.emit [RunEvent.ranTask owner task]
        match task with
        | Task.start child => drive interp fuel m [Cmd.evaluate child, Cmd.drainDue]
        | Task.resume target token answer =>
          drive interp fuel m [Cmd.resume target token answer, Cmd.drainDue]) m₀ =
      (tasks.foldl (fireStep interp fuel owner) (m₀, b)).1 := by
  generalize hF : (fun (m : RunMachine ν σ β ε δ ι α χ St) (task : Task ν σ β ε δ ι α) =>
      let m := m.emit [RunEvent.ranTask owner task]
      match task with
      | Task.start child => drive interp fuel m [Cmd.evaluate child, Cmd.drainDue]
      | Task.resume target token answer =>
        drive interp fuel m [Cmd.resume target token answer, Cmd.drainDue]) = F
  have hstep : ∀ (m : RunMachine ν σ β ε δ ι α χ St) (task : Task ν σ β ε δ ι α),
      F m task = (driveState interp fuel (m.emit [RunEvent.ranTask owner task]) (taskCmds task)).1 := by
    intro m task
    rw [← hF]
    cases task <;> simp only [taskCmds, drive_eq_driveState]
  induction tasks generalizing m₀ b with
  | nil => rfl
  | cons task tasks ih =>
    rw [List.foldl_cons, List.foldl_cons, hstep]
    exact ih _ _

theorem fire_eq_fireState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    stepDecision.fire interp fuel m owner = (fireState interp fuel m owner).1 := by
  cases h : m.fiber? owner with
  | none => rw [fire_unknown interp fuel m owner h]; simp only [fireState, h]
  | some o =>
    rw [fire_eq interp fuel m owner o h]
    simp only [fireState, h]
    exact fireTasks_eq interp fuel owner _ _ true

/-- Once a task's loop did not settle, the receipt stays false. -/
theorem fireTasks_false (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (owner : FiberId)
    (tasks : List (Task ν σ β ε δ ι α)) (m₀ : RunMachine ν σ β ε δ ι α χ St) :
    (tasks.foldl (fireStep interp fuel owner) (m₀, false)).2 = false := by
  induction tasks generalizing m₀ with
  | nil => rfl
  | cons task tasks ih => simp only [List.foldl_cons, fireStep, Bool.false_and]; exact ih _

/-- A fire whose every loop settled is the same fire at every larger fuel. -/
theorem fireTasks_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel k : Nat) (owner : FiberId)
    (tasks : List (Task ν σ β ε δ ι α)) (m₀ : RunMachine ν σ β ε δ ι α χ St) (b : Bool)
    (h : (tasks.foldl (fireStep interp fuel owner) (m₀, b)).2 = true) :
    tasks.foldl (fireStep interp (fuel + k) owner) (m₀, b) =
      tasks.foldl (fireStep interp fuel owner) (m₀, b) := by
  induction tasks generalizing m₀ b with
  | nil => rfl
  | cons task tasks ih =>
    simp only [List.foldl_cons] at h ⊢
    have hset : settled (driveState interp fuel (m₀.emit [RunEvent.ranTask owner task]) (taskCmds task))
        = true := by
      cases hs : settled (driveState interp fuel (m₀.emit [RunEvent.ranTask owner task]) (taskCmds task))
      · exfalso
        have : (fireStep interp fuel owner (m₀, b) task).2 = false := by
          simp only [fireStep, hs, Bool.and_false]
        rw [show fireStep interp fuel owner (m₀, b) task =
            ((fireStep interp fuel owner (m₀, b) task).1, false) from Prod.ext rfl this] at h
        rw [fireTasks_false] at h
        cases h
      · rfl
    have hstep : fireStep interp (fuel + k) owner (m₀, b) task = fireStep interp fuel owner (m₀, b) task := by
      simp only [fireStep, driveState_settled_add interp fuel _ _ hset k]
    rw [hstep]
    exact ih _ _ h

theorem fireState_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (h : (fireState interp fuel m owner).2 = true) :
    ∀ k, fireState interp (fuel + k) m owner = fireState interp fuel m owner := by
  intro k
  unfold fireState at h ⊢
  cases hf : m.fiber? owner with
  | none => rfl
  | some o =>
    rw [hf] at h
    exact fireTasks_stable interp fuel k owner _ _ true h

theorem fire_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId)
    (h : (fireState interp fuel m owner).2 = true) :
    ∀ k, stepDecision.fire interp (fuel + k) m owner = stepDecision.fire interp fuel m owner := by
  intro k
  rw [fire_eq_fireState, fire_eq_fireState, fireState_stable interp fuel m owner h k]

/-- `flushAll` with its receipt: did the rounds stop with nothing armed (or a halt) rather
than run out, every fire settled? -/
def flushAllState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
    Nat → RunMachine ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St × Bool
  | 0, m => (m, m.armed.isEmpty || m.stuck.isSome)
  | rounds + 1, m =>
    match m.armed with
    | [] => (m, true)
    | owner :: _ =>
      if m.stuck.isSome then (m, true)
      else
        let r := fireState interp fuel m owner
        let s := flushAllState interp fuel rounds r.1
        (s.1, r.2 && s.2)

theorem flushAll_eq_flushAllState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) :
    stepDecision.flushAll interp fuel rounds m = (flushAllState interp fuel rounds m).1 := by
  induction rounds generalizing m with
  | zero => rfl
  | succ rounds ih =>
    cases ha : m.armed with
    | nil => rw [flushAll_idle interp fuel rounds m ha]; simp only [flushAllState, ha]
    | cons owner rest =>
      cases hs : m.stuck with
      | some why =>
        simp only [stepDecision.flushAll, flushAllState, ha, hs, Option.isSome_some, if_true]
      | none =>
        rw [flushAll_round interp fuel rounds m owner rest ha hs, ih, fire_eq_fireState]
        simp only [flushAllState, ha, hs, Option.isSome_none, Bool.false_eq_true, if_false]

/-- A flush that stopped on its own is the same flush at every larger fuel and round count. -/
theorem flushAllState_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (h : (flushAllState interp fuel rounds m).2 = true) :
    ∀ k j, flushAllState interp (fuel + k) (rounds + j) m = flushAllState interp fuel rounds m := by
  intro k j
  induction rounds generalizing m j with
  | zero =>
    simp only [flushAllState] at h
    rw [Nat.zero_add]
    cases j with
    | zero => simp only [flushAllState, h]
    | succ j =>
      cases ha : m.armed with
      | nil => simp only [flushAllState, ha, List.isEmpty_nil, Bool.true_or]
      | cons owner rest =>
        rw [ha] at h
        simp only [List.isEmpty_cons, Bool.false_or] at h
        simp only [flushAllState, ha, h, if_true, List.isEmpty_cons, Bool.false_or]
  | succ rounds ih =>
    rw [Nat.succ_add]
    cases ha : m.armed with
    | nil => simp only [flushAllState, ha]
    | cons owner rest =>
      cases hs : m.stuck.isSome
      · simp only [flushAllState, ha, hs, Bool.false_eq_true, if_false] at h ⊢
        obtain ⟨hr, hs'⟩ := Bool.and_eq_true_iff.mp h
        rw [fireState_stable interp fuel m owner hr k, ih _ hs']
      · simp only [flushAllState, ha, hs, if_true]

theorem flushAll_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (h : (flushAllState interp fuel rounds m).2 = true) :
    ∀ k j, stepDecision.flushAll interp (fuel + k) (rounds + j) m =
      stepDecision.flushAll interp fuel rounds m := by
  intro k j
  rw [flushAll_eq_flushAllState, flushAll_eq_flushAllState, flushAllState_stable interp fuel rounds m h k j]

/-- `flushRoot` with its receipt (`runSyncExit`'s flush of the root's dispatcher): did the
rounds stop on an empty dispatcher (or a halt) rather than run out, every fire settled? -/
def flushRootState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (root : FiberId) :
    Nat → RunMachine ν σ β ε δ ι α χ St → RunMachine ν σ β ε δ ι α χ St × Bool
  | 0, m =>
    match m.fiber? root with
    | none => (m, true)
    | some o => (m, o.dispatcher.buckets.isEmpty || m.stuck.isSome)
  | rounds + 1, m =>
    match m.fiber? root with
    | none => (m, true)
    | some o =>
      if o.dispatcher.buckets.isEmpty || m.stuck.isSome then (m, true)
      else
        let r := fireState interp fuel m root
        let s := flushRootState interp fuel root rounds r.1
        (s.1, r.2 && s.2)

theorem flushRoot_eq_flushRootState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (root : FiberId) (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St) :
    stepDecision.flushRoot interp fuel root rounds m = (flushRootState interp fuel root rounds m).1 := by
  induction rounds generalizing m with
  | zero => cases hf : m.fiber? root <;> simp only [stepDecision.flushRoot, flushRootState, hf]
  | succ rounds ih =>
    cases hf : m.fiber? root with
    | none => simp only [stepDecision.flushRoot, flushRootState, hf]
    | some o =>
      cases hb : o.dispatcher.buckets.isEmpty || m.stuck.isSome
      · simp only [stepDecision.flushRoot, flushRootState, hf, hb, Bool.false_eq_true, if_false]
        rw [ih, fire_eq_fireState]
      · simp only [stepDecision.flushRoot, flushRootState, hf, hb, if_true]

theorem flushRootState_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (root : FiberId)
    (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (h : (flushRootState interp fuel root rounds m).2 = true) :
    ∀ k j, flushRootState interp (fuel + k) root (rounds + j) m =
      flushRootState interp fuel root rounds m := by
  intro k j
  induction rounds generalizing m j with
  | zero =>
    rw [Nat.zero_add]
    cases j with
    | zero => rfl
    | succ j =>
      cases hf : m.fiber? root with
      | none => simp only [flushRootState, hf]
      | some o =>
        simp only [flushRootState, hf] at h
        simp only [flushRootState, hf, h, if_true]
  | succ rounds ih =>
    rw [Nat.succ_add]
    cases hf : m.fiber? root with
    | none => simp only [flushRootState, hf]
    | some o =>
      cases hb : o.dispatcher.buckets.isEmpty || m.stuck.isSome
      · simp only [flushRootState, hf, hb, Bool.false_eq_true, if_false] at h ⊢
        obtain ⟨hr, hs'⟩ := Bool.and_eq_true_iff.mp h
        rw [fireState_stable interp fuel m root hr k, ih _ hs']
      · simp only [flushRootState, hf, hb, if_true]

theorem flushRoot_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (root : FiberId)
    (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (h : (flushRootState interp fuel root rounds m).2 = true) :
    ∀ k j, stepDecision.flushRoot interp (fuel + k) root (rounds + j) m =
      stepDecision.flushRoot interp fuel root rounds m := by
  intro k j
  rw [flushRoot_eq_flushRootState, flushRoot_eq_flushRootState,
    flushRootState_stable interp fuel root rounds m h k j]

/-- One decision with its receipt: the machine `stepDecision` leaves, and whether the fuel
sufficed for it — every loop it ran settled, and a `flush` stopped on its own. -/
def stepDecisionState (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) : RunDecision ν σ β ε δ ι α → RunMachine ν σ β ε δ ι α χ St × Bool
  | RunDecision.fire owner => fireState interp fuel m owner
  | RunDecision.flush => flushAllState interp fuel fuel m
  | RunDecision.evaluate id => loop (driveState interp fuel m [Cmd.evaluate id, Cmd.drainDue])
  | RunDecision.yieldVerdict id verdict =>
    (m.modify id fun f => { f with yieldOverride := some verdict }, true)
  | RunDecision.answerAsync id token answer =>
    loop (driveState interp fuel m [Cmd.resume id token answer, Cmd.drainDue])
  | RunDecision.interruptFrom interruptor annotations target =>
    match m.fiber? target with
    | none => (m, true)
    | some t =>
      let (t, applyNow) := interruptRecord interp interruptor annotations t
      let m := m.emit [RunEvent.interruptRecorded interruptor target]
      let m := if t.frame.deferredInterrupt && t.running then
        m.emit [RunEvent.interruptDeferred target] else m
      let m := m.update t
      if applyNow then loop (driveState interp fuel m [Cmd.evaluate target, Cmd.drainDue]) else (m, true)
  | RunDecision.installMiddleware => ({ m with middlewareInstalled := true }, true)
where
  /-- A loop's receipt: its machine, and whether it settled. -/
  loop (r : RunMachine ν σ β ε δ ι α χ St × List (Cmd ν σ β ε δ ι α)) :
      RunMachine ν σ β ε δ ι α χ St × Bool := (r.1, settled r)

theorem stepDecision_eq_state (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α) :
    stepDecision interp fuel m decision = (stepDecisionState interp fuel m decision).1 := by
  cases decision <;> simp only [stepDecision, stepDecisionState, stepDecisionState.loop,
    fire_eq_fireState, flushAll_eq_flushAllState, drive_eq_driveState] <;>
    (repeat' split) <;> first | rfl | simp_all

/-- A decision whose fuel sufficed is the same decision, receipt included, at every larger
fuel. -/
theorem stepDecisionState_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (h : (stepDecisionState interp fuel m decision).2 = true) :
    ∀ k, stepDecisionState interp (fuel + k) m decision = stepDecisionState interp fuel m decision := by
  intro k
  cases decision with
  | fire owner => exact fireState_stable interp fuel m owner h k
  | flush => exact flushAllState_stable interp fuel fuel m h k k
  | evaluate id =>
    simp only [stepDecisionState, stepDecisionState.loop] at h ⊢
    rw [driveState_settled_add interp fuel m _ h k]
  | answerAsync id token answer =>
    simp only [stepDecisionState, stepDecisionState.loop] at h ⊢
    rw [driveState_settled_add interp fuel m _ h k]
  | interruptFrom interruptor annotations target =>
    simp only [stepDecisionState, stepDecisionState.loop] at h ⊢
    split at h
    · rfl
    · rename_i f _
      cases ha : (interruptRecord interp interruptor annotations f).2
      · simp only [Bool.false_eq_true, if_false]
      · rw [ha] at h
        simp only [if_true] at h ⊢
        rw [driveState_settled_add interp fuel _ _ h k]
  | yieldVerdict id verdict => rfl
  | installMiddleware => rfl

theorem stepDecision_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (h : (stepDecisionState interp fuel m decision).2 = true) :
    ∀ k, stepDecision interp (fuel + k) m decision = stepDecision interp fuel m decision := by
  intro k
  rw [stepDecision_eq_state, stepDecision_eq_state, stepDecisionState_stable interp fuel m decision h k]

/-! ## Sufficiency along a tape, and stability -/

/-- Fuel `fuel` suffices for `tape` from `m`: every decision's receipt says so, on the
machine the previous decisions left; a stuck machine ends the replay and needs nothing.
Decidable by construction — it is the replay itself, with the receipts. -/
def Suffices (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) :
    List (RunDecision ν σ β ε δ ι α) → RunMachine ν σ β ε δ ι α χ St → Bool
  | [], _ => true
  | decision :: tape, m =>
    match m.stuck with
    | some _ => true
    | none =>
      let r := stepDecisionState interp fuel m decision
      r.2 && Suffices interp fuel tape r.1

/-- Compatibility: under `Suffices`, every larger fuel replays to the same result. -/
theorem replay_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St)
    (h : Suffices interp fuel tape m = true) :
    ∀ k, replayEval interp (fuel + k) tape m = replayEval interp fuel tape m := by
  intro k
  induction tape generalizing m with
  | nil => rfl
  | cons decision tape ih =>
    unfold replayEval
    cases hs : m.stuck with
    | some why => rfl
    | none =>
      simp only [Suffices, hs] at h
      obtain ⟨hr, hrest⟩ := Bool.and_eq_true_iff.mp h
      rw [stepDecision_stable interp fuel m decision hr k]
      apply ih
      rw [stepDecision_eq_state]
      exact hrest

/-- A sufficient fuel stays sufficient. -/
theorem Suffices_mono (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St)
    (h : Suffices interp fuel tape m = true) : ∀ k, Suffices interp (fuel + k) tape m = true := by
  intro k
  induction tape generalizing m with
  | nil => rfl
  | cons decision tape ih =>
    cases hs : m.stuck with
    | some why => simp only [Suffices, hs]
    | none =>
      simp only [Suffices, hs] at h ⊢
      obtain ⟨hr, hrest⟩ := Bool.and_eq_true_iff.mp h
      rw [stepDecisionState_stable interp fuel m decision hr k, hr, ih _ hrest]
      rfl

theorem Suffices_of_le (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat} (h : n ≤ n')
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St)
    (hs : Suffices interp n tape m = true) : Suffices interp n' tape m = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact Suffices_mono interp n tape m hs k

/-- Monotonicity where it is stability: under `Suffices`, more fuel is the same result. -/
theorem replay_obs_mono_of_suffices (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St)
    (hs : Suffices interp n tape m = true) :
    ReplayResult.le (replayEval interp n tape m) (replayEval interp n' tape m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [replay_stable interp n tape m hs k]
  exact ReplayResult.le_refl _

/-! ## Monotonicity on one loop, per decision kind

The decisions that run one loop or none. `fire` and `flush` refresh the fuel between tasks
and rounds and are refused (`APPROX-FB-REFRESH`). -/

/-- The decision runs at most one `drive`. -/
def SingleLoop : RunDecision ν σ β ε δ ι α → Bool
  | RunDecision.fire _ => false
  | RunDecision.flush => false
  | _ => true

/-- More fuel on a single-loop decision extends the trace. -/
theorem stepDecision_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat} (h : n ≤ n')
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) :
    Extends (stepDecision interp n m decision) (stepDecision interp n' m decision) := by
  cases decision with
  | fire owner => cases hd
  | flush => cases hd
  | evaluate id => exact drive_trace_mono interp h m _
  | answerAsync id token answer => exact drive_trace_mono interp h m _
  | yieldVerdict id verdict => exact Extends.refl _
  | installMiddleware => exact Extends.refl _
  | interruptFrom interruptor annotations target =>
    simp only [stepDecision]
    split
    · exact Extends.refl _
    · split
      · exact drive_trace_mono interp h _ _
      · exact Extends.refl _

/-- A single-loop decision that halted is the same decision at every larger fuel. -/
theorem stepDecision_stuck_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) (hs : (stepDecision interp fuel m decision).stuck.isSome = true) :
    ∀ k, stepDecision interp (fuel + k) m decision = stepDecision interp fuel m decision := by
  intro k
  cases decision with
  | fire owner => cases hd
  | flush => cases hd
  | evaluate id =>
    simp only [stepDecision] at hs ⊢
    rw [drive_eq_driveState] at hs
    exact drive_stable_of_stuck interp fuel m _ hs k
  | answerAsync id token answer =>
    simp only [stepDecision] at hs ⊢
    rw [drive_eq_driveState] at hs
    exact drive_stable_of_stuck interp fuel m _ hs k
  | yieldVerdict id verdict => rfl
  | installMiddleware => rfl
  | interruptFrom interruptor annotations target =>
    simp only [stepDecision] at hs ⊢
    split at hs
    · rfl
    · rename_i f _
      cases ha : (interruptRecord interp interruptor annotations f).2
      · simp only [Bool.false_eq_true, if_false]
      · rw [ha] at hs
        simp only [if_true] at hs ⊢
        rw [drive_eq_driveState] at hs
        exact drive_stable_of_stuck interp fuel _ _ hs k

/-- The frontier half of monotonicity on a one-decision tape: a frontier at fuel `n` is
below the result at any larger fuel. -/
theorem replay_frontier_mono_single (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) {m₁ : RunMachine ν σ β ε δ ι α χ St}
    (hf : replayEval interp n [decision] m = ReplayResult.frontier m₁) :
    ReplayResult.le (ReplayResult.frontier m₁) (replayEval interp n' [decision] m) := by
  refine ReplayResult.frontier_le ?_
  unfold replayEval at hf ⊢
  cases hs : m.stuck with
  | some why =>
    rw [hs] at hf
    change ReplayResult.stuck why m = ReplayResult.frontier m₁ at hf
    cases hf
  | none =>
    rw [hs] at hf
    change replayEval interp n [] (stepDecision interp n m decision) = ReplayResult.frontier m₁ at hf
    change Extends m₁ (replayEval interp n' [] (stepDecision interp n' m decision)).machine
    rw [replayEval_nil_machine]
    have : m₁ = stepDecision interp n m decision := by
      revert hf
      unfold replayEval
      (repeat' split) <;> intro hf <;> cases hf <;> rfl
    rw [this]
    exact stepDecision_trace_mono interp h m decision hd

/-- The stuck half: a halt at fuel `n` is the result at every larger fuel. -/
theorem replay_stuck_mono_single (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) {why : Stuck} {m₁ : RunMachine ν σ β ε δ ι α χ St}
    (hst : replayEval interp n [decision] m = ReplayResult.stuck why m₁) :
    ReplayResult.le (ReplayResult.stuck why m₁) (replayEval interp n' [decision] m) := by
  show replayEval interp n' [decision] m = ReplayResult.stuck why m₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  unfold replayEval at hst ⊢
  cases hs : m.stuck with
  | some why' => rw [hs] at hst; exact hst
  | none =>
    rw [hs] at hst
    change replayEval interp n [] (stepDecision interp n m decision) = ReplayResult.stuck why m₁ at hst
    change replayEval interp (n + k) [] (stepDecision interp (n + k) m decision) = ReplayResult.stuck why m₁
    have hstuck : (stepDecision interp n m decision).stuck.isSome = true := by
      revert hst
      unfold replayEval
      (repeat' split) <;> intro hst <;> cases hst <;> simp_all
    rw [stepDecision_stuck_stable interp n m decision hd hstuck k]
    exact hst

/-! ## The colimit: the least sufficient fuel under a bound

A bounded search, by hand: there is no `Nat.find` here. -/

/-- The least `f ≤ bound` at which `p` holds, by recursion on the bound. -/
def leastUpTo (p : Nat → Bool) : Nat → Option Nat
  | 0 => if p 0 then some 0 else none
  | n + 1 =>
    match leastUpTo p n with
    | some f => some f
    | none => if p (n + 1) then some (n + 1) else none

theorem leastUpTo_none {p : Nat → Bool} :
    ∀ {n : Nat}, leastUpTo p n = none → ∀ g, g ≤ n → p g = false := by
  intro n
  induction n with
  | zero =>
    intro h g le
    have : g = 0 := Nat.le_zero.mp le
    subst this
    cases hp : p 0
    · rfl
    · simp [leastUpTo, hp] at h
  | succ n ih =>
    intro h g le
    cases inner : leastUpTo p n with
    | some f => rw [leastUpTo, inner] at h; cases h
    | none =>
      rw [leastUpTo, inner] at h
      cases hp : p (n + 1)
      · rcases Nat.lt_or_ge g (n + 1) with lt | ge
        · exact ih inner g (Nat.le_of_lt_succ lt)
        · have : g = n + 1 := Nat.le_antisymm le ge
          subst this
          exact hp
      · simp [hp] at h

theorem leastUpTo_sound {p : Nat → Bool} :
    ∀ {n f : Nat}, leastUpTo p n = some f → p f = true := by
  intro n
  induction n with
  | zero =>
    intro f h
    cases hp : p 0
    · simp [leastUpTo, hp] at h
    · simp [leastUpTo, hp] at h; subst h; exact hp
  | succ n ih =>
    intro f h
    cases inner : leastUpTo p n with
    | some f' => rw [leastUpTo, inner] at h; cases h; exact ih inner
    | none =>
      rw [leastUpTo, inner] at h
      cases hp : p (n + 1)
      · simp [hp] at h
      · simp [hp] at h; subst h; exact hp

theorem leastUpTo_le {p : Nat → Bool} :
    ∀ {n f : Nat}, leastUpTo p n = some f → f ≤ n := by
  intro n
  induction n with
  | zero =>
    intro f h
    cases hp : p 0
    · simp [leastUpTo, hp] at h
    · simp [leastUpTo, hp] at h; omega
  | succ n ih =>
    intro f h
    cases inner : leastUpTo p n with
    | some f' =>
      rw [leastUpTo, inner] at h
      cases h
      exact Nat.le_succ_of_le (ih inner)
    | none =>
      rw [leastUpTo, inner] at h
      cases hp : p (n + 1)
      · simp [hp] at h
      · simp [hp] at h; omega

theorem leastUpTo_least {p : Nat → Bool} :
    ∀ {n f : Nat}, leastUpTo p n = some f → ∀ g, g < f → p g = false := by
  intro n
  induction n with
  | zero =>
    intro f h g lt
    cases hp : p 0
    · simp [leastUpTo, hp] at h
    · simp [leastUpTo, hp] at h; omega
  | succ n ih =>
    intro f h g lt
    cases inner : leastUpTo p n with
    | some f' => rw [leastUpTo, inner] at h; cases h; exact ih inner g lt
    | none =>
      rw [leastUpTo, inner] at h
      cases hp : p (n + 1)
      · simp [hp] at h
      · simp [hp] at h
        subst h
        exact leastUpTo_none inner g (Nat.le_of_lt_succ lt)

theorem leastUpTo_isSome {p : Nat → Bool} {n g : Nat} (holds : p g = true) (le : g ≤ n) :
    (leastUpTo p n).isSome = true := by
  cases h : leastUpTo p n with
  | some f => rfl
  | none => rw [leastUpTo_none h g le] at holds; cases holds

/-- The least fuel found under a larger bound is the same. -/
theorem leastUpTo_bound_mono {p : Nat → Bool} {n f : Nat} (found : leastUpTo p n = some f) :
    ∀ {m : Nat}, n ≤ m → leastUpTo p m = some f := by
  intro m
  induction m with
  | zero => intro le; rw [Nat.le_zero.mp le] at found; exact found
  | succ m ih =>
    intro le
    rcases Nat.lt_or_ge n (m + 1) with lt | ge
    · have inner := ih (Nat.le_of_lt_succ lt)
      rw [leastUpTo, inner]
    · have : n = m + 1 := Nat.le_antisymm le ge
      subst this
      exact found

/-- The least fuel under `bound` that suffices for `tape` from `m`; `none` records "none
under this bound", never divergence. -/
def leastSufficient (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) (bound : Nat) :
    Option Nat :=
  leastUpTo (fun fuel => Suffices interp fuel tape m) bound

theorem leastSufficient_sound (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat}
    (found : leastSufficient interp tape m bound = some f) : Suffices interp f tape m = true :=
  leastUpTo_sound found

theorem leastSufficient_least (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat}
    (found : leastSufficient interp tape m bound = some f) :
    ∀ g, g < f → Suffices interp g tape m = false :=
  leastUpTo_least found

theorem leastSufficient_le (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat}
    (found : leastSufficient interp tape m bound = some f) : f ≤ bound :=
  leastUpTo_le found

/-- Raising the bound cannot change a least sufficient fuel that already exists. -/
theorem leastSufficient_bound_mono (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat}
    (found : leastSufficient interp tape m bound = some f) {bound' : Nat} (le : bound ≤ bound') :
    leastSufficient interp tape m bound' = some f :=
  leastUpTo_bound_mono found le

theorem leastSufficient_isSome (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {n bound : Nat}
    (hs : Suffices interp n tape m = true) (le : n ≤ bound) :
    (leastSufficient interp tape m bound).isSome = true :=
  leastUpTo_isSome hs le

/-- Coherence: the replay at the least sufficient fuel is the replay at every fuel above
it — the join of the chain, reached at a finite stage. -/
theorem replay_colimit (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat}
    (found : leastSufficient interp tape m bound = some f) :
    ∀ k, replayEval interp (f + k) tape m = replayEval interp f tape m :=
  replay_stable interp f tape m (leastSufficient_sound interp tape m found)

/-- Any sufficient fuel under the bound finds the colimit, and finds the same one: the
searched fuel is at most that fuel, and the replay there is the replay at the searched
fuel. The colimit is a function of the tape and the machine, not of the bound or of the
fuel that found it. -/
theorem replay_colimit_eq_of_sufficient (interp : RunInterp ν σ β ε δ ι α χ St)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) {n bound : Nat}
    (hs : Suffices interp n tape m = true) (le : n ≤ bound) :
    ∃ f, leastSufficient interp tape m bound = some f ∧ f ≤ n ∧
      replayEval interp n tape m = replayEval interp f tape m := by
  have isSome := leastSufficient_isSome interp tape m hs le
  cases found : leastSufficient interp tape m bound with
  | none => rw [found] at isSome; cases isSome
  | some f =>
    have fle : f ≤ n := by
      rcases Nat.lt_or_ge n f with lt | ge
      · have := leastSufficient_least interp tape m found n lt
        rw [hs] at this
        cases this
      · exact ge
    refine ⟨f, rfl, fle, ?_⟩
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le fle
    exact replay_colimit interp tape m found k

end Effect4.Machine
