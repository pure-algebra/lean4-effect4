import Effect4.Machine.Fibers
import Effect4.Laws.Machine.Clauses

/-!
# Machine.Approximation — the fuel laws over the live fiber machine (G2)

Review: `docs/research/2026-09-05-effects-papers-review.md` §3 G2. Packet:
`Test/contracts/machine-approximation.contract.md`. Batteries:
`Test/Machine/Runtime/ApproximationContract.lean` (the guards and the rows `E4-APPROX-CE-001`
to `E4-APPROX-CE-004`) and `Test/Machine/Runtime/ApproximationAxiomReport.lean`. The name
mirrors the archived Flow module (`git:c407ab7:Effect4/Semantics/Approximation.lean`); the
machine under it is `src/Effect4/Machine/Fibers.lean`, whose loop `drive` spends one fuel per
command and retains unfinished commands in `driveState` when the fuel is gone.
Tasks, flush rounds and replay decisions stop at the first unfinished unit of work.

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
  hooks return stores, so nothing the frame instance's `RunInterp` chooses can
  shrink a trace. An arbitrary D1 `FiberEvaluator` can return a whole machine:
  its trace premise is explicit in `drive_extends_of_step` and
  `drive_trace_mono_of_step` (`CORE-FB-TRACE`).
* **Fuel is monotone across work boundaries.** `drive_trace_mono`, `fire_trace_mono`,
  `flushAll_trace_mono`, and `stepDecision_trace_mono_all` extend the trace at every
  larger budget. `replay_obs_mono` proves the replay order along every tape.
* **The order and the three laws over `replayEval`.** `ReplayResult.le`: a `frontier m` is
  below every result whose trace extends `m.trace`; `finished` and `stuck` are below
  themselves only. Reflexive, transitive, antisymmetric on terminal results. Then the
  receipts `fireState`, `flushAllState`, `flushRootState`, `stepDecisionState` and the
  decidable predicate `Suffices interp fuel tape m` ("every loop a decision ran exhausted its
  commands, every `flush` stopped with nothing armed before its rounds ran out"), with
  `replay_stable` (under `Suffices`, every larger fuel replays to the same result),
  `Suffices_mono` (a sufficient fuel stays sufficient), `replay_obs_mono_of_suffices`, the
  terminal-implies-sufficient law `Suffices_of_replay_terminal`, the
  frontier and stuck halves of monotonicity on a one-decision tape
  (`replay_frontier_mono_single`, `replay_stuck_mono_single`), and the bounded search
  `leastSufficient` with `replay_colimit`: the fuel it finds is sufficient, every smaller
  fuel is not, the result does not move once one sufficient fuel is under the bound
  (`leastSufficient_bound_mono`, `replay_colimit_eq_of_sufficient`).

What is deliberately not said, each named so it is a refusal and not an omission:

* `APPROX-FB-REFRESH` and `APPROX-FB-FINISHED` are retired by the first runtime
  proof-graph slice. Rows `E4-APPROX-CE-002/003/004` retain the regression witnesses:
  unfinished cleanup is a frontier, and later tasks and decisions do not run after
  exhaustion. The command loop itself remains resumable (`driveState_add`).
* Sufficiency is not termination: a tape can be exhausted with fibers still waiting.
  `E4-BEH-CE-002` records the empty-tape counterexample. No theorem here projects
  arbitrary trace-prefix order to exits and stores (`E4-BEH-CE-001`).
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
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-! ## The loop with its residue

`drive` (`Fibers.lean`) is tail recursive: every arm either returns the machine or runs one
command and goes on with one fuel less. `driveStep` is that one command, on a machine that
is not stuck; `driveState` is the loop keeping the commands it did not run. -/

/-- One fuel of `drive` on a command is `driveStep`, unless the machine is stuck. -/
theorem drive_succ_cons (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmd : Cmd ν σ β ε δ ι α κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) :
    drive interp (fuel + 1) m (cmd :: rest) =
      if m.stuck.isSome then m
      else drive interp fuel (driveStep interp m cmd rest).1 (driveStep interp m cmd rest).2 := by
  cases hs : m.stuck.isSome
  · simp [drive, driveState, hs]
  · simp [drive, driveState, hs]

theorem drive_zero (interp : RunInterp ν σ β ε δ ι α χ St κ) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) : drive interp 0 m cmds = m := rfl

theorem drive_nil (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : drive interp fuel m [] = m := by
  cases fuel <;> rfl

theorem drive_stuck (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
    (h : m.stuck.isSome = true) : drive interp fuel m cmds = m := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases cmds with
    | nil => rfl
    | cons cmd rest => rw [drive_succ_cons, if_pos h]

theorem driveState_zero (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    driveState interp 0 m cmds = (m, cmds) := rfl

theorem driveState_nil (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : driveState interp fuel m [] = (m, []) := by
  cases fuel <;> rfl

theorem driveState_succ_cons (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmd : Cmd ν σ β ε δ ι α κ)
    (rest : List (Cmd ν σ β ε δ ι α κ)) :
    driveState interp (fuel + 1) m (cmd :: rest) =
      if m.stuck.isSome then (m, cmd :: rest)
      else driveState interp fuel (driveStep interp m cmd rest).1 (driveStep interp m cmd rest).2 :=
  rfl

/-- A stuck machine keeps its commands, whatever the fuel. -/
theorem driveState_stuck (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
    (h : m.stuck.isSome = true) : driveState interp fuel m cmds = (m, cmds) := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
    cases cmds with
    | nil => rfl
    | cons cmd rest => rw [driveState_succ_cons, if_pos h]

/-- `drive` is the machine half of `driveState`. -/
theorem drive_eq_driveState (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    drive interp fuel m cmds = (driveState interp fuel m cmds).1 := rfl

/-- The splitting law: fuel `a + b` is fuel `a`, then fuel `b` on what fuel `a` left. The
corner cases compose because fuel `0` leaves everything, no command leaves nothing, and a
stuck machine leaves its commands. -/
theorem driveState_add (interp : RunInterp ν σ β ε δ ι α χ St κ) (a b : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
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

/-- A decision's public machine is the machine in its receipt. -/
theorem stepDecision_eq_state (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (decision : RunDecision ν σ β ε δ ι α) :
    stepDecision interp fuel m decision = (stepDecisionState interp fuel m decision).1 := rfl

/-- The splitting law on `drive`. -/
theorem drive_add (interp : RunInterp ν σ β ε δ ι α χ St κ) (a b : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    drive interp (a + b) m cmds =
      drive interp b (driveState interp a m cmds).1 (driveState interp a m cmds).2 := by
  rw [drive_eq_driveState, drive_eq_driveState, driveState_add]

/-- A run whose commands were exhausted never changes with more fuel: the compatibility law
on the loop. -/
theorem drive_stable_of_done (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
    (h : (driveState interp fuel m cmds).2 = []) :
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds := by
  intro k
  rw [drive_add, h, drive_nil, drive_eq_driveState]

/-- Nor does a run that halted. -/
theorem drive_stable_of_stuck (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
    (h : (driveState interp fuel m cmds).1.stuck.isSome = true) :
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds := by
  intro k
  rw [drive_add, drive_stuck _ _ _ _ h, drive_eq_driveState]

/-- Exhausted commands stay exhausted, and the machine stays. -/
theorem driveState_done_add (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
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
def Extends (m m' : RunMachine ν σ β ε δ ι α χ St κ φ η) : Prop := m.trace <+: m'.trace

theorem Extends.refl (m : RunMachine ν σ β ε δ ι α χ St κ φ η) : Extends m m := List.prefix_rfl

theorem Extends.trans {a b c : RunMachine ν σ β ε δ ι α χ St κ φ η} (h₁ : Extends a b) (h₂ : Extends b c) :
    Extends a c := List.IsPrefix.trans h₁ h₂

/-- The form the review states: the later trace is the earlier one followed by some events. -/
theorem Extends.exists {a b : RunMachine ν σ β ε δ ι α χ St κ φ η} (h : Extends a b) :
    ∃ ev, b.trace = a.trace ++ ev :=
  let ⟨ev, hev⟩ := h
  ⟨ev, hev.symm⟩

theorem emit_trace (m : RunMachine ν σ β ε δ ι α χ St) (ev : List (RunEvent ν σ β ε δ ι α χ)) :
    (m.emit ev).trace = m.trace ++ ev := by
  -- the field-local guard (direction L4): an empty emit is the trace itself
  cases ev with
  | nil => exact (List.append_nil _).symm
  | cons _ _ => rfl

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
    {mode : Supervision.ScopeMode} {scope : Nat} {target : FiberId}
    {interruptor : Option FiberId} {extra : ReasonAnnotations α} :
    Grows m (linkScope interp m mode scope target interruptor extra) := by
  unfold Grows linkScope
  try dsimp only
  (repeat' split) <;> trace_leaf

/-- The parallel close's forks (§20): one spawn per finalizer, each extending the last. -/
theorem forkFinalizers_grows {interp : RunInterp ν σ β ε δ ι α χ St}
    {host : RunFiber ν σ β ε δ ι α χ} :
    ∀ {m : RunMachine ν σ β ε δ ι α χ St} {programs : List (Prim ν σ β ε δ ι α)},
      Grows m (forkFinalizers interp m host programs)
  | m, [] => Grows.refl m []
  | m, program :: rest => by
    unfold Grows forkFinalizers
    try dsimp only
    exact Extends.trans
      (spawn_grows (interp := interp) (m := m) (parent := host) (program := program)
        (options := ⟨true, true, Supervision.MaskMode.inherit⟩))
      (forkFinalizers_grows (interp := interp) (host := host) (programs := rest))

/-- The hops through the leaves. -/
macro "hops_leaf" : tactic => `(tactic| first
  | exact spawn_grows
  | exact start_grows
  | exact interruptEach_grows
  | exact countdownPark_grows
  | exact linkScope_grows
  | exact forkFinalizers_grows)

theorem launchEntrant_grows {interp : RunInterp ν σ β ε δ ι α χ St} {raceId : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {host : RunFiber ν σ β ε δ ι α χ}
    {program : Prim ν σ β ε δ ι α} : Grows m (launchEntrant interp raceId m host program) := by
  unfold Grows launchEntrant
  try dsimp only
  trace_chain with hops_leaf

/-- `injectYield` extends the diagnostic trace and changes no store observation. -/
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
  unfold Grows exitFiber exitFiber.exitInterruptChildren exitFiber.exitStore
  try dsimp only
  (repeat' split) <;> trace_chain with hops_observers

/-! ### `evaluatePrim` and its arms -/

/-- A race's registration only marks the race (D6a). -/
theorem registerRace_extends {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ}
    {yielding : Bool} {raceId : Nat} :
    Extends m (registerRace m f yielding raceId).machine := by
  unfold registerRace
  try dsimp only
  split <;> trace_leaf

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

/-- `fiberInterruptAs` only records (D6b); the target's run and the return are commands. -/
theorem interruptAs_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {target who : FiberId} :
    Extends m (evaluatePrim.interruptAs interp m f yielding target who).machine := by
  unfold evaluatePrim.interruptAs
  try dsimp only
  (repeat' split) <;> trace_leaf

theorem withFiber_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool}
    {action : WithFiberAction ν σ β ε δ ι α χ} :
    Extends m (evaluatePrim.withFiber interp m f yielding action).machine := by
  unfold evaluatePrim.withFiber
  try dsimp only
  (repeat' split) <;> first
    | exact interruptAs_extends
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
    | exact registerRace_extends
    | trace_leaf; done
    | trace_chain with hops_leaf

theorem iteration_extends {interp : RunInterp ν σ β ε δ ι α χ St}
    {m : RunMachine ν σ β ε δ ι α χ St} {f : RunFiber ν σ β ε δ ι α χ} {yielding : Bool} :
    Extends m (iteration interp m f yielding).machine := by
  unfold iteration
  try dsimp only
  split
  · next it h => exact Extends.trans (injectYield_extends h) evaluatePrim_extends
  · exact evaluatePrim_extends

/-! ### The loop -/

theorem settle_grows {id : FiberId} {rest : List (Cmd ν σ β ε δ ι α)} {it : Iter ν σ β ε δ ι α χ St} :
    Grows it.machine (settle id rest it) := by
  unfold Grows settle
  (repeat' split) <;> trace_leaf

/-- Posting a task keeps the trace's prefix: a halt, or an update, an arm and an emit. -/
theorem postTask_extends {m : RunMachine ν σ β ε δ ι α χ St} {owner : FiberId}
    {priority : Nat} {task : Task ν σ β ε δ ι α} :
    Extends m (m.postTask owner priority task) := by
  unfold RunMachine.postTask
  split <;> trace_leaf

/-- The drain of owed resumes grows the machine: every scheduled entry is a post. -/
theorem drainOwed_grows_aux (m : RunMachine ν σ β ε δ ι α χ St) :
    ∀ (due : List (Owed (Prim ν σ β ε δ ι α))), Grows m (drainOwed m due)
  | [] => Grows.refl _ _
  | d :: rest => by
    unfold drainOwed
    split
    · exact drainOwed_grows_aux m rest
    · exact Extends.trans postTask_extends (drainOwed_grows_aux _ rest)

theorem drainOwed_grows {m : RunMachine ν σ β ε δ ι α χ St}
    {due : List (Owed (Prim ν σ β ε δ ι α))} : Grows m (drainOwed m due) :=
  drainOwed_grows_aux m due

/-- The hops of one command: the observer folds, a single fired observer (an entrant's
enrollment, D6a), an entrant's launch, the exit path, the drain of owed resumes (the scheduler surface), and a settle from an iteration the
command built itself (the registration's return, D6a). -/
macro "hops_cmd" : tactic => `(tactic| first
  | hops_observers
  | exact drainOwed_grows
  | exact fireObserver_grows
  | exact launchEntrant_grows
  | exact exitFiber_grows
  | exact settle_grows)

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

theorem fireStep_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {owner : FiberId} {acc : RunMachine ν σ β ε δ ι α χ St × Bool}
    {task : Task ν σ β ε δ ι α} :
    Extends acc.1 (fireStep interp fuel owner acc task).1 := by
  unfold fireStep
  split
  · dsimp only
    rw [← drive_eq_driveState]
    exact Extends.trans (by trace_leaf) drive_extends
  · exact Extends.refl _

theorem fireTasks_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {owner : FiberId} {acc : RunMachine ν σ β ε δ ι α χ St × Bool}
    {tasks : List (Task ν σ β ε δ ι α)} :
    Extends acc.1 (tasks.foldl (fireStep interp fuel owner) acc).1 := by
  induction tasks generalizing acc with
  | nil => exact Extends.refl _
  | cons task tasks ih =>
    rw [List.foldl_cons]
    exact Extends.trans fireStep_extends ih

theorem fire_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {owner : FiberId} :
    Extends m (stepDecision.fire interp fuel m owner) := by
  unfold stepDecision.fire fireState
  try dsimp only
  split
  · exact Extends.refl _
  · next o _ =>
    refine Extends.trans (b := (m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner)
      (by trace_leaf) ?_
    exact fireTasks_extends (interp := interp) (fuel := fuel) (owner := owner)
      (acc := ((m.update { o with dispatcher := o.dispatcher.drain.2 }).disarm owner, true))
      (tasks := o.dispatcher.drain.1)

theorem fire_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    ∃ ev, (stepDecision.fire interp fuel m owner).trace = m.trace ++ ev :=
  fire_extends.exists

theorem flushAll_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel rounds : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} :
    Extends m (stepDecision.flushAll interp fuel rounds m) := by
  change Extends m (flushAllState interp fuel rounds m).1
  induction rounds generalizing m with
  | zero => exact Extends.refl _
  | succ rounds ih =>
    unfold flushAllState
    split
    · exact Extends.refl _
    · split
      · exact Extends.refl _
      · dsimp only
        split
        · exact Extends.trans fire_extends ih
        · exact fire_extends

theorem flushAll_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) :
    ∃ ev, (stepDecision.flushAll interp fuel rounds m).trace = m.trace ++ ev :=
  flushAll_extends.exists

theorem flushRoot_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat} {root : FiberId}
    {rounds : Nat} {m : RunMachine ν σ β ε δ ι α χ St} :
    Extends m (stepDecision.flushRoot interp fuel root rounds m) := by
  change Extends m (flushRootState interp fuel root rounds m).1
  induction rounds generalizing m with
  | zero => cases h : m.fiber? root <;> simp only [flushRootState, h] <;> exact Extends.refl _
  | succ rounds ih =>
    unfold flushRootState
    split
    · exact Extends.refl _
    · split
      · exact Extends.refl _
      · dsimp only
        split
        · exact Extends.trans fire_extends ih
        · exact fire_extends

theorem flushRoot_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (root : FiberId) (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St) :
    ∃ ev, (stepDecision.flushRoot interp fuel root rounds m).trace = m.trace ++ ev :=
  flushRoot_extends.exists

/-- An advance extends the trace it starts from: every fire drains, drives and flushes, each of
which extends (the timer, A4). -/
theorem advance_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel millis : Nat} :
    ∀ {rounds : Nat} {m : RunMachine ν σ β ε δ ι α χ St},
      Extends m (advanceState interp fuel millis rounds m).1
  | 0, m => Extends.refl _
  | rounds + 1, m => by
    unfold advanceState
    split
    · exact Extends.refl _
    · rcases hc : interp.clockStep millis m.state with ⟨o, st⟩
      cases o with
      | none => exact List.prefix_rfl
      | some owed =>
        dsimp only
        have h1 : Extends m ({ m with state := st } : RunMachine ν σ β ε δ ι α χ St) :=
          List.prefix_rfl
        have h2 : Extends m
            (drainOwed ({ m with state := st } : RunMachine ν σ β ε δ ι α χ St) [owed]).1 :=
          Extends.trans h1 drainOwed_grows
        have h3 : Extends m (driveState interp fuel
            (drainOwed ({ m with state := st } : RunMachine ν σ β ε δ ι α χ St) [owed]).1
            ((drainOwed ({ m with state := st } : RunMachine ν σ β ε δ ι α χ St) [owed]).2 ++
              [Cmd.drainDue])).1 := by
          rw [← drive_eq_driveState]
          exact Extends.trans h2 drive_extends
        split
        · split
          · exact Extends.trans h3 (Extends.trans flushAll_extends advance_extends)
          · exact Extends.trans h3 flushAll_extends
        · exact h3

theorem stepDecision_extends {interp : RunInterp ν σ β ε δ ι α χ St} {fuel : Nat}
    {m : RunMachine ν σ β ε δ ι α χ St} {decision : RunDecision ν σ β ε δ ι α} :
    Extends m (stepDecision interp fuel m decision) := by
  cases decision <;> simp only [stepDecision, stepDecisionState, stepDecisionState.loop] <;>
    (repeat' split) <;> first
    | exact fire_extends
    | exact flushAll_extends
    | exact advance_extends
    | trace_chain with hops_loop

theorem stepDecision_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α) :
    ∃ ev, (stepDecision interp fuel m decision).trace = m.trace ++ ev :=
  stepDecision_extends.exists

/-- The machine inside a replay result. -/
def ReplayResult.machine : ReplayResult ν σ β ε δ ι α χ St κ φ η →
    RunMachine ν σ β ε δ ι α χ St κ φ η
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
    · dsimp only
      have hstep : Extends m (stepDecisionState interp fuel m decision).1 := by
        rw [← stepDecision_eq_state]
        exact stepDecision_extends
      split
      · exact Extends.trans hstep ih
      · exact hstep

theorem replayEval_trace_extends (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St) :
    ∃ ev, (replayEval interp fuel tape m).machine.trace = m.trace ++ ev :=
  replayEval_extends.exists

/-! ### Fuel is monotone on one loop -/

/-- An arbitrary evaluator needs a trace-preservation premise. The frame
instance discharges it with `driveStep_grows`; D1 does not constrain every
possible interpreter to retain a trace (`CORE-FB-TRACE`). -/
theorem drive_extends_of_step (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (hstep : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) cmd rest,
      Extends m (driveStep interp m cmd rest).1)
    (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ)) :
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
      · exact Extends.trans (hstep m cmd rest) (ih _ _)

theorem drive_trace_mono_of_step (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (hstep : ∀ (m : RunMachine ν σ β ε δ ι α χ St κ φ η) cmd rest,
      Extends m (driveStep interp m cmd rest).1)
    {n n' : Nat} (h : n ≤ n') (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (cmds : List (Cmd ν σ β ε δ ι α κ)) :
    Extends (drive interp n m cmds) (drive interp n' m cmds) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [drive_add, drive_eq_driveState interp n]
  exact drive_extends_of_step interp hstep k _ _

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
def le (a b : ReplayResult ν σ β ε δ ι α χ St κ φ η) : Prop :=
  match a with
  | frontier m => m.trace <+: b.machine.trace
  | finished m => b = finished m
  | stuck why m => b = stuck why m

/-- A result more fuel is not meant to refine. -/
def terminal : ReplayResult ν σ β ε δ ι α χ St κ φ η → Bool
  | frontier _ => false
  | finished _ => true
  | stuck _ _ => true

theorem le_refl (a : ReplayResult ν σ β ε δ ι α χ St κ φ η) : le a a := by
  cases a with
  | frontier m => exact List.prefix_rfl
  | finished m => rfl
  | stuck why m => rfl

theorem le_trans {a b c : ReplayResult ν σ β ε δ ι α χ St κ φ η} (h₁ : le a b) (h₂ : le b c) : le a c := by
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
theorem le_antisymm_terminal {a b : ReplayResult ν σ β ε δ ι α χ St κ φ η} (ht : a.terminal = true)
    (h₁ : le a b) (_ : le b a) : a = b := by
  cases a with
  | frontier m => cases ht
  | finished m => exact h₁.symm
  | stuck why m => exact h₁.symm

/-- A frontier is below anything that extends it. -/
theorem frontier_le {m : RunMachine ν σ β ε δ ι α χ St κ φ η} {b : ReplayResult ν σ β ε δ ι α χ St κ φ η}
    (h : Extends m b.machine) : le (frontier m) b := h

end ReplayResult

/-- The empty tape classifies the machine and keeps it. -/
theorem replayEval_nil_machine (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) : (replayEval interp fuel [] m).machine = m := by
  unfold replayEval
  (repeat' split) <;> rfl

/-- A single decision always returns its own machine, including at a fuel frontier. -/
theorem replayEval_single_machine (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hs : m.stuck = none) :
    (replayEval interp fuel [decision] m).machine = stepDecision interp fuel m decision := by
  rw [stepDecision_eq_state]
  simp only [replayEval, hs]
  (repeat' split) <;> rfl

/-! ## The receipts: what a decision ran, and whether its fuel sufficed

`settled` is "the commands were exhausted or the machine halted": a halted loop keeps its
commands (`driveState_stuck`), so exhaustion alone would call a stuck run insufficient. -/

/-- A settled loop is the loop at every larger fuel, commands included. -/
theorem driveState_settled_add (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
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

theorem drive_stable_of_settled (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (cmds : List (Cmd ν σ β ε δ ι α κ))
    (h : settled (driveState interp fuel m cmds) = true) :
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds := by
  intro k
  rw [drive_eq_driveState, drive_eq_driveState, driveState_settled_add interp fuel m cmds h k]

/-- Later tasks leave both the machine and the false receipt unchanged. -/
theorem fireTasks_stopped (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) (owner : FiberId)
    (tasks : List (Task ν σ β ε δ ι α κ)) (m₀ : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    tasks.foldl (fireStep interp fuel owner) (m₀, false) = (m₀, false) := by
  induction tasks with
  | nil => rfl
  | cons task tasks ih =>
    simpa only [List.foldl_cons, fireStep, Bool.false_eq_true, if_false] using ih

theorem fire_eq_fireState (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId) :
    stepDecision.fire interp fuel m owner = (fireState interp fuel m owner).1 := rfl

/-- Once a task's loop did not settle, the receipt stays false. -/
theorem fireTasks_false (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) (owner : FiberId)
    (tasks : List (Task ν σ β ε δ ι α κ)) (m₀ : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    (tasks.foldl (fireStep interp fuel owner) (m₀, false)).2 = false := by
  rw [fireTasks_stopped]

/-- A fire whose every loop settled is the same fire at every larger fuel. -/
theorem fireTasks_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel k : Nat) (owner : FiberId)
    (tasks : List (Task ν σ β ε δ ι α κ)) (m₀ : RunMachine ν σ β ε δ ι α χ St κ φ η) (b : Bool)
    (h : (tasks.foldl (fireStep interp fuel owner) (m₀, b)).2 = true) :
    tasks.foldl (fireStep interp (fuel + k) owner) (m₀, b) =
      tasks.foldl (fireStep interp fuel owner) (m₀, b) := by
  induction tasks generalizing m₀ b with
  | nil => rfl
  | cons task tasks ih =>
    cases b with
    | false => rw [fireTasks_stopped, fireTasks_stopped]
    | true =>
      simp only [List.foldl_cons, fireStep, if_true] at h ⊢
      cases hs : settled (driveState interp fuel (m₀.emit [RunEvent.ranTask owner task]) (taskCmds task))
      · rw [hs, fireTasks_false] at h
        cases h
      · rw [driveState_settled_add interp fuel _ _ hs k]
        simpa only [hs] using ih _ _ h

theorem fireState_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId)
    (h : (fireState interp fuel m owner).2 = true) :
    ∀ k, fireState interp (fuel + k) m owner = fireState interp fuel m owner := by
  intro k
  unfold fireState at h ⊢
  cases hf : m.fiber? owner with
  | none => rfl
  | some o =>
    rw [hf] at h
    exact fireTasks_stable interp fuel k owner _ _ true h

theorem fire_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (owner : FiberId)
    (h : (fireState interp fuel m owner).2 = true) :
    ∀ k, stepDecision.fire interp (fuel + k) m owner = stepDecision.fire interp fuel m owner := by
  intro k
  rw [fire_eq_fireState, fire_eq_fireState, fireState_stable interp fuel m owner h k]

theorem flushAll_eq_flushAllState (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    stepDecision.flushAll interp fuel rounds m = (flushAllState interp fuel rounds m).1 := rfl

/-- A flush that stopped on its own is the same flush at every larger fuel and round count. -/
theorem flushAllState_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (h : (flushAllState interp fuel rounds m).2 = true) :
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
        cases hr : (fireState interp fuel m owner).2
        · simp only [hr, Bool.false_eq_true, if_false] at h
        · simp only [hr, if_true] at h
          rw [fireState_stable interp fuel m owner hr k]
          simp only [hr, if_true]
          exact ih _ h j
      · simp only [flushAllState, ha, hs, if_true]

theorem flushAll_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (h : (flushAllState interp fuel rounds m).2 = true) :
    ∀ k j, stepDecision.flushAll interp (fuel + k) (rounds + j) m =
      stepDecision.flushAll interp fuel rounds m := by
  intro k j
  rw [flushAll_eq_flushAllState, flushAll_eq_flushAllState, flushAllState_stable interp fuel rounds m h k j]

theorem flushRoot_eq_flushRootState (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (root : FiberId) (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    stepDecision.flushRoot interp fuel root rounds m = (flushRootState interp fuel root rounds m).1 := rfl

/-- An advance whose fuel sufficed is the same advance, receipt included, at every larger fuel
and fire budget (the timer, A4): each fire's drive was settled and each flush's receipt true,
so both are stable, and the loop recurs on the same machine. -/
theorem advanceState_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel millis : Nat) :
    ∀ (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η),
      (advanceState interp fuel millis rounds m).2 = true →
      ∀ k j, advanceState interp (fuel + k) millis (rounds + j) m =
        advanceState interp fuel millis rounds m
  | 0, m, h, _, _ => by simp only [advanceState, Bool.false_eq_true] at h
  | rounds + 1, m, h, k, j => by
    rw [Nat.succ_add]
    unfold advanceState at h ⊢
    cases hs : m.stuck.isSome
    · simp only [hs, Bool.false_eq_true, if_false] at h ⊢
      rcases hc : interp.clockStep millis m.state with ⟨o, st⟩
      rw [hc] at h
      cases o with
      | none => rfl
      | some owed =>
        dsimp only at h ⊢
        split at h
        · rename_i hsd
          rw [driveState_settled_add interp fuel _ _ hsd k]
          simp only [hsd, if_true]
          split at h
          · rename_i hf
            rw [flushAllState_stable interp fuel fuel _ hf k k]
            simp only [hf, if_true]
            exact advanceState_stable interp fuel millis rounds _ h k j
          · rename_i hf
            exact absurd h hf
        · simp at h
    · simp only [hs, if_true]

theorem flushRootState_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) (root : FiberId)
    (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
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
        cases hr : (fireState interp fuel m root).2
        · simp only [hr, Bool.false_eq_true, if_false] at h
        · simp only [hr, if_true] at h
          rw [fireState_stable interp fuel m root hr k]
          simp only [hr, if_true]
          exact ih _ h j
      · simp only [flushRootState, hf, hb, if_true]

theorem flushRoot_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) (root : FiberId)
    (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (h : (flushRootState interp fuel root rounds m).2 = true) :
    ∀ k j, stepDecision.flushRoot interp (fuel + k) root (rounds + j) m =
      stepDecision.flushRoot interp fuel root rounds m := by
  intro k j
  rw [flushRoot_eq_flushRootState, flushRoot_eq_flushRootState,
    flushRootState_stable interp fuel root rounds m h k j]

/-- A decision whose fuel sufficed is the same decision, receipt included, at every larger
fuel. -/
theorem stepDecisionState_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (decision : RunDecision ν σ β ε δ ι α)
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
    cases fuel with
    | zero =>
      change m.stuck.isSome = true at h
      cases k with
      | zero => rfl
      | succ k =>
        simp only [stepDecisionState, prepareAsyncAnswer, h, if_true, stepDecisionState.loop]
        rw [driveState_stuck interp _ m _ h]
        simp [settled, h]
    | succ fuel =>
      simp only [Nat.succ_add, stepDecisionState, stepDecisionState.loop] at h ⊢
      have hd := driveState_settled_add interp (fuel + 1)
        { m with state := (prepareAsyncAnswer interp m id token answer).1 } _ h k
      rw [show fuel + 1 + k = fuel + k + 1 from Nat.succ_add fuel k] at hd
      rw [hd]
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
  | advance millis => exact advanceState_stable interp fuel millis fuel m h k k

theorem stepDecision_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St κ φ η) (decision : RunDecision ν σ β ε δ ι α)
    (h : (stepDecisionState interp fuel m decision).2 = true) :
    ∀ k, stepDecision interp (fuel + k) m decision = stepDecision interp fuel m decision := by
  intro k
  rw [stepDecision_eq_state, stepDecision_eq_state, stepDecisionState_stable interp fuel m decision h k]

/-! ## More fuel at the task and round boundaries -/

/-- A task snapshot at a larger budget extends the earlier trace. An unfinished
task stops the smaller run before the following task can emit an event. -/
theorem fireTasks_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) (fuel k : Nat)
    (owner : FiberId) (tasks : List (Task ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) (b : Bool) :
    Extends (tasks.foldl (fireStep interp fuel owner) (m, b)).1
      (tasks.foldl (fireStep interp (fuel + k) owner) (m, b)).1 := by
  induction tasks generalizing m b with
  | nil => exact Extends.refl _
  | cons task tasks ih =>
    cases b with
    | false => rw [fireTasks_stopped, fireTasks_stopped]; exact Extends.refl _
    | true =>
      simp only [List.foldl_cons, fireStep, if_true]
      cases hs : settled (driveState interp fuel (m.emit [RunEvent.ranTask owner task]) (taskCmds task))
      · rw [fireTasks_stopped]
        have hd : Extends
            (driveState interp fuel (m.emit [RunEvent.ranTask owner task]) (taskCmds task)).1
            (driveState interp (fuel + k) (m.emit [RunEvent.ranTask owner task]) (taskCmds task)).1 := by
          rw [← drive_eq_driveState, ← drive_eq_driveState]
          exact drive_trace_mono interp (Nat.le_add_right fuel k) _ _
        exact Extends.trans hd (fireTasks_extends (interp := interp) (fuel := fuel + k)
          (owner := owner) (tasks := tasks)
          (acc := ((driveState interp (fuel + k) (m.emit [RunEvent.ranTask owner task]) (taskCmds task)).1,
            settled (driveState interp (fuel + k) (m.emit [RunEvent.ranTask owner task]) (taskCmds task)))))
      · rw [driveState_settled_add interp fuel _ _ hs k]
        simpa only [hs] using ih
          (driveState interp fuel (m.emit [RunEvent.ranTask owner task]) (taskCmds task)).1 true

theorem fire_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) (fuel k : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (owner : FiberId) :
    Extends (stepDecision.fire interp fuel m owner) (stepDecision.fire interp (fuel + k) m owner) := by
  simp only [stepDecision.fire, fireState]
  cases hf : m.fiber? owner with
  | none => exact Extends.refl _
  | some o => exact fireTasks_trace_mono interp fuel k owner _ _ true

/-- More task fuel and more rounds extend a flush's trace, even if the smaller
flush stopped at a fuel frontier. -/
theorem flushAll_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (k j : Nat) :
    Extends (stepDecision.flushAll interp fuel rounds m)
      (stepDecision.flushAll interp (fuel + k) (rounds + j) m) := by
  change Extends (flushAllState interp fuel rounds m).1
    (flushAllState interp (fuel + k) (rounds + j) m).1
  induction rounds generalizing m j with
  | zero =>
    simp only [Nat.zero_add, flushAllState]
    exact flushAll_extends
  | succ rounds ih =>
    rw [Nat.succ_add]
    cases ha : m.armed with
    | nil => simp only [flushAllState, ha]; exact Extends.refl _
    | cons owner rest =>
      cases hs : m.stuck.isSome
      · simp only [flushAllState, ha, hs, Bool.false_eq_true, if_false]
        have hfire : Extends (fireState interp fuel m owner).1 (fireState interp (fuel + k) m owner).1 := by
          simpa only [stepDecision.fire] using fire_trace_mono interp fuel k m owner
        cases hr : (fireState interp fuel m owner).2
        · simp only [Bool.false_eq_true, if_false]
          cases hr' : (fireState interp (fuel + k) m owner).2
          · simpa only [Bool.false_eq_true, if_false] using hfire
          · simp only [if_true]
            exact Extends.trans hfire flushAll_extends
        · rw [fireState_stable interp fuel m owner hr k]
          simp only [hr, if_true]
          exact ih _ j
      · simp only [flushAllState, ha, hs, if_true]; exact Extends.refl _

/-! ## Sufficiency along a tape, and stability -/

/-- Fuel `fuel` suffices for `tape` from `m`: every decision's receipt says so, on the
machine the previous decisions left; a stuck machine ends the replay and needs nothing.
Decidable by construction — it is the replay itself, with the receipts. -/
def Suffices (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat) :
    List (RunDecision ν σ β ε δ ι α) → RunMachine ν σ β ε δ ι α χ St κ φ η → Bool
  | [], _ => true
  | decision :: tape, m =>
    match m.stuck with
    | some _ => true
    | none =>
      let r := stepDecisionState interp fuel m decision
      r.2 && Suffices interp fuel tape r.1

/-- A terminal replay did not cross an unfinished unit of work. The converse
fails for tapes that leave live fibers waiting for another decision. -/
theorem Suffices_of_replay_terminal (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (h : (replayEval interp fuel tape m).terminal = true) :
    Suffices interp fuel tape m = true := by
  induction tape generalizing m with
  | nil => rfl
  | cons decision tape ih =>
    cases hs : m.stuck with
    | some why => simp only [Suffices, hs]
    | none =>
      simp only [replayEval, hs] at h
      cases hr : (stepDecisionState interp fuel m decision).2
      · simp only [hr, Bool.false_eq_true, if_false, ReplayResult.terminal] at h
      · simp only [hr, if_true] at h
        simp only [Suffices, hs, hr, ih _ h, Bool.true_and]

/-- Compatibility: under `Suffices`, every larger fuel replays to the same result. -/
theorem replay_stable (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
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
      dsimp only
      rw [stepDecisionState_stable interp fuel m decision hr k]
      simp only [hr, if_true]
      exact ih _ hrest

/-- A sufficient fuel stays sufficient. -/
theorem Suffices_mono (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
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

theorem Suffices_of_le (interp : RunInterp ν σ β ε δ ι α χ St κ) {n n' : Nat} (h : n ≤ n')
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (hs : Suffices interp n tape m = true) : Suffices interp n' tape m = true := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  exact Suffices_mono interp n tape m hs k

/-- Monotonicity where it is stability: under `Suffices`, more fuel is the same result. -/
theorem replay_obs_mono_of_suffices (interp : RunInterp ν σ β ε δ ι α χ St κ) {n n' : Nat}
    (h : n ≤ n') (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (hs : Suffices interp n tape m = true) :
    ReplayResult.le (replayEval interp n tape m) (replayEval interp n' tape m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [replay_stable interp n tape m hs k]
  exact ReplayResult.le_refl _

/-! ## Monotonicity on one loop, per decision kind

The decisions that run one loop or none. The task and round laws above handle
`fire` and `flush`; the old `APPROX-FB-REFRESH` refusal is retired. -/

/-- The decision runs at most one `drive`. -/
def SingleLoop : RunDecision ν σ β ε δ ι α → Bool
  | RunDecision.fire _ => false
  | RunDecision.flush => false
  | RunDecision.advance _ => false
  | _ => true

/-- More fuel and a larger fire budget extend an advance's trace (the timer, A4): a fire whose
drive or flush stopped at the smaller fuel is extended by the larger one, and a fire that
completed is the same fire. -/
theorem advance_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) (fuel millis : Nat) :
    ∀ (rounds : Nat) (m : RunMachine ν σ β ε δ ι α χ St) (k j : Nat),
      Extends (advanceState interp fuel millis rounds m).1
        (advanceState interp (fuel + k) millis (rounds + j) m).1
  | 0, m, k, j => by simp only [Nat.zero_add, advanceState]; exact advance_extends
  | rounds + 1, m, k, j => by
    rw [Nat.succ_add]
    unfold advanceState
    cases hs : m.stuck.isSome
    · simp only [hs, Bool.false_eq_true, if_false]
      rcases hc : interp.clockStep millis m.state with ⟨o, st⟩
      cases o with
      | none => exact Extends.refl _
      | some owed =>
        dsimp only
        generalize hR : drainOwed { m with state := st } [owed] = R
        have hd := drive_trace_mono interp (Nat.le_add_right fuel k) R.1 (R.2 ++ [Cmd.drainDue])
        rw [drive_eq_driveState interp fuel, drive_eq_driveState interp (fuel + k)] at hd
        cases hsd : settled (driveState interp fuel R.1 (R.2 ++ [Cmd.drainDue]))
        · simp only [hsd, Bool.false_eq_true, if_false]
          refine Extends.trans hd ?_
          split
          · split
            · exact Extends.trans flushAll_extends advance_extends
            · exact flushAll_extends
          · exact Extends.refl _
        · rw [driveState_settled_add interp fuel _ _ hsd k]
          simp only [hsd, if_true]
          cases hf : (flushAllState interp fuel fuel (driveState interp fuel R.1 (R.2 ++ [Cmd.drainDue])).1).2
          · simp only [hf, Bool.false_eq_true, if_false]
            have hfl : Extends (flushAllState interp fuel fuel
                  (driveState interp fuel R.1 (R.2 ++ [Cmd.drainDue])).1).1
                (flushAllState interp (fuel + k) (fuel + k)
                  (driveState interp fuel R.1 (R.2 ++ [Cmd.drainDue])).1).1 :=
              flushAll_trace_mono interp fuel fuel _ k k
            refine Extends.trans hfl ?_
            split
            · exact advance_extends
            · exact Extends.refl _
          · rw [flushAllState_stable interp fuel fuel _ hf k k]
            simp only [hf, if_true]
            exact advance_trace_mono interp fuel millis rounds _ k j
    · simp only [hs, if_true]; exact Extends.refl _

/-- More fuel on a single-loop decision extends the trace. -/
theorem stepDecision_trace_mono (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat} (h : n ≤ n')
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) :
    Extends (stepDecision interp n m decision) (stepDecision interp n' m decision) := by
  cases decision with
  | fire owner => cases hd
  | flush => cases hd
  | advance millis => cases hd
  | evaluate id => exact drive_trace_mono interp h m _
  | answerAsync id token answer =>
    cases n with
    | zero =>
      cases n' with
      | zero => exact Extends.refl _
      | succ n' =>
        have he := drive_extends (interp := interp) (fuel := n' + 1)
          (m := { m with state := (prepareAsyncAnswer interp m id token answer).1 })
          (cmds := [Cmd.resume id token (prepareAsyncAnswer interp m id token answer).2, Cmd.drainDue])
        simpa only [stepDecision, stepDecisionState, stepDecisionState.loop, Extends,
          drive_eq_driveState] using he
    | succ n =>
      cases n' with
      | zero => exact False.elim (Nat.not_succ_le_zero n h)
      | succ n' => exact drive_trace_mono interp h _ _
  | yieldVerdict id verdict => exact Extends.refl _
  | installMiddleware => exact Extends.refl _
  | interruptFrom interruptor annotations target =>
    simp only [stepDecision, stepDecisionState, stepDecisionState.loop]
    split
    · exact Extends.refl _
    · split
      · exact drive_trace_mono interp h _ _
      · exact Extends.refl _

/-- Every decision now extends its trace with more fuel: task and round
boundaries stop instead of continuing after exhaustion. -/
theorem stepDecision_trace_mono_all (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (m : RunMachine ν σ β ε δ ι α χ St)
    (decision : RunDecision ν σ β ε δ ι α) :
    Extends (stepDecision interp n m decision) (stepDecision interp n' m decision) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  cases decision with
  | fire owner => exact fire_trace_mono interp n k m owner
  | flush => exact flushAll_trace_mono interp n n m k k
  | advance millis => exact advance_trace_mono interp n millis n m k k
  | evaluate id | yieldVerdict id verdict | answerAsync id token answer
  | interruptFrom interruptor annotations target | installMiddleware =>
    exact stepDecision_trace_mono interp (Nat.le_add_right n k) m _ rfl

/-- More fuel refines replay on every tape. A frontier is compared by trace
prefix; finished and stuck results are unchanged. The initial machine is fixed. -/
theorem replay_obs_mono (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) :
    ReplayResult.le (replayEval interp n tape m) (replayEval interp n' tape m) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  induction tape generalizing m with
  | nil => exact ReplayResult.le_refl _
  | cons decision tape ih =>
    cases hs : m.stuck with
    | some why => simp only [replayEval, hs]; exact ReplayResult.le_refl _
    | none =>
      simp only [replayEval, hs]
      cases hr : (stepDecisionState interp n m decision).2
      · simp only [Bool.false_eq_true, if_false]
        have hd : Extends (stepDecisionState interp n m decision).1
            (stepDecisionState interp (n + k) m decision).1 := by
          rw [← stepDecision_eq_state, ← stepDecision_eq_state]
          exact stepDecision_trace_mono_all interp (Nat.le_add_right n k) m decision
        cases hr' : (stepDecisionState interp (n + k) m decision).2
        · simp only [Bool.false_eq_true, if_false]
          exact hd
        · simp only [if_true]
          exact Extends.trans hd replayEval_extends
      · rw [stepDecisionState_stable interp n m decision hr k]
        simp only [hr, if_true]
        exact ih _

/-- A single-loop decision that halted is the same decision at every larger fuel. -/
theorem stepDecision_stuck_stable (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) (hs : (stepDecision interp fuel m decision).stuck.isSome = true) :
    ∀ k, stepDecision interp (fuel + k) m decision = stepDecision interp fuel m decision := by
  intro k
  cases decision with
  | fire owner => cases hd
  | flush => cases hd
  | advance millis => cases hd
  | evaluate id =>
    simp only [stepDecision, stepDecisionState, stepDecisionState.loop] at hs ⊢
    exact drive_stable_of_stuck interp fuel m _ hs k
  | answerAsync id token answer =>
    cases fuel with
    | zero =>
      change m.stuck.isSome = true at hs
      cases k with
      | zero => rfl
      | succ k =>
        simp only [Nat.zero_add, stepDecision, stepDecisionState, stepDecisionState.loop,
          prepareAsyncAnswer, hs, if_true]
        simpa only [drive_eq_driveState] using
          drive_stuck interp (Nat.add 0 k + 1) m
            [Cmd.resume id token (interp.answerCode answer), Cmd.drainDue] hs
    | succ fuel =>
      simp only [Nat.succ_add, stepDecision, stepDecisionState, stepDecisionState.loop] at hs ⊢
      have hd := drive_stable_of_stuck interp (fuel + 1)
        { m with state := (prepareAsyncAnswer interp m id token answer).1 } _ hs k
      simpa only [Nat.succ_add, drive_eq_driveState] using hd
  | yieldVerdict id verdict => rfl
  | installMiddleware => rfl
  | interruptFrom interruptor annotations target =>
    simp only [stepDecision, stepDecisionState, stepDecisionState.loop] at hs ⊢
    split at hs
    · rfl
    · rename_i f _
      cases ha : (interruptRecord interp interruptor annotations f).2
      · simp only [Bool.false_eq_true, if_false]
      · rw [ha] at hs
        simp only [if_true] at hs ⊢
        exact drive_stable_of_stuck interp fuel _ _ hs k

/-- The frontier half of monotonicity on a one-decision tape: a frontier at fuel `n` is
below the result at any larger fuel. -/
theorem replay_frontier_mono_single (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (hd : SingleLoop decision = true) {m₁ : RunMachine ν σ β ε δ ι α χ St}
    (hf : replayEval interp n [decision] m = ReplayResult.frontier m₁) :
    ReplayResult.le (ReplayResult.frontier m₁) (replayEval interp n' [decision] m) := by
  refine ReplayResult.frontier_le ?_
  cases hs : m.stuck with
  | some why =>
    simp only [replayEval, hs] at hf
    cases hf
  | none =>
    have hm := congrArg ReplayResult.machine hf
    rw [replayEval_single_machine interp n m decision hs] at hm
    change stepDecision interp n m decision = m₁ at hm
    rw [← hm, replayEval_single_machine interp n' m decision hs]
    exact stepDecision_trace_mono interp h m decision hd

/-- The stuck half: a halt at fuel `n` is the result at every larger fuel. -/
theorem replay_stuck_mono_single (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}
    (h : n ≤ n') (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α)
    (_hd : SingleLoop decision = true) {why : Stuck} {m₁ : RunMachine ν σ β ε δ ι α χ St}
    (hst : replayEval interp n [decision] m = ReplayResult.stuck why m₁) :
    ReplayResult.le (ReplayResult.stuck why m₁) (replayEval interp n' [decision] m) := by
  show replayEval interp n' [decision] m = ReplayResult.stuck why m₁
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  have ht : (replayEval interp n [decision] m).terminal = true := by rw [hst]; rfl
  rw [replay_stable interp n [decision] m (Suffices_of_replay_terminal interp n [decision] m ht) k]
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
