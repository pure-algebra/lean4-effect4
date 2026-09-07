import Effect4.Machine.Approximation
import Effect4.Api
import Test.Program.CompileContract

/-!
# Approximation contract — the fuel laws over the live fiber machine, frozen

Review: `docs/research/2026-09-05-effects-papers-review.md` §3 G2. Packet:
`Test/contracts/machine-approximation.contract.md`. The module under contract is
`src/Effect4/Machine/Approximation.lean`; the machine it speaks about is
`src/Effect4/Machine/Fibers.lean`.

The obligations below are ascribed at their exact propositions, under the section variables
the module takes, so a declaration that keeps the frozen name but weakens the statement fails
here (`Test/Machine/Runtime/StoresLawsContract.lean` is the model). The executable receipts
are `#guard`s over first-order values on small programs of `Test/Program/CompileContract.lean`
run through `Api.load` at the compile fuel `400` and the machine fuel the guard names: the
three corner cases of the splitting law, the law itself at several splits, stability once the
commands are exhausted, the trace prefix on one loop, the receipts of `fire`, the least
sufficient fuel, and the register rows as pairs of guards. Machine equality is not decidable
at the `Api` types (`Race` carries no `DecidableEq`), so two machines are compared on their
traces, stores, root exit and fiber count.

Register rows (`Test/Counterexamples/REGISTER.md`):

* `E4-APPROX-CE-001` — the loop is stable in fuel without a side condition. Refuted: `pBindSync`
  at fuel `1` and `2` differ (one more event) while fuel `1` leaves two commands unrun;
  `drive_stable_of_done` carries the residual `(driveState …).2 = []`.
* `E4-APPROX-CE-002` — repaired by stopping replay when commands remain. A recorded fiber
  exit with unfinished drains now produces a frontier. Terminal replay implies sufficiency
  (`Suffices_of_replay_terminal`); sufficiency alone can still leave waiting fibers.
* `E4-APPROX-CE-003` — repaired by stopping before the next tape decision when a loop
  exhausts its fuel. The interrupt waits, so the traces at fuel `1` and `2` are prefixes.
  `replay_obs_mono` proves the order for every tape and every pair of ordered budgets.
* `E4-APPROX-CE-004` — repaired by stopping the dispatcher snapshot at its first unfinished
  task. The second child remains unstarted; `fire_trace_mono` covers all budgets.
-/

set_option autoImplicit false
set_option maxRecDepth 10000

namespace Test.Runtime.ApproximationContract

open Effect4
open Effect4.Machine
open Effect4.Program
open Test.Syntax.CompileContract (fuel pSucceed pBindSync pYieldNow deferredChild)

universe u v

/-! ## The frozen statements -/

section Statements

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

#check (Effect4.Machine.drive_eq_driveState :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (cmds : List (Cmd ν σ β ε δ ι α)),
    drive interp fuel m cmds = (driveState interp fuel m cmds).1)

#check (Effect4.Machine.driveState_add :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (a b : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (cmds : List (Cmd ν σ β ε δ ι α)),
    driveState interp (a + b) m cmds =
      driveState interp b (driveState interp a m cmds).1 (driveState interp a m cmds).2)

#check (Effect4.Machine.drive_add :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (a b : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (cmds : List (Cmd ν σ β ε δ ι α)),
    drive interp (a + b) m cmds =
      drive interp b (driveState interp a m cmds).1 (driveState interp a m cmds).2)

#check (Effect4.Machine.drive_stable_of_done :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (cmds : List (Cmd ν σ β ε δ ι α)), (driveState interp fuel m cmds).2 = [] →
    ∀ k, drive interp (fuel + k) m cmds = drive interp fuel m cmds)

#check (Effect4.Machine.drive_trace_extends :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (cmds : List (Cmd ν σ β ε δ ι α)),
    ∃ ev, (drive interp fuel m cmds).trace = m.trace ++ ev)

#check (Effect4.Machine.stepDecision_trace_extends :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : RunMachine ν σ β ε δ ι α χ St)
    (decision : RunDecision ν σ β ε δ ι α),
    ∃ ev, (stepDecision interp fuel m decision).trace = m.trace ++ ev)

#check (Effect4.Machine.replayEval_trace_extends :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St),
    ∃ ev, (replayEval interp fuel tape m).machine.trace = m.trace ++ ev)

#check (Effect4.Machine.drive_trace_mono :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}, n ≤ n' →
    ∀ (m : RunMachine ν σ β ε δ ι α χ St) (cmds : List (Cmd ν σ β ε δ ι α)),
    RunMachine.Extends (drive interp n m cmds) (drive interp n' m cmds))

#check (Effect4.Machine.ReplayResult.le_refl :
  ∀ (a : ReplayResult ν σ β ε δ ι α χ St), ReplayResult.le a a)
#check (Effect4.Machine.ReplayResult.le_trans :
  ∀ {a b c : ReplayResult ν σ β ε δ ι α χ St}, ReplayResult.le a b → ReplayResult.le b c →
    ReplayResult.le a c)
#check (Effect4.Machine.ReplayResult.le_antisymm_terminal :
  ∀ {a b : ReplayResult ν σ β ε δ ι α χ St}, a.terminal = true → ReplayResult.le a b →
    ReplayResult.le b a → a = b)

#check (Effect4.Machine.replay_stable :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St), Suffices interp fuel tape m = true →
    ∀ k, replayEval interp (fuel + k) tape m = replayEval interp fuel tape m)

#check (Effect4.Machine.Suffices_mono :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St), Suffices interp fuel tape m = true →
    ∀ k, Suffices interp (fuel + k) tape m = true)

#check (Effect4.Machine.replay_obs_mono_of_suffices :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}, n ≤ n' →
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St),
    Suffices interp n tape m = true →
    ReplayResult.le (replayEval interp n tape m) (replayEval interp n' tape m))

#check (Effect4.Machine.replay_obs_mono :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}, n ≤ n' →
    ∀ (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St),
    ReplayResult.le (replayEval interp n tape m) (replayEval interp n' tape m))

#check (Effect4.Machine.Suffices_of_replay_terminal :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (tape : List (RunDecision ν σ β ε δ ι α)) (m : RunMachine ν σ β ε δ ι α χ St),
    (replayEval interp fuel tape m).terminal = true → Suffices interp fuel tape m = true)

#check (Effect4.Machine.replay_frontier_mono_single :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}, n ≤ n' →
    ∀ (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α),
    SingleLoop decision = true → ∀ {m₁ : RunMachine ν σ β ε δ ι α χ St},
    replayEval interp n [decision] m = ReplayResult.frontier m₁ →
    ReplayResult.le (ReplayResult.frontier m₁) (replayEval interp n' [decision] m))

#check (Effect4.Machine.replay_stuck_mono_single :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) {n n' : Nat}, n ≤ n' →
    ∀ (m : RunMachine ν σ β ε δ ι α χ St) (decision : RunDecision ν σ β ε δ ι α),
    SingleLoop decision = true → ∀ {why : Stuck} {m₁ : RunMachine ν σ β ε δ ι α χ St},
    replayEval interp n [decision] m = ReplayResult.stuck why m₁ →
    ReplayResult.le (ReplayResult.stuck why m₁) (replayEval interp n' [decision] m))

#check (Effect4.Machine.replay_colimit :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat},
    leastSufficient interp tape m bound = some f →
    ∀ k, replayEval interp (f + k) tape m = replayEval interp f tape m)

#check (Effect4.Machine.leastSufficient_least :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat},
    leastSufficient interp tape m bound = some f → ∀ g, g < f → Suffices interp g tape m = false)

#check (Effect4.Machine.leastSufficient_bound_mono :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) {bound f : Nat},
    leastSufficient interp tape m bound = some f → ∀ {bound' : Nat}, bound ≤ bound' →
    leastSufficient interp tape m bound' = some f)

#check (Effect4.Machine.replay_colimit_eq_of_sufficient :
  ∀ (interp : RunInterp ν σ β ε δ ι α χ St) (tape : List (RunDecision ν σ β ε δ ι α))
    (m : RunMachine ν σ β ε δ ι α χ St) {n bound : Nat},
    Suffices interp n tape m = true → n ≤ bound →
    ∃ f, leastSufficient interp tape m bound = some f ∧ f ≤ n ∧
      replayEval interp n tape m = replayEval interp f tape m)

end Statements

/-! ## Harness: programs at the compile fuel, machines at the fuel a guard names -/

abbrev CmdA := Cmd EffName EffThunk Val Err Defect FiberId Ann

/-- The loaded machine of a program, at the compile fuel of the compile contract. -/
def machineOf (p : NativeEff) : Api.Machine := Api.load p fuel

/-- A replay at machine fuel `f`, the compile fuel held at `fuel`. -/
def runAt (p : NativeEff) (f : Nat) (tape : List Api.Decision) : Api.Run :=
  match replayEval (interpOf p) f tape (machineOf p) with
  | ReplayResult.finished m => ⟨Api.Outcome.finished, m⟩
  | ReplayResult.frontier m => ⟨Api.Outcome.frontier, m⟩
  | ReplayResult.stuck why m => ⟨Api.Outcome.stuck why, m⟩

/-- `0` finished, `1` frontier, `2` stuck. -/
def tag : Api.Outcome → Nat
  | .finished => 0
  | .frontier => 1
  | .stuck _ => 2

/-- The commands `RunDecision.evaluate root` runs. -/
def evaluateCmds : List CmdA := [Cmd.evaluate Api.root, Cmd.drainDue]

/-- The loop with its residue on the evaluate commands: the machine and how many commands
were left. -/
def loopAt (p : NativeEff) (f : Nat) : Api.Machine × Nat :=
  let r := driveState (interpOf p) f (machineOf p) evaluateCmds
  (r.1, r.2.length)

def sufficesAt (p : NativeEff) (f : Nat) (tape : List Api.Decision) : Bool :=
  Suffices (interpOf p) f tape (machineOf p)

def leastAt (p : NativeEff) (tape : List Api.Decision) (bound : Nat) : Option Nat :=
  leastSufficient (interpOf p) tape (machineOf p) bound

/-- Two machines agree on what a guard can decide: the trace, the stores, the root's exit and
the fiber count. -/
def sameMachine (a b : Api.Machine) : Bool :=
  a.trace == b.trace && a.state == b.state &&
    (a.fiber? Api.root).bind RunFiber.exit == (b.fiber? Api.root).bind RunFiber.exit &&
    a.fibers.length == b.fibers.length

/-- The tape's abort signal on the root (`runFork`'s, `Fibers.lean`). -/
def interruptRoot : Api.Decision := RunDecision.interruptFrom none ReasonAnnotations.empty Api.root

/-- Two deferred-start children on the root's dispatcher, the root awaiting the first: after
`evaluate` the dispatcher holds two `start` tasks. -/
def pTwoDeferred : NativeEff :=
  .bind (.withFiber (.fork (.succeed (.lit (.nat 1))) deferredChild))
    (.bind (.withFiber (.fork (.succeed (.lit (.nat 2))) deferredChild))
      (.awaitFiber (.var 0) Supervision.ObserverMode.joinEffect))

#guard (typeOf nativeSignature pTwoDeferred).isSome

/-! ## The splitting law and its corner cases -/

section Splitting

/-- `driveState (a + b)` against `driveState b` on what `driveState a` left. -/
def splitAgrees (p : NativeEff) (a b : Nat) : Bool :=
  let m := machineOf p
  let whole := driveState (interpOf p) (a + b) m evaluateCmds
  let first := driveState (interpOf p) a m evaluateCmds
  let rest := driveState (interpOf p) b first.1 first.2
  sameMachine whole.1 rest.1 && whole.2.length == rest.2.length

-- fuel `0` runs nothing and leaves every command
#guard (loopAt pBindSync 0).2 = 2
#guard sameMachine (loopAt pBindSync 0).1 (machineOf pBindSync)
-- no command leaves nothing, whatever the fuel
#guard (driveState (interpOf pSucceed) 5 (machineOf pSucceed) []).2.length = 0
#guard sameMachine (driveState (interpOf pSucceed) 5 (machineOf pSucceed) []).1 (machineOf pSucceed)
-- a stuck machine keeps its commands and records nothing
#guard (driveState (interpOf pSucceed) 5
  { machineOf pSucceed with stuck := some (Stuck.unknownFiber ⟨7⟩) } evaluateCmds).2.length = 2
#guard (driveState (interpOf pSucceed) 5
  { machineOf pSucceed with stuck := some (Stuck.unknownFiber ⟨7⟩) } evaluateCmds).1.trace.length = 0
-- the law at several splits, both corner cases included
#guard splitAgrees pBindSync 0 3
#guard splitAgrees pBindSync 3 0
#guard splitAgrees pBindSync 2 2
#guard splitAgrees pBindSync 1 5
#guard splitAgrees pBindSync 4 9
#guard splitAgrees pSucceed 2 1
#guard splitAgrees pSucceed 3 4

-- `drive` is the machine half
#guard sameMachine (drive (interpOf pBindSync) 3 (machineOf pBindSync) evaluateCmds) (loopAt pBindSync 3).1

end Splitting

/-! ## Stability once the commands are exhausted (`drive_stable_of_done`) -/

section Stability

-- `pSucceed`: two commands left at fuel `3`, one at `4`, none from `5`
#guard (loopAt pSucceed 3).2 = 2
#guard (loopAt pSucceed 4).2 = 1
#guard (loopAt pSucceed 5).2 = 0
#guard (loopAt pSucceed 6).2 = 0
#guard sameMachine (loopAt pSucceed 5).1 (loopAt pSucceed 9).1
#guard sameMachine (loopAt pSucceed 5).1 (loopAt pSucceed 400).1
-- `pBindSync`: none from `8`
#guard (loopAt pBindSync 7).2 = 1
#guard (loopAt pBindSync 8).2 = 0
#guard sameMachine (loopAt pBindSync 8).1 (loopAt pBindSync 30).1

end Stability

/-! ## The trace only grows, and is monotone on one loop -/

section Trace

-- a chain of frontiers, each trace a prefix of the next (`drive_trace_mono`)
#guard (List.range 8).all fun f =>
  (runAt pBindSync f [Api.evaluate]).trace.isPrefixOf (runAt pBindSync (f + 1) [Api.evaluate]).trace
#guard (List.range 8).all fun f => tag (runAt pBindSync f [Api.evaluate]).outcome == 1
#guard tag (runAt pBindSync 8 [Api.evaluate]).outcome == 0
-- the frontier at fuel `2` is below the finished result at `8`: the order's frontier arm
#guard (runAt pBindSync 2 [Api.evaluate]).trace.isPrefixOf (runAt pBindSync 8 [Api.evaluate]).trace
-- every decision extends the trace it starts from (`stepDecision_trace_extends`)
#guard let m := (runAt pBindSync 2 [Api.evaluate]).machine
  m.trace.isPrefixOf (stepDecision (interpOf pBindSync) 3 m interruptRoot).trace
#guard let m := (runAt pBindSync 2 [Api.evaluate]).machine
  m.trace.isPrefixOf (stepDecision (interpOf pBindSync) 0 m interruptRoot).trace
-- a decision that runs no loop is fuel-independent
#guard let m := machineOf pBindSync
  sameMachine (stepDecision (interpOf pBindSync) 0 m (RunDecision.yieldVerdict Api.root true))
    (stepDecision (interpOf pBindSync) 9 m (RunDecision.yieldVerdict Api.root true))

end Trace

/-! ## The least sufficient fuel (`replay_colimit`) -/

section Colimit

#guard leastAt pSucceed [Api.evaluate] 10 = some 5
#guard leastAt pSucceed [Api.evaluate] 4 = none
#guard leastAt pSucceed [Api.evaluate] 100 = some 5
#guard leastAt pBindSync [Api.evaluate] 20 = some 8
#guard leastAt pBindSync [Api.evaluate, interruptRoot] 20 = some 8
#guard leastAt pYieldNow [Api.evaluate, Api.flush] 50 = some 7
-- D6b: each tracked child's exit path is now `observe`, `exitDone` and the drain, and the
-- tracking itself is a command, so the two-child join settles at 30 commands (20 before).
#guard leastAt pTwoDeferred [Api.evaluate, Api.flush] 80 = some 30
-- sufficiency is upward closed, and false below the least
#guard sufficesAt pSucceed 4 [Api.evaluate] = false
#guard sufficesAt pSucceed 5 [Api.evaluate] = true
#guard sufficesAt pSucceed 6 [Api.evaluate] = true
#guard sufficesAt pSucceed 400 [Api.evaluate] = true
-- the join: the replay at the least sufficient fuel is the replay above it
#guard sameMachine (runAt pYieldNow 7 [Api.evaluate, Api.flush]).machine
  (runAt pYieldNow 40 [Api.evaluate, Api.flush]).machine
#guard (runAt pYieldNow 7 [Api.evaluate, Api.flush]).exit == some (Exit.success (Val.nat 5))
#guard sameMachine (runAt pTwoDeferred 30 [Api.evaluate, Api.flush]).machine
  (runAt pTwoDeferred 400 [Api.evaluate, Api.flush]).machine
#guard (runAt pTwoDeferred 30 [Api.evaluate, Api.flush]).exit == some (Exit.success (Val.nat 1))

end Colimit

/-! ## The register rows -/

section Rows

-- E4-APPROX-CE-001: the loop is not stable in fuel by itself; the residual is the side
-- condition
#guard (runAt pBindSync 1 [Api.evaluate]).trace.length = 1
#guard (runAt pBindSync 2 [Api.evaluate]).trace.length = 2
#guard !sameMachine (loopAt pBindSync 1).1 (loopAt pBindSync 2).1
#guard (loopAt pBindSync 1).2 = 2
#guard (loopAt pBindSync 8).2 = 0
#guard sameMachine (loopAt pBindSync 8).1 (loopAt pBindSync 9).1

-- E4-APPROX-CE-002, repaired: recorded exits with unfinished drains are frontiers
#guard tag (runAt pSucceed 3 [Api.evaluate]).outcome == 1
#guard (loopAt pSucceed 3).2 = 2
#guard sufficesAt pSucceed 3 [Api.evaluate] = false
#guard sufficesAt pSucceed 5 [Api.evaluate] = true
#guard tag (runAt pYieldNow 5 [Api.evaluate, Api.flush]).outcome == 1
#guard sufficesAt pYieldNow 5 [Api.evaluate, Api.flush] = false
#guard sufficesAt pYieldNow 7 [Api.evaluate, Api.flush] = true
#guard tag (runAt pTwoDeferred 16 [Api.evaluate, Api.flush]).outcome == 1
#guard sufficesAt pTwoDeferred 16 [Api.evaluate, Api.flush] = false

-- E4-APPROX-CE-003, repaired: the interrupt waits behind unfinished evaluation
#guard (runAt pBindSync 1 [Api.evaluate, interruptRoot]).trace.length = 1
#guard (runAt pBindSync 2 [Api.evaluate, interruptRoot]).trace.length = 2
#guard (runAt pBindSync 1 [Api.evaluate, interruptRoot]).trace.isPrefixOf
  (runAt pBindSync 2 [Api.evaluate, interruptRoot]).trace
#guard !((runAt pBindSync 2 [Api.evaluate, interruptRoot]).trace.isPrefixOf
  (runAt pBindSync 1 [Api.evaluate, interruptRoot]).trace)
-- the same tape under `Suffices` is stable
#guard sufficesAt pBindSync 8 [Api.evaluate, interruptRoot] = true
#guard sameMachine (runAt pBindSync 8 [Api.evaluate, interruptRoot]).machine
  (runAt pBindSync 9 [Api.evaluate, interruptRoot]).machine

-- E4-APPROX-CE-004, repaired: the later task waits behind the unfinished child
/-- The machine after the root's `evaluate`: the root parked on its await, two `start`
tasks on its dispatcher, the dispatcher armed. -/
def twoTasks : Api.Machine := (runAt pTwoDeferred 400 [Api.evaluate]).machine
def fireAt (f : Nat) : Api.Machine :=
  stepDecision (interpOf pTwoDeferred) f twoTasks (RunDecision.fire Api.root)

#guard (twoTasks.fiber? Api.root).map (fun o => (o.dispatcher.drain).1.length) = some 2
#guard twoTasks.armed.length = 1
#guard tag (runAt pTwoDeferred 400 [Api.evaluate]).outcome == 1
#guard (fireAt 1).trace.length = 12
#guard (fireAt 2).trace.length = 13
#guard (fireAt 1).trace.isPrefixOf (fireAt 2).trace
#guard !((fireAt 2).trace.isPrefixOf (fireAt 1).trace)
-- both still extend the machine they fired from (`fire_trace_extends`)
#guard twoTasks.trace.isPrefixOf (fireAt 1).trace
#guard twoTasks.trace.isPrefixOf (fireAt 2).trace
-- the receipt refuses both, accepts the full fuel, and the fire is then stable
#guard (fireState (interpOf pTwoDeferred) 1 twoTasks Api.root).2 = false
#guard (fireState (interpOf pTwoDeferred) 2 twoTasks Api.root).2 = false
#guard (fireState (interpOf pTwoDeferred) 400 twoTasks Api.root).2 = true
#guard (fireAt 400).trace == (fireAt 401).trace
#guard sameMachine (fireAt 400) (fireAt 401)

-- Monotonicity across the task boundary and the replay boundary, including exhaustion.
#guard (List.range 25).all fun f => (fireAt f).trace.isPrefixOf (fireAt (f + 1)).trace
#guard (List.range 25).all fun f =>
  (runAt pTwoDeferred f [Api.evaluate, Api.flush, interruptRoot]).trace.isPrefixOf
    (runAt pTwoDeferred (f + 1) [Api.evaluate, Api.flush, interruptRoot]).trace

end Rows

end Test.Runtime.ApproximationContract
