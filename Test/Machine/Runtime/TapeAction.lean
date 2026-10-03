import Effect4.Laws.Machine.Approximation
import Test.Machine.Runtime.ApproximationContract

/-!
# The tape acts on machines: controls

Controls for `replayEval_append` and its corollaries (`src/Effect4/Laws/Machine/Approximation.lean`;
formal pass, algebra note A7, probe `P3TapeAction.lean`). The red control is the naive action
law, which would replay the suffix from the machine a fuel frontier reached: it fails at every
fuel frontier whose machine is neither stuck nor finished (`naive_append_fails`, proved for
every evaluator), and such a frontier exists (`pBindSync` at machine fuel 2, tested). The law's
two arms are exercised on the same program (tested).
-/

set_option autoImplicit false
set_option maxRecDepth 10000
namespace Test.Runtime.TapeAction
open Effect4 Effect4.Machine Effect4.Program
open Test.Runtime.ApproximationContract (machineOf sameMachine interruptRoot)
open Test.Syntax.CompileContract (pBindSync)

universe u v

section Generic

variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {κ φ η : Type (max u v)} [core : FiberCore ν β ε δ ι α κ φ]
variable [evaluator : FiberEvaluator ν σ β ε δ ι α χ St κ φ η]

/-- **Red control: the naive action law fails at a fuel frontier.** If a prefix ends at a fuel
frontier whose machine is neither stuck nor finished, replaying the prefix with an empty suffix
is that fuel frontier, while replaying the empty suffix from the frontier's machine is a tape
frontier. Fuel exhaustion is absorbing; it is not the end of the tape. -/
theorem naive_append_fails (interp : RunInterp ν σ β ε δ ι α χ St κ) (fuel : Nat)
    (a : List (RunDecision ν σ β ε δ ι α)) (m m' : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (h : replayEval interp fuel a m = .frontier .fuel m')
    (hs : m'.stuck = none) (hf : m'.finished = false) :
    replayEval interp fuel (a ++ []) m ≠
      replayEval interp fuel [] (replayEval interp fuel a m).machine := by
  rw [replayEval_append_fuel interp fuel a [] m m' h, h]
  simp only [ReplayResult.machine, replayEval, hs, hf, Bool.false_eq_true, ↓reduceIte]
  intro heq
  injection heq with hwhy
  cases hwhy

end Generic

/-- `0` finished, `1` fuel frontier, `2` tape frontier, `3` stuck. -/
def kind : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores → Nat
  | .finished _ => 0
  | .frontier .fuel _ => 1
  | .frontier .tape _ => 2
  | .stuck _ _ => 3

/-- `pBindSync` evaluated at machine fuel 2: a fuel frontier. -/
def frontierAt2 := replayEval (interpOf pBindSync) 2 [Api.evaluate] (machineOf pBindSync)

-- the frontier the red control needs exists, and its machine is neither stuck nor finished
#guard kind frontierAt2 == 1
#guard frontierAt2.machine.stuck.isNone && !frontierAt2.machine.finished

/-- The law's two sides on `pBindSync`: the whole tape, and the prefix continued by
`ReplayResult.thenReplay`. -/
def agreesAt (f : Nat) (a b : List Api.Decision) : Bool :=
  let whole := replayEval (interpOf pBindSync) f (a ++ b) (machineOf pBindSync)
  let split := ReplayResult.thenReplay (interpOf pBindSync) f b
    (replayEval (interpOf pBindSync) f a (machineOf pBindSync))
  kind whole == kind split && sameMachine whole.machine split.machine

-- the fuel arm absorbs the suffix; the other arms hand the machine on
#guard agreesAt 2 [Api.evaluate] [interruptRoot]
#guard agreesAt 8 [Api.evaluate] [interruptRoot]
#guard agreesAt 8 [] [Api.evaluate, interruptRoot]
#guard agreesAt 8 [Api.evaluate, interruptRoot] []

/-! At that frontier the naive law's two sides differ: a fuel frontier against a tape frontier. -/

/--
error: Expression
  kind (replayEval (interpOf pBindSync) 2 ([Api.evaluate] ++ []) (machineOf pBindSync)) ==
    kind (replayEval (interpOf pBindSync) 2 [] frontierAt2.machine)
did not evaluate to `true`
-/
#guard_msgs (error) in
#guard kind (replayEval (interpOf pBindSync) 2 ([Api.evaluate] ++ []) (machineOf pBindSync)) ==
  kind (replayEval (interpOf pBindSync) 2 [] frontierAt2.machine)

end Test.Runtime.TapeAction
