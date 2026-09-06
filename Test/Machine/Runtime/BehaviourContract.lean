import Effect4.Machine.Behaviour
import Test.Machine.Runtime.ApproximationContract

/-!
# Behavior contract and counterexamples

Packet: `Test/contracts/machine-behaviour.contract.md`. The quantified statements
pin the public obligations. The guards are finite replay checks with a fixed
compile budget. The counterexamples challenge the proposed frontier projection
and the identification of sufficiency with termination.
-/

set_option autoImplicit false

namespace Test.Runtime.BehaviourContract

open Effect4 Effect4.Machine Effect4.Program
open Test.Runtime.ApproximationContract
open Test.Syntax.CompileContract (pSucceed pBindSync pYieldNow)

#check (Beh_fuel_irrelevant : ∀ (interp : RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores)
  (m : Api.Machine) (tape : List Api.Decision) (n n' : Nat)
  (h : Suffices interp n tape m = true) (h' : Suffices interp n' tape m = true),
  Beh interp m tape n h = Beh interp m tape n' h')

#check (obs_mono_of_le_terminal : ∀ {a b : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores},
  a.terminal = true → ReplayResult.le a b → (obs a.machine).le (obs b.machine))

def observedAt (p : NativeEff) (fuel : Nat) (tape : List Api.Decision) : Obs :=
  obs (replayEval (interpOf p) fuel tape (machineOf p)).machine

#guard observedAt pSucceed 5 [Api.evaluate] = observedAt pSucceed 20 [Api.evaluate]
#guard observedAt pBindSync 8 [Api.evaluate] = observedAt pBindSync 20 [Api.evaluate]
#guard observedAt pYieldNow 7 [Api.evaluate, Api.flush] =
  observedAt pYieldNow 20 [Api.evaluate, Api.flush]
#guard (observedAt pSucceed 5 [Api.evaluate]).exits = [(Api.root, some (.success (.nat 42)))]
#guard (observedAt pBindSync 8 [Api.evaluate]).stores.refs = []

def bare : Api.Machine := RunMachine.empty Stores.empty
def withCell : Api.Machine := { bare with state := { Stores.empty with refs := [Val.unit] } }

-- E4-BEH-CE-001: trace-prefix order alone does not protect the stores.
theorem equal_traces : withCell.trace = bare.trace := rfl

theorem frontiers_related : ReplayResult.le (.frontier withCell) (.frontier bare) :=
  List.prefix_rfl

theorem observations_not_related : ¬ (obs withCell).le (obs bare) := by
  intro h
  exact Nat.not_succ_le_zero 0 h.2.1

theorem frontier_projection_false :
    ¬ (∀ (a b : ReplayResult EffName EffThunk Val Err Defect FiberId Ann Ctx Stores),
      ReplayResult.le a b → (obs a.machine).le (obs b.machine)) := by
  intro h
  exact observations_not_related (h (.frontier withCell) (.frontier bare) frontiers_related)

#guard (Val.cell ⟨0⟩).validIn withCell.state
#guard !(Val.cell ⟨0⟩).validIn bare.state
#guard obs withCell ≠ obs bare

-- Equal observations really do ignore the trace.
def traceChanged : Api.Machine := { bare with trace := [RunEvent.started Api.root] }
#guard obs bare = obs traceChanged
#guard bare.trace ≠ traceChanged.trace

-- E4-BEH-CE-002: a settled empty tape need not have terminated its fiber.
theorem empty_tape_suffices : Suffices (interpOf pSucceed) 0 [] (machineOf pSucceed) = true := rfl
#guard tag (runAt pSucceed 0 []).outcome = 1
#guard (observedAt pSucceed 0 []).exits = [(Api.root, none)]

example : Beh (interpOf pSucceed) (machineOf pSucceed) [] 0 empty_tape_suffices =
    observedAt pSucceed 100 [] := rfl

end Test.Runtime.BehaviourContract
