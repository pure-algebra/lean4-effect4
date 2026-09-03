/-
Contract packet: `test/contracts/trace-patched-host.contract.md` (P-T11, light
ceremony D2), Lean half: the projections from the frame machine's and the
scheduler's alphabets into the service-level trace alphabet. No simulation is
claimed; the projections give a future bridge theorem its statement.
-/

import Effect4.Target.TypeScript.Simulation

namespace Effect4Test.Target.TypeScript.SimulationContract

open Effect4 Effects.Trace

#check @Effect4.Exit.toOutcome
#check @Effect4.FrameEvent.toTrace
#check @Effect4.FrameEvent.traceOf
#check @Effect4.Event.toTrace
#check @Effect4.FrameEvent.traceOf_nil
#check @Effect4.FrameEvent.toTrace_popped
#check @Effect4.FrameEvent.traceOf_finalizers

/-- Exits over natural values and string errors, defects and interruptors. -/
abbrev E := Exit Nat String String Nat Unit

def outcome (exit : E) : Outcome Val :=
  Exit.toOutcome (fun n => .nat n) (fun e => .str e) (fun d => .str ("defect " ++ d)) exit

-- A value projects to its success.
example : outcome (.success 42) = .success (.nat 42) := by decide
-- The first failure's error projects to the failure, whatever follows it.
example : outcome (.failure ⟨[.fail "boom" ReasonAnnotations.empty, .die "later" ReasonAnnotations.empty]⟩) = .failure (.str "boom") := by decide
-- An interruption with no failure before it is `interrupted`.
example : outcome (.failure ⟨[.interrupt (some 1) ReasonAnnotations.empty]⟩) = .interrupted := by decide
-- A defect with no failure projects through `defect`.
example : outcome (.failure ⟨[.die "oops" ReasonAnnotations.empty]⟩) = .failure (.str "defect oops") := by decide

/-- A frame trace with two finalizers, pushes and pops between them, and the
yielded exit projects to exactly the finalizer rows and the outcome. -/
example :
    FrameEvent.traceOf (ν := String) (σ := Unit) (β := Nat) (ε := String) (δ := String) (ι := Nat) (α := Unit)
      (fun name => if name == "a" then 1 else 2)
      (fun n : Nat => .nat n) (fun e : String => .str e) (fun d : String => .str d)
      [ .pushed (.success 0), .ranFinalizer "b" (.success 5), .popped (.success 0)
      , .ranFinalizer "a" (.success 5), .yielded (.success 5) ] =
    [ .finalizer 2 (.success (.nat 5)), .finalizer 1 (.success (.nat 5)), .done (.success (.nat 5)) ] := by
  decide

-- A scheduler completion projects to the outcome; a scheduling event to nothing.
example : Event.toTrace (τ := Nat) (fun n => .success (.nat n)) (.completed ⟨0⟩ 7) =
    some (.done (.success (.nat 7))) := by decide
example : Event.toTrace (τ := Nat) (fun n => .success (.nat n)) (.scheduled ⟨0⟩) = none := by decide

end Effect4Test.Target.TypeScript.SimulationContract
