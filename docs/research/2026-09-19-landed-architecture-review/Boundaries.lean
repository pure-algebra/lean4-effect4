import Effect4.Laws.Auto.Obligations
import Effect4.Laws.Program.Progress
import Effect4.Run
import Effect4.Program.Fragment

namespace Review.Ledger
open ProofGraph

def closed : Obligation True := ⟨⟩
def leftover (n : Nat) : ProofWanted (n = n) := ⟨⟩
#typed_state_obligations Review.Ledger ceiling 0 using aesop
#print axioms closed.checked
end Review.Ledger

namespace Review.World
open Effect4 Effect4.Machine Effect4.Program

def good : Stores := { Stores.empty with refs := [.nat 0] }
def bad : Stores := { Stores.empty with refs := [.bool false] }

theorem ordered : good.le bad := by
  refine ⟨by decide, by decide, ?_, by decide, ?_, by decide⟩
  · intro key h
    exact h
  · intro key h
    exact h

theorem goodTyped : Effect4.Program.Stores.HeapNat good := by decide
theorem badUntyped : ¬ Effect4.Program.Stores.HeapNat bad := by decide

theorem heapNotMonotone :
    ¬ (∀ s s' : Stores, s.le s' → Effect4.Program.Stores.HeapNat s →
      Effect4.Program.Stores.HeapNat s') :=
  fun h => badUntyped (h good bad ordered goodTyped)

#print axioms heapNotMonotone
#print axioms ordered
#print axioms goodTyped
#print axioms badUntyped
end Review.World

namespace Review.StraightFrontier
open Effect4 Effect4.Machine Effect4.Program

def p : NativeEff := .bind (.succeed (.lit (.nat 1))) (.succeed (.lit (.nat 2)))
#guard Denote.Straight p = true
def initial : Api.Machine :=
  let m := Api.load p 400
  { m with fibers := m.fibers.map (fun f => { f with preventYield := true }) }
#guard (initial.fiber? Api.root).map RunFiber.preventYield = some true
#guard (stepDecisionState (interpOf p) 1 initial Api.evaluate).2 = false
#guard ((stepDecisionState (interpOf p) 400 initial Api.evaluate).1.fiber? Api.root).bind
  RunFiber.exit = some (.success (.nat 2))
end Review.StraightFrontier
