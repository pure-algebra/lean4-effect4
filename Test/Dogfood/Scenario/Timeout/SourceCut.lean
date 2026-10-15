import Test.Dogfood.Proofs.HostTimeoutNumberSourceSlots

/-!
Concepts: scope-lifetime-finalization R11 and translation-simulation R10.
Consumer: the actual source annotation of both Timeout numeric goals.
Readers: the real count continuation and refreshed completed-exit view.
Controls: the outer form finalizer and a changed entry fuel cannot impersonate the attempt entry.
These checks establish no initialized or whole-run history.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Timeout.SourceCut
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Proofs.HostTimeoutNumberConfiguration
open Test.Dogfood.Proofs.HostTimeoutNumberSourceSlots

example (context : CountContext) (view : Test.Dogfood.Proofs.HostTimeoutFlow.View) :
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      ((interpAt Test.Dogfood.Proofs.HostTimeoutSource.program view fetch.table).contA
        (.cont (context.point.child 0)) .unit) :=
  CodeClosure.Slots.interp_contA_at _ fragment _ _ (contract context)
    (fun p held completedView => completed context p completedView held) view fetch.table _ .unit
    ((transport context).child (entry context) 0)

example (context : CountContext) :
    ¬ At context {context.point with path := [1,1,1,0,0,1,0,0]} := by
  intro held
  have lower := held.subtree.length_le
  change 12 ≤ 8 at lower
  omega

example (context : CountContext) :
    ¬ At context {context.point with fuel := context.point.fuel + 1} := by
  intro held
  have fuel := held.entryFuel rfl
  change context.fuel + 4 + 1 = context.fuel + 4 at fuel
  omega

end Test.Dogfood.Scenario.Timeout.SourceCut
