import Effect4.Laws.Program.PlaceFunding.Commands
import Test.Dogfood.Scenario.Atomic.WriterMachine
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.WriterFunding
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.PlaceFunding
open WriterPhase

theorem administrative (id : Nat) (root : NativeEff) (table : RowTable) :
    Administration (WriterMachine.ledger id) (fun code => current id code = 0) (interpOf root table) where
  race := by
    intro race cleanup exit
    cases cleanup
    · cases exit <;> rfl
    · rfl
  await := by
    intro machine kind
    unfold asVoidCode
    fun_cases awaitCode (interpOf root table) machine kind
    all_goals aesop (add norm simp [current, cata_prim, interpOf, thunk, name, Prim.ofExit]) (add safe cases [Supervision.ObserverMode, Exit])
  children := fun _ _ => rfl
  park := fun _ => rfl
  cancel := by
    intro fiber race token
    simp only [WriterMachine.ledger, frame, saved, interpOf, name, storeName,
      List.map_cons, List.sum_cons, Nat.zero_add]
    exact Nat.le_refl _
  iterator := by
    intro fiber
    simp only [WriterMachine.ledger, frame, saved, interpOf, name, storeName,
      List.map_cons, List.sum_cons, Nat.zero_add]
    exact Nat.le_refl _


theorem terminal_zero (id : Nat) (code : NCode) (reply : SourceScope.TerminalReply code) :
    current id code = 0 := by
  cases reply <;> rfl

-- An arbitrary callback push may hold a real note reservation.
-- Actual commands never choose this stored note callback as their cancel frame.
def emptyFiber : SourceScope.SourceFiber := RunFiber.make ⟨0⟩ (.success .unit) false (0, false) emptyCtx

def noteCallback : EffName := .store (.seq (.syncOp (.refUpdate ⟨0⟩ (Store.noteAt 1 0) [])))

example : WriterPhase.frame 1 {emptyFiber.frame with stack := [.asyncFinalizer noteCallback]} = 1 := by
  rfl

example : WriterPhase.frame 1 emptyFiber.frame = 0 := rfl

example : ¬ (∀ fiber name, (WriterMachine.ledger 1).fiber
    {fiber with frame.stack := .asyncFinalizer name :: fiber.frame.stack} ≤ (WriterMachine.ledger 1).fiber fiber) := by
  intro broad
  have impossible := broad emptyFiber noteCallback
  change 1 ≤ 0 at impossible
  omega
end Test.Dogfood.Scenario.Atomic.WriterFunding
