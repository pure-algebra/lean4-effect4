import Effect4.Laws.Program.FinalizerRace
import Effect4.Laws.Program.PlaceFunding.Control
import Effect4.Laws.Machine.WriterActions
import Effect4.Laws.Program.NativeReplies
import Effect4.Laws.Program.SourceOpportunityCommands

/-!
Concept: scope-lifetime-finalization, R11.
Question: command control for the joint finalizer source and custody budget.
Consumer: the selected-source command invariant.
Reach: actual metadata edits, interruption, native replies and administrative code.
The race and detached program places remain present in the ledger.
These facts establish no native evaluator debit or whole-history bound.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

abbrev Free (root : NativeEff) (q : List Nat) (code : NCode) : Prop := current root q code = 0

/-- Actual metadata edits and interruptions keep or lower the existing source frame places. -/
theorem control (root : NativeEff) (q : List Nat) :
    PlaceFunding.Control (ledger root q) (Free root q) where
  metadata := by
    intro old next _ active stack _
    change frame root q next.frame ≤ frame root q old.frame
    simp only [frame, active, stack, Nat.le_refl]
  interruption := Machine.WriterWeights.interrupt_weight_le (frameModel root q)
  replace := by
    intro fiber code free
    change frame root q {fiber.frame with current := code} ≤ frame root q fiber.frame
    simp only [frame, free, Nat.zero_add]
    omega
  entry := by
    intro owner code flag budget context free
    simp only [ledger, RunFiber.make, FrameFiber.start, frame, free, List.map_nil,
      List.sum_nil, Nat.add_zero]
  clear := by
    intro fiber
    change frame root q {fiber.frame with stack := []} ≤ frame root q fiber.frame
    simp only [frame, List.map_nil, List.sum_nil, Nat.add_zero]
    omega

/-- Actual administrative trace events spend no selected source reservation. -/
theorem events (root : NativeEff) (q : List Nat) : PlaceFunding.Events (ledger root q) where
  administrative := by
    intro event administrative
    cases event
    case frame owner event => cases administrative
    all_goals exact Nat.le_refl _

/-- Scope bookkeeping changes no active source place in the store. -/
theorem stores (root : NativeEff) (q : List Nat) (table : RowTable) :
    PlaceFunding.StoreHooks (ledger root q) (interpOf root table) where
  link := fun _ _ _ _ _ _ _ => Nat.le_refl _
  drop := fun _ _ _ _ _ => Nat.le_refl _
  due := fun _ => Nat.le_refl _
  wake := fun _ _ _ => Nat.le_refl _

/-- Native completed replies and represented reference reads carry no selected source. -/
theorem terminal_zero (root : NativeEff) (q : List Nat) (code : NCode)
    (reply : SourceScope.TerminalReply code) : Free root q code := by
  cases reply <;> rfl

/-- The native wait result carries no selected source reservation. -/
theorem await_zero (root : NativeEff) (q : List Nat) (table : RowTable)
    (machine : NativeMachine) (kind : ParkKind) :
    Free root q (awaitCode (interpOf root table) machine kind) := by
  have bound := current_le root q (awaitCode (interpOf root table) machine kind)
  rw [SourceScope.Opportunities.await_code_zero root q table machine kind] at bound
  exact Nat.eq_zero_of_le_zero bound

/-- Native administrative code and saved cleanup hooks carry no selected source reservation. -/
theorem administration (root : NativeEff) (q : List Nat) (table : RowTable) :
    PlaceFunding.Administration (ledger root q) (Free root q) (interpOf root table) where
  race := fun race cleanup exit => terminal_zero root q _ (SourceScope.race_settle_reply root table race cleanup exit)
  await := by
    intro machine kind
    change current root q (awaitCode (interpOf root table) machine kind) + 0 = 0
    rw [await_zero, Nat.add_zero]
  children := fun _ _ => rfl
  park := fun _ => rfl
  cancel := by
    intro fiber race token
    change current root q fiber.frame.current + (0 + (fiber.frame.stack.map (saved root q)).sum) ≤
      frame root q fiber.frame
    simp only [Nat.zero_add, frame, Nat.le_refl]
  iterator := by
    intro fiber
    change current root q fiber.frame.current + (0 + (fiber.frame.stack.map (saved root q)).sum) ≤
      frame root q fiber.frame
    simp only [Nat.zero_add, frame, Nat.le_refl]

end Effect4.Program.FinalizerSource
