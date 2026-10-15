import Effect4.Program.Compile

/-!
Concept: store-typing R4, serving `Atomic.Store.shop_stages`.
Consumer: the root's exact answer classes and its coupled fork transition.
These fixed source binder positions carry no history assertion.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The root binds its cells and seven returned fiber handles at these actual positions. -/
def expected (slot : Nat) : Option Val :=
  if slot < 3 then some (Val.cell ⟨slot⟩)
  else if slot < 9 then some (Val.fiber ⟨slot - 2⟩)
  else if slot = 15 then some (Val.fiber ⟨7⟩)
  else none

/-- The number allocated next changes only at an actual root fork binder. -/
def rank (binder : Nat) : Nat :=
  if binder < 9 then binder - 2 else if binder < 16 then 7 else 8

/-- A returned handle occupies the exact binder that requested it. -/
def Answer (binder : Nat) (value : Val) : Prop :=
  ∀ required, expected binder = some required → value = required

/-- Await, sleep and the final interruption allocate no new child identity. -/
theorem rank_unchanged (binder : Nat) (late : 9 ≤ binder) (notFork : binder ≠ 15) :
    rank (binder + 1) = rank binder := by
  have old : ¬ binder < 9 := by omega
  have next : ¬ binder + 1 < 9 := by omega
  simp only [rank, if_neg old, if_neg next]
  by_cases middle : binder < 16
  · have after : binder + 1 < 16 := by omega
    simp only [if_pos middle, if_pos after]
  · have after : ¬ binder + 1 < 16 := by omega
    simp only [if_neg middle, if_neg after]

end Test.Dogfood.Scenario.Atomic.RootSlots
