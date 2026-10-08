import Effect4.Modules.Step
import Effect4.Laws.Modules.Step
import Effect4.Schema.Modeled.Derive
import Effect4.Schema.FieldRef.Elab

/-! Probe REIFY-1: can a step's value equation against an ordinary Lean function close by one
fixed tactic? Hand-reified first; the elaborator comes after. -/

set_option autoImplicit false
open Effect4 Effect4.Program Effect4.Schema Effect4.Schema.Model Effect4.Modules

namespace ReifyProbe

structure Sem where
  permits : Nat
  taken : Nat
  deriving Modeled, Repr

def semFields : List (String × Bool × Ty) := [("permits", false, .nat), ("taken", false, .nat)]

example : Modeled.ty (α := Sem) = .record semFields := rfl

/-- The model, as ordinary Lean. -/
def takeIfAvailable (need : Nat) (s : Sem) : Bool × Sem :=
  if need ≤ s.permits - s.taken then (true, { s with taken := s.taken + need }) else (false, s)

def permitsF : FieldRef semFields .nat := field_ref% "permits"
def takenF : FieldRef semFields .nat := field_ref% "taken"

abbrev Γ : List Ty := [.nat, .record semFields]
def need : Input Γ .nat := .here _ _
def cell : Input Γ (.record semFields) := .there _ (.here _ _)

/-- The hand reification: what the elaborator would write. -/
def takeStep : Step Γ (.prod .bool (.record semFields)) :=
  .ite (.not (.lt (.sub (.get (.var cell) permitsF) (.get (.var cell) takenF)) (.var need)))
    (.pair (.bool true) (.set (.var cell) takenF (.add (.get (.var cell) takenF) (.var need))))
    (.pair (.bool false) (.var cell))

/-- The value equation, stated against the Lean function through `Modeled.toC`. -/
theorem takeStep_eval (n : Nat) (s : Sem) :
    takeStep.eval (Γ := Γ) Leaves.refused ((n, (Modeled.toC s, ())) : Inputs Leaves.refused Γ) =
      Modeled.toC (takeIfAvailable n s) := by
  refine (Step.eval_ite (Γ := Γ) Leaves.refused _ _ _ _).trans ?_
  show cond (!decide (s.permits - s.taken < n)) _ _ = _
  by_cases h : n ≤ s.permits - s.taken
  · have test : (!decide (s.permits - s.taken < n)) = true := by
      simp only [Bool.not_eq_true', decide_eq_false_iff_not, Nat.not_lt]
      exact h
    rw [test]
    simp only [takeIfAvailable, h, if_true, cond_true]
    rfl
  · have test : (!decide (s.permits - s.taken < n)) = false := by
      simp only [Bool.not_eq_false', decide_eq_true_eq]
      exact Nat.lt_of_not_le h
    rw [test]
    simp only [takeIfAvailable, h, if_false, cond_false]
    rfl

end ReifyProbe
