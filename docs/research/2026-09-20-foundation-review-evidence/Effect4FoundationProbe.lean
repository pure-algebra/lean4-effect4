import Effect4.Laws.Program.Typed.World
import Effect4.Laws.Run
import Effect4.Laws.Program.EvaluateR
import Effect4.Laws.Program.RuntimeR

open Lean Elab Command
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched

#print Effect4.Program.Typed.Preds
#print Effect4.Program.Typed.RSavedOk
#print Effect4.Program.Typed.RStateOk
#print Effect4.Program.Typed.TaskOk
#print Effect4.Program.Typed.CmdOk
#print Effect4.Program.Typed.CaptureOk
#print Effect4.Program.Typed.StoresOk
#check Effect4.Program.Typed.protocol_order
#check Effect4.Laws.Effects.Typed.mono
#check Effect4.Program.Sched.loadR

run_elab do
  logInfo m!"Preds is a class: {Lean.isClass (← getEnv) ``Effect4.Program.Typed.Preds}"

namespace FoundationReview

theorem resume_target_erased {W : Type} (P : Typed.Preds W) (w : W) (e : Typed.Expect)
    (a b : FiberId) (t u : Nat) (p : RProgram) :
    Typed.TaskOk P w e (.resume a t p) ↔ Typed.TaskOk P w e (.resume b u p) := Iff.rfl

theorem command_target_erased {W : Type} (P : Typed.Preds W) (w : W) (e : Typed.Expect)
    (a b : FiberId) (t u : Nat) (p : RProgram) :
    Typed.CmdOk P w e (.resume a t p) ↔ Typed.CmdOk P w e (.resume b u p) := Iff.rfl

theorem capture_location_erased {W : Type} (P : Typed.Preds W) (w : W)
    (e : Typed.Expect) (c : Capture) (path : List Nat) (root : Nat) :
    Typed.CaptureOk P w e c ↔ Typed.CaptureOk P w e { c with path, root } := by
  constructor
  · intro h
    exact ⟨h.c0, h.c1⟩
  · intro h
    exact ⟨h.c0, h.c1⟩

def vacant : Nat → Option Bool := fun _ => none
def filled : Nat → Option Bool := fun _ => some false
def conditional (table : Nat → Option Bool) : Prop :=
  ∀ b, table 0 = some b → b = true

theorem conditional_not_monotone :
    Typed.TableExtends vacant filled ∧ conditional vacant ∧ ¬ conditional filled := by
  refine ⟨?_, ?_, ?_⟩
  · intro k b h
    cases h
  · intro b h
    cases h
  · intro h
    have impossible : false = true := h false rfl
    cases impossible

#print axioms resume_target_erased
#print axioms command_target_erased
#print axioms capture_location_erased
#print axioms conditional_not_monotone

end FoundationReview
