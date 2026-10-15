import Effect4.Laws.Program.FinalizerInterp
import Effect4.Laws.Program.CodeClosure.Funding

/-!
Concept: scope-lifetime-finalization R11.
Question: actual callback accounting serves `once_placed_outside_census`.
Consumer: the selected-source native evaluator debit.
The shared frame producer spends each saved reservation at the actual selected callback.
The source annotation distinguishes unary success transfers from ordinary callback slots.
This local accounting proves no history bound or progress.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Ordinary value callbacks retain their original name reservation. -/
theorem ordinary_value_le (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (callback : EffName) (value : Val) (placed : OncePlaced (.eff root) q = true)
    (held : OrdinaryNameAt q callback) :
    current root q ((interpAt root view table).contA callback value) ≤ name q callback := by
  have bounded := (interp_value root q view table callback value placed (ordinary_name q callback held)).2
  cases callback
  case releaseUnder => exact held.elim
  all_goals exact bounded

/-- Every actual callback spends the reservation of its source role. -/
theorem fundingHooks (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) :
    CodeClosure.Funding.Hooks (nativeWeights root q) (savedSuccess q (name q))
      (OrdinaryNameAt q) (NameAt q) (interpAt root view table).toPrimInterp where
  value := fun callback value held => (interp_value root q view table callback value placed held).2
  bothValue := fun callback value held => ordinary_value_le root q view table callback value placed held
  cause := fun callback cause held => (interp_cause root q view table callback cause (ordinary_name q callback held)).2
  iterator := fun callback value held => (interp_iter root q view table callback value placed (ordinary_name q callback held)).2
  loop := fun callback cursor value held => (interp_loop_resume root q view table callback cursor value placed (ordinary_name q callback held)).2
  cancel := by
    intro callback cause _
    change current root q (cancelProgramOf callback) + 0 ≤ name q callback
    rw [(cancellation root q callback).2, Nat.zero_add]
    exact Nat.zero_le _

/-- The shared value-arm proof uses the full source annotation. -/
theorem armA_le (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (code : NCode) (value : Val)
    (provided : Option ExitV) (next : NCode) (pushed : List NCode) (held : CodeAt q code)
    (found : code.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    current root q next + (pushed.map (saved root q)).sum ≤ saved root q code :=
  CodeClosure.Funding.armA _ _ _ _ _ _ (fundingHooks root q view table placed) code value provided next pushed held found

/-- The shared cause-arm proof uses the full source annotation. -/
theorem armE_le (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (code : NCode) (cause : CauseV)
    (provided : Option ExitV) (next : NCode) (pushed : List NCode) (held : CodeAt q code)
    (found : code.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    current root q next + (pushed.map (saved root q)).sum ≤ saved root q code :=
  CodeClosure.Funding.armE _ _ _ _ _ _ (fundingHooks root q view table placed) code cause provided next pushed held found

/-- Existing code and saved frames retain the full source annotation. -/
def FrameAt (q : List Nat) (fiber : SourceFrame) : Prop :=
  CodeAt q fiber.current ∧ ∀ code ∈ fiber.stack, CodeAt q code

/-- Actual value return spends the selected callback and remaining saved reservations. -/
theorem resumeValue_le (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (fiber : SourceFrame) (value : Val)
    (provided : Option ExitV) (held : FrameAt q fiber) :
    FrameWeights.returned (frameModel root q)
      ((fiber.resumeValue (interpAt root view table).toPrimInterp value provided).1) ≤
        (fiber.stack.map (saved root q)).sum := by
  apply FrameWeights.resumeValue_le (frameModel root q) _ fiber value provided (fun _ => rfl)
  intro code next pushed selected evaluated
  have owned := CodeClosure.Family.value_selected root table (OrdinaryNameAt q) (NameAt q)
    (ThunkAt q) (hooks root q table placed) view fiber value code held.2 selected
  exact armA_le root q view table placed code value provided next pushed owned evaluated

/-- Actual failure return spends the selected handler and remaining saved reservations. -/
theorem resumeCause_le (root : NativeEff) (q : List Nat) (view) (table : RowTable)
    (placed : OncePlaced (.eff root) q = true) (fiber : SourceFrame) (cause : CauseV)
    (provided : Option ExitV) (held : FrameAt q fiber) :
    FrameWeights.returned (frameModel root q)
      ((fiber.resumeCause (interpAt root view table).toPrimInterp cause provided).1) ≤
        (fiber.stack.map (saved root q)).sum := by
  apply FrameWeights.resumeCause_le (frameModel root q) _ fiber cause provided (fun _ => rfl)
  intro code next pushed selected evaluated
  have owned := CodeClosure.Family.cause_selected root table (OrdinaryNameAt q) (NameAt q)
    (ThunkAt q) (hooks root q table placed) view fiber cause code held.2 selected
  exact armE_le root q view table placed code _ _ next pushed owned evaluated

end Effect4.Program.FinalizerSource
