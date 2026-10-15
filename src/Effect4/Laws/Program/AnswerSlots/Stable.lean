import Effect4.Laws.Machine.AnswerFlowHead
import Effect4.Program.Compile

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: allocation prefixes enter one supplied stable answer-flow instance.
Reach: existing source code, value classes and uniform saved families at actual interpreter views.
Limit: this interface supplies no allocation certificate or history invariant itself.
Consumer: the common allocation adapter and Prefix and protected crew instances.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- A stable source instance annotates existing code and values, with one broad entry class. -/
structure StableSpec where
  root : NativeEff
  table : RowTable
  Kind : Type
  rootKind : Kind
  value : Kind → Val → Prop
  code : Kind → NCode → Prop
  success : ∀ kind answer, value kind answer → code kind (.success answer)
  failure : ∀ kind cause, code kind (.failure cause)

/-- The stable source model reads the actual completed-fiber view for installed finalizer programs. -/
def StableSpec.model (spec : StableSpec) (view : List (FiberId × ExitV)) :
    AnswerFlow.Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann)
      Unit spec.Kind where
  future _ _ := True
  future_refl _ := trivial
  future_trans _ _ _ _ _ := trivial
  value _ := spec.value
  cause _ _ _ := True
  code _ := spec.code
  finalizer _ name exit := ((interpAt spec.root view spec.table).finalizerProgram name exit).map
    (finalizerCode (interpAt spec.root view spec.table) exit)
  success _ := spec.success
  failure _ kind cause _ := spec.failure kind cause

/-- A stable source instance retains common saved endpoints and actual pushed paths under all views. -/
structure StableLaws (spec : StableSpec) where
  Edge : Unit → spec.Kind → spec.Kind → NCode → Prop
  family : ∀ view, AnswerFlow.SavedFamily (spec.model view)
    (interpAt spec.root view spec.table).toPrimInterp Edge
  head : ∀ view kind program, spec.code kind program →
    AnswerFlow.HeadAt (spec.model view) (interpAt spec.root view spec.table).toPrimInterp Edge () kind program
end Effect4.Program.AnswerSlots
