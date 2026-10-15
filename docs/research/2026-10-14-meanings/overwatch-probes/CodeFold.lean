import Effect4.Laws.Program.AnswerSlots.Typed
import Effect4.Machine.Fold

/-!
# Overwatch probe: the code-graph predicates are one fold

Concept: store-typing R4. Question: the code-graph walks of `SourceScope`, `AnswerSlots` and
`AnswerSlots.Typed`, which every value goal reads. Consumer: one parametric code-graph lifting.

`AnswerSlots.CodeAt` (`src/Effect4/Laws/Program/AnswerSlots/Syntax.lean`) is a hand traversal of
runtime code. Runtime code has a generated fold, `cata_prim` (`src/Effect4/Machine/Fold.lean`),
which `PrimWeights` already uses for weights. This probe checks that the predicate is that fold
at one algebra, parametric in its name and thunk predicates, and that a conjunction of predicates
is the fold at the pointwise conjunction.

Reach. Every name predicate, thunk predicate and runtime code.
Not established. The compile, callback and interpreter closure theorems stay per predicate.
-/

set_option autoImplicit false

namespace Overwatch.CodeFold
open Effect4 Effect4.Machine Effect4.Program

/-- The code-graph lifting of a name predicate and a thunk predicate, as one algebra. -/
def codeAlg (name : EffName → Prop) (thunk : EffThunk → Prop) :
    PrimAlgebra EffName EffThunk Val Err Defect FiberId Ann Prop where
  prim_success _ := True
  prim_failure _ := True
  prim_sync suspended := thunk suspended
  prim_suspend suspended := thunk suspended
  prim_withFiber suspended := thunk suspended
  prim_yieldableError _ := True
  prim_iterator callback _ := name callback
  prim_onSuccess body callback := body ∧ name callback
  prim_onSuccessConst body next := body ∧ next
  prim_onFailure body callback := body ∧ name callback
  prim_onSuccessAndFailure body success failure := body ∧ name success ∧ name failure
  prim_exitFrame body := body
  prim_onExit body callback _ := body ∧ name callback
  prim_setInterruptible _ := True
  prim_whileLoop callback _ := name callback
  prim_yieldNowWith _ := True
  prim_async register _ cancel := name register ∧ ∀ callback ∈ cancel, name callback
  prim_asyncFinalizer callback := name callback

/-- `AnswerSlots.CodeAt` is the fold at its name and thunk predicates (`hom_eq_cata_prim`). -/
theorem answerSlots_is_fold (bindings : List Val) (code : NCode) :
    AnswerSlots.CodeAt bindings code =
      cata_prim (codeAlg (AnswerSlots.NameAt bindings) (AnswerSlots.ThunkAt bindings)) code := by
  let hom : PrimHom (codeAlg (AnswerSlots.NameAt bindings) (AnswerSlots.ThunkAt bindings)) := by
    refine ⟨AnswerSlots.CodeAt bindings,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    all_goals intros; rfl
  exact hom_eq_cata_prim hom code

/-- A conjunction of two liftings is the lifting of the pointwise conjunction. -/
theorem fold_and (name₁ name₂ : EffName → Prop) (thunk₁ thunk₂ : EffThunk → Prop) (code : NCode) :
    cata_prim (codeAlg (fun n => name₁ n ∧ name₂ n) (fun t => thunk₁ t ∧ thunk₂ t)) code ↔
      cata_prim (codeAlg name₁ thunk₁) code ∧ cata_prim (codeAlg name₂ thunk₂) code := by
  induction code with
  | success _ | failure _ | yieldableError _ | setInterruptible _ | yieldNowWith _ =>
    exact ⟨fun _ => ⟨trivial, trivial⟩, fun _ => trivial⟩
  | sync _ | suspend _ | withFiber _ | iterator _ _ | whileLoop _ _ | asyncFinalizer _ => exact Iff.rfl
  | onSuccess body callback ih =>
    show (_ ∧ (name₁ callback ∧ name₂ callback)) ↔ (_ ∧ name₁ callback) ∧ (_ ∧ name₂ callback)
    rw [ih]
    exact and_and_and_comm
  | onFailure body callback ih =>
    show (_ ∧ (name₁ callback ∧ name₂ callback)) ↔ (_ ∧ name₁ callback) ∧ (_ ∧ name₂ callback)
    rw [ih]
    exact and_and_and_comm
  | onExit body callback flag ih =>
    show (_ ∧ (name₁ callback ∧ name₂ callback)) ↔ (_ ∧ name₁ callback) ∧ (_ ∧ name₂ callback)
    rw [ih]
    exact and_and_and_comm
  | onSuccessConst body next ih₁ ih₂ =>
    show (_ ∧ _) ↔ (_ ∧ _) ∧ (_ ∧ _)
    rw [ih₁, ih₂]
    exact and_and_and_comm
  | onSuccessAndFailure body success failure ih =>
    show (_ ∧ (name₁ success ∧ name₂ success) ∧ (name₁ failure ∧ name₂ failure)) ↔
      (_ ∧ name₁ success ∧ name₁ failure) ∧ (_ ∧ name₂ success ∧ name₂ failure)
    rw [ih]
    exact ⟨fun ⟨⟨b₁, b₂⟩, ⟨s₁, s₂⟩, ⟨f₁, f₂⟩⟩ => ⟨⟨b₁, s₁, f₁⟩, ⟨b₂, s₂, f₂⟩⟩,
      fun ⟨⟨b₁, s₁, f₁⟩, ⟨b₂, s₂, f₂⟩⟩ => ⟨⟨b₁, b₂⟩, ⟨s₁, s₂⟩, ⟨f₁, f₂⟩⟩⟩
  | exitFrame body ih => exact ih
  | async register flag cancel =>
    show ((name₁ register ∧ name₂ register) ∧ ∀ c ∈ cancel, name₁ c ∧ name₂ c) ↔
      (name₁ register ∧ ∀ c ∈ cancel, name₁ c) ∧ (name₂ register ∧ ∀ c ∈ cancel, name₂ c)
    exact ⟨fun ⟨⟨r₁, r₂⟩, all⟩ => ⟨⟨r₁, fun c m => (all c m).1⟩, ⟨r₂, fun c m => (all c m).2⟩⟩,
      fun ⟨⟨r₁, all₁⟩, ⟨r₂, all₂⟩⟩ => ⟨⟨r₁, r₂⟩, fun c m => ⟨all₁ c m, all₂ c m⟩⟩⟩

end Overwatch.CodeFold
