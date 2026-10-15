import Effect4.Laws.Machine.AnswerFlowViews
import Effect4.Laws.Machine.AnswerFlowRecursive

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: one recursive saved-family adapter accepts uniform semantic callback edges.
Reach: existing loop and iterator hooks and a supplied semantic family.
Limit: native callback, initialization and history producers remain explicit.
Consumer: view-uniform Typed and Initialized saved graphs.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4 Effect4.Contracts
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (Semantic : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
variable (broad : Kind) (Loop Iter : World → ν → Prop)

/-- Recursive syntax names join any supplied semantic edge family. -/
inductive RecursiveFamilyEdge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop
  | saved {world input output frame} (held : Semantic world input output frame) :
      RecursiveFamilyEdge world input output frame
  | loop {world name} (cursor : β) (held : Loop world name) :
      RecursiveFamilyEdge world broad broad (.whileLoop name cursor)
  | iterator {world name} (cursor : β) (held : Iter world name) :
      RecursiveFamilyEdge world broad broad (.iterator name cursor)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- A semantic callback retains its actual pushed suffix in the common recursive family. -/
theorem recursive_family_result (world : World) (output : Kind) (next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α))
    (held : FamilyResult model Semantic world output next pushed) :
    FamilyResult model (RecursiveFamilyEdge Semantic broad Loop Iter) world output next pushed := by
  obtain ⟨input, code, path⟩ := held
  exact ⟨input, code, path.map (fun _ _ _ edge => .saved edge)⟩

/-- The existing recursive hook algebra composes with a supplied semantic saved family. -/
theorem recursive_family_of (semantic : SavedFamily model interp Semantic)
    (hooks : RecursiveHooks model interp broad Loop Iter) :
    SavedFamily model interp (RecursiveFamilyEdge Semantic broad Loop Iter) := by
  constructor
  · intro world input output frame edge nextWorld future value good absent
    cases edge with
    | saved held => exact semantic.skip world input output frame held nextWorld future value good absent
    | loop => cases absent
    | iterator => cases absent
  · intro world input output frame edge nextWorld future cause good absent
    cases edge with
    | saved held => exact semantic.skipCause world input output frame held nextWorld future cause good absent
    | loop => exact good
    | iterator => exact good
  · intro world input output frame edge nextWorld future value provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      exact recursive_family_result model Semantic broad Loop Iter nextWorld output next pushed
        (semantic.answer world input output frame held nextWorld future value provided next pushed good supplied absent arm)
    | loop cursor held =>
      have later := hooks.loop_future world nextWorld future _ held
      have code := hooks.loop_resume nextWorld _ cursor value later
      change (match interp.loopResume _ cursor value with
        | .continue next body => some (body, [Prim.whileLoop _ next])
        | .finish body => some (body, [])) = some (next, pushed) at arm
      cases actual : interp.loopResume _ cursor value with
      | «continue» cursor body =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, code, .cons (.loop cursor later) (.nil broad)⟩
      | finish body =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, code, .nil broad⟩
    | iterator cursor held =>
      have later := hooks.iter_future world nextWorld future _ held
      have code := hooks.iter_next nextWorld _ value later
      change (match (interp.iterNext _ value).2 with
        | .done result => some (Prim.success result, [])
        | .halt reason => some (Prim.failure reason, [])
        | .resume body continueAs => some (body, [Prim.iterator continueAs cursor])) = some (next, pushed) at arm
      cases actual : (interp.iterNext _ value).2 with
      | done result =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, model.success nextWorld broad result code, .nil broad⟩
      | halt reason =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, model.failure nextWorld broad reason code, .nil broad⟩
      | resume body continueAs =>
        rw [actual] at arm code
        cases arm
        exact ⟨broad, code.1, .cons (.iterator cursor code.2) (.nil broad)⟩
  · intro world input output frame edge nextWorld future cause provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      exact recursive_family_result model Semantic broad Loop Iter nextWorld output next pushed
        (semantic.cause world input output frame held nextWorld future cause provided next pushed good supplied absent arm)
    | loop => cases arm
    | iterator => cases arm
  · intro world input output frame edge nextWorld future exit next good program
    cases edge with
    | saved held => exact semantic.program world input output frame held nextWorld future exit next good program
    | loop => cases program
    | iterator => cases program
  · intro world input output frame edge nextWorld future fiber cause delivered good selected interrupted skipped
    cases edge with
    | saved held => exact semantic.discard world input output frame held nextWorld future fiber cause delivered good selected interrupted skipped
    | loop => cases selected
    | iterator => cases selected
end Effect4.Machine.AnswerFlow
