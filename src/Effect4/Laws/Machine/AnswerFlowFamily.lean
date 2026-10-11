import Effect4.Laws.Machine.AnswerFlow
import Effect4.Laws.Machine.PopTraceFamily

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: HeapSites.heap_sites_keep and Timeout's numeric history goals share native frame transport.
Reach: external predicates on existing saved frames, with actual future-world callback premises.
Consumers: the lexical NativeFrameScope instance and the state-indexed numeric AnswerFlow instance.
This family supplies no source admission, current-code weakening, command history, or progress.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- An absent installed finalizer supplies the exact pure-callback interception premise.
Consumer: the lexical native frame instance. -/
theorem programOf_none
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (world : World) (frame : Prim ν σ β ε δ ι α) (exit : Exit β ε δ ι α)
    (absent : ∀ name, model.finalizer world name exit = none) : programOf model world frame exit = none := by
  unfold programOf
  split
  · exact absent _
  · rfl

/-- The same current-code result composes through an external saved-frame path. -/
def FamilyResult
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (world : World) (output : Kind) (next : Prim ν σ β ε δ ι α)
    (pushed : List (Prim ν σ β ε δ ι α)) : Prop :=
  ∃ input, model.code world input next ∧ Path (Edge world) input output pushed

/-- Six actual callback obligations parameterize the existing saved-frame contract.
The edge remains external, so an arbitrary recursive lexical callback needs no finite recursive proof. -/
structure SavedFamily
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) : Prop where
  skip : ∀ world input output frame, Edge world input output frame →
    ∀ nextWorld, model.future world nextWorld → ∀ value,
    model.value nextWorld input value → frame.hasArm .contA = false → model.value nextWorld output value
  skipCause : ∀ world input output frame, Edge world input output frame →
    ∀ nextWorld, model.future world nextWorld → ∀ cause,
    model.cause nextWorld input cause → frame.hasArm .contE = false → model.cause nextWorld output cause
  answer : ∀ world input output frame, Edge world input output frame →
    ∀ nextWorld, model.future world nextWorld → ∀ value provided next pushed,
    model.value nextWorld input value → (∀ exit ∈ provided, ExitAt model nextWorld input exit) →
    programOf model nextWorld frame (provided.getD (.success value)) = none →
    frame.armA interp value provided = some (next, pushed) →
    FamilyResult model Edge nextWorld output next pushed
  cause : ∀ world input output frame, Edge world input output frame →
    ∀ nextWorld, model.future world nextWorld → ∀ cause provided next pushed,
    model.cause nextWorld input cause → (∀ exit ∈ provided, ExitAt model nextWorld input exit) →
    programOf model nextWorld frame (provided.getD (.failure cause)) = none →
    frame.armE interp cause provided = some (next, pushed) →
    FamilyResult model Edge nextWorld output next pushed
  program : ∀ world input output frame, Edge world input output frame →
    ∀ nextWorld, model.future world nextWorld → ∀ exit next,
    ExitAt model nextWorld input exit → programOf model nextWorld frame exit = some next →
    model.code nextWorld output next
  discard : ∀ world input output frame, Edge world input output frame →
    ∀ nextWorld, model.future world nextWorld →
    ∀ (fiber : FrameFiber ν σ β ε δ ι α) cause delivered,
    model.cause nextWorld input cause → frame.hasArm .contE = true →
    (frame.ensure fiber).1.interrupted = true →
    FrameFiber.skippedCause .contE frame (frame.ensure fiber).1 (some cause) = some delivered →
    model.cause nextWorld output delivered

/-- Existing semantic results read the same shared path, without changing their public carrier. -/
theorem result_family
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α) {world : World} {output : Kind}
    {next : Prim ν σ β ε δ ι α} {pushed : List (Prim ν σ β ε δ ι α)}
    (result : ResultAt model interp world output next pushed) :
    FamilyResult model (SavedAt model interp) world output next pushed := by
  cases result with
  | mk _ input _ _ _ code stack => exact ⟨input, code, stack_path model interp stack⟩

/-- The existing inductive saved contract is one instance of the external callback family. -/
theorem saved_family
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α) : SavedFamily model interp (SavedAt model interp) := {
  skip := by
    intro world input output frame held
    cases held with
    | mk _ _ _ _ skip _ _ _ _ _ => exact skip
  skipCause := by
    intro world input output frame held
    cases held with
    | mk _ _ _ _ _ skip _ _ _ _ => exact skip
  answer := by
    intro world input output frame held nextWorld future value provided next pushed good supplied absent arm
    cases held with
    | mk _ _ _ _ _ _ answer _ _ _ =>
      exact result_family model interp (answer nextWorld future value provided next pushed good supplied absent arm)
  cause := by
    intro world input output frame held nextWorld future cause provided next pushed good supplied absent arm
    cases held with
    | mk _ _ _ _ _ _ _ answer _ _ =>
      exact result_family model interp (answer nextWorld future cause provided next pushed good supplied absent arm)
  program := by
    intro world input output frame held
    cases held with
    | mk _ _ _ _ _ _ _ _ program _ => exact program
  discard := by
    intro world input output frame held
    cases held with
    | mk _ _ _ _ _ _ _ _ _ discard => exact discard

}

end Effect4.Machine.AnswerFlow
