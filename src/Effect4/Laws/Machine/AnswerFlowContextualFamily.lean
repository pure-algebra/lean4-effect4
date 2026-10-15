import Effect4.Laws.Machine.AnswerFlowFamily

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: Atomic and Timeout transport actual recorded interruption causes through saved handlers.
Reach: existing saved frames, actual callback results and an explicit recorded-cause admission predicate.
Consumer: the shared cause-pop proof and the numeric application families.
The legacy family remains an instance. Admission requires an actual command invariant.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]

/-- Saved-handler discard reads the actual admitted recorded cause. -/
structure ContextualSavedFamily
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (Allowed : World → Option (Cause ε δ ι α) → Prop) : Prop where
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
    Allowed nextWorld (frame.ensure fiber).1.interruptedCause →
    (frame.ensure fiber).1.interrupted = true →
    FrameFiber.skippedCause .contE frame (frame.ensure fiber).1 (some cause) = some delivered →
    model.cause nextWorld output delivered

/-- Every legacy unconditional family admits every chosen recorded-cause predicate. -/
theorem SavedFamily.contextual
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (Allowed : World → Option (Cause ε δ ι α) → Prop)
    (family : SavedFamily model interp Edge) : ContextualSavedFamily model interp Edge Allowed := {
  skip := family.skip
  skipCause := family.skipCause
  answer := family.answer
  cause := family.cause
  program := family.program
  discard world input output frame held nextWorld future fiber cause delivered good selected _admitted interrupted actual :=
    family.discard world input output frame held nextWorld future fiber cause delivered good selected interrupted actual

}


/-- A family with unrestricted recorded causes recovers the original public contract. -/
theorem ContextualSavedFamily.unconditional
    (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
    (interp : PrimInterp ν σ β ε δ ι α)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (family : ContextualSavedFamily model interp Edge (fun _ _ => True)) : SavedFamily model interp Edge where
  skip := family.skip
  skipCause := family.skipCause
  answer := family.answer
  cause := family.cause
  program := family.program
  discard world input output frame held nextWorld future fiber cause delivered good selected interrupted actual :=
    family.discard world input output frame held nextWorld future fiber cause delivered good selected trivial interrupted actual

end Effect4.Machine.AnswerFlow
