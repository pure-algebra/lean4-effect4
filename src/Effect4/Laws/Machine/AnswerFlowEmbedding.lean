import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: an initialized phase model reuses an existing stable saved family and native head.
Reach: explicit world and answer-class maps, a future-closed ready predicate and the same interpreter.
Limit: the embedding supplies no initialization, readiness or native command preservation proof.
Consumer: the shared initializer and protected stable crew answer model.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
universe u v w
open Effect4 Effect4.Contracts
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World Kind NewWorld NewKind : Type w}
variable (oldModel : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (newModel : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) NewWorld NewKind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (worldOf : NewWorld → World) (kindOf : Kind → NewKind) (Ready : NewWorld → Prop)

/-- A ready phase retains the existing stable model's answer and current-code meanings. -/
structure FamilyEmbedding : Prop where
  ready_future : ∀ world nextWorld, newModel.future world nextWorld → Ready world → Ready nextWorld
  future : ∀ world nextWorld, newModel.future world nextWorld → Ready world →
    oldModel.future (worldOf world) (worldOf nextWorld)
  value_read : ∀ world kind value, Ready world → newModel.value world (kindOf kind) value →
    oldModel.value (worldOf world) kind value
  value_write : ∀ world kind value, Ready world → oldModel.value (worldOf world) kind value →
    newModel.value world (kindOf kind) value
  cause_read : ∀ world kind cause, Ready world → newModel.cause world (kindOf kind) cause →
    oldModel.cause (worldOf world) kind cause
  cause_write : ∀ world kind cause, Ready world → oldModel.cause (worldOf world) kind cause →
    newModel.cause world (kindOf kind) cause
  code : ∀ world kind program, Ready world → oldModel.code (worldOf world) kind program →
    newModel.code world (kindOf kind) program
  finalizer : ∀ world name exit, Ready world →
    newModel.finalizer world name exit = oldModel.finalizer (worldOf world) name exit

/-- Initializer semantic frames coexist with the mapped existing stable saved edges. -/
inductive EmbeddedEdge (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) :
    NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop
  | saved {world input output frame} (held : SavedAt newModel interp world input output frame) :
      EmbeddedEdge Edge world input output frame
  | mapped {world input output frame} (ready : Ready world)
      (held : Edge (worldOf world) input output frame) :
      EmbeddedEdge Edge world (kindOf input) (kindOf output) frame

variable {oldModel newModel worldOf kindOf Ready}

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Installed finalizer interception agrees at every embedded ready world. -/
theorem FamilyEmbedding.programOf (embedding : FamilyEmbedding oldModel newModel worldOf kindOf Ready)
    (world : NewWorld) (ready : Ready world) (frame : Prim ν σ β ε δ ι α) (exit : Exit β ε δ ι α) :
    programOf newModel world frame exit = programOf oldModel (worldOf world) frame exit := by
  cases frame
  case onExit body name flag => exact embedding.finalizer world name exit ready
  all_goals rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Actual exits map back to the stable input class without changing their values or causes. -/
theorem FamilyEmbedding.exit_read (embedding : FamilyEmbedding oldModel newModel worldOf kindOf Ready)
    (world : NewWorld) (ready : Ready world) (kind : Kind) (exit : Exit β ε δ ι α)
    (good : ExitAt newModel world (kindOf kind) exit) : ExitAt oldModel (worldOf world) kind exit := by
  cases exit with
  | success value => exact embedding.value_read world kind value ready good
  | failure cause => exact embedding.cause_read world kind cause ready good

/-- Existing stable callback results map their actual code and ordered saved path together. -/
theorem FamilyEmbedding.result (embedding : FamilyEmbedding oldModel newModel worldOf kindOf Ready)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) (world : NewWorld) (ready : Ready world)
    (output : Kind) (next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (held : FamilyResult oldModel Edge (worldOf world) output next pushed) :
    FamilyResult newModel (EmbeddedEdge newModel interp worldOf kindOf Ready Edge) world (kindOf output) next pushed := by
  obtain ⟨input, code, path⟩ := held
  exact ⟨kindOf input, embedding.code world input next ready code,
    path.map_objects kindOf (fun _ _ _ saved => .mapped ready saved)⟩

/-- Ready stable edges and new initializer semantic edges share one saved-family proof. -/
theorem FamilyEmbedding.family (embedding : FamilyEmbedding oldModel newModel worldOf kindOf Ready)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) (family : SavedFamily oldModel interp Edge) :
    SavedFamily newModel interp (EmbeddedEdge newModel interp worldOf kindOf Ready Edge) := by
  have semantic := saved_family newModel interp
  constructor
  · intro world input output frame edge nextWorld future value good absent
    cases edge with
    | saved held => exact semantic.skip world input output frame held nextWorld future value good absent
    | mapped ready held =>
      have later := embedding.ready_future world nextWorld future ready
      exact embedding.value_write nextWorld _ value later (family.skip _ _ _ frame held _
        (embedding.future world nextWorld future ready) value
        (embedding.value_read nextWorld _ value later good) absent)
  · intro world input output frame edge nextWorld future cause good absent
    cases edge with
    | saved held => exact semantic.skipCause world input output frame held nextWorld future cause good absent
    | mapped ready held =>
      have later := embedding.ready_future world nextWorld future ready
      exact embedding.cause_write nextWorld _ cause later (family.skipCause _ _ _ frame held _
        (embedding.future world nextWorld future ready) cause
        (embedding.cause_read nextWorld _ cause later good) absent)
  · intro world input output frame edge nextWorld future value provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      obtain ⟨middle, code, path⟩ := semantic.answer world input output frame held nextWorld future value provided next pushed good supplied absent arm
      exact ⟨middle, code, path.map (fun _ _ _ saved => .saved saved)⟩
    | mapped ready held =>
      have later := embedding.ready_future world nextWorld future ready
      apply embedding.result interp Edge nextWorld later _ next pushed
      apply family.answer _ _ _ frame held _ (embedding.future world nextWorld future ready)
        value provided next pushed (embedding.value_read nextWorld _ value later good)
      · intro exit member
        exact embedding.exit_read nextWorld later _ exit (supplied exit member)
      · rw [← embedding.programOf nextWorld later]
        exact absent
      · exact arm
  · intro world input output frame edge nextWorld future cause provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      obtain ⟨middle, code, path⟩ := semantic.cause world input output frame held nextWorld future cause provided next pushed good supplied absent arm
      exact ⟨middle, code, path.map (fun _ _ _ saved => .saved saved)⟩
    | mapped ready held =>
      have later := embedding.ready_future world nextWorld future ready
      apply embedding.result interp Edge nextWorld later _ next pushed
      apply family.cause _ _ _ frame held _ (embedding.future world nextWorld future ready)
        cause provided next pushed (embedding.cause_read nextWorld _ cause later good)
      · intro exit member
        exact embedding.exit_read nextWorld later _ exit (supplied exit member)
      · rw [← embedding.programOf nextWorld later]
        exact absent
      · exact arm
  · intro world input output frame edge nextWorld future exit next good program
    cases edge with
    | saved held => exact semantic.program world input output frame held nextWorld future exit next good program
    | mapped ready held =>
      have later := embedding.ready_future world nextWorld future ready
      apply embedding.code nextWorld _ next later
      apply family.program _ _ _ frame held _ (embedding.future world nextWorld future ready)
        exit next (embedding.exit_read nextWorld later _ exit good)
      rw [← embedding.programOf nextWorld later]
      exact program
  · intro world input output frame edge nextWorld future fiber cause delivered good selected interrupted skipped
    cases edge with
    | saved held => exact semantic.discard world input output frame held nextWorld future fiber cause delivered good selected interrupted skipped
    | mapped ready held =>
      have later := embedding.ready_future world nextWorld future ready
      exact embedding.cause_write nextWorld _ delivered later
        (family.discard _ _ _ frame held _ (embedding.future world nextWorld future ready) fiber cause delivered
          (embedding.cause_read nextWorld _ cause later good) selected interrupted skipped)
/-- Embedded saved edges retain the stable and initializer future contracts together. -/
theorem FamilyEmbedding.edge_future (embedding : FamilyEmbedding oldModel newModel worldOf kindOf Ready)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (transport : ∀ world nextWorld, oldModel.future world nextWorld → ∀ input output frame,
      Edge world input output frame → Edge nextWorld input output frame)
    (world nextWorld : NewWorld) (future : newModel.future world nextWorld)
    (input output : NewKind) (frame : Prim ν σ β ε δ ι α)
    (held : EmbeddedEdge newModel interp worldOf kindOf Ready Edge world input output frame) :
    EmbeddedEdge newModel interp worldOf kindOf Ready Edge nextWorld input output frame := by
  cases held with
  | saved owned => exact .saved (saved_mono newModel interp future owned)
  | mapped ready owned =>
    exact .mapped (embedding.ready_future world nextWorld future ready)
      (transport _ _ (embedding.future world nextWorld future ready) _ _ _ owned)

/-- The existing stable native head maps into the ready initialized model without rechecking callbacks. -/
theorem FamilyEmbedding.head (embedding : FamilyEmbedding oldModel newModel worldOf kindOf Ready)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (world : NewWorld) (ready : Ready world) (input : Kind) (program : Prim ν σ β ε δ ι α)
    (held : HeadAt oldModel interp Edge (worldOf world) input program) :
    HeadAt newModel interp (EmbeddedEdge newModel interp worldOf kindOf Ready Edge)
      world (kindOf input) program := by
  cases held with
  | success value good => exact .success value (embedding.value_write world input value ready good)
  | failure cause good => exact .failure cause (embedding.cause_write world input cause ready good)
  | sync thunk good => exact .sync thunk (embedding.value_write world input _ ready good)
  | suspend thunk code => exact .suspend thunk (embedding.code world input _ ready code)
  | withFiber thunk code => exact .withFiber thunk (embedding.code world input _ ready code)
  | yieldableError error good => exact .yieldableError error (embedding.cause_write world input _ ready good)
  | iterator name cursor code answer =>
    refine .iterator name cursor (embedding.code world input _ ready code) ?_
    intro next pushed actual
    exact embedding.result interp Edge world ready input next pushed (answer next pushed actual)
  | onSuccess middle body name code saved =>
    exact .onSuccess (kindOf middle) body name (embedding.code world middle body ready code) (.mapped ready saved)
  | onSuccessConst middle body next code saved =>
    exact .onSuccessConst (kindOf middle) body next (embedding.code world middle body ready code) (.mapped ready saved)
  | onFailure middle body name code saved =>
    exact .onFailure (kindOf middle) body name (embedding.code world middle body ready code) (.mapped ready saved)
  | onSuccessAndFailure middle body success failure code saved =>
    exact .onSuccessAndFailure (kindOf middle) body success failure (embedding.code world middle body ready code) (.mapped ready saved)
  | exitFrame middle body code saved =>
    exact .exitFrame (kindOf middle) body (embedding.code world middle body ready code) (.mapped ready saved)
  | onExit middle body name flag code saved =>
    exact .onExit (kindOf middle) body name flag (embedding.code world middle body ready code) (.mapped ready saved)
  | setInterruptible flag good => exact .setInterruptible flag (embedding.cause_write world input _ ready good)
  | asyncFinalizer name good => exact .asyncFinalizer name (embedding.cause_write world input _ ready good)
  | yieldNowWith priority code => exact .yieldNowWith priority (embedding.code world input _ ready code)
  | async register signal cancel code => exact .async register signal cancel (embedding.code world input _ ready code)
  | whileLoop name cursor proceed finish =>
    refine .whileLoop name cursor ?_ ?_
    · intro next body actual
      exact embedding.result interp Edge world ready input body _ (proceed next body actual)
    · intro body actual
      exact embedding.result interp Edge world ready input body _ (finish body actual)
end Effect4.Machine.AnswerFlow
