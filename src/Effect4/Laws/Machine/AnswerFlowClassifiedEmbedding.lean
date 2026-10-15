import Effect4.Laws.Machine.AnswerFlowEmbedding

/-!
Concept: store-typing R4.
Consumer: QueueWorkers.jobs_step, whose notification segments retain a captured request phase.
The actual input class establishes readiness at the callback's current world.
Readiness need not persist through arbitrary future worlds with no classified input.
The adapter reuses actual saved-family arms; it adds no compiler, pop or native traversal.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable {World Kind NewWorld NewKind : Type w}
variable (oldModel : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (newModel : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) NewWorld NewKind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (worldOf : NewWorld → World) (kindOf : Kind → NewKind) (Ready : NewWorld → Prop)

/-- Each classified input supplies the local condition needed to reuse an existing family. -/
structure ClassifiedInputEmbedding : Prop where
  future : ∀ world nextWorld, newModel.future world nextWorld → oldModel.future (worldOf world) (worldOf nextWorld)
  value_ready : ∀ world kind value, newModel.value world (kindOf kind) value → Ready world
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

/-- Source-stable edges remain stored even when their classified input later becomes empty. -/
inductive ClassifiedEdgeOver
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) :
    NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop
  | saved {world input output frame} (held : Semantic world input output frame) :
      ClassifiedEdgeOver Semantic Edge world input output frame
  | mapped {world input output frame} (held : Edge (worldOf world) input output frame) :
      ClassifiedEdgeOver Semantic Edge world (kindOf input) (kindOf output) frame

/-- Cause-side closure reads the actual mapped edge and actual selected arm, without input readiness. -/
structure ClassifiedCauseTransfer
    (newModel : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) NewWorld NewKind)
    (interp : PrimInterp ν σ β ε δ ι α)
    (worldOf : NewWorld → World) (kindOf : Kind → NewKind)
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop) : Prop where
  skip : ∀ world input output frame, Edge (worldOf world) input output frame →
    ∀ nextWorld, newModel.future world nextWorld → ∀ cause,
    newModel.cause nextWorld (kindOf input) cause → frame.hasArm .contE = false →
    newModel.cause nextWorld (kindOf output) cause
  cause : ∀ world input output frame, Edge (worldOf world) input output frame →
    ∀ nextWorld, newModel.future world nextWorld → ∀ cause provided next pushed,
    newModel.cause nextWorld (kindOf input) cause →
    (∀ exit ∈ provided, ExitAt newModel nextWorld (kindOf input) exit) →
    programOf newModel nextWorld frame (provided.getD (.failure cause)) = none →
    frame.armE interp cause provided = some (next, pushed) →
    FamilyResult newModel (ClassifiedEdgeOver worldOf kindOf Semantic Edge) nextWorld (kindOf output) next pushed
  program : ∀ world input output frame, Edge (worldOf world) input output frame →
    ∀ nextWorld, newModel.future world nextWorld → ∀ cause next,
    newModel.cause nextWorld (kindOf input) cause →
    programOf newModel nextWorld frame (.failure cause) = some next →
    newModel.code nextWorld (kindOf output) next
  discard : ∀ world input output frame, Edge (worldOf world) input output frame →
    ∀ nextWorld, newModel.future world nextWorld →
    ∀ (fiber : FrameFiber ν σ β ε δ ι α) cause delivered,
    newModel.cause nextWorld (kindOf input) cause → frame.hasArm .contE = true →
    (frame.ensure fiber).1.interrupted = true →
    FrameFiber.skippedCause .contE frame (frame.ensure fiber).1 (some cause) = some delivered →
    newModel.cause nextWorld (kindOf output) delivered

/-- The original interface additionally obtains local readiness from every classified cause. -/
structure ClassifiedEmbedding : Prop extends ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready where
  cause_ready : ∀ world kind cause, newModel.cause world (kindOf kind) cause → Ready world

variable {oldModel newModel worldOf kindOf Ready}
omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The actual exit maps to the existing family's exact input class. -/
theorem ClassifiedInputEmbedding.exit_read (embedding : ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready)
    (world : NewWorld) (ready : Ready world) (kind : Kind) (exit : Exit β ε δ ι α)
    (good : ExitAt newModel world (kindOf kind) exit) : ExitAt oldModel (worldOf world) kind exit := by
  cases exit with
  | success value => exact embedding.value_read world kind value ready good
  | failure cause => exact embedding.cause_read world kind cause ready good

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Installed finalizer interception agrees at the actual classified callback cut. -/
theorem ClassifiedInputEmbedding.programOf (embedding : ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready)
    (world : NewWorld) (ready : Ready world) (frame : Prim ν σ β ε δ ι α) (exit : Exit β ε δ ι α) :
    programOf newModel world frame exit = programOf oldModel (worldOf world) frame exit := by
  cases frame
  case onExit body name flag => exact embedding.finalizer world name exit ready
  all_goals rfl

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- An actual old-family result retains its output and complete pushed path under the local condition. -/
theorem ClassifiedInputEmbedding.result_over (embedding : ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready)
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (world : NewWorld) (ready : Ready world) (output : Kind)
    (next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (held : FamilyResult oldModel Edge (worldOf world) output next pushed) :
    FamilyResult newModel (ClassifiedEdgeOver worldOf kindOf Semantic Edge) world (kindOf output) next pushed := by
  obtain ⟨input, code, path⟩ := held
  exact ⟨kindOf input, embedding.code world input next ready code,
    path.map_objects kindOf (fun _ _ _ saved => .mapped saved)⟩

/-- Existing source and local semantic edges consume actual input readiness before producing output code. -/
theorem ClassifiedInputEmbedding.family_over (embedding : ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready)
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (semantic : SavedFamily newModel interp Semantic) (family : SavedFamily oldModel interp Edge)
    (causes : ClassifiedCauseTransfer newModel interp worldOf kindOf Semantic Edge) :
    SavedFamily newModel interp (ClassifiedEdgeOver worldOf kindOf Semantic Edge) := by
  constructor
  · intro world input output frame edge nextWorld future value good absent
    cases edge with
    | saved held => exact semantic.skip world input output frame held nextWorld future value good absent
    | mapped held =>
      have ready := embedding.value_ready nextWorld _ value good
      exact embedding.value_write nextWorld _ value ready (family.skip _ _ _ frame held _
        (embedding.future world nextWorld future) value (embedding.value_read nextWorld _ value ready good) absent)
  · intro world input output frame edge nextWorld future cause good absent
    cases edge with
    | saved held => exact semantic.skipCause world input output frame held nextWorld future cause good absent
    | mapped held => exact causes.skip world _ _ frame held nextWorld future cause good absent
  · intro world input output frame edge nextWorld future value provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      obtain ⟨middle, code, path⟩ := semantic.answer world input output frame held nextWorld future value provided next pushed good supplied absent arm
      exact ⟨middle, code, path.map (fun _ _ _ saved => .saved saved)⟩
    | mapped held =>
      have ready := embedding.value_ready nextWorld _ value good
      apply embedding.result_over Semantic Edge nextWorld ready _ next pushed
      apply family.answer _ _ _ frame held _ (embedding.future world nextWorld future)
        value provided next pushed (embedding.value_read nextWorld _ value ready good)
      · exact fun exit member => embedding.exit_read nextWorld ready _ exit (supplied exit member)
      · rw [← embedding.programOf nextWorld ready]; exact absent
      · exact arm
  · intro world input output frame edge nextWorld future cause provided next pushed good supplied absent arm
    cases edge with
    | saved held =>
      obtain ⟨middle, code, path⟩ := semantic.cause world input output frame held nextWorld future cause provided next pushed good supplied absent arm
      exact ⟨middle, code, path.map (fun _ _ _ saved => .saved saved)⟩
    | mapped held => exact causes.cause world _ _ frame held nextWorld future cause provided next pushed good supplied absent arm
  · intro world input output frame edge nextWorld future exit next good program
    cases edge with
    | saved held => exact semantic.program world input output frame held nextWorld future exit next good program
    | mapped held =>
      cases exit with
      | success value =>
        have ready := embedding.value_ready nextWorld _ value good
        apply embedding.code nextWorld _ next ready
        apply family.program _ _ _ frame held _ (embedding.future world nextWorld future)
          (.success value) next (embedding.value_read nextWorld _ value ready good)
        rw [← embedding.programOf nextWorld ready]
        exact program
      | failure cause => exact causes.program world _ _ frame held nextWorld future cause next good program
  · intro world input output frame edge nextWorld future fiber cause delivered good selected interrupted skipped
    cases edge with
    | saved held => exact semantic.discard world input output frame held nextWorld future fiber cause delivered good selected interrupted skipped
    | mapped held => exact causes.discard world _ _ frame held nextWorld future fiber cause delivered good selected interrupted skipped

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Stored source edges retain their annotation even if a future world empties the phase-filtered input class. -/
theorem ClassifiedInputEmbedding.edge_future_over
    (embedding : ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready)
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (semantic : ∀ world nextWorld, newModel.future world nextWorld → ∀ input output frame,
      Semantic world input output frame → Semantic nextWorld input output frame)
    (transport : ∀ world nextWorld, oldModel.future world nextWorld → ∀ input output frame,
      Edge world input output frame → Edge nextWorld input output frame)
    (world nextWorld : NewWorld) (future : newModel.future world nextWorld)
    (input output : NewKind) (frame : Prim ν σ β ε δ ι α)
    (held : ClassifiedEdgeOver worldOf kindOf Semantic Edge world input output frame) :
    ClassifiedEdgeOver worldOf kindOf Semantic Edge nextWorld input output frame := by
  cases held with
  | saved owned => exact .saved (semantic world nextWorld future input output frame owned)
  | mapped owned => exact .mapped (transport _ _ (embedding.future world nextWorld future) _ _ frame owned)

/-- An actual current head reuses the source family under its present phase evidence. -/
theorem ClassifiedInputEmbedding.head_over (embedding : ClassifiedInputEmbedding oldModel newModel worldOf kindOf Ready)
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (world : NewWorld) (ready : Ready world) (input : Kind) (program : Prim ν σ β ε δ ι α)
    (held : HeadAt oldModel interp Edge (worldOf world) input program) :
    HeadAt newModel interp (ClassifiedEdgeOver worldOf kindOf Semantic Edge)
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
    exact embedding.result_over Semantic Edge world ready input next pushed (answer next pushed actual)
  | onSuccess middle body name code saved =>
    exact .onSuccess (kindOf middle) body name (embedding.code world middle body ready code) (.mapped saved)
  | onSuccessConst middle body next code saved =>
    exact .onSuccessConst (kindOf middle) body next (embedding.code world middle body ready code) (.mapped saved)
  | onFailure middle body name code saved =>
    exact .onFailure (kindOf middle) body name (embedding.code world middle body ready code) (.mapped saved)
  | onSuccessAndFailure middle body success failure code saved =>
    exact .onSuccessAndFailure (kindOf middle) body success failure (embedding.code world middle body ready code) (.mapped saved)
  | exitFrame middle body code saved =>
    exact .exitFrame (kindOf middle) body (embedding.code world middle body ready code) (.mapped saved)
  | onExit middle body name flag code saved =>
    exact .onExit (kindOf middle) body name flag (embedding.code world middle body ready code) (.mapped saved)
  | setInterruptible flag good => exact .setInterruptible flag (embedding.cause_write world input _ ready good)
  | asyncFinalizer name good => exact .asyncFinalizer name (embedding.cause_write world input _ ready good)
  | yieldNowWith priority code => exact .yieldNowWith priority (embedding.code world input _ ready code)
  | async register signal cancel code => exact .async register signal cancel (embedding.code world input _ ready code)
  | whileLoop name cursor proceed finish =>
    refine .whileLoop name cursor ?_ ?_
    · intro next body actual
      exact embedding.result_over Semantic Edge world ready input body _ (proceed next body actual)
    · intro body actual
      exact embedding.result_over Semantic Edge world ready input body _ (finish body actual)

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- The original readiness-based exit reading remains available. -/
theorem ClassifiedEmbedding.exit_ready (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready)
    (world : NewWorld) (kind : Kind) (exit : Exit β ε δ ι α)
    (good : ExitAt newModel world (kindOf kind) exit) : Ready world := by
  cases exit with
  | success value => exact embedding.value_ready world kind value good
  | failure cause => exact embedding.cause_ready world kind cause good

/-- The original interface projects to its classified-input implementation. -/
abbrev ClassifiedEmbedding.exit_read (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready) :=
  embedding.toClassifiedInputEmbedding.exit_read

/-- The original interface projects to its classified-input implementation. -/
abbrev ClassifiedEmbedding.programOf (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready) :=
  embedding.toClassifiedInputEmbedding.programOf

/-- The original interface projects to its classified-input implementation. -/
abbrev ClassifiedEmbedding.result_over (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready) :=
  embedding.toClassifiedInputEmbedding.result_over

/-- The original interface projects to its classified-input implementation. -/
abbrev ClassifiedEmbedding.edge_future_over (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready) :=
  embedding.toClassifiedInputEmbedding.edge_future_over

/-- The original interface projects to its classified-input implementation. -/
abbrev ClassifiedEmbedding.head_over (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready) :=
  embedding.toClassifiedInputEmbedding.head_over interp

/-- Existing callers retain the readiness-based family as an instance of the selected cause contract. -/
theorem ClassifiedEmbedding.family_over (embedding : ClassifiedEmbedding oldModel newModel worldOf kindOf Ready)
    (Semantic : NewWorld → NewKind → NewKind → Prim ν σ β ε δ ι α → Prop)
    (Edge : World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)
    (semantic : SavedFamily newModel interp Semantic) (family : SavedFamily oldModel interp Edge) :
    SavedFamily newModel interp (ClassifiedEdgeOver worldOf kindOf Semantic Edge) := by
  let values := embedding.toClassifiedInputEmbedding
  apply values.family_over interp Semantic Edge semantic family
  constructor
  · intro world input output frame held nextWorld future cause good absent
    have ready := embedding.cause_ready nextWorld _ cause good
    exact values.cause_write nextWorld _ cause ready (family.skipCause _ _ _ frame held _
      (values.future world nextWorld future) cause (values.cause_read nextWorld _ cause ready good) absent)
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent arm
    have ready := embedding.cause_ready nextWorld _ cause good
    apply values.result_over Semantic Edge nextWorld ready _ next pushed
    apply family.cause _ _ _ frame held _ (values.future world nextWorld future)
      cause provided next pushed (values.cause_read nextWorld _ cause ready good)
    · exact fun exit member => values.exit_read nextWorld ready _ exit (supplied exit member)
    · rw [← values.programOf nextWorld ready]; exact absent
    · exact arm
  · intro world input output frame held nextWorld future cause next good program
    have ready := embedding.cause_ready nextWorld _ cause good
    apply values.code nextWorld _ next ready
    apply family.program _ _ _ frame held _ (values.future world nextWorld future)
      (.failure cause) next (values.cause_read nextWorld _ cause ready good)
    rw [← values.programOf nextWorld ready]
    exact program
  · intro world input output frame held nextWorld future fiber cause delivered good selected interrupted skipped
    have ready := embedding.cause_ready nextWorld _ cause good
    exact values.cause_write nextWorld _ delivered ready
      (family.discard _ _ _ frame held _ (values.future world nextWorld future) fiber cause delivered
        (values.cause_read nextWorld _ cause ready good) selected interrupted skipped)

end Effect4.Machine.AnswerFlow
