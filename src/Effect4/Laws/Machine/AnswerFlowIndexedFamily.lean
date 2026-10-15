import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: store-typing R4.
Consumer: QueueWorkers.jobs_step, whose saved stack mixes ordinary and classified source regions.
An indexed union retains each existing family's input, output and complete pushed path.
This adapter reuses the supplied actual callback families and adds no callback or pop traversal.
-/
set_option autoImplicit false
namespace Effect4.Machine.AnswerFlow
open Effect4 Effect4.Contracts
universe u v w t
variable {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} {World Kind : Type w} {Index : Type t}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
variable (model : Model (ν := ν) (σ := σ) (β := β) (ε := ε) (δ := δ) (ι := ι) (α := α) World Kind)
variable (interp : PrimInterp ν σ β ε δ ι α)
variable (edges : Index → World → Kind → Kind → Prim ν σ β ε δ ι α → Prop)

/-- A saved frame retains the member family that certifies its actual endpoints. -/
def IndexedEdge (world : World) (input output : Kind) (frame : Prim ν σ β ε δ ι α) : Prop :=
  ∃ index, edges index world input output frame

omit [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] in
/-- Every actual pushed frame keeps its original member family in the common stack relation. -/
theorem indexed_result (index : Index) (world : World) (output : Kind)
    (next : Prim ν σ β ε δ ι α) (pushed : List (Prim ν σ β ε δ ι α))
    (held : FamilyResult model (edges index) world output next pushed) :
    FamilyResult model (IndexedEdge edges) world output next pushed := by
  obtain ⟨input, code, path⟩ := held
  exact ⟨input, code, path.map (fun _ _ _ saved => ⟨index, saved⟩)⟩

/-- An indexed union consumes the supplied actual families without weakening any input class. -/
theorem indexed_family (families : ∀ index, SavedFamily model interp (edges index)) :
    SavedFamily model interp (IndexedEdge edges) where
  skip := by
    intro world input output frame held
    obtain ⟨index, owned⟩ := held
    exact (families index).skip world input output frame owned
  skipCause := by
    intro world input output frame held
    obtain ⟨index, owned⟩ := held
    exact (families index).skipCause world input output frame owned
  answer := by
    intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    obtain ⟨index, owned⟩ := held
    exact indexed_result model edges index nextWorld output next pushed
      ((families index).answer world input output frame owned nextWorld future value provided next pushed good supplied absent actual)
  cause := by
    intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    obtain ⟨index, owned⟩ := held
    exact indexed_result model edges index nextWorld output next pushed
      ((families index).cause world input output frame owned nextWorld future cause provided next pushed good supplied absent actual)
  program := by
    intro world input output frame held
    obtain ⟨index, owned⟩ := held
    exact (families index).program world input output frame owned
  discard := by
    intro world input output frame held
    obtain ⟨index, owned⟩ := held
    exact (families index).discard world input output frame owned

/-- The actual current head uses the same member inclusion as every frame it pushes. -/
theorem indexed_head (index : Index) (world : World) (input : Kind)
    (program : Prim ν σ β ε δ ι α)
    (held : HeadAt model interp (edges index) world input program) :
    HeadAt model interp (IndexedEdge edges) world input program := by
  cases held
  case iterator name cursor code answer =>
    refine .iterator name cursor code ?_
    intro next pushed actual
    exact indexed_result model edges index world input next pushed (answer next pushed actual)
  case whileLoop name cursor proceed finish =>
    refine .whileLoop name cursor ?_ ?_
    · intro next body actual
      exact indexed_result model edges index world input body _ (proceed next body actual)
    · intro body actual
      exact indexed_result model edges index world input body [] (finish body actual)
  all_goals aesop (add norm simp [IndexedEdge]) (add safe constructors [HeadAt]) (add safe apply [Exists.intro])
end Effect4.Machine.AnswerFlow
