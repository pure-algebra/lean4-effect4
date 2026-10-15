import Effect4.Laws.Program.AnswerSlots.InitializedCallbacks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual initializer heads join their typed allocation callbacks to the shared saved family.
Reach: the certified leading allocation protocol and arbitrary source budgets.
Limit: native synchronous answers still require their actual store-operation producer.
Consumer: initialized native evaluation and the joint crew driver.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- Allocation continuations join the existing semantic saved-frame constructor. -/
theorem bound_edge (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (input output : Kind) (body : NCode) (name : EffName)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
      ValueAt spec nextWorld input answer → CodeAt spec nextWorld output
        ((interpAt spec.root view spec.table).contA name answer)) :
    Edge spec completed world input output (.onSuccess body name) := by
  apply AnswerFlow.EmbeddedEdgeOver.saved
  refine ⟨?_, by intro body previous scope flag same; cases same⟩
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_success
    · intro nextWorld future answer good
      exact callback nextWorld future view answer good
    · intro nextWorld future cause good
      exact good
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- An initializer child exposes either its actual reference allocation or a live source frontier. -/
theorem allocation_code (spec : Spec) (world : World) (index : Nat) (point : Point)
    (small : index < spec.initialization.width) (stage : RootStage spec world index point) :
    CodeAt spec world (.allocated index)
      (compileEff (.perform .refMake (spec.initialization.request index)) (point.child 0)) := by
  cases amount : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount (.inl stage.2.1)
  | succ fuel =>
    rw [spec.initialization.operation index (point.child 0) fuel small amount]
    exact .allocating small stage

/-- The gate child exposes either its actual deferred allocation or a live source frontier. -/
theorem gate_code (spec : Spec) (world : World) (point : Point)
    (stage : RootStage spec world spec.initialization.width point) :
    CodeAt spec world .gate
      (compileEff (.perform (.deferredMakeOf spec.gateValue spec.gateError) (.lit .unit)) (point.child 0)) := by
  cases amount : (point.child 0).fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount (.inl stage.2.1)
  | succ fuel =>
    rw [gate_operation spec (point.child 0) fuel amount]
    exact .gateAllocating stage

/-- An initialized source frontier retains its existing answer class under actual suspension. -/
theorem frontier_code (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) (point : Point) (zero : point.fuel = 0) (phase : Phase spec world) :
    CodeAt spec world kind ((interpAt spec.root completed spec.table).suspendBody (.body point)) := by
  change CodeAt spec world kind (suspendBodyAt spec.root (.body {point with completed}))
  simp only [suspendBodyAt, zero]
  exact .frontier rfl phase

/-- Every actual initializer root has the existing native current-head contract. -/
theorem initial_head (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (index : Nat) (point : Point)
    (stage : RootStage spec world index point) :
    AnswerFlow.HeadAt (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (Edge spec completed) world (.stable .root) (resolve spec.root point) := by
  cases amount : point.fuel with
  | zero =>
    unfold resolve
    split
    · rw [Agreement.compileEff_at_zero _ amount]
      exact .suspend _ (frontier_code spec completed world _ point amount (.inl stage.2.1))
    · exact .failure _ (.inl stage.2.1)
  | succ fuel =>
    by_cases small : index < spec.initialization.width
    · rw [spec.initialization.compile index point fuel small stage.2.2.1 amount]
      refine .onSuccess (Kind.allocated index) _ _ (allocation_code spec world index point small stage) ?_
      exact bound_edge spec completed world (.allocated index) (.stable .root) _ _
        (allocation_callback spec world · index point small stage)
    · have bound := stage.1
      have last : index = spec.initialization.width := by omega
      subst index
      obtain ⟨tail, found⟩ := spec.gate_head
      rw [← stage.2.2.1] at found
      rw [Agreement.resolve_of_at found, Agreement.compileEff_bind _ _ amount]
      refine .onSuccess Kind.gate _ _ (gate_code spec world point stage) ?_
      apply bound_edge spec completed world .gate (.stable .root)
      intro nextWorld future view answer good
      exact gate_callback spec fragment world nextWorld point stage view answer good
end Effect4.Program.AnswerSlots.Initialized
