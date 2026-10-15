import Effect4.Laws.Program.AnswerSlots.InitializedPhases

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: the shared initialized graph supplies native heads and exact forced-yield continuations.
Reach: actual initialization stages, protected stable code and equal transient allocation counts.
Limit: stateful sync answers use their native store producer rather than the pure frame fallback.
Consumer: the coupled initialized crew evaluator and actual-history driver.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Initialized
open Effect4 Effect4.Machine Effect4.Program

/-- A forced yield resumes the same next code at the exact allocation counts it parked with. -/
theorem yield_edge (spec : Spec) (completed : List (FiberId × ExitV)) (world : World)
    (kind : Kind) (priority : Nat) (next : NCode) (owned : CodeAt spec world kind next) :
    Edge spec completed world (.yielded world.state.refs.length world.state.deferreds.cells.length) kind
      (.onSuccessConst (.yieldNowWith priority) next) := by
  apply AnswerFlow.EmbeddedEdgeOver.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    apply AnswerFlow.saved_constant
    · intro nextWorld future value good
      exact code_rebase spec world kind next owned nextWorld future good.2.2.1.symm good.2.2.2.1.symm
    · intro nextWorld future cause good
      exact good
  · intro loop cursor same
    cases same
  · intro generator cursor same
    cases same

/-- The shared initialized source graph supplies every pure current head.
Stateful allocation heads are consumed by the actual native synchronous producer. -/
theorem head (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (completed : List (FiberId × ExitV)) (world : World) (kind : Kind) (program : NCode)
    (owned : CodeAt spec world kind program) (noSync : ∀ thunk, program ≠ .sync thunk) :
    AnswerFlow.HeadAt (model spec completed) (interpAt spec.root completed spec.table).toPrimInterp
      (Edge spec completed) world kind program := by
  cases owned with
  | success good => exact .success _ good
  | failure phase => exact .failure _ phase
  | initial stage => exact initial_head spec fragment completed world _ _ stage
  | allocating small stage => exact (noSync _ rfl).elim
  | gateAllocating stage => exact (noSync _ rfl).elim
  | stable ready held =>
    exact AnswerFlow.FamilyEmbedding.head_over (interpAt spec.root completed spec.table).toPrimInterp
      (embedding spec completed) (Semantic spec) (Typed.Edge spec.toSpec completed) world ready _ program
      (Typed.head spec.toSpec fragment completed _ program held)
  | frontier zero phase => exact .suspend _ (frontier_code spec completed world kind _ zero phase)
  | yielding phase refsEq deferredEq pending => exact .yieldNowWith _ (.yielding phase refsEq deferredEq pending)
  | bound first callback =>
    exact .onSuccess _ _ _ first (bound_edge spec completed world _ _ _ _ callback)
  | yieldThen phase held =>
    by_cases ready : Ready spec world
    · refine .onSuccessConst (Kind.stable Typed.Kind.root) _ _ (.stable ready rfl) ?_
      apply AnswerFlow.EmbeddedEdgeOver.saved
      refine ⟨?_, ?_, ?_⟩
      · intro view
        apply AnswerFlow.saved_constant
        · intro nextWorld future value good
          exact code_future_ready spec world kind _ held nextWorld future ready
        · intro nextWorld future cause good
          exact good
      · intro loop cursor same
        cases same
      · intro generator cursor same
        cases same

    · exact .onSuccessConst (Kind.yielded world.state.refs.length world.state.deferreds.cells.length) _ _
        (.yielding phase rfl rfl ready) (yield_edge spec completed world kind _ _ held)

/-- The actual closed source starts in the first initializer stage with no allocated cells. -/
theorem initial_code (spec : Spec) (state : Stores) (fuel : Nat) (tape : List Bool)
    (refs : state.refs.length = 0) (deferred : state.deferreds.cells.length = 0) :
    CodeAt spec ⟨⟨0⟩, state⟩ (.stable .root) (compileEff spec.root (rootPoint fuel tape)) := by
  have source : resolve spec.root (rootPoint fuel tape) = compileEff spec.root (rootPoint fuel tape) := rfl
  rw [← source]
  exact .initial ⟨Nat.zero_le _, rfl, rfl, rfl, refs, deferred, rfl⟩
end Effect4.Program.AnswerSlots.Initialized
