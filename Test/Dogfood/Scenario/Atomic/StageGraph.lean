import Test.Dogfood.Scenario.Atomic.StageSource
import Test.Dogfood.Scenario.Atomic.StageFinalizer
import Effect4.Laws.Machine.AnswerFlowViewsRefined
import Effect4.Laws.Machine.AnswerFlowEmbedding

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Consumer: the actual running request producer for `Atomic.Store.shop_stages`.
The annotation distinguishes the ignored pre-decision yield from its decision answer.
Saved callbacks quantify over actual answer classes and every completed-fiber view.
The source-entry and whole-command producers remain separate obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Current code retains the precise request stage required by its next actual operation. -/
inductive CodeAt (root : NativeEff) (table : RowTable) : StageWorld.World → StageWorld.Kind → NCode → Prop
  | success {world kind value} (good : ValueAt world kind value) : CodeAt root table world kind (.success value)
  | failure {world kind cause} (good : CauseAt world kind cause) : CodeAt root table world kind (.failure cause)
  | decision {world id env} (waiting : world.stages id = .waiting) :
      CodeAt root table world (.decision id) (.sync (.op (.refModify ⟨0⟩ (Store.decisionAt env.length) env)))
  | deposit {world id env} (admitted : world.stages id = .admitted) :
      CodeAt root table world (.deposit id) (.sync (.op (.refModify ⟨1⟩ (Store.depositAt id env.length) env)))
  | reading {world id} : CodeAt root table world (.seen id) (.sync (.op (.refGet ⟨0⟩)))
  | note {world id env used admitted rejected}
      (positive : world.stages id = .deposited → 1 ≤ admitted + rejected) :
      CodeAt root table world (.note id)
        (.sync (.op (.refUpdate ⟨2⟩ (Store.noteAt id (env.length + 1))
          (env ++ [Test.Dogfood.P4RateLimiter.windowVal used admitted rejected]))))
  | yielding {world id priority} (waiting : world.stages id = .waiting) :
      CodeAt root table world (.waiting id) (.yieldNowWith priority)
  | frontier {world kind point} (zero : point.fuel = 0) :
      CodeAt root table world kind (Effect4.Program.frontier point)
  | suspended {world kind thunk}
      (next : ∀ view, CodeAt root table world kind ((interpAt root view table).suspendBody thunk)) :
      CodeAt root table world kind (.suspend thunk)
  | bound {world input output body name} (first : CodeAt root table world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt nextWorld input answer → CodeAt root table nextWorld output
          ((interpAt root view table).contA name answer))
      (skip : ∀ nextWorld, Future world nextWorld → ∀ cause,
        CauseAt nextWorld input cause → CauseAt nextWorld output cause) :
      CodeAt root table world output (.onSuccess body name)

/-- The answer-flow model reads the same stage world used by actual primitive writes. -/
def model (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
      (ι := FiberId) (α := Ann) StageWorld.World StageWorld.Kind where
  future := Future
  future_refl world := order.refl world
  future_trans _ _ _ one two := order.trans one two
  value := ValueAt
  cause := CauseAt
  code := CodeAt root table
  finalizer := fun _ name exit => ((interpAt root view table).finalizerProgram name exit).map
    (finalizerCode (interpAt root view table) exit)
  success := fun _ _ _ held => .success held
  failure := fun _ _ _ held => .failure held

/-- Ordinary bind callbacks retain their semantic contract at every actual completed-fiber view. -/
def Semantic (root : NativeEff) (table : RowTable) :=
  ViewSavedAt (model root table) (fun view => (interpAt root view table).toPrimInterp)

/-- The request graph reuses the checked finalizer restore and merge family. -/
def Edge (root : NativeEff) (table : RowTable) :=
  EmbeddedEdgeOver id id (fun (_ : StageWorld.World) => True) (Semantic root table) StageFinalizer.Edge

/-- The same model embeds its existing finalizer family without changing its world or classes. -/
theorem embedding (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    FamilyEmbedding (model root table view) (model root table view) id id (fun _ => True) where
  ready_future := fun _ _ _ held => held
  future := fun _ _ held _ => held
  value_read := fun _ _ _ _ held => held
  value_write := fun _ _ _ _ held => held
  cause_read := fun _ _ _ _ held => held
  cause_write := fun _ _ _ _ held => held
  code := fun _ _ _ _ held => held
  finalizer := fun _ _ _ _ => rfl

/-- Native bind edges consume the actual answer class and preserve the separate failure class. -/
theorem bound_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (input output : StageWorld.Kind) (body : NCode) (name : EffName)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
      ValueAt nextWorld input answer → CodeAt root table nextWorld output ((interpAt root view table).contA name answer))
    (skip : ∀ nextWorld, Future world nextWorld → ∀ cause,
      CauseAt nextWorld input cause → CauseAt nextWorld output cause) :
    Edge root table world input output (.onSuccess body name) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨?_, ?_, ?_⟩
  · intro view
    exact saved_success (model root table view) (interpAt root view table).toPrimInterp world input output body name
      (fun nextWorld future answer good => callback nextWorld future view answer good) skip
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- The whole saved request suffix shares one actual recorded-cause admission. -/
theorem family (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    ContextualSavedFamily (model root table view) (interpAt root view table).toPrimInterp
      (Edge root table) StageFinalizer.Allowed := by
  exact (embedding root table view).contextual_family_over (interpAt root view table).toPrimInterp (Semantic root table) StageFinalizer.Edge
    StageFinalizer.Allowed StageFinalizer.Allowed (fun _ _ _ held => held)
    (SavedFamily.contextual (model root table view) (interpAt root view table).toPrimInterp
      (Semantic root table) StageFinalizer.Allowed
      (ViewSavedAt.family (model root table) (fun view => (interpAt root view table).toPrimInterp) view))
    (StageFinalizer.family (model root table view) rfl rfl rfl root table view)

/-- Exact source resolution supplies the decision code with its actual waiting premise. -/
theorem decision_source (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (fuel : Nat)
    (path : point.path = StageSource.decisionPath id) (amount : point.fuel = fuel + 1)
    (sourceOwned : SourceScope.At built.program point) (captured : point.env[0]? = some (.cell ⟨0⟩))
    (world : StageWorld.World) (waiting : world.stages id = .waiting) :
    CodeAt built.program built.table world (.decision id) (resolve built.program point) := by
  rw [StageSource.resolve_decision built accepted id member point fuel path amount sourceOwned captured]
  exact .decision waiting

/-- The actual admitted branch supplies precisely its own deposited identity. -/
theorem deposit_source (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (fuel : Nat)
    (path : point.path = StageSource.depositPath id) (amount : point.fuel = fuel + 1)
    (sourceOwned : SourceScope.At built.program point) (captured : point.env[1]? = some (.cell ⟨1⟩))
    (world : StageWorld.World) (admitted : world.stages id = .admitted) :
    CodeAt built.program built.table world (.deposit id) (resolve built.program point) := by
  rw [StageSource.resolve_deposit built accepted id member point fuel path amount sourceOwned captured]
  exact .deposit admitted

/-- An actual stage-sensitive synchronous head chooses its new world and returned class together.
The window, account and cleanup premises come from the coupled numeric heap invariant. -/
theorem sync_answer (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : StageWorld.Kind) (operation : SyncOp) (owned : CodeAt root table world kind (.sync (.op operation)))
    (state : Stores) (used admitted rejected : Nat) (ids : List Nat) (log : List Val)
    (window : refPeek state.refs ⟨0⟩ = some (Test.Dogfood.P4RateLimiter.windowVal used admitted rejected))
    (account : refPeek state.refs ⟨1⟩ = some (Store.Writes.account ids))
    (cleanups : refPeek state.refs ⟨2⟩ = some (.list log))
    (positive : ∀ id, world.stages id = .deposited → 1 ≤ admitted + rejected) :
    ∃ nextWorld after answer, syncOpStep operation state = some (after, answer) ∧
      Future world nextWorld ∧ ValueAt nextWorld kind answer := by
  cases owned with
  | decision waiting =>
    obtain ⟨after, answer, actual, future, good⟩ := StageWorld.decision world _ waiting state _ used admitted rejected window
    exact ⟨_, after, answer, actual, future, good⟩
  | deposit good =>
    obtain ⟨after, answer, actual, future, value⟩ := StageWorld.deposit world _ good state _ ids account
    exact ⟨_, after, answer, actual, future, value⟩
  | reading =>
    refine ⟨world, state, Test.Dogfood.P4RateLimiter.windowVal used admitted rejected, ?_, order.refl world,
      used, admitted, rejected, rfl, positive _⟩
    change (refStep (.refGet ⟨0⟩) state.refs).map (fun step => ({state with refs := step.2}, step.1)) = _
    simp only [refStep, window, Option.map_some]
  | note good =>
    obtain ⟨after, actual, future, value⟩ := StageWorld.note world _ state _ _ _ _ log good cleanups
    exact ⟨_, after, .unit, actual, future, value⟩

end Test.Dogfood.Scenario.Atomic.StageGraph
