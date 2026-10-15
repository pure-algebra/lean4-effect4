import Test.Dogfood.Scenario.Atomic.StageSource
import Test.Dogfood.Scenario.Atomic.StageFinalizer
import Effect4.Laws.Machine.AnswerFlowViewsRefined
import Effect4.Laws.Machine.AnswerFlowEmbedding
import Effect4.Laws.Machine.AnswerFlowHooks

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

/-- Request answer classes name the same owner as the current source role. -/
def Owns (owner : Nat) : StageWorld.Kind → Prop
  | .waiting id | .seen id | .decision id | .deposit id | .body id | .finalized id | .note id | .cleanup id => owner = id
  | .ordinary | .rootAnswer _ | .rootPause _ => False
  | .paused id incoming _ _ => owner = id ∧ Owns owner incoming

/-- A failed body installs its merge wrapper; a successful body restores after cleanup directly. -/
def FinalizerKind (owner : Nat) : ExitV → StageWorld.Kind
  | .success _ => .cleanup owner
  | .failure _ => .note owner

/-- Current code retains the precise request stage required by its next actual operation. -/
inductive CodeAt (root : NativeEff) (table : RowTable) (owner : Nat) : StageWorld.World → StageWorld.Kind → NCode → Prop
  | success {world kind value} (good : ValueAt world kind value) : CodeAt root table owner world kind (.success value)
  | failure {world kind cause} (good : CauseAt world kind cause) : CodeAt root table owner world kind (.failure cause)
  | decision {world env} (waiting : world.stages owner = .waiting) :
      CodeAt root table owner world (.decision owner) (.sync (.op (.refModify ⟨0⟩ (Store.decisionAt env.length) env)))
  | deposit {world env} (admitted : world.stages owner = .admitted) :
      CodeAt root table owner world (.deposit owner) (.sync (.op (.refModify ⟨1⟩ (Store.depositAt owner env.length) env)))
  | reading {world} : CodeAt root table owner world (.seen owner) (.sync (.op (.refGet ⟨0⟩)))
  | note {world env used admitted rejected}
      (positive : world.stages owner = .deposited → 1 ≤ admitted + rejected) :
      CodeAt root table owner world (.note owner)
        (.sync (.op (.refUpdate ⟨2⟩ (Store.noteAt owner (env.length + 1))
          (env ++ [Test.Dogfood.P4RateLimiter.windowVal used admitted rejected]))))
  | yielding {world priority} (waiting : world.stages owner = .waiting) :
      CodeAt root table owner world (.waiting owner) (.yieldNowWith priority)
  | pause {world kind priority} (owns : Owns owner kind) :
      CodeAt root table owner world (.paused owner kind (world.stages owner) (world.cleaned owner)) (.yieldNowWith priority)
  | pausing {world kind priority next} (owns : Owns owner kind)
      (held : CodeAt root table owner world kind next) :
      CodeAt root table owner world kind (.onSuccessConst (.yieldNowWith priority) next)
  | frontier {world kind point} (zero : point.fuel = 0) :
      CodeAt root table owner world kind (Effect4.Program.frontier point)
  | suspended {world kind thunk}
      (next : ∀ view, CodeAt root table owner world kind ((interpAt root view table).suspendBody thunk)) :
      CodeAt root table owner world kind (.suspend thunk)
  | guardedExit {world body point} (first : CodeAt root table owner world (.body owner) body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view exit,
        StageFinalizer.BodyExit nextWorld owner exit →
        CodeAt root table owner nextWorld (FinalizerKind owner exit)
          (resolve root (({point with completed := view} : Point).childWith 1 (reifyExitVal exit)))) :
      CodeAt root table owner world (.finalized owner) (.onExit body (.fin point) false)
  | restoring {world body exit} (captured : StageFinalizer.BodyExit world owner exit)
      (first : CodeAt root table owner world (.cleanup owner) body) :
      CodeAt root table owner world (.finalized owner) (.onSuccess body (.restore exit))
  | merging {world body exit} (captured : StageFinalizer.BodyExit world owner exit)
      (first : CodeAt root table owner world (.note owner) body) :
      CodeAt root table owner world (.cleanup owner) (.onFailure body (.merge exit))
  | bound {world input output body name} (localInput : Owns owner input) (first : CodeAt root table owner world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt nextWorld input answer → CodeAt root table owner nextWorld output
          ((interpAt root view table).contA name answer))
      (skip : ∀ nextWorld, Future world nextWorld → ∀ cause,
        CauseAt nextWorld input cause → CauseAt nextWorld output cause) :
      CodeAt root table owner world output (.onSuccess body name)

/-- A different request's write leaves this owner's delivered value class unchanged. -/
theorem value_other (owner : Nat) (kind : StageWorld.Kind) (owns : Owns owner kind)
    (before after : StageWorld.World) (stage : before.stages owner = after.stages owner)
    (cleaned : before.cleaned owner = after.cleaned owner) (value : Val) (good : ValueAt before kind value) :
    ValueAt after kind value := by
  cases kind with
  | paused id incoming savedStage savedCleaned =>
    obtain ⟨rfl, localKind⟩ := owns
    exact ⟨stage.symm.trans good.1, cleaned.symm.trans good.2⟩
  | _ =>
    all_goals dsimp only [Owns] at owns
    all_goals cases owns
    all_goals cases value
    all_goals simp only [ValueAt, stage, cleaned] at good ⊢
    all_goals exact good

/-- Unaffected request causes retain both deposit and positive cleanup evidence. -/
theorem cause_other (owner : Nat) (kind : StageWorld.Kind) (owns : Owns owner kind)
    (before after : StageWorld.World) (stage : before.stages owner = after.stages owner)
    (cleaned : before.cleaned owner = after.cleaned owner) (cause : CauseV) (good : CauseAt before kind cause) :
    CauseAt after kind cause := by
  induction kind with
  | paused id incoming savedStage savedCleaned ih =>
    obtain ⟨rfl, localKind⟩ := owns
    exact ⟨stage.symm.trans good.1, cleaned.symm.trans good.2.1, ih localKind good.2.2⟩
  | _ =>
    all_goals dsimp only [Owns] at owns
    all_goals cases owns
    all_goals simpa only [CauseAt, stage, cleaned] using good

/-- Actual nonacting request code reads only its owner's unchanged stage and cleanup facts. -/
theorem code_other (root : NativeEff) (table : RowTable) (owner : Nat)
    (before : StageWorld.World) (kind : StageWorld.Kind) (code : NCode)
    (owned : CodeAt root table owner before kind code) :
    ∀ after, Future before after → before.stages owner = after.stages owner →
      before.cleaned owner = after.cleaned owner → Owns owner kind → CodeAt root table owner after kind code := by
  induction owned with
  | success good =>
    intro after future stage cleaned owns
    exact .success (value_other owner _ owns _ after stage cleaned _ good)
  | failure good =>
    intro after future stage cleaned owns
    exact .failure (cause_other owner _ owns _ after stage cleaned _ good)
  | decision waiting =>
    intro after future stage cleaned owns
    exact .decision (stage ▸ waiting)
  | deposit admitted =>
    intro after future stage cleaned owns
    exact .deposit (stage ▸ admitted)
  | reading =>
    intro after future stage cleaned owns
    exact .reading
  | note positive =>
    intro after future stage cleaned owns
    exact .note (fun deposited => positive (stage.symm ▸ deposited))
  | yielding waiting =>
    intro after future stage cleaned owns
    exact .yielding (stage ▸ waiting)
  | pause localKind =>
    intro after future stage cleaned owns
    rw [stage, cleaned]
    exact .pause localKind
  | pausing localKind held ih =>
    intro after future stage cleaned owns
    exact .pausing localKind (ih after future stage cleaned owns)
  | frontier zero =>
    intro after future stage cleaned owns
    exact .frontier zero
  | suspended next ih =>
    intro after future stage cleaned owns
    exact .suspended (fun view => ih view after future stage cleaned owns)
  | guardedExit first callback ihFirst ihCallback =>
    intro after future stage cleaned owns
    exact .guardedExit (ihFirst after future stage cleaned rfl)
      (fun later next view exit good => callback later (order.trans future next) view exit good)
  | restoring captured first ih =>
    intro after future stage cleaned owns
    exact .restoring (StageFinalizer.body_exit_future _ after future owner _ captured)
      (ih after future stage cleaned rfl)
  | merging captured first ih =>
    intro after future stage cleaned owns
    exact .merging (StageFinalizer.body_exit_future _ after future owner _ captured)
      (ih after future stage cleaned rfl)
  | bound localInput first callback skip ihFirst ihCallback =>
    intro after future stage cleaned owns
    exact .bound localInput (ihFirst after future stage cleaned localInput)
      (fun later next view answer good => callback later (order.trans future next) view answer good)
      (fun later next cause good => skip later (order.trans future next) cause good)

/-- The answer-flow model reads the same stage world used by actual primitive writes. -/
def model (root : NativeEff) (table : RowTable) (owner : Nat) (view : List (FiberId × ExitV)) :
    Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
      (ι := FiberId) (α := Ann) StageWorld.World StageWorld.Kind where
  future := Future
  future_refl world := order.refl world
  future_trans _ _ _ one two := order.trans one two
  value := ValueAt
  cause := CauseAt
  code := CodeAt root table owner
  finalizer := fun _ name exit => ((interpAt root view table).finalizerProgram name exit).map
    (finalizerCode (interpAt root view table) exit)
  success := fun _ _ _ held => .success held
  failure := fun _ _ _ held => .failure held

/-- Ordinary bind callbacks retain their semantic contract at every actual completed-fiber view. -/
structure Semantic (root : NativeEff) (table : RowTable) (owner : Nat)
    (world : StageWorld.World) (input output : StageWorld.Kind) (frame : NCode) : Prop where
  held : ViewSavedAt (model root table owner) (fun view => (interpAt root view table).toPrimInterp)
    world input output frame
  inputOwned : Owns owner input
  outputOwned : Owns owner output

/-- The request graph reuses the checked finalizer restore and merge family. -/
def Edge (root : NativeEff) (table : RowTable) (owner : Nat) :=
  EmbeddedEdgeOver id id (fun (_ : StageWorld.World) => True) (Semantic root table owner) (StageFinalizer.Edge owner)

/-- The same model embeds its existing finalizer family without changing its world or classes. -/
theorem embedding (root : NativeEff) (table : RowTable) (owner : Nat) (view : List (FiberId × ExitV)) :
    FamilyEmbedding (model root table owner view) (model root table owner view) id id (fun _ => True) where
  ready_future := fun _ _ _ held => held
  future := fun _ _ held _ => held
  value_read := fun _ _ _ _ held => held
  value_write := fun _ _ _ _ held => held
  cause_read := fun _ _ _ _ held => held
  cause_write := fun _ _ _ _ held => held
  code := fun _ _ _ _ held => held
  finalizer := fun _ _ _ _ => rfl

/-- Actual native finalizer wrapping uses the captured body exit and the completed cleanup class. -/
theorem finalizer_code (root : NativeEff) (table : RowTable) (owner : Nat)
    (view : List (FiberId × ExitV)) (world : StageWorld.World) (exit : ExitV) (program : NCode)
    (captured : StageFinalizer.BodyExit world owner exit)
    (good : CodeAt root table owner world (FinalizerKind owner exit) program) :
    CodeAt root table owner world (.finalized owner) (finalizerCode (interpAt root view table) exit program) := by
  cases exit with
  | success value => exact .restoring captured good
  | failure cause => exact .restoring captured (.merging captured good)

/-- Actual restoring mask frames use the shared identity answer contract. -/
theorem mask_edge (root : NativeEff) (table : RowTable) (owner : Nat)
    (world : StageWorld.World) (kind : StageWorld.Kind) (flag : Bool) (owns : Owns owner kind) :
    Edge root table owner world kind kind (.setInterruptible flag) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨fun view => saved_mask (model root table owner view) (interpAt root view table).toPrimInterp world kind flag,
    ?_, ?_⟩, owns, owns⟩
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- Native bind edges consume the actual answer class and preserve the separate failure class. -/
theorem bound_edge (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (input output : StageWorld.Kind) (body : NCode) (name : EffName)
    (inputOwned : Owns owner input) (outputOwned : Owns owner output)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
      ValueAt nextWorld input answer → CodeAt root table owner nextWorld output ((interpAt root view table).contA name answer))
    (skip : ∀ nextWorld, Future world nextWorld → ∀ cause,
      CauseAt nextWorld input cause → CauseAt nextWorld output cause) :
    Edge root table owner world input output (.onSuccess body name) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨?_, ?_, ?_⟩, inputOwned, outputOwned⟩
  · intro view
    exact saved_success (model root table owner view) (interpAt root view table).toPrimInterp world input output body name
      (fun nextWorld future answer good => callback nextWorld future view answer good) skip
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- A scheduler pause ignores its returned value while retaining this owner's actual phase.
The saved failure arm retains the original incoming cause class. -/
theorem pause_edge (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (kind : StageWorld.Kind) (priority : Nat) (next : NCode) (owns : Owns owner kind)
    (held : CodeAt root table owner world kind next) :
    Edge root table owner world (.paused owner kind (world.stages owner) (world.cleaned owner)) kind
      (.onSuccessConst (.yieldNowWith priority) next) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨?_, ?_, ?_⟩, ⟨rfl, owns⟩, owns⟩
  · intro view
    apply saved_constant (model root table owner view) (interpAt root view table).toPrimInterp
    · intro after future answer good
      exact code_other root table owner world kind next held after future good.1.symm good.2.symm owns
    · intro after future cause good
      exact good.2.2
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- The whole saved request suffix shares one actual recorded-cause admission. -/
theorem family (root : NativeEff) (table : RowTable) (owner : Nat) (view : List (FiberId × ExitV)) :
    ContextualSavedFamily (model root table owner view) (interpAt root view table).toPrimInterp
      (Edge root table owner) StageFinalizer.Allowed := by
  exact (embedding root table owner view).contextual_family_over (interpAt root view table).toPrimInterp (Semantic root table owner) (StageFinalizer.Edge owner)
    StageFinalizer.Allowed StageFinalizer.Allowed (fun _ _ _ held => held)
    (SavedFamily.contextual (model root table owner view) (interpAt root view table).toPrimInterp
      (Semantic root table owner) StageFinalizer.Allowed
      (ViewSavedAt.refined_family (model root table owner) (fun view => (interpAt root view table).toPrimInterp)
        (Semantic root table owner) (fun _ _ _ _ held => held.held) view))
    (StageFinalizer.family (model root table owner view) rfl rfl rfl owner root table view)

/-- Exact source resolution supplies the decision code with its actual waiting premise. -/
theorem decision_source (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (fuel : Nat)
    (path : point.path = StageSource.decisionPath id) (amount : point.fuel = fuel + 1)
    (sourceOwned : SourceScope.At built.program point) (captured : point.env[0]? = some (.cell ⟨0⟩))
    (world : StageWorld.World) (waiting : world.stages id = .waiting) :
    CodeAt built.program built.table id world (.decision id) (resolve built.program point) := by
  rw [StageSource.resolve_decision built accepted id member point fuel path amount sourceOwned captured]
  exact .decision waiting

/-- The actual admitted branch supplies precisely its own deposited identity. -/
theorem deposit_source (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (fuel : Nat)
    (path : point.path = StageSource.depositPath id) (amount : point.fuel = fuel + 1)
    (sourceOwned : SourceScope.At built.program point) (captured : point.env[1]? = some (.cell ⟨1⟩))
    (world : StageWorld.World) (admitted : world.stages id = .admitted) :
    CodeAt built.program built.table id world (.deposit id) (resolve built.program point) := by
  rw [StageSource.resolve_deposit built accepted id member point fuel path amount sourceOwned captured]
  exact .deposit admitted

/-- An actual stage-sensitive synchronous head chooses its new world and returned class together.
The window, account and cleanup premises come from the coupled numeric heap invariant. -/
theorem sync_answer (root : NativeEff) (table : RowTable) (owner : Nat) (world : StageWorld.World)
    (kind : StageWorld.Kind) (operation : SyncOp) (owned : CodeAt root table owner world kind (.sync (.op operation)))
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
