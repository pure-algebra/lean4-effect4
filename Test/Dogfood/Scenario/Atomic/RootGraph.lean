import Test.Dogfood.Scenario.Atomic.RootSource
import Test.Dogfood.Scenario.Atomic.DaemonGraph
import Effect4.Laws.Machine.AnswerFlowEmbedding
import Test.Dogfood.Scenario.Atomic.StageFresh
import Test.Dogfood.Scenario.Atomic.RootBindings
import Effect4.Laws.Machine.AnswerFlowViewsRefined
import Effect4.Laws.Program.AnswerSlots.Points

/-!
Concept: store-typing R4.
Consumer: the actual root role and its request-entry assignments in `Atomic.Store.shop_stages`.
The root retains exact source bindings and its next-fiber counter through native answers.
This annotation supplies no command or history producer by itself.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.RootGraph
open Effect4 Effect4.Machine Effect4.Program Effect4.Machine.AnswerFlow
open StageWorld

/-- Root answer classes carry either its next bound answer or one ignored scheduler pause. -/
def Owns : StageWorld.Kind → Prop
  | .ordinary | .rootAnswer _ | .rootPause _ => True
  | _ => False

/-- An actual root source point retains its immutable bindings, path and allocation counter. -/
def PointAt (root : NativeEff) (world : StageWorld.World) (point : Point) : Prop :=
  SourceScope.At root point ∧ RootBindings.PointAt point ∧
    3 ≤ point.env.length ∧ point.env.length ≤ 18 ∧ world.nextId = RootSlots.rank point.env.length

/-- Current root code distinguishes actual source entries, fork actions and ignored native answers. -/
inductive CodeAt (root : NativeEff) (table : RowTable) : StageWorld.World → StageWorld.Kind → NCode → Prop
  | ignored {world code} (held : DaemonGraph.CodeAt root table code) :
      CodeAt root table world .ordinary code
  | success {world kind value} (good : ValueAt world kind value) : CodeAt root table world kind (.success value)
  | failure {world kind cause} : CodeAt root table world kind (.failure cause)
  | entry {world point} (held : PointAt root world point) : CodeAt root table world .ordinary (resolve root point)
  | frontier {world kind point} (zero : point.fuel = 0) : CodeAt root table world kind (Effect4.Program.frontier point)
  | action {world point} (held : PointAt root world point) :
      CodeAt root table world (.rootAnswer point.env.length) (.withFiber (.act (point.child 0)))
  | await {world binder target} (counter : world.nextId = RootSlots.rank (binder + 1))
      (ignored : RootSlots.expected binder = none) :
      CodeAt root table world (.rootAnswer binder) (.suspend (.park (.join target .awaitValue)))
  | sleep {world binder millis} (counter : world.nextId = RootSlots.rank (binder + 1))
      (ignored : RootSlots.expected binder = none) :
      CodeAt root table world (.rootAnswer binder)
        (.async (.store (.registerSleep millis)) true (some (.store .cancelSleep)))
  | interrupting {world binder target who} (counter : world.nextId = RootSlots.rank (binder + 1))
      (ignored : RootSlots.expected binder = none) :
      CodeAt root table world (.rootAnswer binder) (.withFiber (.store (.act (.interruptAs target who))))
  | readReply {world kind} (cell : RefKey) (owned : Owns kind) (values : ∀ value, ValueAt world kind value) :
      CodeAt root table world kind (.sync (.store (.op (.refGet cell))))
  | read {world} : CodeAt root table world .ordinary (.sync (.op (.refGet ⟨0⟩)))
  | join {world counter} (target : FiberId) (mode : Supervision.ObserverMode)
      (captured : world.nextId = counter) :
      CodeAt root table world (.rootPause counter) (.suspend (.park (.join target mode)))
  | awaitAll {world counter} (targets : List FiberId) (captured : world.nextId = counter) :
      CodeAt root table world (.rootPause counter) (.suspend (.park (.awaitAll targets)))
  | pause {world priority} : CodeAt root table world (.rootPause world.nextId) (.yieldNowWith priority)
  | pausing {world kind priority next} (localKind : Owns kind) (held : CodeAt root table world kind next) :
      CodeAt root table world kind (.onSuccessConst (.yieldNowWith priority) next)
  | bound {world input output body name} (inputOwned : Owns input)
      (first : CodeAt root table world input body)
      (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
        ValueAt nextWorld input answer → CodeAt root table nextWorld output ((interpAt root view table).contA name answer))
      :
      CodeAt root table world output (.onSuccess body name)

/-- An ignored root body answer retains its allocation counter without constraining the value. -/
theorem ignored_answer (world : StageWorld.World) (binder : Nat) (value : Val)
    (counter : world.nextId = RootSlots.rank (binder + 1)) (ignored : RootSlots.expected binder = none) :
    ValueAt world (.rootAnswer binder) value := by
  refine ⟨counter, ?_⟩
  intro required impossible
  rw [ignored] at impossible
  cases impossible
/-- A root void reply marks an ignored answer endpoint, which accepts any awaited result. -/
theorem unit_value (world : StageWorld.World) (kind : StageWorld.Kind) (owns : Owns kind)
    (good : ValueAt world kind .unit) (value : Val) : ValueAt world kind value := by
  fun_cases Owns kind
  all_goals aesop (add norm simp [Owns, ValueAt]) (add safe apply [RootSlots.answer_of_unit])

/-- The root's delivered values depend on its counter and its immutable captured bindings. -/
theorem value_counter (before after : StageWorld.World) (counter : before.nextId = after.nextId)
    (kind : StageWorld.Kind) (owns : Owns kind) (value : Val) (good : ValueAt before kind value) :
    ValueAt after kind value := by
  cases kind
  all_goals dsimp only [Owns] at owns
  all_goals cases owns
  all_goals simp only [ValueAt, counter] at good ⊢
  all_goals exact good

/-- Actual source metadata survives a request write that preserves the root counter. -/
theorem point_counter (root : NativeEff) (before after : StageWorld.World)
    (counter : before.nextId = after.nextId) (point : Point) (held : PointAt root before point) :
    PointAt root after point :=
  ⟨held.1, held.2.1, held.2.2.1, held.2.2.2.1, counter.symm.trans held.2.2.2.2⟩

/-- Other request writes retain the whole actual root continuation at its unchanged counter. -/
theorem code_counter (root : NativeEff) (table : RowTable) (before : StageWorld.World)
    (kind : StageWorld.Kind) (code : NCode) (held : CodeAt root table before kind code) :
    ∀ after, Future before after → before.nextId = after.nextId → Owns kind →
      CodeAt root table after kind code := by
  induction held with
  | ignored code =>
    intro after future counter owns
    exact .ignored code
  | success good =>
    intro after future counter owns
    exact .success (value_counter _ after counter _ owns _ good)
  | failure =>
    intro after future counter owns
    exact .failure
  | entry point =>
    intro after future counter owns
    exact .entry (point_counter root _ after counter _ point)
  | frontier zero =>
    intro after future counter owns
    exact .frontier zero
  | action point =>
    intro after future counter owns
    exact .action (point_counter root _ after counter _ point)
  | await old ignored =>
    intro after future counter owns
    exact .await (counter.symm.trans old) ignored
  | sleep old ignored =>
    intro after future counter owns
    exact .sleep (counter.symm.trans old) ignored
  | interrupting old ignored =>
    intro after future counter owns
    exact .interrupting (counter.symm.trans old) ignored
  | readReply cell owned values =>
    intro after future counter owns
    exact .readReply cell owned (fun value => value_counter _ after counter _ owns value (values value))
  | read =>
    intro after future counter owns
    exact .read
  | join target mode captured =>
    intro after future counter owns
    exact .join target mode (counter.symm.trans captured)
  | awaitAll targets captured =>
    intro after future counter owns
    exact .awaitAll targets (counter.symm.trans captured)
  | pause =>
    intro after future counter owns
    rw [counter]
    exact .pause
  | pausing localKind first ih =>
    intro after future counter owns
    exact .pausing localKind (ih after future counter owns)
  | bound inputOwned first callback ihFirst ihCallback =>
    intro after future counter owns
    exact .bound inputOwned (ihFirst after future counter inputOwned)
      (fun later next view answer good => callback later (order.trans future next) view answer good)

/-- Await, sleep and interruption binders declare no stored handle answer. -/
theorem ignored_binder (binder : Nat) (late : 9 ≤ binder) (notFork : binder ≠ 15) :
    RootSlots.expected binder = none := by
  have low : ¬ binder < 3 := by omega
  have middle : ¬ binder < 9 := by omega
  simp only [RootSlots.expected, if_neg low, if_neg middle, if_neg notFork]

/-- The root's actual await operand names its already-bound request fiber. -/
theorem await_target (point : Point) (held : RootBindings.PointAt point) (slot : Nat)
    (source : (9 ≤ point.env.length ∧ point.env.length < 14 ∧ slot = point.env.length - 5) ∨
      (point.env.length = 16 ∧ slot = 15)) : ∃ target, point.env[slot]? = some (.fiber target) := by
  rcases source with early | late
  · have low : ¬ slot < 3 := by omega
    have high : slot < 9 := by omega
    refine ⟨⟨slot - 2⟩, held.1 slot _ ?_ (by omega)⟩
    simp only [RootSlots.expected, if_neg low, if_pos high]
  · obtain ⟨length, rfl⟩ := late
    exact ⟨⟨7⟩, held.1 15 _ rfl (by omega)⟩

/-- Exact root bindings supply the three immutable cells captured by every spawned request. -/
theorem cells (point : Point) (held : RootBindings.PointAt point) (enough : 3 ≤ point.env.length) :
    AnswerSlots.Prefix [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩] point.env := by
  unfold AnswerSlots.Prefix
  apply List.ext_getElem?
  intro index
  rw [List.getElem?_take]
  change (if index < 3 then point.env[index]? else none) =
    [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩][index]?
  by_cases small : index < 3
  · rw [if_pos small]
    have choices : index = 0 ∨ index = 1 ∨ index = 2 := by omega
    rcases choices with rfl | rfl | rfl
    · exact held.1 0 _ rfl (by omega)
    · exact held.1 1 _ rfl (by omega)
    · exact held.1 2 _ rfl (by omega)
  · rw [if_neg small]
    exact (List.getElem?_eq_none (by change 3 ≤ index; omega)).symm

/-- The actual fork body keeps its captured source level beneath the three generated child edges. -/
theorem fork_child_scope (root : NativeEff) (world : StageWorld.World) (point : Point)
    (body rest : NativeEff) (options : Supervision.ForkOptions) (held : PointAt root world point)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind (.withFiber (.fork body options)) rest))) :
    SourceScope.At root (((point.child 0).child 0).child 0) := by
  have source : SourceScope.levelAt (.eff root) 0 (point.path ++ [0, 0, 0]) = some point.env.length := by
    rw [SourceScope.levelAt_suffix _ _ point.path [0, 0, 0] 0 found, held.1]
    rfl
  simpa only [SourceScope.At, Point.child, List.append_assoc, List.cons_append, List.nil_append] using source

/-- A real root bind answer extends its exact handles and advances the actual source point. -/
theorem continuation (root : NativeEff) (table : RowTable) (before after : StageWorld.World)
    (point : Point) (first rest : NativeEff) (held : PointAt root before point)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind first rest)))
    (remaining : point.env.length < 18) (view : List (FiberId × ExitV)) (answer : Val)
    (good : ValueAt after (.rootAnswer point.env.length) answer) :
    CodeAt root table after .ordinary ((interpAt root view table).contA (.cont point) answer) := by
  let refreshed : Point := {point with completed := view}
  let next := refreshed.childWith 1 answer
  change CodeAt root table after .ordinary (resolve root next)
  apply CodeAt.entry
  have lower := held.2.2.1
  refine ⟨(SourceScope.bind_contA root refreshed first rest answer found held.1).2,
    RootBindings.childWith refreshed answer held.2.1 good.2, ?_, ?_, ?_⟩
  · change 3 ≤ (point.env ++ [answer]).length
    simp only [List.length_append, List.length_singleton]
    omega
  · change (point.env ++ [answer]).length ≤ 18
    simp only [List.length_append, List.length_singleton]
    omega
  · change after.nextId = RootSlots.rank (point.env ++ [answer]).length
    simpa only [List.length_append, List.length_singleton] using good.1

/-- Root failures carry no request observation, while successful bind answers retain exact handles. -/
def model (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    Model (ν := EffName) (σ := EffThunk) (β := Val) (ε := Err) (δ := Defect)
      (ι := FiberId) (α := Ann) StageWorld.World StageWorld.Kind where
  future := Future
  future_refl world := order.refl world
  future_trans _ _ _ one two := order.trans one two
  value := ValueAt
  cause := fun _ _ _ => True
  code := CodeAt root table
  finalizer := fun _ name exit => ((interpAt root view table).finalizerProgram name exit).map
    (finalizerCode (interpAt root view table) exit)
  success := fun _ _ _ held => .success held
  failure := fun _ _ _ _ => .failure

/-- Actual root saved frames retain their root-only endpoints and all completed-view callbacks. -/
structure Semantic (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (input output : StageWorld.Kind) (frame : NCode) : Prop where
  held : ViewSavedAt (model root table) (fun view => (interpAt root view table).toPrimInterp)
    world input output frame
  inputOwned : Owns input
  outputOwned : Owns output
  noScoped : ∀ body previous scope flag, frame ≠ .onExit body (.scopedExit previous scope) flag

/-- Root ignored code reuses the daemon's stable heap-preserving answer family. -/
theorem ignored_embedding (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    FamilyEmbedding (DaemonGraph.model root table view) (model root table view) id
      (fun (_ : Unit) => StageWorld.Kind.ordinary) (fun _ => True) where
  ready_future := fun _ _ _ held => held
  future := fun _ _ held _ => held
  value_read := fun _ _ _ _ _ => True.intro
  value_write := fun _ _ _ _ _ => True.intro
  cause_read := fun _ _ _ _ _ => True.intro
  cause_write := fun _ _ _ _ _ => True.intro
  code := fun _ _ _ _ held => .ignored held
  finalizer := fun _ _ _ _ => rfl

/-- The root's exact source callbacks coexist with its existing ignored native family. -/
def Edge (root : NativeEff) (table : RowTable) :=
  EmbeddedEdgeOver id (fun (_ : Unit) => StageWorld.Kind.ordinary) (fun (_ : StageWorld.World) => True)
    (Semantic root table) (DaemonGraph.Edge root table)

/-- The existing uniform saved-family theorem handles both actual root callback kinds. -/
theorem family (root : NativeEff) (table : RowTable) (view : List (FiberId × ExitV)) :
    SavedFamily (model root table view) (interpAt root view table).toPrimInterp (Edge root table) :=
  (ignored_embedding root table view).family_over (interpAt root view table).toPrimInterp
    (Semantic root table) (DaemonGraph.Edge root table)
    (ViewSavedAt.refined_family (model root table) (fun view => (interpAt root view table).toPrimInterp)
      (Semantic root table) (fun _ _ _ _ held => held.held) view)
    (DaemonGraph.family root table view)

/-- Generic root success wrappers reuse the same uniform callback contract. -/
theorem bound_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (input output : StageWorld.Kind) (body : NCode) (name : EffName)
    (inputOwned : Owns input) (outputOwned : Owns output)
    (callback : ∀ nextWorld, Future world nextWorld → ∀ view answer,
      ValueAt nextWorld input answer → CodeAt root table nextWorld output
        ((interpAt root view table).contA name answer)) :
    Edge root table world input output (.onSuccess body name) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨?_, ?_, ?_⟩, inputOwned, outputOwned, (by intro body previous scope flag equal; cases equal)⟩
  · intro view
    exact saved_success (model root table view) (interpAt root view table).toPrimInterp world input output body name
      (fun after future answer good => callback after future view answer good)
      (fun _ _ _ _ => True.intro)
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- A real root bind consumes its declared answer at the same future counter. -/
theorem cont_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (point : Point) (first rest : NativeEff) (held : PointAt root world point)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind first rest)))
    (remaining : point.env.length < 18) (body : NCode) :
    Edge root table world (.rootAnswer point.env.length) .ordinary (.onSuccess body (.cont point)) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨?_, ?_, ?_⟩, True.intro, True.intro, (by intro body previous scope flag equal; cases equal)⟩
  · intro view
    apply saved_success (model root table view) (interpAt root view table).toPrimInterp
    · intro after future answer good
      exact continuation root table world after point first rest held found remaining view answer good
    · intro after future cause good
      exact True.intro
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- Native interruptibility restoration keeps the same root answer class. -/
theorem mask_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : StageWorld.Kind) (owns : Owns kind) (flag : Bool) :
    Edge root table world kind kind (.setInterruptible flag) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨fun view => saved_mask (model root table view) (interpAt root view table).toPrimInterp world kind flag,
    ?_, ?_⟩, owns, owns, (by intro body previous scope flag equal; cases equal)⟩
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal

/-- An injected root pause ignores its value while retaining the counter of its real continuation. -/
theorem pause_edge (root : NativeEff) (table : RowTable) (world : StageWorld.World)
    (kind : StageWorld.Kind) (owns : Owns kind) (priority : Nat) (next : NCode)
    (held : CodeAt root table world kind next) :
    Edge root table world (.rootPause world.nextId) kind (.onSuccessConst (.yieldNowWith priority) next) := by
  apply EmbeddedEdgeOver.saved
  refine ⟨⟨?_, ?_, ?_⟩, True.intro, owns, (by intro body previous scope flag equal; cases equal)⟩
  · intro view
    apply saved_constant (model root table view) (interpAt root view table).toPrimInterp
    · intro after future value good
      exact code_counter root table world kind next held after future good.symm owns
    · intro after future cause good
      exact True.intro
  · intro name cursor equal
    cases equal
  · intro name cursor equal
    cases equal
end Test.Dogfood.Scenario.Atomic.RootGraph
