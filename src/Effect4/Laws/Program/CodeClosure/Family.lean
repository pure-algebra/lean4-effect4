import Effect4.Laws.Program.CodeClosure.Predicate
import Effect4.Laws.Program.AnswerSlots.Stable

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: one saved-frame and head producer for generated code annotations.
Consumers: the direct source annotation and unrestricted finalizer source accounting.
Reach: supplied leaf predicates and their actual interpreter callback closure.
The producer adds no source representation, initialization, or history premise.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Family
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.AnswerSlots

/-- A recursive result retains the source annotation of its actual body. -/
def LoopResult (names successNames : EffName → Prop) (thunks : EffThunk → Prop) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => RoleCode names successNames thunks body

/-- An iterator retains both its yielded body and actual continuation. -/
def IterResult (names successNames : EffName → Prop) (thunks : EffThunk → Prop) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Prop
  | .resume body next => RoleCode names successNames thunks body ∧ names next
  | _ => True

/-- The actual interpreter callbacks consume and produce the supplied leaf annotation. -/
structure Hooks (root : NativeEff) (table : RowTable)
    (names successNames : EffName → Prop) (thunks : EffThunk → Prop) : Prop where
  value : ∀ view name value, successNames name → RoleCode names successNames thunks ((interpAt root view table).contA name value)
  bothValue : ∀ view name value, names name → RoleCode names successNames thunks ((interpAt root view table).contA name value)
  cause : ∀ view name cause, names name → RoleCode names successNames thunks ((interpAt root view table).contE name cause)
  suspend : ∀ view thunk, thunks thunk → RoleCode names successNames thunks ((interpAt root view table).suspendBody thunk)
  iterator : ∀ view name value, names name → IterResult names successNames thunks (((interpAt root view table).iterNext name value).2)
  loopEnter : ∀ view name cursor, names name → LoopResult names successNames thunks ((interpAt root view table).loopEnter name cursor)
  loopResume : ∀ view name cursor answer, names name → LoopResult names successNames thunks ((interpAt root view table).loopResume name cursor answer)
  cancel : ∀ view name cause, RoleCode names successNames thunks ((interpAt root view table).cancelThenFail name cause)
  finalizer : ∀ view name exit body, names name →
    (interpAt root view table).finalizerProgram name exit = some body → RoleCode names successNames thunks body
  restore : ∀ view exit body, RoleCode names successNames thunks body → RoleCode names successNames thunks (finalizerCode (interpAt root view table) exit body)

/-- The broad stable class retains the supplied callback roles and admits every answer. -/
def sourceSpec (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop) : StableSpec where
  root := root
  table := table
  Kind := Unit
  rootKind := ()
  value _ _ := True
  code _ := RoleCode names successNames thunks
  success _ _ _ := trivial
  failure _ _ := trivial

/-- Every exit representation contains no delayed source environment. -/
theorem source_ofExit (names successNames : EffName → Prop) (thunks : EffThunk → Prop) (exit : ExitV) : RoleCode names successNames thunks (Prim.ofExit exit) := by
  cases exit <;> trivial

/-- Actual value callbacks retain the current code and every pushed binding certificate. -/
theorem source_armA (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) (view)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : RoleCode names successNames thunks frame)
    (actual : frame.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    RoleCode names successNames thunks next ∧ ∀ code ∈ pushed, RoleCode names successNames thunks code := by
  fun_cases Prim.armA (interpAt root view table).toPrimInterp frame value provided
  case case3 body onValue onCause =>
    have closed := hooks.bothValue view onValue value owned.2.1
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [Prim.armA])
  case case10 generator cursor body next selected =>
    have closed := hooks.iterator view generator value owned
    rw [selected] at closed
    aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [Prim.armA, IterResult])
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [Prim.armA, LoopResult]) (add safe apply [source_ofExit, hooks.value]) (add safe forward [hooks.loopResume])


/-- Actual cause callbacks retain the current code and every pushed binding certificate. -/
theorem source_armE (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) (view)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : RoleCode names successNames thunks frame)
    (actual : frame.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    RoleCode names successNames thunks next ∧ ∀ code ∈ pushed, RoleCode names successNames thunks code := by
  fun_cases Prim.armE (interpAt root view table).toPrimInterp frame cause provided
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [Prim.armE]) (add safe apply [source_ofExit, hooks.cause, hooks.cancel])

/-- The same binding certificate annotates saved code at every completed-fiber view. -/
def sourceEdge (names successNames : EffName → Prop) (thunks : EffThunk → Prop) (_ : Unit) (_ _ : Unit) : NCode → Prop := RoleCode names successNames thunks

/-- An actual saved suffix composes the same immutable binding certificate. -/
theorem source_path (names successNames : EffName → Prop) (thunks : EffThunk → Prop) (frames : List NCode)
    (owned : ∀ code ∈ frames, RoleCode names successNames thunks code) :
    Contracts.Path (sourceEdge names successNames thunks ()) () () frames := by
  induction frames with
  | nil => exact .nil ()
  | cons frame rest ih =>
    exact .cons (owned frame (.head _)) (ih (fun code member => owned code (.tail _ member)))

/-- Reading an actual saved path recovers every frame's supplied source annotation. -/
theorem source_path_owned (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    {input output : Unit} {frames : List NCode}
    (path : Contracts.Path (sourceEdge names successNames thunks ()) input output frames) :
    ∀ code ∈ frames, RoleCode names successNames thunks code := by
  induction path with
  | nil kind => intro code member; cases member
  | cons head tail ih =>
    intro code member
    rcases List.mem_cons.mp member with same | rest
    · rw [same]; exact head
    · exact ih code rest

/-- Every actual callback view supplies the common saved-frame obligations. -/
theorem source_family (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) (view) :
    AnswerFlow.SavedFamily ((sourceSpec root table names successNames thunks).model view)
      (interpAt root view table).toPrimInterp (sourceEdge names successNames thunks) := by
  constructor
  · intros; trivial
  · intros; trivial
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := source_armA root table names successNames thunks hooks view frame value provided next pushed held actual
    cases output
    exact ⟨(), code, source_path names successNames thunks pushed stack⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := source_armE root table names successNames thunks hooks view frame cause provided next pushed held actual
    cases output
    exact ⟨(), code, source_path names successNames thunks pushed stack⟩
  · intro world input output frame held nextWorld future exit next good installed
    cases frame
    case onExit body name flag =>
      change Option.map (finalizerCode (interpAt root view table) exit)
        ((interpAt root view table).finalizerProgram name exit) = some next at installed
      obtain ⟨program, found, equal⟩ := Option.map_eq_some_iff.mp installed
      rw [← equal]
      exact hooks.restore view exit program (hooks.finalizer view name exit program held.2 found)
    all_goals cases installed
  · intros; trivial

/-- Every permitted current head consumes the same stable binding class. -/
theorem source_head (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) (view) (code : NCode) (owned : RoleCode names successNames thunks code) :
    AnswerFlow.HeadAt ((sourceSpec root table names successNames thunks).model view)
      (interpAt root view table).toPrimInterp (sourceEdge names successNames thunks) () () code := by
  cases code
  case success value => exact .success value trivial
  case failure cause => exact .failure cause trivial
  case sync thunk => exact .sync thunk trivial
  case suspend thunk => exact .suspend thunk (hooks.suspend view thunk owned)
  case withFiber thunk => exact .withFiber thunk (hooks.suspend view thunk owned)
  case yieldableError error => exact .yieldableError error trivial
  case iterator name cursor =>
    refine .iterator name cursor owned ?_
    intro next pushed actual
    obtain ⟨code, slots⟩ := source_armA root table names successNames thunks hooks view _ cursor none next pushed owned actual
    exact ⟨(), code, source_path names successNames thunks pushed slots⟩
  case whileLoop name cursor =>
    have slots := hooks.loopEnter view name cursor owned
    refine .whileLoop name cursor ?_ ?_
    · intro next body actual
      rw [actual] at slots
      exact ⟨(), slots, .cons owned (.nil ())⟩
    · intro body actual
      rw [actual] at slots
      exact ⟨(), slots, .nil ()⟩
  case onSuccess body name => exact .onSuccess () body name owned.1 owned
  case onSuccessConst body next => exact .onSuccessConst () body next owned.1 owned
  case onFailure body name => exact .onFailure () body name owned.1 owned
  case onSuccessAndFailure body success failure => exact .onSuccessAndFailure () body success failure owned.1 owned
  case exitFrame body => exact .exitFrame () body owned owned
  case onExit body name flag => exact .onExit () body name flag owned.1 owned
  case yieldNowWith priority => exact .yieldNowWith priority owned
  case async register signal cancel => exact .async register signal cancel owned
  case setInterruptible flag => exact .setInterruptible flag trivial
  case asyncFinalizer name => exact .asyncFinalizer name trivial

/-- The existing stable interface accepts the shared point annotation at every actual view. -/
def sourceLaws (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) : StableLaws (sourceSpec root table names successNames thunks) where
  Edge := sourceEdge names successNames thunks
  family := source_family root table names successNames thunks hooks
  head view kind code owned := by
    cases kind
    exact source_head root table names successNames thunks hooks view code owned

/-- The shared value pop retains the source annotation of its selected callback.
Consumer: selected-source frame accounting. -/
theorem value_selected (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop)
    (thunks : EffThunk → Prop) (hooks : Hooks root table names successNames thunks) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (value : Val) (selected : NCode)
    (stack : ∀ frame ∈ fiber.stack, RoleCode names successNames thunks frame)
    (found : (fiber.getCont .contA false).answer = .frame selected) :
    RoleCode names successNames thunks selected := by
  obtain ⟨incoming, middle, good, owned, suffix⟩ :=
    AnswerFlow.External.getCont_value_selected
      ((sourceSpec root table names successNames thunks).model view)
      (interpAt root view table).toPrimInterp (sourceEdge names successNames thunks)
      (source_family root table names successNames thunks hooks view) (fun _ _ => trivial)
      () () () fiber value selected True.intro (source_path names successNames thunks fiber.stack stack) found
  exact owned

/-- The shared cause pop retains the annotation after restoring masks combine interruptions.
Consumer: selected-source frame accounting. -/
theorem cause_selected (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop)
    (thunks : EffThunk → Prop) (hooks : Hooks root table names successNames thunks) (view : List (FiberId × ExitV))
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (cause : CauseV) (selected : NCode)
    (stack : ∀ frame ∈ fiber.stack, RoleCode names successNames thunks frame)
    (found : (fiber.getCont .contE true (some cause)).answer = .frame selected) :
    RoleCode names successNames thunks selected := by
  obtain ⟨incoming, middle, delivered, carried, good, owned, suffix⟩ :=
    AnswerFlow.External.getCont_cause_selected
      ((sourceSpec root table names successNames thunks).model view)
      (interpAt root view table).toPrimInterp (sourceEdge names successNames thunks)
      (source_family root table names successNames thunks hooks view) (fun _ _ => trivial)
      () () () fiber cause selected True.intro (fun _ _ _ _ _ => trivial)
      (source_path names successNames thunks fiber.stack stack) found
  exact owned

end Effect4.Program.CodeClosure.Family
