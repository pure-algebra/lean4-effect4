import Effect4.Laws.Program.CodeClosure.Predicate
import Effect4.Laws.Program.CodeClosure.PredicateFamily

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

/-- The leaf annotation supplies the generic constructor-aware callback contract. -/
theorem predicateRules (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop)
    (thunks : EffThunk → Prop) (hooks : Hooks root table names successNames thunks) :
    PredicateFamily.Rules root table (RoleCode names successNames thunks) where
  success := fun _ => trivial
  failure := fun _ => trivial
  mask := fun _ => trivial
  children := by
    intro code held
    cases code
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [PredicateFamily.Children])
  suspend := by
    intro view thunk held
    rcases held with held | held
    all_goals exact hooks.suspend view thunk held
  value := source_armA root table names successNames thunks hooks
  cause := source_armE root table names successNames thunks hooks
  loopContinue := by
    intro view callback cursor next body held found
    have supplied := hooks.loopEnter view callback cursor held
    rw [found] at supplied
    exact ⟨supplied, held⟩
  loopFinish := by
    intro view callback cursor body held found
    have supplied := hooks.loopEnter view callback cursor held
    rw [found] at supplied
    exact supplied
  finalizer := by
    intro view frame exit next held installed
    cases frame
    case onExit body name flag =>
      obtain ⟨program, found, equal⟩ := Option.map_eq_some_iff.mp installed
      rw [← equal]
      exact hooks.restore view exit program (hooks.finalizer view name exit program held.2 found)
    all_goals cases installed

/-- Every actual callback view supplies the common saved-frame obligations. -/
theorem source_family (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) (view) :
    AnswerFlow.SavedFamily ((sourceSpec root table names successNames thunks).model view)
      (interpAt root view table).toPrimInterp (sourceEdge names successNames thunks) :=
  PredicateFamily.family root table (RoleCode names successNames thunks)
    (predicateRules root table names successNames thunks hooks) view

/-- Every permitted current head consumes the same stable binding class. -/
theorem source_head (root : NativeEff) (table : RowTable) (names successNames : EffName → Prop) (thunks : EffThunk → Prop)
    (hooks : Hooks root table names successNames thunks) (view) (code : NCode) (owned : RoleCode names successNames thunks code) :
    AnswerFlow.HeadAt ((sourceSpec root table names successNames thunks).model view)
      (interpAt root view table).toPrimInterp (sourceEdge names successNames thunks) () () code :=
  PredicateFamily.head root table (RoleCode names successNames thunks)
    (predicateRules root table names successNames thunks hooks) view code owned

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
