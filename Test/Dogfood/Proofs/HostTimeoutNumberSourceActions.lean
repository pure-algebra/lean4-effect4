import Test.Dogfood.Proofs.HostTimeoutNumberSourceSlots
import Effect4.Laws.Program.CodeClosure.Qualified.Stable
import Effect4.Laws.Program.CodeClosure.PredicateFamily

/-!
Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: pending attempt code retains only the native action leaves its source can mint.
Consumers: the actual pending native producer and both Timeout numeric endpoint goals.
Reach: the actual attempt subtree, source callback leaves, and existing saved-frame producer.
Limit: this annotation supplies neither numeric heap authority nor an initialized history.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberSourceActions
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutNumberConfiguration HostTimeoutNumberSourceSlots

/-- The source fold marks constructors outside the attempt's ordinary direct fragment. -/
def exceptionalSource (code : NativeEff) (path : List Nat) : List (List Nat) :=
  match code with
  | .succeed _ | .fail _ | .perform _ _ | .bind _ _ | .onExit _ _ => []
  | _ => [path]

def exceptional : PathYield NativeOp (List Nat) := { eff := exceptionalSource }

/-- These exceptional source positions all precede the pending attempt subtree. -/
theorem exceptional_positions : Node.foldList exceptional [] (.eff HostTimeoutSource.program) =
    [[1,1,1,0], [1,1,1,0,0,0], [1,1,1,0,0,1], [1,1,1,0,0,1,0,0,0],
     [1,1,1,1], [1,1,1,1,0], [1,1,1,1,0,0]] := by
  kernel_rfl

/-- The actual subtree retains the constructor classification used by native leaf contracts. -/
theorem ordinary_source (context : CountContext) (point : Point) (code : NativeEff)
    (held : At context point)
    (found : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff code)) :
    exceptional.eff code point.path = [] := by
  have lower := held.subtree.length_le
  change 12 ≤ point.path.length at lower
  have bounded : ∀ path ∈ Node.foldList exceptional [] (.eff HostTimeoutSource.program),
      path.length < 12 := by
    rw [exceptional_positions]
    intro path member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with first | second | third | fourth | fifth | sixth | seventh
    all_goals subst path; decide
  have subset := Node.yieldAt_subset_of_at exceptional point.path (.eff HostTimeoutSource.program)
    (.eff code) [] found
  change exceptionalSource code point.path ⊆ _ at subset
  have impossible : ¬ point.path ∈ exceptionalSource code point.path :=
    fun member => Nat.not_lt_of_ge lower (bounded point.path (subset member))
  have shape : exceptionalSource code point.path = [] ∨
      exceptionalSource code point.path = [point.path] := by
    fun_cases exceptionalSource code point.path
    all_goals aesop (rule_sets := [Effect4.CodeClosure])
  rcases shape with empty | singleton
  · exact empty
  · exact (impossible (singleton.symm ▸ List.mem_singleton_self point.path)).elim

/-- Only source callbacks and the native finalizer's ordinary wrappers belong to the attempt. -/
def NameAt (context : CountContext) : EffName → Prop
  | .cont point | .caught point | .caughtError point | .onValue point | .onCause point
  | .fin point | .loop point => At context point
  | .restore _ | .merge _ | .constant _ | .reFail _ | .abort | .serviceLookup _
  | .external _ _ _ | .registerAwait _ | .cancelAwait _ => True
  | .store (.registerSleep _) | .store .cancelSleep => True
  | _ => False

/-- Source actions retain their actual point; no embedded native action is admitted. -/
def ThunkAt (context : CountContext) : EffThunk → Prop
  | .pure point | .body point | .act point => At context point
  | .op _ | .park _ | .getCtx | .captureMask => True
  | _ => False

/-- The existing generated code fold carries these exact leaves through current and saved code. -/
abbrev CodeAt (context : CountContext) := CodeClosure.Code (NameAt context) (ThunkAt context)

/-- The prior environment-only action slot admits a direct cancellation absent from this subtree. -/
theorem broad_cancel_admitted (context : CountContext) (race : Nat) :
    CodeClosure.Slots.CodeAt (At context) (AnswerSlots.Prefix (bindings context))
      (.withFiber (.store (.act (.cancelRace race)))) := by
  trivial

/-- The pending source annotation rejects the fabricated direct race-cancellation action. -/
theorem cancel_rejected (context : CountContext) (race : Nat) :
    ¬ CodeAt context (.withFiber (.store (.act (.cancelRace race)))) := by
  intro owned
  exact owned

/-- The ordinary async router creates only external, sleep, and deferred registration leaves. -/
theorem asynchronous (context : CountContext) (row : NativeOp) (request : Term) (point : Point) :
    CodeAt context (asyncRoute row request point) := by
  fun_cases asyncRoute row request point
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, NameAt, badShape])

/-- The existing compiler fold consumes the restricted source leaves directly. -/
theorem compilation (context : CountContext) :
    CodeClosure.CompileContract HostTimeoutSource.program (At context) (NameAt context) (ThunkAt context) := by
  refine {
    child := ?_, body := ?_, pure := ?_, act := ?_, operation := ?_, asynchronous := ?_,
    cont := ?_, caught := ?_, caughtError := ?_, onValue := ?_, onCause := ?_, fin := ?_,
    forkScoped := ?_, acquire := ?_, service := ?_, provideService := ?_, provideContext := ?_,
    getContext := ?_, captureMask := ?_, park := ?_ }
  case refine_1 => intro p e i found held selected; exact (transport context).child held i
  case refine_2 => intro p e found held; exact held
  case refine_3 => intro p term found held; exact held
  case refine_4 => intro p e found held; exact held
  case refine_5 => intros; trivial
  case refine_6 => intros; exact asynchronous context _ _ _
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, ThunkAt, exceptional, exceptionalSource]) (add safe forward [ordinary_source])

/-- Resolving an actual retained point uses the shared compiler closure. -/
theorem resolve_at (context : CountContext) (point : Point) (held : At context point) :
    CodeAt context (resolve HostTimeoutSource.program point) := by
  unfold resolve
  split
  · rename_i code found
    exact CodeClosure.compile_closure (compilation context) code point found held
  · trivial

/-- A callback's actual bound child remains in the same source subtree. -/
theorem resolve_argument (context : CountContext) (point : Point) (index : Nat) (value : Val)
    (held : At context point) :
    CodeAt context (resolve HostTimeoutSource.program (point.childWith index value)) :=
  resolve_at context _ ((transport context).childWith held index value)

/-- Value leaves reuse actual source resolution and the ordinary native wrappers. -/
theorem value_leaf (context : CountContext) (name : EffName) (value : Val)
    (owned : NameAt context name) : CodeAt context (contAOf HostTimeoutSource.program name value) := by
  revert owned
  fun_cases contAOf HostTimeoutSource.program name value
  all_goals intro owned
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, ThunkAt, CodeAt, Prim.ofExit, badShape, Effect4.Machine.contAOf, embed]) (add norm unfold [serviceLookupK]) (add safe apply [resolve_argument])

/-- Failure leaves resolve only actual retained source children or ordinary exit wrappers. -/
theorem cause_leaf (context : CountContext) (name : EffName) (cause : CauseV)
    (owned : NameAt context name) : CodeAt context (contEOf HostTimeoutSource.program name cause) := by
  revert owned
  fun_cases contEOf HostTimeoutSource.program name cause
  all_goals intro owned
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, ThunkAt, CodeAt, Prim.ofExit, badShape, Effect4.Machine.contEOf, embed]) (add safe apply [resolve_argument])

/-- A selected source child keeps the same bindings whether or not it binds an answer. -/
theorem resolve_selected (context : CountContext) (point : Point) (index : Nat) (value : Option Val)
    (held : At context point) :
    CodeAt context (resolve HostTimeoutSource.program (point.childBind index value)) := by
  cases value with
  | none => exact resolve_at context _ ((transport context).child held index)
  | some value => exact resolve_argument context point index value held

/-- Suspended source leaves reuse the existing body contract and compiler fold. -/
theorem suspend_leaf (context : CountContext) (thunk : EffThunk) (owned : ThunkAt context thunk) :
    CodeAt context (suspendBodyAt HostTimeoutSource.program thunk) := by
  cases thunk
  case body point =>
    exact CodeClosure.suspend_body_at _ fragment (At context) (CodeAt context)
      { compiled := fun code point found held => CodeClosure.compile_closure (compilation context) code point found held
        frontier := fun _ held => held
        child := fun point held => resolve_at context _ ((transport context).child held 0)
        selected := fun point first bound held => resolve_selected context point _ bound held
        loop := fun _ _ held => held
        badShape := trivial } point owned
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [ThunkAt, CodeAt, suspendBodyAt, badShape])

/-- Value invocation refreshes only the actual retained point's completed-exit view. -/
theorem value_actual (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt context name) :
    CodeAt context ((interpAt HostTimeoutSource.program view table).contA name value) := by
  apply value_leaf context
  cases name
  case cont point | onValue point => exact completed context point view owned
  all_goals exact owned

/-- Cause invocation preserves the same actual source callback after view refresh. -/
theorem cause_actual (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (name : EffName) (cause : CauseV) (owned : NameAt context name) :
    CodeAt context ((interpAt HostTimeoutSource.program view table).contE name cause) := by
  apply cause_leaf context
  cases name
  case caught point | caughtError point | onCause point => exact completed context point view owned
  all_goals exact owned

/-- No source iterate lies within the pending attempt's actual subtree. -/
theorem loop_absent (context : CountContext) (point : Point) (held : At context point) :
    loopAt HostTimeoutSource.program point = none := by
  fun_cases loopAt HostTimeoutSource.program point
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add safe forward [ordinary_source]) (add norm simp [exceptional, exceptionalSource])

/-- Actual async cleanup names retain only the cancellation programs the source can mint. -/
theorem cancel_leaf (context : CountContext) (name : EffName) (owned : NameAt context name) :
    CodeAt context (cancelProgramOf name) := by
  fun_cases NameAt context name
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, ThunkAt, cancelProgramOf, Effect4.Machine.cancelProgram, embed])

/-- A refreshed source suspension uses the same retained source binding. -/
theorem suspend_actual (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (thunk : EffThunk) (owned : ThunkAt context thunk) :
    CodeAt context ((interpAt HostTimeoutSource.program view table).suspendBody thunk) := by
  apply suspend_leaf context
  cases thunk
  case body point => exact completed context point view owned
  all_goals exact owned

/-- Allowed iterator leaves have no residual generated source program. -/
theorem iterator_leaf (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (name : EffName) (value : Val) (owned : NameAt context name) :
    CodeClosure.Arms.Iteration (CodeAt context)
      (((interpAt HostTimeoutSource.program view table).iterNext name value).2) := by
  fun_cases NameAt context name
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, CodeClosure.Arms.Iteration, interpAt, interpOf, stores, embedStep])

/-- Actual loop resumption cannot invent an iterate inside the attempt. -/
theorem loop_leaf (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (name : EffName) (cursor value : Val) (owned : NameAt context name) :
    CodeClosure.Arms.Loop (CodeAt context) name
      ((interpAt HostTimeoutSource.program view table).loopResume name cursor value) := by
  cases name
  case loop point =>
    have absent := loop_absent context {point with completed := view} (completed context point view owned)
    change CodeClosure.Arms.Loop (CodeAt context) (.loop point)
      (loopResumeAt HostTimeoutSource.program {point with completed := view} cursor value)
    rw [loopResumeAt, absent]
    trivial
  all_goals trivial

/-- The existing single arm producer consumes the restricted actual callback leaves. -/
theorem arm_rules (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable) :
    CodeClosure.Arms.Rules (CodeAt context)
      (interpAt HostTimeoutSource.program view table).toPrimInterp where
  success _ := trivial
  failure _ := trivial
  value _body callback value held := value_actual context view table callback value held.2
  constant _body _next held := held.2
  bothValue _body callback _other value held := value_actual context view table callback value held.2.1
  cause _body callback cause held := cause_actual context view table callback cause held.2
  bothCause _body _other callback cause held := cause_actual context view table callback cause held.2.2
  cancel callback _cause held := ⟨cancel_leaf context callback held, trivial⟩
  iterator callback _cursor value held := iterator_leaf context view table callback value held
  loop callback cursor value held := loop_leaf context view table callback cursor value held

/-- An installed finalizer resolves the actual admitted source callback. -/
theorem finalizer_leaf (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (name : EffName) (exit : ExitV) (body : NCode) (owned : NameAt context name)
    (found : (interpAt HostTimeoutSource.program view table).finalizerProgram name exit = some body) :
    CodeAt context body := by
  cases name
  case fin point =>
    cases found
    exact resolve_argument context _ 1 (reifyExitVal exit) (completed context point view owned)
  case store stored =>
    fun_cases NameAt context (.store stored)
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [NameAt, interpAt, interpOf])
  case scopeClose scope => exact owned.elim
  case restoreCtx previous => exact owned.elim
  all_goals cases found

/-- The finalizer's restore and merge wrappers retain the same restricted annotation. -/
theorem finalizer_wrapper (context : CountContext) (view : HostTimeoutFlow.View) (table : RowTable)
    (exit : ExitV) (body : NCode) (owned : CodeAt context body) :
    CodeAt context (finalizerCode (interpAt HostTimeoutSource.program view table) exit body) := by
  cases exit with
  | success value => exact ⟨owned, trivial⟩
  | failure cause => exact ⟨⟨owned, trivial⟩, trivial⟩

/-- One supplied actual-code predicate reuses the common current and saved producer. -/
theorem rules (context : CountContext) :
    CodeClosure.PredicateFamily.Rules HostTimeoutSource.program
      Test.Dogfood.Scenario.Timeout.fetch.table (CodeAt context) where
  success _ := trivial
  failure _ := trivial
  children := by
    intro code owned
    cases code
    all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeClosure.PredicateFamily.Children, CodeAt])
  mask _ := trivial
  suspend := by
    intro view thunk owned
    apply suspend_actual context view _ thunk
    rcases owned with owned | owned
    all_goals exact owned
  value view frame value provided next pushed owned actual :=
    CodeClosure.Arms.value _ _ (arm_rules context view _) frame value provided next pushed owned actual
  cause view frame cause provided next pushed owned actual :=
    CodeClosure.Arms.cause _ _ (arm_rules context view _) frame cause provided next pushed owned actual
  loopContinue := by
    intro view callback cursor next body owned actual
    cases callback
    case loop point =>
      have absent := loop_absent context {point with completed := view} (completed context point view owned)
      change loopNextAt HostTimeoutSource.program {point with completed := view} cursor = _ at actual
      rw [loopNextAt, absent] at actual
      cases actual
    all_goals cases actual
  loopFinish := by
    intro view callback cursor body owned actual
    cases callback
    case loop point =>
      have absent := loop_absent context {point with completed := view} (completed context point view owned)
      change loopNextAt HostTimeoutSource.program {point with completed := view} cursor = _ at actual
      rw [loopNextAt, absent] at actual
      cases actual
      trivial
    all_goals cases actual; trivial
  finalizer := by
    intro view frame exit next owned installed
    cases frame
    case onExit body callback flag =>
      obtain ⟨program, found, same⟩ := Option.map_eq_some_iff.mp installed
      rw [← same]
      exact finalizer_wrapper context view _ exit program (finalizer_leaf context view _ callback exit program owned.2 found)
    all_goals cases installed

/-- The actual attempt entry receives the restricted source certificate from the compiler fold. -/
theorem entry_code (context : CountContext) : CodeAt context context.entry :=
  resolve_at context context.point (entry context)

/-- The retained entry exposes the same actual count binder and its primitive write. -/
theorem entry_parts (context : CountContext) :
    CodeAt context context.bound ∧ CodeAt context context.write := by
  have source := entry_code context
  change CodeAt context (resolve HostTimeoutSource.program
    (HostTimeoutNumberEntry.attemptPoint context.captured (context.fuel + 1) context.delay context.n context.previous)) at source
  rw [HostTimeoutNumberEntry.attempt_code] at source
  exact ⟨source.1, source.1.1⟩

/-- Current heads consume the same restricted code annotation as actual saved callbacks. -/
theorem head (context : CountContext) (view : HostTimeoutFlow.View) (code : NCode)
    (owned : CodeAt context code) :
    AnswerFlow.HeadAt
      ((CodeClosure.PredicateFamily.spec HostTimeoutSource.program
        Test.Dogfood.Scenario.Timeout.fetch.table (CodeAt context) (rules context)).model view)
      (HostTimeoutFlow.interpreter view).toPrimInterp (CodeClosure.PredicateFamily.edge (CodeAt context)) () () code :=
  CodeClosure.PredicateFamily.head _ _ _ (rules context) view code owned

/-- Saved frames reuse the existing actual-code predicate producer without another pop walk. -/
theorem family (context : CountContext) (view : HostTimeoutFlow.View) :
    AnswerFlow.SavedFamily
      ((CodeClosure.PredicateFamily.spec HostTimeoutSource.program
        Test.Dogfood.Scenario.Timeout.fetch.table (CodeAt context) (rules context)).model view)
      (HostTimeoutFlow.interpreter view).toPrimInterp (CodeClosure.PredicateFamily.edge (CodeAt context)) :=
  CodeClosure.PredicateFamily.family _ _ _ (rules context) view

/-- Current and saved code carry one actual source action annotation. -/
structure FrameAt (context : CountContext) (frame : HostTimeoutFrames.NativeFrame) : Prop where
  current : CodeAt context frame.current
  saved : ∀ code ∈ frame.stack, CodeAt context code

/-- Frame metadata transport keeps the exact source action leaves. -/
theorem FrameAt.fields (context : CountContext) (before after : HostTimeoutFrames.NativeFrame)
    (held : FrameAt context before) (current : after.current = before.current)
    (stack : after.stack = before.stack) : FrameAt context after := by
  constructor
  · rw [current]; exact held.current
  · rw [stack]; exact held.saved

/-- Actual native finalizer dispatch retains the admitted action leaves in the same frame. -/
theorem finalizer_frame (context : CountContext) (view : HostTimeoutFlow.View)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool) (exit : ExitV)
    (current : fiber.frame.current = Prim.ofExit exit) (held : FrameAt context fiber.frame) :
    let next := evaluatePrim.finalizerOr (HostTimeoutFlow.interpreter view) machine fiber yielding exit
    FrameAt context next.fiber.frame := by
  let spec := CodeClosure.PredicateFamily.spec HostTimeoutSource.program
    Test.Dogfood.Scenario.Timeout.fetch.table (CodeAt context) (rules context)
  let edge := CodeClosure.PredicateFamily.edge (CodeAt context)
  have path := CodeClosure.PredicateFamily.path (CodeAt context) fiber.frame.stack held.saved
  have good : AnswerFlow.ExitAt (spec.model view) () () exit := by cases exit <;> trivial
  obtain ⟨output, next⟩ := AnswerFlow.External.Native.finalizer_frame (spec.model view)
    (HostTimeoutFlow.interpreter view) edge (family context view) (by intros; trivial)
    () () () machine fiber yielding exit current held.current path good
    (by intros; trivial) (by intros; rfl)
  obtain ⟨input, code, saved⟩ := next
  exact ⟨code, CodeClosure.PredicateFamily.path_owned (CodeAt context) saved⟩

/-- Joint numeric and source heads exclude both unminted native race-cancellation forms. -/
theorem no_native_action (context : CountContext) (state : Stores)
    (kind : HostTimeoutNumberPhaseFlow.Kind) (thunk : EffThunk)
    (numeric : HostTimeoutNumberPhaseFlow.CodeAt state kind (.withFiber thunk))
    (source : CodeAt context (.withFiber thunk)) : False := by
  cases numeric
  all_goals exact source

/-- The actual ordinary frame step retains the same restricted current and saved source leaves. -/
theorem frame_step (context : CountContext) (view : HostTimeoutFlow.View)
    (before after : HostTimeoutFrames.NativeFrame) (events : List (FrameEvent EffName EffThunk Val Err Defect FiberId Ann))
    (held : FrameAt context before)
    (actual : FrameFiber.step (HostTimeoutFlow.interpreter view).toPrimInterp before = (.running after, events))
    (noSuccess : ∀ value, before.current ≠ .success value)
    (noFailure : ∀ cause, before.current ≠ .failure cause)
    (noSync : ∀ thunk, before.current ≠ .sync thunk) : FrameAt context after := by
  let spec := CodeClosure.PredicateFamily.spec HostTimeoutSource.program
    Test.Dogfood.Scenario.Timeout.fetch.table (CodeAt context) (rules context)
  have path := CodeClosure.PredicateFamily.path (CodeAt context) before.stack held.saved
  have moved := AnswerFlow.frame_step (spec.model view) (HostTimeoutFlow.interpreter view).toPrimInterp
    (CodeClosure.PredicateFamily.edge (CodeAt context)) () () () before
    (head context view before.current held.current) path
    (by
      intro value provided current good
      rcases current with ⟨current, supplied⟩ | ⟨thunk, current, equal, supplied⟩
      · exact (noSuccess value current).elim
      · exact (noSync thunk current).elim)
    (by intro cause current good; exact (noFailure cause current).elim)
  rw [actual] at moved
  obtain ⟨input, code, saved⟩ := moved
  exact ⟨code, CodeClosure.PredicateFamily.path_owned (CodeAt context) saved⟩

end Test.Dogfood.Proofs.HostTimeoutNumberSourceActions

