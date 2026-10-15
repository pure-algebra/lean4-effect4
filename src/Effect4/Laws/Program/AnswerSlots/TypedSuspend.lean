import Effect4.Laws.Program.AnswerSlots.TypedCallbacks

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: suspension and loop entry retain protected source points.
Reach: the direct lexical fragment, represented decisions and actual native suspension.
Limit: action and command closure remain separate obligations.
Consumer: the protected native evaluation and saved loop family.
-/
set_option autoImplicit false
set_option maxHeartbeats 8000000
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- A represented selection cannot enter a release child belonging to an acquisition head. -/
theorem select_source (spec : Spec) (point : Point)
    (term : Term) (decision : Decision) (yes no : NativeEff) (value : Val)
    (first : Bool) (bound : Option Val)
    (found : Node.at_ (.eff spec.root) point.path = some (.eff (.select term decision yes no)))
    (source : SourceScope.At spec.root point) (slots : Prefix spec.bindings point.env)
    (answer : decision.decide value = some (first, bound)) :
    SourcePoint spec (point.childBind (cond first 0 1) bound) := by
  refine ⟨SourceScope.select_scope_at spec.root point term decision yes no value first bound found source answer,
    childBind slots _ bound, .inl ?_⟩
  exact childBind_ordinary spec.root spec.acquisitions (sites spec) point _ bound
    (.inr (not_acquisition spec.root point _ found (fun _ _ wrong => nomatch wrong)))

/-- A suspension executes only the source point or captured wrapper its actual thunk owns. -/
theorem suspend_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (thunk : EffThunk) (owned : ThunkAt spec thunk) :
    CodeAt spec .root (suspendBodyAt spec.root thunk) := by
  revert owned
  fun_cases suspendBodyAt spec.root thunk
  case case2 point n fuel body found =>
    intro owned
    exact resolve_source spec fragment _ (zero_source spec point
      (SourceScope.next_of_at spec.root point _ 0 0 found owned.1 rfl) owned.2.1)
  all_goals intro owned
  all_goals have lexical := SourceScope.suspend_at spec.root fragment _ owned.1
  all_goals have leading := AnswerSlots.suspend_at spec.root fragment spec.bindings _ owned.2.1
  all_goals aesop (add norm simp [CodeAt, ValueAt, ThunkAt, NameAt, OrdinaryName, ProtectedName,
    StoreThunkAt, FinAt, SourceScope.ThunkAt, SourceScope.CodeAt, SourceScope.NameAt,
    SourceScope.StoreThunkAt, SourceScope.FinAt, SourceScope.directHead,
    AnswerSlots.ThunkAt, AnswerSlots.CodeAt, AnswerSlots.NameAt, AnswerSlots.StoreThunkAt,
    AnswerSlots.FinAt, SourcePoint, badShape, frontier]) (add safe apply [(compile_at spec fragment),
      (resolve_source spec fragment), select_source, progOf_at]) (add safe forward [SourceScope.Fragment.at, select_source])

/-- A native loop result retains its protected body. -/
def LoopAt (spec : Spec) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt spec .root body

/-- Loop completion exposes a completed value or shape failure. -/
theorem loopFinish_at (spec : Spec) (point : Point) (cursor : Val) :
    CodeAt spec .root (loopFinishAt spec.root point cursor) := by
  fun_cases loopFinishAt spec.root point cursor
  all_goals trivial

/-- The actual loop's cursor enters a child-zero source body. -/
theorem loopNext_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (point : Point) (cursor : Val) (source : SourcePoint spec point) :
    LoopAt spec (loopNextAt spec.root point cursor) := by
  fun_cases loopNextAt spec.root point cursor
  case case1 test step body found reads =>
    exact resolve_source spec fragment _ (argument_source spec point 0 cursor
      (SourceScope.loop_head_at spec.root point test step body source.1 found)
      source.2.1 (.inl (by decide)))
  all_goals aesop (add norm simp [LoopAt, loopFinish_at, CodeAt, badShape]) (add safe apply [(resolve_source spec fragment), argument_source, SourceScope.loop_head_at])

/-- Loop resumption keeps the original protected source point across cursor updates. -/
theorem loopResume_at (spec : Spec) (fragment : SourceScope.Fragment spec.root)
    (point : Point) (cursor answer : Val) (source : SourcePoint spec point) :
    LoopAt spec (loopResumeAt spec.root point cursor answer) := by
  unfold loopResumeAt
  cases found : loopAt spec.root point with
  | none => trivial
  | some row =>
    obtain ⟨test, step, body⟩ := row
    simp only []
    cases value : evalTerm (point.env ++ [cursor, answer]) step with
    | none => trivial
    | some next => exact loopNext_at spec fragment point next source
end Effect4.Program.AnswerSlots.Typed
