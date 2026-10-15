import Effect4.Laws.Program.CodeClosure.Interp
import Effect4.Laws.Program.AnswerSlots.Stable

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual source callbacks retain one supplied code annotation through native frames.
Consumers: the Prefix stable instance and both Timeout numeric endpoint producers.
Reach: the existing direct source fragment, actual callback views, and actual saved suffixes.
Limit: this instance supplies no initialization, numeric effects, or command history.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.AnswerSlots

/-- The broad stable class retains initialized point env and admits every answer. -/
def prefixSpec (root : NativeEff) (table : RowTable) (point : Point → Prop) (env : List Val → Prop) : StableSpec where
  root := root
  table := table
  Kind := Unit
  rootKind := ()
  value _ _ := True
  code _ := CodeAt point env
  success _ _ _ := trivial
  failure _ _ := trivial

/-- Every exit representation contains no delayed source environment. -/
theorem prefix_ofExit (point : Point → Prop) (env : List Val → Prop) (exit : ExitV) : CodeAt point env (Prim.ofExit exit) := by
  cases exit <;> trivial

/-- Actual value callbacks retain the current code and every pushed binding certificate. -/
theorem prefix_armA (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (stable : ViewStable point) (view) (table : RowTable)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt point env frame)
    (actual : frame.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    CodeAt point env next ∧ ∀ code ∈ pushed, CodeAt point env code := by
  fun_cases Prim.armA (interpAt root view table).toPrimInterp frame value provided
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, Prim.armA, LoopAt, IterAt]) (add safe apply [prefix_ofExit, (interp_contA_at root fragment point env contract stable)]) (add safe forward [(interp_loopResume_at root fragment point env contract stable), interp_iter_at])

/-- Actual cause callbacks retain the current code and every pushed binding certificate. -/
theorem prefix_armE (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (stable : ViewStable point) (view) (table : RowTable)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt point env frame)
    (actual : frame.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    CodeAt point env next ∧ ∀ code ∈ pushed, CodeAt point env code := by
  fun_cases Prim.armE (interpAt root view table).toPrimInterp frame cause provided
  all_goals aesop (rule_sets := [Effect4.CodeClosure]) (add norm simp [CodeAt, Prim.armE]) (add safe apply [prefix_ofExit, (interp_contE_at root fragment point env contract stable), interp_cancel_at])

/-- Native finalizer restoration adds no delayed source environment. -/
theorem prefix_finalizerCode (root : NativeEff) (point : Point → Prop) (env : List Val → Prop) (view) (table : RowTable)
    (exit : ExitV) (body : NCode) (owned : CodeAt point env body) :
    CodeAt point env (finalizerCode (interpAt root view table) exit body) := by
  cases exit with
  | success value => exact ⟨owned, trivial⟩
  | failure cause => exact ⟨⟨owned, trivial⟩, trivial⟩

/-- The same binding certificate annotates saved code at every completed-fiber view. -/
def prefixEdge (point : Point → Prop) (env : List Val → Prop) (_ : Unit) (_ _ : Unit) : NCode → Prop := CodeAt point env

/-- An actual saved suffix composes the same immutable binding certificate. -/
theorem prefix_path (point : Point → Prop) (env : List Val → Prop) (frames : List NCode)
    (owned : ∀ code ∈ frames, CodeAt point env code) :
    Contracts.Path (prefixEdge point env ()) () () frames := by
  induction frames with
  | nil => exact .nil ()
  | cons frame rest ih =>
    exact .cons (owned frame (.head _)) (ih (fun code member => owned code (.tail _ member)))

/-- Reading an actual saved path recovers every frame's supplied source annotation. -/
theorem prefix_path_owned (point : Point → Prop) (env : List Val → Prop)
    {input output : Unit} {frames : List NCode}
    (path : Contracts.Path (prefixEdge point env ()) input output frames) :
    ∀ code ∈ frames, CodeAt point env code := by
  induction path with
  | nil kind => intro code member; cases member
  | cons head tail ih =>
    intro code member
    rcases List.mem_cons.mp member with same | rest
    · rw [same]; exact head
    · exact ih code rest

/-- Every actual callback view supplies the common saved-frame obligations. -/
theorem prefix_family (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (stable : ViewStable point) (table : RowTable) (view) :
    AnswerFlow.SavedFamily ((prefixSpec root table point env).model view)
      (interpAt root view table).toPrimInterp (prefixEdge point env) := by
  constructor
  · intros; trivial
  · intros; trivial
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := prefix_armA root fragment point env contract stable view table frame value provided next pushed held actual
    cases output
    exact ⟨(), code, prefix_path point env pushed stack⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := prefix_armE root fragment point env contract stable view table frame cause provided next pushed held actual
    cases output
    exact ⟨(), code, prefix_path point env pushed stack⟩
  · intro world input output frame held nextWorld future exit next good installed
    cases frame
    case onExit body name flag =>
      change Option.map (finalizerCode (interpAt root view table) exit)
        ((interpAt root view table).finalizerProgram name exit) = some next at installed
      obtain ⟨program, found, equal⟩ := Option.map_eq_some_iff.mp installed
      rw [← equal]
      exact prefix_finalizerCode root point env view table exit program
        (interp_fin_at root fragment point env contract stable view table name exit program held.2 found)
    all_goals cases installed
  · intros; trivial

/-- Every permitted current head consumes the same stable binding class. -/
theorem prefix_head (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env) (stable : ViewStable point) (table : RowTable) (view) (code : NCode) (owned : CodeAt point env code) :
    AnswerFlow.HeadAt ((prefixSpec root table point env).model view)
      (interpAt root view table).toPrimInterp (prefixEdge point env) () () code := by
  cases code
  case success value => exact .success value trivial
  case failure cause => exact .failure cause trivial
  case sync thunk => exact .sync thunk trivial
  case suspend thunk => exact .suspend thunk (interp_suspend_at root fragment point env contract stable view table thunk owned)
  case withFiber thunk => exact .withFiber thunk (interp_suspend_at root fragment point env contract stable view table thunk owned)
  case yieldableError error => exact .yieldableError error trivial
  case iterator name cursor =>
    refine .iterator name cursor owned ?_
    intro next pushed actual
    obtain ⟨code, slots⟩ := prefix_armA root fragment point env contract stable view table _ cursor none next pushed owned actual
    exact ⟨(), code, prefix_path point env pushed slots⟩
  case whileLoop name cursor =>
    have slots := interp_loopEnter_at root fragment point env contract stable view table name cursor owned
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
def prefixLaws (root : NativeEff) (fragment : SourceScope.Fragment root)
    (point : Point → Prop) (env : List Val → Prop) (contract : Contract root point env)
    (stable : ViewStable point) (table : RowTable) : StableLaws (prefixSpec root table point env) where
  Edge := prefixEdge point env
  family := prefix_family root fragment point env contract stable table
  head view kind code owned := by
    cases kind
    exact prefix_head root fragment point env contract stable table view code owned

end Effect4.Program.CodeClosure.Slots
