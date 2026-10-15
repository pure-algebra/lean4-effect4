import Effect4.Laws.Program.AnswerSlots.Interp
import Effect4.Laws.Program.AnswerSlots.Stable

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: Atomic.shop_stages and the numeric cleanup goals retain initialized root bindings.
Reach: the direct source fragment, all completed-fiber views and actual saved callback suffixes.
Limit: allocation, source ownership and command history remain separate premises.
Consumer: the common allocation-prefix adapter and its Atomic and Timeout instances.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- The broad stable class retains initialized bindings and admits every answer. -/
def prefixSpec (root : NativeEff) (table : RowTable) (bindings : List Val) : StableSpec where
  root := root
  table := table
  Kind := Unit
  rootKind := ()
  value _ _ := True
  code _ := CodeAt bindings
  success _ _ _ := trivial
  failure _ _ := trivial

/-- Every exit representation contains no delayed source environment. -/
theorem prefix_ofExit (bindings : List Val) (exit : ExitV) : CodeAt bindings (Prim.ofExit exit) := by
  cases exit <;> trivial

/-- Actual value callbacks retain the current code and every pushed binding certificate. -/
theorem prefix_armA (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (view) (table : RowTable)
    (frame : NCode) (value : Val) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt bindings frame)
    (actual : frame.armA (interpAt root view table).toPrimInterp value provided = some (next, pushed)) :
    CodeAt bindings next ∧ ∀ code ∈ pushed, CodeAt bindings code := by
  fun_cases Prim.armA (interpAt root view table).toPrimInterp frame value provided
  all_goals aesop (add norm simp [CodeAt, Prim.armA, LoopAt, IterAt]) (add safe apply [prefix_ofExit, (interp_contA_at root bindings fragment)]) (add safe forward [(interp_loopResume_at root bindings fragment), interp_iter_at])

/-- Actual cause callbacks retain the current code and every pushed binding certificate. -/
theorem prefix_armE (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (view) (table : RowTable)
    (frame : NCode) (cause : CauseV) (provided : Option ExitV) (next : NCode) (pushed : List NCode)
    (owned : CodeAt bindings frame)
    (actual : frame.armE (interpAt root view table).toPrimInterp cause provided = some (next, pushed)) :
    CodeAt bindings next ∧ ∀ code ∈ pushed, CodeAt bindings code := by
  fun_cases Prim.armE (interpAt root view table).toPrimInterp frame cause provided
  all_goals aesop (add norm simp [CodeAt, Prim.armE]) (add safe apply [prefix_ofExit, (interp_contE_at root bindings fragment), interp_cancel_at])

/-- Native finalizer restoration adds no delayed source environment. -/
theorem prefix_finalizerCode (root : NativeEff) (bindings : List Val) (view) (table : RowTable)
    (exit : ExitV) (body : NCode) (owned : CodeAt bindings body) :
    CodeAt bindings (finalizerCode (interpAt root view table) exit body) := by
  cases exit with
  | success value => exact ⟨owned, trivial⟩
  | failure cause => exact ⟨⟨owned, trivial⟩, trivial⟩

/-- The same binding certificate annotates saved code at every completed-fiber view. -/
def prefixEdge (bindings : List Val) (_ : Unit) (_ _ : Unit) : NCode → Prop := CodeAt bindings

/-- An actual saved suffix composes the same immutable binding certificate. -/
theorem prefix_path (bindings : List Val) (frames : List NCode)
    (owned : ∀ code ∈ frames, CodeAt bindings code) :
    Contracts.Path (prefixEdge bindings ()) () () frames := by
  induction frames with
  | nil => exact .nil ()
  | cons frame rest ih =>
    exact .cons (owned frame (.head _)) (ih (fun code member => owned code (.tail _ member)))

/-- Every actual callback view supplies the common saved-frame obligations. -/
theorem prefix_family (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) (view) :
    AnswerFlow.SavedFamily ((prefixSpec root table bindings).model view)
      (interpAt root view table).toPrimInterp (prefixEdge bindings) := by
  constructor
  · intros; trivial
  · intros; trivial
  · intro world input output frame held nextWorld future value provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := prefix_armA root fragment bindings view table frame value provided next pushed held actual
    cases output
    exact ⟨(), code, prefix_path bindings pushed stack⟩
  · intro world input output frame held nextWorld future cause provided next pushed good supplied absent actual
    obtain ⟨code, stack⟩ := prefix_armE root fragment bindings view table frame cause provided next pushed held actual
    cases output
    exact ⟨(), code, prefix_path bindings pushed stack⟩
  · intro world input output frame held nextWorld future exit next good installed
    cases frame
    case onExit body name flag =>
      change Option.map (finalizerCode (interpAt root view table) exit)
        ((interpAt root view table).finalizerProgram name exit) = some next at installed
      obtain ⟨program, found, equal⟩ := Option.map_eq_some_iff.mp installed
      rw [← equal]
      exact prefix_finalizerCode root bindings view table exit program
        (interp_fin_at root bindings fragment view table name exit program held.2 found)
    all_goals cases installed
  · intros; trivial

/-- Every permitted current head consumes the same stable binding class. -/
theorem prefix_head (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) (view) (code : NCode) (owned : CodeAt bindings code) :
    AnswerFlow.HeadAt ((prefixSpec root table bindings).model view)
      (interpAt root view table).toPrimInterp (prefixEdge bindings) () () code := by
  cases code
  case success value => exact .success value trivial
  case failure cause => exact .failure cause trivial
  case sync thunk => exact .sync thunk trivial
  case suspend thunk => exact .suspend thunk (interp_suspend_at root bindings fragment view table thunk owned)
  case withFiber thunk => exact .withFiber thunk (interp_suspend_at root bindings fragment view table thunk owned)
  case yieldableError error => exact .yieldableError error trivial
  case iterator name cursor =>
    refine .iterator name cursor owned ?_
    intro next pushed actual
    obtain ⟨code, slots⟩ := prefix_armA root fragment bindings view table _ cursor none next pushed owned actual
    exact ⟨(), code, prefix_path bindings pushed slots⟩
  case whileLoop name cursor =>
    have slots := interp_loopEnter_at root bindings fragment view table name cursor owned
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

/-- The common allocation adapter accepts the existing prefix graph at every actual view. -/
def prefixLaws (root : NativeEff) (fragment : SourceScope.Fragment root)
    (bindings : List Val) (table : RowTable) : StableLaws (prefixSpec root table bindings) where
  Edge := prefixEdge bindings
  family := prefix_family root fragment bindings table
  head view kind code owned := by
    cases kind
    exact prefix_head root fragment bindings table view code owned

end Effect4.Program.AnswerSlots
