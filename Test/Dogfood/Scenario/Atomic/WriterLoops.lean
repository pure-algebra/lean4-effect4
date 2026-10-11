import Test.Dogfood.Scenario.Atomic.WriterSuspensions

/-!
Concept: scope-lifetime-finalization, R11.
Consumer: repeated-body and iterator cases of the actual cleanup writer invariant.
The existing source census excludes the selected note from every repeated body.
-/
set_option autoImplicit false
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Scenario.Atomic.WriterLoops
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope Effect4.Laws.Auto
open WriterPhase WriterSource

/-- The active reservation is bounded by the existing selected-source projection. -/
theorem below_source (id : Nat) (path : List Nat) :
    WriterPhase.below id path ≤ Opportunities.below (Writer.notePath id) path := by
  unfold WriterPhase.below
  split
  · exact Nat.le_refl _
  · exact Nat.zero_le _

/-- The actual loop census excludes every selected note from repeated source bodies. -/
def clearLoops (root : NativeEff) (id : Nat) : Bool :=
  (Node.addresses (.eff root)).all fun path =>
    (Node.at_ (.eff root) path).all fun node => match node with
      | .eff (.iterate _ _ _ _ _ _) => !(path ++ [0]).isPrefixOf (Writer.notePath id)
      | _ => true

theorem loops_census :
    (Store.shopProgram.map fun root => requests.all (clearLoops root)) = some true := by kernel_rfl

theorem loops_clear (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) : Opportunities.ClearLoops built.program (Writer.notePath id) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains admitted).1]
    rfl
  have checked := loops_census
  rw [source] at checked
  exact List.all_eq_true.mp (Option.some.inj checked) id member

/-- A loop's pure exit carries no active note reservation. -/
theorem finish_zero (id : Nat) (root : NativeEff) (point : Point) (cursor : Val) :
    current id (loopFinishAt root point cursor) = 0 := by
  fun_cases loopFinishAt root point cursor
  all_goals rfl

/-- The actual next repeated body has no active cleanup note. -/
theorem next_zero (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (cursor : Val) (owned : At built.program point) :
    (match loopNextAt built.program point cursor with
      | .continue _ body | .finish body => current id body) = 0 := by
  fun_cases loopNextAt built.program point cursor
  case case1 test step body found answer =>
    have scope := childWith_at built.program point 0 cursor (loop_head_at built.program point test step body owned found)
    have bound := resolve_bound built admitted id member (point.childWith 0 cursor) scope
    have zero := Opportunities.loop_child_zero built.program (Writer.notePath id)
      (loops_clear built admitted id member) point test step body found
    have smaller := below_source id (point.path ++ [0])
    change current id (resolve built.program (point.childWith 0 cursor)) ≤ WriterPhase.below id (point.path ++ [0]) at bound
    dsimp only
    omega
  all_goals aesop (add norm simp [current, cata_prim, badShape, finish_zero])

/-- An actual loop reply cannot recreate a cleanup-note reservation. -/
theorem resume_zero (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (cursor value : Val) (owned : At built.program point) :
    (match loopResumeAt built.program point cursor value with
      | .continue _ body | .finish body => current id body) = 0 := by
  unfold loopResumeAt
  cases source : loopAt built.program point with
  | none => rfl
  | some row =>
    obtain ⟨test, step, body⟩ := row
    dsimp only
    cases evaluated : evalTerm (point.env ++ [cursor, value]) step with
    | none => rfl
    | some next => exact next_zero built admitted id member point next owned

/-- The native completed view retains repeated-body exclusion. -/
theorem interp_next_zero (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV)) (callback : EffName) (cursor : Val)
    (owned : NameAt built.program callback) :
    (match (interpAt built.program view built.table).loopEnter callback cursor with
      | .continue _ body | .finish body => current id body) = 0 := by
  cases callback
  case loop point => exact next_zero built admitted id member {point with completed := view} cursor owned
  all_goals rfl

theorem interp_resume_zero (built : Api.Built) (admitted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (view : List (FiberId × ExitV)) (callback : EffName) (cursor value : Val)
    (owned : NameAt built.program callback) :
    (match (interpAt built.program view built.table).loopResume callback cursor value with
      | .continue _ body | .finish body => current id body) = 0 := by
  cases callback
  case loop point => exact resume_zero built admitted id member {point with completed := view} cursor value owned
  all_goals rfl

/-- The existing iterator result counts only an actual future body and callback. -/
def iterMass (id : Nat) : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Nat
  | .resume body next => current id body + name id next
  | _ => 0

/-- Stored close callbacks contain no active writer before their finalizer starts. -/
theorem store_iter_zero (id : Nat) (callback : Name) (value : Val) :
    iterMass id (embedStep ((stores.iterNext callback value).2)) = 0 := by
  cases callback
  case closeSeq remaining exit captured =>
    cases remaining with
    | nil =>
      change iterMass id (embedStep (closeDone (captured ++ reasonsOfVal value))) = 0
      unfold closeDone
      split <;> rfl
    | cons fin rest =>
      change current id (embed (finProgram fin exit)) + 0 = 0
      rw [show current id (embed (finProgram fin exit)) = 0 from
        program_exact id (.finalizerOf fin exit)]
  case closeParDone =>
    change iterMass id (embedStep (closeDone (reasonsOfVal value))) = 0
    unfold closeDone
    split <;> rfl
  all_goals rfl

/-- Native iterators retain zero selected active writer reservation. -/
theorem interp_iter_zero (id : Nat) (root : NativeEff) (view : List (FiberId × ExitV))
    (table : RowTable) (callback : EffName) (value : Val) (owned : NameAt root callback) :
    iterMass id (((interpAt root view table).iterNext callback value).2) = 0 := by
  cases callback
  case gen point path bind => exact owned.elim
  case store stored => exact store_iter_zero id stored value
  all_goals rfl

end Test.Dogfood.Scenario.Atomic.WriterLoops
