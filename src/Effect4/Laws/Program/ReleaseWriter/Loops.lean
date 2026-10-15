import Effect4.Laws.Program.ReleaseWriter.Suspensions

/-!
Concept: scope-lifetime-finalization R11.
Question: repeated bodies cannot recreate the selected direct release reservation.
Reach: source-owned loop and stored close-iterator callbacks of a direct-release source.
Consumers: the shared writer's frame return and native iteration debit for both crews.
The law establishes no loop termination or finalizer progress.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseWriter
open Effect4 Effect4.Machine Effect4.Program

/-- A loop's pure exit has no pending reference write. -/
theorem loop_finish_zero (target : Target) (root : NativeEff) (point : Point) (cursor : Val) :
    current target (loopFinishAt root point cursor) = 0 := by
  fun_cases loopFinishAt root point cursor
  all_goals rfl

/-- Every repeated body enters child zero, outside the selected release child. -/
theorem Source.loop_next_zero {target : Target} {root : NativeEff} (source : Source target root)
    (point : Point) (cursor : Val) :
    (match loopNextAt root point cursor with
      | .continue _ body | .finish body => current target body) = 0 := by
  fun_cases loopNextAt root point cursor
  case case1 test step body found answer =>
    have bounded := source.resolve_bound (point.childWith 0 cursor)
    change current target (resolve root (point.childWith 0 cursor)) ≤ leaf target (point.path ++ [0]) at bounded
    rw [leaf_child_zero target _ 0 (by decide)] at bounded
    exact Nat.eq_zero_of_le_zero bounded
  all_goals aesop (add norm simp [current, pair, cata_prim, badShape, loop_finish_zero])

/-- An actual loop reply re-enters the same excluded repeated body. -/
theorem Source.loop_resume_zero {target : Target} {root : NativeEff} (source : Source target root)
    (point : Point) (cursor value : Val) :
    (match loopResumeAt root point cursor value with
      | .continue _ body | .finish body => current target body) = 0 := by
  unfold loopResumeAt
  cases found : loopAt root point with
  | none => rfl
  | some row =>
    obtain ⟨test, step, body⟩ := row
    dsimp only
    cases evaluated : evalTerm (point.env ++ [cursor, value]) step with
    | none => rfl
    | some next => exact source.loop_next_zero point next

/-- The completed-exit view changes no repeated-body exclusion. -/
theorem Source.interp_next_zero {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV)) (callback : EffName) (cursor : Val) :
    (match (interpAt root view table).loopEnter callback cursor with
      | .continue _ body | .finish body => current target body) = 0 := by
  cases callback
  case loop point => exact source.loop_next_zero {point with completed := view} cursor
  all_goals rfl

/-- The completed-exit view changes no loop reply reservation. -/
theorem Source.interp_resume_zero {target : Target} {root : NativeEff} (source : Source target root)
    (table : RowTable) (view : List (FiberId × ExitV)) (callback : EffName) (cursor value : Val) :
    (match (interpAt root view table).loopResume callback cursor value with
      | .continue _ body | .finish body => current target body) = 0 := by
  cases callback
  case loop point => exact source.loop_resume_zero {point with completed := view} cursor value
  all_goals rfl

/-- An iterator result retains its actual next body and callback reservation. -/
def iterMass (target : Target) : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Nat
  | .resume body next => current target body + name target next
  | _ => 0

/-- Stored closing starts with dormant releases; each receives credit at its own later push. -/
theorem store_iter_zero (target : Target) (callback : Name) (value : Val) :
    iterMass target (embedStep ((stores.iterNext callback value).2)) = 0 := by
  cases callback
  case closeSeq remaining exit captured =>
    cases remaining with
    | nil =>
      change iterMass target (embedStep (closeDone (captured ++ reasonsOfVal value))) = 0
      unfold closeDone
      split <;> rfl
    | cons fin rest =>
      change current target (embed (finProgram fin exit)) + 0 = 0
      rw [show current target (embed (finProgram fin exit)) = 0 from
        Stored.program_exact target (.finalizerOf fin exit)]
  case closeParDone =>
    change iterMass target (embedStep (closeDone (reasonsOfVal value))) = 0
    unfold closeDone
    split <;> rfl
  all_goals rfl

/-- Every admitted native iterator retains zero pending direct-release writes. -/
theorem interp_iter_zero (target : Target) (root : NativeEff) (table : RowTable)
    (view : List (FiberId × ExitV)) (callback : EffName) (value : Val)
    (owned : SourceScope.NameAt root callback) :
    iterMass target (((interpAt root view table).iterNext callback value).2) = 0 := by
  cases callback
  case gen point path bind => exact owned.elim
  case store stored => exact store_iter_zero target stored value
  all_goals rfl

end Effect4.Program.ReleaseWriter
