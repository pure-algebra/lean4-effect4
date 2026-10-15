import Effect4.Laws.Program.FinalizerSuspensions
import Effect4.Laws.Program.FinalizerGeneratorRun
import Effect4.Laws.Program.CodeClosure.Interp

/-!
Concept: scope-lifetime-finalization R11.
Question: recursive callback debit for `once_placed_outside_census`.
Consumer: the full source frame invariant.
Generators split one reservation between the yielded body and its actual continuation.
Repeated loop bodies exclude the selected source through the existing placement census.
These local facts establish no progress or history bound.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace Effect4.Program.FinalizerSource
open Effect4 Effect4.Machine Effect4.Program

/-- Iterator results retain the annotations of their actual body and continuation. -/
def IterAt (q : List Nat) : IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Prop
  | .resume body next => CodeAt q body ∧ OrdinaryNameAt q next
  | _ => True

/-- An iterator divides its reservation between its next body and saved continuation. -/
def iterWeight (root : NativeEff) (q : List Nat) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode → Nat
  | .resume body next => current root q body + name q next
  | _ => 0

/-- The existing stored iterator closure embeds into the full source annotation. -/
theorem stored_iter_at (q : List Nat) (callback : Name) (value : Val)
    (held : CodeClosure.Slots.StoreNameAt (PointAt q) (fun _ => True) callback) :
    IterAt q (embedStep ((stores.iterNext callback value).2)) := by
  have closed := CodeClosure.Slots.store_iter_at (PointAt q) (fun _ => True) callback value held
  cases result : (stores.iterNext callback value).2 with
  | done value => trivial
  | halt cause => trivial
  | resume body next =>
    rw [result] at closed
    exact ⟨embedded_code q body closed.1, direct_name q (.store next) closed.2⟩

/-- Stored iterator callbacks retain release custody without an active source reservation. -/
theorem stored_iter_zero (root : NativeEff) (q : List Nat) (callback : Name) (value : Val) :
    iterWeight root q (embedStep ((stores.iterNext callback value).2)) = 0 := by
  cases callback
  case closeSeq remaining exit captured =>
    cases remaining with
    | nil =>
      change iterWeight root q (embedStep (closeDone (captured ++ reasonsOfVal value))) = 0
      unfold closeDone
      split <;> rfl
    | cons fin rest =>
      change current root q (embed (finProgram fin exit)) + 0 = 0
      rw [fin_program_zero, Nat.zero_add]
  case closeParDone =>
    change iterWeight root q (embedStep (closeDone (reasonsOfVal value))) = 0
    unfold closeDone
    split <;> rfl
  all_goals rfl

/-- The generator's existing statement walk produces the full iterator contract. -/
theorem generator_iter (root : NativeEff) (q : List Nat) (point : Point) (fuel : Nat)
    (pc : List Nat) (values folded : List Val) (counter : FinalizerGenerator.Counter pc)
    (held : PointAt q point) (placed : OncePlaced (.eff root) q = true) :
    IterAt q (runStmts root point fuel pc values folded).2 ∧
      iterWeight root q (runStmts root point fuel pc values folded).2 ≤
        FinalizerGenerator.remaining q (point.path ++ [0]) pc := by
  obtain ⟨closed, bound⟩ := FinalizerGenerator.run_budget root q point fuel pc values folded counter held placed
  generalize (runStmts root point fuel pc values folded).2 = result at closed bound ⊢
  cases result
  case resume body next =>
    cases next
    case gen next pc bind =>
      obtain ⟨path, params, counter, code⟩ := closed
      exact ⟨⟨code, point_same q point next params held, counter⟩, bound⟩
    all_goals exact closed.elim
  all_goals exact ⟨trivial, bound⟩

/-- Actual iterator invocation retains its source and spends its saved reservation. -/
theorem interp_iter (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (callback : EffName) (value : Val) (placed : OncePlaced (.eff root) q = true)
    (held : NameAt q callback) :
    IterAt q (((interpAt root completed table).iterNext callback value).2) ∧
      iterWeight root q (((interpAt root completed table).iterNext callback value).2) ≤ name q callback := by
  cases callback
  case gen point pc bind => exact generator_iter root q {point with completed} point.fuel pc _ [] held.2 held.1 placed
  case store callback => exact ⟨stored_iter_at q callback value held, Nat.le_of_eq (stored_iter_zero root q callback value)⟩
  all_goals exact ⟨trivial, Nat.zero_le _⟩

/-- Loop results retain the body chosen by the native cursor decision. -/
def LoopAt (q : List Nat) : LoopNext Val NCode → Prop
  | .continue _ body | .finish body => CodeAt q body

/-- The loop body's source reservation. -/
def loopWeight (root : NativeEff) (q : List Nat) : LoopNext Val NCode → Nat
  | .continue _ body | .finish body => current root q body

/-- A loop result exposes only a value or failure. -/
theorem loop_finish (root : NativeEff) (q : List Nat) (point : Point) (cursor : Val) :
    CodeAt q (loopFinishAt root point cursor) ∧ current root q (loopFinishAt root point cursor) = 0 := by
  fun_cases loopFinishAt root point cursor
  all_goals exact ⟨trivial, rfl⟩

/-- Native loop entry exposes no repeatedly usable selected source. -/
theorem loop_next (root : NativeEff) (q : List Nat) (point : Point) (cursor : Val)
    (placed : OncePlaced (.eff root) q = true) (held : PointAt q point) :
    LoopAt q (loopNextAt root point cursor) ∧ loopWeight root q (loopNextAt root point cursor) = 0 := by
  fun_cases loopNextAt root point cursor
  case case1 test step body found evaluated =>
    refine ⟨resolve_at root q _ held, ?_⟩
    have bound := resolve_le root q (point.childWith 0 cursor)
    change current root q (resolve root (point.childWith 0 cursor)) ≤ SourceScope.Opportunities.below q (point.path ++ [0]) at bound
    rw [SourceScope.Opportunities.loop_child_zero root q (FinalizerPlacement.clear_loops root q placed) point test step body found] at bound
    exact Nat.eq_zero_of_le_zero bound
  case case2 => exact loop_finish root q point cursor
  all_goals exact ⟨trivial, rfl⟩

/-- Native loop resumption reuses the same checked loop entry. -/
theorem loop_resume (root : NativeEff) (q : List Nat) (point : Point) (cursor answer : Val)
    (placed : OncePlaced (.eff root) q = true) (held : PointAt q point) :
    LoopAt q (loopResumeAt root point cursor answer) ∧ loopWeight root q (loopResumeAt root point cursor answer) = 0 := by
  unfold loopResumeAt
  cases found : loopAt root point with
  | none => exact ⟨trivial, rfl⟩
  | some row =>
    rcases row with ⟨test, step, body⟩
    dsimp only
    cases evaluated : evalTerm (point.env ++ [cursor, answer]) step with
    | none => exact ⟨trivial, rfl⟩
    | some next => exact loop_next root q point next placed held

/-- Actual loop entry changes only the completed-exit view of its point. -/
theorem interp_loop_enter (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (callback : EffName) (cursor : Val) (placed : OncePlaced (.eff root) q = true)
    (held : NameAt q callback) :
    LoopAt q ((interpAt root completed table).loopEnter callback cursor) ∧
      loopWeight root q ((interpAt root completed table).loopEnter callback cursor) = 0 := by
  cases callback
  case loop point => exact loop_next root q {point with completed} cursor placed held
  all_goals exact ⟨trivial, rfl⟩

/-- Actual loop resumption changes only the completed-exit view of its point. -/
theorem interp_loop_resume (root : NativeEff) (q : List Nat) (completed) (table : RowTable)
    (callback : EffName) (cursor answer : Val) (placed : OncePlaced (.eff root) q = true)
    (held : NameAt q callback) :
    LoopAt q ((interpAt root completed table).loopResume callback cursor answer) ∧
      loopWeight root q ((interpAt root completed table).loopResume callback cursor answer) = 0 := by
  cases callback
  case loop point => exact loop_resume root q {point with completed} cursor answer placed held
  all_goals exact ⟨trivial, rfl⟩

end Effect4.Program.FinalizerSource
