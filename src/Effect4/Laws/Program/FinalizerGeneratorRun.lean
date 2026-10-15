import Effect4.Laws.Program.FinalizerGeneratorPC
import Effect4.Laws.Program.FinalizerSyntax

/-!
Concept: scope-lifetime-finalization R11.
Question: native generator producers of `once_placed_outside_census`.
Consumer: full source callback debit through the existing iterator result.
The source reservation counts the yielded code and its later generator continuation.
No source progress or whole-history bound follows from this local producer.
-/
set_option autoImplicit false
namespace Effect4.Program.FinalizerGenerator
open Effect4 Effect4.Machine Effect4.Program
open SourceScope.Opportunities

/-- The actual statement walker returns only its own valid generator continuation. -/
def ResultAt (q : List Nat) (point : Point) : IterStep EffName EffThunk Val Err Defect FiberId Ann → Prop
  | .resume code (.gen next pc _) => next.path = point.path ∧ next.params = point.params ∧
      Counter pc ∧ FinalizerSource.CodeAt q code
  | .resume _ _ => False
  | _ => True

/-- A yielded native body and its saved generator continuation share one source reservation. -/
def resultWeight (root : NativeEff) (q : List Nat) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .resume code (.gen point pc _) =>
      FinalizerSource.current root q code + remaining q (point.path ++ [0]) pc
  | .resume code _ => FinalizerSource.current root q code
  | _ => 0

/-- A real yielded effect occupies the statement's existing two-child source address.
Consumer: the yielded-code compiler bound in `yield_budget`. -/
theorem yield_found (root : NativeEff) (point : Point) (pc : List Nat)
    (effect : NativeEff) (rest : Stmts NativeOp) (bind : Bool)
    (found : blockAt root point pc = some (.cons (if bind then .bindYield effect else .yieldDiscard effect) rest)) :
    Node.at_ (.eff root) (point.path ++ [0] ++ pc ++ [0, 0]) = some (.eff effect) := by
  unfold blockAt at found
  split at found
  · rename_i statements located
    have equal := Option.some.inj found
    cases equal
    rw [Node.at_append, located]
    cases bind <;> rfl
  · cases found

/-- One actual yielded effect splits its source reservation from the later continuation.
Consumer: the two yield cases of the full statement-walker producer. -/
theorem yield_budget (root : NativeEff) (q : List Nat) (point : Point) (effect : NativeEff)
    (bind : Bool) (fuel : Nat) (pc : List Nat) (values folded : List Val)
    (rest : Stmts NativeOp) (held : Counter pc) (parameters : FinalizerSource.PointAt q point)
    (found : blockAt root point pc = some (.cons (if bind then .bindYield effect else .yieldDiscard effect) rest))
    (recursive : ∀ next values folded, Counter next →
      ResultAt q point (runStmts root point fuel next values folded).2 ∧
        resultWeight root q (runStmts root point fuel next values folded).2 ≤
          remaining q (point.path ++ [0]) next) :
    ResultAt q point (runStmts.yieldOf root point effect bind fuel pc values folded).2 ∧
      resultWeight root q (runStmts.yieldOf root point effect bind fuel pc values folded).2 ≤
        remaining q (point.path ++ [0]) pc := by
  have location := yield_found root point pc effect rest bind found
  have compiled := FinalizerSource.compile_le root q effect
    {point with path := point.path ++ [0] ++ pc ++ [0, 0], env := values, fuel := fuel + 1} location
  have annotated := FinalizerSource.compile_at root q effect
    {point with path := point.path ++ [0] ++ pc ++ [0, 0], env := values, fuel := fuel + 1} location parameters
  unfold runStmts.yieldOf
  dsimp only
  generalize actual : compileEff effect
    {point with path := point.path ++ [0] ++ pc ++ [0, 0], env := values, fuel := fuel + 1} = code at compiled annotated ⊢
  cases code
  case success value =>
    obtain ⟨typed, bounded⟩ := recursive (pc ++ [1]) _ _ (Counter.append_next pc held)
    exact ⟨typed, Nat.le_trans bounded (remaining_descend q (point.path ++ [0]) pc [1])⟩
  case failure => exact ⟨True.intro, Nat.zero_le _⟩
  all_goals dsimp only [ResultAt, resultWeight]
  all_goals refine ⟨⟨rfl, rfl, Counter.append_next pc held, annotated⟩, ?_⟩
  all_goals
    exact Nat.le_trans
      (Nat.add_le_add_right compiled (remaining q (point.path ++ [0]) (pc ++ [1])))
      (yield_split q (point.path ++ [0]) pc)

/-- A successful block lookup retains its actual source node.
Consumer: actual exhausted-block redirects in `run_budget`. -/
theorem block_found (root : NativeEff) (point : Point) (pc : List Nat)
    (statements : Stmts NativeOp) (found : blockAt root point pc = some statements) :
    Node.at_ (.eff root) (point.path ++ [0] ++ pc) = some (.stmts statements) := by
  unfold blockAt at found
  split at found
  · rename_i actual located
    cases Option.some.inj found
    exact located
  · cases found

/-- The complete native statement walker retains its source and continuation reservation.
Consumer: the unrestricted generator iterator callback debit. -/
theorem run_budget (root : NativeEff) (q : List Nat) (point : Point) (fuel : Nat)
    (pc : List Nat) (values folded : List Val) (held : Counter pc)
    (parameters : FinalizerSource.PointAt q point) (placed : OncePlaced (.eff root) q = true) :
    ResultAt q point (runStmts root point fuel pc values folded).2 ∧
      resultWeight root q (runStmts root point fuel pc values folded).2 ≤
        remaining q (point.path ++ [0]) pc := by
  induction fuel generalizing pc values folded with
  | zero =>
    unfold runStmts
    refine ⟨⟨rfl, rfl, held, parameters⟩, ?_⟩
    change 0 + remaining q (point.path ++ [0]) pc ≤ remaining q (point.path ++ [0]) pc
    exact Nat.le_of_eq (Nat.zero_add _)
  | succ fuel ih =>
    unfold runStmts
    cases block : blockAt root point pc with
    | none => exact ⟨True.intro, Nat.zero_le _⟩
    | some statements =>
      cases statements with
      | nil =>
        cases exited : blockExit root point pc values with
        | none => exact ⟨True.intro, Nat.zero_le _⟩
        | some next =>
          obtain ⟨valid, debit⟩ := block_exit_remaining root q point pc values next.1 next.2 held placed
            (block_found root point pc .nil block) exited
          obtain ⟨typed, bounded⟩ := ih next.1 next.2 folded valid
          exact ⟨typed, Nat.le_trans bounded debit⟩
      | cons statement rest =>
        dsimp only
        cases statement with
        | bindYield effect =>
          exact yield_budget root q point effect true fuel pc values folded rest held parameters block ih
        | yieldDiscard effect =>
          exact yield_budget root q point effect false fuel pc values folded rest held parameters block ih
        | ret term =>
          dsimp only
          split
          all_goals exact ⟨True.intro, Nat.zero_le _⟩
        | ifElse test yes no =>
          dsimp only
          split
          · obtain ⟨typed, bounded⟩ := ih (pc ++ [0, 0]) values folded (Counter.append_block pc held 0)
            exact ⟨typed, Nat.le_trans bounded (remaining_descend q (point.path ++ [0]) pc [0, 0])⟩
          · obtain ⟨typed, bounded⟩ := ih (pc ++ [0, 1]) values folded (Counter.append_block pc held 1)
            exact ⟨typed, Nat.le_trans bounded (remaining_descend q (point.path ++ [0]) pc [0, 1])⟩
          · exact ⟨True.intro, Nat.zero_le _⟩
        | whileTrue body =>
          obtain ⟨typed, bounded⟩ := ih (pc ++ [0, 0]) values folded (Counter.append_block pc held 0)
          exact ⟨typed, Nat.le_trans bounded (remaining_descend q (point.path ++ [0]) pc [0, 0])⟩
        | breakLoop =>
          cases exited : loopExit root (pc.length + 1) point pc values with
          | none => exact ⟨True.intro, Nat.zero_le _⟩
          | some next =>
            obtain ⟨valid, debit⟩ := loop_exit_remaining root q (point.path ++ [0]) (pc.length + 1)
              point pc values next.1 next.2 held exited
            obtain ⟨typed, bounded⟩ := ih next.1 next.2 folded valid
            exact ⟨typed, Nat.le_trans bounded debit⟩

end Effect4.Program.FinalizerGenerator
