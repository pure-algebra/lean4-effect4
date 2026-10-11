import Effect4.Laws.Program.ReleaseCustody.Evaluation

/-!
Concept: scope-lifetime-finalization, R11.
Question: native iterator and arm producers serve Execution.command_custody.
Reach: actual native callbacks, generator cursors, stored close iterators and loop cursors.
Limit: no source-use uniqueness, progress or host agreement follows.
Unlock: native arm debit and the full evaluator clause.
-/
set_option autoImplicit false
namespace Effect4.Program.ReleaseCustody.Producers
open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.ReleaseCustody.Control

/-- The current completed-exit view changes no callback credit.
Consumer: native value-arm debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interp_contA (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (value : Val) :
    currentCredits q ((interpAt root completed table).contA name value) ≤ nameCredits q name := by
  have producer := Evaluation.contA_credits q root
  cases name <;> dsimp only [interpAt]
  case cont p => exact producer (.cont {p with completed}) value
  case onValue p => exact producer (.onValue {p with completed}) value
  case releaseBody p exit previous => exact producer (.releaseBody {p with completed} exit previous) value
  all_goals exact producer _ value

/-- Every native cause callback carries no release registration credit.
Consumer: native cause-arm debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interp_contE (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (cause : CauseV) :
    currentCredits q ((interpAt root completed table).contE name cause) = 0 := by
  cases name <;> dsimp only [interpAt]
  all_goals exact Evaluation.contE_credits q root _ cause

/-- A stored iterator's reservation depends on its saved finalizers, not its answer cursor.
Consumer: native iterator-arm debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem iterator_future (q : List Nat) (name : EffName) (a b : Val) :
    futureCredits q (.iterator name a) = futureCredits q (.iterator name b) := by
  cases name
  case store stored => cases stored <;> rfl
  all_goals rfl

/-- A returned iterator body and its saved cursor split the iterator's credits.
Consumer: native iterator-arm debit in Execution.command_custody. -/
def iterCredits (q : List Nat) : IterStep EffName EffThunk Val Err Defect FiberId Ann → Nat
  | .resume body name => currentCredits q body + futureCredits q (.iterator name Val.unit)
  | _ => 0

/-- One actual source yield retains zero credits before its registration frame is pushed.
Consumer: runStmts_credits below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem yieldOf_credits (q : List Nat) (root : NativeEff) (p : Point) (e : NativeEff)
    (bind : Bool) (fuel : Nat) (pc : List Nat) (env folded : List Val)
    (recursive : ∀ pc env folded, iterCredits q (runStmts root p fuel pc env folded).2 = 0) :
    iterCredits q (runStmts.yieldOf root p e bind fuel pc env folded).2 = 0 := by
  unfold runStmts.yieldOf
  dsimp only
  have compiled := compile_credits q e
    {p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1}
  generalize h : compileEff e
    {p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1} = code at compiled ⊢
  cases code <;> dsimp only
  case success value => exact recursive _ _ _
  case failure => rfl
  all_goals simp only [iterCredits, futureCredits, Nat.add_zero]
  all_goals exact compiled

/-- Source generator yields create registration templates without pre-existing credits.
Consumer: interp_iter below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem runStmts_credits (q : List Nat) (root : NativeEff) (p : Point) (fuel : Nat)
    (pc : List Nat) (env folded : List Val) :
    iterCredits q (runStmts root p fuel pc env folded).2 = 0 := by
  induction fuel generalizing pc env folded with
  | zero =>
    simp only [runStmts, iterCredits, frontier, currentCredits, futureCredits, Nat.zero_add]
  | succ fuel ih =>
    unfold runStmts
    cases hb : blockAt root p pc with
    | none => rfl
    | some block =>
      cases block with
      | nil =>
        cases he : blockExit root p pc env with
        | none => rfl
        | some next => exact ih _ _ _
      | cons statement rest =>
        cases statement <;> dsimp only
        case bindYield e => exact yieldOf_credits q root p e true fuel pc env folded ih
        case yieldDiscard e => exact yieldOf_credits q root p e false fuel pc env folded ih
        case ret term =>
          cases hv : evalTerm env term <;> rfl
        case ifElse test yes no =>
          cases hv : evalTerm env test with
          | none => rfl
          | some value =>
            cases value <;> dsimp (config := { failIfUnchanged := false }) only
            case bool condition => cases condition <;> exact ih _ _ _
            all_goals rfl
        case whileTrue body => exact ih _ _ _
        case breakLoop =>
          cases hl : loopExit root (pc.length + 1) p pc env with
          | none => rfl
          | some next => exact ih _ _ _
/-- A stored close iterator splits its first finalizer from the residual close order.
Consumer: interp_iter below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem closeSeq_credits (q : List Nat) (order : List FinName) (exit : ExitV)
    (captured : List (Reason Err Defect FiberId Ann)) (value : Val) :
    iterCredits q (embedStep (closeSeqStep order exit captured value)) ≤ orderCredits q order := by
  cases order with
  | nil =>
    change iterCredits q (embedStep (closeDone (captured ++ reasonsOfVal value))) ≤ 0
    unfold closeDone
    split <;> exact Nat.le_refl _
  | cons fin rest =>
    change iterCredits q (embedStep (.resume (.exitFrame (finProgram fin exit))
      (.closeSeq rest exit (captured ++ reasonsOfVal value)))) ≤ orderCredits q (fin :: rest)
    simp only [embedStep, embed, iterCredits, currentCredits, futureCredits,
      fin_program_credits, orderCredits, List.countP_cons, credit, Nat.add_comm]
    exact Nat.le_refl _

/-- Every native iterator transfers only credits already present in its saved name.
Consumer: native iterator-arm debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interp_iter (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (value : Val) :
    iterCredits q ((interpAt root completed table).iterNext name value).2 ≤
      futureCredits q (.iterator name Val.unit) := by
  cases name
  case gen p pc bind =>
    change iterCredits q (runStmts root {p with completed} p.fuel pc
      (if bind then p.env ++ [value] else p.env) []).2 ≤ 0
    rw [runStmts_credits]
    exact Nat.le_refl _
  case store stored =>
    cases stored
    case closeSeq order exit captured => exact closeSeq_credits q order exit captured value
    case closeParDone =>
      change iterCredits q (embedStep (closeDone (reasonsOfVal value))) ≤ 0
      unfold closeDone
      split <;> exact Nat.le_refl _
    all_goals exact Nat.le_refl _
  all_goals exact Nat.le_refl _

/-- Native loop callbacks produce source code whose registrations are not pushed yet.
Consumer: native loop-arm debit in Execution.command_custody. -/
def loopCredits (q : List Nat) : LoopNext Val NCode → Nat
  | .continue _ body | .finish body => currentCredits q body

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loopFinish_credits (q : List Nat) (root : NativeEff) (p : Point) (cursor : Val) :
    currentCredits q (loopFinishAt root p cursor) = 0 := by
  fun_cases loopFinishAt root p cursor <;> rfl

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loopNext_credits (q : List Nat) (root : NativeEff) (p : Point) (cursor : Val) :
    loopCredits q (loopNextAt root p cursor) = 0 := by
  fun_cases loopNextAt root p cursor <;>
    simp only [loopCredits, Evaluation.resolve_credits, loopFinish_credits, currentCredits, badShape]

@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem loopResume_credits (q : List Nat) (root : NativeEff) (p : Point) (cursor answer : Val) :
    loopCredits q (loopResumeAt root p cursor answer) = 0 := by
  fun_cases loopResumeAt root p cursor answer
  case case1 => exact loopNext_credits q root p _
  all_goals rfl

/-- The actual completed-exit loop callback creates no prior registration credits.
Consumer: native loop-arm debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem interp_loopResume (q : List Nat) (root : NativeEff) (completed : List (FiberId × ExitV))
    (table : RowTable) (name : EffName) (cursor answer : Val) :
    loopCredits q ((interpAt root completed table).loopResume name cursor answer) = 0 := by
  cases name
  case loop p => exact loopResume_credits q root {p with completed} cursor answer
  all_goals rfl

/-- Stored asynchronous cancellation contains administrative commands only.
Consumer: native cancellation callback bound below. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem store_cancel (q : List Nat) (name : Name) : currentCredits q (embed (cancelProgram name)) = 0 := by
  fun_cases cancelProgram name <;>
    simp only [embed, currentCredits, opCredits, Names.actionCredits]

/-- Actual asynchronous cancellation introduces no release registration credit.
Consumer: native cause-arm debit in Execution.command_custody. -/
@[semantics "scope-lifetime-finalization" (requirement := R11)]
theorem cancel (q : List Nat) (name : EffName) : currentCredits q (cancelProgramOf name) = 0 := by
  fun_cases cancelProgramOf name <;>
    simp only [currentCredits, opCredits, store_cancel]

end Effect4.Program.ReleaseCustody.Producers
