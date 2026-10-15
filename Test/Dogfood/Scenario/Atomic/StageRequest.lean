import Test.Dogfood.Scenario.Atomic.StageHead
import Effect4.Laws.Program.AnswerSlots.Points

/-!
Concept: store-typing R4, serving `Atomic.Store.shop_stages`.
Consumer: the running request's decision and deposit continuation producers.
The finite source certificates retain actual binders and literal return branches.
The saved callback uses the same stage world that certifies its delivered answer.
No command history or progress follows from this local source contract.
-/
set_option autoImplicit false
namespace Test.Dogfood.Scenario.Atomic.StageRequest
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open StageWorld

/-- The selected admitted source branch contains the deposit binder. -/
def admittedPath (id : Nat) : List Nat := SourcePaths.requestPath id ++ [0, 1, 0]

/-- The rejected source branch returns its literal decision. -/
def rejectedPath (id : Nat) : List Nat := SourcePaths.requestPath id ++ [0, 1, 1]

/-- The body after a deposit either returns admission or plants its downstream failure. -/
def Tail : NativeEff → Prop
  | .fail _ => True
  | .succeed (.lit (.bool true)) => True
  | _ => False

def tailCheck : NativeEff → Bool
  | .fail _ => true
  | .succeed (.lit (.bool true)) => true
  | _ => false

/-- The actual source-site reader retains the deposit term and its following body. -/
def admittedSite (root : NativeEff) (id : Nat) : Bool :=
  match SourceScope.levelAt (.eff root) 0 (admittedPath id), Node.at_ (.eff root) (admittedPath id) with
  | some level, some (.eff (.bind (.perform (.refModifyWith term) (.var 1)) tail)) =>
      term == Store.depositAt id level && tailCheck tail
  | _, _ => false

def rejectedSite (root : NativeEff) (id : Nat) : Bool :=
  match Node.at_ (.eff root) (rejectedPath id) with
  | some (.eff (.succeed (.lit (.bool false)))) => true
  | _ => false

/-- Every admitted source branch deposits exactly its own identity before its tail. -/
theorem admitted_census :
    (Store.shopProgram.map fun root => requests.all (admittedSite root)) = some true := by
  kernel_rfl

/-- Every rejected source branch returns false without a deposit operation. -/
theorem rejected_census :
    (Store.shopProgram.map fun root => requests.all (rejectedSite root)) = some true := by
  kernel_rfl

/-- A positive tail reader recovers the exact source shape that the compiler consumes. -/
theorem tail_read (tail : NativeEff) (checked : tailCheck tail = true) : Tail tail := by
  unfold tailCheck at checked
  split at checked
  · exact True.intro
  · exact True.intro
  · cases checked

/-- Successful admission retains the actual selected source bodies and their lexical depth. -/
theorem branch_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    (∃ level tail, SourceScope.levelAt (.eff built.program) 0 (admittedPath id) = some level ∧
      Node.at_ (.eff built.program) (admittedPath id) =
        some (.eff (.bind (.perform (.refModifyWith (Store.depositAt id level)) (.var 1)) tail)) ∧ Tail tail) ∧
    Node.at_ (.eff built.program) (rejectedPath id) = some (.eff (.succeed (.lit (.bool false)))) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have yes := admitted_census
  have no := rejected_census
  rw [source] at yes no
  have first := List.all_eq_true.mp (Option.some.inj yes) id member
  have second := List.all_eq_true.mp (Option.some.inj no) id member
  constructor
  · unfold admittedSite at first
    split at first
    · rename_i level term tail lexical found
      obtain ⟨termEq, tailOk⟩ := Bool.and_eq_true_iff.mp first
      have same := beq_iff_eq.mp termEq
      subst term
      exact ⟨level, tail, lexical, found, tail_read tail tailOk⟩
    · cases first
  · unfold rejectedSite at second
    split at second
    · assumption
    · cases second

/-- The pre-decision source binder ignores the scheduler's yielded answer. -/
def admitPath (id : Nat) : List Nat := SourcePaths.requestPath id ++ [0, 0]

def admitSite (root : NativeEff) (id : Nat) : Bool :=
  match Node.at_ (.eff root) (admitPath id) with
  | some (.eff (.bind (.yieldNow 0) _)) => true
  | _ => false

/-- All six requests yield before their single admission operation. -/
theorem admit_census :
    (Store.shopProgram.map fun root => requests.all (admitSite root)) = some true := by
  kernel_rfl

theorem admit_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    ∃ rest, Node.at_ (.eff built.program) (admitPath id) = some (.eff (.bind (.yieldNow 0) rest)) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have census := admit_census
  rw [source] at census
  have selected := List.all_eq_true.mp (Option.some.inj census) id member
  unfold admitSite at selected
  split at selected
  · rename_i rest found
    exact ⟨rest, found⟩
  · cases selected

/-- The immutable source environment names the window, account and cleanup cells. -/
def Cells (env : List Val) : Prop :=
  AnswerSlots.Prefix [.cell ⟨0⟩, .cell ⟨1⟩, .cell ⟨2⟩] env

/-- Actual pre-decision source code retains its ignored yield class through the real callback. -/
theorem admit_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (path : point.path = admitPath id)
    (sourceOwned : SourceScope.At built.program point) (cells : Cells point.env)
    (world : StageWorld.World) (waiting : world.stages id = .waiting) :
    StageGraph.CodeAt built.program built.table id world (.decision id) (resolve built.program point) := by
  obtain ⟨rest, found⟩ := admit_at built accepted id member
  rw [← path] at found
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    apply StageGraph.CodeAt.bound (show StageGraph.Owns id (.waiting id) from rfl)
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ available =>
        simp only [compileEff, childFuel]
        exact .yielding waiting
    · intro nextWorld future view answer good
      let refreshed : Point := {point with completed := view}
      let next := refreshed.childWith 1 answer
      change StageGraph.CodeAt built.program built.table id nextWorld (.decision id) (resolve built.program next)
      have node : Node.at_ (.eff built.program) refreshed.path = some (.eff (.bind (.yieldNow 0) rest)) := found
      have sourceNext : SourceScope.At built.program next :=
        (SourceScope.bind_contA built.program refreshed _ rest answer node sourceOwned).2
      have cellsNext : Cells next.env := AnswerSlots.childWith cells 1 answer
      cases nextFuel : next.fuel with
      | zero =>
        rw [SourceScope.resolve_at _ _ _ (Agreement.at_childWith node 1 answer), Agreement.compileEff_at_zero _ nextFuel]
        exact .frontier nextFuel
      | succ available =>
        apply StageGraph.decision_source built accepted id member next available _ nextFuel sourceNext
          (cellsNext.read 0 (by decide)) nextWorld good
        simp only [next, refreshed, Point.childWith, path, admitPath, StageSource.decisionPath, List.append_assoc, List.cons_append, List.nil_append]
    · intro nextWorld future cause good
      exact good

/-- Any real failure after a deposit retains that request's deposited body class. -/
theorem deposited_failure (world : StageWorld.World) (id : Nat)
    (deposited : world.stages id = .deposited) (cause : CauseV) : CauseAt world (.body id) cause :=
  fun _ _ _ => deposited

/-- The actual post-deposit source body retains its body answer class at every fuel. -/
theorem tail_code (root : NativeEff) (table : RowTable) (world : StageWorld.World) (id : Nat)
    (deposited : world.stages id = .deposited) (point : Point) (tail : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff tail)) (shape : Tail tail) :
    StageGraph.CodeAt root table id world (.body id) (resolve root point) := by
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    unfold Tail at shape
    split at shape
    · rename_i term
      simp only [compileEff, amount]
      cases evaluated : evalTerm point.env term with
      | none => exact .failure (deposited_failure world id deposited _)
      | some value => exact .failure (deposited_failure world id deposited _)
    ·
      simp only [compileEff, amount, evalTerm]
      exact .success deposited
    · exact shape.elim

/-- A deposit answer funds exactly its owner's post-deposit source continuation. -/
theorem deposit_value (world : StageWorld.World) (id : Nat) (answer : Val)
    (good : ValueAt world (.deposit id) answer) : world.stages id = .deposited := by
  cases answer
  all_goals aesop (add norm simp [ValueAt])

/-- The real admitted branch installs its deposit callback with the matching request class. -/
theorem admitted_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point)
    (path : point.path = admittedPath id) (sourceOwned : SourceScope.At built.program point)
    (captured : point.env[1]? = some (.cell ⟨1⟩)) (world : StageWorld.World)
    (admitted : world.stages id = .admitted) :
    StageGraph.CodeAt built.program built.table id world (.body id) (resolve built.program point) := by
  obtain ⟨⟨level, tail, lexical, found, shape⟩, rejected⟩ := branch_at built accepted id member
  rw [← path] at lexical found
  have same : level = point.env.length := Option.some.inj (lexical.symm.trans sourceOwned)
  subst level
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    apply StageGraph.CodeAt.bound (show StageGraph.Owns id (.deposit id) from rfl)
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ available =>
        have handle : (point.child 0).env[1]? = some (.cell ⟨1⟩) := captured
        simp only [compileEff, childFuel, evalTerm, handle]
        exact .deposit admitted
    · intro nextWorld future view answer good
      change StageGraph.CodeAt built.program built.table id nextWorld (.body id)
        (resolve built.program (({point with completed := view} : Point).childWith 1 answer))
      exact tail_code built.program built.table nextWorld id (deposit_value nextWorld id answer good)
        _ tail (Agreement.at_childWith found 1 answer) shape
    · intro nextWorld future cause good reason belongs typed
      exact False.elim (good reason belongs typed)


/-- The actual rejected source branch returns its matching body decision at every fuel. -/
theorem rejected_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (path : point.path = rejectedPath id)
    (world : StageWorld.World) (rejected : world.stages id = .rejected) :
    StageGraph.CodeAt built.program built.table id world (.body id) (resolve built.program point) := by
  have found := (branch_at built accepted id member).2
  rw [← path] at found
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    simp only [compileEff, amount, evalTerm]
    exact .success rejected

/-- A selected source branch retains the same lexical length as its actual parent select. -/
theorem select_scope (root : NativeEff) (point : Point) (term : Term) (yes no : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff (.select term .bool yes no)))
    (held : SourceScope.At root point) (selected : Bool) :
    SourceScope.At root (point.child (cond selected 0 1)) := by
  cases selected
  all_goals unfold SourceScope.At
  all_goals change SourceScope.levelAt (.eff root) 0 (point.path ++ [_]) = some point.env.length
  all_goals rw [SourceScope.levelAt_suffix _ _ point.path _ 0 found, held]
  all_goals rfl

/-- The actual branch suspension consumes precisely the delivered stage-certified Boolean. -/
theorem branch_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (world : StageWorld.World) (selected : Bool)
    (path : point.path = StageSource.branchPath id) (sourceOwned : SourceScope.At built.program point)
    (argument : point.env[StageSource.forkBinder id]? = some (.bool selected))
    (captured : point.env[1]? = some (.cell ⟨1⟩))
    (good : ValueAt world (.decision id) (.bool selected)) :
    StageGraph.CodeAt built.program built.table id world (.body id) (resolve built.program point) := by
  obtain ⟨yes, no, found⟩ := StageSource.branch_at built accepted id member
  rw [← path] at found
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_select _ _ _ _ amount]
    apply StageGraph.CodeAt.suspended
    intro view
    let refreshed : Point := {point with completed := view}
    have current : Node.at_ (.eff built.program) refreshed.path = some (.eff (.select (.var (StageSource.forkBinder id)) .bool yes no)) := found
    have sourceCurrent : SourceScope.At built.program refreshed := sourceOwned
    have actual := StageSource.branch_step built accepted id member world refreshed selected fuel amount path argument good
    change StageGraph.CodeAt built.program built.table id world (.body id) (suspendBodyAt built.program (.body refreshed))
    rw [actual.1]
    cases selected with
    | false =>
      apply rejected_code built accepted id member (refreshed.child 1) _ world good
      simp only [Point.child, refreshed, path, StageSource.branchPath, rejectedPath, List.append_assoc, List.cons_append, List.nil_append]
    | true =>
      apply admitted_code built accepted id member (refreshed.child 0) _
        (select_scope built.program refreshed _ yes no current sourceCurrent true) captured world good
      simp only [Point.child, refreshed, path, StageSource.branchPath, admittedPath, List.append_assoc, List.cons_append, List.nil_append]


/-- The request body binds its admission before the exact Boolean selection. -/
def bodyPath (id : Nat) : List Nat := SourcePaths.requestPath id ++ [0]

def bodySite (root : NativeEff) (id : Nat) : Bool :=
  match SourceScope.levelAt (.eff root) 0 (bodyPath id), Node.at_ (.eff root) (bodyPath id) with
  | some level, some (.eff (.bind _ (.select (.var depth) .bool _ _))) =>
      decide (level = StageSource.forkBinder id) && decide (depth = StageSource.forkBinder id)
  | _, _ => false

/-- Actual source lexical levels place the decision exactly in its tested binder slot. -/
theorem body_census :
    (Store.shopProgram.map fun root => requests.all (bodySite root)) = some true := by
  kernel_rfl

theorem body_at (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) :
    ∃ first yes no, SourceScope.levelAt (.eff built.program) 0 (bodyPath id) = some (StageSource.forkBinder id) ∧
      Node.at_ (.eff built.program) (bodyPath id) =
        some (.eff (.bind first (.select (.var (StageSource.forkBinder id)) .bool yes no))) := by
  have source : Store.shopProgram = some built.program := by
    unfold Store.shopProgram
    rw [(Api.Author.build_retains accepted).1]
    rfl
  have census := body_census
  rw [source] at census
  have selected := List.all_eq_true.mp (Option.some.inj census) id member
  unfold bodySite at selected
  split at selected
  · rename_i level first depth yes no lexical found
    obtain ⟨sameLevel, sameDepth⟩ := Bool.and_eq_true_iff.mp selected
    have one := of_decide_eq_true sameLevel
    have two := of_decide_eq_true sameDepth
    subst level
    subst depth
    exact ⟨first, yes, no, lexical, found⟩
  · cases selected

/-- An actual returned decision supplies its tested Boolean and its same-world stage. -/
theorem decision_value (world : StageWorld.World) (id : Nat) (answer : Val)
    (good : ValueAt world (.decision id) answer) :
    ∃ selected, answer = .bool selected ∧ ValueAt world (.decision id) (.bool selected) := by
  cases answer
  all_goals aesop (add norm simp [ValueAt])

/-- The actual body binder connects a waiting request to its own decision and selected branch. -/
theorem body_code (built : Api.Built) (accepted : Api.Author.build (shop .none) = .ok built)
    (id : Nat) (member : id ∈ requests) (point : Point) (path : point.path = bodyPath id)
    (sourceOwned : SourceScope.At built.program point) (cells : Cells point.env)
    (world : StageWorld.World) (waiting : world.stages id = .waiting) :
    StageGraph.CodeAt built.program built.table id world (.body id) (resolve built.program point) := by
  obtain ⟨first, yes, no, lexical, found⟩ := body_at built accepted id member
  rw [← path] at lexical found
  have depth : point.env.length = StageSource.forkBinder id :=
    (Option.some.inj (lexical.symm.trans sourceOwned)).symm
  rw [SourceScope.resolve_at _ _ _ found]
  cases amount : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ amount]
    exact .frontier amount
  | succ fuel =>
    rw [Agreement.compileEff_bind _ _ amount]
    apply StageGraph.CodeAt.bound (show StageGraph.Owns id (.decision id) from rfl)
    · rw [← SourceScope.resolve_at built.program (point.child 0) first (Agreement.at_child found 0)]
      apply admit_code built accepted id member (point.child 0) _ _ cells world waiting
      · simp only [Point.child, path, bodyPath, admitPath, List.append_assoc, List.cons_append, List.nil_append]
      · unfold SourceScope.At
        change SourceScope.levelAt (.eff built.program) 0 (point.path ++ [0]) = some point.env.length
        rw [SourceScope.levelAt_suffix _ _ point.path [0] 0 found, sourceOwned]
        rfl
    · intro nextWorld future view answer good
      obtain ⟨selected, rfl, decision⟩ := decision_value nextWorld id answer good
      let refreshed : Point := {point with completed := view}
      let next := refreshed.childWith 1 (.bool selected)
      have node : Node.at_ (.eff built.program) refreshed.path =
          some (.eff (.bind first (.select (.var (StageSource.forkBinder id)) .bool yes no))) := found
      have scope : SourceScope.At built.program next :=
        (SourceScope.bind_contA built.program refreshed _ _ (.bool selected) node sourceOwned).2
      have prefixHeld : Cells next.env := AnswerSlots.childWith cells 1 (.bool selected)
      change StageGraph.CodeAt built.program built.table id nextWorld (.body id) (resolve built.program next)
      apply branch_code built accepted id member next nextWorld selected _ scope
        (StageSource.decision_argument id refreshed selected depth) (prefixHeld.read 1 (by decide)) decision
      simp only [next, refreshed, Point.childWith, path, bodyPath, StageSource.branchPath, List.append_assoc, List.cons_append, List.nil_append]
    · intro nextWorld future cause good reason belongs typed
      exact False.elim (good reason belongs typed)

end Test.Dogfood.Scenario.Atomic.StageRequest
