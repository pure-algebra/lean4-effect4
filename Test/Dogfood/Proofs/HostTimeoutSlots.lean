import Test.Dogfood.Proofs.HostTimeoutSource

/-!
# Lexical value assertions for every timeout source effect

Placement: host-session-protocol, R6, the source-slot assertion of `stale_never_applies` clause four.
Consumer: the native command assertion and its successful source case.
Every effect location has its own lexical environment and expected successful value.
The cell and log-read slots stay arbitrary; only body-bearing slots require membership.
The cleanup and retry count claims still require separate heap assertions.
The assertions describe proof positions, rather than stored program syntax.
The source theorem does not establish that every reachable machine holds these assertions.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Proofs.HostTimeoutSlots
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSource

/-- The successful values expected at the concrete source positions. -/
inductive Kind
  | any | unit | nat | cell (key : Nat) | body | result

/-- Source results retain body membership while allowing arbitrary failure values. -/
inductive ValueAt (B : List Val) : Kind → Val → Prop
  | any (value : Val) : ValueAt B .any value
  | unit : ValueAt B .unit .unit
  | nat (n : Nat) : ValueAt B .nat (.nat n)
  | cell (key : Nat) : ValueAt B (.cell key) (Val.cell ⟨key⟩)
  | body {value : Val} (member : value ∈ B) : ValueAt B .body value
  | answered {value : Val} (member : value ∈ B) :
      ValueAt B .result (.list [.some value, .none])
  | failed (error : Val) : ValueAt B .result (.list [.none, .some error])
  | empty : ValueAt B .result (.list [.none, .none])

/-- Failures cannot introduce a successful body at any expected source result. -/
def ExitAt (B : List Val) (kind : Kind) : ExitV → Prop
  | .success value => ValueAt B kind value
  | .failure _ => True

/-- The three lexical cell slots; provenance does not inspect their stored values. -/
def cells (a b c : Val) : List Val := [a, b, c]

/-- A running loop body starts with an empty answer column. -/
def running (a b c : Val) (n delay : Nat) (error : Val) : List Val :=
  cells a b c ++ [cursor n delay .none error]

/-- The delay's answer precedes the attempt, handler and finalizer bindings. -/
def ready (a b c : Val) (n delay : Nat) (error : Val) : List Val :=
  running a b c n delay error ++ [.unit]

/-- The case list follows the generated complete source census.
Body-bearing slots carry membership in the current applied-body prefix. -/
inductive EnvAt (B : List Val) : List Nat → List Val → Prop
  | start   : EnvAt B [] ([])
  | countMake   : EnvAt B [0] ([])
  | endedMakeBind (a : Val) : EnvAt B [1] ([a])
  | endedMake (a : Val) : EnvAt B [1,0] ([a])
  | completedMakeBind (a b : Val) : EnvAt B [1,1] ([a, b])
  | completedMake (a b : Val) : EnvAt B [1,1,0] ([a, b])
  | finishBind (a b c : Val)   : EnvAt B [1,1,1] (cells a b c)
  | loop (a b c : Val)   : EnvAt B [1,1,1,0] (cells a b c)
  | iteration (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0] (running a b c n delay error)
  | delaySelect (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,0] (running a b c n delay error)
  | delaySleep (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,0,0] (running a b c n delay error)
  | delayZero (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,0,1] (running a b c n delay error)
  | catch (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1] (ready a b c n delay error)
  | answerBind (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0] (ready a b c n delay error)
  | completeExit (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0] (ready a b c n delay error)
  | race (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0] (ready a b c n delay error)
  | attemptExit (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0] (ready a b c n delay error)
  | countBind (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,0] (ready a b c n delay error)
  | countUpdate (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,0,0] (ready a b c n delay error)
  | http (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,0,1] (ready a b c n delay error ++ [.unit])
  | cleanupBind (a b c : Val) (n delay : Nat) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,1] (ready a b c n delay error ++ [reifyExitVal exit])
  | cleanupRead (a b c : Val) (n delay : Nat) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,1,0] (ready a b c n delay error ++ [reifyExitVal exit])
  | cleanupNoteBind (a b c : Val) (n delay : Nat) (count : Val) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,1,1] (ready a b c n delay error ++ [reifyExitVal exit, count])
  | cleanupNote (a b c : Val) (n delay : Nat) (count : Val) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0] (ready a b c n delay error ++ [reifyExitVal exit, count])
  | cleanupDone (a b c : Val) (n delay : Nat) (count : Val) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,1,1,1] (ready a b c n delay error ++ [reifyExitVal exit, count, .unit])
  | timerBind (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,1,0] (ready a b c n delay error)
  | timerSleep (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,1,0,0] (ready a b c n delay error)
  | timerFail (a b c : Val) (n delay : Nat) (error : Val)  : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,1,0,1] (ready a b c n delay error ++ [.unit])
  | completeBind (a b c : Val) (n delay : Nat) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,1] (ready a b c n delay error ++ [reifyExitVal exit])
  | completeRead (a b c : Val) (n delay : Nat) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,1,0] (ready a b c n delay error ++ [reifyExitVal exit])
  | completeNote (a b c : Val) (n delay : Nat) (count : Val) (error : Val) (exit : ExitV) (good : ExitAt B .body exit) : EnvAt B [1,1,1,0,0,1,0,0,1,1] (ready a b c n delay error ++ [reifyExitVal exit, count])
  | answer (a b c : Val) (n delay : Nat) (error value : Val) (good : value ∈ B) : EnvAt B [1,1,1,0,0,1,0,1] (ready a b c n delay error ++ [value])
  | caught (a b c : Val) (n delay : Nat) (error failure : Val)  : EnvAt B [1,1,1,0,0,1,1] (ready a b c n delay error ++ [failure])
  | result (a b c : Val) (value : Val) (good : ValueAt B .result value) : EnvAt B [1,1,1,1] (cells a b c ++ [value])
  | errorSelect (a b c : Val) (error : Val)  : EnvAt B [1,1,1,1,0] (cells a b c ++ [.list [.none, error]])
  | emptyFail (a b c : Val)   : EnvAt B [1,1,1,1,0,0] (cells a b c ++ [.list [.none, .none]])
  | lastFail (a b c : Val) (error : Val)  : EnvAt B [1,1,1,1,0,1] (cells a b c ++ [.list [.none, .some error], error])
  | rootAnswer (a b c : Val) (value error : Val) (good : value ∈ B) : EnvAt B [1,1,1,1,1] (cells a b c ++ [.list [.some value, error], value])


/-- The expected result at each listed source effect. -/
def kindAt : List Nat → Kind
  | [] => .body
  | [0] => .any
  | [1] => .body
  | [1,0] => .any
  | [1,1] => .body
  | [1,1,0] => .any
  | [1,1,1] => .body
  | [1,1,1,0] => .result
  | [1,1,1,0,0] => .result
  | [1,1,1,0,0,0] => .unit
  | [1,1,1,0,0,0,0] => .unit
  | [1,1,1,0,0,0,1] => .unit
  | [1,1,1,0,0,1] => .result
  | [1,1,1,0,0,1,0] => .result
  | [1,1,1,0,0,1,0,0] => .body
  | [1,1,1,0,0,1,0,0,0] => .body
  | [1,1,1,0,0,1,0,0,0,0,0,0] => .body
  | [1,1,1,0,0,1,0,0,0,0,0,0,0] => .body
  | [1,1,1,0,0,1,0,0,0,0,0,0,0,0] => .unit
  | [1,1,1,0,0,1,0,0,0,0,0,0,0,1] => .body
  | [1,1,1,0,0,1,0,0,0,0,0,0,1] => .unit
  | [1,1,1,0,0,1,0,0,0,0,0,0,1,0] => .any
  | [1,1,1,0,0,1,0,0,0,0,0,0,1,1] => .unit
  | [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0] => .unit
  | [1,1,1,0,0,1,0,0,0,0,0,0,1,1,1] => .unit
  | [1,1,1,0,0,1,0,0,0,0,0,1,0] => .body
  | [1,1,1,0,0,1,0,0,0,0,0,1,0,0] => .unit
  | [1,1,1,0,0,1,0,0,0,0,0,1,0,1] => .body
  | [1,1,1,0,0,1,0,0,1] => .unit
  | [1,1,1,0,0,1,0,0,1,0] => .any
  | [1,1,1,0,0,1,0,0,1,1] => .unit
  | [1,1,1,0,0,1,0,1] => .result
  | [1,1,1,0,0,1,1] => .result
  | [1,1,1,1] => .body
  | [1,1,1,1,0] => .body
  | [1,1,1,1,0,0] => .body
  | [1,1,1,1,0,1] => .body
  | [1,1,1,1,1] => .body
  | _ => .body

/-- Every lexical assertion names an effect in the generated source census. -/
theorem env_site {B : List Val} {path : List Nat} {env : List Val}
    (slots : EnvAt B path env) : ∃ tag, (path, tag) ∈ sourceNodes := by
  cases slots <;>
    simp only [sourceNodes_eq, List.mem_cons, List.not_mem_nil, Prod.mk.injEq]
  all_goals aesop

/-- Every successful source leaf returns the value required by its lexical assertion.
The success clause of the native command assertion consumes this universal lookup theorem. -/
theorem success_value {B : List Val} {path : List Nat} {env : List Val}
    (slots : EnvAt B path env) (term : Term) (value : Val)
    (leaf : Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (.succeed term)))
    (evaluates : evalTerm env term = some value) : ValueAt B (kindAt path) value := by
  rcases success_cases path term leaf with hp | hp | hp | hp | hp
  · subst path
    cases slots with
    | delayZero a b c n delay error =>
      have node : Node.at_ (.eff HostTimeoutSource.program) [1,1,1,0,0,0,1] =
          some (.eff (.succeed (.lit .unit))) := by kernel_rfl
      rw [node] at leaf
      cases leaf
      cases evaluates
      exact ValueAt.unit
  · subst path
    cases slots with
    | cleanupDone a b c n delay count error exit good =>
      have node : Node.at_ (.eff HostTimeoutSource.program) [1,1,1,0,0,1,0,0,0,0,0,0,1,1,1] =
          some (.eff (.succeed (.lit .unit))) := by kernel_rfl
      rw [node] at leaf
      cases leaf
      cases evaluates
      exact ValueAt.unit
  · subst path
    cases slots with
    | answer a b c n delay error body good =>
      have node : Node.at_ (.eff HostTimeoutSource.program) [1,1,1,0,0,1,0,1] =
          some (.eff (.succeed (.app "pair"
            (.cons (.app "some" (.cons (.var 5) .nil)) (.cons (.app "none" .nil) .nil))))) := by
        kernel_rfl
      rw [node] at leaf
      cases leaf
      have eval : evalTerm (ready a b c n delay error ++ [body])
          (.app "pair" (.cons (.app "some" (.cons (.var 5) .nil))
            (.cons (.app "none" .nil) .nil))) = some (answered body) := by kernel_rfl
      rw [eval] at evaluates
      cases evaluates
      exact ValueAt.answered good
  · subst path
    cases slots with
    | caught a b c n delay error failure =>
      have node : Node.at_ (.eff HostTimeoutSource.program) [1,1,1,0,0,1,1] =
          some (.eff (.succeed (.app "pair"
            (.cons (.app "none" .nil) (.cons (.app "some" (.cons (.var 5) .nil)) .nil))))) := by
        kernel_rfl
      rw [node] at leaf
      cases leaf
      have eval : evalTerm (ready a b c n delay error ++ [failure])
          (.app "pair" (.cons (.app "none" .nil)
            (.cons (.app "some" (.cons (.var 5) .nil)) .nil))) =
          some (.list [.none, .some failure]) := by kernel_rfl
      rw [eval] at evaluates
      cases evaluates
      exact ValueAt.failed failure
  · subst path
    cases slots with
    | rootAnswer a b c body error good =>
      have node : Node.at_ (.eff HostTimeoutSource.program) [1,1,1,1,1] =
          some (.eff (.succeed (.var 4))) := by kernel_rfl
      rw [node] at leaf
      cases leaf
      have eval : evalTerm (cells a b c ++ [.list [.some body, error], body]) (.var 4) =
          some body := by kernel_rfl
      rw [eval] at evaluates
      cases evaluates
      exact ValueAt.body good

/-- Enlarging the applied-body prefix retains every source result assertion. -/
theorem ValueAt.mono {B C : List Val} (sub : B ⊆ C) {kind : Kind} {value : Val}
    (good : ValueAt B kind value) : ValueAt C kind value := by
  cases good with
  | any value => exact .any value
  | unit => exact .unit
  | nat n => exact .nat n
  | cell key => exact .cell key
  | body member => exact .body (sub member)
  | answered member => exact .answered (sub member)
  | failed error => exact .failed error
  | empty => exact .empty

/-- Prefix growth retains saved exits across cleanup. -/
theorem ExitAt.mono {B C : List Val} (sub : B ⊆ C) {kind : Kind} {exit : ExitV}
    (good : ExitAt B kind exit) : ExitAt C kind exit := by
  cases exit with
  | success value => exact ValueAt.mono sub good
  | failure cause => exact good

/-- Prefix growth retains the entire concrete lexical assertion. -/
theorem EnvAt.mono {B C : List Val} (sub : B ⊆ C) {path : List Nat} {env : List Val}
    (slots : EnvAt B path env) : EnvAt C path env := by
  cases slots <;> aesop (add safe constructors [EnvAt], safe apply [ValueAt.mono, ExitAt.mono])

/-- The generated fold collects every source bind addressed by a value continuation. -/
def bindYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun e path => match e with | .bind _ _ => [path] | _ => []}
def bindPaths : List (List Nat) := Node.foldList bindYield [] (.eff HostTimeoutSource.program)

theorem bind_at (path : List Nat) (first next : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (.bind first next))) :
    path ∈ bindPaths := by
  have sub := Node.yieldAt_subset_of_at bindYield path (.eff HostTimeoutSource.program)
    (.eff (.bind first next)) [] node
  exact sub (by simp only [Node.yieldAt, bindYield, List.nil_append, List.mem_singleton])

theorem bindPaths_eq : bindPaths =
  [[], [1], [1,1], [1,1,1], [1,1,1,0,0], [1,1,1,0,0,1,0],
    [1,1,1,0,0,1,0,0,0,0,0,0,0], [1,1,1,0,0,1,0,0,0,0,0,0,1],
    [1,1,1,0,0,1,0,0,0,0,0,0,1,1], [1,1,1,0,0,1,0,0,0,0,0,1,0],
    [1,1,1,0,0,1,0,0,1]] := by kernel_rfl

/-- Binding a source success preserves the exact lexical assertion for its continuation.
Consumer: `contA_slots`, the actual interpreter's named continuation clause. -/
theorem bind_slots {B : List Val} {path : List Nat} {env : List Val}
    (slots : EnvAt B path env) (first next : NativeEff) (value : Val)
    (node : Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (.bind first next)))
    (answer : ValueAt B (kindAt (path ++ [0])) value) :
    EnvAt B (path ++ [1]) (env ++ [value]) := by
  have member := bind_at path first next node
  rw [bindPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  · subst path
    cases slots
    exact .endedMakeBind value
  · subst path
    cases slots with
    | endedMakeBind a => exact .completedMakeBind a value
  · subst path
    cases slots with
    | completedMakeBind a b => exact .finishBind a b value
  · subst path
    cases slots with
    | finishBind a b c => exact .result a b c value answer
  · subst path
    cases slots with
    | iteration a b c n delay error =>
      cases answer
      exact .catch a b c n delay error
  · subst path
    cases slots with
    | answerBind a b c n delay error =>
      cases answer with
      | body good => exact .answer a b c n delay error value good
  · subst path
    cases slots with
    | countBind a b c n delay error =>
      cases answer
      exact .http a b c n delay error
  · subst path
    cases slots with
    | cleanupBind a b c n delay error exit good =>
      exact .cleanupNoteBind a b c n delay value error exit good
  · subst path
    cases slots with
    | cleanupNoteBind a b c n delay count error exit good =>
      cases answer
      exact .cleanupDone a b c n delay count error exit good
  · subst path
    cases slots with
    | timerBind a b c n delay error =>
      cases answer
      exact .timerFail a b c n delay error
  · subst path
    cases slots with
    | completeBind a b c n delay error exit good =>
      exact .completeNote a b c n delay value error exit good

/-- The actual source value callback resolves a continuation with those same lexical slots. -/
theorem contA_slots (B : List Val) (point : Point) (slots : EnvAt B point.path point.env)
    (first next : NativeEff) (value : Val) (view : List (FiberId × ExitV))
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.bind first next)))
    (answer : ValueAt B (kindAt (point.path ++ [0])) value) :
    ∃ target : Point,
      (interpAt HostTimeoutSource.program view Test.Dogfood.Scenario.Timeout.fetch.table).contA
        (.cont point) value = resolve HostTimeoutSource.program target ∧
      EnvAt B target.path target.env := by
  refine ⟨({ point with completed := view }.childWith 1 value), rfl, ?_⟩
  exact bind_slots slots first next value node answer

/-- The generated finalizer positions belong to the body and timeout form. -/
def exitYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun e path => match e with | .onExit _ _ => [path] | _ => []}
def exitPaths : List (List Nat) := Node.foldList exitYield [] (.eff HostTimeoutSource.program)

theorem exitPaths_eq : exitPaths =
  [[1,1,1,0,0,1,0,0], [1,1,1,0,0,1,0,0,0,0,0,0]] := by kernel_rfl

/-- The actual source finalizer callback receives a body assertion at its saved-exit slot. -/
theorem finalizer_slots (B : List Val) (point : Point) (slots : EnvAt B point.path point.env)
    (first next : NativeEff) (exit : ExitV) (view : List (FiberId × ExitV))
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.onExit first next)))
    (saved : ExitAt B (kindAt point.path) exit) :
    ∃ target : Point,
      (interpAt HostTimeoutSource.program view Test.Dogfood.Scenario.Timeout.fetch.table).finalizerProgram
        (.fin point) exit = some (resolve HostTimeoutSource.program target) ∧
      EnvAt B target.path target.env := by
  have sub := Node.yieldAt_subset_of_at exitYield point.path (.eff HostTimeoutSource.program)
    (.eff (.onExit first next)) [] node
  have member : point.path ∈ exitPaths := sub
    (by simp only [Node.yieldAt, exitYield, List.nil_append, List.mem_singleton])
  rw [exitPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  refine ⟨({ point with completed := view }.childWith 1 (reifyExitVal exit)), rfl, ?_⟩
  change EnvAt B (point.path ++ [1]) (point.env ++ [reifyExitVal exit])
  rcases member with hp | hp
  · cases point with
    | mk path env fuel tape completed root params call =>
      dsimp only at hp slots saved ⊢
      subst path
      cases slots with
      | completeExit a b c n delay error => exact .completeBind a b c n delay error exit saved
  · cases point with
    | mk path env fuel tape completed root params call =>
      dsimp only at hp slots saved ⊢
      subst path
      cases slots with
      | attemptExit a b c n delay error => exact .cleanupBind a b c n delay error exit saved

/-- The actual native evaluator's successful bind return preserves the source slots.
This is the bind-return clause of the command invariant, with its saved stack retained. -/
theorem native_bind_return (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (first next : NativeEff) (value : Val)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.bind first next)))
    (answer : ValueAt B (kindAt (point.path ++ [0])) value)
    (m : NativeMachine) (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (body : NCode) (yielding : Bool) :
    let before := { f with frame :=
      { f.frame with
        current := Prim.success value
        stack := Prim.onSuccess body (EffName.cont point) :: f.frame.stack
        deferredInterrupt := false } }
    let after := evaluateNative HostTimeoutSource.program m before yielding
      Test.Dogfood.Scenario.Timeout.fetch.table
    ∃ target : Point, EnvAt B target.path target.env ∧
      after.fiber.frame.current = resolve HostTimeoutSource.program target ∧
      after.fiber.frame.stack = f.frame.stack ∧ after.outcome = .continue_ := by
  refine ⟨({ point with completed := m.completedExits }.childWith 1 value),
    bind_slots slots first next value node answer, ?_, ?_, ?_⟩
  · kernel_rfl
  · kernel_rfl
  · kernel_rfl

/-- Race acceptance retains the same body assertion as its observed entrant exits.
The native observer command consumes this clause before constructing its resume. -/
theorem race_accepts (B : List Val)
    (race : Race EffName EffThunk Val Err Defect FiberId Ann NCode)
    (mode : race.mode = .firstExit) (child : FiberId) (exit : ExitV)
    (incoming : ExitAt B .body exit)
    (old : ∀ accepted, race.state.accepted = some accepted → ExitAt B .body accepted) :
    ∀ accepted, (race.afterExit child exit).state.accepted = some accepted →
      ExitAt B .body accepted := by
  intro accepted observed
  change (Supervision.raceCompleteWith race.mode race.state child exit).accepted =
    some accepted at observed
  rw [mode] at observed
  change (Supervision.raceCompleteFirst race.state child exit).accepted = some accepted at observed
  cases selected : race.state.accepted with
  | some previous =>
    rw [Supervision.raceCompleteFirst_keeps race.state child exit previous selected] at observed
    cases observed
    exact old _ selected
  | none =>
    by_cases live : child ∈ race.state.live
    · rw [Supervision.raceCompleteFirst_accepts race.state child exit live selected] at observed
      cases observed
      exact incoming
    · rw [Supervision.raceCompleteFirst_unknown race.state child exit live, selected] at observed
      cases observed

/-- Administrative restore names retain the successful exit saved before cleanup. -/
def Restores (body : Val) (name : EffName) : Prop :=
  name = .restore (.success body) ∨ name = .merge (.success body) ∨
    name = .store (.restore (.success body)) ∨ name = .store (.merge (.success body))

/-- The actual native evaluator returns the saved body after a successful cleanup.
This covers source finalizers and the first-exit race's embedded cleanup restore. -/
theorem native_restore_return (B : List Val) (body cleanup : Val) (member : body ∈ B)
    (name : EffName) (saved : Restores body name) (m : NativeMachine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (program : NCode) (yielding : Bool) :
    let before := { f with frame :=
      { f.frame with
        current := Prim.success cleanup
        stack := Prim.onSuccess program name :: f.frame.stack
        deferredInterrupt := false } }
    let after := evaluateNative HostTimeoutSource.program m before yielding
      Test.Dogfood.Scenario.Timeout.fetch.table
    after.fiber.frame.current = Prim.success body ∧
      after.fiber.frame.stack = f.frame.stack ∧
      after.outcome = .continue_ ∧ ValueAt B .body body := by
  rcases saved with rfl | rfl | rfl | rfl
  all_goals refine ⟨?_, ?_, ?_, .body member⟩
  all_goals kernel_rfl

/-- The source selectors are collected through the same generated path fold. -/
def selectYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun e path => match e with | .select _ _ _ _ => [path] | _ => []}
def selectPaths : List (List Nat) := Node.foldList selectYield [] (.eff HostTimeoutSource.program)

theorem selectPaths_eq : selectPaths =
    [[1,1,1,0,0,0], [1,1,1,1], [1,1,1,1,0]] := by kernel_rfl

/-- The selector's input is a projection of the existing source node. -/
def selectInput : Option (Node NativeOp) → Option (Term × Decision)
  | some (.eff (.select term decision _ _)) => some (term, decision)
  | _ => none

/-- Every decided source arm retains its exact lexical assertion.
Consumer: the native suspension clause of the command assertion. -/
theorem select_slots (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (term : Term) (decision : Decision)
    (left right : NativeEff) (first : Bool) (bound : Option Val)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.select term decision left right)))
    (selected : (evalTerm point.env term).bind decision.decide = some (first, bound)) :
    EnvAt B (point.childBind (cond first 0 1) bound).path
      (point.childBind (cond first 0 1) bound).env := by
  have sub := Node.yieldAt_subset_of_at selectYield point.path (.eff HostTimeoutSource.program)
    (.eff (.select term decision left right)) [] node
  have member : point.path ∈ selectPaths := sub
    (by simp only [Node.yieldAt, selectYield, List.nil_append, List.mem_singleton])
  rw [selectPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have input := congrArg selectInput node
  change selectInput (Node.at_ (.eff HostTimeoutSource.program) point.path) = some (term, decision) at input
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at slots member input selected ⊢
    rcases member with hp | hp | hp
    · subst path
      cases slots with
      | delaySelect a b c n delay error =>
        have spec : selectInput (Node.at_ (.eff HostTimeoutSource.program) [1,1,1,0,0,0]) =
            some (.app "lt" (.cons (.lit (.nat 0))
              (.cons (.app "fst" (.cons (.var 3) .nil)) .nil)), .bool) := by kernel_rfl
        rw [spec] at input
        cases input
        have test : evalTerm (running a b c n delay error)
            (.app "lt" (.cons (.lit (.nat 0))
              (.cons (.app "fst" (.cons (.var 3) .nil)) .nil))) = some (.bool (0 < n)) := by
          kernel_rfl
        rw [test] at selected
        change some (decide (0 < n), none) = some (first, bound) at selected
        cases selected
        by_cases positive : 0 < n
        · simp only [positive, decide_true, cond_true, Point.childBind, Point.child]
          exact .delaySleep a b c n delay error
        · simp only [positive, decide_false, cond_false, Point.childBind, Point.child]
          exact .delayZero a b c n delay error
    · subst path
      cases slots with
      | result a b c value good =>
        have spec : selectInput (Node.at_ (.eff HostTimeoutSource.program) [1,1,1,1]) =
            some (.app "fst" (.cons (.var 3) .nil), .option) := by kernel_rfl
        rw [spec] at input
        cases input
        cases good with
        | @answered body good =>
          have test : evalTerm (cells a b c ++ [.list [.some body, .none]])
              (.app "fst" (.cons (.var 3) .nil)) = some (.some body) := by kernel_rfl
          rw [test] at selected
          cases selected
          exact .rootAnswer a b c _ .none good
        | failed error =>
          have test : evalTerm (cells a b c ++ [.list [.none, .some error]])
              (.app "fst" (.cons (.var 3) .nil)) = some .none := by kernel_rfl
          rw [test] at selected
          cases selected
          exact .errorSelect a b c (.some error)
        | empty =>
          have test : evalTerm (cells a b c ++ [.list [.none, .none]])
              (.app "fst" (.cons (.var 3) .nil)) = some .none := by kernel_rfl
          rw [test] at selected
          cases selected
          exact .errorSelect a b c .none
    · subst path
      cases slots with
      | errorSelect a b c error =>
        have spec : selectInput (Node.at_ (.eff HostTimeoutSource.program) [1,1,1,1,0]) =
            some (.app "snd" (.cons (.var 3) .nil), .option) := by kernel_rfl
        rw [spec] at input
        cases input
        have test : evalTerm (cells a b c ++ [.list [.none, error]])
            (.app "snd" (.cons (.var 3) .nil)) = some error := by kernel_rfl
        rw [test] at selected
        change Decision.decide .option error = some (first, bound) at selected
        unfold Decision.decide at selected
        split at selected <;>
          aesop (add norm simp [Point.childBind, Point.child, Point.childWith],
            safe constructors [EnvAt])

/-- A retry cursor retains the successful answer or the last failure. -/
inductive CursorAt (B : List Val) : Val → Prop
  | state (n delay : Nat) (last : Val) (good : ValueAt B .result last) :
      CursorAt B (.list [.nat n, .list [.nat delay, last]])

/-- A stopped retry cursor returns the same answer/error pair. -/
theorem loop_finish_value (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (cursorValue : Val) (cursorGood : CursorAt B cursorValue)
    (path : point.path = [1,1,1,0]) :
    ∃ last, loopFinishAt HostTimeoutSource.program point cursorValue = Prim.success last ∧
      ValueAt B .result last := by
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots with
    | loop a b c =>
      cases cursorGood with
      | state n delay last good =>
        exact ⟨last, by kernel_rfl, good⟩

/-- The actual retry step copies the body result into the next cursor unchanged. -/
theorem loop_step_value (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (n delay : Nat) (previous last : Val)
    (path : point.path = [1,1,1,0]) :
    loopResumeAt HostTimeoutSource.program point (.list [.nat n, .list [.nat delay, previous]]) last =
      loopNextAt HostTimeoutSource.program point
        (.list [.nat (n + 1), .list [.nat (if 0 < n then delay * 2 else delay), last]]) := by
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots with
    | loop a b c =>
      have equation : loopResumeAt HostTimeoutSource.program
          { path := [1,1,1,0], env := cells a b c, fuel, tape, completed, root, params, call }
          (.list [.nat n, .list [.nat delay, previous]]) last =
          loopNextAt HostTimeoutSource.program
            { path := [1,1,1,0], env := cells a b c, fuel, tape, completed, root, params, call }
            (.list [.nat (n + 1), .list [if decide (0 < n) = true then .nat (delay * 2) else .nat delay, last]]) := by
        kernel_rfl
      rw [equation]
      simp only [decide_eq_true_eq]
      rw [← apply_ite Val.nat (0 < n) (delay * 2) delay]

/-- An answered retry cursor never enters another attempt. -/
theorem loop_answer_stops (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (n delay : Nat) (body error : Val)
    (path : point.path = [1,1,1,0]) :
    loopNextAt HostTimeoutSource.program point (cursor n delay (.some body) error) =
      .finish (Prim.success (.list [.some body, error])) := by
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots
    kernel_rfl

/-- The loop fields are projections of its existing source node. -/
def loopParts : Term × Term × NativeEff :=
  match Node.at_ (.eff HostTimeoutSource.program) [1,1,1,0] with
  | some (.eff (.iterate _ _ test step _ body)) => (test, step, body)
  | _ => (.lit (.bool false), .lit .unit, .succeed (.lit .unit))

/-- Reading the actual loop returns those same source fields. -/
theorem loop_parts (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (path : point.path = [1,1,1,0]) :
    loopAt HostTimeoutSource.program point = some (loopParts.1, loopParts.2.1, loopParts.2.2) := by
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots
    kernel_rfl

/-- The waiting cursor's guard reads only its retry number and empty answer column. -/
theorem loop_waiting_test (a b c : Val) (n delay : Nat) (error : Val) :
    evalTerm (cells a b c ++ [cursor n delay .none error]) loopParts.1 =
      some (.bool (decide (n = 0) || decide (n < 4))) := by kernel_rfl

/-- A waiting retry cursor either enters the exact body slots or returns its last pair.
The actual loop-enter callback consumes this clause; no assumption concerns a heap slot. -/
theorem loop_waiting (B : List Val) (point : Point)
    (slots : EnvAt B point.path point.env) (n delay : Nat) (error : Val)
    (path : point.path = [1,1,1,0]) :
    loopNextAt HostTimeoutSource.program point (cursor n delay .none error) =
      if n = 0 ∨ n < 4 then
        .continue (cursor n delay .none error)
          (resolve HostTimeoutSource.program (point.childWith 0 (cursor n delay .none error)))
      else .finish (Prim.success (.list [.none, error])) := by
  have fields := loop_parts B point slots path
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots with
    | loop a b c =>
      unfold loopNextAt
      rw [fields]
      dsimp only
      rw [loop_waiting_test]
      by_cases allowed : n = 0 ∨ n < 4
      · have test : (decide (n = 0) || decide (n < 4)) = true := by
          rw [← Bool.decide_or]
          exact decide_eq_true allowed
        rw [test, if_pos allowed]
      · have test : (decide (n = 0) || decide (n < 4)) = false := by
          rw [← Bool.decide_or]
          exact decide_eq_false allowed
        rw [test, if_neg allowed]
        kernel_rfl

/-- The first compiled body positions are generated from the source heads. -/
def firstYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun e path => match e with
    | .bind _ _ | .onExit _ _ | .catchIf _ _ _ => [path]
    | _ => []}
def firstPaths : List (List Nat) := Node.foldList firstYield [] (.eff HostTimeoutSource.program)

theorem firstPaths_eq : firstPaths =
  [[], [1], [1,1], [1,1,1], [1,1,1,0,0], [1,1,1,0,0,1],
    [1,1,1,0,0,1,0], [1,1,1,0,0,1,0,0], [1,1,1,0,0,1,0,0,0,0,0,0],
    [1,1,1,0,0,1,0,0,0,0,0,0,0], [1,1,1,0,0,1,0,0,0,0,0,0,1],
    [1,1,1,0,0,1,0,0,0,0,0,0,1,1], [1,1,1,0,0,1,0,0,0,0,0,1,0],
    [1,1,1,0,0,1,0,0,1]] := by kernel_rfl

/-- Entering each compiled body retains its exact lexical assertion.
Consumer: the source expansion clause of the command assertion. -/
theorem first_slots {B : List Val} {path : List Nat} {env : List Val}
    (slots : EnvAt B path env) (first : path ∈ firstPaths) :
    EnvAt B (path ++ [0]) env := by
  rw [firstPaths_eq] at first
  simp only [List.mem_cons, List.not_mem_nil, or_false] at first
  rcases first with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals subst path
  all_goals cases slots
  all_goals aesop (add safe constructors [EnvAt])

/-- A loop body can start only with an empty answer column. -/
theorem iteration_slots {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (n delay : Nat) (error : Val)
    (path : point.path = [1,1,1,0]) :
    EnvAt B (point.childWith 0 (cursor n delay .none error)).path
      (point.childWith 0 (cursor n delay .none error)).env := by
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots with
    | loop a b c => exact .iteration a b c n delay error

/-- The catch callback appends only its failure value, never an answer body. -/
theorem caught_slots {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (error : Val)
    (path : point.path = [1,1,1,0,0,1]) :
    EnvAt B (point.childWith 1 error).path (point.childWith 1 error).env := by
  cases point with
  | mk path env fuel tape completed root params call =>
    dsimp only at path slots ⊢
    subst path
    cases slots with
    | «catch» a b c n delay previous => exact .caught a b c n delay previous error

/-- The source effect is a projection of the existing addressed node. -/
def sourceAt (path : List Nat) : NativeEff :=
  match Node.at_ (.eff HostTimeoutSource.program) path with
  | some (.eff effect) => effect
  | _ => .succeed (.lit .unit)

/-- Every lexical assertion names an actual source effect, including every administrative entry. -/
theorem env_node {B : List Val} {path : List Nat} {env : List Val}
    (slots : EnvAt B path env) :
    Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (sourceAt path)) := by
  cases slots <;> kernel_rfl

/-- A source bind's continuation keeps its parent's expected result class. -/
theorem bind_result_kind (path : List Nat) (first next : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (.bind first next))) :
    kindAt (path ++ [1]) = kindAt path := by
  have member := bind_at path first next node
  rw [bindPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with hp | hp | hp | hp | hp | hp | hp | hp | hp | hp | hp
  all_goals subst path
  all_goals rfl

end Test.Dogfood.Proofs.HostTimeoutSlots
