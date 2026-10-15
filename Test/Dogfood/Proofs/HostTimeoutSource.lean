import Effect4.Laws.Program.Author
import Test.Dogfood.Scenario.Timeout.Model
import Effect4.Laws.Api.AuthorBuild
import Effect4.Laws.Auto.KernelRfl
import Effect4.Program.LayerView
import Test.Dogfood.Proofs.HostPayloads
import Effect4.Laws.Machine.RaceFirst
import Effect4.Laws.Program.PathFold

/-!
# Source slots of the timeout client's returned value

Placement: host-session-protocol, R6, the source-value step of `stale_never_applies` clause four.
The source equations also serve the amended retry claim under translation-simulation, R10.
The composite consumer is `returned_body` in this module.
The machine invariant must retain these source points, environments and saved exits at every command boundary.
The invariant must cover pending resumes, race acceptance, cleanup publication and forced yields.
These equations establish no reachable-machine invariant, progress or runtime agreement.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

namespace Test.Dogfood.Proofs.HostTimeoutSource
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Effect4.Program.Authoring
open Test.Dogfood.Scenario.Timeout

/-- The source program whose names the timeout invariant interprets. -/
def program : NativeEff :=
  match elaborateModule fetch with
  | .ok p => p
  | .error _ => .succeed (.lit .unit)

/-- The kernel establishes the elaboration before any source-flow equation uses it. -/
theorem elaborates : elaborateModule fetch = .ok program := by
  kernel_rfl

/-- A checked build has the exact source program and call table used below. -/
theorem built_fetch {b : Api.Built} (h : Effect4.Api.Author.build fetch = .ok b) :
    b.program = program ∧ b.table = fetch.table := by
  refine ⟨?_, (build_table h).1⟩
  have hp := (Effect4.Api.Author.build_retains h).1
  rw [elaborates] at hp
  exact (Except.ok.inj hp).symm

/-- The generated source fold supplies every effect location to the command-case invariant. -/
def sourceNodes : List (List Nat × String) :=
  foldMapAt_eff [] (· ++ ·) [] program (f_eff := fun e path => [(path, (view_eff e).1)])

/-- The source-case matrix is the generated fold's complete effect-location list. -/
theorem sourceNodes_eq : sourceNodes =
  [([], "bind"),
   ([0], "perform"),
   ([1], "bind"),
   ([1,0], "perform"),
   ([1,1], "bind"),
   ([1,1,0], "perform"),
   ([1,1,1], "bind"),
   ([1,1,1,0], "iterate"),
   ([1,1,1,0,0], "bind"),
   ([1,1,1,0,0,0], "select"),
   ([1,1,1,0,0,0,0], "perform"),
   ([1,1,1,0,0,0,1], "succeed"),
   ([1,1,1,0,0,1], "catchIf"),
   ([1,1,1,0,0,1,0], "bind"),
   ([1,1,1,0,0,1,0,0], "onExit"),
   ([1,1,1,0,0,1,0,0,0], "withFiber"),
   ([1,1,1,0,0,1,0,0,0,0,0,0], "onExit"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,0], "bind"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,0,0], "perform"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,0,1], "perform"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,1], "bind"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,1,0], "perform"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,1,1], "bind"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,1,1,0], "perform"),
   ([1,1,1,0,0,1,0,0,0,0,0,0,1,1,1], "succeed"),
   ([1,1,1,0,0,1,0,0,0,0,0,1,0], "bind"),
   ([1,1,1,0,0,1,0,0,0,0,0,1,0,0], "perform"),
   ([1,1,1,0,0,1,0,0,0,0,0,1,0,1], "fail"),
   ([1,1,1,0,0,1,0,0,1], "bind"),
   ([1,1,1,0,0,1,0,0,1,0], "perform"),
   ([1,1,1,0,0,1,0,0,1,1], "perform"),
   ([1,1,1,0,0,1,0,1], "succeed"),
   ([1,1,1,0,0,1,1], "succeed"),
   ([1,1,1,1], "select"),
   ([1,1,1,1,0], "select"),
   ([1,1,1,1,0,0], "failCause"),
   ([1,1,1,1,0,1], "fail"),
   ([1,1,1,1,1], "succeed")] := by
  kernel_rfl

/-- The successful source leaves, collected by the generated fold. -/
def successYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun e path => match e with
    | .succeed _ => [path]
    | _ => []}

def successPaths : List (List Nat) := Node.foldList successYield [] (.eff program)

/-- Every addressed successful leaf occurs in the generated collection. -/
theorem success_at (path : List Nat) (term : Term)
    (atLeaf : Node.at_ (.eff program) path = some (.eff (.succeed term))) :
    path ∈ successPaths := by
  have sub := Node.yieldAt_subset_of_at successYield path (.eff program)
    (.eff (.succeed term)) [] atLeaf
  exact sub (by simp only [Node.yieldAt, successYield, List.nil_append, List.mem_singleton])

/-- These five locations exhaust the source's successful leaves. -/
theorem successPaths_eq : successPaths =
  [[1,1,1,0,0,0,1], [1,1,1,0,0,1,0,0,0,0,0,0,1,1,1],
    [1,1,1,0,0,1,0,1], [1,1,1,0,0,1,1], [1,1,1,1,1]] := by
  kernel_rfl

/-- The command invariant's successful-source case list follows from lookup, for every path. -/
theorem success_cases (path : List Nat) (term : Term)
    (atLeaf : Node.at_ (.eff program) path = some (.eff (.succeed term))) :
    path = [1,1,1,0,0,0,1] ∨ path = [1,1,1,0,0,1,0,0,0,0,0,0,1,1,1] ∨
      path = [1,1,1,0,0,1,0,1] ∨ path = [1,1,1,0,0,1,1] ∨ path = [1,1,1,1,1] := by
  have member := success_at path term atLeaf
  simpa only [successPaths_eq, List.mem_cons, List.not_mem_nil, or_false] using member

/-- The retry loop's source point. -/
def loopPath : List Nat := [1,1,1,0]

/-- The timeout body's success continuation, inside the typed failure handler. -/
def answerPath : List Nat := loopPath ++ [0,1,0]

/-- The result option selection after the loop. -/
def resultPath : List Nat := [1,1,1,1]

/-- The three lexical cells precede every retry cursor. -/
def cellEnv (count ended completed : Val) : List Val := [count, ended, completed]

/-- The retry cursor's four columns are first-order values. -/
def cursor (n delay : Nat) (answer error : Val) : Val :=
  .list [.nat n, .list [.nat delay, .list [answer, error]]]

/-- A successful body becomes the answer column; the error column is empty. -/
def answered (body : Val) : Val := .list [.some body, .none]

/-- The corresponding handler point binds the cursor and the sleep result before its answer. -/
def answerPoint (count ended completed previousError : Val) (n delay fuel : Nat) : Point :=
  {path := answerPath, env := cellEnv count ended completed ++
    [cursor n delay .none previousError, .unit], fuel := fuel + 2, tape := []}

/-- The loop retains the cells while its cursor stays in the loop frame. -/
def loopPoint (count ended completed : Val) (fuel : Nat) : Point :=
  {path := loopPath, env := cellEnv count ended completed, fuel := fuel + 2, tape := []}

/-- The result selection binds the completed cursor's answer/error pair in slot three. -/
def resultPoint (count ended completed body : Val) (fuel : Nat)
    (view : List (FiberId × ExitV)) : Point :=
  {path := resultPath, env := cellEnv count ended completed ++ [answered body], fuel := fuel + 2, tape := [], completed := view}

/-- The actual continuation wraps the supplied success, with no change to its body. -/
theorem answer_keeps (count ended completed previousError body : Val) (n delay fuel : Nat) (view : List (FiberId × ExitV)) :
    (interpAt program view fetch.table).contA (.cont (answerPoint count ended completed previousError n delay fuel)) body =
      Prim.success (answered body) := by
  kernel_rfl

/-- The loop's actual resume operation retains the supplied success in its finished result. -/
theorem loop_keeps (count ended completed previousError body : Val) (n delay fuel : Nat)
    (view : List (FiberId × ExitV)) :
    (interpAt program view fetch.table).loopResume (.loop (loopPoint count ended completed fuel))
      (cursor n delay .none previousError) (answered body) =
        .finish (Prim.success (answered body)) := by
  cases n <;> kernel_rfl

/-- The post-loop continuation resolves the actual result selection at its lexical slot. -/
theorem result_selection (count ended completed body : Val) (fuel : Nat)
    (view : List (FiberId × ExitV)) :
    (interpAt program view fetch.table).contA (.cont {path := [1,1,1], env := cellEnv count ended completed, fuel := fuel + 3, tape := []})
      (answered body) = Prim.suspend (.body (resultPoint count ended completed body fuel view)) := by
  kernel_rfl

/-- The result selection binds the body's option and returns that exact body. -/
theorem selection_keeps (count ended completed body : Val) (fuel : Nat)
    (view : List (FiberId × ExitV)) :
    (interpAt program view fetch.table).suspendBody (.body (resultPoint count ended completed body fuel view)) = Prim.success body := by
  kernel_rfl

/-- The actual success route retains an arbitrary supplied body through the retry cursor.
The source-flow invariant consumes this equation after the race and finalizers restore their saved success.
The equation alone does not establish that a reachable root obtains its body from a reply application. -/
theorem returned_body (count ended completed previousError body : Val) (n delay fuel : Nat)
    (view : List (FiberId × ExitV)) :
    (interpAt program view fetch.table).contA (.cont (answerPoint count ended completed previousError n delay fuel)) body =
      Prim.success (answered body) ∧
    (interpAt program view fetch.table).loopResume (.loop (loopPoint count ended completed fuel))
      (cursor n delay .none previousError) (answered body) =
        .finish (Prim.success (answered body)) ∧
    (interpAt program view fetch.table).contA (.cont {path := [1,1,1], env := cellEnv count ended completed, fuel := fuel + 3, tape := []})
      (answered body) = Prim.suspend (.body (resultPoint count ended completed body fuel view)) ∧
    (interpAt program view fetch.table).suspendBody (.body (resultPoint count ended completed body fuel view)) = Prim.success body :=
  ⟨answer_keeps count ended completed previousError body n delay fuel view,
    loop_keeps count ended completed previousError body n delay fuel view,
    result_selection count ended completed body fuel view,
    selection_keeps count ended completed body fuel view⟩

/-- Restoring a saved successful body after successful cleanup returns that exact body. -/
theorem cleanup_keeps_body (body cleanup : Val) :
    contAOf program (.restore (.success body)) cleanup = Prim.success body ∧
      contAOf program (.merge (.success body)) cleanup = Prim.success body := ⟨rfl, rfl⟩

/-- The exact reply application's body survives the selected race exit, successful cleanup,
and the actual retry continuation hooks. The source-flow invariant supplies the matching race
and points; this segment does not assert their correlation with every reachable machine. -/
theorem applied_body_through_source
    (s : Run) (reached : Run.Reached s) (key : Api.HostSession.Key)
    (applied : (Api.Runner.result s.runner (.apply key)).phase = .applied)
    (body : Val)
    (read : (Api.HostSession.readReply s.session.pending key).map (·.completion) =
      some (.ofExit (.success body)))
    (race : Race EffName EffThunk Val Err Defect FiberId Ann NCode) (child : FiberId)
    (mode : race.mode = .firstExit) (live : child ∈ race.state.live)
    (unselected : race.state.accepted = none)
    (count ended completed previousError cleanup : Val) (n delay fuel : Nat)
    (view : List (FiberId × ExitV)) :
    (∃ reply, reply ∈ HostPayloads.acceptedReplies s ∧
      reply.key = key ∧ reply.completion = .ofExit (.success body)) ∧
    body ∈ HostPayloads.appliedBodies (s.step (.apply key)) ∧
    (race.afterExit child (.success body)).selected = some child ∧
    (race.afterExit child (.success body)).state.accepted = some (.success body) ∧
    contAOf program (.restore (.success body)) cleanup = Prim.success body ∧
    (interpAt program view fetch.table).loopResume (.loop (loopPoint count ended completed fuel))
      (cursor n delay .none previousError) (answered body) =
        .finish (Prim.success (answered body)) ∧
    (interpAt program view fetch.table).suspendBody (.body (resultPoint count ended completed body fuel view)) =
      Prim.success body := by
  obtain ⟨reply, _, member, same, selected, _, _, _⟩ :=
    HostPayloads.application_payload s reached key applied
  rw [selected, Option.map_some] at read
  have completion := Option.some.inj read
  obtain ⟨hselected, haccepted⟩ := Race.afterExit_first race child (.success body) mode live unselected
  obtain ⟨_, hloop, _, hreturn⟩ := returned_body count ended completed previousError body n delay fuel view
  exact ⟨⟨reply, member, same, completion⟩,
    HostPayloads.application_body s reached key applied body (by rw [selected, Option.map_some]; exact congrArg some completion),
    hselected, haccepted,
    (cleanup_keeps_body body cleanup).1, hloop, hreturn⟩

/-- The source retry test and returned-outcome predicate use the same declared failures. -/
def catchPath : List Nat := loopPath ++ [0,1]
def retryTest : Term :=
  match Node.at_ (.eff program) catchPath with
  | some (.eff (.catchIf t _ _)) => t
  | _ => .lit (.bool false)
def declared (tag message : String) : Bool :=
  tag == "NetworkError" || (tag == "Timeout" || message == "503")
theorem retry_test_evaluates (count ended completed error : Val) (n delay : Nat) (tag message : String) :
  evalTerm (cellEnv count ended completed ++ [cursor n delay .none error, .unit,
    .list [.str tag, .str message]]) retryTest = some (.bool (declared tag message)) := by kernel_rfl
theorem form_retries_eq (n : Nat) (selected : Option FiberId) (role : WinnerRole) (tag message : String) :
  (FormOutcome.mk n selected role (.failure (Cause.fail (.tagged tag message)))).retries =
    declared tag message := by
  change (((tag == "NetworkError") || (tag == "Timeout")) || (message == "503")) =
    ((tag == "NetworkError") || ((tag == "Timeout") || (message == "503")))
  exact Bool.or_assoc _ _ _

/-- The actual source test reads the exact declared predicate of a returned singleton failure.
The retry invariant consumes this equality after completed-form publication. -/
theorem retry_reads_returned (count ended completed error : Val) (n delay : Nat)
    (selected : Option FiberId) (role : WinnerRole) (tag message : String) :
    evalTerm (cellEnv count ended completed ++ [cursor n delay .none error, .unit,
      .list [.str tag, .str message]]) retryTest =
      some (.bool (FormOutcome.mk n selected role (.failure (Cause.fail (.tagged tag message)))).retries) := by
  rw [form_retries_eq]
  exact retry_test_evaluates count ended completed error n delay tag message

end Test.Dogfood.Proofs.HostTimeoutSource
