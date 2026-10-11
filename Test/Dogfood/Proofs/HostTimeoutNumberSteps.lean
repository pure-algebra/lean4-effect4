import Test.Dogfood.Proofs.HostTimeoutNative
import Effect4.Laws.Program.ErrorQueries

/-!
Placement: translation-simulation R10 and scope-lifetime-finalization R11.
Question: the source and heap steps of `Timeout.retries_declared` and `Timeout.cleanup_keeps`.
Consumer: the numeric configuration assertion over actual command histories.
The source assertions retain the retry number below four at every attempt position.
The heap equations read the actual source operations on the three allocated cells.
They do not establish the order of source positions across different fibers.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberSteps
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow

/-- The three handles allocated before the retry loop. -/
def cellSlots : List Val := [Val.cell ⟨0⟩, Val.cell ⟨1⟩, Val.cell ⟨2⟩]

/-- The concrete heap read by the original numeric observations. -/
def numberHeap (count : Nat) (cleanups completed : List Val) : RefHeap :=
  [.nat count, .list cleanups, .list completed]

/-- Source points retain compilation fuel and lexical values as existing first-order data. -/
def sourcePoint (path : List Nat) (env : List Val) (fuel : Nat) : Point :=
  {path, env, fuel := fuel + 1, tape := []}

/-- Read the actual synchronous source head using the native interpreter. -/
def sourceStep (view : View) (point : Point) (state : Stores) : Option (Stores × Val) :=
  match resolve HostTimeoutSource.program point with
  | .sync thunk => (interpreter view).syncState thunk state
  | _ => none

/-- The generated fold collects every reference operation in the actual source.
Consumer: the complete numeric command case census. -/
def refYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun effect path => match effect with
    | .perform .refMake _ | .perform .refGet _ | .perform (.refUpdateWith _) _ => [path]
    | _ => []}

def refPaths : List (List Nat) := Node.foldList refYield [] (.eff HostTimeoutSource.program)

/-- These eight leaves exhaust the source's three allocations, two reads, and three writes. -/
theorem refPaths_eq : refPaths =
    [[0], [1,0], [1,1,0], [1,1,1,0,0,1,0,0,0,0,0,0,0,0],
      [1,1,1,0,0,1,0,0,0,0,0,0,1,0], [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0],
      [1,1,1,0,0,1,0,0,1,0], [1,1,1,0,0,1,0,0,1,1]] := by kernel_rfl

/-- Every actual reference leaf belongs to the exact heap-step matrix. -/
theorem ref_at (path : List Nat) (op : NativeOp) (request : Term)
    (node : Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (.perform op request)))
    (reference : op = .refMake ∨ op = .refGet ∨ ∃ term, op = .refUpdateWith term) :
    path ∈ refPaths := by
  have subset := Node.yieldAt_subset_of_at refYield path (.eff HostTimeoutSource.program)
    (.eff (.perform op request)) [] node
  apply subset
  rcases reference with rfl | rfl | ⟨term, rfl⟩
  all_goals simp only [Node.yieldAt, refYield, List.nil_append, List.mem_singleton]

/-- The source count update retains a bounded retry number independently of its heap input.
Consumer: the counter-write clause of the numeric configuration assertion. -/
theorem count_slots {B : List Val} {env : List Val}
    (slots : EnvAt B [1,1,1,0,0,1,0,0,0,0,0,0,0,0] env) :
    ∃ (a b c : Val) (n : Fin 4) (delay : Nat) (error : Val), env = ready a b c n delay error := by
  cases slots with
  | countUpdate a b c n delay error => exact ⟨a, b, c, n, delay, error, rfl⟩

/-- Allocation mints the counter's exact handle and commits its initial zero. -/
theorem count_make (view : View) (state : Stores) (fuel : Nat) :
    sourceStep view (sourcePoint [0] [] fuel) {state with refs := []} =
      some ({state with refs := [.nat 0]}, Val.cell ⟨0⟩) := by kernel_rfl

/-- The cleanup log is the second allocated cell. -/
theorem cleanup_make (view : View) (state : Stores) (fuel : Nat) :
    sourceStep view (sourcePoint [1,0] [Val.cell ⟨0⟩] fuel)
      {state with refs := [.nat 0]} =
      some ({state with refs := [.nat 0, .list []]}, Val.cell ⟨1⟩) := by kernel_rfl

/-- The completed-form log is the third allocated cell. -/
theorem completed_make (view : View) (state : Stores) (fuel : Nat) :
    sourceStep view (sourcePoint [1,1,0] [Val.cell ⟨0⟩, Val.cell ⟨1⟩] fuel)
      {state with refs := [.nat 0, .list []]} =
      some ({state with refs := numberHeap 0 [] []}, Val.cell ⟨2⟩) := by kernel_rfl

/-- The count writer increments the actual heap count and preserves both logs.
The later history assertion must correlate that count with the active attempt. -/
theorem count_update (view : View) (state : Stores) (fuel count delay : Nat)
    (n : Fin 4) (error : Val) (cleanups completed : List Val) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,0,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error) fuel)
      {state with refs := numberHeap count cleanups completed} =
      some ({state with refs := numberHeap (count + 1) cleanups completed}, .unit) := by
  kernel_rfl

/-- Attempt cleanup reads the committed count without changing any cell. -/
theorem cleanup_read (view : View) (state : Stores) (fuel count delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (cleanups completed : List Val) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit]) fuel)
      {state with refs := numberHeap count cleanups completed} =
      some ({state with refs := numberHeap count cleanups completed}, .nat count) := by
  kernel_rfl

/-- The interruption flag is the source atom's exact exit query. -/
def interruptionFlag (exit : ExitV) : Bool :=
  exit.causeReasons.any (fun reason => decide (reason.tag = .interrupt))

/-- The cleanup note preserves the counter and appends the number read by its prior source slot. -/
theorem cleanup_note (view : View) (state : Stores) (fuel count seen delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (cleanups completed : List Val) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]) fuel)
      {state with refs := numberHeap count cleanups completed} =
      some ({state with refs := numberHeap count (cleanups ++ [.list [.nat seen, .bool (interruptionFlag exit)]]) completed}, .unit) := by
  have prepared : resolve HostTimeoutSource.program
      (sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]) fuel) =
      .sync (.op (.refUpdate ⟨1⟩
        (.app "append" (.cons (.var 7) (.cons
          (.app "cons" (.cons (.app "pair" (.cons (.var 6) (.cons
            (.app "causeIsInterrupt" (.cons (.var 5) .nil)) .nil)))
            (.cons (.app "nil" .nil) .nil))) .nil)))
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]))) := by kernel_rfl
  have queried : nativeAtom "causeIsInterrupt" [reifyExitVal exit] =
      some (.bool (interruptionFlag exit)) := by
    change queryTag .interrupt (reifyExitVal exit) = _
    cases exit with
    | success value => rfl
    | failure cause =>
      change (queryReasons? (Val.exitErr cause)).map
        (fun reasons => Val.bool (reasons.any (fun reason => decide (reason.tag = .interrupt)))) = _
      rw [queryReasons?_exitErr]
      rfl
  let env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
    [reifyExitVal exit, .nat seen] ++ [.list cleanups]
  have fifth : env[5]? = some (reifyExitVal exit) := by kernel_rfl
  have sixth : env[6]? = some (.nat seen) := by kernel_rfl
  have seventh : env[7]? = some (.list cleanups) := by kernel_rfl
  have evaluated : evalTerm env
      (.app "append" (.cons (.var 7) (.cons
        (.app "cons" (.cons (.app "pair" (.cons (.var 6) (.cons
          (.app "causeIsInterrupt" (.cons (.var 5) .nil)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil))) =
      some (.list (cleanups ++ [.list [.nat seen, .bool (interruptionFlag exit)]])) := by
    simp only [evalTerm, evalTerms, fifth, sixth, seventh, Option.bind_eq_bind, Option.bind_some]
    rw [queried]
    kernel_rfl
  unfold sourceStep
  rw [prepared]
  change (refStep
    (.refUpdate ⟨1⟩
      (.app "append" (.cons (.var 7) (.cons
        (.app "cons" (.cons (.app "pair" (.cons (.var 6) (.cons
          (.app "causeIsInterrupt" (.cons (.var 5) .nil)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil)))
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
        [reifyExitVal exit, .nat seen]))
    (numberHeap count cleanups completed)).map
      (fun step => ({state with refs := step.2}, step.1)) = _
  change ((refPeek (numberHeap count cleanups completed) ⟨1⟩).bind
    (fun old => (evalTerm
      (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
        [reifyExitVal exit, .nat seen] ++ [old])
      (.app "append" (.cons (.var 7) (.cons
        (.app "cons" (.cons (.app "pair" (.cons (.var 6) (.cons
          (.app "causeIsInterrupt" (.cons (.var 5) .nil)) .nil)))
          (.cons (.app "nil" .nil) .nil))) .nil)))).map
      (fun written => (Val.unit, refPoke (numberHeap count cleanups completed) ⟨1⟩ written)))).map
        (fun step => ({state with refs := step.2}, step.1)) = _
  have read : refPeek (numberHeap count cleanups completed) ⟨1⟩ =
      some (.list cleanups) := rfl
  rw [read, Option.bind_some]
  change ((evalTerm env _).map _).map _ = _
  rw [evaluated]
  kernel_rfl

/-- The timeout-form finalizer reads the same committed count after race cleanup. -/
theorem completed_read (view : View) (state : Stores) (fuel count delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (cleanups completed : List Val) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,1,0]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit]) fuel)
      {state with refs := numberHeap count cleanups completed} =
      some ({state with refs := numberHeap count cleanups completed}, .nat count) := by
  kernel_rfl

/-- The form note appends the complete saved exit; it neither changes nor rewrites cleanup. -/
theorem completed_note (view : View) (state : Stores) (fuel count seen delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (cleanups completed : List Val) :
    sourceStep view
      (sourcePoint [1,1,1,0,0,1,0,0,1,1]
        (ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]) fuel)
      {state with refs := numberHeap count cleanups completed} =
      some ({state with refs := numberHeap count cleanups (completed ++ [.list [.nat seen, reifyExitVal exit]])}, .unit) := by kernel_rfl

end Test.Dogfood.Proofs.HostTimeoutNumberSteps
