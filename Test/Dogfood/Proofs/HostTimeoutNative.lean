import Test.Dogfood.Proofs.HostTimeoutFlow
import Effect4.Laws.Program.Agreement

/-!
# Source expansion of the Timeout native assertion

Placement: host-session-protocol R6, serving `Timeout.stale_never_applies` clause four.
Consumer: actual native evaluation and the command assertion.
The equations correlate stored callback points with their lexical assertions.
They keep completed-exit views and compilation fuel universally quantified.
They establish no reached-state invariant until the command transport consumes them.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNative
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open HostTimeoutSlots HostTimeoutFlow

/-- Every source bind enters a source body from the complete generated census. -/
theorem bind_first_slots {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (first next : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.bind first next))) :
    EnvAt B (point.child 0).path (point.child 0).env := by
  have sub := Node.yieldAt_subset_of_at firstYield point.path (.eff HostTimeoutSource.program)
    (.eff (.bind first next)) [] node
  have member : point.path ∈ firstPaths := sub
    (by simp only [Node.yieldAt, firstYield, List.nil_append, List.mem_singleton])
  exact first_slots slots member

/-- The actual named bind callback returns source code at its parent's expected value class. -/
theorem bind_callback {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (first next : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.bind first next)))
    (view : View) (value : Val) (good : ValueAt B (kindAt (point.path ++ [0])) value) :
    CodeAt B (kindAt point.path) ((interpreter view).contA (.cont point) value) := by
  change CodeAt B (kindAt point.path)
    (resolve HostTimeoutSource.program ({ point with completed := view }.childWith 1 value))
  have result := bind_result_kind point.path first next node
  rw [← result]
  exact CodeAt.source ({ point with completed := view }.childWith 1 value)
    (bind_slots slots first next value node good)

/-- Expanding a source bind installs an ordered value continuation in the actual primitive. -/
theorem bind_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (first next : NativeEff) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.bind first next)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_bind first next positive]
  refine HeadAt.onSuccess (kindAt (point.path ++ [0])) (kindAt point.path) _ _ ?_ ?_
  · have child : Node.at_ (.eff HostTimeoutSource.program) (point.child 0).path =
        some (.eff first) := Agreement.at_child node 0
    rw [← Agreement.resolve_of_at child]
    exact CodeAt.source _ (bind_first_slots point slots first next node)
  · exact bind_callback point slots first next node

/-- Both source finalizers preserve the body's class and run a unit cleanup. -/
theorem exit_kinds (path : List Nat) (first next : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) path = some (.eff (.onExit first next))) :
    kindAt (path ++ [0]) = kindAt path ∧ kindAt (path ++ [1]) = .unit := by
  have sub := Node.yieldAt_subset_of_at exitYield path (.eff HostTimeoutSource.program)
    (.eff (.onExit first next)) [] node
  have member : path ∈ exitPaths := sub
    (by simp only [Node.yieldAt, exitYield, List.nil_append, List.mem_singleton])
  rw [exitPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with hp | hp
  all_goals subst path
  all_goals exact ⟨rfl, rfl⟩

/-- Source finalizer invocation resolves only its recorded unit cleanup. -/
theorem exit_callback {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (first next : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.onExit first next)))
    (view : View) (exit : ExitV) (program : NCode) (saved : ExitAt B (kindAt point.path) exit)
    (operation : (interpreter view).finalizerProgram (.fin point) exit = some program) :
    CodeAt B .unit program := by
  have eq : program = resolve HostTimeoutSource.program
      ({ point with completed := view }.childWith 1 (reifyExitVal exit)) :=
    (Option.some.inj operation).symm
  rw [eq, ← (exit_kinds point.path first next node).2]
  let target := ({ point with completed := view }.childWith 1 (reifyExitVal exit))
  have targetGood : EnvAt B target.path target.env := by
    have explicit : EnvAt B (point.path ++ [1]) (point.env ++ [reifyExitVal exit]) := by
      cases point with
      | mk path env fuel tape completed root params call =>
        dsimp only at slots node saved ⊢
        have sub := Node.yieldAt_subset_of_at exitYield path (.eff HostTimeoutSource.program)
          (.eff (.onExit first next)) [] node
        have member : path ∈ exitPaths := sub
          (by simp only [Node.yieldAt, exitYield, List.nil_append, List.mem_singleton])
        rw [exitPaths_eq] at member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with hp | hp
        · subst path
          cases slots with
          | completeExit a b c n delay error => exact .completeBind a b c n delay error exit saved
        · subst path
          cases slots with
          | attemptExit a b c n delay error => exact .cleanupBind a b c n delay error exit saved
    exact explicit
  exact CodeAt.source target targetGood

/-- Source finalizer entry installs a body-preserving saved frame. -/
theorem exit_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (first next : NativeEff) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.onExit first next)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_onExit first next positive]
  refine HeadAt.onExit (kindAt point.path) _ _ false ?_ ?_
  · have child : Node.at_ (.eff HostTimeoutSource.program) (point.child 0).path =
        some (.eff first) := Agreement.at_child node 0
    rw [← Agreement.resolve_of_at child, ← (exit_kinds point.path first next node).1]
    have sub := Node.yieldAt_subset_of_at firstYield point.path (.eff HostTimeoutSource.program)
      (.eff (.onExit first next)) [] node
    have member : point.path ∈ firstPaths := sub
      (by simp only [Node.yieldAt, firstYield, List.nil_append, List.mem_singleton])
    exact CodeAt.source (point.child 0) (first_slots slots member)
  · exact exit_callback point slots first next node

/-- Every selector arm has its parent's successful value class. -/
theorem select_kind (point : Point) (term : Term) (decision : Decision)
    (left right : NativeEff) (first : Bool) (bound : Option Val)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.select term decision left right))) :
    kindAt (point.childBind (cond first 0 1) bound).path = kindAt point.path := by
  have sub := Node.yieldAt_subset_of_at selectYield point.path (.eff HostTimeoutSource.program)
    (.eff (.select term decision left right)) [] node
  have member : point.path ∈ selectPaths := sub
    (by simp only [Node.yieldAt, selectYield, List.nil_append, List.mem_singleton])
  rw [selectPaths_eq] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  have path (i : Nat) : (point.childBind i bound).path = point.path ++ [i] := by
    cases bound <;> rfl
  rw [path]
  rcases member with hp | hp | hp
  all_goals rw [hp]
  all_goals cases first <;> rfl

/-- The actual suspended selector resolves only a body allowed by its lexical assertion. -/
theorem select_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (term : Term) (decision : Decision)
    (left right : NativeEff) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.select term decision left right)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_select term decision left right positive]
  refine HeadAt.suspend (kindAt point.path) point ?_
  intro view
  change CodeAt B (kindAt point.path)
    (suspendBodyAt HostTimeoutSource.program (.body { point with completed := view }))
  cases selected : (evalTerm point.env term).bind decision.decide with
  | none =>
    rw [Agreement.suspendBodyAt_select_bad (q := { point with completed := view }) positive node selected]
    exact CodeAt.head (.failure _ _)
  | some choice =>
    rcases choice with ⟨first, bound⟩
    rw [Agreement.suspendBodyAt_select_of_decide (q := { point with completed := view }) positive node selected]
    rw [← select_kind { point with completed := view } term decision left right first bound node]
    exact CodeAt.source _ (select_slots B { point with completed := view } slots term decision
      left right first bound node selected)

/-- Every valid retry cursor enters an asserted attempt or returns an asserted result. -/
theorem loop_next_code {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (path : point.path = [1,1,1,0])
    (cursorValue : Val) (good : CursorAt B cursorValue) :
    LoopAt B (loopNextAt HostTimeoutSource.program point cursorValue) := by
  cases good with
  | state n delay last lastGood =>
    cases lastGood with
    | @answered body member =>
      change LoopAt B (loopNextAt HostTimeoutSource.program point
        (HostTimeoutSource.cursor n delay (.some body) .none))
      rw [loop_answer_stops B point slots n delay body .none path]
      exact .finish _ (.head (.success (.answered member)))
    | failed error declared =>
      change LoopAt B (loopNextAt HostTimeoutSource.program point
        (HostTimeoutSource.cursor n delay .none (.some error)))
      rw [loop_waiting B point slots n delay (.some error) path]
      by_cases allowed : n = 0 ∨ n < 4
      · rw [if_pos allowed]
        refine .enter _ _ (.state n delay _ (.failed error declared)) ?_
        have iteration := iteration_slots point slots n delay (.some error) path (by omega)
        have kind : kindAt (point.childWith 0 (HostTimeoutSource.cursor n delay .none (.some error))).path =
            .result := by rw [Point.childWith, path]; rfl
        rw [← kind]
        exact .source _ iteration
      · rw [if_neg allowed]
        exact .finish _ (.head (.success (.failed error declared)))
    | empty =>
      change LoopAt B (loopNextAt HostTimeoutSource.program point
        (HostTimeoutSource.cursor n delay .none .none))
      rw [loop_waiting B point slots n delay .none path]
      by_cases allowed : n = 0 ∨ n < 4
      · rw [if_pos allowed]
        refine .enter _ _ (.state n delay _ .empty) ?_
        have iteration := iteration_slots point slots n delay .none path (by omega)
        have kind : kindAt (point.childWith 0 (HostTimeoutSource.cursor n delay .none .none)).path =
            .result := by rw [Point.childWith, path]; rfl
        rw [← kind]
        exact .source _ iteration
      · rw [if_neg allowed]
        exact .finish _ (.head (.success .empty))

/-- A retry resumption retains its asserted last result through the actual step callback. -/
theorem loop_resume_code {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (path : point.path = [1,1,1,0])
    (previous answer : Val) (good : CursorAt B previous) (returned : ValueAt B .result answer) :
    LoopAt B (loopResumeAt HostTimeoutSource.program point previous answer) := by
  cases good with
  | state n delay last lastGood =>
    rw [loop_step_value B point slots n delay last answer path]
    exact loop_next_code point slots path _ (.state _ _ _ returned)

/-- The source's error handler has one generated location. -/
def catchYield : PathYield NativeOp (List Nat) :=
  {«eff» := fun e path => match e with | .catchIf _ _ _ => [path] | _ => []}
def catchPaths : List (List Nat) := Node.foldList catchYield [] (.eff HostTimeoutSource.program)

theorem catchPaths_eq : catchPaths = [[1,1,1,0,0,1]] := by kernel_rfl

theorem catch_site (point : Point) (test : Term) (body handler : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.catchIf test body handler))) : point.path = [1,1,1,0,0,1] := by
  have sub := Node.yieldAt_subset_of_at catchYield point.path (.eff HostTimeoutSource.program)
    (.eff (.catchIf test body handler)) [] node
  have member : point.path ∈ catchPaths := sub
    (by simp only [Node.yieldAt, catchYield, List.nil_append, List.mem_singleton])
  simpa only [catchPaths_eq, List.mem_singleton] using member

/-- The actual typed failure callback either rethrows or records only a failure value. -/
theorem catch_callback {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (test : Term) (body handler : NativeEff)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.catchIf test body handler)))
    (view : View) (cause : CauseV) :
    CodeAt B (kindAt point.path) ((interpreter view).contE (.caughtError point) cause) := by
  have path := catch_site point test body handler node
  have action : (interpreter view).contE (.caughtError point) cause =
      match caughtErrorValue? point.env test cause with
      | some error => resolve HostTimeoutSource.program ({ point with completed := view }.childWith 1 error)
      | none => Prim.failure cause := by
    change contEOf HostTimeoutSource.program (.caughtError { point with completed := view }) cause = _
    simp only [Effect4.Program.contEOf, node]
    rfl
  rw [action]
  cases read : caughtErrorValue? point.env test cause with
  | none => exact .head (.failure _ cause)
  | some error =>
    have declared := caught_retryable { point with completed := view } slots test body handler path node cause error read
    have good := caught_slots { point with completed := view } slots error path declared
    have kind : kindAt ({ point with completed := view }.childWith 1 error).path = kindAt point.path := by
      simp only [Point.childWith, path]
      rfl
    rw [← kind]
    exact .source _ good

/-- Source catch entry installs a result-preserving cause continuation. -/
theorem catch_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (test : Term) (body handler : NativeEff) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path =
      some (.eff (.catchIf test body handler)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_catchIf test body handler positive]
  refine HeadAt.onFailure (kindAt point.path) _ _ ?_ (catch_callback point slots test body handler node)
  have child : Node.at_ (.eff HostTimeoutSource.program) (point.child 0).path =
      some (.eff body) := Agreement.at_child node 0
  rw [← Agreement.resolve_of_at child]
  have sub := Node.yieldAt_subset_of_at firstYield point.path (.eff HostTimeoutSource.program)
    (.eff (.catchIf test body handler)) [] node
  have member : point.path ∈ firstPaths := sub
    (by simp only [Node.yieldAt, firstYield, List.nil_append, List.mem_singleton])
  have kind : kindAt (point.child 0).path = kindAt point.path := by
    simp only [Point.child, catch_site point test body handler node]
    rfl
  rw [← kind]
  exact .source _ (first_slots slots member)

/-- Zero compilation fuel remains a source frontier with the same lexical assertion. -/
theorem zero_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (zero : point.fuel = 0) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at (env_node slots), Agreement.compileEff_at_zero _ zero]
  refine HeadAt.suspend (kindAt point.path) point ?_
  intro view
  change CodeAt B (kindAt point.path)
    (suspendBodyAt HostTimeoutSource.program (.body {point with completed := view}))
  simp only [suspendBodyAt, zero]
  rw [← Agreement.compileEff_at_zero (p := {point with completed := view, fuel := 0})
    (sourceAt point.path) rfl,
    ← Agreement.resolve_of_at (q := {point with completed := view, fuel := 0}) (env_node slots)]
  exact .source {point with completed := view, fuel := 0} slots

/-- A positive-fuel successful source leaf obeys its complete lexical result assertion. -/
theorem success_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (term : Term) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.succeed term)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_succeed term positive]
  cases evaluated : evalTerm point.env term with
  | none => exact .failure _ _
  | some value => exact .success (success_value slots term value node evaluated)

/-- Typed source failures cannot produce an answer body. -/
theorem fail_head {B : List Val} (point : Point) (term : Term) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.fail term)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_fail term positive]
  cases evaluated : evalTerm point.env term <;> exact .failure _ _

/-- Cause-valued source failures cannot produce an answer body. -/
theorem fail_cause_head {B : List Val} (point : Point) (term : CauseTerm) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.failCause term)))
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_failCause term positive]
  cases evaluated : causeOf point.env term <;> exact .failure _ _

/-- The retry source's suspension initializes exactly its asserted empty cursor. -/
theorem loop_suspension {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (path : point.path = [1,1,1,0])
    (fuel : Nat) (positive : point.fuel = fuel + 1) :
    suspendBodyAt HostTimeoutSource.program (.body point) =
      Prim.whileLoop (.loop point) (HostTimeoutSource.cursor 0 100 .none .none) := by
  cases point with
  | mk path env compileFuel tape completed root params call =>
    dsimp only at path slots positive ⊢
    subst path
    cases slots
    rw [positive]
    kernel_rfl

/-- The initial native loop name retains every entry and resumption assertion. -/
theorem loop_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) (path : point.path = [1,1,1,0])
    (fuel : Nat) (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  have compiled : resolve HostTimeoutSource.program point = Prim.suspend (.body point) := by
    cases point with
    | mk path env compileFuel tape completed root params call =>
      dsimp only at path slots positive ⊢
      subst path
      cases slots
      rw [positive]
      kernel_rfl
  rw [compiled]
  refine HeadAt.suspend (kindAt point.path) point ?_
  intro view
  change CodeAt B (kindAt point.path)
    (suspendBodyAt HostTimeoutSource.program (.body {point with completed := view}))
  rw [loop_suspension {point with completed := view} slots path fuel positive]
  have kind : kindAt point.path = .result := by rw [path]; rfl
  rw [kind]
  refine .head (.loop _ _ (.state 0 100 _ .empty) ?_ ?_)
  · intro later cursor good
    change LoopAt B (loopNextAt HostTimeoutSource.program
      {point with completed := later} cursor)
    exact loop_next_code {point with completed := later} slots path cursor good
  · intro later previous answer good returned
    change LoopAt B (loopResumeAt HostTimeoutSource.program
      {point with completed := later} previous answer)
    exact loop_resume_code {point with completed := later} slots path previous answer good returned

/-- The counter/log updates return only unit, even when the heap or term lookup refuses. -/
theorem update_answer (cell : RefKey) (term : Term) (env : List Val)
    (state next : Stores) (value : Val)
    (found : syncOpStep (.refUpdate cell term env) state = some (next, value)) :
    value = .unit := by
  change (refStep (.refUpdate cell term env) state.refs).map
    (fun step => ({state with refs := step.2}, step.1)) = some (next, value) at found
  obtain ⟨answer, step, eq⟩ := Option.map_eq_some_iff.mp found
  change (refPeek state.refs cell).bind (fun old =>
    (evalTerm (env ++ [old]) term).map fun written =>
      (Val.unit, refPoke state.refs cell written)) = some answer at step
  obtain ⟨old, _, computed⟩ := Option.bind_eq_some_iff.mp step
  obtain ⟨written, _, same⟩ := Option.map_eq_some_iff.mp computed
  cases same
  exact (Prod.mk.inj eq).2.symm

/-- A synchronous source row either discards an arbitrary result or receives unit. -/
inductive SourceRow : Kind → NativeOp → Prop
  | make : SourceRow .any .refMake
  | get : SourceRow .any .refGet
  | update (term : Term) : SourceRow .unit (.refUpdateWith term)
  | sleep : SourceRow .unit .sleep
  | external (index : Nat) : SourceRow .body (.external index)

/-- The actual operation thunk satisfies its source row's successful value assertion. -/
theorem source_sync_head {B : List Val} {kind : Kind} {op : NativeOp}
    (allowed : SourceRow kind op) (env : List Val) (request : Val) (operation : SyncOp)
    (writes : WritesAt op env request)
    (found : NativeOp.syncOpOf op env request = some operation) :
    HeadAt B kind (.sync (.op operation)) := by
  cases allowed with
  | make =>
    have shape : operation = .refMake request := Option.some.inj found.symm
    subst operation
    exact .sync .any _ (fun _ _ _ value _ => .any value) (fun _ => .any _) (.make request writes)
  | get =>
    have shape : ∃ key, operation = .refGet ⟨key⟩ := by
      unfold NativeOp.syncOpOf at found
      repeat' split at found
      all_goals aesop
    rcases shape with ⟨key, rfl⟩
    exact .sync .any _ (fun _ _ _ value _ => .any value) (fun _ => .any _) (.get ⟨key⟩)
  | update term =>
    have shape : ∃ key, operation = .refUpdate ⟨key⟩ term env := by
      unfold NativeOp.syncOpOf at found
      repeat' split at found
      all_goals aesop
    rcases shape with ⟨key, rfl⟩
    refine .sync .unit _ ?_ (fun _ => .unit) (.update ⟨key⟩ term env writes)
    intro view state next value step
    change syncOpStep (.refUpdate ⟨key⟩ term env) state = some (next, value) at step
    rw [update_answer _ _ _ _ _ _ step]
    exact .unit
  | sleep => cases found
  | external index => cases found

/-- The actual asynchronous route either refuses or registers the source's body/unit answer. -/
theorem source_async_head {B : List Val} {kind : Kind} {op : NativeOp}
    (allowed : SourceRow kind op) (point : Point) (term : Term) :
    HeadAt B kind (asyncRoute op term point) := by
  cases allowed with
  | make | get | update _ => exact .failure _ _
  | external index =>
    unfold asyncRoute
    cases evalTerm point.env term with
    | none => exact .failure _ _
    | some value => exact .external _ _ _
  | sleep =>
    unfold asyncRoute
    cases (evalTerm point.env term).bind NativeOp.sleepMillisOf with
    | none => exact .failure _ _
    | some millis =>
      cases millis with
      | zero => exact .yieldNow _
      | succ n => exact .sleep _

/-- The synchronous dispatch consumes the exact selected operation thunk. -/
theorem sync_source_dispatch {B : List Val} {kind : Kind} {op : NativeOp}
    (allowed : SourceRow kind op) (point : Point) (term : Term)
    (writes : ∀ request, evalTerm point.env term = some request → WritesAt op point.env request) :
    HeadAt B kind (match evalTerm point.env term with
      | some request => match NativeOp.syncOpOf op point.env request with
        | some operation => .sync (.op operation)
        | none => badShape
      | none => badShape) := by
  cases result : evalTerm point.env term with
  | none => exact .failure _ _
  | some request =>
    dsimp only
    cases found : NativeOp.syncOpOf op point.env request with
    | none => exact .failure _ _
    | some operation => exact source_sync_head allowed point.env request operation (writes request result) found

/-- Every admitted concrete source row expands to the appropriate native head. -/
theorem perform_head {B : List Val} (point : Point) (op : NativeOp) (term : Term)
    (allowed : SourceRow (kindAt point.path) op) (fuel : Nat)
    (node : Node.at_ (.eff HostTimeoutSource.program) point.path = some (.eff (.perform op term)))
    (positive : point.fuel = fuel + 1)
    (writes : ∀ request, evalTerm point.env term = some request → WritesAt op point.env request) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  rw [Agreement.resolve_of_at node, Agreement.compileEff_perform op term positive]
  generalize expected : kindAt point.path = kind at allowed ⊢
  cases allowed with
  | external index => exact source_async_head (.external index) point term
  | sleep => exact source_async_head .sleep point term
  | make => exact sync_source_dispatch .make point term writes
  | get => exact sync_source_dispatch .get point term writes
  | update update => exact sync_source_dispatch (.update update) point term writes

/-- Source descriptors only expose existing constructor fields at a concrete source point. -/
def bindParts (path : List Nat) : NativeEff × NativeEff :=
  match sourceAt path with
  | .bind first next => (first, next)
  | _ => (.succeed (.lit .unit), .succeed (.lit .unit))
def exitParts (path : List Nat) : NativeEff × NativeEff :=
  match sourceAt path with
  | .onExit first next => (first, next)
  | _ => (.succeed (.lit .unit), .succeed (.lit .unit))
def selectParts (path : List Nat) : Term × Decision × NativeEff × NativeEff :=
  match sourceAt path with
  | .select term decision first next => (term, decision, first, next)
  | _ => (.lit .unit, .bool, .succeed (.lit .unit), .succeed (.lit .unit))
def catchParts (path : List Nat) : Term × NativeEff × NativeEff :=
  match sourceAt path with
  | .catchIf term first next => (term, first, next)
  | _ => (.lit .unit, .succeed (.lit .unit), .succeed (.lit .unit))
def performParts (path : List Nat) : NativeOp × Term :=
  match sourceAt path with
  | .perform op term => (op, term)
  | _ => (.refMake, .lit .unit)
def succeedPart (path : List Nat) : Term :=
  match sourceAt path with
  | .succeed term => term
  | _ => .lit .unit

def updatePart (path : List Nat) : Term :=
  match (performParts path).1 with
  | .refUpdateWith term => term
  | _ => .lit .unit
def failPart (path : List Nat) : Term :=
  match sourceAt path with
  | .fail term => term
  | _ => .lit .unit
def failCausePart (path : List Nat) : CauseTerm :=
  match sourceAt path with
  | .failCause term => term
  | _ => .interrupt none

/-- The actual timeout race has exactly its source attempt and timer entrants. -/
theorem race_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env)
    (path : point.path = [1,1,1,0,0,1,0,0,0]) (fuel : Nat)
    (positive : point.fuel = fuel + 1) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  let attempt := ((point.child 0).child 0).child 0
  let timer := (((point.child 0).child 0).child 1).child 0
  let race : NAction := .raceAllFirst
    [resolve HostTimeoutSource.program attempt, resolve HostTimeoutSource.program timer]
    (some ((point.child 0).child 0).path)
  have compiled : resolve HostTimeoutSource.program point = .withFiber (.act point) := by
    cases point with
    | mk path env fuel tape completed root params call =>
      dsimp only at path slots positive ⊢
      subst path
      cases slots
      rw [positive]
      kernel_rfl
  have operation (view : View) : (interpreter view).withFiberOf (.act point) = some race := by
    cases point with
    | mk path env fuel tape completed root params call =>
      dsimp only [interpreter, race, attempt, timer] at path slots ⊢
      subst path
      cases slots
      kernel_rfl
  have entrants : ∀ code ∈ [resolve HostTimeoutSource.program attempt,
      resolve HostTimeoutSource.program timer], CodeAt B .body code := by
    intro code member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with eq | eq
    · rw [eq]
      have target : kindAt attempt.path = .body := by simp only [attempt, Point.child, path]; rfl
      rw [← target]
      refine .source attempt ?_
      cases point with
      | mk path env fuel tape completed root params call =>
        dsimp only [attempt, Point.child] at path slots ⊢
        subst path
        cases slots with
        | race a b c n delay error => exact .attemptExit a b c n delay error
    · rw [eq]
      have target : kindAt timer.path = .body := by simp only [timer, Point.child, path]; rfl
      rw [← target]
      refine .source timer ?_
      cases point with
      | mk path env fuel tape completed root params call =>
        dsimp only [timer, Point.child] at path slots ⊢
        subst path
        cases slots with
        | race a b c n delay error => exact .timerBind a b c n delay error
  rw [compiled]
  have kind : kindAt point.path = .body := by rw [path]; rfl
  rw [kind]
  exact .action .body (.act point) (fun _ => race) operation (fun _ => .race _ _ entrants)

/-- The existing application signature supplies its argument data for exact source equations. -/
def writeArgs : Term → Terms
  | .app _ args => args
  | _ => .nil

/-- Every concrete lexical assertion expands to an asserted actual native head.
The complete source census supplies all thirty-eight cases, at every compilation fuel. -/
theorem source_head {B : List Val} (point : Point)
    (slots : EnvAt B point.path point.env) :
    HeadAt B (kindAt point.path) (resolve HostTimeoutSource.program point) := by
  cases point with
  | mk path env compileFuel tape completed root params call =>
    cases compileFuel with
    | zero => exact zero_head _ slots rfl
    | succ fuel =>
      have kept := slots
      cases slots
      case start =>
        exact bind_head _ kept (bindParts []).1 (bindParts []).2 fuel (by kernel_rfl) rfl
      case countMake =>
        have row : (performParts [0]).1 = .refMake := by kernel_rfl
        have allowed : SourceRow (kindAt [0]) (performParts [0]).1 := by
          rw [row]
          exact .make
        exact perform_head _ (performParts [0]).1 (performParts [0]).2
          allowed fuel (by kernel_rfl) rfl (by
            intro value found
            rw [row]
            have term : (performParts [0]).2 = .lit (.nat 0) := by kernel_rfl
            rw [term] at found
            exact nat_outer _ 0 value found)
      case endedMakeBind =>
        exact bind_head _ kept (bindParts [1]).1 (bindParts [1]).2 fuel (by kernel_rfl) rfl
      case endedMake =>
        have row : (performParts [1,0]).1 = .refMake := by kernel_rfl
        have allowed : SourceRow (kindAt [1,0]) (performParts [1,0]).1 := by
          rw [row]
          exact .make
        exact perform_head _ (performParts [1,0]).1 (performParts [1,0]).2
          allowed fuel (by kernel_rfl) rfl (by
            intro value found
            rw [row]
            have empty : ∀ env, evalTerm env (performParts [1,0]).2 = some (.list []) := by
              intro env; kernel_rfl
            rw [empty] at found
            cases found
            exact .list [])
      case completedMakeBind =>
        exact bind_head _ kept (bindParts [1,1]).1 (bindParts [1,1]).2 fuel (by kernel_rfl) rfl
      case completedMake =>
        have row : (performParts [1,1,0]).1 = .refMake := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,0]) (performParts [1,1,0]).1 := by
          rw [row]
          exact .make
        exact perform_head _ (performParts [1,1,0]).1 (performParts [1,1,0]).2
          allowed fuel (by kernel_rfl) rfl (by
            intro value found
            rw [row]
            have empty : ∀ env, evalTerm env (performParts [1,1,0]).2 = some (.list []) := by
              intro env; kernel_rfl
            rw [empty] at found
            cases found
            exact .list [])
      case finishBind =>
        exact bind_head _ kept (bindParts [1,1,1]).1 (bindParts [1,1,1]).2 fuel (by kernel_rfl) rfl
      case loop =>
        exact loop_head _ kept rfl fuel rfl
      case iteration =>
        exact bind_head _ kept (bindParts [1,1,1,0,0]).1 (bindParts [1,1,1,0,0]).2 fuel (by kernel_rfl) rfl
      case delaySelect =>
        exact select_head _ kept (selectParts [1,1,1,0,0,0]).1 (selectParts [1,1,1,0,0,0]).2.1
          (selectParts [1,1,1,0,0,0]).2.2.1 (selectParts [1,1,1,0,0,0]).2.2.2 fuel (by kernel_rfl) rfl
      case delaySleep =>
        have row : (performParts [1,1,1,0,0,0,0]).1 = .sleep := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,0,0]) (performParts [1,1,1,0,0,0,0]).1 := by
          rw [row]
          exact .sleep
        exact perform_head _ (performParts [1,1,1,0,0,0,0]).1 (performParts [1,1,1,0,0,0,0]).2
          allowed fuel (by kernel_rfl) rfl (fun _ _ => True.intro)
      case delayZero =>
        exact success_head _ kept (succeedPart [1,1,1,0,0,0,1]) fuel (by kernel_rfl) rfl
      case «catch» =>
        exact catch_head _ kept (catchParts [1,1,1,0,0,1]).1 (catchParts [1,1,1,0,0,1]).2.1
          (catchParts [1,1,1,0,0,1]).2.2 fuel (by kernel_rfl) rfl
      case answerBind =>
        exact bind_head _ kept (bindParts [1,1,1,0,0,1,0]).1 (bindParts [1,1,1,0,0,1,0]).2 fuel (by kernel_rfl) rfl
      case completeExit =>
        exact exit_head _ kept (exitParts [1,1,1,0,0,1,0,0]).1 (exitParts [1,1,1,0,0,1,0,0]).2 fuel (by kernel_rfl) rfl
      case race =>
        exact race_head _ kept rfl fuel rfl
      case attemptExit =>
        exact exit_head _ kept (exitParts [1,1,1,0,0,1,0,0,0,0,0,0]).1 (exitParts [1,1,1,0,0,1,0,0,0,0,0,0]).2 fuel (by kernel_rfl) rfl
      case countBind =>
        exact bind_head _ kept (bindParts [1,1,1,0,0,1,0,0,0,0,0,0,0]).1 (bindParts [1,1,1,0,0,1,0,0,0,0,0,0,0]).2 fuel (by kernel_rfl) rfl
      case countUpdate =>
        have row : (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,0]).1 = .refUpdateWith (updatePart [1,1,1,0,0,1,0,0,0,0,0,0,0,0]) := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,0,0,0,0,0,0]) (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,0]).1 := by
          rw [row]
          exact .update _
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,0]).1 (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,0]).2
          allowed fuel (by kernel_rfl) rfl (by
            intro request _
            rw [row]
            intro old value found
            have term : updatePart [1,1,1,0,0,1,0,0,0,0,0,0,0,0] = .app "succ"
                (writeArgs (updatePart [1,1,1,0,0,1,0,0,0,0,0,0,0,0])) := by kernel_rfl
            rw [term] at found
            exact app_outer .succ _ _ value found)
      case http =>
        have row : (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,1]).1 = .external 0 := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,0,0,0,0,0,1]) (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,1]).1 := by
          rw [row]
          exact .external _
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,1]).1 (performParts [1,1,1,0,0,1,0,0,0,0,0,0,0,1]).2
          allowed fuel (by kernel_rfl) rfl (fun _ _ => True.intro)
      case cleanupBind =>
        exact bind_head _ kept (bindParts [1,1,1,0,0,1,0,0,0,0,0,0,1]).1 (bindParts [1,1,1,0,0,1,0,0,0,0,0,0,1]).2 fuel (by kernel_rfl) rfl
      case cleanupRead =>
        have row : (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,0]).1 = .refGet := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,0,0,0,0,1,0]) (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,0]).1 := by
          rw [row]
          exact .get
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,0]).1 (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,0]).2
          allowed fuel (by kernel_rfl) rfl (fun _ _ => True.intro)
      case cleanupNoteBind =>
        exact bind_head _ kept (bindParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1]).1 (bindParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1]).2 fuel (by kernel_rfl) rfl
      case cleanupNote =>
        have row : (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]).1 = .refUpdateWith (updatePart [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]) := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]) (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]).1 := by
          rw [row]
          exact .update _
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]).1 (performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]).2
          allowed fuel (by kernel_rfl) rfl (by
            intro request _
            rw [row]
            intro old value found
            have term : updatePart [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0] = .app "append"
                (writeArgs (updatePart [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0])) := by kernel_rfl
            rw [term] at found
            exact app_outer .append _ _ value found)
      case cleanupDone =>
        exact success_head _ kept (succeedPart [1,1,1,0,0,1,0,0,0,0,0,0,1,1,1]) fuel (by kernel_rfl) rfl
      case timerBind =>
        exact bind_head _ kept (bindParts [1,1,1,0,0,1,0,0,0,0,0,1,0]).1 (bindParts [1,1,1,0,0,1,0,0,0,0,0,1,0]).2 fuel (by kernel_rfl) rfl
      case timerSleep =>
        have row : (performParts [1,1,1,0,0,1,0,0,0,0,0,1,0,0]).1 = .sleep := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,0,0,0,1,0,0]) (performParts [1,1,1,0,0,1,0,0,0,0,0,1,0,0]).1 := by
          rw [row]
          exact .sleep
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,0,0,0,1,0,0]).1 (performParts [1,1,1,0,0,1,0,0,0,0,0,1,0,0]).2
          allowed fuel (by kernel_rfl) rfl (fun _ _ => True.intro)
      case timerFail =>
        exact fail_head _ (failPart [1,1,1,0,0,1,0,0,0,0,0,1,0,1]) fuel (by kernel_rfl) rfl
      case completeBind =>
        exact bind_head _ kept (bindParts [1,1,1,0,0,1,0,0,1]).1 (bindParts [1,1,1,0,0,1,0,0,1]).2 fuel (by kernel_rfl) rfl
      case completeRead =>
        have row : (performParts [1,1,1,0,0,1,0,0,1,0]).1 = .refGet := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,1,0]) (performParts [1,1,1,0,0,1,0,0,1,0]).1 := by
          rw [row]
          exact .get
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,1,0]).1 (performParts [1,1,1,0,0,1,0,0,1,0]).2
          allowed fuel (by kernel_rfl) rfl (fun _ _ => True.intro)
      case completeNote =>
        have row : (performParts [1,1,1,0,0,1,0,0,1,1]).1 = .refUpdateWith (updatePart [1,1,1,0,0,1,0,0,1,1]) := by kernel_rfl
        have allowed : SourceRow (kindAt [1,1,1,0,0,1,0,0,1,1]) (performParts [1,1,1,0,0,1,0,0,1,1]).1 := by
          rw [row]
          exact .update _
        exact perform_head _ (performParts [1,1,1,0,0,1,0,0,1,1]).1 (performParts [1,1,1,0,0,1,0,0,1,1]).2
          allowed fuel (by kernel_rfl) rfl (by
            intro request _
            rw [row]
            intro old value found
            have term : updatePart [1,1,1,0,0,1,0,0,1,1] = .app "append"
                (writeArgs (updatePart [1,1,1,0,0,1,0,0,1,1])) := by kernel_rfl
            rw [term] at found
            exact app_outer .append _ _ value found)
      case answer =>
        exact success_head _ kept (succeedPart [1,1,1,0,0,1,0,1]) fuel (by kernel_rfl) rfl
      case caught =>
        exact success_head _ kept (succeedPart [1,1,1,0,0,1,1]) fuel (by kernel_rfl) rfl
      case result =>
        exact select_head _ kept (selectParts [1,1,1,1]).1 (selectParts [1,1,1,1]).2.1
          (selectParts [1,1,1,1]).2.2.1 (selectParts [1,1,1,1]).2.2.2 fuel (by kernel_rfl) rfl
      case errorSelect =>
        exact select_head _ kept (selectParts [1,1,1,1,0]).1 (selectParts [1,1,1,1,0]).2.1
          (selectParts [1,1,1,1,0]).2.2.1 (selectParts [1,1,1,1,0]).2.2.2 fuel (by kernel_rfl) rfl
      case emptyFail =>
        exact fail_cause_head _ (failCausePart [1,1,1,1,0,0]) fuel (by kernel_rfl) rfl
      case lastFail =>
        exact fail_head _ (failPart [1,1,1,1,0,1]) fuel (by kernel_rfl) rfl
      case rootAnswer =>
        exact success_head _ kept (succeedPart [1,1,1,1,1]) fuel (by kernel_rfl) rfl

end Test.Dogfood.Proofs.HostTimeoutNative
