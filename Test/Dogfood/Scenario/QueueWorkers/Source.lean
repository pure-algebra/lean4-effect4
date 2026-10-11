import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Program.WriterScope

/-!
# The queue crew's first take writer

Concept: translation-simulation R10, serving QueueWorkers `Assertions.jobs_step`.
The source facts range over every job count and successful crew build.
The command consumer commits the actual source writer on an arbitrary fiber and retains its command suffix.
The source level describes lexical length only; it establishes no cell alias or value typing.
The current-point, store-answer and command-budget premises remain explicit.
This consumer establishes no whole-run source ownership or job custody.
-/

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

namespace Test.Dogfood.Scenario.QueueWorkers.Source

open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Programs

/-- The first worker's take attempt, in the existing source address scheme. -/
def takePath : List Nat :=
  [1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 1, 0]

/-- The actual elaborated take term; `take_source` excludes the fallback. -/
def takeTerm : Term :=
  match Node.at_ (.eff (queueProgram 0)) takePath with
  | some (.eff (.perform (.refModifyWith term) _)) => term
  | _ => .lit .unit

/-- Every job count has this same take writer and captured queue request.
Consumer: `take_loop`. -/
theorem take_source (total : Nat) :
    Node.at_ (.eff (queueProgram total)) takePath =
      some (.eff (.perform (.refModifyWith takeTerm) (.var 0))) := by
  kernel_rfl

/-- The generated binder table gives twelve captured values at this writer.
Consumer: `take_scope`. -/
theorem take_level (total : Nat) :
    SourceScope.levelAt (.eff (queueProgram total)) 0 takePath = some 12 := by
  kernel_rfl

/-- A point at the actual writer with its lexical length satisfies the shared scope predicate.
Consumer: the heap writer transfer at this program site. -/
theorem take_scope (total : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b)
    (p : Point) (hp : p.path = takePath) (he : p.env.length = 12) : SourceScope.At b.program p := by
  unfold SourceScope.At
  rw [queue_built_program total b hb, hp, he]
  exact take_level total

/-- One actual first-worker take writer command commits before all pending resumes.
Consumer: QueueWorkers `Assertions.jobs_step`.
The point's current code, queue cell reading and exact term answer remain explicit. -/
theorem take_loop (total : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b)
    (m : Api.Machine) (id : FiberId)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (p : Point) (hp : p.path = takePath) (fuel : Nat) (q : RefKey)
    (state : Stores) (value : Val) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : m.fiber? id = some f) (current : f.frame.current = resolve b.program p)
    (positive : p.fuel = fuel + 1) (reads : evalTerm p.env (.var 0) = some (.cell q))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (answer : syncOpStep (.refModify q takeTerm p.env) m.state = some (state, value)) :
    driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := .success value } },
       [.drainDue, .deliver id yielding] ++ rest) := by
  have source : Node.at_ (.eff b.program) p.path =
      some (.eff (.perform (.refModifyWith takeTerm) (.var 0))) := by
    rw [queue_built_program total b hb, hp]
    exact take_source total
  rw [SourceScope.resolve_at b.program p _ source] at current
  exact StoreExecution.modify_loop b.program b.table m id f takeTerm (.var 0) p fuel q
    state value yielding rest found current positive reads interrupt override budget answer

/-- At the concrete source site, the command also keeps a heap predicate certified at every writer.
Consumer: the native writer closure used by `Assertions.jobs_step`.
The source-scope and site premises remain explicit. -/
theorem take_loop_keeps (total : Nat) (b : Api.Built) (hb : Api.Author.build (crew total) = .ok b)
    (P : Val → Prop) (m : Api.Machine) (id : FiberId)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (p : Point) (hp : p.path = takePath) (he : p.env.length = 12) (fuel : Nat) (q : RefKey)
    (state : Stores) (value : Val) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : m.fiber? id = some f) (current : f.frame.current = resolve b.program p)
    (positive : p.fuel = fuel + 1) (reads : evalTerm p.env (.var 0) = some (.cell q))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (answer : syncOpStep (.refModify q takeTerm p.env) m.state = some (state, value))
    (sites : HeapSites.SitesKeep b.program P) (heap : HeapSites.HeapOk P m.state.refs) :
    driveStep (evaluator := evaluatorFor b.program b.table) (interpOf b.program b.table) m
        (.loop id yielding) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := .success value } },
       [.drainDue, .deliver id yielding] ++ rest) ∧ HeapSites.HeapOk P state.refs := by
  have source : Node.at_ (.eff b.program) p.path =
      some (.eff (.perform (.refModifyWith takeTerm) (.var 0))) := by
    rw [queue_built_program total b hb, hp]
    exact take_source total
  exact SourceScope.modify_loop_keeps b.program b.table P m id f takeTerm (.var 0) p fuel q
    state value yielding rest found source (take_scope total b hb p hp he) sites current
    positive reads interrupt override budget answer heap

end Test.Dogfood.Scenario.QueueWorkers.Source
