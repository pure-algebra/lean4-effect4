import Effect4.Laws.Program.SourceScope
import Effect4.Laws.Program.HeapSites

/-!
# Native writer transfers from source scope

Concept: store-typing R4, serving `HeapSites.heap_sites_keep` and QueueWorkers `Assertions.jobs_step`.
These consumers join actual compiler callbacks, source-site facts and exact native commands.
They retain source scope and site premises explicitly.
They establish no whole-configuration provenance closure, custody, progress or outside observation agreement.
-/

set_option autoImplicit false

namespace Effect4.Program.SourceScope

open Effect4 Effect4.Machine Effect4.Program
open Effect4.Program.HeapSites

/-- The source-site premise applies to the actual compiled writer and its captured environment.
Consumer: Atomic and Queue native writer preservation. -/
theorem resolve_modify_keeps (root : NativeEff) (P : Val → Prop) (p : Point)
    (term request : Term) (q : RefKey) (fuel : Nat)
    (found : Node.at_ (.eff root) p.path = some (.eff (.perform (.refModifyWith term) request)))
    (hscope : At root p) (sites : SitesKeep root P)
    (positive : p.fuel = fuel + 1) (reads : evalTerm p.env request = some (.cell q)) :
    resolve root p = .sync (.op (.refModify q term p.env)) ∧
      OpKeeps P (.refModify q term p.env) := by
  refine ⟨(resolve_at root p _ found).trans
    (StoreExecution.compile_modify term request p fuel q positive reads), ?_⟩
  apply sites p.path (.refModifyWith term) request p.env (.cell q) (.refModify q term p.env)
    found hscope reads
  cases q
  rfl

/-- An actual compiled writer command keeps the heap's predicate before any owed resumes.
Consumer: Atomic `heap_sites_keep` and Queue command preservation.
The source and scope hypotheses remain explicit. -/
theorem modify_loop_keeps (root : NativeEff) (table : RowTable) (P : Val → Prop)
    (m : Api.Machine) (id : FiberId)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx)
    (term request : Term) (p : Point) (fuel : Nat) (q : RefKey)
    (state : Stores) (value : Val) (yielding : Bool)
    (rest : List (Cmd EffName EffThunk Val Err Defect FiberId Ann))
    (found : m.fiber? id = some f)
    (source : Node.at_ (.eff root) p.path = some (.eff (.perform (.refModifyWith term) request)))
    (hs : At root p) (sites : SitesKeep root P)
    (current : f.frame.current = resolve root p)
    (positive : p.fuel = fuel + 1) (reads : evalTerm p.env request = some (.cell q))
    (interrupt : f.frame.deferredInterrupt = false) (override : f.yieldOverride = none)
    (budget : f.currentOpCount + 1 < f.maxOpsBeforeYield)
    (answer : syncOpStep (.refModify q term p.env) m.state = some (state, value))
    (heap : HeapOk P m.state.refs) :
    driveStep (evaluator := evaluatorFor root table) (interpOf root table) m
        (.loop id yielding) rest =
      (({ m with state }).update
        { countOp f with frame := { f.frame with current := .success value } },
       [.drainDue, .deliver id yielding] ++ rest) ∧ HeapOk P state.refs := by
  obtain ⟨resolved, keeps⟩ := resolve_modify_keeps root P p term request q fuel
    source hs sites positive reads
  rw [resolved] at current
  exact ⟨ControlSteps.loop_sync_op root table m id f (.refModify q term p.env)
    state value yielding rest found current interrupt override budget answer,
    keeps m.state state value answer heap⟩

end Effect4.Program.SourceScope
