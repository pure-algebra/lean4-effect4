import Test.Dogfood.Proofs.QueueWorkersCustodyTransfers
import Effect4.Laws.Program.AnswerSlots.PrefixStable
import Effect4.Laws.Program.CrewLogs.Writes

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.Assertions.jobs_step, at the worker's actual assignment write.
The existing prefix graph retains a resolved payload after the actual bind captures it.
The native write spends that same occurrence in the conserving ledger.
Whole-history source-role and request ownership remain separate obligations.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustody
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario.QueueWorkers

/-- An actual bind rebases the existing prefix graph on its full captured environment and answer. -/
theorem bound_prefix (root : NativeEff) (fragment : SourceScope.Fragment root) (table : RowTable)
    (view : List (FiberId × ExitV)) (point : Point) (value : Val) :
    AnswerSlots.CodeAt (point.env ++ [value]) ((interpAt root view table).contA (.cont point) value) := by
  change AnswerSlots.CodeAt (point.env ++ [value])
    (resolve root (({point with completed := view} : Point).childWith 1 value))
  apply AnswerSlots.resolve_at root fragment
  exact List.take_length

/-- The worker appends the resolved payload and its own literal identity. -/
def assignmentTerm (oldIndex jobIndex worker : Nat) : Term :=
  .app "append" (.cons (.var oldIndex) (.cons
    (.app "cons" (.cons (.app "pair" (.cons (.var jobIndex) (.cons (.lit (.nat worker)) .nil)))
      (.cons (.app "nil" .nil) .nil))) .nil))

/-- The exact assignment expression reads the captured job and the actual old list. -/
theorem assignment_value (env : List Val) (index job worker : Nat)
    (captured : env[index]? = some (.nat job)) (old : Val) :
    evalTerm (env ++ [old]) (assignmentTerm env.length index worker) =
      old.asList?.map (fun values => .list (values ++ [gave job worker])) := by
  have oldSlot : (env ++ [old])[env.length]? = some old := List.getElem?_concat_length
  have jobSlot : (env ++ [old])[index]? = some (.nat job) :=
    (List.getElem?_append_left (List.getElem?_eq_some_iff.mp captured).1).trans captured
  simp only [assignmentTerm, evalTerm, evalTerms, oldSlot, jobSlot, Option.bind_some,
    nativeAtom, NativeAtom.ofName?]
  change (old.asList?.bind fun values => some (Val.list (values ++ [gave job worker]))) = _
  cases old.asList? <;> rfl

/-- The actual assignment primitive appends exactly the captured payload, without reading a replacement. -/
theorem assignment_sync (env : List Val) (index job worker : Nat)
    (captured : env[index]? = some (.nat job)) (stores : Stores) (old : List Val)
    (read : refPeek stores.refs ⟨3⟩ = some (.list old)) :
    syncOpStep (.refUpdate ⟨3⟩ (assignmentTerm env.length index worker) env) stores =
      some ({stores with refs := refPoke stores.refs ⟨3⟩ (.list (old ++ [gave job worker]))}, .unit) := by
  have computed := assignment_value env index job worker captured (.list old)
  have written := refStep_update stores.refs ⟨3⟩ (assignmentTerm env.length index worker) env
    (.list old) (.list (old ++ [gave job worker])) read computed
  change (refStep _ stores.refs).map _ = _
  rw [written]
  rfl

/-- The assignment's returned world retires its exact worker credit. -/
def assignWorld (world : World) (token job worker : Nat) : World :=
  setStage {world with ledger := assignLedger world.ledger job worker} token (.spent job)

/-- Assignment cannot revive a request or alter another request's phase. -/
theorem assignWorld_future (world : World) (token job worker : Nat)
    (phase : world.requests token = .holding job) : Future world (assignWorld world token job worker) := by
  intro selected
  by_cases same : selected = token
  · subst selected
    simpa only [assignWorld, setStage, ↓reduceIte, phase] using Advances.spend job
  · simpa only [assignWorld, setStage, if_neg same] using Advances.refl (world.requests selected)

/-- One actual assignment simultaneously changes the heap, ledger and stale-answer class. -/
theorem assignment_commit (world : World) (token job worker : Nat)
    (phase : world.requests token = .holding job) (holding : job ∈ world.ledger.custody)
    (conserved : world.ledger.Conserved) (env : List Val) (index : Nat)
    (captured : env[index]? = some (.nat job)) (stores : Stores)
    (read : refPeek stores.refs ⟨3⟩ = some (.list (world.ledger.assigned.map (fun p => gave p.1 p.2)))) :
    syncOpStep (.refUpdate ⟨3⟩ (assignmentTerm env.length index worker) env) stores =
      some ({stores with refs := (refPoke stores.refs ⟨3⟩
        (.list ((assignWorld world token job worker).ledger.assigned.map (fun p => gave p.1 p.2))))}, .unit) ∧
    Future world (assignWorld world token job worker) ∧
    (assignWorld world token job worker).ledger.Conserved ∧
    ValueAt (assignWorld world token job worker) (.spent token) .unit := by
  refine ⟨?_, assignWorld_future world token job worker phase,
    assignLedger_conserved world.ledger job worker holding conserved, ?_⟩
  · simpa only [assignWorld, setStage, assignLedger, List.map_append, List.map_cons, List.map_nil]
      using assignment_sync env index job worker captured stores _ read
  · exact ⟨job, by simp only [assignWorld, setStage, ↓reduceIte]⟩

end Test.Dogfood.Proofs.QueueWorkersCustody
