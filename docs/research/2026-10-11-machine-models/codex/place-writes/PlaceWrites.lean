import Test.Dogfood.Proofs.HostTimeoutNumberEntry
import Test.Dogfood.Scenario.Atomic.WriterPhase
import Test.Dogfood.Scenario.Programs
import Effect4.Laws.Machine.PrimWeights
import ProofGraph.AxiomAudit

/-!
Concept: scope-lifetime-finalization R11 and store-typing R4.
Consumers: Timeout.cleanup_keeps, Timeout.retries_declared, Atomic.Cleanup.log_debits,
and Workers.Assertions.logs_step.
Research probe: exact native writer leaves exchange code potential for data potential.
The model counts a selected operation, not callbacks or a reached history.
No second syntax traversal, machine-store label inference, or history producer is introduced.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace PlaceWrites
open Effect4 Effect4.Machine Effect4.Program Effect4.Laws.Auto
open Test.Dogfood.Proofs

/-- One selected actual store row supplies the leaf of the existing native fold. -/
def model (operation : SyncOp) (mass : Nat) : PrimWeights.Model EffName EffThunk where
  name := fun _ => 0
  thunk := fun suspended => match suspended with
    | .op actual => if actual = operation then mass else 0
    | _ => 0

abbrev current (operation : SyncOp) (mass : Nat) (code : NCode) : Nat :=
  cata_prim (PrimWeights.currentAlgebra (model operation mass)) code

theorem leaf (operation : SyncOp) (mass : Nat) :
    current operation mass (.sync (.op operation)) = mass := by
  change (if operation = operation then mass else 0) = mass
  rw [if_pos rfl]

theorem answered (operation : SyncOp) (mass : Nat) (value : Val) :
    current operation mass (.success value) = 0 := rfl

/-- The same actual append expression accepts literal, acquired, and paired entries. -/
def appendOne (level : Nat) (entry : Term) : Term :=
  .app "append" (.cons (.var level) (.cons
    (.app "cons" (.cons entry (.cons (.app "nil" .nil) .nil))) .nil))

/-- A local data place reads the selected reference without introducing a heap carrier. -/
def data (weight : Val → Nat) (refs : RefHeap) (cell : RefKey) : Nat :=
  match refPeek refs cell with
  | some (.list entries) => (entries.map weight).sum
  | _ => 0

/-- Exact evaluation and the real row kernel supply one local append debit.
The premises do not certify a source site, a mint, or a command history. -/
theorem append_debit (weight : Val → Nat) (cell : RefKey) (term : Term) (env : List Val)
    (state : Stores) (entries : List Val) (entry : Val)
    (read : refPeek state.refs cell = some (.list entries))
    (evaluated : evalTerm (env ++ [.list entries]) term = some (.list (entries ++ [entry]))) :
    let operation := SyncOp.refUpdate cell term env
    let next := {state with refs := refPoke state.refs cell (.list (entries ++ [entry]))}
    syncOpStep operation state = some (next, .unit) ∧
    data weight next.refs cell + current operation (weight entry) (.success .unit) =
      data weight state.refs cell + current operation (weight entry) (.sync (.op operation)) := by
  dsimp only
  constructor
  · change (refStep (.refUpdate cell term env) state.refs).map _ = _
    rw [refStep_update state.refs cell term env (.list entries) (.list (entries ++ [entry])) read evaluated]
    rfl
  · rw [answered, leaf]
    unfold data
    rw [refPeek_poke_self state.refs cell (.list (entries ++ [entry])) (.list entries) read, read]
    simp only [List.map_append, List.map_cons, List.map_nil, List.sum_append,
      List.sum_cons, List.sum_nil, Nat.add_zero]

/-- The actual Timeout cleanup term comes from the existing source lookup. -/
def cleanupTerm : Term :=
  match (HostTimeoutNative.performParts [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]).1 with
  | .refUpdateWith term => term
  | _ => .lit .unit

/-- The existing source slots resolve to the actual second-cell cleanup writer. -/
theorem timeout_cleanup_code (fuel delay seen : Nat) (n : Fin 4) (error : Val) (exit : ExitV) :
    resolve HostTimeoutSource.program
      (HostTimeoutNumberSteps.sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0]
        (HostTimeoutSlots.ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]) fuel) =
      .sync (.op (.refUpdate ⟨1⟩ cleanupTerm
        (HostTimeoutSlots.ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay error ++
          [reifyExitVal exit, .nat seen]))) := by kernel_rfl

/-- The exact existing cleanup equation exchanges one leaf for one data entry.
Its saved number is arbitrary; order and attempt ownership remain separate premises. -/
theorem timeout_cleanup_debit (view : HostTimeoutFlow.View) (state : Stores) (fuel count seen delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (entries completed : List Val) :
    let env := HostTimeoutSlots.ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay error ++
      [reifyExitVal exit, .nat seen]
    let operation := SyncOp.refUpdate ⟨1⟩ cleanupTerm env
    HostTimeoutNumberSteps.sourceStep view
      (HostTimeoutNumberSteps.sourcePoint [1,1,1,0,0,1,0,0,0,0,0,0,1,1,0] env fuel)
      {state with refs := HostTimeoutNumberSteps.numberHeap count entries completed} =
      some ({state with refs := (HostTimeoutNumberSteps.numberHeap count
        (entries ++ [.list [.nat seen, .bool (HostTimeoutNumberSteps.interruptionFlag exit)]]) completed)}, .unit) ∧
    (entries ++ [Val.list [.nat seen, .bool (HostTimeoutNumberSteps.interruptionFlag exit)]]).length +
      current operation 1 (.success .unit) =
      entries.length + current operation 1 (.sync (.op operation)) := by
  dsimp only
  refine ⟨HostTimeoutNumberSteps.cleanup_note view state fuel count seen delay n error exit entries completed, ?_⟩
  rw [answered, leaf]
  simp only [List.length_append, List.length_cons, List.length_nil, Nat.zero_add, Nat.add_zero]

/-- The actual count row exchanges its leaf for one unit of the committed count. -/
theorem timeout_count_debit (state : Stores) (count delay : Nat) (n : Fin 4) (error : Val)
    (entries completed : List Val) :
    let operation := SyncOp.refUpdate ⟨0⟩ HostTimeoutNumberEntry.countTerm
      (HostTimeoutSlots.ready (.cell ⟨0⟩) (.cell ⟨1⟩) (.cell ⟨2⟩) n delay error)
    syncOpStep operation {state with refs := HostTimeoutNumberSteps.numberHeap count entries completed} =
      some ({state with refs := HostTimeoutNumberSteps.numberHeap (count + 1) entries completed}, .unit) ∧
    count + 1 + current operation 1 (.success .unit) =
      count + current operation 1 (.sync (.op operation)) := by
  dsimp only
  refine ⟨HostTimeoutNumberEntry.count_sync state count delay n error entries completed, ?_⟩
  rw [answered, leaf, Nat.add_zero]

/-- Atomic's real note term is the same append leaf, with a paired literal identity. -/
theorem atomic_append_shape (id level : Nat) :
    Test.Dogfood.Scenario.Atomic.Store.noteAt id level =
      appendOne level
        (.app "pair" (.cons (.lit (.nat id)) (.cons
          (.app "add" (.cons (.field .required (.var (level - 1)) "admitted")
            (.cons (.field .required (.var (level - 1)) "rejected") .nil))) .nil))) := rfl

/-- The existing Atomic native write supplies the literal-identity data debit. -/
theorem atomic_debit (id : Nat) (cell : RefKey) (env : List Val) (state next : Stores) (answer : Val)
    (written : syncOpStep (.refUpdate cell (Test.Dogfood.Scenario.Atomic.Store.noteAt id env.length) env)
      state = some (next, answer)) :
    let operation := SyncOp.refUpdate cell (Test.Dogfood.Scenario.Atomic.Store.noteAt id env.length) env
    Test.Dogfood.Scenario.Atomic.Writer.heapCount id next.refs + current operation 1 (.success answer) =
      Test.Dogfood.Scenario.Atomic.Writer.heapCount id state.refs + current operation 1 (.sync (.op operation)) := by
  dsimp only
  rw [answered, leaf]
  letI : ReflBEq Nat := Nat.instLawfulBEq.toReflBEq
  have counted := Test.Dogfood.Scenario.Atomic.Writer.note_heap_count id id cell env state next answer written
  rw [if_pos (BEq.refl id)] at counted
  exact (Nat.add_zero _).trans counted

/-- The actual first worker release uses the same append expression with its acquired slot. -/
theorem workers_source (total : Nat) :
    Node.at_ (.eff (Test.Dogfood.Scenario.Programs.workersProgram total))
      (Test.Dogfood.Scenario.Programs.crewAcquire 1 ++ [1]) =
      some (.eff (.perform (.refUpdateWith (appendOne 7 (.var 5))) (.var 1))) := by kernel_rfl

/-- A captured release cell and acquired literal produce one local code-to-data exchange. -/
theorem workers_debit (state : Stores) (opened assigned count gate exit : Val)
    (cell : RefKey) (entries : List Val)
    (read : refPeek state.refs cell = some (.list entries)) :
    let env := [opened, Val.cell cell, assigned, count, gate, .nat 1, exit]
    let operation := SyncOp.refUpdate cell (appendOne 7 (.var 5)) env
    let next := {state with refs := refPoke state.refs cell (.list (entries ++ [.nat 1]))}
    syncOpStep operation state = some (next, .unit) ∧
    data (fun _ => 1) next.refs cell + current operation 1 (.success .unit) =
      data (fun _ => 1) state.refs cell + current operation 1 (.sync (.op operation)) := by
  dsimp only
  apply append_debit (fun _ => 1) cell (appendOne 7 (.var 5))
    [opened, .cell cell, assigned, count, gate, .nat 1, exit] state entries (.nat 1) read
  kernel_rfl
end PlaceWrites


-- Control: the local append balance allows a wrong saved attempt number.
-- This is a finite observation control, not an admitted-history counterexample.
#guard !(Test.Dogfood.Scenario.Timeout.Observation.cleanupKeeps
  {calls := [], receipts := [], applications := [], retired := [], stored := [],
    attempts := 1, cleanups := [.list [.nat 7, .bool false]], root := .running, timers := []})
