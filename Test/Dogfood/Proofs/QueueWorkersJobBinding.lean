import Test.Dogfood.Proofs.QueueWorkersCustodyFlow
import Test.Dogfood.Proofs.QueueWorkersCustodyAssignmentSource

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, through its actual worker success binder and assignment cut.
The actual continuation appends the classified job; the source census selects its immediate writer.
No separate job-membership premise supplies the assignment's occurrence.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersJobBinding
open Effect4 Effect4.Machine Effect4.Program
open QueueWorkersCustodyFlow

/-- The worker's immediate continuation retains the classified job in its actual last slot. -/
def Capture (root : NativeEff) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point) : Prop :=
  SourceScope.At root point ∧ ∃ job,
    ValueAt world (.job owner) (.nat job) ∧ point.env[point.env.length - 1]? = some (.nat job)

/-- The request binder captures the actual published key of its waiting owner. -/
def RequestCapture (root : NativeEff) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (index : Nat) (point : Point) : Prop :=
  SourceScope.At root point ∧ ∃ token value, Owns world owner token ∧
    QueueWorkersRequestKeys.KeyAt world.requests token value ∧
    world.requests.custody.requests token = .waiting ∧
    point.env[index]? = some value

/-- The real request-allocation callback appends its classified key, preserving its literal token. -/
theorem request_callback (root : NativeEff) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (before after : NativeEff) (value : Val) (view : List (FiberId × ExitV)) (table : RowTable)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind before after)))
    (source : SourceScope.At root point) (answer : ValueAt world (.workerKey owner) value) :
    (interpAt root view table).contA (.cont point) value =
      resolve root ({point with completed := view}.childWith 1 value) ∧
    RequestCapture root world owner point.env.length ({point with completed := view}.childWith 1 value) := by
  obtain ⟨token, selected, published, waiting⟩ := answer
  refine ⟨rfl, ?_, token, value, selected, published, waiting, ?_⟩
  · apply SourceScope.childWith_at root _ 1 value
    exact SourceScope.next_of_at root _ (.bind before after) 1 1 found source rfl
  · have last : (point.env ++ [value])[point.env.length]? = some value := List.getElem?_concat_length
    exact last

/-- Hint and retry binders append their own values without replacing the captured request key. -/
theorem request_bound (root : NativeEff) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (index : Nat)
    (point : Point) (child : Nat) (value : Val)
    (next : SourceScope.NextAt root point child 1)
    (held : RequestCapture root world owner index point) :
    RequestCapture root world owner index (point.childWith child value) := by
  obtain ⟨_source, token, key, selected, published, waiting, captured⟩ := held
  refine ⟨SourceScope.childWith_at root point child value next,
    token, key, selected, published, waiting, ?_⟩
  exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp captured).1).trans captured

/-- The actual worker binder appends the successful job consumed by its assignment child. -/
theorem callback (root : NativeEff) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (before after : NativeEff) (job : Nat) (view : List (FiberId × ExitV)) (table : RowTable)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind before after)))
    (source : SourceScope.At root point) (answer : ValueAt world (.job owner) (.nat job)) :
    (interpAt root view table).contA (.cont point) (.nat job) =
      resolve root ({point with completed := view}.childWith 1 (.nat job)) ∧
    Capture root world owner ({point with completed := view}.childWith 1 (.nat job)) := by
  refine ⟨rfl, ?_, job, answer, ?_⟩
  · apply SourceScope.childWith_at root _ 1 (.nat job)
    exact SourceScope.next_of_at root _ (.bind before after) 1 1 found source rfl
  · have last : (point.env ++ [Val.nat job])[point.env.length]? = some (.nat job) :=
      List.getElem?_concat_length
    simpa only [Point.childWith, List.length_append, List.length_singleton, Nat.add_sub_cancel] using last

/-- Entering the immediate assignment child retains that exact slot and current request. -/
theorem child (root : NativeEff) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (assignment rest : NativeEff)
    (found : Node.at_ (.eff root) point.path = some (.eff (.bind assignment rest)))
    (held : Capture root world owner point) : Capture root world owner (point.child 0) := by
  refine ⟨?_, held.2⟩
  apply SourceScope.child_at root point 0
  exact SourceScope.next_of_at root point (.bind assignment rest) 0 0 found held.1 rfl

/-- The actual source assignment consumes the job appended by its successful worker binder. -/
theorem assignment_native (total : Nat) (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point) (term : Term)
    (held : Capture (Test.Dogfood.Scenario.Programs.queueProgram total) world owner point)
    (found : Node.at_ (.eff (Test.Dogfood.Scenario.Programs.queueProgram total)) point.path =
      some (.eff (.perform (.refUpdateWith term) (.var 3))))
    (credits : QueueWorkersCustody.Credits world.requests.custody)
    (conserved : world.requests.custody.ledger.Conserved) (stores : Stores)
    (read : refPeek stores.refs ⟨3⟩ = some (.list
      (world.requests.custody.ledger.assigned.map (fun pair =>
        Test.Dogfood.Scenario.QueueWorkers.gave pair.1 pair.2)))) :
    ∃ worker ∈ [1, 2], ∃ job token, Owns world owner token ∧
      syncOpStep (.refUpdate ⟨3⟩ term point.env) stores =
        some ({stores with refs := refPoke stores.refs ⟨3⟩ (.list
          ((assigned world token job worker).requests.custody.ledger.assigned.map (fun pair =>
            Test.Dogfood.Scenario.QueueWorkers.gave pair.1 pair.2)))}, .unit) ∧
      Future world (assigned world token job worker) ∧
      (assigned world token job worker).requests.custody.ledger.Conserved ∧
      QueueWorkersCustody.Credits (assigned world token job worker).requests.custody ∧
      ValueAt (assigned world token job worker) (.captured owner token (.spent token)) .unit := by
  obtain ⟨job, answer, captured⟩ := held.2
  obtain ⟨worker, member, shape, length⟩ :=
    QueueWorkersCustodyAssignmentSource.assignment_at total point term held.1 found
  have slot : point.env.length - 1 = worker + 7 := by omega
  rw [slot] at captured
  obtain ⟨token, selected, actual, future, conserving, counted, spent⟩ :=
    QueueWorkersCustodyFlow.assignment_native world owner job worker credits conserved answer
      point.env (worker + 7) captured stores read
  exact ⟨worker, member, job, token, selected, (by rw [shape]; exact actual), future, conserving, counted, spent⟩
end Test.Dogfood.Proofs.QueueWorkersJobBinding
