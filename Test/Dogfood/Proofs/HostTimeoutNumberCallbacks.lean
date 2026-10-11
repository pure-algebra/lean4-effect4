import Test.Dogfood.Proofs.HostTimeoutNumberEntry

/-!
Placement: scope-lifetime-finalization R11 and translation-simulation R10.
Question: saved count-read callbacks of Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the numeric saved-answer contract and its reference command transfer.
The actual callbacks retain their captured source metadata and the count returned by the heap.
These equations supply no reached-state or budget producer.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
namespace Test.Dogfood.Proofs.HostTimeoutNumberCallbacks
open Effect4 Effect4.Machine Effect4.Program
open HostTimeoutSource HostTimeoutSlots HostTimeoutFlow HostTimeoutNumberSteps HostTimeoutNumberState

/-- The cleanup binder captures the exiting attempt and its exact allocated handles. -/
def cleanupPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0,0,0,0,0,0,1]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++ [reifyExitVal exit]
    fuel := fuel + 3}

/-- The completed-form binder captures the selected exit after the race cleanup. -/
def completedPoint (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV) : Point :=
  {captured with
    path := [1,1,1,0,0,1,0,0,1]
    env := ready (Val.cell ⟨0⟩) (Val.cell ⟨1⟩) (Val.cell ⟨2⟩) n delay error ++ [reifyExitVal exit]
    fuel := fuel + 2}

/-- The cleanup source pushes its count-read callback before either log write. -/
theorem cleanup_code (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV) :
    let point := cleanupPoint captured fuel delay n error exit
    resolve HostTimeoutSource.program point =
      .onSuccess (.sync (.op (.refGet ⟨0⟩))) (.cont point) := by
  dsimp only
  kernel_rfl

/-- The form source pushes its count-read callback after receiving the selected exit. -/
theorem completed_code (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV) :
    let point := completedPoint captured fuel delay n error exit
    resolve HostTimeoutSource.program point =
      .onSuccess (.sync (.op (.refGet ⟨0⟩))) (.cont point) := by
  dsimp only
  kernel_rfl

/-- The real cleanup callback appends the actual returned count to the captured environment. -/
theorem cleanup_callback (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) (exit : ExitV) (count : Nat) :
    let point := cleanupPoint captured fuel delay n error exit
    (interpreter view).contA (.cont point) (.nat count) =
      .onSuccess
        (resolve HostTimeoutSource.program
          (({point with completed := view}.childWith 1 (.nat count)).child 0))
        (.cont ({point with completed := view}.childWith 1 (.nat count))) := by
  dsimp only
  kernel_rfl

/-- The real form callback resolves its writer with the returned count and the exact saved exit. -/
theorem completed_callback (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) (exit : ExitV) (count : Nat) :
    let point := completedPoint captured fuel delay n error exit
    (interpreter view).contA (.cont point) (.nat count) =
      resolve HostTimeoutSource.program ({point with completed := view}.childWith 1 (.nat count)) := rfl

/-- Cleanup's actual read belongs to the active attempt's committed-count phase. -/
theorem cleanup_read_at (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (cleanups completed : List Val) (exits : List ExitV)
    (numbers : Numbers (n.val + 1) cleanups completed exits)
    (own : n.val + 1 = cleanups.length + 1) :
    ReferenceAtPoint ((cleanupPoint captured fuel delay n error exit).child 0)
      (numberHeap (n.val + 1) cleanups completed) := by
  exact ReferenceAt.cleanupRead (fuel + 1) delay n error exit cleanups completed exits numbers own

/-- Cleanup's callback uses the exact count from its read, rather than an arbitrary number. -/
theorem cleanup_note_at (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) (exit : ExitV) (cleanups completed : List Val) (exits : List ExitV)
    (numbers : Numbers (n.val + 1) cleanups completed exits)
    (own : n.val + 1 = cleanups.length + 1) :
    ReferenceAtPoint
      (({cleanupPoint captured fuel delay n error exit with completed := view}.childWith 1
        (.nat (n.val + 1))).child 0)
      (numberHeap (n.val + 1) cleanups completed) := by
  exact ReferenceAt.cleanupNote fuel delay n error exit cleanups completed exits numbers own

/-- The form read follows the completed attempt's cleanup. -/
theorem completed_read_at (captured : Point) (fuel delay : Nat) (n : Fin 4) (error : Val) (exit : ExitV)
    (cleanups completed : List Val) (exits : List ExitV)
    (numbers : Numbers (n.val + 1) cleanups completed exits)
    (cleanupComplete : cleanups.length = n.val + 1) (own : exits.length = n.val) :
    ReferenceAtPoint ((completedPoint captured fuel delay n error exit).child 0)
      (numberHeap (n.val + 1) cleanups completed) := by
  exact ReferenceAt.completedRead fuel delay n error exit cleanups completed exits numbers cleanupComplete own

/-- The form callback keeps the count returned by its actual reference read. -/
theorem completed_note_at (view : View) (captured : Point) (fuel delay : Nat) (n : Fin 4)
    (error : Val) (exit : ExitV) (cleanups completed : List Val) (exits : List ExitV)
    (numbers : Numbers (n.val + 1) cleanups completed exits)
    (cleanupComplete : cleanups.length = n.val + 1) (own : exits.length = n.val) :
    ReferenceAtPoint
      ({completedPoint captured fuel delay n error exit with completed := view}.childWith 1
        (.nat (n.val + 1)))
      (numberHeap (n.val + 1) cleanups completed) := by
  exact ReferenceAt.completedNote fuel delay n error exit cleanups completed exits numbers cleanupComplete own

/-- Real reference source steps ignore only the metadata their operations do not read. -/
theorem reference_fields (view : View) (state : Stores) (point : Point)
    (owned : ReferenceAtPoint point state.refs) :
    sourceStep view point state = sourceStep view (referencePoint point) state := by
  obtain ⟨op, request, fuel, node, reference, positive⟩ := reference_source owned
  have code := reference_code_fields point op request fuel positive node reference
  unfold sourceStep
  rw [code]

/-- The actual cleanup read and callback feed the exact writer and finish the active cleanup gap. -/
theorem cleanup_transfer (view : View) (state : Stores) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (cleanups completed : List Val) (exits : List ExitV)
    (heap : state.refs = numberHeap (n.val + 1) cleanups completed)
    (numbers : Numbers (n.val + 1) cleanups completed exits)
    (own : n.val + 1 = cleanups.length + 1) :
    let point := cleanupPoint captured fuel delay n error exit
    let bound := {point with completed := view}.childWith 1 (.nat (n.val + 1))
    let written := cleanups ++ [.list [.nat (n.val + 1), .bool (interruptionFlag exit)]]
    sourceStep view (point.child 0) state = some (state, .nat (n.val + 1)) ∧
      (interpreter view).contA (.cont point) (.nat (n.val + 1)) =
        .onSuccess (resolve HostTimeoutSource.program (bound.child 0)) (.cont bound) ∧
      sourceStep view (bound.child 0) state =
        some ({state with refs := numberHeap (n.val + 1) written completed}, .unit) ∧
      Numbers (n.val + 1) written completed exits := by
  dsimp only
  constructor
  · have owned := cleanup_read_at captured fuel delay n error exit cleanups completed exits numbers own
    rw [← heap] at owned
    rw [reference_fields view state _ owned]
    have answer := cleanup_read view state (fuel + 1) (n.val + 1) delay n error exit cleanups completed
    have same : {state with refs := numberHeap (n.val + 1) cleanups completed} = state := by rw [← heap]
    rw [same] at answer
    exact answer
  constructor
  · exact cleanup_callback view captured fuel delay n error exit (n.val + 1)
  constructor
  · have owned := cleanup_note_at view captured fuel delay n error exit cleanups completed exits numbers own
    rw [← heap] at owned
    rw [reference_fields view state _ owned]
    have answer := cleanup_note view state fuel (n.val + 1) (n.val + 1) delay n error exit cleanups completed
    have same : {state with refs := numberHeap (n.val + 1) cleanups completed} = state := by rw [← heap]
    rw [same] at answer
    exact answer
  · exact cleanup_numbers numbers own (interruptionFlag exit)

/-- The actual form read and callback publish the selected exit after cleanup without changing the count. -/
theorem completed_transfer (view : View) (state : Stores) (captured : Point) (fuel delay : Nat)
    (n : Fin 4) (error : Val) (exit : ExitV) (cleanups completed : List Val) (exits : List ExitV)
    (heap : state.refs = numberHeap (n.val + 1) cleanups completed)
    (numbers : Numbers (n.val + 1) cleanups completed exits)
    (cleanupComplete : cleanups.length = n.val + 1) (own : exits.length = n.val) :
    let point := completedPoint captured fuel delay n error exit
    let bound := {point with completed := view}.childWith 1 (.nat (n.val + 1))
    let written := completed ++ [.list [.nat (n.val + 1), reifyExitVal exit]]
    sourceStep view (point.child 0) state = some (state, .nat (n.val + 1)) ∧
      (interpreter view).contA (.cont point) (.nat (n.val + 1)) = resolve HostTimeoutSource.program bound ∧
      sourceStep view bound state = some ({state with refs := numberHeap (n.val + 1) cleanups written}, .unit) ∧
      Numbers (n.val + 1) cleanups written (exits ++ [exit]) := by
  dsimp only
  constructor
  · have owned := completed_read_at captured fuel delay n error exit cleanups completed exits numbers cleanupComplete own
    rw [← heap] at owned
    rw [reference_fields view state _ owned]
    have answer := completed_read view state fuel (n.val + 1) delay n error exit cleanups completed
    have same : {state with refs := numberHeap (n.val + 1) cleanups completed} = state := by rw [← heap]
    rw [same] at answer
    exact answer
  constructor
  · rfl
  constructor
  · have owned := completed_note_at view captured fuel delay n error exit cleanups completed exits numbers cleanupComplete own
    rw [← heap] at owned
    rw [reference_fields view state _ owned]
    have answer := completed_note view state fuel (n.val + 1) (n.val + 1) delay n error exit cleanups completed
    have same : {state with refs := numberHeap (n.val + 1) cleanups completed} = state := by rw [← heap]
    rw [same] at answer
    exact answer
  · exact completed_numbers numbers cleanupComplete (by omega) (n.val + 1) exit

/-- Read the synchronous operation from the existing resolved source code.
Consumer: reference_sync checks this projection at every numeric reference leaf. -/
def operationOf (point : Point) : SyncOp :=
  match resolve HostTimeoutSource.program point with
  | .sync (.op operation) => operation
  | _ => .refGet ⟨0⟩

/-- Every numeric reference input resolves an actual native synchronous operation. -/
theorem reference_sync (point : Point) (heap : RefHeap) (owned : ReferenceAtPoint point heap) :
    ∃ op, resolve HostTimeoutSource.program point = .sync (.op op) := by
  obtain ⟨op, request, fuel, node, reference, positive⟩ := reference_source owned
  rw [reference_code_fields point op request fuel positive node reference]
  have canonical : ∀ (p : Point) (refs : RefHeap), ReferenceAt p refs →
      ∃ operation, resolve HostTimeoutSource.program p = .sync (.op operation) := by
    intro p refs held
    refine ⟨operationOf p, ?_⟩
    cases held
    all_goals kernel_rfl
  exact canonical (referencePoint point) heap owned

/-- The actual native evaluator consumes the eight-leaf numeric source contract.
It retains the saved stack and every store field except the source's reference mutation. -/
theorem native_reference (machine : Effect4.Program.NativeMachine) (fiber : HostTimeoutEvaluation.NativeFiber)
    (yielding : Bool) (point : Point)
    (current : fiber.frame.current = resolve HostTimeoutSource.program point)
    (owned : ReferenceAtPoint point machine.state.refs) :
    ∃ next value,
      evaluateNative HostTimeoutSource.program machine fiber yielding Scenario.Timeout.fetch.table =
        ⟨{machine with state := next}, {fiber with frame := {fiber.frame with current := .success value}},
          yielding, .answered, [.drainDue]⟩ ∧
      HeapAt next.refs ∧ ReferenceAnswer point next.refs value := by
  obtain ⟨op, code⟩ := reference_sync point machine.state.refs owned
  obtain ⟨next, value, step, heap, answer⟩ :=
    reference_step_point machine.completedExits machine.state point owned
  unfold sourceStep at step
  rw [code] at step
  have sync : syncOpStep op machine.state = some (next, value) := step
  exact ⟨next, value, ControlSteps.native_sync_op HostTimeoutSource.program Scenario.Timeout.fetch.table
    machine fiber yielding op next value (current.trans code) sync, heap, answer⟩

end Test.Dogfood.Proofs.HostTimeoutNumberCallbacks
