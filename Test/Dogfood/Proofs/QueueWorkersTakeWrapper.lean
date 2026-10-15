import Test.Dogfood.Proofs.QueueWorkersRequestFlow
import Effect4.Laws.Program.NativeActionFlow

/-!
Concept: store-typing R4 and translation-simulation R10.
Consumer: QueueWorkers.jobs_step, through the complete authored Queue.take expression.
The mask getter's callback consumes an actual saved flag before allocating its request.
The existing request producer owns the retry, waiting cleanup and returned job.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
namespace Test.Dogfood.Proofs.QueueWorkersTakeWrapper
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

def maskPath (worker : Nat) := (QueueWorkersRequestFlow.allocationPath worker).dropLast
def path (worker : Nat) := (maskPath worker).dropLast
def allocation (worker : Nat) : NativeEff :=
  .bind (.perform (.deferredMakeOf .unit .never) (.lit .unit)) (QueueWorkersRequestFlow.allocationBody worker)

/-- The take wrapper reads the entry flag before entering its authored uninterruptible body. -/
theorem source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (path worker) = some (.eff
      (.bind (.withFiber .getInterruptible) (.uninterruptible (allocation worker)))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- The mask body is the original source parent of request allocation. -/
theorem mask_source (total worker : Nat) (member : worker ∈ [1, 2]) :
    Node.at_ (.eff (Programs.queueProgram total)) (maskPath worker) =
      some (.eff (.uninterruptible (allocation worker))) := by
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  rcases List.mem_cons.mp member with rfl | member
  · kernel_rfl
  exact (List.not_mem_nil member).elim

/-- Source children preserve the actual wrapper, mask and allocation positions. -/
theorem paths (worker : Nat) (member : worker ∈ [1, 2]) :
    path worker ++ [1] = maskPath worker ∧
      maskPath worker ++ [0] = QueueWorkersRequestFlow.allocationPath worker := by
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by kernel_rfl, by kernel_rfl⟩
  rcases List.mem_cons.mp member with rfl | member
  · exact ⟨by kernel_rfl, by kernel_rfl⟩
  exact (List.not_mem_nil member).elim

/-- The actual masked body starts the complete request producer at its real source child. -/
theorem masked_body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = maskPath worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    QueueWorkersJobGraph.CodeAt total table owner world (.job owner)
      (resolve (Programs.queueProgram total) point) := by
  have found := mask_source total worker member
  rw [← atPath] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_uninterruptible _ fuel]
    apply QueueWorkersJobGraph.CodeAt.masking (body := resolve (Programs.queueProgram total) (point.child 0)) (flag := false)
    · simp only [actionAt, found]
    · apply QueueWorkersRequestFlow.allocate_body total worker member table world owner (point.child 0)
      · exact SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found owned rfl)
      · change point.path ++ [0] = QueueWorkersRequestFlow.allocationPath worker
        rw [atPath, (paths worker member).2]
      · exact leading

/-- The complete authored take binds only its real mask flag and returns its own classified job. -/
theorem body (total worker : Nat) (member : worker ∈ [1, 2]) (table : RowTable)
    (world : QueueWorkersCustodyFlow.World) (owner : FiberId) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = path worker)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env) :
    QueueWorkersJobGraph.CodeAt total table owner world (.job owner)
      (resolve (Programs.queueProgram total) point) := by
  have found := source total worker member
  rw [← atPath] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .maskFlag) True.intro
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_withFiber _ childFuel (by intros; intro impossible; cases impossible)]
        apply QueueWorkersJobGraph.CodeAt.maskGetter
        simp only [actionAt, Agreement.at_child (p := point) found 0]
        rfl
    · intro nextWorld future view answer good
      change QueueWorkersJobGraph.CodeAt total table owner nextWorld (.job owner)
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 answer))
      apply masked_body total worker member table nextWorld owner _
      · exact SourceScope.childWith_at _ _ 1 answer (SourceScope.next_of_at _ _ _ 1 1 found owned rfl)
      · change point.path ++ [1] = maskPath worker
        rw [atPath, (paths worker member).1]
      · exact leading.append [answer]
/-- The actual getter returns its saved flag and pushes only the existing mask-restoration edge. -/
theorem getter_path (total : Nat) (table : RowTable) (owner : FiberId)
    (world : QueueWorkersCustodyFlow.World) (view : List (FiberId × ExitV)) (output : Kind)
    (machine : NativeMachine) (fiber : SourceScope.SourceFiber) (yielding : Bool)
    (stack : Contracts.Path (QueueWorkersJobFamilies.Edge total table owner world) .maskFlag output fiber.frame.stack) :
    let next := evaluatePrim.withFiber (interpAt (Programs.queueProgram total) view table)
      machine fiber yielding .getInterruptible
    QueueWorkersJobGraph.CodeAt total table owner world .maskFlag next.fiber.frame.current ∧
      Contracts.Path (QueueWorkersJobFamilies.Edge total table owner world) .maskFlag output next.fiber.frame.stack := by
  change QueueWorkersJobGraph.CodeAt total table owner world .maskFlag (.success (Val.savedMask fiber.frame.interruptible)) ∧
    Contracts.Path (QueueWorkersJobFamilies.Edge total table owner world) .maskFlag output fiber.frame.uninterruptible.stack
  exact SourceScope.masked_path (QueueWorkersJobGraph.model total table owner view)
    (QueueWorkersJobFamilies.Edge total table owner) world .maskFlag output fiber.frame _
    (.success ⟨fiber.frame.interruptible, rfl⟩) ⟨none, QueueWorkersJobGraph.mask_saved total table owner world .maskFlag true⟩ stack
end Test.Dogfood.Proofs.QueueWorkersTakeWrapper
