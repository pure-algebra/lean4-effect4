import Test.Dogfood.Proofs.QueueWorkersOfferRequest

/-!
Concept: translation-simulation R10 and store-typing R4.
Consumer: QueueWorkers.jobs_step, after its actual observed offer-entry push.
The saved callback requires the same holding request to remain unpublished before entering request allocation.
The separate entry native cut creates that occurrence at the actual trace event.
-/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
namespace Test.Dogfood.Proofs.QueueWorkersOfferWrapper
open Effect4 Effect4.Machine Effect4.Program
open Test.Dogfood.Scenario Test.Dogfood.Scenario.QueueWorkers
open QueueWorkersCustodyFlow

def maskPath : List Nat := QueueWorkersOfferRequest.allocationPath.dropLast

def allocation (total : Nat) : NativeEff :=
  match Node.at_ (.eff (Programs.queueProgram total)) QueueWorkersOfferRequest.allocationPath with
  | some (.eff body) => body
  | _ => .succeed (.lit .unit)

theorem source (total : Nat) :
    Node.at_ (.eff (Programs.queueProgram total)) offerEntryPath = some (.eff
      (.bind (.withFiber .getInterruptible) (.uninterruptible (allocation total)))) := by kernel_rfl

theorem mask_source (total : Nat) :
    Node.at_ (.eff (Programs.queueProgram total)) maskPath =
      some (.eff (.uninterruptible (allocation total))) := by kernel_rfl

theorem paths : offerEntryPath ++ [1] = maskPath ∧
    maskPath ++ [0] = QueueWorkersOfferRequest.allocationPath := by
  exact ⟨by kernel_rfl, by kernel_rfl⟩

/-- The actual mask callback enters the real allocator with its same unpublished held occurrence. -/
theorem masked_body (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = maskPath)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (unpublished : world.requests.keys token = none)
    (payload : point.env[10]? = some (.nat job)) :
    QueueWorkersJobGraph.CodeAt total rows owner world .ordinary (resolve (Programs.queueProgram total) point) := by
  have found := mask_source total
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
    · apply QueueWorkersOfferRequest.body total rows world owner token job (point.child 0)
      · exact SourceScope.child_at _ _ 0 (SourceScope.next_of_at _ _ _ 0 0 found owned rfl)
      · change point.path ++ [0] = QueueWorkersOfferRequest.allocationPath
        rw [atPath, paths.2]
      · exact leading
      · exact selected
      · exact holding
      · exact unpublished
      · exact payload

/-- The real getter binder consumes the unpublished class produced by the actual entry event. -/
theorem body (total : Nat) (rows : RowTable) (world : QueueWorkersCustodyFlow.World)
    (owner : FiberId) (token job : Nat) (point : Point)
    (owned : SourceScope.At (Programs.queueProgram total) point)
    (atPath : point.path = offerEntryPath)
    (leading : AnswerSlots.Prefix InitialSlots.bindings point.env)
    (selected : Owns world owner token)
    (holding : world.requests.custody.requests token = .holding job)
    (unpublished : world.requests.keys token = none)
    (payload : point.env[10]? = some (.nat job)) :
    QueueWorkersJobGraph.CodeAt total rows owner world .ordinary (resolve (Programs.queueProgram total) point) := by
  have found := source total
  rw [← atPath] at found
  rw [Agreement.resolve_of_at found]
  cases fuel : point.fuel with
  | zero =>
    rw [Agreement.compileEff_at_zero _ fuel]
    exact .frontier fuel
  | succ amount =>
    rw [Agreement.compileEff_bind _ _ fuel]
    apply QueueWorkersJobGraph.CodeAt.bound (input := .unpublished owner token job) rfl
    · cases childFuel : (point.child 0).fuel with
      | zero =>
        rw [Agreement.compileEff_at_zero _ childFuel]
        exact .frontier childFuel
      | succ remaining =>
        rw [Agreement.compileEff_withFiber _ childFuel (by intros; intro impossible; cases impossible)]
        apply QueueWorkersJobGraph.CodeAt.heldGetter _ selected holding unpublished
        simp only [actionAt, Agreement.at_child (p := point) found 0]
        rfl
    · intro nextWorld future view answer good
      obtain ⟨nextSelected, nextHolding, absent, flag, rfl⟩ := good
      change QueueWorkersJobGraph.CodeAt total rows owner nextWorld .ordinary
        (resolve (Programs.queueProgram total) ({point with completed := view}.childWith 1 (Val.savedMask flag)))
      apply masked_body total rows nextWorld owner token job
      · exact SourceScope.childWith_at _ _ 1 (Val.savedMask flag) (SourceScope.next_of_at _ _ _ 1 1 found owned rfl)
      · change point.path ++ [1] = maskPath
        rw [atPath, paths.1]
      · exact leading.append _
      · exact nextSelected
      · exact nextHolding
      · exact absent
      · exact (List.getElem?_append_left (List.getElem?_eq_some_iff.mp payload).1).trans payload
end Test.Dogfood.Proofs.QueueWorkersOfferWrapper
