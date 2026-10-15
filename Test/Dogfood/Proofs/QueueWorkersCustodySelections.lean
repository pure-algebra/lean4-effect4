import Test.Dogfood.Proofs.QueueWorkersCustodyRetry

/-!
Concept: translation-simulation R10.
Consumer: QueueWorkers.jobs_step, at the take attempt and retry result boundaries.
The actual option branch returns the value computed from its own captured payload.
The notification prefix classes preserve the captured option until this branch executes.
-/
set_option autoImplicit false
namespace Test.Dogfood.Proofs.QueueWorkersCustody
open Effect4 Effect4.Machine Effect4.Program

/-- An actual source option selection binds its own payload and returns its computed result. -/
theorem select_return (root : NativeEff) (point : Point) (fuel : Nat)
    (scrutinee resultTerm : Term) (fallback : NativeEff) (payload value : Val)
    (available : point.fuel = fuel + 2)
    (found : Node.at_ (.eff root) point.path =
      some (.eff (.select scrutinee .option fallback (.succeed resultTerm))))
    (selected : evalTerm point.env scrutinee = some (.some payload))
    (answer : evalTerm (point.env ++ [payload]) resultTerm = some value) :
    suspendBodyAt root (.body point) = .success value := by
  have decision : (evalTerm point.env scrutinee).bind Decision.option.decide = some (false, some payload) := by
    rw [selected]
    rfl
  have arm : Node.at_ (.eff root) (point.childWith 1 payload).path = some (.eff (.succeed resultTerm)) :=
    (Agreement.at_childWith found 1 payload).trans rfl
  have childFuel : (point.childWith 1 payload).fuel = fuel + 1 := by
    simp only [Point.childWith, available]
    omega
  rw [Agreement.suspendBodyAt_select_of_decide available found decision]
  change resolve root (point.childWith 1 payload) = _
  rw [Agreement.resolve_of_at arm, Agreement.compileEff_succeed resultTerm childFuel]
  change (match evalTerm (point.env ++ [payload]) resultTerm with
    | some result => Prim.success result | none => badShape) = _
  rw [answer]

/-- The retry result's final source binder returns the exact option payload. -/
theorem select_payload (root : NativeEff) (point : Point) (fuel : Nat)
    (scrutinee : Term) (fallback : NativeEff) (job : Nat)
    (available : point.fuel = fuel + 2)
    (found : Node.at_ (.eff root) point.path =
      some (.eff (.select scrutinee .option fallback (.succeed (.var point.env.length)))))
    (selected : evalTerm point.env scrutinee = some (.some (.nat job))) :
    suspendBodyAt root (.body point) = .success (.nat job) :=
  select_return root point fuel scrutinee (.var point.env.length) fallback (.nat job) (.nat job)
    available found selected List.getElem?_concat_length

end Test.Dogfood.Proofs.QueueWorkersCustody
