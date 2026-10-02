import Effect4.Laws.Program.Guard.Handshake

/-! M4's literal guard-or-inert boundary. The quantified stale-token controls use
the production helper. The duplicate-ID countermodel explains its uniqueness
premise; it is not a reachable state or a refutation of the frozen M4 target.
No ownership, answer typing, progress, fairness or target-runtime claim is made. -/
set_option autoImplicit false
set_option maxRecDepth 8192

namespace Test.Program.ParkHandshake
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

def program : NativeEff := .succeed (.lit (.nat 0))
def firstFiber : NFiber :=
  { RunFiber.make Api.root (.success (.nat 0)) true (2048, false) emptyCtx with
    parked := .withGuard 7 }
def waiter : Waiter Unit := ⟨Api.root, 7, 0, ()⟩
def active : NativeMachine :=
  { Api.load program 10 [] with
    fibers := [firstFiber]
    state := { Stores.empty with timers := TimerStore.empty.sleep Api.root 7 100 } }
def unparked : NativeMachine :=
  { active with fibers := [{ firstFiber with parked := .notParked }] }
def wrongToken : NativeMachine :=
  { active with fibers := [{ firstFiber with parked := .withGuard 8 }] }
def duplicated : NativeMachine :=
  { active with fibers := [firstFiber, { firstFiber with parked := .notParked }] }

theorem active_waiter : waiter ∈ active.state.pendingWaiters := by decide +kernel
theorem active_guard : firstFiber.parked = .withGuard waiter.token := rfl

theorem active_handshake :
    letI := evaluatorFor program []
    Machine.ParkHandshake (interpOf program []) active := by
  letI := evaluatorFor program []
  exact parkHandshake_of_fiberIds_nodup _ _ (by decide +kernel)

theorem unparked_inert :
    letI := evaluatorFor program []
    Inert (interpOf program []) unparked Api.root 7 := by
  letI := evaluatorFor program []
  exact inert_of_lookup_not_guard _ _ _ _ { firstFiber with parked := .notParked }
    (by decide +kernel) (by decide +kernel)

theorem wrong_token_inert :
    letI := evaluatorFor program []
    Inert (interpOf program []) wrongToken Api.root 7 := by
  letI := evaluatorFor program []
  exact inert_of_lookup_not_guard _ _ _ _ { firstFiber with parked := .withGuard 8 }
    (by decide +kernel) (by decide +kernel)

theorem matching_zero_budget (answer : Prim EffName EffThunk Val Err Defect FiberId Ann) :
    letI := evaluatorFor program []
    drive (interpOf program []) 0 active [.resume Api.root 7 answer] = active := by
  letI := evaluatorFor program []
  exact drive_zero _ _ _

theorem matching_stuck_inert :
    letI := evaluatorFor program []
    Inert (interpOf program []) (active.halt (.unknownFiber Api.root)) Api.root 7 := by
  letI := evaluatorFor program []
  intro fuel answer
  rw [drive_stuck _ _ _ _ (by rfl)]

theorem duplicate_ids : ¬ (duplicated.fibers.map RunFiber.id).Nodup := by decide +kernel

theorem matching_resume_changes_observation :
    letI := evaluatorFor program []
    obs (drive (interpOf program []) 10 duplicated [.resume Api.root 7 (.success (.nat 9))]) ≠
      obs duplicated := by
  decide +kernel

theorem duplicates_not_inert :
    letI := evaluatorFor program []
    ¬ Inert (interpOf program []) duplicated Api.root 7 := by
  letI := evaluatorFor program []
  intro inert
  exact matching_resume_changes_observation (inert 10 (.success (.nat 9)))

theorem duplicates_refuse_handshake :
    letI := evaluatorFor program []
    ¬ Machine.ParkHandshake (interpOf program []) duplicated := by
  letI := evaluatorFor program []
  intro handshake
  have result := handshake waiter (by decide +kernel)
    { firstFiber with parked := .notParked } (by decide +kernel) rfl
  rcases result with guarded | inert
  · cases guarded
  · exact duplicates_not_inert inert

#print axioms active_handshake
#print axioms unparked_inert
#print axioms wrong_token_inert
#print axioms matching_zero_budget
#print axioms matching_stuck_inert
#print axioms matching_resume_changes_observation
#print axioms duplicates_refuse_handshake
#print axioms Effect4.Machine.fiber_lookup_of_mem_nodup
#print axioms Effect4.Machine.drive_resume_unchanged_of_lookup_not_guard
#print axioms Effect4.Machine.parkHandshake_of_fiberIds_nodup
#print axioms Effect4.Program.Guard.M4Handshake.parkHandshake_reachable.checked

end Test.Program.ParkHandshake
