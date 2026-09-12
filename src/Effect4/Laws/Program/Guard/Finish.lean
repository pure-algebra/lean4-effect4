import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.Interruption

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.Finish
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard

/-- Both sides are unparked, so replacing the executing fiber preserves all requests. -/
theorem requestOf_update_unparked_eq {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (hid : g.id = f.id)
    (oldPark : f.parked = .notParked) (newPark : g.parked = .notParked)
    (fiber : FiberId) (token : Nat) :
    requestOf (m.update g) fiber token = requestOf m fiber token := by
  by_cases he : g.id = fiber
  · have hold : m.fiber? fiber = some f := by simpa only [← he, hid] using hf
    have hnew := fiber_lookup_update_self hold g he
    simp only [requestOf, hnew, hold]
    dsimp only [bind, Option.bind]
    simp [guard, newPark, oldPark]
    rfl
  · exact requestOf_update_other m g fiber token he

theorem fiberGuardState_publish {m : NativeMachine} {f : NFiber}
    (valid : FiberGuardState m f) (exit : ExitV) : FiberGuardState m (f.publish exit) := by
  refine ⟨valid.below, rfl, ?_, ?_, ?_, ?_, valid.codes, valid.tasks⟩
  · intro h; exact False.elim (h rfl)
  · intro token h; cases h
  · intro _; exact ⟨rfl, rfl⟩
  · intro h; cases h

theorem guardState_publish {m : NativeMachine} {f : NFiber}
    (state : GuardState m) (hf : m.fiber? f.id = some f) (exit : ExitV) :
    GuardState (m.update (f.publish exit)) := by
  have member := List.mem_of_find?_eq_some hf
  exact guardState_update_unparked state hf (f.publish exit) rfl
    (fiberGuardState_publish (guardState_fiber state member) exit)
    (reservedKeys_fiber (f := f) state member) rfl

abbrev childExitFiber (p : NativeEff) (table : RowTable) (f : NFiber) (exit : ExitV) : NFiber :=
  { f with
    finalizing := some exit
    running := false
    frame := { f.frame with
      deferredInterrupt := false
      current := Prim.onSuccess ((interpOf p table).interruptAllCode f.children)
        ((interpOf p table).restoreName exit) } }

theorem fiberGuardState_childExit (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (valid : FiberGuardState m f)
    (park : f.parked = .notParked) (exit : ExitV) :
    FiberGuardState m (childExitFiber p table f exit) := by
  refine ⟨valid.below, valid.pending, ?_, valid.parkedBelow, ?_, ?_, ?_, valid.tasks⟩
  · intro _; rfl
  · intro _; exact ⟨park, rfl⟩
  · intro h; cases h
  · refine ⟨raceCodeOwned_of_no_sites m f.id _ ?_, valid.codes.2⟩
    rfl

theorem guardState_childExit (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (park : f.parked = .notParked) (exit : ExitV) :
    GuardState (m.update (childExitFiber p table f exit)) := by
  have member := List.mem_of_find?_eq_some hf
  exact guardState_update_unparked state hf (childExitFiber p table f exit) rfl
    (fiberGuardState_childExit p table (guardState_fiber state member) park exit)
    (reservedKeys_fiber (f := f) state member) park

theorem guardState_cleared (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (exited : f.exit.isSome = true) :
    GuardState (m.update (f.cleared (interpOf p table))) := by
  have h := guardState_driveStep_exitDone p table m f.id [] state ⟨f, hf, exited⟩
  simpa only [driveStep, hf] using h

theorem guardState_exitFiber (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (park : f.parked = .notParked) (exit : ExitV) :
    GuardState (exitFiber (interpOf p table) m { f with running := false } exit).1 := by
  unfold exitFiber
  split
  · exact guardState_emit (guardState_childExit p table state hf park exit) _
  · have base := guardState_emit (guardState_publish state hf exit)
      [RunEvent.exited f.id exit]
    cases ho : f.observers with
    | nil =>
      have lookup : ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]).fiber?
          (f.publish exit).id = some (f.publish exit) := fiber_lookup_update_self hf _ rfl
      have clear := guardState_cleared p table base lookup rfl
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using clear
    | cons o os =>
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using base

theorem requestOf_exitFiber (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f)
    (park : f.parked = .notParked) (exit : ExitV) (fiber : FiberId) (token : Nat) :
    requestOf (exitFiber (interpOf p table) m { f with running := false } exit).1 fiber token =
      requestOf m fiber token := by
  unfold exitFiber
  split
  · exact requestOf_update_unparked_eq hf (childExitFiber p table f exit) rfl park park fiber token
  · have base := requestOf_update_unparked_eq hf (f.publish exit) rfl park rfl fiber token
    cases ho : f.observers with
    | nil =>
      have lookup : ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]).fiber?
          (f.publish exit).id = some (f.publish exit) := fiber_lookup_update_self hf _ rfl
      have clear := requestOf_update_view lookup ((f.publish exit).cleared (interpOf p table))
        ⟨rfl, rfl, rfl⟩ fiber token
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using clear.trans base
    | cons o os =>
      simpa only [exitFiber.exitStore, RunFiber.publish, ho, requestOf, RunMachine.emit, RunMachine.fiber?] using base

theorem nextToken_exitFiber (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (exit : ExitV) :
    (exitFiber (interpOf p table) m f exit).1.nextToken = m.nextToken := by
  unfold exitFiber
  split
  · rfl
  · cases ho : f.observers <;> simp only [exitFiber.exitStore, RunFiber.publish, ho] <;> rfl

theorem reservedKeys_exitFiber (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} {keys : List GuardKey}
    (hf : m.fiber? f.id = some f) (park : f.parked = .notParked) (exit : ExitV)
    (reserved : ReservedKeys m keys) :
    ReservedKeys (exitFiber (interpOf p table) m { f with running := false } exit).1 keys := by
  apply reservedKeys_of_same_requests reserved
  · rw [nextToken_exitFiber]; exact Nat.le_refl _
  · exact requestOf_exitFiber p table hf park exit

theorem interruptedAt_update {m : NativeMachine} {f : NFiber}
    (hf : m.fiber? f.id = some f) (g : NFiber) (hid : g.id = f.id)
    (keeps : Interrupted f → Interrupted g) {fiber : FiberId}
    (before : InterruptedAt m fiber) : InterruptedAt (m.update g) fiber := by
  obtain ⟨old, hold, interrupted⟩ := before
  by_cases he : g.id = fiber
  · have same : old = f := by
      have hf' : m.fiber? fiber = some f := by simpa only [← he, hid] using hf
      exact Option.some.inj (hold.symm.trans hf')
    exact ⟨g, fiber_lookup_update_self hold g he, keeps (same ▸ interrupted)⟩
  · refine ⟨old, ?_, interrupted⟩
    simp only [fiber_lookup_update, hold, Option.map_some, fiber_id_of_lookup hold,
      Ne.symm he, ↓reduceIte]

theorem interruptedAt_exitFiber (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (state : GuardState m)
    (hf : m.fiber? f.id = some f) (exit : ExitV) {fiber : FiberId}
    (before : InterruptedAt m fiber) :
    InterruptedAt (exitFiber (interpOf p table) m { f with running := false } exit).1 fiber := by
  unfold exitFiber
  split
  · apply interruptedAt_update hf (childExitFiber p table f exit) rfl _ before
    intro h
    exact Effect4.Program.Guard.Interruption.interrupted_of_recorded_or_exit _
      ((Effect4.Program.Guard.Interruption.interrupted_iff_recorded_or_exit f
        (state.deferredCause f (List.mem_of_find?_eq_some hf))).mp h)
  · have base : InterruptedAt ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]) fiber :=
      interruptedAt_update hf (f.publish exit) rfl (fun _ => Or.inr rfl) before
    cases ho : f.observers with
    | nil =>
      have lookup : ((m.update (f.publish exit)).emit [RunEvent.exited f.id exit]).fiber?
          (f.publish exit).id = some (f.publish exit) := fiber_lookup_update_self hf _ rfl
      have clear := interruptedAt_cleared p table lookup fiber base
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using clear
    | cons o os =>
      simpa only [exitFiber.exitStore, RunFiber.publish, ho] using base

theorem guardState_driveStep_finish (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (exit : ExitV) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.finish target exit)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.finish target exit) rest).1 := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  simpa only [driveStep, hf] using guardState_exitFiber p table state
    (by simpa only [fiber_id_of_lookup hf] using hf) park exit

theorem requestOf_driveStep_finish (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (exit : ExitV) (rest : List NCmd)
    (authority : CommandAuthority p table m (.finish target exit))
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.finish target exit) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  simpa only [driveStep, hf] using requestOf_exitFiber p table
    (by simpa only [fiber_id_of_lookup hf] using hf) park exit fiber token

theorem reservedKeys_driveStep_finish (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (exit : ExitV) (rest : List NCmd)
    (authority : CommandAuthority p table m (.finish target exit))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.finish target exit) rest).1 keys := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  simpa only [driveStep, hf] using reservedKeys_exitFiber p table
    (by simpa only [fiber_id_of_lookup hf] using hf) park exit reserved

theorem interruptedAt_driveStep_finish (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (exit : ExitV) (rest : List NCmd)
    (state : GuardState m) (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.finish target exit) rest).1 fiber := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using before
  | some f =>
    simpa only [driveStep, hf] using interruptedAt_exitFiber p table state
      (by simpa only [fiber_id_of_lookup hf] using hf) exit before


end Effect4.Program.Guard.Finish
