import Effect4.Laws.Program.Guard.Contract

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.AnswerDecision
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue

theorem prepareExternalAnswer_sites (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (stores : Stores) :
    raceSites (prepareExternalAnswer table current answer stores).2 = [] := by
  unfold prepareExternalAnswer
  dsimp only
  repeat' first | exact raceSites_completion answer | rfl | split

theorem prepareAsyncAnswer_shape (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (target : FiberId) (offered : Nat) (answer : Completion Val Err Defect FiberId Ann) :
    let result := prepareAsyncAnswer (interpOf p table) m target offered answer
    result.1.timers = m.state.timers ∧ result.1.deferreds = m.state.deferreds ∧
      raceSites result.2 = [] := by
  unfold prepareAsyncAnswer
  split
  · exact ⟨rfl, rfl, raceSites_completion answer⟩
  · exact ⟨(prepareExternalAnswer_internal_state table _ answer m.state).1,
      (prepareExternalAnswer_internal_state table _ answer m.state).2,
      prepareExternalAnswer_sites table _ answer m.state⟩

theorem guardState_prepareAsyncAnswer (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (target : FiberId) (offered : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (state : GuardState m) :
    GuardState { m with state := (prepareAsyncAnswer (interpOf p table) m target offered answer).1 } := by
  obtain ⟨timers, deferreds, _⟩ := prepareAsyncAnswer_shape p table m target offered answer
  apply guardState_withState state
  · simp only [storeKeys, timers, deferreds]
    exact List.Subset.refl _
  · rw [deferreds]
    exact ⟨state.internalCodes.1, state.internalCodes.2.1⟩

theorem guardQueue_drainDue (p : NativeEff) (table : RowTable) (m : NativeMachine) :
    GuardQueue p table m [.drainDue] := by
  constructor
  · intro c hc; rcases List.mem_singleton.mp hc with rfl; trivial
  · exact List.nodup_nil
  · exact ⟨by simp [commandKeys], by simp [commandKeys]⟩
  · intro c hc; rcases List.mem_singleton.mp hc with rfl; rfl

theorem guardQueue_resume_from_tail (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (token : Nat) (answer : NCode)
    (rest : List NCmd) (state : GuardState m)
    (tail : GuardQueue p table m rest) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.resume target token answer) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using tail
  | some f =>
    cases hp : f.parked with
    | notParked => simpa only [driveStep, hf, hp] using tail
    | withGuard parkedToken =>
      simp only [driveStep, hf, hp]
      split
      · rename_i he
        subst parkedToken
        have hmem : f ∈ m.fibers := List.mem_of_find?_eq_some hf
        have hexit : f.exit.isSome = false := by
          cases hx : f.exit.isSome with
          | false => rfl
          | true =>
            have hn := (state.exited f hmem hx).1
            rw [hp] at hn; cases hn
        let g : NFiber := { f with
          parked := .notParked
          pending := f.pending.filter (fun p => p.token ≠ token)
          frame := { f.frame with current := answer } }
        let n := (m.update g).emit [RunEvent.resumedWith target token answer]
        have controls : ControlsPreserved m n := controlsPreserved_update_parked (f := f)
          (by simpa only [fiber_id_of_lookup hf] using hf) g rfl
          (by rw [hp]; intro h; cases h) hexit
        have races : RaceHostsPreserved m n := fun _ race hr => ⟨race, hr, rfl⟩
        exact guardQueue_cons_evaluate p table target (guardQueue_transport p table tail
          controls races (Nat.le_refl _) (requestOf_update_unparked_subset m g rfl))
      · exact tail


theorem registrationQueue_resume_result (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (offered : Nat) (code : NCode)
    (rest : List NCmd) (registration : RegistrationQueue rest) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.resume target offered code) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first | exact registration | exact ⟨True.intro, registration⟩ | split

theorem guardState_answerDrive (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (target : FiberId) (offered : Nat) (code : NCode)
    (state : GuardState m) (sites : raceSites code = []) :
    letI := evaluatorFor p table
    GuardState (driveState (interpOf p table) fuel m [.resume target offered code, .drainDue]).1 := by
  letI := evaluatorFor p table
  cases fuel with
  | zero => exact state
  | succ fuel =>
    simp only [driveState]
    split
    · exact state
    · exact (driver.invariant fuel _ _
        (guardState_driveStep_resume p table m target offered code [.drainDue] state sites)
        (guardQueue_resume_from_tail p table m target offered code [.drainDue] state
          (guardQueue_drainDue p table m))
        (registrationQueue_resume_result p table m target offered code [.drainDue]
          ⟨True.intro, True.intro⟩)).1

theorem requestOrInterrupted_answerDrive (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (target fiber : FiberId) (offered token : Nat) (code : NCode) (request : NativeOp × Val)
    (state : GuardState m) (sites : raceSites code = [])
    (hr : requestOf m fiber token = some request) (different : target ≠ fiber ∨ offered ≠ token) :
    letI := evaluatorFor p table
    requestOf (driveState (interpOf p table) fuel m [.resume target offered code, .drainDue]).1
      fiber token = some request ∨
      InterruptedAt (driveState (interpOf p table) fuel m [.resume target offered code, .drainDue]).1 fiber := by
  letI := evaluatorFor p table
  cases fuel with
  | zero => exact Or.inl hr
  | succ fuel =>
    simp only [driveState]
    split
    · exact Or.inl hr
    · exact driver.request fuel _ _ fiber token request
        (guardState_driveStep_resume p table m target offered code [.drainDue] state sites)
        (guardQueue_resume_from_tail p table m target offered code [.drainDue] state
          (guardQueue_drainDue p table m))
        (registrationQueue_resume_result p table m target offered code [.drainDue]
          ⟨True.intro, True.intro⟩)
        (driveStep_resume_wrong_key p table m fiber target token offered request code [.drainDue] hr different)

theorem guardState_answerAsync (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (target : FiberId) (offered : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (state : GuardState m) :
    GuardState (steppedBy p fuel table m (.answerAsync target offered answer)) := by
  letI := evaluatorFor p table
  cases fuel with
  | zero => exact state
  | succ fuel =>
    exact guardState_answerDrive p table driver (fuel + 1) _ target offered _
      (guardState_prepareAsyncAnswer p table m target offered answer state)
      (prepareAsyncAnswer_shape p table m target offered answer).2.2

theorem requestOrInterrupted_answerAsync (p : NativeEff) (table : RowTable)
    (driver : DriverContract p table) (fuel : Nat) (m : NativeMachine)
    (target fiber : FiberId) (offered token : Nat) (answer : Completion Val Err Defect FiberId Ann)
    (request : NativeOp × Val) (state : GuardState m)
    (hr : requestOf m fiber token = some request) (different : target ≠ fiber ∨ offered ≠ token) :
    requestOf (steppedBy p fuel table m (.answerAsync target offered answer)) fiber token = some request ∨
      InterruptedAt (steppedBy p fuel table m (.answerAsync target offered answer)) fiber := by
  letI := evaluatorFor p table
  cases fuel with
  | zero => exact Or.inl hr
  | succ fuel =>
    exact requestOrInterrupted_answerDrive p table driver (fuel + 1) _ target fiber offered token _ request
      (guardState_prepareAsyncAnswer p table m target offered answer state)
      (prepareAsyncAnswer_shape p table m target offered answer).2.2 hr different

end Effect4.Program.Guard.AnswerDecision
