import Effect4.Laws.Program.Guard.Core
import Effect4.Laws.Program.Guard.RegistrationQueue

/-! Remaining control-case wrappers.
Proof graph: registration-tail transport through the nine command branches;
unchanged interruption fields through update/postTask/drainOwed; reserved resume
keys exclude outstanding external requests; the five observation wrappers then
feed the owning agent's driver induction. No outer driver proof is claimed. -/
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.ControlRemainder
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.RegistrationQueue

/-- Every drained command is a resume, so it adds no registration obligation. -/
theorem registrationQueue_drainOwed (m : NativeMachine) (due : List (Owed NCode)) :
    RegistrationQueue (drainOwed m due).2 := by
  induction due generalizing m with
  | nil => trivial
  | cons owed due ih =>
    cases mode : owed.mode with
    | now =>
      simpa only [drainOwed, mode, RegistrationQueue, RegistrationTail] using And.intro True.intro (ih m)
    | scheduled owner priority => simpa only [drainOwed, mode] using ih (m.postTask owner priority
        (.resume owed.waiter owed.token owed.code))

theorem registrationQueue_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (registration : RegistrationQueue (.evaluate target :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.evaluate target) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first | exact registration.2 | exact ⟨True.intro, registration.2⟩ | split

theorem registrationQueue_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (token : Nat) (answer : NCode) (rest : List NCmd)
    (registration : RegistrationQueue (.resume target token answer :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.resume target token answer) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first | exact registration.2 | exact ⟨True.intro, registration.2⟩ | split

theorem registrationQueue_driveStep_wake (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (list : WakeKey) (phase : WakePhase) (rest : List NCmd)
    (registration : RegistrationQueue (.wake list phase :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.wake list phase) rest).2 := by
  letI := evaluatorFor p table
  exact registration.2

theorem registrationQueue_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd)
    (registration : RegistrationQueue (.raceCancel raceId host yielding remaining visited :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest).2 := by
  letI := evaluatorFor p table
  cases remaining <;> simp only [driveStep]
  all_goals repeat' first
    | exact ⟨True.intro, registration.2⟩
    | exact ⟨True.intro, True.intro, registration.2⟩
    | split

theorem registrationQueue_driveStep_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rest : List NCmd) (registration : RegistrationQueue (.drainDue :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m .drainDue rest).2 := by
  letI := evaluatorFor p table
  exact registrationQueue_append (registrationQueue_drainOwed _ _) registration.2

theorem registrationQueue_driveStep_interruptTarget (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (rest : List NCmd) (registration : RegistrationQueue (.interruptTarget target who extra :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.interruptTarget target who extra) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first | exact registration.2 | exact ⟨True.intro, registration.2⟩ | split

theorem registrationQueue_driveStep_exitDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (registration : RegistrationQueue (.exitDone target :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.exitDone target) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  split <;> exact registration.2

theorem registrationQueue_driveStep_trackChild (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (parent child : FiberId) (rest : List NCmd)
    (registration : RegistrationQueue (.trackChild parent child :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.trackChild parent child) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first | exact registration.2 | split

theorem registrationQueue_driveStep_link (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (rest : List NCmd)
    (registration : RegistrationQueue (.link mode scope target who extra :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.link mode scope target who extra) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep, linkScope]
  repeat' first | exact registration.2 | exact ⟨True.intro, registration.2⟩ | split

/-- A field update that keeps the old interruption witness. -/
theorem interruptedAt_update_mark {m : NativeMachine} {f : NFiber}
    (lookup : m.fiber? f.id = some f) (g : NFiber) (id : g.id = f.id)
    (mark : Interrupted f → Interrupted g) (fiber : FiberId) (h : InterruptedAt m fiber) :
    InterruptedAt (m.update g) fiber := by
  obtain ⟨old, hold, interrupted⟩ := h
  by_cases he : old.id = f.id
  · have hlookup : m.fiber? f.id = some old := by
      simpa only [← he, fiber_id_of_lookup hold] using hold
    have same : old = f := Option.some.inj (hlookup.symm.trans lookup)
    subst old
    exact ⟨g, fiber_lookup_update_self hold g (id.trans (fiber_id_of_lookup hold)), mark interrupted⟩
  · refine ⟨old, ?_, interrupted⟩
    simp only [fiber_lookup_update, hold, Option.map_some, id, he, ↓reduceIte]

theorem interruptedAt_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.evaluate target) rest).1 fiber := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? target with
  | none => simpa only [driveStep, lookup] using h
  | some f =>
    simp only [driveStep, lookup]
    split
    · exact h
    · refine interruptedAt_update_mark (f := f) (by simpa only [fiber_id_of_lookup lookup] using lookup)
        { f with running := true, currentOpCount := 0 } rfl ?_ fiber h
      exact fun h => h

theorem interruptedAt_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (token : Nat) (answer : NCode) (rest : List NCmd)
    (fiber : FiberId) (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.resume target token answer) rest).1 fiber := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? target with
  | none => simpa only [driveStep, lookup] using h
  | some f =>
    cases park : f.parked with
    | notParked => simpa only [driveStep, lookup, park] using h
    | withGuard guarded =>
      simp only [driveStep, lookup, park]
      split
      · refine interruptedAt_update_mark (f := f) (by simpa only [fiber_id_of_lookup lookup] using lookup)
          { f with
            parked := .notParked
            pending := f.pending.filter (fun pending => pending.token ≠ token)
            frame := { f.frame with current := answer } } rfl ?_ fiber h
        exact fun h => h
      · exact h

theorem interruptedAt_driveStep_wake (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (list : WakeKey) (phase : WakePhase) (rest : List NCmd)
    (fiber : FiberId) (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.wake list phase) rest).1 fiber := by
  letI := evaluatorFor p table
  exact h

theorem interruptedAt_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd) (fiber : FiberId)
    (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest).1 fiber := by
  letI := evaluatorFor p table
  cases remaining <;> simp only [driveStep]
  all_goals repeat' first | exact h | split

theorem interruptedAt_postTask (m : NativeMachine) (owner : FiberId) (priority : Nat)
    (task : NTask) (fiber : FiberId) (h : InterruptedAt m fiber) :
    InterruptedAt (m.postTask owner priority task) fiber := by
  unfold RunMachine.postTask
  cases lookup : m.fiber? owner with
  | none => exact h
  | some f =>
    refine interruptedAt_update_mark (f := f)
      (by simpa only [fiber_id_of_lookup lookup] using lookup)
      { f with dispatcher := f.dispatcher.enqueue priority task } rfl ?_ fiber h
    exact fun h => h

theorem interruptedAt_drainOwed (m : NativeMachine) (due : List (Owed NCode))
    (fiber : FiberId) (h : InterruptedAt m fiber) : InterruptedAt (drainOwed m due).1 fiber := by
  induction due generalizing m with
  | nil => exact h
  | cons owed due ih =>
    cases mode : owed.mode with
    | now => simpa only [drainOwed, mode] using ih m h
    | scheduled owner priority =>
      simpa only [drainOwed, mode] using
        ih _ (interruptedAt_postTask m owner priority (.resume owed.waiter owed.token owed.code) fiber h)

theorem interruptedAt_driveStep_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rest : List NCmd) (fiber : FiberId) (h : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m .drainDue rest).1 fiber := by
  letI := evaluatorFor p table
  exact interruptedAt_drainOwed _ _ fiber h

/-- Resume never creates an external request; its replacement is unparked. -/
theorem requestOf_driveStep_resume_subset (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (offered : Nat) (answer : NCode) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber token = some request →
      requestOf m fiber token = some request := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? target with
  | none => simp only [driveStep, lookup]; exact fun h => h
  | some f =>
    cases park : f.parked with
    | notParked => simp only [driveStep, lookup, park]; exact fun h => h
    | withGuard guarded =>
      simp only [driveStep, lookup, park]
      split
      · exact requestOf_update_unparked_subset m _ rfl fiber token request
      · exact fun h => h

/-- A reserved resume key cannot be the key of any outstanding external request. -/
theorem requestOf_driveStep_resume_reserved (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (offered : Nat) (answer : NCode) (rest : List NCmd)
    (reserved : ReservedKeys m [(target, offered)]) (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  cases before : requestOf m fiber token with
  | none =>
    cases after : requestOf (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber token with
    | none => rfl
    | some request =>
      have old := requestOf_driveStep_resume_subset p table m target offered answer rest fiber token request after
      rw [before] at old
      cases old
  | some request =>
    apply driveStep_resume_wrong_key p table m fiber target token offered request answer rest before
    by_cases other : target = fiber
    · right
      intro same
      exact reserved.disjoint fiber token request before
        (List.mem_singleton.mpr (by simp only [other, same]))
    · exact Or.inl other

/-- Ordinary command queues supply the reserved-head premise internally. -/
theorem requestOf_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (offered : Nat) (answer : NCode) (rest : List NCmd)
    (queue : GuardQueue p table m (.resume target offered answer :: rest))
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  apply requestOf_driveStep_resume_reserved p table m target offered answer rest
  exact reservedKeys_subset queue.keys (by
    intro key member
    exact List.mem_append_left _ member)

theorem requestOf_driveStep_wake (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (list : WakeKey) (phase : WakePhase) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.wake list phase) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  rfl

theorem requestOf_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd) (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest).1 fiber token = requestOf m fiber token := by
  letI := evaluatorFor p table
  cases remaining <;> simp only [driveStep]
  all_goals repeat' first | rfl | split

/-- Exact request equality already in GuardCore supplies the evaluate case. -/
theorem requestOrInterrupted_driveStep_evaluate (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (h : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.evaluate target) rest).1 fiber token = some request ∨
      InterruptedAt (driveStep (interpOf p table) m (.evaluate target) rest).1 fiber := by
  letI := evaluatorFor p table
  exact Or.inl ((requestOf_driveStep_evaluate p table m target fiber token rest).trans h)

theorem requestOrInterrupted_driveStep_resume (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (offered : Nat) (answer : NCode) (rest : List NCmd)
    (queue : GuardQueue p table m (.resume target offered answer :: rest))
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (h : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber token = some request ∨
      InterruptedAt (driveStep (interpOf p table) m (.resume target offered answer) rest).1 fiber := by
  letI := evaluatorFor p table
  exact Or.inl ((requestOf_driveStep_resume p table m target offered answer rest queue fiber token).trans h)

theorem requestOrInterrupted_driveStep_wake (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (list : WakeKey) (phase : WakePhase) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (h : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.wake list phase) rest).1 fiber token = some request ∨
      InterruptedAt (driveStep (interpOf p table) m (.wake list phase) rest).1 fiber := by
  letI := evaluatorFor p table
  exact Or.inl ((requestOf_driveStep_wake p table m list phase rest fiber token).trans h)

theorem requestOrInterrupted_driveStep_raceCancel (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (raceId : Nat) (host : FiberId) (yielding : Bool)
    (remaining visited : List FiberId) (rest : List NCmd)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (h : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m
      (.raceCancel raceId host yielding remaining visited) rest).1 fiber token = some request ∨
      InterruptedAt (driveStep (interpOf p table) m
        (.raceCancel raceId host yielding remaining visited) rest).1 fiber := by
  letI := evaluatorFor p table
  exact Or.inl ((requestOf_driveStep_raceCancel p table m raceId host yielding remaining visited rest fiber token).trans h)

/-- Exact request equality already in GuardCore supplies the drainDue case. -/
theorem requestOrInterrupted_driveStep_drainDue (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rest : List NCmd) (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (h : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m .drainDue rest).1 fiber token = some request ∨
      InterruptedAt (driveStep (interpOf p table) m .drainDue rest).1 fiber := by
  letI := evaluatorFor p table
  exact Or.inl ((requestOf_driveStep_drainDue p table m rest fiber token).trans h)

end Effect4.Program.Guard.ControlRemainder
