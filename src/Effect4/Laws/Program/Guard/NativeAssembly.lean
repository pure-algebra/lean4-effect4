import Effect4.Laws.Program.Guard.NativeState
import Effect4.Laws.Program.Guard.NativeStateMotion
import Effect4.Laws.Program.Guard.NativeStateExternal
import Effect4.Laws.Program.Guard.NativeStateLinks
import Effect4.Laws.Program.Guard.ReturnTasks
import Effect4.Laws.Program.Guard.Settle
import Effect4.Laws.Program.Guard.SettleQueue
import Effect4.Laws.Program.Guard.RegistrationNested
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace Effect4.Program.Guard.NativeAssembly
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.Settle Effect4.Program.Guard.SettleQueue Effect4.Program.Guard.ReturnFields

/-- A stored owner has the external-key disjointness already recorded by GuardState.
Consumer: outcome disposition after the actual addressed message word. -/
theorem stored_guardSafe_at {active : Option FiberId} {m : NativeMachine} {f : NFiber}
    (state : GuardState m active) (lookup : m.fiber? f.id = some f) :
    ∀ token request, f.parked = .withGuard token → externalRequest f.frame.current = some request →
      (f.id, token) ∉ internalKeys m ∧ (f.id, token) ∉ fiberKeys f := by
  intro token request park code
  have offered : requestOf m f.id token = some request := by
    unfold requestOf
    rw [lookup]
    simp only [Option.bind_some, park, guard, pure, bind, ↓reduceIte]
    exact code
  refine ⟨state.requestsOwned f.id token request offered, ?_⟩
  intro member
  exact state.requestsOwned f.id token request offered
    (internalKeys_fiber (List.mem_of_find?_eq_some lookup) member)

/-- Actual settlement installs its local owner, interprets the admitted message word,
then disposes the owner read from that word's final machine.
Consumer: the original native and iteration GuardState endpoints. -/
theorem guardState_settle_messages (id : FiberId) (rest : List NCmd) (it : NIter)
    (state : GuardState it.machine) (old : NFiber)
    (lookup : it.machine.fiber? it.fiber.id = some old)
    (valid : FiberGuardState it.machine it.fiber (some it.fiber.id))
    (running : it.fiber.running = true) (ready : ReadyOutcome it)
    (reserved : ReservedKeys it.machine (fiberKeys it.fiber))
    (safe : ∀ token request, it.fiber.parked = .withGuard token →
      externalRequest it.fiber.frame.current = some request →
      (it.fiber.id, token) ∉ internalKeys it.machine ∧ (it.fiber.id, token) ∉ fiberKeys it.fiber)
    (before : NativeMachine) (admitted : Messages.MessageKeys before it) :
    GuardState (settle id rest it).1 := by
  cases edits : it.edits with
  | nil =>
    exact guardState_settle id rest it state old lookup
      (settledFiber_valid_of_active it valid ready) reserved safe edits
  | cons edit tail =>
    have oldId := fiber_id_of_lookup lookup
    have oldLookup : it.machine.fiber? old.id = some old := by simpa only [oldId] using lookup
    have installed : GuardState (it.machine.update it.fiber) (some it.fiber.id) :=
      guardState_update_at (guardState_relax state _) oldLookup it.fiber oldId.symm valid reserved safe
    have ownLookup : (it.machine.update it.fiber).fiber? it.fiber.id = some it.fiber :=
      fiber_lookup_update_self lookup it.fiber rfl
    have messageKeys := Messages.reserved_editKeys_install admitted lookup
    have finalState := (Messages.guardState_fiberEdits_at it.edits installed messageKeys).1
    obtain ⟨owner, ownerLookup, word⟩ :=
      (Moves.InterferesWithLookup.fiberEdits it.edits (it.machine.update it.fiber)).lookup
        it.fiber.id it.fiber ownLookup
    have ownerId := fiber_id_of_lookup ownerLookup
    have ownedLookup : (applyFiberEdits it.edits (it.machine.update it.fiber)).1.fiber? owner.id = some owner := by
      simpa only [ownerId] using ownerLookup
    have ownedState : GuardState (applyFiberEdits it.edits (it.machine.update it.fiber)).1 (some owner.id) :=
      ownerId.symm ▸ finalState
    have fields := word.controls (Or.inl running)
    let next : NIter := {it with
      machine := (applyFiberEdits it.edits (it.machine.update it.fiber)).1
      fiber := owner
      nested := (applyFiberEdits it.edits (it.machine.update it.fiber)).2 ++ it.nested
      edits := []}
    have readyNext : ReadyOutcome next := by
      cases outcome : it.outcome <;> simp only [ReadyOutcome, next, outcome] at ready ⊢
      all_goals exact fields.2.1.trans ready
    have after := guardState_settleOutcome id rest next ownedState owner ownedLookup
      (settledFiber_valid_of_active next
        (guardState_fiber_at ownedState (List.mem_of_find?_eq_some ownedLookup)) readyNext)
      (reservedKeys_fiber_at ownedState (List.mem_of_find?_eq_some ownedLookup))
      (stored_guardSafe_at ownedState ownedLookup)
    simpa only [settle, next, edits, edits ▸ ownerLookup] using after

theorem guardState_settle_native (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked) :
    GuardState (settle id rest (evaluateNative p m f yielding table)).1 := by
  have member := List.mem_of_find?_eq_some lookup
  have machine := Effect4.Program.Guard.NativeState.evaluateNative_step p table state f yielding ⟨f, lookup⟩
  have links := Effect4.Program.Guard.NativeStateLinks.evaluateNative_links p table m f yielding
  have fresh := evaluateNative_freshPark p table m f yielding park
  obtain ⟨saved, found, _, _, _⟩ := links.controls.active f.id f lookup running park
  have lookup' : (evaluateNative p m f yielding table).machine.fiber?
      (evaluateNative p m f yielding table).fiber.id = some saved := by
    rw [Effect4.Program.Guard.Interruption.evaluateNative_id]
    exact found
  apply guardState_settle_messages id rest _ machine.state.state saved lookup'
    (before := m)
  · exact native_returnedFiber_valid_at p table m f yielding state lookup running park
      (Effect4.Program.Guard.NativeStateMotion.evaluateNative_nextId p table m f yielding)
      (Effect4.Program.Guard.ReturnTasks.evaluateNative_taskRaceSites p table m f yielding
        (state.internalCodes.1 f member))
  · exact (Effect4.Program.Guard.ReturnFields.evaluateNative_running p table m f yielding).trans running
  · exact evaluateNative_ready p table m f yielding park
  · exact returnedFiber_reserved m f _ state member machine.state.tokens fresh machine.state.requests
      (Effect4.Program.Guard.ReturnTasks.evaluateNative_fiberKeys_refined p table m f yielding)
  · apply returnedFiber_guardSafe m f _ state member fresh
      (Effect4.Program.Guard.NativeStateExternal.evaluateNative_external p table m f yielding park)
    intro token request _ external
    rw [Effect4.Program.Guard.ReturnTasks.evaluateNative_external_fiberKeys p table m f yielding request external]
    intro key hk; exact hk
  · exact machine.messages True.intro

theorem guardState_settle_iteration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked) :
    letI := evaluatorFor p table
    GuardState (settle id rest (iteration (interpOf p table) m f yielding)).1 := by
  letI := evaluatorFor p table
  have member := List.mem_of_find?_eq_some lookup
  have machine := Effect4.Program.Guard.NativeState.iteration_step p table state f yielding ⟨f, lookup⟩
  have links := Effect4.Program.Guard.NativeStateLinks.iteration_links p table m f yielding
  have fresh := iteration_freshPark p table m f yielding park
  obtain ⟨saved, found, _, _, _⟩ := links.controls.active f.id f lookup running park
  have lookup' : (iteration (interpOf p table) m f yielding).machine.fiber?
      (iteration (interpOf p table) m f yielding).fiber.id = some saved := by
    rw [Effect4.Program.Guard.Interruption.iteration_id]
    exact found
  apply guardState_settle_messages id rest _ machine.state.state saved lookup'
    (before := m)
  · exact iteration_returnedFiber_valid_at p table m f yielding state lookup running park
      (Effect4.Program.Guard.NativeStateMotion.iteration_nextId p table m f yielding)
      (Effect4.Program.Guard.ReturnTasks.iteration_taskRaceSites p table m f yielding
        (state.internalCodes.1 f member))
  · exact (Effect4.Program.Guard.ReturnFields.iteration_running p table m f yielding).trans running
  · exact iteration_ready p table m f yielding park
  · exact returnedFiber_reserved m f _ state member machine.state.tokens fresh machine.state.requests
      (Effect4.Program.Guard.ReturnTasks.iteration_fiberKeys_refined p table m f yielding)
  · apply returnedFiber_guardSafe m f _ state member fresh
      (Effect4.Program.Guard.NativeStateExternal.iteration_external p table m f yielding park)
    intro token request _ external
    rw [Effect4.Program.Guard.ReturnTasks.iteration_external_fiberKeys p table m f yielding request external]
    intro key hk; exact hk
  · exact machine.messages True.intro

theorem reservedKeys_settle_native (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    ReservedKeys (settle id rest (evaluateNative p m f yielding table)).1 keys := by
  have machine := Effect4.Program.Guard.NativeState.evaluateNative_state p table state f yielding ⟨f, lookup⟩
  exact reservedKeys_settle m id rest _ keys reserved machine.tokens
    (evaluateNative_freshPark p table m f yielding park) machine.requests

theorem reservedKeys_settle_iteration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (settle id rest (iteration (interpOf p table) m f yielding)).1 keys := by
  letI := evaluatorFor p table
  have machine := Effect4.Program.Guard.NativeState.iteration_state p table state f yielding ⟨f, lookup⟩
  exact reservedKeys_settle m id rest _ keys reserved machine.tokens
    (iteration_freshPark p table m f yielding park) machine.requests

theorem request_other_unparked {m : NativeMachine} {f : NFiber} {fiber : FiberId} {token : Nat}
    {request : NativeOp × Val} (lookup : m.fiber? f.id = some f)
    (park : f.parked = .notParked) (hr : requestOf m fiber token = some request) : f.id ≠ fiber := by
  intro same
  obtain ⟨g, hg, guard, _⟩ := requestOf_shape hr
  have eq : f = g := Option.some.inj (lookup.symm.trans (same ▸ hg))
  have : Parked.notParked = .withGuard token := park.symm.trans (eq ▸ guard)
  cases this

/-- Settlement retains another owner's request or its interruption marker.
Consumer: the original native request-fate endpoints. -/
theorem requestOrInterrupted_settle_other (id : FiberId) (rest : List NCmd) (it : NIter)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (other : it.fiber.id ≠ fiber) (offered : requestOf it.machine fiber token = some request) :
    requestOf (settle id rest it).1 fiber token = some request ∨
      InterruptedAt (settle id rest it).1 fiber := by
  cases edits : it.edits with
  | nil => exact Or.inl ((requestOf_settle_other id rest it fiber token other edits).trans offered)
  | cons edit tail =>
    have installed : requestOf (it.machine.update it.fiber) fiber token = some request :=
      (requestOf_update_other _ _ _ _ other).trans offered
    have links := NativeStateLinks.Links.fiberEdits it.edits (it.machine.update it.fiber)
    have fate := links.requests fiber token request installed
    simp only [settle, edits]
    cases lookup : (applyFiberEdits (edit :: tail) (it.machine.update it.fiber)).1.fiber? it.fiber.id with
    | none => exact edits ▸ fate
    | some owner =>
      have ownerId := fiber_id_of_lookup lookup
      have away : owner.id ≠ fiber := fun same => other (ownerId.symm.trans same)
      rcases fate with retained | interrupted
      · left
        exact (requestOf_settleOutcome_other id rest _ fiber token away).trans (edits ▸ retained)
      · right
        apply interruptedAt_settleOutcome id rest _ fiber (edits ▸ interrupted)
        intro same
        exact False.elim (away same)

theorem requestOrInterrupted_settle_native (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request) :
    requestOf (settle id rest (evaluateNative p m f yielding table)).1 fiber token = some request ∨
      InterruptedAt (settle id rest (evaluateNative p m f yielding table)).1 fiber := by
  have other : (evaluateNative p m f yielding table).fiber.id ≠ fiber := by
    simpa only [Effect4.Program.Guard.Interruption.evaluateNative_id] using request_other_unparked lookup park before
  have links := Effect4.Program.Guard.NativeStateLinks.evaluateNative_links p table m f yielding
  rcases links.requests fiber token request before with retained | interrupted
  · exact requestOrInterrupted_settle_other id rest _ fiber token request other retained
  · exact Or.inr (interruptedAt_settle id rest _ fiber interrupted (fun same => False.elim (other same)))

theorem requestOrInterrupted_settle_iteration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (fiber : FiberId) (token : Nat) (request : NativeOp × Val)
    (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (settle id rest (iteration (interpOf p table) m f yielding)).1 fiber token = some request ∨
      InterruptedAt (settle id rest (iteration (interpOf p table) m f yielding)).1 fiber := by
  letI := evaluatorFor p table
  have other : (iteration (interpOf p table) m f yielding).fiber.id ≠ fiber := by
    simpa only [Effect4.Program.Guard.Interruption.iteration_id] using request_other_unparked lookup park before
  have links := Effect4.Program.Guard.NativeStateLinks.iteration_links p table m f yielding
  rcases links.requests fiber token request before with retained | interrupted
  · exact requestOrInterrupted_settle_other id rest _ fiber token request other retained
  · exact Or.inr (interruptedAt_settle id rest _ fiber interrupted (fun same => False.elim (other same)))

theorem interruptedAt_at_lookup {m : NativeMachine} {f : NFiber} {fiber : FiberId}
    (lookup : m.fiber? f.id = some f) (same : f.id = fiber) (before : InterruptedAt m fiber) :
    Interrupted f := by
  obtain ⟨g, hg, interrupted⟩ := before
  have eq : f = g := Option.some.inj (lookup.symm.trans (same ▸ hg))
  exact eq ▸ interrupted

theorem interruptedAt_settle_native (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    InterruptedAt (settle id rest (evaluateNative p m f yielding table)).1 fiber := by
  have links := Effect4.Program.Guard.NativeStateLinks.evaluateNative_links p table m f yielding
  apply interruptedAt_settle id rest _ fiber (links.interrupted fiber before)
  intro same
  have eq : f.id = fiber := (Effect4.Program.Guard.Interruption.evaluateNative_id p table m f yielding).symm.trans same
  exact Effect4.Program.Guard.Interruption.evaluateNative_interrupted p table m f yielding
    (state.deferredCause f (List.mem_of_find?_eq_some lookup)) (interruptedAt_at_lookup lookup eq before)

theorem interruptedAt_settle_iteration (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : FiberId) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (settle id rest (iteration (interpOf p table) m f yielding)).1 fiber := by
  letI := evaluatorFor p table
  have links := Effect4.Program.Guard.NativeStateLinks.iteration_links p table m f yielding
  apply interruptedAt_settle id rest _ fiber (links.interrupted fiber before)
  intro same
  have eq : f.id = fiber := (Effect4.Program.Guard.Interruption.iteration_id p table m f yielding).symm.trans same
  exact Effect4.Program.Guard.Interruption.iteration_interrupted p table m f yielding
    (state.deferredCause f (List.mem_of_find?_eq_some lookup)) (interruptedAt_at_lookup lookup eq before)

theorem guardState_driveStep_loop (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.loop target yielding)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.loop target yielding) rest).1 := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, running, park⟩ := authority
  have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
  simpa only [driveStep, hf] using guardState_settle_iteration p table m f yielding target rest
    state lookup running park

theorem reservedKeys_driveStep_loop (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.loop target yielding))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.loop target yielding) rest).1 keys := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
  simpa only [driveStep, hf] using reservedKeys_settle_iteration p table m f yielding target rest
    state lookup park keys reserved

theorem requestOrInterrupted_driveStep_loop (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (authority : CommandAuthority p table m (.loop target yielding)) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val) (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.loop target yielding) rest).1 fiber token = some request ∨ InterruptedAt (driveStep (interpOf p table) m (.loop target yielding) rest).1 fiber := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
  simpa only [driveStep, hf] using requestOrInterrupted_settle_iteration p table m f yielding target rest
    lookup park fiber token request before

theorem interruptedAt_driveStep_loop (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.loop target yielding) rest).1 fiber := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using before
  | some f =>
    have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    simpa only [driveStep, hf] using interruptedAt_settle_iteration p table m f yielding target rest
      state lookup fiber before

theorem registrationQueue_driveStep_loop (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (registration : Effect4.Program.Guard.RegistrationQueue.RegistrationQueue rest) :
    letI := evaluatorFor p table
    Effect4.Program.Guard.RegistrationQueue.RegistrationQueue
      (driveStep (interpOf p table) m (.loop target yielding) rest).2 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using registration
  | some f =>
    simpa only [driveStep, hf] using Effect4.Program.Guard.RegistrationNested.registrationQueue_settle target rest _
      (Effect4.Program.Guard.RegistrationNested.iteration_registration p table m f yielding) registration

theorem guardState_driveStep_deliver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.deliver target yielding)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.deliver target yielding) rest).1 := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, running, park⟩ := authority
  have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
  simpa only [driveStep, hf] using guardState_settle_native p table m f yielding target rest
    state lookup running park

theorem reservedKeys_driveStep_deliver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.deliver target yielding))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.deliver target yielding) rest).1 keys := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
  simpa only [driveStep, hf] using reservedKeys_settle_native p table m f yielding target rest
    state lookup park keys reserved

theorem requestOrInterrupted_driveStep_deliver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (authority : CommandAuthority p table m (.deliver target yielding)) (fiber : FiberId) (token : Nat)
    (request : NativeOp × Val) (before : requestOf m fiber token = some request) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.deliver target yielding) rest).1 fiber token = some request ∨ InterruptedAt (driveStep (interpOf p table) m (.deliver target yielding) rest).1 fiber := by
  letI := evaluatorFor p table
  obtain ⟨f, hf, _, park⟩ := authority
  have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
  simpa only [driveStep, hf] using requestOrInterrupted_settle_native p table m f yielding target rest
    lookup park fiber token request before

theorem interruptedAt_driveStep_deliver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.deliver target yielding) rest).1 fiber := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using before
  | some f =>
    have lookup : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup hf] using hf
    simpa only [driveStep, hf] using interruptedAt_settle_native p table m f yielding target rest
      state lookup fiber before

theorem registrationQueue_driveStep_deliver (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (target : FiberId) (yielding : Bool) (rest : List NCmd)
    (registration : Effect4.Program.Guard.RegistrationQueue.RegistrationQueue rest) :
    letI := evaluatorFor p table
    Effect4.Program.Guard.RegistrationQueue.RegistrationQueue
      (driveStep (interpOf p table) m (.deliver target yielding) rest).2 := by
  letI := evaluatorFor p table
  cases hf : m.fiber? target with
  | none => simpa only [driveStep, hf] using registration
  | some f =>
    simpa only [driveStep, hf] using Effect4.Program.Guard.RegistrationNested.registrationQueue_settle target rest _
      (Effect4.Program.Guard.RegistrationNested.evaluateNative_registration p table m f yielding) registration

end Effect4.Program.Guard.NativeAssembly
