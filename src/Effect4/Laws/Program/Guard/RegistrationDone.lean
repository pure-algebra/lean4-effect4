import Effect4.Laws.Program.Guard.Continuation

set_option autoImplicit false
set_option maxRecDepth 2048
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue
open Effect4.Program.Guard.Settle Effect4.Program.Guard.ReturnFields

theorem externalRequest_parkOf (p : NativeEff) (table : RowTable) (code : NCode)
    (kind : ParkKind) (park : (interpOf p table).parkOf code = some (.ok kind)) :
    externalRequest code = none := by
  cases code <;> try rfl
  case async register signal cancel => simp [interpOf] at park

theorem requestOf_lookup_unparked {m : NativeMachine} {f : NFiber} {fiber : FiberId}
    (lookup : m.fiber? fiber = some f) (park : f.parked = .notParked) (token : Nat) :
    requestOf m fiber token = none := by
  cases hr : requestOf m fiber token with
  | none => rfl
  | some request =>
    obtain ⟨g, found, hp, _⟩ := requestOf_shape hr
    have eq : g = f := Option.some.inj (found.symm.trans lookup)
    subst g
    rw [park] at hp; cases hp

theorem requestOf_lookup_internal {m : NativeMachine} {f : NFiber} {fiber : FiberId}
    (lookup : m.fiber? fiber = some f) (code : externalRequest f.frame.current = none) (token : Nat) :
    requestOf m fiber token = none := by
  cases hr : requestOf m fiber token with
  | none => rfl
  | some request =>
    obtain ⟨g, found, _, hc⟩ := requestOf_shape hr
    have eq : g = f := Option.some.inj (found.symm.trans lookup)
    subst g
    rw [code] at hc; cases hc

theorem requestOf_update_internal_eq {m : NativeMachine} {f : NFiber}
    (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (g : NFiber) (id : g.id = f.id) (code : externalRequest g.frame.current = none)
    (fiber : FiberId) (token : Nat) :
    requestOf (m.update g) fiber token = requestOf m fiber token := by
  by_cases same : g.id = fiber
  · have old : m.fiber? fiber = some f := by simpa only [← id, same] using lookup
    rw [requestOf_lookup_unparked old park, requestOf_lookup_internal
      (fiber_lookup_update_self old g same) code]
  · exact requestOf_update_other m g fiber token same

theorem guardQueue_update_internal_active (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} {rest : List NCmd}
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m))
    (g : NFiber) (id : g.id = f.id) (code : externalRequest g.frame.current = none) :
    GuardQueue p table (m.update g) rest := by
  have controls : ControlsAway m (m.update g) f.id := by
    simpa only [id] using controlsAway_update m g
  apply guardQueue_transport_away p table (n := m.update g) state ⟨f, lookup, running, park⟩ queue registration fresh
    controls (fun _ race hr => ⟨race, hr, rfl⟩) (Nat.le_refl _)
  exact requestOf_update_noExternal_subset m g code

theorem frameCodeOwned_finalizer {m : NativeMachine} {f : NFiber}
    (owned : FrameCodeOwned m f) (name : EffName) :
    FrameCodeOwned m { f with frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack } } := by
  refine ⟨owned.1, ?_⟩
  intro code member rid site
  rcases List.mem_cons.mp member with rfl | member
  · cases site
  · exact owned.2 code member rid site

theorem guardState_park_internal (m : NativeMachine) (f : NFiber) (frame : NFrame)
    (token : Nat) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (deferred : frame.deferredInterrupt = f.frame.deferredInterrupt)
    (cause : frame.interruptedCause = f.frame.interruptedCause)
    (code : externalRequest frame.current = none)
    (codes : FrameCodeOwned m { f with frame := frame }) (below : token < m.nextToken) :
    GuardState (settle f.id rest
      ⟨m, ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩,
        yielding, .parked, []⟩).1 := by
  have mem := List.mem_of_find?_eq_some lookup
  have old := guardState_fiber state mem
  have pending : f.pending = [] := by simpa only [PendingShape, park] using old.pending
  let g := ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩
  let it : NIter := ⟨m, g, yielding, .parked, []⟩
  have pshape : PendingShape g := by
    simp only [g, RunFiber.park, PendingShape, pending, List.nil_append]
    exact ⟨_, rfl, rfl⟩
  have valid : FiberGuardState m (settledFiber it) := settledFiber_valid it old.below pshape
    True.intro (fun next hp => Parked.withGuard.inj hp ▸ below)
    (active_noExit state (f := f) lookup running) (fun h => cause ▸ old.deferredCause (deferred ▸ h)) codes old.tasks
  exact guardState_settle f.id rest it state f lookup valid (reservedKeys_fiber state (f := f) mem)
    (fun _ _ _ hc => False.elim (by rw [show externalRequest g.frame.current = none from code] at hc; cases hc))

theorem guardQueue_park_internal (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (f : NFiber) (frame : NFrame)
    (token : Nat) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (code : externalRequest frame.current = none)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m)) :
    let result := settle f.id rest
      ⟨m, ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩,
        yielding, .parked, []⟩
    GuardQueue p table result.1 result.2 := by
  simp only [settle, List.nil_append, List.cons_append]
  split
  · let g : NFiber := { ({ f with frame := frame } : NFiber).park
        ⟨token, none, [], [], Resume.void, false⟩ with parked := .notParked, pending := [] }
    exact guardQueue_continue_active p table state lookup running park queue registration fresh g rfl running rfl yielding
  · exact guardQueue_update_internal_active p table state lookup running park queue registration fresh
      { ({ f with frame := frame } : NFiber).park
        ⟨token, none, [], [], Resume.void, false⟩ with running := false } rfl code

theorem requestOf_park_internal (m : NativeMachine) (f : NFiber) (frame : NFrame)
    (token : Nat) (yielding : Bool) (rest : List NCmd)
    (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (code : externalRequest frame.current = none) (fiber : FiberId) (offered : Nat) :
    requestOf (settle f.id rest
      ⟨m, ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩,
        yielding, .parked, []⟩).1 fiber offered = requestOf m fiber offered := by
  simp only [settle]
  split
  · exact requestOf_update_internal_eq lookup park
      { ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩ with parked := .notParked, pending := [] }
      rfl code fiber offered
  · exact requestOf_update_internal_eq lookup park
      { ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩ with running := false }
      rfl code fiber offered

theorem interruptedAt_park_internal (m : NativeMachine) (f : NFiber) (frame : NFrame)
    (token : Nat) (yielding : Bool) (rest : List NCmd)
    (lookup : m.fiber? f.id = some f)
    (deferred : frame.deferredInterrupt = f.frame.deferredInterrupt)
    (cause : frame.interruptedCause = f.frame.interruptedCause)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    InterruptedAt (settle f.id rest
      ⟨m, ({ f with frame := frame } : NFiber).park ⟨token, none, [], [], Resume.void, false⟩,
        yielding, .parked, []⟩).1 fiber := by
  apply interruptedAt_settle _ _ _ fiber before
  intro same
  obtain ⟨old, found, interrupted⟩ := before
  have eq : old = f := Option.some.inj (found.symm.trans (same ▸ lookup))
  subst old
  simpa only [Interrupted, RunFiber.interruptPending, frameCore, RunFiber.park, deferred, cause] using interrupted

theorem guardState_driveStep_registrationDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rid : Nat) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.registrationDone rid yielding)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.registrationDone rid yielding) rest).1 := by
  letI := evaluatorFor p table
  obtain ⟨race, f, hr, hf, running, park, code⟩ := authority
  have hr' : m.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
  let base : NativeMachine := m.updateRace { race with registering := false }
  have state' : GuardState base := guardState_updateRace state hr' _ rfl rfl rfl
    (state.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr))
  have lookup : base.fiber? f.id = some f := by
    change m.fiber? f.id = some f
    simpa only [fiber_id_of_lookup hf] using hf
  have valid := guardState_fiber state' (List.mem_of_find?_eq_some lookup)
  simp only [RunMachine.fiber?] at hf
  simp only [driveStep, hr, RunMachine.updateRace, RunMachine.fiber?, hf]
  cases accepted : race.state.accepted with
  | some exit =>
    let code' := (interpOf p table).raceSettle rid race.state.cleanupNeeded exit
    let frame := { f.frame with current := code' }
    simp only [settle]
    exact guardState_update_unparked state' lookup { f with frame := frame } rfl
      (fiberGuardState_reframe valid frame rfl rfl
        (frameCodeOwned_answer valid.codes code' (raceSites_raceSettle p table rid _ exit)))
      (reservedKeys_fiber state' (f := f) (List.mem_of_find?_eq_some lookup)) park
  | none =>
    let name := (interpOf p table).cancelName ((interpOf p table).raceCancelName rid) f.id race.token
    let frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack }
    have below : race.token < base.nextToken :=
      (reservedKeys_race state (List.mem_of_find?_eq_some hr)).below _ (List.mem_cons_self ..)
    exact guardState_park_internal (base.emit [RunEvent.parkedOn f.id race.token]) f frame
      race.token yielding rest (guardState_emit state' _) lookup running park rfl rfl
      (externalRequest_parkOf p table f.frame.current (.race rid) code)
      (frameCodeOwned_finalizer valid.codes name) below

theorem guardQueue_driveStep_registrationDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rid : Nat) (yielding : Bool) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.registrationDone rid yielding :: rest))
    (registration : RegistrationQueue (.registrationDone rid yielding :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.registrationDone rid yielding) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  obtain ⟨race, f, hr, hf, running, park, code⟩ := queue.authority _ (List.mem_cons_self ..)
  have hr' : m.race? race.id = some race := by simpa only [race_id_of_lookup hr] using hr
  let base : NativeMachine := m.updateRace { race with registering := false }
  have state' : GuardState base := guardState_updateRace state hr' _ rfl rfl rfl
    (state.internalCodes.2.2.2 race (List.mem_of_find?_eq_some hr))
  have lookup : base.fiber? f.id = some f := by
    change m.fiber? f.id = some f
    simpa only [fiber_id_of_lookup hf] using hf
  have queue' : GuardQueue p table base (.registrationDone rid yielding :: rest) :=
    guardQueue_updateRace p table queue hr' _ rfl rfl
  have fresh : f.id ∉ rest.filterMap (commandOwner base) := guardQueue_head_fresh p table queue' (by
    simp only [commandOwner, base, race_lookup_updateRace, hr, Option.map_some,
      ↓reduceIte,
      ← fiber_id_of_lookup hf])
  have tail := guardQueue_tail p table queue'
  simp only [RunMachine.fiber?] at hf
  simp only [driveStep, hr, RunMachine.updateRace, RunMachine.fiber?, hf]
  cases accepted : race.state.accepted with
  | some exit =>
    simp only [settle, List.nil_append, List.cons_append]
    exact guardQueue_continue_active p table state' lookup running park tail registration.2 fresh
      { f with frame := { f.frame with current := (interpOf p table).raceSettle rid race.state.cleanupNeeded exit } }
      rfl running park yielding
  | none =>
    let name := (interpOf p table).cancelName ((interpOf p table).raceCancelName rid) f.id race.token
    let frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack }
    exact guardQueue_park_internal p table (base.emit [RunEvent.parkedOn f.id race.token]) f frame
      race.token yielding rest (guardState_emit state' _) lookup running park
      (externalRequest_parkOf p table f.frame.current (.race rid) code)
      (guardQueue_emit p table tail _) registration.2 fresh

theorem requestOf_driveStep_registrationDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rid : Nat) (yielding : Bool) (rest : List NCmd)
    (authority : CommandAuthority p table m (.registrationDone rid yielding))
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.registrationDone rid yielding) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  obtain ⟨race, f, hr, hf, _, park, code⟩ := authority
  let base : NativeMachine := m.updateRace { race with registering := false }
  have lookup : base.fiber? f.id = some f := by
    change m.fiber? f.id = some f
    simpa only [fiber_id_of_lookup hf] using hf
  simp only [RunMachine.fiber?] at hf
  simp only [driveStep, hr, RunMachine.updateRace, RunMachine.fiber?, hf]
  cases accepted : race.state.accepted with
  | some exit =>
    simp only [settle]
    exact requestOf_update_unparked_eq lookup park
      { f with frame := { f.frame with current := (interpOf p table).raceSettle rid race.state.cleanupNeeded exit } }
      rfl park fiber token
  | none =>
    let name := (interpOf p table).cancelName ((interpOf p table).raceCancelName rid) f.id race.token
    let frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack }
    exact requestOf_park_internal (base.emit [RunEvent.parkedOn f.id race.token]) f frame
      race.token yielding rest lookup park (externalRequest_parkOf p table f.frame.current (.race rid) code) fiber token

theorem reservedKeys_driveStep_registrationDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rid : Nat) (yielding : Bool) (rest : List NCmd)
    (authority : CommandAuthority p table m (.registrationDone rid yielding))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.registrationDone rid yielding) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · simp only [driveStep]
    repeat' first | exact Nat.le_refl _ | (simp only [settle]; split) | split
  · exact requestOf_driveStep_registrationDone p table m rid yielding rest authority

theorem interruptedAt_driveStep_registrationDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rid : Nat) (yielding : Bool) (rest : List NCmd)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.registrationDone rid yielding) rest).1 fiber := by
  letI := evaluatorFor p table
  cases hr : m.race? rid with
  | none => simpa only [driveStep, hr] using before
  | some race =>
    let base : NativeMachine := m.updateRace { race with registering := false }
    simp only [driveStep, hr, RunMachine.updateRace, RunMachine.fiber?]
    cases hf : m.fibers.find? (fun f => f.id = race.host) with
    | none => exact before
    | some f =>
      have lookup : base.fiber? f.id = some f := by
        change m.fiber? f.id = some f
        simpa only [fiber_id_of_lookup (show m.fiber? race.host = some f from hf)] using
          (show m.fiber? race.host = some f from hf)
      cases accepted : race.state.accepted with
      | some exit =>
        simp only [settle]
        exact interruptedAt_update_reframe lookup
          { f.frame with current := (interpOf p table).raceSettle rid race.state.cleanupNeeded exit }
          rfl rfl fiber before
      | none =>
        let name := (interpOf p table).cancelName ((interpOf p table).raceCancelName rid) f.id race.token
        let frame := { f.frame with stack := Prim.asyncFinalizer name :: f.frame.stack }
        exact interruptedAt_park_internal (base.emit [RunEvent.parkedOn f.id race.token]) f frame
          race.token yielding rest lookup rfl rfl fiber before

theorem registrationQueue_driveStep_registrationDone (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (rid : Nat) (yielding : Bool) (rest : List NCmd)
    (registration : RegistrationQueue (.registrationDone rid yielding :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.registrationDone rid yielding) rest).2 := by
  letI := evaluatorFor p table
  simp only [driveStep]
  repeat' first
    | exact registration.2
    | exact ⟨True.intro, registration.2⟩
    | (simp only [settle, List.nil_append, List.cons_append]; split)
    | split


end Effect4.Program.Guard
