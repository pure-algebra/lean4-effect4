import Effect4.Laws.Program.Guard.Observer

set_option autoImplicit false
set_option maxRecDepth 2048
namespace Effect4.Program.Guard
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard.RegistrationQueue

abbrev NFrame := FrameFiber EffName EffThunk Val Err Defect FiberId Ann

theorem fiberGuardState_reframe {m : NativeMachine} {f : NFiber}
    (valid : FiberGuardState m f) (frame : NFrame)
    (deferred : frame.deferredInterrupt = f.frame.deferredInterrupt)
    (cause : frame.interruptedCause = f.frame.interruptedCause)
    (codes : FrameCodeOwned m { f with frame := frame }) :
    FiberGuardState m { f with frame := frame } :=
  ⟨valid.below, valid.pending, valid.idle, valid.parkedBelow, valid.exited,
    fun h => cause ▸ valid.deferredCause (deferred ▸ h), codes, valid.tasks⟩

theorem requestOf_update_unparked_eq {m : NativeMachine} {f : NFiber}
    (lookup : m.fiber? f.id = some f) (park : f.parked = .notParked)
    (g : NFiber) (id : g.id = f.id) (nextPark : g.parked = .notParked)
    (fiber : FiberId) (token : Nat) :
    requestOf (m.update g) fiber token = requestOf m fiber token := by
  by_cases same : g.id = fiber
  · have old : m.fiber? fiber = some f := by simpa only [← id, same] using lookup
    have new := fiber_lookup_update_self old g same
    simp [requestOf, new, old, nextPark, park, guard]
    rfl
  · exact requestOf_update_other m g fiber token same

theorem interruptedAt_update_reframe {m : NativeMachine} {f : NFiber}
    (lookup : m.fiber? f.id = some f) (frame : NFrame)
    (deferred : frame.deferredInterrupt = f.frame.deferredInterrupt)
    (cause : frame.interruptedCause = f.frame.interruptedCause)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    InterruptedAt (m.update { f with frame := frame }) fiber := by
  by_cases same : f.id = fiber
  · obtain ⟨old, found, interrupted⟩ := before
    have equal : old = f := Option.some.inj (found.symm.trans (same ▸ lookup))
    subst old
    refine ⟨{ f with frame := frame }, fiber_lookup_update_self found _ same, ?_⟩
    simpa only [Interrupted, RunFiber.interruptPending, frameCore, deferred, cause] using interrupted
  · exact interruptedAt_update_other m { f with frame := frame } same before

theorem guardQueue_update_active (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} {rest : List NCmd}
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m))
    (g : NFiber) (id : g.id = f.id) (nextPark : g.parked = .notParked) :
    GuardQueue p table (m.update g) rest := by
  have controls : ControlsAway m (m.update g) f.id := by
    simpa only [id] using controlsAway_update m g
  apply guardQueue_transport_away p table (n := m.update g) state ⟨f, lookup, running, park⟩ queue registration fresh
    controls (fun _ race hr => ⟨race, hr, rfl⟩) (Nat.le_refl _)
  exact requestOf_update_unparked_subset m g nextPark

theorem guardQueue_continue_active (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} {rest : List NCmd}
    (state : GuardState m) (lookup : m.fiber? f.id = some f)
    (running : f.running = true) (park : f.parked = .notParked)
    (queue : GuardQueue p table m rest) (registration : RegistrationQueue rest)
    (fresh : f.id ∉ rest.filterMap (commandOwner m))
    (g : NFiber) (id : g.id = f.id) (nextRunning : g.running = true)
    (nextPark : g.parked = .notParked) (yielding : Bool) :
    GuardQueue p table (m.update g) (.loop f.id yielding :: rest) := by
  apply guardQueue_cons_loop p table f.id yielding
    (guardQueue_update_active p table state lookup running park queue registration fresh g id nextPark)
    ⟨g, fiber_lookup_update_self lookup g id, nextRunning, nextPark⟩
  exact fresh

theorem guardQueue_head_fresh (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {command : NCmd} {rest : List NCmd} {fiber : FiberId}
    (queue : GuardQueue p table m (command :: rest)) (owner : commandOwner m command = some fiber) :
    fiber ∉ rest.filterMap (commandOwner m) := by
  have nodup := queue.owners
  rw [List.filterMap_cons, owner] at nodup
  exact (List.nodup_cons.mp nodup).1

theorem raceSites_afterInterrupt (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (host : FiberId) (yielding : Bool) (kind : ParkKind)
    (sites : commandRaceSites (.afterInterrupt host yielding kind) = []) :
    raceSites (asVoidCode (interpOf p table) (awaitCode (interpOf p table) m kind)) = [] := by
  cases kind <;> try rfl
  case join target mode =>
    simp only [awaitCode, asVoidCode, raceSites]
    split
    · exact raceSites_exitValue p table _ mode
    · rfl
  case race rid => cases sites

theorem frameCodeOwned_answer {m : NativeMachine} {f : NFiber}
    (owned : FrameCodeOwned m f) (code : NCode) (sites : raceSites code = []) :
    FrameCodeOwned m { f with frame := { f.frame with current := code } } := by
  exact ⟨fun rid member => False.elim (by rw [sites] at member; cases member), owned.2⟩

theorem guardState_driveStep_afterInterrupt (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.afterInterrupt host yielding kind))
    (sites : commandRaceSites (.afterInterrupt host yielding kind) = []) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.afterInterrupt host yielding kind) rest).1 := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, running, park⟩ := authority
  have hid := fiber_id_of_lookup lookup
  have found : m.fiber? f.id = some f := by simpa only [hid] using lookup
  have valid := guardState_fiber state (List.mem_of_find?_eq_some lookup)
  let code := asVoidCode (interpOf p table) (awaitCode (interpOf p table) m kind)
  let g : NFiber := { f with frame := { f.frame with current := code } }
  have codes := frameCodeOwned_answer valid.codes code (raceSites_afterInterrupt p table m host yielding kind sites)
  simpa only [driveStep, lookup, settle, List.nil_append, List.cons_append] using
    guardState_update_unparked state found g rfl
      (fiberGuardState_reframe valid _ rfl rfl codes)
      (reservedKeys_fiber state (f := f) (List.mem_of_find?_eq_some lookup)) park

theorem guardQueue_driveStep_afterInterrupt (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.afterInterrupt host yielding kind :: rest))
    (registration : RegistrationQueue (.afterInterrupt host yielding kind :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.afterInterrupt host yielding kind) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, running, park⟩ := queue.authority _ (List.mem_cons_self ..)
  have hid := fiber_id_of_lookup lookup
  have found : m.fiber? f.id = some f := by simpa only [hid] using lookup
  have fresh := guardQueue_head_fresh p table queue (show commandOwner m (.afterInterrupt host yielding kind) = some host from rfl)
  simpa only [driveStep, lookup, settle, List.nil_append, List.cons_append] using
    guardQueue_continue_active p table state found running park (guardQueue_tail p table queue)
      registration.2 (hid ▸ fresh)
      { f with frame := { f.frame with current := asVoidCode (interpOf p table) (awaitCode (interpOf p table) m kind) } }
      rfl running park yielding

theorem requestOf_driveStep_afterInterrupt (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (authority : CommandAuthority p table m (.afterInterrupt host yielding kind))
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.afterInterrupt host yielding kind) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, _, park⟩ := authority
  have found : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
  simp only [driveStep, lookup, settle]
  exact requestOf_update_unparked_eq found park
    { f with frame := { f.frame with current := asVoidCode (interpOf p table) (awaitCode (interpOf p table) m kind) } }
    rfl park fiber token

theorem reservedKeys_driveStep_afterInterrupt (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (authority : CommandAuthority p table m (.afterInterrupt host yielding kind))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.afterInterrupt host yielding kind) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · simp only [driveStep]; split <;> exact Nat.le_refl _
  · exact requestOf_driveStep_afterInterrupt p table m host yielding kind rest authority

theorem interruptedAt_driveStep_afterInterrupt (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.afterInterrupt host yielding kind) rest).1 fiber := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? host with
  | none => simpa only [driveStep, lookup] using before
  | some f =>
    have found : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
    simp only [driveStep, lookup, settle]
    exact interruptedAt_update_reframe found
      { f.frame with current := asVoidCode (interpOf p table) (awaitCode (interpOf p table) m kind) }
      rfl rfl fiber before

theorem registrationQueue_driveStep_afterInterrupt (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (kind : ParkKind) (rest : List NCmd)
    (registration : RegistrationQueue (.afterInterrupt host yielding kind :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.afterInterrupt host yielding kind) rest).2 := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? host with
  | none => simpa only [driveStep, lookup] using registration.2
  | some f =>
    simp only [driveStep, lookup, settle, List.nil_append, List.cons_append]
    exact ⟨True.intro, registration.2⟩

theorem frameCodeOwned_closeParAwait (p : NativeEff) (table : RowTable)
    {m : NativeMachine} {f : NFiber} (fibers : List FiberId) (owned : FrameCodeOwned m f) :
    FrameCodeOwned m { f with frame :=
      { f.frame with current := (interpOf p table).parkCode (.awaitAll fibers), stack := Prim.iterator (interpOf p table).closeDoneName (interpOf p table).voidValue :: f.frame.stack } } := by
  constructor
  · intro rid member; cases member
  · intro code member rid site
    rcases List.mem_cons.mp member with rfl | member
    · cases site
    · exact owned.2 code member rid site

theorem guardState_driveStep_closeParAwait (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List NCmd)
    (state : GuardState m) (authority : CommandAuthority p table m (.closeParAwait host yielding fibers)) :
    letI := evaluatorFor p table
    GuardState (driveStep (interpOf p table) m (.closeParAwait host yielding fibers) rest).1 := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, _, park⟩ := authority
  have found : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
  have valid := guardState_fiber state (List.mem_of_find?_eq_some lookup)
  let frame := { f.frame with current := (interpOf p table).parkCode (.awaitAll fibers), stack := Prim.iterator (interpOf p table).closeDoneName (interpOf p table).voidValue :: f.frame.stack }
  simp only [driveStep, lookup, settle]
  exact guardState_update_unparked state found { f with frame := frame } rfl
    (fiberGuardState_reframe valid frame rfl rfl (frameCodeOwned_closeParAwait p table fibers valid.codes))
    (reservedKeys_fiber state (f := f) (List.mem_of_find?_eq_some lookup)) park

theorem guardQueue_driveStep_closeParAwait (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List NCmd)
    (state : GuardState m) (queue : GuardQueue p table m (.closeParAwait host yielding fibers :: rest))
    (registration : RegistrationQueue (.closeParAwait host yielding fibers :: rest)) :
    letI := evaluatorFor p table
    let result := driveStep (interpOf p table) m (.closeParAwait host yielding fibers) rest
    GuardQueue p table result.1 result.2 := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, running, park⟩ := queue.authority _ (List.mem_cons_self ..)
  have hid := fiber_id_of_lookup lookup
  have found : m.fiber? f.id = some f := by simpa only [hid] using lookup
  have fresh := guardQueue_head_fresh p table queue (show commandOwner m (.closeParAwait host yielding fibers) = some host from rfl)
  let frame := { f.frame with current := (interpOf p table).parkCode (.awaitAll fibers), stack := Prim.iterator (interpOf p table).closeDoneName (interpOf p table).voidValue :: f.frame.stack }
  simpa only [driveStep, lookup, settle, List.nil_append, List.cons_append] using
    guardQueue_continue_active p table state found running park (guardQueue_tail p table queue)
      registration.2 (hid ▸ fresh) { f with frame := frame } rfl running park yielding

theorem requestOf_driveStep_closeParAwait (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List NCmd)
    (authority : CommandAuthority p table m (.closeParAwait host yielding fibers))
    (fiber : FiberId) (token : Nat) :
    letI := evaluatorFor p table
    requestOf (driveStep (interpOf p table) m (.closeParAwait host yielding fibers) rest).1 fiber token =
      requestOf m fiber token := by
  letI := evaluatorFor p table
  obtain ⟨f, lookup, _, park⟩ := authority
  have found : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
  simp only [driveStep, lookup, settle]
  exact requestOf_update_unparked_eq found park
    { f with frame := { f.frame with current := (interpOf p table).parkCode (.awaitAll fibers), stack := Prim.iterator (interpOf p table).closeDoneName (interpOf p table).voidValue :: f.frame.stack } }
    rfl park fiber token

theorem reservedKeys_driveStep_closeParAwait (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List NCmd)
    (authority : CommandAuthority p table m (.closeParAwait host yielding fibers))
    (keys : List GuardKey) (reserved : ReservedKeys m keys) :
    letI := evaluatorFor p table
    ReservedKeys (driveStep (interpOf p table) m (.closeParAwait host yielding fibers) rest).1 keys := by
  letI := evaluatorFor p table
  apply reservedKeys_of_same_requests reserved
  · simp only [driveStep]; split <;> exact Nat.le_refl _
  · exact requestOf_driveStep_closeParAwait p table m host yielding fibers rest authority

theorem interruptedAt_driveStep_closeParAwait (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List NCmd)
    (fiber : FiberId) (before : InterruptedAt m fiber) :
    letI := evaluatorFor p table
    InterruptedAt (driveStep (interpOf p table) m (.closeParAwait host yielding fibers) rest).1 fiber := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? host with
  | none => simpa only [driveStep, lookup] using before
  | some f =>
    have found : m.fiber? f.id = some f := by simpa only [fiber_id_of_lookup lookup] using lookup
    simp only [driveStep, lookup, settle]
    exact interruptedAt_update_reframe found
      { f.frame with current := (interpOf p table).parkCode (.awaitAll fibers), stack := Prim.iterator (interpOf p table).closeDoneName (interpOf p table).voidValue :: f.frame.stack }
      rfl rfl fiber before

theorem registrationQueue_driveStep_closeParAwait (p : NativeEff) (table : RowTable)
    (m : NativeMachine) (host : FiberId) (yielding : Bool) (fibers : List FiberId) (rest : List NCmd)
    (registration : RegistrationQueue (.closeParAwait host yielding fibers :: rest)) :
    letI := evaluatorFor p table
    RegistrationQueue (driveStep (interpOf p table) m (.closeParAwait host yielding fibers) rest).2 := by
  letI := evaluatorFor p table
  cases lookup : m.fiber? host with
  | none => simpa only [driveStep, lookup] using registration.2
  | some f =>
    simp only [driveStep, lookup, settle, List.nil_append, List.cons_append]
    exact ⟨True.intro, registration.2⟩



end Effect4.Program.Guard
