import Effect4.Laws.Program.NativeConfiguration

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
Native evaluation retains source locations across the actual interpreter hooks.
The result carries the returned fiber and its nested command list separately.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program
abbrev SourceIteration := Iter EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- An evaluation result retains the stored configuration, acting fiber and pending commands. -/
structure EvaluationAt (root : NativeEff) (it : SourceIteration) : Prop where
  machine : ConfigurationAt root it.machine
  fiber : FiberAt root it.fiber
  commands : CommandsAt root it.nested

/-- Administrative finalizer composition retains the actual cleanup program. -/
theorem finalizer_code_at (root : NativeEff) (completed) (table : RowTable) (exit : ExitV)
    (program : NCode) (owned : CodeAt root program) :
    CodeAt root (finalizerCode (interpAt root completed table) exit program) := by
  cases exit
  · refine ⟨owned, trivial, ?_⟩
    intro _ _ wrong
    cases wrong
  · refine ⟨⟨owned, trivial⟩, trivial, ?_⟩
    intro _ _ wrong
    cases wrong

/-- The native exit-value hook introduces no source writer. -/
theorem exit_value_at (root : NativeEff) (completed) (table : RowTable) (exit : ExitV)
    (mode : Supervision.ObserverMode) : CodeAt root ((interpAt root completed table).exitValue exit mode) := by
  cases mode
  · trivial
  · exact ofExit_at root exit

/-- Asynchronous registration retains stores and every immediate completion program. -/
theorem register_at (root : NativeEff) (completed) (table : RowTable) (name : EffName)
    (fiber : FiberId) (token : Nat) (state : Stores) (owned : ScopesAt root state.scopes) :
    ScopesAt root ((interpAt root completed table).registerAsync name fiber token state).1.scopes ∧
      ∀ code ∈ ((interpAt root completed table).registerAsync name fiber token state).2, CodeAt root code := by
  cases name
  case registerAwait cell =>
    refine ⟨owned, ?_⟩
    intro code member
    rw [Option.mem_def] at member
    obtain ⟨answer, _, eq⟩ := Option.map_eq_some_iff.mp member
    rw [← eq]
    exact completion_at root answer
  case store name =>
    cases name
    case registerAwait cell =>
      refine ⟨owned, ?_⟩
      intro code member
      rw [Option.mem_def] at member
      obtain ⟨answer, _, eq⟩ := Option.map_eq_some_iff.mp member
      rw [← eq]
      exact completion_at root answer
    all_goals exact ⟨owned, by intro code member; cases member⟩
  all_goals exact ⟨owned, by intro code member; cases member⟩

/-- Native synchronous evaluation keeps saved scope captures of the actual operation. -/
theorem sync_at (root : NativeEff) (completed) (table : RowTable) (thunk : EffThunk)
    (state next : Stores) (answer : Val) (owned : ScopesAt root state.scopes)
    (source : ThunkAt root thunk)
    (found : (interpAt root completed table).syncState thunk state = some (next, answer)) :
    ScopesAt root next.scopes := by
  cases thunk
  case op op => exact sync_scopes_at root op state next answer owned source found
  case store thunk =>
    cases thunk
    case op op => exact sync_scopes_at root op state next answer owned source found
    all_goals cases found
  all_goals cases found

/-- A native synchronous evaluation keeps the cell predicate of its checked source writer. -/
theorem sync_heap_at (root : NativeEff) (completed) (table : RowTable) (thunk : EffThunk)
    (state next : Stores) (answer : Val) (P : Val → Prop) (sites : HeapSites.SitesKeep root P)
    (owned : HeapSites.HeapOk P state.refs) (source : ThunkAt root thunk)
    (found : (interpAt root completed table).syncState thunk state = some (next, answer)) :
    HeapSites.HeapOk P next.refs := by
  cases thunk
  case op op => exact op_at_keeps root P sites op source state next answer found owned
  case store thunk =>
    cases thunk
    case op op => exact op_at_keeps root P sites op source state next answer found owned
    all_goals cases found
  all_goals cases found

/-- Native public close returns an owned cleanup program and state-first scope store. -/
theorem interp_close_at (root : NativeEff) (completed) (table : RowTable) (scope : Nat)
    (exit : ExitV) (flag : Bool) (fiber : FiberId) (state next : Stores) (program : NCode)
    (owned : ScopesAt root state.scopes)
    (found : (interpAt root completed table).closeScope scope exit flag fiber state = some (next, program)) :
    ScopesAt root next.scopes ∧ CodeAt root program := by
  change (storesCloseScope scope exit flag state).map (fun r => (r.1, embed r.2)) = some (next, program) at found
  obtain ⟨result, operation, eq⟩ := Option.map_eq_some_iff.mp found
  cases eq
  exact close_public_at root scope exit flag state result.1 result.2 owned operation

/-- Delegating to the actual frame machine retains its returned fiber and nested residue. -/
theorem step_frame_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (evaluatePrim.stepFrame (interpAt root completed table) m fiber yielding) := by
  have next := frame_step_at root fragment completed table fiber.frame held.frame
  unfold evaluatePrim.stepFrame
  cases h : fiber.frame.step (interpAt root completed table).toPrimInterp with
  | mk step events =>
    rw [h] at next
    cases step with
    | running frame =>
      exact ⟨configuration_emit root m _ owned, fiber_frame_at root fiber frame held next,
        by intro command member; cases member⟩
    | finished exit =>
      exact ⟨configuration_emit root m _ owned,
        fiber_frame_at root fiber _ held (frame_exit_at root fiber.frame held.frame),
        by intro command member; cases member⟩

/-- The actual answering finalizer frame retains the continuation name it exposes. -/
theorem pop_finalizer_at (root : NativeEff) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (demand : Effect4.Arm) (skip : Bool) (cause : Option CauseV) (body : NCode) (name : EffName)
    (flag : Bool) (owned : FrameAt root fiber)
    (found : (fiber.getCont demand skip cause).answer = .frame (.onExit body name flag)) :
    NameAt root name := by
  have answer := (getCont_at root fiber demand skip cause owned.2).2
  rw [found] at answer
  exact answer.2

/-- Running the represented finalizer retains its captured source and restoring continuation. -/
theorem finalizer_at (root : NativeEff) (fragment : Fragment root) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (exit : ExitV)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (evaluatePrim.finalizerOr (interpAt root completed table) m fiber yielding exit) := by
  cases exit <;> unfold evaluatePrim.finalizerOr <;> dsimp only
  all_goals
    split
    · rename_i body fin flag answer
      split
      · rename_i program operation
        have finOwned := pop_finalizer_at root fiber.frame _ _ _ body fin flag held.frame answer
        have code := interp_fin_at root fragment completed table fin _ program finOwned operation
        refine ⟨configuration_emit root m _ owned, ⟨⟨?_, ?_⟩,
          held.pending, held.dispatcher⟩, by intro command member; cases member⟩
        · dsimp only
          apply finalizer_code_at root completed table
          exact code
        · exact (getCont_at root fiber.frame _ _ _ held.frame.2).1
      · exact step_frame_at root fragment completed table m fiber yielding owned held
    · exact step_frame_at root fragment completed table m fiber yielding owned held

/-- Starting a spawned child retains the parent's dispatcher and administrative commands. -/
theorem start_at (root : NativeEff) (m : NativeMachine) (parent : SourceFiber) (child : FiberId)
    (immediately : Bool) (owned : ConfigurationAt root m) (held : FiberAt root parent) :
    ConfigurationAt root (start m parent child immediately).1 ∧
      FiberAt root (start m parent child immediately).2.1 ∧
      CommandsAt root (start m parent child immediately).2.2 := by
  unfold start
  split
  · exact ⟨owned, held, by intro command member; rw [List.mem_singleton.mp member]; trivial⟩
  · exact ⟨configuration_emit root _ _ (configuration_arm root m parent.id owned),
      ⟨held.frame, held.pending,
        dispatcher_enqueue_at root parent.dispatcher 0 (.start child) held.dispatcher trivial⟩,
      by intro command member; cases member⟩

/-- A native countdown answer retains its saved continuation. -/
theorem countdown_program_at (root : NativeEff) (completed) (table : RowTable)
    (resume : Resume EffName) (exits : List ExitV) (owned : ResumeAt root resume) :
    CodeAt root (countdownPark.resumePrim (interpAt root completed table) resume exits) := by
  cases resume
  · trivial
  · trivial
  · exact False.elim owned

/-- Native countdown producers resume with exits or void, never a source callback.
Consumer: the countdown observer's queued resume. -/
theorem countdown_program_reply (root : NativeEff) (completed) (table : RowTable)
    (resume : Resume EffName) (exits : List ExitV) (owned : ResumeAt root resume) :
    TerminalReply (countdownPark.resumePrim (interpAt root completed table) resume exits) := by
  cases resume
  · constructor
  · constructor
  · exact False.elim owned

/-- Native observed exits contain no delayed source code.
Consumer: join and observer resume producers. -/
theorem exit_value_reply (root : NativeEff) (completed) (table : RowTable) (exit : ExitV)
    (mode : Supervision.ObserverMode) :
    TerminalReply ((interpAt root completed table).exitValue exit mode) := by
  cases mode
  · constructor
  · cases exit <;> constructor

/-- Native countdown parks retain the pending continuation and actual cleanup frame. -/
theorem countdown_at (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (fiber : SourceFiber) (targets : List FiberId) (resume : Resume EffName) (failFast : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) (saved : ResumeAt root resume) :
    ConfigurationAt root (countdownPark (interpAt root completed table) m fiber targets resume failFast).1 ∧
      FiberAt root (countdownPark (interpAt root completed table) m fiber targets resume failFast).2.1 := by
  have grown : ConfigurationAt root {m with nextToken := m.nextToken + 1} :=
    ⟨owned.fibers, owned.races, owned.scopes⟩
  unfold countdownPark
  dsimp only
  split
  · exact ⟨grown, fiber_current_at root fiber _ held (countdown_program_at root completed table resume _ saved)⟩
  · rename_i exits target remaining walk
    refine ⟨configuration_emit root _ _ ?_, ?_⟩
    · apply configuration_modify root _ target _ grown
      intro other old
      exact ⟨old.frame, old.pending, old.dispatcher⟩
    · apply fiber_park_at root _ _ _ saved
      exact fiber_cancel_at root fiber _ held trivial

/-- Race registration retains its existing entrant programs. -/
theorem register_race_at (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber)
    (yielding : Bool) (id : Nat) (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (registerRace m fiber yielding id) := by
  unfold registerRace
  split
  · exact ⟨owned, held, by intro command member; cases member⟩
  · rename_i race found
    exact ⟨configuration_race_update root m _ owned (configuration_race root m id race owned found),
      held, by intro command member; rcases List.mem_cons.mp member with same | later
               · rw [same]; trivial
               · rcases List.mem_cons.mp later with same | empty
                 · rw [same]; trivial
                 · cases empty⟩

/-- Race entry retains its actual source programs and counted registration primitive. -/
theorem begin_race_at (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (programs : List NCode)
    (site : Option (List Nat)) (mode : Supervision.RaceMode) (owned : ConfigurationAt root m)
    (held : FiberAt root fiber) (entrants : ∀ code ∈ programs, CodeAt root code) :
    EvaluationAt root (beginRace (interpAt root completed table) m fiber yielding programs site mode) :=
  ⟨configuration_begin_race root completed table m fiber yielding programs site mode owned entrants,
    fiber_current_at root fiber _ held trivial, by intro command member; cases member⟩

/-- Recording an interrupt retains all source programs and saved continuations. -/
theorem interrupt_record_at (root : NativeEff) (completed) (table : RowTable)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (interruptRecord (interpAt root completed table) who extra fiber).1 := by
  unfold interruptRecord
  dsimp only
  repeat' split
  all_goals aesop (add safe constructors [FiberAt]) (add norm simp [FrameAt, CodeAt]) (add safe cases [FiberAt])

/-- Linking a fiber registers only its administrative interrupt finalizer. -/
theorem scope_link_at (root : NativeEff) (completed) (table : RowTable) (mode : Supervision.ScopeMode)
    (scope : Nat) (fiber : FiberId) (state next : Stores) (key : Nat)
    (owned : ScopesAt root state.scopes)
    (found : (interpAt root completed table).scopeLinkFiber mode scope fiber state = some (next, key)) :
    ScopesAt root next.scopes := by
  simp only [interpAt, interpOf] at found
  split at found
  · cases found
  · cases found
    exact scope_register_at root state.scopes scope state.nextName _ owned trivial

set_option maxHeartbeats 1600000 in
/-- The actual scope-link command retains its stored programs and administrative residue. -/
theorem link_at (root : NativeEff) (completed) (table : RowTable) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId) (who : Option FiberId)
    (extra : ReasonAnnotations Ann) (owned : ConfigurationAt root m) :
    ConfigurationAt root (linkScope (interpAt root completed table) m mode scope target who extra).1 ∧
      CommandsAt root (linkScope (interpAt root completed table) m mode scope target who extra).2 := by
  unfold linkScope
  cases hs : (interpAt root completed table).scopeStatus scope m.state with
  | none => exact ⟨configuration_halt root m _ owned, by intro command member; cases member⟩
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact ⟨configuration_halt root m _ owned, by intro command member; cases member⟩
      | some fiber =>
        simp only []
        refine ⟨configuration_emit root _ _ (configuration_update root m _ owned
          (interrupt_record_at root completed table who extra fiber
            (configuration_fiber root m target fiber owned hf))), ?_⟩
        split
        · intro command member; rw [List.mem_singleton.mp member]; trivial
        · intro command member; cases member
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact ⟨configuration_halt root m _ owned, by intro command member; cases member⟩
      | some fiber =>
        simp only []
        split
        · exact ⟨owned, by intro command member; cases member⟩
        · cases hl : (interpAt root completed table).scopeLinkFiber mode scope target m.state with
          | none => exact ⟨configuration_halt root m _ owned, by intro command member; cases member⟩
          | some result =>
            rcases result with ⟨state, key⟩
            refine ⟨configuration_emit root _ _ ?_, by intro command member; cases member⟩
            apply configuration_modify root _ target _
              (configuration_store root m state owned
                (scope_link_at root completed table mode scope target m.state state key owned.scopes hl))
            intro other old
            exact ⟨old.frame, old.pending, old.dispatcher⟩


/-- Parallel closing launches exactly the finalizer programs owned by its source captures. -/
theorem fork_finalizers_at (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (programs : List NCode)
    (owned : ConfigurationAt root m) (captured : ∀ code ∈ programs, CodeAt root code) :
    ConfigurationAt root (forkFinalizers (interpAt root completed table) m fiber programs).1 := by
  induction programs generalizing m with
  | nil => exact owned
  | cons program rest ih =>
    have first := captured program (.head _)
    have tail : ∀ code ∈ rest, CodeAt root code := fun code member => captured code (.tail _ member)
    have spawned := configuration_spawn root completed table m fiber program ⟨true, true, .inherit⟩ [] owned first
    exact ih _ spawned tail

/-- Entering a mask retains source scopes while pushing only its administrative restoring frame. -/
theorem mask_frame_at (root : NativeEff) (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann)
    (owned : FrameAt root fiber) : FrameAt root fiber.uninterruptible := by
  unfold FrameFiber.uninterruptible
  split
  · refine ⟨owned.1, ?_⟩
    intro code member
    rcases List.mem_cons.mp member with same | old
    · rw [same]; trivial
    · exact owned.2 code old
  · exact owned

/-- An interruptible region retains its frame and only adds a pending-cause failure replacement. -/
theorem interruptible_frame_at (root : NativeEff)
    (fiber : FrameFiber EffName EffThunk Val Err Defect FiberId Ann) (owned : FrameAt root fiber) :
    FrameAt root fiber.interruptibleRegion.1 ∧ ∀ code ∈ fiber.interruptibleRegion.2, CodeAt root code := by
  unfold FrameFiber.interruptibleRegion
  split
  · exact ⟨owned, by intro code member; cases member⟩
  · refine ⟨⟨owned.1, ?_⟩, ?_⟩
    · intro code member
      rcases List.mem_cons.mp member with same | old
      · rw [same]; trivial
      · exact owned.2 code old
    · unfold FrameFiber.setFiberInterruptible
      dsimp only
      cases fiber.interruptedCause with
      | none => intro code member; cases member
      | some cause =>
        intro code member
        rw [Option.mem_def] at member
        cases member
        trivial

end Effect4.Program.SourceScope
