import Effect4.Laws.Program.NativeExecutor
import Effect4.Laws.Machine.Lift

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The command invariant retains code in the actual queue and dispatcher snapshot.
Its rules follow native evaluation, observers, resumes and scope closure.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The native loop top changes only administrative interrupt fields and its failure primitive. -/
theorem loop_top_at (root : NativeEff) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (runloopTop fiber) := by
  unfold runloopTop
  split
  · exact ⟨⟨trivial, held.frame.2⟩, held.pending, held.dispatcher⟩
  · exact held

/-- Charging an operation leaves every source-bearing slot intact. -/
theorem count_at (root : NativeEff) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (countOp fiber) := ⟨held.frame, held.pending, held.dispatcher⟩

/-- Forced yield retains the deferred program as its actual constant continuation. -/
theorem yield_at (root : NativeEff) (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (it : SourceIteration) (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (found : injectYield m fiber yielding = some it) : EvaluationAt root it := by
  unfold injectYield at found
  split at found
  · cases found
    exact ⟨configuration_emit root m _ owned,
      ⟨⟨⟨trivial, held.frame.1⟩, held.frame.2⟩, held.pending, held.dispatcher⟩,
      by intro command member; cases member⟩
  · cases found

/-- One actual native iteration retains its evaluation result's source locations. -/
theorem iteration_at (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    EvaluationAt root (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding) := by
  have charged := count_at root _ (loop_top_at root fiber held)
  unfold iteration
  dsimp only
  split
  · rename_i it found
    have retained := yield_at root m _ yielding it owned charged found
    exact native_at root fragment table it.machine it.fiber it.yielding retained.machine retained.fiber
  · exact native_at root fragment table m _ yielding owned charged

/-- Settling retains stored source slots and the actual pending command suffix. -/
theorem settle_at (root : NativeEff) (id : FiberId) (rest : List SourceCommand) (it : SourceIteration)
    (owned : EvaluationAt root it) (pending : CommandsAt root rest) :
    ConfigurationAt root (settle id rest it).1 ∧ CommandsAt root (settle id rest it).2 := by
  have stopped : FiberAt root {it.fiber with running := false} :=
    ⟨owned.fiber.frame, owned.fiber.pending, owned.fiber.dispatcher⟩
  have cleared : FiberAt root {it.fiber with parked := .notParked, pending := []} :=
    ⟨owned.fiber.frame, (by intro p member; cases member), owned.fiber.dispatcher⟩
  have installed := configuration_update root it.machine it.fiber owned.machine owned.fiber
  have halted := configuration_update root it.machine _ owned.machine stopped
  have resumed := configuration_update root it.machine _ owned.machine cleared
  have suffix (c : SourceCommand) (admin : CommandAt root c) :
      CommandsAt root (it.nested ++ [c] ++ rest) :=
    commands_append root _ rest
      (commands_append root it.nested [c] owned.commands (by intro x member; rw [List.mem_singleton.mp member]; exact admin)) pending
  unfold settle
  split
  · exact ⟨installed, suffix _ trivial⟩
  · exact ⟨installed, suffix _ trivial⟩
  · split
    · exact ⟨resumed, suffix _ trivial⟩
    · exact ⟨halted, commands_append root _ _ owned.commands pending⟩
  · exact ⟨installed, commands_append root _ _ owned.commands pending⟩
  · exact ⟨installed, suffix _ trivial⟩
  · exact ⟨configuration_halt root _ _ halted, by intro c member; cases member⟩

/-- Race settlement introduces only administrative cleanup and the accepted exit. -/
theorem race_settle_at (root : NativeEff) (table : RowTable) (race : Nat) (cleanup : Bool) (exit : ExitV)
    (allowed : RaceAllowed root) :
    CodeAt root ((interpOf root table).raceSettle race cleanup exit) := by
  change CodeAt root (embed (raceSettleProgram race cleanup exit))
  unfold raceSettleProgram
  split
  · refine ⟨allowed, trivial, ?_⟩
    intro _ _ wrong
    cases wrong
  · cases exit <;> trivial

/-- Race callbacks return a fixed administrative cleanup or the accepted exit.
Consumer: the race observer's actual queued resume. -/
theorem race_settle_reply (root : NativeEff) (table : RowTable) (race : Nat)
    (cleanup : Bool) (exit : ExitV) :
    TerminalReply ((interpOf root table).raceSettle race cleanup exit) := by
  change TerminalReply (embed (raceSettleProgram race cleanup exit))
  unfold raceSettleProgram
  split
  · exact .raceCleanup race exit
  · cases exit <;> constructor

/-- A native owed completion embeds only a completion primitive. -/
theorem owed_completion_at (root : NativeEff) (owed : Owed (Completion Val Err Defect FiberId Ann)) :
    CodeAt root (Owed.mapCode (fun c => embed (completionPrim c)) owed).code ∧
      TerminalReply (Owed.mapCode (fun c => embed (completionPrim c)) owed).code :=
    ⟨completion_at root owed.code, completion_reply owed.code⟩

/-- The due drain retains its scope captures and every actual completion program. -/
theorem due_at (root : NativeEff) (table : RowTable) (state : Stores) (owned : ScopesAt root state.scopes) :
    ScopesAt root ((interpOf root table).dueResumes state).2.scopes ∧
      ∀ owed ∈ ((interpOf root table).dueResumes state).1, CodeAt root owed.code ∧ TerminalReply owed.code := by
  refine ⟨owned, ?_⟩
  intro owed member
  obtain ⟨completion, _, eq⟩ := List.mem_map.mp member
  rw [← eq]
  exact owed_completion_at root completion

/-- Draining owned completions retains the posted tasks and returned resumes. -/
theorem drain_at (root : NativeEff) (m : NativeMachine) (due : List (Owed NCode))
    (owned : ConfigurationAt root m) (saved : ∀ owed ∈ due, CodeAt root owed.code ∧ TerminalReply owed.code) :
    ConfigurationAt root (drainOwed m due).1 ∧ CommandsAt root (drainOwed m due).2 := by
  induction due generalizing m with
  | nil => exact ⟨owned, by intro c member; cases member⟩
  | cons first rest ih =>
    have code := saved first (.head _)
    have tail : ∀ owed ∈ rest, CodeAt root owed.code ∧ TerminalReply owed.code := fun owed member => saved owed (.tail _ member)
    simp only [drainOwed]
    cases mode : first.mode with
    | now =>
      have retained := ih m owned tail
      refine ⟨retained.1, ?_⟩
      intro c member
      rcases List.mem_cons.mp member with same | later
      · rw [same]; exact code
      · exact retained.2 c later
    | scheduled owner priority =>
      exact ih _ (configuration_post_at root m owner priority _ owned code) tail

/-- An actual published exit removes pending callbacks while retaining its source stack. -/
theorem publish_at (root : NativeEff) (fiber : SourceFiber) (exit : ExitV) (held : FiberAt root fiber) :
    FiberAt root (fiber.publish exit) :=
  ⟨held.frame, (by intro p member; cases member), held.dispatcher⟩

/-- Exit completion clears the saved stack without introducing code. -/
theorem cleared_at (root : NativeEff) (table : RowTable) (fiber : SourceFiber) (held : FiberAt root fiber) :
    FiberAt root (fiber.cleared (interpOf root table)) :=
  ⟨⟨held.frame.1, by intro code member; cases member⟩, held.pending, held.dispatcher⟩

/-- The actual exit path retains middleware cleanup and every observer command. -/
theorem exit_fiber_at (root : NativeEff) (table : RowTable) (m : NativeMachine) (fiber : SourceFiber)
    (exit : ExitV) (owned : ConfigurationAt root m) (held : FiberAt root fiber) :
    ConfigurationAt root (exitFiber (interpOf root table) m fiber exit).1 ∧
      CommandsAt root (exitFiber (interpOf root table) m fiber exit).2 := by
  unfold exitFiber
  split
  · exact ⟨configuration_emit root _ _ (configuration_update root m _ owned
      ⟨⟨success_restore_at root _ exit trivial, held.frame.2⟩, held.pending, held.dispatcher⟩),
      by intro c member; rw [List.mem_singleton.mp member]; trivial⟩
  · have published := publish_at root fiber exit held
    have stored := configuration_emit root _ [RunEvent.exited fiber.id exit] (configuration_update root m _ owned published)
    unfold exitFiber.exitStore
    dsimp only
    split
    · exact ⟨configuration_update root _ _ stored (cleared_at root table _ published),
        by intro c member; rw [List.mem_singleton.mp member]; trivial⟩
    · refine ⟨stored, ?_⟩
      intro c member
      rcases List.mem_append.mp member with observer | administrative
      · obtain ⟨o, _, eq⟩ := List.mem_map.mp observer
        rw [← eq]; trivial
      · rcases List.mem_cons.mp administrative with same | later
        · rw [same]; trivial
        · rw [List.mem_singleton.mp later]; trivial

/-- Interrupting a target list changes only administrative fiber fields. -/
theorem interrupt_each_at (root : NativeEff) (table : RowTable) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (acc : NativeMachine × List SourceCommand)
    (owned : ConfigurationAt root acc.1) (pending : CommandsAt root acc.2) :
    ConfigurationAt root (interruptEach (interpOf root table) who extra targets acc).1 ∧
      CommandsAt root (interruptEach (interpOf root table) who extra targets acc).2 := by
  induction targets generalizing acc with
  | nil => exact ⟨owned, pending⟩
  | cons target rest ih =>
    unfold interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc owned pending
    · rename_i fiber found
      have held := configuration_fiber root acc.1 target fiber owned found
      have changed := interrupt_record_at root [] table (some who) extra fiber held
      apply ih
      · exact configuration_emit root _ _ (configuration_update root acc.1 _ owned changed)
      · apply commands_append root _ _ pending
        split
        · intro c member; rw [List.mem_singleton.mp member]; trivial
        · intro c member; cases member

/-- Updating countdown bookkeeping retains its stored continuation name. -/
theorem pending_map_at (root : NativeEff) (fiber : SourceFiber)
    (edit : Pending EffName Val Err Defect FiberId Ann → Pending EffName Val Err Defect FiberId Ann)
    (held : FiberAt root fiber) (kept : ∀ p, (edit p).resumeWith = p.resumeWith) :
    FiberAt root {fiber with pending := fiber.pending.map edit} := by
  refine ⟨held.frame, ?_, held.dispatcher⟩
  intro p member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq, kept]
  exact held.pending old present

/-- Native finalizer removal retains the surviving source captures. -/
theorem drop_at (root : NativeEff) (table : RowTable) (scope key : Nat) (state next : Stores)
    (owned : ScopesAt root state.scopes)
    (found : (interpOf root table).dropFinalizer scope key state = some next) : ScopesAt root next.scopes := by
  simp only [interpOf] at found
  split at found
  · cases found
  · cases found
    exact scope_remove_at root state.scopes scope key owned

set_option maxHeartbeats 1200000 in
/-- Every actual observer callback retains source programs returned as resumes. -/
theorem observer_at (root : NativeEff) (table : RowTable) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List SourceCommand) (observer : Observer)
    (owned : ConfigurationAt root acc.1) (pending : CommandsAt root acc.2) :
    ConfigurationAt root (fireObserver (interpOf root table) id exit acc observer).1 ∧
      CommandsAt root (fireObserver (interpOf root table) id exit acc observer).2 := by
  let m := acc.1.emit [RunEvent.observerFired id observer]
  have base : ConfigurationAt root m := configuration_emit root acc.1 _ owned
  have looked (target : FiberId) (fiber : SourceFiber) (found : m.fiber? target = some fiber) : FiberAt root fiber :=
    configuration_fiber root m target fiber base found
  have updated (fiber : SourceFiber) (held : FiberAt root fiber) : ConfigurationAt root (m.update fiber) :=
    configuration_update root m fiber base held
  have modified (target : FiberId) (edit : SourceFiber → SourceFiber)
      (kept : ∀ fiber, FiberAt root fiber → FiberAt root (edit fiber)) : ConfigurationAt root (m.modify target edit) :=
    configuration_modify root m target edit base kept
  have interrupted (waiter : FiberId) (remaining : List FiberId) :
      ConfigurationAt root (interruptEach (interpOf root table) waiter ((interpOf root table).stackAnnotations waiter) remaining (m, [])).1 ∧
      CommandsAt root (interruptEach (interpOf root table) waiter ((interpOf root table).stackAnnotations waiter) remaining (m, [])).2 :=
    interrupt_each_at root table waiter _ remaining (m, []) base (by intro c member; cases member)
  have saved (waiter : FiberId) (fiber : SourceFiber) (token : Nat) (p : Pending EffName Val Err Defect FiberId Ann)
      (found : m.fiber? waiter = some fiber) (selected : fiber.pending.find? (fun p => p.token = token) = some p) :
      ResumeAt root p.resumeWith :=
    (looked waiter fiber found).pending p (List.mem_of_find?_eq_some selected)
  have first_failed (waiter : FiberId) (remaining : List FiberId) (failure : Bool)
      (next : NativeMachine) (nested : List SourceCommand)
      (found : (if failure then interruptEach (interpOf root table) waiter
        ((interpOf root table).stackAnnotations waiter) remaining (m, []) else (m, [])) = (next, nested)) :
      ConfigurationAt root next ∧ CommandsAt root nested := by
    split at found
    · have h := interrupted waiter remaining
      rw [found] at h
      exact h
    · cases found
      exact ⟨base, by intro c member; cases member⟩
  fun_cases fireObserver (interpOf root table) id exit acc observer
  case case1 waiter token mode emitted =>
    exact ⟨base, commands_append root _ _ pending (by intro c member; rw [List.mem_singleton.mp member]; exact ⟨exit_value_at root [] table exit mode, exit_value_reply root [] table exit mode⟩)⟩
  case case2 parent emitted =>
    exact ⟨configuration_modify root m parent _ base (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩), pending⟩
  case case3 scope key emitted found => exact ⟨configuration_halt root m _ base, pending⟩
  case case4 scope key state emitted found =>
    exact ⟨⟨base.fibers, base.races, drop_at root table scope key m.state state base.scopes found⟩, pending⟩
  case case5 waiter token emitted found => exact ⟨base, pending⟩
  case case6 waiter token fiber selected emitted found => exact ⟨base, pending⟩
  case case7 waiter token fiber p selected collected failure next nested exits walk changed emitted found counted =>
    have moved := first_failed waiter p.remaining failure next nested counted
    have held := looked waiter fiber found
    have resumed := saved waiter fiber token p found selected
    have changedAt : FiberAt root changed := by
      apply pending_map_at root fiber _ held
      intro p
      split <;> rfl
    exact ⟨configuration_update root next changed moved.1 changedAt,
      commands_append root _ _ (commands_append root _ _ pending moved.2)
        (by intro c member; rw [List.mem_singleton.mp member]; exact ⟨countdown_program_at root [] table p.resumeWith exits resumed,
          countdown_program_reply root [] table p.resumeWith exits resumed⟩)⟩
  case case8 waiter token fiber p selected collected failure next nested exits target rest walk observing changed emitted found counted =>
    have moved := first_failed waiter p.remaining failure next nested counted
    have held := looked waiter fiber found
    have observingAt : ConfigurationAt root observing :=
      configuration_modify root next target _ moved.1 (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩)
    have changedAt : FiberAt root changed := by
      apply pending_map_at root fiber _ held
      intro p
      split <;> rfl
    exact ⟨configuration_update root observing changed observingAt changedAt,
      commands_append root _ _ pending moved.2⟩
  case case9 race emitted found => exact ⟨base, pending⟩
  case case10 race previous changed state accepted unsettled selected emitted found updated settling finished =>
    have raceAt := configuration_race root m race previous base found
    have finishedAt : ConfigurationAt root finished :=
      configuration_emit root _ _ (configuration_race_update root _ _
        (configuration_race_update root m changed base raceAt) raceAt)
    refine ⟨finishedAt, commands_append root _ _ pending ?_⟩
    split
    · intro c member; cases member
    · intro c member; rw [List.mem_singleton.mp member]
      exact ⟨race_settle_at root table race state.cleanupNeeded accepted raceAt.2,
        race_settle_reply root table race state.cleanupNeeded accepted⟩
  case case11 race previous changed state stopped emitted found updated =>
    exact ⟨configuration_race_update root m changed base (configuration_race root m race previous base found), pending⟩
  case case12 key emitted => exact ⟨configuration_emit root m _ base, pending⟩

/-- The native await program embeds a represented park or an observed exit. -/
theorem await_code_at (root : NativeEff) (table : RowTable) (m : NativeMachine) (kind : ParkKind) :
    CodeAt root (awaitCode (interpOf root table) m kind) := by
  cases kind
  case join target mode =>
    unfold awaitCode
    dsimp only
    split
    · exact exit_value_at root [] table _ mode
    · trivial
  all_goals trivial

/-- A race entrant is spawned from the actual owned head program. -/
theorem launch_at (root : NativeEff) (table : RowTable) (race : Nat) (m : NativeMachine)
    (host : SourceFiber) (program : NCode) (site : List Nat)
    (owned : ConfigurationAt root m) (source : CodeAt root program) :
    ConfigurationAt root (launchEntrant (interpOf root table) race m host program site).1 := by
  unfold launchEntrant
  exact configuration_spawn root [] table m host program ⟨true, true, .interruptible⟩ site owned source

set_option maxHeartbeats 1600000 in
/-- Every actual native command retains configuration ownership and pending resume code. -/
theorem command_at (root : NativeEff) (fragment : Fragment root) (table : RowTable)
    (m : NativeMachine) (command : SourceCommand) (rest : List SourceCommand)
    (owned : ConfigurationAt root m) (pending : CommandsAt root (command :: rest)) :
    ConfigurationAt root (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1 ∧
      CommandsAt root (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).2 := by
  have suffix : CommandsAt root rest := fun c member => pending c (.tail _ member)
  have head := pending command (.head _)
  have looked (id : FiberId) (fiber : SourceFiber) (found : m.fiber? id = some fiber) : FiberAt root fiber :=
    configuration_fiber root m id fiber owned found
  have races (id : Nat) (race : SourceRace) (found : m.race? id = some race) : RaceAt root race :=
    configuration_race root m id race owned found
  have loops (id : FiberId) (fiber : SourceFiber) (yielding : Bool) (found : m.fiber? id = some fiber) :
      ConfigurationAt root (settle id rest (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding)).1 ∧
        CommandsAt root (settle id rest (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding)).2 :=
    settle_at root id rest _ (iteration_at root fragment table m fiber yielding owned (looked id fiber found)) suffix
  have delivers (id : FiberId) (fiber : SourceFiber) (yielding : Bool) (found : m.fiber? id = some fiber) :
      ConfigurationAt root (settle id rest (evaluateNative root m fiber yielding table)).1 ∧
        CommandsAt root (settle id rest (evaluateNative root m fiber yielding table)).2 :=
    settle_at root id rest _ (native_at root fragment table m fiber yielding owned (looked id fiber found)) suffix
  have observes (id : FiberId) (exit : ExitV) (observer : Observer) :
      ConfigurationAt root (fireObserver (interpOf root table) id exit (m, []) observer).1 ∧
        CommandsAt root (fireObserver (interpOf root table) id exit (m, []) observer).2 :=
    observer_at root table id exit (m, []) observer owned (by intro c member; cases member)
  have due := due_at root table m.state owned.scopes
  have drained := drain_at root {m with state := ((interpOf root table).dueResumes m.state).2}
    ((interpOf root table).dueResumes m.state).1 ⟨owned.fibers, owned.races, due.1⟩ due.2
  fun_cases driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest
  case case3 id fiber found blocked changed =>
    have held := looked id fiber found
    exact ⟨configuration_emit root _ _ (configuration_update root m changed owned ⟨held.frame, held.pending, held.dispatcher⟩),
      by intro c member; rcases List.mem_cons.mp member with same | later
         · rw [same]; trivial
         · exact suffix c later⟩
  case case5 id yielding fiber found => exact loops id fiber yielding found
  case case7 id yielding fiber found => exact delivers id fiber yielding found
  case case9 id answer fiber found token parked changed =>
    have held := looked id fiber found
    have changedAt : FiberAt root changed := by
      refine ⟨⟨head.1, held.frame.2⟩, ?_, held.dispatcher⟩
      intro p member
      exact held.pending p ((List.mem_filter.mp member).1)
    exact ⟨configuration_emit root _ _ (configuration_update root m changed owned changedAt),
      by intro c member; rcases List.mem_cons.mp member with same | later
         · rw [same]; trivial
         · exact suffix c later⟩
  case case16 id race raceFound program more programs blocked host hostFound spawned child spawnedEq updated =>
    have raceAt := races id race raceFound
    have programAt := raceAt.1 program (by rw [programs]; exact .head _)
    have spawnedAt := launch_at root table id m host program (race.nextSite.getD []) owned programAt
    rw [spawnedEq] at spawnedAt
    have moreAt : RaceAt root {race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1])} := by
      refine ⟨?_, raceAt.2⟩
      intro code member
      exact raceAt.1 code (by rw [programs]; exact .tail _ member)
    exact ⟨configuration_emit root _ _ (configuration_race_update root spawned _ spawnedAt moreAt),
      by aesop (add norm simp [CommandsAt, CommandAt, List.mem_cons])⟩
  case case17 id child race fiber fiberFound raceFound updated exit exited changed nested observed =>
    have updatedAt : ConfigurationAt root updated := configuration_race_update root m _ owned (races id race raceFound)
    have kept := observer_at root table child exit (updated, []) (.raceCallback id) updatedAt (by intro c member; cases member)
    rw [observed] at kept
    exact ⟨kept.1, commands_append root _ _ kept.2 suffix⟩
  case case18 id child race fiber fiberFound raceFound updated noExit =>
    have updatedAt : ConfigurationAt root updated := configuration_race_update root m _ owned (races id race raceFound)
    exact ⟨configuration_modify root updated child _ updatedAt (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩), suffix⟩
  case case21 id yielding race raceFound updated missing =>
    exact ⟨configuration_race_update root m _ owned (races id race raceFound), suffix⟩
  case case22 id yielding race raceFound updated fiber found exit accepted code changed =>
    have updatedAt : ConfigurationAt root updated := configuration_race_update root m _ owned (races id race raceFound)
    have held := configuration_fiber root updated race.host fiber updatedAt found
    apply settle_at root _ rest _ _ suffix
    exact ⟨updatedAt, fiber_current_at root fiber code held (race_settle_at root table id _ exit (races id race raceFound).2), by intro c member; cases member⟩
  case case23 id yielding race raceFound updated fiber found missing name before parked =>
    have updatedAt : ConfigurationAt root updated := configuration_race_update root m _ owned (races id race raceFound)
    have held := configuration_fiber root updated race.host fiber updatedAt found
    have canceled : FiberAt root before := fiber_cancel_at root fiber name held trivial
    apply settle_at root _ rest _ _ suffix
    exact ⟨configuration_emit root updated _ updatedAt, fiber_park_at root before _ canceled trivial, by intro c member; cases member⟩
  case case25 target who extra fiber found changed immediate recorded =>
    have held := interrupt_record_at root [] table who extra fiber (looked target fiber found)
    change FiberAt root (interruptRecord (interpOf root table) who extra fiber).1 at held
    rw [recorded] at held
    refine ⟨configuration_emit root _ _ (configuration_update root m changed owned held), ?_⟩
    apply commands_append root _ _ _ suffix
    split
    · intro c member; rw [List.mem_singleton.mp member]; trivial
    · intro c member; cases member
  case case27 host yielding kind fiber found changed =>
    have held := looked host fiber found
    apply settle_at root _ rest _ _ suffix
    exact ⟨owned, fiber_current_at root fiber _ held
      (success_restore_at root _ _ (await_code_at root table m kind)), by intro c member; cases member⟩
  case case34 parent child fiber found live =>
    exact ⟨configuration_modify root _ child _
      (configuration_modify root m parent _ owned (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩))
      (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩), suffix⟩
  case case35 id exit observer changed nested observed =>
    have kept := observes id exit observer
    rw [observed] at kept
    exact ⟨kept.1, commands_append root _ _ kept.2 suffix⟩
  case case37 id fiber found => exact ⟨configuration_update root m _ owned (cleared_at root table fiber (looked id fiber found)), suffix⟩
  case case39 host yielding children fiber found frame changed =>
    have held := looked host fiber found
    have changedAt : FiberAt root changed := by
      refine ⟨⟨trivial, ?_⟩, held.pending, held.dispatcher⟩
      intro c member
      rcases List.mem_cons.mp member with same | later
      · rw [same]; trivial
      · exact held.frame.2 c later
    apply settle_at root _ rest _ _ suffix
    exact ⟨owned, changedAt, by intro c member; cases member⟩
  case case40 mode scope target who extra changed nested linked =>
    have kept := link_at root [] table m mode scope target who extra owned
    change ConfigurationAt root (linkScope (interpOf root table) m mode scope target who extra).1 ∧ CommandsAt root (linkScope (interpOf root table) m mode scope target who extra).2 at kept
    rw [linked] at kept
    exact ⟨kept.1, commands_append root _ _ kept.2 suffix⟩
  case case42 id exit fiber found changed nested finished =>
    have held := looked id fiber found
    have stopped : FiberAt root {fiber with running := false} := ⟨held.frame, held.pending, held.dispatcher⟩
    have kept := exit_fiber_at root table m _ exit owned stopped
    rw [finished] at kept
    exact ⟨kept.1, commands_append root _ _ kept.2 suffix⟩
  case case43 completions state found drainedPair =>
    rw [found] at due
    have kept := drain_at root {m with state} completions ⟨owned.fibers, owned.races, due.1⟩ due.2
    exact ⟨kept.1, commands_append root _ _ kept.2 suffix⟩
  case case44 list phase =>
    refine ⟨⟨owned.fibers, owned.races, ?_⟩, suffix⟩
    change ScopesAt root (Stores.wakeList list phase m.state).scopes
    unfold Stores.wakeList
    split <;> exact owned.scopes
  all_goals aesop (add norm simp [CommandsAt, CommandAt, List.mem_cons])

end Effect4.Program.SourceScope
