import Effect4.Laws.Program.NativeExecutor
import Effect4.Laws.Program.CodeClosure.Configuration
import Effect4.Laws.Machine.Lift

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual code-location transport serves lexical ownership and full finalizer source funding.
Consumer: both configuration instances and their existing decision lifts.
The existing command census consumes supplied local evaluation and administrative facts.
The local facts remain premises; this theorem alone establishes no history funding or release custody.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Configuration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

abbrev EvaluationAt (model : Model) (root : NativeEff) (it : SourceIteration) :=
  SourceScope.EvaluationAt root it (ConfigurationAt model) (FiberAt model) (CommandsAt model)

/-- Actual command producers supply exactly the code and capture locations they change. -/
structure CommandFacts (model : Model) (root : NativeEff) (table : RowTable) : Prop where
  iteration : ∀ m fiber yielding, ConfigurationAt model m → FiberAt model fiber →
    EvaluationAt model root (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding)
  native : ∀ m fiber yielding, ConfigurationAt model m → FiberAt model fiber →
    EvaluationAt model root (evaluateNative root m fiber yielding table)
  settle : ∀ id rest it, EvaluationAt model root it → CommandsAt model rest →
    ConfigurationAt model (Machine.settle id rest it).1 ∧ CommandsAt model (Machine.settle id rest it).2
  observer : ∀ id exit acc observer, ConfigurationAt model acc.1 → CommandsAt model acc.2 →
    ConfigurationAt model (fireObserver (interpOf root table) id exit acc observer).1 ∧
      CommandsAt model (fireObserver (interpOf root table) id exit acc observer).2
  due : ∀ state, model.scopes state.scopes →
    model.scopes ((interpOf root table).dueResumes state).2.scopes ∧
      ∀ owed ∈ ((interpOf root table).dueResumes state).1, model.code owed.code ∧ TerminalReply owed.code
  drain : ∀ m due, ConfigurationAt model m → (∀ owed ∈ due, model.code owed.code ∧ TerminalReply owed.code) →
    ConfigurationAt model (drainOwed m due).1 ∧ CommandsAt model (drainOwed m due).2
  raceSettle : ∀ race cleanup exit, model.races → model.code ((interpOf root table).raceSettle race cleanup exit)
  cancel : ∀ race owner token, model.code (.asyncFinalizer
    ((interpOf root table).cancelName ((interpOf root table).raceCancelName race) owner token))
  interruption : ∀ cause fiber, FiberAt model fiber → FiberAt model (interruptWithCause cause fiber).1
  awaitRestore : ∀ (m : NativeMachine) kind, model.code (asVoidCode (interpOf root table) (awaitCode (interpOf root table) m kind))
  park : ∀ kind, model.code ((interpOf root table).parkCode kind)
  closeDone : model.code (.iterator (interpOf root table).closeDoneName (interpOf root table).voidValue)
  link : ∀ m mode scope target who extra, ConfigurationAt model m →
    ConfigurationAt model (linkScope (interpOf root table) m mode scope target who extra).1 ∧
      CommandsAt model (linkScope (interpOf root table) m mode scope target who extra).2
  exit : ∀ m fiber exit, ConfigurationAt model m → FiberAt model fiber →
    ConfigurationAt model (exitFiber (interpOf root table) m fiber exit).1 ∧
      CommandsAt model (exitFiber (interpOf root table) m fiber exit).2

/-- The existing entrant spawn introduces only its supplied program. -/
theorem launch_at (model : Model) (root : NativeEff) (table : RowTable) (race : Nat)
    (m : NativeMachine) (host : SourceFiber) (program : NCode) (site : List Nat)
    (owned : ConfigurationAt model m) (source : model.code program) :
    ConfigurationAt model (launchEntrant (interpOf root table) race m host program site).1 := by
  unfold launchEntrant
  exact configuration_spawn model root [] table m host program ⟨true, true, .interruptible⟩ site owned source

/-- Clearing retains the current code and empties its saved suffix. -/
theorem cleared_at (model : Model) (root : NativeEff) (table : RowTable)
    (fiber : SourceFiber) (held : FiberAt model fiber) :
    FiberAt model (fiber.cleared (interpOf root table)) :=
  ⟨⟨held.frame.1, by intro code member; cases member⟩, held.pending, held.dispatcher⟩

set_option maxHeartbeats 1600000 in
/-- The single command census retains supplied annotations at every actual code location. -/
theorem command_at (model : Model) (root : NativeEff) (table : RowTable)
    (facts : CommandFacts model root table)
    (m : NativeMachine) (command : SourceCommand) (rest : List SourceCommand)
    (owned : ConfigurationAt model m) (pending : CommandsAt model (command :: rest)) :
    ConfigurationAt model (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).1 ∧
      CommandsAt model (driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest).2 := by
  have suffix : CommandsAt model rest := fun c member => pending c (.tail _ member)
  have head := pending command (.head _)
  have looked (id : FiberId) (fiber : SourceFiber) (found : m.fiber? id = some fiber) : FiberAt model fiber :=
    configuration_fiber model m id fiber owned found
  have races (id : Nat) (race : SourceRace) (found : m.race? id = some race) : RaceAt model race :=
    configuration_race model m id race owned found
  have loops (id : FiberId) (fiber : SourceFiber) (yielding : Bool) (found : m.fiber? id = some fiber) :
      ConfigurationAt model (settle id rest (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding)).1 ∧
        CommandsAt model (settle id rest (iteration (evaluator := evaluatorFor root table) (interpOf root table) m fiber yielding)).2 :=
    facts.settle id rest _ (facts.iteration m fiber yielding owned (looked id fiber found)) suffix
  have delivers (id : FiberId) (fiber : SourceFiber) (yielding : Bool) (found : m.fiber? id = some fiber) :
      ConfigurationAt model (settle id rest (evaluateNative root m fiber yielding table)).1 ∧
        CommandsAt model (settle id rest (evaluateNative root m fiber yielding table)).2 :=
    facts.settle id rest _ (facts.native m fiber yielding owned (looked id fiber found)) suffix
  have observes (id : FiberId) (exit : ExitV) (observer : Observer) :
      ConfigurationAt model (fireObserver (interpOf root table) id exit (m, []) observer).1 ∧
        CommandsAt model (fireObserver (interpOf root table) id exit (m, []) observer).2 :=
    facts.observer id exit (m, []) observer owned (by intro c member; cases member)
  have due := facts.due m.state owned.scopes
  have drained := facts.drain {m with state := ((interpOf root table).dueResumes m.state).2}
    ((interpOf root table).dueResumes m.state).1 ⟨owned.fibers, owned.races, due.1⟩ due.2
  fun_cases driveStep (evaluator := evaluatorFor root table) (interpOf root table) m command rest
  case case3 id fiber found blocked changed =>
    have held := looked id fiber found
    exact ⟨configuration_emit model _ _ (configuration_update model m changed owned ⟨held.frame, held.pending, held.dispatcher⟩),
      by intro c member; rcases List.mem_cons.mp member with same | later
         · rw [same]; trivial
         · exact suffix c later⟩
  case case5 id yielding fiber found => exact loops id fiber yielding found
  case case7 id yielding fiber found => exact delivers id fiber yielding found
  case case9 id answer fiber found token parked changed =>
    have held := looked id fiber found
    have changedAt : FiberAt model changed := by
      refine ⟨⟨head.1, held.frame.2⟩, ?_, held.dispatcher⟩
      intro p member
      exact held.pending p ((List.mem_filter.mp member).1)
    exact ⟨configuration_emit model _ _ (configuration_update model m changed owned changedAt),
      by intro c member; rcases List.mem_cons.mp member with same | later
         · rw [same]; trivial
         · exact suffix c later⟩
  case case16 id race raceFound program more programs blocked host hostFound spawned child spawnedEq updated =>
    have raceAt := races id race raceFound
    have programAt := raceAt.1 program (by rw [programs]; exact .head _)
    have spawnedAt := launch_at model root table id m host program (race.nextSite.getD []) owned programAt
    rw [spawnedEq] at spawnedAt
    have moreAt : RaceAt model {race with programs := more, nextSite := race.nextSite.map (fun site => site ++ [1])} := by
      refine ⟨?_, raceAt.2⟩
      intro code member
      exact raceAt.1 code (by rw [programs]; exact .tail _ member)
    exact ⟨configuration_emit model _ _ (configuration_race_update model spawned _ spawnedAt moreAt),
      by aesop (add norm simp [CommandsAt, CommandAt, List.mem_cons])⟩
  case case17 id child race fiber fiberFound raceFound updated exit exited changed nested observed =>
    have updatedAt : ConfigurationAt model updated := configuration_race_update model m _ owned (races id race raceFound)
    have kept := facts.observer child exit (updated, []) (.raceCallback id) updatedAt (by intro c member; cases member)
    rw [observed] at kept
    exact ⟨kept.1, commands_append model _ _ kept.2 suffix⟩
  case case18 id child race fiber fiberFound raceFound updated noExit =>
    have updatedAt : ConfigurationAt model updated := configuration_race_update model m _ owned (races id race raceFound)
    exact ⟨configuration_modify model updated child _ updatedAt (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩), suffix⟩
  case case21 id yielding race raceFound updated missing =>
    exact ⟨configuration_race_update model m _ owned (races id race raceFound), suffix⟩
  case case22 id yielding race raceFound updated fiber found exit accepted code changed =>
    have updatedAt : ConfigurationAt model updated := configuration_race_update model m _ owned (races id race raceFound)
    have held := configuration_fiber model updated race.host fiber updatedAt found
    apply facts.settle _ rest _ _ suffix
    exact ⟨updatedAt, fiber_current_at model fiber code held (facts.raceSettle id _ exit (races id race raceFound).2), by intro c member; cases member⟩
  case case23 id yielding race raceFound updated fiber found missing name before parked =>
    have updatedAt : ConfigurationAt model updated := configuration_race_update model m _ owned (races id race raceFound)
    have held := configuration_fiber model updated race.host fiber updatedAt found
    have canceled : FiberAt model before := fiber_cancel_at model fiber name held (facts.cancel id fiber.id race.token)
    apply facts.settle _ rest _ _ suffix
    exact ⟨configuration_emit model updated _ updatedAt, fiber_park_at model before _ canceled trivial, by intro c member; cases member⟩
  case case25 target who extra fiber found changed immediate recorded =>
    have held := (facts.interruption (interruptCause (interpOf root table) who extra fiber.id) fiber (looked target fiber found))
    change FiberAt model (interruptRecord (interpOf root table) who extra fiber).1 at held
    rw [recorded] at held
    refine ⟨configuration_emit model _ _ (configuration_update model m changed owned held), ?_⟩
    apply commands_append model _ _ _ suffix
    split
    · intro c member; rw [List.mem_singleton.mp member]; trivial
    · intro c member; cases member
  case case27 host yielding kind fiber found changed =>
    have held := looked host fiber found
    apply facts.settle _ rest _ _ suffix
    exact ⟨owned, fiber_current_at model fiber _ held
      (facts.awaitRestore m kind), by intro c member; cases member⟩
  case case34 parent child fiber found live =>
    exact ⟨configuration_modify model _ child _
      (configuration_modify model m parent _ owned (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩))
      (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩), suffix⟩
  case case35 id exit observer changed nested observed =>
    have kept := observes id exit observer
    rw [observed] at kept
    exact ⟨kept.1, commands_append model _ _ kept.2 suffix⟩
  case case37 id fiber found => exact ⟨configuration_update model m _ owned (cleared_at model root table fiber (looked id fiber found)), suffix⟩
  case case39 host yielding children fiber found frame changed =>
    have held := looked host fiber found
    have changedAt : FiberAt model changed := by
      refine ⟨⟨facts.park _, ?_⟩, held.pending, held.dispatcher⟩
      intro c member
      rcases List.mem_cons.mp member with same | later
      · rw [same]; exact facts.closeDone
      · exact held.frame.2 c later
    apply facts.settle _ rest _ _ suffix
    exact ⟨owned, changedAt, by intro c member; cases member⟩
  case case40 mode scope target who extra changed nested linked =>
    have kept := facts.link m mode scope target who extra owned
    change ConfigurationAt model (linkScope (interpOf root table) m mode scope target who extra).1 ∧ CommandsAt model (linkScope (interpOf root table) m mode scope target who extra).2 at kept
    rw [linked] at kept
    exact ⟨kept.1, commands_append model _ _ kept.2 suffix⟩
  case case42 id exit fiber found changed nested finished =>
    have held := looked id fiber found
    have stopped : FiberAt model {fiber with running := false} := ⟨held.frame, held.pending, held.dispatcher⟩
    have kept := facts.exit m _ exit owned stopped
    rw [finished] at kept
    exact ⟨kept.1, commands_append model _ _ kept.2 suffix⟩
  case case43 completions state found drainedPair =>
    rw [found] at due
    have kept := facts.drain {m with state} completions ⟨owned.fibers, owned.races, due.1⟩ due.2
    exact ⟨kept.1, commands_append model _ _ kept.2 suffix⟩
  case case44 list phase =>
    refine ⟨⟨owned.fibers, owned.races, ?_⟩, suffix⟩
    change model.scopes (Stores.wakeList list phase m.state).scopes
    unfold Stores.wakeList
    split <;> exact owned.scopes
  all_goals aesop (add norm simp [CommandsAt, CommandAt, List.mem_cons])

end Effect4.Program.CodeClosure.Configuration
