import Effect4.Laws.Program.CodeClosure.ConfigurationCommands

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: existing source administration serves both configuration instances.
Consumer: their actual command and decision transports.
Local code introductions and scope changes remain explicit premises.
These proofs move the existing settlement, drain, exit, and observer case analyses.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Configuration
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.SourceScope

/-- Observer callbacks introduce only their supplied terminal programs and scope removal. -/
structure ObserverFacts (model : Model) (root : NativeEff) (table : RowTable) : Prop where
  failure : ∀ cause, model.code (.failure cause)
  exitValue : ∀ exit mode, model.code ((interpOf root table).exitValue exit mode)
  countdown : ∀ resume exits, ResumeAt model resume →
    model.code (countdownPark.resumePrim (interpOf root table) resume exits)
  raceSettle : ∀ race cleanup exit, model.races → model.code ((interpOf root table).raceSettle race cleanup exit)
  drop : ∀ scope key (state next : Stores), model.scopes state.scopes →
    (interpOf root table).dropFinalizer scope key state = some next → model.scopes next.scopes

/-- Shared actual settleOutcome at transport for both code-location instances. -/
theorem settleOutcome_at (model : Model) (root : NativeEff) (id : FiberId) (rest : List SourceCommand) (it : SourceIteration)
    (owned : EvaluationAt model root it) (pending : CommandsAt model rest) :
    ConfigurationAt model (settleOutcome id rest it).1 ∧ CommandsAt model (settleOutcome id rest it).2 := by
  have stopped : FiberAt model {it.fiber with running := false} :=
    ⟨owned.fiber.frame, owned.fiber.pending, owned.fiber.dispatcher⟩
  have cleared : FiberAt model {it.fiber with parked := .notParked, pending := []} :=
    ⟨owned.fiber.frame, (by intro p member; cases member), owned.fiber.dispatcher⟩
  have installed := configuration_update model it.machine it.fiber owned.machine owned.fiber
  have halted := configuration_update model it.machine _ owned.machine stopped
  have resumed := configuration_update model it.machine _ owned.machine cleared
  have suffix (c : SourceCommand) (admin : CommandAt model c) :
      CommandsAt model (it.nested ++ [c] ++ rest) :=
    commands_append model _ rest
      (commands_append model it.nested [c] owned.commands (by intro x member; rw [List.mem_singleton.mp member]; exact admin)) pending
  unfold settleOutcome
  split
  · exact ⟨installed, suffix _ trivial⟩
  · exact ⟨installed, suffix _ trivial⟩
  · split
    · exact ⟨resumed, suffix _ trivial⟩
    · exact ⟨halted, commands_append model _ _ owned.commands pending⟩
  · exact ⟨installed, commands_append model _ _ owned.commands pending⟩
  · exact ⟨installed, suffix _ trivial⟩
  · exact ⟨configuration_halt model _ _ halted, by intro c member; cases member⟩


/-- Shared actual settle at transport for both code-location instances. -/
theorem settle_at (model : Model) (root : NativeEff) (failure : ∀ cause, model.code (.failure cause)) (id : FiberId) (rest : List SourceCommand) (it : SourceIteration)
    (owned : EvaluationAt model root it) (pending : CommandsAt model rest) :
    ConfigurationAt model (settle id rest it).1 ∧ CommandsAt model (settle id rest it).2 := by
  unfold settle
  split
  · exact settleOutcome_at model root id rest it owned pending
  · have changed := fiber_edits_at model failure it.edits _
      (configuration_update model it.machine it.fiber owned.machine owned.fiber)
    dsimp only
    split
    · exact ⟨configuration_halt model _ _ changed.1, by intro command member; cases member⟩
    · rename_i owner found
      exact settleOutcome_at model root id rest _
        ⟨changed.1, configuration_fiber model _ _ owner changed.1 found,
          commands_append model _ _ changed.2 owned.commands⟩ pending


/-- Shared actual drain at transport for both code-location instances. -/
theorem drain_at (model : Model) (m : NativeMachine) (due : List (Owed NCode))
    (owned : ConfigurationAt model m) (saved : ∀ owed ∈ due, model.code owed.code ∧ TerminalReply owed.code) :
    ConfigurationAt model (drainOwed m due).1 ∧ CommandsAt model (drainOwed m due).2 := by
  induction due generalizing m with
  | nil => exact ⟨owned, by intro c member; cases member⟩
  | cons first rest ih =>
    have code := saved first (.head _)
    have tail : ∀ owed ∈ rest, model.code owed.code ∧ TerminalReply owed.code := fun owed member => saved owed (.tail _ member)
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
      exact ih _ (configuration_post_at model m owner priority _ owned code) tail


/-- Shared actual publish at transport for both code-location instances. -/
theorem publish_at (model : Model) (fiber : SourceFiber) (exit : ExitV) (held : FiberAt model fiber) :
    FiberAt model (fiber.publish exit) :=
  ⟨held.frame, (by intro p member; cases member), held.dispatcher⟩


/-- Shared actual exit fiber at transport for both code-location instances. -/
theorem exit_fiber_at (model : Model) (root : NativeEff) (table : RowTable)
    (children : ∀ (fiber : SourceFiber) exit, model.code
      (.onSuccess ((interpOf root table).interruptAllCode fiber.children) ((interpOf root table).restoreName exit))) (m : NativeMachine) (fiber : SourceFiber)
    (exit : ExitV) (owned : ConfigurationAt model m) (held : FiberAt model fiber) :
    ConfigurationAt model (exitFiber (interpOf root table) m fiber exit).1 ∧
      CommandsAt model (exitFiber (interpOf root table) m fiber exit).2 := by
  unfold exitFiber
  split
  · exact ⟨configuration_emit model _ _ (configuration_update model m _ owned
      ⟨⟨children fiber exit, held.frame.2⟩, held.pending, held.dispatcher⟩),
      by intro c member; rw [List.mem_singleton.mp member]; trivial⟩
  · have published := publish_at model fiber exit held
    have stored := configuration_emit model _ [RunEvent.exited fiber.id exit] (configuration_update model m _ owned published)
    unfold exitFiber.exitStore
    dsimp only
    split
    · exact ⟨configuration_update model _ _ stored (cleared_at model root table _ published),
        by intro c member; rw [List.mem_singleton.mp member]; trivial⟩
    · refine ⟨stored, ?_⟩
      intro c member
      rcases List.mem_append.mp member with observer | administrative
      · obtain ⟨o, _, eq⟩ := List.mem_map.mp observer
        rw [← eq]; trivial
      · rcases List.mem_cons.mp administrative with same | later
        · rw [same]; trivial
        · rw [List.mem_singleton.mp later]; trivial


/-- Shared actual interrupt each at transport for both code-location instances. -/
theorem interrupt_each_at (model : Model) (root : NativeEff) (table : RowTable) (failure : ∀ cause, model.code (.failure cause)) (who : FiberId)
    (extra : ReasonAnnotations Ann) (targets : List FiberId) (acc : NativeMachine × List SourceCommand)
    (owned : ConfigurationAt model acc.1) (pending : CommandsAt model acc.2) :
    ConfigurationAt model (interruptEach (interpOf root table) who extra targets acc).1 ∧
      CommandsAt model (interruptEach (interpOf root table) who extra targets acc).2 := by
  induction targets generalizing acc with
  | nil => exact ⟨owned, pending⟩
  | cons target rest ih =>
    unfold interruptEach
    rw [List.foldl_cons]
    split
    · exact ih acc owned pending
    · rename_i fiber found
      have held := configuration_fiber model acc.1 target fiber owned found
      have changed := interrupt_cause_at model failure (interruptCause (interpOf root table) (some who) extra fiber.id) fiber held
      apply ih
      · exact configuration_emit model _ _ (configuration_update model acc.1 _ owned changed)
      · apply commands_append model _ _ pending
        split
        · intro c member; rw [List.mem_singleton.mp member]; trivial
        · intro c member; cases member


/-- Shared actual pending map at transport for both code-location instances. -/
theorem pending_map_at (model : Model) (fiber : SourceFiber)
    (edit : Pending EffName Val Err Defect FiberId Ann → Pending EffName Val Err Defect FiberId Ann)
    (held : FiberAt model fiber) (kept : ∀ p, (edit p).resumeWith = p.resumeWith) :
    FiberAt model {fiber with pending := fiber.pending.map edit} := by
  refine ⟨held.frame, ?_, held.dispatcher⟩
  intro p member
  obtain ⟨old, present, eq⟩ := List.mem_map.mp member
  rw [← eq, kept]
  exact held.pending old present


/-- Shared actual observer at transport for both code-location instances. -/
theorem observer_at (model : Model) (root : NativeEff) (table : RowTable) (facts : ObserverFacts model root table) (id : FiberId) (exit : ExitV)
    (acc : NativeMachine × List SourceCommand) (observer : Observer)
    (owned : ConfigurationAt model acc.1) (pending : CommandsAt model acc.2) :
    ConfigurationAt model (fireObserver (interpOf root table) id exit acc observer).1 ∧
      CommandsAt model (fireObserver (interpOf root table) id exit acc observer).2 := by
  let m := acc.1.emit [RunEvent.observerFired id observer]
  have base : ConfigurationAt model m := configuration_emit model acc.1 _ owned
  unfold fireObserver
  dsimp only
  split
  · exact ⟨base, commands_append model _ _ pending (by
      intro command member
      rw [List.mem_singleton.mp member]
      exact ⟨facts.exitValue exit _, exit_value_reply root [] table exit _⟩)⟩
  · exact ⟨configuration_modify model m _ _ base
      (fun fiber held => ⟨held.frame, held.pending, held.dispatcher⟩), pending⟩
  · split
    · exact ⟨configuration_halt model m _ base, pending⟩
    · rename_i state found
      exact ⟨⟨base.fibers, base.races, facts.drop _ _ m.state state base.scopes found⟩, pending⟩
  · rename_i waiter token
    split
    · exact ⟨base, pending⟩
    · rename_i old oldFound
      split
      · exact ⟨base, pending⟩
      · rename_i p pendingFound
        -- the guard: a firing whose record waits on another fiber only emits its event
        by_cases hg : p.waitingOn = some id
        case neg =>
          rw [if_neg hg]
          exact ⟨base, pending⟩
        rw [if_pos hg]
        have resumeAt := (configuration_fiber model m waiter old base oldFound).pending p
          (List.mem_of_find?_eq_some pendingFound)
        have changed :
            let next := if p.failFast && !exit.isSuccess && p.collected.all Exit.isSuccess then
              interruptEach (interpOf root table) waiter ((interpOf root table).stackAnnotations waiter)
                p.remaining (m, []) else (m, [])
            ConfigurationAt model next.1 ∧ CommandsAt model next.2 := by
          split
          · exact interrupt_each_at model root table facts.failure waiter _ p.remaining (m, []) base
              (by intro command member; cases member)
          · exact ⟨base, by intro command member; cases member⟩
        split
        · exact ⟨changed.1, commands_append model _ _ pending changed.2⟩
        · rename_i current currentFound
          have currentAt := configuration_fiber model _ waiter current changed.1 currentFound
          split
          · exact ⟨changed.1, commands_append model _ _ pending changed.2⟩
          · split
            · rename_i exits walk
              refine ⟨configuration_update model _ _ changed.1 ?_, ?_⟩
              · exact pending_map_at model current _ currentAt (by intro q; split <;> rfl)
              · exact commands_append model _ _ (commands_append model _ _ pending changed.2) (by
                  intro command member
                  rw [List.mem_singleton.mp member]
                  exact ⟨facts.countdown p.resumeWith exits resumeAt,
                    countdown_program_reply root [] table p.resumeWith exits resumeAt⟩)
            · rename_i exits target remaining walk
              let nextCurrent : SourceFiber := {current with pending := current.pending.map fun q =>
                if q.token = token then
                  {q with waitingOn := some target, remaining, collected := exits}
                else q}
              have nextAt : FiberAt model nextCurrent :=
                pending_map_at model current _ currentAt (by intro q; split <;> rfl)
              have observed := fiber_edits_at model facts.failure [.observe target (.countdown waiter token)] _
                (configuration_update model _ nextCurrent changed.1 nextAt)
              exact ⟨observed.1,
                commands_append model _ _ (commands_append model _ _ pending changed.2) observed.2⟩
  · rename_i raceId
    split
    · exact ⟨base, pending⟩
    · rename_i race found
      have raceAt := configuration_race model m raceId race base found
      split
      · refine ⟨configuration_emit model _ _ (configuration_race_update model _ _
          (configuration_race_update model m _ base raceAt) raceAt), commands_append model _ _ pending ?_⟩
        split
        · intro command member
          cases member
        · intro command member
          rw [List.mem_singleton.mp member]
          exact ⟨facts.raceSettle raceId _ _ raceAt.2, race_settle_reply root table raceId _ _⟩
      · exact ⟨configuration_race_update model m _ base raceAt, pending⟩
  · exact ⟨configuration_emit model m _ base, pending⟩


end Effect4.Program.CodeClosure.Configuration
