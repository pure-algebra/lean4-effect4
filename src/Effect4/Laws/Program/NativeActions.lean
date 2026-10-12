import Effect4.Laws.Program.NativeEvaluation

/-!
Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
The native action result retains the source programs that it starts, parks or closes.
All predicates read existing machine fields and the existing command residue.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- The actual first-exit race action retains its allocated owner, token and unlaunched permissions.
Consumers: the lexical action adapter and Timeout's source-qualified race assignment. -/
theorem with_fiber_first_race_programs (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (programs : List NCode)
    (site : Option (List Nat)) (owned : ConfigurationAt root m) (held : FiberAt root fiber)
    (entrants : (∀ code ∈ programs, CodeAt root code) ∧ RaceAllowed root)
    (Permission : NCode → Prop) (permissions : ∀ code ∈ programs, Permission code) :
    let result := evaluatePrim.withFiber (interpAt root completed table) m fiber yielding (.raceAllFirst programs site)
    EvaluationAt root result ∧
      ∃ race : SourceRace, result.machine.races = m.races ++ [race] ∧
        race.id = m.nextRace ∧ race.host = fiber.id ∧ race.token = m.nextToken ∧
        race.programs = programs ∧ (∀ code ∈ race.programs, Permission code) :=
  begin_race_programs root completed table m fiber yielding programs site .firstExit owned held entrants
    Permission permissions

/-- Source ownership through the actual fiber-action evaluator. -/
theorem with_fiber_at (root : NativeEff) (completed) (table : RowTable)
    (m : NativeMachine) (fiber : SourceFiber) (yielding : Bool) (action : NAction)
    (owned : ConfigurationAt root m) (held : FiberAt root fiber) (source : ActionAt root action) :
    EvaluationAt root (evaluatePrim.withFiber (interpAt root completed table) m fiber yielding action) := by
  cases action
  case fork program options site =>
    let before := if options.daemon then m else {m with middlewareInstalled := true}
    have beforeOwned : ConfigurationAt root before := by
      unfold before
      split
      · exact owned
      · exact ⟨owned.fibers, owned.races, owned.scopes⟩
    let spawned := spawn (interpAt root completed table) before fiber program options site
    have child := configuration_spawn root completed table before fiber program options site beforeOwned source
    have started := start_at root spawned.1 spawned.2.1 spawned.2.2 options.startImmediately child held
    refine ⟨started.1, ?_, ?_⟩
    · apply fiber_current_at root _ _ started.2.1
      trivial
    · apply commands_append root _ _ started.2.2
      split
      · intro command member; cases member
      · intro command member; rw [List.mem_singleton.mp member]; trivial
  case forkIn program options scope site =>
    let spawned := spawn (interpAt root completed table) m fiber program {options with daemon := true} site
    have child := configuration_spawn root completed table m fiber program {options with daemon := true} site owned source
    have started := start_at root spawned.1 spawned.2.1 spawned.2.2 options.startImmediately child held
    refine ⟨started.1, ?_, ?_⟩
    · apply fiber_current_at root _ _ started.2.1
      trivial
    · apply commands_append root _ _ started.2.2
      intro command member; rw [List.mem_singleton.mp member]; trivial
  case forkScoped program options site =>
    simp only [evaluatePrim.withFiber]
    split
    · rename_i scope ambient
      let spawned := spawn (interpAt root completed table) m fiber program {options with daemon := true} site
      have child := configuration_spawn root completed table m fiber program {options with daemon := true} site owned source
      have started := start_at root spawned.1 spawned.2.1 spawned.2.2 options.startImmediately child held
      refine ⟨started.1, ?_, ?_⟩
      · apply fiber_current_at root _ _ started.2.1
        trivial
      · apply commands_append root _ _ started.2.2
        intro command member; rw [List.mem_singleton.mp member]; trivial
    · exact ⟨owned, fiber_current_at root fiber _ held trivial, by intro command member; cases member⟩
  case raceAll programs site =>
    exact (begin_race_programs root completed table m fiber yielding programs site .firstSuccess owned held source
      (CodeAt root) source.1).1
  case raceAllFirst programs site =>
    exact (with_fiber_first_race_programs root completed table m fiber yielding programs site owned held source
      (CodeAt root) source.1).1
  case runIn target scope =>
    have linked := link_edits_at root completed table m .fiberRunIn scope target (some target) ReasonAnnotations.empty owned
    exact ⟨linked, fiber_current_at root fiber _ held trivial, by intro command member; cases member⟩
  case awaitAll targets =>
    have countdown := countdown_edits_at root completed table m fiber targets .exitsValue false owned held trivial
    exact ⟨countdown.1, countdown.2, by intro command member; cases member⟩
  case awaitAllFailFast targets =>
    have countdown := countdown_edits_at root completed table m fiber targets .exitsValue true owned held trivial
    exact ⟨countdown.1, countdown.2, by intro command member; cases member⟩
  case awaitNewChildren snapshot =>
    have countdown := countdown_edits_at root completed table m fiber (fiber.children.filter (fun child => !(snapshot.contains child))) .void false owned held trivial
    exact ⟨countdown.1, countdown.2, by intro command member; cases member⟩
  case closePar programs =>
    exact ⟨fork_finalizers_at root completed table m fiber programs owned source.1, held,
      by intro command member
         rcases List.mem_append.mp member with evaluated | finished
         · obtain ⟨child, _, same⟩ := List.mem_map.mp evaluated
           rw [← same]; trivial
         · rw [List.mem_singleton.mp finished]; trivial⟩
  case closeScope scope exit =>
    simp only [evaluatePrim.withFiber]
    split
    · exact ⟨owned, held, by intro command member; cases member⟩
    · rename_i state operation
      have closed := interp_close_at root completed table scope exit fiber.frame.interruptible fiber.id
        m.state state none owned.scopes operation
      exact ⟨configuration_store root m state owned closed.1,
        fiber_current_at root fiber _ held trivial, by intro command member; cases member⟩
    · rename_i state program operation
      have closed := interp_close_at root completed table scope exit fiber.frame.interruptible fiber.id
        m.state state (some program) owned.scopes operation
      have masked := mask_frame_at root fiber.frame held.frame
      exact ⟨configuration_store root m state owned closed.1,
        ⟨⟨closed.2 program rfl, masked.2⟩, held.pending, held.dispatcher⟩,
        by intro command member; cases member⟩
  case interruptAs target who =>
    simp only [evaluatePrim.withFiber, evaluatePrim.interruptAs]
    cases found : m.fiber? target with
    | none => exact ⟨owned, held, by intro command member; cases member⟩
    | some other =>
      exact ⟨configuration_emit root m _ owned, held,
        by intro command member; rw [List.mem_singleton.mp member]; trivial⟩
  case setInterruptible body flag =>
    cases flag with
    | false =>
      have masked := mask_frame_at root fiber.frame held.frame
      exact ⟨owned, ⟨⟨source, masked.2⟩, held.pending, held.dispatcher⟩,
        by intro command member; cases member⟩
    | true =>
      have entry := interruptible_frame_at root fiber.frame held.frame
      have chosen : CodeAt root (fiber.frame.interruptibleRegion.2.getD body) := by
        cases h : fiber.frame.interruptibleRegion.2 with
        | none => exact source
        | some code =>
          apply entry.2 code
          rw [h]
          rfl
      exact ⟨owned, ⟨⟨chosen, entry.1.2⟩, held.pending, held.dispatcher⟩,
        by intro command member; cases member⟩
  case getInterruptible =>
    have masked := mask_frame_at root fiber.frame held.frame
    exact ⟨owned, ⟨⟨trivial, masked.2⟩, held.pending, held.dispatcher⟩,
      by intro command member; cases member⟩
  all_goals have looked (target : FiberId) (other : SourceFiber) (found : m.fiber? target = some other) :
      FiberAt root other := configuration_fiber root m target other owned found
  all_goals simp only [evaluatePrim.withFiber]
  all_goals repeat' split
  all_goals aesop (add safe constructors [EvaluationAt, FiberAt]) (add norm simp [CommandsAt, CommandAt, List.mem_cons, List.mem_append, CodeAt, ThunkAt, StoreThunkAt, StoreActionAt, ProgAt, NameAt, FrameAt, Option.getD_none, Option.getD_some]) (add safe apply [configuration_emit, configuration_update, configuration_map_fibers, fiber_current_at, mask_frame_at]) (add safe forward [looked, (interrupt_record_at root completed table)]) (add safe cases [FiberAt])

end Effect4.Program.SourceScope
