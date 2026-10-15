import Effect4.Laws.Machine.EditWords
import Effect4.Laws.Machine.RaceLookup

/-!
Concept: reactive-scheduling, R11, the machine part of evaluation-moves.
Observer words supply Approximation and the guard/store edit instances.
The countdown retains its current-record reread after nested interruptions.
The words establish no callback admission or progress.
-/
set_option autoImplicit false
namespace Effect4.Machine.Edits
universe u v
variable {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
  {κ φ η : Type (max u v)}
variable [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  [core : FiberCore ν β ε δ ι α κ φ]

def observerTailWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (id : FiberId) (exit : Exit β ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η) :
    Observer → List (Edit ν σ β ε δ ι α χ St κ φ η)
  | .resumeAwait _ _ _ => []
  | .untrackChild parent =>
    match m.fiber? parent with
    | none => []
    | some fiber => [.update {fiber with children := fiber.children.filter fun child => child ≠ id}]
  | .dropScopeFinalizer scope key =>
    match interp.dropFinalizer scope key m.state with
    | none => [.halt (.unknownScope scope)]
    | some state => [.setState state]
  | .countdown waiter token =>
    match m.fiber? waiter with
    | none => []
    | some fiber =>
      match fiber.pending.find? fun p => p.token = token with
      | none => []
      | some pending =>
        -- the machine's guard: a firing acts only when the record waits on the firing fiber
        if pending.waitingOn = some id then
          let fails := pending.failFast && !exit.isSuccess && pending.collected.all Exit.isSuccess
          let changed := if fails then
            interruptEach interp waiter (interp.stackAnnotations waiter) pending.remaining (m, [])
            else (m, [])
          let editsBefore := if fails then
            interruptWords interp waiter (interp.stackAnnotations waiter) pending.remaining (m, [])
            else []
          editsBefore ++ match changed.1.fiber? waiter with
            | none => []
            | some current =>
              match current.pending.find? fun p => p.token = token with
              | none => []
              | some _ =>
                match countdownWalk changed.1 pending.remaining (pending.collected ++ [exit]) with
                | (exits, none) => [.update {current with pending := current.pending.map fun p =>
                    if p.token = token then {p with waitingOn := none, remaining := [], collected := exits} else p}]
                | (exits, some (next, rest)) =>
                  [.update {current with pending := current.pending.map fun p =>
                    if p.token = token then
                      {p with waitingOn := some next, remaining := rest, collected := exits} else p},
                    .observe next (.countdown waiter token)]
        else []
  | .raceCallback raceId =>
    match m.race? raceId with
    | none => []
    | some race =>
      let race := race.afterExit id exit
      [.updateRace race] ++ match race.state.accepted, race.settled with
        | some accepted, false => [.updateRace {race with settled := true}, .emit [.raceSettled raceId accepted]]
        | _, _ => []
  | .callback key => [.emit [.callback key exit]]

def observerWord (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (id : FiberId) (exit : Exit β ε δ ι α) (m : RunMachine ν σ β ε δ ι α χ St κ φ η)
    (observer : Observer) : List (Edit ν σ β ε δ ι α χ St κ φ η) :=
  [.emit [.observerFired id observer]] ++
    observerTailWord interp id exit (m.emit [.observerFired id observer]) observer

/-- Interrupt commands contain only evaluations admitted by the supplied predicate.
Consumer: the observer producer path retains its queue cost and command membership. -/
theorem interrupt_commands_producer (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat) (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (evaluateProducer : ∀ target, weight (.evaluate target) = 0 ∧ Allowed (.evaluate target))
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    (((interruptEach interp who extra targets acc).2).map weight).sum = (acc.2.map weight).sum ∧
      ∀ command ∈ (interruptEach interp who extra targets acc).2,
        command ∈ acc.2 ∨ Allowed command := by
  induction targets generalizing acc with
  | nil => exact ⟨rfl, fun _ member => .inl member⟩
  | cons target targets ih =>
    cases found : acc.1.fiber? target with
    | none => simpa only [interruptEach, List.foldl_cons, found] using ih acc
    | some fiber =>
      let next := interruptRecord interp (some who) extra fiber
      let changed := (acc.1.update next.1).emit [.interruptRecorded (some who) target]
      let queued := acc.2 ++ (if next.2 then [.evaluate target] else [])
      have rest := ih (changed, queued)
      have cost : (queued.map weight).sum = (acc.2.map weight).sum := by
        unfold queued
        split <;> simp only [List.map_append, List.sum_append, List.map_cons, List.map_nil,
          List.sum_cons, List.sum_nil, (evaluateProducer target).1, Nat.add_zero]
      have members : ∀ command ∈ queued, command ∈ acc.2 ∨ Allowed command := by
        intro command member
        rcases List.mem_append.mp member with old | added
        · exact .inl old
        · split at added
          · rcases List.mem_cons.mp added with rfl | impossible
            · exact .inr (evaluateProducer target).2
            · cases impossible
          · cases added
      simpa only [interruptEach, List.foldl_cons, found] using
        And.intro (rest.1.trans cost) (fun command member =>
          (rest.2 command member).elim (members command) Or.inr)

/-- Interrupt commands contain only zero-cost evaluations.
Consumer: the observer producer path retains its generated queue cost. -/
theorem interrupt_commands_cost (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat)
    (evaluateCost : ∀ target, weight (.evaluate target) = 0)
    (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
    (((interruptEach interp who extra targets acc).2).map weight).sum = (acc.2.map weight).sum :=
  (interrupt_commands_producer interp weight (fun _ => True)
    (fun target => ⟨evaluateCost target, True.intro⟩) who extra targets acc).1

/-- One actual observer path retains administrative payloads and generated command cost.
Consumers: release custody, Timeout metadata, and operation-counter command accounting.
The actual update retains the counter, independently of saved-frame equality. -/
theorem observer_producer_path_races
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat) (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer)
    (update : ∀ m target old next, m.fiber? target = some old → next.id = old.id →
      next.frame = old.frame → next.dispatcher = old.dispatcher → next.parked = old.parked →
      next.currentOpCount = old.currentOpCount → next.running = old.running →
      (∀ pending ∈ next.pending, ∃ prior ∈ old.pending,
        pending.token = prior.token ∧ pending.resumeWith = prior.resumeWith) →
      next.observers = old.observers → next.exit = old.exit → next.children ⊆ old.children →
      Edge m ((Edit.update next).apply m) (.update next))
    (observe : ∀ m target observed, observed = observer →
      Edge m ((Edit.observe target observed).apply m) (.observe target observed))
    (fired : ∀ m id observer, Edge m (m.emit [.observerFired id observer]) (.emit [.observerFired id observer]))
    (settled : ∀ m id exit, Edge m (m.emit [.raceSettled id exit]) (.emit [.raceSettled id exit]))
    (callback : ∀ m key exit, Edge m (m.emit [.callback key exit]) (.emit [.callback key exit]))
    (state : ∀ m scope key s, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = some s →
      Edge m ((Edit.setState s).apply m) (.setState s))
    (halt : ∀ m scope key, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = none →
      Edge m (m.halt (.unknownScope scope)) (.halt (.unknownScope scope)))
    (race : ∀ m raceId old r, observer = .raceCallback raceId →
      m.race? raceId = some old → r.id = old.id → r.programs = old.programs →
      Edge m (m.updateRace r) (.updateRace r))
    (interrupted : ∀ who extra targets held, Effect4.Contracts.Path Edge held.1
      (interruptEach interp who extra targets held).1 (interruptWords interp who extra targets held))
    (evaluateProducer : ∀ target, weight (.evaluate target) = 0 ∧ Allowed (.evaluate target))
    (awaitProducer : ∀ waiter token mode, observer = .resumeAwait waiter token mode →
      weight (.resume waiter token (interp.exitValue exit mode)) = 0 ∧
      Allowed (.resume waiter token (interp.exitValue exit mode)))
    (raceProducer : ∀ raceId host token cleanup accepted, observer = .raceCallback raceId →
      weight (.resume host token (interp.raceSettle raceId cleanup accepted)) = 0 ∧
      Allowed (.resume host token (interp.raceSettle raceId cleanup accepted)))
    (countdownProducer : ∀ waiter token fiber pending exits, observer = .countdown waiter token →
      (acc.1.emit [.observerFired id observer]).fiber? waiter = some fiber → pending ∈ fiber.pending → pending.token = token →
      weight (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits)) = 0 ∧
      Allowed (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits))) :
    Effect4.Contracts.Path Edge acc.1 (fireObserver interp id exit acc observer).1
      (observerWord interp id exit acc.1 observer) ∧
    (((fireObserver interp id exit acc observer).2).map weight).sum = (acc.2.map weight).sum ∧
      ∀ command ∈ (fireObserver interp id exit acc observer).2, command ∈ acc.2 ∨ Allowed command := by
  have awaitCost := fun waiter token mode matching => (awaitProducer waiter token mode matching).1
  have raceCost := fun raceId host token cleanup accepted matching =>
    (raceProducer raceId host token cleanup accepted matching).1
  have countdownCost := fun waiter token fiber pending exits matching found member tokenSame =>
    (countdownProducer waiter token fiber pending exits matching found member tokenSame).1
  have appended (added : List (Cmd ν σ β ε δ ι α κ))
      (good : ∀ command ∈ added, Allowed command) :
      ∀ command ∈ acc.2 ++ added, command ∈ acc.2 ∨ Allowed command :=
    fun command member => (List.mem_append.mp member).elim Or.inl (fun added => .inr (good command added))
  have choicePath (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
      (before : RunMachine ν σ β ε δ ι α χ St κ φ η) (fails : Bool) :
      let changed := if fails then interruptEach interp who extra targets (before, []) else (before, [])
      Effect4.Contracts.Path Edge before changed.1
          (if fails then interruptWords interp who extra targets (before, []) else []) ∧
        (changed.2.map weight).sum = 0 ∧ ∀ command ∈ changed.2, Allowed command := by
    split
    · have producer := interrupt_commands_producer interp weight Allowed evaluateProducer who extra targets (before, [])
      exact ⟨interrupted who extra targets (before, []), producer.1, fun command member =>
        (producer.2 command member).elim (fun impossible => nomatch impossible) (fun proof => proof)⟩
    · exact ⟨.nil _, rfl, fun _ impossible => nomatch impossible⟩
  have chosen (who : FiberId) (extra : ReasonAnnotations α) (targets : List FiberId)
      (before after : RunMachine ν σ β ε δ ι α χ St κ φ η) (nested : List (Cmd ν σ β ε δ ι α κ))
      (fails : Bool)
      (equal : (if fails then interruptEach interp who extra targets (before, []) else (before, [])) =
        (after, nested)) :
      Effect4.Contracts.Path Edge before after
          (if fails then interruptWords interp who extra targets (before, []) else []) ∧
        (nested.map weight).sum = 0 ∧ ∀ command ∈ nested, Allowed command := by
    have prior := choicePath who extra targets before fails
    rw [equal] at prior
    exact prior
  fun_cases fireObserver interp id exit acc observer
  all_goals dsimp (config := {zetaDelta := true}) only at *
  all_goals simp only [observerWord, observerTailWord, List.map_append, List.sum_append,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, *]
  all_goals refine ⟨(Effect4.Contracts.Path.cons (fired acc.1 id _) (.nil _)).append ?_, ?_, ?_⟩
  case case1.refine_1 | case5.refine_1 | case6.refine_1 | case11.refine_1 | case12.refine_1 => exact .nil _
  case case1.refine_2 | case2.refine_2 | case3.refine_2 | case4.refine_2 | case5.refine_2 | case6.refine_2 |
      case11.refine_2 | case12.refine_2 | case14.refine_2 | case15.refine_2 => simp only [Nat.add_zero]
  case case2.refine_1 =>
    unfold RunMachine.modify
    split
    · rename_i found
      simp only [found]
      exact .nil _
    · rename_i fiber found
      simp only [found]
      exact .cons (update _ _ fiber _ found rfl rfl rfl rfl rfl rfl
        (fun pending member => ⟨pending, member, rfl, rfl⟩) rfl rfl
        (fun child member => (List.mem_filter.mp member).1)) (.nil _)
  case case3.refine_1 => exact .cons (halt _ _ _ rfl (by assumption)) (.nil _)
  case case4.refine_1 => exact .cons (state _ _ _ _ rfl (by assumption)) (.nil _)
  case case15.refine_1 => exact .cons (callback _ _ _) (.nil _)
  case case14.refine_1 =>
    rename_i raceId original changed raced pending base found result
    exact .cons (race _ _ original changed rfl found rfl rfl) (.nil _)
  case case7.refine_1 | case8.refine_1 =>
    rename_i choice
    have prior := chosen _ _ _ _ _ _ _ choice
    simpa only [List.append_nil, ↓reduceIte] using prior.1
  case case7.refine_2 | case8.refine_2 | case10.refine_2 =>
    rename_i choice
    have prior := chosen _ _ _ _ _ _ _ choice
    simp only [prior.2.1, applyFiberEdit, List.map_nil, List.sum_nil, Nat.add_zero]
  case case9.refine_1 =>
    rename_i waiter token original pending pendingFound _ collected fails changed nested current currentFound currentPending currentPendingFound exits walked installed base initialFound choice
    have prior := chosen _ _ _ _ _ _ _ choice
    apply prior.1.append
    exact .cons (update changed waiter current _ currentFound rfl rfl rfl rfl rfl rfl
      (by
        intro pending member
        obtain ⟨prior, held, equal⟩ := List.mem_map.mp member
        subst pending
        refine ⟨prior, held, ?_, ?_⟩
        all_goals split <;> rfl) rfl rfl (fun _ member => member)) (.nil _)
  case case10.refine_1 =>
    rename_i waiter token original pending pendingFound _ collected fails changed nested current currentFound currentPending currentPendingFound exits next rest walked installed observed base initialFound choice
    have prior := chosen _ _ _ _ _ _ _ choice
    apply prior.1.append
    exact .cons (update changed waiter current _ currentFound rfl rfl rfl rfl rfl rfl
      (by
        intro pending member
        obtain ⟨prior, held, equal⟩ := List.mem_map.mp member
        subst pending
        refine ⟨prior, held, ?_, ?_⟩
        all_goals split <;> rfl) rfl rfl (fun _ member => member)) (.cons (observe _ _ _ rfl) (.nil _))
  case case9.refine_2 =>
    rename_i waiter token original pending pendingFound _ collected fails changed nested current currentFound currentPending currentPendingFound exits walked installed base initialFound choice
    have prior := chosen _ _ _ _ _ _ _ choice
    rw [prior.2.1, countdownCost _ _ _ _ _ rfl (by assumption) (List.mem_of_find?_eq_some (by assumption))
      (of_decide_eq_true (List.find?_some (p := fun p : Pending ν β ε δ ι α => decide (p.token = token)) pendingFound))]
    simp only [Nat.add_zero]
  case case13.refine_1 =>
    rename_i raceId original changed raced accepted unsettled acceptedAt base found updated settledAt final
    refine (Effect4.Contracts.Path.cons (race _ _ original changed rfl found rfl rfl) (.nil _)).append
      (.cons ?_ (.cons (settled _ _ _) (.nil _)))
    simpa only [changed, Race.afterExit, acceptedAt] using
      race _ _ changed {changed with settled := true} rfl
        (RunMachine.race?_updateRace_at _ _ original changed found rfl) rfl rfl
  case case13.refine_2 =>
    split <;> simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      raceCost _ _ _ _ _ rfl, Nat.add_zero]


  case case2.refine_3 | case3.refine_3 | case4.refine_3 | case5.refine_3 | case6.refine_3 |
      case11.refine_3 | case12.refine_3 | case14.refine_3 | case15.refine_3 =>
    exact fun _ member => .inl member
  case case1.refine_3 =>
    apply appended
    intro command member
    rcases List.mem_cons.mp member with rfl | impossible
    · exact (awaitProducer _ _ _ rfl).2
    · cases impossible
  case case7.refine_3 | case8.refine_3 =>
    rename_i choice
    have prior := chosen _ _ _ _ _ _ _ choice
    exact appended _ prior.2.2
  case case9.refine_3 =>
    rename_i waiter token original pending pendingFound _ collected fails changed nested current currentFound currentPending currentPendingFound exits walked installed base initialFound choice
    have prior := chosen _ _ _ _ _ _ _ choice
    rw [List.append_assoc]
    apply appended
    intro command member
    rcases List.mem_append.mp member with nested | resumed
    · exact prior.2.2 command nested
    · rcases List.mem_cons.mp resumed with rfl | impossible
      · exact (countdownProducer _ _ _ _ _ rfl (by assumption)
          (List.mem_of_find?_eq_some pendingFound)
          (of_decide_eq_true (List.find?_some (p := fun p : Pending ν β ε δ ι α => decide (p.token = token)) pendingFound))).2
      · cases impossible
  case case10.refine_3 =>
    rename_i choice
    have prior := chosen _ _ _ _ _ _ _ choice
    simp only [applyFiberEdit, List.append_nil]
    exact appended _ prior.2.2
  case case13.refine_3 =>
    apply appended
    intro command member
    split at member
    · cases member
    · rcases List.mem_cons.mp member with rfl | impossible
      · exact (raceProducer _ _ _ _ _ rfl).2
      · cases impossible

/-- The original observer contract forgets only the selected race and its retained program list. -/
theorem observer_producer_path_controls
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat) (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer)
    (update : ∀ m target old next, m.fiber? target = some old → next.id = old.id →
      next.frame = old.frame → next.dispatcher = old.dispatcher → next.parked = old.parked →
      next.currentOpCount = old.currentOpCount → next.running = old.running →
      (∀ pending ∈ next.pending, ∃ prior ∈ old.pending,
        pending.token = prior.token ∧ pending.resumeWith = prior.resumeWith) →
      next.observers = old.observers → next.exit = old.exit → next.children ⊆ old.children →
      Edge m ((Edit.update next).apply m) (.update next))
    (observe : ∀ m target observed, observed = observer →
      Edge m ((Edit.observe target observed).apply m) (.observe target observed))
    (fired : ∀ m id observer, Edge m (m.emit [.observerFired id observer]) (.emit [.observerFired id observer]))
    (settled : ∀ m id exit, Edge m (m.emit [.raceSettled id exit]) (.emit [.raceSettled id exit]))
    (callback : ∀ m key exit, Edge m (m.emit [.callback key exit]) (.emit [.callback key exit]))
    (state : ∀ m scope key s, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = some s →
      Edge m ((Edit.setState s).apply m) (.setState s))
    (halt : ∀ m scope key, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = none →
      Edge m (m.halt (.unknownScope scope)) (.halt (.unknownScope scope)))
    (race : ∀ m raceId r, observer = .raceCallback raceId → Edge m (m.updateRace r) (.updateRace r))
    (interrupted : ∀ who extra targets held, Effect4.Contracts.Path Edge held.1
      (interruptEach interp who extra targets held).1 (interruptWords interp who extra targets held))
    (evaluateProducer : ∀ target, weight (.evaluate target) = 0 ∧ Allowed (.evaluate target))
    (awaitProducer : ∀ waiter token mode, observer = .resumeAwait waiter token mode →
      weight (.resume waiter token (interp.exitValue exit mode)) = 0 ∧
      Allowed (.resume waiter token (interp.exitValue exit mode)))
    (raceProducer : ∀ raceId host token cleanup accepted, observer = .raceCallback raceId →
      weight (.resume host token (interp.raceSettle raceId cleanup accepted)) = 0 ∧
      Allowed (.resume host token (interp.raceSettle raceId cleanup accepted)))
    (countdownProducer : ∀ waiter token fiber pending exits, observer = .countdown waiter token →
      (acc.1.emit [.observerFired id observer]).fiber? waiter = some fiber → pending ∈ fiber.pending → pending.token = token →
      weight (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits)) = 0 ∧
      Allowed (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits))) :
    Effect4.Contracts.Path Edge acc.1 (fireObserver interp id exit acc observer).1
      (observerWord interp id exit acc.1 observer) ∧
    (((fireObserver interp id exit acc observer).2).map weight).sum = (acc.2.map weight).sum ∧
      ∀ command ∈ (fireObserver interp id exit acc observer).2, command ∈ acc.2 ∨ Allowed command := by
  exact observer_producer_path_races interp weight Allowed id exit acc observer
    update observe fired settled callback state halt
    (fun m raceId _ r matching _ _ _ => race m raceId r matching)
    interrupted evaluateProducer awaitProducer raceProducer countdownProducer

/-- The accounting projection forgets only the observer update's running equation. -/
theorem observer_producer_path_accounting
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat) (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer)
    (update : ∀ m target old next, m.fiber? target = some old → next.id = old.id →
      next.frame = old.frame → next.dispatcher = old.dispatcher → next.parked = old.parked →
      next.currentOpCount = old.currentOpCount →
      (∀ pending ∈ next.pending, ∃ prior ∈ old.pending,
        pending.token = prior.token ∧ pending.resumeWith = prior.resumeWith) →
      next.observers = old.observers → next.exit = old.exit → next.children ⊆ old.children →
      Edge m ((Edit.update next).apply m) (.update next))
    (observe : ∀ m target observed, observed = observer →
      Edge m ((Edit.observe target observed).apply m) (.observe target observed))
    (fired : ∀ m id observer, Edge m (m.emit [.observerFired id observer]) (.emit [.observerFired id observer]))
    (settled : ∀ m id exit, Edge m (m.emit [.raceSettled id exit]) (.emit [.raceSettled id exit]))
    (callback : ∀ m key exit, Edge m (m.emit [.callback key exit]) (.emit [.callback key exit]))
    (state : ∀ m scope key s, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = some s →
      Edge m ((Edit.setState s).apply m) (.setState s))
    (halt : ∀ m scope key, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = none →
      Edge m (m.halt (.unknownScope scope)) (.halt (.unknownScope scope)))
    (race : ∀ m raceId r, observer = .raceCallback raceId → Edge m (m.updateRace r) (.updateRace r))
    (interrupted : ∀ who extra targets held, Effect4.Contracts.Path Edge held.1
      (interruptEach interp who extra targets held).1 (interruptWords interp who extra targets held))
    (evaluateProducer : ∀ target, weight (.evaluate target) = 0 ∧ Allowed (.evaluate target))
    (awaitProducer : ∀ waiter token mode, observer = .resumeAwait waiter token mode →
      weight (.resume waiter token (interp.exitValue exit mode)) = 0 ∧
      Allowed (.resume waiter token (interp.exitValue exit mode)))
    (raceProducer : ∀ raceId host token cleanup accepted, observer = .raceCallback raceId →
      weight (.resume host token (interp.raceSettle raceId cleanup accepted)) = 0 ∧
      Allowed (.resume host token (interp.raceSettle raceId cleanup accepted)))
    (countdownProducer : ∀ waiter token fiber pending exits, observer = .countdown waiter token →
      (acc.1.emit [.observerFired id observer]).fiber? waiter = some fiber → pending ∈ fiber.pending → pending.token = token →
      weight (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits)) = 0 ∧
      Allowed (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits))) :
    Effect4.Contracts.Path Edge acc.1 (fireObserver interp id exit acc observer).1
      (observerWord interp id exit acc.1 observer) ∧
    (((fireObserver interp id exit acc observer).2).map weight).sum = (acc.2.map weight).sum ∧
      ∀ command ∈ (fireObserver interp id exit acc observer).2, command ∈ acc.2 ∨ Allowed command := by
  exact observer_producer_path_controls interp weight Allowed id exit acc observer
    (fun m target old next found key frame dispatcher parked count _ pending observers exited children =>
      update m target old next found key frame dispatcher parked count pending observers exited children)
    observe fired settled callback state halt race interrupted evaluateProducer awaitProducer
    raceProducer countdownProducer

/-- The original metadata observer path erases only the retained counter equation. -/
theorem observer_producer_path_metadata
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat) (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer)
    (update : ∀ m target old next, m.fiber? target = some old → next.id = old.id →
      next.frame = old.frame → next.dispatcher = old.dispatcher → next.parked = old.parked →
      (∀ pending ∈ next.pending, ∃ prior ∈ old.pending,
        pending.token = prior.token ∧ pending.resumeWith = prior.resumeWith) →
      next.observers = old.observers → next.exit = old.exit → next.children ⊆ old.children →
      Edge m ((Edit.update next).apply m) (.update next))
    (observe : ∀ m target observed, observed = observer →
      Edge m ((Edit.observe target observed).apply m) (.observe target observed))
    (fired : ∀ m id observer, Edge m (m.emit [.observerFired id observer]) (.emit [.observerFired id observer]))
    (settled : ∀ m id exit, Edge m (m.emit [.raceSettled id exit]) (.emit [.raceSettled id exit]))
    (callback : ∀ m key exit, Edge m (m.emit [.callback key exit]) (.emit [.callback key exit]))
    (state : ∀ m scope key s, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = some s →
      Edge m ((Edit.setState s).apply m) (.setState s))
    (halt : ∀ m scope key, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = none →
      Edge m (m.halt (.unknownScope scope)) (.halt (.unknownScope scope)))
    (race : ∀ m raceId r, observer = .raceCallback raceId → Edge m (m.updateRace r) (.updateRace r))
    (interrupted : ∀ who extra targets held, Effect4.Contracts.Path Edge held.1
      (interruptEach interp who extra targets held).1 (interruptWords interp who extra targets held))
    (evaluateProducer : ∀ target, weight (.evaluate target) = 0 ∧ Allowed (.evaluate target))
    (awaitProducer : ∀ waiter token mode, observer = .resumeAwait waiter token mode →
      weight (.resume waiter token (interp.exitValue exit mode)) = 0 ∧
      Allowed (.resume waiter token (interp.exitValue exit mode)))
    (raceProducer : ∀ raceId host token cleanup accepted, observer = .raceCallback raceId →
      weight (.resume host token (interp.raceSettle raceId cleanup accepted)) = 0 ∧
      Allowed (.resume host token (interp.raceSettle raceId cleanup accepted)))
    (countdownProducer : ∀ waiter token fiber pending exits, observer = .countdown waiter token →
      (acc.1.emit [.observerFired id observer]).fiber? waiter = some fiber → pending ∈ fiber.pending → pending.token = token →
      weight (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits)) = 0 ∧
      Allowed (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits))) :
    Effect4.Contracts.Path Edge acc.1 (fireObserver interp id exit acc observer).1
      (observerWord interp id exit acc.1 observer) ∧
    (((fireObserver interp id exit acc observer).2).map weight).sum = (acc.2.map weight).sum ∧
      ∀ command ∈ (fireObserver interp id exit acc observer).2, command ∈ acc.2 ∨ Allowed command := by
  exact observer_producer_path_accounting interp weight Allowed id exit acc observer
    (fun m target old next found key frame dispatcher parked _ pending observers exited children =>
      update m target old next found key frame dispatcher parked pending observers exited children)
    observe fired settled callback state halt race interrupted evaluateProducer awaitProducer
    raceProducer countdownProducer

/-- One actual observer path retains administrative payloads and generated command cost.
Consumers: release custody and the existing machine-only observer path. -/
theorem observer_producer_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (weight : Cmd ν σ β ε δ ι α κ → Nat) (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer)
    (update : ∀ m target old next, m.fiber? target = some old → next.id = old.id →
      next.frame = old.frame → next.dispatcher = old.dispatcher → next.parked = old.parked →
      Edge m ((Edit.update next).apply m) (.update next))
    (observe : ∀ m target observer, Edge m ((Edit.observe target observer).apply m) (.observe target observer))
    (fired : ∀ m id observer, Edge m (m.emit [.observerFired id observer]) (.emit [.observerFired id observer]))
    (settled : ∀ m id exit, Edge m (m.emit [.raceSettled id exit]) (.emit [.raceSettled id exit]))
    (callback : ∀ m key exit, Edge m (m.emit [.callback key exit]) (.emit [.callback key exit]))
    (state : ∀ m scope key s, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = some s →
      Edge m ((Edit.setState s).apply m) (.setState s))
    (halt : ∀ m scope key, observer = .dropScopeFinalizer scope key →
      interp.dropFinalizer scope key m.state = none →
      Edge m (m.halt (.unknownScope scope)) (.halt (.unknownScope scope)))
    (race : ∀ m raceId r, observer = .raceCallback raceId → Edge m (m.updateRace r) (.updateRace r))
    (interrupted : ∀ who extra targets held, Effect4.Contracts.Path Edge held.1
      (interruptEach interp who extra targets held).1 (interruptWords interp who extra targets held))
    (evaluateProducer : ∀ target, weight (.evaluate target) = 0 ∧ Allowed (.evaluate target))
    (awaitProducer : ∀ waiter token mode, observer = .resumeAwait waiter token mode →
      weight (.resume waiter token (interp.exitValue exit mode)) = 0 ∧
      Allowed (.resume waiter token (interp.exitValue exit mode)))
    (raceProducer : ∀ raceId host token cleanup accepted, observer = .raceCallback raceId →
      weight (.resume host token (interp.raceSettle raceId cleanup accepted)) = 0 ∧
      Allowed (.resume host token (interp.raceSettle raceId cleanup accepted)))
    (countdownProducer : ∀ waiter token fiber pending exits, observer = .countdown waiter token →
      (acc.1.emit [.observerFired id observer]).fiber? waiter = some fiber → pending ∈ fiber.pending →
      weight (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits)) = 0 ∧
      Allowed (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits))) :
    Effect4.Contracts.Path Edge acc.1 (fireObserver interp id exit acc observer).1
      (observerWord interp id exit acc.1 observer) ∧
    (((fireObserver interp id exit acc observer).2).map weight).sum = (acc.2.map weight).sum ∧
      ∀ command ∈ (fireObserver interp id exit acc observer).2, command ∈ acc.2 ∨ Allowed command := by
  exact observer_producer_path_metadata interp weight Allowed id exit acc observer
    (fun m target old next found key frame dispatcher parked _ _ _ _ =>
      update m target old next found key frame dispatcher parked)
    (fun m target observed _ => observe m target observed)
    fired settled callback state halt race interrupted evaluateProducer awaitProducer
    raceProducer (fun waiter token fiber pending exits same found member _ =>
      countdownProducer waiter token fiber pending exits same found member)

/-- The shared producer transports any command predicate without a machine invariant.
Consumer: administrative queued-stack constraints. -/
theorem observer_commands
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (Allowed : Cmd ν σ β ε δ ι α κ → Prop)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer)
    (evaluateProducer : ∀ target, Allowed (.evaluate target))
    (awaitProducer : ∀ waiter token mode, observer = .resumeAwait waiter token mode →
      Allowed (.resume waiter token (interp.exitValue exit mode)))
    (raceProducer : ∀ raceId host token cleanup accepted, observer = .raceCallback raceId →
      Allowed (.resume host token (interp.raceSettle raceId cleanup accepted)))
    (countdownProducer : ∀ waiter token fiber pending exits, observer = .countdown waiter token →
      (acc.1.emit [.observerFired id observer]).fiber? waiter = some fiber → pending ∈ fiber.pending →
      Allowed (.resume waiter token (countdownPark.resumePrim (core := core) interp pending.resumeWith exits))) :
    ∀ command ∈ (fireObserver interp id exit acc observer).2, command ∈ acc.2 ∨ Allowed command := by
  let Edge (_ _ : RunMachine ν σ β ε δ ι α χ St κ φ η)
      (_ : Edit ν σ β ε δ ι α χ St κ φ η) : Prop := True
  have interrupted (who : FiberId) (extra : ReasonAnnotations α) (target : FiberId)
      (held : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
      Effect4.Contracts.Path Edge held.1 (interruptEach interp who extra [target] held).1
        (interruptWord interp who extra target held.1) :=
    interrupt_path interp who extra (fun _ _ _ _ => True.intro) (fun _ _ => True.intro) target held
  have produced := observer_producer_path (Edge := Edge) interp (fun _ => 0) Allowed id exit acc observer
    (fun _ _ _ _ _ _ _ _ _ => True.intro) (fun _ _ _ => True.intro)
    (fun _ _ _ => True.intro) (fun _ _ _ => True.intro) (fun _ _ _ => True.intro)
    (fun _ _ _ _ _ _ => True.intro) (fun _ _ _ _ _ => True.intro) (fun _ _ _ _ => True.intro)
    (fun who extra targets held => interrupts_path interp who extra (interrupted who extra) targets held)
    (fun target => ⟨rfl, evaluateProducer target⟩)
    (fun waiter token mode same => ⟨rfl, awaitProducer waiter token mode same⟩)
    (fun raceId host token cleanup accepted same => ⟨rfl, raceProducer raceId host token cleanup accepted same⟩)
    (fun waiter token fiber pending exits same found member =>
      ⟨rfl, countdownProducer waiter token fiber pending exits same found member⟩)
  exact produced.2.2

/-- The exact observer word, including interruption before current countdown lookup. -/
theorem observer_word (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer) :
    (fireObserver interp id exit acc observer).1 = run (observerWord interp id exit acc.1 observer) acc.1 := by
  let Edge (before after : RunMachine ν σ β ε δ ι α χ St κ φ η)
      (edit : Edit ν σ β ε δ ι α χ St κ φ η) := after = edit.apply before
  have interrupted (who : FiberId) (extra : ReasonAnnotations α) (target : FiberId)
      (held : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ)) :
      Effect4.Contracts.Path Edge held.1 (interruptEach interp who extra [target] held).1
        (interruptWord interp who extra target held.1) :=
    interrupt_path interp who extra (fun _ _ _ _ => rfl) (fun _ _ => rfl) target held
  have path := observer_producer_path (Edge := Edge) interp (fun _ => 0) (fun _ => True)
    id exit acc observer
    (fun _ _ _ _ _ _ _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ => rfl) (fun _ _ _ => rfl) (fun _ _ _ => rfl)
    (fun _ _ _ _ _ _ => rfl) (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun who extra targets held => interrupts_path interp who extra (interrupted who extra) targets held)
    (fun _ => ⟨rfl, True.intro⟩) (fun _ _ _ _ => ⟨rfl, True.intro⟩)
    (fun _ _ _ _ _ _ => ⟨rfl, True.intro⟩) (fun _ _ _ _ _ _ _ _ => ⟨rfl, True.intro⟩)
  exact (run_of_path (fun _ _ _ edge => edge) path.1).symm

/-- Actual observer payloads form one path for all per-edit invariant instances. -/
theorem observer_path
    {Edge : RunMachine ν σ β ε δ ι α χ St κ φ η → RunMachine ν σ β ε δ ι α χ St κ φ η →
      Edit ν σ β ε δ ι α χ St κ φ η → Prop}
    (interp : RunInterp ν σ β ε δ ι α χ St κ)
    (realized : ∀ before after edit, Edge before after edit → after = edit.apply before)
    (update : ∀ m target old next, m.fiber? target = some old → next.id = old.id →
      next.frame = old.frame → Edge m ((Edit.update next).apply m) (.update next))
    (observe : ∀ m target observer, Edge m ((Edit.observe target observer).apply m) (.observe target observer))
    (fired : ∀ m id observer, Edge m (m.emit [.observerFired id observer]) (.emit [.observerFired id observer]))
    (settled : ∀ m id exit, Edge m (m.emit [.raceSettled id exit]) (.emit [.raceSettled id exit]))
    (callback : ∀ m key exit, Edge m (m.emit [.callback key exit]) (.emit [.callback key exit]))
    (state : ∀ m s, Edge m ((Edit.setState s).apply m) (.setState s))
    (halt : ∀ m why, Edge m (m.halt why) (.halt why))
    (race : ∀ m r, Edge m (m.updateRace r) (.updateRace r))
    (interrupted : ∀ who extra target acc, Effect4.Contracts.Path Edge acc.1
      (interruptEach interp who extra [target] acc).1 (interruptWord interp who extra target acc.1))
    (id : FiberId) (exit : Exit β ε δ ι α)
    (acc : RunMachine ν σ β ε δ ι α χ St κ φ η × List (Cmd ν σ β ε δ ι α κ))
    (observer : Observer) :
    Effect4.Contracts.Path Edge acc.1 (fireObserver interp id exit acc observer).1
      (observerWord interp id exit acc.1 observer) := by
  have path := observer_producer_path interp (fun _ => 0) (fun _ => True) id exit acc observer
    (fun m target old next found key frame _ _ => update m target old next found key frame)
    observe fired settled callback
    (fun m _ _ s _ _ => state m s)
    (fun m scope _ _ _ => halt m (.unknownScope scope))
    (fun m _ r _ => race m r)
    (fun who extra targets held => interrupts_path interp who extra
      (interrupted who extra) targets held)
    (fun _ => ⟨rfl, True.intro⟩) (fun _ _ _ _ => ⟨rfl, True.intro⟩)
    (fun _ _ _ _ _ _ => ⟨rfl, True.intro⟩) (fun _ _ _ _ _ _ _ _ => ⟨rfl, True.intro⟩)
  have equation := run_of_path realized path.1
  rw [observer_word, equation]
  exact path.1


end Effect4.Machine.Edits
