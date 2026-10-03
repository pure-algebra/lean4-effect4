import Effect4.Laws.Program.Typed.Commands.Clauses.Spawn

/-!
# Laws.Program.Typed.Commands.Clauses.Command — the command-shaped evaluator clauses

Concept 4 (the configuration invariant `I`); steps of `deliver_preserves` and
`loop_preserves` through `evaluate_keeps` (`FiberClauseKeeps`). Three fiber operations whose
work is a machine step beside the fiber's own: `interruptAll` queues one `interruptTarget` per
target and the `afterInterrupt` that awaits them (`Machine/Fibers.lean:1556-1564`), `runIn` links
a fiber to a scope inline (`linkScope`, `:1005-1037`, the `link` command's step), and
`dropObservers` filters every fiber's token observers (`:1434-1441`).

Not established here: progress, or that the queued commands' own steps are typed (their
`StepPreserves` are `Commands/Race.lean`'s and `Commands/Bookkeeping.lean`'s).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## `interruptAll` -/

/-- The interrupts `interruptAll` queues: each reads nothing, owns nothing and carries no key. -/
theorem configTyped_cons_interrupts {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (targets : List FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ConfigTyped root rootTy w m
      ((targets.map fun t => (Cmd.interruptTarget t who extra : RCmd)) ++ q) := by
  induction targets with
  | nil => exact typed
  | cons t ts ih =>
    rw [List.map_cons, List.cons_append]
    exact configTyped_cons_plain ih _ trivial trivial trivial (fun _ h => by cases h) trivial rfl
      (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)

/-- **`interruptAll`** (`fiberInterruptAll`, `Machine/Fibers.lean:1556-1564`, `internal/effect.ts:888-915`,
D6b): the answer frame saved first; each target's interrupt queued, then `afterInterrupt` for the
host, whose reply (`unit`, the targets awaited) walks the saved stack. The targets are declared
(the row's pre), so the await's columns exist (`FiberListColumns` at `unknown`). -/
theorem clause_interruptAll (root : ProgramSource) (rootTy : EffTy) (targets : List FiberId)
    (who : Option FiberId) : FiberClauseKeeps root rootTy (.interruptAll targets who) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  -- the saved answer frame, an arrow from `unit` to the code's type
  let fr' : RSaved := { f.frame with stack := .answer (seqR next) :: f.frame.stack }
  let g : RFiber := { f with frame := fr' }
  have typedNext' : ∀ w', w.leHost w' → ∀ ans : Val, ans = Val.unit →
      TypedProg root w' tin (next ans) :=
    fun w' o ans post => typedNext w' o ans post
  have frame := Evaluating.unitAnswerFrame typedNext'
  have same : ∀ ty', w.Γ f.id = some ty' → ty' = ty :=
    fun _ h => Option.some.inj (h.symm.trans declared)
  have fresh : FiberTyped root w ((m.update f).update g) g :=
    fiberTyped_frame old ev.look ev.running fr'
      (fun ty' d => by
        rw [same ty' d]
        exact ⟨_, positionStack_of_host (hostStack_push frame stack)⟩)
      ⟨prov.recorded, prov.deferred⟩
      (fun _ h => by
        change raceRegistrationR f.frame.current = some _ at h
        rw [hc, raceRegistrationR_typed current] at h
        cases h)
  have edited : ConfigTyped root rootTy w (m.update g) rest := by
    rw [← rupdate_rupdate m (show g.id = f.id from rfl)]
    exact configTyped_frame_edit ev.typed rfl ev.look ev.running fr' fresh
  obtain ⟨f0, hf0, _⟩ := ev.stale
  have lookG : (m.update g).fiber? f.id = some g :=
    rfiber?_update_self (f := f0) (g := g) (by rw [rfiber?_id hf0]; exact hf0) (rfiber?_id hf0).symm
  have after : ConfigTyped root rootTy w (m.update g)
      (.afterInterrupt f.id y (.awaitAll targets) :: rest) := by
    refine configTyped_cons_afterAwaitAll edited y targets ⟨g, lookG, ev.running, notParked⟩
      (by rw [commandOwner_rupdate]; exact owner_free ev.typed.queue rfl) fun x hx => ?_
    rw [lookG] at hx
    cases hx
    refine ⟨.unknown, .unknown, fun t ht => ?_, ty, declared,
      hostStack_push frame (hostStack_races (m := m.update f) (m' := m.update g)
        (racesKept_of_eq fun _ => rfl) stack), ⟨prov.recorded, prov.deferred⟩⟩
    obtain ⟨fty, hfty⟩ := Option.isSome_iff_exists.mp (pre t ht)
    exact ⟨fty, hfty, subN_unknown _, subN_unknown _⟩
  show SettlesTyped root rootTy w f.id rest
    (prepareIterR (FiberAction.interruptAll (interpRAt root.program m.completedExits) m g y targets
      who))
  refine ⟨w, leHost_refl w, ?_⟩
  show ConfigTyped root rootTy w (m.update g)
    ((targets.map fun t => (Cmd.interruptTarget t (some (who.getD g.id))
      ((interpRAt root.program m.completedExits).stackAnnotations g.id) : RCmd)) ++
      [Cmd.afterInterrupt g.id y (ParkKind.awaitAll targets)] ++ rest)
  rw [List.append_assoc]
  exact configTyped_cons_interrupts after targets _ _

/-! ## Observers dropped -/

/-- **Dropping observers from one fiber keeps `I`**: every clause reads a fiber's observers one at a
time (`StoredObserverOk`, the race and bound columns) or through its keys, which only shrink; no
clause asks that a key be held (`configTyped_rupdate`'s `keys`). -/
theorem configTyped_shrinkObservers {root : ProgramSource} {rootTy : EffTy} {w : World}
    {M : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w M q) {x : RFiber}
    (hx : M.fiber? x.id = some x) (obs : List Observer) (sub : ∀ o ∈ obs, o ∈ x.observers) :
    ConfigTyped root rootTy w (M.update { x with observers := obs }) q := by
  let g : RFiber := { x with observers := obs }
  have hmem : x ∈ M.fibers := rfiber?_mem hx
  have old := typed.machine.fiber hmem
  have view : ObsView M (M.update g) := obsView_rupdate hx rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have fresh : FiberTyped root w (M.update g) g :=
    ⟨runFiberOk_congr moved.ok rfl rfl rfl rfl rfl rfl rfl, moved.delivery, moved.below,
      moved.pendingShape, moved.parkedIdle, moved.parkedBelow, moved.exited, moved.exitedStack,
      moved.deferredCause, moved.pendingOwner, fun o ho => moved.observers o (sub o ho),
      moved.registration, moved.code, moved.tokens,
      fun r race hr o ho => moved.raceObservers r race hr o (sub o ho), moved.targetsBelow,
      fun o ho => moved.observersBelow o (sub o ho), moved.children⟩
  have keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys M ∨
      (k.2 < M.nextToken ∧ requestOfR M k.1 k.2 = none) := by
    intro k hk
    refine Or.inl (fiberKeys_internal hmem ?_)
    unfold Guard.fiberKeys at hk ⊢
    rcases List.mem_append.mp hk with hk | hk
    · obtain ⟨o, ho, hko⟩ := List.mem_flatMap.mp hk
      exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨o, sub o ho, hko⟩)
    · exact List.mem_append_right _ hk
  exact configTyped_rupdate typed hx rfl (PendingWeaker.refl _) rfl rfl rfl rfl rfl (fun h => h)
    (fun h => h) keys fresh

/-- **Dropping observers from every fiber keeps `I`**, one fiber at a time along the fiber list
(`configTyped_shrinkObservers`): the fibers before `post` already dropped theirs. -/
theorem configTyped_shrinkAll {root : ProgramSource} {rootTy : EffTy} {w : World} {q : List RCmd}
    (obs : RFiber → List Observer) (sub : ∀ x, ∀ o ∈ obs x, o ∈ x.observers) :
    ∀ (post pre : List RFiber) (M : RState),
      M.fibers = pre.map (fun x => { x with observers := obs x }) ++ post →
      ConfigTyped root rootTy w M q →
      ConfigTyped root rootTy w
        { M with fibers := (pre ++ post).map fun x => { x with observers := obs x } } q := by
  intro post
  induction post with
  | nil =>
    intro pre M hM typed
    rw [List.append_nil] at hM ⊢
    rw [← hM]
    exact typed
  | cons x post ih =>
    intro pre M hM typed
    have nodup := typed.machine.wide.fiberIds
    have hx : M.fiber? x.id = some x := by
      apply rfiber?_of_mem nodup
      rw [hM]
      exact List.mem_append_right _ List.mem_cons_self
    have step := configTyped_shrinkObservers typed hx (obs x) (sub x)
    have hM' : (M.update { x with observers := obs x }).fibers =
        (pre ++ [x]).map (fun x => { x with observers := obs x }) ++ post := by
      have nd : ((pre.map fun x => ({ x with observers := obs x } : RFiber)).map RunFiber.id ++
          x.id :: post.map RunFiber.id).Nodup := by
        have h := nodup
        rw [hM, List.map_append, List.map_cons] at h
        exact h
      obtain ⟨_, ndPost, disj⟩ := List.nodup_append.mp nd
      have xPost : x.id ∉ post.map RunFiber.id := (List.nodup_cons.mp ndPost).1
      have hpre : (pre.map fun x => ({ x with observers := obs x } : RFiber)).map
          (fun y => if y.id = x.id then { x with observers := obs x } else y) =
          pre.map fun x => ({ x with observers := obs x } : RFiber) := by
        conv => rhs; rw [← List.map_id (pre.map fun x => ({ x with observers := obs x } : RFiber))]
        apply List.map_congr_left
        intro y hy
        show (if y.id = x.id then _ else y) = y
        rw [if_neg (fun hid => disj y.id (List.mem_map_of_mem hy) x.id List.mem_cons_self hid)]
      have hpost : post.map (fun y => if y.id = x.id then { x with observers := obs x } else y) =
          post := by
        conv => rhs; rw [← List.map_id post]
        apply List.map_congr_left
        intro y hy
        show (if y.id = x.id then _ else y) = y
        rw [if_neg (fun (hid : y.id = x.id) => xPost (by rw [← hid]; exact List.mem_map_of_mem hy))]
      unfold RunMachine.update
      rw [hM, List.map_append, List.map_cons, hpre, hpost, List.map_append, List.map_singleton,
        List.append_assoc, List.singleton_append]
      show _ ++ (if x.id = x.id then _ else x) :: post = _
      rw [if_pos rfl]
    have next := ih (pre ++ [x]) _ hM' step
    rw [List.append_assoc, List.singleton_append] at next
    exact next

/-- **The evaluated state after `dropObservers`' edit** (`Machine/Fibers.lean:1434-1441`): every
fiber's observers filtered; the evaluated fiber's record is the configuration's own, which the
settlement reinstalls unfiltered, so the edit shrinks every other fiber's observers. -/
theorem Evaluating.dropObs {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (keep : Observer → Bool) :
    Evaluating root rootTy w
      { m with fibers := m.fibers.map fun g => { g with observers := g.observers.filter keep } }
      rest f y := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  have sub : ∀ x : RFiber, ∀ o ∈ (if x.id = f.id then x.observers else x.observers.filter keep),
      o ∈ x.observers := by
    intro x o ho
    by_cases h : x.id = f.id
    · rw [if_pos h] at ho
      exact ho
    · rw [if_neg h] at ho
      exact (List.mem_filter.mp ho).1
  have all := configTyped_shrinkAll
    (fun x => if x.id = f.id then x.observers else x.observers.filter keep) sub
    (m.update f).fibers [] (m.update f) (by rw [List.map_nil, List.nil_append]) ev.typed
  have fibers : (({ m with fibers := m.fibers.map fun (g : RFiber) =>
        { g with observers := g.observers.filter keep } } : RState).update f).fibers =
      ([] ++ (m.update f).fibers).map fun (x : RFiber) =>
        { x with observers := if x.id = f.id then x.observers else x.observers.filter keep } := by
    unfold RunMachine.update
    rw [List.nil_append, List.map_map, List.map_map]
    apply List.map_congr_left
    intro x _
    by_cases h : x.id = f.id
    · show (if x.id = f.id then f else { x with observers := x.observers.filter keep }) =
        ({ (if x.id = f.id then f else x) with observers :=
          if (if x.id = f.id then f else x).id = f.id then (if x.id = f.id then f else x).observers
          else (if x.id = f.id then f else x).observers.filter keep } : RFiber)
      rw [if_pos h, if_pos h, if_pos rfl]
    · show (if x.id = f.id then f else { x with observers := x.observers.filter keep }) =
        ({ (if x.id = f.id then f else x) with observers :=
          if (if x.id = f.id then f else x).id = f.id then (if x.id = f.id then f else x).observers
          else (if x.id = f.id then f else x).observers.filter keep } : RFiber)
      rw [if_neg h, if_neg h, if_neg h]
  refine ⟨configTyped_congr ?_ (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) all,
    ⟨{ f0 with observers := f0.observers.filter keep }, ?_, exit0⟩, ev.running, ev.live⟩
  · exact fibers
  show (m.fibers.map fun g => ({ g with observers := g.observers.filter keep } : RFiber)).find?
    (fun x => decide (x.id = f.id)) = some _
  rw [List.find?_map]
  show (m.fibers.find? fun x => decide (x.id = f.id)).map _ = _
  rw [show (m.fibers.find? fun x => decide (x.id = f.id)) = some f0 from hf0]
  rfl

/-- **`dropObservers`** (`Machine/Fibers.lean:1434-1441`, the park's cleanup, `internal/effect.ts:773`):
every fiber's token observers dropped (`Evaluating.dropObs`), the fiber answered `void`. -/
theorem clause_dropObservers (root : ProgramSource) (rootTy : EffTy) (token : Nat) :
    FiberClauseKeeps root rootTy (.dropObservers token) := by
  intro w m rest f y next ev hc
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.dropObservers
    (interpRAt root.program m.completedExits) m f y token (answerWith next)))
  unfold FiberAction.dropObservers
  have keeps : ∀ keep : Observer → Bool, SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨{ m with fibers := m.fibers.map fun g => { g with observers := g.observers.filter keep } },
        answerR f (next .unit), y, .continue_, []⟩) := fun keep =>
    (ev.dropObs keep).settle_continue _ ((ev.dropObs keep).answer_typed hc (by rw [hc]; rfl)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) .unit (fun _ _ => rfl))
  exact keeps _

/-! ## `runIn`: the link step inline -/

/-- A `modify` that finds its fiber is an `update`. -/
theorem rmodify_found {M : RState} {id : FiberId} {x : RFiber} (k : RFiber → RFiber)
    (h : M.fiber? id = some x) : M.modify id k = M.update (k x) := by
  unfold RunMachine.modify
  rw [h]

/-- An interrupt record keeps the fiber's exit. -/
theorem interruptRecord_exit (interp : RInterp) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (t : RFiber) : (interruptRecord interp who extra t).1.exit = t.exit := by
  unfold interruptRecord
  aesop

section LinkScope
variable (root : ProgramSource) {M : RState} {mode : Supervision.ScopeMode} {scope : Nat}
  {target : FiberId} {interruptor : Option FiberId} {extra : ReasonAnnotations Ann}
  {entry : ScopeEntry} {t : RFiber}

theorem scopeStatus_entry (hentry : M.state.scopes.entryAt scope = some entry) :
    (interpR root.program).scopeStatus scope M.state = some entry.scope.closingExit? := by
  show (M.state.scopes.entryAt scope).map (fun e => e.scope.closingExit?) = _
  rw [hentry]
  rfl

/-- `linkScope` on a closed scope (`Machine/Fibers.lean:1013-1022`): the interrupt recorded. -/
theorem linkScope_closed {ex : ExitV} {t' : RFiber} {applyNow : Bool}
    (hentry : M.state.scopes.entryAt scope = some entry)
    (hclosed : entry.scope.closingExit? = some ex) (ht : M.fiber? target = some t)
    (hr : interruptRecord (interpR root.program) interruptor extra t = (t', applyNow)) :
    linkScope (interpR root.program) M mode scope target interruptor extra =
      ((M.update t').emit
        [RunEvent.scopeClosedOnLink scope target, RunEvent.interruptRecorded interruptor target],
       if applyNow then [Cmd.evaluate target] else []) := by
  unfold linkScope
  rw [scopeStatus_entry root hentry, hclosed]
  simp only [ht, hr]

/-- `linkScope` on an open scope and an exited target: nothing (`:1026-1027`). -/
theorem linkScope_exited (hentry : M.state.scopes.entryAt scope = some entry)
    (hopen : entry.scope.closingExit? = none) (ht : M.fiber? target = some t)
    (hx : t.exit.isSome = true) :
    linkScope (interpR root.program) M mode scope target interruptor extra = (M, []) := by
  unfold linkScope
  rw [scopeStatus_entry root hentry, hopen]
  simp only [ht]
  rw [if_pos hx]

/-- `linkScope` on an open scope and a live target (`:1028-1037`): the store's registration and the
target's drop observer. -/
theorem linkScope_open {s : Stores} {key : Nat} (hentry : M.state.scopes.entryAt scope = some entry)
    (hopen : entry.scope.closingExit? = none) (ht : M.fiber? target = some t)
    (hx : ¬ t.exit.isSome = true)
    (hlink : (interpR root.program).scopeLinkFiber mode scope target M.state = some (s, key)) :
    linkScope (interpR root.program) M mode scope target interruptor extra =
      ((({ M with state := s } : RState).update
          { t with observers := t.observers ++ [.dropScopeFinalizer scope key] }).emit
        [RunEvent.scopeLinked mode scope key target], []) := by
  unfold linkScope
  rw [scopeStatus_entry root hentry, hopen]
  simp only [ht]
  rw [if_neg hx, hlink]
  show ((({ M with state := s } : RState).modify target fun t =>
    { t with observers := t.observers ++ [.dropScopeFinalizer scope key] }).emit
      [RunEvent.scopeLinked mode scope key target], []) = _
  rw [rmodify_found _ (show ({ M with state := s } : RState).fiber? target = some t from ht)]

end LinkScope

/-- **`runIn`** (`fiberRunIn`, `Machine/Fibers.lean:1444-1449`, `internal/effect.ts:5447-5461`): the
link step inline (`linkScope` in mode `fiberRunIn`, the target its own interruptor), the fiber
answered `void`. The pre gives the target declared and the scope live, so the link does not
halt. Each arm moves the evaluated state (the configuration with `deliver` at its head) to the
link's machine: a closed scope records the interrupt (`configTyped_interruptRecord`), an exited
target is left alone, a live one is linked as the `link` command links it (`link_preserves`). On
the fiber itself the settlement overwrites the record, as the machine does: the interrupt record
and the drop observer are lost (the latter by `configTyped_shrinkObservers`). -/
theorem clause_runIn (root : ProgramSource) (rootTy : EffTy) (target : FiberId) (scope : Nat) :
    FiberClauseKeeps root rootTy (.runIn target scope) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, ⟨pre, hlive⟩, _⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have wide := ev.typed.machine.wide
  -- the settlement from the evaluated state over the link's machine
  have finish : ∀ (w' : World) (m' : RState) (nested : List RCmd), w.leHost w' →
      Evaluating root rootTy w' m' rest f y →
      (∀ g : RFiber, g.id = f.id →
        ConfigTyped root rootTy w' (m'.update g) (.loop f.id y :: rest) →
        ConfigTyped root rootTy w' (m'.update g) (nested ++ [.loop f.id y] ++ rest)) →
      SettlesTyped root rootTy w f.id rest
        (prepareIterR ⟨m', answerR f (next .unit), y, FiberAction.outcomeOf m' false, nested⟩) := by
    intro w' m' nested ord ev' push
    have hout : FiberAction.outcomeOf m' false = Outcome.continue_ := by
      unfold FiberAction.outcomeOf
      rw [ev'.live]
      rfl
    rw [hout]
    exact SettlesTyped.mono ord (ev'.settle_nested _ (ev'.answer_typed hc (by rw [hc]; rfl)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) .unit (fun _ _ => rfl)) nested push)
  have evaluate : ∀ (w' : World) (m' : RState) (applyNow : Bool) (g : RFiber), g.id = f.id →
      ConfigTyped root rootTy w' (m'.update g) (.loop f.id y :: rest) →
      ConfigTyped root rootTy w' (m'.update g)
        ((if applyNow then [Cmd.evaluate target] else []) ++ [.loop f.id y] ++ rest) := by
    intro w' m' applyNow g _ typed
    cases applyNow
    · exact typed
    · exact configTyped_cons_evaluate typed target
  -- the store holds the scope; the machine holds the target
  have live : m.state.ScopeLive scope := by
    have l : w.state.ScopeLive scope := hlive
    rw [wide.state] at l
    exact l
  obtain ⟨entry, hentry⟩ := Option.isSome_iff_exists.mp live
  have targetMem : target ∈ (m.update f).fibers.map RunFiber.id := (wide.fibers target).mp pre
  obtain ⟨t₁, ht₁⟩ : ∃ t₁, (m.update f).fiber? target = some t₁ := by
    obtain ⟨x, hx, hid⟩ := List.mem_map.mp targetMem
    refine ⟨x, ?_⟩
    rw [← hid]
    exact rfiber?_of_mem wide.fiberIds hx
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  obtain ⟨s, key, hlink⟩ : ∃ s key,
      (interpR root.program).scopeLinkFiber .fiberRunIn scope target m.state = some (s, key) := by
    obtain ⟨_, h⟩ := scopeLinkFiber_open root .fiberRunIn scope target m.state hentry
    exact ⟨_, _, h⟩
  have typedQ : ConfigTyped root rootTy w (m.update f)
      (.link .fiberRunIn scope target (some target) .empty :: .deliver f.id y :: rest) :=
    configTyped_cons_link ev.typed live (by rw [ht₁]; rfl)
  have hL : linkScope (interpRAt root.program m.completedExits) m .fiberRunIn scope target
      (some target) .empty =
      linkScope (interpR root.program) m .fiberRunIn scope target (some target) .empty := rfl
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.runIn
    (interpRAt root.program m.completedExits) m f y target scope (answerWith next)))
  unfold FiberAction.runIn
  rw [hL]
  by_cases self : target = f.id
  · -- the fiber links itself: the settlement overwrites its record
    subst self
    cases hcl : entry.scope.closingExit? with
    | some ex =>
      rcases hr : interruptRecord (interpR root.program) (some f.id) .empty f0 with ⟨t', applyNow⟩
      have tid : t'.id = f.id := by
        rw [← rfiber?_id hf0, ← interruptRecord_id (interpR root.program) (some f.id) .empty f0, hr]
      have texit : t'.exit = f0.exit := by
        rw [← interruptRecord_exit (interpR root.program) (some f.id) .empty f0, hr]
      rw [linkScope_closed root hentry hcl hf0 hr]
      refine finish w _ _ (leHost_refl w) ⟨?_, ⟨t', ?_, texit.trans exit0⟩, ev.running, ev.live⟩
        (evaluate w _ applyNow)
      · rw [emit_update_comm, rupdate_rupdate m (show f.id = t'.id from tid.symm)]
        exact configTyped_emit ev.typed _
      · show (m.update t').fiber? f.id = some t'
        rw [← tid]
        exact rfiber?_update_self (f := f0) (by rw [rfiber?_id hf0]; exact hf0)
          (tid.trans (rfiber?_id hf0).symm)
    | none =>
      by_cases hx : f0.exit.isSome = true
      · rw [linkScope_exited root hentry hcl hf0 hx]
        exact finish w m [] (leHost_refl w) ev fun _ _ typed => typed
      · rw [linkScope_open root hentry hcl hf0 hx hlink]
        have hxF : ¬ f.exit.isSome = true := by rw [← exit0]; exact hx
        obtain ⟨w', ord, typedL⟩ := link_preserves root rootTy .fiberRunIn scope f.id (some f.id)
          .empty w (m.update f) (.deliver f.id y :: rest) ev.live typedQ
        simp only [driveStep, linkScope_open (M := m.update f) root hentry hcl ev.look hxF hlink,
          List.nil_append] at typedL
        have lookL : ((({ m.update f with state := s } : RState).update
            { f with observers := f.observers ++ [.dropScopeFinalizer scope key] }).emit
              [RunEvent.scopeLinked .fiberRunIn scope key f.id]).fiber? f.id =
            some { f with observers := f.observers ++ [.dropScopeFinalizer scope key] } :=
          rfiber?_update_self (m := { m.update f with state := s }) (f := f)
            (g := { f with observers := f.observers ++ [.dropScopeFinalizer scope key] }) ev.look rfl
        have shrunk := configTyped_shrinkObservers typedL
          (x := { f with observers := f.observers ++ [.dropScopeFinalizer scope key] }) lookL f.observers
          (fun _ ho => List.mem_append_left [.dropScopeFinalizer scope key] ho)
        have shrunk' : ConfigTyped root rootTy w'
            ((({ m with state := s } : RState).update f).emit
              [RunEvent.scopeLinked .fiberRunIn scope key f.id]) (.deliver f.id y :: rest) := by
          have e : (((({ m with state := s } : RState).update f).update
              { f with observers := f.observers ++ [.dropScopeFinalizer scope key] }).emit
                [RunEvent.scopeLinked .fiberRunIn scope key f.id]).update f =
              (({ m with state := s } : RState).update f).emit
                [RunEvent.scopeLinked .fiberRunIn scope key f.id] := by
            rw [emit_update_comm, rupdate_rupdate _
              (show f.id = ({ f with observers := f.observers ++ [.dropScopeFinalizer scope key] } :
                RFiber).id from rfl), rupdate_rupdate _ rfl]
          rw [← e]
          exact shrunk
        have hid0 : f.id = ({ f0 with observers := f0.observers ++ [.dropScopeFinalizer scope key] } :
            RFiber).id := (rfiber?_id hf0).symm
        refine finish w' _ [] ord ⟨?_, ⟨{ f0 with observers :=
          f0.observers ++ [.dropScopeFinalizer scope key] }, ?_, exit0⟩, ev.running, ev.live⟩
          fun _ _ typed => typed
        · rw [emit_update_comm, rupdate_rupdate _ hid0]
          exact shrunk'
        · show (({ m with state := s } : RState).update
            { f0 with observers := f0.observers ++ [.dropScopeFinalizer scope key] }).fiber? f.id = _
          rw [← rfiber?_id hf0]
          exact rfiber?_update_self (m := { m with state := s }) (f := f0)
            (by rw [rfiber?_id hf0]; exact hf0) rfl
  · -- another fiber
    have ht : m.fiber? target = some t₁ := by
      rw [← rfiber?_update_other (m := m) (g := f) self]
      exact ht₁
    cases hcl : entry.scope.closingExit? with
    | some ex =>
      rcases hr : interruptRecord (interpR root.program) (some target) .empty t₁ with ⟨t', applyNow⟩
      have tid : t'.id = target := by
        rw [← rfiber?_id ht, ← interruptRecord_id (interpR root.program) (some target) .empty t₁, hr]
      have ne : f.id ≠ t'.id := fun h => self (tid.symm.trans h.symm)
      rw [linkScope_closed root hentry hcl ht hr]
      refine finish w _ _ (leHost_refl w) ⟨?_, ⟨f0, ?_, exit0⟩, ev.running, ev.live⟩
        (evaluate w _ applyNow)
      · rw [emit_update_comm, rupdate_comm m ne]
        have recorded := configTyped_interruptRecord ev.typed ht₁ (some target) .empty
        rw [hr] at recorded
        cases applyNow
        · exact configTyped_emit recorded _
        · exact configTyped_emit (configTyped_tail recorded) _
      · exact (rfiber?_update_other ne).trans hf0
    | none =>
      by_cases hx : t₁.exit.isSome = true
      · rw [linkScope_exited root hentry hcl ht hx]
        exact finish w m [] (leHost_refl w) ev fun _ _ typed => typed
      · rw [linkScope_open root hentry hcl ht hx hlink]
        obtain ⟨w', ord, typedL⟩ := link_preserves root rootTy .fiberRunIn scope target
          (some target) .empty w (m.update f) (.deliver f.id y :: rest) ev.live typedQ
        simp only [driveStep, linkScope_open (M := m.update f) root hentry hcl ht₁ hx hlink,
          List.nil_append] at typedL
        have ne : f.id ≠ ({ t₁ with observers := t₁.observers ++ [.dropScopeFinalizer scope key] } :
            RFiber).id := fun h => self ((rfiber?_id ht).symm.trans h.symm)
        refine finish w' _ [] ord ⟨?_, ⟨f0, ?_, exit0⟩, ev.running, ev.live⟩ fun _ _ typed => typed
        · rw [emit_update_comm, rupdate_comm _ ne]
          exact typedL
        · exact (rfiber?_update_other ne).trans hf0

end Effect4.Program.Typed
