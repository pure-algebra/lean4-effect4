import Effect4.Laws.Program.Typed.Commands.Clauses.Spawn

/-!
# Laws.Program.Typed.Commands.Clauses.Command — the command-shaped evaluator clauses

Concept 4 (the configuration invariant `I`); steps of `deliver_preserves` and
`loop_preserves` through `evaluate_keeps` (`FiberClauseKeeps`). Three fiber operations whose
work is a machine step beside the fiber's own: `interruptAll` queues one `interruptTarget` per
target and the `afterInterrupt` that awaits them (`Machine/Fibers.lean:1556-1564`), `runIn` links
a fiber to a scope through its addressed link plan (`linkScopeEdits`, the `link` command's
producer), and `dropObservers` filters every installed fiber's token observers.

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
      (by rw [commandOwner_update]; exact owner_free ev.typed.queue rfl) fun x hx => ?_
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

/-- Prepare the actual caller before applying its addressed edits; a step of `clause_dropObservers`
and `clause_runIn` on the typed command preservation path. -/
theorem Evaluating.prepare_continue {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {f : RFiber} {y : Bool}
    (ev : Evaluating root rootTy w m rest f y) (fr : RSaved)
    (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr)
    (edits : List (FiberEdit Err Defect FiberId Ann)) :
    ∃ g : RFiber, g.id = f.id ∧
      prepareIterR ⟨m, {f with frame := fr}, y, .continue_, [], edits⟩ =
        ⟨m, g, y, .continue_, [], edits⟩ ∧
      ConfigTyped root rootTy w (m.update g) (.loop f.id y :: rest) := by
  let fr' : RSaved := {fr with current := prepareR m.completedExits fr.current}
  have code' : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr' :=
    fun ty declared => codeOk_prepare _ ev.view (code ty declared)
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := code' ty declared
  have glue : prepareIterR ⟨m, {f with frame := fr}, y, .continue_, [], edits⟩ =
      ⟨m, {f with frame := fr'}, y, .continue_, [], edits⟩ :=
    prepareScopedExitR_of_typed current
  refine ⟨{f with frame := fr'}, rfl, glue, ?_⟩
  have step := (configTyped_frame_step ev.typed rfl ev.look ev.running fr' code'
    (raceRegistrationR_typed current)).1 y
  rw [rupdate_rupdate m (show ({f with frame := fr'} : RFiber).id = f.id from rfl)] at step
  exact step

/-- The edit word's typed actual result settles without overwriting its selected owner.
This is the common settlement step of `clause_dropObservers` and `clause_runIn`. -/
theorem settle_continue_edits_typed {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {rest : List RCmd} {g : RFiber} {id : FiberId} {y : Bool}
    (edits : List (FiberEdit Err Defect FiberId Ann))
    (declared : (w.Γ g.id).isSome = true)
    (typed : ConfigTyped root rootTy w (applyFiberEdits edits (m.update g)).1
      ((applyFiberEdits edits (m.update g)).2 ++ [.loop id y] ++ rest)) :
    ConfigTyped root rootTy w (settle id rest ⟨m, g, y, .continue_, [], edits⟩).1
      (settle id rest ⟨m, g, y, .continue_, [], edits⟩).2 := by
  obtain ⟨owner, found⟩ : ∃ owner, (applyFiberEdits edits (m.update g)).1.fiber? g.id = some owner := by
    obtain ⟨owner, member, same⟩ := List.mem_map.mp ((typed.machine.wide.fibers g.id).mp declared)
    refine ⟨owner, ?_⟩
    rw [← same]
    exact rfiber?_of_mem typed.machine.wide.fiberIds member
  cases edits with
  | nil => exact typed
  | cons edit edits =>
    simp only [settle, found, settleOutcome, List.append_nil]
    have ownerFound : (applyFiberEdits (edit :: edits) (m.update g)).1.fiber? owner.id = some owner := by
      rw [rfiber?_id found]
      exact found
    rw [rupdate_self ownerFound typed.machine.wide.fiberIds]
    exact typed

/-- `dropObservers` applies its token removal to the prepared caller and all retained fibers. -/
theorem clause_dropObservers (root : ProgramSource) (rootTy : EffTy) (token : Nat) :
    FiberClauseKeeps root rootTy (.dropObservers token) := by
  intro w m rest f y next ev hc
  have code := ev.answer_typed hc (by rw [hc]; rfl)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) .unit (fun _ _ => rfl)
  obtain ⟨g, gid, glue, ready⟩ := ev.prepare_continue _ code [.dropToken token]
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.dropObservers
    (interpRAt root.program m.completedExits) m f y token (answerWith next)))
  change SettlesTyped root rootTy w f.id rest
    (prepareIterR ⟨m, {f with frame := {f.frame with current := next .unit}}, y,
      .continue_, [], [.dropToken token]⟩)
  rw [glue]
  refine ⟨w, leHost_refl w, settle_continue_edits_typed _ ?_ ?_⟩
  · rw [gid]
    exact ev.typed.machine.wide.fibers f.id |>.mpr (List.mem_map.mpr ⟨f, rfiber?_mem ev.look, rfl⟩)
  · let keep : Observer → Bool := fun
      | .resumeAwait _ t _ => t ≠ token
      | .countdown _ t => t ≠ token
      | _ => true
    have all := configTyped_shrinkAll (fun x => x.observers.filter keep)
      (fun _ _ ho => (List.mem_filter.mp ho).1) (m.update g).fibers [] (m.update g)
      (by rw [List.map_nil, List.nil_append]) ready
    exact all

/-! ## `runIn`: the link step inline -/

/-- A `modify` that finds its fiber is an `update`. -/
theorem rmodify_found {M : RState} {id : FiberId} {x : RFiber} (k : RFiber → RFiber)
    (h : M.fiber? id = some x) : M.modify id k = M.update (k x) := by
  unfold RunMachine.modify
  rw [h]

/-- An interrupt record keeps the fiber's exit. -/
theorem interruptRecord_exit (interp : RInterp) (who : Option FiberId) (extra : ReasonAnnotations Ann)
    (t : RFiber) : (interruptRecord interp who extra t).1.exit = t.exit := by
  unfold interruptRecord interruptWithCause
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
  unfold linkScope linkScopeEdits
  rw [scopeStatus_entry root hentry, hclosed]
  simp only [ht, applyFiberEdits, List.foldl, applyFiberEdit, rfiber?_emit, List.nil_append]
  change (((M.emit _).update (interruptRecord (interpR root.program) interruptor extra t).1),
    if (interruptRecord (interpR root.program) interruptor extra t).2 then _ else _) = _
  rw [hr, emit_update_comm]

/-- `linkScope` on an open scope and an exited target: nothing (`:1026-1027`). -/
theorem linkScope_exited (hentry : M.state.scopes.entryAt scope = some entry)
    (hopen : entry.scope.closingExit? = none) (ht : M.fiber? target = some t)
    (hx : t.exit.isSome = true) :
    linkScope (interpR root.program) M mode scope target interruptor extra = (M, []) := by
  unfold linkScope linkScopeEdits
  rw [scopeStatus_entry root hentry, hopen]
  simp only [ht]
  rw [if_pos hx]
  rfl

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
  unfold linkScope linkScopeEdits
  rw [scopeStatus_entry root hentry, hopen]
  simp only [ht]
  rw [if_neg hx, hlink]
  simp only [applyFiberEdits, List.foldl, applyFiberEdit, RunMachine.observe, List.nil_append]
  rw [RunMachine.modify_emit]
  show ((({ M with state := s } : RState).modify target fun t =>
    { t with observers := t.observers ++ [.dropScopeFinalizer scope key] }).emit
      [RunEvent.scopeLinked mode scope key target], []) = _
  rw [rmodify_found _ (show ({ M with state := s } : RState).fiber? target = some t from ht)]

end LinkScope

/-- `runIn` prepares its answer before applying the actual link edit to the installed caller. -/
theorem clause_runIn (root : ProgramSource) (rootTy : EffTy) (target : FiberId) (scope : Nat) :
    FiberClauseKeeps root rootTy (.runIn target scope) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨_, ⟨pre, hlive⟩, _⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have wide := ev.typed.machine.wide
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
  obtain ⟨t0, ht0, sameExit⟩ : ∃ t0, m.fiber? target = some t0 ∧ t0.exit = t₁.exit := by
    by_cases self : target = f.id
    · subst target
      rw [ev.look] at ht₁
      cases ht₁
      exact ⟨f0, hf0, exit0⟩
    · exact ⟨t₁, (rfiber?_update_other self).symm.trans ht₁, rfl⟩
  have status : (interpRAt root.program m.completedExits).scopeStatus scope m.state =
      some entry.scope.closingExit? := scopeStatus_entry root hentry
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.runIn
    (interpRAt root.program m.completedExits) m f y target scope (answerWith next)))
  unfold FiberAction.runIn linkScopeEdits
  rw [status]
  cases closed : entry.scope.closingExit? with
  | some ex =>
    rw [ht0]
    let events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit) :=
      [.scopeClosedOnLink scope target, .interruptRecorded (some target) target]
    let edits : List (FiberEdit Err Defect FiberId Ann) :=
      [.interrupt target (interruptCause (interpR root.program) (some target) .empty target)]
    have emitted := ev.emit events
    have code := emitted.answer_typed hc (by rw [hc]; rfl)
      (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) .unit (fun _ _ => rfl)
    obtain ⟨g, gid, glue, ready⟩ := emitted.prepare_continue _ code edits
    change SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m.emit events, {f with frame := {f.frame with current := next .unit}}, y,
        FiberAction.outcomeOf (m.emit events) false, [],
        [.interrupt target (interruptCause (interpR root.program) (some target) .empty t0.id)]⟩)
    rw [rfiber?_id ht0]
    have out : FiberAction.outcomeOf (m.emit events) false = .continue_ := by
      unfold FiberAction.outcomeOf
      rw [emitted.live]
      rfl
    rw [out, glue]
    refine ⟨w, leHost_refl w, settle_continue_edits_typed edits (by rw [gid]; exact Option.isSome_iff_exists.mpr ⟨ty, declared⟩) ?_⟩
    obtain ⟨t, ht⟩ : ∃ t, ((m.emit events).update g).fiber? target = some t := by
      obtain ⟨t, member, same⟩ := List.mem_map.mp ((ready.machine.wide.fibers target).mp pre)
      refine ⟨t, ?_⟩
      rw [← same]
      exact rfiber?_of_mem ready.machine.wide.fiberIds member
    have recorded := configTyped_interruptRecord ready ht (some target) .empty
    simpa only [edits, applyFiberEdits, List.foldl, applyFiberEdit, ht, interruptRecord,
      rfiber?_id ht, List.nil_append, List.append_assoc, List.singleton_append] using recorded
  | none =>
    rw [ht0]
    dsimp only
    by_cases exited : t0.exit.isSome = true
    · rw [if_pos exited]
      have out : FiberAction.outcomeOf m false = .continue_ := by
        unfold FiberAction.outcomeOf
        rw [ev.live]
        rfl
      rw [out]
      exact ev.settle_continue _ (ev.answer_typed hc (by rw [hc]; rfl)
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) .unit (fun _ _ => rfl))
    · rw [if_neg exited]
      obtain ⟨skip, hlink⟩ := scopeLinkFiber_open root .fiberRunIn scope target m.state hentry
      let s : Stores := {m.state with
        scopes := (m.state.scopes.addFinalizer scope m.state.nextName (.interruptFiber target skip)).1
        nextName := m.state.nextName + 1}
      let events : List (RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx RProgram Unit) :=
        [.scopeLinked .fiberRunIn scope m.state.nextName target]
      let M : RState := ({m with state := s} : RState).emit events
      let edits : List (FiberEdit Err Defect FiberId Ann) :=
        [.observe target (.dropScopeFinalizer scope m.state.nextName)]
      rw [show (interpRAt root.program m.completedExits).scopeLinkFiber .fiberRunIn scope target m.state =
        some (s, m.state.nextName) from hlink]
      have typedQ := configTyped_cons_link (mode := .fiberRunIn) (interruptor := some target)
        (extra := .empty) ev.typed live (by rw [ht₁]; rfl)
      obtain ⟨w', ord, typedL⟩ := link_preserves root rootTy .fiberRunIn scope target (some target)
        .empty w (m.update f) (.deliver f.id y :: rest) ev.live typedQ
      have exited₁ : ¬ t₁.exit.isSome = true := by rw [← sameExit]; exact exited
      have linkEq := linkScope_open (M := m.update f) (interruptor := some target)
        (extra := .empty) root hentry closed ht₁ exited₁ hlink
      simp only [driveStep, linkEq, List.nil_append] at typedL
      let t' : RFiber := {t₁ with observers := t₁.observers ++ [.dropScopeFinalizer scope m.state.nextName]}
      have found₁ : (M.update f).fiber? t₁.id = some t₁ := by
        rw [rfiber?_id ht₁]
        exact ht₁
      have found' : ((M.update f).update t').fiber? t₁.id = some t' :=
        rfiber?_update_self found₁ rfl
      have typedL' : ConfigTyped root rootTy w' ((M.update f).update t') (.deliver f.id y :: rest) := typedL
      have shrunk := configTyped_shrinkObservers (x := t') typedL' found' t₁.observers
        (fun _ ho => List.mem_append_left _ ho)
      rw [rupdate_rupdate _ (show t₁.id = t'.id from rfl),
        rupdate_self found₁ (by simpa only [rupdate_ids] using typedL'.machine.wide.fiberIds)] at shrunk
      have ev' : Evaluating root rootTy w' M rest f y := ⟨shrunk, ev.stale, ev.running, ev.live⟩
      have code := ev'.answer_typed hc (by rw [hc]; rfl)
        (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ _ _ h => nomatch h) .unit (fun _ _ => rfl)
      obtain ⟨g, gid, glue, ready⟩ := ev'.prepare_continue _ code edits
      change SettlesTyped root rootTy w f.id rest
        (prepareIterR ⟨M, {f with frame := {f.frame with current := next .unit}}, y,
          FiberAction.outcomeOf M false, [], edits⟩)
      have out : FiberAction.outcomeOf M false = .continue_ := by
        unfold FiberAction.outcomeOf
        rw [ev'.live]
        rfl
      rw [out, glue]
      refine ⟨w', ord, settle_continue_edits_typed edits (by
        rw [gid]
        exact isSome_extends ord.1.2.1 (Option.isSome_iff_exists.mpr ⟨ty, declared⟩)) ?_⟩
      have added := configTyped_observe ready target (.dropScopeFinalizer scope m.state.nextName)
        (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) (fun _ _ => by
          show (M.update g).state.ScopeLive scope
          rw [← ready.machine.wide.state]
          exact scopeLive_mono ord.1 hlive)
      exact added

end Effect4.Program.Typed
