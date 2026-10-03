import Effect4.Laws.Program.Typed.Commands.Bookkeeping

/-!
# Laws.Program.Typed.Commands.Finish — `evaluate`, `resume` and `finish`

Wave 2's second command group (seat D3). `evaluate` starts an idle fiber (`Machine/Fibers.lean`
`:1849-1856`): the fiber runs, and the queued `loop` reads the code `LiveCode` typed while it was
idle. `resume` (`:1865-1878`) unparks a fiber on its guard token with the answer code the queue's
payload types at the token's declaration (`ResumeOk`), and the saved stack the active park typed
(`ActiveDelivery`) takes that type. Neither command has a halting arm.

`finish` (`:1983-1988`, `exitFiber` `:1772-1803`) and `exitDone` (`:1967-1970`) were false as
stated before decisions row 134 (c) (seat D3, `E4-TYPED-CE-027`: the children clause installs the
middleware program over a stack nothing typed against the exit, and the store clause clears the
stack of a published fiber whose current code may be a race registration marker). Row 134 (c)
adds the clause the loop already keeps: the saved stack of an exited fiber, and of a fiber a
queued `finish` names, is empty (`SchedulerState.exitedStack`, `CommandDeliveryOk`'s `finish`
case). With it the middleware's program is typed at the fiber's declaration over the empty stack
(`middlewareCode_typed`), publishing and clearing change no stack (`configTyped_publish`,
`configTyped_cleared`), and each stored observer fires typed (`observerCommandOk_of_stored`).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-- Typed code is never a race registration marker: the marker's row has `False` as its pre. -/
theorem raceRegistrationR_typed {root : ProgramSource} {w : World} {ty : EffTy} {p : RProgram}
    (h : TypedProg root w ty p) : raceRegistrationR p = none := by
  cases p with
  | pure _ => rfl
  | vis op k =>
    cases op with
    | inl _ => rfl
    | inr fop =>
      cases fop with
      | raceRegister race =>
        obtain ⟨_, pre, _⟩ := TypedProg.fiber_inv h (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
        exact absurd pre id
      | _ => rfl

/-- **M5's load connector, its marker premise discharged** (decisions rows 148, 153 (b)): the root
code's typing makes it no race registration marker (`raceRegistrationR_typed`), so
`load_typed_of_denotesTyped` needs only the fundamental property and the checker's verdict. Placed
here, after the marker fact, since `Finish` imports `Assembly`. -/
theorem load_typed_of_denotesTyped_typed (root : ProgramSource) (rootTy : EffTy)
    (fuel compileFuel : Nat) (denotes : DenotesTyped root)
    (checked : Program.typeOfProgram root.signature root.program = some rootTy) :
    ∃ w, MachineTyped root rootTy w (loadR root.program fuel compileFuel) := by
  have wf := layerRefsWF_of_typeOf checked
  have typed : effTy root.signature [] (Eff.expandIn root.program root.program) = some rootTy := by
    rw [Eff.expandIn_self]
    unfold Program.typeOfProgram at checked
    split at checked
    · exact checked
    · cases checked
  have rootTyped := denotes wf (initialWorld rootTy root.sig.serviceTy) rfl (rootPoint compileFuel)
    root.program rootTy rfl
    ⟨root.program, [], rfl, Conform.Effect4.Typing.effTy_ok typed _, envTyped_nil _,
      fun _ h => nomatch h⟩
  exact load_typed_of_denotesTyped root rootTy fuel compileFuel denotes
    (raceRegistrationR_typed rootTyped) checked

/-- M5's proposition from the connector: its lawful and closed-row premises are not read. -/
theorem loadsTyped_of_denotesTyped_typed (root : ProgramSource) (rootTy : EffTy)
    (fuel compileFuel : Nat) (denotes : DenotesTyped root) :
    LoadsTyped root rootTy fuel compileFuel := fun _ checked _ =>
  load_typed_of_denotesTyped_typed root rootTy fuel compileFuel denotes checked

/-- **The typed load on the layer-free fragment**: a checked program none of whose nodes is a
`provideLayer` loads into `J` (`denotesTyped_of_layerFree`, then the load connector). -/
theorem loadsTyped_of_layerFree (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat)
    (h : LayerFree root.program) : LoadsTyped root rootTy fuel compileFuel :=
  loadsTyped_of_denotesTyped_typed root rootTy fuel compileFuel (denotesTyped_of_layerFree root h)

/-- A queued `loop` or `deliver` names an active fiber (`CommandAuthorityR`), so no queued command
reads the code of a fiber that is not running. -/
theorem not_readsCode_idle {root : ProgramSource} {w : World} {m : RState} {q : List RCmd}
    (queue : QueueOk root w m q) {f : RFiber} (hf : m.fiber? f.id = some f)
    (idle : f.running = false) : ¬ ReadsCode f.id q := by
  rintro ⟨y, r | r⟩
  · obtain ⟨g, hg, running, _⟩ := queue.authority _ r
    rw [hf] at hg
    cases hg
    rw [idle] at running
    cases running
  · obtain ⟨g, hg, running, _⟩ := queue.authority _ r
    rw [hf] at hg
    cases hg
    rw [idle] at running
    cases running

/-- A queued command's owner is active, so a fiber that is not running owns none. -/
theorem not_owner_idle {root : ProgramSource} {w : World} {m : RState} {q : List RCmd}
    (queue : QueueOk root w m q) {f : RFiber} (hf : m.fiber? f.id = some f)
    (idle : f.running = false) : f.id ∉ q.filterMap (Guard.commandOwner m) := by
  intro member
  obtain ⟨c, hc, owner⟩ := List.mem_filterMap.mp member
  have auth := queue.authority c hc
  have active : ∀ id, Guard.ActiveAt m id → id ≠ f.id := by
    rintro id ⟨g, hg, running, _⟩ rfl
    rw [hf] at hg
    cases hg
    rw [idle] at running
    cases running
  cases c with
  | loop fiber _ => cases owner; exact active _ auth rfl
  | deliver fiber _ => cases owner; exact active _ auth rfl
  | finish fiber _ => cases owner; exact active _ auth rfl
  | afterInterrupt fiber _ _ => cases owner; exact active _ auth rfl
  | closeParAwait fiber _ _ => cases owner; exact active _ auth rfl
  | raceCancel _ fiber _ _ _ => cases owner; exact active _ auth rfl
  | registrationDone raceId _ =>
    obtain ⟨race, g, found, hg, running, _⟩ := auth
    simp only [Guard.commandOwner, found, Option.map_some, Option.some.injEq] at owner
    rw [owner, hf] at hg
    cases hg
    rw [idle] at running
    cases running
  | evaluate _ => cases owner
  | resume _ _ _ => cases owner
  | launch _ => cases owner
  | enrollRace _ _ => cases owner
  | interruptTarget _ _ _ => cases owner
  | trackChild _ _ => cases owner
  | observe _ _ _ => cases owner
  | exitDone _ => cases owner
  | link _ _ _ _ _ => cases owner
  | drainDue => cases owner
  | wake _ _ => cases owner

/-! ## `evaluate` (no halting arm) -/

/-- **`evaluate` keeps `I`** at the same world: an idle fiber starts, and the queued `loop` reads
the code `LiveCode` typed. -/
theorem evaluate_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    StepPreserves root rootTy (.evaluate id) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  simp only [driveStep]
  cases hfound : m.fiber? id with
  | none => exact tail
  | some f =>
    dsimp only
    by_cases skip : (f.exit.isSome || f.running || f.parked != .notParked) = true
    · rw [if_pos skip]
      exact tail
    · rw [if_neg skip]
      simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not] at skip
      obtain ⟨⟨noExit, notRunning⟩, notParked⟩ := skip
      have idle : f.running = false := Bool.eq_false_iff.mpr notRunning
      have live : f.exit = none := by
        cases hx : f.exit with
        | none => rfl
        | some _ =>
          rw [hx] at noExit
          exact absurd rfl noExit
      have fid : f.id = id := rfiber?_id hfound
      have hf : m.fiber? f.id = some f := by rw [fid]; exact hfound
      have hmem : f ∈ m.fibers := rfiber?_mem hf
      let g : RFiber := { f with running := true, currentOpCount := 0 }
      have old := typed.machine.fiber hmem
      have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
      have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
      have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
      have gp : g.parked = .notParked := notParked
      have fresh : FiberTyped root w (m.update g) g :=
        ⟨runFiberOk_congr moved.ok rfl rfl rfl rfl rfl rfl rfl, moved.delivery, moved.below,
          moved.pendingShape, (fun hp => absurd gp hp), moved.parkedBelow,
          (fun hx => by rw [show g.exit = f.exit from rfl, live] at hx; cases hx),
          (fun hx => by rw [show g.exit = f.exit from rfl, live] at hx; cases hx),
          moved.deferredCause, moved.pendingOwner, moved.observers, moved.registration,
          (fun _ hr => by cases hr), moved.tokens, moved.raceObservers, moved.targetsBelow,
          moved.observersBelow, moved.children⟩
      have noRequest : ∀ token r, requestOfR (m.update g) g.id token = some r →
          requestOfR m f.id token = some r := by
        intro token r hr
        have off : g.parked ≠ .withGuard token := by
          rw [gp]
          exact fun h => nomatch h
        rw [requestOfR_of_not_parked look off] at hr
        cases hr
      have edited := configTyped_rupdate_gen (g := g) tail hf rfl (PendingWeaker.refl _) rfl
        (fun p => p) (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
        (fun c _ h => commandAuthority_idle (g := g) hf rfl idle live c h)
        (fun _ reads => absurd reads (not_readsCode_idle (f := f) tail.queue hf idle)) fresh
      have head : HeadOk root w (m.update g) (.loop id false) rest := by
        refine ⟨trivial, ⟨g, by rw [← fid]; exact look, rfl, notParked⟩, trivial, ?_, trivial,
          (fun _ h => nomatch h), (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h),
          (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h),
          (fun _ _ _ h => nomatch h)⟩
        intro o howner
        cases howner
        have same : Guard.commandOwner (Code := RProgram) (m.update g) = Guard.commandOwner m := by
          funext c
          cases c with
          | registrationDone raceId yielding => rfl
          | _ => rfl
        rw [same, ← fid]
        exact not_owner_idle tail.queue hf idle
      have readLoop : ReadCode root w (m.update g) (.loop id false :: rest) := by
        intro x hx running reads marker ty declared
        rcases mem_rupdate hx with rfl | ⟨hold, hne⟩
        · exact Or.inl (codeOk_races (racesKept_of_eq (m := m) fun _ => rfl)
            (old.code live idle marker notParked ty declared))
        · obtain ⟨y, r⟩ := reads
          refine (edited.code x hx running ⟨y, ?_⟩ marker ty declared).cons fun y' h => ?_
          · rcases r with r | r
            · rcases List.mem_cons.mp r with h | h
              · cases h
                exact absurd fid.symm hne
              · exact Or.inl h
            · rcases List.mem_cons.mp r with h | h
              · cases h
              · exact Or.inr h
          · cases h
      exact configTyped_emit ⟨edited.machine, readLoop, queueOk_cons head edited.queue⟩ _

/-! ## `resume` (no halting arm) -/

/-- Filtering out the parks of one token finds no park the old list did not. -/
theorem pendingWeaker_filter (l : List RPending) (t0 : Nat) :
    PendingWeaker l (l.filter fun p => decide (p.token ≠ t0)) := by
  intro token p hp
  induction l with
  | nil => cases hp
  | cons x rest ih =>
    rw [List.filter_cons] at hp
    rw [List.find?_cons]
    by_cases hk : decide (x.token ≠ t0) = true
    · rw [if_pos hk, List.find?_cons] at hp
      by_cases hx : x.token = token
      · rw [decide_eq_true hx] at hp ⊢
        exact hp
      · rw [decide_eq_false hx] at hp ⊢
        exact ih hp
    · rw [if_neg hk] at hp
      by_cases hx : x.token = token
      · have found := List.find?_some hp
        have keep := (List.mem_filter.mp (List.mem_of_find?_eq_some hp)).2
        have x0 : x.token = t0 := Decidable.of_not_not (fun h => hk (decide_eq_true h))
        have ptok : p.token = token := of_decide_eq_true found
        have pne : p.token ≠ t0 := of_decide_eq_true keep
        exact absurd (ptok.trans (hx.symm.trans x0)) pne
      · rw [decide_eq_false hx]
        exact ih hp

/-- **The `resume` step from a typed rest and an answer typed when it lands**: the fiber parked on
the token is unparked with the answer code typed at the token's declaration (`ResumeOk`, needed
only when the fiber is parked there), over the stack its park typed there (`ActiveDelivery`).
`resume_preserves` takes the answer's typing from the queue's payload; the answer edit
(`Edits.lean`) from the decision's admission, which types a parked fiber's answer only. -/
theorem resume_step {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} (tail : ConfigTyped root rootTy w m rest) {id : FiberId} {token : Nat}
    {answer : RProgram}
    (payload : (∃ f, m.fiber? id = some f ∧ f.parked = .withGuard token) →
      Contracts.ResumeOk (TypedProg root) w id token answer) :
    ConfigTyped root rootTy w
      (letI := termEvaluatorFor root.program
       driveStep (interpR root.program) m (.resume id token answer) rest).1
      (letI := termEvaluatorFor root.program
       driveStep (interpR root.program) m (.resume id token answer) rest).2 := by
  simp only [driveStep]
  cases hfound : m.fiber? id with
  | none => exact tail
  | some t =>
    dsimp only
    cases hp : t.parked with
    | notParked => exact tail
    | withGuard parkedToken =>
      dsimp only
      by_cases same : parkedToken = token
      · rw [if_pos same]
        subst same
        have tid : t.id = id := rfiber?_id hfound
        have hf : m.fiber? t.id = some t := by rw [tid]; exact hfound
        have hmem : t ∈ m.fibers := rfiber?_mem hf
        have old := tail.machine.fiber hmem
        have idle : t.running = false := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
        have live : t.exit = none := by
          cases hx : t.exit with
          | none => rfl
          | some _ =>
            have stopped := (old.exited (by rw [hx]; rfl)).1
            rw [hp] at stopped
            cases stopped
        obtain ⟨tin, final, declaredToken, declaredFinal, stackOk, prov⟩ :=
          old.delivery parkedToken hp
        have answerTyped : TypedProg root w tin answer :=
          payload ⟨t, hfound, hp⟩ tin (by rw [← tid]; exact declaredToken)
        have shape : ∃ p0, t.pending = [p0] ∧ p0.token = parkedToken := by
          have s := old.pendingShape
          unfold Guard.PendingShape at s
          rw [hp] at s
          exact s
        let g : RFiber := { t with
          parked := .notParked
          pending := t.pending.filter fun p => decide (p.token ≠ parkedToken)
          frame := { t.frame with current := answer } }
        have gp : g.parked = .notParked := rfl
        have gx : g.exit = none := live
        have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
        have view : ObsView m (m.update g) :=
          obsView_rupdate (g := g) hf rfl (pendingWeaker_filter t.pending parkedToken)
        have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
        have provG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
        have notMarker : raceRegistrationR g.frame.current = none :=
          raceRegistrationR_typed answerTyped
        have emptied : g.pending = [] := by
          obtain ⟨p0, single, hp0⟩ := shape
          show (t.pending.filter fun p => decide (p.token ≠ parkedToken)) = []
          have drop : ¬ (decide (p0.token ≠ parkedToken) = true) := by
            rw [hp0]
            exact fun h => of_decide_eq_true h rfl
          rw [single, List.filter_cons, if_neg drop, List.filter_nil]
        have frameOk : ∀ ty, w.Γ g.id = some ty →
            ∃ tin, PositionStack root w tin ty g.frame.stack ∧ InterruptProvenance g.frame := by
          intro ty declared
          obtain ⟨tin', stack', _⟩ := old.position declared
          exact ⟨tin', stack', provG⟩
        have exitedG : g.exit.isSome = true → g.parked = .notParked ∧ g.running = false := by
          intro hx
          rw [gx] at hx
          cases hx
        have registrationG : ∀ raceId, raceRegistrationR g.frame.current = some raceId →
            ∃ race resultTy, (m.update g).race? raceId = some race ∧ race.host = g.id ∧
              w.Θ race.host race.token = some resultTy ∧ StackReply root w (m.update g) g resultTy := by
          intro raceId marker
          rw [notMarker] at marker
          cases marker
        have codeG : g.exit = none → g.running = false → raceRegistrationR g.frame.current = none →
            g.parked = .notParked → ∀ ty, w.Γ g.id = some ty →
              CodeOk root w (m.update g) g.id ty g.frame := by
          intro _ _ _ _ ty declared
          have same : ty = final := by
            have both : w.Γ t.id = some ty := declared
            rw [declaredFinal] at both
            cases both
            rfl
          subst same
          exact ⟨tin, answerTyped, hostStack_races (racesKept_of_eq view.races) stackOk, provG⟩
        have fresh : FiberTyped root w (m.update g) g :=
          { ok := ⟨⟨frameOk⟩, fun q hq => moved.ok.c1 q (List.mem_filter.mp hq).1, moved.ok.c2,
              moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
            delivery := fun _ h => nomatch h
            below := moved.below
            pendingShape := emptied
            parkedIdle := fun h => absurd gp h
            parkedBelow := fun _ h => nomatch h
            exited := exitedG
            exitedStack := fun hx => by rw [gx] at hx; cases hx
            deferredCause := moved.deferredCause
            pendingOwner := fun q hq => moved.pendingOwner q (List.mem_filter.mp hq).1
            observers := moved.observers
            registration := registrationG
            code := codeG
            tokens := fun _ h => nomatch h
            raceObservers := moved.raceObservers
            targetsBelow := fun q hq => moved.targetsBelow q (List.mem_filter.mp hq).1
            observersBelow := moved.observersBelow
            children := moved.children }
        have noRequest : ∀ tok r, requestOfR (m.update g) g.id tok = some r →
            requestOfR m t.id tok = some r := by
          intro tok r hr
          have off : g.parked ≠ .withGuard tok := by
            rw [gp]
            exact fun h => nomatch h
          rw [requestOfR_of_not_parked look off] at hr
          cases hr
        have notRunning : g.running = true → ReadsCode g.id rest →
            raceRegistrationR g.frame.current = none → ∀ ty, w.Γ g.id = some ty →
              SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty g.frame := by
          intro hrun
          rw [show g.running = t.running from rfl, idle] at hrun
          cases hrun
        have edited := configTyped_rupdate_gen (g := g) tail hf rfl
          (pendingWeaker_filter t.pending parkedToken) rfl (fun p => ⟨p.recorded, p.deferred⟩)
          (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
          (fun c _ h => commandAuthority_idle (g := g) hf rfl idle live c h) notRunning fresh
        exact configTyped_cons_evaluate (configTyped_emit edited _) id
      · rw [if_neg same]
        exact tail

/-- **`resume` keeps `I`** at the same world (no halting arm): `resume_step` with the answer typed
by the queue's payload. -/
theorem resume_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat)
    (answer : RProgram) : StepPreserves root rootTy (.resume id token answer) := by
  intro w m rest _ typed
  exact ⟨w, leHost_refl w,
    resume_step (configTyped_tail typed) fun _ => typed.queue.payload _ List.mem_cons_self⟩

/-! ## `exitDone` and `finish` (decisions row 134 (c)) -/

/-- The owner a queued command's head holds is free in the rest of the queue. -/
theorem owner_free {root : ProgramSource} {w : World} {m : RState} {c : RCmd} {rest : List RCmd}
    (queue : QueueOk root w m (c :: rest)) {o : FiberId} (owner : Guard.commandOwner m c = some o) :
    o ∉ rest.filterMap (Guard.commandOwner m) := by
  have nodup := queue.owners
  rw [List.filterMap_cons, owner] at nodup
  exact (List.nodup_cons.mp nodup).1

/-- **Clearing an exited fiber keeps `I`** (`RunFiber.cleared`, `Machine/Fibers.lean:1757`): its
observers, stack, children and context are emptied. The stack is already empty (decisions row 134
(c), `SchedulerState.exitedStack`), so the frame that `RegistrationState` and the position read is
unchanged; no observer is left to type, and the empty context's services fit. -/
theorem configTyped_cleared {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {f : RFiber}
    (hf : m.fiber? f.id = some f) (exited : f.exit.isSome = true) :
    ConfigTyped root rootTy w (m.update (f.cleared (interpR root.program))) q := by
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := typed.machine.fiber hmem
  have empty : f.frame.stack = [] := old.exitedStack exited
  have stopped := old.exited exited
  let g : RFiber := f.cleared (interpR root.program)
  have gframe : g.frame = f.frame := by
    show { f.frame with stack := [] } = f.frame
    rw [← empty]
  have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have fresh : FiberTyped root w (m.update g) g :=
    { ok := ⟨⟨fun ty d => by
            obtain ⟨tin, st, pv⟩ := old.position d
            exact ⟨tin, by rw [gframe]; exact st, by rw [gframe]; exact pv⟩⟩,
          moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4, servicesFit_empty w⟩
      delivery := fun token hp => by
        obtain ⟨tin, final, d1, d2, st, pv⟩ := moved.delivery token hp
        exact ⟨tin, final, d1, d2, by rw [gframe]; exact st, by rw [gframe]; exact pv⟩
      below := moved.below
      pendingShape := moved.pendingShape
      parkedIdle := moved.parkedIdle
      parkedBelow := moved.parkedBelow
      exited := moved.exited
      exitedStack := fun _ => by rw [gframe]; exact empty
      deferredCause := by rw [gframe]; exact moved.deferredCause
      pendingOwner := moved.pendingOwner
      observers := fun _ h => nomatch h
      registration := fun raceId marker => by
        rw [gframe] at marker
        obtain ⟨race, resultTy, found, host, token, reply⟩ := moved.registration raceId marker
        exact ⟨race, resultTy, found, host, token,
          stackReply_congr (f := f) (racesKept_of_eq fun _ => rfl) rfl gframe reply⟩
      code := fun hx => by
        have none' : f.exit = none := hx
        rw [none'] at exited
        cases exited
      tokens := moved.tokens
      raceObservers := fun _ _ _ _ h => nomatch h
      targetsBelow := moved.targetsBelow
      observersBelow := fun _ h => nomatch h
      children := fun _ h => nomatch h }
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  exact configTyped_rupdate_gen (g := g) typed hf rfl (PendingWeaker.refl _)
    (by rw [gframe]) (fun pv => by rw [gframe]; exact pv)
    (fun k hk => Or.inl (fiberKeys_internal hmem (List.mem_append_right _ hk)))
    (fun token r hr => by
      rw [requestOfR_of_not_parked look
        (by rw [show g.parked = f.parked from rfl, stopped.1]; exact fun h => nomatch h)] at hr
      cases hr)
    (fun c _ h => commandAuthority_view (ctlView_rupdate (g := g) hf rfl rfl rfl rfl gframe)
      view.races c h)
    (fun hrun => by rw [show g.running = f.running from rfl, stopped.2] at hrun; cases hrun)
    fresh

/-- **`exitDone` keeps `I`** at the same world: the exited fiber it names is cleared
(`configTyped_cleared`). -/
theorem exitDone_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    StepPreserves root rootTy (.exitDone id) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  simp only [driveStep]
  cases hfound : m.fiber? id with
  | none => exact tail
  | some f =>
    dsimp only
    obtain ⟨found, hfound', exited⟩ : ∃ found, m.fiber? id = some found ∧
        found.exit.isSome = true := typed.queue.authority _ List.mem_cons_self
    rw [hfound] at hfound'
    cases hfound'
    have hf : m.fiber? f.id = some f := by rw [rfiber?_id hfound]; exact hfound
    exact configTyped_cleared tail hf exited

/-- A queued command's registration tail holds against the whole queue
(`Guard.RegistrationQueue.registrationQueue_member`, at the reference machine's commands). -/
theorem registrationTail_member {q : List RCmd} (queue : Guard.RegistrationQueue.RegistrationQueue q)
    {c : RCmd} (member : c ∈ q) : Guard.RegistrationQueue.RegistrationTail c q := by
  induction q with
  | nil => cases member
  | cons first rest ih =>
    have widen : ∀ d : RCmd, Guard.RegistrationQueue.RegistrationTail d rest →
        Guard.RegistrationQueue.RegistrationTail d (first :: rest) := by
      intro d hd
      cases d with
      | launch race =>
        obtain ⟨y, hy⟩ := hd
        exact ⟨y, List.mem_cons_of_mem _ hy⟩
      | enrollRace race child =>
        obtain ⟨y, hy⟩ := hd
        exact ⟨y, List.mem_cons_of_mem _ hy⟩
      | _ => trivial
    rcases List.mem_cons.mp member with rfl | tail
    · exact widen _ queue.1
    · exact widen _ (ih queue.2 tail)

/-- **A queued command's authority survives an edit of a live fiber that owns no queued
command.** The commands that read an active fiber name it as their owner; a queued `launch` or
`enrollRace` names a race whose `registrationDone` is queued (`RegistrationQueue`), whose owner is
the race's host; `exitDone` reads an exited fiber, which `t` is not. -/
theorem commandAuthority_unowned {m : RState} {t g : RFiber} (ht : m.fiber? t.id = some t)
    (hid : g.id = t.id) (live : t.exit = none) {q : List RCmd}
    (free : t.id ∉ q.filterMap (Guard.commandOwner m))
    (reg : Guard.RegistrationQueue.RegistrationQueue q) (c : RCmd) (hc : c ∈ q)
    (h : CommandAuthorityR m c) : CommandAuthorityR (m.update g) c := by
  have owned : ∀ {id}, Guard.commandOwner m c = some id → id ≠ t.id := by
    intro id owner same
    apply free
    rw [← same]
    exact List.mem_filterMap.mpr ⟨c, hc, owner⟩
  have keep : ∀ {id : FiberId} {f : RFiber}, m.fiber? id = some f → id ≠ t.id →
      (m.update g).fiber? id = some f := by
    intro id f hf hne
    rw [rfiber?_update_other (by rw [hid]; exact hne)]
    exact hf
  have active : ∀ {id}, Guard.commandOwner m c = some id → Guard.ActiveAt m id →
      Guard.ActiveAt (m.update g) id := by
    intro id owner act
    obtain ⟨f, hf, running, parked⟩ := act
    exact ⟨f, keep hf (owned owner), running, parked⟩
  have hostActive : ∀ {raceId race}, m.race? raceId = some race →
      (∃ y, .registrationDone raceId y ∈ q) → Guard.ActiveAt m race.host →
        Guard.ActiveAt (m.update g) race.host := by
    intro raceId race found ⟨y, hy⟩ act
    have hne : race.host ≠ t.id := by
      intro same
      apply free
      rw [← same]
      refine List.mem_filterMap.mpr ⟨.registrationDone raceId y, hy, ?_⟩
      simp only [Guard.commandOwner, found, Option.map_some]
    obtain ⟨f, hf, running, parked⟩ := act
    exact ⟨f, keep hf hne, running, parked⟩
  cases c with
  | loop fiber _ => exact active rfl h
  | deliver fiber _ => exact active rfl h
  | finish fiber _ => exact active rfl h
  | afterInterrupt fiber _ _ => exact active rfl h
  | closeParAwait fiber _ _ => exact active rfl h
  | raceCancel _ fiber _ _ _ => exact active rfl h
  | registrationDone raceId _ =>
    obtain ⟨race, f, found, hf, running, parked, marker⟩ := h
    have hne : race.host ≠ t.id := owned (by simp only [Guard.commandOwner, found, Option.map_some])
    exact ⟨race, f, found, keep hf hne, running, parked, marker⟩
  | launch raceId =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, found, hostActive found (registrationTail_member reg hc) act⟩
  | enrollRace raceId _ =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, found, hostActive found (registrationTail_member reg hc) act⟩
  | exitDone fiber =>
    obtain ⟨f, hf, exited⟩ := h
    have hne : fiber ≠ t.id := by
      intro same
      rw [same, ht] at hf
      cases hf
      rw [live] at exited
      cases exited
    exact ⟨f, keep hf hne, exited⟩
  | evaluate _ => trivial
  | resume _ _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- A countdown correlation weakens along its incoming condition. -/
theorem countdownAt_weaken {w : World} {m : RState} {waiter : FiberId} {token : Nat}
    {incoming incoming' : Ty → Ty → Prop} (weaken : ∀ a e, incoming a e → incoming' a e)
    (h : CountdownAt w m waiter token incoming) : CountdownAt w m waiter token incoming' := by
  unfold CountdownAt at h ⊢
  revert h
  cases m.fiber? waiter with
  | none => exact fun _ => trivial
  | some fiber =>
    dsimp only
    cases fiber.pending.find? (fun pending => pending.token = token) with
    | none => exact fun _ => trivial
    | some pending =>
      dsimp only
      rintro ⟨a, e, ty, payload, inc⟩
      exact ⟨a, e, ty, payload, weaken a e inc⟩

/-- **A stored observer fires typed** on its source's exit: the stored correlation reads the
source's declared columns, and the exit is admitted at the source's declaration. -/
theorem observerCommandOk_of_stored {root : ProgramSource} {w : World} {m : RState}
    {source : FiberId} {exit : ExitV} (typedExit : ∀ ty, w.Γ source = some ty → ExitOk w ty exit)
    (o : Observer) (h : StoredObserverOk root w m source o) :
    ObserverCommandOk root w m source exit o := by
  cases o with
  | resumeAwait waiter token mode =>
    obtain ⟨sty, hΓ, hΘ⟩ := h
    exact ⟨sty, hΓ, hΘ, typedExit sty hΓ⟩
  | countdown waiter token =>
    refine countdownAt_weaken (fun a e cols => ?_) h
    obtain ⟨sty, hΓ, ha, he⟩ := cols
    exact exitOk_widen ha he (typedExit sty hΓ)
  | raceCallback raceId =>
    change (match m.race? raceId with
      | none => True
      | some race => ∃ resultTy, RacePayload root w race resultTy ∧
          (source ∈ race.state.live → FiberColumnsBelow w source resultTy.answer resultTy.error)) at h
    change match m.race? raceId with
      | none => True
      | some race => ∃ resultTy, RacePayload root w race resultTy ∧
          (source ∈ race.state.live → ExitOk w resultTy exit)
    revert h
    cases m.race? raceId with
    | none => exact fun _ => trivial
    | some race =>
      dsimp only
      rintro ⟨resultTy, payload, cols⟩
      refine ⟨resultTy, payload, fun hl => ?_⟩
      obtain ⟨sty, hΓ, ha, he⟩ := cols hl
      exact exitOk_widen ha he (typedExit sty hΓ)
  | dropScopeFinalizer scope key => exact h
  | untrackChild parent => trivial
  | callback key => trivial

/-- **The exit middleware's program is typed** at a fiber's declared type when the exit is
admitted there: `interruptAll` of the children, each declared (`fiberPre`; `J`'s `children`),
answers `unit`, then the exit (`restoreR`, `Laws/Program/InterpR.lean:62`). -/
theorem middlewareCode_typed (root : ProgramSource) {w : World} {ty : EffTy}
    (children : List FiberId) (declared : ∀ c ∈ children, (w.Γ c).isSome = true) {exit : ExitV}
    (hex : ExitOk w ty exit) :
    TypedProg root w ty (restoreR (fiberValR (.interruptAll children none) rfl) (.restore exit)) :=
  seqGuard_typed root (mid := EffTy.pure .unit)
    (TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) () declared (fun _ _ _ post => unitAnswer_typed root post))
    (subN_never _) (fun _ o _ _ => .pure (strongExit_mono _ _ _ _ o hex))

/-- The head facts of a `drainDue`: it reads nothing, owns nothing, carries no key. -/
theorem headOk_drainDue (root : ProgramSource) (w : World) (m : RState) (q : List RCmd) :
    HeadOk root w m .drainDue q :=
  ⟨trivial, trivial, trivial, (fun _ h => nomatch h), trivial, (fun _ h => nomatch h),
    (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
    (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- The head facts of an `exitDone` naming an exited fiber. -/
theorem headOk_exitDone (root : ProgramSource) (w : World) (m : RState) (q : List RCmd)
    {id : FiberId} {f : RFiber} (hf : m.fiber? id = some f) (exited : f.exit.isSome = true) :
    HeadOk root w m (.exitDone id) q :=
  ⟨trivial, ⟨f, hf, exited⟩, trivial, (fun _ h => nomatch h), trivial, (fun _ h => nomatch h),
    (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
    (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩

/-- A head command that is neither `loop` nor `deliver` joins a typed configuration. -/
theorem configTyped_cons_head {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} {c : RCmd} (typed : ConfigTyped root rootTy w m q) (head : HeadOk root w m c q)
    (noLoop : ∀ id y, c ≠ .loop id y) (noDeliver : ∀ id y, c ≠ .deliver id y) :
    ConfigTyped root rootTy w m (c :: q) :=
  ⟨typed.machine, readCode_cons noLoop noDeliver typed.code, queueOk_cons head typed.queue⟩

/-- **A fiber's observers fire typed**: one `observe` per observer joins the queue, each with its
command correlation, its keys below the token supply and no external request at them. -/
theorem configTyped_observes {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (source : FiberId) (exit : ExitV)
    (payload : (preds root).exit w (.fiber source) exit) (sourceBelow : source.value < m.nextId) :
    ∀ (obs : List Observer), (∀ o ∈ obs, ObserverCommandOk root w m source exit o) →
      (∀ o ∈ obs, ∀ key ∈ Guard.observerKeys o, key.2 < m.nextToken) →
      (∀ o ∈ obs, ∀ fiber token r, requestOfR m fiber token = some r →
        (fiber, token) ∉ Guard.observerKeys o) →
      (∀ o ∈ obs, ∀ raceId race, m.race? raceId = some race →
        (race.host, race.token) ∉ Guard.observerKeys o) →
      ConfigTyped root rootTy w m (obs.map (Cmd.observe source exit) ++ q)
  | [], _, _, _, _ => typed
  | o :: os, ok, below, freeKeys, raceFree => by
    have rest := configTyped_observes typed source exit payload sourceBelow os
      (fun x hx => ok x (List.mem_cons_of_mem _ hx))
      (fun x hx => below x (List.mem_cons_of_mem _ hx))
      (fun x hx => freeKeys x (List.mem_cons_of_mem _ hx))
      (fun x hx => raceFree x (List.mem_cons_of_mem _ hx))
    refine configTyped_cons_head rest ⟨payload, trivial, trivial, (fun _ h => nomatch h), trivial,
      below o List.mem_cons_self, freeKeys o List.mem_cons_self, ?_, (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), ?_⟩
      (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    · intro src e x hx
      cases hx
      exact ⟨sourceBelow, ok o List.mem_cons_self⟩
    · intro src e x hx
      cases hx
      exact raceFree o List.mem_cons_self

/-- **Publishing a finishing fiber's exit keeps `I`** (`RunFiber.publish`, `Machine/Fibers.lean`
`:1747`): the exit is written, the parks and the finalizing flag cleared, the fiber stopped. Its
stack is empty (decisions row 134 (c)), so `exitedStack` holds and the position is the empty
stack at the fiber's declaration; the exit is admitted there (the queue's payload, row 133). The
observer list is a parameter so that a caller may split on it first. -/
theorem configTyped_publish {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} (tail : ConfigTyped root rootTy w m rest) {f : RFiber}
    (hf : m.fiber? f.id = some f) (live : f.exit = none)
    (empty : f.frame.stack = []) {exit : ExitV}
    (exitF : ∀ ty, w.Γ f.id = some ty → ExitOk w ty exit)
    (freeF : f.id ∉ rest.filterMap (Guard.commandOwner m)) (obs : List Observer)
    (hobs : f.observers = obs) :
    ConfigTyped root rootTy w
      (m.update
        { f with
          running := false
          exit := some exit
          finalizing := none
          frame := { f.frame with deferredInterrupt := false }
          parked := .notParked
          pending := []
          observers := obs }) rest := by
  subst hobs
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := tail.machine.fiber hmem
  obtain ⟨final, declared⟩ : ∃ final, w.Γ f.id = some final :=
    Option.isSome_iff_exists.mp ((tail.machine.wide.fibers f.id).mpr (List.mem_map_of_mem hmem))
  obtain ⟨_, _, provF⟩ := old.position declared
  let p : RFiber :=
    { f with
      running := false
      exit := some exit
      finalizing := none
      frame := { f.frame with deferredInterrupt := false }
      parked := .notParked
      pending := [] }
  have provP : InterruptProvenance p.frame := ⟨provF.recorded, fun h => nomatch h⟩
  have view : ObsView m (m.update p) := obsView_rupdate (g := p) hf rfl (fun _ _ h => nomatch h)
  have look : (m.update p).fiber? p.id = some p := rfiber?_update_self hf rfl
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have fresh : FiberTyped root w (m.update p) p :=
    { ok := ⟨⟨fun ty _ => ⟨ty, by rw [show p.frame.stack = [] from empty]; exact .nil ty, provP⟩⟩,
          (fun _ h => nomatch h), (fun _ h => nomatch h), fun v hv => by
            injection hv with hv
            subst hv
            exact exitF, moved.ok.c4, moved.ok.c5⟩
      delivery := fun _ hp => nomatch hp
      below := moved.below
      pendingShape := rfl
      parkedIdle := fun _ => rfl
      parkedBelow := fun _ hp => nomatch hp
      exited := fun _ => ⟨rfl, rfl⟩
      exitedStack := fun _ => empty
      deferredCause := fun h => nomatch h
      pendingOwner := fun _ h => nomatch h
      observers := moved.observers
      registration := fun raceId marker => by
        obtain ⟨race, resultTy, found, host, token, reply⟩ := moved.registration raceId marker
        exact ⟨race, resultTy, found, host, token,
          stackReply_view (f := f) (racesKept_of_eq fun _ => rfl) rfl rfl (fun _ => provP) reply⟩
      code := fun hx => nomatch hx
      tokens := fun _ hp => nomatch hp
      raceObservers := moved.raceObservers
      targetsBelow := fun _ hp => nomatch hp
      observersBelow := moved.observersBelow
      children := moved.children }
  exact configTyped_rupdate_gen (g := p) tail hf rfl (fun _ _ h => nomatch h) rfl (fun _ => provP)
    (fun k hk => Or.inl (fiberKeys_internal hmem hk))
    (fun token r hr => by
      rw [requestOfR_of_not_parked look (fun h => nomatch h)] at hr
      cases hr)
    (fun c hc h => commandAuthority_unowned (g := p) hf rfl live freeF tail.queue.registration c hc h)
    (fun hrun => nomatch hrun) fresh

/-- **`finish` keeps `I`** at the same world (decisions row 134 (c)). The fiber's stack is empty
(`CommandDeliveryOk`'s `finish` clause) and its exit is admitted at its declaration (the queue's
payload, row 133). With the middleware installed and children tracked, the fiber re-enters with
the middleware's program (`middlewareCode_typed`) over the empty stack, finalizing the exit;
otherwise the exit is published (the stack stays empty, so `exitedStack` holds) and the fiber is
cleared at once (no observer, `configTyped_cleared`), or each observer fires typed
(`observerCommandOk_of_stored`) before `exitDone` and the due drain. -/
theorem finish_preserves (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (exit : ExitV) :
    StepPreserves root rootTy (.finish id exit) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  obtain ⟨f, hfound, running, parked⟩ : Guard.ActiveAt m id :=
    typed.queue.authority _ List.mem_cons_self
  have empty : f.frame.stack = [] := typed.queue.delivery _ List.mem_cons_self f hfound
  have payload : ∀ ty, w.Γ id = some ty → ExitOk w ty exit :=
    typed.queue.payload _ List.mem_cons_self
  have free : id ∉ rest.filterMap (Guard.commandOwner m) := owner_free typed.queue rfl
  have fid : f.id = id := rfiber?_id hfound
  have hf : m.fiber? f.id = some f := by rw [fid]; exact hfound
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have old := typed.machine.fiber hmem
  have live : f.exit = none := by
    cases hx : f.exit with
    | none => rfl
    | some _ =>
      have stopped := (old.exited (by rw [hx]; rfl)).2
      rw [running] at stopped
      cases stopped
  have freeF : f.id ∉ rest.filterMap (Guard.commandOwner m) := by rw [fid]; exact free
  have exitF : ∀ ty, w.Γ f.id = some ty → ExitOk w ty exit := by rw [fid]; exact payload
  obtain ⟨final, declared⟩ : ∃ final, w.Γ f.id = some final :=
    Option.isSome_iff_exists.mp ((typed.machine.wide.fibers f.id).mpr (List.mem_map_of_mem hmem))
  obtain ⟨_, _, provF⟩ := old.position declared
  simp only [driveStep]
  rw [hfound]
  dsimp only
  unfold exitFiber
  split
  · -- the children clause: the middleware's program over the empty stack
    let code := restoreR (fiberValR (.interruptAll f.children none) rfl) (.restore exit)
    let g : RFiber :=
      { f with
        running := false
        finalizing := some exit
        frame := { f.frame with deferredInterrupt := false, current := code } }
    have codeTyped : TypedProg root w final code :=
      middlewareCode_typed root f.children old.children (exitF final declared)
    have provG : InterruptProvenance g.frame := ⟨provF.recorded, fun h => nomatch h⟩
    have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
    have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
    have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
    have finalOf : ∀ ty, w.Γ g.id = some ty → ty = final := by
      intro ty d
      have both : w.Γ f.id = some ty := d
      rw [declared] at both
      cases both
      rfl
    have fresh : FiberTyped root w (m.update g) g :=
      { ok := ⟨⟨fun ty d => ⟨ty, by rw [show g.frame.stack = [] from empty]; exact .nil ty, provG⟩⟩,
            moved.ok.c1, fun v hv => by
              injection hv with hv
              subst hv
              exact exitF, moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
        delivery := fun token hp => by
          rw [show g.parked = f.parked from rfl, parked] at hp
          cases hp
        below := moved.below
        pendingShape := moved.pendingShape
        parkedIdle := fun _ => rfl
        parkedBelow := fun token hp => by
          rw [show g.parked = f.parked from rfl, parked] at hp
          cases hp
        exited := fun hx => by
          rw [show g.exit = f.exit from rfl, live] at hx
          cases hx
        exitedStack := fun hx => by
          rw [show g.exit = f.exit from rfl, live] at hx
          cases hx
        deferredCause := fun h => nomatch h
        pendingOwner := moved.pendingOwner
        observers := moved.observers
        registration := fun raceId marker => by
          rw [show g.frame.current = code from rfl, raceRegistrationR_typed codeTyped] at marker
          cases marker
        code := fun _ _ _ _ ty d => by
          rw [finalOf ty d]
          exact ⟨final, codeTyped, by rw [show g.frame.stack = [] from empty]; exact .nil final,
            provG⟩
        tokens := fun token hp => by
          rw [show g.parked = f.parked from rfl, parked] at hp
          cases hp
        raceObservers := moved.raceObservers
        targetsBelow := moved.targetsBelow
        observersBelow := moved.observersBelow
        children := moved.children }
    have edited := configTyped_rupdate_gen (g := g) tail hf rfl (PendingWeaker.refl _) rfl
      (fun _ => provG) (fun k hk => Or.inl (fiberKeys_internal hmem hk))
      (fun token r hr => by
        rw [requestOfR_of_not_parked look
          (by rw [show g.parked = f.parked from rfl, parked]; exact fun h => nomatch h)] at hr
        cases hr)
      (fun c hc h => commandAuthority_unowned (g := g) hf rfl live freeF tail.queue.registration
        c hc h)
      (fun hrun => nomatch hrun) fresh
    exact configTyped_emit (configTyped_cons_evaluate edited g.id) _
  · -- the store clause: publish, then clear at once or fire each observer
    unfold exitFiber.exitStore
    dsimp only
    cases hobs : f.observers with
    | nil =>
      have typed1 := configTyped_emit (configTyped_publish tail hf live empty exitF freeF [] hobs)
        [RunEvent.exited f.id exit]
      exact configTyped_cons_head (configTyped_cleared typed1 (rfiber?_update_self hf rfl) rfl)
        (headOk_drainDue _ _ _ _) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    | cons o os =>
      have typed1 := configTyped_emit
        (configTyped_publish tail hf live empty exitF freeF (o :: os) hobs)
        [RunEvent.exited f.id exit]
      have hp1 := rfiber?_update_self (m := m)
        (g :=
          { f with
            running := false
            exit := some exit
            finalizing := none
            frame := { f.frame with deferredInterrupt := false }
            parked := .notParked
            pending := []
            observers := o :: os }) hf rfl
      have pmem := rfiber?_mem hp1
      have pTyped := typed1.machine.fiber pmem
      have wide := typed1.machine.wide
      have base := configTyped_cons_head
        (configTyped_cons_head typed1 (headOk_drainDue _ _ _ _) (fun _ _ h => nomatch h)
          (fun _ _ h => nomatch h))
        (headOk_exitDone _ _ _ _ hp1 rfl) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
      have observed := configTyped_observes base f.id exit exitF pTyped.below (o :: os)
        (fun x hx => observerCommandOk_of_stored exitF x (pTyped.observers x hx))
        (fun x hx key hk => wide.keysBelow key
          (fiberKeys_internal pmem (List.mem_append_left _ (List.mem_flatMap.mpr ⟨x, hx, hk⟩))))
        (fun x hx fiber token r hr hk => wide.requestsOwned fiber token r hr
          (fiberKeys_internal pmem (List.mem_append_left _ (List.mem_flatMap.mpr ⟨x, hx, hk⟩))))
        (fun x hx r race hr => pTyped.raceObservers r race hr x hx)
      have regroup : ∀ (A : List RCmd) (x y : RCmd), A ++ (x :: y :: rest) = (A ++ [x, y]) ++ rest :=
        fun A x y => by rw [List.append_assoc]; rfl
      rw [regroup] at observed
      exact observed

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Ledger.step_evaluate :=
  @Effect4.Program.Typed.evaluate_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_resume :=
  @Effect4.Program.Typed.resume_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_exitDone :=
  @Effect4.Program.Typed.exitDone_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_finish :=
  @Effect4.Program.Typed.finish_preserves
-- `M6Ledger`'s report runs at the foot of the last command module, which sees every proof.
