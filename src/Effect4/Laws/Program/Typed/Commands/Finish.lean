import Effect4.Laws.Program.Typed.Commands.Bookkeeping

/-!
# Laws.Program.Typed.Commands.Finish — `evaluate`, `resume` and `finish`

Wave 2's second command group (seat D3). `evaluate` starts an idle fiber (`Machine/Fibers.lean`
`:1849-1856`): the fiber runs, and the queued `loop` reads the code `LiveCode` typed while it was
idle. `resume` (`:1865-1878`) unparks a fiber on its guard token with the answer code the queue's
payload types at the token's declaration (`ResumeOk`), and the saved stack the active park typed
(`ActiveDelivery`) takes that type. Neither command has a halting arm.

`finish` (`:1983-1988`, `exitFiber` `:1772-1803`) is not proved here; seat D3's receipt records
why: its children clause installs the middleware program (`restoreR`, typed at the exit's type)
over the fiber's saved stack, and nothing in `I` makes that stack accept the exit's type (the
stack of a fiber with a queued `finish` is not typed against the exit); its store clause clears
the stack of a published fiber whose current code `I` allows to be a race registration marker,
and `FiberTyped.registration` reads that stack.
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
          moved.deferredCause, moved.pendingOwner, moved.observers, moved.registration,
          (fun _ hr => by cases hr), moved.tokens⟩
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
          (fun _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h)⟩
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
        · exact old.code live idle marker ty declared
        · obtain ⟨y, r⟩ := reads
          refine edited.code x hx running ⟨y, ?_⟩ marker ty declared
          rcases r with r | r
          · rcases List.mem_cons.mp r with h | h
            · cases h
              exact absurd fid.symm hne
            · exact Or.inl h
          · rcases List.mem_cons.mp r with h | h
            · cases h
            · exact Or.inr h
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
            ∃ tin, StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin ty
              g.frame.stack ∧ InterruptProvenance g.frame := by
          intro ty declared
          obtain ⟨tin', stack', _⟩ := old.position declared
          exact ⟨tin', stack', provG⟩
        have exitedG : g.exit.isSome = true → g.parked = .notParked ∧ g.running = false := by
          intro hx
          rw [gx] at hx
          cases hx
        have registrationG : ∀ raceId, raceRegistrationR g.frame.current = some raceId →
            ∃ race resultTy, (m.update g).race? raceId = some race ∧ race.host = g.id ∧
              w.Θ race.host race.token = some resultTy ∧ StackReply root w g resultTy := by
          intro raceId marker
          rw [notMarker] at marker
          cases marker
        have codeG : g.exit = none → g.running = false → raceRegistrationR g.frame.current = none →
            ∀ ty, w.Γ g.id = some ty →
              SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty g.frame := by
          intro _ _ _ ty declared
          have same : ty = final := by
            have both : w.Γ t.id = some ty := declared
            rw [declaredFinal] at both
            cases both
            rfl
          subst same
          exact ⟨tin, answerTyped, stackOk, provG⟩
        have fresh : FiberTyped root w (m.update g) g :=
          { ok := ⟨⟨frameOk⟩, fun q hq => moved.ok.c1 q (List.mem_filter.mp hq).1, moved.ok.c2,
              moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
            delivery := fun _ h => nomatch h
            below := moved.below
            pendingShape := emptied
            parkedIdle := fun h => absurd gp h
            parkedBelow := fun _ h => nomatch h
            exited := exitedG
            deferredCause := moved.deferredCause
            pendingOwner := fun q hq => moved.pendingOwner q (List.mem_filter.mp hq).1
            observers := moved.observers
            registration := registrationG
            code := codeG
            tokens := fun _ h => nomatch h }
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

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Ledger.step_evaluate :=
  @Effect4.Program.Typed.evaluate_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_resume :=
  @Effect4.Program.Typed.resume_preserves
-- `M6Ledger`'s report runs at the foot of the last command module, which sees every proof.
