import Effect4.Laws.Program.Typed.Commands.Finish

/-!
# Laws.Program.Typed.Commands.Race — the race and interrupt commands

Wave 2's third command group (seat D3): `interruptTarget` (`Machine/Fibers.lean:1931-1937`),
`raceCancel` (`:1944-1955`), `afterInterrupt` (`:1938-1943`), `closeParAwait` (`:1976-1983`),
`enrollRace` (`:1897-1911`), `launch` (`:1879-1896`) and `registrationDone` (`:1912-1930`).

None of the first five has a halting arm: an unknown fiber or race leaves the machine and drops
the command. `interruptTarget` records the interrupt (`configTyped_interruptRecord`);
`raceCancel` only rewrites the queue, keeping the host's delivery facts on the commands it
queues; `afterInterrupt` and `closeParAwait` install the await code `CommandDeliveryOk` types
against the host's stack (`StackReply`), and the queued `loop` reads it (`ReadCode`);
`enrollRace` joins the live set under `EnrollRaceOk` and fires or stores the race callback.

`launch` and `registrationDone` are not proved here; seat D3's receipt records why.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

-- `owner_free` (a queued command's owner is free in the rest of the queue) is `Finish.lean`'s.

/-- A command with no payload, no key, no tail obligation and no reading of code, owned by `host`
(or by nobody), queued in front of a typed configuration. -/
theorem configTyped_cons_plain {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (c : RCmd)
    (payload : RCmdOk (preds root) w c) (authority : CommandAuthorityR m c)
    (delivery : CommandDeliveryOk root w m c)
    (owner : ∀ o, Guard.commandOwner m c = some o → o ∉ q.filterMap (Guard.commandOwner m))
    (tail : Guard.RegistrationQueue.RegistrationTail c q)
    (noKeys : Guard.commandKeys c = [])
    (noObserve : ∀ source exit observer, c ≠ .observe source exit observer)
    (noEnroll : ∀ race child, c ≠ .enrollRace race child)
    (noRace : ∀ host yielding race, c ≠ .afterInterrupt host yielding (.race race))
    (noLink : ∀ mode scope target interruptor extra, c ≠ .link mode scope target interruptor extra)
    (noLoop : ∀ id y, c ≠ .loop id y) (noDeliver : ∀ id y, c ≠ .deliver id y) :
    ConfigTyped root rootTy w m (c :: q) := by
  refine ⟨typed.machine, readCode_cons noLoop noDeliver typed.code, queueOk_cons ?_ typed.queue⟩
  refine ⟨payload, authority, delivery, owner, tail, ?_, ?_, ?_, ?_, noRace, ?_, ?_⟩
  · intro key hk
    rw [noKeys] at hk
    cases hk
  · intro _ _ _ _ hk
    rw [noKeys] at hk
    cases hk
  · intro source exit observer h
    exact absurd h (noObserve source exit observer)
  · intro race child h
    exact absurd h (noEnroll race child)
  · intro mode scope target interruptor extra h
    exact absurd h (noLink mode scope target interruptor extra)
  · intro source exit observer h
    exact absurd h (noObserve source exit observer)

/-! ## `interruptTarget` (no halting arm) -/

/-- **`interruptTarget` keeps `I`** at the same world: the interrupt is recorded on the target
(`configTyped_interruptRecord`), with the evaluation an idle interruptible target owes. -/
theorem interruptTarget_preserves (root : ProgramSource) (rootTy : EffTy) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    StepPreserves root rootTy (.interruptTarget target who extra) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  simp only [driveStep]
  cases ht : m.fiber? target with
  | none => exact tail
  | some g => exact configTyped_emit (configTyped_interruptRecord tail ht who extra) _

/-! ## `raceCancel` (no halting arm: it only rewrites the queue) -/

/-- The await list a cancellation walk delivers keeps the cols of the list it walks. -/
theorem fiberListColumns_sub {w : World} {small big : List FiberId} {answer error : Ty}
    (h : FiberListColumns w big answer error) (sub : ∀ id ∈ small, id ∈ big) :
    FiberListColumns w small answer error :=
  fun id hid => h id (sub id hid)

/-- `afterInterrupt` on the visited targets, queued by the cancellation walk's last step. -/
theorem configTyped_cons_afterAwaitAll {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {host : FiberId}
    (yielding : Bool) (visited : List FiberId) (active : Guard.ActiveAt m host)
    (free : host ∉ q.filterMap (Guard.commandOwner m))
    (delivery : ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w visited answer error ∧
        StackReply root w m fiber (EffTy.pure .unit)) :
    ConfigTyped root rootTy w m (.afterInterrupt host yielding (.awaitAll visited) :: q) := by
  refine configTyped_cons_plain typed _ trivial active ?_ ?_ trivial rfl
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
  · intro fiber found
    obtain ⟨answer, error, cols, reply⟩ := delivery fiber found
    exact ⟨EffTy.pure .unit, ⟨answer, error, cols, rfl⟩, reply⟩
  · intro o owner
    cases owner
    exact free

/-- **`raceCancel` keeps `I`** at the same world: each step of the walk queues the interrupt of a
live entrant and the rest of the walk, or the `afterInterrupt` that awaits the visited ones; the
host's delivery facts (`CommandDeliveryOk`) move to the queued command over a sublist. -/
theorem raceCancel_preserves (root : ProgramSource) (rootTy : EffTy) (raceId : Nat)
    (host : FiberId) (yielding : Bool) (remaining visited : List FiberId) :
    StepPreserves root rootTy (.raceCancel raceId host yielding remaining visited) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  have active : Guard.ActiveAt m host := typed.queue.authority _ List.mem_cons_self
  have delivery := typed.queue.delivery _ List.mem_cons_self
  have free : host ∉ rest.filterMap (Guard.commandOwner m) := owner_free typed.queue rfl
  have walked : ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w (visited ++ remaining) answer error ∧
        StackReply root w m fiber (EffTy.pure .unit) := delivery
  have toAfter : ∀ (small : List FiberId), (∀ id ∈ small, id ∈ visited ++ remaining) →
      ConfigTyped root rootTy w m (.afterInterrupt host yielding (.awaitAll small) :: rest) := by
    intro small sub
    refine configTyped_cons_afterAwaitAll tail yielding small active free fun fiber found => ?_
    obtain ⟨answer, error, cols, reply⟩ := walked fiber found
    exact ⟨answer, error, fiberListColumns_sub cols sub, reply⟩
  have toWalk : ∀ (more seen : List FiberId), (∀ id ∈ seen ++ more, id ∈ visited ++ remaining) →
      ConfigTyped root rootTy w m (.raceCancel raceId host yielding more seen :: rest) := by
    intro more seen sub
    refine configTyped_cons_plain tail _ trivial active ?_ ?_ trivial rfl
      (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
      (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    · intro fiber found
      obtain ⟨answer, error, cols, reply⟩ := walked fiber found
      exact ⟨answer, error, fiberListColumns_sub cols sub, reply⟩
    · intro o owner
      cases owner
      exact free
  simp only [driveStep]
  cases remaining with
  | nil => exact toAfter visited fun id hid => List.mem_append_left _ hid
  | cons t more =>
    dsimp only
    cases hr : m.race? raceId with
    | none => exact toAfter visited fun id hid => List.mem_append_left _ hid
    | some race =>
      dsimp only
      by_cases live : t ∈ race.state.live
      · rw [if_pos live]
        have walk := toWalk more (visited ++ [t]) fun id hid => by
          rw [List.append_assoc, List.singleton_append] at hid
          exact hid
        have walk' : ConfigTyped root rootTy w m
            (.raceCancel raceId host yielding more (visited ++ [t]) :: rest) := walk
        refine configTyped_cons_plain walk' _ trivial trivial trivial ?_ trivial rfl
          (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
          (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
        intro o owner
        cases owner
      · rw [if_neg live]
        exact toWalk more visited fun id hid => by
          rcases List.mem_append.mp hid with h | h
          · exact List.mem_append_left _ h
          · exact List.mem_append_right _ (List.mem_cons_of_mem _ h)

/-! ## `enrollRace` (no halting arm) -/

theorem rmodify_race? (m : RState) (id : FiberId) (k : RFiber → RFiber) (raceId : Nat) :
    (m.modify id k).race? raceId = m.race? raceId := by
  unfold RunMachine.modify
  split
  · rfl
  · rfl

/-- **`enrollRace` keeps `I`** at the same world: the entrant joins the live set under the race's
one result type (`EnrollRaceOk`: an id below `nextId`, the race column and the entrant's columns
below it); an exited entrant's callback fires now (`observe_raceCallback`), a live one stores it. -/
theorem enrollRace_preserves (root : ProgramSource) (rootTy : EffTy) (raceId : Nat)
    (child : FiberId) : StepPreserves root rootTy (.enrollRace raceId child) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  have enroll := (typed.queue.enroll raceId child List.mem_cons_self).2
  simp only [driveStep]
  cases hr : m.race? raceId with
  | none => exact tail
  | some race =>
    cases hc : m.fiber? child with
    | none => exact tail
    | some c =>
      dsimp only
      have cid : c.id = child := rfiber?_id hc
      have hcmem : c ∈ m.fibers := rfiber?_mem (show m.fiber? c.id = some c by rw [cid]; exact hc)
      obtain ⟨resultTy, payload, below⟩ : ∃ resultTy, RacePayload root w race resultTy ∧
          FiberColumnsBelow w c.id resultTy.answer resultTy.error := by
        rw [hr, hc] at enroll
        exact enroll
      obtain ⟨cty, declaredC, subA, subE⟩ := below
      have rid : race.id = raceId := rrace?_id hr
      have hr' : m.race? race.id = some race := by rw [rid]; exact hr
      let new : RRace :=
        { race with state := { race.state with live := race.state.live ++ [child] } }
      have payload' : RacePayload root w new resultTy := by
        refine ⟨payload.token, payload.failures, payload.winner, payload.accepted, payload.cleanup,
          fun id hid => ?_, payload.programs⟩
        rcases List.mem_append.mp hid with old | h
        · exact payload.live id old
        · rw [List.mem_singleton] at h
          subst h
          exact ⟨cty, by rw [← cid]; exact declaredC, subA, subE⟩
      have liveNew : ∀ src ∈ new.state.live, src ∈ race.state.live ∨
          (FiberColumnsBelow w src resultTy.answer resultTy.error ∧ src.value < m.nextId) := by
        intro src hsrc
        rcases List.mem_append.mp hsrc with old | h
        · exact Or.inl old
        · rw [List.mem_singleton] at h
          subst h
          exact Or.inr ⟨⟨cty, by rw [← cid]; exact declaredC, subA, subE⟩,
            by rw [← cid]; exact (tail.machine.fiber hcmem).below⟩
      have m1 := configTyped_updateRace tail hr' rfl rfl rfl (new := new) payload' liveNew
      have hr1 : (m.updateRace new).race? raceId = some new := by
        rw [rrace?_updateRace, hr, Option.map_some, if_pos rfl]
      cases hx : c.exit with
      | some exit =>
        dsimp only
        have exitTyped : ExitOk w cty exit := by
          have pay := (typed.machine.fiber hcmem).ok.c3 exit hx
          exact pay cty declaredC
        have obs : ObserverCommandOk root w (m.updateRace new) child exit (.raceCallback raceId) := by
          unfold ObserverCommandOk
          dsimp only
          rw [hr1]
          exact ⟨resultTy, payload', fun _ => exitOk_subN exitTyped subA subE⟩
        exact observe_raceCallback root rootTy m1 child exit raceId obs
      | none =>
        dsimp only
        refine configTyped_modify_quiet m1 child (quiet_observe (.raceCallback raceId) rfl) ?_
          (fun _ _ kept => Or.inl kept)
        intro f hf o ho
        rcases mem_append_observer ho with old | rfl
        · exact Or.inl old
        · refine Or.inr ?_
          have fid : f.id = child := rfiber?_id hf
          unfold StoredObserverOk
          dsimp only
          rw [rmodify_race?, hr1]
          refine ⟨resultTy, payload', fun _ => ⟨cty, ?_, subA, subE⟩⟩
          rw [fid, ← cid]
          exact declaredC

/-! ## Shared: an edit of an active fiber, a queued `loop`, sequencing at one error column -/

/-- An edit of a fiber that keeps its control flags keeps every queued command's authority when
the fiber owns no queued command: a `registrationDone` on a race it hosts reads its code marker,
and that command's owner is the host. -/
theorem commandAuthority_flags {m : RState} {f g : RFiber} (hf : m.fiber? f.id = some f)
    (hid : g.id = f.id) (running : g.running = f.running) (parked : g.parked = f.parked)
    (exit : g.exit = f.exit) {q : List RCmd} (free : f.id ∉ q.filterMap (Guard.commandOwner m))
    (c : RCmd) (hc : c ∈ q) (h : CommandAuthorityR m c) : CommandAuthorityR (m.update g) c := by
  have look : ∀ {id : FiberId} {x : RFiber}, m.fiber? id = some x → ∃ x',
      (m.update g).fiber? id = some x' ∧ x'.running = x.running ∧ x'.parked = x.parked ∧
        x'.exit = x.exit := by
    intro id x hx
    by_cases same : x.id = f.id
    · have xf : x = f := rfiber?_same hf hx same
      have idEq : id = g.id := by rw [hid, ← same]; exact (rfiber?_id hx).symm
      refine ⟨g, ?_, by rw [running, xf], by rw [parked, xf], by rw [exit, xf]⟩
      rw [idEq]
      exact rfiber?_update_self hf hid
    · exact ⟨x, rfiber?_update_keep hf hid hx (fun h => same (by rw [h])), rfl, rfl, rfl⟩
  have active : ∀ {id}, Guard.ActiveAt m id → Guard.ActiveAt (m.update g) id := fun {id} h => by
    obtain ⟨x, hx, run, park⟩ := h
    obtain ⟨x', hx', r', p', _⟩ := look hx
    exact ⟨x', hx', r'.trans run, p'.trans park⟩
  cases c with
  | loop fiber _ => exact active h
  | deliver fiber _ => exact active h
  | finish fiber _ => exact active h
  | afterInterrupt fiber _ _ => exact active h
  | closeParAwait fiber _ _ => exact active h
  | raceCancel _ fiber _ _ _ => exact active h
  | registrationDone raceId y =>
    obtain ⟨race, x, found, hx, run, park, marker⟩ := h
    have hne : x ≠ f := by
      intro same
      apply free
      refine List.mem_filterMap.mpr ⟨.registrationDone raceId y, hc, ?_⟩
      have xid : x.id = race.host := rfiber?_id hx
      simp only [Guard.commandOwner, found, Option.map_some, Option.some.injEq]
      rw [← xid, same]
    exact ⟨race, x, found, rfiber?_update_keep hf hid hx hne, run, park, marker⟩
  | launch raceId =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, found, active act⟩
  | enrollRace raceId _ =>
    obtain ⟨race, found, act⟩ := h
    exact ⟨race, found, active act⟩
  | exitDone fiber =>
    obtain ⟨x, hx, exited⟩ := h
    obtain ⟨x', hx', _, _, e'⟩ := look hx
    exact ⟨x', hx', by rw [e']; exact exited⟩
  | evaluate _ => trivial
  | resume _ _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- A `loop` queued for an active fiber whose code is typed: the queue facts of `I`, and the
code the `loop` reads. -/
theorem configTyped_cons_loop {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {f : RFiber}
    (hf : m.fiber? f.id = some f) (running : f.running = true) (parked : f.parked = .notParked)
    (free : f.id ∉ q.filterMap (Guard.commandOwner m)) (yielding : Bool)
    (code : raceRegistrationR f.frame.current = none → ∀ ty, w.Γ f.id = some ty →
      CodeOk root w m f.id ty f.frame) :
    ConfigTyped root rootTy w m (.loop f.id yielding :: q) := by
  have wide := typed.machine.wide
  refine ⟨typed.machine, ?_, queueOk_cons ?_ typed.queue⟩
  · intro x hx run reads marker ty declared
    by_cases same : x.id = f.id
    · have xf : x = f := rfiber?_same hf (rfiber?_of_mem wide.fiberIds hx) same
      rw [xf] at marker declared ⊢
      exact Or.inl (code marker ty declared)
    · obtain ⟨y, r⟩ := reads
      refine (typed.code x hx run ⟨y, ?_⟩ marker ty declared).cons fun y' h => ?_
      rotate_left
      · cases h
      rcases r with r | r
      · rcases List.mem_cons.mp r with h | h
        · injection h with hid _
          exact absurd hid same
        · exact Or.inl h
      · rcases List.mem_cons.mp r with h | h
        · cases h
        · exact Or.inr h
  · refine ⟨trivial, ⟨f, hf, running, parked⟩, trivial, ?_, trivial, (fun _ h => nomatch h),
      (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h)⟩
    intro o owner
    cases owner
    exact free

/-- **Sequencing at one error column**: a program's failures pass to the outer type unchanged
when its error column is the outer one (the answer column is never read by a failure); the
continuation types the successes. -/
theorem seq_typed_sameError (root : ProgramSource) {w : World} {mid ty : EffTy} {a : RProgram}
    {k : Val → RProgram} (ha : TypedProg root w mid a)
    (hk : ∀ w', w.leHost w' → ∀ v, Fits w' v mid.answer → TypedProg root w' ty (k v))
    (errors : mid.error = ty.error) :
    TypedProg root w ty ((guardR .onSuccess a).bind (seqR k)) := by
  show TypedProg root w ty (.vis (.inr (.guard_ .onSuccess)) _)
  refine TypedProg.guard mid ?_ ?_ ?_
  · show TypedProg root w mid
      ((a.bind fun ex => .vis (.inr (.unguard ex)) Effects.Program.pure).bind (seqR k))
    rw [Effects.Program.bind_assoc]
    exact close_typed root ha (seqR k)
  · intro w' o ex hpost
    obtain ⟨harm, hfit⟩ := hpost
    cases ex with
    | success v =>
      have hf := hfit.1
      rw [fitsExit_success_iff] at hf
      exact hk w' o v hf
    | failure c => exact Bool.noConfusion harm
  · intro w' _ ex hfit hmiss
    cases ex with
    | success v => exact Bool.noConfusion hmiss
    | failure c =>
      have cause := failureFits_cause hfit.1
      rw [errors] at cause
      exact ⟨failureFits_of_cause cause hfit.2, hfit.2⟩

/-! ## `afterInterrupt` (no halting arm) -/

/-- The await an interrupt returns (`asVoidCode (awaitCode kind)`, `Machine/Fibers.lean:1730-1742`)
is typed at the reply type `AfterInterruptReply` names: a live target's join park by the await
row (its pre is the target's declaration), an exited target's exit by its exit column
(`RunFiberOk`'s exit clause), an await-all park at unknown columns. -/
theorem afterInterruptCode_typed (root : ProgramSource) {rootTy : EffTy} {w : World} {m : RState}
    (typed : MachineTyped root rootTy w m) {kind : ParkKind} {replyTy : EffTy}
    (reply : AfterInterruptReply w kind replyTy) :
    TypedProg root w replyTy
      (asVoidCode (interpR root.program) (awaitCode (interpR root.program) m kind)) := by
  have exitTyped : ∀ target ex ty, (m.fiber? target).bind RunFiber.exit = some ex →
      w.Γ target = some ty → ExitOk w ty ex := by
    intro target ex ty hx declared
    obtain ⟨t, ht, tx⟩ := Option.bind_eq_some_iff.mp hx
    have tid : t.id = target := rfiber?_id ht
    have pay := (typed.fiber (rfiber?_mem ht)).ok.c3 ex tx
    exact pay ty (by rw [tid]; exact declared)
  show TypedProg root w replyTy
    ((guardR .onSuccess (awaitCode (interpR root.program) m kind)).bind
      (seqR fun _ => .pure (.success .unit)))
  cases kind with
  | race r => exact reply.elim
  | awaitAll targets =>
    obtain ⟨answer, error, cols, rfl⟩ := reply
    refine seq_typed_clean root (mid := EffTy.pure (.list (.exitOf .unknown .unknown))) ?_
      (fun _ _ _ _ => TypedProg.pure ⟨trivial, trivial⟩) rfl
    refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (Ty.list (.exitOf .unknown .unknown)) ?_ ?_
    · refine ⟨.unknown, .unknown, rfl, fun t ht => ?_⟩
      obtain ⟨fty, declared, _, _⟩ := cols t ht
      exact ⟨fty, declared, Ty.sub_unknown _, Ty.sub_unknown _⟩
    · intro w' _ ans post
      exact TypedProg.pure ⟨post, trivial⟩
  | join target mode =>
    cases mode with
    | joinEffect =>
      obtain ⟨sourceTy, declared, rfl⟩ := reply
      refine seq_typed_sameError root (mid := sourceTy) ?_
        (fun _ _ _ _ => TypedProg.pure ⟨trivial, trivial⟩) rfl
      simp only [awaitCode]
      split
      · rename_i ex hx
        exact TypedProg.pure (exitTyped target ex sourceTy hx declared)
      · refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) PUnit.unit ?_ ?_
        · show (w.Γ target).isSome = true
          rw [declared]
          rfl
        · intro w' o ans post
          obtain ⟨ty, declared', typedAns⟩ := post
          rw [o.1.2.1 _ _ declared] at declared'
          cases declared'
          exact TypedProg.pure typedAns
    | awaitValue =>
      obtain ⟨sourceTy, declared, rfl⟩ := reply
      refine seq_typed_clean root (mid := EffTy.pure (.exitOf sourceTy.answer sourceTy.error)) ?_
        (fun _ _ _ _ => TypedProg.pure ⟨trivial, trivial⟩) rfl
      simp only [awaitCode]
      split
      · rename_i ex hx
        exact TypedProg.pure ⟨(exitTyped target ex sourceTy hx declared).1, trivial⟩
      · refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
          (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) PUnit.unit ?_ ?_
        · show (w.Γ target).isSome = true
          rw [declared]
          rfl
        · intro w' o ans post
          obtain ⟨ty, declared', fitsAns⟩ := post
          rw [o.1.2.1 _ _ declared] at declared'
          cases declared'
          exact TypedProg.pure ⟨fitsAns, trivial⟩

/-- A fiber edit leaves every command's owner where it was: owners read the queued command and
the race table, which a fiber edit does not touch. -/
theorem commandOwner_update (m : RState) (g : RFiber) :
    Guard.commandOwner (Code := RProgram) (m.update g) = Guard.commandOwner m := by
  funext c
  cases c <;> rfl

/-- **`afterInterrupt` keeps `I`** at the same world: the host's code becomes the await its
interrupt returns, typed at the reply type its delivery fact names (`afterInterruptCode_typed`),
over the stack that reply meets (`StackReply`); the queued `loop` reads it. -/
theorem afterInterrupt_preserves (root : ProgramSource) (rootTy : EffTy) (host : FiberId)
    (yielding : Bool) (kind : ParkKind) :
    StepPreserves root rootTy (.afterInterrupt host yielding kind) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  obtain ⟨f, hfound, running, parked⟩ : Guard.ActiveAt m host :=
    typed.queue.authority _ List.mem_cons_self
  have delivery : CommandDeliveryOk root w m (.afterInterrupt host yielding kind) :=
    typed.queue.delivery _ List.mem_cons_self
  have free : host ∉ rest.filterMap (Guard.commandOwner m) := owner_free typed.queue rfl
  simp only [driveStep]
  rw [hfound]
  dsimp only
  have fid : f.id = host := rfiber?_id hfound
  have hf : m.fiber? f.id = some f := by rw [fid]; exact hfound
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have freeF : f.id ∉ rest.filterMap (Guard.commandOwner m) := by rw [fid]; exact free
  obtain ⟨replyTy, reply, final, declared, stackOk, prov⟩ := delivery f hfound
  have code := afterInterruptCode_typed root typed.machine reply
  let g : RFiber := { f with frame := { f.frame with
    current := asVoidCode (interpR root.program) (awaitCode (interpR root.program) m kind) } }
  have old := typed.machine.fiber hmem
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have provG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
  have notMarker : raceRegistrationR g.frame.current = none := raceRegistrationR_typed code
  have codeG : ∀ ty, w.Γ g.id = some ty → CodeOk root w (m.update g) g.id ty g.frame := by
    intro ty d
    have both : w.Γ f.id = some ty := d
    rw [declared] at both
    cases both
    exact ⟨replyTy, code, hostStack_races (racesKept_of_eq view.races) stackOk, provG⟩
  have frameOk : ∀ ty, w.Γ g.id = some ty →
      ∃ tin, PositionStack root w tin ty g.frame.stack ∧ InterruptProvenance g.frame := by
    intro ty d
    obtain ⟨tin, stack', _⟩ := old.position d
    exact ⟨tin, stack', provG⟩
  have deliveryG : ∀ token, g.parked = .withGuard token →
      ∃ tin final, w.Θ g.id token = some tin ∧ w.Γ g.id = some final ∧
        HostStack root w (m.update g) g.id tin final g.frame.stack ∧
        InterruptProvenance g.frame := by
    intro token h
    rw [show g.parked = f.parked from rfl, parked] at h
    cases h
  have registrationG : ∀ raceId, raceRegistrationR g.frame.current = some raceId →
      ∃ race resultTy, (m.update g).race? raceId = some race ∧ race.host = g.id ∧
        w.Θ race.host race.token = some resultTy ∧ StackReply root w (m.update g) g resultTy := by
    intro raceId marker
    rw [notMarker] at marker
    cases marker
  have fresh : FiberTyped root w (m.update g) g :=
    { ok := ⟨⟨frameOk⟩, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
      delivery := deliveryG
      below := moved.below
      pendingShape := moved.pendingShape
      parkedIdle := moved.parkedIdle
      parkedBelow := moved.parkedBelow
      exited := moved.exited
      exitedStack := fun hx => absurd (moved.exited hx).2 (by rw [running]; decide)
      deferredCause := moved.deferredCause
      pendingOwner := moved.pendingOwner
      observers := moved.observers
      registration := registrationG
      code := fun _ _ _ _ ty d => codeG ty d
      tokens := moved.tokens
      raceObservers := moved.raceObservers
      targetsBelow := moved.targetsBelow
      observersBelow := moved.observersBelow
      children := moved.children }
  have noRequest : ∀ tok r, requestOfR (m.update g) g.id tok = some r →
      requestOfR m f.id tok = some r := by
    intro tok r hr
    have off : g.parked ≠ .withGuard tok := by
      rw [show g.parked = f.parked from rfl, parked]
      exact fun h => nomatch h
    rw [requestOfR_of_not_parked look off] at hr
    cases hr
  have edited := configTyped_rupdate_code (g := g) tail hf rfl (PendingWeaker.refl _) rfl
    (fun p => ⟨p.recorded, p.deferred⟩) (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
    (fun c hc h => commandAuthority_flags (g := g) hf rfl rfl rfl rfl freeF c hc h)
    (fun _ _ _ ty d => Or.inl (codeG ty d)) fresh
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
    rw [commandOwner_update]
    exact freeF
  exact configTyped_cons_loop edited look running parked freeG yielding fun _ ty d => codeG ty d

/-! ## `closeParAwait` (no halting arm) -/

/-- A queued command's delivery facts read the stack of the fiber that owns it; an edit of a
fiber that owns no queued command keeps them all. -/
theorem commandDelivery_owner {root : ProgramSource} {w : World} {m : RState} {f g : RFiber}
    (hid : g.id = f.id) {q : List RCmd} (free : f.id ∉ q.filterMap (Guard.commandOwner m))
    (c : RCmd) (hc : c ∈ q) (h : CommandDeliveryOk root w m c) :
    CommandDeliveryOk root w (m.update g) c := by
  have other : ∀ host, Guard.commandOwner m c = some host → host ≠ g.id := by
    intro host owner same
    apply free
    rw [← hid, ← same]
    exact List.mem_filterMap.mpr ⟨c, hc, owner⟩
  have kept : RacesKept m (m.update g) := racesKept_of_eq fun _ => rfl
  cases c with
  | afterInterrupt host _ kind =>
    intro f' hf'
    rw [rfiber?_update_other (other host rfl)] at hf'
    obtain ⟨replyTy, ok, reply⟩ := h f' hf'
    exact ⟨replyTy, ok, stackReply_races kept reply⟩
  | raceCancel _ host _ remaining visited =>
    intro f' hf'
    rw [rfiber?_update_other (other host rfl)] at hf'
    obtain ⟨answer, error, cols, reply⟩ := h f' hf'
    exact ⟨answer, error, cols, stackReply_races kept reply⟩
  | closeParAwait host _ targets =>
    intro f' hf'
    rw [rfiber?_update_other (other host rfl)] at hf'
    obtain ⟨answer, error, cols, protocol, reply⟩ := h f' hf'
    exact ⟨answer, error, cols, protocol, stackReply_races kept reply⟩
  | finish host _ =>
    intro f' hf'
    rw [rfiber?_update_other (other host rfl)] at hf'
    exact h f' hf'
  | evaluate _ => trivial
  | loop _ _ => trivial
  | deliver _ _ => trivial
  | resume _ _ _ => trivial
  | launch _ => trivial
  | enrollRace _ _ => trivial
  | registrationDone _ _ => trivial
  | interruptTarget _ _ _ => trivial
  | trackChild _ _ => trivial
  | observe _ _ _ => trivial
  | exitDone _ => trivial
  | link _ _ _ _ _ => trivial
  | drainDue => trivial
  | wake _ _ => trivial

/-- **A fiber edit by an owner-free fiber keeps `I`**: `configTyped_rupdate_gen` with the stack
free to change, since no queued command's delivery fact reads the stack of a fiber that owns no
queued command (`commandDelivery_owner`). -/
theorem configTyped_rupdate_owner {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} {f g : RFiber} (typed : ConfigTyped root rootTy w m q)
    (hf : m.fiber? f.id = some f) (hid : g.id = f.id) (pending : PendingWeaker f.pending g.pending)
    (free : f.id ∉ q.filterMap (Guard.commandOwner m))
    (keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys m ∨
      (k.2 < m.nextToken ∧ requestOfR m k.1 k.2 = none))
    (request : ∀ token r, requestOfR (m.update g) g.id token = some r →
      requestOfR m f.id token = some r)
    (auth : ∀ c ∈ q, CommandAuthorityR m c → CommandAuthorityR (m.update g) c)
    (readG : g.running = true → ReadsCode g.id q → raceRegistrationR g.frame.current = none →
      ∀ ty, w.Γ g.id = some ty → CodeOk root w (m.update g) g.id ty g.frame)
    (fresh : FiberTyped root w (m.update g) g) : ConfigTyped root rootTy w (m.update g) q := by
  have view : ObsView m (m.update g) := obsView_rupdate hf hid pending
  obtain ⟨machine, code, queue⟩ := typed
  refine ⟨machineTyped_of (machineWide_rupdate machine.wide hid keys request) (fun x hx => ?_),
    ?_, queueOk_transport queue view (Nat.le_refl _) auth
      (fun c hc h => commandDelivery_owner hid free c hc h) ?_ (Nat.le_refl _)⟩
  · rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · exact fresh
    · exact fiberTyped_transport (machine.fiber hold) view (Nat.le_refl _) (Nat.le_refl _)
  · intro x hx hrun reads marker ty declared
    rcases mem_rupdate hx with rfl | ⟨hold, _⟩
    · exact Or.inl (readG hrun reads marker ty declared)
    · exact (code x hold hrun reads marker ty declared).races (racesKept_of_eq view.races)
  · intro fiber token r hr
    by_cases same : fiber = g.id
    · subst same
      rw [hid]
      exact request token r hr
    · rw [requestOfR_congr (rfiber?_update_other same)] at hr
      exact hr

-- `sub_union_self_left` and `sub_union_self_right` are `Typed/Denotation.lean`'s (seat D2), imported here.

/-- The raw union of one column of the declared types of a list of fibers (`never` for an
undeclared one): an upper bound of each in the raw order (`sub_declaredUnion`), and below every
bound the checker's order puts each of them under (`subN_declaredUnion`). It is the certificate
an await-all row's pre needs when its targets' columns are known only in the checker's order. -/
def declaredUnion (w : World) (col : EffTy → Ty) (targets : List FiberId) : Ty :=
  targets.foldr (fun t acc => .union (((w.Γ t).map col).getD .never) acc) .never

theorem sub_declaredUnion {w : World} {col : EffTy → Ty} {targets : List FiberId} {t : FiberId}
    {fty : EffTy} (ht : t ∈ targets) (declared : w.Γ t = some fty) :
    Ty.sub (col fty) (declaredUnion w col targets) = true := by
  induction targets with
  | nil => cases ht
  | cons x rest ih =>
    show Ty.sub (col fty) (.union (((w.Γ x).map col).getD .never) (declaredUnion w col rest)) = true
    rcases List.mem_cons.mp ht with same | later
    · rw [← same, declared, Option.map_some, Option.getD_some]
      exact sub_union_self_left _ _
    · exact Ty.sub_trans _ _ _ (ih later) (sub_union_self_right _ _)

theorem subN_declaredUnion {w : World} {col : EffTy → Ty} {targets : List FiberId} {bound : Ty}
    (below : ∀ t ∈ targets, ∀ fty, w.Γ t = some fty → Ty.subN (col fty) bound = true) :
    Ty.subN (declaredUnion w col targets) bound = true := by
  induction targets with
  | nil =>
    exact (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mpr fun x hx => nomatch hx
  | cons x rest ih =>
    have head : Ty.subN (((w.Γ x).map col).getD .never) bound = true := by
      cases hx : w.Γ x with
      | none => exact (Ty.OrderProof.sub_iff_members Ty.sub_trans _ _).mpr fun y hy => nomatch hy
      | some fty => exact below x List.mem_cons_self fty hx
    have tail := ih fun t ht fty d => below t (List.mem_cons_of_mem _ ht) fty d
    exact Ty.OrderProof.sub_normalize_union_le Ty.sub_trans _ _ _ head tail

/-- The checker's order on a list of exits, column by column. -/
theorem subN_list_exitOf {a e a' e' : Ty} (ha : Ty.subN a a' = true) (he : Ty.subN e e' = true) :
    Ty.subN (.list (.exitOf a e)) (.list (.exitOf a' e')) = true := by
  unfold Ty.subN
  simp only [Ty.normalize]
  rw [Ty.sub_args_list]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true]
  rw [Ty.sub_args_exitOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true]
  exact ⟨ha, he⟩

/-- The await-all park at the columns a close's delivery fact names (`FiberListColumns`, in the
checker's order) is typed at the list of exits at those columns: the row's certificate is the
raw union of the targets' declared columns (`declaredUnion`), which the row's pre reads in the
raw order and the answer's membership transports in the checker's. -/
theorem awaitAllPark_typed (root : ProgramSource) {w : World} {targets : List FiberId}
    {answer error : Ty} (cols : FiberListColumns w targets answer error) (ty : EffTy)
    (hans : ty.answer = .list (.exitOf answer error)) :
    TypedProg root w ty ((interpR root.program).parkCode (.awaitAll targets)) := by
  have hU : Ty.subN (declaredUnion w EffTy.answer targets) answer = true :=
    subN_declaredUnion fun t ht fty d => by
      obtain ⟨fty', d', ha, _⟩ := cols t ht
      rw [d] at d'
      cases d'
      exact ha
  have hE : Ty.subN (declaredUnion w EffTy.error targets) error = true :=
    subN_declaredUnion fun t ht fty d => by
      obtain ⟨fty', d', _, he⟩ := cols t ht
      rw [d] at d'
      cases d'
      exact he
  show TypedProg root w ty (.vis (.inr (.awaitAll targets)) fun v => .pure (.success v))
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h)
    (Ty.list (.exitOf (declaredUnion w EffTy.answer targets) (declaredUnion w EffTy.error targets)))
    ⟨_, _, rfl, fun t ht => ?_⟩ ?_
  · obtain ⟨fty, d, _, _⟩ := cols t ht
    exact ⟨fty, d, sub_declaredUnion (col := EffTy.answer) ht d,
      sub_declaredUnion (col := EffTy.error) ht d⟩
  · intro w' _ ans post
    refine TypedProg.pure ⟨?_, trivial⟩
    show Fits w' ans ty.answer
    rw [hans]
    exact fits_subN w' (subN_list_exitOf hU hE) ans post

/-- **`closeParAwait` keeps `I`** at the same world: the host's code becomes the await-all park
over the close's targets (`awaitAllPark_typed`) under the close generator's iterator frame, whose
protocol and the stack below it are the command's delivery facts; the queued `loop` reads it. -/
theorem closeParAwait_preserves (root : ProgramSource) (rootTy : EffTy) (host : FiberId)
    (yielding : Bool) (targets : List FiberId) :
    StepPreserves root rootTy (.closeParAwait host yielding targets) := by
  intro w m rest _ typed
  refine ⟨w, leHost_refl w, ?_⟩
  have tail := configTyped_tail typed
  obtain ⟨f, hfound, running, parked⟩ : Guard.ActiveAt m host :=
    typed.queue.authority _ List.mem_cons_self
  have delivery : CommandDeliveryOk root w m (.closeParAwait host yielding targets) :=
    typed.queue.delivery _ List.mem_cons_self
  have free : host ∉ rest.filterMap (Guard.commandOwner m) := owner_free typed.queue rfl
  simp only [driveStep]
  rw [hfound]
  dsimp only
  have fid : f.id = host := rfiber?_id hfound
  have hf : m.fiber? f.id = some f := by rw [fid]; exact hfound
  have hmem : f ∈ m.fibers := rfiber?_mem hf
  have freeF : f.id ∉ rest.filterMap (Guard.commandOwner m) := by rw [fid]; exact free
  obtain ⟨answer, error, cols, proto, final, declared, stackOk, prov⟩ := delivery f hfound
  have code := awaitAllPark_typed root cols
    ⟨.list (.exitOf answer error), error, Env.Requirement.empty⟩ rfl
  let g : RFiber := { f with frame := { f.frame with
    stack := .iter (interpR root.program).closeDoneName :: f.frame.stack
    current := (interpR root.program).parkCode (.awaitAll targets) } }
  have old := typed.machine.fiber hmem
  have look : (m.update g).fiber? g.id = some g := rfiber?_update_self hf rfl
  have view : ObsView m (m.update g) := obsView_rupdate (g := g) hf rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have provG : InterruptProvenance g.frame := ⟨prov.recorded, prov.deferred⟩
  have stackG : HostStack root w m f.id
      ⟨.list (.exitOf answer error), error, Env.Requirement.empty⟩ final g.frame.stack :=
    hostStack_push (.iter _ fun _ o => iteratorProtocol_mono o proto) stackOk
  have finalOf : ∀ ty, w.Γ g.id = some ty → ty = final := by
    intro ty d
    have both : w.Γ f.id = some ty := d
    rw [declared] at both
    cases both
    rfl
  have codeG : ∀ ty, w.Γ g.id = some ty → CodeOk root w (m.update g) g.id ty g.frame := by
    intro ty d
    rw [finalOf ty d]
    exact ⟨_, code, hostStack_races (racesKept_of_eq view.races) stackG, provG⟩
  have frameOk : ∀ ty, w.Γ g.id = some ty →
      ∃ tin, PositionStack root w tin ty g.frame.stack ∧ InterruptProvenance g.frame := by
    intro ty d
    rw [finalOf ty d]
    exact ⟨_, positionStack_of_host stackG, provG⟩
  have deliveryG : ∀ token, g.parked = .withGuard token →
      ∃ tin final, w.Θ g.id token = some tin ∧ w.Γ g.id = some final ∧
        HostStack root w (m.update g) g.id tin final g.frame.stack ∧
        InterruptProvenance g.frame := by
    intro token h
    rw [show g.parked = f.parked from rfl, parked] at h
    cases h
  have registrationG : ∀ raceId, raceRegistrationR g.frame.current = some raceId →
      ∃ race resultTy, (m.update g).race? raceId = some race ∧ race.host = g.id ∧
        w.Θ race.host race.token = some resultTy ∧ StackReply root w (m.update g) g resultTy := by
    intro raceId marker
    cases marker
  have fresh : FiberTyped root w (m.update g) g :=
    { ok := ⟨⟨frameOk⟩, moved.ok.c1, moved.ok.c2, moved.ok.c3, moved.ok.c4, moved.ok.c5⟩
      delivery := deliveryG
      below := moved.below
      pendingShape := moved.pendingShape
      parkedIdle := moved.parkedIdle
      parkedBelow := moved.parkedBelow
      exited := moved.exited
      exitedStack := fun hx => absurd (moved.exited hx).2 (by rw [running]; decide)
      deferredCause := moved.deferredCause
      pendingOwner := moved.pendingOwner
      observers := moved.observers
      registration := registrationG
      code := fun _ _ _ _ ty d => codeG ty d
      tokens := moved.tokens
      raceObservers := moved.raceObservers
      targetsBelow := moved.targetsBelow
      observersBelow := moved.observersBelow
      children := moved.children }
  have noRequest : ∀ tok r, requestOfR (m.update g) g.id tok = some r →
      requestOfR m f.id tok = some r := by
    intro tok r hr
    have off : g.parked ≠ .withGuard tok := by
      rw [show g.parked = f.parked from rfl, parked]
      exact fun h => nomatch h
    rw [requestOfR_of_not_parked look off] at hr
    cases hr
  have edited := configTyped_rupdate_owner (g := g) tail hf rfl (PendingWeaker.refl _) freeF
    (fun k hk => Or.inl (fiberKeys_internal hmem hk)) noRequest
    (fun c hc h => commandAuthority_flags (g := g) hf rfl rfl rfl rfl freeF c hc h)
    (fun _ _ _ ty d => codeG ty d) fresh
  have freeG : g.id ∉ rest.filterMap (Guard.commandOwner (m.update g)) := by
    rw [commandOwner_update]
    exact freeF
  exact configTyped_cons_loop edited look running parked freeG yielding fun _ ty d => codeG ty d

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M6Ledger.step_interruptTarget :=
  @Effect4.Program.Typed.interruptTarget_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_raceCancel :=
  @Effect4.Program.Typed.raceCancel_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_enrollRace :=
  @Effect4.Program.Typed.enrollRace_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_afterInterrupt :=
  @Effect4.Program.Typed.afterInterrupt_preserves
#obligation_proved Effect4.Program.Typed.M6Ledger.step_closeParAwait :=
  @Effect4.Program.Typed.closeParAwait_preserves
-- `M6Ledger`'s report runs at the foot of the last command module, which sees every proof.
