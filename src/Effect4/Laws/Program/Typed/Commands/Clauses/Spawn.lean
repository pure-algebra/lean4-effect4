import Effect4.Laws.Program.Typed.Commands.Evaluate

/-!
# Laws.Program.Typed.Commands.Clauses.Spawn — the spawn and race evaluator clauses

Concept 4 (the configuration invariant `I`); steps of `M6Ledger.step_deliver` and
`M6Ledger.step_loop` through `evaluate_keeps` (`FiberClauseKeeps`). The shared shape of `fork`,
`forkIn` and `forkScoped` (`Machine/Fibers.lean:1451-1489`): a child spawned over the evaluated
fiber at the old `nextId` (`spawn`, `:948-966`), started now or deferred onto the parent's
dispatcher (`start`, `:970-977`), the parent answered, the nested commands queued in front of its
`loop` (`Evaluating.spawn_settles`). The allocation is `Launch.lean`'s (`configTyped_alloc`).

Not established here: progress, or that the child's evaluation is typed beyond its typed code.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Contracts

/-! ## The shared shape -/

/-- Installing a fiber and appending a child of another id commute. -/
theorem allocR_update_comm (m : RState) {f child : RFiber} (record : ForkRecord)
    (ne : child.id ≠ f.id) : (allocR m child record).update f = allocR (m.update f) child record := by
  unfold allocR RunMachine.update
  simp only [List.map_append, List.map_cons, List.map_nil, if_neg ne]

/-- `spawn` is the allocation of `Launch.lean` followed by its trace event. -/
theorem spawn_eq (interp : RInterp) (m : RState) (parent : RFiber) (program : RProgram)
    (options : Supervision.ForkOptions) (site : List Nat) :
    ∃ flag, spawn interp m parent program options site =
      ((allocR m (spawnChild m program flag (interp.budgetOf parent.context) parent.context)
        ⟨⟨m.nextId⟩, parent.id, options.daemon, site⟩).emit
          [RunEvent.forked parent.id ⟨m.nextId⟩ options.daemon], parent, ⟨m.nextId⟩) :=
  ⟨_, rfl⟩

/-- The evaluated state moves to a machine with the same fibers, races, store, counters and halt
marker (a trace event, an arm, the middleware latch). -/
theorem Evaluating.congr {root : ProgramSource} {rootTy : EffTy} {w : World} {m m' : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fibers : m'.fibers = m.fibers) (races : m'.races = m.races) (state : m'.state = m.state)
    (nextId : m'.nextId = m.nextId) (nextToken : m'.nextToken = m.nextToken)
    (nextRace : m'.nextRace = m.nextRace) (stuck : m'.stuck = m.stuck) :
    Evaluating root rootTy w m' rest f y := by
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  have fibers' : (m'.update f).fibers = (m.update f).fibers := by
    unfold RunMachine.update
    rw [fibers]
  refine ⟨configTyped_congr (m := m.update f) (m' := m'.update f) fibers' races state nextId
    nextToken nextRace stuck ev.typed, ⟨f0, ?_, exit0⟩, ev.running, by rw [stuck]; exact ev.live⟩
  unfold RunMachine.fiber?
  rw [fibers]
  exact hf0

/-- **The allocation under the evaluated fiber**: the child appended at the old `nextId`, its code
typed and its context the evaluated fiber's, keeps the evaluated state at the world declaring it. -/
theorem Evaluating.alloc {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    {program : RProgram} {cty : EffTy} (typedChild : TypedProg root w cty program)
    (flag : Bool) (budget : Nat × Bool) (record : ForkRecord) :
    Evaluating root rootTy (w.addFiber ⟨m.nextId⟩ cty)
      (allocR m (spawnChild m program flag budget f.context) record) rest f y := by
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  have ne : (spawnChild m program flag budget f.context).id ≠ f.id :=
    Ne.symm (ne_next (m := m) old.below)
  have typed := configTyped_alloc (record := record) (flag := flag) (budget := budget) ev.typed
    typedChild old.ok.c5
  obtain ⟨f0, hf0, exit0⟩ := ev.stale
  refine ⟨?_, ⟨f0, by rw [allocR_fiber_other ne]; exact hf0, exit0⟩, ev.running, ev.live⟩
  rw [allocR_update_comm m record ne]
  exact typed

/-- **A deferred start on the evaluated fiber's dispatcher** (`start`, `Machine/Fibers.lean:970-977`):
a `start` task carries no key and is typed trivially; nothing else moves. -/
theorem Evaluating.enqueueStart {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (child : FiberId) :
    Evaluating root rootTy w m rest
      { f with dispatcher := f.dispatcher.enqueue 0 (.start child) } y := by
  let g : RFiber := { f with dispatcher := f.dispatcher.enqueue 0 (.start child) }
  have look := ev.look
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem look
  have old := ev.typed.machine.fiber hmem
  have view : ObsView (m.update f) ((m.update f).update g) :=
    obsView_rupdate look rfl (PendingWeaker.refl _)
  have moved := fiberTyped_transport old view (Nat.le_refl _) (Nat.le_refl _)
  have fresh : FiberTyped root w ((m.update f).update g) g := by
    refine ⟨⟨moved.ok.c0, moved.ok.c1, moved.ok.c2, moved.ok.c3, ⟨fun b hb => ⟨fun t ht => ?_⟩⟩,
      moved.ok.c5⟩, moved.delivery, moved.below, moved.pendingShape, moved.parkedIdle,
      moved.parkedBelow, moved.exited, moved.exitedStack, moved.deferredCause, moved.pendingOwner,
      moved.observers, moved.registration, moved.code, moved.tokens, moved.raceObservers,
      moved.targetsBelow, moved.observersBelow, moved.children⟩
    rcases mem_insert_tasks hb ht with rfl | ⟨b', hb', ht'⟩
    · trivial
    · exact (old.ok.c4.c0 b' hb').c0 t ht'
  have keys : ∀ k ∈ Guard.fiberKeys g, k ∈ Guard.internalKeys (m.update f) ∨
      (k.2 < (m.update f).nextToken ∧ requestOfR (m.update f) k.1 k.2 = none) := by
    intro k hk
    unfold Guard.fiberKeys at hk
    rcases List.mem_append.mp hk with hk | hk
    · exact Or.inl (fiberKeys_internal hmem (List.mem_append_left _ hk))
    · rcases List.mem_append.mp (bucketKeys_insert hk) with hk | hk
      · exact Or.inl (fiberKeys_internal hmem (List.mem_append_right _ hk))
      · exact absurd hk List.not_mem_nil
  have edited := configTyped_rupdate (g := g) ev.typed look rfl (PendingWeaker.refl _) rfl rfl rfl
    rfl rfl (fun p => p) keys fresh
  rw [rupdate_rupdate m (show g.id = f.id from rfl)] at edited
  exact ⟨edited, ev.stale, ev.running, ev.live⟩

/-- **A continue iteration over nested commands settles typed**: the frame step installs the typed
frame, `settle` queues the nested commands in front of `loop`, which `push` admits. -/
theorem Evaluating.settle_nested {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y y' : Bool} (ev : Evaluating root rootTy w m rest f y)
    (fr : RSaved) (code : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr)
    (nested : List RCmd)
    (push : ∀ g : RFiber, g.id = f.id →
      ConfigTyped root rootTy w (m.update g) (.loop f.id y' :: rest) →
      ConfigTyped root rootTy w (m.update g) (nested ++ [.loop f.id y'] ++ rest)) :
    SettlesTyped root rootTy w f.id rest
      (prepareIterR ⟨m, { f with frame := fr }, y', .continue_, nested⟩) := by
  have view := ev.view
  let fr' : RSaved := { fr with current := prepareR m.completedExits fr.current }
  have code' : ∀ ty, w.Γ f.id = some ty → CodeOk root w (m.update f) f.id ty fr' :=
    fun ty declared => codeOk_prepare m.completedExits view (code ty declared)
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, _, _⟩ := code' ty declared
  have glue : prepareIterR ⟨m, { f with frame := fr }, y', .continue_, nested⟩ =
      ⟨m, { f with frame := fr' }, y', .continue_, nested⟩ := prepareScopedExitR_of_typed current
  rw [glue]
  have step := (configTyped_frame_step ev.typed rfl ev.look ev.running fr' code'
    (raceRegistrationR_typed current)).1 y'
  rw [rupdate_rupdate m (show ({ f with frame := fr' } : RFiber).id = f.id from rfl)] at step
  exact ⟨w, leHost_refl w, push _ rfl step⟩

/-- **The spawn shape settles typed** (`fork`, `forkIn`, `forkScoped`, `Machine/Fibers.lean:1451-1489`):
the child spawned over the evaluated fiber (`spawn`) at the world declaring it at `cty`, its code
typed there; started now (an `evaluate` queued) or deferred onto the parent's dispatcher
(`start`); the parent answered with `code`, typed at the old code's type over the unchanged stack;
then `tail`, which `push` admits in front of the parent's `loop`. -/
theorem Evaluating.spawn_settles {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {rest : List RCmd} {f : RFiber} {y : Bool} (ev : Evaluating root rootTy w m rest f y)
    (interp : RInterp) {program : RProgram} {cty : EffTy} (typedChild : TypedProg root w cty program)
    (options : Supervision.ForkOptions) (site : List Nat) {ty tin : EffTy}
    (declared : w.Γ f.id = some ty) (stack : HostStack root w (m.update f) f.id tin ty f.frame.stack)
    (prov : InterruptProvenance f.frame) {code : RProgram}
    (typedCode : TypedProg root (w.addFiber ⟨m.nextId⟩ cty) tin code) (tail : List RCmd)
    (push : ∀ (M : RState), M.state = m.state → (M.fiber? ⟨m.nextId⟩).isSome = true →
      ConfigTyped root rootTy (w.addFiber ⟨m.nextId⟩ cty) M (.loop f.id y :: rest) →
      ConfigTyped root rootTy (w.addFiber ⟨m.nextId⟩ cty) M (tail ++ .loop f.id y :: rest)) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨(start (spawn interp m f program options site).1 f ⟨m.nextId⟩ options.startImmediately).1,
        answerR (start (spawn interp m f program options site).1 f ⟨m.nextId⟩
          options.startImmediately).2.1 code, y, .continue_,
        (start (spawn interp m f program options site).1 f ⟨m.nextId⟩
          options.startImmediately).2.2 ++ tail⟩) := by
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  have ne : (⟨m.nextId⟩ : FiberId) ≠ f.id := Ne.symm (ne_next (m := m) old.below)
  have freshΓ : w.Γ ⟨m.nextId⟩ = none := (fresh_of_typed ev.typed.machine).2
  have freshM : m.fiber? ⟨m.nextId⟩ = none := by
    rw [← rfiber?_update_other (g := f) ne]
    exact (fresh_of_typed ev.typed.machine).1
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ cty) := addFiber_leHost freshΓ
  obtain ⟨flag, hspawn⟩ := spawn_eq interp m f program options site
  rw [hspawn]
  let record : ForkRecord := ⟨⟨m.nextId⟩, f.id, options.daemon, site⟩
  let child := spawnChild m program flag (interp.budgetOf f.context) f.context
  have ev1 := ev.alloc typedChild flag (interp.budgetOf f.context) record
  -- the new frame, typed at the extended world over the unchanged stack
  have codeNew : ∀ (M : RState), M.races = m.races → ∀ ty',
      (w.addFiber ⟨m.nextId⟩ cty).Γ f.id = some ty' →
      CodeOk root (w.addFiber ⟨m.nextId⟩ cty) M f.id ty' { f.frame with current := code } := by
    intro M races ty' declared'
    rw [addFiber_Γ_other ne] at declared'
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    have kept : RacesKept (m.update f) M := racesKept_of_eq fun r => by
      unfold RunMachine.race?
      rw [races]
      rfl
    exact ⟨tin, typedCode, hostStack_mono ord (hostStack_races kept stack),
      ⟨prov.recorded, prov.deferred⟩⟩
  -- the child is present in every edit of the parent
  have present : ∀ (M : RState) (g : RFiber), M.fibers = m.fibers ++ [child] → g.id = f.id →
      ((M.update g).fiber? ⟨m.nextId⟩).isSome = true := by
    intro M g fibers gid
    rw [rfiber?_update_other (show (⟨m.nextId⟩ : FiberId) ≠ g.id by rw [gid]; exact ne)]
    have look : M.fiber? ⟨m.nextId⟩ = (allocR m child record).fiber? child.id := by
      unfold RunMachine.fiber?
      rw [fibers]
      rfl
    rw [look, allocR_fiber_self freshM]
    rfl
  cases himm : options.startImmediately with
  | true =>
    refine SettlesTyped.mono ord ((ev1.emit _).settle_nested { f.frame with current := code }
      (codeNew _ (by rfl)) _ fun g gid typed => ?_)
    rw [List.append_assoc, List.append_assoc]
    exact configTyped_cons_evaluate (push _ (by rfl) (present _ g (by rfl) gid) typed) _
  | false =>
    refine SettlesTyped.mono ord (((ev1.enqueueStart ⟨m.nextId⟩).congr (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).settle_nested { f.frame with current := code }
      (codeNew _ (by rfl)) _ fun g gid typed => ?_)
    rw [List.append_assoc]
    exact push _ (by rfl) (present _ g (by rfl) gid) typed

/-! ## The nested commands of the spawn shape -/

/-- `trackChild` reads nothing and carries nothing; it joins the queue. -/
theorem configTyped_cons_trackChild {root : ProgramSource} {rootTy : EffTy} {w : World}
    {m : RState} {q : List RCmd} (typed : ConfigTyped root rootTy w m q) (parent child : FiberId) :
    ConfigTyped root rootTy w m (.trackChild parent child :: q) :=
  configTyped_cons_plain typed _ trivial trivial trivial (fun _ h => nomatch h) trivial rfl
    (fun _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h)
    (fun _ _ _ _ _ h => nomatch h) (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)

/-- A `link` to a scope the store holds and a present target joins the queue (`QueueOk.links`). -/
theorem configTyped_cons_link {root : ProgramSource} {rootTy : EffTy} {w : World} {m : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w m q) {mode : Supervision.ScopeMode}
    {scope : Nat} {target : FiberId} {interruptor : Option FiberId} {extra : ReasonAnnotations Ann}
    (live : m.state.ScopeLive scope) (present : (m.fiber? target).isSome = true) :
    ConfigTyped root rootTy w m (.link mode scope target interruptor extra :: q) :=
  ⟨typed.machine, readCode_cons (fun _ _ h => nomatch h) (fun _ _ h => nomatch h) typed.code,
    queueOk_cons ⟨trivial, trivial, trivial, (fun _ h => nomatch h), trivial, (fun _ h => nomatch h),
      (fun _ _ _ _ h => nomatch h), (fun _ _ _ h => nomatch h), (fun _ _ h => nomatch h),
      (fun _ _ _ h => nomatch h), (fun _ _ _ _ _ h => by cases h; exact ⟨live, present⟩),
      (fun _ _ _ h => nomatch h)⟩ typed.queue⟩

/-! ## `fork` -/

/-- **`fork`** (`Machine/Fibers.lean:1451-1461`, `internal/effect.ts:5264-5284`): the body's program is
typed at the certificate (`bodyTyped_typed`); the child is declared there, the parent answered its
handle (the post), and a non-daemon child's tracking queued after its start. -/
theorem clause_fork (root : ProgramSource) (rootTy : EffTy) (child : Body)
    (options : Supervision.ForkOptions) (site : List Nat) :
    FiberClauseKeeps root rootTy (.fork child options site) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have typedChild : TypedProg root w cert
      (bodyR (interpRAt root.program m.completedExits) child) :=
    bodyTyped_typed root ev.typed.machine.sourceWF ev.typed.machine.services m.completedExits pre
  have freshΓ : w.Γ ⟨m.nextId⟩ = none := (fresh_of_typed ev.typed.machine).2
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ cert) := addFiber_leHost freshΓ
  have typedCode : TypedProg root (w.addFiber ⟨m.nextId⟩ cert) tin (next (Val.fiber ⟨m.nextId⟩)) :=
    typedNext _ ord _ ⟨⟨m.nextId⟩, rfl, addFiber_Γ_self⟩
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.fork _ m f y
    (bodyR (interpRAt root.program m.completedExits) child) options (answerWith next) site))
  unfold FiberAction.fork
  cases hd : options.daemon with
  | true =>
    exact ev.spawn_settles _ typedChild options site declared stack prov typedCode []
      (fun _ _ _ typed => typed)
  | false =>
    exact (ev.congr (m' := { m with middlewareInstalled := true }) rfl rfl rfl rfl rfl rfl
      rfl).spawn_settles _ typedChild options site declared
      (hostStack_races (m := m.update f) (racesKept_of_eq fun _ => rfl) stack) prov typedCode
      [.trackChild f.id ⟨m.nextId⟩] (fun _ _ _ typed => configTyped_cons_trackChild typed _ _)

end Effect4.Program.Typed
