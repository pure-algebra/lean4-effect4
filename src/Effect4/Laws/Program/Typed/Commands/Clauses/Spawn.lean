import Effect4.Laws.Program.Typed.Commands.Evaluate
import Effect4.Laws.Program.Typed.Commands.Clauses.Park

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
    rfl rfl (fun p => p) (fun d => d) keys fresh
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
    (typedCode : TypedProg root (w.addFiber ⟨m.nextId⟩ cty) tin code) (tail : RFiber → List RCmd)
    (push : ∀ (g : RFiber) (M : RState), M.state = m.state → (M.fiber? ⟨m.nextId⟩).isSome = true →
      ConfigTyped root rootTy (w.addFiber ⟨m.nextId⟩ cty) M (.loop f.id y :: rest) →
      ConfigTyped root rootTy (w.addFiber ⟨m.nextId⟩ cty) M (tail g ++ .loop f.id y :: rest)) :
    SettlesTyped root rootTy w f.id rest (prepareIterR
      ⟨(start (spawn interp m f program options site).1 f ⟨m.nextId⟩ options.startImmediately).1,
        answerR (start (spawn interp m f program options site).1 f ⟨m.nextId⟩
          options.startImmediately).2.1 code, y, .continue_,
        (start (spawn interp m f program options site).1 f ⟨m.nextId⟩
          options.startImmediately).2.2 ++ tail (start (spawn interp m f program options site).1 f
            ⟨m.nextId⟩ options.startImmediately).2.1⟩) := by
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
    exact configTyped_cons_evaluate (push _ _ (by rfl) (present _ g (by rfl) gid) typed) _
  | false =>
    refine SettlesTyped.mono ord (((ev1.enqueueStart ⟨m.nextId⟩).congr (by rfl) (by rfl)
      (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)).settle_nested { f.frame with current := code }
      (codeNew _ (by rfl)) _ fun g gid typed => ?_)
    rw [List.append_assoc]
    exact push _ _ (by rfl) (present _ g (by rfl) gid) typed

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
    exact ev.spawn_settles _ typedChild options site declared stack prov typedCode (fun _ => [])
      (fun _ _ _ _ typed => typed)
  | false =>
    exact (ev.congr (m' := { m with middlewareInstalled := true }) rfl rfl rfl rfl rfl rfl
      rfl).spawn_settles _ typedChild options site declared
      (hostStack_races (m := m.update f) (racesKept_of_eq fun _ => rfl) stack) prov typedCode
      (fun _ => [.trackChild f.id ⟨m.nextId⟩])
      (fun _ _ _ _ typed => configTyped_cons_trackChild typed _ _)

/-! ## `forkIn` and `forkScoped` -/

/-- **`forkIn`** (`Machine/Fibers.lean:1463-1472`, `internal/effect.ts:5364-5378`): a daemon child of
the point's program, typed at the certificate (`denoteAt_typed`), declared there and answered as
its handle; the link to the scope, present by the pre, queued after its start. -/
theorem clause_forkIn (root : ProgramSource) (rootTy : EffTy) (child : Point)
    (options : Supervision.ForkOptions) (scope : Nat) (site : List Nat) :
    FiberClauseKeeps root rootTy (.forkIn child options scope site) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, ⟨pre, hlive⟩, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have typedChild : TypedProg root w cert
      (bodyR (interpRAt root.program m.completedExits) (.at_ child)) :=
    denoteAt_typed root ev.typed.machine.sourceWF ev.typed.machine.services pre
  have live : m.state.ScopeLive scope := by
    have l : w.state.ScopeLive scope := hlive
    rw [ev.typed.machine.wide.state] at l
    exact l
  have freshΓ : w.Γ ⟨m.nextId⟩ = none := (fresh_of_typed ev.typed.machine).2
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ cert) := addFiber_leHost freshΓ
  have typedCode : TypedProg root (w.addFiber ⟨m.nextId⟩ cert) tin (next (Val.fiber ⟨m.nextId⟩)) :=
    typedNext _ ord _ ⟨⟨m.nextId⟩, rfl, addFiber_Γ_self⟩
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.forkIn _ m f y
    (bodyR (interpRAt root.program m.completedExits) (.at_ child)) options scope (answerWith next)
    site))
  unfold FiberAction.forkIn
  exact ev.spawn_settles _ typedChild { options with daemon := true } site declared stack prov
    typedCode (fun g => [.link .forkIn scope ⟨m.nextId⟩ (some g.id)
      ((interpRAt root.program m.completedExits).stackAnnotations g.id)])
    (fun _ _ state present typed => configTyped_cons_link typed (by rw [state]; exact live) present)

/-- **`forkScoped`** (`Machine/Fibers.lean:1474-1489`, `internal/effect.ts:5400-5406`): `forkIn` on the
context's ambient scope, present by `J` (`ambientScope_live`), its handle answered as a success; with
no ambient scope, the `missingService` defect, which the exit judgment admits at every type. -/
theorem clause_forkScoped (root : ProgramSource) (rootTy : EffTy) (child : Point)
    (options : Supervision.ForkOptions) (site : List Nat) :
    FiberClauseKeeps root rootTy (.forkScoped child options site) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have typedChild : TypedProg root w cert
      (bodyR (interpRAt root.program m.completedExits) (.at_ child)) :=
    denoteAt_typed root ev.typed.machine.sourceWF ev.typed.machine.services pre
  have freshΓ : w.Γ ⟨m.nextId⟩ = none := (fresh_of_typed ev.typed.machine).2
  have ord : w.leHost (w.addFiber ⟨m.nextId⟩ cert) := addFiber_leHost freshΓ
  have typedCode : TypedProg root (w.addFiber ⟨m.nextId⟩ cert) tin
      (next (.success (Val.fiber ⟨m.nextId⟩))) :=
    typedNext _ ord _ ⟨⟨m.nextId⟩, rfl, addFiber_Γ_self⟩
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.forkScoped _ m f y
    (bodyR (interpRAt root.program m.completedExits) (.at_ child)) options
    (fun f v => answerR f (next (.success v))) site))
  unfold FiberAction.forkScoped
  rw [show (interpRAt root.program m.completedExits).ambientScope = Ctx.ambientScope from rfl]
  cases hscope : Ctx.ambientScope f.context with
  | some scope =>
    have live : m.state.ScopeLive scope := by
      have l : w.state.ScopeLive scope :=
        ambientScope_live ev.typed.machine (rfiber?_mem ev.look) hscope
      rw [ev.typed.machine.wide.state] at l
      exact l
    exact ev.spawn_settles _ typedChild { options with daemon := true } site declared stack prov
      typedCode (fun g => [.link .forkIn scope ⟨m.nextId⟩ (some g.id)
        ((interpRAt root.program m.completedExits).stackAnnotations g.id)])
      (fun _ _ state present typed => configTyped_cons_link typed (by rw [state]; exact live) present)
  | none =>
    refine ev.settle_continue { f.frame with current := .pure (.failure (Cause.die .missingService)) }
      (fun ty' declared' => ?_)
    have same : ty' = ty := Option.some.inj (declared'.symm.trans declared)
    subst same
    refine ⟨tin, TypedProg.pure (strongExit_of_clean w tin _ rfl ?_), stack,
      ⟨prov.recorded, prov.deferred⟩⟩
    intro reason member
    simp only [Cause.die_reasons, List.mem_singleton] at member
    subst member
    exact ⟨(fun h => nomatch h), (fun h => nomatch h)⟩

/-! ## `raceRegister` -/

/-- **`raceRegister`** (`registerRace`, `Machine/Fibers.lean:937-944`, rc.112 `:1117-1141`): the
marker's race exists and is hosted here (`RegistrationState`), so the registration does not halt;
the race marked registering (`configTyped_updateRace`), and the race's launch and registration
return queued in place of the head, the return owning the host. -/
theorem clause_raceRegister (root : ProgramSource) (rootTy : EffTy) (raceId : Nat) :
    FiberClauseKeeps root rootTy (.raceRegister raceId) := by
  intro w m rest f y next ev hc
  have look := ev.look
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem look
  have old := ev.typed.machine.fiber hmem
  have marker : raceRegistrationR f.frame.current = some raceId := by rw [hc]; rfl
  obtain ⟨race, _, found, host, _, _⟩ := old.registration raceId marker
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  obtain ⟨resultTy, payload⟩ := ev.typed.machine.wide.races race (List.mem_of_find?_eq_some found)
  have hr : (m.update f).race? race.id = some race := by rw [rrace?_id found]; exact found
  have lookHost : (m.update f).fiber? race.host = some f := by rw [host]; exact look
  have tail := configTyped_tail ev.typed
  have done : ConfigTyped root rootTy w (m.update f) (.registrationDone raceId y :: rest) := by
    refine configTyped_cons_plain tail _ trivial ⟨race, f, found, lookHost, ev.running, notParked,
      marker⟩ trivial (fun o ho => ?_) trivial rfl (fun _ _ _ h => nomatch h)
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
    have ho' : ((m.update f).race? raceId).map Race.host = some o := ho
    rw [found, Option.map_some, host] at ho'
    cases ho'
    exact owner_free ev.typed.queue rfl
  have launched : ConfigTyped root rootTy w (m.update f)
      (.launch raceId :: .registrationDone raceId y :: rest) :=
    configTyped_cons_plain done _ trivial ⟨race, found, ⟨f, lookHost, ev.running, notParked⟩⟩ trivial
      (fun _ h => nomatch h) ⟨y, List.mem_cons_self⟩ rfl (fun _ _ _ h => nomatch h)
      (fun _ _ h => nomatch h) (fun _ _ _ h => nomatch h) (fun _ _ _ _ _ h => nomatch h)
      (fun _ _ h => nomatch h) (fun _ _ h => nomatch h)
  have edited := configTyped_updateRace launched (new := { race with registering := true }) hr rfl
    rfl rfl ⟨payload.token, payload.failures, payload.winner, payload.accepted, payload.cleanup,
      payload.live, payload.programs⟩ (fun _ h => .inl h)
  have found' : m.race? raceId = some race := found
  show SettlesTyped root rootTy w f.id rest (prepareIterR (registerRace m f y raceId))
  unfold registerRace
  rw [found']
  exact ⟨w, leHost_refl w, edited⟩

/-! ## A race appended (`beginRace`, `Machine/Fibers.lean:919-933`) -/

section AddRace
variable {M : RState} {race : RRace}

theorem race?_addRace (r : Nat) :
    ({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } : RState).race? r =
      (M.race? r).or ([race].find? fun s => s.id = r) :=
  List.find?_append

theorem race?_addRace_old {r : Nat} {old : RRace} (h : M.race? r = some old) :
    ({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } : RState).race? r =
      some old := by
  rw [race?_addRace, h]
  rfl

theorem race?_addRace_cases {r : Nat} {r' : RRace}
    (h : ({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } : RState).race? r =
      some r') : M.race? r = some r' ∨ r' = race := by
  rw [race?_addRace] at h
  cases ho : M.race? r with
  | some old =>
    rw [ho] at h
    exact .inl h
  | none =>
    rw [ho, Option.none_or] at h
    exact .inr (List.mem_singleton.mp (List.mem_of_find?_eq_some h))

theorem internalKeys_addRace {k : Guard.GuardKey}
    (hk : k ∈ Guard.internalKeys
      ({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } : RState)) :
    k ∈ Guard.internalKeys M ∨ k = (race.host, race.token) := by
  simp only [Guard.internalKeys, List.map_append, List.map_cons, List.map_nil, List.mem_append,
    List.mem_singleton] at hk ⊢
  aesop

/-- A countdown reads the fibers only: it moves to a machine with the same fibers. -/
theorem countdownAt_sameFibers {w : World} {M' : RState} (fibers : M'.fibers = M.fibers)
    {waiter : FiberId} {token : Nat} {incoming : Ty → Ty → Prop}
    (h : CountdownAt w M waiter token incoming) : CountdownAt w M' waiter token incoming := by
  have look : ∀ id, M'.fiber? id = M.fiber? id := fun id => by
    unfold RunMachine.fiber?
    rw [fibers]
  unfold CountdownAt at h ⊢
  rw [look]
  cases hf : M.fiber? waiter with
  | none => trivial
  | some fiber =>
    rw [hf] at h
    dsimp only at h ⊢
    cases hp : fiber.pending.find? (fun pending => pending.token = token) with
    | none => trivial
    | some pending =>
      rw [hp] at h
      dsimp only at h ⊢
      obtain ⟨answer, error, tokenTy, payload, inc⟩ := h
      exact ⟨answer, error, tokenTy, ⟨payload.token, payload.collected,
        fun id hid target hlook => payload.targets id hid target (by rw [← look]; exact hlook),
        payload.resume⟩, inc⟩

theorem storedObserverOk_addRace {root : ProgramSource} {w : World} {resultTy : EffTy}
    (payload : RacePayload root w race resultTy) (live : race.state.live = []) {source : FiberId}
    (o : Observer) (h : StoredObserverOk root w M source o) :
    StoredObserverOk root w { M with races := M.races ++ [race], nextRace := M.nextRace + 1 }
      source o := by
  cases o with
  | raceCallback raceId =>
    simp only [StoredObserverOk] at h ⊢
    split
    · trivial
    · rename_i r' hr
      rcases race?_addRace_cases hr with old | rfl
      · rw [old] at h
        exact h
      · exact ⟨resultTy, payload, fun hl => by rw [live] at hl; cases hl⟩
  | countdown _ _ => exact countdownAt_sameFibers (M := M) (by rfl) h
  | resumeAwait _ _ _ => exact h
  | dropScopeFinalizer _ _ => exact h
  | untrackChild _ => exact h
  | callback _ => exact h

theorem observerCommandOk_addRace {root : ProgramSource} {w : World} {resultTy : EffTy}
    (payload : RacePayload root w race resultTy) (live : race.state.live = []) {source : FiberId}
    {exit : ExitV} (o : Observer) (h : ObserverCommandOk root w M source exit o) :
    ObserverCommandOk root w { M with races := M.races ++ [race], nextRace := M.nextRace + 1 }
      source exit o := by
  cases o with
  | raceCallback raceId =>
    simp only [ObserverCommandOk] at h ⊢
    split
    · trivial
    · rename_i r' hr
      rcases race?_addRace_cases hr with old | rfl
      · rw [old] at h
        exact h
      · exact ⟨resultTy, payload, fun hl => by rw [live] at hl; cases hl⟩
  | countdown _ _ => exact countdownAt_sameFibers (M := M) (by rfl) h
  | resumeAwait _ _ _ => exact h
  | dropScopeFinalizer _ _ => exact h
  | untrackChild _ => exact h
  | callback _ => exact h

theorem commandAuthority_addRace {c : RCmd} (h : CommandAuthorityR M c) :
    CommandAuthorityR { M with races := M.races ++ [race], nextRace := M.nextRace + 1 } c := by
  cases c with
  | registrationDone raceId _ =>
    obtain ⟨r, fiber, found, host, running, parked, marker⟩ := h
    exact ⟨r, fiber, race?_addRace_old found, host, running, parked, marker⟩
  | launch raceId =>
    obtain ⟨r, found, active⟩ := h
    exact ⟨r, race?_addRace_old found, active⟩
  | enrollRace raceId _ =>
    obtain ⟨r, found, active⟩ := h
    exact ⟨r, race?_addRace_old found, active⟩
  | evaluate _ => exact h
  | loop _ _ => exact h
  | deliver _ _ => exact h
  | finish _ _ => exact h
  | resume _ _ _ => exact h
  | interruptTarget _ _ _ => exact h
  | afterInterrupt _ _ _ => exact h
  | raceCancel _ _ _ _ _ => exact h
  | trackChild _ _ => exact h
  | observe _ _ _ => exact h
  | exitDone _ => exact h
  | closeParAwait _ _ _ => exact h
  | link _ _ _ _ _ => exact h
  | drainDue => exact h
  | wake _ _ => exact h

end AddRace

/-- **A race appended keeps `I`**: its id the next race id, its host present, its token's key below
the counter and fresh (no internal key, no queued key, no request), its payload at its result type,
no live entrant. Every clause reading the races reads an existing race's id, which the append
keeps; a stored or queued race callback at the new id reads the new payload, whose live set is
empty. -/
theorem configTyped_addRace {root : ProgramSource} {rootTy : EffTy} {w : World} {M : RState}
    {q : List RCmd} (typed : ConfigTyped root rootTy w M q) {race : RRace} {resultTy : EffTy}
    (hid : race.id = M.nextRace) (payload : RacePayload root w race resultTy)
    (live : race.state.live = []) (host : (M.fiber? race.host).isSome = true)
    (internal : ∀ k ∈ Guard.internalKeys M, k ≠ (race.host, race.token))
    (queued : ∀ k ∈ q.flatMap Guard.commandKeys, k ≠ (race.host, race.token))
    (below : race.token < M.nextToken) (noRequest : requestOfR M race.host race.token = none) :
    ConfigTyped root rootTy w { M with races := M.races ++ [race], nextRace := M.nextRace + 1 } q := by
  have wide := typed.machine.wide
  have kept : RacesKept M { M with races := M.races ++ [race], nextRace := M.nextRace + 1 } :=
    fun _ old h => ⟨old, race?_addRace_old h, rfl, rfl⟩
  have wideNew : MachineWide root rootTy w
      { M with races := M.races ++ [race], nextRace := M.nextRace + 1 } :=
    { ids := wide.ids
      fibers := wide.fibers
      heap := wide.heap
      promises := wide.promises
      tokenBound := wide.tokenBound
      tokenTargets := wide.tokenTargets
      state := wide.state
      wf := wide.wf
      cells := wide.cells
      rootDeclared := wide.rootDeclared
      races := fun r hr => by
        rcases List.mem_append.mp hr with old | new
        · exact wide.races r old
        · rw [List.mem_singleton.mp new]
          exact ⟨resultTy, payload⟩
      stores := wide.stores
      fiberIds := wide.fiberIds
      raceIds := by
        show ((M.races ++ [race]).map Race.id).Nodup
        rw [List.map_append]
        refine List.nodup_append.mpr ⟨wide.raceIds, List.nodup_cons.mpr ⟨List.not_mem_nil,
          List.nodup_nil⟩, fun a ha b hb same => ?_⟩
        obtain ⟨r, hr, rfl⟩ := List.mem_map.mp ha
        have lt := wide.racesBelow r hr
        have hb' : b = race.id := List.mem_singleton.mp hb
        rw [same, hb', hid] at lt
        exact Nat.lt_irrefl _ lt
      racesBelow := fun r hr => by
        rcases List.mem_append.mp hr with old | new
        · exact Nat.lt_succ_of_lt (wide.racesBelow r old)
        · rw [List.mem_singleton.mp new, hid]
          exact Nat.lt_succ_self _
      raceHosts := fun r hr => by
        rcases List.mem_append.mp hr with old | new
        · exact wide.raceHosts r old
        · rw [List.mem_singleton.mp new]
          exact Option.isSome_iff_exists.mp host
      keysBelow := fun k hk => by
        rcases internalKeys_addRace hk with old | rfl
        · exact wide.keysBelow k old
        · exact below
      requestsBelow := wide.requestsBelow
      requestsOwned := fun fiber token r hr hk => by
        rcases internalKeys_addRace hk with old | same
        · exact wide.requestsOwned fiber token r hr old
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
          have hr' : requestOfR M race.host race.token = some r := hr
          rw [noRequest] at hr'
          cases hr'
      services := wide.services
      live := ⟨wide.live.running, wide.live.dueOwners⟩
      timers := wide.timers
      waiters := wide.waiters
      liveBelow := fun raceId r' hr' id hid' => by
        rcases race?_addRace_cases hr' with old | rfl
        · exact wide.liveBelow raceId r' old id hid'
        · rw [live] at hid'
          cases hid'
      sourceWF := wide.sourceWF }
  have fiberOk : ∀ x ∈ ({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } :
      RState).fibers, FiberTyped root w
        { M with races := M.races ++ [race], nextRace := M.nextRace + 1 } x := by
    intro x hx
    have old := typed.machine.fiber hx
    exact
      { ok := old.ok
        delivery := old.delivery_races kept
        below := old.below
        pendingShape := old.pendingShape
        parkedIdle := old.parkedIdle
        parkedBelow := old.parkedBelow
        exited := old.exited
        exitedStack := old.exitedStack
        deferredCause := old.deferredCause
        pendingOwner := old.pendingOwner
        observers := fun o ho => storedObserverOk_addRace payload live o (old.observers o ho)
        registration := fun raceId marker => by
          obtain ⟨r, resultTy', found, host', token, reply⟩ := old.registration raceId marker
          exact ⟨r, resultTy', race?_addRace_old found, host', token, stackReply_races kept reply⟩
        code := old.code_races kept
        tokens := old.tokens
        raceObservers := fun raceId r' hr' o ho => by
          rcases race?_addRace_cases hr' with h | rfl
          · exact old.raceObservers raceId r' h o ho
          · intro hk
            exact internal _ (fiberKeys_internal (m := M) hx (List.mem_append_left _
              (List.mem_flatMap.mpr ⟨o, ho, hk⟩))) rfl
        targetsBelow := old.targetsBelow
        observersBelow := old.observersBelow
        children := old.children }
  have owners : q.filterMap (Guard.commandOwner
      ({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } : RState)) =
      q.filterMap (Guard.commandOwner M) :=
    filterMap_congr_mem q fun c hc => by
      cases c with
      | registrationDone raceId _ =>
        obtain ⟨r, _, found, _⟩ := typed.queue.authority _ hc
        show (({ M with races := M.races ++ [race], nextRace := M.nextRace + 1 } : RState).race?
          raceId).map Race.host = (M.race? raceId).map Race.host
        rw [race?_addRace_old found, found]
      | _ => rfl
  refine ⟨machineTyped_of wideNew fiberOk, readCode_races (m := M) rfl kept typed.code,
    { payload := typed.queue.payload
      authority := fun c hc => commandAuthority_addRace (typed.queue.authority c hc)
      delivery := fun c hc => commandDelivery_mono (leHost_refl w) (fun _ _ h => h) kept
        (fun _ _ => rfl) (typed.queue.delivery c hc)
      owners := by rw [owners]; exact typed.queue.owners
      registration := typed.queue.registration
      keys := ⟨typed.queue.keys.below, typed.queue.keys.disjoint⟩
      observer := fun s e o ho => ⟨(typed.queue.observer s e o ho).1,
        observerCommandOk_addRace payload live o (typed.queue.observer s e o ho).2⟩
      enroll := fun r c hc => ?_
      noRaceAfterInterrupt := typed.queue.noRaceAfterInterrupt
      links := typed.queue.links
      raceObservers := fun s e o ho raceId r' hr' => by
        rcases race?_addRace_cases hr' with h | rfl
        · exact typed.queue.raceObservers s e o ho raceId r' h
        · intro hk
          exact queued _ (List.mem_flatMap.mpr ⟨_, ho, hk⟩) rfl }⟩
  obtain ⟨race0, found, _⟩ := typed.queue.authority _ hc
  have h := typed.queue.enroll r c hc
  unfold EnrollRaceOk at h ⊢
  rw [race?_addRace_old found]
  rw [found] at h
  exact h

/-! ## `raceAll` -/

/-- **`raceAll`** (`beginRace`, `Machine/Fibers.lean:919-933`, rc.112 `:1493`): the answer frame saved;
the host's next token declared at the certificate (`configTyped_token`); the race appended with the
entrants' programs, each typed at a type below the certificate (the pre, `denoteAt_typed`), and no
live entrant (`configTyped_addRace`); the registration marker installed over the answer frame, which
carries the race's exit to the continuation at the post (`Evaluating.settle_marker`). -/
theorem clause_raceAll (root : ProgramSource) (rootTy : EffTy) (entrants : List Point)
    (site : Option (List Nat)) : FiberClauseKeeps root rootTy (.raceAll entrants site) := by
  intro w m rest f y next ev hc
  obtain ⟨ty, declared⟩ := ev.declared
  obtain ⟨tin, current, stack, prov⟩ := ev.code (by rw [hc]; rfl) ty declared
  rw [hc] at current
  obtain ⟨cert, pre, typedNext⟩ := TypedProg.fiber_inv current (fun _ h => nomatch h)
    (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ _ _ h => nomatch h)
  have wide := ev.typed.machine.wide
  have hmem : f ∈ (m.update f).fibers := rfiber?_mem ev.look
  have old := ev.typed.machine.fiber hmem
  have notParked : f.parked = .notParked := by
    cases hp : f.parked with
    | notParked => rfl
    | withGuard _ =>
      have idle := old.parkedIdle (by rw [hp]; exact fun h => nomatch h)
      rw [ev.running] at idle
      cases idle
  obtain ⟨ord, tokened⟩ := configTyped_token ev.typed (n := f.id) (by rw [declared]; rfl) cert
  let programs := entrants.map fun p => bodyR (interpRAt root.program m.completedExits) (.at_ p)
  let race : RRace := ⟨m.nextRace, f.id, m.nextToken,
    { Supervision.RaceAllState.initial [] with remaining := programs.length }, false, programs,
    false, site⟩
  have payload : RacePayload root (w.addToken f.id m.nextToken cert) race cert :=
    { token := addToken_Θ_self
      failures := strongExit_of_clean _ cert _ rfl (fun _ h => nomatch h)
      winner := fun _ h => nomatch h
      accepted := fun _ h => nomatch h
      cleanup := fun _ h => nomatch h
      live := fun _ h => nomatch h
      programs := fun code hcode => by
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hcode
        obtain ⟨pty, ptyped, ha, he⟩ := pre p hp
        exact ⟨pty, typedProg_mono root w _ pty _ ord
          (denoteAt_typed root ev.typed.machine.sourceWF ev.typed.machine.services ptyped),
          Ty.sub_le_subN ha, Ty.sub_le_subN he⟩ }
  have internal : ∀ k ∈ Guard.internalKeys (m.update f), k ≠ (f.id, m.nextToken) :=
    fun k hk same => by
      have lt := wide.keysBelow k hk
      rw [same] at lt
      exact Nat.lt_irrefl _ lt
  have queued : ∀ k ∈ (Cmd.deliver f.id y :: rest).flatMap Guard.commandKeys,
      k ≠ (f.id, m.nextToken) := fun k hk same => by
    have lt := ev.typed.queue.keys.below k hk
    rw [same] at lt
    exact Nat.lt_irrefl _ lt
  have noRequest : requestOfR (m.update f) f.id m.nextToken = none :=
    requestOfR_of_not_parked ev.look (by rw [notParked]; exact fun h => nomatch h)
  have appended := configTyped_addRace tokened (race := race) rfl payload rfl
    (by show ((m.update f).fiber? f.id).isSome = true; rw [ev.look]; rfl) internal queued
    (Nat.lt_succ_self _) noRequest
  let fr : RSaved := { f.frame with
    current := .vis (.inr (.raceRegister m.nextRace)) Effects.Program.pure
    stack := .answer next :: f.frame.stack }
  have hstack : HostStack root (w.addToken f.id m.nextToken cert) (m.update f) f.id cert ty fr.stack :=
    hostStack_push (answerFrame_typed (fun _ _ _ hex => hex)
      (fun w'' o ans post => typedNext w'' (leHost_trans _ _ _ ord o) ans post))
      (hostStack_mono ord stack)
  have fresh : m.races.find? (fun s => decide (s.id = m.nextRace)) = none := by
    cases hr : (m.update f).race? m.nextRace with
    | none => exact hr
    | some r =>
      have lt := wide.racesBelow r (List.mem_of_find?_eq_some hr)
      rw [rrace?_id hr] at lt
      exact absurd lt (Nat.lt_irrefl _)
  show SettlesTyped root rootTy w f.id rest (prepareIterR (FiberAction.raceAll _ m
    (saveAnswerR f next) y programs site))
  unfold FiberAction.raceAll beginRace
  refine SettlesTyped.mono ord (Evaluating.settle_marker ?_ fr declared
    ⟨m.nextRace, race, cert, rfl, ?_, rfl, addToken_Θ_self, hostStack_races ?_ hstack,
      ⟨prov.recorded, prov.deferred⟩⟩)
  · obtain ⟨f0, hf0, exit0⟩ := ev.stale
    exact ⟨configTyped_congr (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      appended, ⟨f0, hf0, exit0⟩, ev.running, ev.live⟩
  · show (m.races ++ [race]).find? (fun s => decide (s.id = m.nextRace)) = some race
    rw [List.find?_append, fresh, Option.none_or, List.find?_cons, decide_eq_true rfl]
  · intro r old h
    refine ⟨old, ?_, rfl, rfl⟩
    have h' : m.races.find? (fun s => decide (s.id = r)) = some old := h
    show (m.races ++ [race]).find? (fun s => decide (s.id = r)) = some old
    rw [List.find?_append, h']
    rfl

end Effect4.Program.Typed
