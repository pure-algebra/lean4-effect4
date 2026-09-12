import Effect4.Laws.Program.Guard.NativeState

set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 1600000
namespace Effect4.Program.Guard.NativeStateLinks
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Guard
open Effect4.Program.Guard.NativeState
abbrev NInterp := RunInterp EffName EffThunk Val Err Defect FiberId Ann Ctx Stores

/-- Forward facts needed to carry command authority and outstanding guards
across local evaluation. An interrupt may replace the target's request. -/
structure Links (m n : NativeMachine) : Prop where
  controls : CommandControlsPreserved m n
  races : RaceHostsPreserved m n
  requests : ∀ fiber token request, requestOf m fiber token = some request →
    requestOf n fiber token = some request ∨ InterruptedAt n fiber
  interrupted : ∀ fiber, InterruptedAt m fiber → InterruptedAt n fiber

theorem Links.same {m n : NativeMachine} (fibers : n.fibers = m.fibers)
    (races : RaceHostsPreserved m n) : Links m n := by
  have lookup (id : FiberId) : n.fiber? id = m.fiber? id := by
    simp only [RunMachine.fiber?, fibers]
  constructor
  · constructor
    · intro id f hf hr hp
      exact ⟨f, (lookup id).trans hf, hr, hp, rfl⟩
    · intro id f hf hx
      exact ⟨f, (lookup id).trans hf, hx⟩
  · exact races
  · intro id token request hr
    exact Or.inl ((requestOf_eq_of_fiber_eq id token (lookup id)).trans hr)
  · rintro id ⟨f, hf, hi⟩
    exact ⟨f, (lookup id).trans hf, hi⟩

theorem Links.refl (m : NativeMachine) : Links m m :=
  .same rfl (fun _ race hr => ⟨race, hr, rfl⟩)

theorem Links.sameTables {m n : NativeMachine} (fibers : n.fibers = m.fibers)
    (races : n.races = m.races) : Links m n :=
  .same fibers (fun id race hr => ⟨race, by simpa only [RunMachine.race?, races] using hr, rfl⟩)

theorem Links.trans {m n o : NativeMachine} (a : Links m n) (b : Links n o) : Links m o := by
  constructor
  · constructor
    · intro id f hf hr hp
      obtain ⟨g, hg, hgr, hgp, hgc⟩ := a.controls.active id f hf hr hp
      obtain ⟨h, hh, hhr, hhp, hhc⟩ := b.controls.active id g hg hgr hgp
      exact ⟨h, hh, hhr, hhp, hhc.trans hgc⟩
    · intro id f hf hx
      obtain ⟨g, hg, hgx⟩ := a.controls.exited id f hf hx
      exact b.controls.exited id g hg hgx
  · intro id race hr
    obtain ⟨r, hnr, he⟩ := a.races id race hr
    obtain ⟨s, hos, hs⟩ := b.races id r hnr
    exact ⟨s, hos, hs.trans he⟩
  · intro id token request hr
    rcases a.requests id token request hr with hr | hi
    · exact b.requests id token request hr
    · exact Or.inr (b.interrupted id hi)
  · intro id hi
    exact b.interrupted id (a.interrupted id hi)

theorem Links.emit {m n : NativeMachine} (h : Links m n) (events) : Links m (n.emit events) :=
  h.trans (.sameTables rfl rfl)

theorem Links.arm {m n : NativeMachine} (h : Links m n) (owner : FiberId) : Links m (n.arm owner) :=
  h.trans (.sameTables rfl rfl)

theorem Links.store {m n : NativeMachine} (h : Links m n) (stores : Stores) : Links m {n with state := stores} :=
  h.trans (.sameTables rfl rfl)

theorem controls_of_full {m n : NativeMachine} (h : ControlsPreserved m n) :
    CommandControlsPreserved m n := by
  constructor
  · intro id f hf hr hp
    obtain ⟨g, hg, hc, hpark, _, hrun⟩ := h id f hf (Or.inl hp)
    exact ⟨g, hg, hrun hr, hpark.trans hp, hc⟩
  · intro id f hf hx
    obtain ⟨g, hg, _, _, he, _⟩ := h id f hf (Or.inr hx)
    exact ⟨g, hg, by rw [he]; exact hx⟩

theorem Links.modifyFields (m : NativeMachine) (target : FiberId) (k : NFiber → NFiber)
    (view : ∀ f, RequestView f (k f)) (run : ∀ f, (k f).running = f.running)
    (exit : ∀ f, (k f).exit = f.exit) (mark : ∀ f, Interrupted f → Interrupted (k f)) :
    Links m (m.modify target k) := by
  constructor
  · unfold RunMachine.modify
    cases hf : m.fiber? target with
    | none => exact (Links.refl m).controls
    | some f =>
      apply controls_of_full
      exact controlsPreserved_update_fields
        (by simpa only [fiber_id_of_lookup hf] using hf) (k f) (view f) (exit f)
        (fun hr => (run f).trans hr)
  · intro id race hr
    exact ⟨race, by simpa only [RunMachine.race?, Effect4.Program.Guard.FrameOwned.modify_races] using hr, rfl⟩
  · intro id token request hr
    exact Or.inl ((requestOf_modify_view m target id token k view).trans hr)
  · exact interruptedAt_modify_view target k (fun f => (view f).1.symm) mark

theorem Links.observer (m : NativeMachine) (target : FiberId) (observer : Observer) :
    Links m (m.modify target fun f => {f with observers := f.observers ++ [observer]}) :=
  .modifyFields m target _ (fun _ => ⟨rfl,rfl,rfl⟩) (fun _ => rfl) (fun _ => rfl) (fun _ h => h)

theorem Links.interruptRecord (p : NativeEff) (table : RowTable) (completed)
    {m : NativeMachine} {f : NFiber} (hf : m.fiber? f.id = some f)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    Links m (m.update (interruptRecord (interpAt p completed table) who extra f).1) := by
  change Links m (m.update (Effect4.Machine.interruptRecord (interpOf p table) who extra f).1)
  refine ⟨commandControls_interruptRecord p table hf who extra,
    (fun _ race hr => ⟨race, hr, rfl⟩), ?_, interruptedAt_update_interruptRecord p table hf who extra⟩
  intro id token request hr
  let g := (Effect4.Machine.interruptRecord (interpOf p table) who extra f).1
  by_cases he : f.id = id
  · right
    exact ⟨g, he ▸ fiber_lookup_update_self hf g (interruptRecord_id p table who extra f),
      interruptRecord_interrupted p table who extra f⟩
  · left
    exact (requestOf_update_other m g id token
      (fun heq => he ((interruptRecord_id p table who extra f).symm.trans heq))) ▸ hr

theorem Links.spawn (p : NativeEff) (table : RowTable) (completed) (m : NativeMachine)
    (f : NFiber) (code : NCode) (options : Supervision.ForkOptions) :
    Links m (spawn (interpAt p completed table) m f code options).1 := by
  change Links m (Effect4.Machine.spawn (interpOf p table) m f code options).1
  refine ⟨controls_of_full (controlsPreserved_spawnAppend m (spawnedChild p table m f code options)),
    (fun _ race hr => ⟨race, hr, rfl⟩), ?_, ?_⟩
  · intro id token request hr
    exact Or.inl ((requestOf_spawn p table m f code options id token).trans hr)
  · exact fun _ hi => interruptedAt_spawn p table f code options hi

theorem Links.start (m : NativeMachine) (f : NFiber) (child : FiberId) (immediate : Bool) :
    Links m (start m f child immediate).1 := by
  unfold Effect4.Machine.start
  split <;> exact .sameTables rfl rfl

theorem Links.startAfter {m n : NativeMachine} (h : Links m n)
    (f : NFiber) (child : FiberId) (immediate : Bool) :
    Links m (Effect4.Machine.start n f child immediate).1 := h.trans (.start n f child immediate)

theorem Links.forkFinalizers (p : NativeEff) (table : RowTable) (completed)
    (m : NativeMachine) (f : NFiber) (codes : List NCode) :
    Links m (forkFinalizers (interpAt p completed table) m f codes).1 := by
  induction codes generalizing m with
  | nil => exact .refl m
  | cons code rest ih =>
    exact (Links.spawn p table completed m f code ⟨true,true,.inherit⟩).trans (ih _)

theorem Links.beginRace (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (codes : List NCode) :
    Links m (beginRace interp m f yielding codes).machine :=
  .same rfl (raceHostsPreserved_append m [_])

theorem Links.registerRace (m : NativeMachine) (f : NFiber) (yielding : Bool) (id : Nat) :
    Links m (registerRace m f yielding id).machine := by
  unfold Effect4.Machine.registerRace
  split
  · exact .refl m
  · rename_i race hr
    apply Links.same
    · rfl
    · apply raceHostsPreserved_updateRace (race := race)
        (by simpa only [race_id_of_lookup hr] using hr) {race with registering := true} rfl rfl

theorem Links.countdown (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (targets : List FiberId) (resume : Resume EffName) (failFast : Bool) :
    Links m (countdownPark interp m f targets resume failFast).1 := by
  unfold countdownPark
  dsimp only
  split
  · exact .sameTables rfl rfl
  · exact (Links.sameTables (m := m) (n := {m with nextToken := m.nextToken + 1}) rfl rfl
      |>.trans (Links.observer _ _ _)).emit _

theorem Links.linkScope (p : NativeEff) (table : RowTable) (completed) (m : NativeMachine)
    (mode : Supervision.ScopeMode) (scope : Nat) (target : FiberId)
    (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    Links m (linkScope (interpAt p completed table) m mode scope target who extra).1 := by
  unfold Effect4.Machine.linkScope
  cases hs : (interpAt p completed table).scopeStatus scope m.state with
  | none => exact .sameTables rfl rfl
  | some status =>
    cases status with
    | some exit =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact .sameTables rfl rfl
      | some f => exact (Links.interruptRecord p table completed
          (by simpa only [fiber_id_of_lookup hf] using hf) who extra).emit _
    | none =>
      simp only []
      cases hf : m.fiber? target with
      | none => exact .sameTables rfl rfl
      | some f =>
        simp only []
        split
        · exact .refl m
        · cases hl : (interpAt p completed table).scopeLinkFiber mode scope target m.state with
          | none => exact .sameTables rfl rfl
          | some result =>
            rcases result with ⟨stores, key⟩
            exact ((Links.refl m).store stores |>.trans (Links.observer _ target _)).emit _

theorem Links.filterObservers (m : NativeMachine) (keep : Observer → Bool) :
    Links m (filteredMachine keep m) := by
  constructor
  · constructor
    · intro id f hf hr hp
      exact ⟨filteredFiber keep f, by rw [filtered_lookup, hf]; rfl, hr, hp, rfl⟩
    · intro id f hf hx
      exact ⟨filteredFiber keep f, by rw [filtered_lookup, hf]; rfl, hx⟩
  · exact fun _ race hr => ⟨race, hr, rfl⟩
  · intro id token request hr
    exact Or.inl ((filtered_request keep m id token).trans hr)
  · rintro id ⟨f, hf, hi⟩
    exact ⟨filteredFiber keep f, by rw [filtered_lookup, hf]; rfl, hi⟩

theorem stepFrame_links (interp : NInterp) (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Links m (evaluatePrim.stepFrame interp m f yielding).machine := by
  unfold evaluatePrim.stepFrame evaluatePrim.finishFrame
  dsimp only
  split <;> exact .sameTables rfl rfl

theorem finalizerOr_links (interp : NInterp) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Links m (evaluatePrim.finalizerOr interp m f yielding exit).machine := by
  unfold evaluatePrim.finalizerOr
  repeat' first
    | exact .sameTables rfl rfl
    | exact stepFrame_links _ _ _ _
    | dsimp only
    | split

theorem interruptAs_links (p : NativeEff) (table : RowTable) (completed)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (target who : FiberId) :
    Links m (evaluatePrim.interruptAs (interpAt p completed table) m f yielding target who).machine := by
  unfold evaluatePrim.interruptAs
  cases hf : m.fiber? target with
  | none => exact .refl m
  | some targetFiber =>
    exact (Links.interruptRecord p table completed
      (by simpa only [fiber_id_of_lookup hf] using hf) (some who) _).emit _

theorem withFiber_links (p : NativeEff) (table : RowTable) (completed)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) (action : NAction) :
    Links m (evaluatePrim.withFiber (interpAt p completed table) m f yielding action).machine := by
  cases action <;> unfold evaluatePrim.withFiber <;> dsimp only
  all_goals try exact .sameTables rfl rfl
  case fork code options =>
    split
    · exact (Links.spawn p table completed m f code options).startAfter _ _ _
    · exact (Links.sameTables (m := m) (n := {m with middlewareInstalled := true}) rfl rfl).trans
        ((Links.spawn p table completed _ f code options).startAfter _ _ _)
  case forkIn code options scope => exact (Links.spawn p table completed m f code _).startAfter _ _ _
  case forkScoped code options =>
    split
    · exact (Links.spawn p table completed m f code _).startAfter _ _ _
    · exact .refl m
  case ambientScope => split <;> exact .refl m
  case runIn target scope => exact Links.linkScope p table completed m _ _ _ _ _
  case interruptAs target who => exact interruptAs_links p table completed m f yielding target who
  case interruptScoped target => split <;> exact .refl m
  case awaitAll targets => exact Links.countdown _ m f targets _ _
  case awaitAllFailFast targets => exact Links.countdown _ m f targets _ _
  case awaitNewChildren snapshot => exact Links.countdown _ m f _ _ _
  case raceAll entrants => exact Links.beginRace _ m f yielding entrants
  case setInterruptible code mask => cases mask <;> exact .refl m
  case closeScope scope exit => split <;> exact .sameTables rfl rfl
  case closePar codes => exact Links.forkFinalizers p table completed m f codes
  case dropObservers token => exact Links.filterObservers m _
  case cancelRace id => split <;> exact .refl m

theorem Links.joinPark (m : NativeMachine) (f : NFiber) (target : FiberId) (other : NFiber)
    (hf : m.fiber? target = some other) (mode : Supervision.ObserverMode) :
    Links m (({m with nextToken := m.nextToken + 1} : NativeMachine).update
      {other with observers := other.observers ++ [.resumeAwait f.id m.nextToken mode]}) := by
  have step := (Links.sameTables (m := m) (n := {m with nextToken := m.nextToken + 1}) rfl rfl).trans
    (Links.observer _ target (.resumeAwait f.id m.nextToken mode))
  simpa only [RunMachine.modify, show ({m with nextToken := m.nextToken + 1} : NativeMachine).fiber? target = some other from hf] using step

theorem evaluatePrim_links (p : NativeEff) (table : RowTable) (completed)
    (m : NativeMachine) (f : NFiber) (yielding : Bool) :
    Links m (evaluatePrim (interpAt p completed table) m f yielding).machine := by
  unfold evaluatePrim
  repeat' first
    | exact .sameTables rfl rfl
    | exact Links.registerRace m f yielding _
    | exact Links.countdown _ m f _ _ _
    | exact (Links.joinPark m f _ _ (by assumption) _).emit _
    | exact withFiber_links p table completed m f yielding _
    | exact stepFrame_links _ _ _ _
    | exact finalizerOr_links _ _ _ _ _
    | dsimp only
    | split

theorem exitScoped_links (p : NativeEff) (m : NativeMachine) (f : NFiber)
    (yielding : Bool) (exit : ExitV) :
    Links m (exitScoped p m f yielding exit).machine := by
  unfold exitScoped
  repeat' first
    | exact .sameTables rfl rfl
    | exact evaluatePrim_links _ _ _ _ _ _
    | dsimp only
    | split

theorem evaluateNative_links (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    Links m (evaluateNative p m f yielding table).machine := by
  unfold evaluateNative
  repeat' first
    | exact .sameTables rfl rfl
    | exact evaluatePrim_links _ _ _ _ _ _
    | exact exitScoped_links _ _ _ _ _
    | dsimp only
    | split

theorem iteration_links (p : NativeEff) (table : RowTable) (m : NativeMachine)
    (f : NFiber) (yielding : Bool) :
    letI := evaluatorFor p table
    Links m (iteration (interpOf p table) m f yielding).machine := by
  letI := evaluatorFor p table
  unfold iteration
  dsimp only
  cases hy : injectYield m (countOp (runloopTop f)) yielding with
  | none => exact evaluateNative_links _ _ _ _ _
  | some it =>
    unfold injectYield at hy
    split at hy
    · cases hy
      apply ((Links.refl m).emit _).trans
      exact evaluateNative_links _ _ _ _ _
    · cases hy

end Effect4.Program.Guard.NativeStateLinks
