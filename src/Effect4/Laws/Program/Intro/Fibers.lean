import Effect4.Laws.Program.Intro.Errors

/-!
# Intro.Fibers: the concurrency and fiber family

The introductions of the masks, `yieldNow`, `callback`, `awaitFiber` and every `withFiber`
action.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! #### 4. Concurrency & Fibers family -/

theorem intro_uninterruptible (root : NativeEff) (n : Nat) (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.uninterruptible b)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.uninterruptible b) p) (denoteR root (.uninterruptible b) p) := by
  rw [compileEff_uninterruptible b hf, denoteR_uninterruptible root b hpos]
  have hact : actionAt root p = some (.setInterruptible (resolve root (p.child 0)) false) := by
    simp [actionAt, h]
  unfold denoteAction; rw [hact]
  exact CodeMeans.actMask _ _ _ (.at_ (p.child 0)) _ hact (hres _ (hw0 0)) delivers_pure

theorem intro_interruptible (root : NativeEff) (n : Nat) (b : NativeEff) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw0 : ∀ i, (p.child i).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.interruptible b)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (compileEff (.interruptible b) p) (denoteR root (.interruptible b) p) := by
  rw [compileEff_interruptible b hf, denoteR_interruptible root b hpos]
  have hact : actionAt root p = some (.setInterruptible (resolve root (p.child 0)) true) := by
    simp [actionAt, h]
  unfold denoteAction; rw [hact]
  exact CodeMeans.actMask _ _ _ (.at_ (p.child 0)) _ hact (hres _ (hw0 0)) delivers_pure

theorem intro_yieldNow (root : NativeEff) (priority : Nat) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.yieldNow priority) p) (denoteR root (.yieldNow priority) p) := by
  rw [compileEff_yieldNow priority hf, denoteR_yieldNow root priority hpos]
  exact CodeMeans.yieldNow priority _ delivers_seqR_pure

theorem intro_awaitFiber (root : NativeEff) (t : Term) (mode : Supervision.ObserverMode) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0) :
    CodeMeans root (compileEff (.awaitFiber t mode) p) (denoteR root (.awaitFiber t mode) p) := by
  rw [compileEff_awaitFiber t mode hf, denoteR_awaitFiber root t mode hpos]
  rcases hv : evalTerm p.env t with _ | v
  · exact codeMeans_badShape root
  · cases hfib : Val.fiber? v with
    | some id =>
      obtain ⟨id⟩ := id
      have hv := Val.fiber?_exact hfib
      subst hv
      simp only
      cases p.awaitExit ⟨id⟩ mode with
      | some ex => exact codeMeans_ofExit_pure root ex
      | none =>
        cases mode with
        | joinEffect => exact CodeMeans.joinEffect ⟨id⟩ _ delivers_pure
        | awaitValue => exact CodeMeans.joinValue ⟨id⟩ _ delivers_seqR_pure
    | none =>
      have hb : ∀ id, v ≠ Val.fiber ⟨id⟩ := fun id => Val.fiber?_none hfib ⟨id⟩
      split
      · next id heq => exact absurd (Option.some.inj heq) (hb id)
      · split
        · next id heq => exact absurd (Option.some.inj heq) (hb id)
        · exact codeMeans_badShape root

theorem intro_withFiber (root : NativeEff) (n : Nat) (a : ActionTerm NativeOp) (p : Point) (k : Nat)
    (hf : p.fuel = k + 1) (hpos : p.fuel ≠ 0)
    (hw00 : ((p.child 0).child 0).weight < n)
    (h : Node.at_ (.eff root) p.path = some (.eff (.withFiber a)))
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q))
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) → CodeMeans root (compileEff e p) (denoteR root e p)) :
    CodeMeans root (compileEff (.withFiber a) p) (denoteR root (.withFiber a) p) := by
  cases hfs : forkScoped? a with
  | some co =>
    obtain ⟨child, options⟩ := co
    obtain rfl := forkScoped?_some hfs
    rw [compileEff_forkScoped child options hf, denoteR_withFiber root _ p hpos]
    have hact : actionAt root p = some .ambientScope := by simp [actionAt, h]
    unfold denoteAction; rw [hact]
    simp only [denoteFiberAction, h]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (fiberValR .ambientScope rfl) _ ?_ ?_ rfl (fun _ => rfl)
    · exact CodeMeans.actAmbientScope _ _ hact (successV root)
    · intro completed v
      cases hsc : Val.scope? v with
      | some s =>
        have hv := Val.scope?_exact hsc
        subst hv
        show CodeMeans root (Prim.withFiber (.forkInAt p s))
          (prepareR completed (.vis (.inr (.forkIn ((p.child 0).child 0) options s))
            fun v => .pure (.success v)))
        refine CodeMeans.actForkIn _ (resolve root ((p.child 0).child 0)) options _ s _
          ?_ ?_ (successV root)
        · show forkScopedAt root p s = _
          simp [forkScopedAt, h]
        · exact hres _ hw00
      | none =>
        have hne : ∀ s, v ≠ Val.scopeHandle s := Val.scope?_none hsc
        show CodeMeans root (Program.contAOf root (.forkScopedIn p) v) _
        rw [contAOf_forkScopedIn_other root v hne]
        -- the term's scope row is gone with the reader's `none`: both sides are the refusal
        simp only [seqR]
        exact CodeMeans.failure _
  | none =>
    have hnot : ∀ c o, a ≠ .forkScoped c o := forkScoped?_none hfs
    rw [compileEff_withFiber a hf hnot, denoteR_withFiber root a p hpos]
    obtain ⟨act, hact⟩ : ∃ act, actionAt root p = some act := by
      unfold actionAt; rw [h]; exact ⟨_, rfl⟩
    unfold denoteAction; rw [hact]
    have ht : (interpOf root).withFiberOf (.act p) = some act := hact
    cases act with
    | fork program options =>
      obtain rfl := actionAt_fork h hact
      exact CodeMeans.actFork _ _ _ _ _ ht (hres _ hw00) (successV root)
    | forkIn program options scope =>
      obtain rfl := actionAt_forkIn h hact
      exact CodeMeans.actForkIn _ _ _ _ _ _ ht (hres _ hw00) (successV root)
    | forkScoped program options => exact (actionAt_not_forkScoped h hact).elim
    | runIn target scope => exact CodeMeans.actRunIn _ _ _ _ ht (successV root)
    | interrupt target => exact CodeMeans.actInterrupt _ _ _ ht delivers_seqR_pure
    | interruptAs target who => exact CodeMeans.actInterruptAs _ _ _ _ ht delivers_seqR_pure
    | interruptScoped target => exact CodeMeans.actInterruptScoped _ _ _ ht delivers_seqR_pure
    | interruptAll targets who => exact CodeMeans.actInterruptAll _ _ _ _ ht delivers_seqR_pure
    | awaitAll targets => exact CodeMeans.actAwaitAll _ _ _ ht delivers_seqR_pure
    | awaitAllFailFast targets => exact CodeMeans.actAwaitAllFailFast _ _ _ ht delivers_seqR_pure
    | snapshotChildren => exact CodeMeans.actSnapshotChildren _ _ ht (successV root)
    | awaitNewChildren snapshot =>
      exact CodeMeans.actAwaitNewChildren _ _ _ ht delivers_seqR_pure
    | raceAll entrants =>
      obtain ⟨es, rfl, rfl⟩ := actionAt_raceAll h hact
      have hpts : racePoints root p = entrantPoints es ((p.child 0).child 0) := by
        simp [racePoints, h]
      show CodeMeans root _ (.vis (.inr (.raceAll (racePoints root p))) Effects.Program.pure)
      rw [hpts]
      have hes : Node.at_ (.eff root) ((p.child 0).child 0).path = some (.effs es) :=
        at_child_of (n := .action (.raceAll es)) (at_child_of h 0) 0
      obtain ⟨hlen, hc⟩ := entrants_intro root n ih es _ hw00 hes
      exact CodeMeans.actRaceAll _ _ _ _ ht hlen hc delivers_pure
    | setInterruptible body flag => exact (actionAt_not_setInterruptible h hact).elim
    | setContext ctx => exact CodeMeans.actSetContext _ _ _ ht (successV root)
    | getContext => exact CodeMeans.actGetContext _ _ ht (successV root)
    | getId => exact CodeMeans.actGetId _ _ ht (successV root)
    | closeScope scope ex => exact CodeMeans.actCloseScope _ _ _ _ ht delivers_pure
    | refuse cause => exact CodeMeans.actRefuse _ _ _ ht (successV root)
    | dropObservers token => exact CodeMeans.actDropObservers _ _ _ ht (successV root)
    | cancelRace race => exact CodeMeans.actCancelRace _ _ _ ht delivers_seqR_pure
    | ambientScope =>
      obtain ⟨c, o, heq⟩ := actionAt_ambientScope h hact
      exact absurd heq (hnot c o)
    | closePar fins => exact (actionAt_not_closePar h hact).elim

end Effect4.Program.Sched
