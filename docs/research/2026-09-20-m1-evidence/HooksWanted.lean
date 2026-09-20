import Effect4.Laws.Program.Intro
import Effect4.Laws.Auto.Frames

/-!
# The concrete hook agreements (P3, step 3)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The shared loop
reads code only through the interpreter's code-valued hooks and the fiber core. This module
relates, hook by hook, what `interpOf`/`interpAt` (the frame instance) and `interpR`/
`interpRAt` (the term instance) answer, at the relation of `Means.lean`: completions and
stored programs, exit values, parks, the interrupt programs, a settled race, the cancel
chain, finalizer programs, the scope close, and the generator walks. It also states the
store invariant the deferred cells keep — every stored program is a completion — and its
preservation by the store steps, and the `FiberCore` agreements: each core operation
preserves the saved-state relation.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## The remaining store invariant: scope registration keys are fresh -/

/-- Scope registration keys lie below the fresh-name supply at every reachable registration.
Deferred completion shape is now guaranteed by its data type. -/
structure StoresOk (s : Stores) : Prop where
  keysFresh : s.ScopeKeysFresh

#frame_rules StoresOk

/-- The empty store has no registered scope keys. -/
def M1Hooks.storesOk_empty : ProofGraph.Obligation (StoresOk Stores.empty) := ⟨⟩
#proof_wanted M1Hooks.storesOk_empty

theorem storesOk_empty : StoresOk Stores.empty := by
  aesop (add safe constructors StoresOk) (add safe apply Stores.scopeKeysFresh_empty)

/-- A wake changes only the deferred store, whose frame is generated above. -/
def M1Hooks.storesOk_wakeList {s : Stores} (_hs : StoresOk s) (key : WakeKey) (phase : WakePhase) : ProofGraph.Obligation (StoresOk (Stores.wakeList key phase s)) := ⟨⟩
#proof_wanted M1Hooks.storesOk_wakeList

theorem storesOk_wakeList {s : Stores} (hs : StoresOk s) (key : WakeKey) (phase : WakePhase) :
    StoresOk (Stores.wakeList key phase s) := by
  unfold Stores.wakeList
  split
  · exact StoresOk.frame_deferreds s hs _
  · exact hs

/-- Every store step keeps the registration-key bound. -/
def M1Hooks.storesOk_syncOpStep {s s' : Stores} {o : SyncOp} {v : Val} (_hs : StoresOk s)
    (_h : syncOpStep o s = some (s', v)) : ProofGraph.Obligation (StoresOk s') := ⟨⟩
#proof_wanted M1Hooks.storesOk_syncOpStep

theorem storesOk_syncOpStep {s s' : Stores} {o : SyncOp} {v : Val} (hs : StoresOk s)
    (h : syncOpStep o s = some (s', v)) : StoresOk s' := by
  cases o with
  | deferredMake =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact StoresOk.frame_deferreds s hs _
  | deferredIsDone cell =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | deferredPoll cell =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | deferredCompleteWith cell completion =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact StoresOk.frame_deferreds s hs _
  | deferredInterruptWith cell interruptor =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact StoresOk.frame_deferreds s hs _
  | deferredAwaitCleanup cell waiter token =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact StoresOk.frame_deferreds s hs _
  | clockNow =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact hs
  | sleepCancel waiter token =>
    -- the invariant reads nothing of the timer store
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]; exact StoresOk.frame_timers s hs _
  | scopeMake strategy =>
    -- a new scope holds no registrations, and the supply advances past its handle
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact ⟨(ScopeStore.keysBelow_make hs.keysFresh).mono (Nat.le_succ _)⟩
  | scopeAdd scope finalizer =>
    cases hentry : s.scopes.entryAt scope with
    | none => rw [syncOpStep_scopeAdd_none s scope finalizer hentry] at h; cases h
    | some entry =>
      cases hclose : entry.scope.closingExit? with
      | some exit =>
        -- a closed scope answers its exit and keeps the store
        rw [syncOpStep_scopeAdd_closed s scope finalizer hentry hclose] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
      | none =>
        -- the registration key is the supply's own value, and the supply advances past it
        rw [syncOpStep_scopeAdd_open s scope finalizer hentry hclose] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]
        exact ⟨ScopeStore.keysBelow_addUnsafe_entry hs.keysFresh hentry⟩
  | scopeRemove scope key =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact ⟨ScopeStore.keysBelow_removeFinalizer hs.keysFresh⟩
  | scopeIsClosed scope =>
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact hs
  | scopeFork parent strategy =>
    cases hentry : s.scopes.entryAt parent with
    | none => rw [syncOpStep_scopeFork_none s parent strategy hentry] at h; cases h
    | some entry =>
      rw [syncOpStep_scopeFork_some s parent strategy hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]
      -- the shared key is the supply's successor, and the supply advances past both keys
      exact ⟨ScopeStore.keysBelow_forkChild (m := s.nextName + 2) (shared := s.nextName + 1)
        hs.keysFresh (Nat.le_add_right _ _) (Nat.lt_succ_self _)⟩
  | memoFork parent =>
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact ⟨hs.keysFresh.mono (Nat.le_succ _)⟩
  | memoGet layer memoMap =>
    obtain ⟨_, _, hsc, hn⟩ := syncOpStep_memoGet_families s s' layer memoMap v h
    exact ⟨by change ScopeStore.KeysBelow s'.scopes s'.nextName; rw [hsc, hn]; exact hs.keysFresh⟩
  | memoBuild layer memoMap =>
    -- a layer scope holds no registrations; the Deferred is fresh; the supply advances
    have h' := Prod.mk.inj (Option.some.inj h)
    rw [← h'.1]
    exact ⟨(ScopeStore.keysBelow_make hs.keysFresh).mono (Nat.le_succ _)⟩
  | memoComplete layer memoMap exit =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoComplete_none s layer memoMap exit hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
    | some entry =>
      rw [syncOpStep_memoComplete_some s layer memoMap exit hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]
      exact StoresOk.frame_deferreds s hs _
  | memoRelease layer memoMap =>
    cases hentry : s.memo.entryAt memoMap layer with
    | none =>
      rw [syncOpStep_memoRelease_none s layer memoMap hentry] at h
      rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
    | some entry =>
      by_cases hobs : entry.observers ≤ 1
      · rw [syncOpStep_memoRelease_last s layer memoMap hentry hobs] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
      · rw [syncOpStep_memoRelease_dec s layer memoMap hentry hobs] at h
        rw [← (Prod.mk.inj (Option.some.inj h)).1]; exact hs
  | _ =>
    -- every remaining operation is a `refStep`: only the heap changes
    simp only [syncOpStep, Option.map_eq_some_iff] at h
    obtain ⟨_, _, hf⟩ := h
    rw [← (Prod.mk.inj hf).1]; exact StoresOk.frame_refs s hs _

/-! ## Code-valued hooks -/

/-- The external answers and the stored programs read into related code. -/
theorem completion_means (root : NativeEff) (a : Completion Val Err Defect FiberId Ann) :
    CodeMeans root (embed (completionPrim a)) (denoteCompletion a) := by
  cases a with
  | ofExit ex => cases ex <;> aesop (add safe apply [CodeMeans.success, CodeMeans.failure])
  | ofRefGet cell => exact CodeMeans.syncStore _ _ (successV root)

theorem answerCode_means (root : NativeEff) (a : Completion Val Err Defect FiberId Ann) :
    CodeMeans root ((interpOf root).answerCode a) ((interpR root).answerCode a) :=
  completion_means root a

theorem exitValue_means (root : NativeEff) (ex : ExitV) (mode : Supervision.ObserverMode) :
    CodeMeans root ((interpOf root).exitValue ex mode) ((interpR root).exitValue ex mode) := by
  cases mode
  · exact CodeMeans.success _
  · exact codeMeans_ofExit_pure root ex

theorem parkCode_means (root : NativeEff) (kind : ParkKind) :
    CodeMeans root (Prim.suspend (EffThunk.park kind)) ((interpR root).parkCode kind) := by
  cases kind with
  | join target mode =>
    cases mode
    · exact CodeMeans.joinValue target _ delivers_seqR_pure
    · exact CodeMeans.joinEffect target _ delivers_pure
  | race r => exact CodeMeans.racePark r _ delivers_pure
  | awaitAll targets => exact CodeMeans.awaitAllPark targets _ delivers_seqR_pure

theorem interruptCode_means (root : NativeEff) (target : FiberId) :
    CodeMeans root ((interpOf root).interruptCode target) ((interpR root).interruptCode target) :=
  CodeMeans.actInterrupt _ _ _ rfl delivers_seqR_pure

theorem interruptAsCode_means (root : NativeEff) (target who : FiberId) :
    CodeMeans root ((interpOf root).interruptAsCode target who)
      ((interpR root).interruptAsCode target who) :=
  CodeMeans.actInterruptAs _ _ _ _ rfl delivers_seqR_pure

theorem interruptAllCode_means (root : NativeEff) (targets : List FiberId) :
    CodeMeans root ((interpOf root).interruptAllCode targets) ((interpR root).interruptAllCode targets) :=
  CodeMeans.actInterruptAll _ _ _ _ rfl delivers_seqR_pure

/-- The restoring continuation the core composes (`onSuccess` at a `restore` name). -/
theorem restore_means (root : NativeEff) {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂)
    (ex : ExitV) :
    CodeMeans root (Prim.onSuccess c₁ (EffName.restore ex)) (restoreR c₂ (EffName.restore ex)) := by
  show CodeMeans root (Prim.onSuccess c₁ (EffName.restore ex)) ((guardR .onSuccess c₂).bind _)
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ c₂ _ hc ?_ rfl (fun _ => rfl)
  intro completed v
  exact codeMeans_ofExit_pure root ex

/-- The injected yield wrapper. -/
theorem yieldBefore_means (root : NativeEff) {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂) :
    CodeMeans root (Prim.onSuccessConst (Prim.yieldNowWith 0) c₁) (termCore.yieldBefore c₂) := by
  show CodeMeans root (Prim.onSuccessConst (Prim.yieldNowWith 0) c₁) ((guardR .onSuccess _).bind _)
  rw [guardR_bind]
  refine CodeMeans.onSuccessConst _ _ _ _ _ (CodeMeans.yieldNow 0 _ delivers_seqR_pure) ?_ rfl
    (fun _ => rfl)
  intro completed v
  exact hc.prepare completed

theorem raceSettle_means (root : NativeEff) (race : Nat) (needed : Bool) (ex : ExitV) :
    CodeMeans root ((interpOf root).raceSettle race needed ex)
      ((interpR root).raceSettle race needed ex) := by
  cases needed
  · cases ex <;> first | exact CodeMeans.success _ | exact CodeMeans.failure _
  · show CodeMeans root (Prim.onSuccess _ _) ((guardR .onSuccess _).bind _)
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _
      (.vis (.inr (.mask false (.raceCleanup race))) Effects.Program.pure) _ ?_ ?_ rfl (fun _ => rfl)
    · exact CodeMeans.actMask _ _ _ (.raceCleanup race) _ rfl
        (CodeMeans.actCancelRace _ _ _ rfl delivers_seqR_pure) delivers_pure
    · intro completed v
      show CodeMeans root (embed (Prim.ofExit ex)) (prepareR completed (.pure ex))
      cases ex <;> first | exact CodeMeans.success _ | exact CodeMeans.failure _

theorem cancelProgramOf_means (root : NativeEff) (name : EffName) :
    CodeMeans root (cancelProgramOf name) (denoteCancel name) := by
  cases name <;> try exact CodeMeans.success _
  case withWaiter base waiter token =>
    cases base <;> try exact CodeMeans.success _
    case cancelAwait cell => exact CodeMeans.syncOp _ _ (successV root)
    case store n =>
      cases n <;> try exact CodeMeans.success _
      case cancelAwait cell => exact CodeMeans.syncStore _ _ (successV root)
      case cancelSleep => exact CodeMeans.syncStore _ _ (successV root)
      case cancelPark => exact CodeMeans.actDropObservers _ _ _ rfl (successV root)
      case cancelRace r => exact CodeMeans.actCancelRace _ _ _ rfl delivers_seqR_pure
  case store n =>
    cases n <;> try exact CodeMeans.success _
    case withWaiter base waiter token =>
      cases base <;> try exact CodeMeans.success _
      case cancelAwait cell => exact CodeMeans.syncStore _ _ (successV root)
      case cancelSleep => exact CodeMeans.syncStore _ _ (successV root)
      case cancelPark => exact CodeMeans.actDropObservers _ _ _ rfl (successV root)
      case cancelRace r => exact CodeMeans.actCancelRace _ _ _ rfl delivers_seqR_pure

theorem cancelThenFail_means (root : NativeEff) (name : EffName) (cause : CauseV) :
    CodeMeans root ((interpOf root).cancelThenFail name cause)
      ((interpR root).cancelThenFail name cause) := by
  show CodeMeans root (Prim.onSuccess (cancelProgramOf name) (EffName.reFail cause))
    ((guardR .onSuccess (denoteCancel name)).bind _)
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (denoteCancel name) _ (cancelProgramOf_means root name) ?_ rfl
    (fun _ => rfl)
  intro completed v
  exact CodeMeans.failure _

theorem denoteFin_means (root : NativeEff) (fin : FinName) (ex : ExitV) :
    CodeMeans root (embed (finProgram fin ex)) (denoteFin fin ex) := by
  cases fin with
  | interruptFiber fiber skip =>
    cases skip
    · exact CodeMeans.actInterrupt _ _ _ rfl delivers_seqR_pure
    · exact CodeMeans.actInterruptScoped _ _ _ rfl delivers_seqR_pure
  | closeChildScope scope => exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | detachFromParent parent key => exact CodeMeans.syncStore _ _ (successV root)
  | release label fails =>
    cases fails
    · exact CodeMeans.success _
    · exact CodeMeans.failure _
  | parkThen slot => exact CodeMeans.asyncExternal slot _ delivers_pure
  | awaitNewChildren snapshot => exact CodeMeans.actAwaitNewChildren _ _ _ rfl delivers_seqR_pure
  -- a capture's release resolves at its point, on any view, by the introduction
  | foreign c => exact foreignRelease_intro root c ex fun completed => resolve_intro root _
  | closeChildOnFailure scope =>
    cases ex with
    | success _ => exact CodeMeans.success _
    | failure _ => exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | memoDone layer memoMap => exact CodeMeans.syncStore _ _ (successV root)
  -- `observers--`, then the last observer's release closes the layer scope the store answered
  | memoEntry layer memoMap =>
    show CodeMeans root
      (Prim.onSuccess (Prim.sync (.store (.op (.memoRelease layer memoMap))))
        (.store (.closeIfLast ex)))
      ((guardR .onSuccess (storeR (.memoRelease layer memoMap))).bind (seqR fun v =>
        match Val.scope? v with
        | some s => .vis (.inr (.closeScope s ex)) Effects.Program.pure
        | none => .pure (.success .unit)))
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (storeR (.memoRelease layer memoMap)) _
      (CodeMeans.syncStore _ _ (successV root)) ?_ rfl (fun _ => rfl)
    intro completed v
    cases hs : Val.scope? v with
    | some s =>
      obtain rfl := Val.scope?_exact hs
      exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
    | none =>
      show CodeMeans root (embed (Effect4.Machine.contAOf (Name.closeIfLast ex) v))
        (prepareR completed (match Val.scope? v with
          | some s => .vis (.inr (.closeScope s ex)) Effects.Program.pure
          | none => .pure (.success .unit)))
      rw [contAOf_closeIfLast_other ex v (Val.scope?_none hs), hs]
      exact CodeMeans.success _

/-- The term's body hook is the denotation, at every view. -/
theorem bodyR_eq (root : NativeEff) (completed : List (FiberId × ExitV)) (b : Body) :
    bodyR (interpRAt root completed) b = denoteBody root b :=
  by aesop

theorem body_means (root : NativeEff) (b : Body) :
    ∀ {c : NCode}, (match b with
      | .at_ p => c = resolve root p
      | .fin fin ex => c = embed (finProgram fin ex)
      | .raceCleanup race => c = embed (Prim.withFiber (Thunk.act (ActionName.cancelRace race)))
      | .acquireIn p ctx =>
        c = Prim.onSuccess (Prim.withFiber (.store (.act .ambientScope))) (.acquireIn p ctx)
      | .release q previous => c = Prim.onExit (resolve root q) (.restoreCtx previous) false
      | .layerBuild q m scope => c = resolveLayer root q m scope) →
      CodeMeans root c (denoteBody root b) := by
  intro c hc
  cases b with
  | at_ p => rw [hc]; exact resolve_intro root p
  | fin fin ex => rw [hc]; exact denoteFin_means root fin ex
  | raceCleanup race => rw [hc]; exact CodeMeans.actCancelRace _ _ _ rfl delivers_seqR_pure
  | acquireIn p ctx =>
    rw [hc]
    exact acquireIn_intro root p ctx (resolve_intro root _) fun a ex =>
      foreignRelease_intro root _ ex fun completed => resolve_intro root _
  | release q previous => rw [hc]; exact release_intro root q previous (resolve_intro root q)
  | layerBuild q m scope => rw [hc]; exact layerBuild_intro root q m scope

/-- The finalizer programs: both instances name the same finalizers, with related programs. -/
theorem finalizerProgram_means (root : NativeEff) (completed : List (FiberId × ExitV))
    (name : EffName) (ex : ExitV) :
    OptRel (CodeMeans root) ((interpAt root completed).finalizerProgram name ex)
      ((interpRAt root completed).finalizerProgram name ex) := by
  cases name <;> try exact True.intro
  case fin p => exact resolve_intro root _
  case scopeClose scope => exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  case restoreCtx previous => exact CodeMeans.actSetContext _ _ _ rfl (successV root)
  case store n =>
    cases n <;> try exact True.intro
    case finalizerName fin => exact denoteFin_means root fin ex

/-- The parallel close's daemons, pairwise. -/
theorem closePar_zip (root : NativeEff) (ex : ExitV) : ∀ (order : List FinName),
    ∀ x ∈ ((order.map fun fin => finProgram fin ex).map embed).zip
      (order.map fun fin => denoteFin fin ex), CodeMeans root x.1 x.2
  | [], _, hx => by simp at hx
  | fin :: rest, x, hx => by
    simp only [List.map_cons, List.zip_cons_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact denoteFin_means root fin ex
    · exact closePar_zip root ex rest x hx

/-- The unsafe close: the same state, no program or related programs. -/
theorem closeScopeUnsafe_means (root : NativeEff) (scope : Nat) (ex : ExitV) (flag : Bool)
    (s : Stores) :
    OptRel (fun (a : Stores × Option Program) (b : Stores × Option RProgram) =>
        a.1 = b.1 ∧ OptRel (fun p q => CodeMeans root (embed p) q) a.2 b.2)
      (storesCloseScopeUnsafe scope ex flag s) (closeScopeUnsafeR scope ex flag s) := by
  unfold storesCloseScopeUnsafe closeScopeUnsafeR
  cases hs : scopeCloseSnapshot scope ex s with
  | none => exact True.intro
  | some r =>
    obtain ⟨st, strategy, order⟩ := r
    refine ⟨rfl, ?_⟩
    cases order with
    | nil => exact True.intro
    | cons fin rest =>
      cases rest with
      | nil => exact denoteFin_means root fin ex
      | cons fin' rest' =>
        show CodeMeans root (Prim.suspend (EffThunk.store (Thunk.body (ProgName.closeWalk strategy _ ex))))
          (closeWalkR strategy _ ex)
        refine CodeMeans.closeWalk strategy _ ex _ fun completed => ?_
        show CodeMeans root (embed (progOf (ProgName.closeWalk strategy _ ex)))
          (.vis (.inr (.closeIter strategy _ ex)) Effects.Program.pure)
        cases strategy with
        | sequential => exact CodeMeans.closeIterSeq _ ex _ delivers_pure
        | parallel =>
          exact CodeMeans.actClosePar _ _ _ ex _ rfl (by simp [List.length_map])
            (closePar_zip root ex _) delivers_pure

/-- `Scope.close`: the unsafe close's program, or the void success, related. -/
theorem closeScope_means (root : NativeEff) (scope : Nat) (ex : ExitV) (flag : Bool) (id : FiberId)
    (s : Stores) :
    OptRel (fun (a : Stores × NCode) (b : Stores × RProgram) => a.1 = b.1 ∧ CodeMeans root a.2 b.2)
      ((interpOf root).closeScope scope ex flag id s) ((interpR root).closeScope scope ex flag id s) := by
  have h := closeScopeUnsafe_means root scope ex flag s
  show OptRel _ ((storesCloseScope scope ex flag s).map fun r => (r.1, embed r.2))
    (closeScopeR scope ex flag s)
  unfold storesCloseScope closeScopeR
  revert h
  cases storesCloseScopeUnsafe scope ex flag s with
  | none =>
    cases closeScopeUnsafeR scope ex flag s with
    | none => intro _; exact True.intro
    | some _ => intro h; exact absurd h not_false
  | some a =>
    cases closeScopeUnsafeR scope ex flag s with
    | none => intro h; exact absurd h not_false
    | some b =>
      intro h
      obtain ⟨a₁, a₂⟩ := a
      obtain ⟨b₁, b₂⟩ := b
      obtain ⟨h₁, h₂⟩ := h
      refine ⟨h₁, ?_⟩
      cases a₂ with
      | none =>
        cases b₂ with
        | none => exact CodeMeans.success _
        | some _ => exact absurd h₂ not_false
      | some p =>
        cases b₂ with
        | none => exact absurd h₂ not_false
        | some q => exact h₂

/-! ## The generator walks: `runStmts` at the frame, `walkR` at the term -/

/-- The steps of the two walks: the same fold, the same halt, related resumed code under the
same advanced name. -/
inductive StepRel (root : NativeEff) :
    IterStep EffName EffThunk Val Err Defect FiberId Ann NCode →
      IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
  | done (v : Val) : StepRel root (.done v) (.done v)
  | halt (c : CauseV) : StepRel root (.halt c) (.halt c)
  | resume {code : NCode} {code' : RProgram} (name : EffName) (h : CodeMeans root code code') :
      StepRel root (.resume code name) (.resume code' name)

/-- The yield statement at a block position is a source node at its own address. -/
theorem at_yield {root : NativeEff} {p : Point} {pc : List Nat} {s : Stmt NativeOp}
    {rest : Stmts NativeOp} (h : blockAt root p pc = some (.cons s rest)) {e : NativeEff}
    (hs : s = .bindYield e ∨ s = .yieldDiscard e) :
    Node.at_ (.eff root) (p.path ++ [0] ++ pc ++ [0, 0]) = some (.eff e) := by
  have hb : Node.at_ (.eff root) (p.path ++ [0] ++ pc) = some (.stmts (.cons s rest)) := by
    unfold blockAt at h
    rcases hn : Node.at_ (.eff root) (p.path ++ [0] ++ pc) with _ | n
    · rw [hn] at h; cases h
    · rw [hn] at h
      cases n with
      | stmts ss => cases h; rfl
      | _ => cases h
  have e1 : p.path ++ [0] ++ pc ++ [0, 0] = ((p.path ++ [0] ++ pc) ++ [0]) ++ [0] := by
    simp [List.append_assoc]
  rw [e1, Node.at_append, Node.at_append, hb]
  rcases hs with rfl | rfl <;> rfl

/-- One yield step of the two walks agrees, given that the walks agree at the fuel below. -/
theorem yieldOf_rel (root : NativeEff) (p : Point) (fuel : Nat)
    (ih : ∀ pc env folded,
      (runStmts root p fuel pc env folded).1 = (walkR root p fuel pc env folded).1 ∧
        StepRel root (runStmts root p fuel pc env folded).2 (walkR root p fuel pc env folded).2)
    (e : NativeEff) (bind : Bool) (pc : List Nat) (env folded : List Val)
    (he : Node.at_ (.eff root) (p.path ++ [0] ++ pc ++ [0, 0]) = some (.eff e)) :
    (runStmts.yieldOf root p e bind fuel pc env folded).1 =
        (walkR.yieldOf root p e bind fuel pc env folded).1 ∧
      StepRel root (runStmts.yieldOf root p e bind fuel pc env folded).2
        (walkR.yieldOf root p e bind fuel pc env folded).2 := by
  unfold runStmts.yieldOf walkR.yieldOf
  dsimp only
  rw [inlineYield_eq_headExit]
  have hc := code_intro root e { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 } he
  cases hcomp : compileEff e { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 } <;>
    first
    | exact ih _ _ _
    | exact ⟨rfl, StepRel.halt _⟩
    | (rw [hcomp] at hc; exact ⟨rfl, StepRel.resume _ hc⟩)

/-- **The generator walks agree.** -/
theorem runStmts_walkR (root : NativeEff) (p : Point) : ∀ (fuel : Nat) (pc : List Nat) (env folded : List Val),
    (runStmts root p fuel pc env folded).1 = (walkR root p fuel pc env folded).1 ∧
      StepRel root (runStmts root p fuel pc env folded).2 (walkR root p fuel pc env folded).2 := by
  intro fuel
  induction fuel with
  | zero =>
    intro pc env folded
    rw [runStmts, walkR]
    refine ⟨rfl, StepRel.resume _ ?_⟩
    exact CodeMeans.frontier _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ fun completed => by
      rw [suspendBodyAt_zero' rfl]; rfl
  | succ fuel ih =>
    intro pc env folded
    rw [runStmts, walkR]
    cases hb : blockAt root p pc with
    | none => exact ⟨rfl, StepRel.halt _⟩
    | some ss =>
      cases ss with
      | nil =>
        dsimp only
        cases blockExit root p pc env with
        | none => exact ⟨rfl, StepRel.done _⟩
        | some next => exact ih _ _ _
      | cons s rest =>
        dsimp only
        cases s with
        | bindYield e => exact yieldOf_rel root p fuel ih e true pc env folded (at_yield hb (Or.inl rfl))
        | yieldDiscard e => exact yieldOf_rel root p fuel ih e false pc env folded (at_yield hb (Or.inr rfl))
        | ret v =>
          dsimp only
          cases evalTerm env v with
          | some value => exact ⟨rfl, StepRel.done _⟩
          | none => exact ⟨rfl, StepRel.halt _⟩
        | ifElse test a b =>
          dsimp only
          cases evalTerm env test with
          | none => exact ⟨rfl, StepRel.halt _⟩
          | some v =>
            cases v <;> try exact ⟨rfl, StepRel.halt _⟩
            case bool flag => cases flag <;> exact ih _ _ _
        | whileTrue body => exact ih _ _ _
        | breakLoop =>
          dsimp only
          cases loopExit root (pc.length + 1) p pc env with
          | some next => exact ih _ _ _
          | none => exact ⟨rfl, StepRel.halt _⟩

/-- The iterator hook: the same folds and related steps, for every generator name. -/
theorem iterNext_means (root : NativeEff) (completed : List (FiberId × ExitV)) (name : EffName)
    (value : Val) :
    ((interpAt root completed).iterNext name value).1 =
        ((interpRAt root completed).iterNext name value).1 ∧
      StepRel root ((interpAt root completed).iterNext name value).2
        ((interpRAt root completed).iterNext name value).2 := by
  cases name with
  | gen p pc bind => exact runStmts_walkR root { p with completed } p.fuel pc _ []
  | store n =>
    cases n with
    | closeSeq remaining exit captured =>
      show ([], embedStep (closeSeqStep remaining exit captured value)).1 = ([], closeSeqStepR remaining exit captured value).1 ∧
        StepRel root (embedStep (closeSeqStep remaining exit captured value)) (closeSeqStepR remaining exit captured value)
      refine ⟨rfl, ?_⟩
      unfold closeSeqStep closeSeqStepR
      cases remaining with
      | nil =>
        show StepRel root (embedStep (closeDone _)) (closeDone _)
        cases captured ++ reasonsOfVal value with
        | nil => exact StepRel.done _
        | cons r rs => exact StepRel.halt _
      | cons fin rest =>
        refine StepRel.resume _ ?_
        show CodeMeans root (Prim.exitFrame (embed (finProgram fin exit))) ((guardR .all (denoteFin fin exit)).bind _)
        rw [guardR_bind]
        exact CodeMeans.exitFrame _ _ (denoteFin fin exit) _ (denoteFin_means root fin exit)
          (fun _ _ => CodeMeans.success _) rfl (fun _ => rfl)
    | closeParDone =>
      show ([], embedStep (closeDone (reasonsOfVal value))).1 = ([], closeDone (reasonsOfVal value)).1 ∧
        StepRel root (embedStep (closeDone (reasonsOfVal value))) (closeDone (reasonsOfVal value))
      refine ⟨rfl, ?_⟩
      cases reasonsOfVal value with
      | nil => exact StepRel.done _
      | cons r rs => exact StepRel.halt _
    | _ => exact ⟨rfl, StepRel.done value⟩
  | _ => exact ⟨rfl, StepRel.done value⟩

/-- The frame's and the term's loop decisions agree: both continue at one cursor with related
bodies, or both finish with related codes. The one relation the loop's two hooks need. -/
inductive LoopNextMeans (root : NativeEff) : LoopNext Val NCode → LoopNext Val RProgram → Prop
  | «continue» (cursor : Val) {body₁ : NCode} {body₂ : RProgram} (h : CodeMeans root body₁ body₂) :
      LoopNextMeans root (.continue cursor body₁) (.continue cursor body₂)
  | finish {code₁ : NCode} {code₂ : RProgram} (h : CodeMeans root code₁ code₂) :
      LoopNextMeans root (.finish code₁) (.finish code₂)

/-- At one point, the compile's and the reference's loop end agree: the same result term over
the same cursor, or the wrong shape on both sides. -/
theorem loopFinishAt_means (root : NativeEff) (q : Point) (cursor : Val) :
    CodeMeans root (loopFinishAt root q cursor) (loopFinishRAt root q cursor) := by
  unfold loopFinishAt loopFinishRAt
  cases loopResultAt root q with
  | none => exact codeMeans_badShape root
  | some result =>
    dsimp only
    cases evalTerm (q.env ++ [cursor]) result with
    | none => exact codeMeans_badShape root
    | some answer => exact CodeMeans.success _

/-- At one point, the compile's and the reference's test agree arm by arm. -/
theorem loopNextAt_means (root : NativeEff) (q : Point) (cursor : Val) :
    LoopNextMeans root (loopNextAt root q cursor) (loopNextRAt root q cursor) := by
  unfold loopNextAt loopNextRAt
  cases loopAt root q with
  | none => exact .finish (codeMeans_badShape root)
  | some loop =>
    obtain ⟨test, step, body⟩ := loop
    dsimp only
    cases evalTerm (q.env ++ [cursor]) test with
    | none => exact .finish (codeMeans_badShape root)
    | some v =>
      cases v with
      | bool flag =>
        cases flag with
        | true => exact .continue cursor (resolve_intro root _)
        | false => exact .finish (loopFinishAt_means root q cursor)
      | _ => exact .finish (codeMeans_badShape root)

/-- At one point, the compile's and the reference's step-then-test agree. -/
theorem loopResumeAt_means (root : NativeEff) (q : Point) (cursor answer : Val) :
    LoopNextMeans root (loopResumeAt root q cursor answer) (loopResumeRAt root q cursor answer) := by
  unfold loopResumeAt loopResumeRAt
  cases loopAt root q with
  | none => exact .finish (codeMeans_badShape root)
  | some loop =>
    obtain ⟨test, step, body⟩ := loop
    dsimp only
    cases evalTerm (q.env ++ [cursor, answer]) step with
    | none => exact .finish (codeMeans_badShape root)
    | some next => exact loopNextAt_means root q next

theorem loopAt_congr (root : NativeEff) {p p' : Point} (h : p'.path = p.path) :
    loopAt root p' = loopAt root p := by
  simp [loopAt, h]

/-- Two points that differ at most in the captured view are one point at a given view. -/
theorem point_congr {p p' : Point}
    (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
    (completed : List (FiberId × ExitV)) :
    ({ p' with completed } : Point) = ({ p with completed } : Point) :=
  by aesop

theorem childWith_congr {p p' : Point}
    (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
    (completed : List (FiberId × ExitV)) (i : Nat) (v : Val) :
    ({ p' with completed } : Point).childWith i v = ({ p with completed } : Point).childWith i v :=
  by aesop

/-- The loop hooks of loops named up to the captured view are related, entering and
resuming. -/
theorem loopEnter_means (root : NativeEff) (completed : List (FiberId × ExitV)) {p p' : Point}
    (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
    (cursor : Val) :
    LoopNextMeans root ((interpAt root completed).loopEnter (.loop p') cursor)
      ((interpRAt root completed).loopEnter (.loop p) cursor) := by
  show LoopNextMeans root (loopNextAt root ({ p' with completed } : Point) cursor)
    (loopNextRAt root ({ p with completed } : Point) cursor)
  rw [point_congr hp completed]
  exact loopNextAt_means root _ cursor

theorem loopResume_means (root : NativeEff) (completed : List (FiberId × ExitV)) {p p' : Point}
    (hp : p'.path = p.path ∧ p'.env = p.env ∧ p'.fuel = p.fuel ∧ p'.tape = p.tape ∧ p'.root = p.root)
    (cursor answer : Val) :
    LoopNextMeans root ((interpAt root completed).loopResume (.loop p') cursor answer)
      ((interpRAt root completed).loopResume (.loop p) cursor answer) := by
  show LoopNextMeans root (loopResumeAt root ({ p' with completed } : Point) cursor answer)
    (loopResumeRAt root ({ p with completed } : Point) cursor answer)
  rw [point_congr hp completed]
  exact loopResumeAt_means root _ cursor answer

/-! ## The fiber core: every operation preserves the saved-state relation -/

theorem means_answerWith {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂)
    {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂) :
    Means root { f₁ with current := c₁ } { f₂ with current := c₂ } :=
  ⟨h.1, h.2.1, h.2.2.1, hc, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem means_start (root : NativeEff) {c₁ : NCode} {c₂ : RProgram} (hc : CodeMeans root c₁ c₂)
    (flag : Bool) :
    Means root { FrameFiber.start c₁ with interruptible := flag } ⟨c₂, [], flag, none, false⟩ :=
  ⟨rfl, rfl, rfl, hc, StackMeans.nil, trivial⟩

theorem pendingCause_eq {f₁ : FFiber} {f₂ : RSaved} (h : f₁.interruptedCause = f₂.interruptedCause) :
    f₁.pendingCause = f₂.pendingCause := by
  unfold FrameFiber.pendingCause RSaved.pendingCause
  rw [h]
  cases f₂.interruptedCause <;> rfl

theorem means_pendingFailure {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂) :
    Means root { f₁ with deferredInterrupt := false, current := Prim.failure f₁.pendingCause }
      { f₂ with current := .pure (.failure f₂.pendingCause), deferredInterrupt := false } := by
  refine ⟨h.1, h.2.1, rfl, ?_, h.2.2.2.2.1, h.2.2.2.2.2⟩
  rw [pendingCause_eq h.2.1]
  exact CodeMeans.failure _

theorem means_recordCause {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂)
    (cause : CauseV) :
    Means root { f₁ with interruptedCause := some cause } { f₂ with interruptedCause := some cause } :=
  ⟨h.1, rfl, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem means_setDeferred {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂)
    (flag : Bool) :
    Means root { f₁ with deferredInterrupt := flag } { f₂ with deferredInterrupt := flag } :=
  ⟨h.1, h.2.1, rfl, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem means_pushAsyncFinalizer {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂)
    (name : EffName) :
    Means root { f₁ with stack := Prim.asyncFinalizer name :: f₁.stack }
      { f₂ with stack := .asyncFinalizer name :: f₂.stack } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, StackMeans.slot (SlotMeans.asyncFinalizer name) h.2.2.2.2.1,
    h.2.2.2.2.2⟩

theorem means_pushIterator {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂)
    (name : EffName) (cursor : Val) :
    Means root { f₁ with stack := Prim.iterator name cursor :: f₁.stack }
      { f₂ with stack := .iter name :: f₂.stack } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, StackMeans.slot (SlotMeans.iterator name cursor) h.2.2.2.2.1,
    h.2.2.2.2.2⟩

theorem means_clearStack {root : NativeEff} {f₁ : FFiber} {f₂ : RSaved} (h : Means root f₁ f₂) :
    Means root { f₁ with stack := [] } { f₂ with stack := [] } :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, StackMeans.nil, trivial⟩

end Effect4.Program.Sched
