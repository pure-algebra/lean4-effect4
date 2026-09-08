import Effect4.Program.Means

/-!
# Source-address introduction (P3, step 3)

Packet: `Test/contracts/program-runtime-r.contract.md` (the P3 relation). The relation of
`Means.lean` is inhabited at every source address: the frame's compile and the term's
denotation of one node at one point are related (`code_intro`), and so are the programs the
names and thunks of `interpOf` build from addresses (`resolve_intro`). The descent is on
the point's weight (its fuel plus its tape): every child point spends one unit of fuel and
a `choose` one decision, so no structural recursion into the mutual source family is
needed. The term's construction heads never sit at the head of a denotation, so `prepareR`
is the identity on it (`prepareR_denoteR`); the guard clauses' continuations resolve their
constructions against the view the frame's refreshed names read.
-/

set_option autoImplicit false

namespace Effect4.Program.Sched

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Denote Effect4.Program.Agreement

/-! ## Small facts about exits and delivering continuations -/

theorem codeMeans_badShape (root : NativeEff) : CodeMeans root badShape (.pure badShapeExit) :=
  CodeMeans.failure _

theorem codeMeans_ofExit_pure (root : NativeEff) (ex : ExitV) :
    CodeMeans root (Prim.ofExit ex) (.pure ex) := by
  cases ex
  · exact CodeMeans.success _
  · exact CodeMeans.failure _

theorem codeMeans_finish (root : NativeEff) (ex : ExitV) (k : ExitV → RProgram) :
    CodeMeans root (Prim.ofExit ex) (.vis (.inr (.finishFinalizer ex)) k) := by
  cases ex
  · exact CodeMeans.finishSuccess _ _
  · exact CodeMeans.finishFailure _ _

theorem delivers_seqR_pure : Delivers (seqR fun v => Effects.Program.pure (.success v)) := by
  intro ex; cases ex <;> exact Or.inl rfl

theorem successV (root : NativeEff) :
    ∀ v, CodeMeans root (Prim.success v) (Effects.Program.pure (.success v)) :=
  fun v => CodeMeans.success v

/-! ## Guards under `bind` and `prepareR` -/

/-- A guard followed by a tail: the tail runs after the closing marker in the normal branch
and directly on the saved branch. -/
theorem guardR_bind (kind : GuardKind) (body : RProgram) (t : ExitV → RProgram) :
    (guardR kind body).bind t =
      .vis (.inr (.guard_ kind)) fun
        | none => body.bind (unguardTail t)
        | some ex => t ex := by
  refine congrArg (@Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.guard_ kind)))
    (funext fun o => ?_)
  cases o with
  | none =>
    show (body.bind fun ex => @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.unguard ex))
      Effects.Program.pure).bind t = body.bind (unguardTail t)
    rw [Effects.Program.bind_assoc]
    rfl
  | some ex => rfl

theorem prepareR_guardR_bind (completed : List (FiberId × ExitV)) (kind : GuardKind)
    (body : RProgram) (t : ExitV → RProgram) :
    prepareR completed ((guardR kind body).bind t) =
      (guardR kind (prepareR completed body)).bind t := by
  rw [guardR_bind, guardR_bind]
  refine congrArg (@Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.guard_ kind)))
    (funext fun o => ?_)
  cases o with
  | none => exact prepareR_bind completed (delivers_unguardTail t) body
  | some ex => rfl

/-- A construction query at the head resolves against the view. -/
theorem prepareR_constructR (completed : List (FiberId × ExitV))
    (k : List (FiberId × ExitV) → RProgram) :
    prepareR completed (constructR k) = prepareR completed (k completed) := rfl

theorem prepareR_denoteSleep (r : Term) (p : Point) (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteSleep r p) = denoteSleep r p := by
  unfold denoteSleep
  cases (evalTerm p.env r).bind NativeOp.sleepMillisOf with
  | none => rfl
  | some n => cases n <;> rfl

theorem prepareR_denoteAsync (r : Term) (p : Point) (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteAsync r p) = denoteAsync r p := by
  unfold denoteAsync
  cases evalTerm p.env r with
  | none => rfl
  | some v =>
    dsimp only
    cases NativeOp.awaitCellOf v <;> rfl

theorem prepareR_denoteAction (root : NativeEff) (p : Point) (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteAction root p) = denoteAction root p := by
  unfold denoteAction
  cases actionAt root p with
  | none => rfl
  | some act =>
    cases act <;> try rfl
    show prepareR completed (denoteFiberAction root p .ambientScope) =
      denoteFiberAction root p .ambientScope
    simp only [denoteFiberAction]
    split
    · rw [prepareR_guardR_bind]; rfl
    · rfl

/-! ## The denotation, one arm at a time, at positive fuel -/

section denoteEqs

variable (root : NativeEff) {p : Point}

theorem denoteR_succeed (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.succeed t) p =
      .pure (match evalTerm p.env t with | some v => .success v | none => badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_fail (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.fail t) p =
      .pure (match evalTerm p.env t with
        | some v => .failure (Cause.fail (errOf v)) | none => badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_failCause (c : CauseTerm) (h : p.fuel ≠ 0) :
    denoteR root (.failCause c) p =
      .pure (match causeOf p.env c with | some cause => .failure cause | none => badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_yieldError (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.yieldError t) p =
      (match evalTerm p.env t with
       | some v => suspendR p (.pure (.failure (Cause.fail (errOf v))))
       | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_sync (t : Term) (h : p.fuel ≠ 0) :
    denoteR root (.sync t) p =
      .vis (.inr (.sync ((evalTerm p.env t).getD Val.unit))) fun v => .pure (.success v) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_perform (op : NativeOp) (r : Term) (h : p.fuel ≠ 0) :
    denoteR root (.perform op r) p =
      (match (NativeOp.row op).kind with
       | .sync =>
         match (evalTerm p.env r).bind (NativeOp.syncOpOf op) with
         | some operation => .vis (.inl operation) fun v => .pure (.success v)
         | none => .pure badShapeExit
       | .async => denoteAsync r p
       | .program => pending .unsupported p) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_catchCause (b hd : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.catchCause b hd) p =
      (guardR .onFailure (denoteR root b (p.child 0))).bind fun
        | .success v => .pure (.success v)
        | .failure c => constructR fun completed =>
            denoteR root hd ({ p with completed }.childWith 1 (.exitErr c)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_matchCause (b v c : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.matchCause b v c) p =
      (guardR .all (denoteR root b (p.child 0))).bind fun
        | .success x => constructR fun completed =>
            denoteR root v ({ p with completed }.childWith 1 x)
        | .failure cause => constructR fun completed =>
            denoteR root c ({ p with completed }.childWith 2 (.exitErr cause)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_onExit (b f : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.onExit b f) p =
      onExitR (denoteR root b (p.child 0)) fun ex =>
        constructR fun completed => denoteR root f ({ p with completed }.childWith 1 (reifyExitVal ex)) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_yieldNow (priority : Nat) (h : p.fuel ≠ 0) :
    denoteR root (.yieldNow priority) p =
      .vis (.inr (.yieldNow priority)) fun v => .pure (.success v) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_callback (op : NativeOp) (r : Term) (h : p.fuel ≠ 0) :
    denoteR root (.callback op r) p =
      (match op with
       | .sleep => denoteSleep r p
       | _ => match (NativeOp.row op).kind with
         | .async => denoteAsync r p
         | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => cases op <;> (rw [denoteR, hf]; try rfl) <;> (try (intro h; cases h))

theorem denoteR_awaitFiber (t : Term) (mode : Supervision.ObserverMode) (h : p.fuel ≠ 0) :
    denoteR root (.awaitFiber t mode) p =
      (match evalTerm p.env t with
       | some (Val.fiber ⟨id⟩) =>
         match p.awaitExit ⟨id⟩ mode with
         | some exit => .pure exit
         | none => match mode with
           | .joinEffect => .vis (.inr (.await ⟨id⟩ .joinEffect)) Effects.Program.pure
           | .awaitValue => .vis (.inr (.await ⟨id⟩ .awaitValue)) fun v => .pure (.success v)
       | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

/-- The `forkScoped` wrapper's continuation on anything but a scope handle is the wrong
shape (`Compile.lean` `contAOf`, the `forkScopedIn` arms). -/
theorem contAOf_forkScopedIn_other (v : Val) (hne : ∀ s, v ≠ Val.scopeHandle s) :
    Program.contAOf root (.forkScopedIn p) v = badShape := by
  unfold Program.contAOf
  revert hne
  -- `split` keeps every row of the table: the dead rows contradict on the name, the
  -- scope-handle row contradicts `hne`, the wrong-shape row is `rfl`, and the table's
  -- catch-all row contradicts its own "the `forkScopedIn` row did not match" hypothesis
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

/-! The `acquireRelease` names, one equation per arm of `contAOf` (`Compile.lean`; V1). The
value patterns are variables except `acquireIn`'s, whose wrong-shape row is the lemma
`contAOf_acquireIn_other`. -/

theorem contAOf_acquireCtx (v : Val) :
    Program.contAOf root (.acquireCtx p) v =
      match Val.context? v with
      | some ctx => Prim.withFiber (EffThunk.acquireMasked p ctx)
      | none => badShape := rfl

theorem contAOf_acquireIn_scope (ctx : Ctx) (s : Nat) :
    Program.contAOf root (.acquireIn p ctx) (Val.scopeHandle s) =
      Prim.onSuccess (resolve root (p.child 0)) (.acquired p ctx s) := rfl

theorem contAOf_acquireIn_other (ctx : Ctx) (v : Val) (hne : ∀ s, v ≠ Val.scopeHandle s) :
    Program.contAOf root (.acquireIn p ctx) v = badShape := by
  unfold Program.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

theorem contAOf_acquired (ctx : Ctx) (s : Nat) (a : Val) :
    Program.contAOf root (.acquired p ctx s) a =
      Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeAdd s (FinName.foreign (p.capture a ctx)))))
        (.afterScopeAdd a (FinName.foreign (p.capture a ctx))) := rfl

theorem contAOf_afterScopeAdd (a : Val) (fin : FinName) (v : Val) :
    Program.contAOf root (.afterScopeAdd a fin) v =
      if v = Val.unit then Prim.success a
      else
        match exitOfVal v with
        | some exit => Prim.onSuccess (embed (finProgram fin exit)) (.constant a)
        | none => badShape := rfl

theorem contAOf_releaseUnder (ctx : Ctx) (exit : ExitV) (v : Val) :
    Program.contAOf root (.releaseUnder p ctx exit) v =
      match Val.context? v with
      | some previous =>
        Prim.onSuccess (Prim.withFiber (EffThunk.setCtx ctx)) (.releaseBody p exit previous)
      | none => badShape := rfl

theorem contAOf_releaseBody (exit : ExitV) (previous : Ctx) (v : Val) :
    Program.contAOf root (.releaseBody p exit previous) v =
      Prim.withFiber (EffThunk.releaseMasked (p.childWith 1 (reifyExitVal exit)) previous) := rfl

theorem denoteR_uninterruptible (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.uninterruptible b) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_interruptible (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.interruptible b) p = denoteAction root p := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_scoped (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.scoped b) p = .vis (.inr (.scoped (p.child 0))) Effects.Program.pure := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_acquireRelease (a r : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.acquireRelease a r) p =
      (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v =>
        match Val.context? v with
        | some ctx => .vis (.inr (.mask false (.acquireIn p ctx))) Effects.Program.pure
        | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

-- the join's three constructors
theorem denoteR_provideLayer (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff) (h : p.fuel ≠ 0) :
    denoteR root (.provideLayer l i b) p =
      suspendR p (constructR fun completed =>
        provideLayerR (fun q m s => denoteLayer root l q m s) (fun q => denoteR root b q)
          (fun q => inlineYield b q) i { p with completed }) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_service (key : ServiceKey) (h : p.fuel ≠ 0) :
    denoteR root (.service key) p =
      (guardR .onSuccess (fiberValR .getContext rfl)).bind (seqR fun v => serviceLookupR key v) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

theorem denoteR_provideService (key : ServiceKey) (value : Term) (b : NativeEff)
    (h : p.fuel ≠ 0) :
    denoteR root (.provideService key value b) p =
      (match evalTerm p.env value with
       | some v => updateContextR (.provideService key v) (denoteR root b (p.child 0))
       | none => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

end denoteEqs

/-! ## The compile, the arms `Agreement.lean` does not spell -/

section compileEqs

variable {p : Point} {k : Nat}

theorem compileEff_perform_async (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind = .async) :
    compileEff (.perform op r) p =
      (match (evalTerm p.env r).bind NativeOp.awaitCellOf with
       | some cell => Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
       | none => badShape) := by
  rw [compileEff, hf]; simp only [hkind]; try rfl

theorem compileEff_perform_program (op : NativeOp) (r : Term) (hf : p.fuel = k + 1)
    (hkind : (NativeOp.row op).kind = .program) :
    compileEff (.perform op r) p = frontier p := by
  rw [compileEff, hf]; simp only [hkind]; try rfl

theorem compileEff_gen (ss : Stmts NativeOp) (hf : p.fuel = k + 1) :
    compileEff (.gen ss) p = Prim.suspend (EffThunk.body p) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_uninterruptible (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.uninterruptible b) p = Prim.withFiber (EffThunk.act p) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_interruptible (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.interruptible b) p = Prim.withFiber (EffThunk.act p) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_whileLoop (i t s : Term) (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.whileLoop i t s b) p = Prim.suspend (EffThunk.body p) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_yieldNow (priority : Nat) (hf : p.fuel = k + 1) :
    compileEff (.yieldNow priority) p = Prim.yieldNowWith priority := by
  rw [compileEff, hf]; try rfl

theorem compileEff_callback (op : NativeOp) (r : Term) (hf : p.fuel = k + 1) :
    compileEff (.callback op r) p =
      (match op with
       | .sleep =>
         match (evalTerm p.env r).bind NativeOp.sleepMillisOf with
         | some 0 => Prim.yieldNowWith 0
         | some (n + 1) =>
           Prim.async (EffName.store (Name.registerSleep (n + 1))) true
             (some (EffName.store Name.cancelSleep))
         | none => badShape
       | _ =>
         match (NativeOp.row op).kind with
         | .async =>
           match (evalTerm p.env r).bind NativeOp.awaitCellOf with
           | some cell => Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
           | none => badShape
         | _ => badShape) := by
  cases op <;> (simp [compileEff, hf]; try rfl)

theorem compileEff_awaitFiber (t : Term) (mode : Supervision.ObserverMode) (hf : p.fuel = k + 1) :
    compileEff (.awaitFiber t mode) p =
      (match evalTerm p.env t with
       | some (Val.fiber ⟨id⟩) =>
         match p.awaitExit ⟨id⟩ mode with
         | some exit => Prim.ofExit exit
         | none => Prim.suspend (EffThunk.park (ParkKind.join ⟨id⟩ mode))
       | _ => badShape) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_withFiber_forkScoped (child : NativeEff) (options : Supervision.ForkOptions)
    (hf : p.fuel = k + 1) :
    compileEff (.withFiber (.forkScoped child options)) p =
      Prim.onSuccess (Prim.withFiber (EffThunk.act p)) (EffName.forkScopedIn p) := by
  simp [compileEff, hf]

theorem compileEff_withFiber_other (a : ActionTerm NativeOp) (hf : p.fuel = k + 1)
    (hnot : ∀ c o, a ≠ .forkScoped c o) :
    compileEff (.withFiber a) p = Prim.withFiber (EffThunk.act p) := by
  cases a <;> first
    | (simp [compileEff, hf]; done)
    | exact absurd rfl (hnot _ _)

theorem compileEff_scoped (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.scoped b) p = Prim.withFiber (EffThunk.act p) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_acquireRelease (a r : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.acquireRelease a r) p =
      Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.acquireCtx p) := by
  rw [compileEff, hf]; try rfl

theorem compileEff_choose (site : Nat) (l r : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.choose site l r) p =
      (match p.tape with
       | true :: rest => compileEff l { p with path := p.path ++ [0], tape := rest }
       | false :: rest => compileEff r { p with path := p.path ++ [1], tape := rest }
       | [] => frontier p) := by
  rw [compileEff, hf]; try rfl

end compileEqs

/-! ## `prepareR` is the identity on a denotation -/

theorem prepareR_denoteR (root : NativeEff) (e : NativeEff) (p : Point)
    (completed : List (FiberId × ExitV)) :
    prepareR completed (denoteR root e p) = denoteR root e p := by
    cases hf : p.fuel with
    | zero => rw [denoteR_zero root e p hf]; rfl
    | succ k =>
      have hpos : p.fuel ≠ 0 := by rw [hf]; exact Nat.succ_ne_zero k
      cases e with
      | succeed t => rw [denoteR_succeed root t hpos]; rfl
      | fail t => rw [denoteR_fail root t hpos]; rfl
      | failCause c => rw [denoteR_failCause root c hpos]; rfl
      | yieldError t =>
        rw [denoteR_yieldError root t hpos]
        cases evalTerm p.env t <;> rfl
      | sync t => rw [denoteR_sync root t hpos]; rfl
      | suspend b => rw [denoteR_suspend root b p hpos]; rfl
      | perform op r =>
        rw [denoteR_perform root op r hpos]
        cases (NativeOp.row op).kind with
        | sync => cases (evalTerm p.env r).bind (NativeOp.syncOpOf op) <;> rfl
        | async => exact prepareR_denoteAsync r p completed
        | program => rfl
      | bind a b =>
        rw [denoteR_bind root a b p hpos, prepareR_guardR_bind,
          prepareR_denoteR root a (p.child 0) completed]
      | gen ss => rw [denoteR_gen root ss p hpos]; rfl
      | catchCause b hd =>
        rw [denoteR_catchCause root b hd hpos, prepareR_guardR_bind,
          prepareR_denoteR root b (p.child 0) completed]
      | matchCause b v c =>
        rw [denoteR_matchCause root b v c hpos, prepareR_guardR_bind,
          prepareR_denoteR root b (p.child 0) completed]
      | onExit b f =>
        rw [denoteR_onExit root b f hpos]
        unfold onExitR
        rw [prepareR_guardR_bind, prepareR_denoteR root b (p.child 0) completed]
      | exit b =>
        rw [denoteR_exit root b p hpos]
        cases inlineYield b (p.child 0) with
        | some ex => rfl
        | none =>
          show prepareR completed ((guardR .all (denoteR root b (p.child 0))).bind _) = _
          rw [prepareR_guardR_bind, prepareR_denoteR root b (p.child 0) completed]
      | uninterruptible b =>
        rw [denoteR_uninterruptible root b hpos]; exact prepareR_denoteAction root p completed
      | interruptible b =>
        rw [denoteR_interruptible root b hpos]; exact prepareR_denoteAction root p completed
      | branch t a b => rw [denoteR_branch root t a b p hpos]; rfl
      | whileLoop i t s b => rw [denoteR_whileLoop root i t s b p hpos]; rfl
      | yieldNow priority => rw [denoteR_yieldNow root priority hpos]; rfl
      | callback op r =>
        rw [denoteR_callback root op r hpos]
        cases op
        case sleep => exact prepareR_denoteSleep r p completed
        all_goals first
          | rfl
          | exact prepareR_denoteAsync r p completed
          | (rename_i s; cases s <;> rfl)
      | awaitFiber t mode =>
        rw [denoteR_awaitFiber root t mode hpos]
        cases evalTerm p.env t with
        | none => rfl
        | some v =>
          -- the value is a fiber handle or it is not; both sides match on that
          cases hfib : Val.fiber? v with
          | some id =>
            obtain ⟨id⟩ := id
            have hv := Val.fiber?_exact hfib
            subst hv
            simp only
            cases p.awaitExit ⟨id⟩ mode with
            | some ex => rfl
            | none => cases mode <;> rfl
          | none =>
            -- one `split` settles both sides: they match on the same discriminant
            have hb : ∀ id, v ≠ Val.fiber ⟨id⟩ := fun id => Val.fiber?_none hfib ⟨id⟩
            split
            · next id heq => exact absurd (Option.some.inj heq) (hb id)
            · rfl
      | withFiber a =>
        rw [denoteR_withFiber root a p hpos]; exact prepareR_denoteAction root p completed
      | «scoped» b => rw [denoteR_scoped root b hpos]; rfl
      | acquireRelease a r => rw [denoteR_acquireRelease root a r hpos, prepareR_guardR_bind]; rfl
      | provideLayer l i b => rw [denoteR_provideLayer root l i b hpos]; rfl
      | service key => rw [denoteR_service root key hpos, prepareR_guardR_bind]; rfl
      | provideService key value b =>
        rw [denoteR_provideService root key value b hpos]
        cases evalTerm p.env value with
        | some v => unfold updateContextR; rw [prepareR_guardR_bind]; rfl
        | none => rfl
      | choose site l r =>
        rw [denoteR_choose root site l r p hpos]
        cases p.tape with
        | nil => rfl
        | cons flag rest =>
          cases flag
          · exact prepareR_denoteR root r _ completed
          · exact prepareR_denoteR root l _ completed
termination_by structural e

/-! ## Addresses and weights -/

theorem at_child_of {root : NativeEff} {p : Point} {n : Node}
    (h : Node.at_ (Node.eff root) p.path = some n) (i : Nat) :
    Node.at_ (Node.eff root) (p.child i).path = n.child i := by
  simp only [Point.child, Node.at_append, h, Option.bind]

theorem at_childWith_of {root : NativeEff} {p : Point} {n : Node}
    (h : Node.at_ (Node.eff root) p.path = some n) (i : Nat) (v : Val) :
    Node.at_ (Node.eff root) (p.childWith i v).path = n.child i := by
  simp only [Point.childWith, Node.at_append, h, Option.bind]

theorem denoteAt_of_at {root : NativeEff} {q : Point} {e : NativeEff}
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff e)) :
    denoteAt root q = denoteR root e q := by
  simp [denoteAt, h]

/-- The measure the introduction descends: every child point spends a unit of fuel, a
`choose` a unit of tape. -/
def _root_.Effect4.Program.Point.weight (p : Point) : Nat := p.fuel + p.tape.length

theorem weight_child (p : Point) (i : Nat) : (p.child i).weight ≤ p.weight := by
  simp only [Point.weight, Point.child]; omega

theorem weight_child_lt (p : Point) (i : Nat) (h : p.fuel ≠ 0) : (p.child i).weight < p.weight := by
  simp only [Point.weight, Point.child]; omega

theorem weight_childWith_lt (p : Point) (i : Nat) (v : Val) (h : p.fuel ≠ 0) :
    (p.childWith i v).weight < p.weight := by
  simp only [Point.weight, Point.childWith]; omega

theorem weight_completed (p : Point) (completed : List (FiberId × ExitV)) :
    ({ p with completed } : Point).weight = p.weight := rfl

/-! ## What a suspension returns, with the point kept whole -/

theorem suspendBodyAt_zero' {root : NativeEff} {q : Point} (hf : q.fuel = 0) :
    suspendBodyAt root (EffThunk.body q) = frontier q := by
  simp [suspendBodyAt, hf]

theorem suspendBodyAt_gen {root : NativeEff} {q : Point} {k : Nat} {ss : Stmts NativeOp}
    (hf : q.fuel = k + 1) (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.gen ss))) :
    suspendBodyAt root (EffThunk.body q) = Prim.iterator (EffName.gen q [] false) Val.unit := by
  simp [suspendBodyAt, hf, h]

theorem suspendBodyAt_whileLoop {root : NativeEff} {q : Point} {k : Nat} {i t s : Term}
    {b : NativeEff} (hf : q.fuel = k + 1)
    (h : Node.at_ (Node.eff root) q.path = some (Node.eff (.whileLoop i t s b))) :
    suspendBodyAt root (EffThunk.body q) =
      (match evalTerm q.env i with
       | some cursor => Prim.whileLoop (EffName.loop q) cursor
       | none => badShape) := by
  simp [suspendBodyAt, hf, h]; rfl

/-- `resolve` and `denoteAt` are related at every point of weight below the induction's bound. -/
theorem resolve_intro_of (root : NativeEff) (n : Nat)
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) →
        CodeMeans root (compileEff e p) (denoteR root e p))
    (q : Point) (hq : q.weight < n) : CodeMeans root (resolve root q) (denoteAt root q) := by
  unfold resolve denoteAt
  rcases hn : Node.at_ (.eff root) q.path with _ | m
  · exact codeMeans_badShape root
  · cases m with
    | eff e => exact ih q hq e hn
    | _ => exact codeMeans_badShape root

/-- The race entrants, each compiled and denoted at its own list address. -/
theorem entrants_intro (root : NativeEff) (n : Nat)
    (ih : ∀ (p : Point), p.weight < n → ∀ (e : NativeEff),
      Node.at_ (.eff root) p.path = some (.eff e) →
        CodeMeans root (compileEff e p) (denoteR root e p)) :
    ∀ (es : Effs NativeOp) (q : Point), q.weight < n →
      Node.at_ (.eff root) q.path = some (.effs es) →
      (actionAt.entrants es q).length = (entrantPoints es q).length ∧
        ∀ x ∈ (actionAt.entrants es q).zip ((entrantPoints es q).map (denoteAt root)),
          CodeMeans root x.1 x.2
  | .nil, _, _, _ => ⟨rfl, fun _ hx => by simp [actionAt.entrants, entrantPoints] at hx⟩
  | .cons e rest, q, hq, h => by
    have h0 : Node.at_ (.eff root) (q.child 0).path = some (.eff e) := at_child_of h 0
    have h1 : Node.at_ (.eff root) (q.child 1).path = some (.effs rest) := at_child_of h 1
    have tail := entrants_intro root n ih rest (q.child 1) (Nat.lt_of_le_of_lt (weight_child q 1) hq) h1
    refine ⟨by simp only [actionAt.entrants, entrantPoints, List.length_cons, tail.1], ?_⟩
    intro x hx
    simp only [actionAt.entrants, entrantPoints, List.map_cons, List.zip_cons_cons,
      List.mem_cons] at hx
    rcases hx with rfl | hx
    · show CodeMeans root (compileEff e (q.child 0)) (denoteAt root (q.child 0))
      rw [denoteAt_of_at h0]
      exact ih _ (Nat.lt_of_le_of_lt (weight_child q 0) hq) e h0
    · exact tail.2 x hx

/-- What `actionAt` puts in the program-carrying fields of the action of a `withFiber` node,
and the actions it never answers there. -/
theorem actionAt_shape {root : NativeEff} {p : Point} {a : ActionTerm NativeOp}
    (h : Node.at_ (.eff root) p.path = some (.eff (.withFiber a))) {act : NAction}
    (hact : actionAt root p = some act) :
    (∀ program options, act = .fork program options →
      program = resolve root ((p.child 0).child 0)) ∧
    (∀ program options scope, act = .forkIn program options scope →
      program = resolve root ((p.child 0).child 0)) ∧
    (∀ program options, act ≠ .forkScoped program options) ∧
    (∀ entrants, act = .raceAll entrants →
      ∃ es, a = .raceAll es ∧ entrants = actionAt.entrants es ((p.child 0).child 0)) ∧
    (∀ body flag, act ≠ .setInterruptible body flag) ∧
    (act = .ambientScope → ∃ child options, a = .forkScoped child options) ∧
    (∀ fins, act ≠ .closePar fins) := by
  simp only [actionAt, h, Option.some.injEq] at hact
  subst hact
  cases a <;> dsimp only <;> (repeat' split) <;>
    refine ⟨fun _ _ heq => ?_, fun _ _ _ heq => ?_, fun _ _ heq => ?_, fun _ heq => ?_,
      fun _ _ heq => ?_, fun heq => ?_, fun _ heq => ?_⟩ <;>
    cases heq <;> first | rfl | exact ⟨_, rfl, rfl⟩ | exact ⟨_, _, rfl⟩

/-- `finalizerCode` and `finalizerR` are related whenever the finalizer programs are, at
the view the term resolves its construction with. -/
theorem finalizer_intro (root : NativeEff) (completed : List (FiberId × ExitV)) (ex : ExitV)
    {program : NCode} {cleanup : RProgram}
    (hc : CodeMeans root program (prepareR completed cleanup)) :
    CodeMeans root (finalizerCodeAt root completed ex program)
      (prepareR completed (finalizerR ex cleanup)) := by
  cases ex with
  | success v =>
    show CodeMeans root (Prim.onSuccess program (EffName.restore (.success v)))
      (prepareR completed ((guardR .onSuccess cleanup).bind (seqR fun _ =>
        @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.finishFinalizer (.success v)))
          Effects.Program.pure)))
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (prepareR completed cleanup) _ hc ?_ rfl (fun _ => rfl)
    intro completed' v'
    exact codeMeans_finish root (.success v) Effects.Program.pure
  | failure c =>
    show CodeMeans root
      (Prim.onSuccess (Prim.onFailure program (EffName.merge (.failure c)))
        (EffName.restore (.failure c)))
      (prepareR completed ((guardR .onSuccess ((guardR .onFailure cleanup).bind fun
          | .success v => Effects.Program.pure (.success v)
          | .failure c' =>
            Effects.Program.pure (Exit.restoreAfterFinalizer (.failure c) (.failure c')))).bind
        (seqR fun _ =>
          @Effects.Program.vis RSig ExitV (Sum.inr (FiberOp.finishFinalizer (.failure c)))
            Effects.Program.pure)))
    rw [prepareR_guardR_bind, prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ ((guardR .onFailure (prepareR completed cleanup)).bind _) _
      ?_ ?_ rfl (fun _ => rfl)
    · rw [guardR_bind]
      refine CodeMeans.onFailure _ _ _ (prepareR completed cleanup) _ hc ?_ rfl (fun _ => rfl)
      intro completed' c'
      exact codeMeans_ofExit_pure root (Exit.restoreAfterFinalizer (.failure c) (.failure c'))
    · intro completed' v'
      exact codeMeans_finish root (.failure c) Effects.Program.pure

/-! ## The introduction -/

/-- The `forkScoped` node's payload, read decidably (the case split of `code_intro_aux`
stays at the ceiling: no classical choice on an existential). -/
def forkScoped? : ActionTerm NativeOp → Option (NativeEff × Supervision.ForkOptions)
  | .forkScoped child options => some (child, options)
  | _ => none

theorem forkScoped?_some {a : ActionTerm NativeOp} {child : NativeEff}
    {options : Supervision.ForkOptions} (h : forkScoped? a = some (child, options)) :
    a = .forkScoped child options := by
  cases a <;> first
    | (obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h); rfl)
    | (simp [forkScoped?] at h)

theorem forkScoped?_none {a : ActionTerm NativeOp} (h : forkScoped? a = none) :
    ∀ c o, a ≠ .forkScoped c o := by
  intro c o heq
  subst heq
  simp [forkScoped?] at h

/-! ### `acquireRelease`'s pieces (V1)

The release at its point under the context-restoring finalizer, the counted suspend of a
capture's release, and the masked half of the acquire — each against its `Body` or
`denoteFin` term, given the related code at the points they resolve. -/

/-- `provideContext(release(a, exit), context)`'s frame (`internal/effect.ts:2180-2199`): the
release under the finalizer that restores the previous context. -/
theorem release_intro (root : NativeEff) (q : Point) (previous : Ctx)
    (hres : CodeMeans root (resolve root q) (denoteAt root q)) :
    CodeMeans root (Prim.onExit (resolve root q) (.restoreCtx previous) false)
      (denoteBody root (.release q previous)) := by
  show CodeMeans root _ (onExitR (denoteAt root q) fun _ => fiberValR (.setContext previous) rfl)
  unfold onExitR
  rw [guardR_bind]
  refine CodeMeans.onExit _ _ _ (denoteAt root q)
    (fun ex => finalizerR ex (fiberValR (.setContext previous) rfl)) hres ?_ (fun _ _ => rfl) rfl
    (fun _ => rfl)
  intro completed ex program hprog
  have hp' : Prim.withFiber (EffThunk.setCtx previous) = program := Option.some.inj hprog
  rw [← hp']
  refine finalizer_intro root completed ex ?_
  -- `prepareR` is the identity on the `setContext` operation, definitionally
  exact CodeMeans.actSetContext _ _ _ rfl (successV root)

/-- A capture's release (`FinName.foreign`): the counted suspend, the context read, the
captured context set, then the release masked at the capture's point over the exit — the
point refreshed with the view at the release's invocation on both sides. -/
theorem foreignRelease_intro (root : NativeEff) (c : Capture) (ex : ExitV)
    (hres : ∀ completed, CodeMeans root
      (resolve root ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)))
      (denoteAt root ((Point.ofCapture c completed).childWith 1 (reifyExitVal ex)))) :
    CodeMeans root (embed (finProgram (.foreign c) ex)) (denoteFin (.foreign c) ex) := by
  simp only [finProgram, embed, denoteFin]
  refine CodeMeans.foreignRelease c ex _ fun completed => ?_
  simp only [suspendBodyAt]
  rw [prepareR_guardR_bind, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (prepareR completed (fiberValR .getContext rfl)) _ ?_ ?_ rfl
    (fun _ => rfl)
  · exact CodeMeans.actGetContext _ _ rfl (successV root)
  · intro completed' v
    show CodeMeans root (Program.contAOf root (.releaseUnder (Point.ofCapture c) c.ctx ex) v) _
    rw [contAOf_releaseUnder]
    simp only [seqR]
    -- the current context read back off the value, or not
    cases hctx : Val.context? v with
    | some previous =>
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed' (fiberValR (.setContext c.ctx) rfl)) _
        ?_ ?_ rfl (fun _ => rfl)
      · exact CodeMeans.actSetContext _ _ _ rfl (successV root)
      · intro completed'' w
        show CodeMeans root
          (Program.contAOf root
            (.releaseBody { Point.ofCapture c with completed := completed'' } ex previous) w) _
        rw [contAOf_releaseBody]
        simp only [seqR, prepareR_constructR]
        -- `prepareR` is the identity on the mask operation, definitionally; the two release
        -- points are the capture's point at this view, spelled two ways
        exact CodeMeans.actMask _ _ false (.release _ previous) _ rfl
          (release_intro root _ previous (hres completed'')) delivers_pure
    | none => exact codeMeans_badShape root

/-- `uninterruptibleMask(restore => flatMap(scope, scope => tap(acquire, scopeAddFinalizerExit
…)))` (`internal/effect.ts:3977-3986`): the masked half, given the acquire at the point's
child 0 and the capture's release. -/
theorem acquireIn_intro (root : NativeEff) (p : Point) (ctx : Ctx)
    (hres : CodeMeans root (resolve root (p.child 0)) (denoteAt root (p.child 0)))
    (hfin : ∀ (a : Val) (ex : ExitV),
      CodeMeans root (embed (finProgram (.foreign (p.capture a ctx)) ex))
        (denoteFin (.foreign (p.capture a ctx)) ex)) :
    CodeMeans root
      (Prim.onSuccess (Prim.withFiber (.store (.act .ambientScope))) (.acquireIn p ctx))
      (denoteBody root (.acquireIn p ctx)) := by
  show CodeMeans root _ (acquireInR (denoteAt root (p.child 0)) p ctx)
  unfold acquireInR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .ambientScope rfl) _ ?_ ?_ rfl (fun _ => rfl)
  · exact CodeMeans.actAmbientScope _ _ rfl (successV root)
  · intro completed v
    -- the handle the service read answered is a scope handle or it is not
    cases hsc : Val.scope? v with
    | some s =>
      have hv := Val.scope?_exact hsc
      subst hv
      show CodeMeans root (Prim.onSuccess (resolve root (p.child 0)) (.acquired p ctx s)) _
      simp only [seqR, Val.scope?_scopeHandle]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed (denoteAt root (p.child 0))) _
        (hres.prepare _) ?_ rfl (fun _ => rfl)
      intro completed' a
      show CodeMeans root (Program.contAOf root (.acquired p ctx s) a) _
      rw [contAOf_acquired]
      simp only [seqR]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _
        (prepareR completed' (storeR (.scopeAdd s (.foreign (p.capture a ctx))))) _
        (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
      intro completed'' w
      show CodeMeans root (Program.contAOf root (.afterScopeAdd a (.foreign (p.capture a ctx))) w) _
      rw [contAOf_afterScopeAdd]
      simp only [seqR]
      -- unit: the registration took; anything else is the closing exit, read back or not
      by_cases hw : w = Val.unit
      · rw [if_pos hw, if_pos hw, prepareR_pure]
        exact CodeMeans.success a
      · rw [if_neg hw, if_neg hw]
        cases hex : exitOfVal w with
        | some ex =>
          dsimp only
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _
            (prepareR completed'' (denoteFin (.foreign (p.capture a ctx)) ex)) _
            ((hfin a ex).prepare _) ?_ rfl (fun _ => rfl)
          intro completed''' _
          show CodeMeans root (Prim.success a) _
          simp only [seqR, prepareR_pure]
          exact CodeMeans.success a
        | none => exact codeMeans_badShape root
    | none =>
      have hne : ∀ s, v ≠ Val.scopeHandle s := Val.scope?_none hsc
      show CodeMeans root (Program.contAOf root (.acquireIn p ctx) v) _
      rw [contAOf_acquireIn_other root ctx v hne]
      simp only [seqR, hsc, prepareR_pure]
      exact codeMeans_badShape root

/-! ## The join: `Effect.provide`, `Effect.service`, `Effect.provideService`, `Layer.build`

Step by step as `acquireRelease` (V1): one lemma per named continuation, the layer build by
structural recursion on the layer term (`layer_intro`), the memo protocol's three finalizers
proved here so the build needs nothing of `Simulation/Hooks.lean`. -/

/-- The stores' `closeIfLast` on anything but a scope handle: done (`Layer.ts:408`). -/
theorem contAOf_closeIfLast_other (ex : ExitV) (v : Val) (hne : ∀ s, v ≠ Val.scopeHandle s) :
    Effect4.Machine.contAOf (Name.closeIfLast ex) v = Prim.success Val.unit := by
  unfold Effect4.Machine.contAOf
  revert hne
  split <;> intro hne <;> first
    | rfl
    | contradiction
    | exact absurd rfl (hne _)
    | (rename_i heq; exact absurd heq (hne _))
    | simp_all

/-- `fromBuild`'s `onExit` (`Layer.ts:343`): close the layer scope on failure only. -/
theorem closeChildOnFailure_means (root : NativeEff) (child : Nat) (ex : ExitV) :
    CodeMeans root (embed (finProgram (.closeChildOnFailure child) ex))
      (denoteFin (.closeChildOnFailure child) ex) := by
  cases ex with
  | failure cause =>
    simp only [finProgram, embed, denoteFin]
    exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | success v =>
    simp only [finProgram, embed, denoteFin]
    exact CodeMeans.success _

/-- The memo entry finalizer (`Layer.ts:401-410`): `observers--`; the last observer's release
answers the layer scope, closed with the exit. -/
theorem memoEntry_means (root : NativeEff) (layer : LayerId) (memoMap : MemoMapId) (ex : ExitV) :
    CodeMeans root (embed (finProgram (.memoEntry layer memoMap) ex))
      (denoteFin (.memoEntry layer memoMap) ex) := by
  simp only [finProgram, embed, denoteFin]
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.memoRelease layer memoMap)) _
    (CodeMeans.syncStore _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  show CodeMeans root (embed (Effect4.Machine.contAOf (Name.closeIfLast ex) v)) _
  cases hs : Val.scope? v with
  | some s =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (embed (Prim.withFiber (Thunk.act (ActionName.closeScope s ex)))) _
    exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | none =>
    rw [contAOf_closeIfLast_other ex v (Val.scope?_none hs)]
    simp only [embed, prepareR_pure]
    exact CodeMeans.success _

/-- `memoMapBuild`'s `onExit` (`Layer.ts:414-417`): the exit stored, the Deferred completed. -/
theorem memoDone_means (root : NativeEff) (layer : LayerId) (memoMap : MemoMapId) (ex : ExitV) :
    CodeMeans root (embed (finProgram (.memoDone layer memoMap) ex))
      (denoteFin (.memoDone layer memoMap) ex) := by
  simp only [finProgram, embed, denoteFin]
  exact CodeMeans.syncStore _ _ (successV root)

/-- A region under the finalizer that restores the previous context (`updateContext`,
`internal/effect.ts:2092-2095`): `release_intro` on any region. -/
theorem region_intro (root : NativeEff) (body : Region) (previous : Ctx) (r : RProgram)
    (hb : CodeMeans root (regionCode root body) r) :
    CodeMeans root (Prim.onExit (regionCode root body) (.restoreCtx previous) false)
      (onExitR r fun _ => fiberValR (.setContext previous) rfl) := by
  unfold onExitR
  rw [guardR_bind]
  refine CodeMeans.onExit _ _ _ r
    (fun ex => finalizerR ex (fiberValR (.setContext previous) rfl)) hb ?_ (fun _ _ => rfl) rfl
    (fun _ => rfl)
  intro completed ex program hprog
  have hp' : Prim.withFiber (EffThunk.setCtx previous) = program := Option.some.inj hprog
  rw [← hp']
  refine finalizer_intro root completed ex ?_
  exact CodeMeans.actSetContext _ _ _ rfl (successV root)

/-- `updateContext(self, f)` (`internal/effect.ts:2087-2096`): the context read, the identity
shortcut or the set-and-restore region. -/
theorem updateContext_intro (root : NativeEff) (u : Env.ContextUpdate) (body : Region)
    (r : RProgram) (hb : CodeMeans root (regionCode root body) r) :
    CodeMeans root (updateContextAt u body) (updateContextR u r) := by
  unfold updateContextAt updateContextR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _
    (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.updateThen u body) v) _
  rw [contAOf_updateThen]
  unfold updateThenK
  simp only [seqR]
  cases hctx : Val.context? v with
  | some prev =>
    dsimp only
    by_cases hid : updateKeepsIdentity u prev.services = true
    · simp only [hid, eq_self_iff_true, ↓reduceIte]
      exact hb.prepare completed
    · simp only [hid, Bool.false_eq_true, ↓reduceIte]
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _
        (prepareR completed
          (fiberValR (.setContext (Ctx.withServices (u.apply prev.services))) rfl)) _
        (CodeMeans.actSetContext _ _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
      intro completed' _
      show CodeMeans root (Program.contAOf root (.bodyThen body prev) _) _
      rw [contAOf_bodyThen]
      simp only [seqR]
      exact (region_intro root body prev r hb).prepare completed'
  | none => exact codeMeans_badShape root

/-- `scopeAddFinalizerExit(scope, fin)` (`internal/effect.ts:3847-3858`): the registration,
then unit, or the finalizer now when the scope had already closed. -/
theorem scopeAdd_intro (root : NativeEff) (scope : Nat) (fin : FinName)
    (hfin : ∀ ex, CodeMeans root (embed (finProgram fin ex)) (denoteFin fin ex)) :
    CodeMeans root (scopeAddAt scope fin) (scopeAddR scope fin) := by
  unfold scopeAddAt scopeAddR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeAdd scope fin)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed w
  show CodeMeans root (Program.contAOf root (.afterScopeAdd Val.unit fin) w) _
  rw [contAOf_afterScopeAdd]
  simp only [seqR]
  by_cases hw : w = Val.unit
  · rw [if_pos hw, if_pos hw, prepareR_pure]
    exact CodeMeans.success _
  · rw [if_neg hw, if_neg hw]
    cases hex : exitOfVal w with
    | some ex =>
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed (denoteFin fin ex)) _
        ((hfin ex).prepare _) ?_ rfl (fun _ => rfl)
      intro completed' _
      show CodeMeans root (Prim.success Val.unit) _
      simp only [seqR, prepareR_pure]
      exact CodeMeans.success _
    | none => exact codeMeans_badShape root

/-- `fromBuild` (`Layer.ts:333-345`): the layer scope forked from the caller's, the inner build
inside it under the finalizer that closes it on failure. -/
theorem fromBuild_intro (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat)
    (innerR : Nat → RProgram)
    (hinner : ∀ child, CodeMeans root (innerLayerAt root q m child) (innerR child)) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork scope FinalizerStrategy.sequential)))
        (.fromBuildThen q m))
      (fromBuildR scope innerR) := by
  unfold fromBuildR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeFork scope .sequential)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some child =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.fromBuildThen q m) (Val.scopeHandle child)) _
    rw [contAOf_fromBuildThen_scope]
    dsimp only
    unfold onExitR
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onExit _ _ _ (prepareR completed (innerR child))
      (fun ex => finalizerR ex (denoteFin (.closeChildOnFailure child) ex))
      ((hinner child).prepare _) ?_ (fun _ _ => rfl) rfl (fun _ => rfl)
    intro completed' ex program hprog
    have hp' : embed (finProgram (.closeChildOnFailure child) ex) = program :=
      Option.some.inj hprog
    rw [← hp']
    exact finalizer_intro root completed' ex ((closeChildOnFailure_means root child ex).prepare _)
  | none =>
    show CodeMeans root (Program.contAOf root (.fromBuildThen q m) v) _
    rw [contAOf_fromBuildThen_other root q m v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

/-- `getOrElseMemoize` (`Layer.ts:445-457`): the counted suspend, the lookup, a hit's
registration and await, or `memoMapBuild` over the construction. -/
theorem memoize_intro (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat)
    (constructionR : Nat → RProgram)
    (hcons : ∀ layerScope,
      CodeMeans root (constructionAt root q layerScope) (constructionR layerScope)) :
    CodeMeans root (Prim.suspend (EffThunk.memoLookup q m scope))
      (memoizeR q m scope constructionR) := by
  unfold memoizeR suspendR
  refine CodeMeans.suspendMemo q m scope _ fun completed => ?_
  rw [suspendBodyAt_memoLookup, prepareR_guardR_bind, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (prepareR completed (storeR (.memoGet q.path m))) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed' v
  simp only [seqR]
  cases hhit : Val.memoHit? v with
  | some co =>
    obtain ⟨cell, owner⟩ := co
    have hv := Val.memoHit?_exact hhit
    subst hv
    show CodeMeans root
      (Program.contAOf root (.memoize q m scope) (.pair (Val.promise cell) (Val.memoMap owner))) _
    rw [contAOf_memoize_hit]
    dsimp only
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _
      (prepareR completed' (scopeAddR scope (.memoEntry q.path owner))) _
      ((scopeAdd_intro root scope _ (memoEntry_means root _ _)).prepare _) ?_ rfl (fun _ => rfl)
    intro completed'' _
    show CodeMeans root (Program.contAOf root (.awaitPromise cell) _) _
    rw [contAOf_awaitPromise]
    simp only [seqR]
    exact CodeMeans.asyncAwait cell (Val.promise cell) _ delivers_pure
  | none =>
    have hne := Val.memoHit?_none hhit
    by_cases hu : v = Val.unit
    · subst hu
      rw [if_pos rfl]
      show CodeMeans root (Program.contAOf root (.memoize q m scope) Val.unit) _
      rw [contAOf_memoize_unit]
      dsimp only
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed' (storeR (.memoBuild q.path m))) _
        (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
      intro completed'' w
      simp only [seqR]
      cases hls : Val.scope? w with
      | some layerScope =>
        have hw := Val.scope?_exact hls
        subst hw
        show CodeMeans root
          (Program.contAOf root (.buildIntoLayerScope q m scope) (Val.scopeHandle layerScope)) _
        rw [contAOf_buildIntoLayerScope_scope]
        dsimp only
        rw [prepareR_guardR_bind, guardR_bind]
        refine CodeMeans.onSuccess _ _ _
          (prepareR completed'' (scopeAddR scope (.memoEntry q.path m))) _
          ((scopeAdd_intro root scope _ (memoEntry_means root _ _)).prepare _) ?_ rfl
          (fun _ => rfl)
        intro completed''' _
        show CodeMeans root (Program.contAOf root (.thenBuildInto q m layerScope) _) _
        rw [contAOf_thenBuildInto]
        simp only [seqR]
        unfold onExitR
        rw [prepareR_guardR_bind, guardR_bind]
        refine CodeMeans.onExit _ _ _ (prepareR completed''' (constructionR layerScope))
          (fun ex => finalizerR ex (denoteFin (.memoDone q.path m) ex))
          ((hcons layerScope).prepare _) ?_ (fun _ _ => rfl) rfl (fun _ => rfl)
        intro completed'''' ex program hprog
        have hp' : embed (finProgram (.memoDone q.path m) ex) = program := Option.some.inj hprog
        rw [← hp']
        exact finalizer_intro root completed'''' ex ((memoDone_means root _ _ ex).prepare _)
      | none =>
        show CodeMeans root (Program.contAOf root (.buildIntoLayerScope q m scope) w) _
        rw [contAOf_buildIntoLayerScope_other root q m scope w (Val.scope?_none hls)]
        simp only [prepareR_pure]
        exact codeMeans_badShape root
    · rw [if_neg hu]
      show CodeMeans root (Program.contAOf root (.memoize q m scope) v) _
      rw [contAOf_memoize_other root q m scope v hne hu]
      simp only [prepareR_pure]
      exact codeMeans_badShape root

/-- `buildWithMemoMap` (`Layer.ts:756-765`): the `CurrentMemoMap` region over the build, its
answer with the map added. -/
theorem buildWithMemoMap_intro (root : NativeEff) (q : Point) (scope : Nat)
    (buildR : MemoMapId → RProgram)
    (hb : ∀ m, CodeMeans root (resolveLayer root q m scope) (buildR m)) (id : MemoMapId) :
    CodeMeans root
      (updateContextAt (Env.ContextUpdate.provideService Env.currentMemoMapKey (Val.memoMap id))
        (Region.buildAdding q id scope))
      (buildWithMemoMapR buildR id) := by
  unfold buildWithMemoMapR
  refine updateContext_intro root _ _ _ ?_
  simp only [regionCode]
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (buildR id) _ (hb id) ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.addCurrentMemoMap id) v) _
  rw [contAOf_addCurrentMemoMap]
  unfold addCurrentMemoMapK addCurrentMemoMapR
  simp only [seqR]
  cases Env.decode v with
  | some ctx => simp only [prepareR_pure]; exact CodeMeans.success _
  | none => exact codeMeans_badShape root

/-- The memo map forked or created, in hand: `buildWithMemoMap` on it, or the wrong shape. -/
theorem withMemoMapThen_intro (root : NativeEff) (q : Point) (scope : Nat)
    (buildR : MemoMapId → RProgram)
    (hb : ∀ m, CodeMeans root (resolveLayer root q m scope) (buildR m))
    (completed : List (FiberId × ExitV)) (u : Val) :
    CodeMeans root (Program.contAOf root (.withMemoMapThen q scope) u)
      (prepareR completed (match Val.memoMap? u with
        | some id => buildWithMemoMapR buildR id
        | none => .pure badShapeExit)) := by
  cases hid : Val.memoMap? u with
  | some id =>
    have hu := Val.memoMap?_exact hid
    subst hu
    rw [contAOf_withMemoMapThen_memoMap]
    dsimp only
    exact (buildWithMemoMap_intro root q scope buildR hb id).prepare completed
  | none =>
    rw [contAOf_withMemoMapThen_other root q scope u (Val.memoMap?_none hid)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

/-- `provideWith` (`Layer.ts:1915-1923`): the dependency built, the dependent under its
context, the combiner. -/
theorem provideWith_intro (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat)
    (mode : CombineMode) (depR depdR : RProgram)
    (hdep : CodeMeans root (resolveLayer root (q.child 1) m child) depR)
    (hdept : CodeMeans root (resolveLayer root (q.child 0) m child) depdR) :
    CodeMeans root
      (Prim.onSuccess (resolveLayer root (q.child 1) m child) (.provideThen q m child mode))
      (provideWithR depR depdR mode) := by
  unfold provideWithR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ depR _ hdep ?_ rfl (fun _ => rfl)
  intro completed v
  show CodeMeans root (Program.contAOf root (.provideThen q m child mode) v) _
  rw [contAOf_provideThen]
  unfold provideThenK
  simp only [seqR]
  cases hd : Env.decode v with
  | some ctx =>
    dsimp only
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (prepareR completed (updateContextR (.provide ctx) depdR)) _
      ((updateContext_intro root _ (Region.build (q.child 0) m child) depdR hdept).prepare _) ?_
      rfl (fun _ => rfl)
    intro completed' w
    show CodeMeans root (Program.contAOf root (.combineWith mode ctx) w) _
    rw [contAOf_combineWith]
    unfold combineWithK combineWithR
    simp only [seqR]
    cases Env.decode w with
    | some merged => cases mode <;> (simp only [prepareR_pure]; exact CodeMeans.success _)
    | none => exact codeMeans_badShape root
  | none => exact codeMeans_badShape root

/-- `mergeAllEffect` for two siblings (`Layer.ts:1587-1602`): the parallel parent, a sequential
child per sibling with the sibling's build forked into it, the await, the merge. -/
theorem mergeTwo_intro (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat)
    (h0 : ∀ c, CodeMeans root (resolveLayer root (q.child 0) m c) (layerBuildR root (q.child 0) m c))
    (h1 : ∀ c, CodeMeans root (resolveLayer root (q.child 1) m c) (layerBuildR root (q.child 1) m c)) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeFork child FinalizerStrategy.parallel)))
        (.mergeChildren q m))
      (mergeTwoR q m child) := by
  unfold mergeTwoR
  rw [guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (storeR (.scopeFork child .parallel)) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some parent =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.mergeChildren q m) (Val.scopeHandle parent)) _
    rw [contAOf_mergeChildren_scope]
    dsimp only
    unfold mergeForkR
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (prepareR completed (storeR (.scopeFork parent .sequential))) _
      (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
    intro completed₁ w
    simp only [seqR]
    cases hs0 : Val.scope? w with
    | some c0 =>
      have hw := Val.scope?_exact hs0
      subst hw
      show CodeMeans root
        (Program.contAOf root (.mergeForkOne q 0 m parent []) (Val.scopeHandle c0)) _
      rw [contAOf_mergeForkOne_scope]
      dsimp only
      try unfold forkLayerR
      rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed₁ _) _ ?_ ?_ rfl (fun _ => rfl)
      · exact CodeMeans.actFork _ _ _ (.layerBuild (q.child 0) m c0) _ rfl (h0 c0) (successV root)
      · intro completed₂ f0
        show CodeMeans root (Program.contAOf root (.mergeForkNext q 0 m parent []) f0) _
        simp only [seqR]
        cases hf0 : Val.fiber? f0 with
        | some id0 =>
          have hf := Val.fiber?_exact hf0
          subst hf
          rw [contAOf_mergeForkNext_fiber, if_pos rfl]
          dsimp only
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _
            (prepareR completed₂ (storeR (.scopeFork parent .sequential))) _
            (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
          intro completed₃ w1
          simp only [seqR]
          cases hs1 : Val.scope? w1 with
          | some c1 =>
            have hw1 := Val.scope?_exact hs1
            subst hw1
            show CodeMeans root
              (Program.contAOf root (.mergeForkOne q 1 m parent ([] ++ [id0]))
                (Val.scopeHandle c1)) _
            rw [contAOf_mergeForkOne_scope]
            dsimp only
            try unfold forkLayerR
            rw [prepareR_guardR_bind, guardR_bind]
            refine CodeMeans.onSuccess _ _ _ (prepareR completed₃ _) _ ?_ ?_ rfl (fun _ => rfl)
            · exact CodeMeans.actFork _ _ _ (.layerBuild (q.child 1) m c1) _ rfl (h1 c1)
                (successV root)
            · intro completed₄ f1
              show CodeMeans root
                (Program.contAOf root (.mergeForkNext q 1 m parent ([] ++ [id0])) f1) _
              simp only [seqR]
              cases hf1 : Val.fiber? f1 with
              | some id1 =>
                have hf := Val.fiber?_exact hf1
                subst hf
                rw [contAOf_mergeForkNext_fiber, if_neg (by decide)]
                dsimp only
                rw [prepareR_guardR_bind, guardR_bind]
                refine CodeMeans.onSuccess _ _ _
                  (prepareR completed₄ (fiberValR (.awaitAllFailFast [id0, id1]) rfl)) _
                  (CodeMeans.actAwaitAllFailFast _ _ _ rfl delivers_seqR_pure) ?_ rfl
                  (fun _ => rfl)
                intro completed₅ ex
                show CodeMeans root (Program.contAOf root .mergeContexts ex) _
                rw [contAOf_mergeContexts]
                simp only [seqR]
                unfold mergeContextsK mergeContextsR
                cases contextsOf ex with
                | some ctxs => simp only [prepareR_pure]; exact CodeMeans.success _
                | none =>
                  cases reasonsOfVal ex with
                  | nil => exact codeMeans_badShape root
                  | cons reason rest => simp only [prepareR_pure]; exact CodeMeans.failure _
              | none =>
                show CodeMeans root
                  (Program.contAOf root (.mergeForkNext q 1 m parent ([] ++ [id0])) f1) _
                rw [contAOf_mergeForkNext_other root q 1 m parent _ f1 (Val.fiber?_none hf1)]
                simp only [prepareR_pure]
                exact codeMeans_badShape root
          | none =>
            show CodeMeans root
              (Program.contAOf root (.mergeForkOne q 1 m parent ([] ++ [id0])) w1) _
            rw [contAOf_mergeForkOne_other root q 1 m parent _ w1 (Val.scope?_none hs1)]
            simp only [prepareR_pure]
            exact codeMeans_badShape root
        | none =>
          show CodeMeans root (Program.contAOf root (.mergeForkNext q 0 m parent []) f0) _
          rw [contAOf_mergeForkNext_other root q 0 m parent [] f0 (Val.fiber?_none hf0)]
          simp only [prepareR_pure]
          exact codeMeans_badShape root
    | none =>
      show CodeMeans root (Program.contAOf root (.mergeForkOne q 0 m parent []) w) _
      rw [contAOf_mergeForkOne_other root q 0 m parent [] w (Val.scope?_none hs0)]
      simp only [prepareR_pure]
      exact codeMeans_badShape root
  | none =>
    show CodeMeans root (Program.contAOf root (.mergeChildren q m) v) _
    rw [contAOf_mergeChildren_other root q m v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

/-- The layer at a point, resolved by the term: the node's term, denoted. -/
theorem layerBuildR_of_at {root : NativeEff} {q : Point} {l : LayerTerm NativeOp}
    (h : Node.at_ (Node.eff root) q.path = some (Node.layer l)) (m : MemoMapId) (scope : Nat) :
    layerBuildR root q m scope = denoteLayer root l q m scope := by
  simp [layerBuildR, h]

/-- **A layer's build.** At its point, the frame's `compileLayer` and the term's `denoteLayer`
are related, structurally in the layer, given every program at a lighter point. -/
theorem layer_intro (root : NativeEff) (n : Nat)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q)) :
    ∀ (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat), q.weight < n →
      Node.at_ (.eff root) q.path = some (.layer l) →
      CodeMeans root (compileLayer l q m scope) (denoteLayer root l q m scope)
  | .succeed key value, q, m, scope, _, _ => by
    simp only [compileLayer, denoteLayer]
    cases Lit.toVal value with
    | some v => exact CodeMeans.success _
    | none => exact codeMeans_badShape root
  | .fresh inner, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (storeR (.memoFork none)) _
      (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
    intro completed v
    simp only [seqR]
    have hinner := at_child_of h 0
    cases hid : Val.memoMap? v with
    | some id =>
      have hv := Val.memoMap?_exact hid
      subst hv
      show CodeMeans root (Program.contAOf root (.freshThen (q.child 0) scope) (Val.memoMap id)) _
      rw [contAOf_freshThen_memoMap, resolveLayer_of_at root hinner]
      dsimp only
      exact (layer_intro root n hres inner (q.child 0) id scope
        (Nat.lt_of_le_of_lt (weight_child q 0) hq) hinner).prepare completed
    | none =>
      show CodeMeans root (Program.contAOf root (.freshThen (q.child 0) scope) v) _
      rw [contAOf_freshThen_other root _ _ v (Val.memoMap?_none hid)]
      simp only [prepareR_pure]
      exact codeMeans_badShape root
  | .orDie inner, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    rw [guardR_bind]
    have hinner := at_child_of h 0
    refine CodeMeans.onFailure _ _ _ (denoteLayer root inner (q.child 0) m scope) _
      (layer_intro root n hres inner (q.child 0) m scope
        (Nat.lt_of_le_of_lt (weight_child q 0) hq) hinner) ?_ rfl (fun _ => rfl)
    intro completed c
    show CodeMeans root (Prim.failure (orDieCause c))
      (prepareR completed (.pure (.failure (orDieCause c))))
    rw [prepareR_pure]
    exact CodeMeans.failure _
  | .effect key body, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_effect root h]
    refine memoize_intro root q m child _ fun layerScope => ?_
    rw [constructionAt_effect root h]
    refine updateContext_intro root _ (Region.construct (q.child 0) (some key)) _ ?_
    simp only [regionCode]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (denoteR root body (q.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
    · have hb := at_child_of h 0
      have hr := hres (q.child 0) (Nat.lt_of_le_of_lt (weight_child q 0) hq)
      rw [denoteAt_of_at hb] at hr
      exact hr
    · intro completed v
      show CodeMeans root (Program.contAOf root (.bindService (some key)) v) _
      rw [contAOf_bindService]
      simp only [seqR, bindServiceK, bindServiceR, prepareR_pure]
      exact CodeMeans.success _
  | .effectDiscard body, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_effectDiscard root h]
    refine memoize_intro root q m child _ fun layerScope => ?_
    rw [constructionAt_effectDiscard root h]
    refine updateContext_intro root _ (Region.construct (q.child 0) none) _ ?_
    simp only [regionCode]
    rw [guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (denoteR root body (q.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
    · have hb := at_child_of h 0
      have hr := hres (q.child 0) (Nat.lt_of_le_of_lt (weight_child q 0) hq)
      rw [denoteAt_of_at hb] at hr
      exact hr
    · intro completed v
      show CodeMeans root (Program.contAOf root (.bindService none) v) _
      rw [contAOf_bindService]
      simp only [seqR, bindServiceK, bindServiceR, prepareR_pure]
      exact CodeMeans.success _
  | .provide self that, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_provide root h]
    have hs := at_child_of h 0
    have ht := at_child_of h 1
    refine provideWith_intro root q m child .provide _ _ ?_ ?_
    · rw [resolveLayer_of_at root ht]
      exact layer_intro root n hres that (q.child 1) m child
        (Nat.lt_of_le_of_lt (weight_child q 1) hq) ht
    · rw [resolveLayer_of_at root hs]
      exact layer_intro root n hres self (q.child 0) m child
        (Nat.lt_of_le_of_lt (weight_child q 0) hq) hs
  | .provideMerge self that, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_provideMerge root h]
    have hs := at_child_of h 0
    have ht := at_child_of h 1
    refine provideWith_intro root q m child .provideMerge _ _ ?_ ?_
    · rw [resolveLayer_of_at root ht]
      exact layer_intro root n hres that (q.child 1) m child
        (Nat.lt_of_le_of_lt (weight_child q 1) hq) ht
    · rw [resolveLayer_of_at root hs]
      exact layer_intro root n hres self (q.child 0) m child
        (Nat.lt_of_le_of_lt (weight_child q 0) hq) hs
  | .merge left right, q, m, scope, hq, h => by
    simp only [compileLayer, denoteLayer]
    refine fromBuild_intro root q m scope _ fun child => ?_
    rw [innerLayerAt_merge root h]
    have h0 := at_child_of h 0
    have h1 := at_child_of h 1
    refine mergeTwo_intro root q m child ?_ ?_
    · intro c
      rw [resolveLayer_of_at root h0, layerBuildR_of_at h0]
      exact layer_intro root n hres left (q.child 0) m c
        (Nat.lt_of_le_of_lt (weight_child q 0) hq) h0
    · intro c
      rw [resolveLayer_of_at root h1, layerBuildR_of_at h1]
      exact layer_intro root n hres right (q.child 1) m c
        (Nat.lt_of_le_of_lt (weight_child q 1) hq) h1

/-- `Effect.provide`'s protocol after its counted step (`internal/layer.ts:15-21`): the scope
made, the layer built into it, the body under the built context, the scope closed. -/
theorem provideLayer_intro (root : NativeEff) (n : Nat)
    (hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q))
    (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff) (p : Point)
    (completed : List (FiberId × ExitV)) (hp : p.weight ≤ n) (hpos : p.fuel ≠ 0)
    (h : Node.at_ (.eff root) p.path = some (.eff (.provideLayer l i b))) :
    CodeMeans root
      (Prim.onSuccess
        (Prim.sync (EffThunk.op (SyncOp.scopeMake FinalizerStrategy.sequential)))
        (.provideLayerWith p))
      (prepareR completed (provideLayerR (fun q m s => denoteLayer root l q m s)
        (fun q => denoteR root b q) (fun q => inlineYield b q) i p)) := by
  have hw : ∀ j, (p.child j).weight < n := fun j =>
    Nat.lt_of_lt_of_le (weight_child_lt p j hpos) hp
  have hl := at_child_of h 0
  have hb := at_child_of h 1
  have hbuild : ∀ (m : MemoMapId) (scope : Nat),
      CodeMeans root (resolveLayer root (p.child 0) m scope)
        (denoteLayer root l (p.child 0) m scope) := by
    intro m scope
    rw [resolveLayer_of_at root hl]
    exact layer_intro root n hres l (p.child 0) m scope (hw 0) hl
  unfold provideLayerR
  rw [prepareR_guardR_bind, guardR_bind]
  refine CodeMeans.onSuccess _ _ _ (prepareR completed (storeR (.scopeMake .sequential))) _
    (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
  intro completed' v
  simp only [seqR]
  cases hs : Val.scope? v with
  | some scope =>
    have hv := Val.scope?_exact hs
    subst hv
    show CodeMeans root (Program.contAOf root (.provideLayerWith p) (Val.scopeHandle scope)) _
    rw [contAOf_provideLayerWith_scope]
    unfold provideLayerWithK
    rw [h]
    dsimp only
    unfold onExitR
    rw [prepareR_guardR_bind, guardR_bind]
    refine CodeMeans.onExit _ _ _ (prepareR completed' _)
      (fun ex => finalizerR ex (.vis (.inr (.closeScope scope ex)) Effects.Program.pure)) ?_ ?_
      (fun _ _ => rfl) rfl (fun _ => rfl)
    · rw [prepareR_guardR_bind, guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (prepareR completed' _) _ ?_ ?_ rfl (fun _ => rfl)
      · cases i
        · -- `buildWithScope`: the context read, the map forked or created, the build
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _ (prepareR completed' (fiberValR .getContext rfl)) _
            (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
          intro completed'' w
          show CodeMeans root
            (Program.contAOf root (.buildWithScopeFromContext (p.child 0) scope) w) _
          rw [contAOf_buildWithScopeFromContext]
          unfold buildWithScopeK
          simp only [seqR]
          cases hctx : Val.context? w with
          | some ctx =>
            dsimp only
            rw [prepareR_guardR_bind, guardR_bind]
            refine CodeMeans.onSuccess _ _ _ (prepareR completed'' (storeR _)) _
              (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
            intro completed''' u
            simp only [seqR]
            exact withMemoMapThen_intro root (p.child 0) scope _ (fun m => hbuild m scope)
              completed''' u
          | none => exact codeMeans_badShape root
        · -- `local`: a private map, then the build
          simp only [↓reduceIte]
          rw [prepareR_guardR_bind, guardR_bind]
          refine CodeMeans.onSuccess _ _ _ (prepareR completed' (storeR (.memoFork none))) _
            (CodeMeans.syncOp _ _ (successV root)) ?_ rfl (fun _ => rfl)
          intro completed'' w
          simp only [seqR]
          exact withMemoMapThen_intro root (p.child 0) scope _ (fun m => hbuild m scope)
            completed'' w
      · intro completed'' built
        show CodeMeans root (Program.contAOf root (.provideLayerBody p) built) _
        rw [contAOf_provideLayerBody]
        unfold provideLayerBodyK
        simp only [seqR]
        cases hd : Env.decode built with
        | some ctx =>
          dsimp only
          rw [resolve_of_at hb, inlineYield_eq_headExit b (p.child 1), headExit_eq_asExit?]
          cases (compileEff b (p.child 1)).asExit? with
          | some exit =>
            simp only [prepareR_pure]
            exact codeMeans_ofExit_pure root exit
          | none =>
            refine (updateContext_intro root _ (Region.program (p.child 1))
              (denoteR root b (p.child 1)) ?_).prepare _
            show CodeMeans root (resolve root (p.child 1)) _
            have hr := hres (p.child 1) (hw 1)
            rw [resolve_of_at hb, denoteAt_of_at hb] at hr
            rw [resolve_of_at hb]
            exact hr
        | none => exact codeMeans_badShape root
    · intro completed'' ex program hprog
      have hp' : Prim.withFiber (EffThunk.closeScope scope ex) = program := Option.some.inj hprog
      rw [← hp']
      refine finalizer_intro root completed'' ex ?_
      exact CodeMeans.actCloseScope _ _ _ _ rfl delivers_pure
  | none =>
    show CodeMeans root (Program.contAOf root (.provideLayerWith p) v) _
    rw [contAOf_provideLayerWith_other root p v (Val.scope?_none hs)]
    simp only [prepareR_pure]
    exact codeMeans_badShape root

theorem code_intro_aux (root : NativeEff) : ∀ (n : Nat) (p : Point), p.weight < n →
    ∀ (e : NativeEff), Node.at_ (.eff root) p.path = some (.eff e) →
      CodeMeans root (compileEff e p) (denoteR root e p) := by
  intro n
  induction n with
  | zero => intro p hp; exact absurd hp (Nat.not_lt_zero _)
  | succ n ih =>
  intro p hp e h
  have hle : p.weight ≤ n := Nat.lt_succ_iff.mp hp
  cases hf : p.fuel with
  | zero =>
    rw [compileEff_at_zero e hf, denoteR_zero root e p hf]
    exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ fun completed => by
      rw [suspendBodyAt_zero' (q := { p with completed }) hf]; rfl
  | succ k =>
  have hpos : p.fuel ≠ 0 := by rw [hf]; exact Nat.succ_ne_zero k
  have hres : ∀ q : Point, q.weight < n → CodeMeans root (resolve root q) (denoteAt root q) :=
    resolve_intro_of root n ih
  have hw0 : ∀ i, (p.child i).weight < n := fun i =>
    Nat.lt_of_lt_of_le (weight_child_lt p i hpos) hle
  have hw00 : ((p.child 0).child 0).weight < n :=
    Nat.lt_of_le_of_lt (weight_child (p.child 0) 0) (hw0 0)
  have hwc : ∀ (c : List (FiberId × ExitV)) (i : Nat),
      (({ p with completed := c } : Point).child i).weight < n := fun c i =>
    Nat.lt_of_lt_of_le (weight_child_lt { p with completed := c } i hpos) hle
  have hwcw : ∀ (c : List (FiberId × ExitV)) (i : Nat) (v : Val),
      (({ p with completed := c } : Point).childWith i v).weight < n := fun c i v =>
    Nat.lt_of_lt_of_le (weight_childWith_lt { p with completed := c } i v hpos) hle
  cases e with
  | succeed t =>
    rw [compileEff_succeed t hf, denoteR_succeed root t hpos]
    cases evalTerm p.env t with
    | some v => exact CodeMeans.success v
    | none => exact codeMeans_badShape root
  | fail t =>
    rw [compileEff_fail t hf, denoteR_fail root t hpos]
    cases evalTerm p.env t with
    | some v => exact CodeMeans.failure _
    | none => exact codeMeans_badShape root
  | failCause c =>
    rw [compileEff_failCause c hf, denoteR_failCause root c hpos]
    cases causeOf p.env c with
    | some cause => exact CodeMeans.failure _
    | none => exact codeMeans_badShape root
  | yieldError t =>
    rw [compileEff_yieldError t hf, denoteR_yieldError root t hpos]
    cases evalTerm p.env t with
    | some v => exact CodeMeans.yieldError p (errOf v) _ fun _ => CodeMeans.failure _
    | none => exact codeMeans_badShape root
  | sync t =>
    rw [compileEff_sync t hf, denoteR_sync root t hpos, ← syncValueAt_pure h]
    exact CodeMeans.syncPure p _ (CodeMeans.success _)
  | suspend b =>
    rw [compileEff_suspend b hf, denoteR_suspend root b p hpos]
    refine CodeMeans.suspendBody p _ fun completed => ?_
    have hb := at_child_of (p := { p with completed }) h 0
    show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
    rw [suspendBodyAt_suspend (q := { p with completed }) hf h, resolve_of_at hb]
    simp only [prepareR_constructR, prepareR_denoteR]
    exact ih _ (hwc completed 0) b hb
  | perform op r =>
    rw [denoteR_perform root op r hpos]
    cases hk : (NativeOp.row op).kind with
    | sync =>
      rw [compileEff_perform_sync op r hf hk]
      cases evalTerm p.env r with
      | none => exact codeMeans_badShape root
      | some v =>
        dsimp only [Option.bind]
        cases NativeOp.syncOpOf op v with
        | some o => exact CodeMeans.syncOp o _ (successV root)
        | none => exact codeMeans_badShape root
    | async =>
      rw [compileEff_perform_async op r hf hk]
      unfold denoteAsync
      cases evalTerm p.env r with
      | none => exact codeMeans_badShape root
      | some v =>
        dsimp only [Option.bind]
        cases NativeOp.awaitCellOf v with
        | some cell => exact CodeMeans.asyncAwait cell v _ delivers_pure
        | none => exact codeMeans_badShape root
    | program =>
      rw [compileEff_perform_program op r hf hk]
      exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ fun completed => by
        rw [suspendBodyAt_of_at (q := { p with completed }) hf h nofun nofun nofun nofun nofun,
          compileEff_perform_program op r (p := { p with completed }) hf hk]
        rfl
  | bind a b =>
    rw [compileEff_bind a b hf, denoteR_bind root a b p hpos, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (denoteR root a (p.child 0))
      (seqR fun v => constructR fun completed => denoteR root b ({ p with completed }.childWith 1 v))
      ?_ ?_ rfl (fun _ => rfl)
    · exact ih _ (hw0 0) a (at_child_of h 0)
    · intro completed v
      have hb := at_childWith_of (p := { p with completed }) h 1 v
      show CodeMeans root (resolve root ({ p with completed }.childWith 1 v))
        (prepareR completed (constructR _))
      rw [resolve_of_at hb]
      simp only [prepareR_constructR, prepareR_denoteR]
      exact ih _ (hwcw completed 1 v) b hb
  | gen ss =>
    rw [compileEff_gen ss hf, denoteR_gen root ss p hpos]
    refine CodeMeans.suspendBody p _ fun completed => ?_
    show CodeMeans root (suspendBodyAt root (.body { p with completed }))
      (prepareR completed (.vis (.inr (.gen p)) Effects.Program.pure))
    rw [suspendBodyAt_gen (q := { p with completed }) hf h]
    exact CodeMeans.genEntry p _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ delivers_pure
  | catchCause b hd =>
    rw [compileEff_catchCause b hd hf, denoteR_catchCause root b hd hpos, guardR_bind]
    refine CodeMeans.onFailure _ _ _ (denoteR root b (p.child 0)) _ ?_ ?_ rfl (fun _ => rfl)
    · exact ih _ (hw0 0) b (at_child_of h 0)
    · intro completed c
      have hb := at_childWith_of (p := { p with completed }) h 1 (.exitErr c)
      show CodeMeans root (resolve root ({ p with completed }.childWith 1 (.exitErr c)))
        (prepareR completed (constructR _))
      rw [resolve_of_at hb]
      simp only [prepareR_constructR, prepareR_denoteR]
      exact ih _ (hwcw completed 1 _) hd hb
  | matchCause b v c =>
    rw [compileEff_matchCause b v c hf, denoteR_matchCause root b v c hpos, guardR_bind]
    refine CodeMeans.onBoth _ _ _ _ (denoteR root b (p.child 0)) _ ?_ ?_ ?_ rfl (fun _ => rfl)
    · exact ih _ (hw0 0) b (at_child_of h 0)
    · intro completed x
      have hb := at_childWith_of (p := { p with completed }) h 1 x
      show CodeMeans root (resolve root ({ p with completed }.childWith 1 x))
        (prepareR completed (constructR _))
      rw [resolve_of_at hb]
      simp only [prepareR_constructR, prepareR_denoteR]
      exact ih _ (hwcw completed 1 x) v hb
    · intro completed cause
      have hb := at_childWith_of (p := { p with completed }) h 2 (.exitErr cause)
      show CodeMeans root (resolve root ({ p with completed }.childWith 2 (.exitErr cause)))
        (prepareR completed (constructR _))
      rw [resolve_of_at hb]
      simp only [prepareR_constructR, prepareR_denoteR]
      exact ih _ (hwcw completed 2 _) c hb
  | onExit b f =>
    rw [compileEff_onExit b f hf, denoteR_onExit root b f hpos]
    unfold onExitR
    rw [guardR_bind]
    refine CodeMeans.onExit _ _ _ (denoteR root b (p.child 0))
      (fun ex => finalizerR ex (constructR fun completed =>
        denoteR root f ({ p with completed }.childWith 1 (reifyExitVal ex))))
      ?_ ?_ (fun _ _ => rfl) rfl (fun _ => rfl)
    · exact ih _ (hw0 0) b (at_child_of h 0)
    · intro completed ex program hprog
      have hp' : resolve root ({ p with completed }.childWith 1 (reifyExitVal ex)) = program :=
        Option.some.inj hprog
      rw [← hp']
      refine finalizer_intro root completed ex ?_
      have hb := at_childWith_of (p := { p with completed }) h 1 (reifyExitVal ex)
      rw [resolve_of_at hb]
      simp only [prepareR_constructR, prepareR_denoteR]
      exact ih _ (hwcw completed 1 _) f hb
  | exit b =>
    rw [compileEff_exit b hf, denoteR_exit root b p hpos, inlineYield_eq_headExit,
      headExit_eq_asExit?]
    cases (compileEff b (p.child 0)).asExit? with
    | some ex => exact CodeMeans.success _
    | none =>
      show CodeMeans root (Prim.exitFrame _) ((guardR .all _).bind _)
      rw [guardR_bind]
      refine CodeMeans.exitFrame _ _ (denoteR root b (p.child 0))
        (fun ex => .pure (.success (reifyExitVal ex))) ?_ (fun _ _ => CodeMeans.success _) rfl
        (fun _ => rfl)
      exact ih _ (hw0 0) b (at_child_of h 0)
  | uninterruptible b =>
    rw [compileEff_uninterruptible b hf, denoteR_uninterruptible root b hpos]
    have hact : actionAt root p = some (.setInterruptible (resolve root (p.child 0)) false) := by
      simp [actionAt, h]
    unfold denoteAction; rw [hact]
    exact CodeMeans.actMask _ _ _ (.at_ (p.child 0)) _ hact (hres _ (hw0 0)) delivers_pure
  | interruptible b =>
    rw [compileEff_interruptible b hf, denoteR_interruptible root b hpos]
    have hact : actionAt root p = some (.setInterruptible (resolve root (p.child 0)) true) := by
      simp [actionAt, h]
    unfold denoteAction; rw [hact]
    exact CodeMeans.actMask _ _ _ (.at_ (p.child 0)) _ hact (hres _ (hw0 0)) delivers_pure
  | branch t a b =>
    rw [compileEff_branch t a b hf, denoteR_branch root t a b p hpos]
    refine CodeMeans.suspendBody p _ fun completed => ?_
    show CodeMeans root (suspendBodyAt root (.body { p with completed })) (prepareR completed (constructR _))
    simp only [prepareR_constructR]
    rcases hv : evalTerm p.env t with _ | v
    · rw [suspendBodyAt_branch_bad (q := { p with completed }) hf h
        (fun flag heq => by rw [hv] at heq; cases heq)]
      exact codeMeans_badShape root
    · cases v
      case bool flag =>
        cases flag
        · have hb := at_child_of (p := { p with completed }) h 1
          rw [suspendBodyAt_branch_false (q := { p with completed }) hf h hv, resolve_of_at hb]
          simp only [prepareR_denoteR]
          exact ih _ (hwc completed 1) b hb
        · have hb := at_child_of (p := { p with completed }) h 0
          rw [suspendBodyAt_branch_true (q := { p with completed }) hf h hv, resolve_of_at hb]
          simp only [prepareR_denoteR]
          exact ih _ (hwc completed 0) a hb
      all_goals
        rw [suspendBodyAt_branch_bad (q := { p with completed }) hf h
          (fun flag heq => by rw [hv] at heq; cases heq)]
        exact codeMeans_badShape root
  | whileLoop i t s b =>
    rw [compileEff_whileLoop i t s b hf, denoteR_whileLoop root i t s b p hpos]
    refine CodeMeans.suspendBody p _ fun completed => ?_
    show CodeMeans root (suspendBodyAt root (.body { p with completed }))
      (prepareR completed (match evalTerm p.env i with
        | some cursor => .vis (.inr (.loop p cursor)) Effects.Program.pure
        | none => .pure badShapeExit))
    rw [suspendBodyAt_whileLoop (q := { p with completed }) hf h]
    dsimp only
    rcases hv : evalTerm p.env i with _ | cursor
    · exact codeMeans_badShape root
    · exact CodeMeans.loopEntry p _ cursor _ ⟨rfl, rfl, rfl, rfl, rfl⟩ delivers_pure
  | yieldNow priority =>
    rw [compileEff_yieldNow priority hf, denoteR_yieldNow root priority hpos]
    exact CodeMeans.yieldNow priority _ delivers_seqR_pure
  | callback op r =>
    rw [compileEff_callback op r hf, denoteR_callback root op r hpos]
    cases op
    case sleep =>
      unfold denoteSleep
      cases (evalTerm p.env r).bind NativeOp.sleepMillisOf with
      | none => exact codeMeans_badShape root
      | some n =>
        cases n with
        | zero => exact CodeMeans.yieldNow 0 _ delivers_seqR_pure
        | succ n => exact CodeMeans.asyncSleep (n + 1) (Val.nat (n + 1)) _ delivers_pure
    all_goals first
      | exact codeMeans_badShape root
      | (rename_i s; cases s <;> exact codeMeans_badShape root)
      | (unfold denoteAsync
         cases evalTerm p.env r with
         | none => exact codeMeans_badShape root
         | some v =>
           dsimp only [Option.bind]
           cases NativeOp.awaitCellOf v with
           | some cell => exact CodeMeans.asyncAwait cell v _ delivers_pure
           | none => exact codeMeans_badShape root)
  | awaitFiber t mode =>
    rw [compileEff_awaitFiber t mode hf, denoteR_awaitFiber root t mode hpos]
    rcases hv : evalTerm p.env t with _ | v
    · exact codeMeans_badShape root
    · -- the value is a fiber handle or it is not; both sides match on that
      cases hfib : Val.fiber? v with
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
        -- one `split` settles both sides: they match on the same discriminant
        have hb : ∀ id, v ≠ Val.fiber ⟨id⟩ := fun id => Val.fiber?_none hfib ⟨id⟩
        split
        · next id heq => exact absurd (Option.some.inj heq) (hb id)
        · exact codeMeans_badShape root
  | withFiber a =>
    cases hfs : forkScoped? a with
    | some co =>
      obtain ⟨child, options⟩ := co
      obtain rfl := forkScoped?_some hfs
      rw [compileEff_withFiber_forkScoped child options hf, denoteR_withFiber root _ p hpos]
      have hact : actionAt root p = some .ambientScope := by simp [actionAt, h]
      unfold denoteAction; rw [hact]
      simp only [denoteFiberAction, h]
      rw [guardR_bind]
      refine CodeMeans.onSuccess _ _ _ (fiberValR .ambientScope rfl) _ ?_ ?_ rfl (fun _ => rfl)
      · exact CodeMeans.actAmbientScope _ _ hact (successV root)
      · intro completed v
        -- the handle the service read answered is a scope handle or it is not
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
          simp only [seqR]
          first
            | exact CodeMeans.failure _
            | (split
               · first
                   | (next s heq => exact absurd heq (hne s))
                   | (next s => exact absurd rfl (hne s))
               · exact CodeMeans.failure _)
    | none =>
      have hnot : ∀ c o, a ≠ .forkScoped c o := forkScoped?_none hfs
      rw [compileEff_withFiber_other a hf hnot, denoteR_withFiber root a p hpos]
      obtain ⟨act, hact⟩ : ∃ act, actionAt root p = some act := by
        unfold actionAt; rw [h]; exact ⟨_, rfl⟩
      have hs := actionAt_shape h hact
      unfold denoteAction; rw [hact]
      have ht : (interpOf root).withFiberOf (.act p) = some act := hact
      cases act with
      | fork program options =>
        obtain rfl := hs.1 program options rfl
        exact CodeMeans.actFork _ _ _ _ _ ht (hres _ hw00) (successV root)
      | forkIn program options scope =>
        obtain rfl := hs.2.1 program options scope rfl
        exact CodeMeans.actForkIn _ _ _ _ _ _ ht (hres _ hw00) (successV root)
      | forkScoped program options => exact absurd rfl (hs.2.2.1 program options)
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
        obtain ⟨es, rfl, rfl⟩ := hs.2.2.2.1 entrants rfl
        have hpts : racePoints root p = entrantPoints es ((p.child 0).child 0) := by
          simp [racePoints, h]
        show CodeMeans root _ (.vis (.inr (.raceAll (racePoints root p))) Effects.Program.pure)
        rw [hpts]
        have hes : Node.at_ (.eff root) ((p.child 0).child 0).path = some (.effs es) :=
          at_child_of (n := .action (.raceAll es)) (at_child_of h 0) 0
        obtain ⟨hlen, hc⟩ := entrants_intro root n ih es _ hw00 hes
        exact CodeMeans.actRaceAll _ _ _ _ ht hlen hc delivers_pure
      | setInterruptible body flag => exact absurd rfl (hs.2.2.2.2.1 body flag)
      | setContext ctx => exact CodeMeans.actSetContext _ _ _ ht (successV root)
      | getContext => exact CodeMeans.actGetContext _ _ ht (successV root)
      | getId => exact CodeMeans.actGetId _ _ ht (successV root)
      | closeScope scope ex => exact CodeMeans.actCloseScope _ _ _ _ ht delivers_pure
      | refuse cause => exact CodeMeans.actRefuse _ _ _ ht (successV root)
      | dropObservers token => exact CodeMeans.actDropObservers _ _ _ ht (successV root)
      | cancelRace race => exact CodeMeans.actCancelRace _ _ _ ht delivers_seqR_pure
      | ambientScope =>
        obtain ⟨c, o, heq⟩ := hs.2.2.2.2.2.1 rfl
        exact absurd heq (hnot c o)
      | closePar fins => exact absurd rfl (hs.2.2.2.2.2.2 fins)
  | «scoped» b =>
    rw [compileEff_scoped b hf, denoteR_scoped root b hpos]
    exact CodeMeans.scopedNode p b _ h delivers_pure
  | acquireRelease a r =>
    rw [compileEff_acquireRelease a r hf, denoteR_acquireRelease root a r hpos, guardR_bind]
    -- the release's point: the capture's point (this one, the acquired value appended) at
    -- child 1, at any view — one fuel down, so inside the measure
    have hwrel : ∀ (completed : List (FiberId × ExitV)) (a : Val) (ctx : Ctx) (ex : ExitV),
        ((Point.ofCapture (p.capture a ctx) completed).childWith 1 (reifyExitVal ex)).weight < n :=
      fun completed a ctx ex => Nat.lt_of_lt_of_le
        (weight_childWith_lt { p with env := p.env ++ [a], completed } 1 (reifyExitVal ex) hpos) hle
    refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _ ?_ ?_ rfl (fun _ => rfl)
    · exact CodeMeans.actGetContext _ _ rfl (successV root)
    · intro completed v
      show CodeMeans root (Program.contAOf root (.acquireCtx p) v) _
      rw [contAOf_acquireCtx]
      simp only [seqR]
      -- the context read back off the value, or not
      cases hctx : Val.context? v with
      | some ctx =>
        dsimp only
        -- `prepareR` is the identity on the mask operation, definitionally
        refine CodeMeans.actMask _ _ false (.acquireIn p ctx) _ rfl ?_ delivers_pure
        refine acquireIn_intro root p ctx (hres _ (hw0 0)) fun a ex => ?_
        exact foreignRelease_intro root _ ex fun completed' => hres _ (hwrel completed' a ctx ex)
      | none => exact codeMeans_badShape root
  | choose site l r =>
    rw [compileEff_choose site l r hf, denoteR_choose root site l r p hpos]
    rcases ht : p.tape with _ | ⟨flag, rest⟩
    · exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩ fun completed => by
        rw [suspendBodyAt_of_at (q := { p with completed }) hf h nofun nofun nofun nofun nofun,
          compileEff_choose site l r (p := { p with completed }) hf]
        simp only [ht]
        rfl
    · have hw : p.fuel + rest.length < n := by
        simp only [Point.weight] at hle
        rw [ht, List.length_cons] at hle
        omega
      cases flag
      · exact ih { p with path := p.path ++ [1], tape := rest } hw r
          (by rw [Node.at_append, h]; rfl)
      · exact ih { p with path := p.path ++ [0], tape := rest } hw l
          (by rw [Node.at_append, h]; rfl)

  -- the join: the counted step, then the protocol at the point carrying the view
  | provideLayer l i b =>
    rw [compileEff_provideLayer l i b hf, denoteR_provideLayer root l i b hpos]
    unfold suspendR
    refine CodeMeans.suspendBody p _ fun completed => ?_
    rw [suspendBodyAt_provideLayer (q := { p with completed }) hf h, prepareR_constructR]
    exact provideLayer_intro root n hres l i b { p with completed } completed hle hpos h
  -- the context read, then the lookup
  | service key =>
    rw [compileEff_service key hf, denoteR_service root key hpos, guardR_bind]
    refine CodeMeans.onSuccess _ _ _ (fiberValR .getContext rfl) _
      (CodeMeans.actGetContext _ _ rfl (successV root)) ?_ rfl (fun _ => rfl)
    intro completed v
    show CodeMeans root (Program.contAOf root (.serviceLookup key) v) _
    rw [contAOf_serviceLookup]
    unfold serviceLookupK serviceLookupR
    simp only [seqR]
    cases Val.context? v with
    | some ctx =>
      cases hg : ctx.services.getV key with
      | some value => simp only [hg, prepareR_pure]; exact CodeMeans.success _
      | none => simp only [hg, prepareR_pure]; exact CodeMeans.failure _
    | none => exact codeMeans_badShape root
  -- a `Context.add` region over the body
  | provideService key value b =>
    rw [compileEff_provideService key value b hf, denoteR_provideService root key value b hpos]
    cases evalTerm p.env value with
    | some v =>
      have hb := at_child_of h 0
      refine updateContext_intro root _ (Region.program (p.child 0)) (denoteR root b (p.child 0)) ?_
      show CodeMeans root (resolve root (p.child 0)) _
      rw [resolve_of_at hb]
      exact ih _ (hw0 0) b hb
    | none => exact codeMeans_badShape root

/-- **Introduction.** At every source address, the compile and the denotation are related. -/
theorem code_intro (root : NativeEff) (e : NativeEff) (p : Point)
    (h : Node.at_ (.eff root) p.path = some (.eff e)) :
    CodeMeans root (compileEff e p) (denoteR root e p) :=
  code_intro_aux root (p.weight + 1) p (Nat.lt_succ_self _) e h

/-- Every point resolves to related programs (the fallbacks are the same refusal). -/
theorem resolve_intro (root : NativeEff) (q : Point) :
    CodeMeans root (resolve root q) (denoteAt root q) :=
  resolve_intro_of root (q.weight + 1) (fun p _ e h => code_intro root e p h) q (Nat.lt_succ_self _)

/-- Every layer point resolves to related builds (the fallbacks are the same refusal). -/
theorem layerBuild_intro (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) :
    CodeMeans root (resolveLayer root q m scope) (layerBuildR root q m scope) := by
  unfold resolveLayer layerBuildR
  rcases hn : Node.at_ (.eff root) q.path with _ | node
  · exact codeMeans_badShape root
  · cases node
    case layer l =>
      exact layer_intro root (q.weight + 1) (fun q' _ => resolve_intro root q') l q m scope
        (Nat.lt_succ_self _) hn
    all_goals exact codeMeans_badShape root

/-- The loaded roots are related. -/
theorem compile_intro (root : NativeEff) (fuel : Nat) (tape : List Bool) :
    CodeMeans root (compile root fuel tape) (denoteR root root (rootPoint fuel tape)) :=
  code_intro root root (rootPoint fuel tape) rfl

end Effect4.Program.Sched
