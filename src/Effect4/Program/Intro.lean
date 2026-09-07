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
      (match (NativeOp.row op).kind with
       | .async => denoteAsync r p
       | _ => .pure badShapeExit) := by
  cases hf : p.fuel with
  | zero => exact (h hf).elim
  | succ f => rw [denoteR, hf]; try rfl

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
    denoteR root (.acquireRelease a r) p = pending .unsupported p := by
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
      (match (NativeOp.row op).kind with
       | .async =>
         match (evalTerm p.env r).bind NativeOp.awaitCellOf with
         | some cell => Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
         | none => badShape
       | _ => badShape) := by
  rw [compileEff, hf]; try rfl

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
    compileEff (.acquireRelease a r) p = frontier p := by
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
        cases (NativeOp.row op).kind with
        | async => exact prepareR_denoteAsync r p completed
        | sync => rfl
        | program => rfl
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
      | acquireRelease a r => rw [denoteR_acquireRelease root a r hpos]; rfl
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
    exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl⟩ fun completed => by
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
      exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl⟩ fun completed => by
        rw [suspendBodyAt_of_at (q := { p with completed }) hf h nofun nofun nofun nofun,
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
    exact CodeMeans.genEntry p _ _ ⟨rfl, rfl, rfl, rfl⟩ delivers_pure
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
    · exact CodeMeans.loopEntry p _ cursor _ ⟨rfl, rfl, rfl, rfl⟩ delivers_pure
  | yieldNow priority =>
    rw [compileEff_yieldNow priority hf, denoteR_yieldNow root priority hpos]
    exact CodeMeans.yieldNow priority _ delivers_seqR_pure
  | callback op r =>
    rw [compileEff_callback op r hf, denoteR_callback root op r hpos]
    cases hk : (NativeOp.row op).kind with
    | async =>
      unfold denoteAsync
      cases evalTerm p.env r with
      | none => exact codeMeans_badShape root
      | some v =>
        dsimp only [Option.bind]
        cases NativeOp.awaitCellOf v with
        | some cell => exact CodeMeans.asyncAwait cell v _ delivers_pure
        | none => exact codeMeans_badShape root
    | sync => exact codeMeans_badShape root
    | program => exact codeMeans_badShape root
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
    rw [compileEff_acquireRelease a r hf, denoteR_acquireRelease root a r hpos]
    exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl⟩ fun completed => by
      rw [suspendBodyAt_of_at (q := { p with completed }) hf h nofun nofun nofun nofun,
        compileEff_acquireRelease a r (p := { p with completed }) hf]
      rfl
  | choose site l r =>
    rw [compileEff_choose site l r hf, denoteR_choose root site l r p hpos]
    rcases ht : p.tape with _ | ⟨flag, rest⟩
    · exact CodeMeans.frontier p p _ _ ⟨rfl, rfl, rfl, rfl⟩ fun completed => by
        rw [suspendBodyAt_of_at (q := { p with completed }) hf h nofun nofun nofun nofun,
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

/-- **Introduction.** At every source address, the compile and the denotation are related. -/
theorem code_intro (root : NativeEff) (e : NativeEff) (p : Point)
    (h : Node.at_ (.eff root) p.path = some (.eff e)) :
    CodeMeans root (compileEff e p) (denoteR root e p) :=
  code_intro_aux root (p.weight + 1) p (Nat.lt_succ_self _) e h

/-- Every point resolves to related programs (the fallbacks are the same refusal). -/
theorem resolve_intro (root : NativeEff) (q : Point) :
    CodeMeans root (resolve root q) (denoteAt root q) :=
  resolve_intro_of root (q.weight + 1) (fun p _ e h => code_intro root e p h) q (Nat.lt_succ_self _)

/-- The loaded roots are related. -/
theorem compile_intro (root : NativeEff) (fuel : Nat) (tape : List Bool) :
    CodeMeans root (compile root fuel tape) (denoteR root root (rootPoint fuel tape)) :=
  code_intro root root (rootPoint fuel tape) rfl

end Effect4.Program.Sched
