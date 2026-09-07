import Effect4.Machine.Handles
import Effect4.Api
import Effect4.Program.Typed
import Effect4.Program.Agreement

/-!
# The handle invariant at the compiled alphabet

`Effect4.Machine.Handles` proves that replay keeps every collected handle pointing at
something minted, for any name and thunk alphabet whose interpreter is `KeyBounded`. This
module instantiates it at the native alphabet (`EffName`, `EffThunk`, `Point`, `Ctx`) and the
interpreter `interpOf root` of `Effect4.Program.Compile`, and states the result on the public
API:

* `Minted (m : Api.Machine)`: every handle in the declared positions exists (decidable);
* `AnswersValid program fuel tape choices`: every `answerAsync` of the tape names handles
  that exist in the machine it answers (decidable, the C15 `TapeAddressed` reading);
* `load_minted`: a freshly loaded program holds no handle, so it is `Minted`;
* `handles_minted`: `Minted (Api.load …) ∧ AnswersValid … → Minted (Api.replay …).machine`.

What is proved about the compile: the code a point compiles to names only the handles in
the point's environment (`compileEff_keys`, `resolve_keys`), the generator walker keeps to its
environment (`runStmts_keys`), a `withFiber` action names only what its point's terms
evaluate to (`actionAt_keys`), and the embedded stores' programs carry the stores' own keys
(`embed_keys`). The ruling in force is the valid-input premise: `AnswersValid` is a premise of
the theorem, and replay admission is unchanged (`E4-HANDLE-CE-001`).

Excluded, as in the machine module: the cause's interruptor, the exit a scope closed
with, the race's duplicate winner and unused bookkeeping, and a Deferred's waiter targets.
The race's live entrants and accepted exit are collected: both flow into `raceSettle`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## The native alphabet's handles -/

/-- The handles a point holds: the values in scope. -/
def Point.keys (p : Point) : List Handle := p.env.flatMap Val.keys

/-- The handles a name of the compiled alphabet carries. -/
def EffName.keys : EffName → List Handle
  | .cont p => p.keys
  | .caught p => p.keys
  | .onValue p => p.keys
  | .onCause p => p.keys
  | .fin p => p.keys
  | .restore exit => exitKeys exit
  | .merge exit => exitKeys exit
  | .gen p _ _ => p.keys
  | .loop p => p.keys
  | .registerAwait cell => [Handle.promise cell]
  | .cancelAwait cell => [Handle.promise cell]
  | .withWaiter base waiter _ => Handle.fiber waiter :: base.keys
  | .abort => []
  | .reFail _ => []
  | .scopeOpen p => p.keys
  | .scopeProvide p scope => Handle.scope scope :: p.keys
  | .scopeBody p previous => p.keys ++ previous.keys
  | .scopeClose scope => [Handle.scope scope]
  | .restoreCtx previous => previous.keys
  | .constant v => v.keys
  | .store name => name.keys

/-- The handles a thunk of the compiled alphabet carries. -/
def EffThunk.keys : EffThunk → List Handle
  | .pure p => p.keys
  | .body p => p.keys
  | .op operation => operation.keys
  | .park kind => kind.keys
  | .act p => p.keys
  | .getCtx => []
  | .setCtx context => context.keys
  | .closeScope scope exit => Handle.scope scope :: exitKeys exit
  | .store thunk => thunk.keys

/-- The handles of compiled code. -/
abbrev nativeKeys : NCode → List Handle := primKeys EffName.keys EffThunk.keys

/-- The membership search also unfolds the native alphabet, the stores' alphabet and the
points' children. -/
macro_rules
  | `(tactic| sub_tac) => `(tactic| sub_tac norm [Point.keys, Point.child, Point.childWith, Point.childWith2,
      EffName.keys, EffThunk.keys, programKeys, Name.keys, Thunk.keys, ActionName.keys, FinName.keys,
      ProgName.keys, SyncOp.keys, Completion.keys, ParkKind.keys])
  | `(tactic| sub_tac using $hs:term,*) => `(tactic| sub_tac using $hs,* norm [Point.keys, Point.child,
      Point.childWith, Point.childWith2, EffName.keys, EffThunk.keys, programKeys, Name.keys, Thunk.keys,
      ActionName.keys, FinName.keys, ProgName.keys, SyncOp.keys, Completion.keys, ParkKind.keys])

theorem Point.child_keys (p : Point) (i : Nat) : (p.child i).keys = p.keys := rfl

theorem Point.childWith_keys (p : Point) (i : Nat) (v : Val) : (p.childWith i v).keys = p.keys ++ v.keys := by
  simp only [Point.keys, Point.childWith, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem Point.childWith2_keys (p : Point) (i : Nat) (v w : Val) :
    (p.childWith2 i v w).keys = p.keys ++ v.keys ++ w.keys := by
  simp only [Point.keys, Point.childWith2, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

/-! ## The embedding of the stores' programs -/

theorem embed_keys : ∀ p : Program, primKeys EffName.keys EffThunk.keys (embed p) = primKeys Name.keys Thunk.keys p
  | .success _ => rfl
  | .failure _ => rfl
  | .sync _ => rfl
  | .suspend _ => rfl
  | .withFiber _ => rfl
  | .yieldableError _ => rfl
  | .iterator _ _ => rfl
  | .onSuccess body n => by simp only [embed, primKeys, EffName.keys, embed_keys body]
  | .onFailure body n => by simp only [embed, primKeys, EffName.keys, embed_keys body]
  | .onSuccessAndFailure body a e => by simp only [embed, primKeys, EffName.keys, embed_keys body]
  | .exitFrame body => by simp only [embed, primKeys, embed_keys body]
  | .onExit body f flag => by simp only [embed, primKeys, EffName.keys, embed_keys body]
  | .setInterruptible _ => rfl
  | .whileLoop _ _ => rfl
  | .yieldNowWith _ => rfl
  | .async r s c => by cases c <;> rfl
  | .asyncFinalizer _ => rfl

theorem embed_programKeys (p : Program) : nativeKeys (embed p) = programKeys p := embed_keys p

theorem embedAction_keys (a : WithFiberAction Name Thunk Val Err Defect FiberId Ann Ctx) :
    (embedAction a).keys EffName.keys EffThunk.keys = a.keys Name.keys Thunk.keys := by
  cases a <;> simp only [embedAction, WithFiberAction.keys, embed_keys, List.flatMap_map]

/-! ## Terms evaluate inside their environment -/

theorem Lit.toVal_keys (l : Lit) (v : Val) (h : l.toVal = some v) : v.keys = [] := by
  cases l <;> simp only [Lit.toVal, Option.some.injEq] at h <;> (try cases h) <;> rfl

theorem nativeAtom_keys (atom : String) (vs : List Val) (v : Val) (h : nativeAtom atom vs = some v) :
    v.keys ⊆ vs.flatMap Val.keys := by
  unfold nativeAtom at h
  split at h <;> cases h
  all_goals sub_tac norm [Val.tuple]

theorem flatMap_subset_of_subset {α : Type} {f : α → List Handle} {l l' : List α} (h : l' ⊆ l) :
    l'.flatMap f ⊆ l.flatMap f := by
  intro x hx
  obtain ⟨a, ha, hx⟩ := List.mem_flatMap.mp hx
  exact List.mem_flatMap.mpr ⟨a, h ha, hx⟩

mutual
theorem evalTerm_keys (t : Term) (env : List Val) (v : Val) (h : evalTerm env t = some v) :
    v.keys ⊆ env.flatMap Val.keys := by
  cases t with
  | var i =>
    have h' : env[i]? = some v := h
    exact fun x hx => List.mem_flatMap.mpr ⟨v, List.mem_of_getElem? h', hx⟩
  | lit l =>
    have h' : l.toVal = some v := h
    rw [Lit.toVal_keys l v h']
    exact List.nil_subset _
  | app atom args =>
    rw [evalTerm_app] at h
    obtain ⟨vs, hvs, hv⟩ := Option.bind_eq_some_iff.mp h
    exact List.Subset.trans (nativeAtom_keys atom vs v hv) (evalTerms_keys args env vs hvs)
termination_by structural t
theorem evalTerms_keys (ts : Terms) (env : List Val) (vs : List Val) (h : evalTerms env ts = some vs) :
    vs.flatMap Val.keys ⊆ env.flatMap Val.keys := by
  cases ts with
  | nil =>
    have h' : some ([] : List Val) = some vs := h
    cases h'
    exact List.nil_subset _
  | cons head tail =>
    rw [evalTerms_cons] at h
    obtain ⟨v1, hv1, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    cases hcons
    rw [List.flatMap_cons]
    exact List.append_subset.mpr ⟨evalTerm_keys head env v1 hv1, evalTerms_keys tail env rest hrest⟩
termination_by structural ts
end

theorem exitOfVal_keys (v : Val) (e : ExitV) (h : exitOfVal v = some e) : exitKeys e ⊆ v.keys := by
  cases v <;> simp only [exitOfVal] at h <;> cases h <;> exact List.Subset.refl _

theorem awaitCellOf_keys (v : Val) (cell : DeferredKey) (h : NativeOp.awaitCellOf v = some cell) :
    Handle.promise cell ∈ v.keys := by
  cases v <;> simp only [NativeOp.awaitCellOf] at h <;> cases h <;> exact List.mem_singleton.mpr rfl

theorem syncOpOf_keys (op : NativeOp) (v : Val) (o : SyncOp) (h : NativeOp.syncOpOf op v = some o) :
    o.keys ⊆ v.keys := by
  unfold NativeOp.syncOpOf at h
  split at h <;> cases h <;> sub_tac

theorem tuple?_keys (v : Val) : ∀ vs, Val.tuple? v = some vs → vs.flatMap Val.keys ⊆ v.keys := by
  induction v with
  | exitNil =>
    intro vs h
    simp only [Val.tuple?, Option.some.injEq] at h
    subst h
    exact List.nil_subset _
  | exitCons head tail _ ih =>
    intro vs h
    simp only [Val.tuple?] at h
    obtain ⟨rest, hrest, hvs⟩ := Option.map_eq_some_iff.mp h
    subst hvs
    simp only [List.flatMap_cons, Val.keys]
    exact List.append_subset.mpr ⟨List.subset_append_left _ _,
      List.Subset.trans (ih rest hrest) (List.subset_append_right _ _)⟩
  | unit | nat _ | bool _ | fiber _ | fibers _ | cell _ | promise _ | scopeHandle _ | context _ | exitOk _ _
  | exitErr _ =>
    intro vs h
    simp only [Val.tuple?] at h
    cases h

theorem mapM_fiber_keys (g : Val → Option FiberId) (hg : ∀ v id, g v = some id → Handle.fiber id ∈ v.keys) :
    ∀ (vs : List Val) (ids : List FiberId), vs.mapM g = some ids → ids.map Handle.fiber ⊆ vs.flatMap Val.keys
  | [], ids, h => by
    simp only [List.mapM_nil, pure, Option.some.injEq] at h
    subst h
    exact List.nil_subset _
  | v :: vs, ids, h => by
    simp only [List.mapM_cons, bind, pure] at h
    obtain ⟨id, hid, h'⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨rest, hrest, hcons⟩ := Option.bind_eq_some_iff.mp h'
    simp only [Option.some.injEq] at hcons
    subst hcons
    simp only [List.map_cons, List.flatMap_cons]
    exact List.cons_subset.mpr ⟨List.mem_append_left _ (hg v id hid),
      List.Subset.trans (mapM_fiber_keys g hg vs rest hrest) (List.subset_append_right _ _)⟩

/-! ## The compile names only what is in scope -/

theorem frontier_keys (p : Point) : nativeKeys (frontier p) ⊆ p.keys := List.Subset.refl _

/-- An exit's handles are the handles of the primitive that embeds it. -/
theorem exitKeys_eq_nativeKeys_ofExit (exit : ExitV) :
    exitKeys exit = nativeKeys (Prim.ofExit exit) := by
  cases exit <;> rfl

theorem badShape_keys : nativeKeys badShape = [] := rfl

section compileArms

variable {p : Point} {k : Nat}

theorem compileEff_zero (e : NativeEff) (hf : p.fuel = 0) :
    compileEff e p = frontier p := by
  unfold compileEff
  rw [hf]

theorem compileEff_perform (op : NativeOp) (r : Term) (hf : p.fuel = k + 1) :
    compileEff (.perform op r) p =
      (match (NativeOp.row op).kind with
       | .sync =>
         match evalTerm p.env r with
         | some val =>
           match NativeOp.syncOpOf op val with
           | some operation => Prim.sync (EffThunk.op operation)
           | none => badShape
         | none => badShape
       | .async =>
         match (evalTerm p.env r).bind NativeOp.awaitCellOf with
         | some cell => Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
         | none => badShape
       | .program => frontier p) := by
  simp [compileEff, hf]; rfl

theorem compileEff_gen (ss : Stmts NativeOp) (hf : p.fuel = k + 1) :
    compileEff (.gen ss) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

theorem compileEff_uninterruptible (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.uninterruptible b) p = Prim.withFiber (EffThunk.act p) := by
  simp [compileEff, hf]

theorem compileEff_interruptible (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.interruptible b) p = Prim.withFiber (EffThunk.act p) := by
  simp [compileEff, hf]

theorem compileEff_whileLoop (initial test step : Term) (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.whileLoop initial test step b) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

theorem compileEff_yieldNow (priority : Nat) (hf : p.fuel = k + 1) :
    compileEff (.yieldNow priority) p = Prim.yieldNowWith priority := by
  simp [compileEff, hf]

theorem compileEff_callback (register : NativeOp) (r : Term) (hf : p.fuel = k + 1) :
    compileEff (.callback register r) p =
      (match (NativeOp.row register).kind with
       | .async =>
         match (evalTerm p.env r).bind NativeOp.awaitCellOf with
         | some cell => Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
         | none => badShape
       | _ => badShape) := by
  simp [compileEff, hf]; rfl

theorem compileEff_awaitFiber (fiber : Term) (mode : Supervision.ObserverMode) (hf : p.fuel = k + 1) :
    compileEff (.awaitFiber fiber mode) p =
      (match evalTerm p.env fiber with
       | some (Val.fiber id) => Prim.suspend (EffThunk.park (ParkKind.join id mode))
       | _ => badShape) := by
  simp [compileEff, hf]; rfl

theorem compileEff_withFiber (a : ActionTerm NativeOp) (hf : p.fuel = k + 1) :
    compileEff (.withFiber a) p = Prim.withFiber (EffThunk.act p) := by
  simp [compileEff, hf]

theorem compileEff_scoped (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.scoped b) p =
      Prim.onSuccess (Prim.sync (EffThunk.op (SyncOp.scopeMake FinalizerStrategy.sequential)))
        (EffName.scopeOpen p) := by
  simp [compileEff, hf]

theorem compileEff_acquireRelease (a r : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.acquireRelease a r) p = frontier p := by
  simp [compileEff, hf]

theorem compileEff_choose (site : Nat) (l r : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.choose site l r) p =
      (match p.tape with
       | true :: rest => compileEff l { p with path := p.path ++ [0], tape := rest }
       | false :: rest => compileEff r { p with path := p.path ++ [1], tape := rest }
       | [] => frontier p) := by
  simp [compileEff, hf]
  rfl

end compileArms

theorem compileEff_keys : ∀ (e : NativeEff) (p : Point), nativeKeys (compileEff e p) ⊆ p.keys
  | .succeed v, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_succeed v hf]
      split
      · next val hval => exact evalTerm_keys v p.env val hval
      · exact List.nil_subset _
  | .fail e, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_fail e hf]; split <;> exact List.nil_subset _
  | .failCause c, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_failCause c hf]; split <;> exact List.nil_subset _
  | .yieldError e, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_yieldError e hf]; split <;> exact List.nil_subset _
  | .sync t, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_sync t hf]; exact List.Subset.refl _
  | .suspend b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_suspend b hf]; exact List.Subset.refl _
  | .perform op r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_perform op r hf]
      split
      · split
        · next val hval =>
          split
          · next operation hop =>
            exact List.Subset.trans (syncOpOf_keys op val operation hop) (evalTerm_keys r p.env val hval)
          · exact List.nil_subset _
        · exact List.nil_subset _
      · split
        · next cell hcell =>
          obtain ⟨val, hval, hc⟩ := Option.bind_eq_some_iff.mp hcell
          have hmem := awaitCellOf_keys val cell hc
          have hval' := evalTerm_keys r p.env val hval
          have hcellKeys : [Handle.promise cell] ⊆ p.keys := by
            intro key hkey
            obtain rfl := List.mem_singleton.mp hkey
            exact hval' hmem
          sub_tac using hcellKeys
        · exact List.nil_subset _
      · exact frontier_keys p
  | .bind a b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_bind a b hf]
      sub_tac using (compileEff_keys a (p.child 0))
  | .gen ss, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_gen ss hf]; exact frontier_keys p
  | .catchCause b h, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_catchCause b h hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .matchCause b v c, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_matchCause b v c hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .onExit b f, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_onExit b f hf]
      sub_tac using (compileEff_keys b (p.child 0))
  | .exit b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rcases hx : (compileEff b (p.child 0)).asExit? with _ | ex
      · rw [compileEff_exit_frame b hf hx]
        exact compileEff_keys b (p.child 0)
      · -- the folded exit carries the body's own handles
        rw [compileEff_exit_fold b hf hx]
        have hb := compileEff_keys b (p.child 0)
        rw [Prim.asExit?_eq_some _ _ hx, ← exitKeys_eq_nativeKeys_ofExit] at hb
        show (reifyExitVal ex).keys ⊆ p.keys
        rw [Machine.reifyExitVal_keys]
        exact hb
  | .uninterruptible b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_uninterruptible b hf]; exact List.Subset.refl _
  | .interruptible b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_interruptible b hf]; exact List.Subset.refl _
  | .branch t a b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_branch t a b hf]; exact List.Subset.refl _
  | .whileLoop initial test step b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_whileLoop initial test step b hf]; exact frontier_keys p
  | .yieldNow priority, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_yieldNow priority hf]; exact List.nil_subset _
  | .callback register r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_callback register r hf]
      split
      · split
        · next cell hcell =>
          obtain ⟨val, hval, hc⟩ := Option.bind_eq_some_iff.mp hcell
          have hmem := awaitCellOf_keys val cell hc
          have hval' := evalTerm_keys r p.env val hval
          have hcellKeys : [Handle.promise cell] ⊆ p.keys := by
            intro key hkey
            obtain rfl := List.mem_singleton.mp hkey
            exact hval' hmem
          sub_tac using hcellKeys
        · exact List.nil_subset _
      · exact List.nil_subset _
  | .awaitFiber fiber mode, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_awaitFiber fiber mode hf]
      split
      · next id hid => exact evalTerm_keys fiber p.env (Val.fiber id) hid
      · exact List.nil_subset _
  | .withFiber a, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_withFiber a hf]; exact List.Subset.refl _
  | .scoped b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_scoped b hf]; sub_tac
  | .acquireRelease a r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_acquireRelease a r hf]; exact frontier_keys p
  | .choose site l r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_choose site l r hf]
      split
      · next rest _ => exact compileEff_keys l { p with path := p.path ++ [0], tape := rest }
      · next rest _ => exact compileEff_keys r { p with path := p.path ++ [1], tape := rest }
      · exact frontier_keys p

theorem resolve_keys (root : NativeEff) (p : Point) : nativeKeys (resolve root p) ⊆ p.keys := by
  unfold resolve
  split
  · exact compileEff_keys _ _
  · exact List.nil_subset _

theorem entrants_keys (root : NativeEff) : ∀ (es : Effs NativeOp) (q : Point),
    (actionAt.entrants es q).flatMap nativeKeys ⊆ q.keys
  | .nil, _ => List.nil_subset _
  | .cons h t, q => by
    simp only [actionAt.entrants, List.flatMap_cons]
    exact List.append_subset.mpr ⟨compileEff_keys h (q.child 0), entrants_keys root t (q.child 1)⟩

/-! ## The generator walker keeps to its environment -/

theorem blockExit_env (root : NativeEff) (p : Point) (pc : List Nat) (env : List Val) (pc' : List Nat)
    (env' : List Val) (h : blockExit root p pc env = some (pc', env')) : env' ⊆ env := by
  unfold blockExit at h
  repeat' (first | dsimp only at h | split at h)
  all_goals first
    | (cases h <;> exact List.take_subset _ _)
    | (cases h <;> exact List.Subset.refl _)

theorem loopExit_env (root : NativeEff) : ∀ (depth : Nat) (p : Point) (pc : List Nat) (env : List Val)
    (pc' : List Nat) (env' : List Val), loopExit root depth p pc env = some (pc', env') → env' ⊆ env
  | 0, _, _, _, _, _, h => by cases h
  | depth + 1, p, pc, env, pc', env', h => by
    unfold loopExit at h
    repeat' (first | dsimp only at h | split at h)
    all_goals first
      | (cases h <;> exact List.take_subset _ _)
      | (cases h <;> exact List.Subset.refl _)
      | exact List.Subset.trans (loopExit_env root depth _ _ _ _ _ h) (List.take_subset _ _)
      | exact loopExit_env root depth _ _ _ _ _ h

/-- What a generator step may name, given a bound `E` on the environment's handles. -/
def StepKeys (E : List Handle) : IterStep EffName EffThunk Val Err Defect FiberId Ann → Prop
  | IterStep.done r => r.keys ⊆ E
  | IterStep.resume next n' => nativeKeys next ++ EffName.keys n' ⊆ E
  | IterStep.halt _ => True

mutual
theorem runStmts_keys (root : NativeEff) (p : Point) (E : List Handle) :
    ∀ (fuel : Nat) (pc : List Nat) (env folded : List Val), env.flatMap Val.keys ⊆ E →
      StepKeys E (runStmts root p fuel pc env folded).2
  | 0, pc, env, folded, henv => by
    simp only [runStmts, StepKeys]
    sub_tac using henv
  | fuel + 1, pc, env, folded, henv => by
    simp only [runStmts]
    split
    · split
      · simp only [StepKeys]; exact List.nil_subset _
      · next pc' env' hexit =>
        exact runStmts_keys root p E fuel pc' env' folded
          (List.Subset.trans (flatMap_subset_of_subset (blockExit_env root p pc env pc' env' hexit)) henv)
    · next s _ _ =>
      split
      · exact yieldOf_keys root p E fuel _ true pc env folded henv
      · exact yieldOf_keys root p E fuel _ false pc env folded henv
      ·
        split
        · next value hvalue =>
          simp only [StepKeys]
          exact List.Subset.trans (evalTerm_keys _ env value hvalue) henv
        · simp only [StepKeys]
      · split
        · exact runStmts_keys root p E fuel _ env folded henv
        · exact runStmts_keys root p E fuel _ env folded henv
        · simp only [StepKeys]
      · exact runStmts_keys root p E fuel _ env folded henv
      · split
        · next pc' env' hexit =>
          exact runStmts_keys root p E fuel pc' env' folded
            (List.Subset.trans (flatMap_subset_of_subset (loopExit_env root _ p pc env pc' env' hexit)) henv)
        · simp only [StepKeys]
    · simp only [StepKeys]
termination_by fuel _ _ _ _ => (fuel, 0)

theorem yieldOf_keys (root : NativeEff) (p : Point) (E : List Handle) (fuel : Nat) (e : NativeEff) (bind : Bool)
    (pc : List Nat) (env folded : List Val) (henv : env.flatMap Val.keys ⊆ E) :
    StepKeys E (runStmts.yieldOf root p e bind fuel pc env folded).2 := by
  simp only [runStmts.yieldOf]
  have hcode := compileEff_keys e { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 }
  split
  · next value hvalue =>
    rw [hvalue] at hcode
    refine runStmts_keys root p E fuel _ _ _ ?_
    cases bind
    · change env.flatMap Val.keys ⊆ E
      exact henv
    · change (env ++ [value]).flatMap Val.keys ⊆ E
      simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
      exact List.append_subset.mpr ⟨henv, List.Subset.trans hcode henv⟩
  · simp only [StepKeys]
  ·
    simp only [StepKeys]
    exact List.append_subset.mpr ⟨List.Subset.trans hcode henv, henv⟩
termination_by (fuel, 1)
end

/-! ## A fiber action names only what its point evaluates -/

theorem evalTerm_fiber_mem (t : Term) (env : List Val) (id : FiberId) (h : evalTerm env t = some (Val.fiber id)) :
    Handle.fiber id ∈ env.flatMap Val.keys :=
  evalTerm_keys t env _ h (List.mem_singleton.mpr rfl)

theorem evalTerm_scope_mem (t : Term) (env : List Val) (s : Nat) (h : evalTerm env t = some (Val.scopeHandle s)) :
    Handle.scope s ∈ env.flatMap Val.keys :=
  evalTerm_keys t env _ h (List.mem_singleton.mpr rfl)

/-- The fibers a `withFiber` term's value names (`actionAt`'s `handles`): a snapshot or a tuple of
fiber handles. -/
theorem handlesOf_keys (v : Val) (ids : List FiberId)
    (hh : (match v with
           | Val.fibers ids => some ids
           | v => (Val.tuple? v).bind fun vs => vs.mapM fun
             | Val.fiber id => some id
             | _ => none) = some ids) :
    ids.map Handle.fiber ⊆ v.keys := by
  have hg : ∀ (w : Val) (id : FiberId),
      (fun x => match x with | Val.fiber id => some id | _ => none) w = some id → Handle.fiber id ∈ w.keys := by
    intro w id hw
    cases w <;> cases hw <;> exact List.mem_singleton.mpr rfl
  cases v
  case fibers ids' =>
    simp only [Option.some.injEq] at hh
    subst hh
    exact List.Subset.refl _
  all_goals
    simp only [] at hh
    obtain ⟨vs, hvs, hm⟩ := Option.bind_eq_some_iff.mp hh
    exact List.Subset.trans (mapM_fiber_keys _ hg vs ids hm) (tuple?_keys _ vs hvs)

theorem actionAt_keys (root : NativeEff) (p : Point) (a : NAction) (h : actionAt root p = some a) :
    a.keys EffName.keys EffThunk.keys ⊆ p.keys := by
  unfold actionAt at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    exact resolve_keys root (p.child 0)
  · simp only [Option.some.injEq] at h
    subst h
    exact resolve_keys root (p.child 0)
  · rename_i a' _
    simp only [Option.some.injEq] at h
    cases a' with
    | fork prog options =>
      simp only [] at h
      subst h
      exact resolve_keys root _
    | forkIn prog options scope =>
      simp only [] at h
      split at h
      · rename_i s hs
        subst h
        have hs' := evalTerm_scope_mem scope p.env s hs
        sub_tac using (resolve_keys root _)
      · subst h; exact List.nil_subset _
    | forkScoped prog options =>
      simp only [] at h
      subst h
      exact resolve_keys root _
    | runIn target scope =>
      simp only [] at h
      split at h
      · rename_i id s hid hs
        subst h
        have h1 := evalTerm_fiber_mem target p.env id hid
        have h2 := evalTerm_scope_mem scope p.env s hs
        sub_tac
      · subst h; exact List.nil_subset _
    | interrupt target =>
      simp only [] at h
      split at h
      · rename_i id hid
        subst h
        have h1 := evalTerm_fiber_mem target p.env id hid
        sub_tac
      · subst h; exact List.nil_subset _
    | interruptScoped target =>
      simp only [] at h
      split at h
      · rename_i id hid
        subst h
        have h1 := evalTerm_fiber_mem target p.env id hid
        sub_tac
      · subst h; exact List.nil_subset _
    | interruptAll targets interruptor =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        have hids' : ids.map Handle.fiber ⊆ p.keys :=
          List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_keys targets p.env v hv)
        split at h
        · subst h
          sub_tac using hids'
        · rename_i who _
          split at h
          · rename_i id hid
            subst h
            have h1 := evalTerm_fiber_mem who p.env id hid
            sub_tac using hids'
          · subst h; exact List.nil_subset _
      · subst h; exact List.nil_subset _
    | awaitAll targets =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_keys targets p.env v hv)
      · subst h; exact List.nil_subset _
    | awaitAllFailFast targets =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_keys targets p.env v hv)
      · subst h; exact List.nil_subset _
    | snapshotChildren =>
      simp only [] at h
      subst h
      exact List.nil_subset _
    | awaitNewChildren snapshot =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_keys snapshot p.env v hv)
      · subst h; exact List.nil_subset _
    | raceAll es =>
      simp only [] at h
      subst h
      exact entrants_keys root es _
    | setContext context =>
      simp only [] at h
      split at h
      · rename_i ctx hctx
        subst h
        exact evalTerm_keys context p.env (Val.context ctx) hctx
      · subst h; exact List.nil_subset _
    | getContext =>
      simp only [] at h
      subst h
      exact List.nil_subset _
    | getId =>
      simp only [] at h
      subst h
      exact List.nil_subset _
    | closeScope scope exit =>
      simp only [] at h
      split at h
      · rename_i s e hs hexit
        subst h
        have h1 := evalTerm_scope_mem scope p.env s hs
        obtain ⟨v, hv, hev⟩ := Option.bind_eq_some_iff.mp hexit
        have h2 : exitKeys e ⊆ p.keys := List.Subset.trans (exitOfVal_keys v e hev) (evalTerm_keys exit p.env v hv)
        sub_tac using h2
      · subst h; exact List.nil_subset _
  · cases h

/-! ## The hooks of `interpOf` are key-bounded -/

theorem contAOf_native_keys (root : NativeEff) (n : EffName) (v : Val) :
    nativeKeys (Program.contAOf root n v) ⊆ n.keys ++ v.keys := by
  cases n with
  | cont p => simp only [Program.contAOf]; sub_tac using (resolve_keys root (p.childWith 1 v))
  | onValue p => simp only [Program.contAOf]; sub_tac using (resolve_keys root (p.childWith 1 v))
  | restore exit => simp only [Program.contAOf, primKeys_ofExit]; sub_tac
  | merge exit => simp only [Program.contAOf, primKeys_ofExit]; sub_tac
  | reFail cause => simp only [Program.contAOf]; exact List.nil_subset _
  | scopeOpen p =>
    cases v <;> simp only [Program.contAOf] <;> sub_tac
  | scopeProvide p s =>
    cases v <;> simp only [Program.contAOf] <;>
      sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, Ctx.keys]
  | scopeBody p previous => simp only [Program.contAOf]; sub_tac using (resolve_keys root (p.child 0))
  | constant w => simp only [Program.contAOf]; sub_tac
  | abort => simp only [Program.contAOf]; exact List.nil_subset _
  | store name => simp only [Program.contAOf, nativeKeys, embed_keys]; exact Machine.contAOf_keys name v
  | caught p | onCause p | fin p | gen p pc bind | loop p | registerAwait cell | cancelAwait cell
  | withWaiter base waiter token | scopeClose scope | restoreCtx previous =>
    simp only [Program.contAOf]; sub_tac

theorem contEOf_native_keys (root : NativeEff) (n : EffName) (cause : CauseV) :
    nativeKeys (Program.contEOf root n cause) ⊆ n.keys := by
  cases n with
  | caught p => simp only [Program.contEOf]; sub_tac using (resolve_keys root (p.childWith 1 (Val.exitErr cause)))
  | onCause p => simp only [Program.contEOf]; sub_tac using (resolve_keys root (p.childWith 2 (Val.exitErr cause)))
  | restore exit =>
    simp only [Program.contEOf, primKeys_ofExit]
    sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | merge exit =>
    simp only [Program.contEOf, primKeys_ofExit]
    sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | constant w => simp only [Program.contEOf]; exact List.Subset.refl _
  | store name => simp only [Program.contEOf, nativeKeys, embed_keys]; exact Machine.contEOf_keys name cause
  | cont p | onValue p | fin p | gen p pc bind | loop p | registerAwait cell | cancelAwait cell
  | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s | scopeBody p previous
  | scopeClose scope | restoreCtx previous =>
    simp only [Program.contEOf]; exact List.nil_subset _

theorem cancelProgramOf_keys (n : EffName) : nativeKeys (cancelProgramOf n) ⊆ n.keys := by
  unfold cancelProgramOf
  split
  · sub_tac
  · simp only [nativeKeys, embed_keys]; exact Machine.cancelProgram_keys _
  · simp only [nativeKeys, embed_keys]; exact Machine.cancelProgram_keys _
  · exact List.nil_subset _

theorem syncValueAt_keys (root : NativeEff) (t : EffThunk) : (syncValueAt root t).keys ⊆ t.keys := by
  cases t with
  | pure p =>
    simp only [syncValueAt]
    split
    · rename_i term _
      cases hval : evalTerm p.env term with
      | none => exact List.nil_subset _
      | some val => exact evalTerm_keys term p.env val hval
    · exact List.nil_subset _
  | body _ | op _ | park _ | act _ | getCtx | setCtx _ | closeScope _ _ | store _ =>
    simp only [syncValueAt]; exact List.nil_subset _

theorem suspendBodyAt_keys (root : NativeEff) (t : EffThunk) : nativeKeys (suspendBodyAt root t) ⊆ t.keys := by
  cases t with
  | body p =>
    simp only [suspendBodyAt]
    split
    · exact frontier_keys p
    · split
      · split
        · exact resolve_keys root (p.child 0)
        · exact resolve_keys root (p.child 1)
        · exact List.nil_subset _
      · sub_tac
      · split
        · next cursor hcursor => sub_tac using (evalTerm_keys _ p.env cursor hcursor)
        · exact List.nil_subset _
      · exact compileEff_keys _ p
      · exact List.nil_subset _
  | store thunk =>
    cases thunk with
    | body program => simp only [suspendBodyAt, nativeKeys, embed_keys]; exact Machine.progOf_keys program
    | park _ | act _ | op _ => simp only [suspendBodyAt]; exact List.nil_subset _
  | pure _ | op _ | park _ | act _ | getCtx | setCtx _ | closeScope _ _ =>
    simp only [suspendBodyAt]; exact List.nil_subset _

theorem env_bind_keys (p : Point) (v : Val) (bind : Bool) :
    (if bind then p.env ++ [v] else p.env).flatMap Val.keys ⊆ p.keys ++ v.keys := by
  cases bind
  · exact List.subset_append_left _ _
  · show (p.env ++ [v]).flatMap Val.keys ⊆ p.env.flatMap Val.keys ++ v.keys
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.Subset.refl _

theorem interpOf_keyBounded (root : NativeEff) : KeyBounded EffName.keys EffThunk.keys (interpOf root) where
  contA n v := contAOf_native_keys root n v
  contE n c := contEOf_native_keys root n c
  syncValue t := syncValueAt_keys root t
  suspendBody t := suspendBodyAt_keys root t
  reifyExit e := by simp only [interpOf, Machine.reifyExitVal_keys]; exact List.Subset.refl _
  iterNext_done n v r h := by
    cases n with
    | gen p pc bind =>
      simp only [interpOf] at h
      have hs := runStmts_keys root p (p.keys ++ v.keys) p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (env_bind_keys p v bind)
      rw [h] at hs
      exact hs
    | cont p | caught p | onValue p | onCause p | fin p | restore e | merge e | loop p | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopeClose scope | restoreCtx previous | constant w | store name =>
      simp only [interpOf, IterStep.done.injEq] at h
      subst h
      exact List.subset_append_right _ _
  iterNext_resume n v next n' h := by
    cases n with
    | gen p pc bind =>
      simp only [interpOf] at h
      have hs := runStmts_keys root p (p.keys ++ v.keys) p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (env_bind_keys p v bind)
      rw [h] at hs
      exact hs
    | cont p | caught p | onValue p | onCause p | fin p | restore e | merge e | loop p | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopeClose scope | restoreCtx previous | constant w | store name =>
      simp only [interpOf] at h; cases h
  loopBody n c := by
    cases n with
    | loop p => simp only [interpOf]; sub_tac using (resolve_keys root (p.childWith 0 c))
    | cont p | caught p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c' | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopeClose scope | restoreCtx previous | constant w | store name =>
      simp only [interpOf]; sub_tac
  loopStep n c v := by
    cases n with
    | loop p =>
      simp only [interpOf]
      split
      · rename_i test step body _
        cases hval : evalTerm (p.env ++ [c, v]) step with
        | none => sub_tac
        | some val =>
          have hk := evalTerm_keys step (p.env ++ [c, v]) val hval
          simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil] at hk
          sub_tac using hk
      · sub_tac
    | cont p | caught p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c' | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopeClose scope | restoreCtx previous | constant w | store name =>
      simp only [interpOf]; sub_tac
  loopDone n := by simp only [interpOf]; exact List.nil_subset _
  cancelThenFail n c := by
    simp only [interpOf]
    sub_tac using (cancelProgramOf_keys n)
  parkOf code target mode h := by
    simp only [interpOf] at h
    split at h
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      mem_tac [EffThunk.keys, ParkKind.keys]
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      mem_tac [EffThunk.keys, Thunk.keys, ParkKind.keys]
    · cases h
  withFiberOf t a h := by
    cases t with
    | act p => simp only [interpOf] at h; exact actionAt_keys root p a h
    | getCtx => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.nil_subset _
    | setCtx ctx => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    | closeScope scope exit => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    | store thunk =>
      cases thunk with
      | act action =>
        simp only [interpOf, Option.some.injEq] at h
        subst h
        rw [embedAction_keys]
        exact Machine.actionOf_keys action
      | park _ | op _ | body _ => simp only [interpOf] at h; cases h
    | pure _ | body _ | op _ | park _ => simp only [interpOf] at h; cases h
  syncState t s s' v ids h hok := by
    cases t with
    | op operation =>
      simp only [interpOf] at h
      exact ⟨syncOpStep_le operation s s' v h, syncOpStep_keys operation s s' v ids h hok⟩
    | store thunk =>
      cases thunk with
      | op operation =>
        simp only [interpOf] at h
        exact ⟨syncOpStep_le operation s s' v h, syncOpStep_keys operation s s' v ids h hok⟩
      | park _ | act _ | body _ => simp only [interpOf] at h; cases h
    | pure _ | body _ | park _ | act _ | getCtx | setCtx _ | closeScope _ _ => simp only [interpOf] at h; cases h
  registerAsync n fiber token s ids hok := by
    have reg : ∀ cell, Ok ⟨ids, s⟩ ([Handle.promise cell] ++ s.keys) →
        s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } ∧
          Ok ⟨ids, { s with deferreds := (s.deferreds.register cell fiber token).1 }⟩
            ({ s with deferreds := (s.deferreds.register cell fiber token).1 }.keys ++
              (((s.deferreds.register cell fiber token).2.map embed).map nativeKeys).getD []) := by
      intro cell hok
      obtain ⟨hkeys, himm, hlen⟩ := DeferredStore.register_keys s.deferreds cell fiber token
      have hle : s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } :=
        ⟨Nat.le_refl _, hlen, fun _ hh => hh, Nat.le_refl _⟩
      refine ⟨hle, ?_⟩
      have hok' := Ok_mono (World.le_of_state hle) hok
      refine Ok_of_subset ?_ hok'
      refine List.append_subset.mpr ⟨?_, ?_⟩
      · sub_tac using hkeys
      · cases himm' : (s.deferreds.register cell fiber token).2 with
        | none => exact List.nil_subset _
        | some prog =>
          show nativeKeys (embed prog) ⊆ _
          simp only [nativeKeys, embed_keys]
          exact List.Subset.trans (himm prog himm') (by sub_tac)
    cases n with
    | registerAwait cell => simp only [interpOf]; exact reg cell hok
    | store name =>
      cases name with
      | registerAwait cell => simp only [interpOf]; exact reg cell hok
      | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
      | snapshotThen _ | cancelAwait _ | externalRegister _ | abortController | cancelPark | cancelRace _
      | withWaiter _ _ _ | reFail _ | finalizerName _ | closeSeq _ _ _ | closePar _ _ _ _ | mergeAwaitedExits =>
        simp only [interpOf]
        exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
    | cont p | caught p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | loop p
    | cancelAwait cell | withWaiter base waiter token' | abort | reFail c | scopeOpen p | scopeProvide p sc
    | scopeBody p previous | scopeClose scope | restoreCtx previous | constant w =>
      simp only [interpOf]
      exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
  answerCode c := by simp only [interpOf]; rw [embed_keys]; exact Machine.completionPrim_keys c
  dueResumes s ids hok := by
    simp only [interpOf]
    obtain ⟨h1, h2⟩ := DeferredStore.drainDue_keys s.deferreds
    have hle : s.le { s with deferreds := (s.deferreds.drainDue).2 } := by
      refine ⟨Nat.le_refl _, ?_, fun _ hh => hh, Nat.le_refl _⟩
      simp only [DeferredStore.drainDue]
      exact Nat.le_refl _
    refine ⟨hle, ?_⟩
    have hok' := Ok_mono (World.le_of_state hle) hok
    refine Ok_of_subset ?_ hok'
    have h2' : ((s.deferreds.drainDue.1.map fun d => (d.1, d.2.1, embed d.2.2)).flatMap fun r => nativeKeys r.2.2) ⊆
        s.deferreds.keys := by
      rw [List.flatMap_map]
      simp only [embed_keys]
      exact h2
    sub_tac using h1, h2'
  cancelName base fiber token := by simp only [interpOf]; exact List.Subset.refl _
  abortName := rfl
  parkCancelName := rfl
  raceCancelName race := rfl
  raceSettle live exit := by simp only [interpOf]; rw [embed_keys]; exact Machine.raceSettleProgram_keys live exit
  finalizerProgram n e p h := by
    simp only [interpOf] at h
    split at h
    · rename_i q
      simp only [Option.some.injEq] at h
      subst h
      refine List.Subset.trans (resolve_keys root _) ?_
      rw [Point.childWith_keys, Machine.reifyExitVal_keys]
      exact List.Subset.refl _
    · rename_i scope
      simp only [Option.some.injEq] at h
      subst h
      sub_tac
    · rename_i previous
      simp only [Option.some.injEq] at h
      subst h
      sub_tac
    · rename_i fin
      simp only [Option.some.injEq] at h
      subst h
      rw [embed_keys]
      exact Machine.finProgram_keys fin e
    · cases h
  restoreName e := List.Subset.refl _
  mergeName e := List.Subset.refl _
  scopeStatus scope s h := stores_keyBounded.scopeStatus scope s h
  scopeLinkFiber mode scope key fiber s s' ids h hok := stores_keyBounded.scopeLinkFiber mode scope key fiber s s' ids h hok
  dropFinalizer scope key s s' ids h hok := stores_keyBounded.dropFinalizer scope key s s' ids h hok
  closeScope scope exit flag closer s s' p ids h hok := by
    simp only [interpOf] at h
    obtain ⟨r, hr, hrp⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hrp
    obtain ⟨rfl, rfl⟩ := hrp
    obtain ⟨hle, hok'⟩ := stores_keyBounded.closeScope scope exit flag closer s r.1 r.2 ids hr hok
    refine ⟨hle, ?_⟩
    show Ok _ (nativeKeys (embed r.2) ++ _)
    simp only [nativeKeys, embed_keys]
    exact hok'
  emptyContext := rfl
  contextValue ctx := List.Subset.refl _
  exitValue e mode := by
    cases mode with
    | awaitValue => simp only [interpOf, primKeys, Machine.reifyExitVal_keys]; exact List.Subset.refl _
    | joinEffect => simp only [interpOf, primKeys_ofExit]; exact List.Subset.refl _
  fiberValue id := List.Subset.refl _
  fibersValue ids := List.Subset.refl _
  exitsValue exits := by simp only [interpOf, Machine.exitsVal_keys]; exact List.Subset.refl _
  voidValue := rfl

/-! ## The public statement -/

/-- Every collected handle names something minted: a fiber of the machine, or a cell,
Deferred or scope of its stores. Decidable. -/
def Minted (m : Api.Machine) : Prop := MintedAt EffName.keys EffThunk.keys m

instance (m : Api.Machine) : Decidable (Minted m) :=
  inferInstanceAs (Decidable (MintedAt EffName.keys EffThunk.keys m))

/-- The valid-input premise (ruling on `E4-HANDLE-CE-001`): along the replay of `tape` from the
loaded program, every `answerAsync` names handles that exist in the machine it answers.
Decidable; replay admission is unchanged. -/
def AnswersValid (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool := []) :
    Prop :=
  AnswersValidAt (interpOf program) fuel tape (Api.load program fuel choices)

instance (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool) :
    Decidable (AnswersValid program fuel tape choices) :=
  inferInstanceAs (Decidable (AnswersValidAt (interpOf program) fuel tape (Api.load program fuel choices)))

theorem Api.replay_machine (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool) :
    (Api.replay program fuel tape choices).machine =
      (replayEval (interpOf program) fuel tape (Api.load program fuel choices)).machine := by
  unfold Api.replay
  cases replayEval (interpOf program) fuel tape (Api.load program fuel choices) <;> rfl

/-- A loaded program holds no handle: a literal is a unit, a number or a boolean, and the root
point has nothing in scope. -/
theorem load_minted (program : Api.Program) (fuel : Nat) (choices : List Bool := []) :
    Minted (Api.load program fuel choices) := by
  have hcode : nativeKeys (compile program fuel choices) ⊆ [] := compileEff_keys program (rootPoint fuel choices)
  have hmake := make_keys_subset (nk := EffName.keys) (sk := EffThunk.keys) Api.root (compile program fuel choices)
    true (stores.budgetOf emptyCtx) emptyCtx
  have hfiber : (RunFiber.make Api.root (compile program fuel choices) true (stores.budgetOf emptyCtx) emptyCtx :
      RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx).keys EffName.keys EffThunk.keys ⊆ [] :=
    List.Subset.trans hmake (List.append_subset.mpr ⟨hcode, List.Subset.refl _⟩)
  unfold Minted MintedAt MintedIn
  refine Ok_of_subset (b := []) ?_ (Ok_nil _)
  have hempty : Stores.empty.keys = [] := rfl
  simp only [Api.load, Api.compile, RunMachine.keys, RunMachine.empty, List.flatMap_cons,
    List.flatMap_nil, List.map_nil, List.append_nil, hempty]
  exact hfiber

/-- The handle invariant (C13, `handles_minted`): a minted machine replayed on a tape whose
external answers are valid stays minted. -/
theorem handles_minted (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool)
    (h : Minted (Api.load program fuel choices) ∧ AnswersValid program fuel tape choices) :
    Minted (Api.replay program fuel tape choices).machine := by
  rw [Api.replay_machine]
  exact (replayEval_minted EffName.keys EffThunk.keys (interpOf_keyBounded program) fuel tape _ h.2 h.1).2

end Effect4.Program
