import Effect4.Laws.Machine.Handles
import Effect4.Api
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.Agreement

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
the point's captured exits and environment (`compileEff_keys`, `resolve_keys`), the generator
walker keeps to those captured exits and its environment (`runStmts_keys`), a `withFiber` action names only what its point's terms
evaluate to (`actionAt_keys`), and the embedded stores' programs carry the stores' own keys
(`embed_keys`). The ruling in force is the valid-input premise: `AnswersValid` is a premise of
the theorem, and replay admission is unchanged (`E4-HANDLE-CE-001`).

Excluded, as in the machine module: the cause's interruptor, the race's duplicate winner and
unused bookkeeping, and a Deferred's waiter targets. The exit a scope closed with is
collected since V1 (2026-09-07): `scopeAdd` on a closed scope answers it.
The race's live entrants and accepted exit are collected: both flow into `raceSettle`.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine
open Agreement

/-! ## The native alphabet's handles -/

/-- The handles a point holds: captured exit values, then values in scope.
The captured fiber IDs are lookup keys, not dereferenced handles. -/
def Point.keys (p : Point) : List Handle :=
  p.completed.flatMap (fun entry => exitKeys entry.2) ++ p.env.flatMap Val.keys

theorem Point.env_keys_subset (p : Point) : p.env.flatMap Val.keys ⊆ p.keys :=
  List.subset_append_right _ _

/-- The eager join/await answer uses only the captured exit's value handles.
Both observer modes follow the same construction lookup (`internal/effect.ts:767-769,814-816`). -/
theorem Point.awaitExit_keys (p : Point) (target : FiberId) (mode : Supervision.ObserverMode)
    (exit : ExitV) (h : p.awaitExit target mode = some exit) : exitKeys exit ⊆ p.keys := by
  unfold Point.awaitExit at h
  obtain ⟨entry, hfind, hexit⟩ := Option.map_eq_some_iff.mp h
  have hentry := List.mem_of_find?_eq_some hfind
  have hkeys : exitKeys entry.2 ⊆ p.keys := by
    intro key hkey
    exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨entry, hentry, hkey⟩)
  cases mode <;> simp only at hexit <;> subst exit
  · simpa only [exitKeys, Machine.reifyExitVal_keys] using hkeys
  · exact hkeys

/-- A context update's handles: the map it sets or merges, or the value it adds. -/
def _root_.Effect4.Machine.Env.ContextUpdate.keys : Env.ContextUpdate → List Handle
  | .setTo context => Env.Context.handleKeys context
  | .provide that => Env.Context.handleKeys that
  | .provideService _ value => Val.keys value

/-- The handles a region carries: its point, and the memo map and scope of a build. -/
def Region.keys : Region → List Handle
  | .program q => q.keys
  | .build q m scope => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .buildAdding q m scope => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .construct q _ => q.keys

/-- The handles a name of the compiled alphabet carries. -/
def EffName.keys : EffName → List Handle
  | .external _ request => request.keys
  | .cont p => p.keys
  | .caught p | .caughtError p => p.keys
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
  | .scopedExit previous scope => Handle.scope scope :: previous.keys
  | .scopeClose scope => [Handle.scope scope]
  | .restoreCtx previous => previous.keys
  | .forkScopedIn p => p.keys
  | .constant v => v.keys
  | .store name => name.keys
  -- `acquireRelease`'s names (V1): the point, the context read, the scope handle read, the
  -- acquired value and the capture; the release's point, context, exit and previous context
  | .acquireCtx p => p.keys
  | .acquireIn p ctx => p.keys ++ ctx.keys
  | .acquired p ctx scope => Handle.scope scope :: p.keys ++ ctx.keys
  | .afterScopeAdd a finalizer => a.keys ++ finalizer.keys
  | .releaseUnder p ctx exit => p.keys ++ ctx.keys ++ exitKeys exit
  | .releaseBody p exit previous => p.keys ++ exitKeys exit ++ previous.keys
  -- the join's names: the point, the memo map, the scopes, the fibers forked, the contexts
  | .provideLayerWith p => p.keys
  | .provideLayerBody p => p.keys
  | .updateThen update body => update.keys ++ body.keys
  | .bodyThen body previous => body.keys ++ previous.keys
  | .buildWithScopeFromContext q scope => Handle.scope scope :: q.keys
  | .withMemoMapThen q scope => Handle.scope scope :: q.keys
  | .addCurrentMemoMap m => [Handle.memoMap m.index]
  | .fromBuildThen q m => Handle.memoMap m.index :: q.keys
  | .memoize q m scope => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .awaitPromise cell => [Handle.promise cell]
  | .buildIntoLayerScope q m scope => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .thenBuildInto q m layerScope => Handle.scope layerScope :: Handle.memoMap m.index :: q.keys
  | .freshThen q scope => Handle.scope scope :: q.keys
  | .provideThen q m scope _ => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .combineWith _ that => Env.Context.handleKeys that
  | .mergeChildren q m => Handle.memoMap m.index :: q.keys
  | .mergeForkOne q _ m parent forked =>
    Handle.scope parent :: Handle.memoMap m.index :: forked.map Handle.fiber ++ q.keys
  | .mergeForkNext q _ m parent forked =>
    Handle.scope parent :: Handle.memoMap m.index :: forked.map Handle.fiber ++ q.keys
  | .mergeAllChildren q m => Handle.memoMap m.index :: q.keys
  | .mergeAllForkOne q _ m parent forked =>
    Handle.scope parent :: Handle.memoMap m.index :: forked.map Handle.fiber ++ q.keys
  | .mergeAllForkNext q _ m parent forked =>
    Handle.scope parent :: Handle.memoMap m.index :: forked.map Handle.fiber ++ q.keys
  | .mergeContexts => []
  | .serviceLookup _ => []
  | .bindService _ => []
  | .orDie => []

/-- The handles a thunk of the compiled alphabet carries. -/
def EffThunk.keys : EffThunk → List Handle
  | .pure p => p.keys
  | .body p => p.keys
  | .op operation => operation.keys
  | .park kind => kind.keys
  | .act p => p.keys
  | .forkInAt p scope => Handle.scope scope :: p.keys
  | .getCtx => []
  | .setCtx context => context.keys
  | .closeScope scope exit => Handle.scope scope :: exitKeys exit
  | .store thunk => thunk.keys
  | .acquireMasked p ctx => p.keys ++ ctx.keys
  | .releaseMasked p previous => p.keys ++ previous.keys
  | .memoLookup q m scope => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .forkLayer q m scope => Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .awaitAllFailFast targets => targets.map Handle.fiber

/-- The handles of compiled code. -/
abbrev nativeKeys : NCode → List Handle := primKeys EffName.keys EffThunk.keys

/-- The membership search also unfolds the native alphabet, the stores' alphabet and the
points' children. -/
macro_rules
  | `(tactic| sub_tac) => `(tactic| sub_tac norm [Point.keys, Point.child, Point.childWith, Point.childWith2,
      EffName.keys, EffThunk.keys, programKeys, Name.keys, Thunk.keys, ActionName.keys, FinName.keys,
      ProgName.keys, SyncOp.keys, Completion.keys, ParkKind.keys,
      Region.keys, Env.ContextUpdate.keys, updateContextAt, scopeAddAt, List.map_append, List.map_cons,
      List.map_nil])
  | `(tactic| sub_tac using $hs:term,*) => `(tactic| sub_tac using $hs,* norm [Point.keys, Point.child,
      Point.childWith, Point.childWith2, EffName.keys, EffThunk.keys, programKeys, Name.keys, Thunk.keys,
      ActionName.keys, FinName.keys, ProgName.keys, SyncOp.keys, Completion.keys, ParkKind.keys,
      Region.keys, Env.ContextUpdate.keys, updateContextAt, scopeAddAt, List.map_append, List.map_cons,
      List.map_nil])

theorem Point.child_keys (p : Point) (i : Nat) : (p.child i).keys = p.keys := rfl

/-- Walking a spine keeps the handles: only the path and the fuel move (`Point.child`). -/
theorem Point.spine_keys (q : Point) :
    ∀ n, ((List.range n).foldl (fun acc _ => acc.child 1) q).keys = q.keys
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, Point.child_keys]
    exact Point.spine_keys q n

/-- The point of a `mergeAll`'s `i`-th layer carries the merge point's handles. -/
theorem Point.spineChild_keys (q : Point) (i : Nat) : (q.spineChild i).keys = q.keys := by
  unfold Point.spineChild
  rw [Point.child_keys, Point.spine_keys, Point.child_keys]

/-- Forking the build of a `mergeAll`'s `i`-th layer carries the handles the merge point's
build would: the spine moves only the path and the fuel. -/
theorem forkLayer_keys_spine (q : Point) (i : Nat) (m : MemoMapId) (child : Nat) (n : EffName) :
    nativeKeys (Prim.onSuccess (Prim.withFiber (EffThunk.forkLayer (q.spineChild i) m child)) n) =
      nativeKeys (Prim.onSuccess (Prim.withFiber (EffThunk.forkLayer q m child)) n) := by
  simp only [nativeKeys, primKeys, EffThunk.keys, Point.spineChild_keys]

theorem Point.childWith_keys (p : Point) (i : Nat) (v : Val) : (p.childWith i v).keys = p.keys ++ v.keys := by
  simp only [Point.keys, Point.childWith, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.append_assoc]

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
  | .onSuccessConst body next => by simp only [embed, primKeys, embed_keys body, embed_keys next]
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

/-- An embedded generator step ends exactly when the stores' step ends (§20). -/
theorem embedStep_done {s : IterStep Name Thunk Val Err Defect FiberId Ann Program} {r : Val}
    (h : embedStep s = IterStep.done r) : s = IterStep.done r := by
  cases s with
  | done v => simp only [embedStep, IterStep.done.injEq] at h; rw [h]
  | halt c => simp only [embedStep] at h; cases h
  | resume next n => simp only [embedStep] at h; cases h

/-- An embedded generator step yields exactly the stores' yielded code and name, embedded. -/
theorem embedStep_resume {s : IterStep Name Thunk Val Err Defect FiberId Ann Program} {next : NCode}
    {n' : EffName} (h : embedStep s = IterStep.resume next n') :
    ∃ next0 n0, s = IterStep.resume next0 n0 ∧ next = embed next0 ∧ n' = .store n0 := by
  cases s with
  | done v => simp only [embedStep] at h; cases h
  | halt c => simp only [embedStep] at h; cases h
  | resume next0 n0 =>
    simp only [embedStep, IterStep.resume.injEq] at h
    exact ⟨next0, n0, rfl, h.1.symm, h.2.symm⟩

/-! ## Terms evaluate inside their environment -/

theorem Lit.toVal_keys (l : Lit) (v : Val) (h : l.toVal = some v) : v.keys = [] := by
  cases l <;> simp only [Lit.toVal, Option.some.injEq] at h <;> (try cases h) <;> rfl

/-- Cause-tag queries construct only a Boolean, never a new handle. -/
theorem queryTag_keys (tag : ReasonTag) (input output : Val)
    (h : queryTag tag input = some output) : output.keys = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.map_eq_some_iff.mp h
  cases houtput
  rfl

/-- A cause-error query wraps only S2's closed, handle-free error image. -/
theorem queryError_keys (input output : Val) (h : queryError input = some output) :
    output.keys = [] := by
  obtain ⟨reasons, _, houtput⟩ := Option.bind_eq_some_iff.mp h
  cases hfound : (reasons.findSome? Reason.error?).bind valOfErr with
  | none =>
    simp only [hfound] at houtput
    cases houtput
    rfl
  | some value =>
    simp only [hfound] at houtput
    cases houtput
    change value.keys = []
    obtain ⟨error, _, hvalue⟩ := Option.bind_eq_some_iff.mp hfound
    exact valOfErr_keys error value hvalue

theorem nativeAtom_keys (atom : String) (vs : List Val) (v : Val) (h : nativeAtom atom vs = some v) :
    v.keys ⊆ vs.flatMap Val.keys := by
  unfold nativeAtom at h
  obtain ⟨named, _, h⟩ := Option.bind_eq_some_iff.mp h
  unfold NativeAtom.eval at h
  split at h <;> (try cases h) <;> (try (sub_tac norm [Val.tuple]; done))
  all_goals first
    | have free := queryTag_keys _ _ _ h
      rw [free]
      exact List.nil_subset _
    | have free := queryError_keys _ _ h
      rw [free]
      exact List.nil_subset _
    | -- strings returns exactly the argument list
      unfold stringsAtom at h
      split at h
      · cases h
        rw [Val.keys_list]
        exact List.Subset.refl _
      · cases h

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

theorem evalTerm_point_keys (t : Term) (p : Point) (v : Val) (h : evalTerm p.env t = some v) :
    v.keys ⊆ p.keys :=
  List.Subset.trans (evalTerm_keys t p.env v h) p.env_keys_subset

theorem exitOfVal_keys (v : Val) (e : ExitV) (h : exitOfVal v = some e) : exitKeys e ⊆ v.keys := by
  rw [exitImage.ofVal_exact h]
  cases e with
  | success x =>
    show x.keys ⊆ (Val.exitOk x).keys
    rw [Val.keys_exitOk]
    exact List.Subset.refl _
  | failure c => exact List.nil_subset _

theorem awaitCellOf_keys (v : Val) (cell : DeferredKey) (h : NativeOp.awaitCellOf v = some cell) :
    Handle.promise cell ∈ v.keys := by
  unfold NativeOp.awaitCellOf at h
  split at h
  · injection h with h
    subst h
    simp only [Val.keys, Handle.ofCode_promise, Option.toList, List.mem_singleton]
  · exact nomatch h

theorem syncOpOf_keys (op : NativeOp) (v : Val) (o : SyncOp) (h : NativeOp.syncOpOf op v = some o) :
    o.keys ⊆ v.keys := by
  unfold NativeOp.syncOpOf at h
  split at h <;> cases h <;> sub_tac

theorem tuple?_keys (v : Val) : ∀ vs, Val.tuple? v = some vs → vs.flatMap Val.keys ⊆ v.keys := by
  intro vs h
  rw [Val.tuple?_exact h, Val.tuple, Val.keys_list]
  exact List.Subset.refl _

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
      (match op with
       | .external _ => asyncRoute op r p
       | _ => match (NativeOp.row op).kind with
         | .sync =>
           match evalTerm p.env r with
           | some val =>
             match NativeOp.syncOpOf op val with
             | some operation => Prim.sync (EffThunk.op operation)
             | none => badShape
           | none => badShape
         | .async => asyncRoute op r p
         | .program => frontier p) := by
  cases op <;> unfold compileEff <;> rw [hf] <;> rfl

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
      (match register with
       | .external _ =>
         match evalTerm p.env r with
         | some v => Prim.async (EffName.external register v) false none
         | none => badShape
       | .sleep =>
         match (evalTerm p.env r).bind NativeOp.sleepMillisOf with
         | some 0 => Prim.yieldNowWith 0
         | some (n + 1) =>
           Prim.async (EffName.store (Name.registerSleep (n + 1))) true
             (some (EffName.store Name.cancelSleep))
         | none => badShape
       | _ =>
         match (NativeOp.row register).kind with
         | .async =>
           match (evalTerm p.env r).bind NativeOp.awaitCellOf with
           | some cell => Prim.async (EffName.registerAwait cell) true (some (EffName.cancelAwait cell))
           | none => badShape
         | _ => badShape) := by
  cases register <;> (simp [compileEff, hf]; try rfl)

theorem compileEff_awaitFiber (fiber : Term) (mode : Supervision.ObserverMode) (hf : p.fuel = k + 1) :
    compileEff (.awaitFiber fiber mode) p =
      (match evalTerm p.env fiber with
       | some (Val.fiber ⟨id⟩) =>
         match p.awaitExit ⟨id⟩ mode with
         | some exit => Prim.ofExit exit
         | none => Prim.suspend (EffThunk.park (ParkKind.join ⟨id⟩ mode))
       | _ => badShape) := by
  simp [compileEff, hf]; rfl

/-- Every action but `forkScoped` compiles to its `WithFiber` at the point. -/
theorem compileEff_withFiber (a : ActionTerm NativeOp) (hf : p.fuel = k + 1)
    (hnot : ∀ child options, a ≠ .forkScoped child options) :
    compileEff (.withFiber a) p = Prim.withFiber (EffThunk.act p) := by
  cases a <;> first
    | (simp [compileEff, hf]; done)
    | exact absurd rfl (hnot _ _)

/-- `forkScoped` is `flatMap(scope, scope => forkIn(self, scope, options))`
(`internal/effect.ts:5381-5406`, source-repairs §20): the counted `Service` read at the
action under the wrapper's `OnSuccess`, whose continuation is `forkIn` on the handle
(`contAOf_forkScopedIn`). census: fork.scoped -/
theorem compileEff_forkScoped (child : NativeEff) (options : Supervision.ForkOptions)
    (hf : p.fuel = k + 1) :
    compileEff (.withFiber (.forkScoped child options)) p =
      Prim.onSuccess (Prim.withFiber (EffThunk.act p)) (EffName.forkScopedIn p) := by
  simp [compileEff, hf]

/-- The wrapper's continuation on the handle the service read answered is `forkIn` on it
(§20); on anything else the shape is wrong. census: fork.scoped -/
theorem contAOf_forkScopedIn (root : NativeEff) (scope : Nat) :
    Program.contAOf root (EffName.forkScopedIn p) (Val.scopeHandle scope) =
      Prim.withFiber (EffThunk.forkInAt p scope) := rfl

/-- The `forkIn` half reads the child, the options and the point's fuel off the `forkScoped`
node, on the handle the read answered (§20). census: fork.scoped -/
theorem withFiberOf_forkInAt (root : NativeEff) (scope : Nat) :
    (interpOf root).withFiberOf (EffThunk.forkInAt p scope) = forkScopedAt root p scope := rfl

theorem compileEff_scoped (b : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.scoped b) p = Prim.withFiber (EffThunk.act p) := by
  simp [compileEff, hf]

/-- `acquireRelease` compiles to the context read, the rest named (`contAOf`).
census: scope.acquire-release -/
theorem compileEff_acquireRelease (a r : NativeEff) (hf : p.fuel = k + 1) :
    compileEff (.acquireRelease a r) p =
      Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.acquireCtx p) := by
  simp [compileEff, hf]

-- the join's three constructors (`Agreement.lean` states them too, in its own section)
theorem compileEff_provideLayer' (l : LayerTerm NativeOp) (i : Bool) (b : NativeEff)
    (hf : p.fuel = k + 1) :
    compileEff (.provideLayer l i b) p = Prim.suspend (EffThunk.body p) := by
  simp [compileEff, hf]

theorem compileEff_service' (key : ServiceKey) (hf : p.fuel = k + 1) :
    compileEff (.service key) p =
      Prim.onSuccess (Prim.withFiber EffThunk.getCtx) (EffName.serviceLookup key) := by
  simp [compileEff, hf]

theorem compileEff_provideService' (key : ServiceKey) (value : Term) (b : NativeEff)
    (hf : p.fuel = k + 1) :
    compileEff (.provideService key value b) p =
      (match evalTerm p.env value with
       | some v =>
         updateContextAt (Env.ContextUpdate.provideService key v) (Region.program (p.child 0))
       | none => badShape) := by
  simp [compileEff, hf]
  try rfl

/-- The capture registered at a point names the point's handles, the acquired value's and
the context's. -/
theorem Point.capture_keys (p : Point) (a : Val) (ctx : Ctx) :
    (FinName.foreign (p.capture a ctx)).keys ⊆ p.keys ++ a.keys ++ ctx.keys := by
  simp only [FinName.keys, Point.capture, Val.keysList_eq_flatMap, List.flatMap_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil]
  refine List.append_subset.mpr ⟨List.append_subset.mpr ⟨?_, ?_⟩, ?_⟩
  · exact List.Subset.trans p.env_keys_subset
      (List.Subset.trans (List.subset_append_left _ _) (List.subset_append_left _ _))
  · exact List.Subset.trans (List.subset_append_right _ _) (List.subset_append_left _ _)
  · exact List.subset_append_right _ _

/-- DI-61. The shared async dispatcher names only handles already captured at the point. -/
theorem asyncRoute_keys (register : NativeOp) (r : Term) (p : Point) :
    nativeKeys (asyncRoute register r p) ⊆ p.keys := by
  unfold asyncRoute
  cases register
  case external i =>
    cases hv : evalTerm p.env r with
    | none => exact List.nil_subset _
    | some value =>
      simp only [nativeKeys, primKeys, EffName.keys, Option.map_none, Option.getD_none, List.append_nil]
      exact evalTerm_point_keys r p value hv
  case sleep =>
    cases (evalTerm p.env r).bind NativeOp.sleepMillisOf with
    | none => exact List.nil_subset _
    | some n => cases n <;> exact List.nil_subset _
  all_goals first
    | exact List.nil_subset _
    | (rename_i s; cases s <;> exact List.nil_subset _)
    | (simp only [NativeOp.row]
       split
       all_goals first
         | exact List.nil_subset _
         | (next cell hcell =>
             obtain ⟨val, hval, hc⟩ := Option.bind_eq_some_iff.mp hcell
             have hmem := awaitCellOf_keys val cell hc
             have hval' := evalTerm_point_keys r p val hval
             have hcellKeys : [Handle.promise cell] ⊆ p.keys := by
               intro key hkey
               obtain rfl := List.mem_singleton.mp hkey
               exact hval' hmem
             sub_tac using hcellKeys))

/-- A capture's point names the capture's environment. -/
theorem Point.ofCapture_keys (c : Capture) : (Point.ofCapture c).keys ⊆ Val.keysList c.env := by
  simp only [Point.keys, Point.ofCapture, List.flatMap_nil, List.nil_append, Val.keysList_eq_flatMap]
  exact List.Subset.refl _

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
      · next val hval => exact evalTerm_point_keys v p val hval
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
      · exact asyncRoute_keys _ r p
      · split
        · split
          · next val hval =>
            split
            · next operation hop =>
              exact List.Subset.trans (syncOpOf_keys op val operation hop) (evalTerm_point_keys r p val hval)
            · exact List.nil_subset _
          · exact List.nil_subset _
        · exact asyncRoute_keys op r p
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
  | .catchIf test b h, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_catchIf test b h hf]
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
    · simp only [compileEff, hf]
      exact asyncRoute_keys register r p
  | .awaitFiber fiber mode, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_awaitFiber fiber mode hf]
      split
      · next id hid =>
        split
        · next exit hexit =>
          rw [← exitKeys_eq_nativeKeys_ofExit]
          exact p.awaitExit_keys ⟨id⟩ mode exit hexit
        · exact evalTerm_point_keys fiber p (Val.fiber ⟨id⟩) hid
      · exact List.nil_subset _
  | .withFiber a, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · cases a with
      | forkScoped child options =>
        rw [compileEff_forkScoped child options hf]
        sub_tac
      | _ =>
        rw [compileEff_withFiber _ hf (by intro _ _ h; cases h)]
        exact List.Subset.refl _
  | .scoped b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_scoped b hf]; sub_tac
  | .acquireRelease a r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_acquireRelease a r hf]; sub_tac
  | .choose site l r, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_choose site l r hf]
      split
      · next rest _ => exact compileEff_keys l { p with path := p.path ++ [0], tape := rest }
      · next rest _ => exact compileEff_keys r { p with path := p.path ++ [1], tape := rest }
      · exact frontier_keys p
  -- the join: a suspension at the point, a context read, a region over the evaluated value
  | .provideLayer l i b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_provideLayer' l i b hf]; exact List.Subset.refl _
  | .service key, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_service' key hf]; sub_tac
  | .provideService key value b, p => by
    rcases hf : p.fuel with _ | k
    · rw [compileEff_zero _ hf]; exact frontier_keys p
    · rw [compileEff_provideService' key value b hf]
      split
      · next v hv => sub_tac using (evalTerm_point_keys value p v hv)
      · exact List.nil_subset _

theorem resolve_keys (root : NativeEff) (p : Point) : nativeKeys (resolve root p) ⊆ p.keys := by
  unfold resolve
  split
  · exact compileEff_keys _ _
  · exact List.nil_subset _

/-! ## The join: a layer's build, a region and the memo protocol name only what their points hold -/

theorem Env.ContextUpdate.apply_keys (u : Env.ContextUpdate) (c : Env.Ctx) :
    Env.Context.handleKeys (u.apply c) ⊆ u.keys ++ Env.Context.handleKeys c := by
  cases u with
  | setTo context => exact List.subset_append_left _ _
  | provide that =>
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_merge c that hx) with h | h
    · exact List.mem_append_right _ h
    · exact List.mem_append_left _ h
  | provideService key value =>
    show Env.Context.handleKeys (c.add key value) ⊆ Val.keys value ++ Env.Context.handleKeys c
    exact Env.Context.handleKeys_add c key value

theorem compileLayer_keys : ∀ (l : LayerTerm NativeOp) (q : Point) (m : MemoMapId) (scope : Nat),
    nativeKeys (compileLayer l q m scope) ⊆ Handle.scope scope :: Handle.memoMap m.index :: q.keys
  | .succeed key value, q, m, scope => by
    simp only [compileLayer]
    split
    · next v hv =>
      show Val.keys (Env.encode (Env.Context.empty.addV key v)) ⊆ _
      rw [Val.keys_encode]
      intro x hx
      rcases List.mem_append.mp (Env.Context.handleKeys_addV _ key v hx) with h | h
      · rw [Lit.toVal_keys value v hv] at h
        exact absurd h List.not_mem_nil
      · rw [Env.Context.handleKeys_empty] at h
        exact absurd h List.not_mem_nil
    · exact List.nil_subset _
  | .fresh inner, q, m, scope => by simp only [compileLayer]; sub_tac
  | .orDie inner, q, m, scope => by
    simp only [compileLayer]
    sub_tac using (compileLayer_keys inner (q.child 0) m scope)
  | .effect _ _, q, m, scope | .effectDiscard _, q, m, scope | .provide _ _, q, m, scope
  | .provideMerge _ _, q, m, scope | .merge _ _, q, m, scope | .mergeAll _, q, m, scope => by
    simp only [compileLayer]; sub_tac
  | .ref _, _, _, _ => by simp only [compileLayer]; exact List.nil_subset _

/-- A hop keeps the point's handles: only the path and the fuel move. -/
theorem Point.redirect_keys (q : Point) (target : List Nat) : (q.redirect target).keys = q.keys := rfl

theorem resolveLayerTerm_keys (root : NativeEff) (l : LayerTerm NativeOp) (q : Point)
    (m : MemoMapId) (scope : Nat) :
    nativeKeys (resolveLayer.resolveLayerTerm root l q m scope) ⊆
      Handle.scope scope :: Handle.memoMap m.index :: q.keys := by
  cases l with
  | ref target =>
    simp only [resolveLayer.resolveLayerTerm]
    split
    · exact frontier_keys q |>.trans (List.subset_cons_of_subset _ (List.subset_cons_of_subset _ (List.Subset.refl _)))
    · split
      · exact List.nil_subset _
      · rw [← Point.redirect_keys q target]; exact compileLayer_keys _ _ _ _
      · exact List.nil_subset _
  | _ => exact compileLayer_keys _ _ _ _

theorem resolveLayer_keys (root : NativeEff) (q : Point) (m : MemoMapId) (scope : Nat) :
    nativeKeys (resolveLayer root q m scope) ⊆ Handle.scope scope :: Handle.memoMap m.index :: q.keys := by
  unfold resolveLayer
  split
  · exact resolveLayerTerm_keys _ _ _ _ _
  · exact List.nil_subset _

theorem innerLayerAt_keys (root : NativeEff) (q : Point) (m : MemoMapId) (child : Nat) :
    nativeKeys (innerLayerAt root q m child) ⊆ Handle.scope child :: Handle.memoMap m.index :: q.keys := by
  unfold innerLayerAt
  split <;> first
    | sub_tac
    | sub_tac using (resolveLayer_keys root (q.child 1) m child)
    | exact compileLayer_keys _ _ _ _
    | exact List.nil_subset _

theorem constructionAt_keys (root : NativeEff) (q : Point) (layerScope : Nat) :
    nativeKeys (constructionAt root q layerScope) ⊆ Handle.scope layerScope :: q.keys := by
  unfold constructionAt
  split <;> first | sub_tac | exact List.nil_subset _

theorem regionCode_keys (root : NativeEff) (r : Region) : nativeKeys (regionCode root r) ⊆ r.keys := by
  cases r with
  | program q => exact resolve_keys root q
  | build q m scope => exact resolveLayer_keys root q m scope
  | buildAdding q m scope => simp only [regionCode]; sub_tac using (resolveLayer_keys root q m scope)
  | construct q key => simp only [regionCode]; sub_tac using (resolve_keys root q)

theorem updateContextAt_keys (u : Env.ContextUpdate) (r : Region) :
    nativeKeys (updateContextAt u r) ⊆ u.keys ++ r.keys := by
  simp only [updateContextAt]; sub_tac

theorem scopeAddAt_keys (scope : Nat) (fin : FinName) :
    nativeKeys (scopeAddAt scope fin) ⊆ Handle.scope scope :: fin.keys := by
  simp only [scopeAddAt]; sub_tac

theorem contextsOfList_keys : ∀ (vs : List Val) (cs : List Env.Ctx), contextsOfList vs = some cs →
    cs.flatMap Env.Context.handleKeys ⊆ vs.flatMap Val.keys
  | [], cs, h => by
    simp only [contextsOfList, Option.some.injEq] at h
    subst h
    exact List.nil_subset _
  | x :: rest, cs, h => by
    simp only [contextsOfList] at h
    split at h
    · next c hc =>
      split at h
      · next ctx ctxs hctx hrest =>
        simp only [Option.some.injEq] at h
        subst h
        simp only [List.flatMap_cons]
        refine List.append_subset.mpr ⟨?_, ?_⟩
        · have hx := exitOfVal_keys x _ hc
          simp only [exitKeys] at hx
          exact List.Subset.trans (Env.decode_keys hctx) (List.Subset.trans hx (List.subset_append_left _ _))
        · exact List.Subset.trans (contextsOfList_keys rest ctxs hrest) (List.subset_append_right _ _)
      · cases h
    · cases h

theorem contextsOf_keys (v : Val) (cs : List Env.Ctx) (h : contextsOf v = some cs) :
    cs.flatMap Env.Context.handleKeys ⊆ v.keys := by
  unfold contextsOf at h
  split at h
  · rw [Val.keys_list]
    exact contextsOfList_keys _ _ h
  · cases h

theorem mergeContextsK_keys (v : Val) : nativeKeys (mergeContextsK v) ⊆ v.keys := by
  unfold mergeContextsK
  split
  · next ctxs hctxs =>
    show Val.keys (Env.encode (Env.Context.mergeAll ctxs)) ⊆ _
    rw [Val.keys_encode]
    exact List.Subset.trans (Env.Context.handleKeys_mergeAll ctxs) (contextsOf_keys v ctxs hctxs)
  · split <;> exact List.nil_subset _

theorem currentMemoMapOf_keys {c : Env.Ctx} {m : MemoMapId} (h : currentMemoMapOf c = some m) :
    Handle.memoMap m.index ∈ Env.Context.handleKeys c := by
  unfold currentMemoMapOf at h
  split at h
  · rename_i index hv
    simp only [Option.some.injEq] at h
    subst h
    exact Env.Context.getV_keys hv (List.mem_singleton.mpr rfl)
  · cases h

theorem provideLayerWithK_keys (root : NativeEff) (p : Point) (scope : Nat) :
    nativeKeys (provideLayerWithK root p scope) ⊆ Handle.scope scope :: p.keys := by
  unfold provideLayerWithK
  split
  · split <;> sub_tac
  · exact List.nil_subset _

theorem provideLayerBodyK_keys (root : NativeEff) (p : Point) (v : Val) :
    nativeKeys (provideLayerBodyK root p v) ⊆ p.keys ++ v.keys := by
  unfold provideLayerBodyK
  split
  · next built hbuilt =>
    split
    · next exit hexit =>
      have hb := resolve_keys root (p.child 1)
      rw [Prim.asExit?_eq_some _ _ hexit, ← exitKeys_eq_nativeKeys_ofExit] at hb
      rw [← exitKeys_eq_nativeKeys_ofExit]
      exact List.Subset.trans hb (List.subset_append_left _ _)
    · sub_tac using (Env.decode_keys hbuilt)
  · exact List.nil_subset _

theorem updateThenK_keys (root : NativeEff) (u : Env.ContextUpdate) (body : Region) (v : Val) :
    nativeKeys (updateThenK root u body v) ⊆ u.keys ++ body.keys ++ v.keys := by
  unfold updateThenK
  split
  · next prev hprev =>
    rw [Val.context?_exact hprev]
    split
    · sub_tac using (regionCode_keys root body)
    · -- `setContext(next)`'s handles are the update's and the previous map's; the restoring
      -- name carries the region's and the previous map's
      intro x hx
      simp only [nativeKeys, primKeys, EffThunk.keys, EffName.keys, Ctx.keys_withServices,
        Val.keys_context, Ctx.keys_eq_handleKeys, List.mem_append, List.nil_append] at hx ⊢
      rcases hx with h | h | h
      · rcases List.mem_append.mp (Env.ContextUpdate.apply_keys u prev.services h) with h | h
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  · exact List.nil_subset _

theorem buildWithScopeK_keys (q : Point) (scope : Nat) (v : Val) :
    nativeKeys (buildWithScopeK q scope v) ⊆ Handle.scope scope :: q.keys ++ v.keys := by
  unfold buildWithScopeK
  split
  · next ctx hctx =>
    rw [Val.context?_exact hctx]
    cases hm : currentMemoMapOf ctx.services with
    | none => sub_tac
    | some m =>
      show [Handle.memoMap m.index] ++ (Handle.scope scope :: q.keys) ⊆ _
      intro x hx
      rcases List.mem_append.mp hx with h | h
      · rw [List.mem_singleton.mp h]
        refine List.mem_append_right _ ?_
        rw [Val.keys_context, Ctx.keys_eq_handleKeys]
        exact currentMemoMapOf_keys hm
      · exact List.mem_append_left _ h
  · exact List.nil_subset _

theorem addCurrentMemoMapK_keys (m : MemoMapId) (v : Val) :
    nativeKeys (addCurrentMemoMapK m v) ⊆ Handle.memoMap m.index :: v.keys := by
  unfold addCurrentMemoMapK
  split
  · next ctx hctx =>
    show Val.keys (Env.encode _) ⊆ _
    rw [Val.keys_encode]
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_addV _ _ _ hx) with h | h
    · rw [Val.keys_memoMap] at h
      exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
    · exact List.mem_cons_of_mem _ (Env.decode_keys hctx h)
  · exact List.nil_subset _

theorem provideThenK_keys (q : Point) (m : MemoMapId) (scope : Nat) (mode : CombineMode) (v : Val) :
    nativeKeys (provideThenK q m scope mode v) ⊆
      Handle.scope scope :: Handle.memoMap m.index :: q.keys ++ v.keys := by
  unfold provideThenK
  split
  · next ctx hctx => sub_tac using (Env.decode_keys hctx)
  · exact List.nil_subset _

theorem combineWithK_keys (mode : CombineMode) (that : Env.Ctx) (v : Val) :
    nativeKeys (combineWithK mode that v) ⊆ Env.Context.handleKeys that ++ v.keys := by
  unfold combineWithK
  split
  · next merged hm =>
    split
    · show Val.keys (Env.encode merged) ⊆ _
      rw [Val.keys_encode]
      exact List.Subset.trans (Env.decode_keys hm) (List.subset_append_right _ _)
    · show Val.keys (Env.encode (that.merge merged)) ⊆ _
      rw [Val.keys_encode]
      intro x hx
      rcases List.mem_append.mp (Env.Context.handleKeys_merge that merged hx) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (Env.decode_keys hm h)
  · exact List.nil_subset _

theorem bindServiceK_keys (key : Option ServiceKey) (v : Val) :
    nativeKeys (bindServiceK key v) ⊆ v.keys := by
  cases key with
  | some key =>
    show Val.keys (Env.encode (Env.Context.empty.addV key v)) ⊆ _
    rw [Val.keys_encode]
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_addV _ key v hx) with h | h
    · exact h
    · rw [Env.Context.handleKeys_empty] at h
      exact absurd h List.not_mem_nil
  | none =>
    show Val.keys (Env.encode Env.Context.empty) ⊆ _
    rw [Val.keys_encode, Env.Context.handleKeys_empty]
    exact List.nil_subset _

theorem serviceLookupK_keys (key : ServiceKey) (v : Val) :
    nativeKeys (serviceLookupK key v) ⊆ v.keys := by
  unfold serviceLookupK
  split
  · next ctx hctx =>
    split
    · next value hval =>
      rw [Val.context?_exact hctx, Val.keys_context, Ctx.keys_eq_handleKeys]
      exact Env.Context.getV_keys hval
    · exact List.nil_subset _
  · exact List.nil_subset _

theorem entrants_keys (root : NativeEff) : ∀ (es : Effs NativeOp) (q : Point),
    (actionAt.entrants es q).flatMap nativeKeys ⊆ q.keys
  | .nil, _ => List.nil_subset _
  | .cons h t, q => by
    simp only [actionAt.entrants, List.flatMap_cons]
    exact List.append_subset.mpr ⟨compileEff_keys h (q.child 0), entrants_keys root t (q.child 1)⟩

/-! ## The generator walker keeps to its captured exits and environment -/

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

/-- What a generator step may name, given a bound `E` on its point's handles. -/
def StepKeys (E : List Handle) : IterStep EffName EffThunk Val Err Defect FiberId Ann → Prop
  | IterStep.done r => r.keys ⊆ E
  | IterStep.resume next n' => nativeKeys next ++ EffName.keys n' ⊆ E
  | IterStep.halt _ => True

theorem Point.withEnv_keys_subset (p : Point) (env env' : List Val) (h : env' ⊆ env) :
    ({ p with env := env' } : Point).keys ⊆ ({ p with env := env } : Point).keys := by
  apply List.append_subset.mpr
  exact ⟨List.subset_append_left _ _,
    List.Subset.trans (flatMap_subset_of_subset h) (List.subset_append_right _ _)⟩

mutual
theorem runStmts_keys (root : NativeEff) (p : Point) (E : List Handle) :
    ∀ (fuel : Nat) (pc : List Nat) (env folded : List Val),
      ({ p with env := env } : Point).keys ⊆ E →
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
          (List.Subset.trans (p.withEnv_keys_subset env env'
            (blockExit_env root p pc env pc' env' hexit)) henv)
    · next s _ _ =>
      split
      · exact yieldOf_keys root p E fuel _ true pc env folded henv
      · exact yieldOf_keys root p E fuel _ false pc env folded henv
      ·
        split
        · next value hvalue =>
          simp only [StepKeys]
          exact List.Subset.trans (evalTerm_point_keys _ { p with env := env } value hvalue) henv
        · simp only [StepKeys]
      · split
        · exact runStmts_keys root p E fuel _ env folded henv
        · exact runStmts_keys root p E fuel _ env folded henv
        · simp only [StepKeys]
      · exact runStmts_keys root p E fuel _ env folded henv
      · split
        · next pc' env' hexit =>
          exact runStmts_keys root p E fuel pc' env' folded
            (List.Subset.trans (p.withEnv_keys_subset env env'
              (loopExit_env root _ p pc env pc' env' hexit)) henv)
        · simp only [StepKeys]
    · simp only [StepKeys]
termination_by fuel _ _ _ _ => (fuel, 0)

theorem yieldOf_keys (root : NativeEff) (p : Point) (E : List Handle) (fuel : Nat) (e : NativeEff) (bind : Bool)
    (pc : List Nat) (env folded : List Val) (henv : ({ p with env := env } : Point).keys ⊆ E) :
    StepKeys E (runStmts.yieldOf root p e bind fuel pc env folded).2 := by
  simp only [runStmts.yieldOf]
  have hcode := compileEff_keys e { p with path := p.path ++ [0] ++ pc ++ [0, 0], env := env, fuel := fuel + 1 }
  split
  · next value hvalue =>
    rw [hvalue] at hcode
    refine runStmts_keys root p E fuel _ _ _ ?_
    cases bind
    · exact henv
    · change ({ p with env := env ++ [value] } : Point).keys ⊆ E
      have hvalue : value.keys ⊆ E := List.Subset.trans hcode henv
      simpa only [Point.keys, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
        List.append_nil, List.append_assoc] using List.append_subset.mpr ⟨henv, hvalue⟩
  · simp only [StepKeys]
  ·
    simp only [StepKeys]
    exact List.append_subset.mpr ⟨List.Subset.trans hcode henv, henv⟩
termination_by (fuel, 1)
end

/-! ## A fiber action names only what its point evaluates -/

theorem evalTerm_fiber_mem (t : Term) (env : List Val) (id : FiberId) (h : evalTerm env t = some (Val.fiber id)) :
    Handle.fiber id ∈ env.flatMap Val.keys :=
  evalTerm_keys t env _ h (by rw [Val.keys_fiber]; exact List.mem_singleton.mpr rfl)

theorem evalTerm_scope_mem (t : Term) (env : List Val) (s : Nat) (h : evalTerm env t = some (Val.scopeHandle s)) :
    Handle.scope s ∈ env.flatMap Val.keys :=
  evalTerm_keys t env _ h (by rw [Val.keys_scopeHandle]; exact List.mem_singleton.mpr rfl)

/-- The fibers a `withFiber` term's value names (`actionAt`'s `handles`): a snapshot or a tuple of
fiber handles. -/
theorem handlesOf_keys (v : Val) (ids : List FiberId)
    (hh : (match v with
           | Value.fiberSnapshot hs => (Store.Image.list Value.fiberHandle).ofVal hs
           | v => (Val.tuple? v).bind fun vs => vs.mapM fun
             | Val.fiber ⟨id⟩ => some ⟨id⟩
             | _ => none) = some ids) :
    ids.map Handle.fiber ⊆ v.keys := by
  have hg : ∀ (w : Val) (id : FiberId),
      (fun x => match x with | Val.fiber ⟨id⟩ => some ⟨id⟩ | _ => none) w = some id →
        Handle.fiber id ∈ w.keys := by
    intro w id hw
    simp only [] at hw
    split at hw
    · injection hw with hw
      subst hw
      simp only [Val.keys, Handle.ofCode_fiber, Option.toList, List.mem_singleton]
    · exact nomatch hw
  split at hh
  · next hs =>
    rw [(Store.Image.list Value.fiberHandle).ofVal_exact hh]
    show ids.map Handle.fiber ⊆ (Val.fibers ids).keys
    rw [Val.keys_fibers]
    exact List.Subset.refl _
  · obtain ⟨vs, hvs, hm⟩ := Option.bind_eq_some_iff.mp hh
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
      -- the service read names nothing (§20); `forkScopedAt_keys` bounds the `forkIn` half
      simp only [] at h
      subst h
      exact List.nil_subset _
    | runIn target scope =>
      simp only [] at h
      split at h
      · rename_i id s hid hs
        subst h
        have h1 := evalTerm_fiber_mem target p.env ⟨id⟩ hid
        have h2 := evalTerm_scope_mem scope p.env s hs
        sub_tac
      · subst h; exact List.nil_subset _
    | interrupt target =>
      simp only [] at h
      split at h
      · rename_i id hid
        subst h
        have h1 := evalTerm_fiber_mem target p.env ⟨id⟩ hid
        sub_tac
      · subst h; exact List.nil_subset _
    | interruptScoped target =>
      simp only [] at h
      split at h
      · rename_i id hid
        subst h
        have h1 := evalTerm_fiber_mem target p.env ⟨id⟩ hid
        sub_tac
      · subst h; exact List.nil_subset _
    | interruptAll targets interruptor =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        have hids' : ids.map Handle.fiber ⊆ p.keys :=
          List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys targets p v hv)
        split at h
        · subst h
          sub_tac using hids'
        · rename_i who _
          split at h
          · subst h
            sub_tac using hids'
          · subst h; exact List.nil_subset _
      · subst h; exact List.nil_subset _
    | awaitAll targets =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys targets p v hv)
      · subst h; exact List.nil_subset _
    | awaitAllFailFast targets =>
      simp only [] at h
      split at h
      · rename_i ids hids
        obtain ⟨v, hv, hh⟩ := Option.bind_eq_some_iff.mp hids
        subst h
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys targets p v hv)
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
        exact List.Subset.trans (handlesOf_keys v ids hh) (evalTerm_point_keys snapshot p v hv)
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
        obtain ⟨w, hw, hctx'⟩ := Option.bind_eq_some_iff.mp hctx
        rw [Val.context?_exact hctx'] at hw
        have hkeys := evalTerm_point_keys context p (Val.context ctx) hw
        rw [Val.keys_context] at hkeys
        exact hkeys
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
        have h2 : exitKeys e ⊆ p.keys := List.Subset.trans (exitOfVal_keys v e hev) (evalTerm_point_keys exit p v hv)
        sub_tac using h2
      · subst h; exact List.nil_subset _
  · cases h

/-! ## The hooks of `interpOf` are key-bounded -/

/-- `forkScoped`'s `forkIn` half (§20) names the handle the service read answered and the
child's point. -/
theorem forkScopedAt_keys (root : NativeEff) (p : Point) (scope : Nat) (a : NAction)
    (h : forkScopedAt root p scope = some a) :
    a.keys EffName.keys EffThunk.keys ⊆ (EffThunk.forkInAt p scope).keys := by
  unfold forkScopedAt at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    simp only [WithFiberAction.keys, EffThunk.keys]
    sub_tac using (resolve_keys root ((p.child 0).child 0))
  · cases h

-- One table, one budget: the join doubled the arms (`set_option`, as `interpOf_keyBounded`).
set_option maxHeartbeats 800000 in
/-- The compile's continuation table names only what its name and its value name. The join's
names first, each by its continuation's own bound (`Agreement.lean`'s equations select the arm;
a handle-reading name splits on its reader); the rest as one `match` over the name and the
value's shape (the spellings are reducible) — a name whose arm reads no value unfolds to the
arm itself, so the split is optional — the dead rows refuted by `contradiction`; the
`scopeProvide` arm reads the previous context back off the value and splits once more. -/
theorem contAOf_native_keys (root : NativeEff) (n : EffName) (v : Val) :
    nativeKeys (Program.contAOf root n v) ⊆ n.keys ++ v.keys := by
  cases n
  case provideLayerWith p =>
    cases hs : Val.scope? v with
    | some s =>
      rw [Val.scope?_exact hs, contAOf_provideLayerWith_scope]
      exact List.Subset.trans (provideLayerWithK_keys root p s) (by sub_tac)
    | none =>
      rw [contAOf_provideLayerWith_other root p v (Val.scope?_none hs)]
      exact List.nil_subset _
  case provideLayerBody p =>
    rw [contAOf_provideLayerBody]
    exact List.Subset.trans (provideLayerBodyK_keys root p v) (by sub_tac)
  case updateThen u body =>
    rw [contAOf_updateThen]
    exact List.Subset.trans (updateThenK_keys root u body v) (by sub_tac)
  case bodyThen body previous =>
    rw [contAOf_bodyThen]
    sub_tac using (regionCode_keys root body)
  case buildWithScopeFromContext q scope =>
    rw [contAOf_buildWithScopeFromContext]
    exact List.Subset.trans (buildWithScopeK_keys q scope v) (by sub_tac)
  case withMemoMapThen q scope =>
    cases hid : Val.memoMap? v with
    | some id =>
      rw [Val.memoMap?_exact hid, contAOf_withMemoMapThen_memoMap]
      exact List.Subset.trans (updateContextAt_keys _ _) (by sub_tac)
    | none =>
      rw [contAOf_withMemoMapThen_other root q scope v (Val.memoMap?_none hid)]
      exact List.nil_subset _
  case addCurrentMemoMap m =>
    rw [contAOf_addCurrentMemoMap]
    exact List.Subset.trans (addCurrentMemoMapK_keys m v) (by sub_tac)
  case fromBuildThen q m =>
    cases hs : Val.scope? v with
    | some child =>
      rw [Val.scope?_exact hs, contAOf_fromBuildThen_scope]
      sub_tac using (innerLayerAt_keys root q m child)
    | none =>
      rw [contAOf_fromBuildThen_other root q m v (Val.scope?_none hs)]
      exact List.nil_subset _
  case memoize q m scope =>
    cases hh : Val.memoHit? v with
    | some co =>
      obtain ⟨cell, owner⟩ := co
      rw [Val.memoHit?_exact hh, contAOf_memoize_hit]
      sub_tac using (scopeAddAt_keys scope _)
    | none =>
      by_cases hu : v = Val.unit
      · subst hu
        rw [contAOf_memoize_unit]
        sub_tac
      · rw [contAOf_memoize_other root q m scope v (Val.memoHit?_none hh) hu]
        exact List.nil_subset _
  case awaitPromise cell =>
    rw [contAOf_awaitPromise]
    sub_tac
  case buildIntoLayerScope q m scope =>
    cases hs : Val.scope? v with
    | some layerScope =>
      rw [Val.scope?_exact hs, contAOf_buildIntoLayerScope_scope]
      sub_tac using (scopeAddAt_keys scope _)
    | none =>
      rw [contAOf_buildIntoLayerScope_other root q m scope v (Val.scope?_none hs)]
      exact List.nil_subset _
  case thenBuildInto q m layerScope =>
    rw [contAOf_thenBuildInto]
    sub_tac using (constructionAt_keys root q layerScope)
  case freshThen q scope =>
    cases hid : Val.memoMap? v with
    | some id =>
      rw [Val.memoMap?_exact hid, contAOf_freshThen_memoMap]
      exact List.Subset.trans (resolveLayer_keys root q id scope) (by sub_tac)
    | none =>
      rw [contAOf_freshThen_other root q scope v (Val.memoMap?_none hid)]
      exact List.nil_subset _
  case provideThen q m scope mode =>
    rw [contAOf_provideThen]
    exact List.Subset.trans (provideThenK_keys q m scope mode v) (by sub_tac)
  case combineWith mode that =>
    rw [contAOf_combineWith]
    exact List.Subset.trans (combineWithK_keys mode that v) (by sub_tac)
  case mergeChildren q m =>
    cases hs : Val.scope? v with
    | some parent =>
      rw [Val.scope?_exact hs, contAOf_mergeChildren_scope]
      sub_tac
    | none =>
      rw [contAOf_mergeChildren_other root q m v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeForkOne q i m parent forked =>
    cases hs : Val.scope? v with
    | some child =>
      rw [Val.scope?_exact hs, contAOf_mergeForkOne_scope]
      sub_tac
    | none =>
      rw [contAOf_mergeForkOne_other root q i m parent forked v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeForkNext q i m parent forked =>
    cases hf : Val.fiber? v with
    | some id =>
      rw [Val.fiber?_exact hf, contAOf_mergeForkNext_fiber]
      split <;> sub_tac
    | none =>
      rw [contAOf_mergeForkNext_other root q i m parent forked v (Val.fiber?_none hf)]
      exact List.nil_subset _
  case mergeAllChildren q m =>
    cases hs : Val.scope? v with
    | some parent =>
      rw [Val.scope?_exact hs, contAOf_mergeAllChildren_scope]
      split <;> sub_tac
    | none =>
      rw [contAOf_mergeAllChildren_other root q m v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeAllForkOne q i m parent forked =>
    cases hs : Val.scope? v with
    | some child =>
      rw [Val.scope?_exact hs, contAOf_mergeAllForkOne_scope, forkLayer_keys_spine]
      sub_tac
    | none =>
      rw [contAOf_mergeAllForkOne_other root q i m parent forked v (Val.scope?_none hs)]
      exact List.nil_subset _
  case mergeAllForkNext q i m parent forked =>
    cases hf : Val.fiber? v with
    | some id =>
      rw [Val.fiber?_exact hf, contAOf_mergeAllForkNext_fiber]
      split <;> sub_tac
    | none =>
      rw [contAOf_mergeAllForkNext_other root q i m parent forked v (Val.fiber?_none hf)]
      exact List.nil_subset _
  case mergeContexts =>
    rw [contAOf_mergeContexts]
    exact List.Subset.trans (mergeContextsK_keys v) (by sub_tac)
  case serviceLookup key =>
    rw [contAOf_serviceLookup]
    exact List.Subset.trans (serviceLookupK_keys key v) (by sub_tac)
  case bindService key =>
    rw [contAOf_bindService]
    exact List.Subset.trans (bindServiceK_keys key v) (by sub_tac)
  case orDie =>
    show nativeKeys (Prim.success v) ⊆ _
    sub_tac
  -- a known name whose arm reads no value unfolds to the arm itself (the equations of the
  -- table); a handle-reading name keeps its rows, each with an equation on the name and on
  -- the value, and `cases` on those identifies the row's variables or refutes it
  all_goals first
    | (simp only [Program.contAOf]; first
      | (simp only [nativeKeys, embed_keys]; exact Machine.contAOf_keys _ _)
      | (simp only [primKeys_ofExit]; sub_tac)
      | exact List.nil_subset _
      | sub_tac
      | sub_tac using (resolve_keys root _)
      | sub_tac norm [Point.keys, EffName.keys, EffThunk.keys]
      -- the `acquired` arm: the capture's handles are the point's, the value's and the context's
      | sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, SyncOp.keys, FinName.keys, Point.capture,
          Val.keysList_eq_flatMap]
      -- the `releaseBody` arm: the release's point appends the reified exit
      | sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, Point.childWith, Machine.reifyExitVal_keys]
      -- the `scopeProvide` arm: the install's handles are the scope's and the previous map's
      | (split
         · next previous hprev =>
           rw [Val.context?_exact hprev]
           sub_tac using (Ctx.keys_withScope previous _)
             norm [Point.keys, EffName.keys, EffThunk.keys, Val.keys_context]
         · sub_tac)
      -- the `afterScopeAdd` arm: unit answers `a`; a closed scope's exit, read back, runs the
      -- release program under it
      | (split <;> first
          | sub_tac
          | (split
             · next exit hexit =>
               sub_tac using (Machine.finProgram_keys _ exit), (exitOfVal_keys _ exit hexit)
                 norm [Point.keys, EffName.keys, EffThunk.keys, embed_keys]
             · sub_tac)))
    | (unfold Program.contAOf; split <;> (try (rename_i heq; cases heq)) <;>
        (try (rename_i heq; cases heq)) <;> first
        | contradiction
        | (simp only [nativeKeys, embed_keys]; exact Machine.contAOf_keys _ _)
        | (simp only [primKeys_ofExit]; sub_tac)
        | exact List.nil_subset _
        | sub_tac
        | sub_tac using (resolve_keys root _)
        | sub_tac norm [Point.keys, EffName.keys, EffThunk.keys]
        -- the `acquired` arm: the capture's handles are the point's, the value's and the context's
        | sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, SyncOp.keys, FinName.keys, Point.capture,
            Val.keysList_eq_flatMap]
        -- the `releaseBody` arm: the release's point appends the reified exit
        | sub_tac norm [Point.keys, EffName.keys, EffThunk.keys, Point.childWith, Machine.reifyExitVal_keys]
        -- the `scopeProvide` arm: the install's handles are the scope's and the previous map's
        | (split
           · next previous hprev =>
             rw [Val.context?_exact hprev]
             sub_tac using (Ctx.keys_withScope previous _)
               norm [Point.keys, EffName.keys, EffThunk.keys, Val.keys_context]
           · sub_tac)
        -- the `afterScopeAdd` arm: unit answers `a`; a closed scope's exit, read back, runs the
        -- release program under it
        | (split <;> first
            | sub_tac
            | (split
               · next exit hexit =>
                 sub_tac using (Machine.finProgram_keys _ exit), (exitOfVal_keys _ exit hexit)
                   norm [Point.keys, EffName.keys, EffThunk.keys, embed_keys]
               · sub_tac)))

/-- A successful conditional handler binds exactly the once-selected first error. -/
theorem caughtErrorValue?_first {env : List Val} {test : Term} {cause : CauseV} {value : Val}
    (h : caughtErrorValue? env test cause = some value) : firstErrorValue? cause = some value := by
  simp only [caughtErrorValue?, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨found, hfound, h⟩ := h
  split at h
  · cases h; exact hfound
  · cases h

/-- The selected error image cannot introduce a handle into the handler environment. -/
theorem caughtErrorValue?_keys {env : List Val} {test : Term} {cause : CauseV} {value : Val}
    (h : caughtErrorValue? env test cause = some value) : value.keys = [] := by
  have hf := caughtErrorValue?_first h
  simp only [firstErrorValue?, Option.bind_eq_bind, Option.bind_eq_some_iff] at hf
  obtain ⟨error, _, he⟩ := hf
  exact valOfErr_keys error value he

theorem contEOf_native_keys (root : NativeEff) (n : EffName) (cause : CauseV) :
    nativeKeys (Program.contEOf root n cause) ⊆ n.keys := by
  cases n with
  | caught p => simp only [Program.contEOf]; sub_tac using (resolve_keys root (p.childWith 1 (Val.exitErr cause)))
  | caughtError p =>
    simp only [Program.contEOf]
    split
    · split
      · rename_i value hvalue
        have hk := caughtErrorValue?_keys hvalue
        simpa only [Point.keys, Point.childWith, List.flatMap_append, List.flatMap_cons,
          List.flatMap_nil, hk, List.append_nil, EffName.keys] using
          (resolve_keys root (p.childWith 1 value))
      · exact List.nil_subset _
    · exact List.nil_subset _
  | onCause p => simp only [Program.contEOf]; sub_tac using (resolve_keys root (p.childWith 2 (Val.exitErr cause)))
  | restore exit =>
    simp only [Program.contEOf, primKeys_ofExit]
    sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | merge exit =>
    simp only [Program.contEOf, primKeys_ofExit]
    sub_tac using (exitKeys_restoreAfterFinalizer exit _)
  | constant w => simp only [Program.contEOf]; exact List.Subset.refl _
  | store name => simp only [Program.contEOf, nativeKeys, embed_keys]; exact Machine.contEOf_keys name cause
  | orDie => simp only [Program.contEOf]; exact List.nil_subset _
  | cont p | onValue p | fin p | gen p pc bind | loop p | registerAwait cell | cancelAwait cell
  | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s | scopeBody p previous
  | scopedExit previous scope | scopeClose scope | restoreCtx previous | forkScopedIn p
  | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer | releaseUnder p ctx e
  | releaseBody p e previous
  | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
  | buildWithScopeFromContext q scope | withMemoMapThen q scope | addCurrentMemoMap m
  | fromBuildThen q m | memoize q m scope | awaitPromise cell | buildIntoLayerScope q m scope
  | thenBuildInto q m layerScope | freshThen q scope | provideThen q m scope mode
  | combineWith mode that | mergeChildren q m | mergeForkOne q i m parent forked
  | mergeForkNext q i m parent forked | mergeAllChildren q m | mergeAllForkOne q i m parent forked
  | mergeAllForkNext q i m parent forked | mergeContexts | serviceLookup key | bindService key
  | external _ _ =>
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
      | some val => exact evalTerm_point_keys term p val hval
    · exact List.nil_subset _
  | body _ | op _ | park _ | act _ | forkInAt _ _ | getCtx | setCtx _ | closeScope _ _ | store _
  | acquireMasked _ _ | releaseMasked _ _ | memoLookup _ _ _ | forkLayer _ _ _ | awaitAllFailFast _ =>
    simp only [syncValueAt]; exact List.nil_subset _

theorem suspendBodyAt_keys (root : NativeEff) (t : EffThunk) : nativeKeys (suspendBodyAt root t) ⊆ t.keys := by
  cases t with
  | body p =>
    simp only [suspendBodyAt]
    split
    · exact frontier_keys p
    · split
      · exact resolve_keys root (p.child 0)
      · split
        · exact resolve_keys root (p.child 0)
        · exact resolve_keys root (p.child 1)
        · exact List.nil_subset _
      · sub_tac
      · split
        · next cursor hcursor => sub_tac using (evalTerm_point_keys _ p cursor hcursor)
        · exact List.nil_subset _
      -- `Effect.provide`: the scope made, the rest named at the point
      · sub_tac
      · exact compileEff_keys _ p
      · exact List.nil_subset _
  -- `getOrElseMemoize`'s suspend: the lookup, then `memoize` at the point
  | memoLookup q m scope => simp only [suspendBodyAt]; sub_tac
  | store thunk =>
    cases thunk with
    | body program => simp only [suspendBodyAt, nativeKeys, embed_keys]; exact Machine.progOf_keys program
    | park _ | act _ | op _ => simp only [suspendBodyAt]; exact List.nil_subset _
    -- a capture's release: the context read, then the release named at the capture's point
    | foreign capture exit =>
      simp only [suspendBodyAt]
      sub_tac using (Point.ofCapture_keys capture)
  | pure _ | op _ | park _ | act _ | forkInAt _ _ | getCtx | setCtx _ | closeScope _ _
  | acquireMasked _ _ | releaseMasked _ _ | forkLayer _ _ _ | awaitAllFailFast _ =>
    simp only [suspendBodyAt]; exact List.nil_subset _

theorem env_bind_keys (p : Point) (v : Val) (bind : Bool) :
    (if bind then p.env ++ [v] else p.env).flatMap Val.keys ⊆ p.keys ++ v.keys := by
  cases bind with
  | false =>
    change p.env.flatMap Val.keys ⊆ p.keys ++ v.keys
    exact List.Subset.trans p.env_keys_subset (List.subset_append_left _ _)
  | true =>
    change (p.env ++ [v]).flatMap Val.keys ⊆ p.keys ++ v.keys
    simp only [List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    exact List.append_subset.mpr
      ⟨List.Subset.trans p.env_keys_subset (List.subset_append_left _ _), List.subset_append_right _ _⟩

theorem point_bind_keys (p : Point) (v : Val) (bind : Bool) :
    ({ p with env := if bind then p.env ++ [v] else p.env } : Point).keys ⊆ p.keys ++ v.keys := by
  cases bind with
  | false => exact List.subset_append_left _ _
  | true =>
    change (p.childWith 0 v).keys ⊆ p.keys ++ v.keys
    rw [Point.childWith_keys]
    exact List.Subset.refl _

/-- A scalar oracle completion contributes no unallocated handle to resumed code. -/
theorem externalAdmits_keys (table : RowTable) (i : Nat)
    (answer : Completion Val Err Defect FiberId Ann) (allocated : List String)
    (h : externalAdmits table i answer allocated = true) :
    answer.keys = [] := by
  cases answer with
  | ofExit exit =>
    cases exit with
    | failure cause => rfl
    | success value =>
      cases hr : externalRow table i with
      | none => simp [externalAdmits, hr] at h
      | some row =>
        simp only [externalAdmits, hr, Bool.and_eq_true_iff, List.isEmpty_iff] at h
        simp only [Completion.keys, exitKeys, Val.keys_eq_handles, h.2, List.filterMap_nil]
  | ofRefGet cell =>
    cases hr : externalRow table i <;> simp [externalAdmits, hr] at h

/-- A converted reply grows only the external allocation list; every returned handle
is either an already valid input or the fresh index just appended. -/
theorem externalValue_minted (ty : Ty) (s : Stores) (ids : List FiberId)
    (value result : Val) (allocated : List String)
    (hc : externalValue ty s.externals.allocated value = some (allocated, result))
    (hok : Ok ⟨ids, s⟩ (value.keys ++ s.keys)) :
    let next := { s with externals := { s.externals with allocated } }
    s.le next ∧ Ok ⟨ids, next⟩ (next.keys ++ result.keys) := by
  unfold externalValue at hc
  split at hc
  · rename_i target index
    split at hc
    · rename_i ha
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      simp only [Bool.and_eq_true, beq_iff_eq] at ha
      obtain ⟨_, rfl⟩ := ha
      have hle : s.le { s with externals := { s.externals with
          allocated := s.externals.allocated ++ [target] } } :=
        ⟨Nat.le_refl _, Nat.le_refl _, (fun _ h => h), Nat.le_refl _,
          (fun _ h => h), by simp⟩
      refine ⟨hle, Ok_append.mpr ⟨?_, ?_⟩⟩
      · exact Ok_mono (World.le_of_state hle) (Ok_append.mp hok).2
      · simp [Val.keys_eq_handles, Store.Val.handles, Handle.ofCode, HandleKind.ofByte?,
          Ok, Handle.existsIn]
    · cases hc
  · split at hc
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hc)
      exact ⟨Stores.le_refl _, Ok_append.mpr ⟨(Ok_append.mp hok).2, (Ok_append.mp hok).1⟩⟩
    · cases hc

/-- The stateful answer hook meets the generic handle contract for every current
code and table, including refused and nonexternal inputs. -/
theorem prepareExternalAnswer_minted (table : RowTable) (current : Option NCode)
    (answer : Completion Val Err Defect FiberId Ann) (s : Stores) (ids : List FiberId)
    (hok : Ok ⟨ids, s⟩ (answer.keys ++ s.keys)) :
    s.le (prepareExternalAnswer table current answer s).1 ∧
      Ok ⟨ids, (prepareExternalAnswer table current answer s).1⟩
        ((prepareExternalAnswer table current answer s).1.keys ++
          nativeKeys (prepareExternalAnswer table current answer s).2) := by
  have fallback : s.le s ∧ Ok ⟨ids, s⟩ (s.keys ++ nativeKeys (embed (completionPrim answer))) := by
    refine ⟨Stores.le_refl _, ?_⟩
    exact Ok_of_subset (by rw [nativeKeys, embed_keys]; sub_tac using completionPrim_keys answer) hok
  unfold prepareExternalAnswer
  split
  · exact fallback
  · split
    · rename_i i request controller cancel value
      split
      · exact fallback
      · rename_i row hr
        split
        · exact fallback
        · rename_i allocated result hv
          exact externalValue_minted row.answer s ids value result allocated hv hok
    · exact fallback

-- One declaration, forty fields, one heartbeat budget: the key normalisation on the shared
-- carrier (U1) took this instance past the default 200 000 (it was near it before: at
-- 100 000 the pre-U1 text fails too), so the budget is declared here rather than the fields
-- split apart.
set_option maxHeartbeats 800000 in
theorem interpOf_keyBounded (root : NativeEff) (table : RowTable := []) :
    KeyBounded EffName.keys EffThunk.keys (interpOf root table) where
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
        (point_bind_keys p v bind)
      rw [h] at hs
      exact hs
    | store name =>
      -- the stores' generators (a scope's close walk, §20), embedded
      simp only [interpOf] at h
      have hs := stores_keyBounded.iterNext_done name v r (embedStep_done h)
      simpa only [EffName.keys, List.nil_append] using hs
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | loop p | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie | external _ _ =>
      simp only [interpOf, IterStep.done.injEq] at h
      subst h
      exact List.subset_append_right _ _
  iterNext_resume n v next n' h := by
    cases n with
    | gen p pc bind =>
      simp only [interpOf] at h
      have hs := runStmts_keys root p (p.keys ++ v.keys) p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (point_bind_keys p v bind)
      rw [h] at hs
      exact hs
    | store name =>
      simp only [interpOf] at h
      obtain ⟨next0, n0, hstep, rfl, rfl⟩ := embedStep_resume h
      have hs := stores_keyBounded.iterNext_resume name v next0 n0 hstep
      simpa only [nativeKeys, embed_keys, EffName.keys, List.nil_append] using hs
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | loop p | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie | external _ _ =>
      simp only [interpOf] at h; cases h
  loopBody n c := by
    cases n with
    | loop p => simp only [interpOf]; sub_tac using (resolve_keys root (p.childWith 0 c))
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c' | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | store name | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie | external _ _ =>
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
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | registerAwait cell
    | cancelAwait cell | withWaiter base waiter token | abort | reFail c' | scopeOpen p | scopeProvide p s
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | store name | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie | external _ _ =>
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
  parkOfAwaitAll code targets h := by
    simp only [interpOf] at h
    split at h
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      sub_tac
    · rename_i kind
      simp only [Option.some.injEq, Except.ok.injEq] at h
      subst h
      sub_tac
    · cases h
  withFiberOf t a h := by
    cases t with
    | act p => simp only [interpOf] at h; exact actionAt_keys root p a h
    | forkInAt p scope => simp only [interpOf] at h; exact forkScopedAt_keys root p scope a h
    | getCtx => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.nil_subset _
    | setCtx ctx => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    | closeScope scope exit => simp only [interpOf, Option.some.injEq] at h; subst h; exact List.Subset.refl _
    -- the masked acquire: the embedded `Scope` read names nothing, the continuation the point
    -- and the context
    | acquireMasked p ctx =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      sub_tac
    -- the masked release: the resolved point's code and the restoring finalizer
    | releaseMasked p previous =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      sub_tac using (resolve_keys root p)
    -- a sibling's build forked (the join): the layer's code at its point
    | forkLayer q m scope =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      sub_tac using (resolveLayer_keys root q m scope)
    | awaitAllFailFast targets =>
      simp only [interpOf, Option.some.injEq] at h
      subst h
      exact List.Subset.refl _
    | store thunk =>
      cases thunk with
      | act action =>
        simp only [interpOf, Option.some.injEq] at h
        subst h
        rw [embedAction_keys]
        exact Machine.actionOf_keys action
      | park _ | op _ | body _ | foreign _ _ => simp only [interpOf] at h; cases h
    | pure _ | body _ | op _ | park _ | memoLookup _ _ _ => simp only [interpOf] at h; cases h
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
      | park _ | act _ | body _ | foreign _ _ => simp only [interpOf] at h; cases h
    | pure _ | body _ | park _ | act _ | forkInAt _ _ | getCtx | setCtx _ | closeScope _ _
    | acquireMasked _ _ | releaseMasked _ _ | memoLookup _ _ _ | forkLayer _ _ _ | awaitAllFailFast _ =>
      simp only [interpOf] at h; cases h
  registerAsync n fiber token s ids hok := by
    have reg : ∀ cell, Ok ⟨ids, s⟩ ([Handle.promise cell] ++ s.keys) →
        s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } ∧
          Ok ⟨ids, { s with deferreds := (s.deferreds.register cell fiber token).1 }⟩
            ({ s with deferreds := (s.deferreds.register cell fiber token).1 }.keys ++
              (((s.deferreds.register cell fiber token).2.map embed).map nativeKeys).getD []) := by
      intro cell hok
      obtain ⟨hkeys, himm, hlen⟩ := DeferredStore.register_keys s.deferreds cell fiber token
      have hle : s.le { s with deferreds := (s.deferreds.register cell fiber token).1 } :=
        ⟨Nat.le_refl _, hlen, fun _ hh => hh, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩
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
      | registerSleep millis =>
        -- the sleep is a waiter on the timer list, which holds no handle of the world
        simp only [interpOf]
        exact ⟨⟨Nat.le_refl _, Nat.le_refl _, fun _ hh => hh, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩,
          Ok_of_subset (by sub_tac) hok⟩
      | restore _ | merge _ | seq _ | joinOn _ | interruptWith _ | doneInto _ | constant _ | exitOfValue
      | snapshotThen _ | cancelAwait _ | cancelSleep | externalRegister _ | abortController | cancelPark
      | cancelRace _ | withWaiter _ _ _ | reFail _ | finalizerName _ | closeSeq _ _ _ | closeParDone
      | closeIfLast _ =>
        simp only [interpOf]
        exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
    | external op request =>
      cases op with
      | external i =>
        simp only [interpOf]
        split
        · exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
        · cases hq : s.externals.answers with
          | nil =>
            simp only [hq]
            exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
          | cons answer rest =>
            simp only [hq]
            split
            · rename_i ha
              have hinput : Ok ⟨ids, s⟩ (answer.keys ++ s.keys) := by
                rw [externalAdmits_keys table i answer s.externals.allocated ha]
                exact Ok_of_subset (by sub_tac) hok
              exact prepareExternalAnswer_minted table
                (some (.async (.external (.external i) request) false none)) answer s ids hinput
            · exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
      | _ =>
        simp only [interpOf]
        exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
    | cont p | caught p | caughtError p | onValue p | onCause p | fin p | restore e | merge e | gen p pc bind | loop p
    | cancelAwait cell | withWaiter base waiter token' | abort | reFail c | scopeOpen p | scopeProvide p sc
    | scopeBody p previous | scopedExit previous scope | scopeClose scope | restoreCtx previous | constant w
    | forkScopedIn p | acquireCtx p | acquireIn p ctx | acquired p ctx sc' | afterScopeAdd a finalizer
    | releaseUnder p ctx e | releaseBody p e previous
    | provideLayerWith p | provideLayerBody p | updateThen u body | bodyThen body previous
    | buildWithScopeFromContext q scope' | withMemoMapThen q scope' | addCurrentMemoMap mm
    | fromBuildThen q mm | memoize q mm scope' | awaitPromise cell' | buildIntoLayerScope q mm scope'
    | thenBuildInto q mm layerScope | freshThen q scope' | provideThen q mm scope' mode
    | combineWith mode that | mergeChildren q mm | mergeForkOne q i mm parent forked
    | mergeForkNext q i mm parent forked | mergeAllChildren q mm | mergeAllForkOne q i mm parent forked
    | mergeAllForkNext q i mm parent forked | mergeContexts | serviceLookup key | bindService key
    | orDie =>
      simp only [interpOf]
      exact ⟨Stores.le_refl _, Ok_of_subset (by sub_tac) hok⟩
  answerCode c := by simp only [interpOf]; rw [embed_keys]; exact Machine.completionPrim_keys c
  prepareAnswer := prepareExternalAnswer_minted table
  dueResumes s ids hok := by
    simp only [interpOf]
    obtain ⟨h1, h2⟩ := DeferredStore.drainDue_keys s.deferreds
    have hle : s.le { s with deferreds := (s.deferreds.drainDue).2 } := by
      refine ⟨Nat.le_refl _, ?_, fun _ hh => hh, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩
      simp only [DeferredStore.drainDue]
      exact Nat.le_refl _
    refine ⟨hle, ?_⟩
    have hok' := Ok_mono (World.le_of_state hle) hok
    refine Ok_of_subset ?_ hok'
    have h2' : (s.deferreds.drainDue.1.map (Owed.mapCode embed)).flatMap
        (Owed.keys (primKeys EffName.keys EffThunk.keys)) ⊆ s.deferreds.keys := by
      rw [List.flatMap_map]
      refine List.Subset.trans ?_ h2
      intro x hx
      obtain ⟨d, hd, hxd⟩ := List.mem_flatMap.mp hx
      refine List.mem_flatMap.mpr ⟨d, hd, ?_⟩
      simpa [Owed.keys, Owed.mapCode, embed_keys, programKeys] using hxd
    sub_tac using h1, h2'
  wakeList key phase s ids hok := by
    simp only [interpOf]
    obtain ⟨hk, hle⟩ := Stores.wakeList_keys key phase s
    exact ⟨hle, Ok_of_subset hk (Ok_mono (World.le_of_state hle) hok)⟩
  clockStep millis s ids hok := by
    simp only [interpOf]
    rcases hc : s.timers.clockStep millis (Prim.success Val.unit) with ⟨o, timers⟩
    have hle : s.le { s with timers := timers } :=
      ⟨Nat.le_refl _, Nat.le_refl _, fun _ hk => hk, Nat.le_refl _, (fun _ hm => hm), Nat.le_refl _⟩
    refine ⟨hle, Ok_of_subset ?_ (Ok_mono (World.le_of_state hle) hok)⟩
    cases o with
    | none => simp only [Option.map_none, Option.getD_none, List.append_nil]; exact fun _ h => h
    | some d =>
      obtain ⟨hcode, hmode⟩ := TimerStore.clockStep_owed s.timers millis (Prim.success Val.unit) d
        (by rw [hc])
      simp only [Option.map_some, Option.getD_some, Owed.keys, Owed.mapCode, hcode, hmode,
        embed_keys, primKeys, Val.keys, List.append_nil]
      exact fun _ h => h
  cancelName base fiber token := by simp only [interpOf]; exact List.Subset.refl _
  abortName := rfl
  parkCancelName := rfl
  raceCancelName race := rfl
  parkCode kind := by simp only [interpOf]; sub_tac
  interruptCode target := by simp only [interpOf]; rw [embed_keys]; sub_tac
  interruptAsCode target who := by simp only [interpOf]; rw [embed_keys]; sub_tac
  interruptAllCode targets := by simp only [interpOf]; rw [embed_keys]; sub_tac
  raceSettle race cleanupNeeded exit := by
    simp only [interpOf]; rw [embed_keys]; exact Machine.raceSettleProgram_keys race cleanupNeeded exit
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
  contextValue ctx := by simp only [interpOf, Val.keys_context]; exact List.Subset.refl _
  exitValue e mode := by
    cases mode with
    | awaitValue => simp only [interpOf, primKeys, Machine.reifyExitVal_keys]; exact List.Subset.refl _
    | joinEffect => simp only [interpOf, primKeys_ofExit]; exact List.Subset.refl _
  fiberValue id := by simp only [interpOf, Val.keys_fiber]; exact List.Subset.refl _
  fiberIdValue _ := List.nil_subset _
  fibersValue ids := by simp only [interpOf, Val.keys_fibers]; exact List.Subset.refl _
  exitsValue exits := by simp only [interpOf, Machine.exitsVal_keys]; exact List.Subset.refl _
  voidValue := rfl
  scopeValue scope := by simp only [interpOf]; exact List.Subset.refl _
  closeDoneName := rfl
  ambientScope ctx scope h := by
    simp only [interpOf] at h
    exact Ctx.scope_mem_keys h

/-! ## Fresh source construction over machine-owned exits -/

theorem Point.withCompleted_keys (p : Point) (completed : List (FiberId × ExitV)) :
    ({ p with completed } : Point).keys ⊆
      completed.flatMap (fun entry => exitKeys entry.2) ++ p.keys := by
  sub_tac

-- One declaration, one heartbeat budget, as `interpOf_keyBounded` above: the refreshed hooks
-- are read off `interpAt` by `rfl` where they can be (the three below), the rest unfold it.
set_option maxHeartbeats 800000 in
/-- Source callbacks can additionally use the completed-exit values supplied by
the evaluator. Eager code remains bounded by its captured point. -/
theorem interpAt_keyBounded (root : NativeEff) (completed : List (FiberId × ExitV)) (table : RowTable := []) :
    KeyBounded EffName.keys EffThunk.keys (interpAt root completed table)
      (completed.flatMap fun entry => exitKeys entry.2) where
  contA n v := by
    have h : (interpAt root completed table).contA n v = contAOf root (match n with
        | .cont p => .cont { p with completed }
        | .onValue p => .onValue { p with completed }
        | .releaseBody p exit previous => .releaseBody { p with completed } exit previous
        | name => name) v := rfl
    rw [h]
    refine List.Subset.trans (contAOf_native_keys root _ v) ?_
    cases n <;> sub_tac
  contE n c := by
    have h : (interpAt root completed table).contE n c = contEOf root (match n with
        | .caught p => .caught { p with completed }
        | .caughtError p => .caughtError { p with completed }
        | .onCause p => .onCause { p with completed }
        | name => name) c := rfl
    rw [h]
    refine List.Subset.trans (contEOf_native_keys root _ c) ?_
    cases n <;> sub_tac
  suspendBody t := by
    have h : (interpAt root completed table).suspendBody t = suspendBodyAt root (match t with
        | .body p => .body { p with completed }
        | thunk => thunk) := rfl
    rw [h]
    refine List.Subset.trans (suspendBodyAt_keys root _) ?_
    cases t <;> sub_tac
  iterNext_done n v r h := by
    cases n with
    | gen p pc bind =>
      simp only [interpAt] at h
      have hs := runStmts_keys root { p with completed }
        (completed.flatMap (fun entry => exitKeys entry.2) ++ p.keys ++ v.keys)
        p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (List.Subset.trans (point_bind_keys { p with completed } v bind) (by sub_tac))
      rw [h] at hs
      simpa only [StepKeys, EffName.keys, List.append_assoc] using hs
    | store name =>
      simp only [interpAt] at h
      have hs := stores_keyBounded.iterNext_done name v r (embedStep_done h)
      simp only [List.nil_append] at hs
      exact List.Subset.trans hs (List.subset_append_right _ _)
    | _ =>
      simp only [interpAt, IterStep.done.injEq] at h
      subst h
      sub_tac
  iterNext_resume n v next n' h := by
    cases n with
    | gen p pc bind =>
      simp only [interpAt] at h
      have hs := runStmts_keys root { p with completed }
        (completed.flatMap (fun entry => exitKeys entry.2) ++ p.keys ++ v.keys)
        p.fuel pc (if bind then p.env ++ [v] else p.env) []
        (List.Subset.trans (point_bind_keys { p with completed } v bind) (by sub_tac))
      rw [h] at hs
      simpa only [StepKeys, EffName.keys, List.append_assoc] using hs
    | store name =>
      simp only [interpAt] at h
      obtain ⟨next0, n0, hstep, rfl, rfl⟩ := embedStep_resume h
      have hs := stores_keyBounded.iterNext_resume name v next0 n0 hstep
      simp only [List.nil_append] at hs
      simp only [embed_keys, EffName.keys]
      exact List.Subset.trans hs (List.subset_append_right _ _)
    | _ => simp only [interpAt] at h; cases h
  loopBody n c := by
    cases n with
    | loop p =>
      exact List.Subset.trans
        (resolve_keys root ({ p with completed }.childWith 0 c)) (by sub_tac)
    | _ => simp only [interpAt]; sub_tac
  finalizerProgram n e code h := by
    cases n with
    | fin p =>
      simp only [interpAt, Option.some.injEq] at h
      subst code
      refine List.Subset.trans (resolve_keys root _) ?_
      rw [Point.childWith_keys, Machine.reifyExitVal_keys]
      sub_tac
    | _ =>
      simp only [interpAt] at h
      exact List.Subset.trans ((interpOf_keyBounded root).finalizerProgram _ e code h)
        (List.subset_append_right _ _)
  syncValue := (interpOf_keyBounded root table).syncValue
  reifyExit := (interpOf_keyBounded root table).reifyExit
  loopStep := (interpOf_keyBounded root table).loopStep
  loopDone := (interpOf_keyBounded root table).loopDone
  cancelThenFail := (interpOf_keyBounded root table).cancelThenFail
  parkOf := (interpOf_keyBounded root table).parkOf
  parkCode := (interpOf_keyBounded root table).parkCode
  parkOfAwaitAll := (interpOf_keyBounded root table).parkOfAwaitAll
  interruptCode := (interpOf_keyBounded root table).interruptCode
  interruptAsCode := (interpOf_keyBounded root table).interruptAsCode
  interruptAllCode := (interpOf_keyBounded root table).interruptAllCode
  withFiberOf := (interpOf_keyBounded root table).withFiberOf
  syncState := (interpOf_keyBounded root table).syncState
  registerAsync := (interpOf_keyBounded root table).registerAsync
  answerCode := (interpOf_keyBounded root table).answerCode
  prepareAnswer := (interpOf_keyBounded root table).prepareAnswer
  dueResumes := (interpOf_keyBounded root table).dueResumes
  wakeList := (interpOf_keyBounded root table).wakeList
  clockStep := (interpOf_keyBounded root table).clockStep
  cancelName := (interpOf_keyBounded root table).cancelName
  abortName := (interpOf_keyBounded root table).abortName
  parkCancelName := (interpOf_keyBounded root table).parkCancelName
  raceCancelName := (interpOf_keyBounded root table).raceCancelName
  raceSettle := (interpOf_keyBounded root table).raceSettle
  restoreName := (interpOf_keyBounded root table).restoreName
  mergeName := (interpOf_keyBounded root table).mergeName
  scopeStatus := (interpOf_keyBounded root table).scopeStatus
  scopeLinkFiber := (interpOf_keyBounded root table).scopeLinkFiber
  dropFinalizer := (interpOf_keyBounded root table).dropFinalizer
  closeScope := (interpOf_keyBounded root table).closeScope
  emptyContext := (interpOf_keyBounded root table).emptyContext
  contextValue := (interpOf_keyBounded root table).contextValue
  exitValue := (interpOf_keyBounded root table).exitValue
  fiberValue := (interpOf_keyBounded root table).fiberValue
  fiberIdValue := (interpOf_keyBounded root table).fiberIdValue
  fibersValue := (interpOf_keyBounded root table).fibersValue
  exitsValue := (interpOf_keyBounded root table).exitsValue
  voidValue := (interpOf_keyBounded root table).voidValue
  scopeValue := (interpOf_keyBounded root table).scopeValue
  closeDoneName := (interpOf_keyBounded root table).closeDoneName
  ambientScope := (interpOf_keyBounded root table).ambientScope

/-- Ordinary native evaluation uses only the machine's existing completed exits. -/
theorem evaluatePrimAt_minted (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m
      (Handle.fiber f.id :: m.keys EffName.keys EffThunk.keys ++ f.keys EffName.keys EffThunk.keys)) (table : RowTable := []) :
    IterMinted EffName.keys EffThunk.keys m
      (evaluatePrim (interpAt root m.completedExits table) m f yielding) := by
  apply evaluatePrim_minted_with_ambient EffName.keys EffThunk.keys
    (interpAt_keyBounded root m.completedExits table) m f yielding
  apply Ok_append.mpr
  refine ⟨?_, hm⟩
  exact Ok_of_subset (RunMachine.completedExits_keys EffName.keys EffThunk.keys m)
    (Ok_of_subset (by sub_tac) hm)

/-! ## Atomic scoped entry and exit

The close snapshot's and the unsafe close's key bounds (`scopeCloseSnapshot_keys`,
`storesCloseScopeUnsafe_keys`) live with the stores' interpreter in `Machine/Handles`
since §20, where the stores' own `closeScope` bound needs them. -/

/-- Scoped entry allocates its scope and carries the already captured body and
previous context (`internal/effect.ts:3938-3948`). -/
theorem enterScoped_minted (root : NativeEff) (p : Point) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m
      (m.keys EffName.keys EffThunk.keys ++ f.keys EffName.keys EffThunk.keys ++ p.keys)) :
    IterMinted EffName.keys EffThunk.keys m (enterScoped root p m f yielding) := by
  let state := { m.state with
    scopes := m.state.scopes.make m.state.nextName .sequential
    nextName := m.state.nextName + 1 }
  have hstep : syncOpStep (.scopeMake .sequential) m.state =
      some (state, .scopeHandle m.state.nextName) := rfl
  have hle := syncOpStep_le _ _ _ _ hstep
  have hworld : m.world.le ⟨m.fibers.map RunFiber.id, state⟩ := World.le_of_state hle
  have hnew := syncOpStep_keys _ _ _ _ (m.fibers.map RunFiber.id) hstep
    (Ok_of_subset (by sub_tac) hm)
  have hold := Ok_mono hworld hm
  unfold enterScoped IterMinted
  refine ⟨hworld, ?_⟩
  refine Ok_of_subset ?_ (Ok_append.mpr ⟨hold, hnew⟩)
  sub_tac using (resolve_keys root (p.child 0)), (Ctx.keys_withScope f.context m.state.nextName)
    norm [state, Point.keys, Point.child, EffName.keys, EffThunk.keys]

/-- Scoped exit uses the answering frame's captured context and the scope's stored
finalizers, after applying the real pop (`internal/effect.ts:3944-3947`). -/
theorem exitScoped_minted (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool) (exit : ExitV)
    (hm : MintedIn m
      (Handle.fiber f.id :: m.keys EffName.keys EffThunk.keys ++
        f.keys EffName.keys EffThunk.keys ++ exitKeys exit)) :
    IterMinted EffName.keys EffThunk.keys m (exitScoped root m f yielding exit) := by
  unfold exitScoped
  dsimp only
  split
  · next body previous scope flag hpop =>
    have hg := getCont_answer_frame_keys EffName.keys EffThunk.keys f.frame _ _ _ hpop
    simp only [primKeys, List.append_subset] at hg
    have hF : Ok m.world (frameKeys EffName.keys EffThunk.keys f.frame) :=
      Ok_of_subset (by sub_tac) hm
    have hname : Ok m.world (Handle.scope scope :: previous.keys) := Ok_of_subset hg.1.2 hF
    have hpopf := Ok_of_subset hg.2 hF
    have hall := Ok_append.mpr ⟨Ok_append.mpr ⟨hm, hname⟩, hpopf⟩
    split
    · unfold IterMinted
      refine ⟨by rw [world_emit]; exact World.le_refl _, ?_⟩
      simp only [MintedIn]
      rw [world_emit]
      refine Ok_of_subset ?_ hall
      sub_tac
    · next state program hclose =>
      obtain ⟨hle, hkeys⟩ := storesCloseScopeUnsafe_keys scope exit _ m.state state program hclose
      have hworld : m.world.le ⟨m.fibers.map RunFiber.id, state⟩ := World.le_of_state hle
      have hold := Ok_mono hworld hall
      have hclosed : Ok ⟨m.fibers.map RunFiber.id, state⟩
          (program.toList.flatMap programKeys ++ state.keys) :=
        Ok_of_subset hkeys (Ok_mono hworld (Ok_of_subset (by sub_tac) hm))
      cases program with
      | none =>
        unfold IterMinted
        refine ⟨hworld, ?_⟩
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hold, hclosed⟩)
        sub_tac norm [primKeys_ofExit]
      | some program =>
        unfold IterMinted
        refine ⟨hworld, ?_⟩
        refine Ok_of_subset ?_ (Ok_append.mpr ⟨hold, hclosed⟩)
        cases exit <;> simp only [finalizerCode, interpAt, interpOf] <;>
          sub_tac norm [embed_keys]
  · exact evaluatePrimAt_minted root m f yielding (Ok_of_subset (by sub_tac) hm)

/-- The native evaluator's scoped cases and ordinary callback cases share one
handle conclusion; the command/replay proof is unchanged. -/
theorem evaluateNative_minted (root : NativeEff) (m : Api.Machine)
    (f : RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx) (yielding : Bool)
    (hm : MintedIn m
      (Handle.fiber f.id :: m.keys EffName.keys EffThunk.keys ++ f.keys EffName.keys EffThunk.keys)) (table : RowTable := []) :
    IterMinted EffName.keys EffThunk.keys m (evaluateNative root m f yielding table) := by
  unfold evaluateNative
  split
  · next p hcurrent =>
    split
    · apply enterScoped_minted root p m f yielding
      refine Ok_of_subset ?_ hm
      sub_tac norm [hcurrent]
    · exact evaluatePrimAt_minted root m f yielding hm table
  · next value hcurrent =>
    apply exitScoped_minted root m f yielding (.success value)
    refine Ok_of_subset ?_ hm
    sub_tac norm [hcurrent]
  · next cause hcurrent =>
    apply exitScoped_minted root m f yielding (.failure cause)
    refine Ok_of_subset ?_ hm
    sub_tac norm [hcurrent]
  · exact evaluatePrimAt_minted root m f yielding hm table

/-- The runtime view and native scope protocol use only existing or freshly
allocated handles. The shared evaluator transport gives the public replay claim. -/
theorem evaluatorFor_minted (root : NativeEff) (table : RowTable := []) :
    letI := evaluatorFor root table
    EvaluatorMinted EffName.keys EffThunk.keys (interpOf root table) := by
  intro m f yielding hm
  exact evaluateNative_minted root m f yielding (Ok_of_subset (by sub_tac) hm) table

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
  letI := evaluatorFor program
  AnswersValidAt (interpOf program) fuel tape (Api.load program fuel choices)

instance (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool) :
    Decidable (AnswersValid program fuel tape choices) := by
  unfold AnswersValid
  infer_instance

theorem Api.replay_machine (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool) :
    letI := evaluatorFor program
    (Api.replay program fuel tape choices).machine =
      (replayEval (interpOf program) fuel tape (Api.load program fuel choices)).machine := by
  letI := evaluatorFor program
  unfold Api.replay
  cases replayEval (interpOf program) fuel tape (Api.load program fuel choices) <;> rfl

/-- A loaded program holds no handle: a literal is a unit, a number or a boolean, and the root
point has nothing in scope. -/
theorem load_minted (program : Api.Program) (fuel : Nat) (choices : List Bool := [])
    (answers : List (Completion Val Err Defect FiberId Ann) := []) :
    Minted (Api.load program fuel choices answers) := by
  have hcode : nativeKeys (compile program fuel choices) ⊆ [] := compileEff_keys program (rootPoint fuel choices)
  have hmake := make_keys_subset (nk := EffName.keys) (sk := EffThunk.keys) Api.root (compile program fuel choices)
    true (stores.budgetOf emptyCtx) emptyCtx
  have hfiber : (RunFiber.make Api.root (compile program fuel choices) true (stores.budgetOf emptyCtx) emptyCtx :
      RunFiber EffName EffThunk Val Err Defect FiberId Ann Ctx).keys EffName.keys EffThunk.keys ⊆ [] :=
    List.Subset.trans hmake (List.append_subset.mpr ⟨hcode, List.Subset.refl _⟩)
  unfold Minted MintedAt MintedIn
  refine Ok_of_subset (b := []) ?_ (Ok_nil _)
  have hempty : ({ Stores.empty with externals := ExternalStore.ofAnswers answers } : Stores).keys = [] := rfl
  simp only [Api.load, Api.compile, RunMachine.keys, RunMachine.empty, List.flatMap_cons,
    List.flatMap_nil, List.map_nil, List.append_nil, hempty]
  exact hfiber

/-- The handle invariant (C13, `handles_minted`): a minted machine replayed on a tape whose
external answers are valid stays minted. -/
theorem handles_minted (program : Api.Program) (fuel : Nat) (tape : List Api.Decision) (choices : List Bool)
    (h : Minted (Api.load program fuel choices) ∧ AnswersValid program fuel tape choices) :
    Minted (Api.replay program fuel tape choices).machine := by
  letI := evaluatorFor program
  rw [Api.replay_machine]
  exact (replayEval_minted_of_evaluator EffName.keys EffThunk.keys (interpOf_keyBounded program)
    (evaluatorFor_minted program) fuel tape _ h.2 h.1).2

/-- A run returned by checked replay has only live collected handles, for the supplied table
and oracle. The unconsumed oracle remains input data; admission checks it before use. -/
theorem checked_replay_minted (program : Api.Program) (fuel : Nat) (tape : List Api.Decision)
    (choices : List Bool) (answers : List (Completion Val Err Defect FiberId Ann))
    (table : RowTable) (run : Api.Run)
    (h : Api.replayChecked program fuel tape choices answers table = .inl run) :
    Minted run.machine := by
  letI := evaluatorFor program table
  cases hc : replayCheckedFrom program fuel answers table 0 tape
      (Api.load program fuel choices answers) with
  | inr refusal => simp [Api.replayChecked, hc] at h
  | inl result =>
    have hv := replayCheckedFrom_answersValid program fuel answers table 0 tape _ result hc
    have he := replayCheckedFrom_eq_replay program fuel answers table 0 tape _ result hc
    have hm := (replayEval_minted_of_evaluator EffName.keys EffThunk.keys
      (interpOf_keyBounded program table) (evaluatorFor_minted program table) fuel tape _ hv
      (load_minted program fuel choices answers)).2
    rw [← he] at hm
    cases result <;> simp only [Api.replayChecked, hc, Sum.inl.injEq] at h <;> cases h <;> exact hm

end Effect4.Program
