import Effect4.Laws.Machine.Handles
import Effect4.Api
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.Admit
import Effect4.Laws.Program.Agreement

/-!
# The handle invariant at the compiled alphabet — Alphabet

The native alphabet (`EffName`, `EffThunk`, `Point`, `Region`), its handle collection functions,
custom `sub_tac` normalization, and the embedding theorems for the stores' programs.
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

end Effect4.Program
