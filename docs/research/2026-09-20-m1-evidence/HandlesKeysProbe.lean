import Effect4.Laws.Machine.Clauses
import Effect4.Laws.Machine.StoresLaws
import Effect4.Laws.Machine.Approximation

/-!
# Collected handles name allocated objects

Packet: `Test/contracts/machine-handles.contract.md`. Node C13 (`handles_minted`, G5) of
`docs/research/2026-09-05-runtime-proof-graph.md`; the worksheet is
`docs/research/2026-09-05-first-slice-worksheets.md` §W3.

A handle is a fiber id, a Ref key, a Deferred key or a scope key. This module collects the
handles that occur in every carrier of the frame-instance machine — values, exits, contexts,
store operations, names and thunks, code by structural recursion, a fiber's frame, pending
parks, observers, children, dispatcher tasks and exit, a race's host, live entrants and
unforked programs, the store's heap, Deferred completions and owed resumes, and the scope
store's finalizer names — and states `MintedAt nk sk m`: every collected handle names a
fiber of `m.fibers`, a heap index, a Deferred cell or a scope entry of `m.state`. The
predicate is decidable. The trace is excluded.

The alphabet of names and thunks is a parameter (`nk`, `sk`): the stores' own alphabet and
the compile's native alphabet are two instances of one invariant. What the interpreter's
hooks may answer is `KeyBounded`: every hook's output names only handles its inputs named,
an explicit ambient list for source callbacks, or ones the store just minted (`syncState`,
`registerAsync`, `scopeLinkFiber`, `closeScope`, `dueResumes`). Ambient handles must exist
in the machine at evaluation. The stores' interpreter is proved `KeyBounded` here (`stores_keyBounded`); the
compile's `interpOf root` is proved in `Effect4.Program.Handles`, where `Minted` on
`Api.Machine` and the top theorem `handles_minted` live.

What is proved: the frame machine's `step` and every helper `drive` reaches (`spawn`,
`start`, `injectYield`, `evaluatePrim` and its `withFiber` arms, `exitFiber`,
`fireObserver`, `launchEntrant`, `linkScope`, `interruptRecord`, `interruptEach`,
`countdownPark`, `settle`, `driveStep`), then `driveState`, `fire`, `flushAll`, `flushRoot`,
`stepDecision` and `replayEval` keep the invariant, under the tape premise `AnswersValidAt`:
every `answerAsync` on the tape names handles that exist in the machine it is answered
against (the C15 `TapeAddressed` reading, the ruling of 2026-09-06 on `E4-HANDLE-CE-001`).
Replay admission is not changed.

Excluded positions: numeric interruptor provenance in deferredInterruptWith and
interruptAll, and the interruptor inside a `Cause` (`Cause.interrupt (some id)`,
provenance that nothing dereferences; the tape's `interruptFrom` may name any fiber); the
race's duplicate winner, failure reasons and
bookkeeping fields other than `live` and `accepted`; and Deferred waiter and due-resume
targets. The latter become command targets: `driveStep` ignores unknown resume targets,
while the separately collected completion code is what can enter a frame. `Cmd.keys`
likewise collects resume code and finished exits, not target identifiers. The predicate
does not certify every identifier stored anywhere in the machine.
-/

set_option autoImplicit false

namespace Effect4.Machine

open Effect4

/-! ## Handles and their occurrences -/

/-- What a value can name that must have been minted. -/
inductive Handle
  | fiber (id : FiberId)
  | cell (key : RefKey)
  | promise (key : DeferredKey)
  | scope (key : Nat)
  /-- A memo map (`Layer.ts:421-458`; the join). -/
  | memoMap (id : Nat)
  | external (key : Nat)
deriving DecidableEq, Repr

/-- The kind byte and index of a handle: the `handle` frame's payload, `Store.Val.handles`'
entry for it (`HandleKind`, `Machine/Value.lean`). -/
def Handle.code : Handle → UInt8 × Nat
  | .fiber id => (1, id.value)
  | .cell key => (2, key.index)
  | .promise key => (3, key.index)
  | .scope key => (4, key)
  | .memoMap id => (5, id)
  | .external key => (7, key)

/-- The handle of a kind byte and index: the five minted kinds (`memoMap` since the join); an
unregistered byte is no handle. -/
def Handle.ofCode (code : UInt8 × Nat) : Option Handle :=
  match HandleKind.ofByte? code.1 with
  | some .fiber => some (.fiber ⟨code.2⟩)
  | some .cell => some (.cell ⟨code.2⟩)
  | some .promise => some (.promise ⟨code.2⟩)
  | some .scope => some (.scope code.2)
  | some .memoMap => some (.memoMap code.2)
  | some .external => some (.external code.2)
  | none => none

theorem Handle.ofCode_code (h : Handle) : Handle.ofCode h.code = some h := by
  cases h <;> rfl

/-- A code that reads back is the handle's own. -/
theorem Handle.code_ofCode {code : UInt8 × Nat} {h : Handle} (hc : Handle.ofCode code = some h) :
    h.code = code := by
  unfold Handle.ofCode at hc
  split at hc <;> first
    | (next hk =>
        injection hc with hc
        subst hc
        have h1 : code.1 = _ := HandleKind.ofByte?_exact hk
        exact Prod.ext h1.symm rfl)
    | exact nomatch hc

theorem Handle.ofCode_fiber (index : Nat) : Handle.ofCode (1, index) = some (.fiber ⟨index⟩) :=
  by aesop
theorem Handle.ofCode_cell (index : Nat) : Handle.ofCode (2, index) = some (.cell ⟨index⟩) :=
  by aesop
theorem Handle.ofCode_promise (index : Nat) :
    Handle.ofCode (3, index) = some (.promise ⟨index⟩) :=
  by aesop
theorem Handle.ofCode_scope (index : Nat) : Handle.ofCode (4, index) = some (.scope index) :=
  by aesop
theorem Handle.ofCode_memoMap (index : Nat) : Handle.ofCode (5, index) = some (.memoMap index) :=
  by aesop

mutual
/-- The handles of a value: every `handle` frame the carrier carries, read through
`Handle.ofCode`, in payload order — the handle arms, the snapshot's members, a context's
service values, a reified exit's value and the members of a list. A reified failed exit carries
a cause only (`Val.keys_exitErr`); an unregistered byte is not counted. `Val.keys_eq_handles` is the migration check (U1): this is
`Store.Val.handles` filtered. -/
def Val.keys : Val → List Handle
  | .handle kind index => (Handle.ofCode (kind, index)).toList
  | .list values => Val.keysList values
  | .pair a b => Val.keys a ++ Val.keys b
  | .some a => Val.keys a
  | .ctor _ args => Val.keysList args
  | _ => []
/-- The handles of a list of values, back to back. -/
def Val.keysList : List Val → List Handle
  | [] => []
  | value :: rest => Val.keys value ++ Val.keysList rest
end

theorem Val.keysList_eq_flatMap (values : List Val) :
    Val.keysList values = values.flatMap Val.keys := by
  induction values with
  | nil => rfl
  | cons value rest ih => rw [Val.keysList, List.flatMap_cons, ih]

theorem Val.keys_list (values : List Val) : Val.keys (Val.list values) = values.flatMap Val.keys :=
  Val.keysList_eq_flatMap values

theorem Val.keys_fiber (id : FiberId) : (Val.fiber id).keys = [Handle.fiber id] :=
  by aesop
theorem Val.keys_cell (key : RefKey) : (Val.cell key).keys = [Handle.cell key] :=
  by aesop
theorem Val.keys_promise (key : DeferredKey) : (Val.promise key).keys = [Handle.promise key] :=
  by aesop
theorem Val.keys_scopeHandle (key : Nat) : (Val.scopeHandle key).keys = [Handle.scope key] :=
  by aesop
theorem Val.keys_memoMap (id : MemoMapId) : (Val.memoMap id).keys = [Handle.memoMap id.index] :=
  by aesop

theorem Val.keys_exitOk (v : Val) : Val.keys (Val.exitOk v) = v.keys := by
  simp only [Val.keys, Val.keysList, List.append_nil]

theorem Val.keysList_eq_handlesList (values : List Val)
    (ih : ∀ x ∈ values, x.keys = x.handles.filterMap Handle.ofCode) :
    Val.keysList values = (Store.Val.handlesList values).filterMap Handle.ofCode := by
  induction values with
  | nil => rfl
  | cons value rest ihr =>
    rw [Val.keysList, Store.Val.handlesList_cons, List.filterMap_append, ih value (by simp),
      ihr (fun x hx => ih x (by simp [hx]))]

/-- The migration check (U1): the handles a value names are the carrier's `handle` frames
read through `Handle.ofCode`. -/
theorem Val.keys_eq_handles (v : Val) : v.keys = v.handles.filterMap Handle.ofCode := by
  induction v using Store.Val.ind with
  | unit => rfl
  | bool _ => rfl
  | nat _ => rfl
  | str _ => rfl
  | bytes _ => rfl
  | none => rfl
  | ref _ _ => rfl
  | handle kind index =>
    show (Handle.ofCode (kind, index)).toList = List.filterMap Handle.ofCode [(kind, index)]
    rw [List.filterMap_cons, List.filterMap_nil]
    generalize Handle.ofCode (kind, index) = r
    cases r <;> rfl
  | list values ih => exact Val.keysList_eq_handlesList values ih
  | pair a b iha ihb =>
    show Val.keys a ++ Val.keys b = List.filterMap Handle.ofCode (a.handles ++ b.handles)
    rw [List.filterMap_append, iha, ihb]
  | some a ih => exact ih
  | ctor _ args ih => exact Val.keysList_eq_handlesList args ih

/-- A reified failed exit carries a cause only: the cause image writes no handle. -/
theorem Val.keys_exitErr (cause : CauseV) : (Val.exitErr cause).keys = [] := by
  rw [Val.keys_eq_handles]
  show List.filterMap Handle.ofCode (Store.Val.handles (.ctor 1 [causeImage.toVal cause])) = []
  rw [Store.Val.handles, Store.Val.handlesList_cons, causeImage_handleFree cause,
    Store.Val.handlesList_nil]
  rfl

/-- The handles a service map holds: those of every service value. -/
def Env.Context.handleKeys (c : Env.Ctx) : List Handle :=
  c.entries.flatMap fun s => Val.keys s.valueVal

/-- The handles a context holds: those of every service value — a scope handle under
`scopeKey`, anything a program provided; a memo-map handle is not counted
(`Handle.ofCode_memoMap`). Before the join the one handle was the cached ambient scope. -/
def Ctx.keys (ctx : Ctx) : List Handle :=
  ctx.services.entries.flatMap fun s => Val.keys s.valueVal

theorem Ctx.keys_eq_handleKeys (ctx : Ctx) : ctx.keys = Env.Context.handleKeys ctx.services :=
  by aesop

/-- A written entry's handles are its value's: the key's image is handle-free. -/
theorem Val.keys_entryStore (key : ServiceKey) (value : Val) :
    Val.keys (Env.entryStore key value) = value.keys :=
  by aesop

theorem Val.keysList_entryStore :
    ∀ es : List (Env.Service Env.ValU),
      Val.keysList (es.map fun s => Env.entryStore s.key s.valueVal) =
        es.flatMap fun s => Val.keys s.valueVal
  | [] => rfl
  | s :: rest => by
    rw [List.map_cons, Val.keysList, Val.keys_entryStore, List.flatMap_cons,
      Val.keysList_entryStore rest]

theorem Val.keys_context (ctx : Ctx) : (Val.context ctx).keys = ctx.keys := by
  show Val.keys (Env.encode ctx.services) ++ (Val.keys (Store.Val.nat ctx.maxOpsBeforeYield) ++
    (Val.keys (Store.Val.bool ctx.preventYield) ++ [])) = _
  show Val.keysList (ctx.services.entries.map fun s => Env.entryStore s.key s.valueVal) ++
    ([] ++ ([] ++ [])) = _
  rw [Val.keysList_entryStore]
  simp only [List.append_nil]
  rfl

/-- The ambient scope a context answers is a handle it holds. -/
theorem Ctx.scope_mem_keys {ctx : Ctx} {scope : Nat} (h : ctx.ambientScope = some scope) :
    Handle.scope scope ∈ ctx.keys := by
  unfold Ctx.ambientScope Env.ambientScope at h
  cases hv : ctx.services.getV Env.scopeKey with
  | none =>
    rw [hv] at h
    exact nomatch h
  | some v =>
    rw [hv] at h
    have hv' : v = Env.Val.scopeHandle scope := Env.scopeOfVal_some h
    obtain ⟨s, hs, _, hval⟩ := Env.Context.getV_mem hv
    unfold Ctx.keys
    rw [List.mem_flatMap]
    refine ⟨s, hs, ?_⟩
    rw [hval, hv']
    show Handle.scope scope ∈ [Handle.scope scope]
    exact List.mem_singleton.mpr rfl

/-- `scoped`'s install adds the scope's handle and drops at most the previous one. -/
theorem Ctx.keys_withScope (c : Ctx) (scope : Nat) :
    (c.withScope scope).keys ⊆ Handle.scope scope :: c.keys := by
  show (Env.Context.setEntries (U := Env.ValU) Env.scopeKey (Value.scope scope)
    c.services.entries).flatMap (fun s => Val.keys s.valueVal) ⊆ _
  intro x hx
  rcases List.mem_append.mp (Env.Context.flatMap_setEntries_subset _ _ _ _ hx) with h | h
  · exact List.mem_cons.mpr (Or.inl (List.mem_singleton.mp h))
  · exact List.mem_cons_of_mem _ h

/-- A region write's handles: the value's, and the previous map's. -/
theorem Ctx.keys_provide (c : Ctx) (key : ServiceKey) (value : Val) :
    (c.provide key value).keys ⊆ value.keys ++ c.keys := by
  show (Env.Context.setEntries (U := Env.ValU) key value c.services.entries).flatMap
    (fun s => Val.keys s.valueVal) ⊆ _
  intro x hx
  exact Env.Context.flatMap_setEntries_subset _ _ _ _ hx

/-! ### The service map's handles (the join): `encode`, `add`, `merge`, `mergeAll`, `decode` -/

/-- A written service map's handles are its values' (`Val.keys_context`'s first half). -/
theorem Val.keys_encode (c : Env.Ctx) : Val.keys (Env.encode c) = Env.Context.handleKeys c := by
  show Val.keysList (c.entries.map fun s => Env.entryStore s.key s.valueVal) = _
  rw [Val.keysList_entryStore]
  rfl

theorem Env.Context.handleKeys_empty : Env.Context.handleKeys Env.Context.empty = [] :=
  by aesop

theorem Ctx.keys_withServices (s : Env.Ctx) :
    (Ctx.withServices s).keys = Env.Context.handleKeys s :=
  by aesop

/-- `Context.add`'s handles: the value's, and the previous map's. -/
theorem Env.Context.handleKeys_add (c : Env.Ctx) (key : ServiceKey)
    (value : ServiceKey.Carrier Env.ValU key) :
    Env.Context.handleKeys (c.add key value) ⊆ Val.keys value ++ Env.Context.handleKeys c := by
  show (Env.Context.setEntries (U := Env.ValU) key value c.entries).flatMap
    (fun s => Val.keys s.valueVal) ⊆ _
  intro x hx
  exact Env.Context.flatMap_setEntries_subset _ _ _ _ hx

theorem Env.Context.handleKeys_addV (c : Env.Ctx) (key : ServiceKey) (value : Val) :
    Env.Context.handleKeys (c.addV key value) ⊆ Val.keys value ++ Env.Context.handleKeys c :=
  Env.Context.handleKeys_add c key value

theorem Env.Context.handleKeys_mergeEntries (self : Env.Ctx) :
    ∀ es : List (Env.Service Env.ValU),
      Env.Context.handleKeys (Env.Context.mergeEntries self es) ⊆
        Env.Context.handleKeys self ++ es.flatMap fun s => Val.keys s.valueVal
  | [] => by
    simp only [Env.Context.mergeEntries, List.flatMap_nil, List.append_nil]
    exact List.Subset.refl _
  | s :: rest => by
    simp only [Env.Context.mergeEntries, List.flatMap_cons]
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_mergeEntries (self.add s.key s.value) rest hx)
      with h | h
    · rcases List.mem_append.mp (Env.Context.handleKeys_add self s.key s.value h) with h | h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
      · exact List.mem_append_left _ h
    · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- `Context.merge`'s handles: both maps'. -/
theorem Env.Context.handleKeys_merge (a b : Env.Ctx) :
    Env.Context.handleKeys (a.merge b) ⊆ Env.Context.handleKeys a ++ Env.Context.handleKeys b :=
  Env.Context.handleKeys_mergeEntries a b.entries

theorem Env.Context.handleKeys_foldl_merge : ∀ (cs : List Env.Ctx) (acc : Env.Ctx),
    Env.Context.handleKeys (cs.foldl Env.Context.merge acc) ⊆
      Env.Context.handleKeys acc ++ cs.flatMap Env.Context.handleKeys
  | [], acc => by
    simp only [List.foldl_nil, List.flatMap_nil, List.append_nil]
    exact List.Subset.refl _
  | c :: rest, acc => by
    simp only [List.foldl_cons, List.flatMap_cons]
    intro x hx
    rcases List.mem_append.mp (Env.Context.handleKeys_foldl_merge rest (acc.merge c) hx) with h | h
    · rcases List.mem_append.mp (Env.Context.handleKeys_merge acc c h) with h | h
      · exact List.mem_append_left _ h
      · exact List.mem_append_right _ (List.mem_append_left _ h)
    · exact List.mem_append_right _ (List.mem_append_right _ h)

/-- `Context.mergeAll`'s handles: every map's. -/
theorem Env.Context.handleKeys_mergeAll : ∀ cs : List Env.Ctx,
    Env.Context.handleKeys (Env.Context.mergeAll cs) ⊆ cs.flatMap Env.Context.handleKeys
  | [] => List.nil_subset _
  | c :: rest => by
    simp only [Env.Context.mergeAll, List.flatMap_cons]
    exact Env.Context.handleKeys_foldl_merge rest c

/-- A decoded map's handles are the value's. -/
theorem Env.decode_keys {v : Val} {c : Env.Ctx} (h : Env.decode v = some c) :
    Env.Context.handleKeys c ⊆ Val.keys v := by
  rw [Env.decode_exact h, Val.keys_encode]
  exact List.Subset.refl _

/-- A service the map answers is a value it holds: its handles are the map's. -/
theorem Env.Context.getV_keys {c : Env.Ctx} {key : ServiceKey} {value : Val}
    (h : c.getV key = some value) : Val.keys value ⊆ Env.Context.handleKeys c := by
  obtain ⟨s, hs, _, hval⟩ := Env.Context.getV_mem h
  intro x hx
  unfold Env.Context.handleKeys
  rw [List.mem_flatMap]
  refine ⟨s, hs, ?_⟩
  rw [hval]
  exact hx

theorem Val.keys_fibers (ids : List FiberId) : (Val.fibers ids).keys = ids.map Handle.fiber := by
  show Val.keysList [Store.Val.list (ids.map fun id => Value.fiber id.value)] = _
  rw [Val.keysList, Val.keysList, List.append_nil]
  show Val.keysList (ids.map fun id => Value.fiber id.value) = _
  induction ids with
  | nil => rfl
  | cons id rest ih =>
    rw [List.map_cons, Val.keysList, ih]
    rfl

/-- The two forms the structural equations can leave when they fire before the spelled
lemmas: a written cause names nothing, a written snapshot payload names its fibers. Both are
in the key normalisation below so either path converges. -/
theorem Val.keys_causeImage (cause : CauseV) : Val.keys (causeImage.toVal cause) = [] := by
  rw [Val.keys_eq_handles, causeImage_handleFree cause]
  rfl

theorem Val.keys_snapshotPayload (ids : List FiberId) :
    Val.keys ((Store.Image.list Value.fiberHandle).toVal ids) = ids.map Handle.fiber := by
  have := Val.keys_fibers ids
  simp only [Val.keys, Val.keysList, List.append_nil] at this
  exact this

/-- The fibers a snapshot's payload reads back to are handles the payload names. -/
theorem Val.snapshotPayload_keys (handles : Val) :
    ((((Store.Image.list Value.fiberHandle).ofVal handles).getD []).map Handle.fiber) ⊆
      handles.keys := by
  cases h : (Store.Image.list Value.fiberHandle).ofVal handles with
  | none => exact List.nil_subset _
  | some ids =>
    rw [(Store.Image.list Value.fiberHandle).ofVal_exact h]
    have := Val.keys_fibers ids
    simp only [Val.keys, Val.keysList, List.append_nil] at this
    rw [this]
    exact List.Subset.refl _

/-- The handles of an exit: its success value's. `Err` and `Defect` carry no value. -/
def exitKeys : ExitV → List Handle
  | Exit.success v => v.keys
  | Exit.failure _ => []

/-- The handles of an optional exit. -/
def optExitKeys : Option ExitV → List Handle
  | some exit => exitKeys exit
  | none => []

/-- The handles an external completion names. -/
def Completion.keys : Completion Val Err Defect FiberId Ann → List Handle
  | Completion.ofExit exit => exitKeys exit
  | Completion.ofRefGet cell => [Handle.cell cell]

/-- The handles of a park: the joined fiber. -/
def ParkKind.keys : ParkKind → List Handle
  | ParkKind.join target _ => [Handle.fiber target]
  -- a race identity is a lookup key, not a dereferenced handle (D6a)
  | ParkKind.race _ => []
  | ParkKind.awaitAll targets => targets.map Handle.fiber

/-- The handles a finalizer name carries. -/
def FinName.keys : FinName → List Handle
  | FinName.interruptFiber fiber _ => [Handle.fiber fiber]
  | FinName.closeChildScope scope => [Handle.scope scope]
  | FinName.detachFromParent parent _ => [Handle.scope parent]
  | FinName.release _ _ => []
  | FinName.awaitNewChildren snapshot => snapshot.map Handle.fiber
  | FinName.parkThen _ => []
  -- a capture holds the values in scope at registration and the context it runs under
  | FinName.foreign capture => Val.keysList capture.env ++ capture.ctx.keys
  | FinName.closeChildOnFailure scope => [Handle.scope scope]
  | FinName.memoEntry _ memoMap => [Handle.memoMap memoMap.index]
  | FinName.memoDone _ memoMap => [Handle.memoMap memoMap.index]

/-- The handles of a store operation: its keys and the values it writes. -/
def SyncOp.keys : SyncOp → List Handle
  | SyncOp.refMake initial => initial.keys
  | SyncOp.refGet cell => [Handle.cell cell]
  | SyncOp.refSet cell value => Handle.cell cell :: value.keys
  | SyncOp.refGetAndSet cell value => Handle.cell cell :: value.keys
  | SyncOp.refSetAndGet cell value => Handle.cell cell :: value.keys
  | SyncOp.refUpdate cell _ => [Handle.cell cell]
  | SyncOp.refGetAndUpdate cell _ => [Handle.cell cell]
  | SyncOp.refUpdateAndGet cell _ => [Handle.cell cell]
  | SyncOp.refUpdateSome cell _ => [Handle.cell cell]
  | SyncOp.refGetAndUpdateSome cell _ => [Handle.cell cell]
  | SyncOp.refUpdateSomeAndGet cell _ => [Handle.cell cell]
  | SyncOp.refModify cell _ => [Handle.cell cell]
  | SyncOp.refModifySome cell _ => [Handle.cell cell]
  | SyncOp.deferredMake => []
  | SyncOp.deferredIsDone cell => [Handle.promise cell]
  | SyncOp.deferredPoll cell => [Handle.promise cell]
  | SyncOp.deferredCompleteWith cell completion => Handle.promise cell :: completion.keys
  | SyncOp.deferredInterruptWith cell _ => [Handle.promise cell]
  | SyncOp.deferredAwaitCleanup cell waiter _ => [Handle.promise cell, Handle.fiber waiter]
  | SyncOp.clockNow => []
  | SyncOp.sleepCancel waiter _ => [Handle.fiber waiter]
  | SyncOp.scopeMake _ => []
  | SyncOp.scopeAdd scope finalizer => Handle.scope scope :: finalizer.keys
  | SyncOp.scopeRemove scope _ => [Handle.scope scope]
  | SyncOp.scopeIsClosed scope => [Handle.scope scope]
  | SyncOp.scopeFork parent _ => [Handle.scope parent]
  | SyncOp.memoFork none => []
  | SyncOp.memoFork (some parent) => [Handle.memoMap parent.index]
  | SyncOp.memoGet _ memoMap => [Handle.memoMap memoMap.index]
  | SyncOp.memoBuild _ memoMap => [Handle.memoMap memoMap.index]
  | SyncOp.memoComplete _ memoMap exit => Handle.memoMap memoMap.index :: exitKeys exit
  | SyncOp.memoRelease _ memoMap => [Handle.memoMap memoMap.index]

/-- The handles of a declared program name, through its bodies. -/
def ProgName.keys : ProgName → List Handle
  | ProgName.value v => v.keys
  | ProgName.failCause _ => []
  | ProgName.syncOp op => op.keys
  | ProgName.yieldNow _ => []
  | ProgName.park _ => []
  | ProgName.awaitDeferred cell => [Handle.promise cell]
  | ProgName.intoDeferred body cell => Handle.promise cell :: body.keys
  | ProgName.intoBody body cell => Handle.promise cell :: body.keys
  | ProgName.maskedPark _ => []
  | ProgName.awaitFibers targets => targets.map Handle.fiber
  | ProgName.finalizerOf fin exit => fin.keys ++ exitKeys exit
  | ProgName.interruptDeferred cell => [Handle.promise cell]
  | ProgName.onExitOf body fin _ => body.keys ++ fin.keys
  | ProgName.seqOf first second => first.keys ++ second.keys
  | ProgName.forkThen child _ _ => child.keys
  | ProgName.forkOnly child _ => child.keys
  | ProgName.forkInScope child _ scope => Handle.scope scope :: child.keys
  | ProgName.runInScope target scope => [Handle.fiber target, Handle.scope scope]
  | ProgName.forkScopedOf child _ => child.keys
  | ProgName.raceOf _ => []
  | ProgName.closeScopeOf scope exit => Handle.scope scope :: exitKeys exit
  | ProgName.awaitAllNew body => body.keys
  | ProgName.interruptFibers targets => targets.map Handle.fiber
  | ProgName.joinFiber target _ => [Handle.fiber target]
  | ProgName.cancelRace _ => []
  | ProgName.closeWalk _ order exit => order.flatMap FinName.keys ++ exitKeys exit

/-- The handles of a continuation, registration or cancel name of the stores' alphabet. -/
def Name.keys : Name → List Handle
  | Name.restore exit => exitKeys exit
  | Name.merge exit => exitKeys exit
  | Name.seq next => next.keys
  | Name.joinOn _ => []
  | Name.interruptWith cell => [Handle.promise cell]
  | Name.doneInto cell => [Handle.promise cell]
  | Name.constant value => value.keys
  | Name.exitOfValue => []
  | Name.snapshotThen body => body.keys
  | Name.registerAwait cell => [Handle.promise cell]
  | Name.cancelAwait cell => [Handle.promise cell]
  | Name.registerSleep _ => []
  | Name.cancelSleep => []
  | Name.externalRegister _ => []
  | Name.abortController => []
  | Name.cancelPark => []
  | Name.cancelRace _ => []
  | Name.withWaiter base waiter _ => Handle.fiber waiter :: base.keys
  | Name.reFail _ => []
  | Name.finalizerName fin => fin.keys
  | Name.closeSeq remaining exit _ => remaining.flatMap FinName.keys ++ exitKeys exit
  | Name.closeParDone => []
  | Name.closeIfLast exit => exitKeys exit

/-- The handles of a `withFiber` action name. -/
def ActionName.keys : ActionName → List Handle
  | ActionName.fork program _ => program.keys
  | ActionName.forkIn program _ scope => Handle.scope scope :: program.keys
  | ActionName.forkScoped program _ => program.keys
  | ActionName.ambientScope => []
  | ActionName.runIn target scope => [Handle.fiber target, Handle.scope scope]
  | ActionName.interrupt target => [Handle.fiber target]
  -- the interruptor is cause data, not a dereferenced handle (`E4-HANDLE-CE-002`)
  | ActionName.interruptAs target _ => [Handle.fiber target]
  | ActionName.interruptScoped target => [Handle.fiber target]
  | ActionName.interruptAll targets _ => targets.map Handle.fiber
  | ActionName.awaitAll targets => targets.map Handle.fiber
  | ActionName.snapshotChildren => []
  | ActionName.awaitNewChildren snapshot => snapshot.map Handle.fiber
  | ActionName.raceAll _ => []
  | ActionName.setContext context => context.keys
  | ActionName.getContext => []
  | ActionName.getId => []
  | ActionName.closeScope scope exit => Handle.scope scope :: exitKeys exit
  | ActionName.setInterruptible body _ => body.keys
  | ActionName.refuse _ => []
  | ActionName.dropObservers _ => []
  | ActionName.cancelRace _ => []
  | ActionName.closePar order exit => order.flatMap FinName.keys ++ exitKeys exit

/-- The handles of a thunk of the stores' alphabet. -/
def Thunk.keys : Thunk → List Handle
  | Thunk.park kind => kind.keys
  | Thunk.act action => action.keys
  | Thunk.op operation => operation.keys
  | Thunk.body program => program.keys
  | Thunk.foreign capture exit => Val.keysList capture.env ++ capture.ctx.keys ++ exitKeys exit

/-! ## Code, at any name and thunk alphabet -/

variable {ν σ : Type}

/-- The handles of a primitive: the value leaves, the names, the thunks, and the bodies. A
cause contributes nothing (`Cause.interrupt`'s interruptor is provenance, not a handle). -/
def primKeys (nk : ν → List Handle) (sk : σ → List Handle) :
    Prim ν σ Val Err Defect FiberId Ann → List Handle
  | Prim.success value => value.keys
  | Prim.failure _ => []
  | Prim.sync thunk => sk thunk
  | Prim.suspend thunk => sk thunk
  | Prim.withFiber thunk => sk thunk
  | Prim.yieldableError _ => []
  | Prim.iterator generator cursor => nk generator ++ cursor.keys
  | Prim.onSuccess body onValue => primKeys nk sk body ++ nk onValue
  | Prim.onSuccessConst body next => primKeys nk sk body ++ primKeys nk sk next
  | Prim.onFailure body onCause => primKeys nk sk body ++ nk onCause
  | Prim.onSuccessAndFailure body onValue onCause =>
    primKeys nk sk body ++ nk onValue ++ nk onCause
  | Prim.exitFrame body => primKeys nk sk body
  | Prim.onExit body finalizer _ => primKeys nk sk body ++ nk finalizer
  | Prim.setInterruptible _ => []
  | Prim.whileLoop loop cursor => nk loop ++ cursor.keys
  | Prim.yieldNowWith _ => []
  | Prim.async register _ cancel => nk register ++ (cancel.map nk).getD []
  | Prim.asyncFinalizer onInterrupt => nk onInterrupt

/-- The handles of a loop's next move: the entered cursor and the code that runs. -/
def loopNextKeys (nk : ν → List Handle) (sk : σ → List Handle) :
    LoopNext Val (Prim ν σ Val Err Defect FiberId Ann) → List Handle
  | .continue cursor body => cursor.keys ++ primKeys nk sk body
  | .finish code => primKeys nk sk code

/-- The handles of a program of the stores' alphabet. -/
def programKeys : Program → List Handle := primKeys Name.keys Thunk.keys

/-- The handles a `withFiber` action carries. -/
def WithFiberAction.keys (nk : ν → List Handle) (sk : σ → List Handle) :
    WithFiberAction ν σ Val Err Defect FiberId Ann Ctx → List Handle
  | WithFiberAction.fork program _ => primKeys nk sk program
  | WithFiberAction.forkIn program _ scope => Handle.scope scope :: primKeys nk sk program
  | WithFiberAction.forkScoped program _ => primKeys nk sk program
  | WithFiberAction.ambientScope => []
  | WithFiberAction.runIn target scope => [Handle.fiber target, Handle.scope scope]
  | WithFiberAction.interrupt target => [Handle.fiber target]
  | WithFiberAction.interruptAs target _ => [Handle.fiber target]
  | WithFiberAction.interruptScoped target => [Handle.fiber target]
  | WithFiberAction.interruptAll targets _ => targets.map Handle.fiber
  | WithFiberAction.awaitAll targets => targets.map Handle.fiber
  | WithFiberAction.awaitAllFailFast targets => targets.map Handle.fiber
  | WithFiberAction.snapshotChildren => []
  | WithFiberAction.awaitNewChildren snapshot => snapshot.map Handle.fiber
  | WithFiberAction.raceAll entrants => entrants.flatMap (primKeys nk sk)
  | WithFiberAction.setInterruptible body _ => primKeys nk sk body
  | WithFiberAction.setContext context => context.keys
  | WithFiberAction.getContext => []
  | WithFiberAction.getId => []
  | WithFiberAction.closeScope scope exit => Handle.scope scope :: exitKeys exit
  | WithFiberAction.refuse _ => []
  | WithFiberAction.dropObservers _ => []
  | WithFiberAction.cancelRace _ => []
  | WithFiberAction.closePar finalizers => finalizers.flatMap (primKeys nk sk)

/-- The handles a frame holds: its current primitive and its stack. -/
def frameKeys (nk : ν → List Handle) (sk : σ → List Handle)
    (f : FrameFiber ν σ Val Err Defect FiberId Ann) : List Handle :=
  primKeys nk sk f.current ++ f.stack.flatMap (primKeys nk sk)

/-- The handles a countdown's continuation names. -/
def Resume.keys (nk : ν → List Handle) : Resume ν → List Handle
  | Resume.exitsValue => []
  | Resume.void => []
  | Resume.continueWith name => nk name

/-- The handles of an outstanding park: the target observed, the targets left, the exits
collected and the continuation. -/
def Pending.keys (nk : ν → List Handle) (p : Pending ν Val Err Defect FiberId Ann) :
    List Handle :=
  (p.waitingOn.map Handle.fiber).toList ++ p.remaining.map Handle.fiber ++
    p.collected.flatMap exitKeys ++ p.resumeWith.keys nk

/-- The handles an observer names: the fiber it resumes, the parent it untracks, the scope
whose finalizer it drops. -/
def Observer.keys : Observer → List Handle
  | Observer.resumeAwait waiter _ _ => [Handle.fiber waiter]
  | Observer.untrackChild parent => [Handle.fiber parent]
  | Observer.dropScopeFinalizer scope _ => [Handle.scope scope]
  | Observer.countdown waiter _ => [Handle.fiber waiter]
  | Observer.raceCallback _ => []
  | Observer.callback _ => []

/-- The handle a waiter list's key names: the cell of its family, when the kind has one. -/
def WakeKey.keys (key : WakeKey) : List Handle :=
  (Handle.ofCode (key.kind.byte, key.index)).toList

/-- The handles a wake mode names: the dispatcher a scheduled entry is posted to. -/
def WakeMode.keys : WakeMode → List Handle
  | WakeMode.now => []
  | WakeMode.scheduled owner _ => [Handle.fiber owner]

/-- The handles of an owed resume: its code's, and — for a scheduled one, which becomes a
task on a dispatcher — the dispatcher's fiber and the waiter it names. An inline resume names
no fiber, as `Cmd.resume` does not. -/
def Owed.keys {κ : Type} (ck : κ → List Handle) (d : Owed κ) : List Handle :=
  ck d.code ++
    (match d.mode with
      | WakeMode.now => []
      | WakeMode.scheduled owner _ => [Handle.fiber owner, Handle.fiber d.waiter])

/-- Mapping an owed resume carries no handles beyond the input keys when the code map
has that property; the wake mode and waiter remain the same. -/
def M1.Handles.owed_mapCode_keys_subset {κ κ' : Type} (f : κ → κ')
    (sourceKeys : κ → List Handle) (targetKeys : κ' → List Handle)
    (_h : ∀ c, targetKeys (f c) ⊆ sourceKeys c) (d : Owed κ) : ProofGraph.Obligation (
    (d.mapCode f).keys targetKeys ⊆ d.keys sourceKeys) := ⟨⟩
#proof_wanted M1.Handles.owed_mapCode_keys_subset

theorem Owed.mapCode_keys_subset {κ κ' : Type} (f : κ → κ')
    (sourceKeys : κ → List Handle) (targetKeys : κ' → List Handle)
    (h : ∀ c, targetKeys (f c) ⊆ sourceKeys c) (d : Owed κ) :
    (d.mapCode f).keys targetKeys ⊆ d.keys sourceKeys := by
  simp only [Owed.keys, Owed.mapCode]
  exact List.append_subset_append (h d.code) (List.Subset.refl _)

/-- Code-map handle bounds lift through an ordered list of owed resumes. -/
def M1.Handles.owed_flatMap_mapCode_keys_subset {κ κ' : Type} (f : κ → κ')
    (sourceKeys : κ → List Handle) (targetKeys : κ' → List Handle)
    (_h : ∀ c, targetKeys (f c) ⊆ sourceKeys c) (ds : List (Owed κ)) : ProofGraph.Obligation (
    (ds.map (Owed.mapCode f)).flatMap (Owed.keys targetKeys) ⊆ ds.flatMap (Owed.keys sourceKeys)) := ⟨⟩
#proof_wanted M1.Handles.owed_flatMap_mapCode_keys_subset

theorem Owed.flatMap_mapCode_keys_subset {κ κ' : Type} (f : κ → κ')
    (sourceKeys : κ → List Handle) (targetKeys : κ' → List Handle)
    (h : ∀ c, targetKeys (f c) ⊆ sourceKeys c) (ds : List (Owed κ)) :
    (ds.map (Owed.mapCode f)).flatMap (Owed.keys targetKeys) ⊆ ds.flatMap (Owed.keys sourceKeys) := by
  intro x hx
  obtain ⟨mapped, hmapped, hx⟩ := List.mem_flatMap.mp hx
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hmapped
  exact List.mem_flatMap.mpr ⟨d, hd, Owed.mapCode_keys_subset f sourceKeys targetKeys h d hx⟩

/-- The handles of a dispatcher task: the fiber it starts or resumes, the resume's code, the
list a wake names. -/
def Task.keys (nk : ν → List Handle) (sk : σ → List Handle) :
    Task ν σ Val Err Defect FiberId Ann → List Handle
  | Task.start child => [Handle.fiber child]
  | Task.resume target _ answer => Handle.fiber target :: primKeys nk sk answer
  | Task.wake key _ => key.keys

/-- The handles of every task a dispatcher holds. -/
def Dispatcher.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (d : Dispatcher ν σ Val Err Defect FiberId Ann) : List Handle :=
  d.buckets.flatMap fun b => b.tasks.flatMap (Task.keys nk sk)

/-- The handles a fiber holds: its frame, its parks, the exit it is finalizing and the exit it
stored, its observers, its children, its dispatcher and its context. -/
def RunFiber.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (f : RunFiber ν σ Val Err Defect FiberId Ann Ctx) : List Handle :=
  frameKeys nk sk f.frame ++ f.pending.flatMap (Pending.keys nk) ++
    optExitKeys f.finalizing ++ optExitKeys f.exit ++
    f.observers.flatMap Observer.keys ++ f.children.map Handle.fiber ++
    f.dispatcher.keys nk sk ++ f.context.keys

/-- The handles a race holds: its host, its live entrants, the exit it accepted (what
`raceSettle` resumes the host with), and the entrants not yet forked. -/
def Race.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (r : Race ν σ Val Err Defect FiberId Ann) : List Handle :=
  Handle.fiber r.host :: r.state.live.map Handle.fiber ++ optExitKeys r.state.accepted ++
    r.programs.flatMap (primKeys nk sk)

/-- The handles a command carries into a fiber: a resume's answer, a finish's or an
observer's exit, the fibers an interrupt walk or a tracking names, and an await park's
targets (D6b). -/
def Cmd.keys (nk : ν → List Handle) (sk : σ → List Handle) :
    Cmd ν σ Val Err Defect FiberId Ann → List Handle
  | Cmd.resume _ _ answer => primKeys nk sk answer
  | Cmd.finish _ exit => exitKeys exit
  | Cmd.interruptTarget target _ _ => [Handle.fiber target]
  | Cmd.afterInterrupt host _ kind => Handle.fiber host :: kind.keys
  | Cmd.raceCancel _ host _ remaining visited =>
    Handle.fiber host :: (remaining ++ visited).map Handle.fiber
  | Cmd.trackChild parent child => [Handle.fiber parent, Handle.fiber child]
  | Cmd.observe fiber exit observer => Handle.fiber fiber :: exitKeys exit ++ observer.keys
  | Cmd.exitDone fiber => [Handle.fiber fiber]
  | Cmd.closeParAwait host _ fibers => Handle.fiber host :: fibers.map Handle.fiber
  | Cmd.wake key _ => key.keys
  | _ => []

/-- The handles of every command of a list. -/
def cmdsKeys (nk : ν → List Handle) (sk : σ → List Handle)
    (cmds : List (Cmd ν σ Val Err Defect FiberId Ann)) : List Handle :=
  cmds.flatMap (Cmd.keys nk sk)

/-- The handles an iteration's outcome carries: a finished exit. -/
def Outcome.keys : Outcome ν σ Val Err Defect FiberId Ann → List Handle
  | Outcome.finished exit => exitKeys exit
  | _ => []

/-! ## The stores -/

/-- The handles a Deferred cell holds: its stored completion. -/
def DeferredCell.keys (c : DeferredCell) : List Handle :=
  match c.completion with
  | some completion => completion.keys
  | none => []

/-- The handles of the Deferred store: every cell's completion and every owed resume's. -/
def DeferredStore.keys (d : DeferredStore) : List Handle :=
  d.cells.flatMap DeferredCell.keys ++ d.due.flatMap (Owed.keys Completion.keys)

/-- The handles a closed scope's exit carries. The store answers that exit to a registration
on a closed scope (`syncOpStep`, `SyncOp.scopeAdd`; `internal/effect.ts:3851-3853`), so it is
one of the store's own handles. -/
def scopeClosingKeys (sc : ScopeV) : List Handle :=
  match sc.closingExit? with
  | some exit => exitKeys exit
  | none => []

/-- The handles a scope entry holds: its registered finalizer names and, once closed, the
exit it closed with. -/
def ScopeEntry.keys (e : ScopeEntry) : List Handle :=
  (e.scope.finalizers.flatMap fun kf => FinName.keys kf.2) ++ scopeClosingKeys e.scope

/-- The handles of the scope store. -/
def ScopeStore.keys (s : ScopeStore) : List Handle :=
  s.entries.flatMap ScopeEntry.keys

/-- The handles a memo entry holds: its layer scope, its Deferred and its finalizer.
The Deferred store owns the completion's handles. -/
def MemoEntry.keys (e : MemoEntry) : List Handle :=
  [Handle.scope e.layerScope, Handle.promise e.deferred] ++ e.finalizer.keys

/-- The handles of a memo map: its entries'. -/
def MemoMap.keys (m : MemoMap) : List Handle := m.entries.flatMap fun e => e.2.keys

/-- The handles of the memo world. -/
def MemoWorld.keys (w : MemoWorld) : List Handle := w.flatMap MemoMap.keys

/-- The handles the stores hold: the heap's values, the Deferred store, the scope store, the
memo world. -/
def Stores.keys (s : Stores) : List Handle :=
  s.refs.flatMap Val.keys ++ s.deferreds.keys ++ s.scopes.keys ++ s.memo.keys

/-- The handles the machine holds: every fiber's, every race's, the armed queue, the stores. -/
def RunMachine.keys (nk : ν → List Handle) (sk : σ → List Handle)
    (m : RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores) : List Handle :=
  m.fibers.flatMap (RunFiber.keys nk sk) ++ m.races.flatMap (Race.keys nk sk) ++
    m.armed.map Handle.fiber ++ m.state.keys

/-- The handles an iteration leaves: its machine's, its fiber's, its nested commands' and its
finished exit's. -/
def iterKeys (nk : ν → List Handle) (sk : σ → List Handle)
    (it : Iter ν σ Val Err Defect FiberId Ann Ctx Stores) : List Handle :=
  it.machine.keys nk sk ++ it.fiber.keys nk sk ++ cmdsKeys nk sk it.nested ++ it.outcome.keys

/-- The machine at the frame instance, for ascriptions. -/
abbrev NM (ν σ : Type) := RunMachine ν σ Val Err Defect FiberId Ann Ctx Stores

/-! ### The fields the machine's operations leave alone -/

namespace M1.Handles
open Effect4 Effect4.Machine

def register_keys (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    ProofGraph.Obligation (
    (self.register cell waiter token).1.keys ⊆ self.keys ∧
      (∀ p, (self.register cell waiter token).2 = some p → p.keys ⊆ self.keys) ∧
      self.cells.length ≤ (self.register cell waiter token).1.cells.length) := ⟨⟩
#proof_wanted register_keys

def flatMap_resumes_const (ws : List (Waiter Unit)) (e : Completion Val Err Defect FiberId Ann) :
    ProofGraph.Obligation (
    (ws.map fun w => (⟨w.fiber, w.token, e, WakeMode.now⟩ : Owed (Completion Val Err Defect FiberId Ann))).flatMap
        (Owed.keys Completion.keys) ⊆ e.keys) := ⟨⟩
#proof_wanted flatMap_resumes_const

def complete_keys (self : DeferredStore) (cell : DeferredKey) (e : Completion Val Err Defect FiberId Ann) :
    ProofGraph.Obligation (
    (self.complete cell e).1.keys ⊆ self.keys ++ e.keys ∧
      self.cells.length ≤ (self.complete cell e).1.cells.length) := ⟨⟩
#proof_wanted complete_keys

def drainDue_keys (self : DeferredStore) : ProofGraph.Obligation (
    (self.drainDue).2.keys ⊆ self.keys ∧
      (self.drainDue).1.flatMap (Owed.keys Completion.keys) ⊆ self.keys) := ⟨⟩
#proof_wanted drainDue_keys

end M1.Handles

/-- Reading a Deferred cell exposes only handles already owned by its store. -/
def M1.Handles.cellAt_keys_subset {self : DeferredStore} {cell : DeferredKey} {c : DeferredCell}
    (_h : self.cellAt cell = some c) : ProofGraph.Obligation (c.keys ⊆ self.keys) := ⟨⟩
#proof_wanted M1.Handles.cellAt_keys_subset

theorem DeferredStore.cellAt_keys_subset {self : DeferredStore} {cell : DeferredKey} {c : DeferredCell}
    (h : self.cellAt cell = some c) : c.keys ⊆ self.keys := by
  intro x hx
  exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_of_getElem? h, hx⟩)

attribute [aesop norm simp (rule_sets := [Effect4.Stores])]
  DeferredCell.keys DeferredStore.keys Owed.keys

attribute [aesop safe forward (rule_sets := [Effect4.Stores])]
  DeferredStore.cellAt_keys_subset

/-! ### The Deferred store -/

theorem DeferredStore.setCell_keys_subset (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell) :
    (self.setCell cell c).keys ⊆ self.keys ++ c.keys := by
  intro x hx
  simp only [DeferredStore.keys, DeferredStore.setCell, List.mem_append] at hx ⊢
  rcases hx with hx | hx
  · obtain ⟨c', hc', hxc⟩ := List.mem_flatMap.mp hx
    rcases List.mem_or_eq_of_mem_set hc' with h | rfl
    · exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨c', h, hxc⟩))
    · exact Or.inr hxc
  · exact Or.inl (Or.inr hx)

theorem DeferredStore.setCell_le (self : DeferredStore) (cell : DeferredKey) (c : DeferredCell) :
    self.cells.length ≤ (self.setCell cell c).cells.length := by
  rw [DeferredStore.setCell_cells_length]
  exact Nat.le_refl _

attribute [aesop safe apply (rule_sets := [Effect4.Stores])]
  DeferredStore.setCell_keys_subset DeferredStore.setCell_le

theorem DeferredStore.register_keys (self : DeferredStore) (cell : DeferredKey) (waiter : FiberId) (token : Nat) :
    (self.register cell waiter token).1.keys ⊆ self.keys ∧
      (∀ p, (self.register cell waiter token).2 = some p → p.keys ⊆ self.keys) ∧
      self.cells.length ≤ (self.register cell waiter token).1.cells.length := by
  aesop (rule_sets := [Effect4.Stores])

/-- The owed resumes a broadcast wake mints carry the completion's keys and no other. -/
theorem flatMap_resumes_const (ws : List (Waiter Unit)) (e : Completion Val Err Defect FiberId Ann) :
    (ws.map fun w => (⟨w.fiber, w.token, e, WakeMode.now⟩ : Owed (Completion Val Err Defect FiberId Ann))).flatMap
        (Owed.keys Completion.keys) ⊆ e.keys := by
  aesop (rule_sets := [Effect4.Stores])

theorem DeferredStore.complete_keys (self : DeferredStore) (cell : DeferredKey) (e : Completion Val Err Defect FiberId Ann) :
    (self.complete cell e).1.keys ⊆ self.keys ++ e.keys ∧
      self.cells.length ≤ (self.complete cell e).1.cells.length := by
  aesop (rule_sets := [Effect4.Stores])

theorem DeferredStore.drainDue_keys (self : DeferredStore) :
    (self.drainDue).2.keys ⊆ self.keys ∧
      (self.drainDue).1.flatMap (Owed.keys Completion.keys) ⊆ self.keys := by
  aesop (rule_sets := [Effect4.Stores])


end Effect4.Machine
