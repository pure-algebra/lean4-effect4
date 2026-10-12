import Effect4.Laws.Program.ScopeFragment
import Effect4.Laws.Program.SourceOrigin

/-!
# Native residual source ownership

Concept: store-typing R4, serving `HeapSites.heap_sites_keep`.
These predicates inspect existing native code, source points and stored names.
Callback addresses retain the lexical length their invocation supplies.
Stored finalizers retain their release address through every synthetic wrapper.
The direct lexical fragment excludes raw generators, layers and definition invocation.
-/
set_option autoImplicit false
namespace Effect4.Program.SourceScope
open Effect4 Effect4.Machine Effect4.Program

/-- An explicit source allocation is the only parallel-scope producer in this direct fragment.
Consumer: sequential Workers custody through the existing source-history carrier. -/
def ParallelAllowed (root : NativeEff) : Prop :=
  ∃ path request, Node.at_ (.eff root) path = some (.eff (.perform (.scopeMake .parallel) request))

/-- Administrative scope construction is sequential unless the source admits parallel allocation.
Consumer: operation, stored close-walk and scope-store ownership. -/
def StrategyAt (root : NativeEff) (strategy : FinalizerStrategy) : Prop :=
  strategy = .sequential ∨ ParallelAllowed root

/-- The existing address census rejects explicit parallel scope allocations.
Consumer: actual Workers source restriction for release custody. -/
def sequentialHead : Node NativeOp → Bool
  | .eff (.perform (.scopeMake .parallel) _) => false
  | _ => true

def SequentialSource (root : NativeEff) : Prop :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all sequentialHead) = true

/-- The finite source census excludes every parallel-allocation witness.
Consumer: source-owned scope strategy and parallel-action exclusion. -/
theorem SequentialSource.not_parallel {root : NativeEff} (held : SequentialSource root) :
    ¬ ParallelAllowed root := by
  rintro ⟨path, request, found⟩
  have member : path ∈ Node.addresses (.eff root) :=
    (mem_addresses_iff (.eff root) path).mpr (by rw [found]; rfl)
  have head := List.all_eq_true.mp held path member
  rw [found] at head
  cases head

/-- A checked sequential source discharges the existing strategy alternative.
Consumer: actual scopes reached by Workers history. -/
theorem StrategyAt.sequential {root : NativeEff} {strategy : FinalizerStrategy}
    (held : StrategyAt root strategy) (source : SequentialSource root) : strategy = .sequential :=
  held.resolve_right source.not_parallel

/-- A runtime race retains a race action at an actual source address.
Consumer: Workers release custody excludes race-cleanup replies through the existing source carrier. -/
def RaceAllowed (root : NativeEff) : Prop :=
  ∃ path bodies, Node.at_ (.eff root) path = some (.action (.raceAll bodies)) ∨
    Node.at_ (.eff root) path = some (.action (.raceAllFirst bodies))

/-- The generated address census rejects both authored race forms.
Consumer: the actual Workers source restriction in release custody. -/
def raceFreeHead : Node NativeOp → Bool
  | .action (.raceAll _) | .action (.raceAllFirst _) => false
  | _ => true

def RaceFreeSource (root : NativeEff) : Prop :=
  (Node.addresses (.eff root)).all (fun path =>
    (Node.at_ (.eff root) path).all raceFreeHead) = true

/-- The checked source census excludes every runtime race witness.
Consumer: terminal resume sequencing and the actual race-store reader. -/
theorem RaceFreeSource.not_race {root : NativeEff} (held : RaceFreeSource root) :
    ¬ RaceAllowed root := by
  rintro ⟨path, bodies, found | found⟩
  all_goals
    have member : path ∈ Node.addresses (.eff root) :=
      (mem_addresses_iff (.eff root) path).mpr (by rw [found]; rfl)
    have head := List.all_eq_true.mp held path member
    rw [found] at head
    cases head

/-- A first-success race supplies its actual authored action.
Consumer: the native source-action interpreter. -/
theorem raceAllowed_firstSuccess (root : NativeEff) (path : List Nat) (bodies : Effs NativeOp)
    (found : Node.at_ (.eff root) path = some (.action (.raceAll bodies))) : RaceAllowed root :=
  ⟨path, bodies, Or.inl found⟩

/-- A first-exit race supplies its actual authored action.
Consumer: the native source-action interpreter. -/
theorem raceAllowed_firstExit (root : NativeEff) (path : List Nat) (bodies : Effs NativeOp)
    (found : Node.at_ (.eff root) path = some (.action (.raceAllFirst bodies))) : RaceAllowed root :=
  ⟨path, bodies, Or.inr found⟩

/-- The lexical length at the child a callback resolves after appending its arguments. -/
def NextAt (root : NativeEff) (p : Point) (i added : Nat) : Prop :=
  levelAt (.eff root) 0 (p.path ++ [i]) = some (p.env.length + added)

/-- A captured registration retains the actual acquisition head that creates it.
Consumer: captured-finalizer source ownership and application source-use counts. -/
def AcquisitionAt (root : NativeEff) (path : List Nat) : Prop :=
  ∃ acquire release, Node.at_ (.eff root) path = some (.eff (.acquireRelease acquire release))

/-- An authored finalizer callback retains the actual onExit head that creates it.
Consumer: native finalizer source ownership and application source-use counts. -/
def ExitAt (root : NativeEff) (path : List Nat) : Prop :=
  ∃ body finalizer, Node.at_ (.eff root) path = some (.eff (.onExit body finalizer))

/-- A stored foreign finalizer resolves one exit argument beyond its saved environment. -/
def FinAt (root : NativeEff) : FinName → Prop
  | .foreign capture => NextAt root (Point.ofCapture capture) 1 1 ∧ AcquisitionAt root capture.path
  | _ => True

/-- Only source operations can write references; administrative operations retain captures. -/
def OpAt (root : NativeEff) (op : SyncOp) : Prop :=
  match op with
  | .refMake _ | .refSet _ _ | .refGetAndSet _ _ | .refSetAndGet _ _
  | .refUpdate _ _ _ | .refGetAndUpdate _ _ _ | .refUpdateAndGet _ _ _
  | .refUpdateSome _ _ _ | .refGetAndUpdateSome _ _ _ | .refUpdateSomeAndGet _ _ _
  | .refModify _ _ _ | .refModifySome _ _ _ => OpOrigin root op
  | .scopeAdd _ fin => FinAt root fin
  | .scopeMake strategy | .scopeFork _ strategy => StrategyAt root strategy
  | _ => True

/-- Stored program wrappers retain every operation and finalizer they can expose. -/
def ProgAt (root : NativeEff) : ProgName → Prop
  | .syncOp op => OpAt root op
  | .raceOf _ | .cancelRace _ => RaceAllowed root
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => ProgAt root body
  | .finalizerOf fin _ => FinAt root fin
  | .onExitOf body fin _ => ProgAt root body ∧ FinAt root fin
  | .seqOf first second => ProgAt root first ∧ ProgAt root second
  | .closeWalk strategy order _ => (∀ fin ∈ order, FinAt root fin) ∧ StrategyAt root strategy
  | _ => True

/-- Stored continuation wrappers retain their delayed programs and captures. -/
def StoreNameAt (root : NativeEff) : Name → Prop
  | .seq next | .snapshotThen next => ProgAt root next
  | .withWaiter base _ _ => StoreNameAt root base
  | .finalizerName fin => FinAt root fin
  | .closeSeq order _ _ => ∀ fin ∈ order, FinAt root fin
  | _ => True

/-- Stored fiber actions retain their forked, masked and finalizer programs. -/
def StoreActionAt (root : NativeEff) : ActionName → Prop
  | .raceAll _ => RaceAllowed root
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ =>
    ProgAt root body
  | .closePar order _ => (∀ fin ∈ order, FinAt root fin) ∧ ParallelAllowed root
  | _ => True

/-- Stored thunks retain the syntax they expose when evaluated. -/
def StoreThunkAt (root : NativeEff) : Thunk → Prop
  | .op op => OpAt root op
  | .body body => ProgAt root body
  | .act action => StoreActionAt root action
  | .foreign capture _ => FinAt root (.foreign capture)
  | .park _ => True

/-- Source service regions retain their program address; layer regions are outside this fragment. -/
def RegionAt (root : NativeEff) : Region → Prop
  | .program p => At root p
  | _ => False

/-- Source continuation names record the child length their actual invocation supplies. -/
def NameAt (root : NativeEff) : EffName → Prop
  | .external op _ origin =>
    ∃ request, Node.at_ (.eff root) origin = some (.eff (.perform op request))
  | .cont p => NextAt root p 1 1 ∧
    ∃ first rest, Node.at_ (.eff root) p.path = some (.eff (.bind first rest))
  | .caught p => NextAt root p 1 1 ∧
    ∃ body handler, Node.at_ (.eff root) p.path = some (.eff (.catchCause body handler))
  | .caughtError p => NextAt root p 1 1 ∧
    ∃ test body handler, Node.at_ (.eff root) p.path = some (.eff (.catchIf test body handler))
  | .onValue p => NextAt root p 1 1 ∧
    ∃ body success failure, Node.at_ (.eff root) p.path = some (.eff (.matchCause body success failure))
  | .fin p => NextAt root p 1 1 ∧ ExitAt root p.path
  | .onCause p => NextAt root p 2 1
  | .loop p => At root p
  | .scopeOpen p | .scopeProvide p _ | .scopeBody p _ => NextAt root p 0 0
  | .forkScopedIn p => At root p
  | .acquireCtx p | .acquireIn p _ => NextAt root p 0 0 ∧ NextAt root p 1 2 ∧ AcquisitionAt root p.path
  | .acquired p _ _ => NextAt root p 1 2 ∧ AcquisitionAt root p.path
  | .afterScopeAdd _ fin => FinAt root fin
  | .releaseUnder p _ _ | .releaseBody p _ _ => NextAt root p 1 1 ∧ AcquisitionAt root p.path
  | .withWaiter base _ _ => NameAt root base
  | .store name => StoreNameAt root name
  | .provideMask _ region | .updateThen _ region _ | .bodyThen region _ _ => RegionAt root region
  | .gen _ _ _ | .provideLayerWith _ | .provideLayerBody _
  | .buildWithScopeFromContext _ _ | .withMemoMapThen _ _ | .fromBuildThen _ _
  | .memoize _ _ _ | .buildIntoLayerScope _ _ _ | .thenBuildInto _ _ _
  | .freshThen _ _ | .provideThen _ _ _ _ | .mergeChildren _ _ | .mergeForkOne _ _ _ _ _
  | .mergeForkNext _ _ _ _ _ | .mergeAllChildren _ _ | .mergeAllForkOne _ _ _ _ _
  | .mergeAllForkNext _ _ _ _ _ => False
  | _ => True

/-- Native thunks retain the point, operation or stored syntax their interpreter reads. -/
def ThunkAt (root : NativeEff) : EffThunk → Prop
  | .pure p | .body p | .act p | .forkInAt p _ | .releaseMasked p _ => At root p
  | .op op => OpAt root op
  | .store thunk => StoreThunkAt root thunk
  | .acquireMasked p _ => NextAt root p 0 0 ∧ NextAt root p 1 2 ∧ AcquisitionAt root p.path
  | .provideMasked _ region _ | .restoreRegion region _ => RegionAt root region
  | .memoLookup _ _ _ | .forkLayer _ _ _ => False
  | _ => True

/-- Native Async producers use represented deferred or timer cancellation names.
Consumer: source ownership through actual Async parking and source-use accounting. -/
def AsyncCancelAt : EffName → Prop
  | .cancelAwait _ | .store (.cancelAwait _) | .store .cancelSleep => True
  | _ => False

/-- A concrete code retains source ownership in every suspended or saved field. -/
def CodeAt (root : NativeEff) : NCode → Prop
  | .sync thunk | .suspend thunk | .withFiber thunk => ThunkAt root thunk
  | .iterator name _ | .whileLoop name _ | .asyncFinalizer name => NameAt root name
  | .onSuccess body name => CodeAt root body ∧ NameAt root name ∧
      ∀ acquired fin, name = .afterScopeAdd acquired fin →
        ∃ scope, body = .sync (.op (.scopeAdd scope fin))
  | .onFailure body name | .onExit body name _ => CodeAt root body ∧ NameAt root name
  | .onSuccessConst body next => CodeAt root body ∧ CodeAt root next
  | .onSuccessAndFailure body success failure =>
    CodeAt root body ∧ NameAt root success ∧ NameAt root failure
  | .exitFrame body => CodeAt root body
  | .async register _ cancel => NameAt root register ∧ ∀ name ∈ cancel, NameAt root name ∧ AsyncCancelAt name
  | _ => True

/-- A response-sensitive callback retains the actual producer copied into its saved frame.
Consumer: registration sequencing and the existing custody and registration goals. -/
theorem registration_body (root : NativeEff) (body : NCode) (acquired : Val) (fin : FinName)
    (owned : CodeAt root (.onSuccess body (.afterScopeAdd acquired fin))) :
    ∃ scope, body = .sync (.op (.scopeAdd scope fin)) :=
  owned.2.2 acquired fin rfl

/-- Restoring a completed exit uses no registration response callback.
Consumer: native fiber exit and awaited-child cleanup. -/
theorem success_restore_at (root : NativeEff) (body : NCode) (exit : ExitV)
    (owned : CodeAt root body) : CodeAt root (.onSuccess body (.restore exit)) := by
  refine ⟨owned, trivial, ?_⟩
  intro _ _ wrong
  cases wrong

/-- The source walk transports a generated child level to a saved callback address. -/
theorem next_of_at (root : NativeEff) (p : Point) (e : NativeEff) (i added : Nat)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (hs : At root p)
    (child : levelAt (.eff e) p.env.length [i] = some (p.env.length + added)) :
    NextAt root p i added := by
  unfold NextAt
  rw [levelAt_suffix _ _ p.path [i] 0 found, hs]
  exact child

/-- A callback with no new argument retains its source child scope. -/
theorem child_at (root : NativeEff) (p : Point) (i : Nat) (h : NextAt root p i 0) :
    At root (p.child i) := by
  exact h

/-- A callback with one new argument retains its source child scope. -/
theorem childWith_at (root : NativeEff) (p : Point) (i : Nat) (value : Val)
    (h : NextAt root p i 1) : At root (p.childWith i value) := by
  unfold At
  change levelAt (.eff root) 0 (p.path ++ [i]) = some (p.env ++ [value]).length
  rw [List.length_append, List.length_singleton]
  exact h

/-- A source scope allocation supplies its actual parallel-allocation witness when needed.
Consumer: opAt_origin and admitted Workers strategy provenance. -/
theorem strategyAt_origin (root : NativeEff) (strategy : FinalizerStrategy)
    (origin : OpOrigin root (.scopeMake strategy)) : StrategyAt root strategy := by
  cases strategy with
  | sequential => exact Or.inl rfl
  | parallel =>
    obtain ⟨p, row, request, value, found, _, _, operation⟩ := origin
    refine Or.inr ⟨p.path, request, ?_⟩
    fun_cases NativeOp.syncOpOf row p.env value
    all_goals aesop (add norm simp [NativeOp.syncOpOf])

/-- A source-owned operation supplies every residual scope condition of its native operation. -/
theorem opAt_origin (root : NativeEff) (op : SyncOp) (origin : OpOrigin root op) :
    OpAt root op := by
  have noAdd : ∀ scope fin, op ≠ .scopeAdd scope fin := by
    intro scope fin eq
    obtain ⟨p, row, request, value, _, _, _, operation⟩ := origin
    rw [eq] at operation
    exact source_no_scopeAdd row p.env value scope fin operation
  cases op <;> dsimp only [OpAt]
  case scopeMake strategy => exact strategyAt_origin root strategy origin
  case scopeFork scope strategy =>
    obtain ⟨p, row, request, value, _, _, _, operation⟩ := origin
    fun_cases NativeOp.syncOpOf row p.env value <;> aesop (add norm simp [NativeOp.syncOpOf])
  all_goals aesop

/-- A refused shape carries no callback or writer. -/
theorem badShape_at (root : NativeEff) : CodeAt root badShape := trivial

/-- Asynchronous rows only produce registration and cancel names, without reference writers. -/
theorem asyncRoute_at (root : NativeEff) (row : NativeOp) (request : Term) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff (.perform row request))) :
    CodeAt root (asyncRoute row request p) := by
  fun_cases asyncRoute row request p
  all_goals aesop (add norm simp [CodeAt, ThunkAt, NameAt, StoreNameAt, AsyncCancelAt, badShape])

/-- A provider region's body is its child zero, which binds nothing. A step of `compile_at`. -/
theorem provideContext_region (root : NativeEff) (p : Point) (context : Term) (body : NativeEff)
    (found : Node.at_ (.eff root) p.path = some (.eff (.provideContext context body)))
    (hs : At root p) : RegionAt root (.program (p.child 0)) :=
  child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl))

/-- The compiler retains source scope in every residual slot of this source fragment. -/
theorem compile_at (root : NativeEff) (fragment : Fragment root) (e : NativeEff) (p : Point)
    (found : Node.at_ (.eff root) p.path = some (.eff e)) (hs : At root p) :
    CodeAt root (compileEff e p) := by
  revert found hs
  fun_induction compileEff e p
  case case13 p n hf row request kind value hval operation hop nex ncall nparam =>
    intro found hs
    simp only [kind, hval, hop]
    exact opAt_origin root operation ⟨p, row, request, value, found, hs, hval, hop⟩
  case case18 p n hf first rest ih =>
    intro found hs
    refine ⟨ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl))),
      ⟨next_of_at root p _ 1 1 found hs (by rfl), ⟨first, rest, found⟩⟩, ?_⟩
    intro _ _ wrong
    cases wrong
  case case20 p n hf body handler ih =>
    intro found hs
    exact ⟨ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl))),
      ⟨next_of_at root p _ 1 1 found hs (by rfl), ⟨body, handler, found⟩⟩⟩
  case case21 p n hf test body handler ih =>
    intro found hs
    exact ⟨ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl))),
      ⟨next_of_at root p _ 1 1 found hs (by rfl), ⟨test, body, handler, found⟩⟩⟩
  case case22 p n hf body success failure ih =>
    intro found hs
    exact ⟨ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl))),
      ⟨next_of_at root p _ 1 1 found hs (by rfl), ⟨body, success, failure, found⟩⟩,
      next_of_at root p _ 2 1 found hs (by rfl)⟩
  case case23 p n hf body finalizer ih =>
    intro found hs
    exact ⟨ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl))),
      ⟨next_of_at root p _ 1 1 found hs (by rfl), ⟨body, finalizer, found⟩⟩⟩
  case case25 p n hf body noexit ih =>
    intro found hs
    exact ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl)))
  case case37 p n hf acquire release =>
    intro found hs
    refine ⟨trivial, ⟨next_of_at root p _ 0 0 found hs (by rfl),
      next_of_at root p _ 1 2 found hs (by rfl), ⟨acquire, release, found⟩⟩, ?_⟩
    intro _ _ wrong
    cases wrong
  case case40 p n hf key value body val read =>
    intro found hs
    refine ⟨trivial, child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl)), ?_⟩
    intro _ _ wrong
    cases wrong
  case case46 p n hf saved body mask ih =>
    intro found hs
    exact ih (Agreement.at_child found 0)
      (child_at root p 0 (next_of_at root p _ 0 0 found hs (by rfl)))
  all_goals intro found hs
  all_goals have head := fragment.at found
  all_goals aesop (add norm simp [asyncRoute_at, badShape_at, CodeAt, NameAt, ThunkAt, directHead, Prim.ofExit]) (add norm unfold [frontier, badShape, updateContextAt]) (add safe apply [asyncRoute_at, provideContext_region])

/-- Resolving any scoped source point retains every residual source slot. -/
theorem resolve_scoped (root : NativeEff) (fragment : Fragment root) (p : Point)
    (hs : At root p) : CodeAt root (resolve root p) := by
  unfold resolve
  split
  · rename_i e found
    exact compile_at root fragment e p found hs
  · exact badShape_at root

/-- Appending the acquired value leaves precisely one future exit binder for its release. -/
theorem capture_at (root : NativeEff) (p : Point) (value : Val) (ctx : Ctx)
    (hs : NextAt root p 1 2) (source : AcquisitionAt root p.path) : FinAt root (.foreign (p.capture value ctx)) := by
  refine ⟨?_, source⟩
  unfold NextAt at hs ⊢
  change levelAt (.eff root) 0 (p.path ++ [1]) = some ((p.env ++ [value]).length + 1)
  rw [List.length_append, List.length_singleton]
  exact hs

end Effect4.Program.SourceScope
