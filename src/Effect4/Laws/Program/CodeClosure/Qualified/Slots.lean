import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual callback closure retains source point assertions and captured environments.
Consumer: the Prefix callback instance and Timeout's attempt-source refinement.
Reach: existing native and stored names; these predicates establish no initialized history.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Qualified
open Effect4 Effect4.Machine Effect4.Program

/-- A foreign finalizer retains its source annotation. -/
@[reducible] def FinAt (point : Point → Prop) (_env : List Val → Prop) (_writes : SyncOp → Prop) : FinName → Prop
  | .foreign capture => point (Point.ofCapture capture)
  | _ => True

/-- Source update operations and registrations retain their captured environment assertion. -/
@[reducible] def OpAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop)
    (operation : SyncOp) : Prop :=
  match operation with
  | .refUpdate _ _ _ | .refGetAndUpdate _ _ _ | .refUpdateAndGet _ _ _
  | .refUpdateSome _ _ _ | .refGetAndUpdateSome _ _ _ | .refUpdateSomeAndGet _ _ _
  | .refModify _ _ _ | .refModifySome _ _ _ => writes operation
  | .scopeAdd _ fin => FinAt point env writes fin
  | _ => True

/-- The compatibility writer policy retains only the captured update environment. -/
@[reducible] def EnvironmentWrites (env : List Val → Prop) : SyncOp → Prop
  | .refUpdate _ _ values | .refGetAndUpdate _ _ values | .refUpdateAndGet _ _ values
  | .refUpdateSome _ _ values | .refGetAndUpdateSome _ _ values | .refUpdateSomeAndGet _ _ values
  | .refModify _ _ values | .refModifySome _ _ values => env values
  | _ => True

/-- Stored program wrappers retain every captured environment they can expose. -/
@[reducible] def ProgAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : ProgName → Prop
  | .syncOp op => OpAt point env writes op
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => ProgAt point env writes body
  | .finalizerOf fin _ => FinAt point env writes fin
  | .onExitOf body fin _ => ProgAt point env writes body ∧ FinAt point env writes fin
  | .seqOf first second => ProgAt point env writes first ∧ ProgAt point env writes second
  | .closeWalk _ order _ => ∀ fin ∈ order, FinAt point env writes fin
  | _ => True

/-- Stored callbacks retain their delayed captured environments. -/
@[reducible] def StoreNameAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : Name → Prop
  | .seq next | .snapshotThen next => ProgAt point env writes next
  | .withWaiter base _ _ => StoreNameAt point env writes base
  | .finalizerName fin => FinAt point env writes fin
  | .closeSeq order _ _ => ∀ fin ∈ order, FinAt point env writes fin
  | _ => True

/-- Stored actions retain the captured environments of their programs. -/
@[reducible] def StoreActionAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : ActionName → Prop
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ => ProgAt point env writes body
  | .closePar order _ => ∀ fin ∈ order, FinAt point env writes fin
  | _ => True

/-- Stored thunks retain the captured environments of their programs and registrations. -/
@[reducible] def StoreThunkAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : Thunk → Prop
  | .op op => OpAt point env writes op
  | .body body => ProgAt point env writes body
  | .act action => StoreActionAt point env writes action
  | .foreign capture _ => FinAt point env writes (.foreign capture)
  | .park _ => True

/-- A direct program region retains its source annotations. -/
@[reducible] def RegionAt (point : Point → Prop) (_env : List Val → Prop) (_writes : SyncOp → Prop) : Region → Prop
  | .program p => point p
  | _ => False

/-- Every source-bearing continuation name retains the same source annotations. -/
@[reducible] def NameAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : EffName → Prop
  | .cont p | .caught p | .caughtError p | .onValue p | .fin p | .onCause p | .loop p
  | .scopeOpen p | .scopeProvide p _ | .scopeBody p _ | .forkScopedIn p
  | .acquireCtx p | .acquireIn p _ | .acquired p _ _ | .releaseUnder p _ _ | .releaseBody p _ _ =>
    point p
  | .afterScopeAdd _ fin => FinAt point env writes fin
  | .withWaiter base _ _ => NameAt point env writes base
  | .store name => StoreNameAt point env writes name
  | .provideMask _ region | .updateThen _ region _ | .bodyThen region _ _ => RegionAt point env writes region
  | .gen _ _ _ | .provideLayerWith _ | .provideLayerBody _
  | .buildWithScopeFromContext _ _ | .withMemoMapThen _ _ | .fromBuildThen _ _
  | .memoize _ _ _ | .buildIntoLayerScope _ _ _ | .thenBuildInto _ _ _
  | .freshThen _ _ | .provideThen _ _ _ _ | .mergeChildren _ _ | .mergeForkOne _ _ _ _ _
  | .mergeForkNext _ _ _ _ _ | .mergeAllChildren _ _ | .mergeAllForkOne _ _ _ _ _
  | .mergeAllForkNext _ _ _ _ _ => False
  | _ => True

/-- Native thunks retain each source or stored environment they can expose. -/
@[reducible] def ThunkAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) : EffThunk → Prop
  | .pure p | .body p | .act p | .forkInAt p _ | .releaseMasked p _ | .acquireMasked p _ =>
    point p
  | .op op => OpAt point env writes op
  | .store thunk => StoreThunkAt point env writes thunk
  | .provideMasked _ region _ | .restoreRegion region _ => RegionAt point env writes region
  | .memoLookup _ _ _ | .forkLayer _ _ _ => False
  | _ => True

/-- The generated runtime-code fold reads the parameterized native slots. -/
abbrev CodeAt (point : Point → Prop) (env : List Val → Prop) (writes : SyncOp → Prop) :=
  CodeClosure.Code (NameAt point env writes) (ThunkAt point env writes)

end Effect4.Program.CodeClosure.Qualified
