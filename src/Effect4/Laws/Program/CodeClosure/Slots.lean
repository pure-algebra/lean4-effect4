import Effect4.Laws.Program.CodeClosure.Predicate

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: actual callback closure retains source point assertions and captured environments.
Consumer: the Prefix callback instance and Timeout's attempt-source refinement.
Reach: existing native and stored names; these predicates establish no initialized history.
-/
set_option autoImplicit false
namespace Effect4.Program.CodeClosure.Slots
open Effect4 Effect4.Machine Effect4.Program

/-- A foreign finalizer retains its source annotation. -/
@[reducible] def FinAt (point : Point → Prop) (_env : List Val → Prop) : FinName → Prop
  | .foreign capture => point (Point.ofCapture capture)
  | _ => True

/-- Source update operations and registrations retain their captured environment assertion. -/
@[reducible] def OpAt (point : Point → Prop) (env : List Val → Prop) : SyncOp → Prop
  | .refUpdate _ _ environment | .refGetAndUpdate _ _ environment | .refUpdateAndGet _ _ environment
  | .refUpdateSome _ _ environment | .refGetAndUpdateSome _ _ environment | .refUpdateSomeAndGet _ _ environment
  | .refModify _ _ environment | .refModifySome _ _ environment => env environment
  | .scopeAdd _ fin => FinAt point env fin
  | _ => True

/-- Stored program wrappers retain every captured environment they can expose. -/
@[reducible] def ProgAt (point : Point → Prop) (env : List Val → Prop) : ProgName → Prop
  | .syncOp op => OpAt point env op
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => ProgAt point env body
  | .finalizerOf fin _ => FinAt point env fin
  | .onExitOf body fin _ => ProgAt point env body ∧ FinAt point env fin
  | .seqOf first second => ProgAt point env first ∧ ProgAt point env second
  | .closeWalk _ order _ => ∀ fin ∈ order, FinAt point env fin
  | _ => True

/-- Stored callbacks retain their delayed captured environments. -/
@[reducible] def StoreNameAt (point : Point → Prop) (env : List Val → Prop) : Name → Prop
  | .seq next | .snapshotThen next => ProgAt point env next
  | .withWaiter base _ _ => StoreNameAt point env base
  | .finalizerName fin => FinAt point env fin
  | .closeSeq order _ _ => ∀ fin ∈ order, FinAt point env fin
  | _ => True

/-- Stored actions retain the captured environments of their programs. -/
@[reducible] def StoreActionAt (point : Point → Prop) (env : List Val → Prop) : ActionName → Prop
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ => ProgAt point env body
  | .closePar order _ => ∀ fin ∈ order, FinAt point env fin
  | _ => True

/-- Stored thunks retain the captured environments of their programs and registrations. -/
@[reducible] def StoreThunkAt (point : Point → Prop) (env : List Val → Prop) : Thunk → Prop
  | .op op => OpAt point env op
  | .body body => ProgAt point env body
  | .act action => StoreActionAt point env action
  | .foreign capture _ => FinAt point env (.foreign capture)
  | .park _ => True

/-- A direct program region retains its source annotations. -/
@[reducible] def RegionAt (point : Point → Prop) (_env : List Val → Prop) : Region → Prop
  | .program p => point p
  | _ => False

/-- Every source-bearing continuation name retains the same source annotations. -/
@[reducible] def NameAt (point : Point → Prop) (env : List Val → Prop) : EffName → Prop
  | .cont p | .caught p | .caughtError p | .onValue p | .fin p | .onCause p | .loop p
  | .scopeOpen p | .scopeProvide p _ | .scopeBody p _ | .forkScopedIn p
  | .acquireCtx p | .acquireIn p _ | .acquired p _ _ | .releaseUnder p _ _ | .releaseBody p _ _ =>
    point p
  | .afterScopeAdd _ fin => FinAt point env fin
  | .withWaiter base _ _ => NameAt point env base
  | .store name => StoreNameAt point env name
  | .provideMask _ region | .updateThen _ region _ | .bodyThen region _ _ => RegionAt point env region
  | .gen _ _ _ | .provideLayerWith _ | .provideLayerBody _
  | .buildWithScopeFromContext _ _ | .withMemoMapThen _ _ | .fromBuildThen _ _
  | .memoize _ _ _ | .buildIntoLayerScope _ _ _ | .thenBuildInto _ _ _
  | .freshThen _ _ | .provideThen _ _ _ _ | .mergeChildren _ _ | .mergeForkOne _ _ _ _ _
  | .mergeForkNext _ _ _ _ _ | .mergeAllChildren _ _ | .mergeAllForkOne _ _ _ _ _
  | .mergeAllForkNext _ _ _ _ _ => False
  | _ => True

/-- Native thunks retain each source or stored environment they can expose. -/
@[reducible] def ThunkAt (point : Point → Prop) (env : List Val → Prop) : EffThunk → Prop
  | .pure p | .body p | .act p | .forkInAt p _ | .releaseMasked p _ | .acquireMasked p _ =>
    point p
  | .op op => OpAt point env op
  | .store thunk => StoreThunkAt point env thunk
  | .provideMasked _ region _ | .restoreRegion region _ => RegionAt point env region
  | .memoLookup _ _ _ | .forkLayer _ _ _ => False
  | _ => True

/-- The generated runtime-code fold reads the parameterized native slots. -/
abbrev CodeAt (point : Point → Prop) (env : List Val → Prop) :=
  CodeClosure.Code (NameAt point env) (ThunkAt point env)

end Effect4.Program.CodeClosure.Slots
