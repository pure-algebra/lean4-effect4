import Effect4.Laws.Program.AnswerSlots.Points

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: stable native syntax retains the root bindings used by the crew log proofs.
Reach: existing code, continuation names, operations, program names and finalizer captures.
Limit: this annotation supplies no allocation, acquired identity or history proof.
Consumer: the answer-flow stable code class for Workers and QueueWorkers.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots
open Effect4 Effect4.Machine Effect4.Program

/-- A foreign finalizer retains its immutable leading bindings. -/
def FinAt (bindings : List Val) : FinName → Prop
  | .foreign capture => Prefix bindings capture.env
  | _ => True

/-- Source update operations and registrations retain their captured leading bindings. -/
def OpAt (bindings : List Val) : SyncOp → Prop
  | .refUpdate _ _ env | .refGetAndUpdate _ _ env | .refUpdateAndGet _ _ env
  | .refUpdateSome _ _ env | .refGetAndUpdateSome _ _ env | .refUpdateSomeAndGet _ _ env
  | .refModify _ _ env | .refModifySome _ _ env => Prefix bindings env
  | .scopeAdd _ fin => FinAt bindings fin
  | _ => True

/-- Stored program wrappers retain every captured environment they can expose. -/
def ProgAt (bindings : List Val) : ProgName → Prop
  | .syncOp op => OpAt bindings op
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => ProgAt bindings body
  | .finalizerOf fin _ => FinAt bindings fin
  | .onExitOf body fin _ => ProgAt bindings body ∧ FinAt bindings fin
  | .seqOf first second => ProgAt bindings first ∧ ProgAt bindings second
  | .closeWalk _ order _ => ∀ fin ∈ order, FinAt bindings fin
  | _ => True

/-- Stored callbacks retain their delayed captured environments. -/
def StoreNameAt (bindings : List Val) : Name → Prop
  | .seq next | .snapshotThen next => ProgAt bindings next
  | .withWaiter base _ _ => StoreNameAt bindings base
  | .finalizerName fin => FinAt bindings fin
  | .closeSeq order _ _ => ∀ fin ∈ order, FinAt bindings fin
  | _ => True

/-- Stored actions retain the captured environments of their programs. -/
def StoreActionAt (bindings : List Val) : ActionName → Prop
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ => ProgAt bindings body
  | .closePar order _ => ∀ fin ∈ order, FinAt bindings fin
  | _ => True

/-- Stored thunks retain the captured environments of their programs and registrations. -/
def StoreThunkAt (bindings : List Val) : Thunk → Prop
  | .op op => OpAt bindings op
  | .body body => ProgAt bindings body
  | .act action => StoreActionAt bindings action
  | .foreign capture _ => FinAt bindings (.foreign capture)
  | .park _ => True

/-- A direct program region retains its leading bindings. -/
def RegionAt (bindings : List Val) : Region → Prop
  | .program p => Prefix bindings p.env
  | _ => False

/-- Every source-bearing continuation name retains the same initialized leading bindings. -/
def NameAt (bindings : List Val) : EffName → Prop
  | .cont p | .caught p | .caughtError p | .onValue p | .fin p | .onCause p | .loop p
  | .scopeOpen p | .scopeProvide p _ | .scopeBody p _ | .forkScopedIn p
  | .acquireCtx p | .acquireIn p _ | .acquired p _ _ | .releaseUnder p _ _ | .releaseBody p _ _ =>
    Prefix bindings p.env
  | .afterScopeAdd _ fin => FinAt bindings fin
  | .withWaiter base _ _ => NameAt bindings base
  | .store name => StoreNameAt bindings name
  | .provideMask _ region | .updateThen _ region _ | .bodyThen region _ _ => RegionAt bindings region
  | .gen _ _ _ | .provideLayerWith _ | .provideLayerBody _
  | .buildWithScopeFromContext _ _ | .withMemoMapThen _ _ | .fromBuildThen _ _
  | .memoize _ _ _ | .buildIntoLayerScope _ _ _ | .thenBuildInto _ _ _
  | .freshThen _ _ | .provideThen _ _ _ _ | .mergeChildren _ _ | .mergeForkOne _ _ _ _ _
  | .mergeForkNext _ _ _ _ _ | .mergeAllChildren _ _ | .mergeAllForkOne _ _ _ _ _
  | .mergeAllForkNext _ _ _ _ _ => False
  | _ => True

/-- Native thunks retain each source or stored environment they can expose. -/
def ThunkAt (bindings : List Val) : EffThunk → Prop
  | .pure p | .body p | .act p | .forkInAt p _ | .releaseMasked p _ | .acquireMasked p _ =>
    Prefix bindings p.env
  | .op op => OpAt bindings op
  | .store thunk => StoreThunkAt bindings thunk
  | .provideMasked _ region _ | .restoreRegion region _ => RegionAt bindings region
  | .memoLookup _ _ _ | .forkLayer _ _ _ => False
  | _ => True

/-- The native code graph retains leading bindings in every delayed source-bearing field. -/
def CodeAt (bindings : List Val) : NCode → Prop
  | .sync thunk | .suspend thunk | .withFiber thunk => ThunkAt bindings thunk
  | .iterator name _ | .whileLoop name _ | .asyncFinalizer name => NameAt bindings name
  | .onSuccess body name | .onFailure body name | .onExit body name _ =>
    CodeAt bindings body ∧ NameAt bindings name
  | .onSuccessConst body next => CodeAt bindings body ∧ CodeAt bindings next
  | .onSuccessAndFailure body success failure =>
    CodeAt bindings body ∧ NameAt bindings success ∧ NameAt bindings failure
  | .exitFrame body => CodeAt bindings body
  | .async register _ cancel => NameAt bindings register ∧ ∀ name ∈ cancel, NameAt bindings name
  | _ => True
end Effect4.Program.AnswerSlots
