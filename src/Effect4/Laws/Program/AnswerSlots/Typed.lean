import Effect4.Laws.Program.AnswerSlots.Initialization
import Effect4.Laws.Machine.AnswerFlowHead

/-!
Concept: store-typing R4 and scope-lifetime-finalization R11.
Question: protected acquired callbacks retain their exact connection answer class.
Reach: annotations of existing native code, names, captures and source operations.
Limit: initialization, the dynamic store invariant and command closure remain separate.
Consumer: the stable native answer-flow class of Workers and QueueWorkers.
-/
set_option autoImplicit false
namespace Effect4.Program.AnswerSlots.Typed
open Effect4 Effect4.Machine Effect4.Program

/-- The stable graph distinguishes ordinary answers from each acquisition's literal answer. -/
inductive Kind
  | root
  | connection (identity : Nat)
deriving DecidableEq

/-- A crew supplies its actual source, initialized bindings and acquisition positions. -/
structure Spec where
  root : NativeEff
  table : RowTable
  bindings : List Val
  identities : List Nat
  acquirePath : Nat → List Nat
  acquiredIndex : Nat → Nat
  sites : ∀ identity ∈ identities, SourceScope.AcquisitionAt root (acquirePath identity)
  complete : ∀ path, SourceScope.AcquisitionAt root path →
    ∃ identity ∈ identities, path = acquirePath identity
  acquisitionLevel : ∀ identity ∈ identities,
    SourceScope.levelAt (.eff root) 0 (acquirePath identity) = some (acquiredIndex identity)
  acquisitionBody : ∀ identity ∈ identities, ∃ note,
    Node.at_ (.eff root) (acquirePath identity ++ [0]) =
      some (.eff (.bind note (.succeed (.lit (.nat identity)))))

/-- The selected acquisition paths of the crew. -/
def Spec.acquisitions (spec : Spec) : List (List Nat) := spec.identities.map spec.acquirePath

/-- A captured point retains its own acquisition identity after the initialized leading slots. -/
def CapturedPoint (spec : Spec) (point : Point) : Prop :=
  Prefix spec.bindings point.env ∧ ∃ identity ∈ spec.identities,
    point.path = spec.acquirePath identity ∧
      point.env[spec.acquiredIndex identity]? = some (.nat identity)

/-- A source release point retains the acquired identity its writer reads. -/
def ReleasePoint (spec : Spec) (point : Point) : Prop :=
  SourceScope.At spec.root point ∧ Prefix spec.bindings point.env ∧
    ∃ identity ∈ spec.identities, point.path = spec.acquirePath identity ++ [1] ∧
      point.env[spec.acquiredIndex identity]? = some (.nat identity)

/-- A source point is ordinary or carries its selected release's acquired identity. -/
def PointPermission (spec : Spec) (point : Point) : Prop :=
  Ordinary spec.acquisitions point ∨ ∃ identity ∈ spec.identities,
    point.path = spec.acquirePath identity ++ [1] ∧
      point.env[spec.acquiredIndex identity]? = some (.nat identity)

/-- Every source operation retains either ordinary entry or its certified release identity. -/
def SourcePoint (spec : Spec) (point : Point) : Prop :=
  SourceScope.At spec.root point ∧ Prefix spec.bindings point.env ∧
    PointPermission spec point

/-- Foreign finalizers retain the source capture and the actual acquired identity. -/
def FinAt (spec : Spec) : FinName → Prop
  | .foreign capture => SourceScope.FinAt spec.root (.foreign capture) ∧
      CapturedPoint spec (Point.ofCapture capture)
  | fin => SourceScope.FinAt spec.root fin

/-- A native source write retains its actual source point, request and environment. -/
def OperationSource (spec : Spec) (operation : SyncOp) : Prop :=
  ∃ (point : Point) (row : NativeOp) (request : Term) (value : Val),
    SourcePoint spec point ∧
      Node.at_ (.eff spec.root) point.path = some (.eff (.perform row request)) ∧
      evalTerm point.env request = some value ∧ row.syncOpOf point.env value = some operation

/-- Update operations retain their source provenance; registrations retain their acquired capture. -/
def OpAt (spec : Spec) (operation : SyncOp) : Prop :=
  match operation with
  | .refMake _ | .refSet _ _ | .refGetAndSet _ _ | .refSetAndGet _ _
  | .refUpdate _ _ _ | .refGetAndUpdate _ _ _ | .refUpdateAndGet _ _ _
  | .refUpdateSome _ _ _ | .refGetAndUpdateSome _ _ _ | .refUpdateSomeAndGet _ _ _
  | .refModify _ _ _ | .refModifySome _ _ _ => OperationSource spec operation
  | .scopeAdd _ fin => FinAt spec fin
  | _ => True

/-- Stored program wrappers retain protected captured finalizers and source writes. -/
def ProgAt (spec : Spec) : ProgName → Prop
  | .syncOp op => OpAt spec op
  | .intoDeferred body _ | .intoBody body _ | .forkThen body _ _ | .forkOnly body _
  | .forkInScope body _ _ | .forkScopedOf body _ | .awaitAllNew body => ProgAt spec body
  | .finalizerOf fin _ => FinAt spec fin
  | .onExitOf body fin _ => ProgAt spec body ∧ FinAt spec fin
  | .seqOf first second => ProgAt spec first ∧ ProgAt spec second
  | .closeWalk _ order _ => ∀ fin ∈ order, FinAt spec fin
  | _ => True

/-- Stored callback wrappers retain protected captures. -/
def StoreNameAt (spec : Spec) : Name → Prop
  | .seq next | .snapshotThen next => ProgAt spec next
  | .withWaiter base _ _ => StoreNameAt spec base
  | .finalizerName fin => FinAt spec fin
  | .closeSeq order _ _ => ∀ fin ∈ order, FinAt spec fin
  | _ => True

/-- Stored action wrappers retain their protected delayed programs. -/
def StoreActionAt (spec : Spec) : ActionName → Prop
  | .fork body _ | .forkIn body _ _ | .forkScoped body _ | .setInterruptible body _ => ProgAt spec body
  | .closePar order _ => ∀ fin ∈ order, FinAt spec fin
  | _ => True

/-- Stored thunks retain their protected delayed code and finalizers. -/
def StoreThunkAt (spec : Spec) : Thunk → Prop
  | .op op => OpAt spec op
  | .body body => ProgAt spec body
  | .act action => StoreActionAt spec action
  | .foreign capture _ => FinAt spec (.foreign capture)
  | .park _ => True

/-- A service region resolves only an ordinary or certified release point. -/
def RegionAt (spec : Spec) : Region → Prop
  | .program point => SourcePoint spec point
  | _ => False

/-- Protected callbacks cannot receive an ordinary unknown answer as an acquired identity. -/
def ProtectedName (spec : Spec) : EffName → Prop
  | .acquired _ _ _ => False
  | .acquireCtx point | .acquireIn point _ =>
    SourcePoint spec point ∧ ∃ identity ∈ spec.identities, point.path = spec.acquirePath identity
  | .cont point | .caught point | .caughtError point | .onValue point | .fin point | .onCause point
  | .loop point | .scopeOpen point | .scopeProvide point _ | .scopeBody point _ | .forkScopedIn point =>
    SourcePoint spec point
  | .provideMask _ region | .updateThen _ region _ | .bodyThen region _ _ => RegionAt spec region
  | .afterScopeAdd _ fin => FinAt spec fin
  | .releaseUnder p _ _ | .releaseBody p _ _ => CapturedPoint spec p
  | .withWaiter base _ _ => ProtectedName spec base
  | .store name => StoreNameAt spec name
  | _ => True

/-- Source, prefix and acquired-capture annotations meet at the actual continuation name. -/
def OrdinaryName (spec : Spec) (name : EffName) : Prop :=
  SourceScope.NameAt spec.root name ∧ AnswerSlots.NameAt spec.bindings name ∧ ProtectedName spec name

/-- Ordinary callbacks keep the broad class; the two acquisition edges retain their exact literal. -/
def NameAt (spec : Spec) : Kind → Kind → EffName → Prop
  | .root, .root, name => OrdinaryName spec name
  | .root, .connection identity, .cont point =>
    identity ∈ spec.identities ∧ SourceScope.NameAt spec.root (.cont point) ∧
      SourcePoint spec point ∧ point.path = spec.acquirePath identity ++ [0]
  | .connection identity, .root, .acquired point ctx scope =>
    identity ∈ spec.identities ∧ SourceScope.NameAt spec.root (.acquired point ctx scope) ∧
      SourcePoint spec point ∧ point.path = spec.acquirePath identity
  | _, _, _ => False

/-- A stable thunk retains its source and prefix, with certified release points and registrations. -/
def ThunkAt (spec : Spec) (thunk : EffThunk) : Prop :=
  SourceScope.ThunkAt spec.root thunk ∧ AnswerSlots.ThunkAt spec.bindings thunk ∧
    match thunk with
    | .op op => OpAt spec op
    | .store thunk => StoreThunkAt spec thunk
    | .releaseMasked point _ => ReleasePoint spec point
    | .pure point | .body point | .act point | .forkInAt point _ | .acquireMasked point _ => SourcePoint spec point
    | .provideMasked _ region _ | .restoreRegion region _ => RegionAt spec region
    | _ => True

/-- Each successful connection answer is its own literal identity. -/
def ValueAt : Kind → Val → Prop
  | .root, _ => True
  | .connection identity, value => value = .nat identity

/-- The stable native graph records the actual intermediate answer class of every success binder. -/
def CodeAt (spec : Spec) (kind : Kind) : NCode → Prop
  | .success value => ValueAt kind value
  | .failure _ => True
  | .onSuccess body name => ∃ input, CodeAt spec input body ∧ NameAt spec input kind name
  | .onSuccessConst body next => CodeAt spec .root body ∧ CodeAt spec kind next
  | .suspend (.body point) =>
    (point.fuel = 0 ∧ SourcePoint spec point) ∨ (kind = .root ∧ ThunkAt spec (.body point))
  | .sync thunk | .suspend thunk | .withFiber thunk => kind = .root ∧ ThunkAt spec thunk
  | .onFailure body name | .onExit body name _ =>
    kind = .root ∧ CodeAt spec .root body ∧ NameAt spec .root .root name
  | .onSuccessAndFailure body success failure =>
    kind = .root ∧ CodeAt spec .root body ∧ NameAt spec .root .root success ∧ NameAt spec .root .root failure
  | .exitFrame body => kind = .root ∧ CodeAt spec .root body
  | .iterator name _ | .whileLoop name _ | .asyncFinalizer name => kind = .root ∧ NameAt spec .root .root name
  | .async register _ cancel => kind = .root ∧ NameAt spec .root .root register ∧
      ∀ name ∈ cancel, NameAt spec .root .root name
  | _ => kind = .root

/-- The stable graph uses the actual native finalizer interpreter, including onExit interception. -/
def model (spec : Spec) (view : List (FiberId × ExitV)) : AnswerFlow.Model (ν := EffName) (σ := EffThunk)
    (β := Val) (ε := Err) (δ := Defect) (ι := FiberId) (α := Ann) Unit Kind where
  future := fun _ _ => True
  future_refl _ := trivial
  future_trans _ _ _ _ _ := trivial
  value := fun _ => ValueAt
  cause := fun _ _ _ => True
  code := fun _ => CodeAt spec
  finalizer := fun _ name exit =>
    ((interpAt spec.root view spec.table).finalizerProgram name exit).map
      (finalizerCode (interpAt spec.root view spec.table) exit)
  success := fun _ _ _ good => good
  failure := fun _ _ _ _ => trivial
end Effect4.Program.AnswerSlots.Typed
