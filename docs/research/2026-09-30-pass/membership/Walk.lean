import Effect4.Laws.Program.Typed.Assembly
import Test.Program.LoadedAdmission

/-!
# Research probe: the slice-5 program judgment, stack walk and delivery, restated over `Fits`

Seat MEMBERSHIP, 2026-09-30 pass. Base `be15b062`. The migration measured: every declaration of
`Typed/Admission.lean`, `Typed/Residual.lean` and `Typed/Stack.lean` whose statement or body
mentions `StrongValue`, `StrongExit` or `ServicesOk`, copied at its line range, renamed
(`walk_baseline.py` builds that renamed-only copy), then edited until it checks with `Fits`
and `FitsExit` in place of the old judgments. The diff between the baseline and this file is
the migration's proof effort for these modules.

The shared definitions block is a verbatim copy of `Fits.lean`'s (`prelude_check.py`).
-/

set_option autoImplicit false

namespace Research.Pass.Membership
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Program.Denote Effect4.Laws.Effects Contracts

/-- The typed world (`Laws/Program/Typed/World.lean:52`). -/
abbrev W := Effect4.Program.Typed.World

/-! ## Capability declarations, read from the world's tables

An invariant handle (`refOf`, `deferredOf`, and the native cell and deferred spellings) relates
its declared type to the static type through `inv`. Two readings are measured here:
`Equiv` (subtyping both ways, which is how `Ty.sub` states invariance, `Program/Ty.lean:452-453`)
and equality (how `HandlesFit` states it, `Typed/Admission.lean:41-42`). `Fits` takes `Equiv`;
`FitsEq` takes equality. -/

/-- The relation an invariant handle's declared type must bear to the static type. -/
abbrev Inv := Ty → Ty → Prop

/-- Invariance as `Ty.sub` reads it: subtyping both ways. -/
def Equiv (declared t : Ty) : Prop := declared.sub t = true ∧ t.sub declared = true

/-- A cell declared at a type `inv`-related to `t`. -/
def RefDeclared (w : W) (inv : Inv) (key : RefKey) (t : Ty) : Prop :=
  ∃ t', w.Ρ key = some t' ∧ inv t' t

/-- A deferred declared at columns `inv`-related to `(a, e)`. -/
def PromiseDeclared (w : W) (inv : Inv) (key : DeferredKey) (a e : Ty) : Prop :=
  ∃ a' e', w.«Π» key = some (a', e') ∧ inv a' a ∧ inv e' e

/-- A fiber declared at a type below `(a, e)`: the fiber handle is covariant. -/
def FiberDeclared (w : W) (id : FiberId) (a e : Ty) : Prop :=
  ∃ fty, w.Γ id = some fty ∧ fty.answer.sub a = true ∧ fty.error.sub e = true

/-- Declared liveness: every cell, deferred and fiber handle the value names is declared in the
world's tables. The table form, not the store-length form of `HandlesLive`: the two agree under
`WorldValid` (`live_iff_handlesLive` below), and only the table form follows from an allocation's
post (`storePost (.refMake _)` names `w'.Ρ key`, never the heap length). -/
def Live (w : W) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => (w.Ρ key).isSome = true
  | .promise key => (w.«Π» key).isSome = true
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

/-- The reserved and external handle spellings (`Val.hasTy`'s `.handle` arm), with the native
cell and deferred spellings read as their declarations: `Ref.Ref<number>` is a cell declared at
`nat`, `Deferred.Deferred<number, number>` a deferred declared at `(nat, nat)`. -/
def HandleFits (w : W) (inv : Inv) (kind : UInt8) (index : Nat) (target : String) : Prop :=
  match HandleKind.ofByte? kind with
  | some .cell => target = NativeOp.refTarget ∧ RefDeclared w inv ⟨index⟩ .nat
  | some .promise => target = NativeOp.deferredTarget ∧ PromiseDeclared w inv ⟨index⟩ .nat .nat
  | some .scope => target = Ty.scopeTarget
  | some .external => externalHandleTarget target = true ∧
      w.state.externals.allocated[index]? = some target
  | _ => False

/-- Membership at a service's static type (decision row 90): the service table's types are
scalars and non-context handles (`nativeServiceTypes`, `nativeReservedServiceTypes`), so this
needs no recursion; `flatFits_fits` connects it to `Fits`. -/
def FlatFits (w : W) (inv : Inv) (v : Val) : Ty → Prop
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .string => match v with | .str _ => True | _ => False
  | .handle target =>
    match v with | .handle kind index => HandleFits w inv kind index target | _ => False
  | _ => False

/-- A context's services fit their keys' static types. -/
def ServicesFit (w : W) (inv : Inv) (services : Env.Ctx) : Prop :=
  ∀ key sv sty, services.getV key = some sv → nativeServiceTy key = some sty →
    FlatFits w inv sv sty

/-- Every typed failure of a cause has an image satisfying `member`; defects and interruptions
are outside the error column (`reasonAdmits`, `Program/ErrorImage.lean:31`). -/
def CauseFits (member : Val → Prop) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ member v
  | .die _ _ | .interrupt _ _ => True

/-- **The membership judgment.** The arms and value shapes are `Val.hasTy`'s, one for one; the
handle leaves read the world's declaration tables; `unknown` requires declared liveness. -/
def FitsInv (w : W) (inv : Inv) (v : Val) : Ty → Prop
  | .never => False
  | .unit => match v with | .unit => True | _ => False
  | .nat => match v with | .nat _ => True | _ => False
  | .int => False
  | .string => match v with | .str _ => True | _ => False
  | .bool => match v with | .bool _ => True | _ => False
  | .handle target =>
    match v with
    | .handle kind index => HandleFits w inv kind index target
    | _ => target = Ty.contextTarget ∧
        ∃ ctx, Val.context? v = some ctx ∧ ServicesFit w inv ctx.services ∧ Live w v
  | .option a =>
    match v with
    | .none => True
    | .some x => FitsInv w inv x a
    | _ => False
  | .list a =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ∀ id ∈ ids, FitsInv w inv (Val.fiber id) a
      | none => False
    | .list values => ∀ x ∈ values, FitsInv w inv x a
    | _ => False
  | .prod a b =>
    match v with
    | .list [x, y] => FitsInv w inv x a ∧ FitsInv w inv y b
    | _ => False
  | .except e a =>
    match v with
    | .ctor 0 [err] => FitsInv w inv err e
    | .ctor 1 [val] => FitsInv w inv val a
    | _ => False
  | .exitOf a e =>
    match v with
    | Val.exitOk x => FitsInv w inv x a
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => CauseFits (fun x => FitsInv w inv x e) c
      | none => False
    | _ => False
  | .causeOf e =>
    match Val.cause? v with
    | some c => CauseFits (fun x => FitsInv w inv x e) c
    | none => False
  | .fiberOf a e =>
    match v with
    | Value.fiber index => FiberDeclared w ⟨index⟩ a e
    | _ => False
  | .union l r => FitsInv w inv v l ∨ FitsInv w inv v r
  | .lit s => match v with | .str s' => s' = s | _ => False
  | .refOf t =>
    match v with
    | Value.cell index => RefDeclared w inv ⟨index⟩ t
    | _ => False
  | .deferredOf a e =>
    match v with
    | Value.promise index => PromiseDeclared w inv ⟨index⟩ a e
    | _ => False
  | .var _ => False
  | .unknown => Live w v

/-- **The proposed judgment**: invariant handles read as `Ty.sub` reads them. -/
abbrev Fits (w : W) (v : Val) (ty : Ty) : Prop := FitsInv w Equiv v ty

/-- The same recursion with `HandlesFit`'s equality at invariant handles. -/
abbrev FitsEq (w : W) (v : Val) (ty : Ty) : Prop := FitsInv w (· = ·) v ty

/-- The exit judgment is the value judgment at the reified exit (`reifyExitVal`,
`Machine/Stores.lean:1637`): an exit is a value of `Exit<A, E>`. -/
def FitsExit (w : W) (ty : EffTy) (ex : ExitV) : Prop :=
  Fits w (reifyExitVal ex) (.exitOf ty.answer ty.error)

/-- The cause judgment, at an error column. -/
abbrev FitsCause (w : W) (errTy : Ty) (c : CauseV) : Prop :=
  CauseFits (fun x => Fits w x errTy) c

/-! ### Four basic facts every probe file uses -/

/-- A successful exit fits exactly when its value fits the answer column. -/
theorem fitsExit_success_iff (w : W) (ty : EffTy) (v : Val) :
    FitsExit w ty (.success v) ↔ Fits w v ty.answer := Iff.rfl

/-- A failed exit fits exactly when its cause fits the error column. -/
theorem fitsExit_failure_iff (w : W) (ty : EffTy) (c : CauseV) :
    FitsExit w ty (.failure c) ↔ FitsCause w ty.error c := by
  unfold FitsExit
  simp only [reifyExitVal, Fits, FitsInv, Store.Image.ofVal_toVal]

theorem causeFits_map {m1 m2 : Val → Prop} (hm : ∀ x, m1 x → m2 x) {c : CauseV}
    (h : CauseFits m1 c) : CauseFits m2 c := by
  intro r hr
  have hr' := h r hr
  cases r with
  | fail e ann =>
    obtain ⟨v, hv, h1⟩ := hr'
    exact ⟨v, hv, hm v h1⟩
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- A service's membership at a flat type is membership. -/
theorem flatFits_fitsInv {w : W} {inv : Inv} {v : Val} {t : Ty} (h : FlatFits w inv v t) :
    FitsInv w inv v t := by
  cases t
  case unit => exact h
  case nat => exact h
  case bool => exact h
  case string => exact h
  case handle target =>
    simp only [FlatFits] at h
    split at h
    · exact h
    · exact h.elim
  all_goals exact h.elim

/-! End of the shared block. -/

/-! ## The two names the restated declarations read -/

/-- The old argument order, so the restated statements keep their spelling. -/
abbrev StrongValueF (w : W) (ty : Ty) (v : Val) : Prop := Fits w v ty

/-- The context's services at the `Ty.sub` reading. -/
abbrev ServicesFitE (w : W) (services : Env.Ctx) : Prop := ServicesFit w Equiv services

/-! ## The restated declarations (baseline segments, edited) -/

-- src/Effect4/Laws/Program/Typed/Admission.lean:77-80
/-- An evaluation environment typed pointwise at the corresponding static types. -/
def EnvTypedF (w : W) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → StrongValueF w ty v

-- src/Effect4/Laws/Program/Typed/Admission.lean:90-119
/-- D13 source admission at an addressed program node, under the source's row table
(`E4-SCHED-CE-014`: the empty table refused bodies that perform a host row). -/
def PointTypedF (src : ProgramSource) (w : W) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check (nativeSignature src.table) env point.path e = .ok ty ∧
    EnvTypedF w env point.env

/-- Admitted bodies covering all six `Body` constructors. -/
inductive BodyTypedF (src : ProgramSource) (w : W) : Body → EffTy → Prop
  | at_ (p : Point) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.at_ p) ty
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : FitsExit w ty ex) :
      BodyTypedF src w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTypedF src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTypedF src w p ty) :
      BodyTypedF src w (.layerBuild p m scope) ty

/-- A strong value at the answer column is a strong successful exit. -/
theorem fitsExit_success (w : W) (ty : EffTy) (v : Val) (h : StrongValueF w ty.answer v) :
    FitsExit w ty (.success v) := h

-- src/Effect4/Laws/Program/Typed/Admission.lean:127-168
/-- A clean failure fits every effect type at every world: the error column constrains
`Fail` reasons only. -/
theorem fitsExit_of_clean (w : W) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) : FitsExit w ty (.failure c) := by
  have hall : ∀ r ∈ c.reasons, r.tag ≠ .fail := by
    intro r hr
    exact bne_iff_ne.mp (List.all_eq_true.mp h r hr)
  rw [fitsExit_failure_iff]
  intro r hr
  have hne := hall r hr
  cases r with
  | fail e ann => exact absurd rfl hne
  | die _ _ => trivial
  | interrupt _ _ => trivial

/-- At a `never` error column a strong failure is clean: no value has type `never`. -/
theorem cleanExit_of_never_fits (w : W) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
    (h : FitsExit w ty (.failure c)) : cleanExit (.failure c) = true := by
  rw [fitsExit_failure_iff, never] at h
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  have hr' := h r hr
  cases r with
  | fail e ann =>
    obtain ⟨v, _, hv⟩ := hr'
    exact False.elim hv
  | die _ _ => rfl
  | interrupt _ _ => rfl

-- src/Effect4/Laws/Program/Typed/Residual.lean:34-86
def storePreF (root : ProgramSource) (w : W) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ StrongValueF w cert initial
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValueF w ty v
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValueF w ty v
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValueF w ty v
  | .refUpdate cell _ | .refGetAndUpdate cell _ | .refUpdateAndGet cell _
  | .refUpdateSome cell _ | .refGetAndUpdateSome cell _ | .refUpdateSomeAndGet cell _
  | .refModify cell _ | .refModifySome cell _ => ∃ ty, w.Ρ cell = some ty
  | .deferredMake => cert.1.closed = true ∧ cert.2.closed = true
  | .deferredIsDone key | .deferredPoll key | .deferredAwaitCleanup key _ _ => (w.«Π» key).isSome = true
  | .deferredCompleteWith key _ => (w.«Π» key).isSome = true
  | .deferredInterruptWith key _ => (w.«Π» key).isSome = true
  | .clockNow | .sleepCancel _ _ => True
  | .scopeMake _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ | .scopeFork _ _ => True
  | .memoFork _ | .memoComplete _ _ _ | .memoRelease _ _ => True
  -- the looked-up layer's own checked error type (decision row 90)
  | .memoGet layer _ => ∃ l lt, Node.at_ (.eff root.program) layer = some (.layer l) ∧
      Checker.checkLayer (nativeSignature root.table) layer l = .ok lt ∧ lt.error = cert
  | .memoBuild _ _ => cert.1.closed = true ∧ cert.2.closed = true

def storePostF (w' : W) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refUpdate _ _ | .refUpdateSome _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ | .refGetAndUpdateSome cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refUpdateAndGet cell _ | .refUpdateSomeAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValueF w' ty ans
  | .refModify _ _ | .refModifySome _ _ => ∃ n, ans = Val.nat n
  | .deferredMake => ∃ key : DeferredKey, ans = Val.promise key ∧ w'.«Π» key = some cert
  | .deferredIsDone _ => ∃ b, ans = Val.bool b
  | .deferredPoll _ => ∃ b, ans = Val.bool b
  | .deferredCompleteWith _ _ | .deferredInterruptWith _ _ | .deferredAwaitCleanup _ _ _ => ∃ b, ans = Val.bool b
  | .clockNow => ∃ n, ans = Val.nat n
  | .sleepCancel _ _ => ans = Val.unit
  | .scopeMake _ => ∃ sc, ans = Val.scopeHandle sc
  | .scopeAdd _ _ | .scopeRemove _ _ => ∃ b, ans = Val.bool b
  | .scopeIsClosed _ => ∃ b, ans = Val.bool b
  | .scopeFork _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoFork _ => ∃ id, ans = Val.memoMap id
  | .memoGet _ _ => ans = Val.unit ∨ ∃ cell owner, Val.memoHit? ans = some (cell, owner) ∧
      w'.«Π» cell = some (.handle Ty.contextTarget, cert)
  | .memoBuild _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoComplete _ _ _ | .memoRelease _ _ => ans = Val.unit

def Ψ_SF (root : ProgramSource) : Protocol W StoreSig where
  Cert := StoreCert
  pre := storePreF root
  post := storePostF

-- src/Effect4/Laws/Program/Typed/Residual.lean:116-259
def fiberPreF (root : ProgramSource) (w : W) (op : FiberOp) (cert : FiberCert op) : Prop :=
  match op with
  | .getId | .yieldNow _ | .ambientScope | .sync _ => True
  -- the context set keeps every service at its key's type (decision row 90)
  | .setContext ctx => ServicesFitE w ctx.services
  | .getContext => cert = .handle Ty.contextTarget
  | .await target _ => (w.Γ target).isSome = true
  | .awaitAll targets | .awaitAllFailFast targets =>
    ∃ a e, cert = .list (.exitOf a e) ∧ ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧
      fty.answer.sub a = true ∧ fty.error.sub e = true
  | .raceAll entrants _ => ∀ p ∈ entrants, ∃ ty, PointTypedF root w p ty ∧
      ty.answer.sub cert.answer = true ∧ ty.error.sub cert.error = true
  | .async register _ => asyncPre root w register cert
  | .suspend _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _ | .interruptAll _ _
  | .runIn _ _ | .awaitNewChildren _ => True
  | .guard_ _ | .unguard _ | .finishFinalizer _ | .scopeExit _ _ _ | .construction
  | .closeScope _ _ | .foreignRelease _ _ | .closeWalk _ _ _ | .closeIter _ _ _
  | .raceRegister _ | .cancelRace _ | .dropObservers _ | .frontier _ _ => True
  | .snapshotChildren => cert = .list (.fiberOf .unknown .unknown)
  | .scoped body => PointTypedF root w body cert
  | .mask _ body => BodyTypedF root w body cert
  | .forkScoped child _ _ => PointTypedF root w child cert
  | .fork body _ _ => BodyTypedF root w body cert
  | .forkIn child _ _ _ => PointTypedF root w child cert
  | .gen p => PointTypedF root w p cert
  | .loop p _ => PointTypedF root w p cert
  | .refuse _ => False

def fiberPostF (w' : W) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op with
  | .getId => ∃ (id : FiberId), ans = Val.nat id.value
  | .getContext | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren => StrongValueF w' cert ans
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ | .awaitNewChildren _ => ans = Val.unit
  | .ambientScope => ∃ sc, ans = Val.scopeHandle sc
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ FitsExit w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ StrongValueF w' ty.answer ans
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    FitsExit w' cert ans
  | .unguard ex | .finishFinalizer ex | .closeScope _ ex | .scopeExit _ _ ex | .closeIter _ _ ex => ans = ex
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ FitsExit w' cert ex
  -- a live frontier is never answered (fuel exhaustion is not an exit)
  | .frontier _ _ => False
  -- the completed exits a callback reads, each at its fiber's declared type
  | .construction => ∀ p ∈ ans, ∃ ty, w'.Γ p.1 = some ty ∧ FitsExit w' ty p.2
  | .suspend _ | .refuse _ => True

def Ψ_FF (root : ProgramSource) : Protocol W FiberSig where
  Cert := FiberCert
  pre := fiberPreF root
  post := fiberPostF

/-! ## The program judgment -/

/-- The one typing of a reference program at an effect type. Store and fiber operations follow
`Ψ_SF` and `Ψ_FF`: a certificate, its precondition, and a continuation for every answer the
postcondition admits at every later world. The fiber arm excludes the four control markers,
which have their own arms. A guard's body is typed at the guard's certified intermediate type
`mid`; the saved arm runs on the exits the guard row admits at `mid`, and an exit the arm does
not take must fit the outer type. `unguard` and `finishFinalizer` carry an exit at the current
type and type no continuation: the reference machine never resumes one (`evaluateFiberR`
hands the payload to `deliverR`; `popR`'s answer glue passes it to the next frame).
`scopeExit` carries its exit and keeps its continuation. -/
inductive TypedProgF (root : ProgramSource) : W → EffTy → RProgram → Prop
  | pure {w : W} {ty : EffTy} {ex : ExitV} (exit : FitsExit w ty ex) :
      TypedProgF root w ty (.pure ex)
  | store {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : (Ψ_SF root).Cert op) (pre : (Ψ_SF root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_SF root).post w' op cert ans → TypedProgF root w' ty (k ans)) :
      TypedProgF root w ty (.vis (.inl op) k)
  | fiber {w : W} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : (Ψ_FF root).Cert op) (pre : (Ψ_FF root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_FF root).post w' op cert ans →
        TypedProgF root w' ty (k ans)) :
      TypedProgF root w ty (.vis (.inr op) k)
  | guard {w : W} {ty : EffTy} {kind : GuardKind} {k : Option ExitV → RProgram}
      (mid : EffTy) (body : TypedProgF root w mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, fiberPostF w' (.guard_ kind) mid (some ex) →
        TypedProgF root w' ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → kind.hasExitArm ex = false →
        FitsExit w' ty ex) :
      TypedProgF root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex) : TypedProgF root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : W} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex) : TypedProgF root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : W} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, TypedProgF root w' ty (k ans)) :
      TypedProgF root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

namespace TypedProgF

theorem pure_inv {root : ProgramSource} {w : W} {ty : EffTy} {ex : ExitV}
    (h : TypedProgF root w ty (.pure ex)) : FitsExit w ty ex := by
  cases h with
  | pure exit => exact exit

theorem store_inv {root : ProgramSource} {w : W} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
    (h : TypedProgF root w ty (.vis (.inl op) k)) :
    ∃ cert : (Ψ_SF root).Cert op, (Ψ_SF root).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_SF root).post w' op cert ans → TypedProgF root w' ty (k ans) := by
  cases h with
  | store cert pre next => exact ⟨cert, pre, next⟩

/-- A guard's typing is exactly the saved frame's arrow (`Contracts.FrameAccepts.resume`) at
`mid`, with the body typed at `mid`. -/
theorem guard_inv {root : ProgramSource} {w : W} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProgF root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, TypedProgF root w mid (k none) ∧
      (∀ w', w.leHost w' → ∀ ex, fiberPostF w' (.guard_ kind) mid (some ex) →
        TypedProgF root w' ty (k (some ex))) ∧
      (∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → kind.hasExitArm ex = false →
        FitsExit w' ty ex) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip => exact ⟨mid, body, run, skip⟩

end TypedProgF

/-- FR-09's marker payload inversion: a typed `unguard` carries an exit at the current type. -/
theorem unguard_payload_invF (root : ProgramSource) (w : W) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProgF root w ty (.vis (.inr (.unguard ex)) k)) :
    FitsExit w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_invF (root : ProgramSource) (w : W) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProgF root w ty (.vis (.inr (.finishFinalizer ex)) k)) :
    FitsExit w ty ex := by
  cases h with
  | fiber _ _ notFinish _ _ _ _ => exact absurd rfl (notFinish ex)
  | finishFinalizer payload => exact payload

-- src/Effect4/Laws/Program/Typed/Residual.lean:261-308
/-! ## Interpreter hook contracts -/

/-! The recursive hook contracts use mutually inductive step witnesses. This is the
strictly positive form of the brief's existential resume clause: the resume constructor
stores its intermediate type and the next protocol witness. No new program syntax is
stored, and no termination theorem for arbitrary source code is asserted. -/
mutual
  inductive IteratorProtocolF (root : ProgramSource) (w : W) : EffTy → EffTy → EffName → Prop
    | step {tin tout : EffTy} {name : EffName}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValueF w tin.answer v →
          IteratorAnswerF root w tout ((interpR root.program).iterNext name v).2) :
        IteratorProtocolF root w tin tout name
  inductive IteratorAnswerF (root : ProgramSource) (w : W) :
      EffTy → IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
    | done {tout : EffTy} (result : Val) (typed : FitsExit w tout (.success result)) :
        IteratorAnswerF root w tout (.done result)
    | halt {tout : EffTy} (cause : CauseV) (typed : FitsExit w tout (.failure cause)) :
        IteratorAnswerF root w tout (.halt cause)
    | resume {tout : EffTy} (code : RProgram) (name : EffName) (tin : EffTy)
        (typed : TypedProgF root w tin code) (tail : IteratorProtocolF root w tin tout name) :
        IteratorAnswerF root w tout (.resume code name)
end

mutual
  inductive LoopProtocolF (root : ProgramSource) (w : W) : EffTy → EffTy → EffName → Val → Prop
    | step {tin tout : EffTy} {name : EffName} {cursor : Val}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValueF w tin.answer v →
          LoopAnswerF root w tout name ((interpR root.program).loopResume name cursor v)) :
        LoopProtocolF root w tin tout name cursor
  inductive LoopAnswerF (root : ProgramSource) (w : W) :
      EffTy → EffName → LoopNext Val RProgram → Prop
    | continue {tout : EffTy} {name : EffName} (cursor : Val) (body : RProgram) (tin : EffTy)
        (typed : TypedProgF root w tin body) (tail : LoopProtocolF root w tin tout name cursor) :
        LoopAnswerF root w tout name (.continue cursor body)
    | finish {tout : EffTy} {name : EffName} (code : RProgram) (typed : TypedProgF root w tout code) :
        LoopAnswerF root w tout name (.finish code)
end

/-- The three named hook arrows (slice 5 brief §3.3 as amended 2026-09-23). The async clause
types the cancellation only for an incoming failure that is itself typed at the frame's
type, the evidence `popR` holds at that arm (`E4-SCHED-CE-010`). -/
def frameProtocolsF (root : ProgramSource) : Contracts.FrameProtocols where
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, FitsExit w tin (.failure cause) →
    cause.hasInterrupts = true → TypedProgF root w tout ((interpR root.program).cancelThenFail name cause)
  iterator := IteratorProtocolF root
  loop := LoopProtocolF root

-- src/Effect4/Laws/Program/Typed/Residual.lean:319-344
theorem strongValue_bool_trueF (w : W) : StrongValueF w .bool (Val.bool true) := trivial

theorem strongExit_boolF (w : W) (v : Val) (hv : StrongValueF w .bool v) :
    FitsExit w (EffTy.pure .bool) (.success v) := hv

theorem settling_ref_allocationF (root : ProgramSource) (w : W) (_h0 : HeapTypedAt w ⟨0⟩ .nat) :
    TypedProgF root w (EffTy.pure .bool) refAllocGetProg := by
  refine TypedProgF.store (cert := Ty.bool) ⟨rfl, strongValue_bool_trueF w⟩ ?_
  intro w' _ ans hpost
  rcases hpost with ⟨key, rfl, hkey⟩
  dsimp only [refAllocCont]
  refine TypedProgF.store (cert := ()) ⟨Ty.bool, hkey⟩ ?_
  intro w'' hle v hpost'
  rcases hpost' with ⟨ty', hkey', hv⟩
  have extendsΡ := hle.1.2.2.2.1
  have sameKey : w''.Ρ key = some Ty.bool := extendsΡ key Ty.bool hkey
  change w''.Ρ key = some ty' at hkey'
  rw [sameKey] at hkey'
  cases hkey'
  exact TypedProgF.pure (strongExit_boolF w'' v hv)

-- src/Effect4/Laws/Program/Typed/Residual.lean:358-387
theorem settling_forkF (root : ProgramSource) (w : W) (child : Body) (cert : EffTy)
    (hbody : BodyTypedF root w child cert) :
    TypedProgF root w (EffTy.pure (.fiberOf cert.answer cert.error)) (forkProg child) := by
  refine TypedProgF.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_FF, fiberPostF] at hpost
  rcases hpost with ⟨id, rfl, hid⟩
  exact TypedProgF.pure ⟨cert, hid, Ty.sub_refl _, Ty.sub_refl _⟩

theorem settling_maskF (root : ProgramSource) (w : W) (flag : Bool) (body : Body) (cert : EffTy)
    (hbody : BodyTypedF root w body cert) :
    TypedProgF root w cert (maskProg flag body) := by
  refine TypedProgF.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_FF, fiberPostF] at hpost
  exact TypedProgF.pure hpost

-- src/Effect4/Laws/Program/Typed/Stack.lean:20-42
/-- Exactly the facts `popR`'s three named-hook arms need about an interpreter. -/
structure HookLawsF (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols) : Prop where
  asyncFinalizer : ∀ w tin tout name, hooks.asyncFinalizer w tin tout name →
    tin = tout ∧ ∀ cause, FitsExit w tin (.failure cause) → cause.hasInterrupts = true →
      TypedProgF root w tout (interp.cancelThenFail name cause)
  iterator : ∀ w tin tout name, hooks.iterator w tin tout name →
    tin.error = tout.error ∧ ∀ v, StrongValueF w tin.answer v →
      match (interp.iterNext name v).2 with
      | .done result => FitsExit w tout (.success result)
      | .halt cause => FitsExit w tout (.failure cause)
      | .resume code name' => ∃ tin', TypedProgF root w tin' code ∧ hooks.iterator w tin' tout name'
  loop : ∀ w tin tout name cursor, hooks.loop w tin tout name cursor →
    tin.error = tout.error ∧ ∀ v, StrongValueF w tin.answer v →
      match interp.loopResume name cursor v with
      | .continue cursor' body => ∃ tin', TypedProgF root w tin' body ∧
          hooks.loop w tin' tout name cursor'
      | .finish code => TypedProgF root w tout code

/-- The two outcomes of the walk, at the saved stack's final type. -/
def WalkTypedF (root : ProgramSource) (hooks : FrameProtocols) (w : W) (tout : EffTy) :
    RSaved × Option ExitV → Prop
  | (frame, none) => SavedOk (TypedProgF root) FitsExit hooks w tout frame
  | (_, some ex) => FitsExit w tout ex

-- src/Effect4/Laws/Program/Typed/Stack.lean:86-336
/-- A failure depends only on the error column. -/
theorem fitsExit_failure_of_error {w : W} {tin tout : EffTy} {c : CauseV}
    (herr : tin.error = tout.error) (h : FitsExit w tin (.failure c)) : FitsExit w tout (.failure c) := by
  rw [fitsExit_failure_iff] at h ⊢
  rw [← herr]
  exact h

theorem walk_savedF {root : ProgramSource} {hooks : FrameProtocols} {w : W} {tout : EffTy}
    {x : RSaved} (tin : EffTy) (code : TypedProgF root w tin x.current)
    (stack : StackAccepts (TypedProgF root) FitsExit hooks w tin tout x.stack)
    (hp : InterruptProvenance x) : WalkTypedF root hooks w tout (x, none) :=
  ⟨tin, code, stack, hp⟩

theorem walk_doneF {root : ProgramSource} {hooks : FrameProtocols} {w : W} {tout : EffTy}
    {x : RSaved} {ex : ExitV} (h : FitsExit w tout ex) : WalkTypedF root hooks w tout (x, some ex) :=
  h

/-! ## The walk -/

theorem popR_typedF (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (laws : HookLawsF root interp hooks) (w : W) :
    ∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProgF root) FitsExit hooks w tin tout stack →
      FitsExit w tin ex → InterruptProvenance frame →
      WalkTypedF root hooks w tout (popR interp ex stack frame) := by
  intro stack
  induction stack with
  | nil =>
    intro tin tout ex frame hstack hex _
    cases hstack
    exact hex
  | cons slot rest ih =>
    intro tin tout ex frame hstack hex hp
    cases hstack with
    | cons head tail =>
    cases head with
    | restoreMask flag =>
      obtain ⟨current, stack, interruptible, ic, deferred⟩ := frame
      cases ic with
      | none => exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
      | some c =>
        cases flag with
        | false =>
          cases ex <;> simp only [popR, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;>
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        | true =>
          cases ex with
          | success v =>
            simp only [popR, Bool.not_false, Bool.and_self, ↓reduceIte]
            exact walk_savedF _ (TypedProgF.pure (fitsExit_of_clean w _ c (recorded_clean hp rfl)))
              tail ⟨hp.recorded, hp.deferred⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
    | finalizerMask flag =>
      obtain ⟨current, stack, interruptible, ic, deferred⟩ := frame
      cases ic with
      | none => exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
      | some c =>
        cases flag with
        | false =>
          cases ex <;> simp only [popR, Bool.false_and, Bool.false_eq_true, ↓reduceIte] <;>
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        | true =>
          cases ex with
          | success v =>
            simp only [popR, Bool.not_false, Bool.and_self, ↓reduceIte]
            exact walk_savedF _ (TypedProgF.pure (fitsExit_of_clean w _ c (recorded_clean hp rfl)))
              tail ⟨hp.recorded, hp.deferred⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
    | resume kind next run skip =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      have hp' : ∀ (c : RProgram) (s : List ScopeFrame) (b : Bool),
          InterruptProvenance ⟨c, s, b, ic, deferred⟩ := fun _ _ _ => ⟨hp.recorded, hp.deferred⟩
      -- the preempted skip passes the sanitized cause, clean by provenance
      have preempt : ∀ (ty : EffTy) (cause ic' : CauseV), ic = some ic' →
          FitsExit w ty (.failure (Cause.sanitize cause ic')) := fun ty cause _ h =>
        fitsExit_of_clean w ty _ (sanitize_clean_exit hp cause h)
      cases kind with
      | onSuccess =>
        cases ex with
        | success v =>
          simp only [popR]
          exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases ic <;> exact ih _ _ _ _ tail (skip _ hex rfl) (hp' _ _ _)
      | onFailure =>
        cases ex with
        | success v =>
          simp only [popR]
          exact ih _ _ _ _ tail (skip _ hex rfl) (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
          · exact ih _ _ _ _ tail (preempt _ c _ rfl) (hp' _ _ _)
      | all =>
        cases ex with
        | success v =>
          simp only [popR]
          exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_savedF _ (run _ hex rfl) tail (hp' _ _ _)
          · exact ih _ _ _ _ tail (preempt _ c _ rfl) (hp' _ _ _)
      | onExit b =>
        cases b with
        | false =>
          cases ex <;> simp only [popR] <;>
            exact walk_savedF _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
        | true =>
          cases ex with
          | success v =>
            simp only [popR]
            exact walk_savedF _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
          | failure c =>
            simp only [popR]
            cases i <;> cases ic
            · exact walk_savedF _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact walk_savedF _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact walk_savedF _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact ih _ _ _ _ tail (preempt _ c _ rfl) (hp' _ _ _)
    | answer next run =>
      have hrun := run ex hex
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      simp only [popR]
      split
      · rename_i ex' heq
        rw [heq] at hrun
        exact ih _ _ _ _ tail (TypedProgF.pure_inv hrun) ⟨hp.recorded, hp.deferred⟩
      · rename_i ex' k heq
        rw [heq] at hrun
        exact ih _ _ _ _ tail (unguard_payload_invF _ _ _ _ _ hrun) ⟨hp.recorded, hp.deferred⟩
      · exact walk_savedF _ hrun tail ⟨hp.recorded, hp.deferred⟩
    | asyncFinalizer name protocol =>
      obtain ⟨same, cancel⟩ := laws.asyncFinalizer w _ _ name protocol
      subst same
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        have code : TypedProgF root w tin
            (if c.hasInterrupts then interp.cancelThenFail name c else .pure (.failure c)) := by
          split
          · rename_i hint
            exact cancel c hex hint
          · exact TypedProgF.pure hex
        simp only [popR]
        cases i
        · exact walk_savedF _ code tail ⟨hp.recorded, hp.deferred⟩
        · exact walk_savedF _ code (.cons (.restoreMask _ _) tail) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        simp only [popR]
        cases i <;> cases ic
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact walk_savedF _ (TypedProgF.pure (fitsExit_of_clean w _ _ (pendingCause_clean ⟨hp.recorded, hp.deferred⟩)))
            tail ⟨hp.recorded, hp.deferred⟩
    | iter name protocol =>
      obtain ⟨errors, step⟩ := laws.iterator w _ _ name protocol
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (fitsExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex
        cases hs : (interp.iterNext name v).2 with
        | done result =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_savedF _ (TypedProgF.pure h) tail ⟨hp.recorded, hp.deferred⟩
        | halt cause =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_savedF _ (TypedProgF.pure h) tail ⟨hp.recorded, hp.deferred⟩
        | resume code name' =>
          rw [hs] at h
          obtain ⟨tin', typed, next⟩ := h
          simp only [popR, hs]
          exact walk_savedF _ typed (.cons (.iter _ next) tail) ⟨hp.recorded, hp.deferred⟩
    | loop name cursor protocol =>
      obtain ⟨errors, step⟩ := laws.loop w _ _ name cursor protocol
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (fitsExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex
        cases hs : interp.loopResume name cursor v with
        | «continue» cursor' body =>
          rw [hs] at h
          obtain ⟨tin', typed, next⟩ := h
          simp only [popR, hs]
          exact walk_savedF _ typed (.cons (.loop _ _ next) tail) ⟨hp.recorded, hp.deferred⟩
        | finish code =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_savedF _ h tail ⟨hp.recorded, hp.deferred⟩

/-! ## The reference interpreter's hooks -/

/-- The concrete hook contracts are exactly what the walk needs of `interpR` (the M5 hook
obligation of the slice 5 brief, closed here because the repaired protocols state them
directly). -/
theorem hookLaws_interpRF (root : ProgramSource) :
    HookLawsF root (interpR root.program) (frameProtocolsF root) where
  asyncFinalizer _ _ _ _ h := h
  iterator w tin tout name h := by
    cases h with
    | step errors next =>
      refine ⟨errors, fun v hv => ?_⟩
      have answer := next v hv
      revert answer
      generalize ((interpR root.program).iterNext name v).2 = s
      intro answer
      cases answer with
      | done result typed => exact typed
      | halt cause typed => exact typed
      | resume code name' tin' typed tail => exact ⟨tin', typed, tail⟩
  loop w tin tout name cursor h := by
    cases h with
    | step errors next =>
      refine ⟨errors, fun v hv => ?_⟩
      have answer := next v hv
      revert answer
      generalize (interpR root.program).loopResume name cursor v = s
      intro answer
      cases answer with
      | «continue» cursor' body tin' typed tail => exact ⟨tin', typed, tail⟩
      | finish code typed => exact typed

/-- The walk on the reference interpreter needs no hook premise. -/
theorem popR_typed_interpRF (root : ProgramSource) (w : W) (stack : List ScopeFrame)
    (tin tout : EffTy) (ex : ExitV) (frame : RSaved)
    (hstack : StackAccepts (TypedProgF root) FitsExit (frameProtocolsF root) w tin tout stack)
    (hex : FitsExit w tin ex) (hp : InterruptProvenance frame) :
    WalkTypedF root (frameProtocolsF root) w tout (popR (interpR root.program) ex stack frame) :=
  popR_typedF root _ _ (hookLaws_interpRF root) w stack tin tout ex frame hstack hex hp

-- src/Effect4/Laws/Program/Typed/Stack.lean:340-349
/-- Installing an operation's code below its answer adapter keeps the saved state typed: the
adapter and the old stack meet at `middle`, the code has the operation's own type `tin`. -/
theorem saveAnswerR_typedF (root : ProgramSource) (hooks : FrameProtocols) (w : W)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (hcode : TypedProgF root w tin code)
    (hnext : ∀ ex, FitsExit w tin ex → TypedProgF root w middle (next ex))
    (hstack : StackAccepts (TypedProgF root) FitsExit hooks w middle final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    SavedOk (TypedProgF root) FitsExit hooks w final (answerR (saveAnswerR f next) code).frame :=
  ⟨tin, hcode, .cons (.answer next hnext) hstack, ⟨hp.recorded, hp.deferred⟩⟩

-- src/Effect4/Laws/Program/Typed/Stack.lean:359-373
/-- A resume at the parked token installs the delivered code, which `ResumeOk` types at the
token's declared type, over the stack the park saved at that type. -/
theorem deliver_activeF (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : W) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (found : m.fiber? f.id = some f) (parked : f.parked = .withGuard token)
    (declared : w.Θ f.id token = some tin) (typed : ResumeOk (TypedProgF root) w f.id token code)
    (hstack : StackAccepts (TypedProgF root) FitsExit hooks w tin final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    (letI := termEvaluatorFor root.program
     driveStep interp m (.resume f.id token code) rest) =
      ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
    SavedOk (TypedProgF root) FitsExit hooks w final (resumed f token code).frame := by
  refine ⟨?_, tin, typed tin declared, hstack, ⟨hp.recorded, hp.deferred⟩⟩
  simp only [driveStep, found, parked, ↓reduceIte]
  rfl


-- src/Effect4/Laws/Program/Typed/Assembly.lean:33-73
/-- A completion at an effect type: an exit strongly, a reference completion through the
heap table. -/
def CompletionStrongF (w : W) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => FitsExit w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub ty.answer = true

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. -/
def CaptureTypedF (root : ProgramSource) (w : W) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check (nativeSignature root.table) env c.path (.acquireRelease acquire release) = .ok t ∧
    Checker.check (nativeSignature root.table) env (c.path ++ [0]) acquire = .ok a ∧
    EnvTypedF w (env ++ [a.answer]) c.env ∧ ServicesFitE w c.ctx.services

/-- The generated bundle, instantiated with the strong judgments. -/
def predsF (root : ProgramSource) : Preds W where
  SavedOk w e x := ∀ ty, expectOf w e = some ty →
    Contracts.SavedOk (TypedProgF root) FitsExit (frameProtocolsF root) w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → FitsExit w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProgF root) w target token code
  ServiceOk w _ ctx := ServicesFitE w ctx.services
  RaceOk w _ races := ∀ r ∈ races, (w.Θ r.host r.token).isSome = true
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrongF w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → StrongValueF w ty v
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrongF w ⟨a, e, Env.Requirement.empty⟩ c
  CaptureOk w _ c := CaptureTypedF root w c

/-- The typed state: world validity, the generated whole-state predicate over `predsF`, and the
active-delivery correlation: a parked fiber's saved stack expects its token's declared type. -/
def TypedStateF (root : ProgramSource) (rootTy : EffTy) (w : W) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (predsF root) w m ∧
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProgF root) FitsExit (frameProtocolsF root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame


-- src/Effect4/Laws/Program/Typed/Assembly.lean:78-97
/-- A host answer is admitted: an answer to a fiber parked at that token fits the token's
declared type. Answers to anything else run inertly and impose nothing. -/
def AnswerOkF (w : W) (m : RState) : Api.Decision → Prop
  | .answerAsync target token answer =>
    (∃ f, m.fiber? target = some f ∧ f.parked = .withGuard token) →
      ∃ ty, w.Θ target token = some ty ∧ CompletionStrongF w ty answer
  | _ => True

/-- The queued commands carry typed resumes. -/
def QueueOkF (root : ProgramSource) (w : W) (cmds : List RCmd) : Prop :=
  ∀ c ∈ cmds, match c with
    | .resume target token code => Contracts.ResumeOk (TypedProgF root) w target token code
    | _ => True

/-- One command keeps the typed state and the queue typed, at some later world. -/
def StepPreservesF (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, TypedStateF root rootTy w m → QueueOkF root w (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedStateF root rootTy w' r.1 ∧ QueueOkF root w' r.2

-- src/Effect4/Laws/Program/Typed/Assembly.lean:101-139
theorem envTyped_appendF {w : W} {env : List Ty} {vals : List Val} {ty : Ty} {v : Val}
    (h : EnvTypedF w env vals) (hv : StrongValueF w ty v) : EnvTypedF w (env ++ [ty]) (vals ++ [v]) := by
  refine ⟨by simp only [List.length_append, h.1, List.length_singleton], fun i t x ht hx => ?_⟩
  by_cases hi : i < env.length
  · rw [List.getElem?_append_left hi] at ht
    rw [List.getElem?_append_left (h.1 ▸ hi)] at hx
    exact h.2 i t x ht hx
  · have hge : env.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hge] at ht
    rw [List.getElem?_append_right (h.1 ▸ hge)] at hx
    rw [← h.1] at hx
    cases hk : i - env.length with
    | zero =>
      rw [hk] at ht hx
      simp only [List.getElem?_cons_zero, Option.some.injEq] at ht hx
      subst ht hx
      exact hv
    | succ k =>
      rw [hk] at ht
      simp only [List.getElem?_cons_succ, List.getElem?_nil] at ht
      cases ht

/-- A capture's release runs at the point its path's `acquireRelease` checks it at: the
release child, over the checker's environment extended by the acquired value and the exit. -/
theorem capture_lookupF (root : ProgramSource) (w : W) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (h : CaptureTypedF root w c)
    (hex : StrongValueF w (.exitOf .unknown .unknown) exVal) :
    ∃ rty, PointTypedF root w ((Point.ofCapture c completed).childWith 1 exVal) rty := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, _⟩ := h
  obtain ⟨a', r, hacq', hrel, _, _⟩ := Checker.inv_acquireRelease _ _ _ _ _ t hcheck
  rw [hacq] at hacq'
  cases hacq'
  refine ⟨r, release, env ++ [a.answer, .exitOf .unknown .unknown], ?_, hrel, ?_⟩
  · show Node.at_ (.eff root.program) (c.path ++ [1]) = some (.eff release)
    rw [Agreement.Node.at_append, hnode]
    rfl
  · show EnvTypedF w (env ++ [a.answer, .exitOf .unknown .unknown]) (c.env ++ [exVal])
    have := envTyped_appendF henv hex
    simpa only [List.append_assoc, List.singleton_append] using this


-- src/Effect4/Laws/Program/Typed/Residual.lean:389-433
/-! FR-09's payload inversions, restated over the one judgment under their M3a names. -/
namespace M3aAdmissionObligations

theorem unguard_payload_invF (root : ProgramSource) (w : W) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProgF root w ty (.vis (.inr (.unguard ex)) k) → FitsExit w ty ex) := ⟨⟩

theorem finishFinalizer_payload_invF (root : ProgramSource) (w : W) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProgF root w ty (.vis (.inr (.finishFinalizer ex)) k) → FitsExit w ty ex) := ⟨⟩

end M3aAdmissionObligations

namespace M3aResidualObligations

theorem settling_ref_allocationF (_root : ProgramSource) (_w : W) (_h0 : HeapTypedAt _w ⟨0⟩ .nat) :
    ProofGraph.Obligation (TypedProgF _root _w (EffTy.pure .bool) refAllocGetProg) := ⟨⟩

theorem settling_ref_preserves_nat (_w _w' : W) (_ordered : _w.leHost _w') (_h0 : HeapTypedAt _w ⟨0⟩ .nat) :
    ProofGraph.Obligation (HeapTypedAt _w' ⟨0⟩ .nat) := ⟨⟩

theorem settling_forkF (_root : ProgramSource) (_w : W) (_child : Body) (_cert : EffTy)
    (_hbody : BodyTypedF _root _w _child _cert) :
    ProofGraph.Obligation (TypedProgF _root _w (EffTy.pure (.fiberOf _cert.answer _cert.error)) (forkProg _child)) := ⟨⟩

theorem settling_maskF (_root : ProgramSource) (_w : W) (_flag : Bool) (_body : Body) (_cert : EffTy)
    (_hbody : BodyTypedF _root _w _body _cert) :
    ProofGraph.Obligation (TypedProgF _root _w _cert (maskProg _flag _body)) := ⟨⟩

end M3aResidualObligations

/-! W weakening (ruling 2026-09-23, audit A4): typing survives every later world the host
order allows. The hook clauses are stated at one world and consumed at later ones, and every
continuation of `TypedProgF` is typed at the world its answer arrives in, so the stack and
delivery proofs of slice 5 need these three. Declared, not proved. -/
namespace M3bWorld

theorem strongValue_mono (w w' : W) (ty : Ty) (v : Val) :
    ProofGraph.Obligation (w.leHost w' → StrongValueF w ty v → StrongValueF w' ty v) := ⟨⟩

theorem strongExit_mono (w w' : W) (ty : EffTy) (ex : ExitV) :
    ProofGraph.Obligation (w.leHost w' → FitsExit w ty ex → FitsExit w' ty ex) := ⟨⟩

theorem typedProg_mono (root : ProgramSource) (w w' : W) (ty : EffTy) (p : RProgram) :
    ProofGraph.Obligation (w.leHost w' → TypedProgF root w ty p → TypedProgF root w' ty p) := ⟨⟩

end M3bWorld

-- src/Effect4/Laws/Program/Typed/Stack.lean:385-425
namespace M4Stack

theorem popR_typedF (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (_laws : HookLawsF root interp hooks) (w : W) : ProofGraph.Obligation
    (∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProgF root) FitsExit hooks w tin tout stack →
      FitsExit w tin ex → InterruptProvenance frame →
      WalkTypedF root hooks w tout (popR interp ex stack frame)) := ⟨⟩

theorem saveAnswerR_typedF (root : ProgramSource) (hooks : FrameProtocols) (w : W)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (_hcode : TypedProgF root w tin code)
    (_hnext : ∀ ex, FitsExit w tin ex → TypedProgF root w middle (next ex))
    (_hstack : StackAccepts (TypedProgF root) FitsExit hooks w middle final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    (SavedOk (TypedProgF root) FitsExit hooks w final (answerR (saveAnswerR f next) code).frame) := ⟨⟩

theorem deliver_activeF (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : W) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard token)
    (_declared : w.Θ f.id token = some tin) (_typed : ResumeOk (TypedProgF root) w f.id token code)
    (_hstack : StackAccepts (TypedProgF root) FitsExit hooks w tin final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) =
        ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
      SavedOk (TypedProgF root) FitsExit hooks w final (resumed f token code).frame) := ⟨⟩

theorem deliver_stale (root : ProgramSource) (interp : RInterp) (m : RState) (f : RFiber)
    (parkedToken token : Nat) (code : RProgram) (rest : List RCmd)
    (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard parkedToken)
    (_stale : parkedToken ≠ token) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) = (m, rest)) := ⟨⟩

end M4Stack

namespace M5Hooks
theorem hookLaws_interpRF (root : ProgramSource) :
    ProofGraph.Obligation (HookLawsF root (interpR root.program) (frameProtocolsF root)) := ⟨⟩
end M5Hooks

-- src/Effect4/Laws/Program/Typed/Assembly.lean:146-229
namespace M3bAssembly

theorem typedState_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      ∃ w, TypedStateF root rootTy w (loadR root.program fuel compileFuel)) := ⟨⟩

theorem capture_lookupF (root : ProgramSource) (w : W) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (_h : CaptureTypedF root w c)
    (_hex : StrongValueF w (.exitOf .unknown .unknown) exVal) : ProofGraph.Obligation
    (∃ rty, PointTypedF root w ((Point.ofCapture c completed).childWith 1 exVal) rty) := ⟨⟩

end M3bAssembly

namespace M6Ledger

theorem step_evaluate (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.evaluate id)) := ⟨⟩

theorem step_loop (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.loop id yielding)) := ⟨⟩

theorem step_deliver (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.deliver id yielding)) := ⟨⟩

theorem step_finish (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (exit : ExitV) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.finish id exit)) := ⟨⟩

theorem step_resume (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat) (code : RProgram) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.resume id token code)) := ⟨⟩

theorem step_launch (root : ProgramSource) (rootTy : EffTy) (race : Nat) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.launch race)) := ⟨⟩

theorem step_enrollRace (root : ProgramSource) (rootTy : EffTy) (race : Nat) (child : FiberId) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.enrollRace race child)) := ⟨⟩

theorem step_registrationDone (root : ProgramSource) (rootTy : EffTy) (race : Nat) (yielding : Bool) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.registrationDone race yielding)) := ⟨⟩

theorem step_interruptTarget (root : ProgramSource) (rootTy : EffTy) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.interruptTarget target who extra)) := ⟨⟩

theorem step_afterInterrupt (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (kind : ParkKind) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.afterInterrupt host yielding kind)) := ⟨⟩

theorem step_raceCancel (root : ProgramSource) (rootTy : EffTy) (race : Nat) (host : FiberId)
    (yielding : Bool) (remaining visited : List FiberId) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.raceCancel race host yielding remaining visited)) := ⟨⟩

theorem step_trackChild (root : ProgramSource) (rootTy : EffTy) (parent child : FiberId) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.trackChild parent child)) := ⟨⟩

theorem step_observe (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) (exit : ExitV) (observer : Observer) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.observe fiber exit observer)) := ⟨⟩

theorem step_exitDone (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.exitDone fiber)) := ⟨⟩

theorem step_closeParAwait (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (fibers : List FiberId) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.closeParAwait host yielding fibers)) := ⟨⟩

theorem step_link (root : ProgramSource) (rootTy : EffTy) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.link mode scope target interruptor extra)) := ⟨⟩

theorem step_drainDue (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (StepPreservesF root rootTy .drainDue) := ⟨⟩

theorem step_wake (root : ProgramSource) (rootTy : EffTy) (list : WakeKey) (phase : WakePhase) :
    ProofGraph.Obligation (StepPreservesF root rootTy (.wake list phase)) := ⟨⟩

/-- A tape decision keeps the typed state when its host answer, if any, is admitted. -/
theorem decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    ProofGraph.Obligation (∀ w m, TypedStateF root rootTy w m → AnswerOkF w m d →
      ∃ w', w.leHost w' ∧ TypedStateF root rootTy w'
        (letI := termEvaluatorFor root.program
         stepDecisionState (interpR root.program) fuel m d).1) := ⟨⟩

/-- The capstone: every state an admitted tape reaches from an admitted source is typed. -/
theorem typedState_reachable (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      RReachable root fuel m → ∃ w, TypedStateF root rootTy w m) := ⟨⟩

end M6Ledger

/-! ## Consumers re-proved against `Fits` (effort measured in the note)

The three representative consumers of `Test/Program/LoadedAdmission.lean` that build a value
judgment (a fiber handle, a context's service, a checker-typed body), and the positive
counterpart of `Gaps.lean`'s G10: the loaded code of `Ref.make(5)` is typed at every world. -/

open Test.Program.LoadedAdmission (one forked readService natKey natKey_ty)

theorem env0F (w : W) : EnvTypedF w [] [] := ⟨rfl, fun _ _ _ h => nomatch h⟩

/-- `fork_admitted` (`LoadedAdmission.lean:48`): its value part was 11 lines of key
bookkeeping; here it is the declaration. -/
theorem fork_admittedF (w : W) :
    TypedProgF forked w (EffTy.pure (.fiberOf .nat .never)) (denoteR forked forked (rootPoint 20)) := by
  refine TypedProgF.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) (EffTy.pure .nat)
    (BodyTypedF.at_ _ _ ⟨one, [], rfl, by decide +kernel, env0F w⟩) ?_
  intro w' _ ans hpost
  obtain ⟨id, rfl, hid⟩ := hpost
  exact TypedProgF.pure ⟨_, hid, Ty.sub_refl _, Ty.sub_refl _⟩

/-- A context's fit gives its services' fits (decision row 90's clause, now read from `Fits`). -/
theorem fits_context_services {w : W} {v : Val} (h : Fits w v (.handle Ty.contextTarget)) :
    ∀ ctx, Val.context? v = some ctx → ServicesFitE w ctx.services := by
  intro ctx hctx
  simp only [Fits, FitsInv] at h
  split at h
  · exact nomatch hctx
  · obtain ⟨_, ctx0, hctx0, hs, _⟩ := h
    rw [hctx0] at hctx
    cases hctx
    exact hs

/-- `lookup_typed` (`LoadedAdmission.lean:118`). -/
theorem lookup_typedF (w : W) (ty : EffTy) (answer : ty.answer = .nat) (v : Val)
    (typed : ∀ ctx, Val.context? v = some ctx → ServicesFitE w ctx.services) :
    TypedProgF readService w ty (serviceLookupR natKey v) := by
  unfold serviceLookupR
  split
  · rename_i ctx hctx
    split
    · rename_i sv hget
      have hf := flatFits_fitsInv (typed ctx hctx natKey sv .nat hget natKey_ty)
      refine TypedProgF.pure (fitsExit_success w ty sv ?_)
      rw [answer]
      exact hf
    · exact TypedProgF.pure (fitsExit_of_clean w ty _ rfl)
  · exact TypedProgF.pure (fitsExit_of_clean w ty _ rfl)

/-- `service_admitted` (`LoadedAdmission.lean:134`). -/
theorem service_admittedF (w : W) (ty : EffTy) (answer : ty.answer = .nat) :
    TypedProgF readService w ty (denoteR readService readService (rootPoint 20)) := by
  refine TypedProgF.guard (EffTy.pure (.handle Ty.contextTarget)) ?_ ?_ ?_
  · refine TypedProgF.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun _ _ _ h => nomatch h) (Ty.handle Ty.contextTarget) rfl ?_
    intro w' _ ans hpost
    exact TypedProgF.unguard (fitsExit_success w' _ ans hpost)
  · intro w' _ ex hpost
    cases ex with
    | failure c => exact Bool.noConfusion hpost.1
    | success v => exact lookup_typedF w' ty answer v (fits_context_services hpost.2)
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact fitsExit_of_clean w' ty c (cleanExit_of_never_fits w' _ c rfl hex)

/-- The positive counterpart of `Gaps.lean`'s `typedState_load_false`: under `Fits` the loaded
code of `Ref.make(5)` is typed at every world. -/
def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
abbrev refTy : EffTy := EffTy.pure (.handle NativeOp.refTarget)

theorem refProg_typedF (w : W) :
    TypedProgF (refProg : ProgramSource) w refTy (denoteR refProg refProg (rootPoint 20)) := by
  refine TypedProgF.store (cert := Ty.nat) ⟨rfl, trivial⟩ ?_
  intro w' _ ans hpost
  obtain ⟨key, rfl, hs⟩ := hpost
  exact TypedProgF.pure ⟨rfl, .nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩

#print axioms fitsExit_success
#print axioms fitsExit_of_clean
#print axioms cleanExit_of_never_fits
#print axioms fitsExit_failure_of_error
#print axioms unguard_payload_invF
#print axioms finishFinalizer_payload_invF
#print axioms settling_ref_allocationF
#print axioms settling_forkF
#print axioms settling_maskF
#print axioms popR_typedF
#print axioms hookLaws_interpRF
#print axioms popR_typed_interpRF
#print axioms saveAnswerR_typedF
#print axioms deliver_activeF
#print axioms envTyped_appendF
#print axioms capture_lookupF
#print axioms fork_admittedF
#print axioms fits_context_services
#print axioms lookup_typedF
#print axioms service_admittedF
#print axioms refProg_typedF

end Research.Pass.Membership
