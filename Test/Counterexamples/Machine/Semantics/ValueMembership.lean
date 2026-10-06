import Effect4.Laws.Program.Typed.Assembly

/-!
E4-TYPED-CE-004/005/006: membership follows value structure and declared handles.
The Reviewed namespace retains the old value, residual and state judgments so
G1–G7 and the old Ref.make initialization obstruction remain executable falsifiers.
Those declarations are local historical copies, not production predicates.
ExactSpelling retains the rejected equality reading of invariant handles for G7.

The positive controls use the production Fits and TypedState judgments. Their
loaded-state witnesses cover Ref.make(5) and Ref.make(5).flatMap(Ref.get), at the
stated compile budget; they do not discharge general initialization or M6.
Sources: membership/Gaps.lean, verify-fits.lean and Fits.lean in the 2026-09-30 pass.
-/

set_option autoImplicit false
set_option maxRecDepth 8192
namespace Test.Counterexamples.Machine.Semantics.ValueMembership
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed Effect4.Program.Sched
open Effect4.Program.Denote Effect4.Laws.Effects Effect4.Program.Typed.Contracts
abbrev World := Effect4.Program.Typed.World
abbrev W := World

namespace Reviewed

/-- A value's handle indices are within the allocated bounds of the world. -/
def HandlesLive (w : World) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => key.index < w.state.refs.length
  | .promise key => key.index < w.state.deferreds.cells.length
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

/-- A context's services fit their keys' static types, the ones the checker reads
(`nativeServiceTy`, `Checker.lean` `.service`/`.provideService`). Decision row 90 (2026-09-24):
the checker types a service by its key, so the typing is static; a service value's own nested
handles are not re-checked here (a ref-typed service is refused, not mistyped). -/
def ServicesOk (w : World) (services : Env.Ctx) : Prop :=
  ∀ key sv sty, services.getV key = some sv → nativeServiceTy key = some sty →
    ValueOk w sty sv ∧ HandlesLive w sv

/-- Nested handle types align with the world typing tables. A fiber handle is covariant, as the
checker's `Ty.sub` is (`Program/Ty.lean`), so a handle widened to `fiberOf unknown unknown` fits
(ruling 2026-09-23, audit §8); refs and deferreds are invariant, as there. -/
def HandlesFit (w : World) (v : Val) (ty : Ty) : Prop :=
  match ty with
  | .refOf t => ∀ key, Handle.cell key ∈ v.keys → w.Ρ key = some t
  | .deferredOf a e => ∀ key, Handle.promise key ∈ v.keys → w.«Π» key = some (a, e)
  | .fiberOf a e => ∀ id, Handle.fiber id ∈ v.keys → ∃ fty, w.Γ id = some fty ∧
      fty.answer.sub a = true ∧ fty.error.sub e = true
  | .prod a b => match v with
    | .pair v1 v2 => HandlesFit w v1 a ∧ HandlesFit w v2 b
    | _ => True
  | .option a => match v with
    | .some v1 => HandlesFit w v1 a
    | _ => True
  | .list a => match v with
    | .list vs => ∀ x ∈ vs, HandlesFit w x a
    | _ => True
  | .union a b => HandlesFit w v a ∨ HandlesFit w v b
  | .unknown => HandlesLive w v
  -- the context handle carries its services' typing (decision row 90)
  | .handle s => s = Ty.contextTarget → ∀ ctx, Val.context? v = some ctx → ServicesOk w ctx.services
  | _ => True

/-- Strong values: well-shaped, nested handles declared at the right types, and live. -/
def StrongValue (w : World) (ty : Ty) (v : Val) : Prop :=
  ValueOk w ty v ∧ HandlesFit w v ty ∧ HandlesLive w v

/-- Strong causes: every failure payload has an admitted image satisfying `StrongValue`. -/
def StrongCause (w : World) (errTy : Ty) (c : CauseV) : Prop :=
  ∀ r ∈ c.reasons, match r with
  | .fail e _ => ∃ v, valOfErr e = some v ∧ StrongValue w errTy v
  | .die _ _ | .interrupt _ _ => True

/-- Strong exits: successful values and failure causes carry strong typing. Defects and
interruptions remain admitted. -/
def StrongExit (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  ExitFits w ty ex ∧
  (∀ v, ex = .success v → StrongValue w ty.answer v) ∧
  (∀ c, ex = .failure c → StrongCause w ty.error c)

/-- An evaluation environment typed pointwise at the corresponding static types. -/
def EnvTyped (w : World) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → StrongValue w ty v

/-- D13 source admission at an addressed program node, under the source's row table
(`E4-SCHED-CE-014`: the empty table refused bodies that perform a host row). -/
def PointTyped (src : ProgramSource) (w : World) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff src.program) point.path = some (.eff e) ∧
    Checker.check (nativeSignature src.table) env point.path e = .ok ty ∧
    EnvTyped w env point.env

/-- Admitted bodies covering all six `Body` constructors. -/
inductive BodyTyped (src : ProgramSource) (w : World) : Body → EffTy → Prop
  | at_ (p : Point) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.at_ p) ty
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : StrongExit w ty ex) :
      BodyTyped src w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTyped src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.layerBuild p m scope) ty

/-! ## The Store Protocol (31 SyncOp rows) -/

def StoreCert : SyncOp → Type
  | .refMake _ | .memoGet _ _ => Ty
  | .deferredMake | .memoBuild _ _ => Ty × Ty
  | _ => PUnit

def storePre (root : ProgramSource) (w : World) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ StrongValue w cert initial
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValue w ty v
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValue w ty v
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValue w ty v
  | .refUpdate cell _ _ | .refGetAndUpdate cell _ _ | .refUpdateAndGet cell _ _
  | .refUpdateSome cell _ _ | .refGetAndUpdateSome cell _ _ | .refUpdateSomeAndGet cell _ _
  | .refModify cell _ _ | .refModifySome cell _ _ => ∃ ty, w.Ρ cell = some ty
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

def storePost (w' : World) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refUpdate _ _ _ | .refUpdateSome _ _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ _ | .refGetAndUpdateSome cell _ _ =>
    ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refUpdateAndGet cell _ _ | .refUpdateSomeAndGet cell _ _ =>
    ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refModify _ _ _ | .refModifySome _ _ _ => ∃ n, ans = Val.nat n
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

def Ψ_S (root : ProgramSource) : Protocol World StoreSig where
  Cert := StoreCert
  pre := storePre root
  post := storePost

/-! ## The Fiber Protocol (41 FiberOp rows) -/

/-- An operation whose answer is an installed body's exit, a registration's delivery or a
spawned fiber certifies that type (`EffTy`); one answering a typed value certifies the value's
type (`Ty`). A guard certifies its intermediate type (`E4-SCHED-CE-011`). Ruling 2026-09-23,
typed-state admission audit: a `True` post refused every program consuming the answer
(`E4-SCHED-CE-013`). -/
def FiberCert : FiberOp → Type
  | .fork _ _ _ | .forkIn _ _ _ _ | .forkScoped _ _ _ | .mask _ _ | .guard_ _ | .scoped _
  | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ => EffTy
  | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren | .getContext => Ty
  | _ => PUnit

/-- The type an async registration's answer is certified at: a timer's `unit`, a deferred's
completion at the promise table's columns, a host row's columns from the source's row table.
A host slot (`FinName.parkThen`'s release) is certified by the host protocol, a correlation the
state predicate owns; any other registration is not generated code and is refused. -/
def asyncPre (root : ProgramSource) (w : World) (register : EffName) (cert : EffTy) : Prop :=
  match register with
  | .store (.registerSleep _) => Ty.unit.sub cert.answer = true
  | .registerAwait cell | .store (.registerAwait cell) =>
    ∃ a e, w.«Π» cell = some (a, e) ∧ a.sub cert.answer = true ∧ e.sub cert.error = true
  | .external op _ =>
    ((nativeSignature root.table).rowOf op).answer.sub cert.answer = true ∧
      ((nativeSignature root.table).rowOf op).error.sub cert.error = true
  | .store (.externalRegister _) => True
  | _ => False

def fiberPre (root : ProgramSource) (w : World) (op : FiberOp) (cert : FiberCert op) : Prop :=
  match op with
  | .getId | .yieldNow _ | .ambientScope | .sync _ | .getInterruptible => True
  -- the context set keeps every service at its key's type (decision row 90)
  | .setContext ctx => ServicesOk w ctx.services
  | .getContext => cert = .handle Ty.contextTarget
  | .await target _ => (w.Γ target).isSome = true
  | .awaitAll targets | .awaitAllFailFast targets =>
    ∃ a e, cert = .list (.exitOf a e) ∧ ∀ t ∈ targets, ∃ fty, w.Γ t = some fty ∧
      fty.answer.sub a = true ∧ fty.error.sub e = true
  | .raceAll entrants _ => ∀ p ∈ entrants, ∃ ty, PointTyped root w p ty ∧
      ty.answer.sub cert.answer = true ∧ ty.error.sub cert.error = true
  | .async register _ => asyncPre root w register cert
  | .suspend _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _ | .interruptAll _ _
  | .runIn _ _ | .awaitNewChildren _ => True
  | .guard_ _ | .unguard _ | .finishFinalizer _ | .scopeExit _ _ _ | .construction
  | .closeScope _ _ | .foreignRelease _ _ | .closeWalk _ _ _ | .closeIter _ _ _
  | .raceRegister _ | .cancelRace _ | .dropObservers _ | .frontier _ _ => True
  | .snapshotChildren => cert = .list (.fiberOf .unknown .unknown)
  | .scoped body => PointTyped root w body cert
  | .mask _ body => BodyTyped root w body cert
  | .forkScoped child _ _ => PointTyped root w child cert
  | .fork body _ _ => BodyTyped root w body cert
  | .forkIn child _ _ _ => PointTyped root w child cert
  | .gen p => PointTyped root w p cert
  | .loop p _ => PointTyped root w p cert
  | .refuse _ => False

def fiberPost (w' : World) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op with
  | .getId => ∃ (id : FiberId), ans = Val.nat id.value
  | .getInterruptible => ∃ (flag : Bool), ans = Val.savedMask flag
  | .getContext | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren => StrongValue w' cert ans
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ | .awaitNewChildren _ => ans = Val.unit
  | .ambientScope => ∃ sc, ans = Val.scopeHandle sc
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ StrongExit w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ StrongValue w' ty.answer ans
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    StrongExit w' cert ans
  | .unguard ex | .finishFinalizer ex | .closeScope _ ex | .scopeExit _ _ ex | .closeIter _ _ ex => ans = ex
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ StrongExit w' cert ex
  -- a live frontier is never answered (fuel exhaustion is not an exit)
  | .frontier _ _ => False
  -- the completed exits a callback reads, each at its fiber's declared type
  | .construction => ∀ p ∈ ans, ∃ ty, w'.Γ p.1 = some ty ∧ StrongExit w' ty p.2
  | .suspend _ | .refuse _ => True

def Ψ_F (root : ProgramSource) : Protocol World FiberSig where
  Cert := FiberCert
  pre := fiberPre root
  post := fiberPost

/-! ## The program judgment -/

/-- The one typing of a reference program at an effect type. Store and fiber operations follow
`Ψ_S` and `Ψ_F`: a certificate, its precondition, and a continuation for every answer the
postcondition admits at every later world. The fiber arm excludes the four control markers,
which have their own arms. A guard's body is typed at the guard's certified intermediate type
`mid`; the saved arm runs on the exits the guard row admits at `mid`, and an exit the arm does
not take must fit the outer type. `unguard` and `finishFinalizer` carry an exit at the current
type and type no continuation: the reference machine never resumes one (`evaluateFiberR`
hands the payload to `deliverR`; `popR`'s answer glue passes it to the next frame).
`scopeExit` carries its exit and keeps its continuation. -/
inductive TypedProg (root : ProgramSource) : World → EffTy → RProgram → Prop
  | pure {w : World} {ty : EffTy} {ex : ExitV} (exit : StrongExit w ty ex) :
      TypedProg root w ty (.pure ex)
  | store {w : World} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : (Ψ_S root).Cert op) (pre : (Ψ_S root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_S root).post w' op cert ans → TypedProg root w' ty (k ans)) :
      TypedProg root w ty (.vis (.inl op) k)
  | fiber {w : World} {ty : EffTy} {op : FiberOp} {k : op.answer → RProgram}
      (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
      (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
      (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex)
      (cert : (Ψ_F root).Cert op) (pre : (Ψ_F root).pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, (Ψ_F root).post w' op cert ans →
        TypedProg root w' ty (k ans)) :
      TypedProg root w ty (.vis (.inr op) k)
  | guard {w : World} {ty : EffTy} {kind : GuardKind} {k : Option ExitV → RProgram}
      (mid : EffTy) (body : TypedProg root w mid (k none))
      (run : ∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        TypedProg root w' ty (k (some ex)))
      (skip : ∀ w', w.leHost w' → ∀ ex, StrongExit w' mid ex → kind.hasExitArm ex = false →
        StrongExit w' ty ex) :
      TypedProg root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : World} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : StrongExit w ty ex) : TypedProg root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : World} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : StrongExit w ty ex) : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : World} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : StrongExit w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, TypedProg root w' ty (k ans)) :
      TypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

namespace TypedProg

theorem pure_inv {root : ProgramSource} {w : World} {ty : EffTy} {ex : ExitV}
    (h : TypedProg root w ty (.pure ex)) : StrongExit w ty ex := by
  cases h with
  | pure exit => exact exit

theorem store_inv {root : ProgramSource} {w : World} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
    (h : TypedProg root w ty (.vis (.inl op) k)) :
    ∃ cert : (Ψ_S root).Cert op, (Ψ_S root).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_S root).post w' op cert ans → TypedProg root w' ty (k ans) := by
  cases h with
  | store cert pre next => exact ⟨cert, pre, next⟩

/-- A guard's typing is exactly the saved frame's arrow (`Contracts.FrameAccepts.resume`) at
`mid`, with the body typed at `mid`. -/
theorem guard_inv {root : ProgramSource} {w : World} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProg root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, TypedProg root w mid (k none) ∧
      (∀ w', w.leHost w' → ∀ ex, fiberPost w' (.guard_ kind) mid (some ex) →
        TypedProg root w' ty (k (some ex))) ∧
      (∀ w', w.leHost w' → ∀ ex, StrongExit w' mid ex → kind.hasExitArm ex = false →
        StrongExit w' ty ex) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip => exact ⟨mid, body, run, skip⟩

end TypedProg

/-- FR-09's marker payload inversion: a typed `unguard` carries an exit at the current type. -/
theorem unguard_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.unguard ex)) k)) :
    StrongExit w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)) :
    StrongExit w ty ex := by
  cases h with
  | fiber _ _ notFinish _ _ _ _ => exact absurd rfl (notFinish ex)
  | finishFinalizer payload => exact payload

/-! ## Interpreter hook contracts -/

/-! The recursive hook contracts use mutually inductive step witnesses. This is the
strictly positive form of the brief's existential resume clause: the resume constructor
stores its intermediate type and the next protocol witness. No new program syntax is
stored, and no termination theorem for arbitrary source code is asserted. -/
mutual
  inductive IteratorProtocol (root : ProgramSource) (w : World) : EffTy → EffTy → EffName → Prop
    | step {tin tout : EffTy} {name : EffName}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValue w tin.answer v →
          IteratorAnswer root w tout ((interpR root.program).iterNext name v).2) :
        IteratorProtocol root w tin tout name
  inductive IteratorAnswer (root : ProgramSource) (w : World) :
      EffTy → IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
    | done {tout : EffTy} (result : Val) (typed : StrongExit w tout (.success result)) :
        IteratorAnswer root w tout (.done result)
    | halt {tout : EffTy} (cause : CauseV) (typed : StrongExit w tout (.failure cause)) :
        IteratorAnswer root w tout (.halt cause)
    | resume {tout : EffTy} (code : RProgram) (name : EffName) (tin : EffTy)
        (typed : TypedProg root w tin code) (tail : IteratorProtocol root w tin tout name) :
        IteratorAnswer root w tout (.resume code name)
end

mutual
  inductive LoopProtocol (root : ProgramSource) (w : World) : EffTy → EffTy → EffName → Val → Prop
    | step {tin tout : EffTy} {name : EffName} {cursor : Val}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValue w tin.answer v →
          LoopAnswer root w tout name ((interpR root.program).loopResume name cursor v)) :
        LoopProtocol root w tin tout name cursor
  inductive LoopAnswer (root : ProgramSource) (w : World) :
      EffTy → EffName → LoopNext Val RProgram → Prop
    | continue {tout : EffTy} {name : EffName} (cursor : Val) (body : RProgram) (tin : EffTy)
        (typed : TypedProg root w tin body) (tail : LoopProtocol root w tin tout name cursor) :
        LoopAnswer root w tout name (.continue cursor body)
    | finish {tout : EffTy} {name : EffName} (code : RProgram) (typed : TypedProg root w tout code) :
        LoopAnswer root w tout name (.finish code)
end

/-- The three named hook arrows (slice 5 brief §3.3 as amended 2026-09-23). The async clause
types the cancellation only for an incoming failure that is itself typed at the frame's
type, the evidence `popR` holds at that arm (`E4-SCHED-CE-010`). -/
def frameProtocols (root : ProgramSource) : Contracts.FrameProtocols where
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, StrongExit w tin (.failure cause) →
    cause.hasInterrupts = true → TypedProg root w tout ((interpR root.program).cancelThenFail name cause)
  iterator := IteratorProtocol root
  loop := LoopProtocol root
  -- the reviewed judgment had no `scoped` guard's slot (decisions row 188 (a) came later)
  scopeExit _ _ _ := False

/-- The type a position is expected at: the root's and each fiber's declared type (D7). -/
def expectOf (w : World) : Expect → Option EffTy
  | .root => w.Γ Api.root
  | .fiber id => w.Γ id
  | .hook _ => none

/-- A completion at an effect type: an exit strongly, a reference completion through the
heap table. -/
def CompletionStrong (w : World) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => StrongExit w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub ty.answer = true

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. -/
def CaptureTyped (root : ProgramSource) (w : World) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check (nativeSignature root.table) env c.path (.acquireRelease acquire release) = .ok t ∧
    Checker.check (nativeSignature root.table) env (c.path ++ [0]) acquire = .ok a ∧
    EnvTyped w (env ++ [a.answer]) c.env ∧ ServicesOk w c.ctx.services

/-- The generated bundle, instantiated with the strong judgments. -/
def preds (root : ProgramSource) : Preds World where
  SavedOk w e x := ∀ ty, expectOf w e = some ty →
    Contracts.SavedOk (TypedProg root) StrongExit (frameProtocols root) w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → StrongExit w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProg root) w target token code
  ServiceOk w _ ctx := ServicesOk w ctx.services
  RaceOk w _ races := ∀ r ∈ races, (w.Θ r.host r.token).isSome = true
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrong w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → StrongValue w ty v
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c
  -- absent when this judgment was reviewed; decisions row 151 (a″) states it in production `preds`
  FinalizerOk _ _ _ := True
  CaptureOk w _ c := CaptureTyped root w c
  -- refused when this judgment was reviewed; decisions row 140 states it in production `preds`
  ScopeExitOk _ _ _ := True

/-- The typed state: world validity, the generated whole-state predicate over `preds`, and the
active-delivery correlation: a parked fiber's saved stack expects its token's declared type. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) StrongExit (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

end Reviewed

/-! The unchanged experimental equality reading, confined to this test. -/
namespace ExactSpelling
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
`WorldValid` (before finding F-WF; `Live` now also reads raw registration and presence), and only the table form follows from an allocation's
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
  | some .cell => target = "Ref.Ref<number>" ∧ RefDeclared w inv ⟨index⟩ .nat
  | some .promise => target = "Deferred.Deferred<number, number>" ∧ PromiseDeclared w inv ⟨index⟩ .nat .nat
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
  -- the historical relation predates the data wave's forms (decisions row 162)
  | _ => False

/-- **The proposed judgment**: invariant handles read as `Ty.sub` reads them. -/
abbrev Fits (w : W) (v : Val) (ty : Ty) : Prop := FitsInv w Equiv v ty

/-- The same recursion with `HandlesFit`'s equality at invariant handles. -/
abbrev FitsEq (w : W) (v : Val) (ty : Ty) : Prop := FitsInv w (· = ·) v ty

end ExactSpelling

/-! ## Worlds for the controls -/

/-- Fiber 1 declared at `string`, nothing else declared, empty stores. -/
def wString : W :=
  { ids := [], state := Stores.empty,
    Γ := tableInsert (fun _ => none) ⟨1⟩ (EffTy.pure .string),
    «Π» := fun _ => none, Ρ := fun _ => none, Θ := fun _ _ => none }

/-- Fiber 1 declared at `nat`. -/
def wNat : W :=
  { ids := [], state := Stores.empty,
    Γ := tableInsert (fun _ => none) ⟨1⟩ (EffTy.pure .nat),
    «Π» := fun _ => none, Ρ := fun _ => none, Θ := fun _ _ => none }

/-- Cell 0 declared at `bool`, holding `true`. -/
def wBoolCell : W :=
  { ids := [], state := { Stores.empty with refs := [.bool true] },
    Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .bool, Θ := fun _ _ => none }

/-- Cell 0 declared at `nat`, holding `7`. -/
def wNatCell : W :=
  { ids := [], state := { Stores.empty with refs := [.nat 7] },
    Γ := fun _ => none, «Π» := fun _ => none,
    Ρ := tableInsert (fun _ => none) ⟨0⟩ .nat, Θ := fun _ _ => none }

theorem wString_one : wString.Γ ⟨1⟩ = some (EffTy.pure .string) := by
  simp only [wString]
  exact insert_here _ _ _
theorem wNat_one : wNat.Γ ⟨1⟩ = some (EffTy.pure .nat) := by
  simp only [wNat]
  exact insert_here _ _ _
theorem wBoolCell_zero : wBoolCell.Ρ ⟨0⟩ = some .bool := by
  simp only [wBoolCell]
  exact insert_here _ _ _
theorem wNatCell_zero : wNatCell.Ρ ⟨0⟩ = some .nat := by
  simp only [wNatCell]
  exact insert_here _ _ _

theorem string_not_sub_nat : Ty.sub .string .nat = false :=
  Ty.sub_eq_false_of_not_sameHead .string .nat rfl rfl rfl rfl rfl

theorem bool_not_sub_nat : Ty.sub .bool .nat = false :=
  Ty.sub_eq_false_of_not_sameHead .bool .nat rfl rfl rfl rfl rfl

/-- The declaration check refuses fiber 1 at `nat` where it is declared `string`. -/
theorem fiber1_refused : ¬ FiberDeclared wString ⟨1⟩ .nat .never := by
  rintro ⟨fty, hs, ha, _⟩
  rw [wString_one] at hs
  cases hs
  change Ty.sub .string .nat = true at ha
  rw [string_not_sub_nat] at ha
  exact Bool.noConfusion ha

theorem fiber1_accepted : FiberDeclared wNat ⟨1⟩ .nat .never :=
  ⟨EffTy.pure .nat, wNat_one, Ty.sub_refl _, Ty.sub_refl _⟩

/-- Fiber 1 is live (a fiber's `Reviewed.HandlesLive` clause is the table). -/
theorem handlesLive_one {v : Val} (hk : v.keys = [Handle.fiber ⟨1⟩]) : Reviewed.HandlesLive wString v := by
  intro k hmem
  rw [hk, List.mem_singleton] at hmem
  subst hmem
  show (wString.Γ ⟨1⟩).isSome = true
  rw [wString_one]
  rfl

/-! ## The converse of `fits_hasTy` is false -/

theorem shape_without_fit :
    Val.hasTy (Value.fiber 1) (.fiberOf .nat .never) wString.state.externals.allocated = true ∧
      ¬ Fits wString (Value.fiber 1) (.fiberOf .nat .never) :=
  ⟨rfl, fun h => fiber1_refused h⟩

theorem converse_false :
    ¬ ∀ (w : W) (v : Val) (ty : Ty),
      Val.hasTy v ty w.state.externals.allocated = true → Fits w v ty :=
  fun h => shape_without_fit.2 (h _ _ _ shape_without_fit.1)

/-! ## The gaps: `Reviewed.StrongValue` admits, `Fits` refuses, and admits the honest value

G1–G4 are `PredicateProbe.lean`'s four (product, Result, successful exit, union); G5 is the
contract's snapshot bullet (§4); G6 is the native cell spelling, which `HandlesFit` never checks
(its `.handle` arm types contexts only, `Typed/Admission.lean:57`). -/

-- G1: a product is a two-cell list; `HandlesFit` looks for `.pair`.
theorem g1_old : Reviewed.StrongValue wString (.prod (.fiberOf .nat .never) .unit) (.list [Value.fiber 1, .unit]) :=
  ⟨rfl, trivial, handlesLive_one rfl⟩
theorem g1_refused : ¬ Fits wString (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit) :=
  fun h => fiber1_refused h.1
theorem g1_control : Fits wNat (.list [Value.fiber 1, .unit]) (.prod (.fiberOf .nat .never) .unit) :=
  ⟨fiber1_accepted, trivial⟩

-- G2: a Result's success arm.
theorem g2_old : Reviewed.StrongValue wString (.except .never (.fiberOf .nat .never)) (.ctor 1 [Value.fiber 1]) :=
  ⟨rfl, trivial, handlesLive_one rfl⟩
theorem g2_refused : ¬ Fits wString (.ctor 1 [Value.fiber 1]) (.except .never (.fiberOf .nat .never)) :=
  fun h => fiber1_refused h
theorem g2_control : Fits wNat (.ctor 1 [Value.fiber 1]) (.except .never (.fiberOf .nat .never)) :=
  fiber1_accepted

-- G3: a successful reified exit.
theorem g3_old :
    Reviewed.StrongValue wString (.exitOf (.fiberOf .nat .never) .never) (Value.exitOk (Value.fiber 1)) :=
  ⟨rfl, trivial, handlesLive_one rfl⟩
theorem g3_refused :
    ¬ Fits wString (Value.exitOk (Value.fiber 1)) (.exitOf (.fiberOf .nat .never) .never) :=
  fun h => fiber1_refused h
theorem g3_control : Fits wNat (Value.exitOk (Value.fiber 1)) (.exitOf (.fiberOf .nat .never) .never) :=
  fiber1_accepted

-- G4: a union whose shape evidence and handle evidence come from different branches.
theorem g4_old : Reviewed.StrongValue wString (.union (.fiberOf .nat .never) .unit) (Value.fiber 1) :=
  ⟨rfl, Or.inr trivial, handlesLive_one rfl⟩
theorem g4_refused : ¬ Fits wString (Value.fiber 1) (.union (.fiberOf .nat .never) .unit) :=
  fun h => h.elim (fun hf => fiber1_refused hf) (fun hu => hu)
theorem g4_control : Fits wNat (Value.fiber 1) (.union (.fiberOf .nat .never) .unit) :=
  Or.inl fiber1_accepted

-- G5: a fiber snapshot, which the shape check decodes and `HandlesFit` skips.
theorem g5_old : Reviewed.StrongValue wString (.list (.fiberOf .nat .never)) (Val.fibers [⟨1⟩]) :=
  ⟨rfl, trivial, handlesLive_one (by rw [Val.keys_fibers]; rfl)⟩
theorem g5_refused : ¬ Fits wString (Val.fibers [⟨1⟩]) (.list (.fiberOf .nat .never)) := by
  intro h
  simp only [Effect4.Program.Typed.Fits, Val.snapshot?_fibers] at h
  exact fiber1_refused (h ⟨1⟩ (List.mem_singleton_self _))
theorem g5_control : Fits wNat (Val.fibers [⟨1⟩]) (.list (.fiberOf .nat .never)) := by
  simp only [Effect4.Program.Typed.Fits, Val.snapshot?_fibers]
  intro id hid
  rw [List.mem_singleton] at hid
  subst hid
  exact fiber1_accepted

-- G6: the native cell spelling `Ref.Ref<number>` at a cell declared `bool`. The old strong
-- judgment accepted it: its coarse check read the cell's kind byte at the spelling, and
-- `HandlesFit` has no arm for a spelling (the proof at `a917b768`). The state plan's T3a retired
-- the spelling: no value fits it (`Val.hasTy_handle_retired`), so the old side is pinned as that
-- refusal, and the cell type the spelling denoted, `refOf nat`, carries the pair.
theorem g6_old : ¬ Reviewed.StrongValue wBoolCell (.handle "Ref.Ref<number>") (Value.cell 0) :=
  fun h => Bool.noConfusion ((Val.hasTy_handle_retired (by decide)).symm.trans h.1)
theorem g6_refused : ¬ Fits wBoolCell (Value.cell 0) (.refOf .nat) := by
  rintro ⟨t', hs, hsub, _⟩
  rw [wBoolCell_zero] at hs
  cases hs
  change Ty.sub .bool .nat = true at hsub
  rw [bool_not_sub_nat] at hsub
  exact Bool.noConfusion hsub
theorem g6_control : Fits wNatCell (Value.cell 0) (.refOf .nat) :=
  ⟨.nat, wNatCell_zero, Ty.sub_refl _, Ty.sub_refl _⟩

/-! ## G7: invariance spelled as equality is not closed under the checker's subtyping

`refOf nat` and `refOf (union nat nat)` are subtypes of each other under `Ty.sub`. `HandlesFit`
(and `ExactSpelling.FitsEq`) demand the declared spelling exactly, so they break subsumption at an invariant
handle; `Fits` (subtyping both ways) keeps it (`fits_sub`, `Fits.lean`). -/

theorem sub_nat_union : Ty.sub .nat (.union .nat .nat) = true := by
  rw [Ty.sub_union_right .nat .nat .nat rfl, Ty.sub_refl]
  rfl

theorem sub_union_nat : Ty.sub (.union .nat .nat) .nat = true := by
  rw [Ty.sub_union_left .nat .nat .nat (fun h => Ty.noConfusion h), Ty.sub_refl]
  rfl

theorem sub_ref_equiv : Ty.sub (.refOf .nat) (.refOf (.union .nat .nat)) = true := by
  rw [Ty.sub_args_refOf]
  simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith, List.all_cons,
    List.all_nil, Bool.and_true, sub_nat_union, sub_union_nat]

theorem cell0_keys : Val.keys (Value.cell 0) = [Handle.cell ⟨0⟩] := Val.keys_cell ⟨0⟩

theorem natCell_old : Reviewed.StrongValue wNatCell (.refOf .nat) (Value.cell 0) := by
  refine ⟨rfl, fun key hkey => ?_, fun k hk => ?_⟩
  · rw [cell0_keys, List.mem_singleton] at hkey
    cases hkey
    exact wNatCell_zero
  · rw [cell0_keys, List.mem_singleton] at hk
    subst hk
    exact Nat.zero_lt_one

theorem natCell_old_refused : ¬ Reviewed.StrongValue wNatCell (.refOf (.union .nat .nat)) (Value.cell 0) := by
  intro h
  have hs := h.2.1 ⟨0⟩ (by rw [cell0_keys]; exact List.mem_singleton_self _)
  rw [wNatCell_zero] at hs
  cases hs

theorem strongValue_not_closed_under_sub :
    ¬ ∀ (w : W) (a b : Ty) (v : Val), Ty.sub a b = true → Reviewed.StrongValue w a v → Reviewed.StrongValue w b v :=
  fun h => natCell_old_refused (h _ _ _ _ sub_ref_equiv natCell_old)

theorem fitsEq_not_closed_under_sub :
    ¬ ∀ (w : W) (a b : Ty) (v : Val), Ty.sub a b = true → ExactSpelling.FitsEq w v a → ExactSpelling.FitsEq w v b := by
  intro h
  have hb := h wNatCell _ _ (Value.cell 0) sub_ref_equiv ⟨.nat, wNatCell_zero, rfl⟩
  obtain ⟨t', hs, heq⟩ := hb
  rw [wNatCell_zero] at hs
  cases hs
  cases heq

/-- The subtyping reading (in the checker's order since row 137) admits the equivalent
spelling, where the old judgment refuses it. -/
theorem natCell_equiv_spelling :
    Fits wNatCell (Value.cell 0) (.refOf (.union .nat .nat)) ∧
      ¬ Reviewed.StrongValue wNatCell (.refOf (.union .nat .nat)) (Value.cell 0) :=
  ⟨⟨.nat, wNatCell_zero, Ty.sub_le_subN sub_nat_union, Ty.sub_le_subN sub_union_nat⟩,
    natCell_old_refused⟩

/-! The old loaded-state claim, with every retired predicate resolved locally. -/
namespace ReviewedLoad
/-! ## G10: the declared M5 obligation `typedState_load` is false for `Ref.make(5)`

`loadsTyped` (`Typed/Assembly.lean:148-150`, `#proof_wanted`) promises a typed
initial state for every checked source with closed columns. The one-line program below checks at
`refOf nat` (kernel, `decide +kernel`; the cell spelling `Ref.Ref<number>` before the state plan's
T3a); its loaded code is the store protocol's
`refMake` step followed by returning the answer (`loaded_root`, by `rfl`). Every typed state of the
loaded machine types that code at the root's type, and `refProg_untypable` refutes that at every
world with an empty heap and an undeclared cell 0, which `WorldValid` forces for the loaded
machine. The obstruction is G8's: `HandlesLive` reads the heap length, the post names only the
table. -/

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
abbrev refTy : EffTy := EffTy.pure (.refOf .nat)

theorem refProg_checks : Api.typeOf refProg [] = some refTy := by decide +kernel

theorem loaded_root : ∃ f, (loadR refProg 20 20).fiber? Api.root = some f ∧
    f.frame.stack = [] ∧ f.frame.current = denoteR refProg refProg (rootPoint 20) :=
  ⟨_, rfl, rfl, rfl⟩

/-- No typed derivation of the loaded code at any world with an empty heap and cell 0 undeclared. -/
theorem refProg_untypable (w : W) (hRho : w.Ρ ⟨0⟩ = none) (hrefs : w.state.refs = []) :
    ¬ Reviewed.TypedProg refProg w refTy (denoteR refProg refProg (rootPoint 20)) := by
  intro h
  obtain ⟨cert, _, next⟩ := Reviewed.TypedProg.store_inv h
  have hle : w.leHost (w.addRef w.state ⟨0⟩ cert) := by
    refine ⟨⟨⟨fun _ h => h, Stores.le_refl _⟩, table_refl _, table_refl _,
      insert_extends _ _ _ hRho, ⟨fun key ty h => ?_, fun key types h => ?_⟩, fun _ => table_refl _,
      rfl⟩,
      fun _ _ h => h⟩
    · exact ⟨insert_extends _ _ _ hRho key ty h.1, fun value hv => h.2 value hv⟩
    · exact ⟨h.1, fun cell hc comp hcomp =>
        completionOk_extends w (w.addRef w.state ⟨0⟩ cert) types (insert_extends _ _ _ hRho) rfl comp
          (h.2 cell hc comp hcomp)⟩
  have post : (Reviewed.Ψ_S (refProg : ProgramSource)).post (w.addRef w.state ⟨0⟩ cert) (.refMake (.nat 5))
      cert (Val.cell ⟨0⟩) := ⟨⟨0⟩, rfl, insert_here w.Ρ ⟨0⟩ cert⟩
  have hex := Reviewed.TypedProg.pure_inv (next _ hle _ post)
  have hv := hex.2.1 (Val.cell ⟨0⟩) rfl
  have hlive := hv.2.2 (Handle.cell ⟨0⟩) (by rw [Val.keys_cell]; exact List.mem_singleton_self _)
  change 0 < w.state.refs.length at hlive
  rw [hrefs] at hlive
  exact Nat.lt_irrefl 0 hlive

/-- **The obligation's instance at `Ref.make(5)` is false**: its premises hold and no typed state
of the loaded machine exists. -/
theorem typedState_load_false :
    ¬ (Api.typeOf refProg [] = some refTy →
      ∃ w, Reviewed.TypedState (refProg : ProgramSource) refTy w (loadR refProg 20 20)) := by
  intro obligation
  obtain ⟨w, valid, ok, _⟩ := obligation refProg_checks
  obtain ⟨f, hf, hstack, hcur⟩ := loaded_root
  have hmem : f ∈ (loadR refProg 20 20).fibers := List.mem_of_find?_eq_some hf
  have hid : f.id = Api.root := by
    have found := List.find?_some hf
    change (f.id == Api.root) = true at found
    exact beq_iff_eq.mp found
  have hroot : expectOf w (.fiber f.id) = some refTy := by
    rw [hid]
    exact valid.root
  obtain ⟨tin, hprog, hst, _⟩ := (ok.c0 f hmem).c0.c0 _ hroot
  rw [hstack] at hst
  cases hst
  rw [hcur] at hprog
  have hRho : w.Ρ ⟨0⟩ = none := by
    cases hs : w.Ρ ⟨0⟩ with
    | none => rfl
    | some t =>
      have live : (w.Ρ ⟨0⟩).isSome = true := by rw [hs]; rfl
      exact absurd ((valid.heap ⟨0⟩).mp live) (Nat.lt_irrefl 0)
  have hrefs : w.state.refs = [] := by
    rw [valid.state]
    rfl
  exact refProg_untypable w hRho hrefs hprog

end ReviewedLoad

/-! ## New: the allocation programs' loaded code under the proposed judgment -/

def refProg : NativeEff := .perform .refMake (.lit (.nat 5))
def getProg : NativeEff := .bind (.perform .refMake (.lit (.nat 5))) (.perform .refGet (.var 0))

/-- The seat's `refProg_typedF`, re-proved here: allocate and return, at every world. -/
theorem refProg_typedF (w : W) :
    TypedProg (refProg : ProgramSource) w (EffTy.pure (.refOf .nat))
      (denoteR refProg refProg (rootPoint 20)) := by
  refine TypedProg.store (cert := Ty.nat) trivial ?_
  intro w' _ ans hpost
  obtain ⟨key, rfl, hs⟩ := hpost
  exact TypedProg.pure ⟨⟨.nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩

/-- The continuation after the guard, for a cell: the read. -/
theorem getProg_after (index : Nat) (completed : List (FiberId × ExitV)) :
    denoteRWith getProg 19 (Eff.perform NativeOp.refGet (Term.var 0))
      ({ (rootPoint 20) with completed }.childWith 1 (Val.cell ⟨index⟩)) =
      .vis (.inl (.refGet ⟨index⟩)) fun v => .pure (.success v) := rfl

/-- `Ref.make(5).flatMap(r => Ref.get(r))` at every world. The guard's body allocates and
unguards the cell at `refOf nat`; the declaration the post names is the fit. The run arm
reads the cell's declaration from the value's fit (the only link across the guard), carries it
to the later worlds, and reads the answer through `fits_subN` from the declaration's `Equiv` to
`nat` (the checker's order, row 137). The skip arm is a clean failure. -/
theorem getProg_typedF (w : W) :
    TypedProg (getProg : ProgramSource) w (EffTy.pure .nat)
      (denoteR getProg getProg (rootPoint 20)) := by
  refine TypedProg.guard (EffTy.pure (.refOf .nat)) ?_ ?_ ?_
  · refine TypedProg.store (cert := Ty.nat) trivial ?_
    intro w' _ ans hpost
    obtain ⟨key, rfl, hs⟩ := hpost
    exact TypedProg.unguard ⟨⟨.nat, hs, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩
  · intro w' _ ex hpost
    cases ex with
    | failure c => exact Bool.noConfusion hpost.1
    | success v =>
      have hv : Fits w' v (.refOf .nat) := hpost.2.1
      obtain ⟨⟨index⟩, rfl, t', hΡ, hsub, _⟩ := fits_refOf_inv hv
      refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h)
        (fun _ h => nomatch h) (fun _ _ _ h => nomatch h) () trivial ?_
      intro w'' hle' completed _
      rw [getProg_after]
      refine TypedProg.store (cert := ()) ⟨t', hle'.1.2.2.2.1 _ _ hΡ⟩ ?_
      intro w''' hle'' ans hpost'
      obtain ⟨ty, hty, hfit⟩ := hpost'
      have hsame : w'''.Ρ ⟨index⟩ = some t' := hle''.1.2.2.2.1 _ _ (hle'.1.2.2.2.1 _ _ hΡ)
      change w'''.Ρ ⟨index⟩ = some ty at hty
      rw [hsame] at hty
      cases hty
      exact TypedProg.pure ⟨fits_subN w''' hsub ans hfit, trivial⟩
  · intro w' _ ex hex miss
    cases ex with
    | success v => exact Bool.noConfusion miss
    | failure c => exact strongExit_of_clean w' _ c (cleanExit_of_never_fits w' _ c rfl hex.1) hex.2

/-! ## New: the M5 instance itself holds under the proposed judgment

For a program whose loaded code is typed at every world, the restated typed state holds at the
initial world: the one fiber's saved state is typed, and every other generated clause is over an
empty list or the empty context. So `typedState_load`, restated over `Fits`, is true at
`Ref.make(5)` and at the bind program, the two instances `verify-load.lean` refutes for
`StrongValue`. (No claim is made for every program.) Stated at every budget and source since
seat A's landing (2026-10-01). Since seat I2 (2026-10-01) the argument lives once in
`Laws/Program/Typed/Assembly.lean` (`typedState_load_of_code`, the generated part of
`machineTyped_load` over row 134's split), and this battery keeps a one-line use. -/

theorem typedStateF_load (root : ProgramSource) (ty : EffTy) (fuel compileFuel : Nat)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none)
    (code : ∀ w, TypedProg root w ty (denoteR root.program root.program (rootPoint compileFuel))) :
    ∃ w, TypedState root ty w (loadR root.program fuel compileFuel) :=
  typedState_load_of_code root ty fuel compileFuel noMarker code

theorem typedStateF_load_ref :
    ∃ w, TypedState (refProg : ProgramSource) (EffTy.pure (.refOf .nat)) w
      (loadR refProg 20 20) :=
  typedStateF_load refProg _ 20 20 rfl refProg_typedF

theorem typedStateF_load_get :
    ∃ w, TypedState (getProg : ProgramSource) (EffTy.pure .nat) w (loadR getProg 20 20) :=
  typedStateF_load getProg _ 20 20 rfl getProg_typedF

/-- The existing TypedState bank supplies the heap-extension rule. -/
theorem search_heap_extends (w : W) (cert : Ty) (hRho : w.Ρ ⟨0⟩ = none) :
    TableExtends w.Ρ (w.addRef w.state ⟨0⟩ cert).Ρ := by
  aesop (rule_sets := [Effect4.TypedState])

/-- Red control: without the bank the same search makes no progress. -/
example (w : W) (cert : Ty) (hRho : w.Ρ ⟨0⟩ = none) :
    TableExtends w.Ρ (w.addRef w.state ⟨0⟩ cert).Ρ := by
  fail_if_success aesop
  exact insert_extends _ _ _ hRho

end Test.Counterexamples.Machine.Semantics.ValueMembership
