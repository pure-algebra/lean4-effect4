import Effect4.Laws.Program.Typed.Assembly

/-! Research-only concatenation. Definitions, signatures and proof bodies are copied from the
named candidate. Imports and post-namespace proofgraph commands are omitted; see the map.
This checks copied declarations, not production module integration or obligation ceilings. -/

open Effect4.Program.Typed

namespace Research.Slice6.H2Repaired
abbrev World := Effect4.Program.Typed.World
end Research.Slice6.H2Repaired

/-! Source block: Admission.lean (Repaired). -/


/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts, using the value membership judgments from `Typed/Membership.lean`. The shared exit
judgment also excludes `badName` and `notImplemented`; clean failures require that explicit
exclusion premise. `missingService` remains admitted in part one. Control admission (FR-09) is an
arm of the one program judgment `TypedProg` in `Typed/Residual.lean` (ruling 2026-09-23).
-/

set_option autoImplicit false
namespace Research.Slice6.H2Repaired

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-- Part one excludes only `badName` and `notImplemented`. The type argument is retained
for the shared exit interface; `missingService` remains admitted pending part two. -/
def NoShapeDefect (_ty : EffTy) : ExitV → Prop
  | .success _ => True
  | .failure cause => ∀ reason ∈ cause.reasons, match reason with
    | .die defect _ => defect ≠ .badName ∧ defect ≠ .notImplemented
    | _ => True

/-- Base membership and the part-one defect exclusion at every typed exit position. -/
def ExitOk (w : World) (ty : EffTy) (ex : ExitV) : Prop :=
  FitsExit w ty ex ∧ NoShapeDefect ty ex

/-- Part one: an interrupt reason carries neither excluded defect. -/
theorem noShapeDefect_of_interrupts (ty : EffTy) (cause : CauseV)
    (interrupts : ∀ reason ∈ cause.reasons, reason.tag = .interrupt) :
    NoShapeDefect ty (.failure cause) := by
  intro reason member
  have tag := interrupts reason member
  cases reason with
  | fail _ _ => trivial
  | die _ _ => cases tag
  | interrupt _ _ => trivial

/-- Removing Fail reasons does not introduce a shape defect. -/
theorem noShapeDefect_stripFail (ty : EffTy) (cause : CauseV)
    (shape : NoShapeDefect ty (.failure cause)) :
    NoShapeDefect ty (.failure cause.stripFail) := by
  intro reason member
  exact shape reason ((Cause.mem_stripFail reason cause).mp member).1

/-- Combine contains only reasons from its two inputs. -/
theorem noShapeDefect_combine (ty : EffTy) (left right : CauseV)
    (leftShape : NoShapeDefect ty (.failure left))
    (rightShape : NoShapeDefect ty (.failure right)) :
    NoShapeDefect ty (.failure (Cause.combine left right)) := by
  intro reason member
  rcases (Cause.mem_combine reason left right).mp member with fromLeft | fromRight
  · exact leftShape reason fromLeft
  · exact rightShape reason fromRight

/-- Sanitization strips Fail reasons and combines the remaining original reasons with
recorded interruption reasons; exclusion is required of both inputs. -/
theorem noShapeDefect_sanitize (ty : EffTy) (cause interrupted : CauseV)
    (shape : NoShapeDefect ty (.failure cause))
    (interruptShape : NoShapeDefect ty (.failure interrupted)) :
    NoShapeDefect ty (.failure (Cause.sanitize cause interrupted)) :=
  noShapeDefect_combine ty cause.stripFail interrupted
    (noShapeDefect_stripFail ty cause shape) interruptShape

/-- An evaluation environment typed pointwise at the corresponding static types. -/
def EnvTyped (w : World) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → Fits w v ty

/-- The program the typed state is about, with the host-row table its checker reads. A bare
program coerces to a source with the empty table. -/
structure ProgramSource where
  program : NativeEff
  table : RowTable := []

instance : Coe NativeEff ProgramSource := ⟨fun program => { program }⟩

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
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : ExitOk w ty ex) :
      BodyTyped src w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTyped src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.layerBuild p m scope) ty

/-- Membership at the answer column gives the successful exit; its defect exclusion is vacuous. -/
theorem strongExit_success (w : World) (ty : EffTy) (v : Val) (h : Fits w v ty.answer) :
    ExitOk w ty (.success v) := ⟨h, trivial⟩

/-- A clean failure has base membership at every effect type because the error column
constrains only `Fail` reasons. The strengthened exit judgment separately requires the
explicit defect-exclusion premise: `cleanExit` alone admits `badName` and `notImplemented`. -/
theorem strongExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) (shape : NoShapeDefect ty (.failure c)) :
    ExitOk w ty (.failure c) := ⟨fitsExit_of_clean w ty c h, shape⟩

/-- At a `never` error column a fitting failure is clean: no value has type `never`. -/
theorem cleanExit_of_never (w : World) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
    (h : ExitOk w ty (.failure c)) : cleanExit (.failure c) = true := cleanExit_of_never_fits w ty c never h.1

end Research.Slice6.H2Repaired

/-! Source block: Residual.lean (Repaired). -/


/-!
# Laws.Program.Typed.Residual — concrete protocols and the program judgment

Defines `Ψ_S` over all 31 `SyncOp` rows with ghost certificates, `Ψ_F` over all 40 `FiberOp`
rows with dependent carriers, the one program judgment `TypedProg`, the interpreter hook
contracts, and the two settling program cases:
1. Polymorphic ref allocation and read on a heterogeneous heap.
2. Addressed fork and mask with body admission.

`TypedProg` is the slice 5 contract ruling of 2026-09-23
(`docs/research/2026-09-23-foundations-slice5-contract-ruling.md`, `E4-SCHED-CE-010/011/012`):
one certificate per operation, shared by its precondition, its postcondition and its
continuation, with the control markers typed by their own arms.
-/

set_option autoImplicit false
namespace Research.Slice6.H2Repaired

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-! ## The Store Protocol (31 SyncOp rows) -/

def StoreCert : SyncOp → Type
  | .refMake _ | .memoGet _ _ => Ty
  | .deferredMake | .memoBuild _ _ => Ty × Ty
  | _ => PUnit

def storePre (root : ProgramSource) (w : World) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ Fits w initial cert
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
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

def storePost (w' : World) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refUpdate _ _ | .refUpdateSome _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ | .refGetAndUpdateSome cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
  | .refUpdateAndGet cell _ | .refUpdateSomeAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ Fits w' ans ty
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

def Ψ_S (root : ProgramSource) : Protocol World StoreSig where
  Cert := StoreCert
  pre := storePre root
  post := storePost

/-! ## The Fiber Protocol (40 FiberOp rows) -/

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
  | .getId | .yieldNow _ | .ambientScope | .sync _ => True
  -- the context set keeps every service at its key's type (decision row 90)
  | .setContext ctx => ServicesFit w ctx.services
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
  | .getContext | .awaitAll _ | .awaitAllFailFast _ | .snapshotChildren => Fits w' ans cert
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ | .awaitNewChildren _ => ans = Val.unit
  | .ambientScope => ∃ sc, ans = Val.scopeHandle sc
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ ExitOk w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ Fits w' ans ty.answer
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    ExitOk w' cert ans
  | .unguard ex | .finishFinalizer ex | .closeScope _ ex | .scopeExit _ _ ex | .closeIter _ _ ex => ans = ex
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ ExitOk w' cert ex
  -- a live frontier is never answered (fuel exhaustion is not an exit)
  | .frontier _ _ => False
  -- the completed exits a callback reads, each at its fiber's declared type
  | .construction => ∀ p ∈ ans, ∃ ty, w'.Γ p.1 = some ty ∧ ExitOk w' ty p.2
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
  | pure {w : World} {ty : EffTy} {ex : ExitV} (exit : ExitOk w ty ex) :
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
      (skip : ∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) :
      TypedProg root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : World} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : TypedProg root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : World} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex) : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : World} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : ExitOk w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, TypedProg root w' ty (k ans)) :
      TypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

namespace TypedProg

theorem pure_inv {root : ProgramSource} {w : World} {ty : EffTy} {ex : ExitV}
    (h : TypedProg root w ty (.pure ex)) : ExitOk w ty ex := by
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
      (∀ w', w.leHost w' → ∀ ex, ExitOk w' mid ex → kind.hasExitArm ex = false →
        ExitOk w' ty ex) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip => exact ⟨mid, body, run, skip⟩

end TypedProg

/-- FR-09's marker payload inversion: a typed `unguard` carries an exit at the current type. -/
theorem unguard_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.unguard ex)) k)) :
    ExitOk w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)) :
    ExitOk w ty ex := by
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
        (next : ∀ v, Fits w v tin.answer →
          IteratorAnswer root w tout ((interpR root.program).iterNext name v).2) :
        IteratorProtocol root w tin tout name
  inductive IteratorAnswer (root : ProgramSource) (w : World) :
      EffTy → IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
    | done {tout : EffTy} (result : Val) (typed : ExitOk w tout (.success result)) :
        IteratorAnswer root w tout (.done result)
    | halt {tout : EffTy} (cause : CauseV) (typed : ExitOk w tout (.failure cause)) :
        IteratorAnswer root w tout (.halt cause)
    | resume {tout : EffTy} (code : RProgram) (name : EffName) (tin : EffTy)
        (typed : TypedProg root w tin code) (tail : IteratorProtocol root w tin tout name) :
        IteratorAnswer root w tout (.resume code name)
end

mutual
  inductive LoopProtocol (root : ProgramSource) (w : World) : EffTy → EffTy → EffName → Val → Prop
    | step {tin tout : EffTy} {name : EffName} {cursor : Val}
        (errors : tin.error = tout.error)
        (next : ∀ v, Fits w v tin.answer →
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
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, ExitOk w tin (.failure cause) →
    cause.hasInterrupts = true → TypedProg root w tout ((interpR root.program).cancelThenFail name cause)
  iterator := IteratorProtocol root
  loop := LoopProtocol root

/-! ## Settling Case 1: Polymorphic ref allocation and read on heterogeneous heap -/

def refAllocCont : Val → RProgram
  | .handle 2 index => .vis (.inl (.refGet ⟨index⟩)) fun v => .pure (.success v)
  | _ => .pure (.success (Val.bool false))

def refAllocGetProg : RProgram :=
  .vis (.inl (.refMake (Val.bool true))) refAllocCont

theorem strongValue_bool_true (w : World) : Fits w (Val.bool true) .bool := trivial

theorem strongExit_bool (w : World) (v : Val) (hv : Fits w v .bool) :
    ExitOk w (EffTy.pure .bool) (.success v) := strongExit_success w (EffTy.pure .bool) v hv

theorem settling_ref_allocation (root : ProgramSource) (w : World) (_h0 : HeapTypedAt w ⟨0⟩ .nat) :
    TypedProg root w (EffTy.pure .bool) refAllocGetProg := by
  refine TypedProg.store (cert := Ty.bool) ⟨rfl, strongValue_bool_true w⟩ ?_
  intro w' _ ans hpost
  rcases hpost with ⟨key, rfl, hkey⟩
  dsimp only [refAllocCont]
  refine TypedProg.store (cert := ()) ⟨Ty.bool, hkey⟩ ?_
  intro w'' hle v hpost'
  rcases hpost' with ⟨ty', hkey', hv⟩
  have extendsΡ := hle.1.2.2.2.1
  have sameKey : w''.Ρ key = some Ty.bool := extendsΡ key Ty.bool hkey
  change w''.Ρ key = some ty' at hkey'
  rw [sameKey] at hkey'
  cases hkey'
  exact TypedProg.pure (strongExit_bool w'' v hv)

theorem settling_ref_preserves_nat (w w' : World) (ordered : w.leHost w') (h0 : HeapTypedAt w ⟨0⟩ .nat) :
    HeapTypedAt w' ⟨0⟩ .nat :=
  heapTypedAt_mono w w' ⟨0⟩ .nat ordered h0

/-! ## Settling Case 2: Addressed fork and mask with body admission -/

def forkProg (child : Body) : RProgram :=
  .vis (.inr (.fork child ⟨false, false, .inherit⟩ [])) fun ans => .pure (.success ans)

def maskProg (flag : Bool) (body : Body) : RProgram :=
  .vis (.inr (.mask flag body)) fun ans => .pure ans

theorem settling_fork (root : ProgramSource) (w : World) (child : Body) (cert : EffTy)
    (hbody : BodyTyped root w child cert) :
    TypedProg root w (EffTy.pure (.fiberOf cert.answer cert.error)) (forkProg child) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_F, fiberPost] at hpost
  rcases hpost with ⟨id, rfl, hid⟩
  exact TypedProg.pure ⟨⟨cert, hid, Ty.sub_refl _, Ty.sub_refl _⟩, trivial⟩

theorem settling_mask (root : ProgramSource) (w : World) (flag : Bool) (body : Body) (cert : EffTy)
    (hbody : BodyTyped root w body cert) :
    TypedProg root w cert (maskProg flag body) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_F, fiberPost] at hpost
  exact TypedProg.pure hpost

/-! FR-09's payload inversions, restated over the one judgment under their M3a names. -/
namespace M3aAdmissionObligations

theorem unguard_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProg root w ty (.vis (.inr (.unguard ex)) k) → ExitOk w ty ex) := ⟨⟩

theorem finishFinalizer_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k) → ExitOk w ty ex) := ⟨⟩

end M3aAdmissionObligations

namespace M3aResidualObligations

theorem settling_ref_allocation (_root : ProgramSource) (_w : World) (_h0 : HeapTypedAt _w ⟨0⟩ .nat) :
    ProofGraph.Obligation (TypedProg _root _w (EffTy.pure .bool) refAllocGetProg) := ⟨⟩

theorem settling_ref_preserves_nat (_w _w' : World) (_ordered : _w.leHost _w') (_h0 : HeapTypedAt _w ⟨0⟩ .nat) :
    ProofGraph.Obligation (HeapTypedAt _w' ⟨0⟩ .nat) := ⟨⟩

theorem settling_fork (_root : ProgramSource) (_w : World) (_child : Body) (_cert : EffTy)
    (_hbody : BodyTyped _root _w _child _cert) :
    ProofGraph.Obligation (TypedProg _root _w (EffTy.pure (.fiberOf _cert.answer _cert.error)) (forkProg _child)) := ⟨⟩

theorem settling_mask (_root : ProgramSource) (_w : World) (_flag : Bool) (_body : Body) (_cert : EffTy)
    (_hbody : BodyTyped _root _w _body _cert) :
    ProofGraph.Obligation (TypedProg _root _w _cert (maskProg _flag _body)) := ⟨⟩

end M3aResidualObligations

/-! World weakening (ruling 2026-09-23, audit A4): typing survives every later world the host
order allows. The hook clauses are stated at one world and consumed at later ones, and every
continuation of `TypedProg` is typed at the world its answer arrives in, so the stack and
delivery proofs of slice 5 need these three. The membership cases follow from the membership
transport laws; residual-program weakening remains an open obligation. -/

/-- Value membership persists along the host-world order, with the ledger's binder order. -/
theorem strongValue_mono (w w' : World) (ty : Ty) (v : Val) :
    w.leHost w' → Fits w v ty → Fits w' v ty :=
  fun ordered h => fits_mono ordered h

/-- Exit membership persists along the host-world order, with the ledger's binder order. -/
theorem strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV) :
    w.leHost w' → ExitOk w ty ex → ExitOk w' ty ex :=
  fun ordered h => ⟨fitsExit_mono ordered h.1, h.2⟩

namespace M3bWorld

theorem strongValue_mono (w w' : World) (ty : Ty) (v : Val) :
    ProofGraph.Obligation (w.leHost w' → Fits w v ty → Fits w' v ty) := ⟨⟩

theorem strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV) :
    ProofGraph.Obligation (w.leHost w' → ExitOk w ty ex → ExitOk w' ty ex) := ⟨⟩

theorem typedProg_mono (root : ProgramSource) (w w' : World) (ty : EffTy) (p : RProgram) :
    ProofGraph.Obligation (w.leHost w' → TypedProg root w ty p → TypedProg root w' ty p) := ⟨⟩

end M3bWorld

end Research.Slice6.H2Repaired

/-! Source block: Stack.lean (Repaired). -/


/-!
# Laws.Program.Typed.Stack — the saved stack's walk preserves typing

Slice 5 (M4) of the foundations plan, as amended by the contract ruling of 2026-09-23 and the
protocol repair of 2026-09-24. `popR_typed`: delivering a typed exit to a typed stack either
installs typed code over a typed remaining stack, or completes with an exit typed at the stack's
final type. Its only premises are `HookLaws` (the three named hooks) and `InterruptProvenance`
(recorded causes are interrupts); there is no run premise. A preempted catch passes the sanitized
cause (`U-01`), which carries no `Fail` and so fits every type.
-/

set_option autoImplicit false
namespace Research.Slice6.H2Repaired
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-- Exactly the facts `popR`'s three named-hook arms need about an interpreter. -/
structure HookLaws (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols) : Prop where
  asyncFinalizer : ∀ w tin tout name, hooks.asyncFinalizer w tin tout name →
    tin = tout ∧ ∀ cause, ExitOk w tin (.failure cause) → cause.hasInterrupts = true →
      TypedProg root w tout (interp.cancelThenFail name cause)
  iterator : ∀ w tin tout name, hooks.iterator w tin tout name →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match (interp.iterNext name v).2 with
      | .done result => ExitOk w tout (.success result)
      | .halt cause => ExitOk w tout (.failure cause)
      | .resume code name' => ∃ tin', TypedProg root w tin' code ∧ hooks.iterator w tin' tout name'
  loop : ∀ w tin tout name cursor, hooks.loop w tin tout name cursor →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match interp.loopResume name cursor v with
      | .continue cursor' body => ∃ tin', TypedProg root w tin' body ∧
          hooks.loop w tin' tout name cursor'
      | .finish code => TypedProg root w tout code

/-- The two outcomes of the walk, at the saved stack's final type. -/
def WalkTyped (root : ProgramSource) (hooks : FrameProtocols) (w : World) (tout : EffTy) :
    RSaved × Option ExitV → Prop
  | (frame, none) => SavedOk (TypedProg root) ExitOk hooks w tout frame
  | (_, some ex) => ExitOk w tout ex

/-! ## Clean exits along the walk -/

/-- A cause whose reasons are all interrupts is clean. -/
theorem cleanExit_of_interrupts (c : CauseV) (h : ∀ r ∈ c.reasons, r.tag = .interrupt) :
    cleanExit (.failure c) = true := by
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  rw [h r hr]
  rfl

/-- A recorded interrupt is clean. -/
theorem recorded_clean {x : RSaved} (hp : InterruptProvenance x) {c : CauseV}
    (hc : x.interruptedCause = some c) : cleanExit (.failure c) = true :=
  cleanExit_of_interrupts c (hp.recorded c hc)

/-- The cause a masked region injects is clean. -/
theorem pendingCause_clean {x : RSaved} (hp : InterruptProvenance x) :
    cleanExit (.failure x.pendingCause) = true := by
  cases hc : x.interruptedCause with
  | some c =>
    have : x.pendingCause = c := by simp only [RSaved.pendingCause, hc, Option.getD_some]
    rw [this]
    exact recorded_clean hp hc
  | none =>
    have : x.pendingCause = Cause.empty := by simp only [RSaved.pendingCause, hc, Option.getD_none]
    rw [this]
    rfl

/-- The sanitized cause at a preempted catch is clean (`U-01`, `Cause.sanitize_clean`). -/
theorem sanitize_clean_exit {x : RSaved} (hp : InterruptProvenance x) (cause : CauseV) {ic : CauseV}
    (hic : x.interruptedCause = some ic) : cleanExit (.failure (Cause.sanitize cause ic)) = true := by
  have hne : ∀ r ∈ ic.reasons, r.tag ≠ .fail := by
    intro r hr heq
    have := hp.recorded ic hic r hr
    rw [heq] at this
    cases this
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  exact bne_iff_ne.mpr (Cause.sanitize_clean cause ic hne r hr)

/-- A recorded cause has only interrupt reasons, so it meets part one's exclusion. -/
theorem recorded_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x)
    {cause : CauseV} (recorded : x.interruptedCause = some cause) :
    NoShapeDefect ty (.failure cause) :=
  noShapeDefect_of_interrupts ty cause (hp.recorded cause recorded)

/-- The injected pending cause is recorded interruption or the empty cause. -/
theorem pendingCause_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x) :
    NoShapeDefect ty (.failure x.pendingCause) := by
  cases recorded : x.interruptedCause with
  | some cause =>
    have pending : x.pendingCause = cause := by
      simp only [RSaved.pendingCause, recorded, Option.getD_some]
    rw [pending]
    exact recorded_noShapeDefect ty hp recorded
  | none =>
    have pending : x.pendingCause = Cause.empty := by
      simp only [RSaved.pendingCause, recorded, Option.getD_none]
    rw [pending]
    exact noShapeDefect_of_interrupts ty Cause.empty (fun _ member => nomatch member)

/-- Preemption keeps exclusion only when the original cause has it; provenance supplies
exclusion of the recorded cause. No requirement-row transport is claimed in part one. -/
theorem sanitize_noShapeDefect (ty : EffTy) {x : RSaved} (hp : InterruptProvenance x)
    (cause : CauseV) {interrupted : CauseV} (recorded : x.interruptedCause = some interrupted)
    (shape : NoShapeDefect ty (.failure cause)) :
    NoShapeDefect ty (.failure (Cause.sanitize cause interrupted)) :=
  noShapeDefect_sanitize ty cause interrupted shape (recorded_noShapeDefect ty hp recorded)

/-- In part one, failure membership depends on the error column and the exclusion
is independent of all type columns. -/
theorem strongExit_failure_of_error {w : World} {tin tout : EffTy} {c : CauseV}
    (herr : tin.error = tout.error) (h : ExitOk w tin (.failure c)) : ExitOk w tout (.failure c) := ⟨fitsExit_failure_of_error herr h.1, h.2⟩

theorem walk_saved {root : ProgramSource} {hooks : FrameProtocols} {w : World} {tout : EffTy}
    {x : RSaved} (tin : EffTy) (code : TypedProg root w tin x.current)
    (stack : StackAccepts (TypedProg root) ExitOk hooks w tin tout x.stack)
    (hp : InterruptProvenance x) : WalkTyped root hooks w tout (x, none) :=
  ⟨tin, code, stack, hp⟩

theorem walk_done {root : ProgramSource} {hooks : FrameProtocols} {w : World} {tout : EffTy}
    {x : RSaved} {ex : ExitV} (h : ExitOk w tout ex) : WalkTyped root hooks w tout (x, some ex) :=
  h

/-! ## The walk -/

theorem popR_typed (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (laws : HookLaws root interp hooks) (w : World) :
    ∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProg root) ExitOk hooks w tin tout stack →
      ExitOk w tin ex → InterruptProvenance frame →
      WalkTyped root hooks w tout (popR interp ex stack frame) := by
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
            exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ c (recorded_clean hp rfl) (recorded_noShapeDefect _ hp rfl)))
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
            exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ c (recorded_clean hp rfl) (recorded_noShapeDefect _ hp rfl)))
              tail ⟨hp.recorded, hp.deferred⟩
          | failure c' =>
            simp only [popR, Bool.not_true, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
            exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
    | resume kind next run skip =>
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      have hp' : ∀ (c : RProgram) (s : List ScopeFrame) (b : Bool),
          InterruptProvenance ⟨c, s, b, ic, deferred⟩ := fun _ _ _ => ⟨hp.recorded, hp.deferred⟩
      -- Provenance makes the recorded cause clean; the original cause must also
      -- satisfy exclusion, supplied by the incoming typed exit.
      have preempt : ∀ (ty : EffTy) (cause ic' : CauseV),
          NoShapeDefect ty (.failure cause) → ic = some ic' →
          ExitOk w ty (.failure (Cause.sanitize cause ic')) := fun ty cause _ shape h =>
        strongExit_of_clean w ty _ (sanitize_clean_exit hp cause h)
          (sanitize_noShapeDefect ty hp cause h shape)
      cases kind with
      | onSuccess =>
        cases ex with
        | success v =>
          simp only [popR]
          exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
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
          · exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
          · exact ih _ _ _ _ tail (preempt _ c _ hex.2 rfl) (hp' _ _ _)
      | all =>
        cases ex with
        | success v =>
          simp only [popR]
          exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
        | failure c =>
          simp only [popR]
          cases i <;> cases ic
          · exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
          · exact walk_saved _ (run _ hex rfl) tail (hp' _ _ _)
          · exact ih _ _ _ _ tail (preempt _ c _ hex.2 rfl) (hp' _ _ _)
      | onExit b =>
        cases b with
        | false =>
          cases ex <;> simp only [popR] <;>
            exact walk_saved _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
        | true =>
          cases ex with
          | success v =>
            simp only [popR]
            exact walk_saved _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
          | failure c =>
            simp only [popR]
            cases i <;> cases ic
            · exact walk_saved _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact walk_saved _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact walk_saved _ (run _ hex rfl) (.cons (.finalizerMask _ _) tail) (hp' _ _ _)
            · exact ih _ _ _ _ tail (preempt _ c _ hex.2 rfl) (hp' _ _ _)
    | answer next run =>
      have hrun := run ex hex
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      simp only [popR]
      split
      · rename_i ex' heq
        rw [heq] at hrun
        exact ih _ _ _ _ tail (TypedProg.pure_inv hrun) ⟨hp.recorded, hp.deferred⟩
      · rename_i ex' k heq
        rw [heq] at hrun
        exact ih _ _ _ _ tail (unguard_payload_inv _ _ _ _ _ hrun) ⟨hp.recorded, hp.deferred⟩
      · exact walk_saved _ hrun tail ⟨hp.recorded, hp.deferred⟩
    | asyncFinalizer name protocol =>
      obtain ⟨same, cancel⟩ := laws.asyncFinalizer w _ _ name protocol
      subst same
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        have code : TypedProg root w tin
            (if c.hasInterrupts then interp.cancelThenFail name c else .pure (.failure c)) := by
          split
          · rename_i hint
            exact cancel c hex hint
          · exact TypedProg.pure hex
        simp only [popR]
        cases i
        · exact walk_saved _ code tail ⟨hp.recorded, hp.deferred⟩
        · exact walk_saved _ code (.cons (.restoreMask _ _) tail) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        simp only [popR]
        cases i <;> cases ic
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact ih _ _ _ _ tail hex ⟨hp.recorded, hp.deferred⟩
        · exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ _ (pendingCause_clean ⟨hp.recorded, hp.deferred⟩)
          (pendingCause_noShapeDefect _ ⟨hp.recorded, hp.deferred⟩)))
            tail ⟨hp.recorded, hp.deferred⟩
    | iter name protocol =>
      obtain ⟨errors, step⟩ := laws.iterator w _ _ name protocol
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (strongExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex.1
        cases hs : (interp.iterNext name v).2 with
        | done result =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_saved _ (TypedProg.pure h) tail ⟨hp.recorded, hp.deferred⟩
        | halt cause =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_saved _ (TypedProg.pure h) tail ⟨hp.recorded, hp.deferred⟩
        | resume code name' =>
          rw [hs] at h
          obtain ⟨tin', typed, next⟩ := h
          simp only [popR, hs]
          exact walk_saved _ typed (.cons (.iter _ next) tail) ⟨hp.recorded, hp.deferred⟩
    | loop name cursor protocol =>
      obtain ⟨errors, step⟩ := laws.loop w _ _ name cursor protocol
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (strongExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex.1
        cases hs : interp.loopResume name cursor v with
        | «continue» cursor' body =>
          rw [hs] at h
          obtain ⟨tin', typed, next⟩ := h
          simp only [popR, hs]
          exact walk_saved _ typed (.cons (.loop _ _ next) tail) ⟨hp.recorded, hp.deferred⟩
        | finish code =>
          rw [hs] at h
          simp only [popR, hs]
          exact walk_saved _ h tail ⟨hp.recorded, hp.deferred⟩

/-! ## The reference interpreter's hooks -/

/-- The concrete hook contracts are exactly what the walk needs of `interpR` (the M5 hook
obligation of the slice 5 brief, closed here because the repaired protocols state them
directly). -/
theorem hookLaws_interpR (root : ProgramSource) :
    HookLaws root (interpR root.program) (frameProtocols root) where
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
theorem popR_typed_interpR (root : ProgramSource) (w : World) (stack : List ScopeFrame)
    (tin tout : EffTy) (ex : ExitV) (frame : RSaved)
    (hstack : StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin tout stack)
    (hex : ExitOk w tin ex) (hp : InterruptProvenance frame) :
    WalkTyped root (frameProtocols root) w tout (popR (interpR root.program) ex stack frame) :=
  popR_typed root _ _ (hookLaws_interpR root) w stack tin tout ex frame hstack hex hp

/-! ## Saving and delivering -/

/-- Installing an operation's code below its answer adapter keeps the saved state typed: the
adapter and the old stack meet at `middle`, the code has the operation's own type `tin`. -/
theorem saveAnswerR_typed (root : ProgramSource) (hooks : FrameProtocols) (w : World)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (hcode : TypedProg root w tin code)
    (hnext : ∀ ex, ExitOk w tin ex → TypedProg root w middle (next ex))
    (hstack : StackAccepts (TypedProg root) ExitOk hooks w middle final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    SavedOk (TypedProg root) ExitOk hooks w final (answerR (saveAnswerR f next) code).frame :=
  ⟨tin, hcode, .cons (.answer next hnext) hstack, ⟨hp.recorded, hp.deferred⟩⟩

/-- The fiber a matching resume leaves: unparked, the token's pending entries dropped, the
delivered code current, the stack untouched. -/
def resumed (f : RFiber) (token : Nat) (code : RProgram) : RFiber :=
  { f with
    parked := .notParked
    pending := f.pending.filter (fun p => p.token ≠ token)
    frame := { f.frame with current := code } }

/-- A resume at the parked token installs the delivered code, which `ResumeOk` types at the
token's declared type, over the stack the park saved at that type. -/
theorem deliver_active (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : World) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (found : m.fiber? f.id = some f) (parked : f.parked = .withGuard token)
    (declared : w.Θ f.id token = some tin) (typed : ResumeOk (TypedProg root) w f.id token code)
    (hstack : StackAccepts (TypedProg root) ExitOk hooks w tin final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    (letI := termEvaluatorFor root.program
     driveStep interp m (.resume f.id token code) rest) =
      ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
    SavedOk (TypedProg root) ExitOk hooks w final (resumed f token code).frame := by
  refine ⟨?_, tin, typed tin declared, hstack, ⟨hp.recorded, hp.deferred⟩⟩
  simp only [driveStep, found, parked, ↓reduceIte]
  rfl

/-- A resume at another token leaves the machine and the queue as they were. -/
theorem deliver_stale (root : ProgramSource) (interp : RInterp) (m : RState) (f : RFiber)
    (parkedToken token : Nat) (code : RProgram) (rest : List RCmd)
    (found : m.fiber? f.id = some f) (parked : f.parked = .withGuard parkedToken)
    (stale : parkedToken ≠ token) :
    (letI := termEvaluatorFor root.program
     driveStep interp m (.resume f.id token code) rest) = (m, rest) := by
  simp only [driveStep, found, parked, stale, ↓reduceIte]


namespace M4Stack

theorem popR_typed (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (_laws : HookLaws root interp hooks) (w : World) : ProofGraph.Obligation
    (∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProg root) ExitOk hooks w tin tout stack →
      ExitOk w tin ex → InterruptProvenance frame →
      WalkTyped root hooks w tout (popR interp ex stack frame)) := ⟨⟩

theorem saveAnswerR_typed (root : ProgramSource) (hooks : FrameProtocols) (w : World)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (_hcode : TypedProg root w tin code)
    (_hnext : ∀ ex, ExitOk w tin ex → TypedProg root w middle (next ex))
    (_hstack : StackAccepts (TypedProg root) ExitOk hooks w middle final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    (SavedOk (TypedProg root) ExitOk hooks w final (answerR (saveAnswerR f next) code).frame) := ⟨⟩

theorem deliver_active (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : World) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard token)
    (_declared : w.Θ f.id token = some tin) (_typed : ResumeOk (TypedProg root) w f.id token code)
    (_hstack : StackAccepts (TypedProg root) ExitOk hooks w tin final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) =
        ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
      SavedOk (TypedProg root) ExitOk hooks w final (resumed f token code).frame) := ⟨⟩

theorem deliver_stale (root : ProgramSource) (interp : RInterp) (m : RState) (f : RFiber)
    (parkedToken token : Nat) (code : RProgram) (rest : List RCmd)
    (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard parkedToken)
    (_stale : parkedToken ≠ token) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) = (m, rest)) := ⟨⟩

end M4Stack

namespace M5Hooks
theorem hookLaws_interpR (root : ProgramSource) :
    ProofGraph.Obligation (HookLaws root (interpR root.program) (frameProtocols root)) := ⟨⟩
end M5Hooks

end Research.Slice6.H2Repaired

/-! Source block: Assembly.lean (Repaired). -/


/-!
# Laws.Program.Typed.Assembly — the typed state of the reference machine

Slice 5's assembly (§3.5 of the brief, as amended): the generated predicate bundle `Preds`
instantiated with the strong judgments (`preds`), the typed state (`TypedState`: validity, the
generated whole-state predicate, and the active-delivery correlation), reachability
(`RReachable`), admitted host answers (`AnswerOk`), and the declared obligations the milestones
after slice 5 prove: initialization (`typedState_load`, M5) and the transition ledger, one
preservation obligation per command constructor (M6). `capture_lookup` is proved here.

Two limits of the generated bundle are recorded rather than papered over: `PendingOk` receives
the enclosing position, not the fiber, so it can only say every pending token is declared for
some fiber; `RaceOk` says each race's host is parked at a declared token, and the race's result
type is the host's declared token type through `ResumeOk` on the resume it enqueues.
-/

set_option autoImplicit false
namespace Research.Slice6.H2Repaired
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-- The type a position is expected at: the root's and each fiber's declared type (D7). -/
def expectOf (w : World) : Expect → Option EffTy
  | .root => w.Γ Api.root
  | .fiber id => w.Γ id
  | .hook _ => none

/-- A completion at an effect type: an exit strongly, a reference completion through the
heap table. -/
def CompletionStrong (w : World) (ty : EffTy) : Completion Val Err Defect FiberId Ann → Prop
  | .ofExit ex => ExitOk w ty ex
  | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ t.sub ty.answer = true

/-- A capture's release is admitted: its path addresses an `acquireRelease` the checker types
under an environment its values fit, extended by the acquired value, and its context's
services are typed. -/
def CaptureTyped (root : ProgramSource) (w : World) (c : Capture) : Prop :=
  ∃ (acquire release : NativeEff) (env : List Ty) (t a : EffTy),
    Node.at_ (.eff root.program) c.path = some (.eff (.acquireRelease acquire release)) ∧
    Checker.check (nativeSignature root.table) env c.path (.acquireRelease acquire release) = .ok t ∧
    Checker.check (nativeSignature root.table) env (c.path ++ [0]) acquire = .ok a ∧
    EnvTyped w (env ++ [a.answer]) c.env ∧ ServicesFit w c.ctx.services

/-- The generated bundle, instantiated with the strong judgments. -/
def preds (root : ProgramSource) : Preds World where
  SavedOk w e x := ∀ ty, expectOf w e = some ty →
    Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → ExitOk w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProg root) w target token code
  ServiceOk w _ ctx := ServicesFit w ctx.services
  RaceOk w _ races := ∀ r ∈ races, (w.Θ r.host r.token).isSome = true
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrong w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → Fits w v ty
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c
  CaptureOk w _ c := CaptureTyped root w c

/-- The typed state: world validity, the generated whole-state predicate over `preds`, and the
active-delivery correlation: a parked fiber's saved stack expects its token's declared type. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (preds root) w m ∧
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) ExitOk (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

/-- M6's reference runner has no host table, so its tapes contain no host answer.
Clock advances, dispatcher decisions and interrupts remain in scope (row 95). -/
def NoHostAnswer : Api.Decision → Prop
  | .answerAsync _ _ _ => False
  | _ => True

/-- A state a tape with no host answer reaches from the loaded program. -/
def RReachable (root : ProgramSource) (fuel : Nat) (m : RState) : Prop :=
  ∃ tape, (∀ d ∈ tape, NoHostAnswer d) ∧ m = (replayR root.program fuel tape).machine

/-- A host answer is admitted: an answer to a fiber parked at that token fits the token's
declared type. Answers to anything else run inertly and impose nothing. -/
def AnswerOk (w : World) (m : RState) : Api.Decision → Prop
  | .answerAsync target token answer =>
    (∃ f, m.fiber? target = some f ∧ f.parked = .withGuard token) →
      ∃ ty, w.Θ target token = some ty ∧ CompletionStrong w ty answer
  | _ => True

/-- The queued commands carry typed resumes. -/
def QueueOk (root : ProgramSource) (w : World) (cmds : List RCmd) : Prop :=
  ∀ c ∈ cmds, match c with
    | .resume target token code => Contracts.ResumeOk (TypedProg root) w target token code
    | _ => True

/-- One command keeps the typed state and the queue typed, at some later world. -/
def StepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, TypedState root rootTy w m → QueueOk root w (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 ∧ QueueOk root w' r.2

/-! ## The capture lookup -/

theorem envTyped_append {w : World} {env : List Ty} {vals : List Val} {ty : Ty} {v : Val}
    (h : EnvTyped w env vals) (hv : Fits w v ty) : EnvTyped w (env ++ [ty]) (vals ++ [v]) := by
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
theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (h : CaptureTyped root w c)
    (hex : Fits w exVal (.exitOf .unknown .unknown)) :
    ∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty := by
  obtain ⟨acquire, release, env, t, a, hnode, hcheck, hacq, henv, _⟩ := h
  obtain ⟨a', r, hacq', hrel, _, _⟩ := Checker.inv_acquireRelease _ _ _ _ _ t hcheck
  rw [hacq] at hacq'
  cases hacq'
  refine ⟨r, release, env ++ [a.answer, .exitOf .unknown .unknown], ?_, hrel, ?_⟩
  · show Node.at_ (.eff root.program) (c.path ++ [1]) = some (.eff release)
    rw [Agreement.Node.at_append, hnode]
    rfl
  · show EnvTyped w (env ++ [a.answer, .exitOf .unknown .unknown]) (c.env ++ [exVal])
    have := envTyped_append henv hex
    simpa only [List.append_assoc, List.singleton_append] using this

/-! ## Declared obligations

`typedState_load` (M5: initialization from an admitted source). The transition ledger (M6): one
preservation obligation per command constructor, one for a tape decision under admitted host
answers, and the capstone that every reachable state is typed. Declared, not proved. -/
namespace M3bAssembly

theorem typedState_load (root : ProgramSource) (rootTy : EffTy) (fuel compileFuel : Nat) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      ∃ w, TypedState root rootTy w (loadR root.program fuel compileFuel)) := ⟨⟩

theorem capture_lookup (root : ProgramSource) (w : World) (c : Capture)
    (completed : List (FiberId × ExitV)) (exVal : Val) (_h : CaptureTyped root w c)
    (_hex : Fits w exVal (.exitOf .unknown .unknown)) : ProofGraph.Obligation
    (∃ rty, PointTyped root w ((Point.ofCapture c completed).childWith 1 exVal) rty) := ⟨⟩

end M3bAssembly

namespace M6Ledger

theorem step_evaluate (root : ProgramSource) (rootTy : EffTy) (id : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.evaluate id)) := ⟨⟩

theorem step_loop (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.loop id yielding)) := ⟨⟩

theorem step_deliver (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.deliver id yielding)) := ⟨⟩

theorem step_finish (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (exit : ExitV) :
    ProofGraph.Obligation (StepPreserves root rootTy (.finish id exit)) := ⟨⟩

theorem step_resume (root : ProgramSource) (rootTy : EffTy) (id : FiberId) (token : Nat) (code : RProgram) :
    ProofGraph.Obligation (StepPreserves root rootTy (.resume id token code)) := ⟨⟩

theorem step_launch (root : ProgramSource) (rootTy : EffTy) (race : Nat) :
    ProofGraph.Obligation (StepPreserves root rootTy (.launch race)) := ⟨⟩

theorem step_enrollRace (root : ProgramSource) (rootTy : EffTy) (race : Nat) (child : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.enrollRace race child)) := ⟨⟩

theorem step_registrationDone (root : ProgramSource) (rootTy : EffTy) (race : Nat) (yielding : Bool) :
    ProofGraph.Obligation (StepPreserves root rootTy (.registrationDone race yielding)) := ⟨⟩

theorem step_interruptTarget (root : ProgramSource) (rootTy : EffTy) (target : FiberId) (who : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreserves root rootTy (.interruptTarget target who extra)) := ⟨⟩

theorem step_afterInterrupt (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (kind : ParkKind) :
    ProofGraph.Obligation (StepPreserves root rootTy (.afterInterrupt host yielding kind)) := ⟨⟩

theorem step_raceCancel (root : ProgramSource) (rootTy : EffTy) (race : Nat) (host : FiberId)
    (yielding : Bool) (remaining visited : List FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.raceCancel race host yielding remaining visited)) := ⟨⟩

theorem step_trackChild (root : ProgramSource) (rootTy : EffTy) (parent child : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.trackChild parent child)) := ⟨⟩

theorem step_observe (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) (exit : ExitV) (observer : Observer) :
    ProofGraph.Obligation (StepPreserves root rootTy (.observe fiber exit observer)) := ⟨⟩

theorem step_exitDone (root : ProgramSource) (rootTy : EffTy) (fiber : FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.exitDone fiber)) := ⟨⟩

theorem step_closeParAwait (root : ProgramSource) (rootTy : EffTy) (host : FiberId) (yielding : Bool) (fibers : List FiberId) :
    ProofGraph.Obligation (StepPreserves root rootTy (.closeParAwait host yielding fibers)) := ⟨⟩

theorem step_link (root : ProgramSource) (rootTy : EffTy) (mode : Supervision.ScopeMode) (scope : Nat)
    (target : FiberId) (interruptor : Option FiberId) (extra : ReasonAnnotations Ann) :
    ProofGraph.Obligation (StepPreserves root rootTy (.link mode scope target interruptor extra)) := ⟨⟩

theorem step_drainDue (root : ProgramSource) (rootTy : EffTy) :
    ProofGraph.Obligation (StepPreserves root rootTy .drainDue) := ⟨⟩

theorem step_wake (root : ProgramSource) (rootTy : EffTy) (list : WakeKey) (phase : WakePhase) :
    ProofGraph.Obligation (StepPreserves root rootTy (.wake list phase)) := ⟨⟩

/-- A tape decision keeps the typed state when its host answer, if any, is admitted. -/
theorem decision_preserves (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (d : Api.Decision) :
    ProofGraph.Obligation (∀ w m, TypedState root rootTy w m → AnswerOk w m d →
      ∃ w', w.leHost w' ∧ TypedState root rootTy w'
        (letI := termEvaluatorFor root.program
         stepDecisionState (interpR root.program) fuel m d).1) := ⟨⟩

/-- The capstone obligation: every state a tape with no host answer reaches from a
checked, closed source is typed. This restriction repairs `E4-SCHED-CE-015` for host answers
only. The statement remains refuted on programs with no host by `E4-PROV-CE-005`,
`E4-PROV-CE-006` and `E4-SCHED-CE-016`. The table-based Fits judgment repairs the
liveness obstruction E4-TYPED-CE-004; the general M5 initialization proof is still open.

`ExitOk` excludes `badName` and `notImplemented` at typed code, saved-stack, queued-result
and stored-completion exit positions (`E4-TYPED-CE-007`). The initialization, transition and
reachability proofs remain open, so this judgment alone does not establish their absence
from every run. `missingService` remains admitted at every requirement row in H2 part one;
its exclusion requires the held frame-and-operation contract amendment (row 117). -/
theorem typedState_reachable (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      RReachable root fuel m → ∃ w, TypedState root rootTy w m) := ⟨⟩

end M6Ledger

end Research.Slice6.H2Repaired



/-! H2 part-one candidate controls; not yet compiled. These are new test declarations.
The old field-only placement is retained separately in FieldOnlyRed.lean. -/
set_option autoImplicit false
namespace Test.Program.H2PartOne
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

/-- The base membership judgment remains deliberately unchanged. -/
theorem base_badName_still_fits (w : W) (ty : EffTy) :
    FitsExit w ty (.failure (Cause.die .badName)) := fitsExit_of_clean w ty _ rfl

theorem clean_still_allows_badName :
    cleanExit (.failure (Cause.die .badName)) = true := rfl

theorem badName_refused (w : W) (ty : EffTy) :
    ¬ Research.Slice6.H2Repaired.ExitOk w ty (.failure (Cause.die .badName)) := by
  intro typed
  have excluded := typed.2 (.die .badName .empty) (List.mem_singleton_self _)
  exact excluded.1 rfl

theorem notImplemented_refused (w : W) (ty : EffTy) :
    ¬ Research.Slice6.H2Repaired.ExitOk w ty (.failure (Cause.die .notImplemented)) := by
  intro typed
  have excluded := typed.2 (.die .notImplemented .empty) (List.mem_singleton_self _)
  exact excluded.2 rfl

theorem bad_current_code_refused (root : Research.Slice6.H2Repaired.ProgramSource) (w : W) (ty : EffTy) :
    ¬ Research.Slice6.H2Repaired.TypedProg root w ty (.pure (.failure (Cause.die .badName))) :=
  fun typed => badName_refused w ty (Research.Slice6.H2Repaired.TypedProg.pure_inv typed)

theorem notImplemented_current_code_refused (root : Research.Slice6.H2Repaired.ProgramSource) (w : W) (ty : EffTy) :
    ¬ Research.Slice6.H2Repaired.TypedProg root w ty (.pure (.failure (Cause.die .notImplemented))) :=
  fun typed => notImplemented_refused w ty (Research.Slice6.H2Repaired.TypedProg.pure_inv typed)

/-- The defect clause is finite and independent of requirement rows in part one. -/
theorem ordinary_die_shape (ty : EffTy) (defect : Defect)
    (notBadName : defect ≠ .badName) (implemented : defect ≠ .notImplemented) :
    Research.Slice6.H2Repaired.NoShapeDefect ty (.failure (Cause.die defect)) := by
  intro reason member
  simp only [Cause.die_reasons, List.mem_singleton] at member
  subst member
  exact ⟨notBadName, implemented⟩

theorem user_die_admitted (w : W) (ty : EffTy) (payload : Nat) :
    Research.Slice6.H2Repaired.ExitOk w ty (.failure (Cause.die (.user payload))) :=
  Research.Slice6.H2Repaired.strongExit_of_clean w ty _ rfl
    (ordinary_die_shape ty (.user payload) (by intro h; cases h) (by intro h; cases h))

theorem user_current_code_admitted (root : Research.Slice6.H2Repaired.ProgramSource) (w : W) (ty : EffTy) (payload : Nat) :
    Research.Slice6.H2Repaired.TypedProg root w ty (.pure (.failure (Cause.die (.user payload)))) :=
  Research.Slice6.H2Repaired.TypedProg.pure (user_die_admitted w ty payload)

theorem missingService_admitted_at_any_type (w : W) (ty : EffTy) :
    Research.Slice6.H2Repaired.ExitOk w ty (.failure (Cause.die .missingService)) :=
  Research.Slice6.H2Repaired.strongExit_of_clean w ty _ rfl
    (ordinary_die_shape ty .missingService (by intro h; cases h) (by intro h; cases h))

theorem missingService_empty_admitted (w : W) :
    Research.Slice6.H2Repaired.ExitOk w (EffTy.pure .unit) (.failure (Cause.die .missingService)) :=
  missingService_admitted_at_any_type w _

theorem missingService_nonempty_admitted (w : W) :
    Research.Slice6.H2Repaired.ExitOk w ⟨.unit, .never, Env.Requirement.single nativeScopeKey⟩
      (.failure (Cause.die .missingService)) := missingService_admitted_at_any_type w _

theorem missingService_current_code_admitted (root : Research.Slice6.H2Repaired.ProgramSource) (w : W) (ty : EffTy) :
    Research.Slice6.H2Repaired.TypedProg root w ty (.pure (.failure (Cause.die .missingService))) :=
  Research.Slice6.H2Repaired.TypedProg.pure (missingService_admitted_at_any_type w ty)

#print axioms base_badName_still_fits
#print axioms clean_still_allows_badName
#print axioms badName_refused
#print axioms notImplemented_refused
#print axioms bad_current_code_refused
#print axioms notImplemented_current_code_refused
#print axioms ordinary_die_shape
#print axioms user_die_admitted
#print axioms user_current_code_admitted
#print axioms missingService_admitted_at_any_type
#print axioms missingService_empty_admitted
#print axioms missingService_nonempty_admitted
#print axioms missingService_current_code_admitted
end Test.Program.H2PartOne

namespace Test.Program.H2LookupDiagnostic
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Program.Typed
abbrev W := Effect4.Program.Typed.World

def natKey : ServiceKey := ⟨⟨4⟩, ⟨4⟩⟩
def readService : NativeEff := .service natKey

theorem unit_is_not_context : Val.context? .unit = none := rfl

theorem missing_context_returns_badName :
    serviceLookupR natKey .unit = .pure (.failure (Cause.die .badName)) := rfl

theorem old_service_premise_vacuous (w : W) :
    ∀ ctx, Val.context? .unit = some ctx → ServicesFit w ctx.services := by
  intro ctx lookup
  rw [unit_is_not_context] at lookup
  cases lookup

/-- The exact old lookup_typed signature is false after the requested shared-exit strengthening.
This is a test-helper contract diagnostic, not a ninth production proof repair. -/
theorem old_lookup_statement_false (w : W) : ¬ (
    ∀ (ty : EffTy), ty.answer = .nat → ∀ v : Val,
      (∀ ctx, Val.context? v = some ctx → ServicesFit w ctx.services) →
      Research.Slice6.H2Repaired.TypedProg readService w ty (serviceLookupR natKey v)) := by
  intro claimed
  have typed := claimed (EffTy.pure .nat) rfl .unit (old_service_premise_vacuous w)
  rw [missing_context_returns_badName] at typed
  exact Test.Program.H2PartOne.bad_current_code_refused readService w _ typed

/-- Proposed test-only amendment: demand that the input actually decodes as a context.
Do not replace the existing helper without reporting its changed premise. -/
theorem proposed_lookup_typed (w : W) (ty : EffTy) (answer : ty.answer = .nat) (v : Val)
    (isContext : ∃ ctx, Val.context? v = some ctx)
    (typed : ∀ ctx, Val.context? v = some ctx → ServicesFit w ctx.services)
    (keyType : nativeServiceTy natKey = some .nat) :
    Research.Slice6.H2Repaired.TypedProg readService w ty (serviceLookupR natKey v) := by
  obtain ⟨ctx, hctx⟩ := isContext
  unfold serviceLookupR
  rw [hctx]
  split
  · rename_i value found
    have hfit := flatFits_fits (typed ctx hctx natKey value .nat found keyType)
    apply Research.Slice6.H2Repaired.TypedProg.pure
    apply Research.Slice6.H2Repaired.strongExit_success
    rw [answer]
    exact hfit
  · exact Research.Slice6.H2Repaired.TypedProg.pure (Test.Program.H2PartOne.missingService_admitted_at_any_type w ty)

#print axioms unit_is_not_context
#print axioms missing_context_returns_badName
#print axioms old_service_premise_vacuous
#print axioms old_lookup_statement_false
#print axioms proposed_lookup_typed
end Test.Program.H2LookupDiagnostic
