import Effect4.Laws.Program.Typed.Assembly

/-! Research-only concatenation. Definitions, signatures and proof bodies are copied from the
named candidate. Imports and post-namespace proofgraph commands are omitted; see the map.
This checks copied declarations, not production module integration or obligation ceilings. -/

open Effect4.Program.Typed

namespace Research.Slice6.H2H1Baseline
abbrev World := Effect4.Program.Typed.World
end Research.Slice6.H2H1Baseline

/-! Source block: Admission.lean (Baseline). -/


/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts, using the value membership judgments from `Typed/Membership.lean`; the clean-exit
lemmas type interrupt-only and defect-only failures at every effect type. Control admission (FR-09) is an
arm of the one program judgment `TypedProg` in `Typed/Residual.lean` (ruling 2026-09-23).
-/

set_option autoImplicit false
namespace Research.Slice6.H2H1Baseline

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

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
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : FitsExit w ty ex) :
      BodyTyped src w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTyped src w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTyped src w p ty) :
      BodyTyped src w (.layerBuild p m scope) ty

/-- Membership at the answer column gives membership of the successful exit. -/
theorem strongExit_success (w : World) (ty : EffTy) (v : Val) (h : Fits w v ty.answer) :
    FitsExit w ty (.success v) := h

/-- A clean failure fits every effect type at every world: the error column constrains
`Fail` reasons only. -/
theorem strongExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
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

/-- At a `never` error column a fitting failure is clean: no value has type `never`. -/
theorem cleanExit_of_never (w : World) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
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

end Research.Slice6.H2H1Baseline

/-! Source block: Residual.lean (Baseline). -/


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
namespace Research.Slice6.H2H1Baseline

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
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ FitsExit w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ Fits w' ans ty.answer
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
  | pure {w : World} {ty : EffTy} {ex : ExitV} (exit : FitsExit w ty ex) :
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
      (skip : ∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → kind.hasExitArm ex = false →
        FitsExit w' ty ex) :
      TypedProg root w ty (.vis (.inr (.guard_ kind)) k)
  | unguard {w : World} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex) : TypedProg root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer {w : World} {ty : EffTy} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex) : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scopeExit {w : World} {ty : EffTy} {prev : Ctx} {sc : Nat} {ex : ExitV} {k : ExitV → RProgram}
      (payload : FitsExit w ty ex)
      (next : ∀ w', w.leHost w' → ∀ ans, TypedProg root w' ty (k ans)) :
      TypedProg root w ty (.vis (.inr (.scopeExit prev sc ex)) k)

namespace TypedProg

theorem pure_inv {root : ProgramSource} {w : World} {ty : EffTy} {ex : ExitV}
    (h : TypedProg root w ty (.pure ex)) : FitsExit w ty ex := by
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
      (∀ w', w.leHost w' → ∀ ex, FitsExit w' mid ex → kind.hasExitArm ex = false →
        FitsExit w' ty ex) := by
  cases h with
  | fiber notGuard _ _ _ _ _ _ => exact absurd rfl (notGuard kind)
  | guard mid body run skip => exact ⟨mid, body, run, skip⟩

end TypedProg

/-- FR-09's marker payload inversion: a typed `unguard` carries an exit at the current type. -/
theorem unguard_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.unguard ex)) k)) :
    FitsExit w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k)) :
    FitsExit w ty ex := by
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
    | done {tout : EffTy} (result : Val) (typed : FitsExit w tout (.success result)) :
        IteratorAnswer root w tout (.done result)
    | halt {tout : EffTy} (cause : CauseV) (typed : FitsExit w tout (.failure cause)) :
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
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, FitsExit w tin (.failure cause) →
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
    FitsExit w (EffTy.pure .bool) (.success v) := hv

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
  exact TypedProg.pure ⟨cert, hid, Ty.sub_refl _, Ty.sub_refl _⟩

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
    ProofGraph.Obligation (TypedProg root w ty (.vis (.inr (.unguard ex)) k) → FitsExit w ty ex) := ⟨⟩

theorem finishFinalizer_payload_inv (root : ProgramSource) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k) → FitsExit w ty ex) := ⟨⟩

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
    w.leHost w' → FitsExit w ty ex → FitsExit w' ty ex :=
  fun ordered h => fitsExit_mono ordered h

namespace M3bWorld

theorem strongValue_mono (w w' : World) (ty : Ty) (v : Val) :
    ProofGraph.Obligation (w.leHost w' → Fits w v ty → Fits w' v ty) := ⟨⟩

theorem strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV) :
    ProofGraph.Obligation (w.leHost w' → FitsExit w ty ex → FitsExit w' ty ex) := ⟨⟩

theorem typedProg_mono (root : ProgramSource) (w w' : World) (ty : EffTy) (p : RProgram) :
    ProofGraph.Obligation (w.leHost w' → TypedProg root w ty p → TypedProg root w' ty p) := ⟨⟩

end M3bWorld

end Research.Slice6.H2H1Baseline

/-! Source block: Stack.lean (Baseline). -/


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
namespace Research.Slice6.H2H1Baseline
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects Contracts

/-- Exactly the facts `popR`'s three named-hook arms need about an interpreter. -/
structure HookLaws (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols) : Prop where
  asyncFinalizer : ∀ w tin tout name, hooks.asyncFinalizer w tin tout name →
    tin = tout ∧ ∀ cause, FitsExit w tin (.failure cause) → cause.hasInterrupts = true →
      TypedProg root w tout (interp.cancelThenFail name cause)
  iterator : ∀ w tin tout name, hooks.iterator w tin tout name →
    tin.error = tout.error ∧ ∀ v, Fits w v tin.answer →
      match (interp.iterNext name v).2 with
      | .done result => FitsExit w tout (.success result)
      | .halt cause => FitsExit w tout (.failure cause)
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
  | (frame, none) => SavedOk (TypedProg root) FitsExit hooks w tout frame
  | (_, some ex) => FitsExit w tout ex

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

/-- A failure depends only on the error column. -/
theorem strongExit_failure_of_error {w : World} {tin tout : EffTy} {c : CauseV}
    (herr : tin.error = tout.error) (h : FitsExit w tin (.failure c)) : FitsExit w tout (.failure c) := by
  rw [fitsExit_failure_iff] at h ⊢
  rw [← herr]
  exact h

theorem walk_saved {root : ProgramSource} {hooks : FrameProtocols} {w : World} {tout : EffTy}
    {x : RSaved} (tin : EffTy) (code : TypedProg root w tin x.current)
    (stack : StackAccepts (TypedProg root) FitsExit hooks w tin tout x.stack)
    (hp : InterruptProvenance x) : WalkTyped root hooks w tout (x, none) :=
  ⟨tin, code, stack, hp⟩

theorem walk_done {root : ProgramSource} {hooks : FrameProtocols} {w : World} {tout : EffTy}
    {x : RSaved} {ex : ExitV} (h : FitsExit w tout ex) : WalkTyped root hooks w tout (x, some ex) :=
  h

/-! ## The walk -/

theorem popR_typed (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (laws : HookLaws root interp hooks) (w : World) :
    ∀ (stack : List ScopeFrame) (tin tout : EffTy) (ex : ExitV) (frame : RSaved),
      StackAccepts (TypedProg root) FitsExit hooks w tin tout stack →
      FitsExit w tin ex → InterruptProvenance frame →
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
            exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ c (recorded_clean hp rfl)))
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
            exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ c (recorded_clean hp rfl)))
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
        strongExit_of_clean w ty _ (sanitize_clean_exit hp cause h)
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
          · exact ih _ _ _ _ tail (preempt _ c _ rfl) (hp' _ _ _)
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
          · exact ih _ _ _ _ tail (preempt _ c _ rfl) (hp' _ _ _)
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
            · exact ih _ _ _ _ tail (preempt _ c _ rfl) (hp' _ _ _)
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
        · exact walk_saved _ (TypedProg.pure (strongExit_of_clean w _ _ (pendingCause_clean ⟨hp.recorded, hp.deferred⟩)))
            tail ⟨hp.recorded, hp.deferred⟩
    | iter name protocol =>
      obtain ⟨errors, step⟩ := laws.iterator w _ _ name protocol
      obtain ⟨current, stack, i, ic, deferred⟩ := frame
      cases ex with
      | failure c =>
        simp only [popR]
        exact ih _ _ _ _ tail (strongExit_failure_of_error errors hex) ⟨hp.recorded, hp.deferred⟩
      | success v =>
        have h := step v hex
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
        have h := step v hex
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
    (hstack : StackAccepts (TypedProg root) FitsExit (frameProtocols root) w tin tout stack)
    (hex : FitsExit w tin ex) (hp : InterruptProvenance frame) :
    WalkTyped root (frameProtocols root) w tout (popR (interpR root.program) ex stack frame) :=
  popR_typed root _ _ (hookLaws_interpR root) w stack tin tout ex frame hstack hex hp

/-! ## Saving and delivering -/

/-- Installing an operation's code below its answer adapter keeps the saved state typed: the
adapter and the old stack meet at `middle`, the code has the operation's own type `tin`. -/
theorem saveAnswerR_typed (root : ProgramSource) (hooks : FrameProtocols) (w : World)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (hcode : TypedProg root w tin code)
    (hnext : ∀ ex, FitsExit w tin ex → TypedProg root w middle (next ex))
    (hstack : StackAccepts (TypedProg root) FitsExit hooks w middle final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    SavedOk (TypedProg root) FitsExit hooks w final (answerR (saveAnswerR f next) code).frame :=
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
    (hstack : StackAccepts (TypedProg root) FitsExit hooks w tin final f.frame.stack)
    (hp : InterruptProvenance f.frame) :
    (letI := termEvaluatorFor root.program
     driveStep interp m (.resume f.id token code) rest) =
      ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
    SavedOk (TypedProg root) FitsExit hooks w final (resumed f token code).frame := by
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
      StackAccepts (TypedProg root) FitsExit hooks w tin tout stack →
      FitsExit w tin ex → InterruptProvenance frame →
      WalkTyped root hooks w tout (popR interp ex stack frame)) := ⟨⟩

theorem saveAnswerR_typed (root : ProgramSource) (hooks : FrameProtocols) (w : World)
    (tin middle final : EffTy) (f : RFiber) (next : ExitV → RProgram) (code : RProgram)
    (_hcode : TypedProg root w tin code)
    (_hnext : ∀ ex, FitsExit w tin ex → TypedProg root w middle (next ex))
    (_hstack : StackAccepts (TypedProg root) FitsExit hooks w middle final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    (SavedOk (TypedProg root) FitsExit hooks w final (answerR (saveAnswerR f next) code).frame) := ⟨⟩

theorem deliver_active (root : ProgramSource) (interp : RInterp) (hooks : FrameProtocols)
    (w : World) (tin final : EffTy) (m : RState) (f : RFiber) (token : Nat) (code : RProgram)
    (rest : List RCmd) (_found : m.fiber? f.id = some f) (_parked : f.parked = .withGuard token)
    (_declared : w.Θ f.id token = some tin) (_typed : ResumeOk (TypedProg root) w f.id token code)
    (_hstack : StackAccepts (TypedProg root) FitsExit hooks w tin final f.frame.stack)
    (_hp : InterruptProvenance f.frame) : ProofGraph.Obligation
    ((letI := termEvaluatorFor root.program
      driveStep interp m (.resume f.id token code) rest) =
        ((m.update (resumed f token code)).emit [.resumedWith f.id token code], .evaluate f.id :: rest) ∧
      SavedOk (TypedProg root) FitsExit hooks w final (resumed f token code).frame) := ⟨⟩

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

end Research.Slice6.H2H1Baseline

/-! Source block: Scheduler.lean (Baseline). -/


/-!
H1 scheduler statements, without a command-preservation proof. The predicates inspect the
actual tables and finite buffered payloads. The exact reference code-site traversal is OPEN
(H1-RCODE-SITES); this file supplies neither a head-only approximation nor a predicate over
all possible continuation answers. The direct race-registration authority is settled.
-/
set_option autoImplicit false
namespace Research.Slice6.H2H1Baseline
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote

abbrev RPending := Pending EffName Val Err Defect FiberId Ann
abbrev RRace := Race EffName EffThunk Val Err Defect FiberId Ann RProgram

/-- The checker's two result types, not the source fiber type in both modes. -/
def observerDeliveredType (mode : Supervision.ObserverMode) (sourceTy : EffTy) : EffTy :=
  match mode with
  | .joinEffect => sourceTy
  | .awaitValue => EffTy.pure (.exitOf sourceTy.answer sourceTy.error)

def observerDeliveredExit (mode : Supervision.ObserverMode) (exit : ExitV) : ExitV :=
  match mode with
  | .joinEffect => exit
  | .awaitValue => .success (reifyExitVal exit)

/-- Reification is exactly the value at Exit<A,E> in FitsExit's definition. -/
theorem reifyExitVal_fits (w : World) (ty : EffTy) (exit : ExitV)
    (typed : FitsExit w ty exit) :
    Fits w (reifyExitVal exit) (.exitOf ty.answer ty.error) := typed

theorem observerDeliveredExit_fits (w : World) (ty : EffTy) (exit : ExitV)
    (mode : Supervision.ObserverMode) (typed : FitsExit w ty exit) :
    FitsExit w (observerDeliveredType mode ty) (observerDeliveredExit mode exit) := by
  cases mode with
  | joinEffect => exact typed
  | awaitValue => exact reifyExitVal_fits w ty exit typed

/-- The actual interpreter hook constructs the result just typed above. -/
theorem observer_exitValue_typed (root : ProgramSource) (w : World) (ty : EffTy)
    (exit : ExitV) (mode : Supervision.ObserverMode) (typed : FitsExit w ty exit) :
    TypedProg root w (observerDeliveredType mode ty)
      ((interpR root.program).exitValue exit mode) := by
  cases mode with
  | joinEffect => exact TypedProg.pure typed
  | awaitValue => exact TypedProg.pure (reifyExitVal_fits w ty exit typed)

/-- Only the two exit columns are aggregated; requirement transport is H2's separate debt. -/
def FiberColumnsBelow (w : World) (id : FiberId) (answer error : Ty) : Prop :=
  ∃ ty, w.Γ id = some ty ∧ ty.answer.sub answer = true ∧ ty.error.sub error = true

/-- A race's one result declaration owns every buffered value and each unlaunched program.
Existing live fiber declarations are constrained; missing fibers are not invented. -/
structure RacePayload (root : ProgramSource) (w : World) (race : RRace)
    (resultTy : EffTy) : Prop where
  token : w.Θ race.host race.token = some resultTy
  failures : FitsCause w resultTy.error ⟨race.state.failures⟩
  winner : ∀ pair ∈ race.state.winner, Fits w pair.2 resultTy.answer
  accepted : ∀ exit ∈ race.state.accepted, FitsExit w resultTy exit
  cleanup : ∀ wait ∈ race.state.cleanup, FitsExit w resultTy wait.result
  live : ∀ id ∈ race.state.live, ∀ childTy, w.Γ id = some childTy →
    childTy.answer.sub resultTy.answer = true ∧ childTy.error.sub resultTy.error = true
  programs : ∀ code ∈ race.programs, ∃ childTy, TypedProg root w childTy code ∧
    childTy.answer.sub resultTy.answer = true ∧ childTy.error.sub resultTy.error = true

/-- The finite pending record reached by a countdown observer. Joins also use Pending with
void metadata, so this predicate is attached only through an actual countdown observer. -/
structure CountdownPayload (w : World) (m : RState) (waiter : FiberId)
    (pending : RPending) (answer error : Ty) (tokenTy : EffTy) : Prop where
  token : w.Θ waiter pending.token = some tokenTy
  collected : ∀ exit ∈ pending.collected,
    FitsExit w ⟨answer, error, Env.Requirement.empty⟩ exit
  targets : ∀ id ∈ pending.waitingOn.toList ++ pending.remaining,
    ∀ fiber, m.fiber? id = some fiber → FiberColumnsBelow w fiber.id answer error
  resume : match pending.resumeWith with
    | .exitsValue => tokenTy = EffTy.pure (.list (.exitOf answer error))
    | .void => tokenTy = EffTy.pure .unit
    | .continueWith (.restore saved) => FitsExit w tokenTy saved
    | .continueWith _ => FitsExit w tokenTy outsideExit

/-- Follow exactly fireObserver's waiter and pending lookups. Missing lookups are inert.
The supplied condition shares the aggregate witnesses with all buffered values. -/
def CountdownAt (w : World) (m : RState) (waiter : FiberId) (token : Nat)
    (incoming : Ty → Ty → Prop) : Prop :=
  match m.fiber? waiter with
  | none => True
  | some fiber =>
    match fiber.pending.find? (fun pending => pending.token = token) with
    | none => True
    | some pending => ∃ answer error tokenTy,
        CountdownPayload w m waiter pending answer error tokenTy ∧ incoming answer error

/-- A stored observer's source declaration is connected to the destination token. -/
def StoredObserverOk (root : ProgramSource) (w : World) (m : RState)
    (source : FiberId) : Observer → Prop
  | .resumeAwait waiter token mode => ∃ sourceTy,
      w.Γ source = some sourceTy ∧ w.Θ waiter token = some (observerDeliveredType mode sourceTy)
  | .countdown waiter token => CountdownAt w m waiter token (FiberColumnsBelow w source)
  | .raceCallback raceId =>
    match m.race? raceId with
    | none => True
    | some race => ∃ resultTy, RacePayload root w race resultTy ∧
        (source ∈ race.state.live → FiberColumnsBelow w source resultTy.answer resultTy.error)
  | .untrackChild _ | .dropScopeFinalizer _ _ | .callback _ => True

/-- A queued observer must type what it can deliver or buffer, including a race callback
while registration is still active. The three no-payload variants keep their machine guards. -/
def ObserverCommandOk (root : ProgramSource) (w : World) (m : RState)
    (source : FiberId) (exit : ExitV) : Observer → Prop
  | .resumeAwait waiter token mode => ∃ sourceTy,
      w.Γ source = some sourceTy ∧
      w.Θ waiter token = some (observerDeliveredType mode sourceTy) ∧ FitsExit w sourceTy exit
  | .countdown waiter token => CountdownAt w m waiter token
      (fun answer error => FitsExit w ⟨answer, error, Env.Requirement.empty⟩ exit)
  | .raceCallback raceId =>
    match m.race? raceId with
    | none => True
    | some race => ∃ resultTy, RacePayload root w race resultTy ∧
        (source ∈ race.state.live → FitsExit w resultTy exit)
  | .untrackChild _ | .dropScopeFinalizer _ _ | .callback _ => True

/-- Enrollment may fire an already-exited entrant immediately, so queueing only a typed
observe command is insufficient. This clause uses the same declared result as RacePayload. -/
def EnrollRaceOk (root : ProgramSource) (w : World) (m : RState)
    (raceId : Nat) (child : FiberId) : Prop :=
  match m.race? raceId, m.fiber? child with
  | some race, some fiber => ∃ resultTy, RacePayload root w race resultTy ∧
      FiberColumnsBelow w fiber.id resultTy.answer resultTy.error
  | _, _ => True

structure ObserverState (root : ProgramSource) (w : World) (m : RState) : Prop where
  pendingOwner : ∀ fiber ∈ m.fibers, ∀ pending ∈ fiber.pending,
    (w.Θ fiber.id pending.token).isSome = true
  observers : ∀ fiber ∈ m.fibers, ∀ observer ∈ fiber.observers,
    StoredObserverOk root w m fiber.id observer

/-- Settled guard state clauses on the shared machine. No reference code-site condition
is claimed here: frameCodes/internalCodes remain H1-RCODE-SITES. -/
structure SchedulerState (m : RState) : Prop where
  fiberIds : (m.fibers.map RunFiber.id).Nodup
  fibersBelow : ∀ fiber ∈ m.fibers, fiber.id.value < m.nextId
  raceIds : (m.races.map Race.id).Nodup
  racesBelow : ∀ race ∈ m.races, race.id < m.nextRace
  raceHosts : ∀ race ∈ m.races, ∃ fiber, m.fiber? race.host = some fiber
  keysBelow : Guard.InternalKeysBelow m
  requestsBelow : ∀ fiber token request, requestOfR m fiber token = some request → token < m.nextToken
  requestsOwned : ∀ fiber token request, requestOfR m fiber token = some request →
    (fiber, token) ∉ Guard.internalKeys m
  pendingShape : ∀ fiber ∈ m.fibers, Guard.PendingShape fiber
  parkedIdle : ∀ fiber ∈ m.fibers, fiber.parked ≠ .notParked → fiber.running = false
  parkedBelow : ∀ fiber ∈ m.fibers, ∀ token,
    fiber.parked = .withGuard token → token < m.nextToken
  exited : ∀ fiber ∈ m.fibers, fiber.exit.isSome = true →
    fiber.parked = .notParked ∧ fiber.running = false
  deferredCause : ∀ fiber ∈ m.fibers, fiber.frame.deferredInterrupt = true →
    fiber.frame.interruptedCause.isSome = true

/-- The reference evaluator consumes this operation directly; interpR.parkOf is none. -/
def raceRegistrationR : RProgram → Option Nat
  | .vis (.inr (.raceRegister raceId)) _ => some raceId
  | _ => none

/-- A concrete reply must meet the actual saved stack, independently of whatever type
certified the current administrative operation. This names a local delivery boundary. -/
def StackReply (root : ProgramSource) (w : World) (fiber : RFiber) (replyTy : EffTy) : Prop :=
  ∃ final, w.Γ fiber.id = some final ∧
    Contracts.StackAccepts (TypedProg root) FitsExit (frameProtocols root) w replyTy final
      fiber.frame.stack ∧ Contracts.InterruptProvenance fiber.frame

/-- The direct registration marker owns a real race on this fiber, and the race token's
result meets this host's saved continuation. This finite current-code clause covers both
immediate buffered settlement and parking; it is not the open recursive code-site scan. -/
def RegistrationState (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ fiber ∈ m.fibers, ∀ raceId, raceRegistrationR fiber.frame.current = some raceId →
    ∃ race resultTy, m.race? raceId = some race ∧ race.host = fiber.id ∧
      w.Θ race.host race.token = some resultTy ∧ StackReply root w fiber resultTy

/-- A loaded code with no direct registration marker needs no race/token correlation yet. -/
theorem registrationState_load (root : ProgramSource) (w : World) (fuel compileFuel : Nat)
    (noMarker : raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = none) :
    RegistrationState root w (loadR root.program fuel compileFuel) := by
  intro fiber hf raceId marker
  change fiber ∈ [_] at hf
  rw [List.mem_singleton] at hf
  subst fiber
  change raceRegistrationR (denoteR root.program root.program (rootPoint compileFuel)) = some raceId at marker
  rw [noMarker] at marker
  cases marker

/-- The existing await protocol certifies a finite list of declared target columns.
This is a command-admission requirement; the runtime's missing-target behavior is unchanged. -/
def FiberListColumns (w : World) (targets : List FiberId) (answer error : Ty) : Prop :=
  ∀ id ∈ targets, FiberColumnsBelow w id answer error

/-- asVoid(awaitCode kind) has a unit answer. joinEffect can retain the target's typed
failures; awaitValue and awaitAll return encoded exits as successful values. -/
def AfterInterruptReply (w : World) : ParkKind → EffTy → Prop
  | .join target .joinEffect, replyTy => ∃ sourceTy, w.Γ target = some sourceTy ∧
      replyTy = ⟨.unit, sourceTy.error, Env.Requirement.empty⟩
  | .join target .awaitValue, replyTy => ∃ sourceTy, w.Γ target = some sourceTy ∧
      replyTy = EffTy.pure .unit
  | .awaitAll targets, replyTy => ∃ answer error, FiberListColumns w targets answer error ∧
      replyTy = EffTy.pure .unit
  | .race _, _ => False

/-- Commands with no carried code can still install a concrete reply or an iterator frame.
Their finite targets and result columns must meet the actual host stack. This does not ask
that an evaluated transition be typed, and does not quantify over unknown code continuations. -/
def CommandDeliveryOk (root : ProgramSource) (w : World) (m : RState) : RCmd → Prop
  | .afterInterrupt host _ kind => ∀ fiber, m.fiber? host = some fiber →
      ∃ replyTy, AfterInterruptReply w kind replyTy ∧ StackReply root w fiber replyTy
  | .raceCancel _ host _ remaining visited => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w (visited ++ remaining) answer error ∧
        StackReply root w fiber (EffTy.pure .unit)
  | .closeParAwait host _ targets => ∀ fiber, m.fiber? host = some fiber →
      ∃ answer error, FiberListColumns w targets answer error ∧
        (frameProtocols root).iterator w
          ⟨.list (.exitOf answer error), error, Env.Requirement.empty⟩
          ⟨.unit, error, Env.Requirement.empty⟩ (interpR root.program).closeDoneName ∧
        StackReply root w fiber ⟨.unit, error, Env.Requirement.empty⟩
  | _ => True

def CommandAuthorityR (m : RState) : RCmd → Prop
  | .loop fiber _ | .deliver fiber _ | .finish fiber _ => Guard.ActiveAt m fiber
  | .afterInterrupt fiber _ _ | .closeParAwait fiber _ _ | .raceCancel _ fiber _ _ _ =>
      Guard.ActiveAt m fiber
  | .registrationDone raceId _ =>
      ∃ race fiber, m.race? raceId = some race ∧ m.fiber? race.host = some fiber ∧
        fiber.running = true ∧ fiber.parked = .notParked ∧
        raceRegistrationR fiber.frame.current = some raceId
  | .launch raceId | .enrollRace raceId _ =>
      ∃ race, m.race? raceId = some race ∧ Guard.ActiveAt m race.host
  | .exitDone fiber => ∃ found, m.fiber? fiber = some found ∧ found.exit.isSome = true
  | _ => True

structure ReservedKeysR (m : RState) (keys : List Guard.GuardKey) : Prop where
  below : ∀ key ∈ keys, key.2 < m.nextToken
  disjoint : ∀ fiber token request, requestOfR m fiber token = some request →
    (fiber, token) ∉ keys

def QueueFresh (m : RState) (commands : List RCmd) : Prop :=
  ∀ key ∈ commands.flatMap Guard.commandKeys, key.2 < m.nextToken

/-- The result obligation on resumeAwait is about the actual delivered program. -/
theorem observerCommand_resume_typed (root : ProgramSource) (w : World) (m : RState)
    (source waiter : FiberId) (token : Nat) (mode : Supervision.ObserverMode) (exit : ExitV)
    (typed : ObserverCommandOk root w m source exit (.resumeAwait waiter token mode)) :
    Contracts.ResumeOk (TypedProg root) w waiter token
      ((interpR root.program).exitValue exit mode) := by
  obtain ⟨sourceTy, _, declared, exitTyped⟩ := typed
  intro tokenTy htoken
  rw [declared] at htoken
  cases htoken
  exact observer_exitValue_typed root w sourceTy exit mode exitTyped

/-- A loaded machine has no active external request, regardless of the loaded code. -/
theorem requestOfR_load_none (program : NativeEff) (fuel compileFuel : Nat)
    (fiber : FiberId) (token : Nat) :
    requestOfR (loadR program fuel compileFuel) fiber token = none := by
  unfold requestOfR
  cases hf : (loadR program fuel compileFuel).fiber? fiber with
  | none => rfl
  | some found =>
    have member := List.mem_of_find?_eq_some hf
    change found ∈ [_] at member
    rw [List.mem_singleton] at member
    subst found
    rfl

theorem schedulerState_load (program : NativeEff) (fuel compileFuel : Nat) :
    SchedulerState (loadR program fuel compileFuel) := by
  constructor
  · exact List.nodup_cons.mpr ⟨List.not_mem_nil, List.nodup_nil⟩
  · intro fiber hf
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    exact Nat.zero_lt_succ 0
  · exact List.nodup_nil
  · intro race hr; cases hr
  · intro race hr; cases hr
  · intro key hk; cases hk
  · intro fiber token request hr
    rw [requestOfR_load_none] at hr
    cases hr
  · intro fiber token request hr
    rw [requestOfR_load_none] at hr
    cases hr
  · intro fiber hf
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    rfl
  · intro fiber hf hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    exact False.elim (hp rfl)
  · intro fiber hf token hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hp
  · intro fiber hf hx
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hx
  · intro fiber hf hd
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hd

theorem observerState_load (root : ProgramSource) (w : World) (fuel compileFuel : Nat) :
    ObserverState root w (loadR root.program fuel compileFuel) := by
  constructor
  · intro fiber hf pending hp
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases hp
  · intro fiber hf observer ho
    change fiber ∈ [_] at hf
    rw [List.mem_singleton] at hf
    subst fiber
    cases ho

end Research.Slice6.H2H1Baseline

/-! Source block: Assembly.lean (Baseline). -/


/-!
# Laws.Program.Typed.Assembly — the typed state of the reference machine

Slice 5's assembly (§3.5 of the brief, as amended): the generated predicate bundle `Preds`
instantiated with the strong judgments (`preds`), the typed state (`TypedState`: validity, the
generated whole-state predicate, and the active-delivery correlation), reachability
(`RReachable`), admitted host answers (`AnswerOk`), and the declared obligations the milestones
after slice 5 prove: initialization (`typedState_load`, M5) and the transition ledger, one
preservation obligation per command constructor (M6). `capture_lookup` is proved here.

H1 adds the settled scheduler guards and observer-to-token payload connections. `PendingOk`
still receives no enclosing fiber, so `ObserverState.pendingOwner` supplies that correlation.
`RaceOk` owns every buffered race payload and finite unlaunched program. The reference code-site
scan remains explicitly OPEN (H1-RCODE-SITES); no continuation-wide approximation is claimed.
All eighteen command-preservation declarations remain obligations.
-/

set_option autoImplicit false
namespace Research.Slice6.H2H1Baseline
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
  | .ofExit ex => FitsExit w ty ex
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
    Contracts.SavedOk (TypedProg root) FitsExit (frameProtocols root) w ty x
  PendingOk w _ ps := ∀ p ∈ ps, ∃ id, (w.Θ id p.token).isSome = true
  exit w e ex := ∀ ty, expectOf w e = some ty → FitsExit w ty ex
  ResumeOk w _ target token code := Contracts.ResumeOk (TypedProg root) w target token code
  ServiceOk w _ ctx := ServicesFit w ctx.services
  RaceOk w _ races := ∀ r ∈ races, ∃ resultTy, RacePayload root w r resultTy
  PromiseTable w s := ∀ o ∈ s.deferreds.due, ∀ ty, w.Θ o.waiter o.token = some ty →
    CompletionStrong w ty o.code
  HeapCell w key v := ∀ ty, w.Ρ key = some ty → Fits w v ty
  PromiseCell w key cell := ∀ a e, w.«Π» key = some (a, e) →
    ∀ c, cell.completion = some c → CompletionStrong w ⟨a, e, Env.Requirement.empty⟩ c
  CaptureOk w _ c := CaptureTyped root w c

/-- A terminal fiber delivers the exit carried by its queued finish, or the exit already
published on that fiber. This finite boundary does not assert that an arbitrary queue is inert. -/
def TerminalFiber (m : RState) (commands : List RCmd) (id : FiberId) : Prop :=
  (∃ exit, .finish id exit ∈ commands) ∨
    ∃ fiber ∈ m.fibers, fiber.id = id ∧ fiber.exit.isSome = true

/-- The generated saved position retains its identity while its current code becomes inert. -/
def TerminalPosition (m : RState) (commands : List RCmd) : Expect → Prop
  | .root => TerminalFiber m commands Api.root
  | .fiber id => TerminalFiber m commands id
  | .hook _ => False

/-- Current code is inert after a machine halt, while its finish is queued, or after its exit
has been published. Halting does not require an empty queue: some native halt paths retain it.
The executable command loop checks halt before dispatch; raw `driveStep` requires its explicit
not-halted premise in `StepPreserves`. -/
def CodeInert (m : RState) (commands : List RCmd) (position : Expect) : Prop :=
  m.stuck.isSome = true ∨ TerminalPosition m commands position

/-- Only the current-code premise is conditional. The stack still composes to the declared
fiber type, and interrupt provenance is required even when current code is inert. -/
def SavedPosition (root : ProgramSource) (w : World) (m : RState) (commands : List RCmd)
    (position : Expect) (final : EffTy) (saved : RSaved) : Prop :=
  ∃ tin, (¬ CodeInert m commands position → TypedProg root w tin saved.current) ∧
    StackAccepts (TypedProg root) FitsExit (frameProtocols root) w tin final saved.stack ∧
    InterruptProvenance saved

/-- All generated data clauses are unchanged. Only saved current code is conditional on
`CodeInert`; queued exit typing is still the unchanged `preds.exit` in `RCmdOk`. -/
def statePreds (root : ProgramSource) (m : RState) (commands : List RCmd) : Preds World :=
  { preds root with
    SavedOk := fun w position saved => ∀ ty, expectOf w position = some ty →
      SavedPosition root w m commands position ty saved }

/-- A fully typed saved frame also satisfies the conditional current-code clause. -/
theorem savedPosition_of_saved (root : ProgramSource) (w : World) (m : RState)
    (commands : List RCmd) (position : Expect) (final : EffTy) (saved : RSaved)
    (typed : Contracts.SavedOk (TypedProg root) FitsExit (frameProtocols root) w final saved) :
    SavedPosition root w m commands position final saved := by
  obtain ⟨tin, code, stack, provenance⟩ := typed
  exact ⟨tin, fun _ => code, stack, provenance⟩

/-- The active park and saved stack agree on what the declared token delivers. -/
def ActiveDelivery (root : ProgramSource) (w : World) (m : RState) : Prop :=
  ∀ f ∈ m.fibers, ∀ token, f.parked = .withGuard token →
    ∃ tin final, w.Θ f.id token = some tin ∧ w.Γ f.id = some final ∧
      StackAccepts (TypedProg root) FitsExit (frameProtocols root) w tin final f.frame.stack ∧
      InterruptProvenance f.frame

/-- World validity, every generated typed position, active delivery, the settled native guard
conditions, and the exact observer/pending correlations. Internal key bounds live here so every
StepPreserves input/output carries them. Its explicit queue controls the saved current-code
clause; the empty queue remains the initialization and completed-run interface. Arbitrary queues
are still admitted by their own fact, including generated typing for every carried finish.
H1-RCODE-SITES is an explicit remaining condition, not an established invariant. -/
def TypedState (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (commands : List RCmd := []) : Prop :=
  WorldValid rootTy w m ∧ RStateOk (statePreds root m commands) w m ∧
    ActiveDelivery root w m ∧ SchedulerState m ∧ ObserverState root w m ∧ RegistrationState root w m

/-- PendingOk supplies a declaration; WorldValid bounds all declarations. -/
theorem pending_below (root : ProgramSource) (rootTy : EffTy) (w : World) (m : RState)
    (commands : List RCmd) (typed : TypedState root rootTy w m commands) (f : RFiber) (hf : f ∈ m.fibers)
    (p : Pending EffName Val Err Defect FiberId Ann) (hp : p ∈ f.pending) :
    p.token < m.nextToken := by
  obtain ⟨id, declared⟩ := (typed.2.1.c0 f hf).c1 p hp
  cases h : w.Θ id p.token with
  | none => rw [h] at declared; cases declared
  | some tokenTy => exact typed.1.tokenBound id p.token tokenTy h

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

/-- Every queued command's generated content judgment, scheduler authority and keys, plus
observer and enrollment payload correlation. H1-RCODE-SITES remains OPEN for resume code:
there is intentionally no field claiming an unimplemented recursive reference scan. The direct
forbidden afterInterrupt race form is recorded separately and exactly. -/
structure QueueOk (root : ProgramSource) (w : World) (m : RState)
    (commands : List RCmd) : Prop where
  payload : ∀ command ∈ commands, RCmdOk (preds root) w command
  authority : ∀ command ∈ commands, CommandAuthorityR m command
  delivery : ∀ command ∈ commands, CommandDeliveryOk root w m command
  owners : (commands.filterMap (Guard.commandOwner m)).Nodup
  registration : Guard.RegistrationQueue.RegistrationQueue commands
  keys : ReservedKeysR m (commands.flatMap Guard.commandKeys)
  observer : ∀ source exit observer, .observe source exit observer ∈ commands →
    ObserverCommandOk root w m source exit observer
  enroll : ∀ race child, .enrollRace race child ∈ commands → EnrollRaceOk root w m race child
  noRaceAfterInterrupt : ∀ host yielding race,
    .afterInterrupt host yielding (.race race) ∉ commands

theorem QueueOk.fresh {root : ProgramSource} {w : World} {m : RState} {commands : List RCmd}
    (queue : QueueOk root w m commands) : QueueFresh m commands := queue.keys.below

/-- One dispatched command keeps the typed state and queue typed at some later world.
The exact `m.stuck = none` dispatch premise is shared with `Machine.Lift.StepKeeps` and
`driveState`; it does not assert reachability or constrain the pending suffix. -/
def StepPreserves (root : ProgramSource) (rootTy : EffTy) (cmd : RCmd) : Prop :=
  ∀ w m rest, m.stuck = none → TypedState root rootTy w m (cmd :: rest) →
    QueueOk root w m (cmd :: rest) →
    let r := (letI := termEvaluatorFor root.program
              driveStep (interpR root.program) m cmd rest)
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' r.1 r.2 ∧ QueueOk root w' r.1 r.2

/-- The eighteen command facts, once proved, provide exactly the existing generic loop
premise. This adapter proves no individual command fact and requires no reachability premise. -/
theorem stepKeeps_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command) :
    letI := termEvaluatorFor root.program
    Machine.Lift.StepKeeps hostOrder (interpR root.program)
      (fun w m commands => TypedState root rootTy w m commands ∧ QueueOk root w m commands) := by
  letI := termEvaluatorFor root.program
  intro w m command rest running typed
  exact steps command w m rest running typed.1 typed.2

/-- Conditional assembly lift through the actual command loop, including its halt boundary.
All eighteen `StepPreserves` facts remain hypotheses, not discharged obligations. -/
theorem driveState_typed_of_stepPreserves (root : ProgramSource) (rootTy : EffTy)
    (steps : ∀ command, StepPreserves root rootTy command)
    (fuel : Nat) (w : World) (m : RState) (commands : List RCmd)
    (typed : TypedState root rootTy w m commands) (queue : QueueOk root w m commands) :
    letI := termEvaluatorFor root.program
    let result := driveState (interpR root.program) fuel m commands
    ∃ w', w.leHost w' ∧ TypedState root rootTy w' result.1 result.2 ∧
      QueueOk root w' result.1 result.2 := by
  letI := termEvaluatorFor root.program
  exact Machine.Lift.driveState_lift hostOrder (interpR root.program)
    (fun w m commands => TypedState root rootTy w m commands ∧ QueueOk root w m commands)
    (stepKeeps_of_stepPreserves root rootTy steps) fuel w m commands ⟨typed, queue⟩

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

M6 does not yet claim that a run never dies with `badName`, `notImplemented`, or
`missingService` when nothing is required. Row 107 and brief item H2 require that exclusion
in the exit judgment read by code, saved stacks, queued results and stored completions;
a check on finished fibers alone is insufficient (`E4-TYPED-CE-007`). Keep this disclaimer
until that repair lands, retaining any part that remains open. -/
theorem typedState_reachable (root : ProgramSource) (rootTy : EffTy) (fuel : Nat) (m : RState) :
    ProofGraph.Obligation (Api.typeOf root.program root.table = some rootTy → ClosedEff rootTy →
      RReachable root fuel m → ∃ w, TypedState root rootTy w m) := ⟨⟩

end M6Ledger

end Research.Slice6.H2H1Baseline

