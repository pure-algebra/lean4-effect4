import Effect4.Laws.Program.Typed.Admission
import Effect4.Laws.Program.Typed.Contracts
import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Auto.Obligations

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
namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-! ## The Store Protocol (31 SyncOp rows) -/

def StoreCert : SyncOp → Type
  | .refMake _ | .memoGet _ _ => Ty
  | .deferredMake | .memoBuild _ _ => Ty × Ty
  | _ => PUnit

/-- What each store row demands of its request (decisions row 136 for `refModify`,
`refModifySome` and the scope rows). -/
def storePre (root : ProgramSource) (w : World) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ Fits w initial cert
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ Fits w v ty
  | .refUpdate cell _ | .refGetAndUpdate cell _ | .refUpdateAndGet cell _
  | .refUpdateSome cell _ | .refGetAndUpdateSome cell _ | .refUpdateSomeAndGet cell _ =>
    ∃ ty, w.Ρ cell = some ty
  -- the native row's declared cell type (`Ref.Ref<number>`, `HandleFits`'s cell arm): the
  -- handler answers the cell's old value, which the `nat` post then describes
  | .refModify cell _ | .refModifySome cell _ => RefDeclared w cell .nat
  | .deferredMake => cert.1.closed = true ∧ cert.2.closed = true
  | .deferredIsDone key | .deferredPoll key | .deferredAwaitCleanup key _ _ => (w.«Π» key).isSome = true
  -- the completion fits the promise's declared columns (`CompletionStrong`'s two arms), so the
  -- completed cell stays typed; an ill-typed completion leaves no later world over the new store
  | .deferredCompleteWith key completion => ∃ a e, w.«Π» key = some (a, e) ∧
      match completion with
      | .ofExit ex => ExitOk w ⟨a, e, Env.Requirement.empty⟩ ex
      | .ofRefGet cell => ∃ t, w.Ρ cell = some t ∧ Ty.subN t a = true
  | .deferredInterruptWith key _ => (w.«Π» key).isSome = true
  | .clockNow | .sleepCancel _ _ => True
  | .scopeMake _ => True
  -- the named scope is live in the world's store, so the store never steps to a frontier
  -- (`syncOpStep` answering `none`, which the evaluator answers `unit`; row 139's liveness)
  | .scopeAdd scope _ | .scopeRemove scope _ | .scopeIsClosed scope | .scopeFork scope _ =>
    (w.state.scopes.entryAt scope).isSome = true
  | .memoFork _ | .memoComplete _ _ _ | .memoRelease _ _ => True
  -- the looked-up layer's own checked error type (decision row 90)
  | .memoGet layer _ => ∃ l lt, Node.at_ (.eff root.program) layer = some (.layer l) ∧
      Checker.checkLayer root.signature layer l = .ok lt ∧ lt.error = cert
  | .memoBuild _ _ => cert.1.closed = true ∧ cert.2.closed = true

/-- What each store row's answer satisfies: the store's actual answer (decisions row 136; the
handler's adequacy is `StoreImplements`, `Typed/Adequacy.lean`). -/
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
  | .deferredCompleteWith _ _ | .deferredInterruptWith _ _ => ∃ b, ans = Val.bool b
  | .deferredAwaitCleanup _ _ _ => ans = Val.unit
  | .clockNow => ∃ n, ans = Val.nat n
  | .sleepCancel _ _ => ans = Val.unit
  | .scopeMake _ => ∃ sc, ans = Val.scopeHandle sc
  -- an open scope registers and answers `unit`; a closed one answers its closing exit, at
  -- `Exit<unknown, unknown>` (DI-94's release type), for the caller to run the finalizer now
  | .scopeAdd _ _ => ans = Val.unit ∨
      ∃ ex, ans = reifyExitVal ex ∧ FitsExit w' ⟨.unknown, .unknown, Env.Requirement.empty⟩ ex
  | .scopeRemove _ _ => ans = Val.unit
  | .scopeIsClosed _ => ∃ b, ans = Val.bool b
  | .scopeFork _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoFork _ => ∃ id, ans = Val.memoMap id
  | .memoGet _ _ => ans = Val.unit ∨ ∃ cell owner, Val.memoHit? ans = some (cell, owner) ∧
      w'.«Π» cell = some (.handle Ty.contextTarget, cert)
  | .memoBuild _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoComplete _ _ _ => ans = Val.unit
  -- the last observer's release answers the layer's scope handle, for the caller to close
  | .memoRelease _ _ => ans = Val.unit ∨ ∃ sc, ans = Val.scopeHandle sc

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

/-- **Row 116's host-row entry**: the operation is in the source signature's domain, and the
row's columns are below the certificate. Outside the table the row is the placeholder, whose
`never` columns are below every certificate, so without the bit the entry held at every
certificate at a short table and constrained at a longer one
(`Test/Program/TypedProgRows.lean`, `typedProg_not_table_monotone_of`); with it `TypedProg` is
monotone along an appended table (`typedProg_rows_append`). -/
def bitEntry (root : ProgramSource) (op : NativeOp) (cert : EffTy) : Prop :=
  root.signature.dom op = true ∧
    (root.signature.rowOf op).answer.sub cert.answer = true ∧
    (root.signature.rowOf op).error.sub cert.error = true

/-- The type an async registration's answer is certified at: a timer's `unit`, a deferred's
completion at the promise table's columns, a host row's columns from the source's row table
when the row is in its domain (`bitEntry`, row 116).
A host slot (`FinName.parkThen`'s release) is certified by the host protocol, a correlation the
state predicate owns; any other registration is not generated code and is refused.

Decisions row 137 (ratified 2026-10-01), reviewed here: the certificate is chosen by the
typing derivation, which may take it equal to the declared columns, so these comparisons stay in
`Ty.sub`; `fits_normalize` bridges a certificate to the checker's normalized type. The same holds
for `fiberPre`'s `awaitAll` and `raceAll` entries. -/
def asyncPre (root : ProgramSource) (w : World) (register : EffName) (cert : EffTy) : Prop :=
  match register with
  | .store (.registerSleep _) => Ty.unit.sub cert.answer = true
  | .registerAwait cell | .store (.registerAwait cell) =>
    ∃ a e, w.«Π» cell = some (a, e) ∧ a.sub cert.answer = true ∧ e.sub cert.error = true
  | .external op _ => bitEntry root op cert
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
  | .suspend _ | .interrupt _ | .interruptScoped _ | .interruptAll _ _
  | .awaitNewChildren _ => True
  -- row 139's halting arms (seat C's census): the step halts on an unknown target or an absent
  -- scope (`FiberAction.interruptAs`, `linkScope` from `runIn` and `forkIn`,
  -- `FiberAction.closeScope`, `prepareScopedExitR`), so the row demands them; a race
  -- registration marker is `RegistrationState`'s, never typed code
  | .interruptAs target _ => (w.Γ target).isSome = true
  | .runIn target scope =>
    (w.Γ target).isSome = true ∧ (w.state.scopes.entryAt scope).isSome = true
  | .guard_ _ | .unguard _ | .finishFinalizer _ | .construction
  | .foreignRelease _ _ | .closeWalk _ _ _ | .closeIter _ _ _
  | .cancelRace _ | .dropObservers _ | .frontier _ _ => True
  | .scopeExit _ scope _ | .closeScope scope _ => (w.state.scopes.entryAt scope).isSome = true
  | .raceRegister _ => False
  | .snapshotChildren => cert = .list (.fiberOf .unknown .unknown)
  | .scoped body => PointTyped root w body cert
  | .mask _ body => BodyTyped root w body cert
  | .forkScoped child _ _ => PointTyped root w child cert
  | .fork body _ _ => BodyTyped root w body cert
  | .forkIn child _ scope _ =>
    PointTyped root w child cert ∧ (w.state.scopes.entryAt scope).isSome = true
  | .gen p => PointTyped root w p cert
  | .loop p _ => PointTyped root w p cert
  | .refuse _ => False

/-- What each fiber row's answer satisfies: what the machine delivers to the continuation
(decisions row 136 for the await-by-value, close-scope and close-walk rows). -/
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
    -- the encoded exit, the checker's own rule (`Program/Checker.lean:196`) and row 106's token
    -- rule (`observerDeliveredType`), not the target's answer column
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ Fits w' ans (.exitOf ty.answer ty.error)
  | .fork _ _ _ | .forkIn _ _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkScoped _ _ _ => ∃ id : FiberId, ans = .success (Val.fiber id) ∧ w'.Γ id = some cert
  | .mask _ _ | .scoped _ | .raceAll _ _ | .raceRegister _ | .async _ _ | .gen _ | .loop _ _ =>
    ExitOk w' cert ans
  | .unguard ex | .finishFinalizer ex | .scopeExit _ _ ex => ans = ex
  -- `Scope.close` answers `void` and the close walk its merged exit: a success or a clean
  -- failure, an exit at `⟨unit, never⟩`, never the closing argument
  | .closeScope _ _ | .closeIter _ _ _ => ExitOk w' (EffTy.pure .unit) ans
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

/-- The fiber arm's inversion (TY-16): an operation that is none of the four control markers is
typed by its certificate, its pre, and a continuation for every answer the post admits at every
later world. -/
theorem fiber_inv {root : ProgramSource} {w : World} {ty : EffTy} {op : FiberOp}
    {k : op.answer → RProgram} (h : TypedProg root w ty (.vis (.inr op) k))
    (notGuard : ∀ kind, op ≠ .guard_ kind) (notUnguard : ∀ ex, op ≠ .unguard ex)
    (notFinish : ∀ ex, op ≠ .finishFinalizer ex)
    (notScopeExit : ∀ prev sc ex, op ≠ .scopeExit prev sc ex) :
    ∃ cert : (Ψ_F root).Cert op, (Ψ_F root).pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, (Ψ_F root).post w' op cert ans → TypedProg root w' ty (k ans) := by
  cases h with
  | fiber _ _ _ _ cert pre next => exact ⟨cert, pre, next⟩
  | guard _ _ _ _ => exact absurd rfl (notGuard _)
  | unguard _ => exact absurd rfl (notUnguard _)
  | finishFinalizer _ => exact absurd rfl (notFinish _)
  | scopeExit _ _ => exact absurd rfl (notScopeExit _ _ _)

/-- A guard's typing: the body at the guard's intermediate type `mid`, a run arm for the exits
the guard row admits at `mid` and a skip arm, both at every later world. With the Kripke-closed
frame judgment (row 135) this is the arrow of the frame the evaluator saves
(`saveR`'s `.resume kind`), with the run arm's premise curried: `TypedProg.guard_frame`, stated
below the hook protocols. Before row 135
the frame's arms were stated at one world, so the two were not the same arrow, whatever this
docstring then said. -/
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
stored, and no termination theorem for arbitrary source code is asserted.

They are Kripke-closed in their own definitions (decisions row 135): a step answers every value
that fits at every later world, and the answer's `resume`/`continue` tail is a protocol at that
answer's world. So a protocol holds at every later world with one intermediate type
(`iteratorProtocol_mono`, `loopProtocol_mono`), which is what the walk needs when it re-pushes
the resumed frame. Wrapping a one-world protocol at the frame is not enough: the pushed
protocol could then pick its intermediate type per world (`output_not_kripke`,
`Test/Program/FramesNotKripke.lean`). The world is an index, not a parameter, since a step's
answer lives at a later world. -/
mutual
  inductive IteratorProtocol (root : ProgramSource) : World → EffTy → EffTy → EffName → Prop
    | step {w : World} {tin tout : EffTy} {name : EffName}
        (errors : tin.error = tout.error)
        (next : ∀ w', w.leHost w' → ∀ v, Fits w' v tin.answer →
          IteratorAnswer root w' tout ((interpR root.program).iterNext name v).2) :
        IteratorProtocol root w tin tout name
  inductive IteratorAnswer (root : ProgramSource) :
      World → EffTy → IterStep EffName EffThunk Val Err Defect FiberId Ann RProgram → Prop
    | done {w : World} {tout : EffTy} (result : Val) (typed : ExitOk w tout (.success result)) :
        IteratorAnswer root w tout (.done result)
    | halt {w : World} {tout : EffTy} (cause : CauseV) (typed : ExitOk w tout (.failure cause)) :
        IteratorAnswer root w tout (.halt cause)
    | resume {w : World} {tout : EffTy} (code : RProgram) (name : EffName) (tin : EffTy)
        (typed : TypedProg root w tin code) (tail : IteratorProtocol root w tin tout name) :
        IteratorAnswer root w tout (.resume code name)
end

mutual
  inductive LoopProtocol (root : ProgramSource) : World → EffTy → EffTy → EffName → Val → Prop
    | step {w : World} {tin tout : EffTy} {name : EffName} {cursor : Val}
        (errors : tin.error = tout.error)
        (next : ∀ w', w.leHost w' → ∀ v, Fits w' v tin.answer →
          LoopAnswer root w' tout name ((interpR root.program).loopResume name cursor v)) :
        LoopProtocol root w tin tout name cursor
  inductive LoopAnswer (root : ProgramSource) :
      World → EffTy → EffName → LoopNext Val RProgram → Prop
    | continue {w : World} {tout : EffTy} {name : EffName} (cursor : Val) (body : RProgram)
        (tin : EffTy) (typed : TypedProg root w tin body)
        (tail : LoopProtocol root w tin tout name cursor) :
        LoopAnswer root w tout name (.continue cursor body)
    | finish {w : World} {tout : EffTy} {name : EffName} (code : RProgram)
        (typed : TypedProg root w tout code) :
        LoopAnswer root w tout name (.finish code)
end

/-- The three named hook arrows (slice 5 brief §3.3 as amended 2026-09-23), each closed under
later worlds (row 135). The async clause types the cancellation only for an incoming failure
that is itself typed at the frame's type, at the world the failure arrives in, the evidence
`popR` holds at that arm (`E4-SCHED-CE-010`). -/
def frameProtocols (root : ProgramSource) : Contracts.FrameProtocols where
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ w', w.leHost w' →
    ∀ cause, ExitOk w' tin (.failure cause) → cause.hasInterrupts = true →
      TypedProg root w' tout ((interpR root.program).cancelThenFail name cause)
  iterator := IteratorProtocol root
  loop := LoopProtocol root

/-- An iterator protocol holds at every later world, with the same intermediate type. -/
theorem iteratorProtocol_mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {tin tout : EffTy} {name : EffName} (h : IteratorProtocol root w tin tout name) :
    IteratorProtocol root w' tin tout name := by
  cases h with
  | step errors next =>
    exact .step errors (fun w'' o v hv => next w'' (leHost_trans _ _ _ ord o) v hv)

/-- A loop protocol holds at every later world, with the same intermediate type. -/
theorem loopProtocol_mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {tin tout : EffTy} {name : EffName} {cursor : Val} (h : LoopProtocol root w tin tout name cursor) :
    LoopProtocol root w' tin tout name cursor := by
  cases h with
  | step errors next =>
    exact .step errors (fun w'' o v hv => next w'' (leHost_trans _ _ _ ord o) v hv)

/-- The async finalizer's clause holds at every later world. -/
theorem asyncFinalizerProtocol_mono {root : ProgramSource} {w w' : World} (ord : w.leHost w')
    {tin tout : EffTy} {name : EffName} (h : (frameProtocols root).asyncFinalizer w tin tout name) :
    (frameProtocols root).asyncFinalizer w' tin tout name :=
  ⟨h.1, fun w'' o => h.2 w'' (leHost_trans _ _ _ ord o)⟩

namespace TypedProg

/-- **A guard's typing is the saved frame's arrow**: the body is typed at `mid`, and the frame
the evaluator saves (`saveR f kind (fun ex => k (some ex))`, `EvaluateR.lean:147`) is accepted
from `mid` to the guard's type, at every later world. -/
theorem guard_frame {root : ProgramSource} {w : World} {ty : EffTy} {kind : GuardKind}
    {k : Option ExitV → RProgram} (h : TypedProg root w ty (.vis (.inr (.guard_ kind)) k)) :
    ∃ mid : EffTy, TypedProg root w mid (k none) ∧
      Contracts.FrameAccepts (TypedProg root) ExitOk (frameProtocols root) w mid ty
        (.resume kind fun ex => k (some ex)) := by
  obtain ⟨mid, body, run, skip⟩ := guard_inv h
  exact ⟨mid, body, .resume kind _ (fun w' ord ex hex arm => run w' ord ex ⟨arm, hex⟩) skip⟩

end TypedProg

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

/-! World weakening (ruling 2026-09-23, audit A4; decisions rows 87 and 135): typing survives
every later world the host order allows. Every continuation of `TypedProg` is typed at the
world its answer arrives in, so only the leaves, the demands and a guard's body need transport:
the leaves by the membership transport laws, the demands by `storePre_mono` and
`fiberPre_mono`, the body by induction. The saved stack is Kripke-closed (`Contracts`), so a
saved frame transports once its code does (`savedOk_mono`). -/

/-- Value membership persists along the host-world order, with the ledger's binder order. -/
theorem strongValue_mono (w w' : World) (ty : Ty) (v : Val) :
    w.leHost w' → Fits w v ty → Fits w' v ty :=
  fun ordered h => fits_mono ordered h

/-- Exit membership persists along the host-world order, with the ledger's binder order. -/
theorem strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV) :
    w.leHost w' → ExitOk w ty ex → ExitOk w' ty ex :=
  fun ordered h => ⟨fitsExit_mono ordered h.1, h.2⟩

section Mono
variable {w w' : World}

theorem envTyped_mono (ord : w.leHost w') {env : List Ty} {vals : List Val}
    (h : EnvTyped w env vals) : EnvTyped w' env vals :=
  ⟨h.1, fun i ty v hi hv => fits_mono ord (h.2 i ty v hi hv)⟩

theorem pointTyped_mono (ord : w.leHost w') {src : ProgramSource} {p : Point} {ty : EffTy}
    (h : PointTyped src w p ty) : PointTyped src w' p ty := by
  obtain ⟨e, env, hat, hchk, henv⟩ := h
  exact ⟨e, env, hat, hchk, envTyped_mono ord henv⟩

theorem bodyTyped_mono (ord : w.leHost w') {src : ProgramSource} {b : Body} {ty : EffTy}
    (h : BodyTyped src w b ty) : BodyTyped src w' b ty := by
  cases h with
  | at_ p ty h => exact .at_ p ty (pointTyped_mono ord h)
  | fin name ex ty hex => exact .fin name ex ty (strongExit_mono _ _ _ _ ord hex)
  | raceCleanup race => exact .raceCleanup race
  | acquireIn p ctx ty h => exact .acquireIn p ctx ty (pointTyped_mono ord h)
  | release p prev ty h => exact .release p prev ty (pointTyped_mono ord h)
  | layerBuild p m scope ty h => exact .layerBuild p m scope ty (pointTyped_mono ord h)

/-- Every store row's demand is upward closed (all 31 rows). -/
theorem storePre_mono (root : ProgramSource) (ord : w.leHost w') (op : SyncOp)
    (cert : StoreCert op) (h : storePre root w op cert) : storePre root w' op cert := by
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  cases op with
  | refMake initial =>
    simp only [storePre] at h ⊢
    exact ⟨h.1, fits_mono ord h.2⟩
  | refGet cell | refUpdate cell _ | refGetAndUpdate cell _ | refUpdateAndGet cell _
  | refUpdateSome cell _ | refGetAndUpdateSome cell _ | refUpdateSomeAndGet cell _ =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty⟩ := h
    exact ⟨ty, hRho _ _ hty⟩
  | refModify cell _ | refModifySome cell _ =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty, equiv⟩ := h
    exact ⟨ty, hRho _ _ hty, equiv⟩
  | refSet cell v | refGetAndSet cell v | refSetAndGet cell v =>
    simp only [storePre] at h ⊢
    obtain ⟨ty, hty, hv⟩ := h
    exact ⟨ty, hRho _ _ hty, fits_mono ord hv⟩
  | deferredIsDone key | deferredPoll key | deferredAwaitCleanup key _ _
  | deferredInterruptWith key _ =>
    simp only [storePre] at h ⊢
    exact isSome_extends hPi h
  | deferredCompleteWith key completion =>
    simp only [storePre] at h ⊢
    obtain ⟨a, e, hkey, typed⟩ := h
    refine ⟨a, e, hPi _ _ hkey, ?_⟩
    cases completion with
    | ofExit ex => exact strongExit_mono _ _ _ _ ord typed
    | ofRefGet cell =>
      obtain ⟨t, ht, sub⟩ := typed
      exact ⟨t, hRho _ _ ht, sub⟩
  | deferredMake | memoBuild _ _ | memoGet _ _ => exact h
  | scopeAdd scope _ | scopeRemove scope _ | scopeIsClosed scope | scopeFork scope _ =>
    simp only [storePre] at h ⊢
    exact ord.1.1.2.2.2.1 scope h
  | clockNow | sleepCancel _ _ | scopeMake _ | memoFork _ | memoComplete _ _ _ | memoRelease _ _ =>
    exact trivial

theorem asyncPre_mono (root : ProgramSource) (ord : w.leHost w') (register : EffName)
    (cert : EffTy) (h : asyncPre root w register cert) : asyncPre root w' register cert := by
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  unfold asyncPre at h ⊢
  split at h
  · exact h
  · obtain ⟨a, e, hc, ha, he⟩ := h
    exact ⟨a, e, hPi _ _ hc, ha, he⟩
  · obtain ⟨a, e, hc, ha, he⟩ := h
    exact ⟨a, e, hPi _ _ hc, ha, he⟩
  · exact h
  · exact h
  · exact h.elim

/-- Every fiber row's demand is upward closed (all 40 rows). -/
theorem fiberPre_mono (root : ProgramSource) (ord : w.leHost w') (op : FiberOp)
    (cert : FiberCert op) (h : fiberPre root w op cert) : fiberPre root w' op cert := by
  have hGamma : TableExtends w.Γ w'.Γ := ord.1.2.1
  have hPi : TableExtends w.«Π» w'.«Π» := ord.1.2.2.1
  have hRho : TableExtends w.Ρ w'.Ρ := ord.1.2.2.2.1
  cases op with
  | fork body _ _ => exact bodyTyped_mono ord h
  | mask _ body => exact bodyTyped_mono ord h
  -- row 139: scope entries persist along the host order, the fiber table grows
  | forkIn child _ scope _ => exact ⟨pointTyped_mono ord h.1, ord.1.1.2.2.2.1 scope h.2⟩
  | forkScoped child _ _ => exact pointTyped_mono ord h
  | «scoped» body => exact pointTyped_mono ord h
  | gen p => exact pointTyped_mono ord h
  | loop p _ => exact pointTyped_mono ord h
  | await target _ =>
    simp only [fiberPre] at h ⊢
    exact isSome_extends hGamma h
  | awaitAll targets | awaitAllFailFast targets =>
    simp only [fiberPre] at h ⊢
    obtain ⟨a, e, hc, hall⟩ := h
    refine ⟨a, e, hc, fun t ht => ?_⟩
    obtain ⟨fty, hf, ha, he⟩ := hall t ht
    exact ⟨fty, hGamma _ _ hf, ha, he⟩
  | raceAll entrants _ =>
    simp only [fiberPre] at h ⊢
    intro p hp
    obtain ⟨ty, hpt, ha, he⟩ := h p hp
    exact ⟨ty, pointTyped_mono ord hpt, ha, he⟩
  | async register _ => exact asyncPre_mono root ord register cert h
  | setContext ctx =>
    simp only [fiberPre] at h ⊢
    exact servicesFit_map hPi hRho ord.2 (fun _ hs => scopeLive_mono ord.1 hs) (serviceTy_of_le ord.1) h
  | getContext | snapshotChildren => exact h
  | refuse _ | raceRegister _ => exact (h : False).elim
  | interruptAs target _ =>
    simp only [fiberPre] at h ⊢
    exact isSome_extends hGamma h
  | runIn target scope =>
    simp only [fiberPre] at h ⊢
    exact ⟨isSome_extends hGamma h.1, ord.1.1.2.2.2.1 scope h.2⟩
  | scopeExit _ scope _ | closeScope scope _ =>
    simp only [fiberPre] at h ⊢
    exact ord.1.1.2.2.2.1 scope h
  | getId | yieldNow _ | ambientScope | sync _ | suspend _ | interrupt _
  | interruptScoped _ | interruptAll _ _ | awaitNewChildren _ | guard_ _ | unguard _
  | finishFinalizer _ | construction | foreignRelease _ _
  | closeWalk _ _ _ | closeIter _ _ _ | cancelRace _ | dropObservers _
  | frontier _ _ => exact trivial

end Mono

/-- **`TypedProg` is world-monotone** (closes `M3bWorld.typedProg_mono`; seat ALGEBRA's P2,
2026-10-01). Every continuation clause already quantifies over later worlds, so only the
leaves, the demands and the guard's body need transport. -/
theorem typedProg_mono (root : ProgramSource) (w w' : World) (ty : EffTy) (p : RProgram)
    (ord : w.leHost w') (h : TypedProg root w ty p) : TypedProg root w' ty p := by
  induction h generalizing w' with
  | pure exit => exact .pure (strongExit_mono _ _ _ _ ord exit)
  | store cert pre next _ =>
    exact .store cert (storePre_mono root ord _ cert pre)
      (fun w'' ord' ans post => next w'' (leHost_trans _ _ _ ord ord') ans post)
  | fiber notGuard notUnguard notFinish notScopeExit cert pre next _ =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert (fiberPre_mono root ord _ cert pre)
      (fun w'' ord' ans post => next w'' (leHost_trans _ _ _ ord ord') ans post)
  | guard mid _ run skip ihBody _ =>
    exact .guard mid (ihBody _ ord)
      (fun w'' ord' ex post => run w'' (leHost_trans _ _ _ ord ord') ex post)
      (fun w'' ord' ex hfit harm => skip w'' (leHost_trans _ _ _ ord ord') ex hfit harm)
  | unguard payload => exact .unguard (strongExit_mono _ _ _ _ ord payload)
  | finishFinalizer payload => exact .finishFinalizer (strongExit_mono _ _ _ _ ord payload)
  | scopeExit payload next _ =>
    exact .scopeExit (strongExit_mono _ _ _ _ ord payload)
      (fun w'' ord' ans => next w'' (leHost_trans _ _ _ ord ord') ans)

/-- A saved frame of the typed state transports along the host order. -/
theorem savedOk_mono (root : ProgramSource) (w w' : World) (final : EffTy) (x : RSaved)
    (ord : w.leHost w')
    (h : Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final x) :
    Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w' final x :=
  Contracts.savedOk_mono (fun {w w'} {ty} {p} o hp => typedProg_mono root w w' ty p o hp) ord h

/-! ## `TypedProg` along an appended row table (decisions rows 115, 116; TY-12)

An appended row extends the source's signature under the same service declarations
(`SigApp.rows_append`), so every precondition that reads the source transports along it: the
checked points (`check_ext`), the memo layer (`checkLayer_ext`) and the host-row entry, whose
domain bit puts the operation in the shorter table's domain, where the longer table's row is the
same (`bitEntry_rows_append`). No postcondition reads the source. So `TypedProg` is monotone along
an appended table (`typedProg_rows_append`), beside its monotonicity along the world order
(`typedProg_mono`). Without the bit it is not (`Test/Program/TypedProgRows.lean`,
`typedProg_not_table_monotone_of`). Moved from that battery (seat A), where it was proved under
the entry's transport as a hypothesis; the bit makes it hold outright. -/

/-- **Row 116's entry transports along an appended table** (proved): the bit puts the operation in
the shorter domain, where the longer table's row is the same. -/
theorem bitEntry_rows_append (src src' : ProgramSource) (t' : RowTable)
    (htab : src'.table = src.table ++ t') (op : NativeOp) (cert : EffTy)
    (h : bitEntry src op cert) : bitEntry src' op cert := by
  obtain ⟨hdom, ha, he⟩ := h
  have hrow := (rows_append src.table t').row op hdom
  show (nativeSignature src'.table).dom op = true ∧
    ((nativeSignature src'.table).rowOf op).answer.sub cert.answer = true ∧
    ((nativeSignature src'.table).rowOf op).error.sub cert.error = true
  rw [htab, hrow.2]
  exact ⟨hrow.1, ha, he⟩

section RowsAppend

variable (src src' : ProgramSource) (t' : RowTable)
  (hprog : src'.program = src.program) (htab : src'.table = src.table ++ t')
  (hsvc : src'.services = src.services)
include hprog htab hsvc

omit hprog in
/-- The longer source's signature extends the shorter one's: an appended row table under the
same service declarations. -/
theorem signature_rows_append : SigExtends src.signature src'.signature := by
  show SigExtends src.sig.signature (SigApp.mk src'.table src'.services).signature
  rw [htab, hsvc]
  exact SigApp.rows_append src.sig t'

theorem pointTyped_rows_append {w : World} {point : Point} {ty : EffTy}
    (h : PointTyped src w point ty) : PointTyped src' w point ty := by
  obtain ⟨e, env, hat, hcheck, henv⟩ := h
  refine ⟨e, env, ?_, ?_, henv⟩
  · rw [hprog]
    exact hat
  · exact check_ext (signature_rows_append src src' t' htab hsvc) hcheck

theorem bodyTyped_rows_append {w : World} {body : Body} {ty : EffTy}
    (h : BodyTyped src w body ty) : BodyTyped src' w body ty := by
  cases h with
  | at_ p ty hp => exact .at_ p ty (pointTyped_rows_append src src' t' hprog htab hsvc hp)
  | fin name ex ty hex => exact .fin name ex ty hex
  | raceCleanup race => exact .raceCleanup race
  | acquireIn p ctx ty hp =>
    exact .acquireIn p ctx ty (pointTyped_rows_append src src' t' hprog htab hsvc hp)
  | release p prev ty hp =>
    exact .release p prev ty (pointTyped_rows_append src src' t' hprog htab hsvc hp)
  | layerBuild p m scope ty hp =>
    exact .layerBuild p m scope ty (pointTyped_rows_append src src' t' hprog htab hsvc hp)

theorem storePre_rows_append {w : World} {op : SyncOp} {cert : StoreCert op}
    (h : storePre src w op cert) : storePre src' w op cert := by
  cases op with
  | memoGet layer m =>
    obtain ⟨l, lt, hat, hcheck, herr⟩ := h
    refine ⟨l, lt, ?_, ?_, herr⟩
    · rw [hprog]
      exact hat
    · exact checkLayer_ext (signature_rows_append src src' t' htab hsvc) hcheck
  | _ => exact h

omit hprog hsvc in
theorem asyncPre_rows_append {w : World} {register : EffName} {cert : EffTy}
    (h : asyncPre src w register cert) : asyncPre src' w register cert := by
  cases register with
  | external op req => exact bitEntry_rows_append src src' t' htab op cert h
  | store name => cases name <;> exact h
  | _ => exact h

theorem fiberPre_rows_append {w : World} {op : FiberOp} {cert : FiberCert op}
    (h : fiberPre src w op cert) : fiberPre src' w op cert := by
  cases op with
  | raceAll entrants race =>
    intro p hp
    obtain ⟨ty, hpt, ha, he⟩ := h p hp
    exact ⟨ty, pointTyped_rows_append src src' t' hprog htab hsvc hpt, ha, he⟩
  | async register token => exact asyncPre_rows_append src src' t' htab h
  | «scoped» body => exact pointTyped_rows_append src src' t' hprog htab hsvc h
  | mask flag body => exact bodyTyped_rows_append src src' t' hprog htab hsvc h
  | forkScoped child options path => exact pointTyped_rows_append src src' t' hprog htab hsvc h
  | fork body options path => exact bodyTyped_rows_append src src' t' hprog htab hsvc h
  | forkIn child options scope path =>
    exact ⟨pointTyped_rows_append src src' t' hprog htab hsvc h.1, h.2⟩
  | gen p => exact pointTyped_rows_append src src' t' hprog htab hsvc h
  | loop p name => exact pointTyped_rows_append src src' t' hprog htab hsvc h
  | _ => exact h

/-- **`TypedProg` is monotone along an appended row table** (TY-12's positive control, proved;
rows 115, 116): the same program typed under the shorter source is typed under the longer one, at
every world and type. -/
theorem typedProg_rows_append :
    ∀ {w : World} {ty : EffTy} {p : RProgram}, TypedProg src w ty p → TypedProg src' w ty p := by
  intro w ty p h
  induction h with
  | pure exit => exact .pure exit
  | store cert pre next ih =>
    exact .store cert (storePre_rows_append src src' t' hprog htab hsvc pre)
      fun w' hle ans hpost => ih w' hle ans hpost
  | fiber notGuard notUnguard notFinish notScopeExit cert pre next ih =>
    exact .fiber notGuard notUnguard notFinish notScopeExit cert
      (fiberPre_rows_append src src' t' hprog htab hsvc pre)
      fun w' hle ans hpost => ih w' hle ans hpost
  | guard mid body run skip ihbody ihrun =>
    exact .guard mid ihbody (fun w' hle ex hpost => ihrun w' hle ex hpost) skip
  | unguard payload => exact .unguard payload
  | finishFinalizer payload => exact .finishFinalizer payload
  | scopeExit payload next ih => exact .scopeExit payload fun w' hle ans => ih w' hle ans

end RowsAppend

namespace M3bWorld

theorem strongValue_mono (w w' : World) (ty : Ty) (v : Val) :
    ProofGraph.Obligation (w.leHost w' → Fits w v ty → Fits w' v ty) := ⟨⟩

theorem strongExit_mono (w w' : World) (ty : EffTy) (ex : ExitV) :
    ProofGraph.Obligation (w.leHost w' → ExitOk w ty ex → ExitOk w' ty ex) := ⟨⟩

theorem typedProg_mono (root : ProgramSource) (w w' : World) (ty : EffTy) (p : RProgram) :
    ProofGraph.Obligation (w.leHost w' → TypedProg root w ty p → TypedProg root w' ty p) := ⟨⟩

/-- A saved stack transports along the host order (row 135). -/
theorem stackAccepts_mono (root : ProgramSource) (w w' : World) (a b : EffTy)
    (s : List ScopeFrame) : ProofGraph.Obligation (w.leHost w' →
      Contracts.StackAccepts (TypedProg root) ExitOk (frameProtocols root) w a b s →
      Contracts.StackAccepts (TypedProg root) ExitOk (frameProtocols root) w' a b s) := ⟨⟩

/-- A saved frame (code and stack) transports along the host order (row 135). -/
theorem savedOk_mono (root : ProgramSource) (w w' : World) (final : EffTy) (x : RSaved) :
    ProofGraph.Obligation (w.leHost w' →
      Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w final x →
      Contracts.SavedOk (TypedProg root) ExitOk (frameProtocols root) w' final x) := ⟨⟩

end M3bWorld

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3aResidualObligations.settling_ref_allocation :=
  @Effect4.Program.Typed.settling_ref_allocation
#obligation_proved Effect4.Program.Typed.M3aResidualObligations.settling_ref_preserves_nat :=
  @Effect4.Program.Typed.settling_ref_preserves_nat
#obligation_proved Effect4.Program.Typed.M3aResidualObligations.settling_fork :=
  @Effect4.Program.Typed.settling_fork
#obligation_proved Effect4.Program.Typed.M3aResidualObligations.settling_mask :=
  @Effect4.Program.Typed.settling_mask

#obligation_proved Effect4.Program.Typed.M3aAdmissionObligations.unguard_payload_inv :=
  @Effect4.Program.Typed.unguard_payload_inv
#obligation_proved Effect4.Program.Typed.M3aAdmissionObligations.finishFinalizer_payload_inv :=
  @Effect4.Program.Typed.finishFinalizer_payload_inv

#typed_state_obligations Effect4.Program.Typed.M3aAdmissionObligations ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])
#typed_state_obligations Effect4.Program.Typed.M3aResidualObligations ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])

#obligation_proved Effect4.Program.Typed.M3bWorld.strongValue_mono :=
  @Effect4.Program.Typed.strongValue_mono
#obligation_proved Effect4.Program.Typed.M3bWorld.strongExit_mono :=
  @Effect4.Program.Typed.strongExit_mono
#obligation_proved Effect4.Program.Typed.M3bWorld.typedProg_mono :=
  @Effect4.Program.Typed.typedProg_mono
#obligation_proved Effect4.Program.Typed.M3bWorld.stackAccepts_mono :=
  fun _ _ _ _ _ _ ord h => Effect4.Program.Typed.Contracts.stackAccepts_mono ord h
#obligation_proved Effect4.Program.Typed.M3bWorld.savedOk_mono :=
  @Effect4.Program.Typed.savedOk_mono
-- The scope's audit and report run at the foot of `Typed/Assembly.lean`, after the bundle's
-- `SavedOk` transport joins it (row 87: `M3bWorld.preds_savedOk_mono`), so it is counted once.
