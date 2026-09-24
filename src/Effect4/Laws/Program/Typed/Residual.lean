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
  | .refMake _ => Ty
  | .deferredMake | .memoBuild _ _ => Ty × Ty
  | _ => PUnit

def storePre (w : World) (op : SyncOp) (cert : StoreCert op) : Prop :=
  match op with
  | .refMake initial => cert.closed = true ∧ StrongValue w cert initial
  | .refGet cell => ∃ ty, w.Ρ cell = some ty
  | .refSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValue w ty v
  | .refGetAndSet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValue w ty v
  | .refSetAndGet cell v => ∃ ty, w.Ρ cell = some ty ∧ StrongValue w ty v
  | .refUpdate cell _ | .refGetAndUpdate cell _ | .refUpdateAndGet cell _
  | .refUpdateSome cell _ | .refGetAndUpdateSome cell _ | .refUpdateSomeAndGet cell _
  | .refModify cell _ | .refModifySome cell _ => ∃ ty, w.Ρ cell = some ty
  | .deferredMake => cert.1.closed = true ∧ cert.2.closed = true
  | .deferredIsDone key | .deferredPoll key | .deferredAwaitCleanup key _ _ => (w.«Π» key).isSome = true
  | .deferredCompleteWith key _ => (w.«Π» key).isSome = true
  | .deferredInterruptWith key _ => (w.«Π» key).isSome = true
  | .clockNow | .sleepCancel _ _ => True
  | .scopeMake _ | .scopeAdd _ _ | .scopeRemove _ _ | .scopeIsClosed _ | .scopeFork _ _ => True
  | .memoFork _ | .memoGet _ _ | .memoComplete _ _ _ | .memoRelease _ _ => True
  | .memoBuild _ _ => cert.1.closed = true ∧ cert.2.closed = true

def storePost (w' : World) (op : SyncOp) (cert : StoreCert op) (ans : Val) : Prop :=
  match op with
  | .refMake _ => ∃ key : RefKey, ans = Val.cell key ∧ w'.Ρ key = some cert
  | .refGet cell => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refSet cell _ => ans = Val.cell cell
  | .refGetAndSet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refSetAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refUpdate _ _ | .refUpdateSome _ _ => ans = Val.unit
  | .refGetAndUpdate cell _ | .refGetAndUpdateSome cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refUpdateAndGet cell _ | .refUpdateSomeAndGet cell _ => ∃ ty, w'.Ρ cell = some ty ∧ StrongValue w' ty ans
  | .refModify _ _ | .refModifySome _ _ => True
  | .deferredMake => ∃ key : DeferredKey, ans = Val.promise key ∧ w'.«Π» key = some cert
  | .deferredIsDone _ => ∃ b, ans = Val.bool b
  | .deferredPoll _ => True
  | .deferredCompleteWith _ _ | .deferredInterruptWith _ _ | .deferredAwaitCleanup _ _ _ => ∃ b, ans = Val.bool b
  | .clockNow => ∃ n, ans = Val.nat n
  | .sleepCancel _ _ => ans = Val.unit
  | .scopeMake _ => ∃ sc, ans = Val.scopeHandle sc
  | .scopeAdd _ _ | .scopeRemove _ _ => ∃ b, ans = Val.bool b
  | .scopeIsClosed _ => ∃ b, ans = Val.bool b
  | .scopeFork _ _ => ∃ sc, ans = Val.scopeHandle sc
  | .memoFork _ => ∃ id, ans = Val.memoMap id
  | .memoGet _ _ => True
  | .memoBuild _ _ => True
  | .memoComplete _ _ _ | .memoRelease _ _ => ans = Val.unit

def Ψ_S : Protocol World StoreSig where
  Cert := StoreCert
  pre := storePre
  post := storePost

/-! ## The Fiber Protocol (40 FiberOp rows) -/

/-- Fork and mask certify their body's type. A guard certifies its intermediate type: the type
of its body and of every exit its saved arm receives (ruling 2026-09-23, `E4-SCHED-CE-011`). -/
def FiberCert : FiberOp → Type
  | .fork _ _ _ | .mask _ _ | .guard_ _ => EffTy
  | _ => PUnit

def fiberPre (root : NativeEff) (w : World) (op : FiberOp) (cert : FiberCert op) : Prop :=
  match op with
  | .getId | .getContext | .setContext _ | .yieldNow _ | .ambientScope | .sync _ => True
  | .await target _ => (w.Γ target).isSome = true
  | .awaitAll targets | .awaitAllFailFast targets => ∀ t ∈ targets, (w.Γ t).isSome = true
  | .raceAll _ _ | .async _ _ | .suspend _ | .interrupt _ | .interruptAs _ _
  | .interruptScoped _ | .interruptAll _ _ | .runIn _ _ | .awaitNewChildren _ => True
  | .guard_ _ | .unguard _ | .finishFinalizer _ | .scopeExit _ _ _ | .construction
  | .closeScope _ _ | .foreignRelease _ _ | .closeWalk _ _ _ | .closeIter _ _ _
  | .gen _ | .loop _ _ | .raceRegister _ | .cancelRace _ | .snapshotChildren
  | .dropObservers _ => True
  | .scoped body => ∃ ty, PointTyped root w body ty
  | .mask _ body => BodyTyped root w body cert
  | .forkScoped child _ _ => ∃ ty, PointTyped root w child ty
  | .fork body _ _ => BodyTyped root w body cert
  | .forkIn child _ _ _ => ∃ ty, PointTyped root w child ty
  | .frontier _ _ => True
  | .refuse _ => False

def fiberPost (w' : World) (op : FiberOp) (cert : FiberCert op) (ans : op.answer) : Prop :=
  match op with
  | .getId => ∃ (id : FiberId), ans = Val.nat id.value
  | .getContext => True
  | .setContext _ | .yieldNow _ | .interrupt _ | .interruptAs _ _ | .interruptScoped _
  | .interruptAll _ _ | .runIn _ _ | .cancelRace _ | .dropObservers _
  | .foreignRelease _ _ | .closeWalk _ _ _ => ans = Val.unit
  | .ambientScope => ∃ sc, ans = Val.scopeHandle sc
  | .sync value => ans = value
  | .await target mode => match mode with
    | .joinEffect => ∃ ty, w'.Γ target = some ty ∧ StrongExit w' ty ans
    | .awaitValue => ∃ ty, w'.Γ target = some ty ∧ StrongValue w' ty.answer ans
  | .fork _ _ _ => ∃ id : FiberId, ans = Val.fiber id ∧ w'.Γ id = some cert
  | .forkIn _ _ _ _ => ∃ (c : EffTy) (id : FiberId), ans = Val.fiber id ∧ w'.Γ id = some c
  | .mask _ _ => StrongExit w' cert ans
  | .unguard ex | .finishFinalizer ex | .closeScope _ ex | .scopeExit _ _ ex | .closeIter _ _ ex => ans = ex
  | .guard_ kind => match ans with
    | none => True
    | some ex => kind.hasExitArm ex = true ∧ StrongExit w' cert ex
  | _ => True

def Ψ_F (root : NativeEff) : Protocol World FiberSig where
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
inductive TypedProg (root : NativeEff) : World → EffTy → RProgram → Prop
  | pure {w : World} {ty : EffTy} {ex : ExitV} (exit : StrongExit w ty ex) :
      TypedProg root w ty (.pure ex)
  | store {w : World} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
      (cert : Ψ_S.Cert op) (pre : Ψ_S.pre w op cert)
      (next : ∀ w', w.leHost w' → ∀ ans, Ψ_S.post w' op cert ans → TypedProg root w' ty (k ans)) :
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

theorem pure_inv {root : NativeEff} {w : World} {ty : EffTy} {ex : ExitV}
    (h : TypedProg root w ty (.pure ex)) : StrongExit w ty ex := by
  cases h with
  | pure exit => exact exit

theorem store_inv {root : NativeEff} {w : World} {ty : EffTy} {op : SyncOp} {k : Val → RProgram}
    (h : TypedProg root w ty (.vis (.inl op) k)) :
    ∃ cert : Ψ_S.Cert op, Ψ_S.pre w op cert ∧
      ∀ w', w.leHost w' → ∀ ans, Ψ_S.post w' op cert ans → TypedProg root w' ty (k ans) := by
  cases h with
  | store cert pre next => exact ⟨cert, pre, next⟩

/-- A guard's typing is exactly the saved frame's arrow (`Contracts.FrameAccepts.resume`) at
`mid`, with the body typed at `mid`. -/
theorem guard_inv {root : NativeEff} {w : World} {ty : EffTy} {kind : GuardKind}
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
theorem unguard_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV)
    (k : ExitV → RProgram) (h : TypedProg root w ty (.vis (.inr (.unguard ex)) k)) :
    StrongExit w ty ex := by
  cases h with
  | fiber _ notUnguard _ _ _ _ _ => exact absurd rfl (notUnguard ex)
  | unguard payload => exact payload

theorem finishFinalizer_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV)
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
  inductive IteratorProtocol (root : NativeEff) (w : World) : EffTy → EffTy → EffName → Prop
    | step {tin tout : EffTy} {name : EffName}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValue w tin.answer v →
          IteratorAnswer root w tout ((interpR root).iterNext name v).2) :
        IteratorProtocol root w tin tout name
  inductive IteratorAnswer (root : NativeEff) (w : World) :
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
  inductive LoopProtocol (root : NativeEff) (w : World) : EffTy → EffTy → EffName → Val → Prop
    | step {tin tout : EffTy} {name : EffName} {cursor : Val}
        (errors : tin.error = tout.error)
        (next : ∀ v, StrongValue w tin.answer v →
          LoopAnswer root w tout name ((interpR root).loopResume name cursor v)) :
        LoopProtocol root w tin tout name cursor
  inductive LoopAnswer (root : NativeEff) (w : World) :
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
def frameProtocols (root : NativeEff) : Contracts.FrameProtocols where
  asyncFinalizer w tin tout name := tin = tout ∧ ∀ cause, StrongExit w tin (.failure cause) →
    cause.hasInterrupts = true → TypedProg root w tout ((interpR root).cancelThenFail name cause)
  iterator := IteratorProtocol root
  loop := LoopProtocol root

/-! ## Settling Case 1: Polymorphic ref allocation and read on heterogeneous heap -/

def refAllocCont : Val → RProgram
  | .handle 2 index => .vis (.inl (.refGet ⟨index⟩)) fun v => .pure (.success v)
  | _ => .pure (.success (Val.bool false))

def refAllocGetProg : RProgram :=
  .vis (.inl (.refMake (Val.bool true))) refAllocCont

theorem strongValue_bool_true (w : World) : StrongValue w .bool (Val.bool true) := by
  refine ⟨rfl, trivial, fun h mem => ?_⟩
  cases mem

theorem strongExit_bool (w : World) (v : Val) (hv : StrongValue w .bool v) :
    StrongExit w (EffTy.pure .bool) (.success v) := by
  refine ⟨hv.1, fun v' heq => ?_, fun _ heq => nomatch heq⟩
  injection heq with heq
  subst heq
  exact hv

theorem settling_ref_allocation (root : NativeEff) (w : World) (_h0 : HeapTypedAt w ⟨0⟩ .nat) :
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

theorem settling_fork (root : NativeEff) (w : World) (child : Body) (cert : EffTy)
    (hbody : BodyTyped root w child cert) :
    TypedProg root w (EffTy.pure (.fiberOf cert.answer cert.error)) (forkProg child) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_F, fiberPost] at hpost
  rcases hpost with ⟨id, rfl, hid⟩
  refine TypedProg.pure ⟨rfl, fun v' heq => ?_, fun _ heq => nomatch heq⟩
  injection heq with heq
  subst heq
  refine ⟨rfl, fun id' mem => ?_, fun h mem => ?_⟩
  · simp only [Val.keys, Handle.ofCode_fiber, Option.toList, List.mem_singleton] at mem
    injection mem with eq_id
    subst eq_id
    exact ⟨cert, hid, rfl, rfl⟩
  · simp only [Val.keys, Handle.ofCode_fiber, Option.toList, List.mem_singleton] at mem
    subst h
    dsimp only [handleLive]
    rw [hid]
    rfl

theorem settling_mask (root : NativeEff) (w : World) (flag : Bool) (body : Body) (cert : EffTy)
    (hbody : BodyTyped root w body cert) :
    TypedProg root w cert (maskProg flag body) := by
  refine TypedProg.fiber (fun _ h => nomatch h) (fun _ h => nomatch h) (fun _ h => nomatch h)
    (fun _ _ _ h => nomatch h) cert hbody ?_
  intro w' _ ans hpost
  dsimp only [Ψ_F, fiberPost] at hpost
  exact TypedProg.pure hpost

/-! FR-09's payload inversions, restated over the one judgment under their M3a names. -/
namespace M3aAdmissionObligations

theorem unguard_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProg root w ty (.vis (.inr (.unguard ex)) k) → StrongExit w ty ex) := ⟨⟩

theorem finishFinalizer_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (TypedProg root w ty (.vis (.inr (.finishFinalizer ex)) k) → StrongExit w ty ex) := ⟨⟩

end M3aAdmissionObligations

namespace M3aResidualObligations

theorem settling_ref_allocation (_root : NativeEff) (_w : World) (_h0 : HeapTypedAt _w ⟨0⟩ .nat) :
    ProofGraph.Obligation (TypedProg _root _w (EffTy.pure .bool) refAllocGetProg) := ⟨⟩

theorem settling_ref_preserves_nat (_w _w' : World) (_ordered : _w.leHost _w') (_h0 : HeapTypedAt _w ⟨0⟩ .nat) :
    ProofGraph.Obligation (HeapTypedAt _w' ⟨0⟩ .nat) := ⟨⟩

theorem settling_fork (_root : NativeEff) (_w : World) (_child : Body) (_cert : EffTy)
    (_hbody : BodyTyped _root _w _child _cert) :
    ProofGraph.Obligation (TypedProg _root _w (EffTy.pure (.fiberOf _cert.answer _cert.error)) (forkProg _child)) := ⟨⟩

theorem settling_mask (_root : NativeEff) (_w : World) (_flag : Bool) (_body : Body) (_cert : EffTy)
    (_hbody : BodyTyped _root _w _body _cert) :
    ProofGraph.Obligation (TypedProg _root _w _cert (maskProg _flag _body)) := ⟨⟩

end M3aResidualObligations

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
