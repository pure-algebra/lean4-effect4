import Effect4.Laws.Program.Typed.Validity
import Effect4.Laws.Program.Typed.Contracts
import Effect4.Program.Checker
import Effect4.Program.Admission
import Effect4.Laws.Program.Handles
import Effect4.Laws.Program.Sched
import Effect4.Laws.Effects.Protocol
import Effect4.Laws.Auto.Obligations

/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts; strong value/cause/exit judgments resolving FR-07; control admission and marker
payload inversion resolving FR-09.

Stack and interruption preemption contracts remain held.
-/

set_option autoImplicit false
namespace Effect4.Program.Typed

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Denote
open Effect4.Laws.Effects

/-- A value's handle indices are within the allocated bounds of the world. -/
def HandlesLive (w : World) (v : Val) : Prop :=
  ∀ h ∈ v.keys, match h with
  | .cell key => key.index < w.state.refs.length
  | .promise key => key.index < w.state.deferreds.cells.length
  | .fiber id => (w.Γ id).isSome = true
  | _ => True

/-- Nested handle types align with the world typing tables. -/
def HandlesFit (w : World) (v : Val) (ty : Ty) : Prop :=
  match ty with
  | .refOf t => ∀ key, Handle.cell key ∈ v.keys → w.Ρ key = some t
  | .deferredOf a e => ∀ key, Handle.promise key ∈ v.keys → w.«Π» key = some (a, e)
  | .fiberOf a e => ∀ id, Handle.fiber id ∈ v.keys → ∃ fty, w.Γ id = some fty ∧ fty.answer = a ∧ fty.error = e
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
  Contracts.ExitFits w ty ex ∧
  (∀ v, ex = .success v → StrongValue w ty.answer v) ∧
  (∀ c, ex = .failure c → StrongCause w ty.error c)

/-- An evaluation environment typed pointwise at the corresponding static types. -/
def EnvTyped (w : World) (env : List Ty) (vals : List Val) : Prop :=
  env.length = vals.length ∧
  ∀ (i : Nat) (ty : Ty) (v : Val), env[i]? = some ty → vals[i]? = some v → StrongValue w ty v

/-- D13 source admission at an addressed program node. -/
def PointTyped (root : NativeEff) (w : World) (point : Point) (ty : EffTy) : Prop :=
  ∃ (e : NativeEff) (env : List Ty),
    Node.at_ (.eff root) point.path = some (.eff e) ∧
    Checker.check (nativeSignature []) env point.path e = .ok ty ∧
    EnvTyped w env point.env

/-- Admitted bodies covering all six `Body` constructors. -/
inductive BodyTyped (root : NativeEff) (w : World) : Body → EffTy → Prop
  | at_ (p : Point) (ty : EffTy) (h : PointTyped root w p ty) :
      BodyTyped root w (.at_ p) ty
  | fin (name : FinName) (ex : ExitV) (ty : EffTy) (hex : StrongExit w ty ex) :
      BodyTyped root w (.fin name ex) ty
  | raceCleanup (race : Nat) :
      BodyTyped root w (.raceCleanup race) (EffTy.pure .unit)
  | acquireIn (p : Point) (ctx : Ctx) (ty : EffTy) (h : PointTyped root w p ty) :
      BodyTyped root w (.acquireIn p ctx) ty
  | release (p : Point) (prev : Ctx) (ty : EffTy) (h : PointTyped root w p ty) :
      BodyTyped root w (.release p prev) ty
  | layerBuild (p : Point) (m : MemoMapId) (scope : Nat) (ty : EffTy) (h : PointTyped root w p ty) :
      BodyTyped root w (.layerBuild p m scope) ty

/-- Dedicated control-admission predicate guaranteeing that top-level control nodes
carry payloads satisfying `StrongExit`. For pure leaves and other operations, holds by
recursion on continuations. -/
inductive ControlAdmitted (root : NativeEff) : World → EffTy → RProgram → Prop
  | pure (w : World) (ty : EffTy) (ex : ExitV) :
      ControlAdmitted root w ty (.pure ex)
  | vis_inl (w : World) (ty : EffTy) (op : SyncOp) (k : Val → RProgram) :
      (∀ w', w.leHost w' → ∀ ans, ControlAdmitted root w' ty (k ans)) →
      ControlAdmitted root w ty (.vis (.inl op) k)
  | unguard (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
      StrongExit w ty ex →
      (∀ w', w.leHost w' → ControlAdmitted root w' ty (k ex)) →
      ControlAdmitted root w ty (.vis (.inr (.unguard ex)) k)
  | finishFinalizer (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
      StrongExit w ty ex →
      (∀ w', w.leHost w' → ControlAdmitted root w' ty (k ex)) →
      ControlAdmitted root w ty (.vis (.inr (.finishFinalizer ex)) k)
  | scoped (w : World) (ty : EffTy) (body : Point) (bty : EffTy) (k : ExitV → RProgram) :
      PointTyped root w body bty →
      (∀ w', w.leHost w' → ∀ ans, ControlAdmitted root w' ty (k ans)) →
      ControlAdmitted root w ty (.vis (.inr (.scoped body)) k)
  | scopeExit (w : World) (ty : EffTy) (prev : Ctx) (sc : Nat) (ex : ExitV) (k : ExitV → RProgram) :
      StrongExit w ty ex →
      (∀ w', w.leHost w' → ∀ ans, ControlAdmitted root w' ty (k ans)) →
      ControlAdmitted root w ty (.vis (.inr (.scopeExit prev sc ex)) k)
  | other (w : World) (ty : EffTy) (op : FiberOp) (k : op.answer → RProgram) :
      (∀ ex, op ≠ .unguard ex) →
      (∀ ex, op ≠ .finishFinalizer ex) →
      (∀ pt, op ≠ .scoped pt) →
      (∀ prev sc ex, op ≠ .scopeExit prev sc ex) →
      (∀ w', w.leHost w' → ∀ ans, ControlAdmitted root w' ty (k ans)) →
      ControlAdmitted root w ty (.vis (.inr op) k)

theorem unguard_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram)
    (h : ControlAdmitted root w ty (.vis (.inr (.unguard ex)) k)) : StrongExit w ty ex := by
  cases h with
  | unguard _ _ _ _ hex _ => exact hex
  | other _ _ _ _ hne _ _ _ _ => exact False.elim (hne ex rfl)

theorem finishFinalizer_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram)
    (h : ControlAdmitted root w ty (.vis (.inr (.finishFinalizer ex)) k)) : StrongExit w ty ex := by
  cases h with
  | finishFinalizer _ _ _ _ hex _ => exact hex
  | other _ _ _ _ _ hne _ _ _ => exact False.elim (hne ex rfl)

namespace M3aAdmissionObligations

theorem unguard_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (ControlAdmitted root w ty (.vis (.inr (.unguard ex)) k) → StrongExit w ty ex) := ⟨⟩

theorem finishFinalizer_payload_inv (root : NativeEff) (w : World) (ty : EffTy) (ex : ExitV) (k : ExitV → RProgram) :
    ProofGraph.Obligation (ControlAdmitted root w ty (.vis (.inr (.finishFinalizer ex)) k) → StrongExit w ty ex) := ⟨⟩

end M3aAdmissionObligations

end Effect4.Program.Typed

#obligation_proved Effect4.Program.Typed.M3aAdmissionObligations.unguard_payload_inv :=
  @Effect4.Program.Typed.unguard_payload_inv
#obligation_proved Effect4.Program.Typed.M3aAdmissionObligations.finishFinalizer_payload_inv :=
  @Effect4.Program.Typed.finishFinalizer_payload_inv

#typed_state_obligations Effect4.Program.Typed.M3aAdmissionObligations ceiling 0
  using aesop (rule_sets := [Effect4.TypedState])
