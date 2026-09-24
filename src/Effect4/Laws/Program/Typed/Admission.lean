import Effect4.Laws.Program.Typed.Validity
import Effect4.Program.Checker
import Effect4.Laws.Program.Sched

/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts; strong value/cause/exit judgments resolving FR-07; the clean-exit lemmas that type
interrupt-only and defect-only failures at every effect type. Control admission (FR-09) is an
arm of the one program judgment `TypedProg` in `Typed/Residual.lean` (ruling 2026-09-23).
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
  ExitFits w ty ex ∧
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

/-- An exit whose failure carries no `Fail` reason: interruptions and defects only. Every
success is clean. The sanitized exit at a preempted skip is clean (`Cause.sanitize_clean`). -/
def cleanExit : ExitV → Bool
  | .success _ => true
  | .failure c => c.reasons.all fun r => r.tag != .fail

/-- A clean failure fits every effect type at every world: the error column constrains
`Fail` reasons only. -/
theorem strongExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) : StrongExit w ty (.failure c) := by
  have hall : ∀ r ∈ c.reasons, r.tag ≠ .fail := by
    intro r hr
    exact bne_iff_ne.mp (List.all_eq_true.mp h r hr)
  refine ⟨?_, (fun _ heq => nomatch heq), fun c' heq => ?_⟩
  · change causeAdmits _ ty.error c = true
    unfold causeAdmits
    rw [List.all_eq_true]
    intro r hr
    have hne := hall r hr
    cases r with
    | fail e ann => exact absurd rfl hne
    | die _ _ => rfl
    | interrupt _ _ => rfl
  · cases heq
    intro r hr
    have hne := hall r hr
    cases r with
    | fail e ann => exact absurd rfl hne
    | die _ _ => trivial
    | interrupt _ _ => trivial

/-- At a `never` error column a strong failure is clean: no value has type `never`. -/
theorem cleanExit_of_never (w : World) (ty : EffTy) (c : CauseV) (never : ty.error = .never)
    (h : StrongExit w ty (.failure c)) : cleanExit (.failure c) = true := by
  have hadm : causeAdmits (fun value ty => Val.hasTy value ty w.state.externals.allocated)
      ty.error c = true := h.1
  rw [never] at hadm
  unfold cleanExit
  rw [List.all_eq_true]
  intro r hr
  have hr' := List.all_eq_true.mp hadm r hr
  cases r with
  | fail e ann =>
    cases hval : valOfErr e with
    | none => simp only [reasonAdmits, hval] at hr'; cases hr'
    | some v => simp only [reasonAdmits, hval] at hr'; cases hr'
  | die _ _ => rfl
  | interrupt _ _ => rfl

end Effect4.Program.Typed
