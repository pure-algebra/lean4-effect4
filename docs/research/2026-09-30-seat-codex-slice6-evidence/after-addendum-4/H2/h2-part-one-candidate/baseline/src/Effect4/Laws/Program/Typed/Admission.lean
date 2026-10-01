import Effect4.Laws.Program.Typed.Membership
import Effect4.Program.Checker
import Effect4.Laws.Program.Sched

/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts, using the value membership judgments from `Typed/Membership.lean`; the clean-exit
lemmas type interrupt-only and defect-only failures at every effect type. Control admission (FR-09) is an
arm of the one program judgment `TypedProg` in `Typed/Residual.lean` (ruling 2026-09-23).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed

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

end Effect4.Program.Typed
