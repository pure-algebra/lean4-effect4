import Effect4.Laws.Program.Typed.Membership
import Effect4.Program.Checker
import Effect4.Laws.Program.Sched

/-!
# Laws.Program.Typed.Admission — source and control admission for typed programs

D13 source admission (checking paths and environments against the checker) before protocol
contracts, using the value membership judgments from `Typed/Membership.lean`. The shared exit
judgment also excludes `badName` and `notImplemented`; clean failures require that explicit
exclusion premise. `missingService` remains admitted in part one. Control admission (FR-09) is an
arm of the one program judgment `TypedProg` in `Typed/Residual.lean` (ruling 2026-09-23).
-/

set_option autoImplicit false
namespace Effect4.Program.Typed

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
    ExitOk w ty (.success v) := h

/-- A clean failure has base membership at every effect type because the error column
constrains only `Fail` reasons. The strengthened exit judgment separately requires the
explicit defect-exclusion premise: `cleanExit` alone admits `badName` and `notImplemented`. -/
theorem strongExit_of_clean (w : World) (ty : EffTy) (c : CauseV)
    (h : cleanExit (.failure c) = true) (shape : NoShapeDefect ty (.failure c)) :
    ExitOk w ty (.failure c) := by
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
    (h : ExitOk w ty (.failure c)) : cleanExit (.failure c) = true := by
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
