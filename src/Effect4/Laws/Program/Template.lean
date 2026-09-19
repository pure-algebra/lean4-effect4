import Effect4.Laws.Program.TypeAlgebra
import Effect4.Program.Typing
import Effect4.Program.Native
import Aesop

/-!
# Laws.Program.Template — the row-template calculus (decisions row 42)

`Ty.instantiate`, `Ty.infer` and `Ty.matchTemplate` (`Program/Ty.lean`) with their laws. A
match is sound by its own guard (`matchTemplate_sound`). On a closed template the calculus is
the identity and subsumption (`instantiate_closed`, `infer_closed`, `matchTemplate_closed`),
so a row with no parameter types exactly as it did before the templates (`rowTy_closed`,
`rowTy_closed_some`). `closed` survives `normalize` (`closed_normalize`), which carries a
row's closedness through the signature's canonical view (`Row.normalizeTypes`). The native
rows of this cut are all closed (`NativeOp.row_closed`): no row is a template until step 3
of `docs/research/2026-09-18-rows-42-43-plan.md`.
-/

namespace Effect4.Program

open Effect4.Machine.Env (Requirement)

namespace Ty

theorem closed_members (t : Ty) (h : closed t = true) : ∀ x ∈ members t, closed x = true := by
  induction t <;> aesop (add norm simp [closed, members])

theorem closed_factors (t : Ty) (h : closed t = true) : ∀ x ∈ factors t, closed x = true := by
  cases t <;> aesop (add norm simp [factors, closed, members], safe forward closed_members)

theorem closed_ofMembers (xs : List Ty) (h : ∀ x ∈ xs, closed x = true) :
    closed (ofMembers xs) = true := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases xs <;> aesop (add norm simp [ofMembers, closed])

theorem closed_normalize (t : Ty) (h : closed t = true) : closed (normalize t) = true := by
  induction t with
  | prod a b iha ihb =>
    aesop (add norm simp [closed, normalize, productMembers, mem_normalizeRow],
      safe apply closed_ofMembers, safe forward closed_factors)
  | union a b iha ihb =>
    aesop (add norm simp [closed, normalize, mem_normalizeRow],
      safe apply closed_ofMembers, safe forward closed_members)
  | _ => aesop (add norm simp [closed, normalize])

theorem instantiate_closed (σ : Subst) (t : Ty) (h : closed t = true) : instantiate σ t = t := by
  induction t <;> aesop (add norm simp [closed, instantiate])

theorem infer_closed (σ : Subst) (t r : Ty) (h : closed t = true) : infer σ t r = σ := by
  induction t generalizing σ r <;> cases r <;> aesop (add norm simp [closed, infer])

/-- A match is sound: the request is a subtype of the template at the bindings. -/
theorem matchTemplate_sound (σ : Subst) (t r : Ty) (σ' : Subst)
    (h : matchTemplate σ t r = some σ') : sub r (instantiate σ' t) = true := by
  unfold matchTemplate at h
  aesop

/-- On a closed template the match is subsumption and the seed. -/
theorem matchTemplate_closed (σ : Subst) (t r : Ty) (h : closed t = true) :
    matchTemplate σ t r = if sub r t then some σ else none := by
  simp only [matchTemplate, infer_closed σ t r h, instantiate_closed σ t h]

end Ty

/-- A closed row types as before the templates: subsumption at the request, its own columns. -/
theorem rowTy_closed (row : Row) (r : Ty) (hreq : row.request.closed = true)
    (hans : row.answer.closed = true) (herr : row.error.closed = true) :
    rowTy row r =
      if Ty.sub r.normalize row.request.normalize then
        some ⟨row.answer.normalize, row.error.normalize, Requirement.ofList row.requires⟩
      else none := by
  simp only [rowTy, Ty.matchTemplate_closed [] _ _ (Ty.closed_normalize _ hreq)]
  split <;> simp only [Option.map_some, Option.map_none, Ty.instantiate_closed _ _ hans,
    Ty.instantiate_closed _ _ herr]

/-- `rowTy_closed`, read off a successful match. -/
theorem rowTy_closed_some {row : Row} {r : Ty} {t : EffTy} (hreq : row.request.closed = true)
    (hans : row.answer.closed = true) (herr : row.error.closed = true)
    (h : rowTy row r = some t) :
    Ty.sub r.normalize row.request.normalize = true ∧
      t = ⟨row.answer.normalize, row.error.normalize, Requirement.ofList row.requires⟩ := by
  rw [rowTy_closed row r hreq hans herr] at h
  aesop

/-- Every native row of this cut is closed: no row is a template yet. -/
theorem NativeOp.row_closed (op : NativeOp) :
    (NativeOp.row op).request.closed = true ∧ (NativeOp.row op).answer.closed = true ∧
      (NativeOp.row op).error.closed = true := by
  cases op with
  | scopeMake strategy => cases strategy <;> exact ⟨rfl, rfl, rfl⟩
  | _ => exact ⟨rfl, rfl, rfl⟩

/-- The native signature's canonical rows are closed. -/
theorem nativeSignature_row_closed (op : NativeOp) :
    (nativeSignature.rowOf op).request.closed = true ∧
      (nativeSignature.rowOf op).answer.closed = true ∧
      (nativeSignature.rowOf op).error.closed = true := by
  show ((nativeRowOf [] op).normalizeTypes).request.closed = true ∧
    ((nativeRowOf [] op).normalizeTypes).answer.closed = true ∧
    ((nativeRowOf [] op).normalizeTypes).error.closed = true
  rw [nativeRowOf_nil]
  exact ⟨Ty.closed_normalize _ (NativeOp.row_closed op).1,
    Ty.closed_normalize _ (NativeOp.row_closed op).2.1,
    Ty.closed_normalize _ (NativeOp.row_closed op).2.2⟩

end Effect4.Program
