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

/-! ## What a row's template may say, and what the guard buys (plan 1.8)

Three properties of the calculus, stated as theorems rather than left in prose.

`templateAdmissible` and `Row.wellScoped` are the two shapes a row's template must have for
inference to mean anything, and both hold of every native row of this cut. `sub_sound` and
`sub_not_complete` are the two halves of what the guard is worth: the order NEVER admits a
value the target would refuse, and it DOES refuse pairs whose value sets agree. A checker
built on it can lose a program, never mistype one — L4's anchored completeness is the
statement that says which programs it loses, and it is not this one.

The predicates are defined here and not in the core because nothing but a proof reads them:
no reader, printer, emitter or codec asks whether a template is admissible. -/

namespace Ty

/-- The parameters a template mentions, in occurrence order. -/
def varsOf : Ty → List Nat
  | .var i => [i]
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _ => []
  | .option t | .list t | .causeOf t | .refOf t => varsOf t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .union a b | .deferredOf a b =>
    varsOf a ++ varsOf b

/-- A template is admissible when no parameter sits under a union head. `infer` walks the
template and the request together and binds at a position; a union is a ROW, whose members
the request may carry in any order and any number, so a parameter inside one names no
position and the guard would be all that decided the match. -/
def templateAdmissible : Ty → Bool
  | .union a b => a.closed && b.closed
  | .option t | .list t | .causeOf t | .refOf t => templateAdmissible t
  | .prod a b | .except a b | .exitOf a b | .fiberOf a b | .deferredOf a b =>
    templateAdmissible a && templateAdmissible b
  | .never | .unknown | .unit | .nat | .int | .string | .bool | .handle _ | .lit _
  | .var _ => true

theorem templateAdmissible_of_closed (t : Ty) (h : closed t = true) :
    templateAdmissible t = true := by
  induction t <;> aesop (add norm simp [closed, templateAdmissible])

theorem varsOf_eq_nil_of_closed (t : Ty) (h : closed t = true) : varsOf t = [] := by
  induction t <;> aesop (add norm simp [closed, varsOf])

end Ty

/-- A row is well scoped when every parameter its answer or its error mentions is one its
request binds. `infer` reads bindings from the request alone (`rowTy`), so a parameter that
appeared only on an answer would be instantiated at nothing and printed back as a `var`. -/
def Row.wellScoped (row : Row) : Bool :=
  (row.answer.varsOf ++ row.error.varsOf).all fun i => row.request.varsOf.contains i

/-- Every native row of this cut has an admissible template. Vacuously, because every row is
closed (`row_closed`) — but the statement is the one that survives step 3 of
`docs/research/2026-09-18-rows-42-43-plan.md`, when the rows stop being closed. -/
theorem NativeOp.row_templateAdmissible (op : NativeOp) :
    (NativeOp.row op).request.templateAdmissible = true ∧
      (NativeOp.row op).answer.templateAdmissible = true ∧
      (NativeOp.row op).error.templateAdmissible = true :=
  ⟨Ty.templateAdmissible_of_closed _ (NativeOp.row_closed op).1,
    Ty.templateAdmissible_of_closed _ (NativeOp.row_closed op).2.1,
    Ty.templateAdmissible_of_closed _ (NativeOp.row_closed op).2.2⟩

/-- Every native row of this cut is well scoped, for the same reason and with the same
future: a row that binds a parameter on its answer without binding it on its request fails
here rather than in the printer. -/
theorem NativeOp.row_wellScoped (op : NativeOp) : (NativeOp.row op).wellScoped = true := by
  simp only [Row.wellScoped, Ty.varsOf_eq_nil_of_closed _ (NativeOp.row_closed op).2.1,
    Ty.varsOf_eq_nil_of_closed _ (NativeOp.row_closed op).2.2, List.append_nil, List.all_nil]

/-- **The order is sound for membership.** Whatever the guard admits, the value really does
inhabit the template's instance: this is `hasTy_sub`, named here as the half of the guard's
worth that a consumer may rely on. -/
theorem sub_sound (a b : Ty) (v : Effect4.Machine.Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true :=
  hasTy_sub a b v allocated hsub hv

/-- **The order is NOT complete for membership**, and the witness is one line of TypeScript:
`Option<number | string>` and `Option<number> | Option<string>` have the same values, and
`sub` refuses the pair because it is structural — the left node is an `option` and the right
one is a row. Anything that reads `sub` as "the value sets are included" is wrong, and this
theorem is what makes that a fact of the tree rather than a caveat in a comment. -/
theorem sub_not_complete :
    (∀ v : Effect4.Machine.Val, Val.hasTy v (.option (.union .nat .string)) = true →
        Val.hasTy v (.union (.option .nat) (.option .string)) = true) ∧
      Ty.sub (.option (.union .nat .string)) (.union (.option .nat) (.option .string))
        = false := by
  refine ⟨fun v hv => ?_, ?_⟩
  · cases v
    case none => rfl
    case some x => exact hv
    all_goals exact Bool.noConfusion hv
  -- `decide` cannot do this: `Ty.sub` is a well-founded recursion and the kernel does not
  -- reduce it. The view's own lemmas do, and each step is one of the order's rules
  · have hsn : Ty.sub .string .nat = false :=
      Ty.sub_eq_false_of_not_sameHead .string .nat rfl rfl rfl rfl rfl
    have hns : Ty.sub .nat .string = false :=
      Ty.sub_eq_false_of_not_sameHead .nat .string rfl rfl rfl rfl rfl
    have hun : Ty.sub (.union .nat .string) .nat = false := by
      rw [Ty.sub_union_left _ _ _ (fun h => Ty.noConfusion h), hsn, Bool.and_false]
    have hus : Ty.sub (.union .nat .string) .string = false := by
      rw [Ty.sub_union_left _ _ _ (fun h => Ty.noConfusion h), hns, Bool.false_and]
    rw [Ty.sub_union_right _ _ _ rfl, Ty.sub_args_option, Ty.sub_args_option]
    simp only [Ty.argsBelow, Ty.args, Ty.Variance.holds, List.zip, List.zipWith,
      List.all_cons, List.all_nil, Bool.and_true, hun, hus, Bool.or_false]

end Effect4.Program
