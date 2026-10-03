import Effect4.Program.Fold

/-!
# Raw type formation

Rows 192 and 193 require distinct record names and string map keys before a
normalizer can discard syntax. Row templates may defer an open map key until
instantiation. Program annotations cannot defer it. The generated folds collect
raw occurrences; this module supplies their local judgment and located check.

The coordinator places `raw-formation` under decidability of the type algebra.
Its consumers are runtime admission, checked module reading and production, and
checked replay. This judgment says nothing about typing or inhabitance.
-/

namespace Effect4.Program

inductive FormationReason where
  | repeatedField (name : String)
  | mapKey
  deriving DecidableEq, Repr

/-- A refusal retains the raw type; its path ends in a preorder occurrence index. -/
structure FormationRefusal where
  path : List String
  ty : Ty
  reason : FormationReason
  deriving DecidableEq, Repr

namespace Formation

/-- The local formation judgment at one raw type occurrence. -/
def HeadFormed (template : Bool) : Ty → Prop
  | .record fields => (fields.map Prod.fst).Nodup
  | .map key _ => key.normalize = .string ∨ (template = true ∧ key.closed = false)
  | _ => True

instance (template : Bool) (ty : Ty) : Decidable (HeadFormed template ty) := by
  cases ty <;> unfold HeadFormed <;> infer_instance

/-- One raw occurrence and the boundary position that owns it. -/
structure Site where
  path : List String
  template : Bool
  ty : Ty
  deriving DecidableEq, Repr

abbrev Reason := FormationReason
abbrev Refusal := FormationRefusal

/-- A diagnostic reason. Only a failed `HeadFormed` check exposes this result. -/
def reason (ty : Ty) : Reason :=
  match ty with
  | .record fields => .repeatedField ((Field.firstRepeated fields).getD "")
  | _ => .mapKey

/-- Raw occurrences, including the root, collected without normalization. -/
def nodes (ty : Ty) : List Ty := foldMap_ty [] (· ++ ·) ty (fun t => [t])

/-- Attach a stable enclosing boundary path and preorder index to each occurrence. -/
def sites (template : Bool) (path : List String) (ty : Ty) : List Site :=
  (nodes ty).zipIdx.map fun (t, i) => ⟨path ++ ["type", toString i], template, t⟩

/-- The declarative judgment over every raw occurrence in a collection. -/
def Formed (input : List Site) : Prop := ∀ site ∈ input, HeadFormed site.template site.ty

/-- First raw formation failure. Its successful branch retains no normalized replacement. -/
def check : List Site → Option Refusal
  | [] => none
  | site :: rest =>
    if HeadFormed site.template site.ty then check rest
    else some ⟨site.path, site.ty, reason site.ty⟩

/-- Decidability of `raw-formation`; admission certificates consume the forward direction. -/
theorem check_eq_none_iff (input : List Site) : check input = none ↔ Formed input := by
  induction input with
  | nil => exact ⟨fun _ _ h => (nomatch h), fun _ => rfl⟩
  | cons site rest ih =>
    simp only [check, Formed, List.forall_mem_cons] at ih ⊢
    split
    · rename_i h
      exact ⟨fun hr => ⟨h, ih.mp hr⟩, fun hr => ih.mpr hr.2⟩
    · rename_i h
      exact ⟨fun hf => (nomatch hf), fun hf => False.elim (h hf.1)⟩

/-- The three raw columns of every supplied row. Open keys are template positions. -/
def tableSites (table : List Row) : List Site :=
  table.zipIdx.flatMap fun (row, i) =>
    sites true ["table", toString i, "request"] row.request ++
    sites true ["table", toString i, "answer"] row.answer ++
    sites true ["table", toString i, "error"] row.error

/-- Strict checks for the three raw columns after actual template substitution. -/
def instantiatedSites (row : Row) (bindings : Ty.Subst) : List Site :=
  sites false ["row", "request"] (row.request.instantiate bindings) ++
  sites false ["row", "answer"] (row.answer.instantiate bindings) ++
  sites false ["row", "error"] (row.error.instantiate bindings)

/-- The only type annotation stored in an effect node is its iteration cursor. -/
def programSites {Op : Type} (program : Eff Op) : List Site :=
  foldMapAt_eff (M := List Site) [] (· ++ ·) [] program
    (f_eff := fun e path => match e with
      | .iterate (some ty) _ _ _ _ _ =>
        sites false ("program" :: path.map toString ++ ["cursorTy"]) ty
      | _ => [])

/-- The shared raw input of every checked public boundary. -/
def input {Op : Type} (program : Eff Op) (table : List Row) : List Site :=
  tableSites table ++ programSites program

/-- Raw formation of the exact program and table, before typing or printing. -/
def InputFormed {Op : Type} (program : Eff Op) (table : List Row) : Prop :=
  Formed (input program table)

/-- The shared checked boundary; no consumer owns a separate type traversal. -/
def checkInput {Op : Type} (program : Eff Op) (table : List Row) : Option Refusal :=
  check (input program table)

/-- The `raw-formation` claim, used by every checked boundary's certificate. -/
theorem checkInput_eq_none_iff {Op : Type} (program : Eff Op) (table : List Row) :
    checkInput program table = none ↔ InputFormed program table :=
  check_eq_none_iff (input program table)

end Formation
end Effect4.Program
