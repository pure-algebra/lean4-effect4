module

public import Effect4.Program.LayerView

/-!
# Raw type formation

Rows 192 and 193 require distinct record names and string map keys before a
normalizer can discard syntax. A deferred's error column is an error type the error
alphabet admits (`admittedErrTy`), since a deferred fails only with a value `errOf`
carries (decisions rows 42 and 120, the state plan's T3a). Row templates may defer an
open map key or an open error column until instantiation. Program annotations cannot
defer either. A type variable is formed in a template only (decisions row 288, point 6 a):
a row's column may hold a parameter, and a program's annotation may not. A declared service
carrier is no template either: `Effect.service(key)` answers it as it is declared
(`serviceSites`). The generated folds collect raw occurrences; this module supplies their
local judgment and located check.

The coordinator places `raw-formation` under decidability of the type algebra.
Its consumers are runtime admission, checked module reading and production, and
checked replay. This judgment says nothing about typing or inhabitance.
-/

@[expose] public section

namespace Effect4.Program

inductive FormationReason where
  | repeatedField (name : String)
  | mapKey
  /-- A deferred's error column that the error alphabet does not admit (`admittedErrTy`):
  `Deferred.fail` would fail it with a value `errOf` cannot carry (decisions rows 42, 120). -/
  | deferredError
  /-- A type variable outside a template (decisions row 288, point 6 a). A row's column may hold
  a parameter, which the checker instantiates at each use. A program's annotation states a
  program's type, which holds none: the checker would give the program a type that is not
  closed, or close the variable to `never` without a word. The refusal keeps the variable. -/
  | typeVariable
  deriving DecidableEq, Repr

/-- A refusal retains the raw type; its path ends in a preorder occurrence index. -/
structure FormationRefusal where
  path : List String
  ty : Ty
  reason : FormationReason
  deriving DecidableEq, Repr

namespace Formation

/-- The local formation judgment at one raw type occurrence. A type variable is formed in a
template only, so a type whose every occurrence is formed outside a template is closed
(`Formation.closed_of_formed`, `Laws/Program/Typing/Closed.lean`). -/
def HeadFormed (template : Bool) : Ty → Prop
  | .record fields => (fields.map Prod.fst).Nodup
  | .map key _ => key.normalize = .string ∨ (template = true ∧ key.closed = false)
  | .deferredOf _ error => admittedErrTy error = true ∨ (template = true ∧ error.closed = false)
  | .var _ => template = true
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
  | .deferredOf _ _ => .deferredError
  | .var _ => .typeVariable
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

/-- The declared carrier of every service declaration, checked strictly. A carrier is no
template: no use instantiates it, and `Effect.service(key)` answers it as it is declared. So a
type variable in a carrier is refused, and a repeated field name, a map key and a deferred's
error column inside it are checked as an annotation's are (decisions row 288, point 6 a, at a
site that is no template). -/
def serviceSites (services : List (ServiceKey × Ty)) : List Site :=
  services.zipIdx.flatMap fun (entry, i) =>
    sites false ["service", toString i, "carrier"] entry.2

/-- Raw declarations in a term, collected by the generated term fold: a record's fields, and
the accumulator type a list fold states (decisions row 228), as a loop's cursor annotation is a
program annotation. -/
def termAnnotations (path : List String) (term : Term) : List (List String × Ty) :=
  foldMapAt_term [] (· ++ ·) [] term (f_term := fun term pos => match term with
    | .record fields _ _ => [(path ++ ["term"] ++ pos.map toString ++ ["fields"], .record fields)]
    | .fold (some accTy) _ _ _ => [(path ++ ["term"] ++ pos.map toString ++ ["accTy"], accTy)]
    | _ => [])

/-- Cause leaves carry terms too; the generated cause fold retains their order. -/
def causeAnnotations (path : List String) (cause : CauseTerm) : List (List String × Ty) :=
  cata_cause (R := fun _ => List String → List (List String × Ty)) {
    cause_fail := fun term pos => termAnnotations (pos ++ ["fail"]) term
    cause_die := fun term pos => termAnnotations (pos ++ ["die"]) term
    cause_interrupt := fun who pos =>
      who.toList.flatMap (termAnnotations (pos ++ ["interrupt"]))
    cause_both := fun left right pos => left (pos ++ ["left"]) ++ right (pos ++ ["right"])
  } cause path

/-- Read type-bearing leaves from a generated program-family view. An operation argument is
read through the alphabet's own views, at the path segment `op`. Its binder term
(`ScopedOp.term?`) is program syntax that a read-modify-write row runs, so a declaration or a
stated type inside it is an annotation like any other. Its type arguments (`ScopedOp.typeArgs`)
are types the program states, each at the segment `typeArgs` and its position: `Deferred.make<A,
E>()` states two (decisions row 212, the state plan's T5, part B). -/
def argumentAnnotations {Op : Type} [ScopedOp Op] (path : List String) (index : Nat) :
    ArgF Op (EffSelfCarrier Op) → List (List String × Ty)
  | .term term => termAnnotations (path ++ ["argument", toString index]) term
  | .cause cause => causeAnnotations (path ++ ["argument", toString index]) cause
  | .optTerm term => term.toList.flatMap (termAnnotations (path ++ ["argument", toString index]))
  | .optTy ty => ty.toList.map fun t => (path ++ ["cursorTy"], t)
  | .op op => (ScopedOp.term? op).toList.flatMap
      (termAnnotations (path ++ ["argument", toString index, "op"])) ++
    (ScopedOp.typeArgs op).zipIdx.map fun (ty, position) =>
      (path ++ ["argument", toString index, "op", "typeArgs", toString position], ty)
  | _ => []

/-- The generated view supplies every leaf without a second program-constructor match. -/
def nodeAnnotations {Op : Type} [ScopedOp Op] (fam : EffFam) (node : EffSelfCarrier Op fam)
    (path : List Nat) : List (List String × Ty) :=
  ((view fam node).2.zipIdx).flatMap fun (argument, index) =>
    argumentAnnotations ("program" :: path.map toString) index argument

/-- Every raw program annotation. Formation and the integer profile share this collector.
The existing iteration annotation retains its `cursorTy` path. -/
def programAnnotations {Op : Type} [ScopedOp Op] (program : Eff Op) : List (List String × Ty) :=
  foldMapAt_eff [] (· ++ ·) [] program
    (f_eff := nodeAnnotations .eff) (f_stmt := nodeAnnotations .stmt)
    (f_stmts := nodeAnnotations .stmts) (f_effs := nodeAnnotations .effs)
    (f_action := nodeAnnotations .action) (f_layer := nodeAnnotations .layer)
    (f_layers := nodeAnnotations .layers)

/-- Strict raw formation reaches every program annotation, including nested record terms. -/
def programSites {Op : Type} [ScopedOp Op] (program : Eff Op) : List Site :=
  (programAnnotations program).flatMap fun (path, ty) => sites false path ty

/-- The shared raw input of every checked public boundary: the supplied rows' columns, the
declared service carriers, and the program's annotations, in that order. A boundary at a row
table alone declares no carrier: its signature is the native one, whose carriers are built in. -/
def input {Op : Type} [ScopedOp Op] (program : Eff Op) (table : List Row)
    (services : List (ServiceKey × Ty) := []) : List Site :=
  tableSites table ++ (serviceSites services ++ programSites program)

/-- Raw formation of the exact program, table and declared carriers, before typing or
printing. -/
def InputFormed {Op : Type} [ScopedOp Op] (program : Eff Op) (table : List Row)
    (services : List (ServiceKey × Ty) := []) : Prop :=
  Formed (input program table services)

/-- The shared checked boundary; no consumer owns a separate type traversal. -/
def checkInput {Op : Type} [ScopedOp Op] (program : Eff Op) (table : List Row)
    (services : List (ServiceKey × Ty) := []) : Option Refusal :=
  check (input program table services)

/-- The `raw-formation` claim, used by every checked boundary's certificate. -/
theorem checkInput_eq_none_iff {Op : Type} [ScopedOp Op] (program : Eff Op) (table : List Row)
    (services : List (ServiceKey × Ty) := []) :
    checkInput program table services = none ↔ InputFormed program table services :=
  check_eq_none_iff (input program table services)

end Formation
end Effect4.Program
