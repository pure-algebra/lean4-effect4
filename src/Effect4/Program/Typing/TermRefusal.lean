import Effect4.Program.Typing.Rules
import Effect4.Program.Fold

/-!
Field-specific reasons for failed record term typing. The diagnostic fold never returns a type.
`argTy` and `argsTy` remain the acceptance rules; the caller invokes this fold only after failure.
Program paths and nested term addresses remain separate data.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- A record typing failure, with the field name when one field caused the failure. -/
inductive RecordTypingReason
  | duplicateDeclaration (name : String)
  | duplicateSupplied (name : String)
  | missingRequired (name : String)
  | unknownSupplied (name : String)
  | fieldNotSubtype (name : String) (actual expected : Ty)
  | columnLengths (names values : Nat)
  | missingReadField (name : String) (branch : Ty)
  | optionalReadField (name : String) (branch : Ty)
  | declarationFormation (why : FormationRefusal)
deriving DecidableEq

/-- An address within a term, followed by its record-specific reason.
Indices count immediate term children: argument positions, target zero, replacement one. -/
structure RecordTermRefusal where
  path : List Nat
  reason : RecordTypingReason
deriving DecidableEq

/-- The address of a cause leaf and the independent address within that leaf's term. -/
structure RecordCauseRefusal where
  causePath : List Nat
  term : RecordTermRefusal
deriving DecidableEq

namespace TermRefusal

/-- Explain a failed declaration using its original names, before normalization. -/
def declaration (fields : Record.Fields) : Option RecordTypingReason :=
  match Field.firstRepeated fields with
  | some name => some (.duplicateDeclaration name)
  | none => (Formation.check (Formation.sites false [] (.record fields))).map
      RecordTypingReason.declarationFormation

/-- Explain the column and field checks after all supplied terms have types. -/
def construction (fields : Record.Fields) (names : List String) (types : List Ty) :
    Option RecordTypingReason :=
  match Machine.Record.zipNames names types with
  | none => some (.columnLengths names.length types.length)
  | some arguments =>
    match Field.firstRepeated arguments with
    | some name => some (.duplicateSupplied name)
    | none =>
      match arguments.find? (fun argument => (Field.firstOf argument.1 fields).isNone) with
      | some argument => some (.unknownSupplied argument.1)
      | none => fields.findSome? fun field =>
        match Field.firstOf field.1 arguments with
        | none => if field.2.1 then none else some (.missingRequired field.1)
        | some actual => if Ty.sub actual.normalize field.2.2.normalize then none
          else some (.fieldNotSubtype field.1 actual field.2.2)

/-- Explain the first unsupported read alternative. A non-record keeps the generic fallback. -/
def readField (mode : FieldReadMode) (target : Ty) (name : String) :
    Option RecordTypingReason :=
  (Ty.members target.normalize).foldr (fun branch rest =>
    match branch with
    | .record fields =>
      match Field.firstOf name fields with
      | none => some (.missingReadField name branch)
      | some (optional, _) =>
        if mode = .required ∧ optional = true then some (.optionalReadField name branch)
        else rest
    | _ => none) none

private def Carrier : TermFam → Type
  | .term => Term × (Bool → List Nat → Option RecordTermRefusal)
  | .terms => Terms × (Bool → List Nat → Nat → Option RecordTermRefusal)

/-- The generated term fold carries its raw node beside a diagnostic computation.
Only failed children are descended into, in the typing rule's order and literal mode. -/
private def algebra (infer : Bool → Term → Option Ty)
    (inferArgs : Bool → Terms → Option (List Ty)) (constAtom : String → Bool) :
    TermAlgebra Carrier where
  term_var level := (.var level, fun _ _ => none)
  term_lit value := (.lit value, fun _ _ => none)
  term_app atom args := (.app atom args.1, fun _ path =>
    args.2 (constAtom atom) path 0)
  term_record fields names values := (.record fields names values.1, fun _ path =>
    match declaration fields with
    | some why => some ⟨path, why⟩
    | none =>
      match inferArgs true values.1 with
      | none => values.2 true path 0
      | some types => (construction fields names types).map (⟨path, ·⟩))
  term_field mode target name := (.field mode target.1 name, fun _ path =>
    match infer false target.1 with
    | none => target.2 false (path ++ [0])
    | some type => (readField mode type name).map (⟨path, ·⟩))
  term_recordSet target name value := (.recordSet target.1 name value.1, fun _ path =>
    match infer false target.1 with
    | none => target.2 false (path ++ [0])
    | some _ => match infer true value.1 with
      | none => value.2 true (path ++ [1])
      | some _ => none)
  terms_nil := (.nil, fun _ _ _ => none)
  terms_cons head tail := (.cons head.1 tail.1, fun flag path index =>
    match infer flag head.1 with
    | none => head.2 flag (path ++ [index])
    | some _ => tail.2 flag path (index + 1))

/-- Diagnose a failed term. This function never supplies a successful type. -/
def locate {Op : Type} (sig : Signature Op) (env : TyEnv) (term : Term) :
    Option RecordTermRefusal :=
  (cata_term (algebra (argTy sig env) (argsTy sig env) sig.constAtom) term).2 false []

private def CauseCarrier (_ : CauseTermFam) : Type :=
  CauseTerm × (List Nat → Option RecordCauseRefusal)

private def causeAlgebra (inferCause : CauseTerm → Option Ty) (inferTerm : Term → Option Ty)
    (diagnose : Term → Option RecordTermRefusal) : CauseTermAlgebra CauseCarrier where
  cause_fail term := (.fail term, fun path =>
    match inferTerm term with
    | none => (diagnose term).map (⟨path, ·⟩)
    | some _ => none)
  cause_die term := (.die term, fun path =>
    match inferTerm term with
    | none => (diagnose term).map (⟨path, ·⟩)
    | some _ => none)
  cause_interrupt term := (.interrupt term, fun path => do
    let who ← term
    match inferTerm who with
    | none => (diagnose who).map (⟨path, ·⟩)
    | some _ => none)
  cause_both left right := (.both left.1 right.1, fun path =>
    match inferCause left.1 with
    | none => left.2 (path ++ [0])
    | some _ => right.2 (path ++ [1]))

/-- Diagnose a failed cause while keeping cause and term addresses separate. -/
def locateCause {Op : Type} (sig : Signature Op) (env : TyEnv) (cause : CauseTerm) :
    Option RecordCauseRefusal :=
  (cata_cause (causeAlgebra (causeTy sig env) (termTy sig env) (locate sig env)) cause).2 []

end TermRefusal
end Effect4.Program
