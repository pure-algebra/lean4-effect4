import Effect4.Program.Typing.Rules
import Effect4.Program.Fold

/-!
Located reasons for failed record and tuple term typing. The diagnostic fold never returns a type.
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

/-- Why a normalized alternative cannot supply a static tuple position. -/
inductive TupleTypingReason
  | nonTuple (branch : Ty)
  | outOfBounds (arity : Nat)
deriving DecidableEq

/-- A static tuple refusal retains the raw index and its separate term address. -/
structure TupleTermRefusal where
  path : List Nat
  index : Nat
  reason : TupleTypingReason
deriving DecidableEq

/-- Cause and term addresses remain separate for a failed tuple projection. -/
structure TupleCauseRefusal where
  causePath : List Nat
  term : TupleTermRefusal
deriving DecidableEq

/-- The diagnostic fold's alternatives, independent of term acceptance. -/
inductive TermTypingRefusal
  | record (why : RecordTermRefusal)
  | tuple (why : TupleTermRefusal)
deriving DecidableEq

/-- The corresponding diagnostic alternatives inside cause leaves. -/
inductive CauseTypingRefusal
  | record (why : RecordCauseRefusal)
  | tuple (why : TupleCauseRefusal)
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

/-- Explain the first rejected normalized alternative, consulting the actual projection rule. -/
def tupleIndex (target : Ty) (index : Nat) : Option TupleTypingReason :=
  (Ty.members target.normalize).foldr (fun branch rest =>
    if (Tuple.project index branch).isSome then rest else
      match branch with
      | .tuple items => some (.outOfBounds items.length)
      | .prod _ _ => some (.outOfBounds 2)
      | _ => some (.nonTuple branch)) none

private def Carrier : TermFam → Type
  | .term => Term × (Bool → List Nat → Option TermTypingRefusal)
  | .terms => Terms × (Bool → List Nat → Nat → Option TermTypingRefusal)

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
    | some why => some (.record ⟨path, why⟩)
    | none =>
      match inferArgs true values.1 with
      | none => values.2 true path 0
      | some types => (construction fields names types).map (fun why => .record ⟨path, why⟩))
  term_field mode target name := (.field mode target.1 name, fun _ path =>
    match infer false target.1 with
    | none => target.2 false (path ++ [0])
    | some type => (readField mode type name).map (fun why => .record ⟨path, why⟩))
  term_recordSet target name value := (.recordSet target.1 name value.1, fun _ path =>
    match infer false target.1 with
    | none => target.2 false (path ++ [0])
    | some _ => match infer true value.1 with
      | none => value.2 true (path ++ [1])
      | some _ => none)
  term_tupleAt target index := (.tupleAt target.1 index, fun _ path =>
    match infer false target.1 with
    | none => target.2 false (path ++ [0])
    | some type => (tupleIndex type index).map (fun why => .tuple ⟨path, index, why⟩))
  terms_nil := (.nil, fun _ _ _ => none)
  terms_cons head tail := (.cons head.1 tail.1, fun flag path index =>
    match infer flag head.1 with
    | none => head.2 flag (path ++ [index])
    | some _ => tail.2 flag path (index + 1))

/-- Diagnose a failed term. This function never supplies a successful type. -/
def diagnose {Op : Type} (sig : Signature Op) (env : TyEnv) (term : Term) :
    Option TermTypingRefusal :=
  (cata_term (algebra (argTy sig env) (argsTy sig env) sig.constAtom) term).2 false []

/-- Compatibility projection for callers that request record-specific diagnostics. -/
def locate {Op : Type} (sig : Signature Op) (env : TyEnv) (term : Term) :
    Option RecordTermRefusal := do
  match ← diagnose sig env term with
  | .record why => some why
  | .tuple _ => none

private def inCause (path : List Nat) : TermTypingRefusal → CauseTypingRefusal
  | .record why => .record ⟨path, why⟩
  | .tuple why => .tuple ⟨path, why⟩

private def CauseCarrier (_ : CauseTermFam) : Type :=
  CauseTerm × (List Nat → Option CauseTypingRefusal)

private def causeAlgebra (inferCause : CauseTerm → Option Ty) (inferTerm : Term → Option Ty)
    (diagnose : Term → Option TermTypingRefusal) : CauseTermAlgebra CauseCarrier where
  cause_fail term := (.fail term, fun path =>
    match inferTerm term with
    | none => (diagnose term).map (inCause path)
    | some _ => none)
  cause_die term := (.die term, fun path =>
    match inferTerm term with
    | none => (diagnose term).map (inCause path)
    | some _ => none)
  cause_interrupt term := (.interrupt term, fun path => do
    let who ← term
    match inferTerm who with
    | none => (diagnose who).map (inCause path)
    | some _ => none)
  cause_both left right := (.both left.1 right.1, fun path =>
    match inferCause left.1 with
    | none => left.2 (path ++ [0])
    | some _ => right.2 (path ++ [1]))

/-- Diagnose a failed cause while keeping cause and term addresses separate. -/
def diagnoseCause {Op : Type} (sig : Signature Op) (env : TyEnv) (cause : CauseTerm) :
    Option CauseTypingRefusal :=
  (cata_cause (causeAlgebra (causeTy sig env) (termTy sig env) (diagnose sig env)) cause).2 []

/-- Compatibility projection retaining the separate record cause and term addresses. -/
def locateCause {Op : Type} (sig : Signature Op) (env : TyEnv) (cause : CauseTerm) :
    Option RecordCauseRefusal := do
  match ← diagnoseCause sig env cause with
  | .record why => some why
  | .tuple _ => none

end TermRefusal
end Effect4.Program
