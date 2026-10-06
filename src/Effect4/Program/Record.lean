module

public import Effect4.Program.Ty
public import Effect4.Program.UnionRule
public import Effect4.Machine.Record

/-! Record type operations over types already computed by the term checker.
Recursive declaration formation is checked before these operations by public admission.
These checks retain original field and supplied-name duplicates before normalization.

The field read and the overwrite read their target member by member: each is a rule of one
record type (`fieldOf`, `setOf`), lifted to every type by `UnionRule.lift`
(`src/Effect4/Program/UnionRule.lean`). The lifted rule reads the target's normal form, asks the
record rule at every union member, and joins the answers. One member that is no fitting record
refuses the target, and `never` answers `never`. -/

@[expose] public section

namespace Effect4.Program.Record

abbrev Fields := List (String × Bool × Ty)

/-- Check supplied argument types against every declared field, including absent fields. -/
def argumentsFit (fields : Fields) (arguments : List (String × Ty)) : Bool :=
  arguments.all (fun argument => (Field.firstOf argument.1 fields).isSome) &&
  fields.all (fun field => match Field.firstOf field.1 arguments with
    | none => field.2.1
    | some actual => Ty.sub actual.normalize field.2.2.normalize)

/-- Check original columns before returning the normalized declared record type. -/
def check (fields : Fields) (presentNames : List String) (argumentTypes : List Ty) : Option Ty := do
  let arguments ← Machine.Record.zipNames presentNames argumentTypes
  if (fields.map Prod.fst).Nodup ∧ presentNames.Nodup ∧ argumentsFit fields arguments = true then
    some (Ty.normalize (.record fields))
  else none

/-- The record-only field rule. Optional mode also accepts required declarations. -/
def fieldOf (optional : Bool) (name : String) : Ty → Option Ty
  | .record fields => do
    let (mayBeAbsent, type) ← Field.firstOf name fields
    if optional then some (.option type)
    else if mayBeAbsent then none else some type
  | _ => none

/-- Join branch results only after every input alternative admits the field operation: the
join of a list of answers (`UnionRule.joinAll`) at types, from `never`. -/
def joinResults (types : List Ty) : Ty := UnionRule.joinAll types

/-- Read a declared field from every normalized record alternative: the record-only field rule,
lifted (`UnionRule.lift`). -/
def fieldType (optional : Bool) (target : Ty) (name : String) : Option Ty :=
  UnionRule.lift (fieldOf optional name) target

/-- The record-only overwrite rule makes the replacement field required. -/
def setOf (name : String) (valueType : Ty) : Ty → Option Ty
  | .record fields => some (Ty.normalize (.record ((name, false, valueType) ::
      fields.filter (fun field => decide (field.1 ≠ name)))))
  | _ => none

/-- Overwrite every record alternative. An unsupported alternative refuses the operation: the
record-only overwrite rule, lifted (`UnionRule.lift`). -/
def setType (target : Ty) (name : String) (valueType : Ty) : Option Ty :=
  UnionRule.lift (setOf name valueType) target

/-- A required literal discriminant, read from the canonical field declarations. -/
def tagOf : Ty → Option String
  | .record fields =>
    match Field.firstOf "_tag" (Ty.canon fields) with
    | some (false, .lit tag) => some tag
    | _ => none
  | _ => none

/-- Whether this record alternative carries the selected literal. -/
def isTag (tag : String) (type : Ty) : Bool :=
  match tagOf type with
  | some actual => decide (actual = tag)
  | none => false

/-- Partition an entire literal-tagged record column; empty sides are bottom. -/
def tagArms (tag : String) (target : Ty) : Option (Ty × Ty) :=
  let members := target.normalize.members
  if members.all (fun type => (tagOf type).isSome) then
    some (Ty.ofMembers (members.filter (isTag tag)),
      Ty.ofMembers (members.filter (fun type => !(isTag tag type))))
  else none

end Effect4.Program.Record
