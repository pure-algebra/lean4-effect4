module

public import Effect4.Program.TyExpand
public import Effect4.Program.Record

/-!
# Program.TyHead — a type's head members under a declaration table, and the readers on them

A declared name is nominal (decisions rows 124, 158 and 401 (1)), read iso-recursively. The
checker reads a declared name by its body where it reads a type by shape. A record field written
at a declared name folds a member of the name's body into it. The order `Ty.sub` does not change.
The plan is `docs/research/2026-10-16-usability-scope/wiring-plan.md`.

* **The head members** (`Ty.headMembers`): a type's union members, with each declared reference
  replaced by its body's head members. It recurses as the checker under a table does
  (`Val.hasTyIn`, `Program/TyDecls.lean`): on the declared names not yet unfolded since the last
  value constructor. So it needs no fuel, and a name met again in one head adds no member.
* **The readers under a table**: the union members `Ty.membersIn`, the lifted rules
  `UnionRule.liftIn` and `UnionRule.extendAllIn`, the field read `Record.fieldTypeIn`, the
  update `Record.setTypeIn` and the tag dispatch `Record.tagArmsIn`.
* **The fold of a written field** (`Record.fieldAdmitsIn`, `Record.argumentsFitIn`,
  `Record.checkIn`): a field written at a declared name takes an argument below the name's
  body. One level: the fold reads the field's own head, and a nested position folds where it is
  written.

Each reader is its table-free original at the empty table by definition: it matches on the table
first, or it is the original's combinator at the table's reader. So a law of the original holds
unchanged wherever the table is empty. The laws are `Laws/Program/TyHead.lean`.
-/

@[expose] public section

namespace Effect4.Program

/-- **The head members** of a type under a table, from the names unfolded so far: each union
member of `t`, with a declared reference that `seen` does not hold replaced by its body's head
members. A reference that `seen` holds adds none: its unfolding returned to it before a value
constructor, as an unguarded table's does. Each member answered is no declared reference. -/
def Ty.headMembers (decls : TyDecls) (seen : List String) (t : Ty) : List Ty :=
  t.members.flatMap fun m =>
    match _h : decls.unfold? m with
    | some (name, body) =>
      if _hs : seen.contains name then [] else Ty.headMembers decls (name :: seen) body
    | none => [m]
termination_by decls.unseen seen
decreasing_by
  exact TyDecls.unseen_cons_lt (TyDecls.body?_of_unfold? _h) (Bool.eq_false_iff.mpr _hs)

/-- **The union members under a table**: the head members of the normal form. At the empty table
they are the normal form's union members, by definition. -/
def Ty.membersIn (decls : TyDecls) (t : Ty) : List Ty :=
  match decls with
  | [] => t.normalize.members
  | _ => Ty.headMembers decls [] t.normalize

namespace UnionRule

variable {α : Type} [Answer α]

/-- **The lifted rule under a table**: the member rule at every union member under the table,
and the join of the answers. At the empty table it is `lift`, by definition. -/
def liftIn (decls : TyDecls) (rule : Ty → Option α) (target : Ty) : Option α :=
  match decls with
  | [] => lift rule target
  | _ => ((Ty.membersIn decls target).mapM rule).map joinAll

/-- The member rule's raw answer first, and the lifted rule under the table elsewhere. At the
empty table it is `extendAll`, by definition. -/
def extendAllIn (decls : TyDecls) (rule : Ty → Option α) (target : Ty) : Option α :=
  match decls with
  | [] => extendAll rule target
  | _ => (rule target).orElse fun _ => liftIn decls rule target

end UnionRule

namespace Record

/-- Read a declared field from every record member under the table. At the empty table it is
`fieldType`. -/
def fieldTypeIn (decls : TyDecls) (optional : Bool) (target : Ty) (name : String) : Option Ty :=
  UnionRule.liftIn decls (fieldOf optional name) target

/-- Overwrite every record member under the table. At the empty table it is `setType`. -/
def setTypeIn (decls : TyDecls) (target : Ty) (name : String) (valueType : Ty) : Option Ty :=
  UnionRule.liftIn decls (setOf name valueType) target

/-- Partition a literal-tagged record column under the table. At the empty table it is
`tagArms`. -/
def tagArmsIn (decls : TyDecls) (tag : String) (target : Ty) : Option (Ty × Ty) :=
  let members := Ty.membersIn decls target
  if members.all (fun type => (tagOf type).isSome) then
    some (Ty.ofMembers (members.filter (isTag tag)),
      Ty.ofMembers (members.filter (fun type => !(isTag tag type))))
  else none

/-- **The fold of a written field**: a field written at `declared` takes an argument of type
`actual` below it in the order, or, where `declared` is a declared name, below the name's body.
At the empty table it is the order alone. -/
def fieldAdmitsIn (decls : TyDecls) (actual declared : Ty) : Bool :=
  match decls with
  | [] => Ty.sub actual.normalize declared.normalize
  | _ => Ty.sub actual.normalize declared.normalize ||
      match decls.unfold? declared.normalize with
      | some (_, body) => Ty.sub actual.normalize body.normalize
      | none => false

/-- Check supplied argument types against every declared field, each by the fold. At the empty
table it is `argumentsFit`. -/
def argumentsFitIn (decls : TyDecls) (fields : Fields) (arguments : List (String × Ty)) : Bool :=
  arguments.all (fun argument => (Field.firstOf argument.1 fields).isSome) &&
  fields.all (fun field => match Field.firstOf field.1 arguments with
    | none => field.2.1
    | some actual => fieldAdmitsIn decls actual field.2.2)

/-- Check a record's columns by the fold before returning its normalized declared type. At the
empty table it is `check`. -/
def checkIn (decls : TyDecls) (fields : Fields) (presentNames : List String)
    (argumentTypes : List Ty) : Option Ty := do
  let arguments ← Machine.Record.zipNames presentNames argumentTypes
  if (fields.map Prod.fst).Nodup ∧ presentNames.Nodup ∧
      argumentsFitIn decls fields arguments = true then
    some (Ty.normalize (.record fields))
  else none

end Record

end Effect4.Program
