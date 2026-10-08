module

public meta import Lean
public import Effect4.Schema.FieldRef

/-!
# Schema.FieldRef.Elab — a field reference by name

`field_ref% "taken"` elaborates against an expected type `FieldRef fs t` and writes the
positional reference to the field named `taken` of `fs`. An author names the field; the position
is computed from the schema that owns it, so inserting another field moves the position with it
(overwatch finding OW-03, `docs/research/2026-10-08-seat-MODULES-L3-receipt.md`).

The expected schema determines the field's type, so a caller may leave that type to inference.
Only an unresolved schema postpones name lookup.

It refuses, at the name's syntax:

- an expected type that is not a `FieldRef` (the schema must be known where the name is
  written);
- a schema whose list, names or flags do not reduce to literals;
- a name that no field has, or that two fields have;
- an optional field: a reference names a required one;
- a field whose type is not `t`.

The reference it writes is the stored data, `FieldRef.here` and `FieldRef.there`, so the laws of
`src/Effect4/Laws/Schema/FieldRef.lean` apply unchanged. This module is meta code with no
theorem (decisions row 330, slice L3).
-/

public meta section

namespace Effect4.Schema.FieldRef.Elab

open Lean Meta Elab Term

/-- One field of a schema, as reduced expressions: its name, whether it is optional, its type. -/
structure Entry where
  name : String
  optional : Bool
  type : Expr

/-- Read a reduced Boolean literal. -/
def boolOf? (e : Expr) : MetaM (Option Bool) := do
  let e ← whnf e
  if e.isConstOf ``Bool.true then return some true
  if e.isConstOf ``Bool.false then return some false
  return none

/-- Read a schema's fields, reducing the list one cell at a time, at most `fuel` cells. -/
def entries (fuel : Nat) (e : Expr) : MetaM (Option (List Entry)) := do
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let e ← whnf e
    if e.isAppOfArity ``List.nil 1 then return some []
    unless e.isAppOfArity ``List.cons 3 do return none
    let field ← whnf (e.getArg! 1)
    unless field.isAppOfArity ``Prod.mk 4 do return none
    let rest ← whnf (field.getArg! 3)
    unless rest.isAppOfArity ``Prod.mk 4 do return none
    let .lit (.strVal name) ← whnf (field.getArg! 2) | return none
    let some optional ← boolOf? (rest.getArg! 2) | return none
    let some later ← entries fuel (e.getArg! 2) | return none
    return some ({ name, optional, type := rest.getArg! 3 } :: later)

/-- The positional reference at a position, as syntax. -/
def positional : Nat → MetaM (TSyntax `term)
  | 0 => `(Effect4.Schema.FieldRef.here _ _ _)
  | k + 1 => do `(Effect4.Schema.FieldRef.there _ _ _ $(← positional k))

/-- `field_ref% "name"`: the reference to the required field `name` of the expected schema. -/
syntax (name := fieldRefStx) "field_ref% " str : term

@[term_elab fieldRefStx]
def elabFieldRef : TermElab := fun stx expected? => do
  match stx with
  | `(field_ref% $n:str) =>
    let target := n.getString
    tryPostponeIfNoneOrMVar expected?
    let some expected := expected?
      | throwErrorAt n "field_ref%: the expected type must be a known FieldRef"
    let expected ← whnfR (← instantiateMVars expected)
    unless expected.isAppOfArity ``Effect4.Schema.FieldRef 2 do
      throwErrorAt n "field_ref%: the expected type {expected} is not a FieldRef"
    let schema ← instantiateMVars (expected.getArg! 0)
    let some fields ← entries 4096 schema | do
      if schema.hasExprMVar then tryPostpone
      throwErrorAt n "field_ref%: the schema {schema} does not reduce to a list of literal fields"
    let positions := (List.range fields.length).filter fun i =>
      (fields[i]?.map (·.name)) == some target
    match positions with
    | [] => throwErrorAt n "field_ref%: the schema has no field {target}"
    | [i] =>
      let some entry := fields[i]? | throwErrorAt n "field_ref%: the schema has no field {target}"
      if entry.optional then
        throwErrorAt n "field_ref%: the field {target} is optional; a reference names a required field"
      unless ← isDefEq entry.type (expected.getArg! 1) do
        throwErrorAt n "field_ref%: the field {target} has type {entry.type}, not {expected.getArg! 1}"
      elabTermEnsuringType (← positional i) expected
    | _ => throwErrorAt n "field_ref%: two fields of the schema are named {target}"
  | _ => throwUnsupportedSyntax

end Effect4.Schema.FieldRef.Elab
