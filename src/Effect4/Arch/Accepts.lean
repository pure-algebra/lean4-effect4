import Effect4.Schema.Document

/-!
# Arch.Accepts

Owner: the structural acceptance of a JSON value by a persisted schema — the
Lean face of "this payload is an instance of this schema".

`acceptsShape` decides, by the shape of the representation and the value alone,
whether the value inhabits the schema's *encoded* side: keywords by kind,
literals by value, enums by membership, tuples positionally with a homogeneous
rest, objects by property signature (a missing property is accepted exactly
when optional; an extra key is accepted when the object declares no index
signature, which is `Schema.Struct`'s own default, and otherwise must satisfy
one), unions by `anyOf`/`oneOf`, references through the document's table and
`suspend` through its thunk. Fuel bounds the two non-structural steps.

## What it does not decide, said here

* **Filters.** `checks` are not evaluated: a filter's predicate is host code.
  So this is acceptance of the *shape*; a schema with checks accepts a superset
  here of what rc.112 accepts.
* **Keywords with no JSON inhabitant.** `undefined`, `void`, `bigint`,
  `symbol`, `uniqueSymbol` and a bigint literal are refused: JSON has no such
  value, and the encoded side is JSON here.
* **Declarations and template literals.** Refused until their semantics are
  stated; a `declaration`'s encoded form is the host's, not the shape's.
* **Duplicate keys.** An object with a repeated key is refused outright:
  rc.112 parses it into a map where the earlier binding vanishes
  (`E4-SCHEMA-CE-012`), so nothing about it is shape-decidable.

`Effect4.Schema.Value` owns the relational judgment this approximates; nothing
here is worded as that judgment.
-/

namespace Effect4.Arch

open Effect4

/-- Positional tuple matching: the fixed elements, optional ones allowed to be
absent at the end, then a homogeneous rest. More than one rest representation
(a rest with trailing elements) is outside this checker. -/
def matchElements (accept : Representation → Json → Bool) :
    List Element → List Representation → List Json → Bool
  | [], [], [] => true
  | [], [], _ :: _ => false
  | [], [rest], xs => xs.all (accept rest)
  | [], _ :: _ :: _, _ => false
  | element :: elements, rest, [] =>
    element.isOptional && elements.all (·.isOptional) && decide (rest.length ≤ 1)
  | element :: elements, rest, x :: xs =>
    accept element.type x && matchElements accept elements rest xs

/-- No key twice. -/
def keysUnique : List (String × Json) → Bool
  | [] => true
  | (key, _) :: entries => !(entries.any (·.1 == key)) && keysUnique entries

/-- The name of a property signature, when it is a string key. -/
def propertyName : PropertyKey → Option String
  | .string key => some key
  | _ => none

/-- Structural acceptance under a document's references table, fuel-bounded. -/
def acceptsShape (document : Document) : Nat → Representation → Json → Bool
  | 0, _, _ => false
  | fuel + 1, representation, value =>
    match representation, value with
    | .unknown _ _, _ => true
    | .any _ _, _ => true
    | .never _ _, _ => false
    | .null _ _, .null => true
    | .string _ _, .str _ => true
    | .number _ _, .number _ => true
    | .boolean _ _, .bool _ => true
    | .objectKeyword _ _, .obj _ => true
    | .literal _ _ (.string s), .str t => s == t
    | .literal _ _ (.boolean b), .bool c => b == c
    | .literal _ _ (.number x), .number y => x.bits == y.bits
    | .enum _ _ entries, v =>
      entries.any fun entry =>
        match entry.value, v with
        | .string s, .str t => s == t
        | .number x, .number y => x.bits == y.bits
        | _, _ => false
    | .arrays _ _ elements rest, .arr xs =>
      matchElements (acceptsShape document fuel) elements rest xs
    | .objects _ _ properties indexes, .obj entries =>
      keysUnique entries &&
      properties.all (fun property =>
        match propertyName property.name with
        | some key =>
          match entries.find? (·.1 == key) with
          | some found => acceptsShape document fuel property.type found.2
          | none => property.isOptional
        | none => false) &&
      entries.all (fun entry =>
        properties.any (fun property => propertyName property.name == some entry.1) ||
        indexes.isEmpty ||
        indexes.any (fun index =>
          acceptsShape document fuel index.parameter (.str entry.1) &&
          acceptsShape document fuel index.type entry.2))
    | .union _ _ types .anyOf, v => types.any (fun t => acceptsShape document fuel t v)
    | .union _ _ types .oneOf, v =>
      (types.filter (fun t => acceptsShape document fuel t v)).length == 1
    | .reference key, v =>
      match document.references.find? (·.key == key.value) with
      | some entry => acceptsShape document fuel entry.representation v
      | none => false
    | .suspend _ _ thunk, v => acceptsShape document fuel thunk v
    | _, _ => false

/-- Acceptance of a value by a document's root, at a depth no view here approaches. -/
def accepts (document : Document) (value : Json) : Bool :=
  acceptsShape document 64 document.representation value

end Effect4.Arch
