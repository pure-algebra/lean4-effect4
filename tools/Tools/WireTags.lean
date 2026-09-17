import Lean

/-!
# Tools.WireTags

The one loader of the wire tag assignment, `tools/Effect4Gen/wire-tags.json`. Every Lean tool
that writes or checks canonical bytes reads the assignment through this module: the generator
of Lean codecs, its projection guard, the OCaml and TypeScript emitters, the golden bytes and
the wire manifest.

A wire tag is the number a constructor carries in the canonical bytes. It is not the
constructor's compiled position: a retired constructor leaves a hole, a later declaration
order does not move a tag, and the runtime layout checks keep reading the declaration.

The loader refuses, by name, a file that breaks a rule: an unknown format or key, a tag or a
name given twice inside one family, a listed structure, an active name that is not a declared
constructor, a declared constructor with no active row, a retired name that is still declared.
A family that is not listed carries its declaration positions and has no retired tag.
-/

namespace Tools.WireTags
open Lean

/-- The path of the assignment, relative to the repository root. -/
def path : System.FilePath := "tools/Effect4Gen/wire-tags.json"

def format : String := "effect4-wire-tags-v1"

/-- One family's rows: active and retired constructors by short name, each with its tag. -/
structure Family where
  name : Name
  active : List (String × Nat)
  retired : List (String × Nat)
deriving Inhabited, Repr

/-- The assignment as read from the file, checked for its own consistency. -/
structure Assignment where
  families : List Family
deriving Inhabited, Repr

def Assignment.find? (a : Assignment) (family : Name) : Option Family :=
  a.families.find? (·.name == family)

private def duplicates {α : Type} [BEq α] (xs : List α) : List α :=
  let rec go : List α → List α → List α
    | [], out => out.reverse
    | x :: rest, out => if rest.contains x && !out.contains x then go rest (x :: out) else go rest out
  go xs []

private def readRows (family where_ : String) (j : Json) : Except String (List (String × Nat)) := do
  let obj ← match j with
    | .obj kvs => pure kvs
    | _ => throw s!"wire tags: {family}.{where_} is not an object"
  obj.toList.mapM fun (name, value) =>
    match value.getNat? with
    | .ok tag => pure (name, tag)
    | .error _ => throw s!"wire tags: {family}.{where_}.{name} is not a natural number"

/-- Parse the file's text and check the rules that need no environment. -/
def parse (text : String) : Except String Assignment := do
  let json ← (Json.parse text).mapError fun e => s!"wire tags: {e}"
  let top ← match json with
    | .obj kvs => pure kvs
    | _ => throw "wire tags: the file is not an object"
  for (key, _) in top.toList do
    unless ["format", "comment", "families"].contains key do
      throw s!"wire tags: unknown key {key}"
  unless (top.get? "format") == some (Json.str format) do
    throw s!"wire tags: the format is not {format}"
  let families ← match top.get? "families" with
    | some (.obj kvs) => pure kvs
    | _ => throw "wire tags: families is not an object"
  let rows ← families.toList.mapM fun (family, body) => do
    let fields ← match body with
      | .obj kvs => pure kvs
      | _ => throw s!"wire tags: {family} is not an object"
    for (key, _) in fields.toList do
      unless ["active", "retired"].contains key do
        throw s!"wire tags: {family} has the unknown key {key}"
    let active ← match fields.get? "active" with
      | some j => readRows family "active" j
      | none => throw s!"wire tags: {family} has no active rows"
    let retired ← match fields.get? "retired" with
      | some j => readRows family "retired" j
      | none => throw s!"wire tags: {family} has no retired rows"
    if active.isEmpty then throw s!"wire tags: {family} has no active constructor"
    let all := active ++ retired
    match duplicates (all.map (·.2)) with
    | [] => pure ()
    | tags => throw s!"wire tags: {family} gives the tags {tags} twice"
    match duplicates (all.map (·.1)) with
    | [] => pure ()
    | names => throw s!"wire tags: {family} names {names} twice"
    pure { name := family.toName, active, retired : Family }
  return { families := rows }

/-- Read and parse the assignment. The working directory is the repository root, as it is for
every `lake env lean --run` tool and for every elaborator Lake starts. -/
def load (file : System.FilePath := path) : IO Assignment := do
  let text ← IO.FS.readFile file
  match parse text with
  | .ok a => pure a
  | .error e => throw (IO.userError e)

/-- The short name of a constructor. -/
def shortName (ctor : Name) : String := ctor.componentsRev.head!.toString

/-- The wire tag of every declared constructor of one family, in declaration order. A listed
family is checked against the declaration; an unlisted one carries its positions. -/
def tagsOf (a : Assignment) (family : Name) (isStruct : Bool) (ctors : List Name) :
    Except String (List Nat) :=
  match a.find? family with
  | none => .ok (List.range ctors.length)
  | some row => do
    if isStruct then throw s!"wire tags: {family} is a structure and may not be listed"
    let declared := ctors.map shortName
    for (name, _) in row.active do
      unless declared.contains name do
        throw s!"wire tags: {family}.{name} is active but not a declared constructor"
    for (name, _) in row.retired do
      if declared.contains name then
        throw s!"wire tags: {family}.{name} is retired but still declared"
    declared.mapM fun name =>
      match row.active.lookup name with
      | some tag => pure tag
      | none => throw s!"wire tags: {family}.{name} is declared but has no active tag"

/-- `tagsOf` against an environment: the family's constructors are read from its declaration. -/
def tagsIn (a : Assignment) (env : Environment) (family : Name) : Except String (List Nat) :=
  match env.find? family with
  | some (.inductInfo info) => tagsOf a family (isStructure env family) info.ctors
  | _ => .error s!"wire tags: {family} is not an inductive family"

/-- Every family the caller requires must be listed: the program world has no silent default. -/
def requireListed (a : Assignment) (families : List Name) : Except String Unit :=
  match families.filter fun f => (a.find? f).isNone with
  | [] => .ok ()
  | missing => .error s!"wire tags: the families {missing} are not listed"

/-- Every listed family must be one the caller knows: a misspelt family name is refused. -/
def requireKnown (a : Assignment) (env : Environment) : Except String Unit :=
  match a.families.filter fun f => !(env.contains f.name) with
  | [] => .ok ()
  | unknown => .error s!"wire tags: the listed families {unknown.map (·.name)} are not declared"

end Tools.WireTags
