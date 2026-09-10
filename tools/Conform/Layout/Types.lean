import Lean.Data.Json
import Conform.Core.Report
import Conform.Core.Policy

/-!
# Conform.Layout.Types — the three first-order languages a layout check speaks

**What it is.** Three small languages, none of which names anything in this repository:

* `TypeRef` — an applied type spelling (`Option (Option Nat)`), the only way a type reaches a
  check. Parameters are positional.
* `DataValue` — a *source* value: a constructor of a named type applied to argument values,
  plus the three scalar literals. `Option`, `List` and `Prod` are ordinary types here
  (`Option.none`, `List.cons`, `Prod.mk`), so a container needs no special case anywhere.
* `TVal` — a *target* value: what a target's runtime actually holds. `null` is a value of this
  language, which is the whole point: a layout that maps two distinct `DataValue`s to one
  `TVal` is exactly a representation collision, and the collision is exhibited, not asserted.

The constructor information a check needs about the environment (`InductiveVal`,
`ConstructorVal`) reaches it as a `World` of plain `TypeView` records; the reflection that
builds one is `Conform.Layout.Reflect`, and it takes the names as arguments.

**Depends on.** `Lean.Name`, `Lean.Json`, `Conform.Core.Report`. Nothing from this repository's
libraries — the extensibility rule (`docs/research/type-tooling/brief-common.md`).

**Properties.**
* **No partial definitions.** Every recursion over the three nested-inductive languages is
  structural: equality is `deriving BEq` (which does reach through the `List` and the
  `String × _` of `objV`) and `render` is written out in a `mutual` block with its list
  companion, so nothing here is `partial` and nothing is `opaque` — *by construction*.
* **A value renders to exactly one string.** `TVal.render` is total and injective on the shapes
  it is used for in reports; two `DataValue`s that render to the same `TVal` render to the same
  string, which is what a counterexample row prints — *by construction*.
-/

namespace Conform.Layout

open Lean (Name Json ToJson toJson)

/-! ## Types -/

/-- An applied type spelling. `param i` is the `i`-th parameter of the declaration a rule is
stated for; a check that meets one outside a parameterised rule refuses. -/
inductive TypeRef where
  | con (head : Name) (args : List TypeRef)
  | param (index : Nat)
deriving Inhabited, BEq

namespace TypeRef

mutual
/-- `Option (Option Nat)`, with the full head names shortened to their last component. -/
def render : TypeRef → String
  | .con h [] => h.toString
  | .con h args => h.toString ++ " " ++ " ".intercalate (renderArgs args)
  | .param i => s!"?{i}"
def renderArgs : List TypeRef → List String
  | [] => []
  | a :: as => (match a with | .con _ (_ :: _) => "(" ++ render a ++ ")" | _ => render a)
      :: renderArgs as
end

mutual
/-- Whether a spelling still mentions a parameter: a subject that does is not a nesting. -/
def hasParam : TypeRef → Bool
  | .param _ => true
  | .con _ args => hasParamList args
def hasParamList : List TypeRef → Bool
  | [] => false
  | a :: as => hasParam a || hasParamList as
end

/-- The head constant, when there is one. -/
def head? : TypeRef → Option Name
  | .con h _ => some h
  | .param _ => none

def args : TypeRef → List TypeRef
  | .con _ as => as
  | .param _ => []

mutual
/-- Versioned structural encoding. Display text never determines type identity. -/
def encode : TypeRef → Json
  | .con n args => Json.mkObj [("format", .str "conform-type-v1"), ("kind", .str "con"),
      ("name", .str n.toString), ("args", .arr (encodeArgs args).toArray)]
  | .param i => Json.mkObj [("format", .str "conform-type-v1"), ("kind", .str "param"), ("index", toJson i)]
def encodeArgs : List TypeRef → List Json
  | [] => []
  | a :: rest => encode a :: encodeArgs rest
end
instance : ToJson TypeRef := ⟨encode⟩

/-- Bound recursive input before elaboration, with strict unknown-key validation. -/
def readAt : Nat → Json → Conform.Policy.Reader TypeRef
  | 0, _ => Conform.Policy.fail "type nesting limit exceeded"
  | fuel + 1, j => do
    let get ← Conform.Policy.object j ["format", "kind", "name", "args", "index"]
    let format ← Conform.Policy.field get "format" Conform.Policy.string
    unless format == "conform-type-v1" do Conform.Policy.fail "unsupported type format"
    let kind ← Conform.Policy.field get "kind" Conform.Policy.string
    match kind with
    | "con" =>
      let get ← Conform.Policy.object j ["format", "kind", "name", "args"]
      let n ← Conform.Policy.field get "name" Conform.Policy.name
      let args ← Conform.Policy.field get "args" fun a => Conform.Policy.array a (readAt fuel)
      return .con n args.toList
    | "param" =>
      let get ← Conform.Policy.object j ["format", "kind", "index"]
      return .param (← Conform.Policy.field get "index" Conform.Policy.nat)
    | _ => Conform.Policy.fail s!"unknown type kind {kind}"

def reader := readAt 256

mutual
/-- Substitute the parameters of a rule by the arguments of an applied type. -/
def instantiate (subst : List TypeRef) : TypeRef → TypeRef
  | .con h args => .con h (instantiateList subst args)
  | .param i => match subst[i]? with | some t => t | none => .param i
def instantiateList (subst : List TypeRef) : List TypeRef → List TypeRef
  | [] => []
  | a :: as => instantiate subst a :: instantiateList subst as
end

end TypeRef

/-! ## The world: constructor information as plain data -/

/-- One computationally relevant field of one constructor. -/
structure FieldView where
  /-- The binder name, verbatim (`inner`, `left`, `answer`). -/
  name : String
  type : TypeRef
deriving Inhabited

/-- One constructor: its short name, its declaration index, its relevant fields in order. -/
structure CtorView where
  name : String
  index : Nat
  fields : List FieldView
deriving Inhabited

/-- One type constructor: the constructor information a layout check is allowed to see. -/
structure TypeView where
  name : Name
  /-- Parameter names, in order; a field's `TypeRef.param i` refers to position `i`. -/
  params : List String := []
  isStructure : Bool := false
  ctors : List CtorView := []
deriving Inhabited

/-- The closed set of types a run checks over. -/
structure World where
  types : Array TypeView := #[]
  /-- Applied requests stay distinct from the generic declaration registry. -/
  applications : Array TypeRef := #[]
deriving Inhabited

namespace World

def find? (w : World) (n : Name) : Option TypeView := w.types.find? (·.name == n)

def names (w : World) : List Name := w.types.toList.map (·.name)

def ctor? (w : World) (n : Name) (c : String) : Option CtorView := do
  let t ← w.find? n
  t.ctors.find? (·.name == c)

end World

/-! ## Source values -/

/-- A value of a type in the world: a constructor applied to argument values, or a scalar
literal. `Option`, `List` and `Prod` are ordinary types (`Option.none`, `List.cons`,
`Prod.mk`), so no container is a special case of the languages. -/
inductive DataValue where
  | ctor (type : Name) (ctor : String) (args : List DataValue)
  | natLit (n : Nat)
  | strLit (s : String)
  | boolLit (b : Bool)
deriving Inhabited, BEq

namespace DataValue

mutual
/-- The Lean spelling: `Option.some (Option.none)`. -/
def render : DataValue → String
  | .ctor t c [] => t.toString ++ "." ++ c
  | .ctor t c as => t.toString ++ "." ++ c ++ " " ++ " ".intercalate (renderArgs as)
  | .natLit n => toString n
  | .strLit s => toString (Json.str s)
  | .boolLit b => toString b
def renderArgs : List DataValue → List String
  | [] => []
  | a :: as => (match a with | .ctor _ _ (_ :: _) => "(" ++ render a ++ ")" | _ => render a)
      :: renderArgs as
end

/-- The Lean spelling, not the tree: the schema is not the record (as for `TypeRef`). -/
instance : ToJson DataValue := ⟨fun v => Json.str v.render⟩

end DataValue

/-! ## Target values -/

/-- What a target's runtime holds. `null` is a value here: a layout is injective exactly when
no two source values reach the same `TVal`. -/
inductive TVal where
  | null
  | undef
  | boolV (b : Bool)
  | numV (n : Nat)
  | strV (s : String)
  | arrV (xs : List TVal)
  /-- An object: fields in the order the layout writes them. Equality is positional: a layout
  writes a constructor's fields in one order, so two objects that differ only in field order
  came from two different layouts and are not the same layout's value. `sortFields` is the
  normal form a caller applies first when it wants to compare across layouts. -/
  | objV (fields : List (String × TVal))
  /-- A constructor application in the target's own variant language (OCaml `Ty_option t`,
  the canonical wire's `ctor i args`). -/
  | conV (name : String) (args : List TVal)
  | tupV (xs : List TVal)
deriving Inhabited, BEq

namespace TVal

/-- Object fields in key order: two emitters that write the same fields in different orders
hold the same value. -/
def sortFields (fs : List (String × TVal)) : List (String × TVal) :=
  (fs.toArray.qsort (fun a b => a.1 < b.1)).toList

mutual
/-- One unambiguous spelling, used in counterexample rows. -/
def render : TVal → String
  | .null => "null"
  | .undef => "undefined"
  | .boolV b => toString b
  | .numV n => toString n
  | .strV s => toString (Json.str s)
  | .arrV xs => "[" ++ ", ".intercalate (renderList xs) ++ "]"
  | .tupV xs => "(" ++ ", ".intercalate (renderList xs) ++ ")"
  | .conV n [] => n
  | .conV n xs => n ++ " (" ++ ", ".intercalate (renderList xs) ++ ")"
  | .objV fs => "{" ++ ", ".intercalate (renderFields fs) ++ "}"
def renderList : List TVal → List String
  | [] => []
  | x :: xs => render x :: renderList xs
def renderFields : List (String × TVal) → List String
  | [] => []
  | (k, v) :: fs => (k ++ ": " ++ render v) :: renderFields fs
end

/-- The rendered spelling, not the tree: the schema is not the record (as for `TypeRef`). -/
instance : ToJson TVal := ⟨fun v => Json.str v.render⟩

/-- Whether this target value is the target's null. The nullable admissibility condition is
stated over exactly this predicate. -/
def isNull : TVal → Bool
  | .null => true
  | _ => false

end TVal

/-! ## What a check refuses with -/

/-- A refusal of a layout operation: what could not be done, and where. -/
structure Err where
  code : String
  message : String
  path : List String := []
deriving Inhabited

namespace Err

def render (e : Err) : String :=
  (if e.path.isEmpty then "" else "/".intercalate e.path.reverse ++ ": ") ++ e.message

/-- Hand-written, not `deriving ToJson`: `path` is stored innermost-first (`under` conses) and
written outermost-first, so the schema is not the record. -/
def toJson (e : Err) : Json :=
  Json.mkObj [("code", Json.str e.code), ("message", Json.str e.message),
    ("path", Json.arr (e.path.reverse.toArray.map Json.str))]

instance : ToJson Err := ⟨toJson⟩

def under (segment : String) (e : Err) : Err := { e with path := segment :: e.path }

end Err

abbrev LayoutM := Except Err

def refuse {α} (code message : String) : LayoutM α := .error { code, message }

end Conform.Layout
