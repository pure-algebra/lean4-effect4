import Lean.Data.Json
import Conform.Core.Obligation

/-!
# Conform.Model.Container — container models by composition, and the law that was missing

**What it is.** Two halves of one idea, neither of which names a codec class of its own
(Codex's rule, `2026-09-09-type-tooling-design.md` §4: *the first model-building API should use
the exact existing `Image` contract … avoid a parallel codec class with the same meaning*):

* a **plan** — a first-order description of a composed model (`optionOf (optionOf (element
  Nat))`), which a check can read, report and refuse, and
* a **builder** — `Combinators M`, the record of container combinators an element library
  supplies over its own model carrier `M`, and `build`, which turns a plan into a model of
  the type the plan describes, or into `none` at exactly the element the environment lacked.

`Plan.carrier` makes the plan drive the *type*: `build` on `optionOf (listOf (element Nat))`
has type `Option (M (Option (List Nat)))`, so a composed model cannot be built at a type the
plan does not describe, and the `none` is the missing element rather than a wrong model.

`resolve` is the reporting half: it walks the plan against an `Env` and answers the
`Conform.Obligation`s a caller would have to discharge — `representation.image-missing` for an
element with no model, `representation.law-missing` for a combinator the library does not
supply (a sum, in the `Store.Image` library as it stands).

**Depends on.** `Conform.Core.Obligation`, `Lean.Json`. Nothing from this repository's
libraries: the element library reaches it as a `Combinators` record and a `Library` description.

**Properties.**
* **No second codec class.** `Combinators` holds *functions of the caller's own model type*; it
  never declares a model type, a law or an encoding — *by construction*.
* **The plan types the model.** `build`'s result type is `Option (M p.carrier)` — *by
  construction*.
* **A missing combinator is an obligation, not a hole.** `sumOf` is `Option`-valued and
  `resolve` reports its absence with the plan position that needed it — *by construction*.
-/

namespace Conform.Model

open Lean (Name Json)

/-! ## The plan -/

/-- A first-order description of a composed model. -/
inductive Plan where
  /-- An element model the environment supplies, by name. -/
  | element (name : Name)
  | optionOf (inner : Plan)
  | listOf (inner : Plan)
  | pairOf (fst snd : Plan)
  | sumOf (left right : Plan)
deriving Inhabited

namespace Plan

/-- The combinator each node needs from the element library. -/
def combinator : Plan → String
  | .element _ => "element"
  | .optionOf _ => "optionOf"
  | .listOf _ => "listOf"
  | .pairOf _ _ => "pairOf"
  | .sumOf _ _ => "sumOf"

def render : Plan → String
  | .element n => n.toString
  | .optionOf p => "Option (" ++ render p ++ ")"
  | .listOf p => "List (" ++ render p ++ ")"
  | .pairOf a b => "(" ++ render a ++ " × " ++ render b ++ ")"
  | .sumOf a b => "(" ++ render a ++ " ⊕ " ++ render b ++ ")"

/-- The Lean type a plan describes, given the type each element name stands for. -/
def carrier (elem : Name → Type) : Plan → Type
  | .element n => elem n
  | .optionOf p => Option (carrier elem p)
  | .listOf p => List (carrier elem p)
  | .pairOf a b => carrier elem a × carrier elem b
  | .sumOf a b => Sum (carrier elem a) (carrier elem b)

end Plan

/-! ## The builder -/

/-- The container combinators an element library supplies over its own model carrier. This is
a record of the caller's *existing* functions — `Store.Image.option`, `.list`, `.pair` — not a
new class: nothing here declares a model, an encoding or a law. -/
structure Combinators (M : Type → Type) where
  optionOf : {α : Type} → M α → M (Option α)
  listOf : {α : Type} → M α → M (List α)
  pairOf : {α β : Type} → M α → M β → M (α × β)
  /-- `none` when the library has no sum combinator. `Store.Image` has `ctor1`/`ctor2`/`ctor3`
  and `equiv` but no `sum`, so a plan that reaches a `sumOf` node gets an obligation of kind
  `representation.law-missing` rather than a model. -/
  sumOf : Option ({α β : Type} → M α → M β → M (Sum α β)) := none

/-- The model a plan describes, or `none` at the first element the environment lacks (or the
first combinator the library does not supply). -/
def build {M : Type → Type} (C : Combinators M) (elem : Name → Type)
    (models : (n : Name) → Option (M (elem n))) : (p : Plan) → Option (M (p.carrier elem))
  | .element n => models n
  | .optionOf p => (build C elem models p).map C.optionOf
  | .listOf p => (build C elem models p).map C.listOf
  | .pairOf a b => do
    let ma ← build C elem models a
    let mb ← build C elem models b
    pure (C.pairOf ma mb)
  | .sumOf a b =>
    match C.sumOf with
    | none => none
    | some f =>
      match build C elem models a, build C elem models b with
      | some ma, some mb => some (f ma mb)
      | _, _ => none

/-! ## The reporting half -/

/-- What an element library offers, as data a check can read. -/
structure Library where
  name : String
  /-- The combinator names `Combinators` actually supplies. -/
  combinators : List String := ["element", "optionOf", "listOf", "pairOf"]
  /-- The laws every model of this library carries, by name. -/
  laws : List String := ["ofVal_toVal", "ofVal_exact"]
deriving Inhabited

/-- Which element models exist, and which laws each was shown to have. -/
structure Env where
  /-- Element name ↦ the laws that element's model carries. -/
  models : List (Name × List String) := []
deriving Inhabited

/-- What a resolved plan is worth. -/
structure Resolution where
  /-- The combinator chain, as a reader would write it. -/
  expression : String
  /-- The laws the composed model carries: the intersection of the library's laws and every
  element's. -/
  laws : List String
deriving Inhabited

/-- Walk a plan against a library and an environment. Every missing piece is an obligation
naming the plan position that needed it; a plan with no missing piece resolves. -/
def resolve (lib : Library) (env : Env) (subjectPath : List String) (plan : Plan) :
    Resolution × Array Obligation := Id.run do
  let mut obligations : Array Obligation := #[]
  let mut laws : List String := lib.laws
  let rec walk (p : Plan) (path : String) :
      StateM (Array Obligation × List String) String := do
    let c := p.combinator
    unless lib.combinators.contains c do
      modify fun (os, ls) =>
        (os.push
          { kind := "representation.law-missing"
            subject := { kind := "model", path := subjectPath ++ [path] }
            status := .unsupported
            profile := lib.name
            statement := s!"the {lib.name} library supplies no `{c}` combinator, so the model \
of {p.render} cannot be composed from its parts"
            detail := Json.mkObj [("combinator", Json.str c), ("plan", Json.str p.render)] },
         ls)
    match p with
    | .element n =>
      match env.models.find? (·.1 == n) with
      | some (_, ls) =>
        modify fun (os, acc) => (os, acc.filter fun l => ls.contains l)
        return n.toString
      | none =>
        modify fun (os, acc) =>
          (os.push
            { kind := "representation.image-missing"
              subject := { kind := "model", path := subjectPath ++ [path] }
              status := .unproved
              profile := lib.name
              statement := s!"no {lib.name} model for the element {n}"
              detail := Json.mkObj [("element", Json.str n.toString)] }, acc)
        return s!"⟨no model for {n}⟩"
    | .optionOf q => return s!"{lib.name}.option ({← walk q (path ++ ".inner")})"
    | .listOf q => return s!"{lib.name}.list ({← walk q (path ++ ".elem")})"
    | .pairOf a b =>
      return s!"{lib.name}.pair ({← walk a (path ++ ".fst")}) ({← walk b (path ++ ".snd")})"
    | .sumOf a b =>
      return s!"{lib.name}.sum ({← walk a (path ++ ".left")}) ({← walk b (path ++ ".right")})"
  let (expr, (os, ls)) := (walk plan "").run (obligations, laws)
  obligations := os
  laws := ls
  return ({ expression := expr, laws }, obligations)

/-- The obligation kinds this module emits. -/
def registry : Obligation.Registry :=
  [ { id := "representation.image-missing"
      description := "a container model needs an element model that was not supplied" }
  , { id := "representation.law-missing"
      description := "a container model needs a combinator or a law of its element that the \
element library does not supply" } ]

end Conform.Model
