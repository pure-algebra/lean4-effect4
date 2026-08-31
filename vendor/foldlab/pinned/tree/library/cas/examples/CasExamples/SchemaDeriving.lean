import Cas.Schema.Deriving

/-!
# Schema derivation — ordinary Lean structures on the schema plane

This example is also the acceptance test for `deriving Described`:
field order is canonicalized, optionality is inferred from `Option`,
parameters receive the required `Described` instances, and the generic
codec laws are inherited without per-structure serialization proofs.

Since union stage 2 the same handler covers non-recursive INDUCTIVES,
which derive as Effect-shaped tagged unions: one member per
constructor, each a struct whose first field is the `_tag` literal, the
members ordered by tag, and the mode `oneOf`. The acceptance facts are
the same three — the code is what the design says, the round trip
holds, and encoding is injective — plus the one the union adds: the
generated code is DISCRIMINATED, which is what makes its denotation the
member sum rather than `Empty`.
-/

namespace CasExamples.SchemaDeriving

open Cas.Schema

structure Profile where
  displayName : String
  enabled : Bool
  nickname : Option String
  deriving Described

example : Described.code (α := Profile) =
    .struct [
      ("displayName", false, .str),
      ("enabled", false, .bool),
      ("nickname", true, .str)
    ] := by
  rfl

example (profile : Profile) :
    Described.decode (Described.encode profile) = some profile :=
  Described.decode_encode profile

example {left right : Profile}
    (h : Described.encode left = Described.encode right) : left = right :=
  Described.encode_inj h

structure Box (α : Type) where
  value : α
  deriving Described

example : Described (Box String) := inferInstance

example (box : Box String) :
    Described.decode (Described.encode box) = some box :=
  Described.decode_encode box

/-! ## Constructor alternatives — the tagged union -/

inductive Step where
  | wait
  | move (distance : SafeInt)
  | greet (name : String) (title : Option String)
  deriving Described

/-- The code the handler emits, spelled out: members sorted by tag
(`greet`, `move`, `wait` — NOT the source order), the discriminant
first inside each member, and the mode always written. -/
example : Described.code (α := Step) =
    .union [
      .struct [
        ("_tag", false, .lit (.str "greet")),
        ("name", false, .str),
        ("title", true, .str)
      ],
      .struct [
        ("_tag", false, .lit (.str "move")),
        ("distance", false, .int)
      ],
      .struct [("_tag", false, .lit (.str "wait"))]
    ] .oneOf := by
  rfl

/-- The generated discrimination fact — emitted with the instance, so a
consumer never has to re-derive it. -/
example : Ast.discriminated (Described.code (α := Step)) = true :=
  Step.schemaDiscriminated

example (step : Step) :
    Described.decode (Described.encode step) = some step :=
  Described.decode_encode step

example {left right : Step}
    (h : Described.encode left = Described.encode right) : left = right :=
  Described.encode_inj h

-- The wire shape is Effect's: the member that matched, tag included,
-- with no envelope of the union's own. Checked at elaboration, the way
-- the lane checks every executable claim.
#guard Cas.Json.renderCompact (Described.encode (Step.greet "ada" none))
  == "{\"_tag\":\"greet\",\"name\":\"ada\"}"
#guard Cas.Json.renderCompact (Described.encode Step.wait) == "{\"_tag\":\"wait\"}"

end CasExamples.SchemaDeriving
