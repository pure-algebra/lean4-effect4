import Effect4.Codegen.SchemaCode
import TypeScript.Render

/-!
# Typed Schema code: finite evaluations and the printer's refusals

The code printer (`Effect4.Codegen.SchemaCode`, CR-4) writes a representation as the Schema
expression an Effect user writes. Each guard below is a finite evaluation that no theorem covers,
or a red control of a refusal. Every pin is the rendered bytes of
`TypeScript.Render.expr TypeScript.house0 0`, inlined in the guard, since a battery definition
over a rendered `String` reaches `Classical.choice`.

That each code builds the Schema whose representation is its input is checked at rc.112, not
here: `make check-schema-codec` compares every generated Schema of the codec corpus with
rc.112's revival of Lean's document (`harness/truth/schema-codec/check.ts`).
-/

namespace Test.Codegen.SchemaCode

open Effect4 Effect4.Program Effect4.Codegen
open TypeScript (house0)
open TypeScript.Render (expr)

/-- A record whose keys need the computed form: one of them is `__proto__`. -/
def protoRecord : Ty :=
  .record [("", false, .string), ("__proto__", false, .nat), ("a-b", false, .bool)]

/-- A string node with one annotation, which the printer refuses. -/
def annotated : Representation := .string (some [⟨"description", .str "a name"⟩]) []

-- A natural is a number with the bridge's two checks, each its own `.check`, in order.
#guard (SchemaCode.ofTy .nat).toOption.map (expr house0 0) =
  some "Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0))"

-- An optional field is under `Schema.optionalKey`, and plain keys stay plain.
#guard (SchemaCode.ofTy (.record [("name", false, .string), ("nickname", true, .option .string)])
    ).toOption.map (expr house0 0) =
  some ("Schema.Struct({ name: Schema.String, " ++
    "nickname: Schema.optionalKey(Schema.Option(Schema.String)) })")

-- A `__proto__` key makes every key computed, so the literal defines the field (row 196).
#guard (SchemaCode.ofTy protoRecord).toOption.map (expr house0 0) =
  some ("Schema.Struct({ [\"\"]: Schema.String, [\"__proto__\"]: " ++
    "Schema.Number.check(Schema.isInt()).check(Schema.isGreaterThanOrEqualTo(0)), " ++
    "[\"a-b\"]: Schema.Boolean })")

-- The defect slot of an exit and of a cause is `Schema.Defect()`.
#guard (SchemaCode.ofTy (.exitOf .bool .string)).toOption.map (expr house0 0) =
  some "Schema.Exit(Schema.Boolean, Schema.String, Schema.Defect())"
#guard (SchemaCode.ofTy (.causeOf .never)).toOption.map (expr house0 0) =
  some "Schema.Cause(Schema.Never, Schema.Defect())"

-- A map is a record of its key and value; an empty tuple is a tuple; a list is an array.
#guard (SchemaCode.ofTy (.map .string .never)).toOption.map (expr house0 0) =
  some "Schema.Record(Schema.String, Schema.Never)"
#guard (SchemaCode.ofTy (.tuple [])).toOption.map (expr house0 0) =
  some "Schema.Tuple([])"
#guard (SchemaCode.ofTy (.list (.except .string .bool))).toOption.map
    (expr house0 0) =
  some "Schema.Array(Schema.Result(Schema.Boolean, Schema.String))"

-- A check the authoring writes prints as rc.112 writes it, a pattern with its flags.
#guard (SchemaCode.code ((Schema.withCheck Schema.string (Schema.Check.pattern "^a" "i")).getD
    Schema.string)).toOption.map (expr house0 0) =
  some "Schema.String.check(Schema.isPattern(new RegExp(\"^a\", \"i\")))"

-- A `oneOf` union carries its mode; an empty union stays a union, as rc.112 keeps it.
#guard (SchemaCode.code (Schema.oneOf Schema.string [Schema.boolean])).toOption.map
    (expr house0 0) =
  some "Schema.Union([Schema.String, Schema.Boolean], { mode: \"oneOf\" })"
#guard (SchemaCode.code (.union none [] [] .anyOf)).toOption.map (expr house0 0) =
  some "Schema.Union([])"

/-! ## Red controls: what the printer refuses, by the node's name -/

-- A `Ref` is a handle, and its declaration has no Schema.
#guard (match SchemaCode.ofTy (.refOf .nat) with | .error why => some why | .ok _ => none) =
  some "the declaration effect/schema/Ref has no Schema code"
-- A host handle neither.
#guard (match SchemaCode.ofTy (.handle "Host.Resource") with
    | .error why => some why | .ok _ => none) =
  some "the declaration Host.Resource has no Schema code"
-- The bridge leaves `number` unlowered (decisions rows 121, 158, 160, 161), so it has no code.
#guard (match SchemaCode.ofTy .number with | .error why => some why | .ok _ => none) =
  some "the declaration effect4/unlowered/number has no Schema code"
-- Annotations are refused, by the node.
#guard (match SchemaCode.code annotated with | .error why => some why | .ok _ => none) =
  some "the keyword String carries annotations, and the code printer writes none"
-- A reference needs a references table.
#guard (match SchemaCode.code (Schema.reference "Person") with
    | .error why => some why | .ok _ => none) =
  some "the reference Person needs a references table, which the printer lacks"
-- A check outside the table, and a known check at another payload, are refused by id.
#guard (match SchemaCode.code ((Schema.withCheck Schema.string (Schema.Check.named "my/check")).getD
      Schema.string) with | .error why => some why | .ok _ => none) =
  some "the check my/check with its payload has no Schema code"
#guard (match SchemaCode.code ((Schema.withCheck Schema.number
      (Schema.Check.named "effect/schema/isInt" (.str "x"))).getD Schema.number) with
    | .error why => some why | .ok _ => none) =
  some "the check effect/schema/isInt with its payload has no Schema code"

end Test.Codegen.SchemaCode
