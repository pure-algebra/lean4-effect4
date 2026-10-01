import Effect4.Laws.Schema.Codec
import Effect4.Schema.Bridge

/-!
# Seat EFFECT, probe 1 (2026-10-01): what the schema bridge and the JSON codec prove and refuse

Run through the one-compiler lock:
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <this file>`.
The `#print axioms` lines report theorems already in the tree. Every `#guard` is a finite probe.
-/

set_option autoImplicit false

namespace DataProbeEffect

open Effect4 Effect4.Program Effect4.Machine

/-! ## 1. The laws the tree already has, and their axioms -/

#print axioms Effect4.Schema.Bridge.ofSchema_schema
#print axioms Effect4.Program.CTy.ofSchema_schema
#print axioms Effect4.Schema.decode_of_encode
#print axioms Effect4.Schema.decode_encode
#print axioms Effect4.Schema.hasTy_decode
#print axioms Effect4.Schema.encode_injective
#print axioms Effect4.Schema.encode_sub

/-! ## 2. A record and a tagged variant are Schema data; `Ty` refuses to read them -/

/-- rc.112 `Schema.Struct({ id: Schema.Number, name: Schema.String })`, as the persisted carrier
(`Schema/Authoring.lean`'s `struct`). -/
def userRep : Representation :=
  Schema.struct [Schema.property "id" Schema.number, Schema.property "name" Schema.string]

/-- p5's `Entry`: `{ _tag: "Deposit"; amount: number } | { _tag: "Withdraw"; amount: number }`. -/
def entryRep : Representation :=
  Schema.variant [("Deposit", [Schema.property "amount" Schema.number]),
                  ("Withdraw", [Schema.property "amount" Schema.number])]

/-- The same record over the one numeric type `Ty` inhabits (`nat`: `Schema.Int` with `≥ 0`). -/
def userNatRep : Representation :=
  Schema.struct [Schema.property "id" (Ty.schema .nat), Schema.property "name" Schema.string]

#guard Ty.ofSchema userRep = none
#guard Ty.ofSchema entryRep = none
#guard Ty.ofSchema userNatRep = none

/-! ## 3. A plain `Schema.Number` has no `Ty`; `nat` refuses numbers rc.112's `Number` admits -/

#guard Ty.ofSchema Schema.number = none
#guard Ty.ofSchema (Ty.schema .nat) = some .nat

/-- JSON `1.5` and `-1`, as binary64 bits. rc.112 `Schema.Number` accepts both
(`vendor/effect-4.0.0-rc.112/src/SchemaAST.ts:1427-1436`, `Predicate.isNumber`). -/
def onePointFive : Json := .number (Float64.ofBits 0x3FF8000000000000)
def minusOne : Json := .number (Float64.ofBits 0xBFF0000000000000)

#guard Schema.decode .nat onePointFive = none
#guard Schema.decode .nat minusOne = none
#guard Schema.decode .nat (Arch.Json.ofNat 7) = some (.nat 7)

/-! ## 4. Retraction is proved (section 1); exactness holds only modulo object-key order -/

def someOne : Val := .some (.nat 1)
def canonical : Json := .obj [("_tag", .str "Some"), ("value", Arch.Json.ofNat 1)]
def reordered : Json := .obj [("value", Arch.Json.ofNat 1), ("_tag", .str "Some")]

#guard Schema.encode (.option .nat) someOne = some canonical
#guard Schema.decode (.option .nat) canonical = some someOne
#guard Schema.decode (.option .nat) reordered = some someOne
#guard reordered ≠ canonical

/-! ## 5. `SchemaError` fits today's error image only as DB-15's tagged pair -/

#guard rawSupportedErrTy (.prod (.lit "SchemaError") .string) = true
#guard supportedErrTy (.prod (.lit "SchemaError") .string) = true
#guard errOf (.list [.str "SchemaError", .str "Expected number, got \"x\""]) =
  .tagged "SchemaError" "Expected number, got \"x\""
-- p2's `NotFound { id: number }` as the nearest pair `Ty` has: refused by the image.
#guard rawSupportedErrTy (.prod (.lit "NotFound") .nat) = false

end DataProbeEffect
