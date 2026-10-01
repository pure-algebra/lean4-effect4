import Effect4.Schema.Bridge
import Effect4.Schema.Codec
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Admits

/-!
# Verifier of seat EFFECT (2026-10-01): tree facts the seat's findings lean on or missed

Run through the one-compiler lock:
`bash …/scratchpad/serial.sh lake env lean -M6144 -DwarningAsError=true <this file>`.
Every `#guard` is a finite probe against the tree at `ba9783c3` (source as at `bc77e97f`).
The `#print axioms` lines report theorems already in the tree that a record extension must keep.
-/

set_option autoImplicit false

namespace VerifyEffect

open Effect4 Effect4.Program Effect4.Machine

/-! ## 1. `ofSchema` reads a union only when it has exactly two members (EFF-06, §5 "covered today")

rc.112's `Schema.Literals(["a", "b", "c"])` persists as one flat `anyOf` union of three literals.
`Bridge.ofSchema` has one union arm, `.union _ [] [a, b] .anyOf` (`Schema/Bridge.lean`), so a
foreign three-member literal union does not read, while the tree's own (nested binary) image does. -/

def lit2 : Representation :=
  .union none [] [Schema.literalString "a", Schema.literalString "b"] .anyOf
def lit3 : Representation :=
  .union none [] [Schema.literalString "a", Schema.literalString "b", Schema.literalString "c"] .anyOf
def ty3 : Ty := .union (.lit "a") (.union (.lit "b") (.lit "c"))

#guard Ty.ofSchema lit2 = some (.union (.lit "a") (.lit "b"))
#guard Ty.ofSchema lit3 = none
#guard (Ty.ofSchema (Ty.schema ty3)).isSome

/-! ## 2. `ofSchema` does not read annotations, including ones that change rc.112's decode

rc.112 merges `ast.annotations.parseOptions` into the parse options (`SchemaParser.ts:1096-1102`)
and the default formatter reads `identifier` (`verify-ts/verify-parse-options.log`, P4–P6). The
tree's read answers the same `Ty` with or without them, so "exact modulo `stripAnn`" (S-a1)
identifies two schemas rc.112 decodes differently. -/

def strictAnn : Annotations :=
  some [⟨"parseOptions", .obj [("onExcessProperty", .str "error")]⟩]
def identifierAnn : Annotations := some [⟨"identifier", .str "UserId"⟩]

#guard Ty.ofSchema (.string strictAnn []) = some .string
#guard Ty.ofSchema (.string identifierAnn []) = some .string
#guard Ty.ofSchema (.string strictAnn []) = Ty.ofSchema Schema.string

/-! ## 3. The codec's object policy, as the tracked battery already pins it
(`Test/Codegen/SchemaGenerationContract.lean:245-248`, under the owner-approved
`Test/contracts/schema-codec.contract.md:25-28`: "duplicates, missing fields and extra fields
refuse. The decoder's strict field set is narrower than Effect's default excess-property
stripping"). rc.112 refuses the same excess key under `onExcessProperty: "error"`
(`verify-ts/verify-parse-options.log`, P1). -/

#guard Ty.decode (.option .nat) (.obj [("value", Arch.Json.ofNat 7), ("_tag", .str "Some")]) =
  some (.some (.nat 7))
#guard Ty.decode (.option .nat) (.obj [("_tag", .str "Some"), ("_tag", .str "None")]) = none
#guard Ty.decode (.option .nat) (.obj [("_tag", .str "None"), ("extra", .bool true)]) = none

/-! ## 4. A name-keyed record value spelled as DB-15's SQL-row shape is already a member of other
types (EFF-09's recommendation)

`{ a: 1, b: 2 }` as "a canonical list of (name, value) pairs" is the `Val` below. It inhabits
`list (prod string nat)` and `prod (prod string nat) (prod string nat)` today, and the codec writes
it as a JSON array of arrays: nothing in the value says "object". -/

def abPairs : Val := .list [.list [.str "a", .nat 1], .list [.str "b", .nat 2]]

#guard Effect4.Program.Val.hasTy abPairs (.list (.prod .string .nat)) [] = true
#guard Effect4.Program.Val.hasTy abPairs (.prod (.prod .string .nat) (.prod .string .nat)) [] = true
#guard Ty.encode (.list (.prod .string .nat)) abPairs =
  some (.arr [.arr [.str "a", Arch.Json.ofNat 1], .arr [.str "b", Arch.Json.ofNat 2]])

/-! ## 5. `int` is in `Ty`, read from `Schema.Int`, and uninhabited (DI-67): the middle route the
seat's S5 does not list -/

#guard Ty.ofSchema (Ty.schema .int) = some .int
#guard Effect4.Program.Val.hasTy (.nat 1) .int [] = false
#guard Ty.encode .int (.nat 1) = none

/-! ## 6. Laws a record constructor must keep: canonical antisymmetry (DI-15 (3)) and membership
monotone in `sub` (DI-15, boundary decision 4) -/

#print axioms Effect4.Program.Ty.sub_antisymm_canonical
#print axioms Effect4.Program.hasTy_sub

end VerifyEffect
