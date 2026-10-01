import Effect4.Laws.Schema.Codec
import Effect4.Schema.Bridge

/-!
# Verifier of seat TYPES (formal pass, 2026-10-01): probe C's guard is taken at `N = id`

Research probe, outside every root; nothing imports it.

The seat's probe C (`ExactByImageProbe.lean`, SHA-256 `1d2fb97f…`) proves a generic fact (any
retraction becomes exact modulo `N` when its read is guarded by the writer's image) and then
instantiates it at the codec and at the schema bridge with `N := id`. Its note names the
normalisers `N_J` (object key order) and `N_S` (annotations that do not change decoding), but
neither instance uses them. At `N = id` the guarded read refuses inputs the unguarded read
accepts and the frozen contract requires it to accept:

* `Test/contracts/schema-codec.contract.md`: "Object field order is immaterial". Today's decoder
  reads object fields by name (`Schema/Codec.lean:76-89`, `fields?`), so a key-permuted image
  decodes; the guard at `id` refuses it (tested below).
* `ofSchema` ignores a number's annotations (`Schema/Bridge.lean:83-87`); the guard at `id`
  refuses an annotated image of `nat` that reads back exactly (tested below).

With a key-order normaliser in place of `id` the guard keeps the permuted image and still refuses
the data probe's V2 `Success` image (tested below). So "probe C's guard" is a correct route for
stage 1 only with `N_J`/`N_S` as functions, and `readExact_iff`'s premise (the read is
`N`-invariant) is then owed for each. `readExact` below is copied from probe C §1.
-/

set_option autoImplicit false

namespace Research.TypesVerify.Normaliser

open Effect4 Effect4.Program Effect4.Machine

/-- Copied from probe C §1: the image-checked read. -/
def readExact {A F : Type} [DecidableEq F] (write : A → Option F) (read : F → Option A)
    (N : F → F) (f : F) : Option A :=
  (read f).filter (fun a => decide ((write a).map N = some (N f)))

/-- Probe C's codec instance: `N = id`. -/
def decodeExactId (t : Ty) (j : Json) : Option Val :=
  readExact (Schema.encode t) (Schema.decode t) id j

/-- A top-level key sort: enough for the one-level witnesses below (a real `N_J` recurses). -/
def sortTop : Json → Json
  | .obj es => .obj (es.mergeSort (fun a b => decide (a.1 < b.1) || a.1 == b.1))
  | j => j

/-- The same guard modulo key order. -/
def decodeExactJ (t : Ty) (j : Json) : Option Val :=
  readExact (Schema.encode t) (Schema.decode t) sortTop j

def overlap : Ty := .union (.except .nat .nat) (.exitOf .nat .nat)
def jFailure : Json := .obj [("_tag", .str "Failure"), ("failure", Effect4.Arch.Json.ofNat 1)]
def jFailurePerm : Json := .obj [("failure", Effect4.Arch.Json.ofNat 1), ("_tag", .str "Failure")]
def jSuccess : Json := .obj [("_tag", .str "Success"), ("value", Effect4.Arch.Json.ofNat 1)]

-- tested: the contract's clause holds today; a key-permuted image decodes
#guard Schema.decode overlap jFailurePerm = some (.ctor 0 [.nat 1])
#guard Schema.decode (.except .nat .nat) jFailurePerm = some (.ctor 0 [.nat 1])
-- tested (RED CONTROL): probe C's guard at `N = id` refuses it, at the overlap and at a plain
-- `except`, so taken as written it would break the contract's "field order is immaterial"
#guard decodeExactId overlap jFailurePerm = none
#guard decodeExactId (.except .nat .nat) jFailurePerm = none
-- tested: modulo key order the guard keeps both spellings and still refuses V2's Success image
#guard decodeExactJ overlap jFailurePerm = some (.ctor 0 [.nat 1])
#guard decodeExactJ overlap jFailure = some (.ctor 0 [.nat 1])
#guard decodeExactJ overlap jSuccess = none

/-- Probe C's schema instance: `N = id`. -/
def ofSchemaExactId (r : Representation) : Option Ty :=
  readExact (fun t => some (Schema.Bridge.schema t)) Schema.Bridge.ofSchema id r

/-- `nat`'s image with an (empty) annotation list where `schema` writes `none`. -/
def annotatedNat : Representation :=
  match Schema.Bridge.schema .nat with
  | .number _ checks => .number (some []) checks
  | r => r

-- tested: `ofSchema` reads it as `nat` (annotations are ignored), the guard at `id` refuses it
#guard Schema.Bridge.ofSchema annotatedNat = some .nat
#guard annotatedNat ≠ Schema.Bridge.schema .nat
#guard ofSchemaExactId annotatedNat = none

end Research.TypesVerify.Normaliser
