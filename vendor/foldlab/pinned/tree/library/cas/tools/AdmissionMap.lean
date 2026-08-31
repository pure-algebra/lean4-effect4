import Cas.Schema.AdmissionMap
import Gate

/-!
# The admission-map emitter — `lake exe admissionmap`

Emits `conformance/admission-map.json` — the ACC-1 carrier-adequacy
table, projected from `Cas.Schema.admissionMapV0`. `--check` is the
byte-identity gate.

## The ACC-1 totality check

The document's bytes are a pure projection of the Lean value, and the
value's own guards pin every claim it makes about the CODE. What no
`#guard` can reach is the file on disk: the committed inventory
(`experiments/entity-store-extract/inventory.json`) is the extraction
that enumerates the AST union, and totality is a statement ABOUT it —
every inventory variant has exactly one row, and no row over the AST
union is un-inventoried.

So the check runs here, in `IO`, before the fixture is returned, in
BOTH emit and `--check` mode: the map cannot be regenerated past an
inventory it no longer covers. Failure throws with the offending
variant named.

The reading is textual on purpose. `Cas.Json.parse` accepts exactly
the canonical rendering — no whitespace anywhere — and the inventory
is a pretty-printed extractor artifact, so the house parser refuses
it by design. Counting the extractor's own `"variant": "…"` field is
the narrow reading that needs no second parser: the count fixes the
size of the inventory's variant list, and the per-row count fixes
which names fill it.
-/

namespace AdmissionMapMain

open Cas.Schema

def outPath : System.FilePath := "conformance" / "admission-map.json"

/-- The map's emitted header. `schemaVersion` opens at the `mapVersion`
the document already declares, and that field stays for one release
beside the header that now carries it. -/
def emitted : Gate.Emitted where
  schemaVersion := admissionMapV0.mapVersion
  emitter := "admissionmap"
  module := "library/cas/tools/AdmissionMap.lean"

/-- The committed inventory, relative to `library/cas` (the directory
every `lake exe` in this package runs from). -/
def inventoryPath : System.FilePath :=
  ".." / ".." / "experiments" / "entity-store-extract" / "inventory.json"

/-- How many times a needle occurs in a haystack: one fewer piece than
the split leaves. -/
private def occurrences (haystack needle : String) : Nat :=
  (haystack.splitOn needle).length - 1

private def variantField (name : String) : String :=
  "\"variant\": \"" ++ name ++ "\""

/-- ACC-1: every inventory variant has exactly one row, and the map's
AST keying has exactly the inventory's size. -/
def checkTotality : IO Unit := do
  let text ← try IO.FS.readFile inventoryPath catch _ =>
    throw (IO.userError
      s!"ACC-1: cannot read the committed inventory at {inventoryPath}")
  let names := admissionMapV0.astNames
  for name in names do
    let n := occurrences text (variantField name)
    unless n == 1 do
      throw (IO.userError
        s!"ACC-1: the map rows `{name}` over the AST union, but the \
inventory spells it {n} times — every inventory variant has exactly one row")
  let total := occurrences text "\"variant\": \""
  unless total == names.length do
    throw (IO.userError
      s!"ACC-1: the inventory enumerates {total} variants and the map rows \
{names.length} over the AST union — every inventory variant has exactly one row")

-- The table's projection is an OBJECT, which is where the header goes.
-- `Emitted.onto` passes a non-object through unchanged; this is what
-- makes that arm unreachable here.
#guard match admissionMapV0.toValue with | .obj _ => true | _ => false

/-- The map, headed. The projection is `Cas.Schema`'s, so the header is
prepended to the value rather than spelled into a field list. -/
def document : String :=
  Cas.Json.document (emitted.onto admissionMapV0.toValue)

def fixtures : IO (List Gate.Fixture) := do
  checkTotality
  return [⟨outPath, document,
    s!"{admissionMapV0.rows.length} rows \
({admissionMapV0.count "ADMITTED"} admitted, \
{admissionMapV0.count "DEFERRED"} deferred, \
{admissionMapV0.count "REJECTED"} rejected)"⟩]

end AdmissionMapMain

def main := Gate.main "lake exe admissionmap" AdmissionMapMain.fixtures
