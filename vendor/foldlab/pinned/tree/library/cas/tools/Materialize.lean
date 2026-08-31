import Cas
import Cas.Backend.EmitAst
import Gate

/-!
# The estate-native materializer — `lake exe materialize`

THE SECOND REGISTER of the P6 differential (SCHEMA-MATERIALIZATION.md
ruling-queue item 18). `Cas.Materialize.source` on the TypeScript side
prints a materialized schema through Effect's own
`SchemaRepresentation.toCodeDocument`; this tool prints the SAME stored
node through the estate's own printer (`Cas/Backend/EmitAst.lean` for
the lowering, `Cas/Backend/Ts.lean` for the layout). Two independent
generators, one denotation — and the vitest differential
(`test/MaterializeDifferential.test.ts`) is what holds them to it, by
EVALUATING both modules and comparing schemas, never by comparing
source text.

The tool materializes FROM STORE CONTENT, exactly as the TypeScript
door does. It reads the committed payload bytes under `schemas/` and
recovers the code through `Cas.Schema.ingestBytes` — the bytes-in door
(`parse` composed with `ingest`) — so nothing here re-elaborates the
Lean registry and a payload the door refuses stops the emission by
name. The provenance stamp is the address `schemas/addresses.json`
pins, read rather than recomputed: one file owns that identity.

`lake exe materialize` regenerates every registered fixture (`--all` is
the same thing said out loud); a bare fixture name emits just that one.
`--check` is the byte-identity gate, wired into `check:cas`. Run from
the package root (`library/cas`).
-/

open Cas Cas.Schema Cas.Backend Cas.Backend.Ts

namespace MaterializeMain

/-! ## Reading the committed schema directory -/

def schemaDir : System.FilePath := "schemas"

/-- Where the materialized estate modules live: inside the effects
package's test tree, so the existing `tsc -p tsconfig.test.json
--noEmit` pass typechecks generated output as a matter of course —
the compile gate of ruling-queue item 17, paid for by placement. -/
def outDir : System.FilePath :=
  "../effects/test/generated/materialized/estate"

private def field? (v : Json.Value) (key : String) : Option Json.Value :=
  match v with
  | .obj fs => (fs.find? (·.1 == key)).map (·.2)
  | _ => none

private def asStr? : Json.Value → Option String
  | .str s => some s
  | _ => none

private def asArr? : Json.Value → Option (List Json.Value)
  | .arr xs => some xs
  | _ => none

/-- The strict door parses CANONICAL bytes and nothing else
(`Json.parse_sound`: every accepted document IS the canonical rendering
of the value it answers), and the committed MANIFESTS are pretty-printed
for a reader. This drops the insignificant whitespace between tokens and
touches nothing else: inside a string literal every character is copied
verbatim, escapes included. The schema PAYLOADS need no such pass — they
are already `renderCompact` output, which is what the door speaks. -/
private def compactGo : Bool → Bool → List Char → List Char
  | _, true, c :: cs => c :: compactGo true false cs
  | true, false, c :: cs =>
    if c == '\\' then c :: compactGo true true cs
    else if c == '"' then c :: compactGo false false cs
    else c :: compactGo true false cs
  | false, false, c :: cs =>
    if c == '"' then c :: compactGo true false cs
    else if c == ' ' || c == '\n' || c == '\t' || c == '\r' then
      compactGo false false cs
    else c :: compactGo false false cs
  | _, _, [] => []

private def compactJson (s : String) : String :=
  String.ofList (compactGo false false s.toList)

private def readJson (path : System.FilePath) : IO Json.Value := do
  let text ← IO.FS.readFile path
  match Json.parse (compactJson text) with
  | some v => pure v
  | none => throw (IO.userError s!"{path} is not canonical JSON")

/-- The refusal names, verbatim from the door's taxonomy — the same
words `lake exe verdicts` writes into the conformance corpus. -/
private def refusalName : IngestRefusal → String
  | .notASchema => "notASchema"
  | .illFormed => "illFormed"
  | .wrongRevision => "wrongRevision"
  | .nonEmptyReferences => "nonEmptyReferences"
  | .unguardedCycle => "unguardedCycle"
  | .unknownDeclaration => "unknownDeclaration"

/-- One registered fixture, as this tool needs it: the registry name,
the TypeScript binding it exports, the address that stamps it, and the
code recovered from the committed bytes. -/
structure Row where
  name : String
  binding : String
  address : String
  code : Ast

/-- `union-pin` ⇒ `unionPin`. The same transliteration the TypeScript
suite applies to the same registry, so a binding name is a fact about
the fixture name and not about who spelled it. -/
def bindingName (name : String) : String :=
  match name.splitOn "-" with
  | [] => name
  | first :: rest =>
    first ++ String.join (rest.map fun word =>
      match word.toList with
      | [] => ""
      | c :: cs => String.singleton c.toUpper ++ String.ofList cs)

/-- The registry, read from the committed manifest and address file and
materialized through the bytes door. Order is `index.json`'s order,
which is `tools/Schemas.lean`'s registry order. -/
def loadRows : IO (List Row) := do
  let index ← readJson (schemaDir / "index.json")
  let addresses ← readJson (schemaDir / "addresses.json")
  let some (rows : List Json.Value) := (field? index "schemas").bind asArr?
    | throw (IO.userError "schemas/index.json has no schemas array")
  let some (addressRows : List Json.Value) :=
      (field? addresses "schemas").bind asArr?
    | throw (IO.userError "schemas/addresses.json has no schemas array")
  rows.mapM fun row => do
    let some name := (field? row "name").bind asStr?
      | throw (IO.userError "schemas/index.json row has no name")
    let some file := (field? row "file").bind asStr?
      | throw (IO.userError s!"schemas/index.json row {name} has no file")
    let some addressRow := addressRows.find? fun a =>
        (field? a "name").bind asStr? == some name
      | throw (IO.userError s!"schemas/addresses.json pins no address for {name}")
    let some address := (field? addressRow "address").bind asStr?
      | throw (IO.userError s!"schemas/addresses.json row {name} has no address")
    let payload ← IO.FS.readFile (schemaDir / file)
    match ingestBytes payload with
    | .ok code =>
      pure { name, binding := bindingName name, address, code }
    | .error refusal =>
      throw (IO.userError
        s!"schemas/{file} is refused by the ingestion door: {refusalName refusal}")

/-! ## The emitted module -/

/-- Does the lowering reach the estate's own reference codec? Only then
does the module import it — an unused import is a lie about what the
generated file depends on. -/
private def mentionsCanonicalSchema (rendered : String) : Bool :=
  (rendered.splitOn "CanonicalSchema.").length > 1

/-- The reference codec's home, spelled relative to the emitted module
(`test/generated/materialized/estate/<name>.ts`). -/
def canonicalSchemaPath : String := "../../../../src/cas/CanonicalSchema.ts"

/-- The lane's emitted header, shared by every materialized module and
the barrel. The modules declared no version before this one, so their
`schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "materialize"
  module := "library/cas/tools/Materialize.lean"

def moduleOf (row : Row) : Ts.Module :=
  let value := constructorExpr [] row.code
  let rendered := Render.expr house0 0 value
  { header := [
      "GENERATED — do not edit. The ESTATE-NATIVE materialization of the",
      s!"canonical schema node `{row.name}`, lowered from its committed",
      s!"payload (`library/cas/schemas/{row.name}.json`) by",
      "`lake exe materialize` through the estate's own printer",
      "(`Cas/Backend/EmitAst.lean`, `Cas/Backend/Ts.lean`); regeneration",
      "is byte-identity-gated (`--check`, wired into `check:cas`).",
      "",
      "This is the SECOND REGISTER of the P6 differential:",
      "`Cas.Materialize.source` prints the same node through Effect's own",
      "`toCodeDocument`, and MaterializeDifferential asserts the two",
      "modules EVALUATE to one schema. The two texts legitimately differ",
      "in spelling; the denotation is the identity.",
      "",
      s!"Materialized from a schema node (kind tag 0x{Nat.toDigits 16 schemaKindTag.toNat |> String.ofList}):",
      s!"  - {row.binding} — {row.address}"
    ] ++ emitted.headerLines,
    imports :=
      [.named ["Schema"] "effect"] ++
        (if mentionsCanonicalSchema rendered then
          [.all "CanonicalSchema" canonicalSchemaPath] else []),
    decls := [.const {
      doc := [s!"The canonical code stored at `{row.address}`."],
      name := row.binding,
      value }] }

/-- The barrel: what makes the differential's coverage a fact about the
registry rather than about which imports someone remembered to write.
Its bytes go red the moment a fixture is added or removed. -/
def indexModule (rows : List Row) : Ts.Module where
  header := [
    "GENERATED — do not edit. The estate-native materialized modules,",
    "one export per registered canonical-schema fixture, emitted by",
    "`lake exe materialize`; regeneration is byte-identity-gated",
    "(`--check`, wired into `check:cas`).",
    "",
    "The differential suite reads the registry through this barrel, so",
    "a fixture that gains or loses a module moves these bytes."
  ] ++ emitted.headerLines
  imports := []
  decls := [.raw (String.intercalate "\n" (rows.map fun row =>
    "export { " ++ row.binding ++ " } from \"./" ++ row.name ++ ".ts\""))]

def moduleFixture (row : Row) : Gate.Fixture :=
  { path := outDir / (row.name ++ ".ts"),
    content := Render.module house0 (moduleOf row),
    label := s!"estate materialization of {row.name}" }

def indexFixture (rows : List Row) : Gate.Fixture :=
  { path := outDir / "index.ts",
    content := Render.module house0 (indexModule rows),
    label := s!"{rows.length} materialized modules" }

def fixtures (selected : Option String) : IO (List Gate.Fixture) := do
  let rows ← loadRows
  match selected with
  | none => return rows.map moduleFixture ++ [indexFixture rows]
  | some name =>
    match rows.find? (·.name == name) with
    | some row => return [moduleFixture row]
    | none =>
      throw (IO.userError
        s!"no registered schema fixture named {name}; \
registered: {String.intercalate ", " (rows.map (·.name))}")

end MaterializeMain

def main := Gate.mainSelect "lake exe materialize" MaterializeMain.fixtures
