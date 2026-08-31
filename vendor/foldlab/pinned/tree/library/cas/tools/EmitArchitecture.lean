import Cas.Architecture
import Cas.Backend.Ts
import Gate

/-!
# The architecture emitter — `lake exe emitarchitecture`

R11 applied to the library's SELF-DESCRIPTION. `Cas.foldlabCas` and
`src/cas/Architecture.ts` used to carry the same fifty-seven strings —
every carrier's form and its two homes, every law's meaning and its
capabilities, every backend's meaning and what it provides, and the
capability-matrix pin — in two hand-maintained spellings held together
by one shared pin over a projection that deliberately drops the prose.
The pin could see the matrix and nothing else: two descriptions could
disagree about what `graphVerify` MEANS, or about which order a
backend's capabilities are written in, and every gate in the estate
stayed green.

This tool prints the description into the effects package as data. The
runtime module keeps what is genuinely not data — the Schema of the
description, the service, the layer, the matrix derivation, and the
seam-to-service-key map, which names TypeScript service keys the model
does not carry — and reads the rows from here. `--check` is the
byte-identity gate.

## The capability union is the seam set

`ArchCapability` is emitted as the sorted seam keys rather than as the
three constructors of `Cas.Capability`, because the seam set is what
the model's own theorems quantify over: `lawsNeedOnlySeams` and
`backendsProvideOnlySeams` say every capability that appears anywhere
in the description is a seam. A capability outside the seams would be
one nothing can serve, so the union that types the emitted rows is the
seam column and cannot be anything else.
-/

namespace EmitArchitectureMain

open Cas Cas.Backend.Ts

/-! ## The columns the emitted types are built from -/

/-- Sorted keys — the order both this emitter and the model's own
`capsJson` put capability lists in. -/
private def sortedKeys (xs : List String) : List String :=
  xs.mergeSort fun a b => decide (a ≤ b)

/-- The capability union's members: the seam set, sorted. -/
def seamKeys : List String := sortedKeys (foldlabCas.seams.map Capability.key)

/-- The plane union's members: every plane a law names, deduplicated
and sorted. A plane is not a column of its own in the model — it is
whatever the laws say — so the emitted union is read off them. -/
def planeKeys : List String :=
  sortedKeys ((foldlabCas.laws.map ArchLaw.plane).eraseDups)

-- The two unions are the ones the runtime module's Schema spells: the
-- three seams, and the two planes. A widening in Lean widens these on
-- the next regeneration, and the byte gate says so until it has run.
#guard seamKeys == ["read", "roots", "write"]
#guard planeKeys == ["cas", "server"]

/-- A TypeScript string-literal union over already-quoted members. -/
private def unionOf (members : List String) : String :=
  String.intercalate " | " (members.map fun m => "\"" ++ m ++ "\"")

/-! ## The rows -/

private def capsExpr (cs : List Capability) : Expr :=
  .arr (cs.map fun c => .str c.key)

private def typeRow (t : ArchType) : Expr :=
  .objectML [("form", .str t.form), ("lean", .str t.lean),
    ("name", .str t.name), ("ts", .str t.ts)]

private def lawRow (l : ArchLaw) : Expr :=
  .objectML [("means", .str l.means), ("name", .str l.name),
    ("needs", capsExpr l.needs), ("plane", .str l.plane)]

private def backendRow (b : ArchBackend) : Expr :=
  .objectML [("means", .str b.means), ("name", .str b.name),
    ("provides", capsExpr b.provides)]

/-- The description as one object, in the runtime module's own field
order. Row ORDER is the model's, and it is load-bearing prose order,
not identity: the matrix both sides pin sorts every list it projects,
so a reordering here is a reading change and a pin change is not. -/
private def descriptionExpr : Expr :=
  .objectML [
    ("backends", .arr (foldlabCas.backends.map backendRow)),
    ("laws", .arr (foldlabCas.laws.map lawRow)),
    ("seams", capsExpr foldlabCas.seams),
    ("types", .arr (foldlabCas.types.map typeRow))]

/-! ## The declarations

The row types are raw blocks: they are TypeScript declarations, not
expressions, and the fragment the printer carries is deliberately
expression-only. Their doc comments are the model's own — each one is
the docstring of the `Cas.Architecture` structure it mirrors. -/

private def capabilityBlock : String :=
  "/** One capability of the byte plane — the unit the seams split by.\n" ++
  " * The union IS the seam set: the model's `lawsNeedOnlySeams` and\n" ++
  " * `backendsProvideOnlySeams` say no law needs and no backend\n" ++
  " * provides a capability outside it. */\n" ++
  "export type ArchCapability = " ++ unionOf seamKeys

private def typeRowBlock : String :=
  "/** One carrier of the data vocabulary, with its model and runtime\n" ++
  " * homes. */\n" ++
  "export interface ArchTypeRow {\n" ++
  "  readonly form: string\n" ++
  "  readonly lean: string\n" ++
  "  readonly name: string\n" ++
  "  readonly ts: string\n" ++
  "}"

private def lawRowBlock : String :=
  "/** One law above the seams: what it means, and which capabilities\n" ++
  " * it needs — nothing else about storage. The plane union is read\n" ++
  " * off the laws themselves. */\n" ++
  "export interface ArchLawRow {\n" ++
  "  readonly means: string\n" ++
  "  readonly name: string\n" ++
  "  readonly needs: ReadonlyArray<ArchCapability>\n" ++
  "  readonly plane: " ++ unionOf planeKeys ++ "\n" ++
  "}"

private def backendRowBlock : String :=
  "/** One backend below the seams: which capabilities it provides —\n" ++
  " * dumbness is the absence of anything else to say. */\n" ++
  "export interface ArchBackendRow {\n" ++
  "  readonly means: string\n" ++
  "  readonly name: string\n" ++
  "  readonly provides: ReadonlyArray<ArchCapability>\n" ++
  "}"

private def descriptionBlock : String :=
  "/** The library's shape: data vocabulary, seams, laws, backends. */\n" ++
  "export interface ArchDescription {\n" ++
  "  readonly backends: ReadonlyArray<ArchBackendRow>\n" ++
  "  readonly laws: ReadonlyArray<ArchLawRow>\n" ++
  "  readonly seams: ReadonlyArray<ArchCapability>\n" ++
  "  readonly types: ReadonlyArray<ArchTypeRow>\n" ++
  "}"

private def decls : List Decl := [
  .raw capabilityBlock,
  .raw typeRowBlock,
  .raw lawRowBlock,
  .raw backendRowBlock,
  .raw descriptionBlock,
  .const {
    name := "architecture",
    type := some "ArchDescription",
    doc := ["The value: `@foldlab/cas` — the description `Cas.foldlabCas`",
      "carries, row for row and string for string. `src/cas/Architecture.ts`",
      "lifts it through the description's own Schema; nothing between the",
      "two is retyped."],
    value := descriptionExpr },
  .const {
    name := "capabilityMatrixPin",
    doc := ["The pinned canonical rendering of the load-bearing shared",
      "projection — which capabilities each law needs, each backend",
      "provides, the seam set, and the data-vocabulary names. Both sides",
      "DERIVE the matrix from their own copy of the description and",
      "render it through their own canonical JSON; this is the one",
      "literal they are both held to, and it is emitted from the model's",
      "`Cas.capabilityMatrixPin` so there is no longer a second home to",
      "update."],
    value := .str capabilityMatrixPin }
]

/-- The description's emitted header. The module declared no version
before this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "emitarchitecture"
  module := "library/cas/tools/EmitArchitecture.lean"

private def archModule : Module where
  header := [
    "GENERATED — do not edit. THE ARCHITECTURE, as data: the data",
    "vocabulary with its model and runtime homes, the capability seams,",
    "the laws above them, the backends below them, and the capability",
    "matrix's pinned rendering — emitted from",
    "`library/cas/Cas/Architecture.lean` by `lake exe emitarchitecture`;",
    "regeneration is byte-identity-gated (`--check`, wired into",
    "`check:cas`).",
    "",
    "`src/cas/Architecture.ts` is this file's consumer, and what it adds",
    "is everything here is not: the Schema of the description, the",
    "service and the layer that carry it, the matrix derivation the",
    "pin above is compared against, and the seam-to-service-key map,",
    "which names TypeScript service keys the model does not carry. The",
    "two descriptions used to be two hand-maintained spellings agreeing",
    "only on the matrix — so they could disagree about what a law MEANS",
    "with every gate green. Now there is one."
  ] ++ emitted.headerLines
  imports := []
  decls := decls

def rendered : String := Render.module house0 archModule

/-- Where the description lands in the effects package — the tool's
own knowledge of its artifact, so no caller carries the path. A
positional argument overrides it. -/
def defaultTarget : System.FilePath :=
  "../effects/src/cas/generated/architecture.ts"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  return [⟨target.getD defaultTarget, rendered,
    s!"{foldlabCas.types.length} carriers, {foldlabCas.seams.length} seams, \
{foldlabCas.laws.length} laws, {foldlabCas.backends.length} backends"⟩]

end EmitArchitectureMain

def main := Gate.mainAt "lake exe emitarchitecture" EmitArchitectureMain.fixtures
