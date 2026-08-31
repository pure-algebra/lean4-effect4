import Cas
import Cas.Vectors.Schema
import Cas.Backend.EmitAst
import Gate

/-!
# The wire-mirror emitter — `lake exe emitwire`

Slice 1 of the TypeScript backend (EFFECTS-BACKEND): the effects
package's canonical Effect Schema values become GENERATED. The
registry below lowers the same `Described` codes the schema fixtures
pin, with structural sharing, into one provenance-stamped module.
`--check` is the byte-identity gate.

The generator makes no domain choices: names, order, and doc lines are
registry data; the codes are `Described.code` of the wire structures;
the emitted expressions evaluate on the TypeScript side to schemas whose
native representation bytes the CanonicalSchemaPin suite compares against
the Lean fixtures — generator correctness through independent
evaluation, never self-comparison.
-/

open Cas.Schema Cas.Backend Cas.Backend.Ts

namespace EmitWireMain

/-- The registry: emission order is sharing order — later codes factor
through earlier names. -/
def registry : List (String × String × Ast) := [
  ("refSchema", "One typed reference: expected kind tag and hex address.",
    Described.code (α := Cas.Vectors.Wire.VectorRef)),
  ("nodeSchema", "One node: scalar header fields, hex payload, ordered references.",
    Described.code (α := Cas.Vectors.Wire.VectorNode)),
  ("bindingSchema", "One binding: the Lean-computed address and the node it binds.",
    Described.code (α := Cas.Vectors.Wire.VectorBinding)),
  ("vectorSchema", "A registered conformance vector: metadata plus the store word.",
    Described.code (α := Cas.Vectors.Wire.VectorDocument)),
  ("indexEntrySchema", "One index row: where a fixture lives and what its word binds.",
    Described.code (α := Cas.Vectors.Wire.IndexEntry)),
  ("indexSchema", "The index.json manifest over the Lean vector registry.",
    Described.code (α := Cas.Vectors.Wire.VectorIndex))
]

def decls : List Decl := Id.run do
  let mut env : List (String × Ast) := []
  let mut out : List Decl := []
  for (name, doc, code) in registry do
    out := out ++ [.const { doc := [doc], name, value := constructorExpr env code }]
    env := env ++ [(name, code)]
  return out

/-- The mirror's emitted header. The module declared no version before
this one, so its `schemaVersion` opens at 1. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "emitwire"
  module := "library/cas/tools/EmitWire.lean"

def wireModule : Ts.Module where
  header := [
    "GENERATED — do not edit. The canonical Effect Schema mirrors of the",
    "conformance-vector wire format, lowered from the Lean codes in",
    "`library/cas/Cas/Vectors/Schema.lean` (`Described.code` of the",
    "wire structures) by `lake exe emitwire`; regeneration is",
    "byte-identity-gated (`--check`, wired into `check:cas`). The",
    "CanonicalSchemaPin suite compares their native representation bytes",
    "against the Lean-emitted fixtures — the drift tripwire, now",
    "derived on both sides."
  ] ++ emitted.headerLines
  imports := [
    .named ["Schema"] "effect"
  ]
  decls := decls

def rendered : String := Render.module house0 wireModule

/-- Where the mirror module lives in the effects package — the
registry's own knowledge of its artifact, so no caller has to carry
the path. A positional argument overrides it. -/
def defaultTarget : System.FilePath :=
  "../effects/src/cas/generated/ConformanceVectorSchema.ts"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  return [⟨target.getD defaultTarget, rendered, s!"{registry.length} mirrors"⟩]

end EmitWireMain

def main := Gate.mainAt "lake exe emitwire" EmitWireMain.fixtures
