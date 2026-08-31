import Cas.Lift.Taxonomy
import Cas.Values.Markdown

/-!
# The lift manifest — the v0 rule set as data

The interchange document of the effect-lift lane (R11: one manifest
owns the protocol, both language surfaces generated from it). The
authority INVERTED here 2026-08-28 per the library-graduation design:
this data replaces the hand-authored `manifest.json` as the source,
value-identical under the canonical encoding, with layout moving to
the house manifest printer (`Cas.Json.render`) in the same act.

Every ruled constant of the differential-testing rulings lives here:
rule enables, `candidateDepthMax` (R4), `natBits` and the canonical
natural pattern (R6), the payload hex domain (R7), the pinned detail
strings (R1/R2/R6/R7), and the declared-unreachable codes with their
revival conditions (R9). Engines consume this data; none of them may
hard-code a choice it makes.
-/

namespace Cas.Lift

/-- One recognition rule row: identity, register, syntactic scope,
whether v0 enables it, and its plain-language meaning. -/
structure Rule where
  name : String
  register : String
  scope : String
  enabled : Bool
  description : String

/-- One element of the recognized Effect-TS surface: its name, its
concrete syntax, and its plain-language meaning. The element table is
the DSL's semantic dictionary — what a lifted program MEANS, element
by element — and every projection (manifest JSON, the human Markdown,
generated schema annotations) draws from these rows. -/
structure Element where
  name : String
  spelling : String
  description : String

/-- A declared-unreachable code and what revives it (ruling R9). -/
structure Unreachable where
  code : RefusalCode
  revival : String

/-- The manifest: the whole protocol of the lift, as data. -/
structure Manifest where
  manifestVersion : Nat
  language : String
  pins : List (String × String)
  rules : List Rule
  candidateDepthMax : Nat
  natBits : Nat
  natLiteralPattern : String
  payloadHexPattern : String
  details : List (String × String)
  unreachableV0 : List Unreachable
  elements : List Element

/-- v0 — data verbatim from the frozen hand-authored manifest
(authority inversion; value-parity is the freeze gate). The form
register (F1–F4, ruled) lands as revision 1 through the sieve-first
architecture, not before. -/
def manifestV0 : Manifest where
  manifestVersion := 0
  language := "cas-libfree"
  pins := [
    ("compilerLeg", "typescript@5.9.2"),
    ("oxcLeg", "oxlint@1.80.0 + effect-oxlint@0.3.4 (mpsuesser/effect-oxlint @ d8c892f4)"),
    ("effect", "4.0.0-rc.112 (rule-authoring dependency; recognition is version-neutral by import resolution)")
  ]
  rules := [
    { name := "program-decl", register := "R-GEN", scope := "declaration", enabled := true,
      description := "Recognize a candidate store-program declaration (the program frame)." },
    { name := "const-yield-put", register := "R-GEN", scope := "statement", enabled := true,
      description := "Recognize one binding step: const answer = yield* store.put(node)." },
    { name := "node-literal", register := "R-GEN", scope := "expression", enabled := true,
      description := "Recognize the closed node-literal shape of a put argument." },
    { name := "answer-ref", register := "R-GEN", scope := "expression", enabled := true,
      description := "Resolve each ref name to the index of an earlier answer." },
    { name := "return-word", register := "R-GEN", scope := "statement", enabled := true,
      description := "Recognize the final return as the dense, ordered answer array." },
    { name := "hex-helper", register := "R-GEN", scope := "declaration", enabled := false,
      description := "Pin the in-file hex helper (disabled in v0: lifts carry helperUnpinned instead)." },
    { name := "const-yield-load", register := "R-GEN", scope := "statement", enabled := false,
      description := "Recognize a load binding (disabled: load is not yet documented)." },
    { name := "body-partition", register := "R-GEN", scope := "body", enabled := true,
      description := "Partition the generator body into binding steps and the final return." }
  ]
  candidateDepthMax := 64
  natBits := 32
  natLiteralPattern := "^(0|[1-9][0-9]*)$"
  payloadHexPattern := "^([0-9a-f]{2})*$"
  details := [
    ("payloadNotHexCall", "payload is not hex(\"…\")"),
    ("payloadNotStringLiteral", "payload argument is not a plain string literal"),
    ("payloadHexDomain", "payload hex is not lowercase even-length"),
    ("optionalChain", "optional chain in the spine"),
    ("natNotLiteral", "{role} is not a numeric literal"),
    ("natNotCanonical", "{role} is not canonical decimal"),
    ("natOutOfRange", "{role} does not fit {bits} bits")
  ]
  unreachableV0 := [
    { code := .refForward,
      revival := "a two-pass binder walk (v0 resolves refs against earlier binders only)" },
    { code := .importOpaque,
      revival := "import-form rules (v0 admits every effect-module binding form alike)" },
    { code := .helperUnpinned,
      revival := "Rule 7 landing (hex pinning is disabled; the Lift carries a boolean instead)" }
  ]
  elements := [
    { name := "program-frame",
      spelling := "export const p = (store) => E.gen(function* () { … })",
      description := "A store program: an exported constant holding an Effect generator over its capabilities — in v0, exactly one, the store. Everything the program does is listed in its body, one step per line." },
    { name := "store-binder",
      spelling := "(store)",
      description := "The store capability, bound as the program's parameter. In v0 it is the only capability the grammar recognizes — a staging choice, not language law: the model composes effect signatures by sum, and multi-capability frames are the manifest's largest planned growth (the wild census's top refusal bucket)." },
    { name := "binding",
      spelling := "const a = yield* store.put(node)",
      description := "One program step: perform a store operation and bind its answer to a name. Steps run top to bottom." },
    { name := "put-op",
      spelling := "store.put(node)",
      description := "Admit one node into the store. The answer is the node's content address; admitting the same node twice answers the same address." },
    { name := "node-literal",
      spelling := "{ kind, payload, refs }",
      description := "The node being admitted: what kind it is, its opaque payload bytes, and its references to nodes admitted earlier." },
    { name := "kind-version",
      spelling := "version: 0",
      description := "The kind's schema version — a canonical decimal natural that fits 32 bits." },
    { name := "kind-tag",
      spelling := "tag: 71",
      description := "The kind's wire tag — which sort of node this is — a canonical decimal natural that fits 32 bits." },
    { name := "payload-hex",
      spelling := "payload: hex(\"ff\")",
      description := "The payload bytes, spelled in lowercase even-length hex. The program never interprets them." },
    { name := "ref",
      spelling := "{ id: a, expectedTag: 71 }",
      description := "A reference to an earlier answer by its bound name, carrying the kind tag the referenced node is expected to have." },
    { name := "return-word",
      spelling := "return [a, b]",
      description := "The program's result: exactly the bound answers, in order. This is the run's word — the observation every realization is judged by." }
  ]

/-- The manifest as a JSON value (keys sort at render, per the house
printer). -/
def Manifest.toValue (m : Manifest) : Cas.Json.Value :=
  .obj [
    ("manifestVersion", .nat m.manifestVersion),
    ("language", .str m.language),
    ("pins", .obj (m.pins.map fun (k, v) => (k, .str v))),
    ("rules", .arr (m.rules.map fun r => .obj [
      ("name", .str r.name),
      ("register", .str r.register),
      ("scope", .str r.scope),
      ("enabled", .bool r.enabled),
      ("description", .str r.description)])),
    ("candidateDepthMax", .nat m.candidateDepthMax),
    ("natBits", .nat m.natBits),
    ("natLiteralPattern", .str m.natLiteralPattern),
    ("payloadHexPattern", .str m.payloadHexPattern),
    ("details", .obj (m.details.map fun (k, v) => (k, .str v))),
    ("unreachableV0", .arr (m.unreachableV0.map fun u => .obj [
      ("code", .str u.code.wire),
      ("revival", .str u.revival)])),
    ("elements", .arr (m.elements.map fun e => .obj [
      ("name", .str e.name),
      ("spelling", .str e.spelling),
      ("description", .str e.description)]))
  ]
open Cas.Values.Markdown

/-- The human projection of the manifest (P4): generated beside the
JSON by `lake exe emitlift`, never hand-maintained, byte-gated like
its sibling. -/
def Manifest.toMarkdown (m : Manifest) : String :=
  render [
    .h1 s!"effect-lift manifest v{m.manifestVersion}",
    .p [.text "GENERATED — projection of ", .code "Cas.Lift.manifestV0",
        .text " by ", .code "lake exe emitlift", .text "; do not edit."],
    .p [.text "Language: ", .code m.language],
    .h2 "Pins",
    .table {
      headers := #v["pin", "value"]
      rows := m.pins.map fun (k, v) => #v[⟨[.code k]⟩, ⟨[.code v]⟩] },
    .h2 "The language, element by element",
    .table {
      headers := #v["element", "spelling", "meaning"]
      rows := m.elements.map fun e =>
        #v[⟨[.code e.name]⟩, ⟨[.code e.spelling]⟩, ⟨[.text e.description]⟩] },
    .h2 "Rules",
    .table {
      headers := #v["rule", "scope", "enabled", "meaning"]
      rows := m.rules.map fun r =>
        #v[⟨[.code r.name]⟩, ⟨[.text r.scope]⟩,
           ⟨[.text (if r.enabled then "yes" else "no")]⟩,
           ⟨[.text r.description]⟩] },
    .h2 "Constants",
    .ul [
      [.text s!"candidate depth max: {m.candidateDepthMax}"],
      [.text s!"nat bits: {m.natBits}"],
      [.text "nat literal pattern: ", .code m.natLiteralPattern],
      [.text "payload hex pattern: ", .code m.payloadHexPattern]],
    .h2 "Refusal details (pinned)",
    .table {
      headers := #v["key", "detail"]
      rows := m.details.map fun (k, v) => #v[⟨[.code k]⟩, ⟨[.code v]⟩] },
    .h2 "Unreachable in v0",
    .table {
      headers := #v["code", "revival"]
      rows := m.unreachableV0.map fun u =>
        #v[⟨[.code u.code.wire]⟩, ⟨[.text u.revival]⟩] }
  ]

/-- The rendered manifest document — the bytes of `manifest.json`. -/
def document : String := Cas.Json.document manifestV0.toValue
def markdown : String := manifestV0.toMarkdown

end Cas.Lift
