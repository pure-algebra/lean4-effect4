import Cas.Vectors.Registry
import Cas.Backend.EmitProg
import Cas.Backend.ProgProse
import Cas.Codec.Sha256
import Gate

/-!
# The program emitter — `lake exe emitprograms`

Slice 2 of the TypeScript backend, the language's hello world: every
registered grammar term lowered to a straight-line Effect program that
re-performs the term's puts against a REAL store, computing addresses
through the host's own digest. The VectorPrograms suite runs each
program and asserts its answered addresses equal the vector fixture's
word, binding for binding — the cross-host run gate (EFFECTS-BACKEND
R5): same program, both hosts, identical words or red.
-/

open Cas.Schema Cas.Backend Cas.Backend.Ts Cas.Vectors.Registry Cas.Grammar

namespace EmitProgramsMain

def hexHelper : String :=
  "const hex = (s: string): Uint8Array =>\n" ++
  "  Uint8Array.from({ length: s.length / 2 }, (_, i) =>\n" ++
  "    Number.parseInt(s.slice(i * 2, i * 2 + 2), 16))"

abbrev Row := String × String × String × ((t : Ty) × Tree t)

/-- (program name, vector fixture name, authored POINT, term) — the
vector registry's order.

Two registers, and the emitted docstring carries both. The POINT is
AUTHORED: one sentence saying what this program is FOR, which no walk
over the term can recover, because "the smallest program" and "a
provenance pin as store content" are facts about why the row is in the
registry, not about its puts. Everything after it is COMPUTED: the
term's effect envelope verbalized (`Cas/Backend/ProgProse.lean`), from
the same term the statements are lowered from, so the byte gate checks
the description rather than transcribing it.

The authored line is E3's answer to the toProse lane: verbalizing the
envelope replaced the hand docs wholesale, and it should have replaced
only their second half. -/
def pureRows : List Row := [
  ("valueSingle", "value-single",
    "One opaque value node — the smallest program.", ⟨_, helloValue⟩),
  ("blobTwoLeaves", "blob-two-leaves",
    "A two-leaf blob: chunks, leaves, parent, manifest.", ⟨_, blobTwoLeaves⟩),
  ("fileReadme", "file-readme",
    "A named file over a one-chunk blob.", ⟨_, fileReadme⟩),
  ("journalTwoEntries", "journal-two-entries",
    "A journal: genesis and two entries over saved files.", ⟨_, journalTwo⟩),
  ("sharedChunk", "shared-chunk",
    "Two leaves over one shared chunk — the duplicate put replays as a dedup.",
    ⟨_, blobSharedChunk⟩),
  ("gitPinCommit", "git-pin-commit",
    "The lean4-tree-sitter pin commit as a git node — a provenance pin as store content.",
    ⟨_, gitPinCommit⟩)
]

/-- The schema program needs the payload-bound witness, so it joins
the registry in `IO` (the vector tool's own pattern). -/
def schemaRow : IO Row := do
  if small : (Cas.Grammar.utf8 vectorDocumentCode.payload).length < 4294967296 then
    return ("schemaVectorDocument", "schema-vector-document",
      "The vector format's own canonical schema as a schema node.",
      ⟨_, .schema ⟨Cas.Grammar.utf8 vectorDocumentCode.payload, small⟩⟩)
  else
    throw (IO.userError "schema program: payload exceeds the node byte bound")

/-! ## The program's own address — R7's stamp clause, discharged

R7 requires that any static projection generated for ergonomics be
STAMPED with the address of the term it projects, "so parity is a
digest check". Until now `VectorPrograms.ts` and
`VectorProgramLifts.json` carried names and no addresses, which is the
estate's flagship generated-program artifact failing the estate's
flagship program ruling.

The address a program HAS is not a new notion invented here. It is
`Cas.Lang.encodeProg`'s: a table is laid down children-first as step
nodes (tag 14), then one cont node (tag 15) naming them all in program
order, and the program's address is that cont node's. Under the
production digest (`Cas.sha256Addr`, the same one the vector lane runs)
the address is a computed fact about the term, not a convention — which
is exactly what makes it a CROSS-HOST gate: a host that mirrors
`encodeProg` must compute these same 64 hex characters or go red.

Note what is NOT emitted: no word. The direction law says words are
minted by RUNNING and by nothing else; an address is laid down by
encoding, so it is the encoder's to answer and the runner's to ignore. -/

/-- One code point's step-node address under the production digest. -/
def stepAddressOf (l : Cas.Lang.PLine) : String :=
  Cas.hexS (Cas.Lang.lineAddr Cas.sha256Addr l).val

/-- A table's cont-node address under the production digest — THE
program's address, the one a `cont` root is published at. -/
def contAddressOf (p : Cas.Lang.PProg) : String :=
  Cas.hexS
    (Cas.sha256Addr (Cas.encodeNode (Cas.Lang.tableNode Cas.sha256Addr p))).val

/-- The stamp line carried in the generated program's own docstring —
R7's "stamped with the address of the term it projects", spelled where
a reader of the TypeScript meets it. -/
def stampLine (p : Cas.Lang.PProg) : String :=
  s!"Its address as content — the cont node `Cas.Lang.encodeProg` lays "
    ++ s!"down for this table under the production digest — is "
    ++ s!"{contAddressOf p}."

/-- The emitter is partial on `PProg` (puts only, earlier-answer
operands only — `Cas.Backend.progProgram`). Every registered term
lowers inside that domain, so a `none` here is a defect in the walk and
is named as one rather than silently skipped.

The doc block is `point :: envelope ++ stamp`: the authored sentence
first, then the computed lines, then R7's address stamp. Only the first
line is transcribed, and it is transcribed because it is not derivable;
the byte gate still checks the whole block, so neither the envelope half
nor the stamp can drift from the term. -/
def progDecl (name : String) (point : String) (tree : (t : Ty) × Tree t) :
    IO Decl := do
  let doc := (point :: tree.2.docLines) ++ [stampLine (treeProg tree.2)]
  match treeProgram doc name tree.2 with
  | some d => return .prog d
  | none => throw (IO.userError
      s!"program {name}: the lowered table is outside the recognized surface")

def moduleDecls (rows : List Row) : IO (List Decl) := do
  let progs ← rows.mapM fun (name, _, point, tree) => progDecl name point tree
  return .raw hexHelper :: progs ++
    [.const {
      doc := ["Every generated program beside its vector fixture's name."]
      name := "programs"
      value := .arr (rows.map fun (name, fixture, _, _) =>
        .object [("name", .str fixture), ("run", .ident name)])
    }]

/-- The lane's emitted header. The module declared no version before
this one, so its `schemaVersion` opens at 1.

The two JSON documents beside it are deliberately NOT headed. Both are
top-level ARRAYS, and both are one half of a byte comparison the
TypeScript side performs against its own rendering of the same value —
`canonJson(liftSource(VectorPrograms.ts))` for the lift documents, a
host's own digest answers for the addresses. A field this side alone
writes would not describe the artifact, it would break the comparison
the artifact exists for. -/
def emitted : Gate.Emitted where
  schemaVersion := 1
  emitter := "emitprograms"
  module := "library/cas/tools/EmitPrograms.lean"

def programsModule (rows : List Row) : IO Ts.Module := do
  return {
    header := [
      "GENERATED — do not edit. Straight-line Effect programs lowered",
      "from the registered grammar terms (`Cas/Vectors/Registry.lean`)",
      "by `lake exe emitprograms`; regeneration is byte-identity-gated",
      "(`--check`, wired into `check:cas`). Each program re-performs its",
      "term's puts against a live store — addresses computed by the",
      "host's own digest — and the VectorPrograms suite asserts the",
      "answers equal the Lean-computed word, binding for binding: the",
      "cross-host run gate."
    ] ++ emitted.headerLines
    imports := [
      .named ["Effect"] "effect",
      .types ["CasStoreShape"] "../../src/cas/Store.ts"
    ]
    decls := ← moduleDecls rows }

def rendered (rows : List Row) : IO String := do
  return Render.module house0 (← programsModule rows)

/-! ## The round-trip document (P3)

The second artifact: the lift document the recognizer must answer for
each generated program, in the harness's own canonical JSON, in
declaration order. It is emitted from the SAME `PProg` the TypeScript
was printed from, so the two fixtures cannot drift apart, and the
harness's side of the gate is a byte comparison against
`canonJson(liftSource(VectorPrograms.ts))`.

The Lean half of the round trip runs HERE, before the bytes are written:
every document is decoded back through `Cas.Lift.decodeLiftBytes` and
compared to the table it came from. `decodeLiftBytes_encodeLiftBytes`
proves that in general; this runs it on the registered programs, so a
regression in either direction is a red gate and not a stale theorem. -/

/-- The `PProg → document → PProg` leg, executed on one row. Answers the
document's canonical bytes. -/
def liftDocumentOf (name : String) (tree : (t : Ty) × Tree t) :
    IO Cas.Json.Value := do
  let lifted := treeLifted name tree.2
  let some doc := Cas.Lift.encodeLift lifted
    | throw (IO.userError
        s!"lift document {name}: the table is outside the decoder's domain")
  let bytes := Cas.Json.renderCompact doc
  match Cas.Lift.decodeLiftBytes bytes with
  | .error _ => throw (IO.userError
      s!"lift document {name}: its own bytes did not decode back")
  | .ok back =>
    if back = lifted then return doc
    else throw (IO.userError
      s!"lift document {name}: decoded back to a different program")

def liftsDocument (rows : List Row) : IO String := do
  let docs ← rows.mapM fun (name, _, _, tree) => liftDocumentOf name tree
  return Cas.Json.renderCompact (.arr docs) ++ "\n"

/-! ## The address document (O1's cross-host gate)

The third artifact, and the one that turns `encodeProg` from a theorem
into an operational claim a second host must meet. For each registered
program: the step-node address of every code point, in program order,
and the cont-node address that names them — all under
`Cas.sha256Addr`.

A host mirroring `Cas.Lang.encodeProg` puts the same nodes into a real
store and reads its OWN digest's answers back. Those answers must equal
these bytes. That is the whole gate, and it is a stronger one than the
lift document's: the lift document pins what a program SAYS, this pins
what a program IS. -/

/-- One program's addresses as the canonical document. -/
def addressDocumentOf (name : String) (tree : (t : Ty) × Tree t) :
    Cas.Json.Value :=
  let p := treeProg tree.2
  .obj [
    ("contAddress", .str (contAddressOf p)),
    ("name", .str name),
    ("stepAddresses", .arr (p.map fun l => .str (stepAddressOf l)))]

def addressesDocument (rows : List Row) : IO String := do
  let docs := rows.map fun (name, _, _, tree) => addressDocumentOf name tree
  return Cas.Json.renderCompact (.arr docs) ++ "\n"

/-- Where the generated programs live in the effects package — the
registry's own knowledge of its artifact. A positional argument
overrides it; the lift documents follow it to the sibling path. -/
def defaultTarget : System.FilePath :=
  "../effects/test/generated/VectorPrograms.ts"

/-- The lift documents' path, derived from the programs' own. -/
def liftsTargetOf (programs : System.FilePath) : System.FilePath :=
  match programs.parent with
  | some dir => dir / "VectorProgramLifts.json"
  | none => "VectorProgramLifts.json"

/-- The address document's path, derived the same way. -/
def addressesTargetOf (programs : System.FilePath) : System.FilePath :=
  match programs.parent with
  | some dir => dir / "VectorProgramAddresses.json"
  | none => "VectorProgramAddresses.json"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) := do
  let rows := pureRows ++ [← schemaRow]
  let programs := target.getD defaultTarget
  let text ← rendered rows
  let lifts ← liftsDocument rows
  let addresses ← addressesDocument rows
  return [
    ⟨programs, text, s!"{rows.length} programs"⟩,
    ⟨addressesTargetOf programs, addresses,
      s!"{rows.length} program addresses"⟩,
    ⟨liftsTargetOf programs, lifts,
      s!"{rows.length} lift documents (round-tripped)"⟩]

end EmitProgramsMain

def main := Gate.mainAt "lake exe emitprograms" EmitProgramsMain.fixtures
