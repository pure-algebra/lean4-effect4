import Cas
import Cas.Schema.Deriving
import Cas.Backend.EmitAst
import Gate

/-!
# The word-wire emitter — `lake exe emitword`

The registry of the word's wire records: the receipt
(`Cas.Lang.WordWire.LogEntry`) and the history document
(`Cas.Lang.WordWire.History`) become GENERATED Effect Schema mirrors,
on `emitwire`'s exact pattern — `deriving Described` supplies the
canonical codes, the registry below lowers them with structural
sharing, and `--check` is the byte-identity gate wired into
`check:cas`. The host's word log persists rows in this spelling and
`cas history --json` answers this document, so neither surface ever
carries an ad-hoc shape: the record is registered here or it does not
ride the wire.

TWO FIXTURES, one registry. The effects package's mirror is the first;
the workbench's (`experiments/workbench/src/generated/`) is the second,
and it exists because the front end is a separate package that may not
import the first — the two name different `effect` versions, and that
split is unruled (`experiments/workbench/README.md`, C6 pending). A
front end holding a hand copy of a record the store language already
describes is exactly what that README refuses, so the copy is emitted:
the same `decls`, printed by the same printer in the same run, with a
header that says which file a reader is standing in.
-/

open Cas.Schema Cas.Backend Cas.Backend.Ts

deriving instance Described for Cas.Lang.WordWire.LogEntry
deriving instance Described for Cas.Lang.WordWire.History

namespace EmitWordMain

/-- The registry: emission order is sharing order — the history
document factors through the receipt's name. -/
def registry : List (String × String × Ast) := [
  ("wordLogEntrySchema",
    "One receipt: the persisted record of one admission — seq is the mark (zero-based word index), at is epoch milliseconds on the admitting host's clock.",
    Described.code (α := Cas.Lang.WordWire.LogEntry)),
  ("wordHistorySchema",
    "The history document: the word's suffix from a mark, in admission order, with the next mark.",
    Described.code (α := Cas.Lang.WordWire.History))
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
  emitter := "emitword"
  module := "library/cas/tools/EmitWord.lean"

/-- The mirror module, at whichever header its copy is read under. The
`imports` and `decls` are the SAME values for every copy — one registry,
lowered once — so two mirrors of this module can differ only in the
prose that says where each one lives and why, never in a declaration. -/
def moduleWith (header : List String) : Ts.Module where
  header := header ++ emitted.headerLines
  imports := [
    .named ["Schema"] "effect"
  ]
  decls := decls

def wordModule : Ts.Module := moduleWith [
  "GENERATED — do not edit. The canonical Effect Schema mirrors of the",
  "word's wire records — the receipt and the history document — lowered",
  "from the Lean codes in `library/cas/Cas/Lang/WordWire.lean`",
  "(`Described.code` of the wire structures) by `lake exe emitword`;",
  "regeneration is byte-identity-gated (`--check`, wired into",
  "`check:cas`). The word log persists rows in this spelling and",
  "`cas history --json` answers this document."
]

/-- The workbench's copy. Same declarations, different reader: the front
end is a separate package with its own `effect` dependency, so it cannot
import the effects package's mirror without settling the two-copies
question that package's README parks (C6 pending). What it can do is
read the same registry, which is what this second fixture is.

The header quotes the obligation that makes it a fixture rather than a
hand copy, because the file is where somebody tempted to edit it will be
standing. -/
def workbenchModule : Ts.Module := moduleWith [
  "GENERATED — do not edit. The canonical Effect Schema mirrors of the",
  "word's wire records — the receipt and the history document — lowered",
  "from the Lean codes in `library/cas/Cas/Lang/WordWire.lean`",
  "(`Described.code` of the wire structures) by `lake exe emitword`;",
  "regeneration is byte-identity-gated (`--check`, wired into",
  "`check:cas`).",
  "",
  "THE WORKBENCH'S COPY, and the law it exists under —",
  "`experiments/workbench/README.md`: «any surface the store language",
  "already describes must be generated, never typed by hand». The word",
  "log's records are such a surface, so the front end reads them from",
  "the same registry the effects package does rather than from a",
  "transcription of it. The declarations below are the SAME Lean values",
  "`library/effects/src/cas/generated/WordLogSchema.ts` carries, printed",
  "by the same printer in the same run; only this header differs, and it",
  "differs because the two files are read by different people."
]

def rendered : String := Render.module house0 wordModule

def workbenchRendered : String := Render.module house0 workbenchModule

/-- Where the mirror module lives in the effects package — the
registry's own knowledge of its artifact, so no caller has to carry
the path. A positional argument overrides it. -/
def defaultTarget : System.FilePath :=
  "../effects/src/cas/generated/WordLogSchema.ts"

/-- Where the workbench's copy lives. FIXED, not derived from the
effects target: the two are mirrors in different packages, not siblings
in one generated directory, so a re-pointed effects artifact must not
drag the front end's copy after it. `EmitGrammar.registryTarget` is the
precedent for a second fixture the positional override does not move. -/
def workbenchTarget : System.FilePath :=
  "../../experiments/workbench/src/generated/WordLogSchema.ts"

def fixtures (target : Option System.FilePath) : IO (List Gate.Fixture) :=
  return [
    ⟨target.getD defaultTarget, rendered, s!"{registry.length} mirrors"⟩,
    ⟨workbenchTarget, workbenchRendered,
      s!"{registry.length} mirrors, the workbench's copy"⟩]

end EmitWordMain

def main := Gate.mainAt "lake exe emitword" EmitWordMain.fixtures
