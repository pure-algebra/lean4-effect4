import Lean
import Conform.Core.Report
import Conform.Core.Policy
import Conform.Manifest.Readers

/-!
# Conform.Manifest.Mirror — `family.mirror.agrees`

**What it is.** The check that closes the *other* half of coverage. `Conform.Lcnf.Cases` asks
whether every consumer **in Lean** has an arm for every constructor; a family's alphabet is also
restated in OCaml, in TypeScript, in a text manifest and in frozen fixtures, and LCNF cannot see
any of those. This module reads each of those artefacts back to a constructor list with
`Conform.Manifest.Readers`, maps its spellings to Lean constructor names, and compares — **names
and order** — with the environment's own list. One `Conform.Row` per `(family, mirror)`.

**Depends on.** `Lean` (the environment's `InductiveVal.ctors`), `Conform.Core.Report`,
`Conform.Core.Policy`, `Conform.Manifest.Readers`. No repository module and no `Effect4` name: the
mirror list is a JSON file (`tools/Conform/Effect4/mirrors.json` for this tree).

**What it deliberately does not do.** It does not walk `-- cut-from:` stamps or decide whether a
generated file is up to date: that is `scripts/lib/check_generated.py`'s job and duplicating it
would give the tree two disagreeing answers to one question. This check is the complement — it
reads what the file *says* rather than when it was cut, so it also covers the **hand-written**
copies, which no stamp walk can.

**Properties.**
* **A mirror that cannot be read is `unresolved`, never a pass.** A missing file, an unparsable
  block, a family that is not an inductive and an artefact declared to have no text grammar all
  produce a row whose outcome is `unresolved` and whose message names the cause — *by
  construction* (`checkOne`).
* **Order is checked.** Two lists with the same members in a different order are a refusal, and
  the message names the first position that differs as well as any rename — *by construction*
  (`compare`).
* **Normalisation is declared, not inferred.** A mirror says how its spellings map back
  (`stripPrefix`, `rename`, `aliases`); nothing is guessed, and a spelling the declaration does
  not reach shows up as a rename in the diff — *by construction*.
-/

namespace Conform.Manifest

open Lean

/-! ## 1. The mirror list -/

/-- One artefact that restates one family's constructors. -/
structure Mirror where
  /-- The Lean inductive this artefact mirrors. -/
  family : Name
  /-- The file, relative to the repository root the driver runs in. -/
  file : System.FilePath
  /-- Which text grammar reads it. -/
  kind : Kind
  /-- The key that names the family inside that artefact (its own vocabulary). -/
  key : String
  /-- A prefix every constructor spelling carries and the Lean name does not (`Ty_`). Removed
  before `rename`; a spelling without it is a refusal, not a silent pass-through. -/
  stripPrefix : Option String := none
  /-- How the remaining spelling maps to a Lean constructor's short name. -/
  rename : Rename := .identity
  /-- Exceptions to `rename`, as `(artefact spelling after stripPrefix, Lean short name)`. -/
  aliases : Array (String × String) := #[]
  /-- What this artefact is, for the row's message. -/
  note : Option String := none
deriving Inhabited

structure MirrorSpec where
  mirrors : Array Mirror
  note : Option String := none
deriving Inhabited

/-! ### 1.1 The reader -/

namespace MirrorSpec

open Conform.Policy

private def readKind (j : Json) (get : String → Option Json) : Policy.Reader Kind := do
  let id ← string j
  match id with
  | "json-inventory" =>
    let shape ← field? get "json" fun s => do
      let g ← object s ["array", "key", "list"]
      let array ← field g "array" string
      let key ← field g "key" string
      let list ← field g "list" string
      pure ({ array, key, list } : JsonShape)
    pure (.jsonInventory (shape.getD {}))
  | "text-manifest" => pure .textManifest
  | "ts-tag-union" => pure .tsTagUnion
  | "ts-tagged-union" => pure .tsTaggedUnion
  | "ocaml-ctor-names" => pure .ocamlCtorNames
  | "ocaml-type-block" => pure .ocamlTypeBlock
  | "ocaml-match-arms" => pure .ocamlMatchArms
  | "ts-literals" => pure .tsLiterals
  | "ts-switch-cases" => pure .tsSwitchCases
  | "unresolved" =>
    match ← field? get "reason" string with
    | some r => pure (.unresolved r)
    | none => fail "`reader: \"unresolved\"` needs a `reason`: why no text grammar reaches it"
  | other =>
    fail s!"`{other}` is not a reader (json-inventory, text-manifest, ts-tag-union, \
            ts-tagged-union, ocaml-ctor-names, ocaml-type-block, ocaml-match-arms, ts-literals, \
            ts-switch-cases, unresolved)"

private def readMirror (j : Json) : Policy.Reader Mirror := do
  let get ← object j
    ["family", "file", "reader", "key", "json", "reason", "stripPrefix", "rename", "aliases", "note"]
  let family ← field get "family" Policy.name
  let file ← field get "file" string
  let kind ← field get "reader" fun r => readKind r get
  let key ← field get "key" string
  let stripPrefix ← field? get "stripPrefix" string
  let rename ← field? get "rename" fun r =>
    enum r [("identity", Rename.identity), ("ocaml-ctor", Rename.ocamlCtor)]
  let aliases ← field? get "aliases" fun a => array a fun pair => do
    let g ← object pair ["from", "to"]
    let f ← field g "from" string
    let t ← field g "to" string
    pure (f, t)
  let note ← field? get "note" string
  return { family, file := file, kind, key, stripPrefix, rename := rename.getD .identity
         , aliases := aliases.getD #[], note }

def read (j : Json) : Policy.Reader MirrorSpec := do
  let get ← object j ["mirrors", "note"]
  let note ← field? get "note" string
  let mirrors ← field get "mirrors" fun m => array m readMirror
  if mirrors.isEmpty then fail "`mirrors` is empty: there is nothing to compare"
  return { mirrors, note }

def load (file : System.FilePath) : IO MirrorSpec := Policy.load file read

end MirrorSpec

/-! ## 2. Comparison -/

/-- The difference between what an artefact says and what the environment says, in the vocabulary a
red row has to speak: a constructor the artefact lacks, one it has that the family does not, and
the first position at which the common constructors are in a different order. -/
structure Diff where
  missing : Array String
  extra : Array String
  /-- `(index, expected, found)` of the first position where the two agree on membership but not on
  order. -/
  misordered : Option (Nat × String × String)
deriving Inhabited

def Diff.agrees (d : Diff) : Bool :=
  d.missing.isEmpty && d.extra.isEmpty && d.misordered.isNone

/-- `expected` is the environment's list, `found` the artefact's. Order is compared on the
constructors both lists carry, so a rename and a reorder are reported as the two different things
they are. -/
def diff (expected found : Array String) : Diff :=
  let inFound : Std.HashSet String := found.foldl (init := {}) (·.insert ·)
  let inExpected : Std.HashSet String := expected.foldl (init := {}) (·.insert ·)
  let missing := expected.filter fun c => !inFound.contains c
  let extra := found.filter fun c => !inExpected.contains c
  -- `zip` truncates to the shorter list, which is exactly the bound the hand loop guarded
  let common := (expected.filter inFound.contains).zip (found.filter inExpected.contains)
  let misordered := (common.findIdx? fun (e, f) => e != f).map fun i =>
    (i, common[i]!.1, common[i]!.2)
  { missing, extra, misordered }

private def list (xs : Array String) : String :=
  if xs.isEmpty then "none" else ", ".intercalate xs.toList

def Diff.message (d : Diff) : String :=
  let parts : List String :=
    (if d.missing.isEmpty then [] else [s!"absent from the artefact: {list d.missing}"]) ++
    (if d.extra.isEmpty then [] else [s!"present in the artefact and not in the family: {list d.extra}"]) ++
    (match d.misordered with
     | some (i, e, f) => [s!"out of order at position {i}: the family has `{e}`, the artefact `{f}`"]
     | none => [])
  "; ".intercalate parts

def Diff.toJson (d : Diff) : Json :=
  Json.mkObj
    [ ("missing", Json.arr (d.missing.map Json.str))
    , ("extra", Json.arr (d.extra.map Json.str))
    , ("misordered", match d.misordered with
        | some (i, e, f) =>
          Json.mkObj [("index", Json.num i), ("family", Json.str e), ("artefact", Json.str f)]
        | none => Json.null) ]

/-! ## 3. The check -/

private def subjectOf (m : Mirror) : Subject :=
  { kind := "familyMirror", path := [m.family.toString, m.kind.id, m.file.toString] }

/-- Map one artefact spelling back to a Lean constructor short name. -/
private def normalise (m : Mirror) (s : String) : Except String String := do
  let base ← match m.stripPrefix with
    | none => pure s
    | some p =>
      if s.startsWith p then pure (dropS s p.length)
      else throw s!"`{s}` does not carry the declared prefix `{p}`"
  match m.aliases.find? fun (f, _) => f == base with
  | some (_, t) => pure t
  | none => pure (m.rename.apply base)

/-- The environment's constructors of `m.family`, as short names in declaration order.
`InductiveVal.ctors` is the built-in; `getConstInfoInduct` is deliberately not, because this
check owes its caller a named refusal rather than an exception. -/
private def familyCtors (env : Environment) (f : Name) : Except String (Array String) :=
  match env.find? f with
  | some (.inductInfo i) => .ok (i.ctors.toArray.map Name.getString!)
  | some _ => .error s!"`{f}` is a constant but not an inductive type"
  | none => .error s!"`{f}` is not a constant of the imported environment"

def checkOne (env : Environment) (m : Mirror) : IO Row := do
  let subject := subjectOf m
  let why := match m.note with | some n => s!" ({n})" | none => ""
  match familyCtors env m.family with
  | .error e => return Row.unresolved "family.mirror.agrees" subject e
  | .ok expected =>
    if let some reason := m.kind.isUnresolved then
      return Row.unresolved "family.mirror.agrees" subject
        s!"{m.file} restates `{m.family}` in a form no text grammar recovers: {reason}{why}"
        (Json.mkObj [("family", Json.str m.family.toString), ("file", Json.str m.file.toString)])
    unless (← System.FilePath.pathExists m.file) do
      return Row.unresolved "family.mirror.agrees" subject
        s!"{m.file} does not exist; the mirror list names it{why}"
    let text ← IO.FS.readFile m.file
    match readWith m.kind text m.key with
    | .error e =>
      return Row.unresolved "family.mirror.agrees" subject
        s!"{m.file}: the `{m.kind.id}` grammar did not reach `{m.key}`: {e}{why}"
    | .ok raw =>
      let mut found : Array String := #[]
      for r in raw do
        match normalise m r with
        | .ok n => found := found.push n
        | .error e =>
          return Row.refused "family.mirror.agrees" subject
            s!"{m.file}: {e}{why}"
            (Json.mkObj [("raw", Json.arr (raw.map Json.str))])
      let d := diff expected found
      let detail := Json.mkObj
        [ ("family", Json.str m.family.toString)
        , ("file", Json.str m.file.toString)
        , ("reader", Json.str m.kind.id)
        , ("key", Json.str m.key)
        , ("expected", Json.arr (expected.map Json.str))
        , ("found", Json.arr (found.map Json.str))
        , ("raw", Json.arr (raw.map Json.str))
        , ("diff", d.toJson) ]
      if d.agrees then
        return Row.pass "family.mirror.agrees" subject .tested
          s!"{m.file} restates `{m.family}`'s {expected.size} constructors, in order{why}" detail
      else
        return Row.counterexample "family.mirror.agrees" subject
          s!"{m.file} disagrees with `{m.family}`: {d.message}{why}" detail

/-- Every mirror in the list gets exactly one row; `expected` is the list's length, and the files
the list *names* and that exist come back, in first-mention order, so the driver can hash them into
the report's `inputs`.

Note that this is the list's files, not the files `checkOne` opened: a mirror declared
`reader: "unresolved"` is never read and its file is still hashed, because an edit to it should
still make the gate's stamp miss. `Array.contains` over a list that has sixteen entries in this
tree is the deduplication, and the array keeps the order the digests are taken in. -/
def required (spec : MirrorSpec) : Array CheckId :=
  spec.mirrors.map fun m => ⟨"family.mirror.agrees", subjectOf m⟩

def check (spec : MirrorSpec) : CoreM (Array Row × Nat × Array System.FilePath) := do
  let env ← getEnv
  let mut rows : Array Row := #[]
  let mut files : Array System.FilePath := #[]
  for m in spec.mirrors do
    rows := rows.push (← checkOne env m)
    if !files.contains m.file && (← System.FilePath.pathExists m.file) then
      files := files.push m.file
  return (rows, spec.mirrors.size, files)

end Conform.Manifest
