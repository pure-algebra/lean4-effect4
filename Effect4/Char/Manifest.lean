import Effect4.Char.Core
import Effect4.Char.Evidence

/-!
# Char.Manifest

Owner: the flat manifest a characterized component projects to, and its store
payload.

A component is described once, in Lean, as carriers, step, reading, kinds,
failure models, grade bundles, tests and mutants. The manifest is the erasure
of that description: strings, naturals, booleans, digests and lists of those,
with `DecidableEq` and `Repr`, so it can be stored, compared and rendered. The
proof-carrying bundles never leave their module; `Entry` is their flat row
(`Effect4/Char/Core.lean`, `Guarded.entry`, `Graded.entry`), and a `GradeRow`
is the flat row of a `Graded`, with the excluded kinds by their spellings
(ruling R1) rather than as values of `K`.

The manifest is derived from the environment by `char-gate derive` and checked
against it by `#characterize`, neither of which lives here: this module is the
carrier those two agree on. `declared` is the name list the derivation law
compares to the walk, `derived = declared` in both directions
(`workshop/Char/08-codegen/02-manifest-derivation.md`, section 1).

Ruling R5: the store payload is the JSON projection through the one
`Canonical Json` instance; the address is `digestOf` of it. Pins are cited by
address (`Effect4/Store/Pin.lean`, `Pin.address`), claims by value (`Claim`
stays typed, R5), evidence by value inside a grade row. Keys are emitted in
declaration order and are never sorted.
-/

namespace Effect4.Char

open Effect4.Store
open Effect4.Arch

/-- A list of strings as a JSON array. -/
private def strings (xs : List String) : Json := .arr (xs.map Json.str)

/-- The flat row of a proof-carrying bundle, as store content. -/
def Entry.json (e : Entry) : Json :=
  .obj [("id", .str e.id), ("family", .str e.family), ("sentence", .str e.sentence)]

/-- The three axes, as store content. -/
def Grade.json (g : Grade) : Json :=
  .obj [("noLoss", .bool g.noLoss), ("noDup", .bool g.noDup), ("order", .bool g.order)]

/-- One observable operation of a component: its label's spelling and the
addresses of the pins that anchor it in the pinned source. -/
structure Verb where
  label : String
  /-- Addresses of `Effect4.Store.Pin` entities, in a fixed order. -/
  pins : List Digest
deriving DecidableEq, Repr, Inhabited

def Verb.json (v : Verb) : Json :=
  .obj [("label", .str v.label), ("pins", .arr (v.pins.map fun d => Json.str d.hex))]

/-- The flat row of a `Graded` bundle: the failure model by name, its excluded
kinds by spelling, its escape sentences, the grade, and the evidence backing
the soundness law. -/
structure GradeRow where
  failure : String
  /-- The kinds a graded run may not contain, spelled. Ruling R1. -/
  excluded : List String
  escapes : List String
  grade : Grade
  evidence : Evidence
deriving DecidableEq, Repr, Inhabited

/-- Project a `Graded` bundle to its row. The `Prop` fields stay behind. -/
def GradeRow.ofGraded {S L C K : Type} [DecidableEq C] [DecidableEq K]
    (g : Graded S L C K) (evidence : Evidence) : GradeRow :=
  { failure := g.failure.name
    excluded := g.failure.excludedSpelled g.kinds
    escapes := g.failure.escapes
    grade := g.grade
    evidence := evidence }

def GradeRow.json (r : GradeRow) : Json :=
  .obj
    [ ("failure", .str r.failure)
    , ("excluded", strings r.excluded)
    , ("escapes", strings r.escapes)
    , ("grade", r.grade.json)
    , ("evidence", r.evidence.json) ]

/-- The manifest: one component, flat. Name lists refer to declarations of the
component's own modules; `#characterize` is what ties each name to the
environment. -/
structure Manifest where
  component : String
  /-- The label spellings, in constructor order: `Kinds.all.map Kinds.spell`. -/
  labels : List String
  verbs : List Verb
  /-- Names of the `structure … : Prop` invariants. -/
  invariants : List String
  /-- Names of the theorems that are laws. -/
  laws : List String
  /-- The flat rows of the `Guarded` and `Graded` bundles, in name order. -/
  entries : List Entry
  grades : List GradeRow
  /-- Names of the `by decide` receipts: suite passes, mutants killed, not vacuous. -/
  receipts : List String
  /-- The `Mutant.id` of every declared mutant. -/
  mutants : List String
  claims : List Claim
deriving DecidableEq, Repr, Inhabited

namespace Manifest

/-- The names the manifest declares, in the order the derivation law compares
them: invariants, laws, entry ids, receipts, mutants. The environment walk must
produce exactly this list, as a sorted duplicate-free set. -/
def declared (m : Manifest) : List String :=
  m.invariants ++ m.laws ++ m.entries.map Entry.id ++ m.receipts ++ m.mutants

/-- The trie name: `["char", component, "manifest"]`. Rebound on every derivation;
the previous content stays at its address. -/
def path (m : Manifest) : Path := ["char", m.component, "manifest"]

/-- The manifest as store content, per ruling R5. -/
def json (m : Manifest) : Json :=
  .obj
    [ ("type", .str "manifest")
    , ("component", .str m.component)
    , ("labels", strings m.labels)
    , ("verbs", .arr (m.verbs.map Verb.json))
    , ("invariants", strings m.invariants)
    , ("laws", strings m.laws)
    , ("entries", .arr (m.entries.map Entry.json))
    , ("grades", .arr (m.grades.map GradeRow.json))
    , ("receipts", strings m.receipts)
    , ("mutants", strings m.mutants)
    , ("claims", .arr (m.claims.map Claim.json)) ]

/-- The address: the digest of the payload through the one `Canonical Json`. -/
def address (m : Manifest) : Digest := digestOf m.json

/-- Equal manifests have equal addresses; the converse is never assumed. -/
theorem address_congr {m n : Manifest} (h : m = n) : m.address = n.address :=
  congrArg address h

end Manifest

instance : Canonical Manifest := ⟨fun m => encode m.json⟩

end Effect4.Char
