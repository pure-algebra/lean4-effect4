import Effect4.Char.Evidence

/-!
# Char.Manifest

Owner: the flat manifest a characterized component projects to, and the node it is.

A component is described once, in Lean, as carriers, step, reading, kinds,
failure models, grade bundles, tests and mutants. The manifest is the erasure
of that description: strings, naturals, booleans, references and lists of those,
with `DecidableEq` and `Repr`, so it can be stored, compared and rendered. The
proof-carrying bundles never leave their module; `Entry` is their flat row
(`src/Effect4/Char/Core.lean`, `Guarded.entry`, `Graded.entry`), and a
`GradeRow` is the flat row of a `Graded`, with the excluded kinds by their
spellings (ruling R1) rather than as values of `K`.

The manifest is derived from the environment by `char-gate derive` and checked
against it by `#characterize`, neither of which lives here: this module is the
carrier those two agree on. `declared` is the name list the derivation law
compares to the walk, `derived = declared` in both directions
(`docs/research/2026-09-05-workshop-char/08-codegen/02-manifest-derivation.md`, section 1).

Ruling R5 as re-ruled by Q1: the store payload is the carrier's own structural
bytes, not a JSON projection, so `Manifest.json` and the four helper printers
that fed it (`Entry.json`, `Grade.json`, `Verb.json`, `GradeRow.json`) are
retired with `Manifest.address`; the node address is `Effect4.Store.address`, the
instance is generated in `Char/Derived.lean`, and the manifest files
under kind `component` (plan §3, row 13 — the row is named for this carrier).
A printer, when one is wanted, is `Canonical.print`, read off the same shape the
spec is, and it still emits the keys in declaration order and digests as
lowercase hex.

Pins are cited by `Ref Pin` (Q4: a pointer that names a node is a reference, never
a digest and never hex), claims by value (`Claim` stays typed, R5), evidence by
value inside a grade row.
-/

set_option autoImplicit false

namespace Effect4.Char

open Effect4.Store

/-- One observable operation of a component: its label's spelling and the
references to the pins that anchor it in the pinned source. -/
structure Verb where
  label : String
  /-- References to `Effect4.Store.Pin` nodes, in a fixed order. -/
  pins : List (Ref Pin)
deriving DecidableEq, Repr, Inhabited

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

/-- The name a manifest binds: `["char", component, "manifest"]`. Rebound on every
derivation; the previous content stays at its address. Names left the store with the trie
(Q3), so this is a plain list of segments and a name space is a `tree` node. -/
def path (m : Manifest) : List String := ["char", m.component, "manifest"]

end Manifest

/-! ## Receipts -/

#print axioms GradeRow.ofGraded
#print axioms Manifest.declared
#print axioms Manifest.path

end Effect4.Char
