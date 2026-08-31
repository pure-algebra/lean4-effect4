/-
PDD-3 — THE BREAK PASS.  Attack module.

SUBJECT      branch `agent/opus-cc-mac/pdd-3`, tip `92a64ec4` (packet
             close); the work in `4c39bf4e` / `326064e3` / `f486689f`.
PACKET       `library/cas/contracts/PDD-3.contract.md`
VERDICT      see `RESULTS.md` beside this file.

THIS FILE IS OUTSIDE EVERY LAKE TARGET, DELIBERATELY.  `lakefile.toml`
roots are `Cas` (its root module alone), `CasBackend` (glob
`Cas.Backend.+`), `CasExamples` (`srcDir = examples`) and `Gate`
(`srcDir = tools`, globs `Gate`/`Walk`).  `contracts/` is under none of
them, so nothing here reaches `lake build`, no ledger byte moves, and
the attack cannot be mistaken for a claim the estate makes.

RUN IT:  from `library/cas`,
    lake env lean contracts/attacks/PDD-3/Attack.lean

Everything below elaborates or fails.  Where a probe is a measurement
rather than a proposition — the blowup timings, the TypeScript door, the
live Effect validator — the numbers are in `RESULTS.md` and the code
that produced them is quoted there.
-/
import Cas.Schema.Ingest

open Cas.Schema

namespace PDD3.Attack

/-- The door, as a string, so a witness reads as its answer. -/
def door (d : Document) : String :=
  match ingestDocument d.envelope with
  | .ok _ => "ADMIT"
  | .error e => s!"REFUSE {repr e}"

/-- Did the door admit it? -/
def admits (d : Document) : Bool :=
  match ingestDocument d.envelope with
  | .ok _ => true
  | .error _ => false

/-! ############################################################
## §1 — FAILED ATTACK: the edge relation misses a nesting

`Ast.bareRefs` ends in a catch-all `| _ => []` (`Guarded.lean:74`).  The
attack is the obvious one: find a constructor that carries a nested
`Ast` and falls into that catch-all — a reference buried there would be
invisible to the edge relation, and a real cycle would be admitted.

IT FAILS, and the census is why.  The constructors carrying a nested
`Ast` are exactly `arr`, `struct`, `decl` (its `typeParameters`),
`union`, `tuple` (first / more / rest) and `susp`; every one has its own
arm.  The catch-all covers `null`, `bool`, `int`, `str`, `lit`, `ref`
and `enum`, and none of those carries an `Ast`: `LitVal` is four
scalars, `EnumValue` is two, `ref` is a `UInt8`, and `decl`'s `payload`
is `DeclPayload`, which is five scalars (`Declarations.lean:56-62`) — so
the one field the `decl` arm does NOT walk cannot hide a reference
either. -/

/-- A reference buried under struct → union → arr → tuple-rest →
declaration type parameter. -/
def deepRef : Ast :=
  .struct [("f", false,
    .union [.arr (.tuple (false, .null) [(false, .bool)]
                    (some (.decl .option .null [.reference "A"])))] .anyOf)]

/-- The same nesting with one `susp` on the path. -/
def deepGuarded : Ast :=
  .struct [("f", false,
    .union [.arr (.tuple (false, .null) [(false, .bool)]
                    (some (.susp (.decl .option .null [.reference "A"]))))] .anyOf)]

-- The walk finds it through all five, and one guard hides it.
#guard deepRef.bareRefs == ["A"]
#guard deepGuarded.bareRefs == []

-- Per-position witnesses, so the census is checked and not asserted: the
-- tuple's FIRST element, its LATER elements and its REST are three
-- different constructor fields, and all three are walked.
#guard (Ast.tuple (false, .reference "A") [] none).bareRefs == ["A"]
#guard (Ast.tuple (false, .null) [(false, .reference "A")] none).bareRefs == ["A"]
#guard (Ast.tuple (false, .null) [] (some (.reference "A"))).bareRefs == ["A"]
#guard (Ast.arr (.reference "A")).bareRefs == ["A"]
#guard (Ast.struct [("f", false, .reference "A")]).bareRefs == ["A"]
#guard (Ast.union [.reference "A"] .anyOf).bareRefs == ["A"]
#guard (Ast.decl .option .null [.reference "A"]).bareRefs == ["A"]

-- And the constructors with no `Ast` child contribute nothing, which is
-- what the catch-all is for.
#guard (Ast.enum [("A", .str "x")]).bareRefs == []
#guard (Ast.lit (.str "A")).bareRefs == []
#guard (Ast.ref 9).bareRefs == []

/-- The deep reference, as a table. -/
def deepNest : Document :=
  { references := [("A", deepRef)], representation := .reference "A" }

/-- The same, guarded. -/
def deepNestGuarded : Document :=
  { references := [("A", deepGuarded)], representation := .reference "A" }

-- The deep one cycles and is refused; the guarded one is admitted.  The
-- edge extraction is ADEQUATE for the relation it is defined to
-- generate.
#guard !deepNest.guarded
#guard deepNestGuarded.guarded
#guard !admits deepNest
#guard admits deepNestGuarded

/-! ############################################################
## §2 — HOLE: `Guarded` decides CONSTRUCTIBILITY, not productivity

`Guarded.lean:21-26` states why the discipline exists:

> resolving an unguarded cycle never terminates, and Effect's own codec
> does not refuse one … The refusal is this door's to make or nobody's.

and `IngestRefusal.unguardedCycle` (`Ingest.lean:105-116`) says the same
in the taxonomy: "Resolving one never terminates — the resolver unfolds
`A` to get `A` — so the table is refused rather than carried."

The witnesses below are documents whose resolver unfolds `A` to get `A`,
forever, and BOTH DOORS ADMIT THEM.  `Ast.susp` is a DELAY, not a
constructor: putting the recursive occurrence under one defers the loop,
it does not break it.  What `bareRefs` decides is that the EAGER
revival terminates — a real property, and the one `bareStructCycle` is
about — but it is not the property the prose claims.

Measured consequence (`RESULTS.md` §2): W1's live validator runs forever
(killed at 60s, no output), W2's blows the stack (`RangeError: Maximum
call stack size exceeded`), and the control — the builder's own
`guardedList` — decodes correctly in 1ms. -/

/-- W1 — the bare knot.  `A = susp(reference A)`, root `reference A`. -/
def suspBareSelf : Document :=
  { references := [("A", .susp (.reference "A"))],
    representation := .reference "A" }

/-- W2 — the knot a careless author actually writes, `A = A | null`,
with the `susp` Effect's generator puts on a recursive position. -/
def suspUnionKnot : Document :=
  { references := [("A", .susp (.union [.reference "A", .null] .anyOf))],
    representation := .reference "A" }

/-- W1' — the knot at one remove, so no single entry looks suspicious:
`A = susp(reference B)`, `B = reference A`.  The cycle `A → B → A` does
pass through a `susp`, exactly as the ruled theorem asks. -/
def suspIndirect : Document :=
  { references := [("A", .susp (.reference "B")), ("B", .reference "A")],
    representation := .reference "A" }

#guard suspBareSelf.guarded
#guard suspUnionKnot.guarded
#guard suspIndirect.guarded
#guard admits suspBareSelf
#guard admits suspUnionKnot
#guard admits suspIndirect

/-- W1 is `Guarded` as a PROP, not merely as the procedure's answer — so
this is a fact about the SPECIFICATION, not about the implementation.
The theorem under attack is what carries it. -/
theorem suspBareSelf_guarded : suspBareSelf.Guarded :=
  (references_guarded_decidable suspBareSelf).mp (by decide)

theorem suspUnionKnot_guarded : suspUnionKnot.Guarded :=
  (references_guarded_decidable suspUnionKnot).mp (by decide)

theorem suspIndirect_guarded : suspIndirect.Guarded :=
  (references_guarded_decidable suspIndirect).mp (by decide)

/-- The distinction the relation does not draw, named so the repair is
citable: the HEAD position of an entry is what you reach through `susp`
wrappers alone, before any constructor.  A cycle through head positions
only is the non-productive one. -/
def headName : Ast → Option String
  | .reference n => some n
  | .susp a => headName a
  | _ => none

-- W1's head is a self-edge the bare relation does not have.  W2's head
-- is `none` — a union is not a constructor for this purpose either,
-- which is why the repair is a RULING and not a one-line patch: the
-- productive positions are the ones that build a JSON value, and
-- `union` builds none.  Recorded, not designed.
#guard headName (.susp (.reference "A")) == some "A"
#guard headName (.susp (.union [.reference "A", .null] .anyOf)) == none
#guard headName (.struct [("next", false, .reference "A")]) == none

/-! ############################################################
## §3 — HOLE: the battery cannot tell fuel `|table|` from fuel `0`

`Guarded.lean:46-48` says the fuel bound is where the theorem earns its
exact value.  No WITNESS tests it.  Every admitted C6 row in the
conformance corpus, and every admitted `#guard` beside the falsifiers,
has an EMPTY bare-edge relation — so a door answering "every table entry
has no bare successor at all" (`settles 0`, fuel zero) agrees with the
shipped door on the whole 71-case corpus and on every `#guard` in
`Ingest.lean`.

`guardedWrong` below IS that door.  It is not a correct implementation —
`references_guarded_decidable` is false of it, proved below — but
nothing in the battery exhibits the disagreement, so the fuel is held by
the theorem alone. -/

/-- The wrong door: fuel zero, dressed as the real one. -/
def guardedWrong (d : Document) : Bool :=
  d.names.all (fun n => (d.out n).isEmpty)

/-- Corpus row `admit-references-table`, verbatim. -/
def rowAdmitReferencesTable : Document :=
  { references := [("Node", .str)], representation := .str }

/-- Corpus row `admit-guarded-recursion` — the builder's `guardedList`. -/
def rowAdmitGuardedRecursion : Document := guardedList

/-- Corpus row `refuse-unguarded-alias-cycle`. -/
def rowRefuseAliasCycle : Document := aliasCycle

/-- Corpus row `refuse-unguarded-struct-cycle`. -/
def rowRefuseStructCycle : Document := bareStructCycle

-- THE ADEQUACY GAP, EXHIBITED.  The wrong door agrees with the shipped
-- door on every C6 row the estate carries.
#guard guardedWrong rowAdmitReferencesTable == rowAdmitReferencesTable.guarded
#guard guardedWrong rowAdmitGuardedRecursion == rowAdmitGuardedRecursion.guarded
#guard guardedWrong rowRefuseAliasCycle == rowRefuseAliasCycle.guarded
#guard guardedWrong rowRefuseStructCycle == rowRefuseStructCycle.guarded

-- It agrees on §1's and §2's witnesses too, so nothing added above
-- closes the gap either.
#guard guardedWrong deepNest == deepNest.guarded
#guard guardedWrong deepNestGuarded == deepNestGuarded.guarded
#guard guardedWrong suspBareSelf == suspBareSelf.guarded
#guard guardedWrong suspUnionKnot == suspUnionKnot.guarded

-- And it agrees on every row with an EMPTY table — 67 of the corpus's
-- 71 — because `List.all` over no names is `true` on both sides.
#guard guardedWrong (Document.mk [] Ast.str) == (Document.mk [] Ast.str).guarded

/-- THE MISSING WITNESS.  One acyclic edge is all it takes: `A` names
`B`, `B` is a code. -/
def chain1 : Document :=
  { references := [("A", .reference "B"), ("B", .str)],
    representation := .reference "A" }

/-- Two edges, so `settles` recurses more than once. -/
def chain2 : Document :=
  { references := [("A", .reference "B"), ("B", .reference "C"), ("C", .str)],
    representation := .reference "A" }

-- The shipped door admits both; the fuel-zero door refuses both.
#guard chain1.guarded
#guard !guardedWrong chain1
#guard chain2.guarded
#guard !guardedWrong chain2
#guard admits chain1
#guard admits chain2

/-- `chain1` is `Guarded`, and the fuel-zero door refuses it, so
`guardedWrong` does not decide `Guarded` — and the corpus never asks. -/
theorem chain1_guarded : chain1.Guarded :=
  (references_guarded_decidable chain1).mp (by decide)

theorem guardedWrong_is_not_the_decision :
    ¬ (∀ d : Document, guardedWrong d = true ↔ d.Guarded) := by
  intro h
  have := (h chain1).mpr chain1_guarded
  exact absurd this (by decide)

/-! ############################################################
## §4 — the refusal taxonomy, exhibited per case

`documentRefusal` (`Ingest.lean:400-402`) is
`if d.guarded then .illFormed else .unguardedCycle`: guardedness is
tested FIRST, so an unguarded document earns `unguardedCycle` whatever
else is wrong with it.  The TypeScript door runs `admitNode` over every
table entry BEFORE its guardedness filter, so it earns the entry's own
refusal instead.  The pair below is the divergence — same bytes, both
doors refuse, different names.  `RESULTS.md` §4. -/

/-- An unguarded cycle whose table entry is ALSO ill formed (`b` before
`a`).  Lean answers `unguardedCycle`; TypeScript answers `illFormed`. -/
def unsortedAndCyclic : Document :=
  { references := [("A", .struct [("b", false, .reference "A"),
                                  ("a", false, .str)])],
    representation := .reference "A" }

/-- Its control, with the cycle removed: both doors say `illFormed`. -/
def unsortedOnly : Document :=
  { references := [("A", .struct [("b", false, .str), ("a", false, .str)])],
    representation := .reference "A" }

#guard (match ingestDocument unsortedAndCyclic.envelope with
        | .error .unguardedCycle => true | _ => false)
#guard (match ingestDocument unsortedOnly.envelope with
        | .error .illFormed => true | _ => false)

-- The refusal is NOT a coincidental `illFormed` from an earlier check:
-- the two witness tables the builder shipped still earn `unguardedCycle`
-- by name, and so does a cycle with an unrelated defect on it.
#guard (match ingestDocument aliasCycle.envelope with
        | .error .unguardedCycle => true | _ => false)
#guard (match ingestDocument bareStructCycle.envelope with
        | .error .unguardedCycle => true | _ => false)

/-- A DEAD cyclic entry, unreachable from the root.  The packet's claim
scope says "A DEAD table entry is not refused"
(`PDD-3.contract.md:147`); a dead entry that CYCLES is.  Both doors
agree, so this is a claim-scope imprecision, not a divergence. -/
def deadCycle : Document :=
  { references := [("A", .reference "A")], representation := .str }

#guard (match ingestDocument deadCycle.envelope with
        | .error .unguardedCycle => true | _ => false)

/-- A DANGLING name is admitted, exactly as the packet says. -/
def dangling : Document :=
  { references := [("A", .reference "Nope")], representation := .reference "A" }

#guard admits dangling

/-! ############################################################
## §5 — HOLE: the door is EXPONENTIAL in the table size

The packet's `DECREASES` line reads "`|dom(R)| - |visited|` for the
guardedness search" (`PDD-3.contract.md:243`).  There is no visited set
in `Document.settles`, on either side of the wire: the variant is the
FUEL, structurally, and the search re-walks every path.  On a table
whose entries each name the next one twice, the door is `Θ(2ⁿ)`.

`fanTable n` is ACYCLIC, has `n+1` entries, and is admitted.  Timings for
both doors are in `RESULTS.md` §5; the short version is that a
7657-byte document with 25 table entries takes the Lean door 303
seconds.  This is the ingestion door for FOREIGN content, so the input
is by definition attacker-chosen. -/

def fanEntry (i : Nat) : String × Ast :=
  (s!"n{i}", .struct [("x", false, .reference s!"n{i+1}"),
                      ("y", false, .reference s!"n{i+1}")])

def fanTable (n : Nat) : Document :=
  { references := (List.range n).map fanEntry ++ [(s!"n{n}", .str)],
    representation := .reference "n0" }

-- Small enough to run at elaboration; the curve is in `RESULTS.md`.
#guard (fanTable 8).guarded
#guard (fanTable 8).references.length == 9

/-! ############################################################
## §6 — FAILED ATTACKS on the round trip and the decoder

Each of these was an attempt to find a spelling the decoder accepts that
the encoder cannot produce, or a `repNorm` that is not idempotent.  All
of them fail; the castle is right here. -/

-- Key order is EXACT on both new arms: the canonical spelling decodes
-- and no permutation of it does.
#guard (Ast.ofRepresentationJson
  (.obj [("$ref", .str "A"), ("_tag", .str "Reference")])).isSome
#guard !(Ast.ofRepresentationJson
  (.obj [("_tag", .str "Reference"), ("$ref", .str "A")])).isSome
#guard (Ast.ofRepresentationJson
  (.obj [("_tag", .str "Suspend"), ("checks", .arr []),
         ("thunk", Ast.str.toRepresentationJson)])).isSome
#guard !(Ast.ofRepresentationJson
  (.obj [("thunk", Ast.str.toRepresentationJson), ("checks", .arr []),
         ("_tag", .str "Suspend")])).isSome
#guard !(Ast.ofRepresentationJson
  (.obj [("checks", .arr []), ("_tag", .str "Suspend"),
         ("thunk", Ast.str.toRepresentationJson)])).isSome

/-- Adversarial nesting for `repNorm`: suspends inside suspends inside a
union carrying a reference and a literal null, which is where the one
collapse of register R13 lives. -/
def nastySusp : Ast :=
  .susp (.susp (.union [.lit .null, .reference "A", .susp (.lit .null)] .anyOf))

#guard nastySusp.repNorm.repNorm.payload == nastySusp.repNorm.payload
#guard (match Ast.ofRepresentationJson nastySusp.toRepresentationJson with
        | some b => b.payload == nastySusp.repNorm.payload
        | none => false)
#guard (match Ast.ofRepresentationJson deepRef.toRepresentationJson with
        | some b => b.payload == deepRef.repNorm.payload
        | none => false)

-- The document round trip, on a table with content in it.
#guard (match Document.ofEnvelope chain2.envelope with
        | some d => d.payload == chain2.repNorm.payload
        | none => false)
#guard (match Document.ofEnvelope guardedList.envelope with
        | some d => d.payload == guardedList.repNorm.payload
        | none => false)

/-- FAILED: the table's key order is not a spelling the door refuses —
`canonValue` sorts it before the decoder sees it, so an out-of-order
table is normalised, not turned away.  The TypeScript comment says the
same, so the doors agree; the `Document.WF` strict-order clause is
therefore unreachable at the door except through DUPLICATE keys, which
is `RESULTS.md` §4. -/
def outOfOrder : Document :=
  { references := [("B", .str), ("A", .str)], representation := .str }

#guard admits outOfOrder

/-- FAILED: the empty table key is refused, by both doors. -/
def emptyKey : Document :=
  { references := [("", .str)], representation := .str }

#guard (match ingestDocument emptyKey.envelope with
        | .error .illFormed => true | _ => false)

-- FAILED: `ingest`, the bare-code arm, still refuses a document with a
-- table by its own name.  Narrowing `nonEmptyReferences` widened
-- nothing.
#guard (match ingest guardedList.envelope with
        | .error .nonEmptyReferences => true | _ => false)
#guard (match ingest chain2.envelope with
        | .error .nonEmptyReferences => true | _ => false)

/-! ############################################################
## §7 — the bytes door does not reach the document plane

`ingestBytes` (`Ingest.lean:939-942`) is `Cas.Json.parse` composed with
the BARE-CODE arm.  There is no `ingestDocumentBytes`, so the
acquisition loop's read half stops one stage short of the plane this
ticket opened: every document that arrives as BYTES is refused
`nonEmptyReferences`.

Not a break — nothing claims otherwise — but the composition the
TypeScript side has (`Materialize.fromPayload` takes bytes and reads a
document) has no Lean twin, and the duplicate-key divergence of
`RESULTS.md` §4 lives exactly in that gap.  Written out so the gap is
citable: -/

def ingestDocumentBytes (s : String) : Except IngestRefusal Document :=
  match Cas.Json.parse s with
  | some v => ingestDocument (deNumNorm v)
  | none => .error .notASchema

#guard (match ingestDocumentBytes guardedList.payload with
        | .ok d => d.payload == guardedList.payload
        | .error _ => false)
#guard (match ingestBytes guardedList.payload with
        | .error .nonEmptyReferences => true | _ => false)

/-- The duplicate-key witness of `RESULTS.md` §4, as bytes: Lean's parser
keeps both pairs and the strict-order clause refuses; `JSON.parse` keeps
the LAST and the TypeScript door admits.  Lean's answer here is
`unguardedCycle`, because `Document.lookup` takes the FIRST pair — the
two doors read DIFFERENT DOCUMENTS out of one byte string. -/
def dupHarmlessLast : String :=
  "{\"revision\":1,\"value\":{\"references\":{\"A\":{\"$ref\":\"A\",\"_tag\":\"Reference\"},\"A\":{\"_tag\":\"String\",\"checks\":[]}},\"representation\":{\"_tag\":\"String\",\"checks\":[]}}}"

#guard (match ingestDocumentBytes dupHarmlessLast with
        | .error .unguardedCycle => true | _ => false)

/-- The pre-C6 control for the same hazard — a duplicate `_tag` on a NODE
with an empty table.  Lean refuses `notASchema`, TypeScript admits.  The
duplicate-key family PREDATES this ticket; what PDD-3 changed is that
the table is read, so a duplicate TABLE key now splits the verdict where
both doors used to answer `nonEmptyReferences`. -/
def dupTagNode : String :=
  "{\"revision\":1,\"value\":{\"references\":{},\"representation\":{\"_tag\":\"String\",\"_tag\":\"Null\",\"checks\":[]}}}"

#guard (match ingestDocumentBytes dupTagNode with
        | .error .notASchema => true | _ => false)

end PDD3.Attack
