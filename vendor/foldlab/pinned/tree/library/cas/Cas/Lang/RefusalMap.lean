import Cas.Lang.Interp

/-!
# The refusal correspondence — the model's clauses against the host's tags

The trust census's AGREEMENT-family gap, closed as far as a DECLARATION
closes it. Both sides of the store boundary have a closed refusal
vocabulary and neither knows the other's: `Cas.Lang.Refusal`
(`Cas/Lang/Interp.lean`) has six clause-named arms, the TypeScript
runtime's `CasError` family (`library/effects/src/cas/Node.ts`) has
seven tagged members, and what crosses the wire is the CLAUSE NAME —
the constructor tag with its payload dropped. Nothing in either tree
said which name meant which. Two vocabularies, one wire, no join.

This module is the join, spelled as DATA. `Refusal.Clause` is the tag
that crosses (`Refusal.clause` is the forgetful map, proved onto);
`CasErrorTag` is the host family, tag for tag, carrying the runtime
`_tag` strings verbatim from `Node.ts`'s `CasErrorTag` constant; and
`Refusal.Clause.hosts` / `CasErrorTag.clause?` are the correspondence
in both directions, with `CasErrorTag.hostOnly` naming what the host
says that the model deliberately does not.

## The correspondence, and why each row holds

- `notWellFormed` ↔ `CasError/NonCanonicalBytes`. The model's
  `Node.WF` is the byte bound the codec quantifies over (payload
  length and reference count below `2^32`,
  `Cas/Core/Node.lean`), so a node that fails it has no canonical
  encoding at all. The host meets the same condition from the decode
  side: bytes that do not decode, or do not re-encode to themselves.
  One condition, two directions of travel.
- `dangling` ↔ `CasError/DanglingReference`. Exact, payload included:
  both carry the missing address, and both are the CAS-002 admission
  clause (`Cas/Core/Admission.lean`).
- `wrongKind` ↔ `CasError/WrongKindReference`. Exact, payload
  included: the offending reference, its declared tag, the resident
  tag.
- `collision` ↔ `CasError/AddressMismatch`. One address, two contents
  — observed at two different moments. The model sees it at
  admission, as `put`'s explicit conflict witness (the occupant
  differs from the incoming node); the host sees it at read, when the
  bytes served at an address do not hash to it. Both are impossible
  above Level 1 of the hash-hypothesis lattice (CAS-003) and both are
  surfaced rather than argued away, which is why they are the same
  row.
- `noObject` ↔ `CasError/ContentNotFound`. Exact: a caller-requested
  address the store does not hold. Admission-time missing references
  stay the distinct `dangling` row on both sides.
- `failed` ↔ `CasError/StoreFailure`. Both are the catch-all that is
  NOT a verdict about content — a backend that failed, a digest that
  failed, an input that is not a node; on the model side, a program
  fault such as `Cas/Lang/Defun.lean`'s dangling answer index. Both
  carry a free-form reason and nothing else.

## The host-only row, stated as such

`CasError/UnknownKind` has no model arm, and that is a decision rather
than an omission. The model's `Cas.Node` carries `version` and `tag`
as OPAQUE bytes; admission never consults them except inside the
wrong-kind reference check, so the store's judgment admits every tag
as content. `UnknownKind` is a verdict about the RUNTIME's
interpretive competence — which versioned kinds this host knows how to
read — not about the content. `Node.ts` says the same thing in its own
words: a tag the registry has not ratified is still admitted as
content. A host-only row is the honest shape for that, and declaring
it is what makes the totality theorem below say something.

## What is proved

Totality in both directions —
`Refusal.Clause.hosts_ne_nil` (every model clause has at least one
host spelling) and `CasErrorTag.mapped_or_hostOnly` (every host tag is
either the image of a clause or declared host-only, with nothing in
both by `CasErrorTag.clause?_none_iff_hostOnly`). Distinctness where
the map claims injectivity — `Refusal.Clause.hosts_disjoint` and its
decidable form `Refusal.Clause.hosts_nodup`, plus
`CasErrorTag.clause?_hosts`, which is the inverse actually inverting.
And that the vocabularies are vocabularies at all: the wire spellings
collide on neither side, and `Refusal.clause` is onto, so no clause
row is dead.

## What is NOT proved, and is the follow-on

This is a DECLARATION, not a gate. Nothing here reads `Node.ts`, so
nothing here can go red when the host adds an eighth member or renames
a tag — the strings below are a hand mirror, in exactly the sense
`Cas/Backend/Admission.lean`'s clause column is. The map is spelled as
first-order lists and total functions so an emitter can print the join
table the way `emitgrammar` prints the grammar manifest, and the
printed table is what a byte gate would then hold `Node.ts` to.
owed(refusal-join-emitter): the emitter that prints this join as the
generated interchange document.
owed(refusal-join-gate): the byte gate that holds the TypeScript
`CasErrorTag` constant to the printed document, which is the step that
turns this declaration into agreement.
-/

namespace Cas.Lang

/-! ## The model side — the clause that crosses the wire -/

/-- The refusal's CLAUSE: the constructor tag with its payload
forgotten. This is what crosses the boundary — a refused exchange
names its clause, never its Lean value — so it is the carrier the
correspondence is stated over. -/
inductive Refusal.Clause where
  | notWellFormed
  | dangling
  | wrongKind
  | collision
  | noObject
  | failed
  deriving DecidableEq, Repr

/-- Every clause, in `Refusal`'s own constructor order. -/
def Refusal.Clause.all : List Refusal.Clause :=
  [.notWellFormed, .dangling, .wrongKind, .collision, .noObject, .failed]

/-- The enumeration is the type. -/
theorem Refusal.Clause.all_complete (c : Refusal.Clause) : c ∈ all := by
  cases c <;> decide

/-- The model's spelling of a clause: the Lean constructor name, which
is also the name the estate's prose and the TypeScript comments already
use for it. -/
def Refusal.Clause.wire : Refusal.Clause → String
  | .notWellFormed => "notWellFormed"
  | .dangling => "dangling"
  | .wrongKind => "wrongKind"
  | .collision => "collision"
  | .noObject => "noObject"
  | .failed => "failed"

/-- The forgetful map: a refusal's clause. -/
def Refusal.clause : Refusal → Refusal.Clause
  | .notWellFormed => .notWellFormed
  | .dangling _ => .dangling
  | .wrongKind _ _ _ => .wrongKind
  | .collision _ => .collision
  | .noObject _ => .noObject
  | .failed _ => .failed

private def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- The clause vocabulary has no dead rows: every clause is the clause
of some refusal. Stated because a correspondence between vocabularies
is worth nothing if one of them names conditions that cannot arise. -/
theorem Refusal.clause_surjective (c : Refusal.Clause) :
    ∃ r : Refusal, r.clause = c := by
  cases c
  · exact ⟨.notWellFormed, rfl⟩
  · exact ⟨.dangling zeroAddr, rfl⟩
  · exact ⟨.wrongKind zeroAddr 0 1, rfl⟩
  · exact ⟨.collision zeroAddr, rfl⟩
  · exact ⟨.noObject zeroAddr, rfl⟩
  · exact ⟨.failed "", rfl⟩

/-- The two clauses the CAS-002 admission judgment can produce. The
model's `Refusal.ofAdmission` lands in exactly this pair, and the pair's
host spellings are exactly the two members `Node.ts` documents as the
admission clauses — which is the one place the two vocabularies already
agreed before this module, unwritten. -/
def Refusal.admissionClauses : List Refusal.Clause := [.dangling, .wrongKind]

theorem Refusal.ofAdmission_clause (e : AdmissionError) :
    (Refusal.ofAdmission e).clause ∈ Refusal.admissionClauses := by
  cases e <;>
    simp [Refusal.ofAdmission, Refusal.clause, Refusal.admissionClauses]

/-! ## The host side — the `CasError` family, tag for tag -/

/-- The TypeScript runtime's CAS error family
(`library/effects/src/cas/Node.ts`), one constructor per member of the
`CasError` union. A HAND MIRROR: this module reads no TypeScript, so
the only thing keeping the two in step today is that they are written
down beside each other. -/
inductive CasErrorTag where
  | addressMismatch
  | nonCanonicalBytes
  | unknownKind
  | danglingReference
  | wrongKindReference
  | contentNotFound
  | storeFailure
  deriving DecidableEq, Repr

/-- Every host tag, in `Node.ts`'s own declaration order. -/
def CasErrorTag.all : List CasErrorTag :=
  [.addressMismatch, .nonCanonicalBytes, .unknownKind, .danglingReference,
   .wrongKindReference, .contentNotFound, .storeFailure]

theorem CasErrorTag.all_complete (t : CasErrorTag) : t ∈ all := by
  cases t <;> decide

/-- The runtime `_tag`, verbatim from the `CasErrorTag` constant in
`Node.ts`. The namespaced spelling is load-bearing over there — a bare
class name at a `catchTag` site never matches — so it is the spelling
carried here. -/
def CasErrorTag.wire : CasErrorTag → String
  | .addressMismatch => "CasError/AddressMismatch"
  | .nonCanonicalBytes => "CasError/NonCanonicalBytes"
  | .unknownKind => "CasError/UnknownKind"
  | .danglingReference => "CasError/DanglingReference"
  | .wrongKindReference => "CasError/WrongKindReference"
  | .contentNotFound => "CasError/ContentNotFound"
  | .storeFailure => "CasError/StoreFailure"

/-! ## The join -/

/-- The host spellings of one model clause. LIST-valued because a host
may in principle spell one model refusal several ways; at this revision
every list is a singleton, which `Refusal.Clause.hosts_nodup` and
`CasErrorTag.clause?_hosts` between them make precise. -/
def Refusal.Clause.hosts : Refusal.Clause → List CasErrorTag
  | .notWellFormed => [.nonCanonicalBytes]
  | .dangling => [.danglingReference]
  | .wrongKind => [.wrongKindReference]
  | .collision => [.addressMismatch]
  | .noObject => [.contentNotFound]
  | .failed => [.storeFailure]

/-- The other direction: the model clause a host tag corresponds to, or
`none` for a host-only tag. Partial ON PURPOSE — `none` is the
declaration that the model deliberately lacks the condition, not a
gap in the table. -/
def CasErrorTag.clause? : CasErrorTag → Option Refusal.Clause
  | .addressMismatch => some .collision
  | .nonCanonicalBytes => some .notWellFormed
  | .unknownKind => none
  | .danglingReference => some .dangling
  | .wrongKindReference => some .wrongKind
  | .contentNotFound => some .noObject
  | .storeFailure => some .failed

/-- The host tags with no model arm, declared as such. See the module
header for why `unknownKind` is one: it is a verdict about this
runtime's interpretive competence, and the store's judgment does not
make verdicts of that kind. -/
def CasErrorTag.hostOnly : List CasErrorTag := [.unknownKind]

/-! ## Totality, both directions -/

/-- Model → host totality: every clause has at least one host
spelling. -/
theorem Refusal.Clause.hosts_ne_nil (c : Refusal.Clause) : c.hosts ≠ [] := by
  cases c <;> decide

/-- Host → model totality: every host tag is either the image of some
clause or declared host-only. Nothing in the host family is
unaccounted for, which is the whole point of writing the host-only list
down instead of leaving the rows out. -/
theorem CasErrorTag.mapped_or_hostOnly (t : CasErrorTag) :
    (∃ c : Refusal.Clause, t ∈ c.hosts) ∨ t ∈ CasErrorTag.hostOnly := by
  cases t
  · exact .inl ⟨.collision, by decide⟩
  · exact .inl ⟨.notWellFormed, by decide⟩
  · exact .inr (by decide)
  · exact .inl ⟨.dangling, by decide⟩
  · exact .inl ⟨.wrongKind, by decide⟩
  · exact .inl ⟨.noObject, by decide⟩
  · exact .inl ⟨.failed, by decide⟩

/-- The two halves of the host family do not overlap: a tag is
host-only exactly when the inverse has nothing to say about it. -/
theorem CasErrorTag.clause?_none_iff_hostOnly (t : CasErrorTag) :
    t.clause? = none ↔ t ∈ CasErrorTag.hostOnly := by
  cases t <;> decide

/-! ## Distinctness, where the map claims it -/

/-- The inverse inverts: a host tag listed under a clause maps back to
exactly that clause. -/
theorem CasErrorTag.clause?_hosts {c : Refusal.Clause} {t : CasErrorTag} :
    t ∈ c.hosts → t.clause? = some c := by
  cases c <;> cases t <;> decide

/-- Distinct clauses claim disjoint host spellings — the injectivity
the map asserts, stated where it bites: no host tag is the agreed
spelling of two different model refusals, so a tag crossing the wire
identifies its clause. -/
theorem Refusal.Clause.hosts_disjoint {c c' : Refusal.Clause}
    (h : c ≠ c') (t : CasErrorTag) : t ∈ c.hosts → t ∉ c'.hosts := by
  cases c <;> cases c' <;> cases t <;>
    first | exact absurd rfl h | decide

/-- The decidable form of the same fact, in the shape an emitter reads:
the six host spellings are pairwise distinct. -/
theorem Refusal.Clause.hosts_nodup : (Refusal.Clause.all.map hosts).Nodup := by
  decide

/-- A host-only tag is the spelling of no clause. The declaration is
honest, not merely asserted. -/
theorem CasErrorTag.hostOnly_unmapped (t : CasErrorTag)
    (h : t ∈ CasErrorTag.hostOnly) (c : Refusal.Clause) : t ∉ c.hosts := by
  cases t <;> cases c <;> revert h <;> decide

/-- Both vocabularies are vocabularies: the model's wire spellings
collide with nothing. -/
theorem Refusal.Clause.wire_nodup : (Refusal.Clause.all.map wire).Nodup := by
  decide

/-- And neither do the host's. -/
theorem CasErrorTag.wire_nodup : (CasErrorTag.all.map wire).Nodup := by
  decide

/-! ## The table, as data for the emitter

The same content as `Refusal.Clause.hosts` and `CasErrorTag.hostOnly`,
carried in row form with the prose each row's join rests on. The
functions are what the theorems above quantify over; the tables are
what a printer walks. `RefusalMap.table_agrees` and
`RefusalMap.hostOnlyTable_hosts` are what keep the two spellings one
spelling. -/

/-- One joined row: a model clause, its host tag, and the one-line
reason the two are the same condition. -/
structure RefusalMap.Row where
  clause : Refusal.Clause
  host : CasErrorTag
  note : String
  deriving Repr

/-- One host-only row: a host tag and why the model lacks it. -/
structure RefusalMap.HostOnlyRow where
  host : CasErrorTag
  note : String
  deriving Repr

/-- THE join table, in clause order. -/
def RefusalMap.table : List RefusalMap.Row := [
  { clause := .notWellFormed, host := .nonCanonicalBytes,
    note := "the byte bound the codec quantifies over, met from the encode side (model) and the decode side (host)" },
  { clause := .dangling, host := .danglingReference,
    note := "the CAS-002 admission clause; both carry the missing address" },
  { clause := .wrongKind, host := .wrongKindReference,
    note := "the CAS-002 kind clause; both carry the reference, its declared tag and the resident tag" },
  { clause := .collision, host := .addressMismatch,
    note := "one address, two contents: the model at admission (put's conflict witness), the host at read (bytes that do not hash to their address)" },
  { clause := .noObject, host := .contentNotFound,
    note := "a requested address the store does not hold; admission-time misses stay the dangling row on both sides" },
  { clause := .failed, host := .storeFailure,
    note := "the catch-all that is not a verdict about content; both carry a free-form reason" }]

/-- THE host-only table. -/
def RefusalMap.hostOnlyTable : List RefusalMap.HostOnlyRow := [
  { host := .unknownKind,
    note := "a verdict about which versioned kinds this runtime interprets, not about the content; the model's node carries version and tag as opaque bytes and admits every tag" }]

/-- The table's clause column is the clause vocabulary, in order. -/
theorem RefusalMap.table_clauses :
    RefusalMap.table.map RefusalMap.Row.clause = Refusal.Clause.all := by
  decide

/-- Every row's host tag is the one the map gives its clause — the
table and the function are one join, not two. -/
theorem RefusalMap.table_agrees :
    RefusalMap.table.all (fun r => decide (r.clause.hosts = [r.host])) := by
  decide

/-- And the host-only table is the host-only list. -/
theorem RefusalMap.hostOnlyTable_hosts :
    RefusalMap.hostOnlyTable.map RefusalMap.HostOnlyRow.host
      = CasErrorTag.hostOnly := by
  decide

end Cas.Lang
