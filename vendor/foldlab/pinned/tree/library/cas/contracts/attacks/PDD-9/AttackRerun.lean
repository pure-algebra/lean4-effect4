import Cas.Backend.TreeProgCorrect

/-!
# PDD-9 — the re-run, against the fix pass

The independent breaker's second pass, against the amended packet and
the coverage fix. `Attack.lean` beside this file is UNEDITED and stays
the record against `b5ad3c1d` / `db2c8344`; this file is the record
against the fix, in PDD-1's shape (`contracts/attacks/PDD-1/AttackAmended.lean`).

```
FIRST PASS  e2703228  attack/opus-cc-mac/pdd-9 — STANDS, HOLE-1 open,
                      NOTE-2 … NOTE-5
PACKET      e2b364e8  the ledger opens — HOLE-1, NOTE-2, NOTE-3
CASTLE      05dc3b65  close HOLE-1 — all seven registered programs run
PACKET      c984a7b5  fill FIXED-BY, re-run the transcripts
```

WHAT IS CHECKED HERE.

1. HOLE-1's closure, COUNTED rather than read: which of the grammar's
   ten clauses had an executed consequence before, and which have one
   now. `(wire tag, reference count)` separates all ten clauses, so the
   count is a computation and not a reading of the source.
2. That the breaker's oracle was adopted FAITHFULLY — a definitional
   identity, not a resemblance — and that the hand-chosen `eraseIdx 2`
   is pinned to it inside the castle.
3. That `Executed.schemaTerm` is the REGISTERED term and not a
   truncated lookalike.
4. The builder's two reasoned refusals, ruled on. The
   `treeProg_Triple` refusal is ruled on by COMPUTATION rather than by
   agreement: the one-state residual of the STORE axis is exhibited,
   and shown not to close the gap `paddedShared` opened — which is what
   makes the refusal correct.

Same fences as `Attack.lean`: outside every lake target, elaborated by
`lake env lean contracts/attacks/PDD-9/AttackRerun.lean` from
`library/cas`, no `sorry`, no `native_decide`, digests in `#eval` only.
-/

namespace Cas.Backend.AttackRerun

open Cas Cas.Grammar Cas.Lang Cas.Backend Cas.Vectors.Registry

set_option maxRecDepth 100000

/-! ## 1. The replica, again, and its pin -/

def toyMix (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => (acc * 257 + b.toNat + 1) % 4294967296) 7

def toyAddr (bs : Bytes) : Addr32 :=
  ⟨(List.range 32).map (fun i => UInt8.ofNat (toyMix bs / 256 ^ (i % 4))),
   by simp⟩

#guard Executed.runVerdict toyAddr blobSharedChunk
  ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 2)

/-! ## 2. The oracle was adopted VERBATIM

`Attack.lean` §2 offered `expected H tr := (Tree.flatten H tr).eraseDups`.
The castle's `Executed.expectedWord` is that function, and the identity
below is `rfl` — the two are the same definition, not two definitions
that agree on a corpus. -/

def expected (H : Bytes → Addr32) {t : Ty} (tr : Tree t) : Word :=
  (Tree.flatten H tr).eraseDups

theorem oracle_adopted_verbatim (H : Bytes → Addr32) {t : Ty} (tr : Tree t) :
    Executed.expectedWord H tr = expected H tr := rfl

#print axioms oracle_adopted_verbatim

-- and the castle pins its hand-chosen index against the oracle, on the
-- witness the index was chosen for
#guard Executed.expectedWord toyAddr blobSharedChunk
  == (Tree.flatten toyAddr blobSharedChunk).eraseIdx 2

-- the index is still the SHARPER statement there: it names WHICH
-- occurrence drops, and the neighbouring erasures are not the word
#guard !Executed.runVerdict toyAddr blobSharedChunk
  ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 1)

#guard !Executed.runVerdict toyAddr blobSharedChunk
  ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 3)

/-! ## 3. HOLE-1's closure, counted

`(wire tag, reference count)` separates all ten clauses of `Tree`:
`value`, `chunk`, `schema`, `git` and `genesis` carry no references and
differ by tag; `leaf`, `manifest` and `file` carry one and differ by
tag; `parent` and `entry` carry two and differ by tag. So the clause
set a term reaches is a computation over its `flatten`. -/

def clausesOf {t : Ty} (tr : Tree t) : List (Nat × Nat) :=
  ((Tree.flatten toyAddr tr).map fun b =>
    (b.node.tag.toNat, b.node.refs.length)).eraseDups

/-- The five terms the castle ran at `b5ad3c1d`. -/
def coveredBefore : List (Nat × Nat) :=
  (clausesOf helloValue ++ clausesOf blobTwoLeaves ++ clausesOf fileReadme
    ++ clausesOf gitPinCommit ++ clausesOf blobSharedChunk).eraseDups

/-- All seven registered terms, which `Executed.check` now runs. -/
def coveredNow : List (Nat × Nat) :=
  (coveredBefore ++ clausesOf journalTwo ++ clausesOf Executed.schemaTerm).eraseDups

/-- The kernel `#guard` half after the fix: `helloValue`,
`blobSharedChunk`, `blobTwoLeaves`, `journalTwo`. -/
def coveredInKernel : List (Nat × Nat) :=
  (clausesOf helloValue ++ clausesOf blobSharedChunk ++ clausesOf blobTwoLeaves
    ++ clausesOf journalTwo).eraseDups

-- SEVEN of ten before the fix
#guard coveredBefore.length == 7

-- TEN of ten after it
#guard coveredNow.length == 10

-- and the three that were missing are exactly the three HOLE-1 named:
-- genesis (entry tag, no refs), entry (entry tag, two refs), schema
#guard (coveredNow.filter fun c => !coveredBefore.contains c)
  == [(12, 0), (12, 2), (83, 0)]

-- the kernel half gained `.genesis` and `.entry` and now reaches eight
-- of ten; `.git` and `.schema` stay `#eval`-only, which is the lane's
-- own rule about where large payloads and digests are computed
#guard coveredInKernel.length == 8

#guard (coveredNow.filter fun c => !coveredInKernel.contains c)
  == [(71, 0), (83, 0)]

-- the two new rows answer their terms, recomputed by this hand
#guard Executed.runVerdict toyAddr journalTwo (expected toyAddr journalTwo)

#eval Executed.runVerdict Cas.sha256Addr journalTwo (expected Cas.sha256Addr journalTwo)

#eval Executed.runVerdict Cas.sha256Addr Executed.schemaTerm
  (expected Cas.sha256Addr Executed.schemaTerm)

/-! ## 4. `Executed.schemaTerm` is the REGISTERED term

`tools/EmitPrograms.lean:63-70` builds the schema row in `IO` with the
payload-bound witness; the castle rebuilds it with `Payload.ofBytes`,
which is total and CLAMPS at the bound. The two agree exactly when the
clamp does not bite, and `List.take` returns a PREFIX — so equal lengths
is equality. `Executed.check` asserts the bound before trusting it,
which is the right shape; the length identity is checked here. -/

#guard (Executed.schemaTerm.node toyAddr).payload.length
  == (Cas.Grammar.utf8 vectorDocumentCode.payload).length

#guard (Cas.Grammar.utf8 vectorDocumentCode.payload).length < 4294967296

/-! ## 5. The `treeProg_Triple` refusal, ruled on by computation

The builder declined to strengthen `treeProg_Triple`, arguing that
GROWTH and STORE are two-state facts and that writing them into a
single-state postcondition rederives `treeProg_two_state`.

For GROWTH (`w' = w₀ ++ v` with `v ⊑ tr.flatten H`) and for STORE as
the packet states it (`Word.toStore w' = Word.toStore (w₀ ++ tr.flatten H)`)
the argument is exact: both mention `w₀`, and `Triple`'s `Q` sees only
`w'`.

But it is not the case that NOTHING frame-flavoured is one-state
expressible. This is:

    residency  —  ∀ b ∈ tr.flatten H, Word.find w' b.address = some b.node

"every node of the term is resident at the end", which needs no `w₀`,
is true of the run, and is failed by the "writes nothing" candidate the
packet's adequacy section names. So the refusal cannot rest on
inexpressibility alone.

It rests on something better, and the computation below is the ruling:
residency does NOT exclude `paddedShared`, the very witness that opened
NOTE-2. Adding it to the Triple would therefore not close the gap it was
raised about — it would add a fourth statement of a fact `treeProg_run`
already carries. The refusal is CORRECT, and this is why. -/

def resident (H : Bytes → Addr32) {t : Ty} (tr : Tree t) (w' : Word) : Bool :=
  (Tree.flatten H tr).all fun b => Word.find w' b.address == some b.node

def shiftAns (k : Nat) : PLine → PLine
  | .put v t p refs =>
    .put v t p (refs.map fun r =>
      (r.1, match r.2 with | .ans i => .ans (i + k) | .lit a => .lit a))
  | .load s => .load s

def outsiderNode : Node :=
  ⟨schemeVersion, Ty.value.wireTag, (Payload.utf8 "outside the term").val, []⟩

def outsiderBinding (H : Bytes → Addr32) : Binding :=
  Binding.mk (H (encodeNode outsiderNode)) outsiderNode

def paddedShared : PProg :=
  .put schemeVersion Ty.value.wireTag (Payload.utf8 "outside the term").val []
    :: (treeProg blobSharedChunk).map (shiftAns 1)

def runPair (H : Bytes → Addr32) (p : PProg) : Option (Addr32 × Word) :=
  match runP H p [] with
  | (.done a, w) => some (a, w)
  | _ => none

-- NOTE-2's witness, restated: same answer, admissible, honest, and one
-- binding outside the term
#guard (runPair toyAddr paddedShared).map Prod.snd
  == some (outsiderBinding toyAddr :: expected toyAddr blobSharedChunk)

#guard !((Tree.flatten toyAddr blobSharedChunk).contains (outsiderBinding toyAddr))

-- residency IS one-state, and IS true of the honest run
#guard resident toyAddr blobSharedChunk (expected toyAddr blobSharedChunk)

-- and it is ALSO true of `paddedShared`'s word — so the strongest
-- one-state frame conjunct available does not exclude the witness, and
-- strengthening the Triple with it would buy nothing
#guard resident toyAddr blobSharedChunk
  (outsiderBinding toyAddr :: expected toyAddr blobSharedChunk)

-- what DOES exclude `paddedShared` is LAW F, exactly as the packet says
#guard paddedShared.length != blobSharedChunk.size

/-! ## 6. The first pass's findings, re-checked against the fix

`badShared` is still a different table with the same run at both
digests, and LAW M still kills it — the fix did not touch LAW M and
this is the regression check that says so. The full proof is
`Attack.lean` §6; the computed half is repeated here so this file
stands alone as the re-run record. -/

def demoteAns (src dst : Nat) : PLine → PLine
  | .put v t p refs =>
    .put v t p (refs.map fun r =>
      (r.1, match r.2 with
            | .ans i => if i == src then .ans dst else .ans i
            | .lit a => .lit a))
  | .load s => .load s

def badShared : PProg := (treeProg blobSharedChunk).map (demoteAns 2 0)

#guard badShared != treeProg blobSharedChunk

#guard badShared.length == blobSharedChunk.size

#guard runPair toyAddr badShared == runPair toyAddr (treeProg blobSharedChunk)

#eval runPair Cas.sha256Addr badShared == runPair Cas.sha256Addr (treeProg blobSharedChunk)

/-! ## 7. The census delta the packet's re-run block does not print

`Executed.expectedWord` is axiom-free and `Executed.runVerdict` carries
`[propext]`, both as the packet now prints. The third `Executed`
declaration the fix introduced is not printed there:

```
Cas.Backend.Executed.schemaTerm  → [propext, Classical.choice, Quot.sound]
Cas.Backend.Executed.check       → [propext, Classical.choice, Quot.sound]
```

Traced: not `Payload.ofBytes` (which prints `[propext, Quot.sound]`) but
`Cas.Vectors.Registry.vectorDocumentCode`, i.e. `Cas.Schema.Described.code`
in the fenced schema plane. All five terms `check` ran before the fix
print `[propext, Quot.sound]`, so the axiom is NEW TO `check` with this
pass and is inherited, not minted.

It bears on nothing the kernel checks: `check` is an `IO Unit` run by
`#eval` through the compiler, no kernel `#guard` mentions `schemaTerm`,
and none of the nine public theorems does either — every one of them
still prints `[propext, Quot.sound]`. Recorded as NOTE-6 in `RESULTS.md`
because the packet's footprint block now names two of the three, under a
header that says "no `Classical.choice`". -/

end Cas.Backend.AttackRerun
