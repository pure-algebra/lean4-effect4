import Cas.Backend.TreeProgCorrect

/-!
# PDD-9 — the adversarial record

WHAT THIS FILE IS. The independent breaker's attack against the PDD-9
contract packet (`library/cas/contracts/PDD-9.contract.md`, commit
`db2c8344`) and its castle
(`library/cas/Cas/Backend/TreeProgCorrect.lean`, commit `b5ad3c1d`).
Every adversarial term, every drifted table and every kernel-checked
verification the attack produced is here, whether it broke something or
not: a failed break attempt is the packet's earned confidence, and
earned confidence is record too.

SUBJECT COMMITS.

```
PACKET  e45a9779  stated before the module exists
CASTLE  b5ad3c1d  treeProg correctness — the two walks, the denotation,
                  the run
PACKET  db2c8344  amended after the module landed — placement, battery,
                  controls, gates
```

IMPORTS. `Cas.Backend.TreeProgCorrect` only, which pulls the castle's
own import set. Nothing imports this file.

THIS FILE MUST NOT ENTER ANY LAKE LIBRARY TARGET. It is adversarial
apparatus, not library content. It sits under `contracts/attacks/`,
outside every `srcDir` and `globs` that `lakefile.toml` declares for
`Cas`, `CasWp`, `CasBackend`, `CasExamples` and `Gate`, so it is
outside `Walk.libraryImports` and moves no byte of
`surface/cas-surface.json`, `surface/cas-obligations.json`,
`surface/cas-laws.json` or `docs/lab-core/ENVIRONMENT.json`. It is
elaborated by hand —
`lake env lean contracts/attacks/PDD-9/Attack.lean` from `library/cas`
— and never by `lake build`. Adding it to a target is a promotion, and
a promotion is a ruling.

NO `sorry`, no `native_decide`, no `ofReduceBool`. Digest computation
runs in `#eval`, never in kernel `decide`, per this lane's law
(`library/cas/AGENTS.md`); the kernel half runs at a toy address
function whose separation over this corpus is MEASURED in §5 rather
than assumed.

Verdict, findings and the full failed-attempt list: `RESULTS.md`
beside this file.
-/

namespace Cas.Backend.Attack

open Cas Cas.Grammar Cas.Lang Cas.Backend Cas.Vectors.Registry

set_option maxRecDepth 100000

/-! ## 1. The toy address function, replicated

`Executed.toyAddr` is `private` to the castle, so the attack cannot name
it. It is restated here byte for byte, and the restatement is PINNED by
reproducing two of the castle's own guards against it. A replica that
had drifted would fail them. -/

def toyMix (bs : Bytes) : Nat :=
  bs.foldl (fun acc b => (acc * 257 + b.toNat + 1) % 4294967296) 7

def toyAddr (bs : Bytes) : Addr32 :=
  ⟨(List.range 32).map (fun i => UInt8.ofNat (toyMix bs / 256 ^ (i % 4))),
   by simp⟩

-- the castle's own two witnesses, recomputed through the replica
#guard Executed.runVerdict toyAddr helloValue (Tree.flatten toyAddr helloValue)

#guard Executed.runVerdict toyAddr blobSharedChunk
  ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 2)

/-! ## 2. The expected word, as an ORACLE rather than a hand-written index

The castle names the deduplicated word by `eraseIdx 2` — an index a
human chose for one term. The general fact is that the run's word is
`flatten` with LATER duplicates dropped, which is a function of the
term. Stating it that way is what lets the corpus below be adversarial
rather than curated: no witness needs a hand-computed erasure list. -/

def expected (H : Bytes → Addr32) {t : Ty} (tr : Tree t) : Word :=
  (Tree.flatten H tr).eraseDups

-- the oracle agrees with the castle's hand-written index on its own witness
#guard expected toyAddr blobSharedChunk
  == (Tree.flatten toyAddr blobSharedChunk).eraseIdx 2

#guard Executed.runVerdict toyAddr blobSharedChunk (expected toyAddr blobSharedChunk)

/-! ## 3. LAW X's coverage — the registered terms the castle does not run

`tools/EmitPrograms.lean:45-70` registers SEVEN programs. `Executed.check`
runs five of them: `valueSingle`, `blobTwoLeaves`, `fileReadme`,
`gitPinCommit`, `sharedChunk`. `journalTwoEntries` and
`schemaVectorDocument` are named nowhere in the castle, at either digest.

The consequence for the constructor coverage: `.genesis`, `.entry` and
`.schema` — three of the grammar's ten clauses, and the two DEEPEST
reference chains the registry has — acquire no executed consequence in
the castle at all.

Run here. Both pass, so this is a coverage claim to correct, not a
defect to fix. -/

def schemaTerm : Tree .schema :=
  .schema (Payload.ofBytes (Cas.Grammar.utf8 vectorDocumentCode.payload))

#guard Executed.runVerdict toyAddr journalTwo (expected toyAddr journalTwo)

#eval Executed.runVerdict Cas.sha256Addr journalTwo (expected Cas.sha256Addr journalTwo)

#eval Executed.runVerdict toyAddr schemaTerm (expected toyAddr schemaTerm)

#eval Executed.runVerdict Cas.sha256Addr schemaTerm (expected Cas.sha256Addr schemaTerm)

/-! ## 4. The adversarial corpus

Deeper than any registered term, and duplication patterns the
`shared-chunk` witness does not reach: two DISTINCT duplicate pairs, a
duplicate that is also the ROOT's own child, a whole duplicated
subtree, a deep spine that duplicates one chunk seven times, and a
journal five entries deep. -/

def cA : Tree .chunk := .chunk (Payload.utf8 "AAAA0123456789ab")
def cB : Tree .chunk := .chunk (Payload.utf8 "BBBB0123456789ab")
def cC : Tree .chunk := .chunk (Payload.utf8 "CCCC0123456789ab")

/-- Two DISTINCT duplicate pairs: `cA` twice and `cB` twice, in leaves
that differ, so no larger subterm is shared. Eleven nodes, nine
bindings. -/
def twoDupPairs : Tree .tree :=
  .parent (.parent (.leaf 0 16 cA) (.leaf 1 16 cB))
          (.parent (.leaf 2 16 cA) (.leaf 3 16 cB))

/-- A duplicate that is also the ROOT's own child: both of the root's
references resolve to ONE address. Five nodes, three bindings. -/
def rootChildDup : Tree .tree := .parent (.leaf 0 16 cC) (.leaf 0 16 cC)

/-- A whole duplicated SUBTREE — five of eleven nodes deduplicate. -/
def subtreeDup : Tree .tree :=
  .parent (.parent (.leaf 0 16 cA) (.leaf 1 16 cB))
          (.parent (.leaf 0 16 cA) (.leaf 1 16 cB))

def spine : Nat → Tree .tree
  | 0 => .leaf 0 16 cA
  | (n + 1) => .parent (spine n) (.leaf (UInt32.ofNat (n + 1)) 16 cB)

/-- Nine levels of `parent`, twenty-six nodes, nineteen bindings —
deeper than `journal-two-entries`, the registry's deepest. -/
def deepSpine : Tree .tree := spine 8

def fileOf (nm : String) (body : String) : Tree .file :=
  .file (Name.utf8 nm) (Name.utf8 "text/plain")
    (.manifest 1 16 1 (.leaf 0 16 (.chunk (Payload.utf8 body))))

def journalN : Nat → Tree .entry
  | 0 => .genesis
  | (n + 1) =>
    .entry (Payload.utf8 s!"note {n + 1}")
      (fileOf s!"f{n + 1}.txt" s!"body {n + 1}") (journalN n)

/-- Five entries over genesis — twenty-six nodes, no sharing, the
longest `.entry` chain anywhere. -/
def deepJournal : Tree .entry := journalN 5

-- the node counts and the dedup counts, pinned
#guard twoDupPairs.size == 11 && (expected toyAddr twoDupPairs).length == 9

#guard rootChildDup.size == 5 && (expected toyAddr rootChildDup).length == 3

#guard subtreeDup.size == 11 && (expected toyAddr subtreeDup).length == 6

#guard deepSpine.size == 26 && (expected toyAddr deepSpine).length == 19

#guard deepJournal.size == 26 && (expected toyAddr deepJournal).length == 26

-- LAW R's conclusion, EXECUTED, on every one of them
#guard Executed.runVerdict toyAddr twoDupPairs (expected toyAddr twoDupPairs)

#guard Executed.runVerdict toyAddr rootChildDup (expected toyAddr rootChildDup)

#guard Executed.runVerdict toyAddr subtreeDup (expected toyAddr subtreeDup)

#guard Executed.runVerdict toyAddr deepSpine (expected toyAddr deepSpine)

#guard Executed.runVerdict toyAddr deepJournal (expected toyAddr deepJournal)

-- LAW W and LAW F, executed on the same corpus
#guard twoDupPairs.table == treeProg twoDupPairs

#guard rootChildDup.table == treeProg rootChildDup

#guard subtreeDup.table == treeProg subtreeDup

#guard deepSpine.table == treeProg deepSpine

#guard deepJournal.table == treeProg deepJournal

#guard (treeProg deepSpine).length == deepSpine.size

#guard (treeProg deepJournal).length == deepJournal.size

/-! ### The same verdicts at the production digest -/

def checkAdversarial : IO Unit := do
  let rows : List (String × Bool) :=
    [("twoDupPairs",
       Executed.runVerdict Cas.sha256Addr twoDupPairs
         (expected Cas.sha256Addr twoDupPairs)),
     ("rootChildDup",
       Executed.runVerdict Cas.sha256Addr rootChildDup
         (expected Cas.sha256Addr rootChildDup)),
     ("subtreeDup",
       Executed.runVerdict Cas.sha256Addr subtreeDup
         (expected Cas.sha256Addr subtreeDup)),
     ("deepSpine",
       Executed.runVerdict Cas.sha256Addr deepSpine
         (expected Cas.sha256Addr deepSpine)),
     ("deepJournal",
       Executed.runVerdict Cas.sha256Addr deepJournal
         (expected Cas.sha256Addr deepJournal)),
     ("journalTwo",
       Executed.runVerdict Cas.sha256Addr journalTwo
         (expected Cas.sha256Addr journalTwo)),
     ("schemaVectorDocument",
       Executed.runVerdict Cas.sha256Addr schemaTerm
         (expected Cas.sha256Addr schemaTerm))]
  for (name, ok) in rows do
    unless ok do
      throw (IO.userError s!"PDD-9 attack: {name}'s run does not answer its term")
  IO.println
    ("PDD-9 attack: seven adversarial and uncovered terms run at the "
      ++ "production digest — every answer is its term's address and every "
      ++ "word is flatten deduplicated")

#eval checkAdversarial

/-! ## 5. Does the toy address function SEPARATE?

PDD-2's NOTE-5 is the precedent: its `Falsifier.lenAddr` addresses a
node by its encoded LENGTH, so witnesses stated at it can be artifacts
of collision. `toyAddr` is a 32-bit mix spread over four distinct bytes,
so the question is empirical and is answered here rather than asserted.

A guard that passed only because `toyAddr` collided would show up as a
word SHORTER than the distinct-node count. `sepReport` prints
(distinct NODES, distinct ADDRESSES) over each term's `flatten`; equality
of the two numbers is separation over exactly the preimages the guards
use. -/

def sepReport (w : Word) : Nat × Nat :=
  ((w.map Binding.node).eraseDups.length,
   (w.map Binding.address).eraseDups.length)

def separates (H : Bytes → Addr32) {t : Ty} (tr : Tree t) : Bool :=
  let r := sepReport (Tree.flatten H tr)
  r.1 == r.2

#guard separates toyAddr blobSharedChunk

#guard separates toyAddr blobTwoLeaves

#guard separates toyAddr journalTwo

#guard separates toyAddr helloValue

#guard separates toyAddr twoDupPairs

#guard separates toyAddr rootChildDup

#guard separates toyAddr subtreeDup

#guard separates toyAddr deepSpine

#guard separates toyAddr deepJournal

-- and the dedup counts do not depend on WHICH digest: the toy function
-- and the production digest agree on every term of the corpus, so no
-- guard above is an artifact of the toy.
def checkSeparation : IO Unit := do
  let rows : List (String × Nat × Nat) :=
    [("blobSharedChunk", (expected toyAddr blobSharedChunk).length,
       (expected Cas.sha256Addr blobSharedChunk).length),
     ("journalTwo", (expected toyAddr journalTwo).length,
       (expected Cas.sha256Addr journalTwo).length),
     ("twoDupPairs", (expected toyAddr twoDupPairs).length,
       (expected Cas.sha256Addr twoDupPairs).length),
     ("rootChildDup", (expected toyAddr rootChildDup).length,
       (expected Cas.sha256Addr rootChildDup).length),
     ("subtreeDup", (expected toyAddr subtreeDup).length,
       (expected Cas.sha256Addr subtreeDup).length),
     ("deepSpine", (expected toyAddr deepSpine).length,
       (expected Cas.sha256Addr deepSpine).length),
     ("deepJournal", (expected toyAddr deepJournal).length,
       (expected Cas.sha256Addr deepJournal).length)]
  for (name, toy, prod) in rows do
    unless toy == prod do
      throw (IO.userError
        s!"PDD-9 attack: {name} deduplicates differently at the two digests")
  IO.println "PDD-9 attack: toy and production digests deduplicate identically"

#eval checkSeparation

/-! ## 6. The drifted table — what each law can and cannot see

The packet's adequacy section names, as its second wrong-but-passing
candidate, "a lowering that emits the right SHAPES with wrong operands",
and says it "dies at LAW M, because the resolved reference addresses are
then not the children's answers".

That reason is too narrow, and the sharpest test of it is a term with a
SHARED subterm, where two different answer indices resolve to the SAME
address. `badShared` is `treeProg blobSharedChunk` with the second
leaf's operand rewritten from `.ans 2` to `.ans 0` — a different line,
the same node, hence the same address at every `H`.

The result is that LAW F cannot see it, and the RUN cannot see it at any
digest — but LAW M still kills it, for a reason the packet does not
state: `embed` builds a `Prog` whose continuations are FUNCTIONS of the
answers, so the equality quantifies over every address the interpreter
could hand back, and no coincidence at one digest discharges it. LAW M
is therefore strictly stronger than run agreement, and that strength is
what closes this class. -/

def demoteAns (src dst : Nat) : PLine → PLine
  | .put v t p refs =>
    .put v t p (refs.map fun r =>
      (r.1, match r.2 with
            | .ans i => if i == src then .ans dst else .ans i
            | .lit a => .lit a))
  | .load s => .load s

def badShared : PProg := (treeProg blobSharedChunk).map (demoteAns 2 0)

def runPair (H : Bytes → Addr32) (p : PProg) : Option (Addr32 × Word) :=
  match runP H p [] with
  | (.done a, w) => some (a, w)
  | _ => none

-- it is a DIFFERENT table: the generated TypeScript would name `a0`
-- where the castle's names `a2`
#guard badShared != treeProg blobSharedChunk

-- LAW F cannot see it
#guard badShared.length == blobSharedChunk.size

-- the RUN cannot see it — same answer, same word, at the toy digest
#guard runPair toyAddr badShared == runPair toyAddr (treeProg blobSharedChunk)

-- nor at the production one
#eval runPair Cas.sha256Addr badShared == runPair Cas.sha256Addr (treeProg blobSharedChunk)

/-- Read the reference list of the `i`-th put of a program, feeding the
continuations the addresses supplied. This is the probe that makes the
denotation's quantification visible: a `Prog`'s continuation is a
function, so the operand a line names is recoverable by applying it at
addresses of one's own choosing. -/
def putRefsAt : Nat → List Addr32 → Prog CasSig Addr32 → List Ref
  | 0, _, .vis (.put n) _ => n.refs
  | (i + 1), (a :: as), .vis (.put _) k => putRefsAt i as (k a)
  | _, _, _ => []

def zeroA : Addr32 := ⟨List.replicate 32 0, by simp⟩
def oneA : Addr32 := ⟨List.replicate 32 1, by simp⟩
def twoA : Addr32 := ⟨List.replicate 32 2, by simp⟩

-- the drifted table's third put names the FIRST answer; the castle's
-- names the THIRD. At distinct answers the two denotations part.
#guard putRefsAt 3 [zeroA, oneA, twoA] (embed badShared)
  != putRefsAt 3 [zeroA, oneA, twoA] (embed (treeProg blobSharedChunk))

/-- **THE DRIFT DIES AT LAW M.** The wrong-operand lowering whose runs
agree with the castle's at every digest is nonetheless excluded by the
meaning theorem — kernel-checked, no `sorry`. -/
theorem badShared_dies_at_LAW_M : embed badShared ≠ Tree.prog blobSharedChunk := by
  rw [← embed_treeProg blobSharedChunk]
  intro h
  exact absurd (congrArg (putRefsAt 3 [zeroA, oneA, twoA]) h) (by decide)

#print axioms badShared_dies_at_LAW_M

/-! ## 7. LAW X's guard, mutated

The packet records two planted defects. Both were reproduced against the
castle by hand (see `RESULTS.md`). Here are the guard-level variants,
including one shape the control set does not cover. -/

def transpose01 (w : Word) : Word :=
  match w with
  | a :: b :: rest => b :: a :: rest
  | _ => w

-- the builder's control: the dedup POSITION
#guard !Executed.runVerdict toyAddr blobSharedChunk
  ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 1)

-- a shape the control set does not cover: a TRANSPOSITION rather than an
-- erasure. The word's length and its multiset of bindings are unchanged,
-- so a count-valued or bag-valued guard would pass it; the castle's
-- guard is a list equality and does not.
#guard !Executed.runVerdict toyAddr blobSharedChunk
  (transpose01 ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 2))

#guard (transpose01 ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 2)).length
  == ((Tree.flatten toyAddr blobSharedChunk).eraseIdx 2).length

-- and §3.5's appending duplicate put, refuted positively as the packet claims
#guard !Executed.runVerdict toyAddr blobSharedChunk
  (Tree.flatten toyAddr blobSharedChunk)

/-! ## 8. What `treeProg_Triple` alone does not say

`Triple H p P Q` is `∀ w, P w → ∃ a w', runP H p w = (.done a, w') ∧ Q a w'`
(`Cas/Lang/Wp.lean:552`). `treeProg_Triple`'s postcondition is
`a = tr.address H ∧ Word.wf w' = true ∧ Honest H w'` — the ANSWER axis and
the two invariants, and NOT the GROWTH or STORE axes the packet's LAW R
block calls load-bearing. Those live in `treeProg_run` and
`treeProg_two_state`, which are the theorems that carry the frame.

The witness: prepend one unrelated put and shift every operand. The run
still answers `tr.address H`; the final word is still admissible and
still honest (every binding is minted by `put`, so its address IS the
digest of its node's pre-image); and the word contains a binding that is
not in `tr.flatten H` at all. `treeProg_Triple`'s postcondition does not
exclude this run; the FRAME half of LAW R does. -/

def shiftAns (k : Nat) : PLine → PLine
  | .put v t p refs =>
    .put v t p (refs.map fun r =>
      (r.1, match r.2 with | .ans i => .ans (i + k) | .lit a => .lit a))
  | .load s => .load s

def outsider : PLine :=
  .put schemeVersion Ty.value.wireTag (Payload.utf8 "outside the term").val []

def paddedShared : PProg := outsider :: (treeProg blobSharedChunk).map (shiftAns 1)

def outsiderBinding (H : Bytes → Addr32) : Binding :=
  Binding.mk (H (encodeNode ⟨schemeVersion, Ty.value.wireTag,
    (Payload.utf8 "outside the term").val, []⟩))
    ⟨schemeVersion, Ty.value.wireTag, (Payload.utf8 "outside the term").val, []⟩

-- ANSWER: the padded table still answers the term's own address
#guard (runPair toyAddr paddedShared).map Prod.fst
  == some (Tree.address toyAddr blobSharedChunk)

-- the final word is the outsider's binding followed by the term's word
#guard (runPair toyAddr paddedShared).map Prod.snd
  == some (outsiderBinding toyAddr :: expected toyAddr blobSharedChunk)

-- INVARIANTS: still admissible, and every binding still honest
#guard Word.wf (outsiderBinding toyAddr :: expected toyAddr blobSharedChunk)

#guard (outsiderBinding toyAddr :: expected toyAddr blobSharedChunk).all
  (fun b => b.address == toyAddr (encodeNode b.node))

-- FRAME: and yet it wrote a binding that is nowhere in the term's flatten
#guard !((Tree.flatten toyAddr blobSharedChunk).contains (outsiderBinding toyAddr))

-- the padded table is of course excluded by LAW F, which is the point of
-- LAW F being in the packet: no ONE law carries the set.
#guard paddedShared.length != blobSharedChunk.size

end Cas.Backend.Attack
