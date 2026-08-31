# PDD-9 — the breaker's verdict

## STATUS — **STANDS-AMENDED. HOLE-1 CLOSED; both refusals CONCURRED.**

Re-run against the fix pass `c984a7b5` on 2026-08-30. HOLE-1 is closed
with mechanical evidence, NOTE-2, NOTE-3 and NOTE-5 are answered, and
the builder's two reasoned refusals are ruled on — both concurred, one
with a correction to its stated ground. One new claim-side row,
**NOTE-6**, worth a line and not a commit of its own. **PDD-9 lands.**

The re-run record is `AttackRerun.lean` beside this file, in PDD-1's
shape; `Attack.lean` is UNEDITED and stays the record against
`b5ad3c1d` / `db2c8344`. It still elaborates clean against the fixed
castle, which is the regression check that the fix took nothing away.

The re-run section is at the bottom of this file.

---


Adversarial record against the PDD-9 contract packet
(`library/cas/contracts/PDD-9.contract.md`, amended at `db2c8344`) and
the castle it specifies (`library/cas/Cas/Backend/TreeProgCorrect.lean`,
`b5ad3c1d`). The machine-checked half is `Attack.lean` beside this file.

```
BREAKER    independent; did not build this castle
PACKET     e45a9779  PDD-9 packet: treeProg correctness, stated before
                     the module exists
CASTLE     b5ad3c1d  PDD-9: treeProg correctness — the two walks, the
                     denotation, the run
PACKET     db2c8344  PDD-9 packet: placement, the landed battery, and
                     the controls
ATTACK     contracts/attacks/PDD-9/Attack.lean
```

# VERDICT — **STANDS** (1 HOLE, 4 NOTEs; no BREAK)

Every gate reproduced. Every law is true. No axiom is smuggled, no
`sorry`, no `native_decide`, no fenced byte moved. Both planted-defect
controls reproduced verbatim by an independent hand, and the drift
device was attacked at the place the packet does not attack it — the
SHIPPED walkers — and held.

One coverage gap: LAW X's executed consequence runs five of the seven
registered programs, and the printed build line calls that "the
registered programs". The two it misses both pass when run here, so the
gap is a claim to correct rather than a defect to fix.

## Findings

### HOLE-1 — LAW X runs five of the seven registered programs, and calls it seven

**Attacked:** LAW X's BATTERY block
(`contracts/PDD-9.contract.md:282-324`) and `Executed.check`
(`Cas/Backend/TreeProgCorrect.lean:852-881`).

The packet writes LAW X's `#eval` half as running

> "over the registered terms of `Cas/Vectors/Registry.lean` that the
> seven generated programs are lowered from
> (`tools/EmitPrograms.lean:45-60`): each term's
> `runP H (treeProg tr) []` is computed and compared, binding for
> binding, against the word and the address the GRAMMAR determines."

`Executed.check` runs `helloValue`, `blobTwoLeaves`, `fileReadme`,
`gitPinCommit` and `blobSharedChunk`. The registry
(`tools/EmitPrograms.lean:47-70`) has seven rows. The two it does not
run:

| program | term | run anywhere in the castle? |
|---|---|---|
| `journalTwoEntries` | `journalTwo` | no — neither `#guard` nor `#eval` |
| `schemaVectorDocument` | the `.schema` row, built in `IO` | no |

The consequence for constructor coverage is sharper than the program
count. Across the whole `Executed` section — kernel `#guard`s and the
`#eval` assert together — three of the grammar's ten clauses acquire NO
executed consequence: **`.genesis`, `.entry` and `.schema`**. `.entry`
is the constructor with the two-child offset arithmetic and the longest
reference chain the registry has; `journalTwo` is the registry's deepest
term at eleven nodes. The kernel half is narrower still: it runs three
terms and reaches six of ten clauses (`.value`, `.chunk`, `.leaf`,
`.parent`, `.manifest`, and `.tree`'s two shapes); `.file` and `.git`
are `#eval`-only.

The build prints, on every `lake build`,

> `PDD-9: runP executed on the registered programs at the production
> digest`

which is the sentence a reader of the job list meets, and it says the
registered programs.

**Both missing runs pass** — verified here at both digests
(`Attack.lean` §3, and `checkAdversarial`'s `journalTwo` and
`schemaVectorDocument` rows). So this is a coverage/claim gap, not a
defect: three more `unless` rows in `Executed.check` close it, and the
printed line then means what it says.

**Ground:** BREAKER.md `proof-mechanics` → "One-witness universal — an
`exists` accepted with none" in its coverage form, and the packet's own
§B.8 citation ("existentials discharged by exhibiting the witness").
The packet's claim-scope section already carries the true sentence —
"LAW X covers the registered terms it names and no others" — so the
packet contradicts itself between §LAW X and §claim-scope, and the
claim-scope half is the honest one.

### NOTE-2 — `treeProg_Triple` carries one of LAW R's three axes

**Attacked:** LAW R's ENSURES and BATTERY
(`contracts/PDD-9.contract.md:127-138, 252-279`) against
`treeProg_Triple` (`TreeProgCorrect.lean:737-743`).

The packet writes LAW R's triple as

```
Triple H (treeProg tr) (…) (fun a w' => a = tr.address H ∧ …)
```

and says immediately below: "Three axes, per §8.0: ANSWER, GROWTH,
STORE … LAW R carries all three". That is true of `treeProg_run` and of
`treeProg_two_state`. It is NOT true of `treeProg_Triple`, whose
postcondition is

```lean
fun a w' => a = tr.address H ∧ Word.wf w' = true ∧ Honest H w'
```

— ANSWER plus two invariants, and neither GROWTH nor STORE. The `…` in
the packet's ENSURES is where the growth axis would go and it is not
there in the theorem.

**Witness, computed** (`Attack.lean` §8): `paddedShared` —
`treeProg blobSharedChunk` with one unrelated put prepended and every
operand shifted. Its run

- answers exactly `blobSharedChunk.address toyAddr` (ANSWER holds),
- ends on a word that is `Word.wf` and every binding of which satisfies
  `b.address = H (encodeNode b.node)` (both invariants hold),
- and contains a binding that is **not in `blobSharedChunk.flatten
  toyAddr` at all** — the FRAME violated.

`treeProg_Triple`'s postcondition does not exclude that run. LAW F does
(the padded table is one line longer), which is the packet's own point
that no single law carries the set — but the packet should not read as
though the triple carries the frame.

Partly disclosed: the castle's own docstring says "`Triple`'s own
postcondition sees only the final state, which is exactly why the
estate's `old` is a logical variable". The correction is one sentence in
the packet's LAW R block naming `treeProg_run` /
`treeProg_two_state` as the axis-carriers and the triple as the
refusal-exclusion form.

### NOTE-3 — LAW M's stated reason is narrower than LAW M

**Attacked:** the packet's second adversarial candidate
(`contracts/PDD-9.contract.md:336-341`): "A lowering that emits the
right SHAPES with wrong operands … dies at LAW M, because the resolved
reference addresses are then not the children's answers."

That reason fails on the sharpest instance of the class. `badShared`
(`Attack.lean` §6) is `treeProg blobSharedChunk` with the second leaf's
operand rewritten from `.ans 2` to `.ans 0` — a **different line
carrying an identical node**, so the resolved address IS the child's
answer, at every `H`. Computed:

```
badShared ≠ treeProg blobSharedChunk                     -- a different table
badShared.length = blobSharedChunk.size                  -- LAW F blind
runP toyAddr badShared []      = runP toyAddr      (treeProg …) []
runP sha256Addr badShared []   = runP sha256Addr   (treeProg …) []
```

The runs agree at both digests, so LAW R's conclusion at any single
address function cannot see it either.

LAW M kills it anyway, and the operative reason is a different one:
`embed` builds a `Prog` whose continuations are FUNCTIONS of the
answers, so the equality `embed p = tr.prog` quantifies over every
address the interpreter could hand back — no coincidence at one digest
discharges it. Kernel-checked here:

```lean
theorem badShared_dies_at_LAW_M : embed badShared ≠ Tree.prog blobSharedChunk
  → depends on axioms: [propext, Quot.sound]
```

proved by probing the third put's reference list at three distinct
chosen answers (`putRefsAt`).

This lands in the builder's favour and is recorded as a **precision
finding**, in PDD-1's re-run-2 style: LAW M is strictly stronger than
run agreement, and the packet's adequacy prose understates its own
theorem. The wrong-operand class is closed; the sentence that closes it
should be "because the denotation quantifies over the answers", not
"because the addresses disagree".

### NOTE-4 — the packet was amended 56 seconds after the implementation commit

```
e45a9779  2026-08-30 01:59:43   packet      1 file  +415
b5ad3c1d  2026-08-30 02:22:08   theorems    1 file  +885
db2c8344  2026-08-30 02:23:04   packet      1 file  +86 −7
```

Packet 22m25s before the theorems; the second packet commit 56s after
them. The amendment is disclosed in its own text ("AMENDMENT entered
after the module landed") and is **additive**: the placement rationale,
two battery names, the Controls section, the gate transcripts and the
axiom footprint. Diffed line by line — no ENSURES clause, no LAW
statement and no FALSIFIER moved. Recorded because PDD-2's NOTE-6
recorded the same shape, not because anything was written to fit.

### NOTE-5 — the drift device holds against the SHIPPED walkers, and it is the only thing that does

Not a defect; a measurement the packet's Controls section does not make.
The packet's two planted defects both mutate `seg`, the restatement.
The class that actually threatens the artifact is a mutation of the
FENCED walkers. Both were tried here (see the controls table below) and
both went red.

Worth recording alongside: under the `lowerTable` mutation,
`Cas/Backend/ProgProse.lean`'s own witness `#guard`
(`ProgProse.lean:298`, put SHAPES only) stayed GREEN and the module
built clean — the drift was invisible to every gate at HEAD before
PDD-9 and is caught only by `table_eq_treeProg` and the two LAW W
`#guard`s. §3.31's error state ("prose describing table A above code
lowered from table B") was live, and this packet is what closes it.

## Gates re-run, verbatim

```
$ lake --wfail build                                    (from library/cas)
ℹ [95/96] Built Cas.Backend.TreeProgCorrect (2.3s)
info: Cas/Backend/TreeProgCorrect.lean:881:0: PDD-9: runP executed on the
registered programs at the production digest — every answer is its term's
address, and shared-chunk deduplicates to four bindings from flatten's five
Build completed successfully (96 jobs).
[exited with code 0]

$ mise run --force check:cas                            → EXIT=0
ok vectors/value-single.json (378 bytes) — 1 bindings
ok vectors/blob-two-leaves.json (2252 bytes) — 6 bindings
ok vectors/file-readme.json (1557 bytes) — 4 bindings
ok vectors/journal-two-entries.json (4195 bytes) — 11 bindings
ok vectors/shared-chunk.json (1922 bytes) — 5 bindings
ok vectors/git-pin-commit.json (2867 bytes) — 1 bindings
ok vectors/schema-vector-document.json (5480 bytes) — 1 bindings
ok vectors/index.json (2045 bytes) — 7 vectors
ok ../effects/test/generated/VectorPrograms.ts (19433 bytes) — 7 programs
ok ../effects/test/generated/VectorProgramAddresses.json (2816 bytes) — 7 program addresses
ok ../effects/test/generated/VectorProgramLifts.json (11193 bytes) — 7 lift documents (round-tripped)
ok surface/cas-surface.json (955041 bytes) — 2026 declarations
ok surface/cas-obligations.json (17363 bytes) — 68 obligations   (10 of 10 controls fire)
ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound, 28 unbound  (13 of 13 controls fire)
ok ../../docs/lab-core/ENVIRONMENT.json (37002 bytes) — 45 tasks, 16 exes, 8 pins (2 distinct)
```

Every figure the packet transcribes is reproduced to the byte. The three
ledger gates did not move, so the FRAME's file claim is discharged
mechanically.

## Axiom census — all nine public theorems, printed by an independent hand

```
'Cas.Backend.treeProg_eq_seg'      depends on axioms: [propext, Quot.sound]
'Cas.Backend.table_eq_seg'         depends on axioms: [propext, Quot.sound]
'Cas.Backend.table_eq_treeProg'    depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_length'      depends on axioms: [propext, Quot.sound]
'Cas.Backend.embed_treeProg'       depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_run'         depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_run_empty'   depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_Triple'      depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_two_state'   depends on axioms: [propext, Quot.sound]
'Cas.Backend.Executed.runVerdict'  depends on axioms: [propext]
```

No `sorryAx`, no `Classical.choice`, no `ofReduceBool`. The packet's
footprint is exact — and note it is one axiom SHORTER than PDD-1's,
which carries `Classical.choice`.

## Controls — planted, red, reverted

Five, of which the packet claims two. Every mutation was reverted and
the tree rebuilt green.

| # | Mutation | Site | Result |
|---|---|---|---|
| C1 | `eraseIdx 2` → `eraseIdx 1` | castle, shared-chunk guard | RED, verbatim: *"Expression `runVerdict toyAddr blobSharedChunk (List.eraseIdx (Tree.flatten toyAddr blobSharedChunk) 1)` did not evaluate to `true`"* — the packet's quoted string, character for character |
| C2 | `seg`'s `.leaf` ref tag `chunk` → `tree` | castle, the restatement | RED in three: `lowerTree_seg` (:244), `lowerTable_seg` (:398), `embedFrom_seg` (:540) — the packet's "three places at once" |
| C3 | `seg`'s `.parent` operands transposed | castle, the restatement — **not in the control set** | RED in three: `lowerTree_seg` (:257), `lowerTable_seg` (:405), `embedFrom_seg` (:581) |
| C4 | `lowerTree`'s `.parent` child visit order swapped | **fenced `Cas/Backend/EmitProg.lean`** — a SHIPPED walker | RED: `lt_parent` (:190) "Not a definitional equality", `lowerTree_seg` (:196), and four executed guards (:830, :841, :844, :846); `#eval check` threw *"blob-two-leaves' run does not answer its term"* |
| C5 | `lowerTable`'s `.parent` operands transposed | **fenced `Cas/Backend/ProgProse.lean`** — the other SHIPPED walker | RED: `lb_parent` (:345) "Not a definitional equality", and LAW W's two `#guard`s (:844, :846). `Cas.Backend.ProgProse` itself built GREEN — its own put-shape guard is blind to operand order |

And the placement claim, checked rather than taken:

| # | Mutation | Result |
|---|---|---|
| C6 | `sorry` planted in `table_eq_treeProg` | `lake --wfail build` EXIT=1, *"warning: Cas/Backend/TreeProgCorrect.lean:452:8: declaration uses `sorry`"* → `error: build failed`. The backend homing genuinely gates the module |

## Break attempts that FAILED — the packet's earned confidence

| # | Attempt | Result |
|---|---|---|
| F1 | Is LAW R quantified at the empty word only? | **No.** `treeProg_run` takes `{w : Word} (hw : Word.wf w = true) (hhon : Honest H w)`; `treeProg_Triple`'s precondition is `fun w => Word.wf w = true ∧ Honest H w`; `treeProg_two_state` universally quantifies `w₀`. `treeProg_run_empty` is the corollary, not the statement. The run-relativity the docket worried about is honoured, and the hypotheses are the necessary ones (the packet's third adequacy candidate is right: `∀ w` without `Honest` is false, not merely unprovable) |
| F2 | Is LAW M a syntactic bridge weaker than meaning? | **No — it is finer.** `embed (treeProg tr) = tr.prog` is an equality of `Prog CasSig Addr32` terms, i.e. stratum-1 syntax of the free monad, which is strictly finer than `ObsEq` (stratum 3, `Defun.lean:419`). It retains put shapes, reference TAGS and operand identity — the last verified by `putRefsAt`, which recovers a line's operand by applying the continuation at addresses of the prober's choosing |
| F3 | Does `embed` forget the `.ans` INDEX where two indices resolve alike? | **No.** The env entries are continuation-BOUND variables, not concrete addresses, so `.ans 0` and `.ans 2` embed to different `Prog` terms even where both name the same node. `badShared_dies_at_LAW_M` is the proof; NOTE-3 records that the packet's stated reason is not this one |
| F4 | A wrong-but-passing table: right shapes, right length, identical runs at every digest | Constructed (`badShared`) and **excluded by LAW M**. Excluded independently by LAW S, since the pin is a total equation |
| F5 | Do the pins detect drift in the SHIPPED walkers, or only in the restatement? | **The shipped ones.** C4 and C5. `lowerTree_seg` and `lowerTable_seg` are total functional characterizations — `∀ tr arr` / `∀ tr s`, answer AND emitted list AND (for `lowerTable`) the counter — so a behavioural change at any tree contradicts them and the `rfl` clause lemma dies first |
| F6 | A drift class that slips past BOTH pins | **None found.** The pins are total, so any unilateral change to either shipped walk is red. A CONSISTENT campaign that drifts both walkers and `seg` together is then caught by LAW M, because `Tree.progK` is fenced in `Cas/Lang/TreeProg.lean`; and a campaign that drifted `progK` too would move the emitted TypeScript bytes and redden `check:cas`. Three independent nets, and the triangle is closed |
| F7 | Deeper nesting than any registered term | `deepSpine` (26 nodes, nine `parent` levels) and `deepJournal` (26 nodes, five `.entry` levels, deeper than `journal-two-entries`' two). Both pass LAW W, LAW F and LAW R's conclusion at the toy digest and at `sha256Addr` |
| F8 | Two DISTINCT duplicate pairs | `twoDupPairs`: 11 nodes → 9 bindings, two independent dedups. Passes |
| F9 | A duplicate that is also the ROOT's own child (both of the root's references resolve to ONE address) | `rootChildDup`: 5 nodes → 3 bindings. Passes. The doubled reference does not make the put conflict or the run refuse |
| F10 | A whole duplicated SUBTREE | `subtreeDup`: 11 nodes → 6 bindings, five dedups. Passes |
| F11 | Is the deduplicated word `flatten` with later duplicates dropped, in general? | Yes — `expected H tr := (Tree.flatten H tr).eraseDups` verified as the run's word on all nine corpus terms at both digests. This is the general form of the castle's hand-written `eraseIdx 2`, and it agrees with it on the castle's own witness |
| F12 | Does `toyAddr` COLLIDE, so that a guard passes only by accident? (PDD-2 NOTE-5's `lenAddr` precedent) | **No.** Distinct nodes = distinct addresses on every corpus term (`separates`, nine `#guard`s), and the toy and production digests deduplicate to the same counts on all seven measured terms (`checkSeparation`). Neither a collision nor a failure to collide is load-bearing anywhere |
| F13 | A LAW X mutation the control set does not cover: TRANSPOSE two bindings instead of erasing one | The guard goes red (`#guard !runVerdict … (transpose01 …)`). The transposed word has the same length and the same multiset, so a count- or bag-valued guard would have passed it; the castle's list equality does not. The guard pins ORDER as well as position |
| F14 | Does the castle's `#eval` half check the CONCLUSION rather than assume the premise? | Yes. `runVerdict` is `a == tr.address H && w == expected && Word.wf w`; no injectivity is used and none is claimed. The packet's claim-scope bullet on `Function.Injective H` is accurate |
| F15 | Does the FILE frame hold? | Yes. Three commits, one file each, disjoint. `Cas/Lang/TreeProg.lean`, `Cas/Backend/EmitProg.lean`, `Cas/Backend/ProgProse.lean`, `Cas/Lang/Defun.lean`, `Cas/Lang/Wp.lean`, `lakefile.toml` and `tools/Walk.lean` all untouched; no fixture byte moved |
| F16 | Is `Cas.Backend.TreeProgCorrect` genuinely in the kernel-checked build? | Yes — C6, and it appears by name at `[95/96]` in the job list |

## What this attack did NOT test

- The generated TypeScript. `progProgram`'s printer
  (`EmitProg.lean:93-126`) is pinned by no theorem here and by no
  theorem in the castle; the byte gate is the whole of it, exactly as
  the packet's claim-scope section says.
- `Function.Injective H` for `sha256Addr`. Named as a hypothesis
  everywhere it is used; nothing here bears on it.
- The cross-host half of R5. Unchanged, and correctly disclaimed.

## Re-run log

| Date | Against | Outcome |
|---|---|---|
| 2026-08-30 | `b5ad3c1d` / `db2c8344` | **STANDS** — HOLE-1 open (LAW X coverage); NOTE-2, NOTE-3, NOTE-4, NOTE-5 raised; no BREAK. `Attack.lean` elaborates clean, every `#guard` green, `badShared_dies_at_LAW_M` kernel-checked at `[propext, Quot.sound]` |
| 2026-08-30 | `05dc3b65` / `c984a7b5` (the fix pass) | **STANDS-AMENDED** — HOLE-1 CLOSED (ten of ten clauses, counted; both new rows red-tested); NOTE-2, NOTE-3, NOTE-5 answered; both reasoned refusals CONCURRED, the `Triple` one by computation; NOTE-6 raised (census scope, one line). No BREAK, no new HOLE. Record: `AttackRerun.lean`. **PDD-9 lands** |

HOLE-1 closes when `Executed.check` names `journalTwo` and the schema
term (and the printed line then means "the registered programs"), or
when the packet's LAW X block is narrowed to the five it runs. Either
is a one-commit fix; the run values are already computed and green in
`Attack.lean` §3.

---

# Re-run 2 — against the fix pass `c984a7b5`

```
DATE       2026-08-30
PACKET     e2b364e8  the ledger opens — HOLE-1, NOTE-2, NOTE-3
CASTLE     05dc3b65  close HOLE-1 — all seven registered programs run
PACKET     c984a7b5  fill FIXED-BY, re-run the transcripts
ATTACK     contracts/attacks/PDD-9/AttackRerun.lean
VERDICT    STANDS-AMENDED — HOLE-1 CLOSED, NOTE-2/3/5 answered,
           both refusals CONCURRED, one new NOTE-6
```

Three commits, one file each, disjoint — the FILE frame still holds and
no fenced byte moved.

## HOLE-1 — **CLOSED**, by count rather than by reading

The remedy is the strong one: both missing runs added rather than the
claim narrowed. Verified mechanically, not read off the diff.

**1. The clause count.** `(wire tag, reference count)` separates all ten
clauses of `Tree` — `value`/`chunk`/`schema`/`git`/`genesis` carry no
references and differ by tag, `leaf`/`manifest`/`file` carry one,
`parent`/`entry` carry two — so the clause set a term reaches is a
computation over its `flatten`. `AttackRerun.lean` §3:

```
coveredBefore.length  = 7    -- the five terms b5ad3c1d ran
coveredNow.length     = 10   -- all seven registered terms
coveredNow \ coveredBefore = [(12,0), (12,2), (83,0)]
                             -- genesis, entry, schema — exactly HOLE-1's three
coveredInKernel.length = 8   -- the #guard half, up from 6
coveredNow \ coveredInKernel = [(71,0), (83,0)]   -- git and schema, #eval-only
```

Ten of ten at the production digest, eight of ten in the kernel. `.git`
and `.schema` staying `#eval`-only is right and not a residue: their
payloads are a signed git commit and a 2.5 KB canonical schema, and this
lane's rule is that such work does not run in kernel `decide`.

**2. The build line means what it says.**

```
info: Cas/Backend/TreeProgCorrect.lean:955:0: PDD-9: runP executed on all
seven registered programs at the production digest — every answer is its
term's address, and shared-chunk deduplicates to four bindings from
flatten's five
```

**3. Both new rows are red-testable, and one was red-tested by this
hand** — the dispatch asked for one, both were done:

| # | Mutation | Result |
|---|---|---|
| C7 | `journalTwo`'s kernel guard: expected word perturbed (`.eraseIdx 4`) | RED at `TreeProgCorrect.lean:891` — *"Expression `runVerdict toyAddr journalTwo (List.eraseIdx (expectedWord toyAddr journalTwo) 4)` did not evaluate to `true`"*. The line number matches the packet's Controls entry |
| C8 | the schema row inside `check`: expectation perturbed (`.eraseIdx 0`) | RED, throwing *"PDD-9: schema-vector-document's run does not answer its term"* — the message the packet quotes, character for character |

**4. The registered term, not a lookalike.** `Executed.schemaTerm`
rebuilds the registry's schema row with `Payload.ofBytes`, which CLAMPS
at the byte bound. `check` asserts the bound before trusting it, which
is the right shape; independently verified here that the clamp does not
bite — `List.take` returns a prefix, so equal lengths is equality, and
`(schemaTerm.node toyAddr).payload.length = (utf8 vectorDocumentCode.payload).length`
(`AttackRerun.lean` §4).

## The oracle — adopted **VERBATIM**, and credited

Not "a function that agrees on a corpus". A definitional identity:

```lean
theorem oracle_adopted_verbatim (H : Bytes → Addr32) {t : Ty} (tr : Tree t) :
    Executed.expectedWord H tr = expected H tr := rfl
  → does not depend on any axioms
```

`Executed.expectedWord H tr = (tr.flatten H).eraseDups` is the oracle of
`Attack.lean` §2 spelled in the castle's own vocabulary. Credit is on the
declaration's docstring, naming the file, the section, the branch and
commit `e2703228`. Faithful, and attributed.

**The `eraseIdx` witness is pinned to it**, in the castle and not only in
prose: `#guard expectedWord toyAddr blobSharedChunk == (blobSharedChunk.flatten toyAddr).eraseIdx 2`.
Keeping both was the right call, and the packet's reason is verified
rather than accepted — the index is the SHARPER statement on that
witness because it names WHICH occurrence drops. Checked here that its
neighbours are not the word: both `eraseIdx 1` and `eraseIdx 3` fail
`runVerdict` (`AttackRerun.lean` §2). The oracle alone would have pinned
the length and the multiset; the index pins the position.

## Refusal 1 — LAW X not narrowed, closed strong instead: **CONCUR**

My HOLE-1 named two remedies and said either was a one-commit fix. The
builder took the better one. Narrowing would have made the sentence true
by shrinking it and left `.genesis`, `.entry` and `.schema` unexecuted —
the three clauses with the two-child offset arithmetic and the longest
reference chains, which is precisely where an executed consequence is
worth having. Closing strong makes the printed line true AND makes the
coverage extensible: with the expectation now a function of the term, a
further registered term is covered by naming it rather than by measuring
an erasure. Concurred without reservation.

## Refusal 2 — `treeProg_Triple` not strengthened: **CONCUR**, with a correction to the ground

The builder's argument is that GROWTH and STORE are two-state facts
about `w₀` and `w'`, that `Triple`'s postcondition sees only `w'`, and
that writing them in is not a strengthening but a rederivation of
`treeProg_two_state`.

For the axes AS THE PACKET STATES THEM that is exact — `w' = w₀ ++ v`
and `Word.toStore w' = Word.toStore (w₀ ++ tr.flatten H)` both mention
`w₀`, and fixing `w₀` inside a `Triple` IS `Triple_two_state_rel`, which
IS `treeProg_two_state`. Conceded.

**But the ground as stated is one step too wide, and the correction
matters because a future reader will use it.** It is not the case that
nothing frame-flavoured is one-state expressible. This is:

```
residency  —  ∀ b ∈ tr.flatten H, Word.find w' b.address = some b.node
```

"every node of the term is resident at the end". It needs no `w₀`, it
would sit in `Q` without complaint, it is true of the run, and it kills
the "writes nothing" candidate the packet's own adequacy section names.
So the refusal cannot rest on inexpressibility.

It rests on something better, and the ruling is a computation rather
than an opinion (`AttackRerun.lean` §5):

```
resident toyAddr blobSharedChunk (expected toyAddr blobSharedChunk)              = true
resident toyAddr blobSharedChunk (outsiderBinding :: expected …)                 = true
```

**Residency does not exclude `paddedShared`** — the very witness that
opened NOTE-2. The strongest one-state frame conjunct available would
therefore not close the gap it was raised about; it would add a fourth
statement of a fact `treeProg_run` already carries, and `paddedShared`
would still pass. What excludes `paddedShared` is LAW F, exactly as the
packet says.

Refusal CONCURRED. The recommended ground is "the one-state residual
does not exclude the witness", not "no frame fact is one-state
expressible". This is a note on the reason, not on the decision, and it
does not need a commit.

## NOTE-2 — **CLOSED as claim-scope**

LAW R's block now attributes each axis to the theorem that carries it,
and `treeProg_Triple`'s own docstring says outright which axes it does
not carry and names `paddedShared`. That is the remedy this record asked
for, and it is in the module as well as the packet, so the fact cannot
be met only in prose a reader of the source never sees.

## NOTE-3 — **CLOSED**

Adequacy candidate 2 now carries the operative reason — `embed`'s
continuations are functions of the answers, so the equality quantifies
over every address the interpreter could return — and cites
`badShared_dies_at_LAW_M` with its axiom print and its provenance. The
packet's claim moved UPWARD, which is the honest direction for this row.

## NOTE-5 — **ADOPTED**

Now the packet's own warrant, in Controls: the `lowerTable` drift was
invisible to every gate at HEAD, `ProgProse.lean:298`'s put-shape
`#guard` included, so §3.31's error state was live rather than
hypothetical. Correctly attributed and correctly used.

## NOTE-4 — accepted as recorded

The packet answers it in prose rather than with a row, on the ground
that it is not a break, and notes that THIS pass's amendments are not
additive and each carries a ledger row. Correct on both counts, and the
distinction is the right one.

## NEW — NOTE-6: the census names two of the three new `Executed` declarations

The packet's re-run footprint block widened the census beyond the nine
theorems, under the header "no `sorryAx`, no `Classical.choice`, no new
axiom", and prints:

```
Executed.runVerdict     → depends on axioms: [propext]
Executed.expectedWord   → does not depend on any axioms
```

The fix introduced a third `Executed` declaration, and it is the one the
block does not print:

```
Cas.Backend.Executed.schemaTerm  → [propext, Classical.choice, Quot.sound]
Cas.Backend.Executed.check       → [propext, Classical.choice, Quot.sound]
```

**Traced.** Not `Payload.ofBytes`, which prints `[propext, Quot.sound]`.
The source is `Cas.Vectors.Registry.vectorDocumentCode`, i.e.
`Cas.Schema.Described.code` in the fenced schema plane. All five terms
`check` ran before the fix print `[propext, Quot.sound]`
(`helloValue`, `blobTwoLeaves`, `fileReadme`, `gitPinCommit`,
`blobSharedChunk`), so the axiom is **new to `check` with this pass**,
and it is inherited, never minted.

**No soundness consequence, and none claimed.** `check` is an `IO Unit`
run by `#eval` through the compiler, so no kernel trust rides on it; no
kernel `#guard` mentions `schemaTerm`; and every one of the nine public
theorems still prints `[propext, Quot.sound]` — reproduced below. The
degree claim ("no `sorry`, no `native_decide`, and no new axiom" for
LAW S/W/F/M/R) is untouched and true.

It is a **census-scope** row: a footprint block that names two of three
sibling declarations, under a header asserting the absence of the axiom
the third one carries. One line closes it — print the row with its
provenance, or bound the header's scope to the theorems. Not a blocker,
and explicitly not a reason to hold the merge.

## Gates re-run at `c984a7b5`, verbatim

```
$ lake --wfail build                                     EXIT=0
ℹ [95/96] Built Cas.Backend.TreeProgCorrect (1.9s)
info: Cas/Backend/TreeProgCorrect.lean:955:0: PDD-9: runP executed on all
seven registered programs at the production digest — every answer is its
term's address, and shared-chunk deduplicates to four bindings from
flatten's five
Build completed successfully (96 jobs).

$ mise run --force check:cas                             EXIT=0
50 `ok` lines, every emitter byte-identical. Unmoved from the first pass:
ok vectors/journal-two-entries.json (4195 bytes) — 11 bindings
ok vectors/schema-vector-document.json (5480 bytes) — 1 bindings
ok vectors/shared-chunk.json (1922 bytes) — 5 bindings
ok ../effects/test/generated/VectorPrograms.ts (19433 bytes) — 7 programs
ok ../effects/test/generated/VectorProgramAddresses.json (2816 bytes) — 7 program addresses
ok ../effects/test/generated/VectorProgramLifts.json (11193 bytes) — 7 lift documents (round-tripped)
ok surface/cas-surface.json (955041 bytes) — 2026 declarations
ok surface/cas-obligations.json (17363 bytes) — 68 obligations
ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound, 28 unbound
```

The three ledger figures are identical to the first pass, so the fix
added eighty-five lines of module and moved no ledger byte — the FRAME's
promotion claim, discharged a second time.

## Axiom census re-run — all nine public theorems

```
'Cas.Backend.treeProg_eq_seg'      depends on axioms: [propext, Quot.sound]
'Cas.Backend.table_eq_seg'         depends on axioms: [propext, Quot.sound]
'Cas.Backend.table_eq_treeProg'    depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_length'      depends on axioms: [propext, Quot.sound]
'Cas.Backend.embed_treeProg'       depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_run'         depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_run_empty'   depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_Triple'      depends on axioms: [propext, Quot.sound]
'Cas.Backend.treeProg_two_state'   depends on axioms: [propext, Quot.sound]
'Cas.Backend.Executed.runVerdict'  depends on axioms: [propext]
'Cas.Backend.Executed.expectedWord' does not depend on any axioms
'Cas.Backend.Executed.schemaTerm'  depends on axioms: [propext, Classical.choice, Quot.sound]   ← NOTE-6
```

No `sorryAx`, no `ofReduceBool`, and no theorem's footprint moved.

## Re-run 2 attempts, pass/fail

| # | Attempt | Result |
|---|---|---|
| G1 | Did the fix take anything away? Re-elaborate the UNEDITED `Attack.lean` against `05dc3b65` | Clean. Every `#guard` green, both `#eval` batteries green, `badShared_dies_at_LAW_M` still kernel-checked at `[propext, Quot.sound]`. The first pass is a live regression object |
| G2 | Is the "all ten clauses" claim true, or is it a reading of the source? | True, and counted — `coveredNow.length == 10`, with the delta over the old five being exactly `[(12,0),(12,2),(83,0)]` |
| G3 | Is `Executed.schemaTerm` the registered term or a clamped lookalike? | The registered term. `check` asserts the bound; the length identity is verified here independently |
| G4 | Is the adopted oracle the same function or merely an agreeing one? | The same — `rfl`, axiom-free |
| G5 | Is the kept `eraseIdx 2` redundant now that the oracle exists? | No. It pins the POSITION, which the oracle does not: `eraseIdx 1` and `eraseIdx 3` both fail `runVerdict` |
| G6 | Are the two new rows decoration, or can they go red? | Both red — C7 at the line the packet names, C8 with the message the packet quotes |
| G7 | Can the `treeProg_Triple` refusal be defeated by a one-state frame conjunct? | **No.** `residency` is one-state and true of the run, but it is also true of `paddedShared`, so it does not close the gap it would be added for. The refusal survives its own best counterargument |
| G8 | Did any theorem's axiom footprint move under the fix? | No — all nine unchanged. A definition's did, which is NOTE-6 |
| G9 | Did the ledger gates move? | No — `955041` / `17363` / `9825`, identical to the first pass |

No BREAK. HOLE-1 closed. **PDD-9 lands.**
