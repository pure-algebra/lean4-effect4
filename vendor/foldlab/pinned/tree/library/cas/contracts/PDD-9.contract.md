# PDD-9 — `treeProg` correctness: the flagship artifact tied to its meaning

The contract packet for owed-ledger item 3 of THE-ALGEBRA
(`.staging/algebraic-review/THE-ALGEBRA.md` L231/L232/L127, §3.5,
§3.31): the estate's flagship generated artifact — seven registered
programs and the R5 gate itself — is tied to `Tree.prog`'s meaning by
nothing, and `runP`, the operation R5's prose names, acquires no
executed consequence anywhere.

```
CATEGORIES algebraic-laws, contracts, termination, inductive-data
```

CATALOG rows opened for those tags, and what each contributed:

- **§4.3 Structural Inclusion** (`inductive-data, termination,
  algebraic-laws, proof-mechanics`) — "use the datatype argument as the
  decreases value; pattern matching exposes the structurally included
  children". Every recursion this packet touches — `lowerTree`,
  `lowerTable`, the private `seg`, and all four inductions — descends
  on a constructor child of `Tree`, so the `termination` class is
  discharged structurally and no metric is invented. The one non-structural
  variant in play is the RUN's, and it is a number, not a wish (below).
- **§4.6 Abstract Syntax Trees for Expressions** (`inductive-data,
  algebraic-laws, termination, specification-design, proof-mechanics`)
  — the section's discipline is that an AST's evaluator equations and
  its structural decreases are ONE mutually recursive contract. Here the
  "evaluator" is the store program and the equations are per-constructor:
  a leaf sort emits one put; a one-child sort emits the child's segment
  then its own put naming the child's answer; a two-child sort emits both.
  The falsifier the section names — "a recursive call on a
  non-structurally-smaller expression" — is why LAW S is stated over an
  offset-indexed `seg` rather than over a fixpoint nobody can see.
- **§4.1 Matching on Datatypes** — "turn each constructor branch into a
  red case". Both walkers have ten clauses and the two ten-clause matches
  are what LAW W compares; a clause that parts from its twin is the whole
  error state §3.31 records.
- **§8.0/§8.3 the sorting trinity** (`specification-design,
  algebraic-laws`) — a spec is a CONJUNCTION and the third axis is the one
  that bites. Here the axes are ANSWER (the run's address), GROWTH (which
  bindings the word gained) and STORE (what the projected store holds).
  Answer alone is satisfied by a program that writes nothing; growth alone
  by one that writes garbage. LAW R carries all three, and the adequacy
  witness below shows why.
- **§1.4 Method Contracts / §2.7 underspecified outputs**
  (`contracts`) — "treat an underspecified output universally". The
  run's growth is a SUBLIST of `flatten`, not `flatten`: shared subterms
  deduplicate. The packet states the sublist and the store equality
  rather than the flattering equality, and the shared-chunk witness is
  kept live so the weaker true form cannot be quietly strengthened into a
  false one.
- **§B.7–B.8 proof mechanics** — universals proved for arbitrary,
  existentials discharged by exhibiting the witness. LAW X is the
  existential half and it is EXECUTED, not asserted.

## The degree claim

**I have shown algebraically that this can be implemented at the Lean
escalation tier, with one law discharged by execution rather than by
proof, and the boundary between the two is written down.**

- LAW S, LAW W, LAW F, LAW M and LAW R are Lean statements over the
  shipped `Cas.Backend.treeProg`, `Cas.Grammar.Tree.table`,
  `Cas.Lang.embed`, `Cas.Lang.runP` and `Cas.Grammar.Tree.prog`
  declarations, proved to the kernel with no `sorry`, no
  `native_decide`, and no new axiom.
- LAW X is DECIDED, not proved: a kernel `#guard` at a toy address
  function and a build-time `#eval` IO assert at the production digest
  (`Cas.sha256Addr`). This lane's law is that digest computation runs in
  `#eval` and never in kernel `decide` (`library/cas/AGENTS.md`,
  "Standing discipline"), and PDD-2's battery
  (`Cas/Lang/Wp.lean:880-903`) is the precedent for the pairing.
- The escalation gate is NEGATIVE, exactly as in PDD-1: this slice adds
  one new theorem module and no bytes. `γ` is discharged by
  `lake exe emitprograms --check` (and the rest of `check:cas`)
  staying byte-identical — the claim is "the model gained theorems and
  every emitted surface stood still", and a red `--check` refutes it.
  There is no host battery because there is no host change.

## The algebra

Three lowerings of one grammar term exist at HEAD and §3.31 records that
no theorem relates any pair:

| lowering | into | site |
|---|---|---|
| `Tree.progK` / `Tree.prog` | `Prog CasSig Addr32` | `Cas/Lang/TreeProg.lean:40,71` |
| `treeProg` | `PProg` | `Cas/Backend/EmitProg.lean:85` |
| `Tree.table` | `PProg` | `Cas/Backend/ProgProse.lean:268` |

This packet closes the triangle: the two `PProg` walks are EQUAL (LAW W),
and the table's denotation IS the term's program (LAW M), from which the
run's meaning follows (LAW R) and the run is then EXECUTED (LAW X).

The bridge is one private restatement, `seg`, and the PIN DEVICE is
PDD-1's: `Cas/Backend/Canon.lean:115-129` carries private `canonDedup`
/ `canonHasKey` and pins them to the shipped `canonServices` by a
kernel-checked theorem, so drift is a red build rather than a silent
divergence. The same device is used here for the same reason and with
one added motive named in the ticket: `putNode` (`EmitProg.lean:46`) and
`putLine` (`ProgProse.lean:227`) are `private` to their modules and both
files are FENCED, so no theorem elsewhere may name them and no edit may
unseal them. `seg` is the third spelling, the two pins hold it to the
first two, and nothing is assumed.

```
REQUIRES   LAW S, W, F, M: nothing — total on every sort `t` and every
           `tr : Tree t`.
           LAW R: `Function.Injective H` (the Level-1 hash hypothesis,
           named at its lattice level per CAS-003 and inherited verbatim
           from `Tree.putTree_correct`), and a starting word that is
           ADMISSIBLE and HONEST (`Word.wf w = true`, `Honest H w`).
           Run-relative, as the estate's rule says: a run's meaning is
           relative to its starting word, and `w` is universally
           quantified only inside those two predicates — never over all
           words. The empty word satisfies both, which is the corollary
           the executed consequence runs.
           LAW X: nothing. It is a computation.

ENSURES    S    treeProg tr = (seg tr 0).1  and
                Tree.table tr = (seg tr 0).1        (the two pins)
           W    Tree.table tr = treeProg tr          (L232)
           F    (treeProg tr).length = tr.size       (the fuel, as a
                fact about the table rather than a hypothesis)
           M    embed (treeProg tr) = tr.prog        (L231, the strong
                form: equality of PROGRAMS, not of runs)
           R    Triple H (treeProg tr)
                  (fun w => Word.wf w = true ∧ Honest H w)
                  (fun a w' => a = tr.address H ∧ …)
                i.e. from every admissible honest word the table's run
                HALTS DONE — refusal excluded — answering exactly
                `tr.address H`, over a word that grew by a SUBLIST of
                `tr.flatten H` and projects to exactly `flatten`'s store,
                staying admissible and honest.
                Two-state form (`old` = the starting word) through
                PDD-2's `Triple_two_state_rel` (`Cas/Lang/Wp.lean:606`);
                `Triple`/`wp` are that packet's vocabulary and are used
                here as the specification language, with credit.
           X    the run of a REGISTERED program, computed: for a term
                with a shared subterm, `runP` answers the term's
                `Tree.address` and the final word is the DEDUPLICATED
                word — four bindings where `flatten` has five.

DECREASES  Structural on `Tree` (§4.3): `seg`, `lowerTree`, `lowerTable`
           and every induction descend on constructor children, so the
           decrease is free and no metric clause is written. The RUN's
           variant is separate and is a NUMBER, not a hypothesis: fuel
           `(treeProg tr).length + 1`, which LAW F identifies with
           `tr.size + 1` — the existential-fuel discipline
           (`Cas/Lang/Handler.lean:115-123`) discharged by
           `runP_embed_agree` and `Triple_run` (`Wp.lean:618`).

FRAME      reads: `tr`, and the starting word `w`.
           writes: the run appends a sublist of `tr.flatten H` to the
           word and nothing else — no binding is removed, no address
           outside `tr.flatten H` is written, and the projected store
           moves by exactly `flatten`'s bindings.
           FILE frame, the load-bearing half: this slice adds ONE new
           module, `library/cas/Cas/Backend/TreeProgCorrect.lean`, and
           edits NO existing file.

           PLACEMENT, and why it is under `Cas/Backend/`. AMENDMENT
           entered after the module landed, on PDD-8's builder's
           verified warning: the `Cas` library's glob is its ROOT
           MODULE alone, so a new module under `Cas/Lang/` is NOT
           kernel-checked by `lake --wfail build` — a planted `sorry`
           stays green there. `CasBackend` globs `Cas.Backend.+`, so a
           backend module is built with no lakefile edit. This module
           is homed there for that reason and the green is verified
           rather than assumed: `Cas.Backend.TreeProgCorrect` appears
           by name in the build job list ("Built
           Cas.Backend.TreeProgCorrect"), and the planted-defect
           controls below fire from inside it.

           In particular it does not touch the
           fenced `Cas/Backend/EmitProg.lean`,
           `Cas/Backend/ProgProse.lean`, `Cas/Lang/TreeProg.lean` or
           `Cas/Lang/Defun.lean`; it does not touch `Cas/Lang/Wp.lean`;
           it does not touch `lakefile.toml` (the `CasBackend` library
           globs `Cas.Backend.+`, so the new module is built and
           kernel-checked with no declaration); it does not touch
           `tools/Walk.lean` (a new backend module is invisible to the
           surface, obligation and law ledgers until it is added to
           `libraryImports`, and adding it is a promotion, hence a
           ruling — `Walk.lean:29-34`); and it moves no fixture byte.
```

## The laws and their falsifiers

```
LAW S      THE PIN. The private restatement computes both shipped walks:
             treeProg tr    = (seg tr 0).1
             Tree.table tr  = (seg tr 0).1
           `seg` is offset-indexed — `seg tr n` is the segment a term
           occupies when its first line sits at index `n` — because that
           is what the answer operands are relative to, and an
           offset-blind restatement could not state LAW M at all.
FALSIFIER  exhibit `tr` with `treeProg tr ≠ (seg tr 0).1`, or with
           `Tree.table tr ≠ (seg tr 0).1`. Mechanically: change one
           clause of either shipped walker and the corresponding pin
           stops elaborating — `lake build` red, no trust added.
BATTERY    library/cas/Cas/Backend/TreeProgCorrect.lean —
           `treeProg_eq_seg`, `table_eq_seg`, kernel-checked.
```

```
LAW W      THE TWO WALKS AGREE (L232). For every sort `t` and every
           `tr : Tree t`:  Tree.table tr = treeProg tr.
           This is the sentence `ProgProse.lean:225` calls prose:
           "The two walks agreeing is prose, not a theorem."
FALSIFIER  exhibit `t` and `tr : Tree t` with
           `Tree.table tr ≠ treeProg tr`. Concretely: a term whose
           emitted table diverges from its walk — the ticket's first
           named falsifier.
BATTERY    library/cas/Cas/Backend/TreeProgCorrect.lean —
           `table_eq_treeProg`; plus `#guard`s exhibiting the equality
           on concrete terms, so a reader meets the fact executed as
           well as proved.
```

```
LAW F      THE TABLE'S LENGTH IS THE TERM'S SIZE.
             (treeProg tr).length = tr.size
           Small, and load-bearing twice: it is what turns `runP`'s
           fuel bound `p.length + 1` into `Tree.putTree_correct`'s
           `tr.size + 1`, and it is what makes the envelope's put count
           a fact about the TERM rather than about the table.
FALSIFIER  exhibit `tr` with `(treeProg tr).length ≠ tr.size`.
BATTERY    library/cas/Cas/Backend/TreeProgCorrect.lean —
           `treeProg_length`.
```

```
LAW M      THE TABLE IS THE TERM'S PROGRAM (L231, strong form).
             embed (treeProg tr) = tr.prog
           Equality in `Prog CasSig Addr32` — the carrier's own
           equality, not an observational one and not a run agreement.
           This is the statement §3.31 says no theorem makes: the
           emitted table's denotation IS the grammar term's store
           program, so the emitter cannot drift from the grammar
           without a red build.
FALSIFIER  exhibit `t` and `tr : Tree t` with
           `embed (treeProg tr) ≠ tr.prog`. A weaker refutation
           suffices and is worth naming: exhibit `H`, `tr` and an
           admissible honest `w` on which the two RUNS disagree in
           status, answer or word — that kills LAW M through LAW R.
BATTERY    library/cas/Cas/Backend/TreeProgCorrect.lean —
           `embed_treeProg`.
```

```
LAW R      THE RUN'S MEANING (L231 as a triple; PDD-2's vocabulary).
           For injective `H`:
             Triple H (treeProg tr)
               (fun w => Word.wf w = true ∧ Honest H w)
               (fun a w' => a = tr.address H ∧
                  ∃ v, v.Sublist (tr.flatten H) ∧ … )
           and, in the two-state reading with `old` the starting word:
             ∀ w₀, Word.wf w₀ ∧ Honest H w₀ →
               ∃ v, v.Sublist (tr.flatten H)
                 ∧ runP H (treeProg tr) w₀ = (.done (tr.address H), w₀ ++ v)
                 ∧ Word.toStore (w₀ ++ v) = Word.toStore (w₀ ++ tr.flatten H)
                 ∧ Word.wf (w₀ ++ v) = true ∧ Honest H (w₀ ++ v)
           Three axes, per §8.0: ANSWER (`tr.address H`), GROWTH (a
           sublist of `flatten`, appended — the frame), STORE (exactly
           `flatten`'s projection). Refusal is excluded by `.done`;
           divergence is excluded by the carrier (`runP_halts`).

           WHICH THEOREM CARRIES WHICH AXIS. AMENDMENT, breaker hand
           (NOTE-2, `contracts/attacks/PDD-9/RESULTS.md`): the first
           draft of this block said "LAW R carries all three" without
           saying of which theorem, and a reader took it of all four.
           It is true of `treeProg_run` and `treeProg_two_state`, whose
           postconditions carry ANSWER, GROWTH and STORE together. It
           is NOT true of `treeProg_Triple`, whose postcondition is
           `fun a w' => a = tr.address H ∧ Word.wf w' = true ∧
           Honest H w'` — ANSWER plus two invariants, and no frame.
           The `Triple` form's job is the one the other two cannot
           state: REFUSAL EXCLUSION at a precondition, in PDD-2's
           anchor, where `P ≤ wp p Q` is the whole content.

           The breaker's witness for the gap is `paddedShared`
           (`Attack.lean` §8): a table whose run answers
           `blobSharedChunk.address`, ends admissible and honest, and
           writes a binding that is not in `blobSharedChunk.flatten` at
           all. `treeProg_Triple` does not exclude it; LAW F and
           `treeProg_two_state` do.

           The Triple is NOT strengthened, and the reason is stated
           rather than left to inference: GROWTH and STORE are
           two-state facts about `w₀` and `w'`, and `Triple`'s
           postcondition sees only `w'`. Writing them into a
           single-state postcondition is not a cheap strengthening —
           it is the two-state triple, which is `treeProg_two_state`
           and already exists.
FALSIFIER  exhibit an injective `H`, a term `tr` and an admissible
           honest `w` such that `runP H (treeProg tr) w` refuses, or
           answers other than `tr.address H`, or leaves a final word
           that is not `w` extended by a sublist of `tr.flatten H`, or
           whose store differs from `flatten`'s — the ticket's second
           named falsifier ("a table whose run answers differently than
           the term's meaning").
BATTERY    library/cas/Cas/Backend/TreeProgCorrect.lean —
           `treeProg_run` and `treeProg_two_state` (all three axes;
           the latter is the two-state form through PDD-2's
           `Triple_two_state_rel`), `treeProg_run_empty` (the
           corollary the executed consequence runs), and
           `treeProg_Triple` (refusal exclusion at a precondition,
           ANSWER and the two invariants — not the frame).
```

```
LAW X      THE EXECUTED CONSEQUENCE (L127). `runP` acquires one, on a
           REGISTERED program, at both address functions this lane
           admits:

             #guard  — kernel-decided, at a toy address function, on
                       four terms including the shared-subterm witness
                       and the registry's deepest term: the run is
                       DONE, the answer is the term's `Tree.address`,
                       and the final word is the DEDUPLICATED word.
             #eval   — a build-time IO assert at the production digest
                       `Cas.sha256Addr`, over ALL SEVEN registered
                       terms of `Cas/Vectors/Registry.lean` that the
                       seven generated programs are lowered from
                       (`tools/EmitPrograms.lean:45-70`): each term's
                       `runP H (treeProg tr) []` is computed and
                       compared, binding for binding, against the word
                       and the address the GRAMMAR determines.

           COVERAGE, counted rather than asserted. AMENDMENT, breaker
           hand (HOLE-1, `contracts/attacks/PDD-9/RESULTS.md`): the
           first draft of this block said "the registered terms … each
           term" while `Executed.check` ran FIVE of the seven, and the
           build line printed on every `lake build` said "the
           registered programs". `journalTwoEntries` and
           `schemaVectorDocument` were run nowhere, at either digest,
           so `.genesis`, `.entry` and `.schema` — three of the
           grammar's ten clauses, including the constructor with the
           two-child offset arithmetic and the longest reference chain
           the registry has — had NO executed consequence. This block
           and §claim-scope contradicted each other and §claim-scope
           was the honest half.

           Closed the strong way rather than by narrowing the claim:
           both runs are added, so all seven registered programs and
           all ten grammar clauses acquire an executed consequence, and
           the printed line means what it says. The breaker had already
           computed both and both PASS (`Attack.lean` §3), so this was
           a coverage claim to correct and never a defect to fix.

           THE EXPECTED WORD IS NOW A FUNCTION OF THE TERM.
           AMENDMENT, adopting the breaker's oracle with credit
           (`Attack.lean` §2, `expected H tr := (flatten H tr).eraseDups`
           — branch `attack/opus-cc-mac/pdd-9`, commit `e2703228`): the
           run's word is `flatten` with LATER duplicates dropped, which
           the term determines. The first draft named it by a
           hand-chosen `eraseIdx 2` on one witness, which does not
           generalize to a corpus. The hand-written index is KEPT as a
           `#guard` pinning the oracle against it on that witness —
           both because it is the sharper statement there (it pins
           WHICH occurrence drops) and because the Controls transcript
           below quotes its failure message character for character.

           The two halves are the same verdict at two digests, which is
           PDD-2's battery pattern (`Wp.lean:880-903`) and this lane's
           standing rule: digests are computed in `#eval`, never in
           kernel `decide`.
FALSIFIER  This is §3.5's own falsifier, and its recorded witness is
           what this law is built to destroy:

             FALSIFIER  change runP's word semantics — make a duplicate
                        put append — and exhibit a red gate
             WITNESS    (at HEAD) no gate goes red

           After this law: the shared-subterm run's word is length-checked
           against the deduplicated word, so an appending duplicate put
           makes the `#guard` fail to elaborate and the `#eval` throw.
           The gate that was absent is present, and it is red under
           exactly the mutation §3.5 names.
BATTERY    library/cas/Cas/Backend/TreeProgCorrect.lean — the `Executed`
           section: `#guard`s over the witness terms and `Executed.check`
           driven by `#eval`. The mutation is refuted POSITIVELY as well
           as negatively — `#guard !runVerdict toyAddr blobSharedChunk
           (blobSharedChunk.flatten toyAddr)` exhibits that the run's
           word is NOT `flatten`, so the appending semantics is killed
           by a computation and not by an argument.
```

## Adequacy — the law set, attacked before it is proved

The §8.0 question: is the conjunction strong enough that no wrong
implementation passes? Three adversarial candidates, and what kills each:

- **A lowering that emits NOTHING.** `treeProg tr = []`. Kills nothing
  in W (both walks empty), passes S if `seg` is emptied too — and dies
  at LAW F (`0 ≠ tr.size`) and at LAW M (`embed [] = failWith …`,
  which is not `tr.prog`). F is in the packet for this reason, not for
  the fuel alone.
- **A lowering that emits the right SHAPES with wrong operands.** Every
  put present, every reference naming line `0`. Survives F, survives the
  put-shape `#guard` that `ProgProse.lean:298` already carries — that
  guard compares put SHAPES only, which §3.31 records as its limit — and
  dies at LAW M.

  THE REASON, CORRECTED. AMENDMENT, breaker hand (NOTE-3): the first
  draft said it dies "because the resolved reference addresses are then
  not the children's answers". That reason is narrower than the law and
  fails on the sharpest instance of the class. `badShared`
  (`Attack.lean` §6) rewrites the second leaf's operand from `.ans 2`
  to `.ans 0` — a DIFFERENT line carrying an IDENTICAL node — so the
  resolved address IS the child's answer, at every `H`. It has the
  right length, so LAW F is blind; its runs agree with the true table's
  at both the toy digest and `sha256Addr`, so LAW R's conclusion at any
  single address function is blind too.

  LAW M kills it anyway, and the operative reason is stronger than the
  one first written: `embed` builds a `Prog` whose CONTINUATIONS ARE
  FUNCTIONS of the answers, so `embed p = tr.prog` quantifies over
  every address the interpreter could hand back, and no coincidence at
  one digest discharges it. The breaker proved it — `badShared_dies_at_
  LAW_M : embed badShared ≠ Tree.prog blobSharedChunk`, kernel-checked
  at `[propext, Quot.sound]`, in
  `library/cas/contracts/attacks/PDD-9/Attack.lean` §6, branch
  `attack/opus-cc-mac/pdd-9`, commit `e2703228`.

  This is the finding that most changes what the packet claims, and it
  changes it upward: LAW M is strictly finer than run agreement, and
  the first draft's adequacy prose understated its own theorem.
- **A meaning theorem that quantifies over the wrong thing.** `∀ w`
  without `Honest H w` is FALSE, not merely unprovable: a word that
  binds the term's address to a DIFFERENT node makes the put conflict
  and the run refuse. The premise is not decoration and it is not a
  wish — it is discharged at the site the executed consequence runs
  (`w = []`, honest and admissible by `Honest.nil` and `rfl`), which is
  why LAW X can be an unconditional computation while LAW R carries
  hypotheses.

The third is the `claim-scope` obligation in its sharpest form and it is
why the packet states LAW R run-relative rather than universally.

## Claim-scope — what these theorems do NOT say

The anti-overclaim class, written before the proofs so it cannot be
written to fit them.

- **Nothing here reaches the TypeScript.** LAW M and LAW R are about
  `treeProg`'s table and its Lean run. `progProgram`'s PRINTING
  (`EmitProg.lean:119`), the generated `VectorPrograms.ts`, and the
  host's `store.put` are claimed by the byte gate and by R5's suite
  alone, exactly as before. No soundness word attaches to host code
  (estate C5).
- **The R5 chain is shortened, not closed.** §3.5 draws the chain as
  `TS host run =gate= fixture word =???= runP/run =bridge= interpretRef`.
  This packet supplies the marked link as an EQUALITY at the Lean end
  (LAW M plus `Tree.putTree_correct`, whose conclusion is a `Sublist`
  for a reason the shared-chunk witness exhibits) and gives `runP` its
  first executed consequence. It does NOT make the TypeScript suite
  compare `List Binding` to `List Binding`; §3.5's closing sentence
  about what R5 certifies today still stands for the cross-host half.
- **The growth is a SUBLIST, never `flatten` itself.** Shared subterms
  deduplicate. A packet claiming `w ++ tr.flatten H` would be claiming
  something false, and the registered `shared-chunk` term is the
  standing witness.
- **LAW R's `Function.Injective H` is a hypothesis about the address
  function, not a proved property of SHA-256.** It is the same Level-1
  premise `Tree.putTree_correct` carries, named rather than assumed. The
  `#eval` half of LAW X therefore checks the CONCLUSION at
  `Cas.sha256Addr`; it does not discharge the premise, and no claim of
  collision resistance is made or needed anywhere in this packet.
- **`seg` is a restatement, not a definition of record.** The two pins
  are what make it admissible. If a future slice routes the emitter
  through one walk (`Cas/Backend/Mcp.lean`'s note), `seg` and LAW W
  retire together and that is the intended end state.
- **LAW X covers the registered terms it names and no others.** It is an
  existential discharged by witnesses, per §B.8, and the packet claims
  exactly the witnesses it runs. Those are now all seven registered
  terms and, through them, all ten grammar clauses — but the sentence
  stands as the governing one: it was already true when the block above
  it was not (HOLE-1), and it is what a future term added to the
  registry without a row in `Executed.check` would fall foul of.
- **Nothing here touches `encodeProg`'s address side.** The cont-node
  address a program HAS (`tools/EmitPrograms.lean:96-103`, R7's stamp) is
  the encoder's fact; this packet is about the runner's, and the two are
  deliberately separate (the direction law: words are minted by running,
  addresses by encoding).

## Obligation classes in play

`contract` (LAW R is the triple itself, `P ≤ wp c Q`, in PDD-2's
anchor), `termination` (structural on `Tree` throughout, §4.3; the run's
variant a number via LAW F), `abstraction` (LAW M is the homomorphism
square between the `PProg` plane and the `Prog` plane — the whole
obligation, per §9.5), `algebraic-laws` (LAW W is the two walks'
equality; LAW S the pin), `conformance` (LAW X, and the negative byte
gate), `adequacy` (the three adversarial candidates above),
`claim-scope` (the section above), `invariant` (`Word.wf` and `Honest`
preserved across the run — carried through from `step_put_honest`),
`frame` (the word grows by an append and by nothing else).

The `domain` class generates one row and it is already discharged
upstream: `progProgram` is partial (`EmitProg.lean:93-108` refuses a
`load` line and a literal-address operand), and `treeProg`'s image
contains neither — every clause of both walkers emits `.put` with `.ans`
operands only. That is visible in `seg` by inspection and is why LAW M's
`resolveRefs` obligations never hit the refusal arm.

## Controls — the guards can go red

A gate that cannot fail proves nothing. Four defects were planted in
the landed module, built, and reverted; all are recorded because the
packet's whole claim is that these laws are attached to something.

The two added on the HOLE-1 fix, so the new coverage is not decoration:

- **`journalTwo`'s kernel guard.** Its expected word perturbed by one
  binding. Red at `TreeProgCorrect.lean:891`.
- **The schema term's production row.** Same perturbation inside
  `check`. Red, and the thrown message is the one the row carries:
  *"PDD-9: schema-vector-document's run does not answer its term"*.

And the two from the first pass:

- **The dedup position.** `eraseIdx 2` moved to `eraseIdx 1` in the
  shared-chunk guard. Red: *"Expression `runVerdict toyAddr
  blobSharedChunk (List.eraseIdx (Tree.flatten toyAddr
  blobSharedChunk) 1)` did not evaluate to `true`"*. The guard pins
  WHICH occurrence deduplicates, not merely how many bindings survive.
- **A drifted walker clause.** `seg`'s `.leaf` reference tag changed
  from `Ty.chunk.wireTag` to `Ty.tree.wireTag` — the shape of the drift
  the pin device exists to catch. Red in three places at once: both
  pins (`lowerTree_seg`, `lowerTable_seg`) and LAW M
  (`embedFrom_seg`). The restatement cannot quietly part from either
  fenced walker.

Both were reproduced verbatim by the independent breaker, who added
four more the builder's set did not cover — a transposed `seg` operand
pair, a mutation of each SHIPPED walker, and a planted `sorry`. All
red; the record is `contracts/attacks/PDD-9/RESULTS.md` §Controls. Two
of those are worth restating here because they measure something this
section did not:

- **The device holds against the FENCED walkers, not only against the
  restatement.** Both of this section's controls mutate `seg`, which is
  the half a builder can edit. The class that actually threatens the
  artifact is a drift in `EmitProg.lean` or `ProgProse.lean`. The
  breaker mutated each (C4: `lowerTree`'s `.parent` visit order; C5:
  `lowerTable`'s `.parent` operands transposed) and both went red — the
  `rfl` clause lemma dies first, with "Not a definitional equality",
  because `lowerTree_seg` and `lowerTable_seg` are TOTAL functional
  characterizations and a behavioural change at any tree contradicts
  them.

- **NOTE-5, and it is this packet's warrant.** Under the `lowerTable`
  mutation, `Cas/Backend/ProgProse.lean`'s own witness `#guard`
  (`ProgProse.lean:298`, put SHAPES only) stayed GREEN and that module
  built clean: the drift was invisible to EVERY gate at HEAD, and is
  caught only by `table_eq_treeProg` and LAW W's two `#guard`s.
  THE-ALGEBRA §3.31's error state — "a generated module can carry prose
  describing table A above code lowered from table B" — was live at
  HEAD, not hypothetical, and closing it is what LAW W buys.

## Gates

Run from `library/cas` unless noted; all verbatim.

Re-run after the HOLE-1 fix (`05dc3b65`); every figure below is from
that tree.

```
lake --wfail build
  → Build completed successfully (96 jobs).
  → Built Cas.Backend.TreeProgCorrect
  → PDD-9: runP executed on all seven registered programs at the
    production digest — every answer is its term's address, and
    shared-chunk deduplicates to four bindings from flatten's five

mise run --force check:cas                            → EXIT=0
  (50 `ok` lines; every emitter's --check byte-identical)
  → ok vectors/shared-chunk.json (1922 bytes) — 5 bindings
  → ok vectors/journal-two-entries.json (4195 bytes) — 11 bindings
  → ok vectors/schema-vector-document.json (5480 bytes) — 1 bindings
  → ok ../effects/test/generated/VectorPrograms.ts (19433 bytes)
       — 7 programs
  → ok ../effects/test/generated/VectorProgramAddresses.json
       (2816 bytes) — 7 program addresses
  → ok ../effects/test/generated/VectorProgramLifts.json (11193 bytes)
       — 7 lift documents (round-tripped)
  (every emitter's --check byte-identical; no fixture moved)

mise run --force check:cas:surface                    → EXIT=0
  → ok surface/cas-surface.json (955041 bytes) — 2026 declarations
mise run --force check:cas:obligations                → EXIT=0
  → 10 of 10 controls fire
  → ok surface/cas-obligations.json (17363 bytes) — 68 obligations
mise run --force check:cas:laws                       → EXIT=0
  → 13 of 13 controls fire
  → ok surface/cas-laws.json (9825 bytes) — 9 of 37 rulings bound

git status                    → clean beyond this packet and the module
```

The three ledger gates staying byte-identical is the FRAME's file claim
discharged, not a coincidence: a new `Cas.Backend.*` leaf is invisible
to `Walk.libraryImports` until it is named there, and naming it is a
promotion, hence a ruling.

Axiom footprint, printed against the compiled module — no `sorryAx`, no
`Classical.choice`, no new axiom:

```
treeProg_eq_seg, table_eq_seg, table_eq_treeProg, treeProg_length,
embed_treeProg, treeProg_run, treeProg_run_empty, treeProg_Triple,
treeProg_two_state
  → depends on axioms: [propext, Quot.sound]
Executed.runVerdict     → depends on axioms: [propext]
Executed.expectedWord   → does not depend on any axioms
```

Reproduced by the independent breaker at `e2703228` and unchanged by
the HOLE-1 fix. The footprint is one axiom shorter than PDD-1's, which
carries `Classical.choice`.

## Breaks

The ledger opened on the independent attack of `b5ad3c1d` / `db2c8344`,
recorded at `library/cas/contracts/attacks/PDD-9/RESULTS.md` and
`Attack.lean`, branch `attack/opus-cc-mac/pdd-9`, commit `e2703228`.
Verdict **STANDS** — no BREAK. No law was refuted, every gate and every
figure reproduced to the byte, the axiom census came back
`[propext, Quot.sound]` by an independent hand, both planted controls
reproduced verbatim, and sixteen break attempts failed, including every
search for a drift class that slips both pins.

All three rows below are therefore claim-side, not implementation-side:
the castle held and parts of the map were wrong. That is the shape
PDD-1's re-run rows have, and it is entered in the same register.

```
BROKE      b5ad3c1d / db2c8344 — the claim, not the code.
LAW        LAW X, as its BATTERY block stated it: the `#eval` half runs
           "over the registered terms of `Cas/Vectors/Registry.lean`
           that the seven generated programs are lowered from …: each
           term's `runP H (treeProg tr) []` is computed and compared"
WITNESS    `Executed.check` ran FIVE of the seven registered rows.
           `journalTwoEntries` (`journalTwo`, the registry's deepest
           term at eleven nodes) and `schemaVectorDocument` were named
           nowhere in the castle, at either digest — so `.genesis`,
           `.entry` and `.schema`, three of the grammar's ten clauses,
           had no executed consequence anywhere, and the line printed
           on every `lake build` said "the registered programs".
           Both missing runs PASS when run: `Attack.lean` §3 and
           `checkAdversarial`'s `journalTwo` and `schemaVectorDocument`
           rows, green at both digests.
CLASS      claim-scope — the stated boundary of the claim did not equal
           its actual coverage. Adjacent: `conformance`, since the
           uncovered clauses are the ones with the two-child offset
           arithmetic and the longest reference chains.
FIXED-BY   05dc3b65 — closed the STRONG way rather than by narrowing
           LAW X to the five it ran. `journalTwo` runs kernel-decided
           at the toy digest and in `check` at production;
           `schemaVectorDocument` runs in `check` at both. All seven
           registered programs and all ten grammar clauses now have an
           executed consequence, and the printed line says "all seven
           registered programs". Both new rows were red-tested (each
           expectation perturbed by one binding, each red, both
           reverted). The expectation is now the breaker's oracle, so
           a further registered term is covered by naming it.
```

```
BROKE      db2c8344 — the packet's LAW R prose.
LAW        "Three axes, per §8.0: ANSWER … GROWTH … STORE … LAW R
           carries all three."
WITNESS    `paddedShared` (`Attack.lean` §8): `treeProg
           blobSharedChunk` with one unrelated put prepended and every
           operand shifted. Its run answers exactly
           `blobSharedChunk.address toyAddr`, ends on a word that is
           `Word.wf` and honest — and contains a binding that is not in
           `blobSharedChunk.flatten toyAddr` at all. `treeProg_Triple`'s
           postcondition (`a = tr.address H ∧ Word.wf w' ∧ Honest H w'`)
           does not exclude it: it carries ANSWER and two invariants,
           and no frame. `treeProg_run` and `treeProg_two_state` do
           carry all three, and LAW F excludes the witness besides.
CLASS      claim-scope.
FIXED-BY   e2b364e8 — the packet's LAW R block; the module's own
           docstring at 05dc3b65. NOT `SPEC-BUG`: CONTRACT.md reserves
           that value for the adequacy class, this row is claim-scope,
           and commits landed that fix it — PDD-1's claim-scope row
           names a SHA for the same reason.
           The theorems are correct and unchanged; the packet
           overclaimed of one of them. LAW R's
           block now attributes each axis to the theorem that carries
           it, and states why the Triple is NOT strengthened: GROWTH
           and STORE are two-state facts and `Triple`'s postcondition
           sees only the final word, so writing them in is not a
           strengthening but a rederivation of `treeProg_two_state`.
           `treeProg_Triple`'s docstring now names `paddedShared` and
           says which axes it does not carry, so the fact cannot be
           met only in the packet.
```

```
BROKE      e45a9779 — the packet's adequacy REASON, in the builder's
           favour.
LAW        Adequacy candidate 2: a lowering with the right shapes and
           wrong operands "dies at LAW M, because the resolved
           reference addresses are then not the children's answers".
WITNESS    `badShared` (`Attack.lean` §6): the second leaf's operand
           rewritten `.ans 2` → `.ans 0`, a different LINE carrying an
           IDENTICAL node. The resolved address IS the child's answer,
           at every `H`; the length is unchanged, so LAW F is blind;
           and `runP` agrees with the true table's run at both the toy
           digest and `sha256Addr`, so LAW R's conclusion at any single
           address function is blind. The stated reason does not apply
           and the class was not closed by it.
CLASS      adequacy — the reason offered for a law, not the law.
FIXED-BY   SPEC-BUG. The adequacy class fired and the packet itself
           was amended (e2b364e8), which is exactly the case
           CONTRACT.md reserves this value for. The amendment runs
           UPWARD: LAW M kills
           `badShared` regardless, by a STRONGER reason than the one
           written: `embed` builds a `Prog` whose continuations are
           FUNCTIONS of the answers, so `embed p = tr.prog` quantifies
           over every address the interpreter could return and no
           coincidence at one digest discharges it. The breaker proved
           it — `badShared_dies_at_LAW_M`, kernel-checked at
           `[propext, Quot.sound]`. The packet now carries that reason.
           No theorem moved: this row records that the law was
           understated, not that it was wrong.
```

One further observation is recorded rather than rowed, because it is
not a break: the breaker noted (NOTE-4) that this packet's second
commit landed 56 seconds after the implementation, and diffed it line
by line to confirm it is additive — no ENSURES clause, no LAW statement
and no FALSIFIER moved. The same shape is on PDD-2's record as its
NOTE-6. The amendments in THIS pass are not additive: they correct two
claims and one reason, and each carries its ledger row above.
