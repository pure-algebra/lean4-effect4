# Scout findings ledger, 2026-09-17

One row per finding that asks for work. The scouts' notes hold the evidence; this file holds the
status, so nothing a scout found is lost between sessions. "Checked" means the coordinator
re-ran or re-read the claim against the tree, and how. Status: **landed** (with the commit),
**queued** (accepted, not started), **ruling** (waits on the owner), **declined** (with the
reason), **open** (not yet assessed).

Notes: A `2026-09-17-scout-reader-as-eff-program.md`; B
`2026-09-17-scout-bidirectional-types-and-iterate-ergonomics.md`; D
`2026-09-17-scout-named-and-exact-service-keys.md`; C
`2026-09-17-scout-schema-and-algebra-simplification.md`; E
`2026-09-17-scout-cleanup-and-organization.md`; F
`2026-09-17-scout-coverage-and-foundations-closeout.md`. The owner's standing direction for this
ledger (2026-09-17): no ceremony over rulings, take the recommendations; be aggressive in deleting
what is drift; de-duplicate, shared representations first; prefer proof changes that speed builds;
narrow builds per step, no full runs until a wave closes.
The coordinator's own note: `2026-09-17-loop-sugar-and-list-elimination.md`.

| id | from | finding | checked | status | tracked at |
| --- | --- | --- | --- | --- | --- |
| A-1 | A | One layer of the reader is authorable today as an `Eff` program with the existing sugar; in `Straight`; agrees with a Lean `matchLayer` and the machine; prints with existing prelude names. | probes 1 and 2 re-run, results match | queued: after R5.2, as a worked demonstration, in the scout's three slices | R4-R6 packet §5b |
| A-2 | A | `Val.ctor` is invisible to the language: no atom or decision sees the generated `Image` of an inductive. | read | open: folded into the tree-types question (C) | loop-sugar note §3b |
| A-3 | A | `run_eq_meaning` and the loop agreement are stated at the empty environment; a program with a free variable is not covered. | read | open | none yet |
| B-1 | B | `iterate`'s annotation optional, `none` synthesized and printed unannotated. | compiled (`ofTy` collisions, typing tells them apart) | **landed** `5185a6cd` (DI-91, ruled) | DI-91 |
| B-2 | B | `admitProgram`'s `int` ban missed a `Ty` inside the tree. | compiled (the counterexample was admitted) | **landed** `5185a6cd` (DI-92; `int` stays) | DI-92 |
| B-3 | B | A unit-result loop could print as the bare `Effect.whileLoop`. | n/a | **declined** by the owner: nothing just retired is refurbished | DI-91 |
| B-4 | B | No term constructs an `Option` value, so `select … .option` can only scrutinize a row's answer. | read (`NativeAtom.all`, `Lit`) | ruling: the option and list kit (`none`, `some`, `nil`, `cons`, `uncons`), or the nominal eliminator of §3b | loop-sugar note §3, §4 |
| B-5 | B | Loop sugar as authoring-only definitions (`iterateWith`, counting, folds, an effectful condition). | compiled: four forms typed and correct on the machine, the list fold correct and untyped | **landed**: `src/Effect4/Program/Authoring/Loops.lean` (`LoopSpec`, `iterateWith`, `forRange`, `foldRange`, `repeatWhile`), its scope laws in `src/Effect4/Laws/Program/Authoring/Loops.lean`, `Test/Program/LoopSugarContract.lean`. The list fold waits on B-4. Names stay the owner's to change. | loop-sugar note §2 |
| B-6 | B | rc.112 has no `Effect.iterate` and no `Effect.loop`. | read (`vendor/…/Effect.ts` exports) | noted; no idiomatic head to print | DI-91 |
| D-1 | D | "Full-key service identity" is one defect: a printed key has no nominal identity on rc.112, so the host's `R` identifies a service by carrier type; the measurement half landed (`38344fcc`), the repair (one nominal class per full key, and spelling `R`) is unstarted. "Named keys" as a change to `ServiceKey`'s data has no written plan; keys stay two numbers. | not yet re-run (the scout reproduced it in Lean and under `tsc`) | ruling: six owner rulings in the note's last section; recommended order R4, R5, then K1 to K4 | scout D's note §6, "What the owner must rule" |
| D-2 | D | `ServiceDef` authoring surface (declare a service once with a shape, then `service`, `provide`, layers), authoring-only (slice K0, no dependency). | read | queued: can land before the reader line; an afternoon | scout D's note §3, §6 |
| D-3 | D | The hand-selection target lane binds no service keys; the corpus lane's adapter branch is dead code. | read, both files | open (defect) | DI-93 |
| D-4 | D | `src/Effect4/Machine/Key.lean` rested the key order's authority on `PORT-MANIFEST.md`, which no longer exists; the citation gate is blind to a bare filename. | read; the file was removed at `1529a1fe` | **landed** with this ledger: the sentence cites `Ascending` in `src/Effect4/Data/Row.lean` and the manifest by revision | this commit |
| D-5 | D | The citation gate does not see bare filenames (`PORT-MANIFEST.md`, the earlier `Codegen/Layer.lean`). | read | open: a second pattern in `scripts/check-source-citations.py` for backticked `*.md`/`*.lean` names with no root | none yet |
| D-6 | D | `declarationTypeRepresentable`'s first disjunct, `printLayer`'s docstring paragraph, DI-24's superseded `R` clause, the scope key named twice with nothing checking agreement, the `nativeServiceTypes` hand list mirrored by hand into the profile. | read | queued with the key slices (K4, K5) | scout D's note §5 |
| D-7 | D | Two different nouns "key" in one M2 bullet of `docs/STATE.md` (the session's reply key, the service key). | read | queued: one glossary sentence | scout D's note §5.10 |
| E-A | E | List A: the red `check-tools` fixture (one coercion), three stale docstrings on `readable`, 18 duplicate guards and two `x = x` theorems in `InvocationContract`, one dead private lemma, stale printer line ranges, four dangling module citations, a Goldens docstring, a test heading. | each re-read; the fixture compiled; the contract rebuilt | **landed** `4a0af845` | this ledger |
| E-C2 | E | `cases-policy-complete.json` and `audit-complete.json` (1,393 lines) run by nothing and stale by four constructors. | grep: no caller | **landed** `1a973c18` (deleted), with the six abandoned `truth-check-*` runs and `clean-check` sweeping the prefix | this ledger |
| E-B1 | E | `Guard/Core.lean` and `Guard/FrameOwned.lean` each declared the same 59 race-ownership declarations; `Guard/Settle.lean` held three lemmas proving the copies equal. | script: 59 textually identical | **landed** `b3ea5a5d`: `Guard/RaceSites.lean` holds them once, the bridge lemmas are gone (511 lines net; `lake build Effect4.Laws.Program.Guard` green) | this ledger |
| E-B2 | E | `Codegen/Read.lean`: 2,571 of 3,507 lines are proof (90 theorems) inside an implementation module; no core module names any of them. | read | **moot**: the owner withdrew the move; the hand reader and the proofs about it are deleted (item 12), and the leaf round trips that remain are what R5.2 builds on | item 12 |
| E-B3 | E | `Laws/Program/Invocation.lean` states one equation a third time. | read | queued | scout E's note B-3 |
| E-B4 | E | `Typing/Blame.lean:431-765`: 51 copies of one tactic line. | read | superseded by C-P7 (the checker written once makes the whole proof a lemma about `Except`) | C-P7 |
| E-B5 | E | Sixteen hand-enumerated leaf lists for the loop fragment; every alphabet change edits all of them. | read; C compiled the generated recursor | queued as C-P4 | C-P4 |
| E-B6 | E | `rowAnswer`'s dead row parameter, 36 sites. | read | queued with R5 (the file is replaced) | R4-R6 packet |
| E-C1 | E | DI-61(c)'s reason for `readable` not being part of admission named `pAwait`, which is now readable. | compiled by the scout | **landed** `4a0af845` in the docstring and `ae8c8478` in DI-61's row | DI-61 |
| E-C3 | E | Generated `Fold.lean` and `Scoped.lean` carry their laws under the core root, while the lifts are emitted as an implementation and a laws module. | read | queued: split at the next Fold regeneration if no core definition needs the theorems | scout E's note C-3 |
| E-C5 | E | The explicit-tactic rule is written in no tracked file. | grep | **landed** `dc8e9b98`: the rule and the verification cadence are in `AGENTS.md` | `AGENTS.md`, Working |
| E-D2 | E | `Eff.arms` and `Eff.constructorNames` are two hand lists guarded only against each other. | compiled by the scout | queued as C-P1 | C-P1 |
| E-D3 | E | 240 line-ranged and 518 shorthand `.lean` citations are outside both citation gates. | measured by the scout | queued as C-P2 | C-P2 |
| E-D6 | E | `Prim.yieldableError` stays (machine alphabet, a green census row) and no program reaches it any more; the census does not say so. | read; checked that no `Eff` constructor compiles to it and no store program builds one | **landed**: the sentence is in `docs/RUNTIME-COVERAGE.md` (the foreign-boundary paragraph) | this ledger |
| F-1 | F | Never compared with rc.112: `select … .option`, `select … .tag`, `iterate` with `some` or a non-unit result, `sleep`, `clockNow`, `awaitFiber .joinEffect`, a failing release, six printable fiber actions, 10 of 20 atoms, 48 of 55 native row positions. | compiled census by the scout | queued: four to six hand programs in the truth corpus; the typed-idiom generator family | scout F's note §9, §11 |
| F-2 | F | 10 of 24 `TypeReason`s and `PrintRefusal.layerRef` have no red control; three belong to `select` and `iterate`. | counted by the scout | **landed**: every reason now has a red control in `Test/Program/BlameContract.lean` (`layerReference` on the unexpanded walker, since `Api.explain` catches an ill-formed reference at the root) | this ledger |
| F-3 | F | 12 of 25 constructors have no proved machine-to-meaning agreement (`gen`, the masks, `yieldNow`, `awaitFiber`, `withFiber`, `scoped`, `acquireRelease`, `provideLayer`, `service`, `provideService`, `catchIf`, async `perform`); for them "never wrong" means our two evaluators agree. | read | open: D5, the typed-state invariant stated once | scout F's note §6, §11.5 |
| F-4 | F | `Test/Program/Gen.lean` lists ten of twenty atoms by hand while `NativeAtom.covers` sits unused; `fns` duplicates `Native.fnNames`; nothing guards that the corpus draws every native row or decision; the truth corpus has no coverage guard. | read | queued: the atom guard moves every corpus byte, so it lands with the baseline promotion; the truth-corpus guard with a named exception list | scout F's note §7, §13 |
| F-5 | F | `harness/truth/select-controls.ts` was compiled by no lane; three `.test.ts` files under `harness/truth/` are run by nothing; `check-compat` was in no aggregate. | read | **landed** `4a0af845` (the copy; `check-compat` in `check-host`); the three orphan tests are **wired** into `check-truth` (all ten tests pass; they cover rc.112's `catchIf` clause, the prelude's cause queries, and the atom-against-prelude inventory guard, which no gate ran) | this ledger |
| F-6 | F | The corpus baseline is still held though the `Eff` series closed. | read | queued: promote with the atom widening (one move of the corpus) | `docs/STATE.md` |
| F-7 | F | DI-73 (is a fiber id a value) is the only recorded run disagreement with rc.112: six corpus programs. | read | open: needs a recommendation | DI-73 |
| C-1 | C | Two schema dialects land in `Representation` (`Ty.schema`/`ofSchema` and `Store.render`/`ShapeDoc.document`) with no theorem between them; composed, they disagree on five formers (`unit` and `option` lost, `nat` reads back as `int`, `bytes` and `digest` silently widen to `string`). | compiled by the scout, with a red control; re-run by the coordinator | pinned: **landed** `da5681e6` (`Test/Schema/DialectContract.lean`); the repair is part of C-P11 | scout C's note §2.2a |
| C-P1 | C | The alphabet's inventory generated from the inductive (`constructorNames`, a flat head enum, `arms` total on it) and a census guard per fragment predicate. | read | half **landed** `edcd1fcc`: `Test/Program/FragmentCensusContract.lean` (a sample per constructor against `constructorNames`; what `Straight` and `Looped` admit; the twelve outside both). The generated head enum is queued. | scout C's note §8 |
| C-P2 | C | Check line numbers in citations (1,516 unguarded sites), rc.112 form included. | measured by the scout | queued | scout C's note §8 |
| C-P3 | C | Pin `Ty.ofSchema ∘ Store.render` on the thirteen formers. | compiled by the scout | **landed** `da5681e6` | scout C's note §8 |
| C-P4 | C | A generated recursor per fragment predicate: 194 lines of constructor enumeration in nine files become none. | compiled probe, re-run green by the coordinator on the current tree (`[propext]`) | queued | scout C's note §4 |
| C-P6 | C | The generator driver rebuilds between groups and takes its order from data, ending the by-hand regeneration ritual. | read | queued | scout C's note §6.3 |
| C-P7 | C | The checker written once in the refusal monad; `effTy` and `explain` as its two projections; `explain_none_iff` becomes a lemma about `Except`. About 520 lines net. | read | queued (two days); supersedes E-B4 | scout C's note §8 |
| C-P8 | C | The same fold is hand-written three times: `Schema/Representation.lean:1255-2111` (857 lines) and six traversals in `Store/Shape.lean` (242) are what `Effect4Gen/Fold.lean` emits; the blocker is that `readBlock` reads `List Representation` as a leaf. About 1,100 lines net. | **landed in the working tree, not committed** (receipt: `docs/research/2026-09-17-generated-nested-fold-receipt.md`). The generator has a position language (leaf/direct/list/option/prod/one-parameter record) and a second emitter for a block with a composite position; regenerating the `Fold` group leaves `src/Effect4/Program/Fold.lean` byte-identical; three red controls (`Array`, an arrow, a two-parameter structure) are refused by name at exit 1. New group `SchemaFold` → `src/Effect4/Schema/Fold.lean` with guards; `Schema/Representation.lean` −854, `Schema/Annotations.lean` −1046 (its four mutual law blocks became two `Hom`s, a `cata_id` and a `funext`), `Schema/EffectfulField.lean` and the recursive-elimination attack ported, `Test/Schema/RepresentationFoldContract.lean` deleted (it restated generated statements). `lake build Effect4 Effect4Laws` 301/301 green, `TestSchema` 68/68 green. | **landed**: `2d0866a5` (the generator reads nested children), `aa72f457` (the `SchemaFold` group), `85e5314d` (the hand fold deleted, consumers ported: `Representation.lean` −854, `Annotations.lean` 2,304 → 1,258, the fold contract test deleted), `ed3a607e` (step 4.1-4.2: `Schema/Check.lean`'s three copies of the recursion are one Boolean algebra of the generated fold; the thirty per-constructor theorems keep names and statements; 1,827 → 1,515). Whole tree green after step 3 (418 jobs). **Remains:** `Codegen/Schema.lean`'s printer as an algebra (patch prepared, to be applied with a before/after text diff of the printer); the wave's sweep. `Store/Shape.lean` stays out: its acceptance and printing recurse on the VALUE with the shape looked up in a table, so they are not folds of the shape. `Annotations.lean`'s three remaining `Hom` blocks (about 340 lines of per-constructor one-liners) would need a layer-level traversal the generator does not emit; not cheap. | scout C's note §6.5; this seat |
| C-P9 | C | Generate the `Ty` arms from `TyAlgebra` (27 hand arms per new constructor today). | read | queued, immediately before C-P10 | scout C's note §2.3 |
| C-P10 | C | `Ty.data name`: the nominal tree type, the missing `.reference` arm of `Ty.ofSchema`; one eliminator subsuming `Decision.option` and `Decision.tag`; no new `Decision` constructor until it is settled. | compiled probe by the scout | queued after the reader line; invariant by name, the `ShapeDoc` on the `Signature` | scout C's note §2.4 |
| C-P11 | C | `src/Effect4/Schema/**`: 9,174 lines, of which 108 code declarations and 173 theorems have no reference anywhere; `Schema/Dimension.lean`'s only reference is its import line. | measured by the scout | step 0 **landed** `01103182` (`Schema/Dimension.lean` deleted); the rest queued: delete what has no consumer | scout C's note §6.4 |
| C-P12 | C | The option and list kit holds as evaluated; all five are atoms (an atom moves no wire byte), nullary atoms already exist. | read | queued after the reader line; `uncons` alone is a day | loop-sugar note §3 |

## What this wave landed (2026-09-17), in order

`5185a6cd` DI-91 and DI-92; `23420ee2` this ledger, DI-93, the `Key.lean` citation; `33990200` the
loop sugar; `4a0af845` scout E's list A and two harness repairs; `1a973c18` the ungated pins and
the abandoned runs deleted; `b3ea5a5d` the Guard block stated once (511 lines net); `01103182`
`Schema/Dimension.lean` deleted; `edcd1fcc` the fragment census; `1f4edcb9` a red control per
refusal reason; `da5681e6` the dialect contract; `dc8e9b98` and `ae8c8478` STATE, `AGENTS.md`,
DI-61.

**Owed by the wave's gate sweep** (the owner stopped the full runs; every step above was checked
by a narrow build): one `make check` and one `make check-host`. Unswept in particular: the root
imports added to `src/Effect4.lean`, `src/Effect4/Laws.lean` and `Test/All.lean`; `check-truth`
with `select-controls.ts` now compiled; `make check-tools` with the repaired fixture.

**Next, in the owner's order of concern** (duplication and drift first): C-P8 (one generated fold
for `Representation` and `Shape`), C-P7 (the checker written once), E-B2 (the reader's proofs
under `Laws/`), C-P4 (the generated fragment recursor), C-P2 (line numbers in the citation gate),
C-P11 (the schema tree's unconsumed declarations); then the reader line R4.1.

## Rulings and dispatch, later on 2026-09-17 (owner: "go with your recommendations")

1. **C-P8 scope:** `Representation` in; `Store/Shape.lean` out (two of its six traversals recurse on
   a value and a shape together; the rest are exhaustive matches); the monadic half for nested
   families is not emitted until something consumes it. Seat dispatched on
   `docs/research/2026-09-17-generated-nested-fold-ready-packet.md` (`a317d502`). Found while
   writing the packet: the nine-helper recursion is hand-written four MORE times
   (`Schema/Check.lean` three, `Codegen/Schema.lean` one); they are the packet's step 4.
2. **E-B2 withdrawn.** The hand reader is to be deleted, not reorganised: `Codegen/Read.lean` and
   its 2,571 proof lines go in one commit when the generic reader passes `ReadContract` (R5.2);
   until then the file is frozen (compile fixes only).
3. **Seat order after C-P8, one at a time:** C-P7 (packet
   `docs/research/2026-09-17-checker-once-ready-packet.md`, probe beside it), C-P4, C-P6, C-P11,
   then R4.1.
4. **C-P7's design changed from the scout's.** `effTy := toOption ∘ checkEff` would change the
   unfolding under 66 `mvcgen` inversion lemmas, the specs generator's six `Option` roots and the
   LCNF rule reader's `refusal: Option.none`. The packet's design is one checker generic in the
   carrier of refusals (`Refusing`: `refuse`, `under`), instantiated at `Option` (today's `effTy`,
   old equations by `rfl`) and at `Except TypeRefusal`; the law is naturality, one `simp only` per
   arm. Probe green. About 360 lines net rather than 520. Two unknowns need the project compiled
   (the specs harvest, `check-cases`); they are the seat's bounded step 0, with a named fallback.
5. **C-P11's rule:** code with no reference anywhere (tests included) is deleted; a theorem stays
   only if a contract packet or a test names it or something uses it.
6. **DI-73** ruled as answered by DI-81; **DI-93** fixed (`f51b2fcb`): one binding rule inside
   `requirements`, the dead adapter branch deleted, the hand-selection lane binds keys by shape.
7. **Parked, unchanged:** the five option/list atoms and any new `Decision` constructor wait for
   `Ty.data`; generate the `Ty` arms before `Ty.data`; both after the reader line. The three
   orphan `.test.ts` files: delete unless one covers what no gate covers (each to be read first).
   The corpus baseline is promoted in the same move that widens the generator's atom list.

8. **Landed the same evening, beside the C-P8 seat** (builds disjoint from the seat's):
   **R4.1** `a008cd97` (`Codegen/Template.lean`, `Laws/Codegen/Template.lean` with `match_inst`,
   `match_keys`, `inst_of_match` at `[propext, Quot.sound]`, `Test/Codegen/TemplateContract.lean`);
   the table architecture probed (`0d39526e`: the printer as a fold of one table-driven layer
   function, the reader as its one-step inverse; the R4 packet §3b); E-D6's sentence and the
   three orphan host tests wired into `check-truth`.

9. **R4.2 and R4.3's guard, the same evening** (`5c502b4d`, with the generated layer view
   `ede32728` and the reader's measure `ecbedb7a`): the table (57 rows) and `printT` as the fold
   of one generic layer function. Re-run after the row reordering, against the oleans then on
   disk: the agreement battery green; 400 of 400 corpus programs print under both printers, so
   the agreement is not vacuous. Owed: a `lake build` of the two modules and their root imports
   once the C-P8 seat has finished (they are in no root yet, so its builds do not see them).

10. **What the schema landing made cheap, measured by reading rather than by counting mentions**
    (the owner's challenge, and a correction of the coordinator's first assessment): the three
    copies in `Schema/Check.lean` (done, −312); the printer in `Codegen/Schema.lean` (a well-founded
    recursion with five size lemmas and seven `decreasing_by` blocks becomes one algebra);
    38 schema declarations that occur nowhere else in `src`, `Test`, `tools` or the top-level docs
    (one linear `grep -F -w -o -f` pass per file, not the scout's 108, which counted uses inside the
    declaring file as none). Of 856 unused-simp-argument warnings in the build log, 613 are in
    `Program/Typing/Blame.lean`, the law C-P7 deletes, and 50 in `Laws/Codegen/HoistingReadable.lean`,
    which goes with the hand reader.

11. **Dead names across the hand-written source, measured** (one linear `grep -F -w -o -f` pass per
    file over `src`, `Test`, `tools` and the top-level docs; generated files left out). In the
    schema tree: 38 found, 35 deleted (198 lines, `79bd2ab5`; whole tree green after it). The three
    annotation-key lawfulness theorems the pass caught were restored: `AnnotationKey.Lawful` is an
    obligation every key owes (as `Store/Shape.lean`'s keys prove theirs), and their keys are in
    use or exported.
    Everywhere else: **no dead code** (one definition, `Store.putOr`, and one private theorem in
    the hand reader), and **532 public theorems that no file, test, contract packet or top-level
    document names**, 313 of them under `Laws/` (most in `Laws/Machine/Witnesses.lean` 33,
    `Laws/Machine/Handles.lean` 28, `Machine/Stores.lean` 28, `Laws/Program/Guard/Core.lean` 26).
    By ruling 5 as written they would go; the coordinator has NOT deleted them, because a law is
    often the product and not a step, and a script cannot tell a headline from an orphan. They
    are the owner's call, module by module.

12. **The reader cutover (R5.1 and R5.3 at once, by the owner's ruling: fast, no ceremony, a
    temporary loss of theorems accepted).** `Codegen/Read.lean` is the table reader: `readT`, one
    generic step over `Templates.table` (first row whose skeleton matches; arguments by sort;
    an argument the classifier determines is supplied; the generated `build`), well-founded on
    the tree's size through `match_below`, total for ANY table; a generator's statements and the
    row call of `perform` stay hand fields, as in the printer. A row is accepted only when the
    printer would choose it for what was read (`Row.selects`), which replaces the hand reader's
    special `catchIf` test. `readable` is the round trip itself, so `roundTrip_eq` is by
    definition. 3,499 lines to 1,810; `Laws/Codegen/HoistingReadable.lean` deleted (305);
    `Laws/Codegen/Module.lean` 330 to 261 with `readModule_printModule` restated over
    `ReadsBack` (any reader); `ModuleEmission.admit` and `Api.admitModule_emitModule` restated
    over "the emitted module reads back".
    Measured before the swap, on the 400 seeded programs: the table reader agrees with the hand
    reader on 356, reads 44 images it refused (loops), never the reverse, never differently;
    exact on 400; round trips 298 to 335.
    **Deleted and owed (R5.2):** `read_print`, `read_exact` (and `_all`, `_native`, `_layer`),
    `roundTrip_weaken`, the structural `readable` with `readable_hoistAll`,
    `printModule_readable`, `readModule_printModule_readable`, `emitModule_complete`,
    `ModuleEmission.readModule`, `Api.printModule_roundTrip`. The faces contract and the design
    map say so (amendment of 2026-09-17).
    **Expected red until R6:** `make check-ts-reader` (the TypeScript reader is a port of the
    hand reader; the corpus directory now holds loops it does not read), and the corpus index
    and tsdiag agreement files regain the loop rows on their next regeneration.
    The table's depth column now carries term depths from the scope algebra (`catchIf`'s test
    under one binder; the loop's test, step and result under one, two and one): the printer
    never read them, the reader does.

13. **The printer cutover** (`d1c58906`, the same ruling). `print` and `printLayer` are the fold
    over the table; the six mutual hand printers are deleted (270 lines); the leaves, the row
    printer, the refusals and the reserved heads moved below the table to
    `Codegen/PrintLeaf.lean`. `Codegen/Print.lean` 731 to 191 lines. The agreement battery had
    been green on every constructor, classifier and the corpus; its agreement guards are removed
    (they would compare a function with itself) and it keeps the table's shape guards.
    The printer and the reader now have NO clause per constructor anywhere: the 57 rows of
    `Codegen/Templates.lean` are the only place a printed form is written. Both cutovers
    together: 4,535 lines of hand recursion and its proofs down to 2,670 across four modules.
    Coordinator's error, corrected by the owner: two whole-tree builds were run for these
    cutovers where narrow builds of the consumers and the four batteries would have shown the
    same. Narrow builds only until the wave closes.

14. **The reader line after the cutover: R6, and five simplifications the owner asked for the same
    evening** (each committed with its narrow builds, the corpus bytes compared before and
    after, and the TypeScript differential at matched 416, mismatched 0).
    - `f6f597ac` **R6**: `ts/eff/read.ts` is one matcher over `ts/eff/templates.gen.ts` (the table,
      argument sorts, field names and program heads, written by `TsGen`); 45 per-head readers gone;
      the corpus regains its 45 loop programs; `check-ts-reader`'s three steps green by hand.
    - `b0912a59` a row states no depth: `Template.levelAt` reads the binders in scope at a hole
      off the skeleton; "a layer is closed" is a fact of the family (`argDepth`). Guarded against
      the binder table (`Node.binders`) child by child. Three entries of the old column had been
      corrected by hand that day.
    - `8c9c186f` a generator and its six statements are rows: the calculus gained seven formers
      with their cases in all five law blocks; no hand recursion is left in printer or reader, in
      either language.
    - `613fa0c6` a classifier pattern either fixes its argument (`is v`) or chooses the row;
      `ArgPat.holds_of_supplies` proved.
    - `0b45e22e` `perform` is a row (`RowOut.rowCall`, last of the program rows): every
      constructor of the row families is in the table; the printer's algebra has no hand
      constructor field. Its signature rows are deliberately NOT compiled to skeletons (it is a
      codec with a proved round trip; compiling would discard about 600 lines of proofs and bring
      the same disjointness back as a premise).
    - `26c046c3` located diagnostics: `readEffAt` / `Api.readAt` give the path to the node that
      refused and, when a reserved head matched no row, what the nearest row's skeleton has where
      the tree parts from it (`Template.explainT`, generic over rows). The refusal stays flat, so
      no pin moved. Same five inputs pinned in Lean and TypeScript.
    From the owner's two external audits, taken: closure by family, `Tpl.head?` as the key for
    R5.2's disjointness (a fact, not a runtime index: 63 rows, the first node rejects, the corpus
    reads in 0.1 s), the `.rowCall` row, path diagnostics, and the shape
    `readable = scopedAt ∧ reconstructible` for R5.2's domain. Declined with reasons: a runtime
    head index; generic spine folds (six lines; the carrier is a reader over `Except`, not a free
    monoid); `cata_ctx` (already landed on 09-16; the structural `readable` it cites is deleted).
    Noted, not reader work: quasi-quoting from the table, semantic cards over the folds.
    **Open question for the owner, found on the way:** the printer emits `forkIn`/`forkScoped`
    with `daemon = false` as the same text as the daemon fork, which rc.112 runs as a daemon; it
    is outside `readable`, but it is printed without a refusal. A refusing row would be one line.
    **Owed: R5.2**, over this final shape.


## Later still on 2026-09-17: R5.2 closed; aesop; the API seats

- **aesop is the law graph's proof search** (`a4168094`, `5e6920cf`, `d563260e`): rules in the
  default set (`Laws/Auto/Inversion.lean`), a census instrument (`Laws/Auto/Census.lean`), the
  AGENTS.md rule rewritten. The rewriter that automated proof replacement was retired by the
  owner ("you don't even know how to use aesop yet"); the workflow that replaced it is in memory
  (`aesop-proof-workflow`): state, `aesop (add …)`, read residual goals, restate.
- **Law 11 over the table** (`52a2b602`, `Laws/Codegen/ReadPrint.lean`, 1,932 lines): `read_print`,
  `readLayer_print`, `ReadsBack.of_Readable` at `[propext, Quot.sound]`. `Readable` is a fold
  (`readableAlg`); the proof is one node step by induction on the image's size; the table-specific
  part is the decided `table_apart` (`rowsApart`: apart by head or by shape, `match_apart`), and
  `decide` found two overlaps the reasons had not named. A new overlapping row fails `table_apart`
  and asks for one `shapeApart` reason — the row contract.
- **Completeness** (`1cdbe2de`, `Laws/Codegen/PrintReadable.lean`): `print_of_readable`,
  `roundTrip_of_readable`, `readable_of_Readable`. Size by a fold (`sizeAlg`, `size_child_lt`
  generic), `inst_of_kinds` + decided `table_holeKinds`.
- **The four module corollaries are back** (`67a3e023`, `2fb7051a`, `Laws/Codegen/ModuleReadable.lean`)
  over `moduleReadable` (per hoisted piece): `readModule_printModule_readable`,
  `ModuleEmission.readModule`, `Api.printModule_roundTrip`, `printModule_readable`,
  `emitModule_complete`. Trap met: `simp` on `(t == t) = true` for `List Nat` brings
  `Classical.choice`; proved structurally.
- **Owner ruling, landed** (`09be67a8`): a child (non-daemon) `forkIn`/`forkScoped` is refused by the
  printer (`internalAction "forkIn:child"`), never printed as the daemon it is not; the corpus
  generator draws daemon forks only; 42 more corpus programs read back (385 of 408). Owed at the
  wave's gate sweep: `harness/truth/corpus.json` (host cut).
- **The API direction** (owner, ratified with two scout notes committed `64619565`): three deep
  modules `Author` / `Run` / `Face` (the term is **Run**, not Session), every convenience a function
  into `List Command`; daemons visible as data (static supervision tree, fiber statuses in the
  observation); layers as the place for composable semantics; the layer binder after this line.
  Three Opus seats dispatched in worktrees `../lean4-effect4-{run,author,daemons}` (branches
  `seat/*`, from `1a8587f2` which adds `Api.Built`), each with the aesop discipline in its brief;
  receipts owed at `docs/research/2026-09-17-seat-{run,author,daemons}-receipt.md`.

## The mid-wave review of the three seats (2026-09-17, owner: "address these findings")

An outside review of the three seat branches, checked against the worktrees before anything
moved. Verified and done, queued to the merge, or refused with the reason:

- **`Api.Built` was uninhabitable** (review 2A, verified: `#print` showed
  `table : {RowTable : Type} → RowTable`, auto-bound). Fixed in main (`3cf0d1e8`) with the run
  seat's exact text (`set_option autoImplicit false`, `open Effect4.Program (RowTable
  AdmittedProgram)`); the author seat was asked to match it so its merge is clean.
- **Two size folds** (2B, verified: `nodeSize*` in `Laws/Api/Supervision.lean` was the section of
  `PrintReadable.lean` plus `nodeSize_pos`). One module now: `Laws/Program/Size.lean`
  (`c2688499`: `sizeAlg`, `size_pos`, `size_child_lt`, imports only the generated view); the
  daemons branch merged (`9aa13150`) and pointed at it (`cdb67adb`, 542 → 501 lines).
- **`Api.Run` renamed `Api.Inspection`** (2C, `8df51c55`, 16 files): the reading a replay is
  taken as (outcome, machine, reasons); `Run` is the seat's value. The run seat's
  `_root_.Effect4.Run` spellings and `Run.inspect : Api.Run`, and the author seat's
  `Built.run : Run`, are edited at their merges.
- **Supervision in the observation** (2D): queued to the run seat's merge, in the daemons seat's
  shape rather than the review's — one field `fibers : List (FiberId × FiberStatus)`, with
  `daemons` and `daemonsQuiet` functions of it (a field that is a function of another field is a
  drift point; receipt §5).
- **aesop in the seats' laws** (3A): stale for the daemons seat (`status_persists` is already
  `unfold statusOf; aesop`; census 8/44 closed, six `rfl` equations kept because aesop's proof of
  two reaches `propext`). The run seat's `result_header` (four `repeat' split; all_goals rfl`
  arms) is within the rules; the one-line shape was sent to the seat as optional.
- **`nativeSignatureWith` into `Api.check`/`explain`** (4B): **not done — a decision.** Moving the
  definition beside `nativeSignature` is free (it is `rfl` at `[]`); threading it through the
  checker changes the certificate's signature, hence `Built`, `HostSession.start`, `Run.open`,
  and the soundness statements (`MeaningSound`, `LoopSound` are stated at `nativeSignature
  table`). The author seat's `build` compares declared carriers against `nativeSignature` and
  refuses a disagreement (`BuildRefusal.serviceCarrier`), which is the honest version until the
  owner rules on carriers beyond the six the type codes spell.
- **`Row.requires := [s.key]` on service operations** (4C): **refused.** `Typing.lean:302` puts a
  row's `requires` into the program's requirement; an operation is a method on a receiver already
  in hand (`ServiceDef.receiver`), and the key is required by `service key`, not by the call. With
  the change a layer's own build would require the key it provides.
- **`letLayer`** (4D) and **`Ty.data`** (4E): after this line, as already planned.

Merge order held: daemons (done) → run → author, then one gate sweep.
