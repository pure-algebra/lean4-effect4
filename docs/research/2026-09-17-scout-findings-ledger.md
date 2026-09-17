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
| E-B1 | E | `Guard/Core.lean` and `Guard/FrameOwned.lean` each declared the same 59 race-ownership declarations; `Guard/Settle.lean` held three lemmas proving the copies equal. | script: 59 textually identical | landing: `Guard/RaceSites.lean` holds them once, the bridge lemmas are gone (about 470 lines off the two slowest proof modules) | this ledger |
| E-B2 | E | `Codegen/Read.lean`: 2,571 of 3,507 lines are proof (90 theorems) inside an implementation module; no core module names any of them. | read | queued: move under `src/Effect4/Laws/Codegen/Read.lean` | scout E's note B-2 |
| E-B3 | E | `Laws/Program/Invocation.lean` states one equation a third time. | read | queued | scout E's note B-3 |
| E-B4 | E | `Typing/Blame.lean:431-765`: 51 copies of one tactic line. | read | superseded by C-P7 (the checker written once makes the whole proof a lemma about `Except`) | C-P7 |
| E-B5 | E | Sixteen hand-enumerated leaf lists for the loop fragment; every alphabet change edits all of them. | read; C compiled the generated recursor | queued as C-P4 | C-P4 |
| E-B6 | E | `rowAnswer`'s dead row parameter, 36 sites. | read | queued with R5 (the file is replaced) | R4-R6 packet |
| E-C1 | E | DI-61(c)'s reason for `readable` not being part of admission named `pAwait`, which is now readable. | compiled by the scout | **landed** `4a0af845` in the docstring (stated as a claim about what is certified); DI-61's row still to amend | DI-61 |
| E-C3 | E | Generated `Fold.lean` and `Scoped.lean` carry their laws under the core root, while the lifts are emitted as an implementation and a laws module. | read | queued: split at the next Fold regeneration if no core definition needs the theorems | scout E's note C-3 |
| E-C5 | E | The explicit-tactic rule is written in no tracked file. | grep | queued: the weaker form into `AGENTS.md` (in `Laws/`: no `simp_all`, `first`, `try`, `aesop`) | scout E's note C-5 |
| E-D2 | E | `Eff.arms` and `Eff.constructorNames` are two hand lists guarded only against each other. | compiled by the scout | queued as C-P1 | C-P1 |
| E-D3 | E | 240 line-ranged and 518 shorthand `.lean` citations are outside both citation gates. | measured by the scout | queued as C-P2 | C-P2 |
| E-D6 | E | `Prim.yieldableError` stays (machine alphabet, a green census row) and no program reaches it any more; the census does not say so. | read | open: one sentence in the census row | none yet |
| F-1 | F | Never compared with rc.112: `select … .option`, `select … .tag`, `iterate` with `some` or a non-unit result, `sleep`, `clockNow`, `awaitFiber .joinEffect`, a failing release, six printable fiber actions, 10 of 20 atoms, 48 of 55 native row positions. | compiled census by the scout | queued: four to six hand programs in the truth corpus; the typed-idiom generator family | scout F's note §9, §11 |
| F-2 | F | 10 of 24 `TypeReason`s and `PrintRefusal.layerRef` have no red control; three belong to `select` and `iterate`. | counted by the scout | queued: ten guards in `Test/Program/BlameContract.lean` | scout F's note §13.3 |
| F-3 | F | 12 of 25 constructors have no proved machine-to-meaning agreement (`gen`, the masks, `yieldNow`, `awaitFiber`, `withFiber`, `scoped`, `acquireRelease`, `provideLayer`, `service`, `provideService`, `catchIf`, async `perform`); for them "never wrong" means our two evaluators agree. | read | open: D5, the typed-state invariant stated once | scout F's note §6, §11.5 |
| F-4 | F | `Test/Program/Gen.lean` lists ten of twenty atoms by hand while `NativeAtom.covers` sits unused; `fns` duplicates `Native.fnNames`; nothing guards that the corpus draws every native row or decision; the truth corpus has no coverage guard. | read | queued: the atom guard moves every corpus byte, so it lands with the baseline promotion; the truth-corpus guard with a named exception list | scout F's note §7, §13 |
| F-5 | F | `harness/truth/select-controls.ts` was compiled by no lane; three `.test.ts` files under `harness/truth/` are run by nothing; `check-compat` was in no aggregate. | read | **landed** `4a0af845` (the copy; `check-compat` in `check-host`); the three orphan tests: wire or delete | this ledger |
| F-6 | F | The corpus baseline is still held though the `Eff` series closed. | read | queued: promote with the atom widening (one move of the corpus) | `docs/STATE.md` |
| F-7 | F | DI-73 (is a fiber id a value) is the only recorded run disagreement with rc.112: six corpus programs. | read | open: needs a recommendation | DI-73 |
| C-1 | C | Two schema dialects land in `Representation` (`Ty.schema`/`ofSchema` and `Store.render`/`ShapeDoc.document`) with no theorem between them; composed, they disagree on five formers (`unit` and `option` lost, `nat` reads back as `int`, `bytes` and `digest` silently widen to `string`). | compiled by the scout, with a red control | queued: C-P3 pins it today; the repair is part of C-P11 | scout C's note §2.2a |
| C-P1 | C | The alphabet's inventory generated from the inductive (`constructorNames`, a flat head enum, `arms` total on it) and a census guard per fragment predicate. | read | queued: the census guards first (minutes) | scout C's note §8 |
| C-P2 | C | Check line numbers in citations (1,516 unguarded sites), rc.112 form included. | measured by the scout | queued | scout C's note §8 |
| C-P3 | C | Pin `Ty.ofSchema ∘ Store.render` on the thirteen formers. | compiled by the scout | queued (an hour) | scout C's note §8 |
| C-P4 | C | A generated recursor per fragment predicate: 194 lines of constructor enumeration in nine files become none. | compiled probe; re-run owed (an olean was mid-rebuild) | queued | scout C's note §4 |
| C-P6 | C | The generator driver rebuilds between groups and takes its order from data, ending the by-hand regeneration ritual. | read | queued | scout C's note §6.3 |
| C-P7 | C | The checker written once in the refusal monad; `effTy` and `explain` as its two projections; `explain_none_iff` becomes a lemma about `Except`. About 520 lines net. | read | queued (two days); supersedes E-B4 | scout C's note §8 |
| C-P8 | C | The same fold is hand-written three times: `Schema/Representation.lean:1255-2111` (857 lines) and six traversals in `Store/Shape.lean` (242) are what `Effect4Gen/Fold.lean` emits; the blocker is that `readBlock` reads `List Representation` as a leaf. About 1,100 lines net. | read; the structural-recursion shape is unprobed | queued: probe first. The owner's priority (duplicated representations) | scout C's note §6.5 |
| C-P9 | C | Generate the `Ty` arms from `TyAlgebra` (27 hand arms per new constructor today). | read | queued, immediately before C-P10 | scout C's note §2.3 |
| C-P10 | C | `Ty.data name`: the nominal tree type, the missing `.reference` arm of `Ty.ofSchema`; one eliminator subsuming `Decision.option` and `Decision.tag`; no new `Decision` constructor until it is settled. | compiled probe by the scout | queued after the reader line; invariant by name, the `ShapeDoc` on the `Signature` | scout C's note §2.4 |
| C-P11 | C | `src/Effect4/Schema/**`: 9,174 lines, of which 108 code declarations and 173 theorems have no reference anywhere; `Schema/Dimension.lean`'s only reference is its import line. | measured by the scout | queued: delete what has no consumer, `Dimension.lean` first | scout C's note §6.4 |
| C-P12 | C | The option and list kit holds as evaluated; all five are atoms (an atom moves no wire byte), nullary atoms already exist. | read | queued after the reader line; `uncons` alone is a day | loop-sugar note §3 |
