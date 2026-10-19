# 2026-10-19 seat 3b receipt: binders by lexical scope (release item 3, part b)

**The one thing to know before merging:** both readers take any binder names. The reader reads
the printer's text as it stands, and any other text after the renaming of its binders to the
printer's names (`Rename.expr`, `src/Effect4/Codegen/Rename.lean`), each use resolved to its
nearest binder. Law 11 (`read_print`) keeps its statement and its domain. Law 12 (`read_exact`)
is restated as a disjunction: the text is the print, or the renaming writes the print. The
brief's one-sided form needs a smaller readable domain, an owner decision (option B under open
items). The oxc engine's rewrite to `a<depth>` names stays, for the reason under "The oxc
rewrite".

## Base and head

Branch `refactor/phase1-phase3`, main checkout, no worktree. Base `96198c7cc`. The owner's
`95b711a06` (one line of `Test/contracts/faces.contract.md`) landed on the branch after the base;
this slice touches no file of it. Head of the code: `f519aed3c`; the commit of this receipt
follows it.

## Commits and their files

1. `c8b6d5ad6` Codegen: the reader takes any binder names, renamed to the printer's.
   - `src/Effect4/Codegen/Rename.lean` (new, 395 lines): the renaming `Rename.expr`, a fold of
     the target syntax over `Rename.Binders`; `Rename.closedHeads` from the layer rows;
     `Var.index?`; and `ReadFailure`, moved here from `Codegen/Read.lean`.
   - `src/Effect4/Codegen/Read.lean`: `readMintedAt` and `readLayerMintedAt` are the old
     entries; `readEffAt` and `readLayerAt` try them, then the renaming. The module note says so.
   - `src/Effect4/Laws/Codegen/Read.lean`: `readMinted_exact`, `readLayerMinted_exact` (the old
     proofs), and `read_exact`, `readLayer_exact` restated.
   - `src/Effect4/Laws/Codegen/ReadPrint.lean`: `readMinted_print`; `read_print` and
     `readLayer_print` with their statements unchanged; the new `read_renamed`.
   - `src/Effect4/Laws/Codegen/PrintTyped.lean` (`readTyped_exact`) and
     `src/Effect4/Laws/Codegen/Mask.lean` (the field `readExact`): restated with law 12.
   - `src/Effect4/Api/Codegen.lean`: the note of `Api.read`.
   - `tools/ProofGraph/Registry.lean`: the claim `binder-names-read`; the title of
     `typed-print-read`.
   - `docs/core/semantics.md` §2.5: the claim's bullet.
   - `Test/Codegen/ReadContract.lean`: the section "Binders by lexical scope" and a pin of the
     `binder` refusal. Four pins move. Three that used a wrong binder name now use a function
     of two binders, with the same answers. `Ref.update(a0, (a0) => a0)` now reads, its
     parameter shadowing the outer binder.
   - `Test/Codegen/TermRows.lean`: the red control pins the refusal of the reader of the
     printer's names, and the reading after the renaming.
2. `f519aed3c` ts/eff: the TypeScript reader takes any binder names, as Lean's does.
   - `ts/eff/read.ts`: `rename` and its helpers, `readMinted` and `readLayerMinted`, the two
     entries, and the adapter's bound names (`Bound`, `exprOf`, `stmtsOf`); `readEffs` goes.
   - `ts/eff/test/read.test.ts`: the describe block "binders by lexical scope", a method off an
     author's binder, and the cases the renaming moves.
   - `ts/eff/test/fold-syntax.test.ts`, `ts/eff/test/term-rows.test.ts`: the wrong-level cases
     now read, renamed.
3. This receipt and `docs/research/2026-10-20-coherence-audit/item3b-option-b-normal-form.lean.txt`.

## The law, placed first (AGENTS.md, the five items)

1. **Concept.** Concept 5, `exact-codecs` (`docs/core/semantics.md` §2.5). The required property
   is the exact embedding of §2.5, point 2: the printer and the reader on the readable domain
   satisfy the retraction `read (print p) = p` (law 11) and exactness under an explicit
   normaliser (law 12).
2. **Question.** The R8 top nodes `read_print` (`src/Effect4/Laws/Codegen/ReadPrint.lean`) and
   `read_exact` (`src/Effect4/Laws/Codegen/Read.lean`) stay. Law 11 keeps its statement. Law 12
   is restated under the reader's named normaliser, the renaming. The new claim of concept 5 is
   `binder-names-read` (`tools/ProofGraph/Registry.lean`), pointer `read_renamed`
   (`src/Effect4/Laws/Codegen/ReadPrint.lean`): a text whose binders rename to the print of a
   readable program reads. Its role is compatibility, as for the other reader claims.
3. **Reach.** The judgment is the reader's acceptance (`readEff`, `readLayer`) on
   `TypeScript.Expr` syntax, at a lawful spelling (`LawfulSpelling`). The observation is the
   program read. Law 11 holds on the readable domain (`Readable`), as before. Law 12 holds for
   every tree the reader accepts. `read_renamed` holds at a readable program. Decisions rows 418
   (the release plan) and 245 (the mask rows keep law 11 and law 12) bound it.
4. **What it does not establish.**
   - No equality of raw texts: two texts that differ in their binders' names read to one program.
   - Nothing of what tsgo accepts. The lexical scope is TypeScript's with two differences. A
     layer clause closes it, as the printer prints a layer at the empty environment. A call's
     head is a name, never a use of a binder. A block's binder is in lexical scope over the whole
     block, as in TypeScript, so a use before its declaration is refused.
   - The TypeScript reader's agreement with the Lean reader is a finite check, not a theorem.
   - A definition's header, a service's closures and the row services' accessors still carry
     the printer's names.
   - `read_renamed` does not say that its two programs agree when the text is itself a print.
5. **What it unlocks.** Release item 4 (agent text in: `open` and `fill` take Effect TypeScript
   text through the reader), rank 3 of the ergonomics probe
   (`docs/research/2026-10-13-agent-ergonomics-probe/README.md`, findings E10 to E12), and R8,
   whose top nodes are the two laws.

Placement of each landed theorem, all concept `exact-codecs`, requirement R8:

| Theorem | File | Role in the graph |
| --- | --- | --- |
| `read_print` (law 11) | `Laws/Codegen/ReadPrint.lean` | R8 top node; statement unchanged |
| `read_exact` (law 12) | `Laws/Codegen/Read.lean` | R8 top node; restated |
| `readLayer_print`, `readLayer_exact` | the same files | the layer forms of the two laws |
| `read_renamed` | `Laws/Codegen/ReadPrint.lean` | pointer of the new claim `binder-names-read` |
| `readMinted_print`, `readMinted_exact`, `readLayerMinted_exact` | the same files | steps of the laws above: the old proofs, at the reader of the printer's names |
| `readTyped_exact` | `Laws/Codegen/PrintTyped.lean` | restated consumer of law 12 (claim `typed-print-read`) |
| `mask_rows_table_premises` | `Laws/Codegen/Mask.lean` | its field `readExact` restated with law 12 |

## The design, and the one choice in it

The renaming is a fold of the target syntax (`TypeScript.cata_expr`, `Codegen/TsFold.lean`). It
resolves a name by the authoring scope reader's rule (`Authoring.Names.resolve`), the one
resolver. It closes the lexical scope under the head of a layer clause (`Rename.closedHeads`,
read off the template table's layer rows), since the printer prints a layer at the empty
environment. It refuses four texts where they stand, with the target syntax's path:

- an unbound name of the printer's form that a renamed binder would capture;
- a binder in a call head's place;
- a name that a parameter list or a block declares twice;
- a use before its block's declaration of that name (`Rename.Binders.later`), as the source
  binding analysis (`Codegen/SourceBindings.lean`) refuses it.

An unbound name of any other form stays as written, so the reader refuses it on the program's
path, as before.

The reader tries the printer's names first (`readMintedAt`) and renames only a text that reader
refuses (`readEffAt`). The order matters at one corner. A term atom may be spelled like a layer
clause's head, such as `Layer.merge`. With a list fold inside it, below a binder, the renaming
closes the lexical scope there and the printer does not, so the renaming does not fix that
print. With the printer's names first, law 11 holds on the whole readable domain, unchanged.
Law 12 is then the disjunction, since that print is accepted as it stands. `ReadFailure` moves
from `Codegen/Read.lean` to `Codegen/Rename.lean`, below the reader, which imports it.

The TypeScript reader (`ts/eff/read.ts`) does the same, clause for clause: `readEff` and
`readLayer` try `readMinted` and `readLayerMinted` first, then `rename`. The adapter from oxc's
tree (`exprOf`) now carries the names its enclosing binders declare, so `r.read(3)` on an
author's binder `r` is a method call on a receiver, as `a0.read(3)` was, and not the dotted head
`r.read`. The unused `readEffs` is deleted.

## The oxc rewrite (the coordinator's scope note)

The rewrite stays, and `ts/eff/ingest/oxc.ts` is unchanged (`wc -l`: 1172). Two reasons, each in
the code:

1. The forms expansion names binders by level, not by source name. `forms.ts` (`expandForm`,
   `effectSlot`) is generated from Lean's `Forms.Template` and shared with `ck.ts`. A template
   makes binders that no source names: `exprForms.bind`, `onExit`, `matchCause` and
   `acquireRelease` bind `a<depth>`, and a template term names a level (`variable`). An argument
   read under inserted slots meets those binders by position: `effectSlot` inserts placeholders
   into the argument's environment, which moves the argument's own binders. For example,
   `Effect.acquireRelease(acquire, (r) => release)` lowers through the form `releaseOne`. The
   template binds `(a<d>, a<d+1>)`, and `r` in the body must be `a<d>`. With source names, the
   template's parameters would have to carry `r`, and the forms algebra never receives it.
2. The environment also drives recognition and the ingest's own refusals: a receiver against a
   head (`methodCall`, `sqlTemplate`), a shadowed scope namespace (`checkScopeBindings`), a call
   of a binder (`E-ANSWER-HIGHER-ORDER`) and an unbound name (`E-REF-UNBOUND`). Both engines must
   give one verdict (`make check-ingest-smoke`), and `read.ts` would answer `unknownIdent`.

The rewrite resolves by the same rule, the last name in the environment (`env.lastIndexOf`,
`term` in `ts/eff/ingest/oxc.ts`), and so does the renaming in `read.ts`. On the oxc engine's
output every binder carries the printer's name, so `read.ts` reads it as it stands and never
renames it. Passing source names would take a forms algebra that names each binder from the
argument's environment, a change to `forms.ts`, which `ck.ts` shares.

## Commands and results

Every Lean command ran as `python3 /private/tmp/seams-lean-one.py lake …`, one at a time. The
last run of each, on the committed sources:

| Command | Result |
| --- | --- |
| `lake build` of the touched modules and their direct dependents: `Effect4.Codegen.{Rename, Read, EraseTypes, Admit, Forms}`, `Effect4.Api.Codegen`, `Effect4.Laws.Program.Folds.Term`, `Effect4.Laws.Codegen.{ReadLeaf, Read, ReadPrint, PrintReadable, PrintTyped, Mask}`, `Effect4.Laws.Api.ModuleReadable`, `ProofGraph.Registry`, `ProofGraph.AxiomAudit`, and the 42 batteries that call a reader entry point (`grep` over `Test/` for `readEff`, `readLayer`, `readTyped`, `roundTrip`, `readModule`, `readFile`, `Api.read`, `readAt`, `readBlock`, `ReadsBack`, `read_print`, `read_exact`) | `Build completed successfully (1365 jobs)` |
| `make batteries-touched BASE=96198c7cc LAKE="python3 /private/tmp/seams-lean-one.py lake"` | `batteries-touched: 6 batteries`; `Build completed successfully (1269 jobs)` |
| `lake env lean` of a scratch file with `#axiom_audit` over the nine modules below | the axiom output below |
| `tsgo --noEmit -p tsconfig.json` in `ts/eff` (tsgo 7.0.0-dev.20260629.1) | no diagnostics |
| `bun test` in `ts/eff` (bun 1.4.2) | `802 pass`, `0 fail`, 30 files |
| `make check-ts LAKE="python3 /private/tmp/seams-lean-one.py lake"` | exit 0, 37.8 s; every lane `PASS`: check-tsgo, tsgo, target (104 of 104 resolved; assignability 742 pairs), ts-reader (501 files: matched 416, mismatched 0, refused with oracle 0), tsdiag, ingest-smoke (`408 exact JSON/wire comparisons on each parser`), service-identity |
| `git status` after the gates | no generated file moved |
| `wc -l ts/eff/ingest/oxc.ts` | 1172, unchanged |
| `python3 scripts/check-language.py --show docs/core/semantics.md` | no finding on the new bullet |

Two runs failed on the way, and each failure is now a control. The first `batteries-touched`
run stopped at the red control of `Test/Codegen/TermRows.lean`: the text of another level now
reads, renamed. That control now pins the refusal of the reader of the printer's names and the
reading after the renaming. `bun test` failed three tests of `read.test.ts` and one each of
`fold-syntax.test.ts` and `term-rows.test.ts`, for the same reason; each now pins the new
answer. The codegen reader is not lowered to OCaml, so `make gen-lcnf` and `make check-ocaml`
were not owed and did not run.

## Axiom output

`#axiom_audit Effect4.Codegen.Rename Effect4.Codegen.Read Effect4.Api.Codegen
Effect4.Laws.Codegen.Read Effect4.Laws.Codegen.ReadPrint Effect4.Laws.Codegen.PrintTyped
Effect4.Laws.Codegen.Mask Test.Codegen.ReadContract Test.Codegen.TermRows`:

```
#axiom_audit: 4616 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

## Open items

1. **Option B, the one-sided exactness (owner decision).** The brief's law 12 reads "a text that
   reads to `p` is `print p` after that renaming". It holds when every print is fixed by the
   renaming. That fails only for a term atom spelled like a layer clause's head with a list
   fold inside, below a binder. Option B: read every text after the renaming, and leave such
   atoms out of the readable domain (`leafReadable`, `Laws/Codegen/ReadPrint.lean`). Law 11
   keeps its text but its domain shrinks; law 12 becomes one-sided; `read_renamed` loses its
   second case. The cost is a printer-side law: every print of a program in the smaller domain
   has the printer's names, the template calculus' half of the work. Its first half, that a text
   in the printer's names renames to itself (`Rename.expr_of_minted`), was proved during this
   slice and is kept out of the tree, in
   `docs/research/2026-10-20-coherence-audit/item3b-option-b-normal-form.lean.txt`.
   Recommendation: keep the landed reader. At the native signature the corner is an ill-typed
   program, since no native atom is spelled like a layer clause (`nativeAtomTy`,
   `src/Effect4/Program/Native.lean`). `PrintLeaf.reserved` already says that a term's atom
   avoids the reserved heads, though the readable domain does not.
2. **The typed reader erases before it renames.** `readTyped` is `readEff` after
   `eraseJoinArgs`, and the erasure matches the printer's names. So a text with an author's
   binder names and the typed print's type arguments at a join is refused. The order rename,
   erase, read belongs to release item 4, which reads modules through the typed reader.
3. **One resolver in TypeScript.** In Lean the renaming uses `Authoring.Names.resolve`. In
   TypeScript the rule is `lastIndexOf` in three places: `read.ts`, `oxc.ts` and `ck.ts`. A
   shared helper would touch `ck.ts`, which the scope note leaves alone.
4. **Stale generated entries.** Semantics generation is paused (decisions row 418 (6)), so
   `generated/semantics.md` is stale at four places. Its claim table and claim sections lack
   `binder-names-read`, and they carry the old title of `typed-print-read`. Its dependency
   table has the old rows of `read_print`, `read_exact`, `readTyped_exact` and
   `mask_rows_table_premises`; their proofs now pass through `readMinted_print` and
   `readMinted_exact`. It lacks the new bullet of `docs/core/semantics.md` §2.5. No claim moved
   between concepts.
5. **Proposed decisions row.** "Release item 3b: the reader reads the printer's text as it
   stands and any other text after the renaming of its binders (`Rename.expr`); law 12 holds
   under that normaliser as a disjunction; option B is open."

## Evidence: finite or host-only

The laws are proved (the axiom output above). The controls are finite: the guards of
`Test/Codegen/ReadContract.lean` ("Binders by lexical scope") and `Test/Codegen/TermRows.lean`,
and the tests of `ts/eff/test/read.test.ts`, `fold-syntax.test.ts` and `term-rows.test.ts`. The
TypeScript reader's agreement with Lean's is finite: those tests and `make check-ts`. Nothing is
host-only.
