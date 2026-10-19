# 2026-10-19 seat 3a receipt: one public JSON spelling (release item 3, part a)

**The one thing to know before merging:** all four parts landed and `make check-ts` passes. A
program has one public JSON, the tagged print with lists as arrays, and `Canonical.print`, `toJson`
and the corpus oracles write it alike. Two facts sit outside the brief's files: the frozen face 7
contract still says `ts/eff/json.gen.ts` writes the `V` spelling (an amendment is proposed under
open items), and four exactness laws now name the cases print `ShapeDoc.print` where they named
`Canonical.print`.

## Base and head

Branch `refactor/phase1-phase3`, main checkout, no worktree. Base `82636b309`. Head of the code:
`8e182f43f`; the commit of this receipt follows it.

## Commits and their files

1. `e826c8ac1` ts/eff: `toJson` writes the tagged print (brief items 1 to 3).
   - `tools/Drivers/TsGen.lean`: `emitJson` writes one tagged writer per family. The positional
     `V` writer and its `consList` are no longer generated.
   - `ts/eff/json.gen.ts`: regenerated (`generate.py --only ts`). No other file of the group moved.
   - `tools/Drivers/Styles.lean`: `Tools.Styles.programJson`, an oracle's bytes: `NatJson.render`
     of `ShapeDoc.printTree`, then a newline. The import of `OCaml5.Eff.Goldens` goes.
   - `tools/Drivers/Corpus.lean`: each `.json` oracle through `programJson`; the import of
     `OCaml5.Eff.Goldens` goes. (`tools/Tools/Corpus.lean`, named in the brief, does not exist.)
   - `ts/eff/check.ts`, `ts/eff/check-styles.ts` (the oracle's shape), `ts/eff/README.md` (which
     JSON goes where; the stale `tools/Tools/Corpus.lean` commands now name
     `tools/Drivers/Corpus.lean`).
   - `ts/eff/test/read.test.ts`, `ts/eff/test/fixtures/todo-file.json`,
     `ts/eff/test/metadata.test.ts` (it compares with the node column, and keeps a control that
     the `V` column is another value), `ts/eff/test/check.test.ts` (new: the corpus check's
     green case and its red control).
   - `ts/eff/ingest/check-corpus.ts` (its positive control), `ts/eff/ingest/fixtures/witnesses/ledger.json`,
     `ts/eff/ingest/test/{printer,first-exit,inclusion,runtime}.test.ts`. `printer.test.ts` reads
     the five program goldens by their canonical bytes (`.bin`), not their `V` JSON.
   - `docs/research/2026-10-13-seat-read/TodoFileFixture.lean`: the fixture's producer writes
     the tagged print.
2. `a2cfa8de5` D2 in Lean: `Canonical.print` is the array print (brief item 4).
   - `src/Effect4/Store/Domain/ShapeJson.lean`: `Canonical.printArrays` is renamed
     `Canonical.print`.
   - `src/Effect4/Store/Domain/Canonical.lean`: the cases `Canonical.print` and its guard go.
   - `src/Effect4/Store/Domain/Shape.lean`, `ShapeRead.lean`: the documentation names
     `ShapeDoc.print` the cases print, the readers' normal form.
   - `src/Effect4/Laws/Store/ShapeRead.lean`, `src/Effect4/Laws/Tool/CodecProfile.lean`:
     `Canonical.ofJson_exact`, `Canonical.readLocated_exact`, `Canonical.ofJsonAnyOrder_exact`
     and `profileLocated_exact` state `(Canonical.shape α).print (Canonical.toVal a)`, which
     the deleted definition unfolded to. Their proofs are unchanged.
   - `src/Effect4/Tool/CodecProfile.lean`, `src/Effect4/Tool/Methods.lean`,
     `tools/Tools/JsonBridge.lean`, `Test/Program/JsonFormControls.lean`,
     `docs/core/api-surface.md`: the new name.
   - `tools/ProofGraph/Registry.lean`: the title of the claim `json-read-exact`.
   - `tools/Effect4Gen/manifest.json`: the groups Pin (also as a meta import), Refusals and
     Runner import `Effect4.Store.Domain.ShapeJson`, because their guards pin the public print.
   - `tools/Effect4Gen/guards/{pin,refusals,runner}.lean`: comments name `Canonical.print`.
   - `src/Effect4/Store/Domain/PinDerived.lean`, `src/Effect4/Api/RefusalsDerived.lean`,
     `src/Effect4/Api/RunnerDerived.lean`: regenerated (`generate.py --only derived`). No
     other derived file moved.
   - `Test/Store/StoreContract.lean`, `Test/Store/Templates.lean`: import ShapeJson.
3. `9b4f49811` tools: two driver lines reflowed under 100 columns; no output moves.
4. `8e182f43f` `Test/Program/JsonFormControls.lean`: `Canonical.print listed = listedAsTs`, and its
   control, the cases print of the same program, is another value.

## Commands and results

Every Lean command ran through `python3 /private/tmp/seams-lean-one.py`.

| Command | Result |
| --- | --- |
| `cd ts/eff && bun test` at the base | 790 pass, 0 fail, 29 files |
| `cd ts/eff && bun run typecheck` (tsgo 7.0.0-dev.20260629.1) at the base | exit 0 |
| `bun run check.ts <base corpus> harness/truth/generated --oracle <base corpus>` at the base | files 501: matched 416, mismatched 0, refused with oracle 0, accepted without oracle 74, refused without oracle 11 |
| `lake build Drivers.Corpus Drivers.TsGen Drivers.Styles` at the base | 773 jobs, built |
| `python3 scripts/generate.py --only ts` | `PASS generate`; only `ts/eff/json.gen.ts` moved |
| `lake build Drivers.Styles Drivers.Corpus` | built (the first try refused `(·.toUInt8)`; `Nat.toUInt8` fixed it) |
| `lake env lean --run tools/Drivers/Corpus.lean <scratch> 400 4` | kept 408 (readable 385) refused 0; `.ts`, `.eff`, `index.tsv` byte-identical to the base's |
| scratch check: each new `.json` through `decodeEff`, then the base's `V` writer, against the base `.json`; and `toJson` of the decoded node against the new bytes | 408 of 408 the same program; 408 of 408 the same bytes |
| the D2 probe: `D2.lean`, and `toJson(decodeEff(program.json))` | both 485 bytes, byte-identical |
| `check.ts` over the new corpus | files 501: matched 416, mismatched 0, and the rest as at the base |
| `check.ts`, new writer, over the base corpus (red control) | matched 0, mismatched 416 |
| `bun ts/eff/ingest/check-corpus.ts printed <new corpus>`; the same over the base corpus (red control) | `PASS printed: 408 exact JSON/wire comparisons on each parser`; `corpus batch 0 failed` |
| `check-corpus.ts inclusion` over the new corpus, and the base's file over the base corpus | one line both times: 408 modules, 298 lifted, 110 refused, one histogram |
| `Corpus.lean --styles <scratch> 400 4`, then `bun run check-styles.ts <scratch>` | 21831 files; `PASS styles construction` |
| `check-styles.ts` on one file whose oracle is in the `V` spelling (red control) | `missing or malformed oracle`, exit 1; its tagged twin passes |
| `lake env lean --run docs/research/2026-10-13-seat-read/TodoFileFixture.lean <scratch>` | `todo-file.txt`, `todo-envelope.txt` byte-identical; `todo-file.json` 5213 bytes, the base fixture's program by the decode check |
| `lake env lean --run tools/Conform/Cli/Audit.lean --config tools/Conform/Effect4/audit.json` | the `ts/eff/json.gen.ts` row passes (29 `Ty` cases, in order); exit 2 from 3 counterexamples and 3 unresolved rows of `ocaml/eff`, outside this slice |
| `lake build Effect4.Store.Domain.ShapeJson` after the item 4 edits | 35 jobs, built |
| `python3 scripts/generate.py --only derived` | `PASS generate` in 1 min 39 s; three derived files moved, as intended |
| `lake build Effect4` with the touched Laws, Tools and driver modules and their direct dependents | 1325 jobs, built, 2 min 36 s |
| `make batteries-touched BASE=82636b309` | 71 batteries, 1448 jobs, built, 2 min 8 s |
| `lake build Effect4.Laws` and the remaining direct-dependent batteries | 1857 jobs, built, 7 min 32 s |
| `make corpus` | kept 408; `generated/corpus-index.tsv` unchanged; `.lake/corpus` identical to the scratch run |
| `make check-ts` | six lanes pass in 35 s: tsgo; target (104 of 104, assignability 742 pairs); ts-reader (files 501: matched 416, mismatched 0; typecheck exit 0; 792 pass, 0 fail, 30 files); tsdiag; ingest-smoke (408 exact comparisons per parser); service-identity |
| `generate.py --only ts --output-dir <scratch>` and `--only derived --output-dir <scratch>` | `PASS generate` both: the committed files are what Lean emits at the head |
| `lake build Test.Program.JsonFormControls`; the red twin of each new line in a scratch file | built; both twins fail (`did not evaluate to true`) |

## Axiom output

`#axiom_audit` (`tools/ProofGraph/AxiomAudit.lean`) over `Effect4.Store.Domain.{Canonical, Shape,
ShapeRead, ShapeJson, PinDerived}`, `Effect4.Api.{RefusalsDerived, RunnerDerived}`,
`Effect4.Tool.{CodecProfile, Methods}`, `Effect4.Laws.Store.ShapeRead`,
`Effect4.Laws.Tool.CodecProfile`, `Test.Program.JsonFormControls`, `Test.Store.StoreContract`
and `Test.Store.Templates`, at the head: `3746 declarations within [propext, Quot.sound], 0 of
them modulo planned goals; 0 planned goals`. The tool modules (`Drivers.*`, `Tools.JsonBridge`,
`ProofGraph.Registry`) stand outside the axiom gate.

## What was deleted

| What | Where | Lines at base → head |
| --- | --- | --- |
| the positional `V` writer, its 31 functions and `consList`, replaced by 31 tagged writers of the same names | `ts/eff/json.gen.ts` | 303 → 301 |
| the `V` emitter | `tools/Drivers/TsGen.lean` (`emitJson`, `emitFamilyJson`, `jsonOf`) | 1366 → 1373, with documentation |
| the cases `Canonical.print` and its guard | `src/Effect4/Store/Domain/Canonical.lean` | 717 → 713 |
| the name `Canonical.printArrays` | `src/Effect4/Store/Domain/ShapeJson.lean` | 437 → 437 |
| the imports of `OCaml5.Eff.Goldens` | `tools/Drivers/Corpus.lean`, `tools/Drivers/Styles.lean` | 157 → 156; 201 → 210 |
| every `V` literal of the TypeScript tests, and their five reads of `ocaml/eff/goldens/*.json` | `ts/eff/test`, `ts/eff/ingest` | rewritten, not removed |

Over the four code commits: 39 files, 564 lines added and 428 deleted
(`git diff --shortstat 82636b309 8e182f43f`).

## Evidence

- **Tested** (finite runs): the corpus comparison (416 files: the 408 corpus programs, and 8
  truth modules read against the wire corpus oracles of their names); the decode check of every new oracle against its `V` predecessor; the styles corpus
  (21831 files); the ts/eff suite (792 tests); the red controls above.
- **Reproduced**: `ts/eff/json.gen.ts` and the three derived modules, by the generators' check
  mode.
- **Proved**: no new theorem. The four restated laws keep their proofs, under
  `[propext, Quot.sound]`.
- **Not established**: no theorem relates `toJson` to `ShapeDoc.printTree`. Their agreement is a
  finite byte comparison on the corpus. Every TypeScript result is host evidence under bun 1.4.2
  and tsgo 7.0.0-dev.20260629.1.

## Open items

1. **Face 7's contract** (`Test/contracts/faces.contract.md`) still lists `ts/eff/json.gen.ts` as
   a `V` implementation. Proposed amendment, for the owner's approval:
   - Face 7 is the tagged print, each list an array: `ShapeDoc.printTree` rendered by
     `NatJson.render`, and `Canonical.print` on the binary64 tree. `ts/eff/json.gen.ts` writes the
     same bytes (`toJson`). Tested: `ts/eff/check.ts` in `make check-ts`, with its red control in
     `ts/eff/test/check.test.ts`. Reproduced: `ts/eff/json.gen.ts` by `make check-gen`.
   - `V`'s spelling keeps one implementation, `OCaml5.Eff.effV.json`, which cuts
     `ocaml/eff/goldens/<name>.json`. It stays an internal fixture format until F1. No test reads
     those files now.
2. Three OCaml-estate comments still say that `ts/eff`'s tests read the `V` goldens:
   `src/OCaml5/Tools/EffGen.lean`'s header, the goldens row of `ocaml/eff/README.md`, and the
   header of `ocaml/eff/test/test_eff.ml`. The brief fences the OCaml `V` estate, so they are
   left for F1.
3. The cases print `ShapeDoc.print` stays. Its only users are the readers' exactness laws,
   which name it as their normal form, and a few guards. It goes with M7's reader deletions
   (`readIn`, `Agrees`, `Canonical.ofJson*`).
4. `generated/semantics.md` still shows the old title and statement of `json-read-exact`.
   Semantics generation is paused (row 418 (6)).
5. The D2 probe's `v.ts` now prints the tagged print, 485 bytes. Its 215-byte figure holds at
   the base only.
6. Found, and older than the base: `generated/tsdiag-agreement.tsv` names the reason `term` where
   the corpus index has said `refusedArguments` since before the base (column 2 only; no verdict
   reads the table). `ts/eff/test/fixtures/todo-file.table.json` differs from what its producer
   writes now, in record field order; the test passes with the committed file.
   `src/Effect4/Run/Kit.lean`'s header still names `Kit_json` as the kit's printer.

## Proposed decisions row (a proposal only)

Release item 3a landed (D2): `Canonical.print`, `ShapeDoc.printTree`, `ts/eff`'s `toJson` and
the corpus oracles write one public JSON, the tagged print with lists as arrays. TypeScript has
no `V` writer. The cases print stays only as the readers' normal form until M7.
