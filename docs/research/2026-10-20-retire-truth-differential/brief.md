# Brief: retire the truth differential

Status: brief, 2026-10-20, from the coordinator to one Opus seat. The owner, 2026-10-20:
"retire the old truth modules". On 2026-10-18 the owner retired the truth lanes from the gates
("just retire them... we'll design better checks"). Their code stayed in the tree, run by no
gate. This slice deletes that code and its recorded results. It keeps what a live gate, the
programs printed as Effect TypeScript syntax, or the codec lane still read. Read `AGENTS.md` in full first, then
`docs/GENERATED.md`'s truth rows and the Makefile's comments at `gen-truth`.

## 1. Where you work

- The checkout `/Users/pooks/Dev/lean4-effect4`, branch `refactor/phase1-phase3`, base
  `fa7bdc304`. No worktree: you edit and commit here. Nobody else runs Lean, make or dune in
  this checkout while you work.
- Your scratch folder is
  `/private/tmp/claude-501/-Users-pooks-Dev-lean4-effect4/2cfa2789-af6f-4183-90be-cdd7f2934e64/scratchpad/truth`.
- Every Lean command runs through the runner, one at a time, never with a thread count:
  `python3 /private/tmp/seams-lean-one.py lake …` and
  `python3 /private/tmp/seams-lean-one.py make <target>`. Never a bare `lake build`,
  `lake build Test`, `make build`, `make check-full`, `make gen-semantics`, `tsc`,
  `git add -A`, `git push`. Never `2>/dev/null` on a Lean command.
- Never edit `docs/core/decisions.md`, `AGENTS.md`, `lakefile.toml`, or the owner's `README.md`.
  If `make check-sweep` rewrites `docs/core/decisions.md`, leave that rewrite uncommitted and
  name it in the receipt.

## 2. The cut

First the inventory, then the cut. Classify every file under `harness/truth/`, every script
under `scripts/` that names it, and every Makefile target, by its consumers:

- **Kept, live.** The prelude: `prelude.ts`, `control.ts`, `records.ts`, `tuples.ts` and
  `prelude-atoms.gen.ts` (`PRELUDE_SOURCES`). The printed programs, the target and
  service-identity lanes, the to-do project and the faces probe import them. The host
  protocol, `session/` (`gen-host-protocol`), which tsdiag and service-identity read. The
  codec lane, `schema-codec/`, run by hand: the acceptance check of moves J and G. The
  `node_modules` link. The `*.typecheck.ts` files, if the tsdiag lane's wildcard reads them
  (check `harness/tsdiag/run-tsdiag.mjs`).
- **Kept, the corpus.** `Truth.lean`'s program corpus and its `--corpus` manifest writer, and
  what they produce. `corpus.json` is the manifest; `tools/target/profile.ts`,
  `tools/target/profile.test.ts` and `tools/Tools/RowTypes.lean` read it in the target lane.
  `generated/*.ts` are the printed modules; the ts-reader lane's `ts/eff/check.ts` and
  `profile.ts` read them. Trim `Truth.lean` to the corpus, the host inputs and the manifest
  writer.
  Delete its recorder: the expected-exit JSON writers, the tapes, the comparison. Read the
  manifest's readers first and keep every field they read; drop the rest.
- **Deleted, the differential.** Under `harness/truth/`: `run-truth.ts`, `result.json`,
  `result.md`, `corpus-results.tsv`, `corpus-known-differences.md`, `corpus-check/`,
  `tapes/`, `build-ledger.tsv`, `build-ledger.run.json`, `check-truth.ps1`, `LANE.md`,
  `RELEASE-LANE.md`, `select-controls.ts` and `P2b.lean`. Under `scripts/`:
  `check-truth.py`, `check-truth-release.py`, `check-corpus.py`, `lib/truth_ledger.py` and
  `lib/truth_host.py`. In the Makefile: `gen-truth-ledger`, `TRUTH_HOST_TESTS` and the
  `truth-check-*` cleanup line. Confirm each by its consumers before deleting; a file a kept
  consumer reads moves to the kept list, and you record why.
- **Decide by consumers.** `ts/eff/ingest/fidelity/roundtrip.ts` runs `run-truth.ts
  --observe` and `IngestPrint.lean`. Keep both only if a `check-ts` lane reaches
  `roundtrip.ts`; read `ts/eff/ingest/check-corpus.ts` and the `ingest-smoke` recipe.
  Otherwise delete both. The five `*.test.ts` of `TRUTH_HOST_TESTS` test the prelude under
  Bun. Keep them if a live lane runs them. Else delete them and record the five names.
- **The producer stays regenerable.** Rename `gen-truth` to what it now does: it builds
  `Truth.lean`'s imports and runs `Truth.lean --corpus` to write `corpus.json` and
  `generated/*.ts`, with no Bun run. Its header comment says what it writes and who reads it.
  Run it once and confirm the committed `corpus.json` and `generated/*.ts` do not change,
  byte for byte. If they change, stop and record the difference; do not commit a changed
  corpus without naming the cause.
- **The documents.** `docs/GENERATED.md`: the truth row now describes the corpus producer
  only, and the retirement paragraph says the differential is gone. `docs/ARCHITECTURE.md`'s
  `harness/truth` row. `docs/core/host-boundary.md` where it names `run-truth.ts`. Every
  docstring or comment in `src/`, `tools/`, `ts/` and `Test/` that names a deleted file (grep
  each deleted name). Where a sentence must keep pointing at a deleted file, cite its last
  Git citation, `git:fa7bdc304:<path>`. Then `make check-sweep`.

## 3. The landing

1. Delete and trim. Run the renamed target through the runner (read the old `gen-truth`
   recipe for the native flags). Then do the byte comparison of §2.
2. `make check-ts` once (its target and ts-reader lanes read the corpus; every lane reruns
   because the Makefile changed).
3. `make check-sweep`.
4. No Lean library module changes, so no axiom walk is owed. If you touch a module under
   `src/`, run `#axiom_audit` over it.

## 4. The commit and the receipt

- Commit by explicit paths, in two commits: the deletions and the trim; then the documents.
  First lines: `Truth: retire the differential; keep the corpus producer` and
  `Docs: the truth harness after the differential's retirement`. The last line of each:
  `Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>`.
- The receipt is `docs/research/2026-10-20-retire-truth-differential/receipt.md`
  (`git add -f`), in controlled English, checked with
  `python3 -I scripts/check-language.py --show`. First, the one thing to know. Then the base
  and head commits. Then the inventory as a table: file, class, consumer, kept or deleted.
  Then the commands and results, the open obligations, and the lines of the deleted files
  (`git diff --stat`). Name what you kept that the owner may still want gone.
