# Seat J2 brief: row 168 (the ingest's parser on the native API or oxc), `check-tsgo` into `check`, and seat J's owed items

Written 2026-10-01 by the coordinator. Base commit `bd5462df` (main after seats J and D1 and probe
S merged, the record committed). Worktree `/Users/pooks/Dev/lean4-effect4-seat-J2`, branch
`seat/J2`; `.lake` cloned from the main checkout, current at the base. Read
`docs/research/2026-10-01-landing/plan.md` (§4 rules, §5 measure), then in full: receipt J
(`docs/research/2026-10-01-landing/receipt-J.md`: step 3's "Owed, with the exact obstacle", step 5's
producer-chain commands, step 7, "What is owed"), decisions rows 168 (ruled) and 17 (the two open
items), `AGENTS.md`'s TypeScript bullet, `docs/GENERATED.md` (the `ts` and `readme` groups;
`TS_EFF_SOURCES` at `Makefile:53`), and `scripts/check-ingest.sh` (every command the ingest lane
runs; it installs with `--frozen-lockfile` and refuses lockfile drift twice). Seats D2 and D3 are
running in parallel on `src/Effect4/Laws/Program/Typed/**` and `Test/Program/{TypedDenotation,
H2PartOne,...}.lean`: you touch a file there only to add one `open scoped` line (step 3a) and
nowhere else. Probes P, Q and U write research files only. Nobody else touches `ts/eff`, the
`Makefile`, `tools/Effect4Gen/manifest.json` or the authoring syntax.

**The one thing.** The owner's rule is one TypeScript compiler, tsgo 7, and `typescript@5.x` never
run, in a gate, a probe or a review. The tree still pins `typescript@5.9.2` (`ts/eff/package.json:19`,
`ts/eff/bun.lock:112`) for six files that use it as a parser (`ts/eff/check-styles.ts`,
`ts/eff/ingest/ck.ts`, `ingest/census/decls-ck.ts`, `ingest/census/corpus.ts`,
`ingest/fidelity/source.ts`, `ingest/census/legs.ts`); seat J measured that TypeScript 7's API lacks
seven of the functions they call (receipt J, step 7 (ii)). Row 168 is ruled: (B) the native API where
the walk needs the oracle's own grammar, (C) `oxc-parser` where the ingest already parses with oxc
(`ts/eff/ingest/oxc.ts`, `pins.ts`, `read.ts`); never 5.9.2; `make check-tsgo` joins `check` with the
landing. After this seat no `node_modules/typescript` below 7 exists under `ts/`, `harness/` or
`tools/`, and `make check` says so.

## Step 1: row 168, the six files

Measure first (reuse `docs/research/2026-10-01-landing/seat-J/ts-api-measure.py`, reading only):
per file, which of the 56 calls it makes and what it does with the tree. Then, per file, by the
ruling:

- The five recognizer files (`ck.ts`, `decls-ck.ts`, `corpus.ts`, `source.ts`, `legs.ts`) walk
  syntax (declarations, modifiers, legs, source positions): route (C), the walk rewritten over the
  oxc tree through the helpers `ingest/oxc.ts` already has (add helpers there, never a second
  parser module). `corpus.ts`'s tsconfig read (`parseConfigFileTextToJson`) becomes a JSONC read of
  your choosing (say which; it must accept the corpus's tsconfigs as they are). The diagnostics
  text (`flattenDiagnosticMessageText`) becomes oxc's own.
- `check-styles.ts` compares TypeScript's parse diagnostics with oxc's (a differential about the
  oracle's grammar): route (B). Measure what the pinned preview ships before choosing the entry:
  `ts/eff/node_modules/@typescript/native-preview/lib` holds `tsgo.js`, `getExePath.js` and
  `version.cjs` only (read 2026-10-01); look at its `dist/` and `package.json` `exports` for an
  `unstable/sync` API. If the preview ships the JS API, use it (`API` client over a snapshot,
  `getSourceFile`, the file's syntactic diagnostics). If it does not, the differential's need is
  the oracle's verdict on a text, which the pinned binary gives as a process: run
  `node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --noEmit --pretty false` over the
  file (the launcher `check-target` runs at `Makefile:393`) and read its diagnostics; that keeps one
  compiler at one version and adds no package. Adding `typescript@7.0.2` to `ts/eff` is the last
  resort (it is tsgo 7, the version `harness/schema-host` pins, so it does not break the rule; but it
  is a second build of the compiler in one tree); if you take it, say why the other two could not do.
- Then delete `typescript: 5.9.2` from `ts/eff/package.json` and let `bun install` rewrite
  `ts/eff/bun.lock` (commit the lock; `check-ingest.sh` compares the lock's hash before and after
  its own `bun install --frozen-lockfile`, so the committed lock must be the one bun writes).
  `ts/eff/ingest/README.md` is generated (`bun ts/eff/ingest/render-readme.ts`, the `readme`
  group): if it names the parser, regenerate it in the chain of step 4, never by hand.

Controls, each run and named with its compiler: `(cd ts/eff && bun run typecheck && bun test)`
(`typecheck` is `tsgo --noEmit -p tsconfig.json`, 7.0.0-dev.20260629.1); `make check-ingest-smoke`
(the printed corpus through the recognizer); `make check-ingest` once at the end of this step (the
lane the change reaches: the foreign corpus, the gate, the metamorphic checks, the OCaml wire
check, fidelity; it is the nightly lane, run it once here because this is the change it exists
for). A refusal fixture that stops being refused, or a census number that moves, is a finding:
record the number before and after and why.

## Step 2: `make check-tsgo` into `check`

Receipt J step 7 (iii) has the one line (a phony `check-tsgo`: no `node_modules/typescript` below 7
under `ts/`, `harness/` or `tools/`). Land it as written, with no exemption, as a prerequisite of
`check` (`Makefile:274`), in `CHECKS` (`:269`) and the help text (`:490`, `:494`), and in `.PHONY`.
Its red control: on the base tree (before step 1) the line exits 1 naming
`ts/eff/node_modules/typescript/package.json: 5.9.2` (receipt J tested this; run it once yourself
and keep the log). After step 1, `make check-tsgo` passes and `make check` includes it.

## Step 3: seat J's owed items

a. **The authoring syntax becomes scoped (row 17's `BuildRefusal` codec, J's option (c)).**
   `syntax (name := daemonFork_) "daemon " term (" in " term)? : term`
   (`src/Effect4/Program/Authoring/Services.lean:151`, namespace `Effect4.Program.Authoring`) and
   `syntax (name := effDo) "eff " doSeq : term` (`Program/Authoring/Sugar.lean:115`, the same
   namespace) become `scoped syntax`, their `macro_rules` with them. Every site that writes `eff …`
   or `daemon …` gains one line, `open scoped Effect4.Program.Authoring`, placed right after the
   file's imports (or as the first line inside its first `namespace`), and nothing else in that file
   changes, so a branch in flight merges textually (a loose grep finds the word in 50 Lean files
   under `src/`, `Test/`, `tools/`; the compiler finds the real sites: make the syntax scoped, build
   the roots, add the line where a file breaks, list every file that gained it in the receipt).
   The leak's probe (`docs/research/2026-10-01-landing/seat-J/probes/DaemonKeywordLeak.lean`)
   becomes a positive control in a new battery `Test/Program/AuthoringScope.lean` at the
   `Test/All.lean` anchor after `Test.Program.AuthorContract` (`:97`): a module that imports
   `Effect4.Api.Author` and writes `{ daemon := … }` for `Supervision.ForkOptions` elaborates, and
   `#guard_msgs (error)` pins that `eff` is not a keyword there without the `open`. Then
   `BuildRefusal` joins the `Refusals` group as one manifest line
   (`tools/Effect4Gen/manifest.json:129`, the group before `Runner`), its codec guarded like the
   other seven (J's `Test/Api/…` guards: same pattern).
b. **`head` per sum (row 17, J's option (b)).** One generic `Canonical.head : α → String` beside
   `Canonical` (`src/Effect4/Store/Domain/Canonical.lean:33`), read off the shape document's
   constructor name at `toVal`'s constructor index; a `#guard` that it agrees with
   `TypeReason.head` (`Program/Typing/Blame.lean:71`) on every constructor, and with
   `ShapeDoc.print`'s spelling for the twenty sums J counted (receipt J, step 3). Report, do not
   fix, J's measured concern that a shape document names a type by its last name
   (`HostSession.Refusal` and `Authoring.Refusal` both `"Refusal"`): one sentence in the receipt
   and a proposed line for row 8.
c. **`Env.mint`'s docstring** (`src/Effect4/Program/Authoring.lean:129-134`): J's one sentence,
   "the level of the construct that binds it; two binders of one construct differ by stem", in
   place of "the level it will be bound at". No build is owed for a docstring.
d. **`Makefile:455`**: the order-only prerequisite `| harness/truth/node_modules` on
   `$(CHK)/host-protocol`; then `make check-host-protocol` from a tree without the link (your
   worktree has none) passes in one run (it runs tsgo; name the version).

## Step 4: the producer chain

A manifest line changed (step 3a), so the generators run in the fixed order with
`LEAN_NUM_THREADS=1`: derived → lcnf → eff → wire → cas (ts, readme), the exact commands receipt J's
step 5 ran (`python3 scripts/generate.py --only <group>` per group, in that order); every output
committed, never hand-edited; `make check-gen` once after. If step 1 changed `ts/eff/package.json`
or the lock, the `ts` and `readme` markers rebuild (`TS_EFF_SOURCES`): the outputs must be
byte-identical or committed with the reason.

## Builds and the testing rule

The ratified rule (data-wave README, "Testing during the wave"): narrow builds while landing
(`lake build Effect4.Program.Authoring.Sugar Effect4.Program.Authoring.Services` and their direct
dependents; `lake env lean <file>` for a battery), the roots once before the receipt
(`LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All`), `make check-gen` once after step 4,
`make check` once at the end (it now carries `check-tsgo`). No `check-full`. One lake at a time
in this worktree. Every TypeScript result names its compiler and version; `tsc` and
`typescript@5.x` are never run, not even to measure.

## Rules

Plan §4 (brief-G's "Rules" list applies verbatim). Commits by explicit paths on `seat/J2`, one per
step (step 3's four items may be one commit each or one for a–b and one for c–d); research files
force-added; no push; never `git merge`/`checkout`/`reset`; a refused permission is recorded,
not worked around. `README.md`, `AGENTS.md`, `docs/core/decisions.md`, `docs/STATE.md`,
`docs/core/system-map.md`, `Test/Counterexamples/REGISTER.md` and `lakefile.toml` are never
edited: propose their lines in the receipt. Evidence words on every claim (proved, tested,
reading, assumed).

## Receipt

`docs/research/2026-10-01-landing/receipt-J2.md` (force-added, committed last): the one thing
first; base and head; every changed path; per step what was measured before, what moved, the
controls that flipped, the exact commands and exit codes with the compiler named; the files that
gained `open scoped`; the lock's hash before and after; the ingest census numbers before and
after; what is owed with the exact obstacle; the proposed lines for rows 17, 168 and 8, for
`AGENTS.md`'s TypeScript bullet (the ingest sentence retired), for `docs/GENERATED.md` if a group's
inputs changed, and for the register if a counterexample was seeded or repaired (the keyword
leak is a candidate `E4-AUTHOR-CE-002`: seeded by J's probe, repaired by 3a).
