# Seat J receipt: rows 16, 17 and 24, seat G's owed items, one TypeScript compiler

Written incrementally by seat J on 2026-10-01 in `/Users/pooks/Dev/lean4-effect4-seat-J`, branch
`seat/J`. Brief: `docs/research/2026-10-01-landing/brief-J.md` (with its amendments, step 7).
Evidence (probes, logs, small scripts) under `docs/research/2026-10-01-landing/seat-J/`. Each
section states its status at the time it was written; the receipt is complete at the commit that
adds it.

## The one thing

All seven steps are on `seat/J` and the tree is green at the head (`lake build Effect4.Laws Test.All`:
743 jobs, both gates; `make check-gen`, `make check-ocaml` and `make check-host-protocol` pass; every
generated file is committed by its producer, in the fixed order), but two of the brief's premises did
not hold. **(1) Row 16 changes four statements of the proof graph**: `awaits_parked`, `awaits_live`,
`requestOf_of_mem_awaits` and `freshCall_facts` name the record's fields where they named the tuple's
projections (the same propositions otherwise), and it changes the LCNF engine cut
(`ocaml/engine/api_engine.ml` and `ocaml/gen/api_gen.ml` gain `and await = { fiber; token; op;
request }`). **(2) Step 7 landed its first lane only**: TypeScript 7's API lacks seven functions the
ingest's parser calls, so `typescript@5.9.2` stays and the `check-tsgo` guard is written but not in
`check` (it is red on this tree): an owner choice, options under step 7. Row 17 is partial:
`BuildRefusal`'s codec and `head` are owed, because importing `Effect4.Api.Author` turns `daemon` and
`eff` into keywords in every importer (a defect of its own, reproduced). Merge notes: no root import
or `Test/All.lean` line was needed (the new module is reached through `RunnerDerived`); the
`Makefile` gains one `DERIVED_OUT` path and one `DERIVED_TRACES` trace.

## Base and head

- Base: `6b3f2c92` (main after pass I2's merge and record). Tested at the start:
  `LEAN_NUM_THREADS=2 lake build --no-build Effect4.Laws Test.All` reports "All targets up-to-date
  (742 jobs)" with both gates printed at `Test/All.lean:169` (exit 0, 0.9 s).
- Head: the commit that adds this receipt, on top of `03e99961`. The commits, in order: `d22f71bd`
  (step 1), `2f95739c` (step 2), `9e466686` (step 3), `ffc8bb93` (step 4), `d8e9b596` (step 5),
  `03e99961` (step 7; step 6 changed no file), then this receipt. Nothing pushed; no merge, checkout or
  reset was run; no permission was refused.

## Step 1: seat G's items (no generator)

Status: landed (commit named under "Base and head").

### Measured before the edit

- `SingleGuard.held_fireStep` (`src/Effect4/Laws/Program/Guard/Single.lean:215`) and
  `OuterDriver.fireStep_preserved` (`src/Effect4/Laws/Program/Guard/OuterDriver.lean:81`) are read
  by nothing (tested: `git grep -n -w` over `src Test tools ts ocaml harness scripts Makefile`
  names only each declaration's own line). The helpers they read each keep another reader after
  the deletion (tested, same grep): `quiet_taskCmds` (`Single.lean:323`), `held_driveState`
  (`:440`, `:455`), `held_emit` (`:320`), `taskCmds_guardQueue` (`OuterDriver.lean:197`, `:240`),
  `taskCmds_registration` (`:241`, `:263`, `:321`), `Preserved.drive` (`:216`, `:319`),
  `Preserved.emit` (`:232`, `:235`). No new dead lemma follows.
- The census's mangled rows (tested, `seat-J/logs/census-all-before.log`, the five censuses
  `Test/Audit/TraversalCensus.lean` prints, run on a scratch copy at the base): exactly two
  `_private` occurrences in all five reports, both in the `Representation` census:
  `fold Effect4.Codegen.Schema:302 Effect4.Codegen.Schema.representation (Representation)
  _private.Effect4.Codegen.Schema.0.Effect4.Codegen.Schema.printAlgebra` and the same for
  `Effect4.Codegen.Schema.check (Check)` at `:305`. The algebra's name becomes text in
  `describeAlgebra` (`src/Effect4/Laws/Auto/Traversals.lean:109-124`, called by `algebrasIn`);
  at the `.fold` arm (`:318`) the names are already strings. A narrow scope does not show the
  rows: `#traversal_census Effect4.Representation under Effect4.Codegen.Schema` prints them
  `opaque` (tested, `seat-J/logs/census-schema-before.log`), because the census only counts the
  folds declared under its scope and `cata_representation` lives in `Effect4.Schema.Fold`.
- The `Machine/Fibers.lean` citations in `src/Effect4/Laws/Machine/Lift.lean` (reading at the
  base, then tested): all were written in `75ee115c` (`git log -S`), and every cited range's text
  is byte-identical to a range 27 lines lower at the base (tested: `seat-J/check-lift-citations.sh`
  diffs the twelve old ranges at `75ee115c` against the new ranges at the base, 12 of 12 the
  same). Receipt G's item 5 lists nine of them; three more are stale and are corrected with them:
  `Framed` (`Lift.lean:141`, Frame section, `:1798-1799` → `:1825-1826`), the `answer` field of
  `DecisionLift` (`:348`, Decision section, `prepareAsyncAnswer`'s halted line `:2076` → `:2103`)
  and `AdmittedReplay` (`:711`, Replay section, `replayEval` `:2161-2174` → `:2188-2200`). Where
  receipt G proposed a different span (`prepareAnswer` as the whole of `prepareAsyncAnswer`,
  `:2100-2107`; the interrupt record as `:2125-2134`; the fire fold as `:2026-2043`), this seat
  keeps the span the author cited, moved by 27 (the `answerAsync` arm's two lines `:2123-2124`;
  `:2125-2133`; `fireState` `:2036-2043`). The two other files `Lift.lean` cites,
  `AnswerDecision.lean:94-112` and `RuntimeR.lean:51-54`, are current (tested, same diff).

### What moved

- **Deleted** (statements and proofs, no reader): `Effect4.Program.Guard.SingleGuard.held_fireStep`
  (`Guard/Single.lean:215-224` at the base) and `Effect4.Program.Guard.OuterDriver.fireStep_preserved`
  (`Guard/OuterDriver.lean:81-94`). Both were `[propext, Quot.sound]` (seat G's
  `logs/statements-final.log`); nothing else changed in either file.
- **The census prints a fold's algebra by its written name** (`src/Effect4/Laws/Auto/Traversals.lean`):
  `writtenName` moves above `describeAlgebra` (same text, same namespace), and `describeAlgebra`,
  the one place an algebra's name becomes text, prints `writtenName n` for a named algebra and
  `writtenName n`/`writtenName m` for a builder and its argument. The `.fold` arm at `:318`
  is unchanged: its `algebras` are already strings there. `env.find? n` still reads the
  declared (mangled) name.
- **Pinned** (`Test/Audit/TraversalCensus.lean`): two `#guard_msgs (whitespace := lax,
  substring := true)` over `#traversal_census Effect4.Representation`, one per row, each
  expecting `<row> (<domain>) Effect4.Codegen.Schema.printAlgebra`. No line number and no tab is
  part of the pin, so an edit above `Codegen/Schema.lean:302` does not move it; the mangled form
  does not contain the expected text (`(Representation) _private.…` against
  `(Representation) Effect4.…`). The module docstring says what is pinned and why.
- **Citations** (`src/Effect4/Laws/Machine/Lift.lean`, docstrings only): the twelve stale
  `Machine/Fibers.lean` ranges above, each moved by 27 lines to the same text.

### The control that flipped

- Red (tested): with the pins added and the instrument at the base (the `Traversals` olean not
  yet rebuilt), `lake env lean -DwarningAsError=true Test/Audit/TraversalCensus.lean` exits 1
  with exactly the two new pins failing (`:74`, `:80`, "Docstring on `#guard_msgs` does not
  match generated message"; `seat-J/logs/census-pin-red.log`).
- Green (tested): after the fix, the narrow build below compiles `Test.Audit.TraversalCensus`
  with both pins passing, and the build log holds no `_private` (it held two at the base): the
  two rows print `… (Representation) Effect4.Codegen.Schema.printAlgebra` and
  `… (Check) Effect4.Codegen.Schema.printAlgebra` (`seat-J/logs/step1-build.log:1941-1942`).

### Commands and results

- `LEAN_NUM_THREADS=2 lake build Effect4.Laws.Machine.Lift Effect4.Laws.Auto.Traversals
  Effect4.Laws.Auto.Exhaustive Effect4.Laws.Program.Guard.Single Effect4.Laws.Program.Guard.OuterDriver
  Effect4.Laws.Program.Guard.Decision Effect4.Laws.Program.Guard Test.Program.GuardFoldLift
  Test.Audit.TraversalCensus`: exit 0, "Build completed successfully (558 jobs)", 0 errors, 0
  warnings, 3 min 59 s wall (`seat-J/logs/step1-build.log`). The targets are the touched modules
  and their direct importers (`git grep -l '^import <module>$'`: `Single` ← `Guard`,
  `Test.Program.GuardFoldLift`; `OuterDriver` ← `Guard.Decision`; `Traversals` ← `Exhaustive`,
  `Test.Audit.TraversalCensus` and the root `Effect4.Laws`, an import list built with step 2's full
  build; `Lift`'s importers need no build for a docstring edit, and step 2's full build rebuilt them).
- `bash docs/research/2026-10-01-landing/seat-J/check-lift-citations.sh`: same=14, differ=0
  (`seat-J/logs/lift-citations.log`).
- No theorem was added or restated in this step; the two deleted ones have no axioms to print.

## Step 2: row 24, the minted spellings

Status: landed (commit named under "Base and head").

### Measured before the edit

- The constant spellings (reading, then tested): `Sugar.bindWith` bound `"_" ++ level`,
  `Sugar.andThen` bound `"_"`, `Loops.iterateWith` bound `"_c<level>"` and `"_a<level>"`, and the
  generated forms bound `"_answer0"` (`andThenEffect`, `andThenThunk`, `asVoid`, `tapEffect`),
  `"_answer1"` (`tapContinuation`, `tapEffect`), `"_exit0"` (`ensuring`) and `"_exit1"`
  (`releaseOne`), seven forms in all; `tapEffect` also read its own `"_answer0"` through `var`.
  Every one is a spelling an author can write: `seat-J/probes/OldMintedSpellings.lean` copies the
  four base definitions verbatim and shows each capture an author's own name (`.var 1` where the
  author meant `.var 0`; exit 0, `seat-J/logs/old-minted-spellings.log`).
- A raw `fun env p =>` body (the shape of `tapMinted`, `Test/Program/AuthorContract.lean:331-345`)
  cannot be the generated form: the `FormsLaws` group proves each form's scope lemma by
  `unfold f; authoring_scoped`, and the tactic applies the lemma named after the head of the goal
  (`Laws/Program/Authoring/Tactic.lean:41-45`), which fails on a lambda ("no lift at the head").
  So the mint is a named combinator with its own `_scoped` lemma, which the tactic finds.
- Who reads the changed definitions (`git grep -w` at the base): `bindWith` (`map`, `repeatWhile`,
  two batteries: `AuthoringContract`, `LoopSugarContract`), `andThen` (the `eff` macro,
  `repeatWhile`, three batteries: `TestClockContract`, `AuthoringContract`, `LoopSugarContract`),
  `iterateWith` (`forRange`, `foldRange`, `repeatWhile`, `LoopSugarContract`); the forms only by
  `AuthorContract` and `AuthoringContract`. No battery pins an old spelling except the red control (`git grep` for
  the constants over `src Test tools ts harness`). The elaborated `Eff` names no binder (levels
  only), so no elaborated tree and no printed byte can move: tested below by the full build and
  by `make gen-derived` leaving every other derived output byte-identical.

### What moved

- `src/Effect4/Program/Authoring/Sugar.lean`: `minting stem k` (new; `k (env.mint stem) env p`),
  the one way the surface names a binder of its own; `bindWith` is `minting "answer" fun x =>
  bind x first (rest (minted x))`; `andThen` is `minting "answer" fun x => bind x first rest`.
- `src/Effect4/Program/Authoring/Loops.lean`: `iterateWith` mints `"cursor"` and `"answer"` and
  reads both through `minted`.
- `src/Effect4/Laws/Program/Authoring/Sugar.lean`: `minting_scoped` (new, proved, `[propext]`);
  `bindWith_scoped` and `andThen_scoped` restated over it, statements unchanged.
  `src/Effect4/Laws/Program/Authoring/Loops.lean`: `iterateWith_scoped` restated over it,
  statement unchanged. These two Laws files are not in the brief's list; they are the scope
  lemmas of the three definitions and their old proofs read `var_scoped` of the old spellings,
  so they move with them (statements byte-identical).
- `tools/Effect4Gen/Forms.lean`: an internal binder (one no argument sees) is
  `Authoring.minting "<role>" fun minted<Role><d> => <construct>` and a template reference to it
  reads `Authoring.minted minted<Role><d>`; parameters are unchanged. The example-argument
  helper's branch for a `"_"`-spelled binder is gone: an argument sees only binders below
  `named`, all parameters, so an example never names an internal binder (the branch was
  unreachable before and after; the generated guards are byte-identical).
- `tools/Effect4Gen/manifest.json`: the `Forms` group imports `Effect4.Program.Authoring.Sugar`
  (for `minting`), the `FormsLaws` group `Effect4.Laws.Program.Authoring.Sugar` (for
  `minting_scoped`); no cycle: neither Sugar module imports a forms module (their import lines,
  reading; the build, tested).
- Generated, by `make gen-derived` (below): `src/Effect4/Codegen/Authoring/Forms.lean` (the seven
  bodies minted, one import line, the header's command line) and
  `src/Effect4/Laws/Program/Authoring/Forms.lean` (one import line and the header's command
  line; the 19 lemma texts byte-identical). So the outputs differ from the base in the minted
  binders and in the import each group needs for the minting, nothing else
  (`seat-J/logs/forms-scratch.diff`, `forms-laws-scratch.diff`).
- `Test/Program/AuthorContract.lean`: the red control flipped and kept, plus three new controls
  (below); `import Effect4.Program.Authoring.Loops`; the module docstring says B-9 is closed for
  every binder the surface names.

### The controls that flipped

All four as pairs in `Test/Program/AuthorContract.lean`: the old expectation under
`#guard_msgs (error)` (its message pinned), then the new one as a plain `#guard`.
- `Forms.tapContinuation "_answer1" …`: was `.var 1` (the continuation's answer), now `.var 0`
  (the author's own); `tapMinted` (the hand expansion) and the generated form agree on
  `"_answer1"` and on `"r"`.
- `bind "_" … (andThen … (succeed (var "_")))`: was `.var 1`, now `.var 0`.
- `bind "_1" … (bindWith … fun _ => succeed (var "_1"))`: was `.var 1`, now `.var 0`.
- `outerCursor` (`bind "_c1"` around an `iterateWith` whose test reads `var "_c1"`): the test
  was `.var 1` (the loop's cursor), now `.var 0`.
Red side tested at the base definitions (`OldMintedSpellings.lean`, all four `#guard`s hold);
green side tested by the battery (`lake env lean -DwarningAsError=true
Test/Program/AuthorContract.lean`, exit 0; `seat-J/logs/step2-authorcontract.log`) and the build.

### Commands and results

- Narrow build of the hand definitions first: `LEAN_NUM_THREADS=2 lake build
  Effect4.Program.Authoring.Sugar Effect4.Program.Authoring.Loops
  Effect4.Laws.Program.Authoring.Sugar Effect4.Laws.Program.Authoring.Loops`: exit 0, 223 jobs.
- The generator on scratch paths before the cut (tested): `LEAN_NUM_THREADS=1 lake env lean
  -DwarningAsError=true -M4096 --run tools/Effect4Gen/Forms.lean --group Forms|FormsLaws
  --imports … --out <scratch>`; the scratch `Forms` module compiled with its 19 drift guards
  (exit 0, `seat-J/logs/forms-scratch-compile.log`), and the 19 generated scope lemmas closed by
  `unfold f; authoring_scoped` against the minted forms in one module
  (`seat-J/probes/FormsMintedProbe.lean`, exit 0, `seat-J/logs/forms-minted-probe.log`).
- `LEAN_NUM_THREADS=2 lake build` (the default targets, so that `make gen-derived`'s own `lake
  build` prerequisite finds nothing to do at one thread): exit 0, 746 jobs, both gates, 3 min 24 s
  (`seat-J/logs/step2-prebuild.summary.log`).
- **`LEAN_NUM_THREADS=1 make gen-derived`: exit 0.** It ran `lake build` (746 jobs, nothing
  rebuilt), `python3 scripts/generate.py --only variances` (the marker was older than the
  worktree's sources; `variances.json` byte-identical) and `python3 scripts/generate.py --only
  derived` (every group of the manifest). Changed: exactly the two forms outputs, each
  byte-identical to the scratch run tested above (`cmp`); every other `DERIVED_OUT` file and
  `variances.json` unchanged (`git status`). `seat-J/logs/step2-gen-derived.summary.log`.
- `LEAN_NUM_THREADS=2 lake build` after the cut and the battery edit: exit 0, 746 jobs, both
  gates ("checked 524 modules and 72072 declarations", `[propext, Quot.sound]`), 1 min 46 s
  (`seat-J/logs/step2-build.summary.log`).
- Axioms (`seat-J/probes/Step2Axioms.lean`, exit 0, `seat-J/logs/step2-axioms.log`):
  `minting_scoped` `[propext]`; `bindWith_scoped`, `andThen_scoped`, `iterateWith_scoped`,
  `map_scoped`, `forRange_scoped`, `foldRange_scoped`, `repeatWhile_scoped` `[propext,
  Quot.sound]`; the 19 regenerated form lemmas `[propext, Quot.sound]` or `[propext]`.

## Step 3: row 17, codecs for the reading types

Status: the two reading types and the Refusals group landed; the build refusal and `head` are
owed (below, with the measured obstacles). Commit named under "Base and head".

### Which eight

The brief says "the three above and the five others `git grep -n 'Refusal' src/Effect4/Api
src/Effect4/Program` names"; that grep names seven others (`BuildRefusal`,
`StraightAdmitRefusal`, `Admit.Refusal`, `Authoring.Refusal`, `Config.Refusal`, `LawfulRefusal`,
`TypeRefusal`), not five. The row's own source names the eight (decisions row 17, sources C-D5 →
`docs/research/2026-09-17-mcp-surface-scout-C.md` §3.3, "every refusal an agent can be shown"):
`Authoring.Reason`, `Authoring.Refusal`, `TypeReason`, `TypeRefusal`, `AuthorRefusal`,
`BuildRefusal`, `PrintRefusal`, `ReadRefusal`. This seat took the row's list. The three the
Runner group carried (`TableRefusal`, `AdmitRefusal`, `HostSession.Refusal`) already had codecs.

### Measured, and what it forced

- **Placement and reachability (reading, then tested).** A new group's output must be reachable
  from the `Effect4` root (the library-root gate), and the root's imports are edited only at an
  anchor a brief names (none for `src/Effect4.lean` here). So the `Refusals` group sits before
  `Runner` and the `Runner` group imports its output; `Api/RunnerDerived.lean` is reached from the
  root through `Api/RunnerBytes.lean`. No cycle: none of the modules the group reads reaches
  `RunnerDerived` or `RunnerBytes` (an import walk over `src`, `Test`, `tools`, `harness`).
  `AdmitRefusal` and `TableRefusal` move from `Runner` to `Refusals` (the build refusal held the
  admission refusal, and a type's instance must precede its holder); their bytes are unchanged
  (the encoding is type-directed), and nothing outside the generated file names their sections
  (`git grep 'RunnerGen\.|TableRefusalC|AdmitRefusalC'`, no hit).
- **A name collision in the generator (tested).** The first cut put `HostSession.Refusal` in the
  group too and failed to build: the generator names a type's section after its last name, so
  `HostSession.Refusal` and `Authoring.Refusal` both became `RefusalC` ("has already been
  declared", `seat-J/logs/step3-gen-derived.summary.log`). `HostSession.Refusal` stays in
  `Runner`.
- **The authoring syntax leaks through an import (tested).** The second cut imported
  `Effect4.Api.Author` (where `BuildRefusal` is declared); it built, but the full build failed in
  `Test/Run/RunContract.lean:88` ("unexpected token ':='; expected term"): `Api.Author` imports
  `Program/Authoring/Services.lean`, whose `syntax "daemon " term …` (`:151`) makes `daemon` a
  keyword wherever it is imported, so `{ daemon := false, … }` (`Supervision.ForkOptions`) stops
  parsing in every module that imports `RunnerDerived`. Reproduced at the import alone:
  `seat-J/probes/DaemonKeywordLeak.lean` (exit 1, the same error, `logs/daemon-keyword-leak.log`).
  So `BuildRefusal` is not in the group (owed, below), and the group imports `Effect4.Api`
  instead (it reaches `Authoring`, `Typing.Blame`, `Codegen.Read`, `Codegen.PrintLeaf`, and adds
  nothing to `RunnerDerived`'s import closure that `Effect4.Api.Runner` did not already reach,
  except `Effect4.Run`).

### What moved

- `tools/Effect4Gen/manifest.json`: a `Refusals` group before `Runner` (Out
  `src/Effect4/Api/RefusalsDerived.lean`, guards `tools/Effect4Gen/guards/refusals.lean`), types
  `TableRefusal`, `AdmitRefusal`, `Authoring.Reason`, `Authoring.Refusal`, `TypeReason`,
  `TypeRefusal`, `AuthorRefusal`, `PrintRefusal`, `ReadRefusal`; the `Runner` group imports
  `Effect4.Api.RefusalsDerived` and `Effect4.Run`, drops the two moved types and appends
  `Effect4.Api.FiberStatus` and `Effect4.Run.Observation` (after every carrier they hold).
- `tools/Effect4Gen/guards/refusals.lean` (new): every constructor of the nine types read back
  exactly, a byte added or removed refused, every value fitting its shape, distinct values
  distinct as bytes, an authoring refusal not read as a read refusal.
  `tools/Effect4Gen/guards/runner.lean`: the six `FiberStatus` alternatives and an `Observation`
  with every field filled read back exactly, refused with a byte added, fitting the shape.
- `Makefile`: `DERIVED_OUT` lists `src/Effect4/Api/RefusalsDerived.lean` (so `check-gen` holds it,
  GENERATED.md's rule), and `DERIVED_TRACES` adds `Run.trace` (the `Runner` group now reads
  `Effect4.Run`, which no listed trace covers; what the `Refusals` group reads, `Effect4.Api` and
  `Effect4.Api.HostSession`, is reached from `Effect4.Api.Runner`, whose trace is listed).
- Generated: `src/Effect4/Api/RefusalsDerived.lean` (new, 9 types) and
  `src/Effect4/Api/RunnerDerived.lean` (two sections out, two in, two imports).
- `src/Effect4/Run.lean`, `src/Effect4/Api/Supervision.lean`: unchanged. The generator needs no
  `deriving` line on either type (both are first-order with every carrier's instance in scope).

### Commands and results

- The `Refusals` group on a scratch path before the second and third cuts (tested): `LEAN_NUM_THREADS=1 lake env lean
  -DwarningAsError=true -M 4096 --run tools/Effect4Gen/Main.lean --group Refusals --imports … --out
  <scratch> --append tools/Effect4Gen/guards/refusals.lean <types> --header-out
  src/Effect4/Api/RefusalsDerived.lean`, then `lake env lean -DwarningAsError=true <scratch>`: exit 0
  both times; the final group's 45 receipts all `[propext, Quot.sound]` or `[propext]`.
- `LEAN_NUM_THREADS=1 make gen-derived`, first cut (with `HostSession.Refusal` in the group): exit 2
  (make), the `RefusalC` collision (`seat-J/logs/step3-gen-derived.summary.log`). Second cut (with
  `Api.Author` imported): exit 0 (`step3-gen-derived-2.summary.log`); the full build after it
  failed in `Test/Run/RunContract.lean:88` (the keyword leak above).
- After the fix: `LEAN_NUM_THREADS=1 python3 scripts/generate.py --only derived` (the producer
  behind `make gen-derived`, run directly because `make gen-derived`'s own `lake build`
  prerequisite could not pass while the tracked `RunnerDerived.lean` imported the leaking module):
  exit 0, "PASS generate" (`step3-generate-derived-3.summary.log`); `RefusalsDerived.lean`
  byte-identical to the scratch run (`cmp`). Then `LEAN_NUM_THREADS=2 lake build`: exit 0, 747 jobs,
  both gates ("135 API/utility modules … every library source is reachable"; "checked 525 modules
  and 72490 declarations", `[propext, Quot.sound]`) (`step3-build.summary.log`). Then
  **`LEAN_NUM_THREADS=1 make gen-derived`: exit 0, no file changed** (a fixpoint;
  `step3-gen-derived-final.summary.log`).
- **`LEAN_NUM_THREADS=1 make check-gen`: exit 0, "PASS check-gen: every Lean-only generated file is
  what its generator emits"**, with step 3's files staged (`git diff` compares the tree with the
  index). It re-cut `eff`, `wire`, `cas`, `ts` and `readme` (their markers predate the worktree), ran
  `bun install --frozen-lockfile` in `ts/eff` (bun 1.4.2, six packages, the pinned lockfile; nothing
  TypeScript was run by it), and found every output byte-identical
  (`step3-check-gen.summary.log`).
- The generator tools were current before the check (`LEAN_NUM_THREADS=2 lake build
  OCaml5.Tools.EffGen OCaml5.Tools.EffWire OCaml5.Tools.CasGoldens Drivers.TsGen Drivers.Corpus`:
  138 jobs, nothing built).

### Owed, with the exact obstacle

1. **`BuildRefusal`'s codec.** Declared in `Effect4.Api.Author`, whose import makes `daemon` (and
   `eff`) keywords in the importer (`DaemonKeywordLeak.lean`). Its instance cannot sit in a group the
   `Runner` group imports. Options: (a) a group of its own whose output the root imports, at an
   anchor the coordinator names in `src/Effect4.lean` (one line), the manifest entry and one
   `DERIVED_OUT` line being this seat's kind of change; (b) move `BuildRefusal` out of `Api/Author.lean`
   into a module without the authoring syntax, after which it joins the `Refusals` group as a manifest
   line; (c) make the authoring syntax scoped (`scoped syntax … ` in `Program/Authoring/Services.lean`
   and `Sugar.lean`, opened where the surface is used), which removes the leak for every importer, not
   only for this codec. Recommended: (c), then the manifest line: a keyword that a library import
   turns on breaks structure instances of `ForkOptions` far from the surface (the leak is a defect of
   its own, measured here), and (c) is the only option that fixes it rather than routing around it.
   Not done: `Services.lean` and `Sugar.lean`'s `eff` macro are not this seat's to rescope, and (a)
   needs a root anchor.
2. **`head : T → String` per sum.** The row and its source (scout C, D12: "emit one `head : T →
   String` per sum from the generator (the pattern `TypeReason.head` sets)") ask for generator output;
   the generator (`tools/Effect4Gen/Main.lean`) and the driver (`tools/Effect4Gen/Driver.lean`, which
   passes a group's manifest fields) are not in this seat's files, and no existing manifest field
   requests it. Measured (the `⟨.sum "…"` shape documents of the two generated files): the sums with a
   codec in the two groups touched here are 20 (Runner, 13: `Err`, `Defect`, `Reason`, `Exit`,
   `Completion`, `RunDecision`, `HostSession.Refusal`, `Phase`, `Command`, `State`, `Stuck`,
   `Outcome`, `FiberStatus`; Refusals, 7: `TableRefusal`, `AdmitRefusal`, `Authoring.Reason`,
   `TypeReason` (which has a hand `head` today, `Program/Typing/Blame.lean:71`), `AuthorRefusal`,
   `PrintRefusal`, `ReadRefusal`). Options: (a) `Main.lean` emits `def head : T →
   String` after each sum's instance, for every group (every derived output gains the functions) or
   behind a manifest field (`Driver.lean` passes it); (b) one generic `Canonical.head : α → String`
   read off the shape document's constructor names at `toVal`'s constructor index (one definition
   beside `Canonical`, no per-type text, the spelling owned once by the shape that is already the
   wire's). Recommended (b): one definition instead of twenty, and the name it prints is by
   construction the one `ShapeDoc.print` prints, which is what the MCP payload carries. Either is a
   few dozen lines outside this seat's files. One more measured fact for either: a shape document
   names a type by its last name, so `HostSession.Refusal` (a sum) and `Authoring.Refusal` (a
   structure) are both `"Refusal"`; no codec today holds both, but one that did would file two
   bodies under one key (row 8's concern, at the derived level).

## Step 4: row 16, `Await` as a structure

Status: landed (commit named under "Base and head"); the LCNF cuts it moves are step 5's.

### Measured before the edit (the brief's stop condition)

- **Readers outside Lean** (`git grep -n 'Await' ts/ ocaml/ src/OCaml5`, then `awaits`/
  `outstanding`/`awaiting` over `ts ocaml harness`): none pins the tuple. The host harness's
  readers are Lean (`harness/truth/session/Keyed.lean:224-227, :308`;
  `harness/truth/session/Session.lean:133-136, :191-194`), and the JSON they write is already a
  record built by hand (`{"fiber", "token", "row", "request"}`); the TypeScript side reads that JSON
  by name (`check-keyed.ts:22, :46` read only `awaits` and its length). OCaml: the only readers are
  the LCNF cuts (`ocaml/engine/api_engine.ml:14311-14353`, `ocaml/gen/api_gen.ml:16464-…`:
  `program_awaits` returns `(int * (int * (native_op * val_))) list`, reached from
  `Api.frontierReasons`), which are generated, so the `lcnf` group is downstream of this step
  (`docs/GENERATED.md`: lcnf reads `Effect4.Api`); no hand-written OCaml names them (`git grep
  program_awaits -- ocaml`, generated files and their closure TSVs only). The step proceeds: the
  readers move together.
- **Lean consumers** (`git grep -w Await` and the `awaits`/`outstanding`/`freshCall` readers, the
  typed-state cone excluded and found to have none): beyond the brief's six sites, `Api/Frontier.lean`
  (`hostReasons`), `Run.lean` (`freshCall`, `driveFrom`), `Laws/Run.lean` (`awaits_ne_nil`'s proof,
  `requestOf_of_mem_awaits`, `freshCall_facts`, `drive_envelope`'s proof), `Laws/Program/ReasonsR.lean`
  (`awaitsR`, `hostReasonsR`), six batteries and the two harness files. Two of them
  (`awaits_ne_nil`'s membership, `Test/Api/ExternalContract.lean:69`'s literal) the greps missed and
  the first full build found (tested: it stopped there and nowhere else, `logs/step4-build.summary.log`).

### What moved

- `src/Effect4/Program/Admit.lean`: `structure Await where fiber : FiberId; token : Nat; op : NativeOp;
  request : Val` (`deriving DecidableEq`; no `Repr`, which nothing reads), with a docstring naming
  row 16; `awaits` builds the record.
- The codec: `Effect4.Program.Await` in the manifest's `Runner` group, before `Run.Observation`
  (which holds `List Await`); the generated shape is `.struct "Await" [("fiber", …), ("token", …),
  ("op", …), ("request", …)]`. `Api/RunnerBytes.lean:83`'s `Canonical.shape (List Program.Await)`
  and `outstandingBytes` now read that instance (their text unchanged). Guards
  (`tools/Effect4Gen/guards/runner.lean`): an `Await` read back exactly, refused with a byte added,
  fitting its shape, and its shape's field names in order; the `Observation` guard now holds that
  record.
- Consumers: `Api/Frontier.lean` (`hostReasons` reads `a.fiber`, `a.token`); `Run.lean`
  (`freshCall`, `driveFrom`); `Laws/Program/ReasonsR.lean` (`awaitsR`, `hostReasonsR`, kept
  textually parallel to `awaits`/`hostReasons`, so `awaits_eq_ref` and `hostReasons_eq_ref` close
  unchanged); `Laws/Api/Supervision.lean` and `Laws/Run.lean` (below);
  `Test/Api/{HostSession,KeyedHost,Runner,Supervision,External}Contract.lean` and
  `Test/Run/RunContract.lean` (14 literals and 4 projections, `⟨…⟩` and `.fiber`/`.token`);
  `harness/truth/session/Keyed.lean` (`awaitJson`, `planRun`) and `Session.lean` (the recorded-call
  lookup and the receipt's `awaits`), whose JSON was already a record and is byte-for-byte the same.
- **Statements that changed** (the brief's "nothing here changes a statement of the proof graph" does
  not hold for row 16, measured: four statements named the tuple's projections): `awaits_parked`
  and `awaits_live` (`Laws/Api/Supervision.lean`: `a.1`, `a.2.1` → `a.fiber`, `a.token`),
  `requestOf_of_mem_awaits` (`Laws/Run.lean`: `requestOf m a.1 a.2.1 = some (a.2.2.1, a.2.2.2)` →
  `requestOf m a.fiber a.token = some (a.op, a.request)`) and `freshCall_facts` (the key
  `⟨await.1, await.2.1⟩` → `⟨await.fiber, await.token⟩`). Same propositions up to the projections'
  names; no hypothesis or conclusion added or dropped. Proofs restated by the same rename:
  `awaits_ne_nil` (one membership), `drive_envelope` (31 projections); none of these proofs uses
  `simp_all`, `first` or `try`.

### The control

- Red (tested, `seat-J/probes/AwaitRecord.lean`, computed from the instances in the tree): the tuple
  `FiberId × Nat × NativeOp × Val` crosses through the generic pair codec as `.pair _ (.pair _
  (.pair _ _))`, three nested pairs with no field name, which is what `outstandingBytes` wrote before
  this step. Green (tested, the same probe and the generated guards): `Await` crosses as `.struct
  "Await"` with the four field names in order, and `List Await` as a list of it.

### Commands and results

- `LEAN_NUM_THREADS=2 lake build Effect4.Program.Admit Effect4.Api.Frontier Effect4.Api.HostSession
  Effect4.Api.Runner Effect4.Run Effect4.Api.RefusalsDerived Effect4.Api.Derived
  Effect4.Store.Domain.Derived.Value Effect4.Store.Domain.Derived.Program` (the `Runner` group's
  imports): first exit 1 (`Run.lean:291-297`, `driveFrom`'s projections), then exit 0 after the
  rename (`logs/step4-imports-build.summary.log`).
- `LEAN_NUM_THREADS=1 python3 scripts/generate.py --only derived`: exit 0, "PASS generate"; changed
  `src/Effect4/Api/RunnerDerived.lean` only (the `AwaitC` section; `logs/step4-generate-derived.summary.log`).
  It is step 5's first producer, run as soon as the sources were in place, because nothing that
  imports `RunnerDerived` builds without the generated record codec (and `make gen-derived` would
  first run a `lake build` that could not pass).
- `LEAN_NUM_THREADS=2 lake build`: exit 1 in 14 min 41 s (`Laws/Run.lean:267`, `awaits_ne_nil`'s
  tuple membership; `Test/Api/ExternalContract.lean:69`, a tuple literal; `logs/step4-build.summary.log`);
  after the two renames, exit 0 in 2 min 51 s: 747 jobs, both gates ("135 API/utility modules …
  every library source is reachable"; "checked 525 modules and 72539 declarations", `[propext,
  Quot.sound]`) (`logs/step4-build-2.summary.log`).
- Axioms (`seat-J/probes/Step4Axioms.lean`, exit 0, `logs/step4-axioms.log`): `awaits_parked`,
  `awaits_live`, `awaits_ne_nil`, `requestOf_of_mem_awaits`, `freshCall_facts`, `drive_envelope`,
  `awaits_eq_ref`, `hostReasons_eq_ref`, `exists_awaitHost_iff`, `observe_awaitingAsync_iff`: each
  `[propext, Quot.sound]`.


## Step 5: the producer chain, in the fixed order

Status: landed (commit named under "Base and head"): the chain ran in order, `check-gen`, `dune build`
and `check-ocaml` passed.

### Which groups the steps reach (`docs/GENERATED.md`'s inputs column, then measured)

- `derived`: rows 24, 17 and 16 all change its inputs (the forms generator, the manifest, the guards).
- `lcnf` (inputs `Effect4.Machine.Fibers`, `Effect4.Api`, the extern table, the prelude): reached by
  row 16, not by rows 24 or 17. The cut of `Effect4.Api.run`/`replay` contains `Program.awaits` and
  `Api.hostReasons` (reached from `Api.frontierReasons`), whose type was the tuple. So it is run, and
  everything after it.
- `eff` (`Effect4.Program.Native`, `OCaml5.Eff.*`, and `ocaml/engine/api_engine.ml` for the layout
  mirror), `wire` (`Effect4.Program.Wire`), `cas` (the store word, genesis, machine stores): no
  authoring form and no `Canonical` line of these types; `eff` reads the regenerated engine face.
  Run in order after `lcnf`; all three byte-identical (below).

### Commands and results (each with `LEAN_NUM_THREADS=1`; the tools prebuilt at two threads)

| Command | Exit | Files it changed |
| --- | --- | --- |
| `make gen-derived` (after step 4's commit) | 0 | none (the fixpoint; `logs/step5-gen-derived.summary.log`) |
| `make gen-lcnf` | 0 (50 s) | `ocaml/engine/api_engine.ml`, `ocaml/gen/api_gen.ml`, `ocaml/gen/closure-api_engine.tsv`, `ocaml/gen/closure-api_gen.tsv`; `fibers_gen.ml`, `machine_gen.ml` and their closures unchanged (`logs/step5-gen-lcnf.summary.log`) |
| `make gen-eff` | 0 | none (`ocaml/eff/*`, the goldens, `ocaml/engine/e4_program_layout.{ml,json}` byte-identical) |
| `make gen-wire` | 0 | none |
| `make gen-cas` | 0 | none |
| `make check-gen` (the four LCNF files staged) | 0, "PASS check-gen" | none (it re-cut `ts`, `readme` and the corpus index; `logs/step5-check-gen.summary.log`) |
| `cd ocaml && opam exec --switch=effect4 -- dune build` | 0 (11 s, a fresh `_build`) | none (`logs/step5-dune-build.log`) |
| `make check-ocaml` | 0 | none: `dune build`, `dune test eff gen clock`, `dune test engine` ("ALL PASS: 0 failure(s)", 107 checks and the FV1–FV9 view checks), `gen-check.sh` C1–C4 ok, "gen-check: PASS" (`logs/step5-check-ocaml.summary.log`) |

The LCNF diff (reading): an OCaml record `and await = { fiber : fiber_id; token : int; op :
native_op; request : val_ }`; `program_awaits` builds `({ fiber = id; token = token_7; op = fst_11;
request = snd_12 } : await)` where it built `(id, (token_7, val__10))`; `hostReasons`' loop takes an
`await list`; the closure TSVs' rows for these three functions carry new hashes. One hunk outside
`awaits`: in `driveStep`'s `Cmd_launch` arm the join point `_jp_76`'s first two parameters are
swapped, in its body and at both of its calls together (before: called `snd fst`, body
`update_race _y_78 … raceLaunched _y_77 … evaluate _y_77`; after: called `fst snd`, body
`update_race _y_77 … raceLaunched _y_78 … evaluate _y_78`): the same function, the compiler's naming
of the join point's parameters, in both `api_engine.ml` and `api_gen.ml`.

## Step 6: the final build

Status: green.

- `LEAN_NUM_THREADS=2 lake build Effect4.Laws Test.All` (the dispatch's two threads; no build of this
  seat took twenty minutes, the longest was 14 min 41 s): exit 0, "Build completed successfully (743
  jobs)", both gates at `Test/All.lean:169`: "Effect4 library-root gate: 135 API/utility modules, 221
  Laws-only modules; every library source is reachable; Effect4 never reaches Laws" and "Effect4
  module and axiom gate: checked 525 modules and 72539 declarations; semantic/test axioms are
  [propext, Quot.sound]; exact implementation boundary (15 module(s), 23 declaration(s)) additionally
  allows Classical.choice" (`logs/step6-build.summary.log`). At the base: 134 API/utility modules, 524
  modules, 72071 declarations. The added module is `RefusalsDerived`; of the 468 added declarations
  most are generated codec sections (the nine refusal types, `FiberStatus`, `Observation`, `Await`),
  with `minting`, `minting_scoped` and the battery's `outerCursor`, less the two deleted theorems
  (reading; the gate counts, it does not list).
- `#print axioms` for every theorem added, restated or deleted: steps 1, 2 and 4 above (each
  `[propext, Quot.sound]` or less; the generated codecs print their own receipts in their files, all
  within the ceiling, and the derived checker refuses `Classical.choice`).
- The generated files, with their producers and exit codes: the table under "Every changed path".

## Step 7: one TypeScript compiler, tsgo 7

Status: (i) landed (commit and its run named below); (ii) measured, not moved: the ingest's AST
functions are missing from TypeScript 7's API; (iii) written and measured red on this tree, not wired
into `check` (the brief: "if an AST function is missing, land (i) alone").

### (i) `check-host-protocol` to tsgo

`scripts/check-host-protocol.py`: the host programs and the adapter sources are type-checked by
`node ts/eff/node_modules/@typescript/native-preview/bin/tsgo --pretty false --noEmit -p <work>/tsconfig.json`
(the same flags `tsc` had, and the launcher `check-target` runs at `Makefile:393`); the script
refuses to start without `node` and the pinned launcher. `bin/tsgo` is a node launcher of the native
compiler (`#!/usr/bin/env node`, `import "../lib/tsgo.js"`), version `7.0.0-dev.20260629.1` (`node …/tsgo
--version`, tested).

- `LEAN_NUM_THREADS=2 make check-host-protocol`, first run: exit 2 before the type check, `bun
  harness/truth/session/run-keyed.ts`: "Cannot find module 'effect/unstable/persistence' from
  '…/harness/truth/session/keyed-bindings.ts'" (`logs/step7-check-host-protocol-first-run.log`).
  The harness resolves `effect` through `harness/truth/node_modules`, a link the Makefile makes
  (`make harness/truth/node_modules`, `ln -s ../../ts/eff/node_modules`) and the `host-protocol` rule
  does not list as a prerequisite (a fresh worktree has no link; the main checkout has had one since
  2026-09-13). Made by its rule, then:
- `LEAN_NUM_THREADS=2 make check-host-protocol`: **exit 0**. "PASS keyed host: 57 actual rc.112 runs;
  52 admitted printed programs", the tsgo check silent (no diagnostic), `bun test` 42 pass, 0 fail,
  "PASS keyed differential: 57 runs, 52 programs, 30 controls; exact exits and keyed applications",
  "PASS host-protocol: fresh projections, typed host programs, keyed replay and negative controls"
  (`logs/step7-check-host-protocol.log`). The same run exercised step 4's harness edits:
  `Keyed.lean emit` and `batch` ran and the keyed differential compared their outputs with the
  host's, and `Session.lean emit` ran (the legacy adapter still builds).
- The control (tested, `logs/step7-tsgo-control.log`): tsgo 7.0.0-dev.20260629.1 with the check's own
  settings over the host programs the check kept (`harness/truth/session/.work/latest/host/*.ts`) and
  the adapter sources: exit 0, 70 files listed; the same plus one file holding `const n: number =
  "one"`: exit 1, "error TS2322: Type 'string' is not assignable to type 'number'". The lane fails on a
  type error.

### (ii) The ingest recognizer's `typescript@5.9.2`: measured

- What the six files use (`seat-J/ts-api-measure.py`, reading only; `logs/ts-api-measure.log`): 75
  members of `ts`, 56 of them called as `ts.f(…)`. All six use it as a parser and nothing else: every
  `createSourceFile` call has no program (`decls-ck.ts:6` says so; `check-styles.ts:14-18` compares its
  parse diagnostics with oxc's), plus `parseConfigFileTextToJson` (a tsconfig read,
  `census/corpus.ts:14`) and `flattenDiagnosticMessageText` (`check-styles.ts:18`). No checker, no
  program, no emit.
- What TypeScript 7 declares (reading the shipped `.d.ts` of `typescript@7.0.2`, bun's cached copy of
  the version `harness/schema-host` pins, and of the installed `@typescript/native-preview@7.0.0-dev.20260629.1`;
  the two agree): the root export `typescript` is `./lib/version.cjs` only (so `import ts from
  "typescript"` has no API); the API is `typescript/unstable/{sync,async,ast,ast/is,…}`. Of the 56,
  **missing**: `ts.createSourceFile` as a parser (TS 7's `createSourceFile(statements, endOfFileToken,
  text, fileName, path)` is a node factory; parsing text goes through the `API` client of
  `unstable/sync`, which spawns the native compiler and serves source files of a snapshot),
  `ts.forEachChild` as a free function (a `Node` method only), `ts.getModifiers`,
  `ts.canHaveModifiers`, `ts.isTypeAssertionExpression`, `ts.parseConfigFileTextToJson`,
  `ts.flattenDiagnosticMessageText`. Present: the other 49 `is*` guards and the enums (`SyntaxKind`,
  `NodeFlags`, `ScriptKind`, `ScriptTarget`) under `unstable/ast`. `effect-tsgo patch --typescript`
  (`harness/schema-host`'s `prepare`) replaces the native binary with Effect's build and adds no JS API
  (its README, read from bun's cached `@effect/tsgo@0.38.0`).
- So the repin is not a version bump: it is a rewrite of the parse entry and the walk. Not done; the
  5.9.2 pin and its lockfile entries stay. No ingest check was run (it would run `typescript@5.9.2`).
- Options (the owner's): **(A)** keep the parser-only dependency under a named exception pinned by
  hash: `ts/eff/package.json`'s `typescript: 5.9.2` with its lockfile integrity
  (`ts/eff/bun.lock:112`, `sha512-CWBzXQrc/qOkhidw1OzBTQuYRbfyxDXJMVJ1XNwUHGROVmuaeiEm3OslpZ1RV96d7SKKjZKrSJu3+t/xlw3R9A==`), imported by these six files for parsing only, never run as a
  compiler, and exempted by name in the guard of (iii). **(B)** write the walk against the native API:
  one parse helper over `unstable/sync`'s `API` (a snapshot of the text in a virtual file system,
  `getSourceFile`), `node.forEachChild(f)` for `ts.forEachChild(node, f)`, the `modifiers` field for
  `getModifiers`/`canHaveModifiers`, a `kind` test for `isTypeAssertionExpression`, the API's
  `parseConfigFile` (or a JSONC read) for the tsconfig, and the diagnostics' own text; then repin
  `typescript` to 7.0.2 (or drop it for the preview's API) and delete the 5.9.2 entries.
  Recommended: (B). It is the owner's rule as stated (one compiler, and `typescript@5.x` never run, in a
  gate either), the AST is the oracle's own grammar (which is what `check-styles.ts`'s differential is
  about), and 49 of the 56 calls carry over by name; until it lands, (A) is the honest description of
  the tree, so the guard should carry the exception by name rather than be absent.

### (iii) The guard

The one line, as it would sit in the `Makefile` (a phony `check-tsgo`, prerequisite of `check`):

    check-tsgo: ## no node_modules/typescript below 7 under ts/, harness/ or tools/ (tsgo 7 is the one compiler)
    	@$(PY) -c 'import json,pathlib,sys; v=lambda p: json.loads(p.read_text())["version"]; bad=[p.as_posix()+": "+v(p) for r in ("ts","harness","tools") for p in sorted(pathlib.Path(r).rglob("node_modules/typescript/package.json")) if int(v(p).split(".")[0]) < 7]; print("\n".join(["FAIL check-tsgo: typescript below 7 (tsgo 7 is the one compiler):"]+bad) if bad else "PASS check-tsgo: no typescript below 7 under ts/, harness/ or tools/"); sys.exit(1 if bad else 0)'

Run as that one line on this tree after `make check-gen` had installed `ts/eff/node_modules`: exit 1,
"FAIL check-tsgo: … ts/eff/node_modules/typescript/package.json: 5.9.2" (tested,
`logs/check-tsgo-proposed.log`). In `check` it would turn `make check` red until (ii) is ruled, so it is
not in the `Makefile` here. With (A) it lands with the one exempted path; with (B) it lands as is.

## Every changed path (`git diff --numstat 6b3f2c92 03e99961`, outside `docs/research`: 38 files, +1846 −408)

| Path | Step | Change |
| --- | --- | --- |
| `src/Effect4/Laws/Machine/Lift.lean` | 1 | twelve stale `Machine/Fibers.lean` citations, docstrings only |
| `src/Effect4/Laws/Program/Guard/Single.lean` | 1 | `held_fireStep` deleted |
| `src/Effect4/Laws/Program/Guard/OuterDriver.lean` | 1 | `fireStep_preserved` deleted |
| `src/Effect4/Laws/Auto/Traversals.lean` | 1 | `writtenName` moved up; `describeAlgebra` prints written names |
| `Test/Audit/TraversalCensus.lean` | 1 | the two fold rows pinned by substring; docstring |
| `src/Effect4/Program/Authoring/Sugar.lean` | 2 | `minting` (new); `bindWith`, `andThen` mint |
| `src/Effect4/Program/Authoring/Loops.lean` | 2 | `iterateWith` mints |
| `src/Effect4/Laws/Program/Authoring/Sugar.lean` | 2 | `minting_scoped` (new); two proofs restated |
| `src/Effect4/Laws/Program/Authoring/Loops.lean` | 2 | `iterateWith_scoped`'s proof restated |
| `tools/Effect4Gen/Forms.lean` | 2 | internal binders minted and read through `minted` |
| `tools/Effect4Gen/manifest.json` | 2, 3, 4 | forms imports; the `Refusals` group; `Runner` imports and types (`Await`, `FiberStatus`, `Observation`) |
| `Test/Program/AuthorContract.lean` | 2 | four B-9 controls flipped and kept as history |
| `tools/Effect4Gen/guards/refusals.lean` (new) | 3 | the refusals' acceptance guards |
| `tools/Effect4Gen/guards/runner.lean` | 3, 4 | `FiberStatus`, `Observation` and `Await` guards |
| `Makefile` | 3 | `DERIVED_OUT` + `RefusalsDerived.lean`; `DERIVED_TRACES` + `Run.trace` |
| `src/Effect4/Program/Admit.lean` | 4 | `structure Await`; `awaits` |
| `src/Effect4/Api/Frontier.lean`, `src/Effect4/Run.lean` | 4 | the record's fields |
| `src/Effect4/Laws/Api/Supervision.lean`, `src/Effect4/Laws/Run.lean`, `src/Effect4/Laws/Program/ReasonsR.lean` | 4 | statements and proofs over the record |
| `Test/Api/{ExternalContract,HostSessionContract,KeyedHostContract,RunnerContract,SupervisionContract}.lean`, `Test/Run/RunContract.lean` | 4 | literals and projections |
| `harness/truth/session/Keyed.lean`, `harness/truth/session/Session.lean` | 4 | the record's fields |
| `scripts/check-host-protocol.py` | 7 | tsgo 7 in place of `tsc` |
| generated (below) | 2–5 | by their producers only |
| `docs/research/2026-10-01-landing/seat-J/**` (force-added) | 1–7 | probes, scripts, logs this receipt cites |
| `docs/research/2026-10-01-landing/receipt-J.md` (force-added) | — | this receipt |

### The generated files, their producers and exit codes

| Generated file | Producer command (each `LEAN_NUM_THREADS=1`) | Step | Exit |
| --- | --- | --- | --- |
| `src/Effect4/Codegen/Authoring/Forms.lean` | `make gen-derived` (`tools/Effect4Gen/Forms.lean --group Forms`) | 2 | 0 |
| `src/Effect4/Laws/Program/Authoring/Forms.lean` | `make gen-derived` (`… --group FormsLaws`) | 2 | 0 |
| `src/Effect4/Api/RefusalsDerived.lean` (new) | `python3 scripts/generate.py --only derived`, then `make gen-derived` (no change) | 3 | 0, 0 (two earlier cuts: 2, 0; measured above) |
| `src/Effect4/Api/RunnerDerived.lean` | step 3: as above; step 4: `python3 scripts/generate.py --only derived`; step 5: `make gen-derived` (no change) | 3, 4 | 0 |
| `ocaml/engine/api_engine.ml`, `ocaml/gen/api_gen.ml`, `ocaml/gen/closure-api_engine.tsv`, `ocaml/gen/closure-api_gen.tsv` | `make gen-lcnf` | 5 | 0 |

Every other path in `GENERATED_PATHS` was re-cut and found byte-identical: `make gen-derived` four times
(steps 2, 3, 3, 5), `variances` once (step 2), `make gen-eff`, `gen-wire`, `gen-cas` (step 5), and
`make check-gen` twice (steps 3 and 5: `eff`, `wire`, `cas`, `ts`, `readme` and the corpus index;
"PASS check-gen" both times).

## What is owed, with the exact obstacle

1. **Row 17, `BuildRefusal`'s codec** (step 3): its module's import leaks the authoring keywords.
   Options (a) its own group with a root import at an anchor the coordinator names, (b) move the type
   out of `Api/Author.lean`, (c) scope the authoring syntax; recommended (c), then one manifest line.
2. **Row 17, `head : T → String` per sum** (step 3): the generator and the driver are not this seat's
   files. Options (a) per-sum emission in `Main.lean`, (b) one generic `Canonical.head` read off the
   shape document; recommended (b). Twenty sums have a codec in the two groups touched.
3. **Step 7 (ii) and (iii)**: the ingest's `typescript@5.9.2` (seven API functions missing in TypeScript
   7: the parser entry `createSourceFile`, `forEachChild` as a function, `getModifiers`,
   `canHaveModifiers`, `isTypeAssertionExpression`, `parseConfigFileTextToJson`,
   `flattenDiagnosticMessageText`). Options (A) a named exception pinned by its lockfile hash, (B) the
   walk rewritten against the native API; recommended (B). The guard's one line is under step 7: with
   (A) it lands with one exempted path, with (B) as is; until then `check` would be red with it.
4. **The daemon keyword leak** (found in step 3, beyond the rows): any module that imports
   `Effect4.Api.Author` (or `Program/Authoring/Services.lean`) cannot write `{ daemon := … }` for
   `Supervision.ForkOptions`. Not repaired (not this seat's files); the repair is option (c) of item 1.
5. **`Env.mint`'s docstring** (`Program/Authoring.lean:131-134`, not this seat's file) says a minted
   name carries "the level it will be bound at". For the second binder of a two-binder lift
   (`iterateWith`'s answer, the forms' `acquireRelease` exit) the minted level is the construct's, one
   below the binding level; the two names still differ by stem, so no capture follows. One sentence:
   "the level of the construct that binds it; two binders of one construct differ by stem".
6. **`make check-host-protocol` in a fresh worktree** (step 7): the rule needs `harness/truth/node_modules`
   but does not list it; the order-only prerequisite `| harness/truth/node_modules` on
   `$(CHK)/host-protocol` closes it (one word in the `Makefile`; not done: outside step 7's list).

Bounded or host-only evidence: the B-9 controls, the census pins, the codec guards and the record
probe are finite checks (tested), not theorems; the tsgo and rc.112 results are host runs (tsgo
7.0.0-dev.20260629.1, bun 1.4.2, the pinned rc.112). The scope lemmas (`minting_scoped` and the
restated ones) and the restated row-16 laws are proved.

## Lines proposed for the coordinator's files

**`docs/core/decisions.md`, row 24, status** (replacing "not started: …"):
> **Landed 2026-10-01** (seat J, `2f95739c`): every binder the authoring surface names is minted.
> `Sugar.minting stem k` hands a convenience `Env.mint stem` (with `minting_scoped`); `bindWith`,
> `andThen` (stem `answer`) and `iterateWith` (`cursor`, `answer`) mint through it and read through
> `minted`; the forms generator mints each internal binder (`Authoring.minting "<role>"`) and reads it
> through `minted`, and `make gen-derived` rewrote exactly the two forms outputs. The red control at
> `Test/Program/AuthorContract.lean` flipped (an author's `"_answer1"` reads their own answer, `.var 0`)
> and is kept as history under `#guard_msgs (error)`, with three new pairs for `andThen`, `bindWith`
> and `iterateWith`, each red at the base definitions (`seat-J/probes/OldMintedSpellings.lean`).

**Row 17, status** (replacing "not started beyond …"):
> **Partly landed 2026-10-01** (seat J, `9e466686`): `Canonical FiberStatus` and `Canonical
> Observation` in the `Runner` group; a `Refusals` group (`Api/RefusalsDerived.lean`, before `Runner`,
> which imports it) for `Authoring.Reason`/`Refusal`, `TypeReason`/`TypeRefusal`, `AuthorRefusal`,
> `PrintRefusal`, `ReadRefusal`, with `AdmitRefusal` and `TableRefusal` moved from `Runner` (bytes
> unchanged), guarded. Open: `BuildRefusal` (importing `Api.Author` makes `daemon`/`eff` keywords in
> every importer; options in receipt J, recommended: scope the authoring syntax) and `head` per sum
> (recommended: one generic `Canonical.head` read off the shape).

**Row 16, status** (replacing "half: …"):
> **Landed 2026-10-01** (seat J, `ffc8bb93`, LCNF `d8e9b596`): `Program.Await` is a structure `{ fiber,
> token, op, request }` whose codec is generated in the `Runner` group (`.struct "Await"` with its field
> names); `awaits`, `awaitsR`, `hostReasons(R)`, `Run.freshCall`/`driveFrom`, six batteries and the two
> harness drivers moved; four law statements now name the fields (`awaits_parked`, `awaits_live`,
> `requestOf_of_mem_awaits`, `freshCall_facts`); the LCNF engine cut carries `type await`. No reader
> outside Lean pinned the tuple.

**Row 150, status** (appended):
> Owed items done 2026-10-01 (seat J, `d22f71bd`): `held_fireStep` and `fireStep_preserved` deleted;
> the Decision section's citations corrected, with three more stale ones (`Framed`, `DecisionLift.answer`,
> `AdmittedReplay`); the traversal census prints a fold's algebra by its written name, pinned in
> `Test/Audit/TraversalCensus.lean`.

**`AGENTS.md`, the TypeScript bullet's last sentence** (replacing "The ingest recognizer's … and
`scripts/check-host-protocol.py`'s `tsc` are the two lanes still to move (seat J)."):
> `scripts/check-host-protocol.py` runs tsgo (seat J, 2026-10-01). The ingest recognizer's
> `typescript@5.9.2` is imported as a parser only and stays until the owner chooses between a named
> exception and a rewrite against TypeScript 7's API (receipt J, step 7); `make check-tsgo` joins `check`
> with that choice.

**`Test/Counterexamples/REGISTER.md`** (one row; the id is the coordinator's):
> `E4-AUTHOR-CE-001` | REPAIRED 2026-10-01 | A binder the authoring surface names for itself cannot
> capture a name the author wrote (B-9) | `Test/Program/AuthorContract.lean`: the four history guards
> (`Forms.tapContinuation "_answer1"`, `andThen` under an author's `"_"`, `bindWith` under `"_1"`, the
> loop `outerCursor` under `"_c1"`), each `.var 1` where the author meant `.var 0` | `Sugar.minting`,
> `minting_scoped`, the forms generator's minted internal binders; decisions row 24 |

**`docs/ARCHITECTURE.md`** (if it lists the API's generated modules): `Api/RefusalsDerived.lean`, the
`Refusals` group's codecs, imported by `Api/RunnerDerived.lean`.

## Plan §5, the three measures

1. **Repeated proofs that disappeared:** none were repeated; two dead theorems went
   (`held_fireStep`, `fireStep_preserved`). What is shared now: one combinator and one lemma
   (`minting`, `minting_scoped`) serve every minted binder, the three hand conveniences and the seven
   generated forms, where a per-construct sugar would have been seven; `bindWith_scoped`,
   `andThen_scoped` and `iterateWith_scoped` are one application of it each.
2. **Program-to-execution connections closed:** none. Rows 24, 17 and 16 are names, codecs and a
   record; the LCNF regeneration carries the same `awaits` into the engine as a record.
3. **The eventual claim:** unchanged. Nothing here bears on M7 or on a lowering claim.
