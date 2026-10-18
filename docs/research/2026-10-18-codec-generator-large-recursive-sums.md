# The codec generator's proofs for large recursive sums (second look)

Status: second look done 2026-10-18; arm lemmas are the generator's only template (owner,
2026-10-18: "log it for a second look later, it's likely unoptimized"). History, not authority.
Found while generating the Tool codec group in seams S3b.

## The one thing to know first

The generator's recursive template did not scale to `Program.EffName`: its round-trip proof timed
out in `whnf` even at four times the default budget. A budget raise treated the symptom and was
reverted. One `rfl` equation per reader arm fixes it (below). Measured on every codec group, it is
faster or even everywhere and needs no raised budget, so it is now the only template.

## What was observed

- `Live.View` reaches `EffName` through one field, `WaitView.registration : Option EffName`
  (`src/Effect4/Run/View.lean`).
- `EffName` has 57 constructors and refers to itself (`withWaiter (base : EffName)`). `Machine.Name`
  also refers to itself. So the generator emits the recursive template: one structural reader
  `raw…` over `Val`, with one `.ctor n [v0, …]` arm per constructor.
- Each arm of the generated `ofVal_toVal` runs `simp only [toVal…, raw…, Canonical.ofVal_toVal]`.
- The one-field arm `cont` times out at 800,000 heartbeats, in `whnf`, inside `simp`.
- The plain (non-recursive) template handles `Machine.SyncOp` (31 constructors) at 400,000. Its
  rule raises the budget only past 32 constructors (`emitPlain`, `tools/Effect4Gen/Main.lean`).
- The recursive template handles `Program.Eff` (29 constructors) at the default budget.

## The likely cause

`simp only [raw…]` needs the reader's equation lemmas. Lean builds them on first use, by splitting
a 57-arm match whose patterns are natural-number literals and list lengths, inside a structural
recursion over the nested inductive `Val`. That construction grows faster than linearly in the arm
count. The budget is not the constraint.

## Candidate fixes, to measure

1. Decode in two stages: `.ctor tag fields => arm tag fields`, with `arm` a match on the tag alone
   and each arm a small match on its field list. The equation lemmas then stay small.
2. Prove each arm without the equation lemmas: rewrite the inner `Canonical.ofVal_toVal` facts,
   then close by definitional unfolding (`show` and `rfl`), which needs no splitter.
3. Emit the equation lemmas once, eagerly, at the reader's definition, and measure whether that
   alone fixes the cost.

Each candidate must keep today's bytes for every existing group: `generate.py --only derived`
refuses a diff.

## What landed (owner's choice, 2026-10-18: fix the generator now)

Measurements first. On the cut file, `rfl` unfolds the reader at one constructor cheaply, and
`toVal`'s equation lemma builds cheaply. `simp only [raw…]` is what times out. So the cost is
the reader's equation lemmas, which Lean builds by splitting the whole match.

The generator gains an opt-in flag, `--arm-lemmas` (`tools/Effect4Gen/Main.lean`):

- `emitArmLemma` states each reader arm as its own equation, proved by `rfl`. The round-trip
  proof rewrites with these instead of the reader's equation lemmas.
- A zero-argument arm closes by `rfl`.
- A plain sum takes the recursive item's exactness: `guarded toVal ofVal` with `guarded_exact`,
  so no proof splits the whole match.

Result: the Tool group through `Live.View` (6,697 lines, `EffName` and `SyncOp` included)
compiles in 6.3 seconds at the default budget, with no `maxHeartbeats` option.

## The second look (2026-10-18): measured, made the default

Method. Every group the codec generator emits (`tools/Effect4Gen/Main.lean`; the other tools'
groups do not read the flag) was emitted twice from c95288fe3, with and without `--arm-lemmas`,
into a scratch directory: one `lake exe effect4gen --batch` over the driver's `--plan` rows
(`generate.py --output-dir` refuses any file that differs from the tree, so it cannot emit the
other variant). The "without" files were byte-identical to the tree for the eight groups that ran
without the flag, and the "with" files for Check and Tool. Each file was then compiled alone,
`lake env lean -DwarningAsError=true <file>` under `/usr/bin/time -l`, one Lean at a time through
the seams lock (three threads), against the tree's built imports. Two passes, the second in the
reverse order. The machine was shared (load average 12 to 14 throughout), so the seconds are
wall clock and noisy; the ratios held across both passes.

| Group | Lines without → with | Bytes without → with | Seconds without (pass 1 / 2) | Seconds with (pass 1 / 2) | Peak MB without → with |
| --- | --- | --- | --- | --- | --- |
| Json | 353 → 381 | 13,531 → 14,537 | 1.4 / 1.2 | 0.9 / 1.1 | 447 → 439 |
| Schema | 1,850 → 2,040 | 84,962 → 95,515 | 10.8 / 13.2 | 3.7 / 6.1 | 905 → 521 |
| Program | 3,831 → 4,190 | 171,000 → 190,615 | 20.6 / 30.1 | 4.7 / 6.8 | 1,052 → 658 |
| Pin | 301 → 294 | 13,305 → 13,163 | 0.9 / 1.5 | 0.8 / 1.7 | 451 → 449 |
| Api | 320 → 303 | 12,100 → 11,935 | 1.1 / 1.1 | 0.8 / 1.7 | 763 → 754 |
| Value | 970 → 1,002 | 37,760 → 40,272 | 5.0 / 5.7 | 1.4 / 1.7 | 558 → 464 |
| Refusals | 3,656 → 3,424 | 172,491 → 174,538 | 20.1 / 26.6 | 3.1 / 4.5 | 1,577 → 1,008 |
| Runner | 2,077 → 1,927 | 99,697 → 98,603 | 4.2 / 5.7 | 2.3 / 4.9 | 1,018 → 977 |
| Check | 834 → 810 | 42,679 → 43,330 | 2.3 / 2.6 | 2.1 / 2.5 | 1,471 → 1,458 |
| Tool | 10,432 → 10,716 | 601,730 → 648,915 | fails at 36.7 / not rerun | 10.8 / 10.9 | 2,199 → 1,817 |

Summed over the nine groups that compile both ways: 66.4 s → 19.9 s (pass 1), 87.6 s → 31.0 s
(pass 2). Tool without the flag fails at the default budget first in `Machine.SyncOp` (31 arms,
`refMake`), before `EffName` is reached.

The budget rule. `Refusals` holds the rule's one user, `TypeReason` (34 arms,
`set_option maxHeartbeats 600000`). With the option deleted from the file: without arm lemmas it
fails (`isDefEq` timeout at 200,000, in `TypeReason.term`, 18.9 s); with arm lemmas it compiles
(3.1 s, then 4.4 s), the same as with the option. So the rule served only the old template.

Reading the table:

- Where a group has large sums or many of them, arm lemmas cut the compile time: Schema, Program,
  Value and Refusals by a factor of two to six in both passes, Runner by a factor of 1.2 to 1.8.
  Schema, Program and Refusals also drop over a third of their peak memory. Small groups (Json,
  Pin, Api, Check) are even within the noise.
- Output size moves both ways and by little: one more `theorem … := rfl` per argument-taking arm,
  one fewer `ofVal_exact` script per plain sum. Tool grows 8 per cent in bytes; Refusals and
  Runner shrink in lines.
- The price is at run time, not measured here: a plain sum's decoder is now `guarded toVal ofVal`,
  so a decode re-encodes what it read once per plain-sum level, as recursive items already did
  (`guarded`, `src/Effect4/Store/Domain/Canonical.lean`). The results are the same, since
  `ofVal` was already exact.

What landed. `--arm-lemmas` is gone as a flag: the recursive and plain templates always emit one
`rfl` equation per argument-taking reader arm, a nullary plain arm closes by `rfl`, and every
non-structure plain sum reads through `guarded toVal ofVal`. A structure keeps its own
`ofVal_exact`. The budget rule (`emitPlain`, past 32 arms) is deleted, and the manifest's Check
and Tool groups no longer pass the flag. Every codec group's file was regenerated (its header
prose now says what is emitted); the other generators' groups are byte-identical.

Evidence for the landing, from c95288fe3, one Lean at a time through `/private/tmp/seams-lean-one.py`:

- `python3 scripts/generate.py --only derived`: PASS, and its closing `lake build` of every
  generated module, 421 jobs, completed. Exactly the ten codec files changed; no codec file holds a
  `maxHeartbeats` option.
- `make batteries-touched BASE=c95288fe3`: "no battery reached". No battery names a changed
  declaration or imports a changed module directly; the instances reach them through umbrella
  imports, which the script does not follow.
- So the batteries that decode these carriers were built by name: `Test.Store.{DerivedCheck,
  StoreContract, Templates, TraitContract, ProgramContent, NodeContract, ProbeContract,
  SeamsRead}`, `Test.Api.RunnerContract`, `Test.Program.{SeamsS3bWire, AnswerSchema,
  LiveRecordControls}`, `Test.Codegen.{DataCodec, SchemaGenerationContract}`,
  `Test.Schema.AnnotationDataPlaneContract`: 1,166 jobs, including the library modules between
  them and the codec files, completed with no error and no warning.
- Not run: the axiom gate, the full battery sweep, `make check-gen`.

## What this does not establish

- The timings are one shared machine's wall clock; only the ratios are claimed.
- Each "with" file was compiled against the tree's "without" builds of the groups it imports;
  the regenerated tree's own build is the evidence for the files as committed.
- The run-time cost of the guard on plain sums is not measured.
- It says nothing about the store, the native codecs or the TypeScript printer.
