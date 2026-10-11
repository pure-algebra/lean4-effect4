# Consolidation audit of the goals lane

The owner, 2026-10-11: audit Codex's work at every merge, so that the representations stay minimal
and improve, and so that Codex's continuous goal absorbs the consolidation. This file is the
running audit. Claude adds a dated section at each merge tick that finds something. Codex reads it,
with `CODEX-PROMPT.md`, at the start of each slice.

## How each section is measured

The merge tick runs one script over the merged range: the session scratchpad's
`consolidation-audit.sh FROM TO`. Over the Lean files that the range adds or changes under
`src/Effect4/Laws` and `Test/Dogfood`, it counts:

- the lines added and removed;
- the uses of the shared laws: `Interferes`, `FramesFollow`, the moves, the footprint, the ledger,
  `AnswerFlow`, `StackRegion`, `LiftPrefix`;
- the private case analyses: an `unfold`, or a `simp only [driveStep]`, of `evaluatePrim`,
  `evaluateNative`, `driveStep`, `iteration`, `exitScoped` or `settle`; a `cases` over a command;
  a `fun_cases` of the evaluator;
- the mentions of `DecisionLift` outside the shared lift;
- the files added, with their lengths.

The base-law modules are the one case analysis each, so they are not counted.

**The direction wanted:**

- shared-law uses rise;
- private case analyses and hand-built lifts fall;
- a consolidation removes more lines than it adds.

A slice that adds a private command or evaluator pass for one scenario is a regression. The audit
names it, and the next prompt asks for its replacement.

## 2026-10-11, the baseline

Range `b74ebab6f..4bc3efc44`: Codex's integration branch over 2026-10-11, 197 commits.

| Measure | Value |
| --- | --- |
| lines in `Laws` and `Dogfood` | 46,377 added, 2,007 removed |
| files changed, added | 262, 207 |
| shared-law uses | 179 |
| private case analyses | 466 |
| hand-built decision lifts | 8 mentions in 7 files: `MaskRuns`, `NativeHeapHistory`, `NativeHeapReplies`, `NativeHistory`, `NativeReplies`, `ReleaseCustody/Lift`, `SourceOpportunityHistory` |

Largest private analyses:

| Module | Private case analyses |
| --- | --- |
| `Laws/Machine/Handles` | 51 |
| `Laws/Machine/MaskRuns` | 26 |
| `Simulation/Evaluate` | 20 |
| `Simulation/Drive` | 20 |
| `StatePreservation` | 19 |
| `StackRegionCommands` | 17 |
| `ReleaseCustody/NativeActionDebit` | 16 |
| `Parking` | 16 |
| `ReleaseCustody/NativeSequencing` | 15 |

The Timeout chain's 36 files (`Test/Dogfood/Proofs/HostTimeout*.lean`) hold about 436 `cases`
lines.

What to do with it: `CODEX-PROMPT.md`, items 1 to 3. The Timeout producer is written over the
shared laws, and the ledgers become instances of `Laws/Machine/Ledger.lean`.

## 2026-10-11 10:25, the first consolidation

Range `0d1acfd87..e2998236e`: 13 commits, a fast-forward.

| Measure | Value |
| --- | --- |
| lines in `Laws` and `Dogfood` | 1,823 added, 737 removed |
| files changed, added | 20, 9 |
| shared-law uses | 137 |
| private case analyses | 19 |
| hand-built decision lifts | 0 |

**Consolidated.**
- `FinalizerCommands` and `FinalizerBookkeeping` are now instances of the stack ledger: from 873
  lines to 524 with `LedgerFinalizer`, all 48 statements unchanged (Codex's
  `2026-10-11-codex-consolidation-receipt.md`).
- `FinalizerCredits` reads `FrameWeights` instead of its own pop traversal.
- `WriterWeights` is one native start bound that Atomic and Workers share.
- The private command and settlement matches in those modules fall from 16 to zero.

**Still per scenario.** `Atomic/WriterMachine` defines its own `fibers` and `outside` sums over the
machine's fibers. They repeat `SourceOpportunityMachine.fibers` and `outside`: both are
current-code weights, which the stack ledger does not cover. The shared replacement is the frame
weight ledger: the stack weight plus the current code, with the `outside` frame rule. It waits for
R2 or for the frame-weight generalization of `Ledger`.

**Verdict: improving.** In the baseline, shared-law uses were 179 against 466 private case
analyses; in this range they are 137 against 19. Lines added still exceed lines removed, by the new
Atomic writer files (505 lines) and the Timeout form family (305 lines).

## 2026-10-11 11:25, the second range (merged at 12:40, below)

Range `e2998236e..23d070d77`: 23 commits on the integration branch, measured from git without a
merge. The merge was aborted: the head does not build (`CODEX-PROMPT.md`, "Blocking"). The counts
leave out `FiberSum` and `FiberSumConnect`, which are Claude's. They are diff counts: what the
range adds and removes, not totals over the changed files.

| Measure | Added | Removed |
| --- | --- | --- |
| lines in `Laws`, `Dogfood` and `Machine` | 1,851 | 782 |
| shared-law uses | 182 | 74 |
| private case analyses | 2 | 13 |
| hand-built decision lifts | 0 | 0 |

**Consolidated.**
- New shared structure:
  - `PopTrace` and `PopTraceFamily`, one pop provenance;
  - `TracedMoves` and `FinalizerMoves`, the labelled moves of item 2;
  - `Contracts/FramePath`;
  - `PrimWeights` with the generated `Machine/Fold.lean`, the one code-weight fold of item 4.
- `ReleaseCustody/NativeStacks` falls from 148 lines to 34 on the shared interference census.
- `FinalizerTransfer` drops 52 lines to the shared finalizer debit.
- The Timeout chain's region prefix, sync transfer and pop now read the shared laws (four
  receipts).

**Still per family.** No family has moved onto `FiberSum` yet. Its own split declarations remain
in `SourceOpportunityMachine` (5), `ReleaseCustody/Outside` (4), `WriterWeights` (2) and Atomic
`WriterMachine` (2). That is item 3's second half.

**Largest private analyses left** (whole-file counts): `Handles` 51, `Guard/Core` 32,
`MaskRuns` 26. The range touched each by one or two lines.

**Verdict: improving.** Shared-law uses rise by 108 and private analyses fall by 11. Lines added
exceed lines removed by 1,069, and the excess is new shared structure. The one defect is the build
break.

## 2026-10-11 12:40, the second range merged

Range `35e3f9559..f821dd533`: 26 commits, merged as `fcfbf5cad`. It holds the 11:25 range and six
commits after it. The counts are diff counts over `Laws`, `Dogfood` and `Machine`: what the range
adds and removes.

| Measure | Added | Removed |
| --- | --- | --- |
| lines | 1,945 | 866 |
| shared-law uses | 197 | 76 |
| private case analyses | 2 | 13 |
| hand-built decision lifts | 0 | 0 |

**Repaired.** `98567f7f2` repairs the two modules that broke at 11:25, and the fifteen other
consumers of `interruptRecord`, across the law graph. Codex rebuilt the whole graph
(`a723a81f0`).

**Consolidated.**
- Item 3's second half: `SourceOpportunityMachine`, `ReleaseCustody/Outside`, `WriterWeights` and
  Atomic `WriterMachine` prove their sums by `FiberSum`. They keep their thirteen declarations by
  name and statement, as the prompt asks; the three library files fall by 11 lines.
- The new files are shared structure: `PopTrace` (285 lines), `TracedMoves` (279),
  `Machine/Fold.lean` (258, generated), `FinalizerMoves` (117), `PopTraceFamily` (85),
  `Contracts/FramePath` (50) and `PrimWeights` (42).
- Codex took up the tokens-in-places note within the hour. Its probe `codex/place-writes/` checks
  the code-to-data write exchange of the Timeout, Atomic and Workers writers. It uses the generated
  fold and adds no traversal.

**Next.** Item 10, machine edits (`../2026-10-11-tokens-in-places/machine-edits.md`). Sixteen
modules re-prove their invariants through every driver helper, about 210 lemmas. The probe shows the
alternative compiles.

**Verdict: improving.** Shared-law uses rise by 121 and private analyses fall by 11. The excess of
lines is new shared structure.


## 2026-10-11 13:45, the frame-rule parameter

Range `1a862c4fd..b4dcef4f1`: two commits, merged as `27076ad79`. The script counts one changed
law file, 27 lines added and 6 removed, no shared-law use, no private case analysis and no hand
lift. The file is `src/Effect4/Laws/Auto/Frames.lean`: `#frame_rules` takes a named state
parameter, for invariants with a later phase index such as the R2 guard state. That is shared proof
tooling.

**Open, not merged.** Codex's R2 change has 81 files open in its worktree, uncommitted. Its draft
`Laws/Machine/Edits.lean` has the sixteen edits that the census of 13:35 finds in the driver.
`CODEX-PROMPT.md` item 10 adds one footprint function and one `dropToken` to it, and item 11 orders
the handle consolidation (`../2026-10-11-handles/README.md`).

**Verdict: flat.** The range adds tooling and no per-scenario structure.

## 2026-10-11 15:40, R2 committed

Range `a9e7a8551..6c4bb709d`: three commits, a fast-forward. Under `Laws` and `Dogfood` the
range adds 7,962 lines and removes 4,021 in 109 files. Six new files hold 1,784 of the added
lines:

- the edit alphabet, `src/Effect4/Laws/Machine/Edits.lean` (329 lines);
- the driver's helpers as words, `EditWords.lean` (599) and `EditObserverWords.lean` (380);
- `FiberSumMessages.lean` (205), `Laws/Program/Guard/Messages.lean` (252) and `Eliminators.lean`
  (19).

Over the changed files, measured before and after by the script's patterns: shared-law uses
86 → 99, private case analyses 554 → 554, hand decision lifts 21 → 21.

- **The consolidation is item 10's alphabet.** Each driver helper has a word and an equation
  (`start_word`, `spawn_word`, `drain_word`, `exit_word`, `observer_word` and the rest).
  `Edits.run_preserves` lifts a fact per edit to every word. `Approximation`, `Ledger`,
  `MaskRuns`, `Handles` and the guard modules read the words.
- **Item 10's two open points are in Codex's open tree** (`codex/machine-fields`, uncommitted
  at 15:20): `MachineField` with its agreement relation, and one `RunMachine.dropToken`. The
  `observe` write is still spelled twice, in `Edit.apply` and in `applyFiberEdit`.
- `Laws/Machine/Clauses.lean` gains eight evaluator unfoldings (10 → 18). They are clause
  equations for R2's new step result, in the shared clause bank, not a private pass.
- `Laws/Machine/Handles.lean` gains `FiberEdit.keys`, a 49th hand support function, and per-edit
  facts (`fiberEdit_world`, `fiberEdits_minted`). The facts are item 11 step 7's shape. The
  support function is what item 11 step 3 generates.

**Verdict: improving in structure, flat in private analyses.** The net 3,941 lines include the
1,784 lines of the new shared alphabet. The replaced proofs keep their names.
