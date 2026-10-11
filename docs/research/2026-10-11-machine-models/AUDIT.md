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
