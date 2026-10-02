# A3: fallback-arm measurement preparation

Read-only source review at `8c9be2588332d9f9094c5a6ecd7d9e3af8a0ac55`.
Toolchain API review: local Lean v4.33.1 source. No compiler was run by this reviewer.

## Delivered

- `measure.py`: reads two source blobs at the exact revision, finds every occurrence of the
  five family names under `src`, `tools`, and `Test`, writes the census and isolated copies.
- `census.json`, `table.md`, `all-sites.git-grep.txt`: **measured static** arms and occurrences.
- `sources/`: exact original blobs, with SHA-256 hashes in `census.json`.
- `baseline/` and `instrumented/`: proposed full-source measurement inputs. Both have an
  identical inline logger and theorem fingerprint footer. The instrumented versions only
  add a wrapper around the existing 22 macro arms, preserving their order and tactic bodies.
- `A3Instrumentation.lean`: the logger source, also usable as a standalone helper if desired.
- `HashReport.lean.txt`: the common footer.
- `Controls.lean`: proposed small positive, rejecting, enclosing-rollback, later-goal-rollback,
  partial-success and nested-family controls. Uncompiled. They predict seven retained messages;
  no predicted number is a measured result.

The census found **five families, 22 direct arms, nine proof call sites, and three nested-family
call sites**. It found no uses of those names outside the two modules. Dynamic selection counts
remain `null` until the coordinator compiles the isolated inputs.

## Why ordinary traces are unsuitable for selected-arm totals

In local Lean source, `Lean/Elab/Tactic/BuiltinTactic.lean:622–632` evaluates `first` through
`<|>`. `Lean/Elab/Tactic/Basic.lean:377–381,435–442` connects its exception handling to saved
state restoration. `Lean/CoreM.lean:409–412` restores `messages`. In contrast,
`Lean/Elab/Term/TermElabM.lean:421–425` explicitly preserves trace state across restoration.
An ordinary trace can therefore contain successful attempts from a discarded enclosing branch.

The proposed wrapper calls the same `evalTactic body`, then `logInfo`, without adding a `done`
check, changing goal order, catching failures, or changing arm priority. Its info message is
discarded with an enclosing failed branch. It never writes a global counter. Successful return
is not by itself a proof that every goal was solved; the partial-success control makes that
distinction explicit. This is a source-grounded design awaiting the coordinator's compiler check.

API locations: `Term.getDeclName?` at `Lean/Elab/Term/TermElabM.lean:685`;
`getRefPosition` at `Lean/Log.lean:51`; `evalTactic` at `Lean/Elab/Tactic/Basic.lean:191`.
The logged declaration identifies the original theorem. The logged line/column is the macro's
current syntax reference in the temporary source, which must not be advertised as an original
source line without checking the mapping. `census.json` supplies exact original arm and call lines.

## Wrappers that make speculative work matter

- `Approximation.lean:308–320`, `trace_chain`: the hop can succeed and its following recursive
  chain can fail, discarding the complete transitive branch. `trace_leaf` at 297–306 has its own
  `try` and `first`, whose success may leave a goal for that chain.
- `Scheduling.lean:51–61`, `queue_chain`: the same issue, multiplied by `all_goals`.
  `queue_leaf` at 42–49 uses splitting and per-goal `first`.
- Outer `first` at Approximation 501–503, 510–516, 572–575, and 728–732, and Scheduling
  202–204, 219–225, and 276–279, places the chains after other candidate solutions.
- Scheduling 279 additionally passes a **six-arm inline `first`** to `queue_chain`:
  drain, `queue_hops`, launch, exit, observer, settle. `queue_hops` selection does not count the
  other five inline arms. It needs its own instrumentation only if the requested scope expands.
- `hops_loop → hops_cmd → hops_observers → hops_leaf` produces overlapping parent/child
  selections. Keep a separate table for each family; never add these counts as distinct hops.
- `repeat' split`, `<;>` and `all_goals` mean one textual call can execute many times.

If later measuring search effort, instrument attempts and outcomes separately with a dedicated
trace class / `withTraceNode` (`Lean/Util/Trace.lean:332–360`) and report them as attempted local
outcomes. Do not substitute those totals for selected-arm counts.

## Coordinator execution conditions

Compile baseline and instrumented copies sequentially with one thread, bounded memory and time,
using the existing artifacts only after verifying that their source revisions match the reviewed
upstream dependencies. Never emit artifacts into the active repository. No generator is required.
The expected limit is two bounded compiles per source file; a harness defect justifies a repair.

Use the same temporary input path / module name for each baseline–instrumented pair, copying
the prepared file into it between runs, to avoid private declaration names differing only because
the filenames differ. The files do not need a separate helper build. The current source artifact
for the original module is not imported by its copy. Scheduling still imports its original
upstream Approximation artifact, as authorized by the coordinator.

Compare successful exit, the exact theorem-name set, count, and each type/value `Expr.hash`
pair from `A3_PROOF` lines. `env.getModuleIdxFor? name = none` filters the footer to current-file
declarations; it includes generated local theorem declarations. `Expr.hash` is a 64-bit
fingerprint (`Lean/Expr.lean:537`) and matching hashes are a finite check, not a theorem of equality.
Investigate mismatches; do not normalize away a changed proof silently. Logging adds elaboration
work, so resource-limit differences are possible even though the same tactic bodies run.

Count only final retained `A3_RETAINED` messages after a successful file compilation. Keep
declaration, family and arm columns. Exclude the `control`, `parent` and `child` families if the
small controls are incorporated into either full-source input. Zero selections at this revision
are evidence about these declarations only, not proof that an arm is universally redundant.
