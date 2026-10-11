# Symbolic crew programs receipt

The symbolic job-count obstacle is resolved without restricting the job count or changing program behaviour.
The two static acquisition facts are proved for every job count and every successful build.
The release-count and queue invariants remain open.

Base: `7719b68b`, with Workers neutral extraction `c92d43b1` cherry-picked as `cff2df507`.
Branch: `codex/symbolic-programs`.

Changed files:

- `src/Effect4/Laws/Program/Placement.lean`: the packet's static path predicates.
- `Test/Dogfood/Scenario/Programs.lean`: universal source, module, build and acquisition equations.
- `Test/Dogfood/Scenario/QueueWorkers/Program.lean`: unchanged queue-crew program definitions.
- `Test/Dogfood/Scenario/QueueWorkers.lean`: imports its neutral program module.
- `docs/research/2026-10-10-goals-packet/codex/SymbolicPrograms.lean`: compiled readers, a loop-path control and the audit.

## Placement and reach

`workers_main_some`, `queue_main_some`, both main equations, both reference facts, both module equations and both built-program equations serve R10.
Their concept is `translation-simulation`.
Their consumers are the two crews' static acquisition facts.
`workers_acquisition_sites` and `queue_acquisition_sites` serve the release bridges.
`workers_placement`, `queue_placement` and both built acquisition facts serve the control-linearity assemblies.
Their concept is `scope-lifetime-finalization`, R11.
Decisions rows 254 and 275 bound these scenario fragments.

The source and module equations quantify over every natural job count.
The built-program equations require successful `Author.build` admission.
The acquisition facts use the packet's original paths and `OncePlaced` predicate.
The node-kind facts separately establish that those paths address `acquireRelease` nodes.
The loop-path control rejects a queue operation inside worker 2's loop, at every job count.

No fact establishes an execution count, progress, a store invariant, finalization or a host observation.
`OncePlaced` is a syntax predicate. Its runtime reading still needs control linearity.
The source-tree fallback is excluded by the proved successful main elaboration.
No theorem rests on a planned goal.

## Route

Close the declared row scope before elaborating the source.
Prove that the resulting tree contains no layer reference.
Apply `Author.elaborateModule_no_declarations` to avoid repeating the reference traversal.
Apply `Author.build_retains` to identify a successful build's stored tree.
Read the acquisition paths from that tree.

This route uses the existing program carrier and the generated node traversal.
It changes no elaborator or core program behaviour.

## Commands and results

- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Workers Test.Dogfood.Scenario.QueueWorkers ProofGraph.AxiomAudit`: passes, 1034 jobs.
- `LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Placement`: passes in the narrow helper build.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.QueueWorkers.Program`: passes, 1024 jobs.
- `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Programs Test.Dogfood.Scenario.QueueWorkers`: passes, 1035 jobs, measured real 32.68 seconds.
- Final `LEAN_NUM_THREADS=3 lake build Test.Dogfood.Scenario.Programs`: passes, 1030 jobs, measured real 4.67 seconds.
- `LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-10-goals-packet/codex/SymbolicPrograms.lean`: passes, measured real 2.26 seconds.
- `#axiom_audit Effect4.Laws.Program.Placement Test.Dogfood.Scenario.Programs Test.Dogfood.Scenario.QueueWorkers.Program`: 99 declarations within `[propext, Quot.sound]`, zero modulo goals, zero goals.
- `git diff --check`: passes.
- Python compares the moved source bytes and every other scenario byte: unchanged, except the new import and removed source block.

The moved source block's SHA256 is `6b45d7a84b3bfd642a2294c7f18a8f4f4e68dbf37b528f81244ad74ba72d9592`.
The largest measured job counts above include restored inputs and are not new proof counts.

## Inconclusive earlier checks

The original `queue-run/scratch/StuckFix.lean` check is interrupted after measured real 118.89 seconds without a verdict.
A direct whole-module kernel equation is interrupted after measured real 141.24 seconds without a verdict.
Neither attempt is a counterexample or a checked failure of the proposed equation.
The staged saved proofs replace those attempts.

## Deferred gates and open work

The coordinator adds the law-root import for `Effect4.Laws.Program.Placement`.
The coordinator adds the test-root import for `Test.Dogfood.Scenario.Programs`.
The neutral queue source is reached through the existing QueueWorkers scenario import.
No root import, lakefile or decisions register changes in this landing.
No external behaviour gate runs: the source definitions and program behaviour stay identical.
The final coordinator pass checks root closure and the shared tactic's implementation exemption.
Release accounting, queue command-boundary invariants and the original scenario goals remain open.
No push occurs.
