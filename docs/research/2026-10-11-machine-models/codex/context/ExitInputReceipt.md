# Context completion input review receipt

Review the proposed shared signature before applying its change.
The implementation still uses one completion input per object.

Base and head: `e4e1f6814`, branch `codex/symbolic-native-fold`.
Proposal: `ExitInputProposal.md`.
Independent control: `ExitDemandProbe.lean`.
Evidence status: checked local runtime control; proposed shared signature.
Proof role: dependency of `typed-state-reachable` preservation, R4 and R9.
Scope: decisions rows 117 and 349; actual service membership and phase capability lower bounds.

## Checks

The independent probe imports only `Effect4.Program.Compile`.
It checks the missing Scope key at the empty entry row.
It reads the actual context setter and deferred-interruption branch.
Run:

```sh
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/ExitDemandProbe.lean
```

Result: pass, with no output.
This control is not an admitted-history counterexample or a progress theorem.

The staged direct setter consumer and its failure-demand control compile separately.
The staged source reader, provider entry and captured-context frame consumers compile.
The shared helper graph builds with the original Stack and Adequacy consumers: 473 jobs.

The staged audit imports those consumers and runs:

```lean
#axiom_audit Effect4.Laws.Contracts.FramePath
  Effect4.Laws.Program.Typed.Contracts Effect4.Laws.Program.Typed.Membership
  Effect4.Laws.Program.Typed.Residual Effect4.Laws.Program.Typed.Seq
  Effect4.Laws.Program.Typed.Context Effect4.Laws.Program.ExpandFix
```

Result: 1,281 declarations within `[propext, Quot.sound]`.
The audit reports zero planned goals and zero declarations modulo planned goals.
These staged source files are not part of this research-only checkpoint.

## Shared structure and pending review

The staged `FrameArrow` generalizes the existing frame relation by its input type.
The staged `ProgramArrow` generalizes the existing residual relation by its input type.
The old type-only judgments are unit-input aliases of those same relations.
There is no parallel program representation or evaluator.
The world transport and program closing cases occur once in the shared relations.

The proposed additional exit-dependent input projection remains unapplied.
Automatic approval review rejects that interface mutation pending explicit signature review.
The coordinator requests this concrete proposal and submits it for owner review.
No failure coverage follows merely from a setter's future successful completion row.
The original typed endpoints remain unfinished until actual phase coverage transports through their existing relations.

The context region uses the existing `StackRegion` and `MaskBracket` structure.
The target context projection remains centrally refused until signature-aware target migration.
No behavior gate runs in this research checkpoint.
