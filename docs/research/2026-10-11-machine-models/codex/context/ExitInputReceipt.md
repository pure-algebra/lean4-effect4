# Context completion input review receipt

The owner approves the proposed shared signature.
The approval selects success and failure service guarantees.
The shared arrows now select their input from the actual delivered exit.

Base and head: `e4e1f6814`, branch `codex/symbolic-native-fold`.
Proposal: `ExitInputProposal.md`.
Independent control: `ExitDemandProbe.lean`.
Evidence status: checked local runtime control; owner-approved shared signature.
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

## Shared structure and owner approval

The staged `FrameArrow` generalizes the existing frame relation by its input type.
The staged `ProgramArrow` generalizes the existing residual relation by its input type.
The old type-only judgments are unit-input aliases of those same relations.
There is no parallel program representation or evaluator.
The world transport and program closing cases occur once in the shared relations.

The approved exit-dependent input projection now compiles in the shared arrows.
Automatic approval review earlier refuses that interface mutation pending explicit signature review.
The owner now supplies that explicit approval.
The owner selects “Approve success/failure service guarantees (Recommended)”.
This approval permits the shared `Object → ExitV → Input` projection.
It retains actual-cut interruption coverage and unchanged unit-input judgments.
No failure coverage follows merely from a setter's future successful completion row.
The original typed endpoints remain unfinished until actual phase coverage transports through their existing relations.

The context region uses the existing `StackRegion` and `MaskBracket` structure.
The target context projection remains centrally refused until signature-aware target migration.
No behavior gate runs in this research checkpoint.

## Checked shared signature checkpoint

Base: `8345cc9ff` before this dependency checkpoint.
The signature is `Object → ExitV → Input` in `FrameArrow` and `ProgramArrow`.
The unit-input type judgments retain their statements and their execution path.
`AmbientPosition` carries the type, guaranteed success row and guaranteed failure row.
`ambientInput` selects the row through the existing `Exit.isSuccess` projection.
`AmbientExit` requires that selected row below the actual available row.

Changed source files:

- `src/Effect4/Laws/Program/Typed/Contracts.lean`
- `src/Effect4/Laws/Program/Typed/Residual.lean`
- `src/Effect4/Laws/Program/Typed/Seq.lean`
- `src/Effect4/Laws/Program/Typed/Membership.lean`
- `src/Effect4/Laws/Program/Typed/Context.lean`
- `src/Effect4/Laws/Program/ExpandFix.lean`

Dependency: the coordinator's shared `Contracts.FramePath` extraction at `232b1baec`.
The coordinator's `Codegen.Types` refusal remains outside this checkpoint.
No runtime module changes in this checkpoint.

Run:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.Context Effect4.Laws.Program.Typed.Stack Effect4.Laws.Program.Typed.Adequacy
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true docs/research/2026-10-11-machine-models/codex/context/ExitDemandConsumer.lean
```

Result: 472 build jobs pass; the consumer passes with no output.
The original Stack and Adequacy consumers compile with their unit-input statements.
The combined audit covers the six changed modules, Stack and Adequacy.
Result: 1,582 declarations within `[propext, Quot.sound]`, zero goals and zero modulo declarations.

The direct setter consumer distinguishes successful and failed completion demands.
The failure control rejects supplied-key coverage before the setter runs.
A synthetic setter can remove entry services after it runs.
Therefore the current-code invariant must carry actual-cut failure coverage separately.
The source provider merges services, which supplies that coverage through its real producer.
The source reader and provider entry use declared carrier membership, not key presence alone.

The existing runtime typing relation still needs its ambient position instance.
The provider restoration still needs the compiled region instance.
This checkpoint does not establish the original reachable typing endpoint.
No behavior gate runs in this proof dependency checkpoint.
