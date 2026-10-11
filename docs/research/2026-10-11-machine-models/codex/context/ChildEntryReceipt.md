# Ambient child entry checkpoint

The entry refinement compiles independently of the remaining M5 source migration.
Do not integrate the preserved Terms migration patch before Denotation and its direct consumers compile.

Base: `ab502ab63`, branch `codex/symbolic-native-fold`.

## Placement and reach

Concept: residual-program-typing, R4 and R9.
Role: preservation dependency of `typed-state-reachable`.
Consumer: the existing source denotation induction and actual current, saved and queued context positions.
Decisions rows 117 and 349 bound the source and load claims.
The approved success and failure service guarantees bound the ambient entry contract.
The original closed M5 and Assembly claim headers remain the acceptance target.

`ambientFiberPre` retains the existing checked point, body and cursor evidence.
Its code-bearing entries additionally require the certificate's required row inside the actual available row.
Each race entrant retains the same checked point witness with its required-row inclusion.
An acquire body additionally requires its captured context to satisfy the actual available row.
A release body additionally requires its previous context to satisfy the actual available row it restores.
Service declarations in a world do not supply either context satisfaction premise.
`ambientFiberPre_mono` uses the existing point, body, loop and world transport laws.
Captured context satisfaction stays unchanged during this world transport.

The unit `fiberPre`, `BodyTyped` and `CaptureTyped` definitions remain unchanged.
The change adds no source representation, world, evaluator, history pass or planned goal.
Foreign finalizer captures still need their ambient hook at the actual installed context.
This checkpoint does not establish that hook or full machine context preservation.

## Actual control and readers

`ForkReaderEntry.lean` uses the actual checked child of an authored fork and typed context reader.
The existing unit body and fiber preconditions hold at that child.
The child's required row does not fit an empty available row.
An empty context does not satisfy that required row.
The refined ambient fork precondition refuses the empty row and accepts the covered row.
The existing admitted closed service provider and native reader pass again.
Its native result remains a finite kernel-checked evaluation.
No outside implementation comparison is claimed.

## Preserved source migration

`TermsMigration.wip.patch` preserves the current source migration.
The existing point and term prefix moves once to `Typed/Denotation/Terms.lean`.
The six existing source leaf declarations retain their names and use `AmbientProg`.
The existing `ChildDenotes` retains its point witness and adds actual required-row inclusion.
The existing bind uses the shared guard arrow and the actual callback's completed view.
It transports the actual environment and parameters to the future world.
The original Denotation file imports Terms and removes the moved declarations.
The patch also contains five drafted region-entry arms.
Those five drafts and the remaining Denotation module have not passed a complete check.
The extracted Terms module has passed its check and audit.
The patch remains research evidence rather than a source landing.
No second exported source theorem family lands in this checkpoint.

## Checks

A single direct Lean process runs at a time with `LEAN_NUM_THREADS=1`.
A copy-on-write artifact overlay avoids a dependency build cascade during concurrent host pressure.
The overlay begins with the existing worktree's checked `Effect4` artifacts.
Each changed output replaces its predecessor in dependency order.

```sh
cp -c -R .lake/build/lib/lean/Effect4/. /private/tmp/context-entry-lib/Effect4
contextEntryLeanPath="$(lake env printenv LEAN_PATH)"
LEAN_PATH="/private/tmp/context-entry-lib:$contextEntryLeanPath" LEAN_NUM_THREADS=1 lean -DwarningAsError=true -o /private/tmp/context-entry-lib/Effect4/Laws/Program/Typed/Residual.olean src/Effect4/Laws/Program/Typed/Residual.lean
```

The same direct command checks Context and the preserved Terms output.
The Scheduler command additionally uses `--root=src`.
The direct reader commands check ForkReaderEntry and ClosedProviderSourceReader.
The audit imports Scheduler and the checked Terms output.
It audits Contracts, Residual, Seq, Context, Scheduler and Denotation.Terms together.

Residual passes without messages.
Context passes in 11.31 seconds.
ForkReaderEntry passes in 14.54 seconds.
Terms passes in 28.47 seconds.
Scheduler passes in 13.34 seconds.
The combined audit passes in 14.06 seconds.
It reports 978 declarations within `[propext, Quot.sound]`, zero planned goals and zero modulo declarations.
The initial Lake attempt fails on a dependent operation certificate spelling.
The repaired direct check spells the existing point and body premises at their actual constructors.
The fallback world transport uses the generated protocol equation.
No proof premise changes to make that failed spelling pass.

Logs: `/private/tmp/context-entry-{residual,context,terms,scheduler}-direct.log`, `/private/tmp/context-fork-entry-direct.log`, `/private/tmp/context-entry-audit.log`.
The final closed-reader log is `/private/tmp/context-entry-closed-reader.log`.
No broader Lake cascade, whole Laws build or behavior gate runs for this proof-only checkpoint.
