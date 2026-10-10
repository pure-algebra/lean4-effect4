# Step 2b target follow-up

Check the newly generated `pDefsModuleLayer` module without changing the implementation worktree.

## Completion criteria

Check the generated module with pinned tsgo 7.
Run its definition and main program against the pinned Effect runtime.
Record the imported input hashes before and after the commands.
Retain the reviewed commit and the limits of each observation.

## Placement

1. Concept: `translation-simulation`, the generated program's execution observation.
2. Question: the finite runtime evidence beside `module-defs-round-trip`, whose proof establishes reconstruction only.
   The probe proposes no theorem and changes no registry claim.
3. Reach: `moduleLayerProg` in `Test/Program/DefinitionsControls.lean`, printed as `pDefsModuleLayer`.
   Its definition and main program name the same module layer under decisions row 341.
   Observe the successful value under synchronous and asynchronous execution.
4. Limits: this check proves no universal execution law, schedule equality, memo sharing count, or source-admission result.
   The Lean result is the owner's recorded evaluation, not a fresh Lean run in this follow-up.
5. Requirement: R3, the finite comparison with the Effect runtime.
   This evidence does not discharge the separate proof audit finding.

## Reviewed state

The implementation base remains `1c98dd94831c060e591cd7e5bef19d6528c5d22a`.
The work remains uncommitted at the recorded source comparison.
The primary head remains `e9d6863eed613a40fe90444925daf5e3bec818c5`.
Claude owns the `module-layers` worktree and prepares the separate live-view slice.
The review leaves both implementation paths unchanged.

## Results

Evidence kind: independent finite target compilation and execution.
The run starts at `2026-10-10T19:16:43.683685+00:00`.
The generated module passes `tsgo 7.0.0-dev.20260629.1` with the truth harness's strict options.
Effect `4.0.0-rc.112` runs under Bun `1.4.2`.
The definition returns `7` synchronously.
The main program returns `7` both synchronously and asynchronously.
Every recorded input remains unchanged during these commands.
The exact commands and hashes are in [result.json](result.json).

## Proof repair

Evidence kind: exact source comparison with the independently compiled and audited candidate.
`moduleLayersOf_split` in `src/Effect4/Laws/Codegen/Module.lean` now uses the verified constructive proof.
That source file matches the candidate byte for byte.
Its direct consumer, `Laws/Api/ModuleReadable.lean`, also matches.
Of 176 original imported law sources, only the repaired module changes.
The patch passes `git apply --reverse --check`, confirming that its change is already present.
This follow-up runs no new Lean build.
The earlier candidate's audit remains the proof evidence for these exact sources.
ML2B-TRUST-01 is repaired in the working tree, not yet recorded as a committed landing.

The owner also corrects the semantics property and registry text.
They distinguish a definition body's own layer from its reference to a module layer.
The finite execution checks remain separate from the reconstruction theorem.

## Owner gate evidence

The retained log reports the truth comparison passing.
The first target run fails because the new fixture occupies different positions in two ordered inventories.
The owner aligns those positions and the subsequent target and reader command exits with status zero.
These are observed owner logs, not independently rerun gates.
They do not establish that every printed module is accepted by the source reader.
The new definition call still receives the existing `unknownHead readKey` refusal in the reader corpus without its oracle.

## Next action

Keep the applied proof repair and the corrected fixture order.
Commit the implementation after its affected checks finish.
Keep TypeScript acceptance, runtime observations, and source-reader admission as separate evidence.

## Compatibility check resolution

The [compatibility follow-up](compatibility/README.md) verifies the separate repair for ML2-C2-01.
The saved text-tag counterexample is now refused, while the authorized field addition remains accepted.
The repair is in the working tree and not yet recorded as a committed landing.
