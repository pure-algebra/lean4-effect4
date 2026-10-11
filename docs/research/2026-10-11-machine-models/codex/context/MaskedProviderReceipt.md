# Current-runtime masked provider evidence

The candidate closes the retained restoration gap at the current R2 runtime.
Only temporary compiler copies run; production Compile and DenoteR stay unchanged.
The reference and M5 migration remain open.
Apply the candidate delta only after the checked context source and existing R2 compiler arity updates.
The delta excludes those three borrowed arity updates.

Base: 33ea7abeb on codex/symbolic-native-fold.
Runtime artifacts: root 6eb40cccd, copied from its entire Machine namespace.
The later root 1591530e9 keeps the same Fibers source at the check.
MaskedProviderEntry.md records the approved paired equations, payloads and changed internal helper reach.
RegionEntryReceipt.md retains the earlier runtime's results separately.

## Placement and reach

Concept: scope-lifetime-finalization; requirement R11; role: preservation control.
Consumer: the approved provider region through existing MaskBracket and StackRegionRun instances.
Concept: residual-program-typing; requirements R4 and R9; role: preservation dependency.
Consumer: the ambient source arm and the original closed M5 and Assembly claims.
Rows 117 and 349 and the approved success/failure service guarantees bound those claims.

The evidence is finite native command execution and symbolic compiler equations.
The body-mask controls use admitted source interruptible and uninterruptible wrappers.
The prefixes do not establish a public HistoryOf derivation or an outside implementation comparison.
The artifact overlay combines checked context-source modules with the current Machine namespace.
It is not a complete integration build of the source and Laws graphs.

## Paired controls

The unchanged compiler still leaves the service installed at interruption cuts six and seven.
Its cut eight includes the restoring context write.
The current runtime reproduces the earlier gap independently.

The masked candidate records no context write at pre-entry cuts two, three and four.
Cut three retains the capture getter's own restoring-slot boundary.
At internal masked cut eight, interruption completes installation and finalizer placement before it reaches the body.
The resulting trace records one installation and one restoration.
At cut ten, the live fiber physically holds the installed service.
Interruption there records exactly one restoration after installation.

The survey checks command-prefix fuels zero through twenty-five.
It contains no isolated restoration write before installation.
The completed body continuation returns savedMask true under the interruptible wrapper.
It returns savedMask false under the uninterruptible wrapper.
Both completed controls record one installation and one restoration.
These controls use a synchronous body to reach completion without a dispatcher flush.
The interruption control retains the original yielding body.

## Checks

One direct Lean process runs with one thread and warnings as errors.
The compiler output goes to its separate copy-on-write artifact overlay.
The candidate and baseline overlays must not be imported together.
They implement different temporary meanings of the same compiler module.

| Check | Result | Seconds |
| --- | --- | --- |
| Temporary masked Compile | passes | 16.87 |
| Current-runtime baseline Compile | passes | 34.42 |
| Baseline survey | passes | 5.35 |
| Baseline kernel controls | passes | 6.32 |
| Masked equations and kernel controls | passes | 12.28 |
| Baseline Compile and control audit | passes | 5.17 |
| Masked Compile and control audit | passes | 6.90 |

The baseline audit reports 1,166 declarations within [propext, Quot.sound], zero goals and zero modulo declarations.
The masked audit reports 1,202 declarations within [propext, Quot.sound], zero goals and zero modulo declarations.
The retained audit logs give the exact commands' output.
No behavior gate or whole-library build runs in this evidence checkpoint.

The temporary compiler's first current-runtime check finds three old five-field Iter literals.
The next check uses the coordinator's existing sixth-field updates and passes.
The first survey finds two fixture spelling errors; the corrected source passes.
An initial audit search path shadows Compile with a source-only directory.
The corrected separate probe path passes the audit.
These failed attempts establish no theorem or finite control.

## Reproduction

Build the temporary baseline from the context-source Compile and the three existing R2 Iter field updates.
Apply ProviderMaskedCandidate.patch only to a separate copy of that baseline.
Use the checked current Machine artifacts for both copies.
Compile ProviderBaselineR2Control.lean against the baseline copy.
Compile ProviderMaskedCandidate.lean against the candidate copy.
Audit Compile and each control in its own overlay.

The compiler command uses --root at its temporary source directory and writes the matching overlay's Compile.olean.
The control command uses the same overlay first in LEAN_PATH.
The audit adds a separate directory containing only its control olean before that overlay.
Each command uses the pinned Lean 4.33.1 executable and -DwarningAsError=true.

## Runtime hashes

The current Fibers source SHA-256 is:
090844e028492f04809d292eff691628ec8ac01dfd67b6d12050e67cb56f97fa.
Its imported olean SHA-256 is:
a4d40bc5dcffcb4b7f35cac0699ce79767f33d84e0cea8126af9763a1de69615.
The root artifact and the imported artifact match exactly.
The imported Frames olean SHA-256 is:
93b52cf99dfad038e560693174792c0ef5f7c786a4565df3f0b69e2a3a167f29.
The imported Stores olean SHA-256 is:
0e4334126d1ac6030ac5816342156f4bee201b94d64b248129760065f5a67330.
The candidate Compile source SHA-256 is:
91c69f9492792ca98605f5b58e0a55a4bcea68a82e2ae5d9fdca47b2e90a21d2.
The baseline Compile source SHA-256 is:
a1774f38a23fb08ae44feb87d229e4a15b9a9c521f348c354d7b995a2633291b.

## Remaining migration

The approved reference updateContextR parameter changes from RProgram to existing Region data.
Sched.Body receives region and contextEntry names; it stores no function or semantic program.
The existing body hooks consume one generated Region fold.
The fold imports Compile at the Laws boundary because Compile is a legacy non-module specialization.
The generator reuses the existing Program.MonadMorphism explicitly and refuses a missing declaration.
The original generated families must remain byte-identical.

The coherent source/reference producer and actual ambient M5 consumers still need migration and checking.
The provider bracket remains an instance of shared region laws.
This finite evidence does not replace that proof.

## Exact direct commands

```sh
contextMaskPath="$(lake env printenv LEAN_PATH)"
LEAN_PATH="/private/tmp/provider-masked-r2-lib:$contextMaskPath" LEAN_NUM_THREADS=1 /usr/bin/time -p /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --root=/private/tmp/provider-masked-source -DwarningAsError=true -o /private/tmp/provider-masked-r2-lib/Effect4/Program/Compile.olean /private/tmp/provider-masked-source/Effect4/Program/Compile.lean
LEAN_PATH="/private/tmp/provider-masked-r2-lib:$contextMaskPath" LEAN_NUM_THREADS=1 /usr/bin/time -p /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --root=/private/tmp/provider-masked-source -DwarningAsError=true -o /private/tmp/provider-masked-source/ProviderMaskedCandidate.olean /private/tmp/provider-masked-source/ProviderMaskedCandidate.lean
LEAN_PATH="/private/tmp/provider-masked-probe-lib:/private/tmp/provider-masked-r2-lib:$contextMaskPath" LEAN_NUM_THREADS=1 /usr/bin/time -p /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --root=/private/tmp/provider-masked-source -DwarningAsError=true /private/tmp/provider-masked-source/ProviderMaskedAudit.lean
LEAN_PATH="/private/tmp/provider-baseline-r2-lib:$contextMaskPath" LEAN_NUM_THREADS=1 /usr/bin/time -p /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --root=/private/tmp/provider-baseline-r2-source -DwarningAsError=true -o /private/tmp/provider-baseline-r2-lib/Effect4/Program/Compile.olean /private/tmp/provider-baseline-r2-source/Effect4/Program/Compile.lean
LEAN_PATH="/private/tmp/provider-baseline-r2-lib:$contextMaskPath" LEAN_NUM_THREADS=1 /usr/bin/time -p /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --root=/private/tmp/provider-baseline-r2-source -DwarningAsError=true -o /private/tmp/provider-baseline-r2-source/ProviderBaselineR2Control.olean /private/tmp/provider-baseline-r2-source/ProviderBaselineR2Control.lean
LEAN_PATH="/private/tmp/provider-baseline-r2-probe-lib:/private/tmp/provider-baseline-r2-lib:$contextMaskPath" LEAN_NUM_THREADS=1 /usr/bin/time -p /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean --root=/private/tmp/provider-baseline-r2-source -DwarningAsError=true /private/tmp/provider-baseline-r2-source/ProviderBaselineR2Audit.lean
```
