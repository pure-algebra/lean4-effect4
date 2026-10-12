# Provider source relation checkpoint

The original code_intro source relation compiles against the paired masked provider construction.
M5 ambient typing and the existing closed Assembly claims remain open.
Integrate this commit after c2a1cdda4 and its prerequisite source chain.

Base: c2a1cdda4 on codex/symbolic-native-fold.
Concept: residual-program-typing; requirements R4 and R9; role: preservation dependency.
Consumer: the original closed M5 and Assembly claims.
Concept: scope-lifetime-finalization; requirement R11; role: preservation dependency.
Consumer: the existing provider source arm and the shared region instance.
Rows 117 and 349 and the approved success/failure service guarantees bound this migration.
No new goal, source assumption or program representation is added.

## Changes

Intro.Region factors its existing restoring-finalizer proof into restoreContext_intro.
The original region_intro header remains an adapter.
restoreRegion_intro and contextEntry_intro use the existing mask and context actions.
updateContext_intro consumes the actual Region body meaning.
Intro.Memo and Intro.Layer expose actual addressed layer builds instead of arbitrary build functions.
Intro.Scope supplies the actual source child certificates.
The original code_intro header remains unchanged and covers the complete source constructor domain.

Changed library paths are Intro/Region.lean, Intro/Memo.lean, Intro/Layer.lean and Intro/Scope.lean.
The paired helper-domain changes remain documented in ProviderPairedReceipt.md.
No machine source or runtime action changes here.

## Checks

Checks use one direct Lean process, one thread and warnings as errors.
The artifact overlay borrows the coordinator's checked R2 dependencies.
Borrowed changes stay outside this commit.
The existing compileEff_provideContext source clause comes from the prerequisite context source checkpoint.

| Module or reader | Result | Seconds |
| --- | --- | --- |
| Intro.Region | passes | 8.31 |
| Intro.Memo | passes | 3.98 |
| Intro.Layer | passes | 5.42 |
| Intro.Scope | passes | 2.60 |
| original Intro endpoint | passes | 5.08 |
| Means dependency | passes | 4.65 |
| actual source reader | passes | 5.59 |
| combined axiom audit | passes | 4.13 |

ProviderSourceAgreementReader.lean applies code_intro to an actual provider with a yield body.
Its second reader keeps fuel symbolic.
The audit reports 448 declarations within [propext, Quot.sound], zero goals and zero modulo declarations.
ProviderSourceAgreementAudit.log retains the audit output.
These are checked source relations, not an outside runtime comparison or a whole-Laws result.

## Remaining work

Ambient Body and admission need the actual supplied service and body-entry certificates.
Denotation and its real direct consumers must compile before the context chain integrates.
The provider restoration claim must instantiate existing MaskBracket and StackRegionRun.
The whole Laws and reached behavior gates remain owed.
