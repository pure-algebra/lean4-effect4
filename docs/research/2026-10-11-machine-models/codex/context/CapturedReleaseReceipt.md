# Captured release context checkpoint

## Merge condition

The newest 22:15 instruction authorizes this seat checkpoint before the primary landing.
The landing merges each new seat commit and waits for the ambient Typed migration.
The checkpoint does not close the original M5 load or Assembly claim.

## Placement

Concept: residual-program-typing, R4 and R9.
Role: preservation helper of the closed source typing claim.
Consumer: Body.release_typed's ambient migration and the actual source denotation producers.
The proof uses the existing ProgramArrow, finalizerR and onExitR composition.
It introduces no program representation, evaluator or stack judgment.
The host boundary remains unchanged.

## Source control

ReleaseAmbientBoundary uses scoped(provideService S 1(acquireRelease unit(service S))).
The source passes admission and has an empty requirement row.
The actual capture contains S; the actual previous map lacks S.
The actual releaseBody continuation produces releaseMasked at the release child.
The reader constructs PointTyped from that source, its checked environment and its empty argument stack.
The reader consumes the actual service denotation and the restoring region composition.
It retains service-table agreement and previous-map membership as explicit semantic premises.
It is neither a whole-history theorem nor an outside-runtime observation.

ReleaseAmbientBoundary.before.lean.txt retains the earlier rejected internal ambient demand.
Its prior successful check uses fcac7de73 plus the uncommitted ordinary-body argument transport.
That demand asks the previous map to satisfy the captured map's complete key row.
The concrete maps refute it.
The retained log is bounded source/control evidence, not a runtime equivalence claim.

## Internal domain correction

BodyCoverage retains the issued AmbientStackTyped policy at ordinary at_, acquireIn and release points.
The source bind and argument-birth producer issue that policy before body admission.
The mask and fork producers transport it through their actual child points.

ambientFiberPre removes the previous-map inclusion demand for release bodies.
The release's checked requirements are covered by its actual captured entry map.
ReleaseMaskAllowed requires the actual release mask to use false.
The compiler's releaseMasked producer already uses false.
The actual source reader proves the role premise, rather than assuming it.
Ordinary true-mask at_ bodies remain admitted.
The synthetic true-release role is refused by a checked control.

ambientFiberInput selects the actual previous key row only after the false release-mask answer.
It makes no restoration promise for a true release mask.
The reference evaluator may skip a true-mask body before its restoring frame exists.

## Composition

ambient_finalizer_guarantees carries distinct success and failure guarantees.
The failure guarantee is included in the success guarantee and in the entry row.
ambient_restore_finalizer_guarantees promises the previous map's keys on success.
Its failure promise is covered at both the pre-write and restored cuts.
ambient_onExit_restore_guarantees consumes the captured body's actual row.
It requires no inclusion between the complete captured and previous rows.

The three original common-row theorem statements remain unchanged.
Their proofs now instantiate the same distinct-guarantee laws.
PointTyped, BodyTyped, RegionTyped, CaptureTyped, fiberPre and TypedProg remain byte-identical to fcac7de73.
The unit getter rule remains unchanged.

## Files

- src/Effect4/Laws/Program/Typed/Residual.lean
- src/Effect4/Laws/Program/Typed/Context.lean
- src/Effect4/Laws/Program/Typed/Denotation.lean
- This receipt and its retained source readers, controls and measured logs.

Codegen.Types, the borrowed FramePath and older Assembly/LayerArm work stay outside this checkpoint.
Root imports, generated target families and behaviour gates remain coordinator-owned.

## Verification

The checks use one direct Lean process, one thread and warningAsError.
The dependency order is Residual, StackCertificates, Context, Terms, Arguments and Denotation.
ProviderSourceReader and ClosedProviderSourceReader retain their original statements.
ReleaseAmbientBoundary reads the actual compiled release producer and the restored source body.
CapturedReleaseArguments reads the actual acquisition/release checker and argument-birth transport.
The final axiom audit covers every changed source module and those direct readers.
The commands use the retained checked R2 dependency overlay and the seat source modules.
They do not certify a whole current-runtime build.

| Check | Seconds | Result |
| --- | ---: | --- |
| Residual | 26.74 | pass |
| StackCertificates | 33.20 | pass |
| Context | 17.92 | pass |
| Denotation.Terms | 26.61 | pass |
| Denotation.Arguments | 22.39 | pass |
| Denotation | 61.06 | pass |
| ProviderSourceReader | 17.60 | pass |
| ClosedProviderSourceReader | 29.43 | pass |
| ReleaseAmbientBoundary | 36.61 | pass |
| CapturedReleaseArguments | 11.19 | pass |
| CapturedReleaseAudit | 64.61 | pass |

The audit reports 1,353 declarations within [propext, Quot.sound].
It reports zero planned goals and zero declarations modulo planned goals.
The retained logs record every command's measured result.
Declaration-byte comparisons confirm the six unchanged unit definitions.
Header comparisons confirm the three unchanged common-row theorem statements.
git diff --check passes for the three changed source files.
The proof slice changes no executable source; behaviour gates remain due at the coordinated sweep.
The source diff adds 153 lines and removes 64 lines across three files.

## Remaining obligations

Body, LayerArm and Assembly still require the approved ambient source migration.
Foreign finalizer admission must retain the actual captured argument policy and requirement coverage.
The existing runtime relation must carry the actual current, saved and queued context coverage.
The false release-mask completion protocol needs its actual evaluator/frame consumer.
No conditional helper here closes those obligations by itself.

Base and head: fcac7de73, codex/symbolic-native-fold.
Primary ownership review observes a99b4d686 and the newest 22:15 instruction.
The landing at 8f1f3d1ac already carries fcac7de73; its outside-Typed changes remain outside this checkpoint.
