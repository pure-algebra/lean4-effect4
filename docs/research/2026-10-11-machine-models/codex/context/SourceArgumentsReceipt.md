# Checked source argument transport

The complete Denotation module passes its direct check and audit.
The Body, LayerArm, and Assembly consumers still require ambient migration.
Do not treat this checkpoint as the closed M5 load acceptance.

## Placement

Concept: residual-program-typing.
Requirement: R4.
Claim: denote-typed.
Role: preservation.
Consumer: the original closed M5 load, through source Denotation, Body, and Assembly.
Decisions rows 117 and 349 and the recorded success/failure guarantees bound the source domain.

## Actual producer and consumer

argument_certificates factors the existing argument-site proof through one certificate policy.
The proof reads the actual checkEffs verdict and argument spine.
The head uses Row.subset_union_left.
The tail composes its bound with Row.subset_union_right.
ambient_argument_birth records that bound in the same StackCertificates fold.
The old private argSites_typed statement remains a unit adapter.

invoke_arm uses the actual invocation verdict and DefDecl.admits body requirement.
It issues the ambient argument certificate before entering the definition body.
param_arm reads the saved certificate at the actual parameter index.
It retains the argument requirement bound and transports value membership through the actual later-world order.
hop_typed consumes that bound at the checked target point.
No service declaration alone supplies runtime coverage.

ChildDenotes retains PointTyped and also takes the existing ambient stack-fold certificate.
The closed empty-scope entry discharges that certificate with ambientStackTyped_nil.
Recursive bind, suspend, selector, handler, and finalizer arms transport the same captured stack.
PointTyped retains its exact definition and public type.
StackTyped retains the previously checked unit meaning and public type.

## Source statement inventory

The following source-specific helpers change from unit program output to the approved ambient input/output, or retain its argument certificate.
Their actual callers must supply checker requirements, installed-map coverage, and captured argument evidence.
Generic unit ProgramArrow, FrameArrow, PointTyped, and StackTyped interfaces remain unchanged.

ChildDenotes previously returns TypedProg from a typed point alone.
It now takes available, checked requirement inclusion, and AmbientStackTyped, then returns AmbientProg at that row.
ProvideLayerArm and childDenotes_upto gain the same ambient completion and stack input.
The new provideContext_arm also uses the actual supplied context membership and installed-map coverage.
hop_typed replaces its unit stack premise with the shared ambient policy and takes its checked requirement bound.
param_arm retains its original point premise and consumes the ambient policy at the actual saved-frame pop.
invoke_arm retains its original point premise and derives its new stack annotation from the actual argument verdict.
The old type-only DenotesTyped packaging in Assembly has not yet migrated.
Its presence here does not count as a proved new-source endpoint.

- denoteR_zero_typed
- succeed_arm
- fail_arm
- failCause_arm
- sync_arm
- yieldNow_arm
- bind_arm
- suspend_arm
- select_arm
- catchCause_arm
- matchCause_arm
- onExit_arm
- scoped_arm
- gen_arm
- iterate_arm
- uninterruptible_arm
- interruptible_arm
- acquireRelease_arm
- catchIf_arm
- awaitFiber_arm
- fork_arm
- forkIn_arm
- forkScoped_arm
- runIn_arm
- interrupt_arm
- interruptScoped_arm
- interruptAll_arm
- awaitAll_arm
- awaitAllFailFast_arm
- snapshotChildren_arm
- awaitNewChildren_arm
- raceAll_arm
- raceAllFirst_arm
- getId_arm
- getInterruptible_arm
- closeScope_arm
- withFiber_arm
- syncPerform_arm
- deferredAwait_arm
- sleep_arm
- external_arm
- call_arm
- hop_typed
- param_arm
- perform_arm
- invoke_arm
- service_arm
- provideService_arm
- exit_arm
- restore_arm

The six existing helper definitions move once and become visible across the proof modules.
Their statements remain unchanged: effsRounds, effsRounds_nil, effsRounds_cons, Eff.expandIn_raceAll, Eff.expandIn_raceAllFirst, and Eff.expandIn_invoke.
Terms owns the moved declarations.
Denotation imports Arguments, which imports Terms.
No duplicate exported family remains in Denotation.

## Remaining direct consumers

LayerArm still uses the previous unit source fundamental-property input.
Body still derives source body typing from that unit input.
Assembly still packages that input as DenotesTyped.
Their migration remains open.

The existing ambient child operation preconditions retain PointTyped and requirement coverage.
They do not yet retain the argument-policy annotation at every native child birth.
The existing BodyCoverage and Region certificate must carry that annotation through their actual captured context.
Foreign scope registration also needs the actual captured context's requirement bound, alongside its existing CaptureTyped evidence.
This checkpoint adds no assumption to the original closed load claim.
It does not establish runtime preservation, progress, all-exit provider restoration, or target agreement.

## Files and checks

Base: 838d01572 on codex/symbolic-native-fold.
The direct checks use one thread, warningAsError, and the retained masked-provider R2 dependency overlay.
The coordinator keeps root imports and the target projection.
No machine file, source checker, target file, or behaviour gate changes here.

- Typed.Context: one shared terminal-fiber leaf adapter.
- Typed.Denotation.Terms: existing term declarations, checked child transports, ambient bind, and ChildDenotes.
- Typed.Denotation.Arguments: one policy-parametric actual argument producer and its ambient instance.
- Typed.Denotation: all source arms and the ambient source induction.

Context passes in 11.18 seconds.
Terms passes in 11.09 seconds.
Arguments passes in 26.32 seconds.
The exact parameter/invoke consumer slice passes in 10.55 seconds.
The recursive source slice passes in 38.62 seconds.
The complete Denotation module passes in 34.97 seconds.
The initial audit passes in 7.90 seconds.
The audit after the current Context rebuild passes in 17.14 seconds.
It checks 829 declarations within propext and Quot.sound, with zero planned goals and zero declarations modulo goals.
git diff --check passes.

The direct checks do not rebuild borrowed R2 dependencies.
The full Body/Assembly migration and outside-runtime gates remain open.
