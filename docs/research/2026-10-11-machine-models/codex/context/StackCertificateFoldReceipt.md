# Shared stack certificate candidate

The candidate preserves the existing public types and proves agreement with their old meaning.
It does not complete the Denotation, Body, or Assembly migration.

## Placement

Concept: residual-program-typing.
Requirement: R4.
Claim: denote-typed.
Role: preservation.
Consumer: the ambient parameter-call input, then the original closed M5 load and Assembly endpoints.

The fold records the actual parameter request, checked program, typed environment, and remaining stack.
Its ambient policy also records the checked program's requirement row inside the available row.
The actual checkEffs producer must discharge this field when invoke creates its argument sites.
A world service declaration alone does not discharge it.

## Candidate

StackCertificateFoldCandidate.lean defines one List.foldr certificate clause.
Its unit_agreement proves agreement with StackTyped in src/Effect4/Laws/Program/Typed/Admission.lean.
Its policy_map transports a policy implication through that fold.
Its ambient_erases returns the unchanged unit predicate.
Its ambient_widen retains the annotation when the available row grows.
Its empty_scope serves the actual closed source entry.
Its pointCertificate refines PointTyped with the same fold and copies no point grammar.
Its point_unit_agreement proves that the unit refinement adds no premise.

The production proposal replaces StackTyped's recursive body with the unit fold specialization.
Its public type remains literally unchanged.
PointTyped's public type and definition remain literally unchanged.
The ambient input uses the shared fold refinement.
The candidate remains research evidence until the production consumers compile.

## Controls

ProviderParameterControl.lean admits a closed definition invocation with a passed context reader requiring service S.
The callee provides S with value 2 before executing that parameter.
The finite kernel-checked native result contains S with value 2.
Provision.satisfies_merge_left proves that the source provider preserves every previously available key.
The internal ContextUpdate.setTo empty control loses S.
No source constructor introduced by this migration produces that raw replacement.
The finite result establishes neither a complete HistoryOf property nor an outside-runtime comparison.

## Rejected proposal

Automatic approval review rejects RejectedStackInputProposal.patch before execution.
The proposal adds an optional public parameter to StackTyped and PointTyped.
The review identifies changed public types and recursive contracts as exceeding proof-only transport.
The file remains unapplied.
Its SHA256 is 77d48dbf0b70f79e2c5f34cbf58dc37def4f470c35be52f5153718131c7f1d99.
The smaller fold candidate preserves those public types.
The coordinator approves this distinct shared-model alternative after its agreement check.

## Checks

Base: e30a74131 on codex/symbolic-native-fold.
The direct Lean checks use one thread and warningAsError with the retained masked-provider R2 dependency overlay.
StackCertificateFoldCandidate.log records a successful 9.18-second check.
ProviderParameterControl.log records a successful 3.37-second check.
StackCertificateCandidateAudit.log records 14 declarations within propext and Quot.sound.
The audit records zero planned goals and zero declarations depending on planned goals.
The checked candidate SHA256 is 84e8b5ad7287eeac4bb1e8e05e027e403de7f6b02de9dd06e30342bbdceb9d8c.
The source Denotation file and its Terms extraction remain uncommitted work.
No root imports, machine definitions, source checker, target projection, or behaviour gates change in this checkpoint.
