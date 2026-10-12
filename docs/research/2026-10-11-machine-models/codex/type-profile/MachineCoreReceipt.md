# Multiplication profile core

Source and proof acceptance passes.
The source commit is `dde23d54a`.
The approved core patch changes only three source paths.
The coordinator owns target generation, incoming-value controls, and the outside-runtime comparisons.

## Source

`Profile.scale` computes exact natural multiplication in `src/Effect4/Machine/Integers.lean`.
`NativeAtom.eval` calls that marker for the represented multiplication atom.
The TypeScript prelude wraps the product with its existing `inProfile` helper.
Internal multiplication remains unchanged.

The retained `MulOutsideProfile` control keeps the exact reference product above the target bound.
It checks the repaired prelude and the new reference marker.
These source checks establish no general reference-to-target simulation.

## Placement

1. Concept: translation-simulation; R8 and the printed TypeScript part of M7.
2. Question: the existing profile-plus-exact claim, with multiplication as its concrete consumer.
3. Reach: exact reference multiplication and the declared target-profile check in the emitted prelude.
4. Limit: the target generation and behavior comparisons remain the coordinator's separate acceptance.
5. Unlock: the approved numeric target row uses one named reference operation.

## Verification

The integrated narrow check passes 353 jobs, including `Effect4.Machine.Integers` and `Effect4.Machine.Term`.
The whole law graph and selected readers pass 1,423 jobs with the paired field cut.
The retained multiplication control passes.
The paired 40-module audit reports 10,229 declarations within `[propext, Quot.sound]`.
It reports zero planned goals and zero declarations depending on planned goals.
The field receipt retains the exact commands and output.
The patch has 12 added lines and seven removed lines across three paths.
The source base is `18cd908b9`.

## Proposed register amendment

Extend the existing profile marker to multiplication through `Profile.scale` beside `Profile.grow`.
The reference remains exact.
Each target refuses a product outside its declared profile before exposing that result.
The coordinator records the ruling and its target evidence.
