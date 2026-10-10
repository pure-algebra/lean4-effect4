# HO-3b invocation review placement

The owner base is `000bcd7ad68e7bbbe4f3478831982a7f9f2f1a42`.
The prior review commit is `d5110c598a952b090d1939ef7a15f628c05a318a`.
HO-3a has landed; invocation TypeScript printing remains working HO-3b code.

## Completion criteria

Check caller captures, nested callbacks, parameter forwarding, callback order, and a fork with actual generated TypeScript.
Compare finite machine answers with the generated module under Effect rc.112.
Keep malformed callback syntax separate from program typing refusals.
Check invocation requests and callbacks through the checked TypeScript term printer and named erasure.
Record input hashes, exact commands, results, and evidence limits.
Persist a local review packet without changing the implementation worktree.

## Raw reconstruction placement

1. Concept: `exact-codecs`; required property: reconstruction of printed modules.
2. Question: `module-defs-round-trip`, role `compatibility`, pointer `readModule_printModule_defs` in `src/Effect4/Laws/Codegen/Module.lean`.
   Invocation cases serve `read_print`, then `Api.printModule_roundTrip` in `src/Effect4/Laws/Api/ModuleReadable.lean`.
3. Reach: definition calls with readable requests at caller depth and callback bodies under one additional argument.
   Decisions rows 340 and 341 retain their order.
   Definition names and parameter names retain the existing separation premises.
4. Limits: reconstruction alone establishes neither program typing nor target acceptance or runtime agreement.
   Callback count remains a source typing check; the raw reader does not own it.
5. Requirements: R8 for reconstruction and target observations; HO-3 supports R2 module authoring.

## Checked TypeScript printing placement

1. Concept: `exact-codecs`; required property: reconstruction modulo the named erasure.
2. Questions: `typed-print-connector`, `typed-print-erasure`, and `typed-print-read`, each with its existing compatibility role.
   Consumers are `printTyped_eq_print`, `eraseJoinArgs_printTyped`, and `readTyped_printTyped` in `src/Effect4/Laws/Codegen/PrintTyped.lean`.
3. Reach: checked invocation requests, callback addresses, and extended environments under decisions rows 325 and 340.
4. Limits: an insertion-policy difference is not by itself target rejection.
   A finite execution comparison proves no universal simulation.
5. Requirement: R8, the connection between stored programs and generated TypeScript.

## Finite execution placement

1. Concept: `translation-simulation`; required property: target observations agree on the named fragment.
2. Question: the generated-program connection under R8; these controls support its boundary and introduce no universal theorem.
3. Reach: the listed closed native programs, their successful exit values, and the recorded finite machine budgets.
   The fork control fixes the existing runner and target runtime; it claims no schedule independence.
4. Limits: no host replies, cleanup, general scheduling, or arbitrary callbacks are established.
5. Requirement: R8; lexical capture evidence supports the module-authoring application under R2.

No new theorem or planned goal is introduced.
The probes use existing program syntax and existing public entry points.
