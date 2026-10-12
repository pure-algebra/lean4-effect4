# Timeout accepted race restoration

The original numeric goals remain open after this local callback slice.
The checked source preserves waiting inputs and requires actual completed attempt cleanup before restoring the selected race exit.

Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.cleanup_keeps and Timeout.retries_declared.
Consumer: the joint source/generation permission, then native command history and the existing numeric readers.
Reach: actual raceSettle, native mask action, and selected-exit callback.
The join reader retains actual attempt identity, completed countdown, and retired writer evidence.
The public-cut reserve, reached source permission, and retired evidence producers remain open.

## Source

Original baseline: c765bc798, HostTimeoutNumberFlow has 605 lines.
Cancellation baseline: TimeoutNumberFlowCancelAccepted.lean has 740 lines.
Final source: /private/tmp/TimeoutNumberFlowRaceSettleAccepted.lean has 830 lines.
Source SHA256: bf581b38476043abee41e0d746a7086594d1c4a865c94296c3aafa02debee439.
The only production path is Test/Dogfood/Proofs/HostTimeoutNumberFlow.lean.

Delta patch: /private/tmp/timeout-race-settle-delta.patch.
Delta SHA256: b772dc38135a6ac2593157e57eaa3804cd78959ec0f26a6d8d4e66690d8afda9.
Full patch: /private/tmp/timeout-race-settle-full.patch.
Full SHA256: 347f51b0ec0770d6bdb0d59567ecafc77f338d54da3ef646dd731eefe14cad5a.

Inventory: /private/tmp/timeout-race-settle-header-inventory.txt.
All 24 original theorem headers remain unchanged.
All 31 prior cancellation theorem headers remain unchanged.
The Kind, ValueAt, CauseAt, and model block matches the 740-line snapshot byte-for-byte.
Two current-code constructors retain actual masked cancellation and selected-exit restoration.
Five local proof bodies move from the initial reader into the existing module.
No evaluator or command analysis is added.

Initial reader: /private/tmp/TimeoutRaceSettleInitialAccepted.lean.
Initial SHA256: fb19158f4089b66bb93e9fa282c3dd1f917f7f147bf2ff1973782cc659d7894d.
Those local proof bodies now belong to the production candidate.

Final reader: /private/tmp/TimeoutRaceSettleAccepted.lean has 49 lines.
Final reader SHA256: 89e955f9165e0d5bb5a10d1cc91a05c18c40807d0dcb31283aee30aa8052ee7d.
It consumes the actual selected Exit rather than the cancellation Cause.
CancelPhase.joined_restore remains the distinct captured-cause consumer.

## Verification

Checks run sequentially with LEAN_NUM_THREADS=1 and warningAsError=true.
The assigned worktree is host-planned-goals/lean4-effect4 at 125865d206dfedd3434d460010366f4fd136d84b.
The final dependency directory belongs to coordinator HEAD 8503a77130a916c6a4879a34a040c09f70f20435.
LEAN_PATH starts with race-settle-check, answer-family-check, timeout-shared-check, and /private/tmp.

1. lean --root=/private/tmp/race-settle-check -o /private/tmp/race-settle-check/Test/Dogfood/Proofs/HostTimeoutNumberFlow.olean /private/tmp/race-settle-check/Test/Dogfood/Proofs/HostTimeoutNumberFlow.lean.
   Result: /private/tmp/timeout-race-settle-family-check.log, passes.
2. lean --root=/private/tmp -o /private/tmp/TimeoutRaceSettleProbe.olean /private/tmp/TimeoutRaceSettleProbe.lean.
   Result: /private/tmp/timeout-race-settle-final-reader-check.log, passes.
3. lean --root=/private/tmp /private/tmp/TimeoutRaceSettleAudit.lean.
   Result: /private/tmp/timeout-race-settle-audit.log.
   The audit permits 185 declarations within propext and Quot.sound, with zero goals and modulo declarations.

Earlier dependency checks stop at missing artifacts while the coordinator rebuilds its graph.
They do not establish final source acceptance.
The completed checks above use the stable coordinator artifacts and production Clauses.

Clauses source SHA256: e2a336646dc53b647d3579b7829643212df025cdd739bb8bf622123273f7dd04.
Clauses object SHA256: 5743978b094644fd396129c10fc9df5c7af37d72678fadac5ce7a5dbafa7605c.

Coordinator independently reports the actual NumberFlow, NumberFormFamily, and NumberCounted build passes 1,145 jobs.
Coordinator reports eight ordered numeric readers pass and joint WaitingAudit permits 657 declarations without goals or modulo declarations.
Those coordinator outputs remain separate acceptance records.
No runtime or host behaviour changes occur in this proof-only slice.

## Next producer

TimeoutReachedPermissionPlacement.md identifies the existing transport to parameterize.
Keep the same native positions and source family; preserve lexical headers as projections.
Actual source allocation issues generation ownership.
Actual permitted writers issue persistent cleanup evidence.
Actual attempt exits or loser joins supply selected-exit restoration.
PublicCutRoomPlan.md retains the separate finite funding and four-command reserve obligations.
