# Shared loop permission receipt

The callback instance is checked. The reached-history producer remains open.

## Placement

- Concept: scope-lifetime-finalization R11 and translation-simulation R10.
- Question: Timeout.retries_declared and Timeout.cleanup_keeps require the actual successor cursor.
- Helper: AnswerFlow.loop_step supplies actual current code and an ordered saved-frame path.
- Consumers: NativeFrameScope.frame_step_at and the numeric root-loop callback instance.
- Reach: actual loopEnter equations, current-code equality, and the existing older path.
- Limit: the theorem supplies no source admission, command history, progress, or future-code weakening.
- Unlock: one shared loop-entry connection for the numeric permission producer.

## Files

The production patch changes two paths.

| Path | Lines before | Lines after | Old theorem headers retained |
| --- | --- | --- | --- |
| src/Effect4/Laws/Machine/AnswerFlowFamily.lean | 117 | 143 | 3 |
| src/Effect4/Laws/Program/NativeFrameScope.lean | 333 | 341 | 21 |

The patch adds no evaluator or command case analysis.
The lexical whileLoop branch consumes the shared theorem.
The existing frame case analysis remains its sole producer.

- Root baseline HEAD: d81746e9e0cafb6f0644426b007805a04fbdfd69.
- Agent worktree HEAD: 125865d206dfedd3434d460010366f4fd136d84b.
- Patch: /private/tmp/answer-flow-loop.patch.
- Patch SHA256: b0b0a99fddbc5f733e0dd2335bb750bda88bb79f448d890614a0aa0b7211841f.
- Numeric probe: /private/tmp/TimeoutRootLoopProbe.lean.
- Probe SHA256: ee6669e1cb9e8a18bbaba7023aecb79cba2c594b14ef066b4951e75cc9941ee7.

| Production source | Baseline SHA256 | Candidate SHA256 |
| --- | --- | --- |
| AnswerFlowFamily.lean | e59bf150e90085536bfd00b9aa582d85d4309c64839a7954b928e0bdbc820fc7 | 21c009e75cb7ef2fed0d4a5cb75a1c144b03dfb13ae5e8670546ea335c869597 |
| NativeFrameScope.lean | cb6d7a96f080836787a98013d5de6641804c2b568da630718f185c42e0a06426 | 7c9b9e03003f84427a8291db75e5df2575a694d7742890f4baab61b8cd765242 |

## Verification

All checks use one thread and the private source overlay.
The Lake command runs in the authorized host worktree.
LEAN_PATH begins with /private/tmp/answer-family-check, /private/tmp/timeout-shared-check, and /private/tmp.

- lake env lean -DwarningAsError=true AnswerFlowFamily.lean: passes.
- lake env lean -DwarningAsError=true NativeFrameScope.lean: passes.
- lake env lean -DwarningAsError=true TimeoutRootLoopProbe.lean: passes.
- #axiom_audit AnswerFlowFamily NativeFrameScope TimeoutRootLoopProbe: 232 declarations, zero modulo, zero planned goals.

Accepted logs:

- /private/tmp/answer-loop-shared-check-2.log.
- /private/tmp/answer-loop-lexical-check-2.log.
- /private/tmp/timeout-root-loop-suffix-check-2.log.
- /private/tmp/answer-flow-loop-accepted-audit.log.

The header comparison checks all 24 pre-existing theorem headers byte-for-byte.
No executable source changes. No behaviour gate is owed for this proof slice.

## Numeric instance

RootAt fixes the source address and the three allocated cells.
Complete couples the cursor, cleanup count, returned-form count, and declared-failure policy.
The actual loop guard supplies Fin 4 before entrant allocation.
The value callback consumes the matching completed body return.
The actual source test supplies the declared-failure fact before retry.
The recursive edge uses SavedFamily and Contracts.Path, without a finite inductive callback cycle.
The actual outer finish binder inhabits the older suffix.
The refusal control rejects a body return against its uncounted predecessor heap.

## Remaining work

The probe does not prove every reached history supplies its premises.
Actual entrant birth assigns the owner and generation from the source child permission.
Actual sync execution supplies persistent cleanup evidence.
Actual attempt exit or completed loser join supplies the completed form permission.
Native finalizer interception stays explicit.
The fixed public budgets supply the pre-count prefix through StackRegion and LiftPrefix.
The original retries_declared and cleanup_keeps goals remain open.
