# Timeout sync transfer receipt

The shared connector combines the exact store answer with its post-state saved-frame contract.
Three existing numeric consumers use it, with unchanged theorem names and statements.
The original numeric history goals remain open.

## Placement

Concept: store-typing, R4, and scope-lifetime-finalization, R11.
Question: `Timeout.cleanup_keeps` and `Timeout.retries_declared` need actual writes joined to their saved return callbacks.
Consumer: `HostTimeoutNumberFlow.cleanup_native_write`, `completed_native_write` and `native_get`.

`ControlSteps.native_sync_answer` consumes the actual synchronous source code and actual `syncOpStep` result.
Its world projection reads the machine's actual stores before and after the operation.
Its explicit premises supply the future relation, post-state value contract and ordered saved stack.
The proof composes `ControlSteps.native_sync_op` with `AnswerFlow.sync_answer`.
It introduces no evaluator or command case analysis.

Reach: any compiled root, row table, actual fiber, synchronous store operation and projected state-indexed model.
The three numeric consumers retain their exact Timeout source, heap image, captured environment and numeric phase premises.
Limit: the connector does not establish those premises or preservation of unrelated live current code.
It supplies no child-source provenance, race winner relation, command history or progress.
The host boundary remains unchanged.

## Existing evaluator interface

`evaluatePrim.fun_cases` exposes 16 generated branches.
Its hypotheses include the actual current code, park selection, registration state, countdown result, target lookup and target exit.
The action and synchronous branches expose actual action selection and actual synchronous returned state and value.
A record with one field per branch would repeat this eliminator.
This slice adds no such record.

`StatePreservation.Hooks.sync` quantifies every interpreter name at a unary store predicate.
It lacks the active source phase needed by the numeric instance.
`NativeEvaluation.sync_heap_at` retains its actual source premise but proves a unary cell predicate.
It does not supply the ordered count, cleanup and completed-form relation.
The full history requires actual child/source and phase transfer premises in the shared classifier.

## Commits and files

Base: `820384481`.
Proof head: `d0539df89`.

- `src/Effect4/Laws/Program/ControlSteps.lean`
- `Test/Dogfood/Proofs/HostTimeoutNumberFlow.lean`

The shared module grows from 60 lines to 85 lines.
The numeric consumer module shrinks from 613 lines to 605 lines.
The total grows from 673 lines to 690 lines.
The diff adds 46 lines and removes 29 lines.
The slice removes three duplicated exact-answer and saved-frame compositions.
It adds no private evaluator or command census.

## Verification

Commands run in the host-planned-goals worktree:

```text
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.ControlSteps Test.Dogfood.Proofs.HostTimeoutNumberFlow
Build completed successfully (1083 jobs).

LEAN_NUM_THREADS=3 lake build Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Scenario.Timeout
Build completed successfully (1169 jobs).

LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/timeout-sync-audit.lean
#axiom_audit: 160 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals

LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/timeout-evaluator-eliminator.lean
Exit 0; the generated evaluatePrim.fun_cases type is retained in the temporary log.

git diff --check
No findings.
```

The first audit starts before the dependent build finishes.
The reported final audit repeats after that build exits, with no concurrent Lake process.
The eliminator inspection first queries a nonexistent convenience name.
The corrected inspection checks only the generated eliminator and exits successfully.
The independent audit imports and audits both affected modules.
The slice changes proofs and their imports, with no executable definition or outside comparison input change.
No additional behavior gate is reached.

## Original goals

The integration base proves `Timeout.stale_never_applies`.
`Timeout.retries_declared` and `Timeout.cleanup_keeps` remain open.
The build of the original Timeout module does not prove those planned goals.
The numeric reached-history producer remains required.
The settled declared-failure retry ruling remains unchanged.
