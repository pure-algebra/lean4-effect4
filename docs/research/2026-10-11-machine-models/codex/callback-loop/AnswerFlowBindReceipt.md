# Ordered bind and actual delay receipt

The actual loop-to-delay-to-catch path is checked. The reached-history producer remains open.

## Placement

Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: Timeout.retries_declared and Timeout.cleanup_keeps require the actual next-generation source entry.
Helper: AnswerFlow.push_success_path joins the current body with its ordered saved callback path.
Consumers: AnswerFlow.push_success, NativeFrameScope.frame_step_at, and the numeric iteration_step.
Reach: actual onSuccess current, body code permission, head edge, and older path.
The shared theorem adds no source admission, state transition, or future current-code transport.
It adds no evaluator or command traversal.

## Production changes

Root source baseline HEAD: 9d7d4e5ef12528985a78f19352004fa2ef6e427f.
Agent worktree HEAD: 125865d206dfedd3434d460010366f4fd136d84b.
The source hashes identify the actual baseline independently of concurrent root changes.

| Path | Lines before | Lines after | Old theorem headers retained |
| --- | --- | --- | --- |
| src/Effect4/Laws/Machine/AnswerFlow.lean | 230 | 246 | 8 |
| src/Effect4/Laws/Program/NativeFrameScope.lean | 357 | 364 | 21 |

The semantic push_success body becomes an adapter to the shared path law.
The lexical onSuccess branch consumes the same law.
The previous two-line semantic proof and implicit lexical branch are replaced.
All 29 existing theorem headers remain byte-for-byte.

Patch: /private/tmp/answer-flow-bind.patch.
Patch SHA256: 88ae5b9eaefacfe64899d957e4bc19bffca774ed72fe8d7c2bc12a781a85001c.
Inventory: /private/tmp/answer-flow-bind-inventory.txt.

| Source | Baseline SHA256 | Candidate SHA256 |
| --- | --- | --- |
| AnswerFlow.lean | cfb8b019fcc39b8dfb30eb977385ce33727e451b7f1694f1ca09adf1b7f0d799 | 2f6861f0ff4664d6fa35673bac6c7719c931f5ab55e67b6644e8636954b79e20 |
| NativeFrameScope.lean | 41bde0a4a6370eeb7fd40d164f31650f2a9a5b815b0d7f034d43c68ec6e85be8 | 39cef85e079afbc8e8b84f39f9dcebd301f0e69104a6530c767f256f58c004fd |

## Concrete numeric consumer

Probe: /private/tmp/TimeoutRootLoopProbe.lean, 663 lines.
Probe SHA256: df10153a1d91d4508bbab160637de7d85cb7722e83d6f463d00564fbb3e24c39.
Prior catch bytes: /private/tmp/TimeoutRootCatchAccepted.lean.
The candidate extends that accepted probe with a delay class and its actual source callback.

iteration_bind reads the actual compiled bind and its suspend child.
root_child retains the exact source address, environment, metadata, and remaining source fuel.
ready_iteration connects the actual source loop to iteration_step.
Its Point.fuel = fuel + 3 premise stays explicit.
iteration_step pushes the actual delay callback above the real loop and finish suffix.
delay_step consumes the actual selected callback and supplied success exit.
That callback retains the complete predecessor image and resolves the actual catch source child.
delay_stack inhabits the three-frame ordered suffix.
delay_wrong_generation_refuses rejects an older delay permission at a newer count heap.
The callback family adds no recursive inductive saved contract.
The pure local model still has no native finalizer hook.
Native store execution and finalizer interception require their separate actual producers.

## Verification

All checks use one thread in the assigned host worktree.
The private LEAN_PATH prefixes are /private/tmp/answer-family-check, /private/tmp/timeout-shared-check, and /private/tmp.
All accepted lean commands use warningAsError=true.

- AnswerFlow.lean: pass; /private/tmp/answer-flow-bind-path-check.log.
- NativeFrameScope.lean: pass; /private/tmp/answer-flow-bind-lexical-check-2.log.
- TimeoutRootLoopProbe.lean: pass; /private/tmp/timeout-delay-entry-check-4.log.
- #axiom_audit AnswerFlow NativeFrameScope TimeoutRootLoopProbe: 321 declarations, zero modulo goals, zero planned goals.
- Audit runner: /private/tmp/AnswerFlowBindAudit.lean.
- Audit output: /private/tmp/answer-flow-bind-final-audit.log.

The private dependency overlay retains the pre-R1 pending carrier.
JointGeneration's retained registration literal includes the old waitingOn field.
Root acceptance under R1 must remove that literal's second argument, none.
The two changed production modules use no removed Pending or Dispatcher fields.
This receipt claims the checked private baseline, not acceptance against R1.
No executable source changes. No behaviour gate is owed for this proof slice.

## Remaining actual producer

The same Ready image must come from actual allocations and the completed previous timeout outcome.
Token-matched delay completion must produce the delivered unit at that generation.
Actual source child assignment must connect the form, attempt, and timer owners.
Actual source sync execution must issue persistent cleanup and publication evidence.
An attempt winner already exits, or a completed loser join contains the attempt.
A timer-only join supplies no attempt cleanup.

The original fixed2000 drive and compile4000 remain unchanged.
count_prefix_region consumes StackRegion and LiftPrefix with an arbitrary remaining budget.
An actual charged-operations bound can discharge its operation-room premise against inherited2048.
The launch must still retain at least four commands before the public exposed cut.
A locally installed onExit does not by itself identify an exposed public finalizer.
Forced yield verdicts, inherited deferred causes, and unfinished command residues remain distinct obligations.
Ready assumes none of those prefix conclusions.
The original retries_declared and cleanup_keeps remain open.
