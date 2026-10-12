# Shared loop callback integration

The shared loop rule and its actual numeric callback instance pass integration checks.
The original Timeout history producer remains open.

## Placement

Concept: scope-lifetime-finalization R11 and translation-simulation R10.
Question: the original Timeout cleanup and declared-retry claims need the actual successor cursor.
Role: helper of those existing claims.
Consumers: lexical frame-step ownership and the numeric root-loop instance.
The helper is `AnswerFlow.loop_step` in `src/Effect4/Laws/Machine/AnswerFlowFamily.lean`.
The lexical consumer is `frame_step_at` in `src/Effect4/Laws/Program/NativeFrameScope.lean`.

The law consumes the actual loopEnter result and the older ordered callback path.
It adds no permission for arbitrary future code.
The numeric instance retains the actual source address, three allocated cells, completed form, and finite generation.
Its saved suffix contains the actual outer finish binder.
Its refusal control rejects a body return against the preceding uncounted heap.
These are conditional proofs, not a producer for every reached history.
They establish no progress or outside-host agreement.

## Change

Base: `43d18858f22777f13c6d9f00900fd12dc9b72133`.
Head: the commit containing this receipt.
The two production paths are named above.
The retained research probes are `CountdownJoinProbe.lean`, `TimeoutJointGenerationProbe.lean`, and `TimeoutRootLoopProbe.lean` in this directory.
`Evidence.json` records exact hashes, line counts, and all twenty-four unchanged theorem statements.
`AgentReceipt.md` retains the separate development evidence and open producer obligations.

The shared module grows from 117 to 143 lines.
The lexical module grows from 333 to 341 lines.
The shared loop law replaces the old lexical branch in the same slice.
No new evaluator or command classification enters production.

## Verification

```sh
LEAN_NUM_THREADS=1 lake build Effect4.Laws.Program.NativeFrameScope Test.Dogfood.Proofs.AnswerFlowFamilyReader Test.Dogfood.Proofs.HostTimeoutNumberFormFamily
```

The build passes with 1,143 jobs; `Build.log` retains the output.
The following command checks the saved probes against the integrated modules.

```sh
LEAN_NUM_THREADS=3 lake env sh -c '
callback_probe_dir="$PWD/docs/research/2026-10-11-machine-models/codex/callback-loop"
export LEAN_PATH="$callback_probe_dir:$LEAN_PATH"
lean --root="$callback_probe_dir" -DwarningAsError=true -o "$callback_probe_dir/CountdownJoinProbe.olean" "$callback_probe_dir/CountdownJoinProbe.lean" &&
lean --root="$callback_probe_dir" -DwarningAsError=true -o "$callback_probe_dir/TimeoutJointGenerationProbe.olean" "$callback_probe_dir/TimeoutJointGenerationProbe.lean" &&
lean --root="$callback_probe_dir" -DwarningAsError=true -o "$callback_probe_dir/TimeoutRootLoopProbe.olean" "$callback_probe_dir/TimeoutRootLoopProbe.lean" &&
lean --root="$callback_probe_dir" -DwarningAsError=true "$callback_probe_dir/Audit.lean"
'
```

All three probe builds pass without diagnostics.
The audit checks both production modules and all three retained probe modules.
It passes for 290 declarations within `[propext, Quot.sound]`.
It finds no planned goal or declaration resting on one in those five modules.
`Audit.log` retains the integrated result.

No executable definition changes, so this slice reaches no behavior gate.
The numeric instance still needs actual entrant allocation, cleanup writes, and completed-form producers through the original reached histories.
