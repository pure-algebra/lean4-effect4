# Timeout pop consolidation receipt

The slice replaces three original-stack proof traversals with one shared specification.
It does not connect the two remaining Timeout goals to reached histories.
The new shared module makes this slice larger overall.
The existing consumer modules shrink together.

## Commits and ownership

Base: `4bc3efc44`.
Code head: `fb7f96998`.
Branch: `codex/timeout-answerflow-consolidation`.
The preserved race-entry checkpoint remains on `codex/host-planned-goals` at `83a4234e4`.
The slice changes no executable definition, root import, gate footer, decision register, or Lake configuration.

The new reader needs the coordinator's `Test/All.lean` import:
`Test.Dogfood.Proofs.MachinePopTrace`.
The existing AnswerFlow imports already reach the shared library module.

## Placement

| Declaration | Path | Concept and requirement | Proof role | Scope and consumer |
| --- | --- | --- | --- | --- |
| `PopTrace.getCont_spec` | `src/Effect4/Laws/Machine/PopTrace.lean` | scope-lifetime-finalization R11; reactive-scheduling R2 | shared structural specification | actual detached continuation pop; source witness and labelled move accounting |
| `PopTrace.popFrom_spec` | same path | same concepts | helper | actual fused pop; getCont specification and saved-stack instances |
| `PopTrace.Trace.original` | same path | same concepts | helper | original consumed prefix and unconsumed suffix; pop readers |
| `PopTrace.Trace.popped` | same path | same concepts | helper | exact original frames interleaved with hook-drain frames; pop readers |
| `PopTrace.Trace.events` | same path | same concepts | helper | exact pop events; labelled frame accounting and pop reader |
| `PopTrace.Trace.stack` | same path | same concepts | helper | surviving scratch and original suffix; pop reader |
| `PopTrace.Trace.selected_original` | same path | same concepts | helper | selected ordinary arm belongs to the consumed original prefix; getCont specification |
| `PopTrace.drain_empty`, `PopTrace.drain_not_frame`, `PopTrace.answer_missing` | same path | same concepts | shared operation helpers | actual hook scratch; original callback witness and semantic/source instances |
| `AnswerFlow.popFrom_value_selected` | `src/Effect4/Laws/Machine/AnswerFlowPop.lean` | store-typing R4; scope-lifetime-finalization R11 | existing semantic consumer | same statement; induction over the shared trace |
| `AnswerFlow.popFrom_cause_selected` | `src/Effect4/Laws/Machine/AnswerFlowCausePop.lean` | same concepts | existing semantic consumer | same statement and actual cause premises; induction over the shared trace |
| `HostTimeoutFrames.pop_from`, `HostTimeoutFrames.get_cont` | `Test/Dogfood/Proofs/HostTimeoutFrames.lean` | host-session-protocol R6 | existing source consumer | exact restricted source family; original stale-body proof chain |

The specification annotates existing primitives and the actual pop result.
Its pairs record one original frame and the exact frames that its hook drain pops.
It introduces no executable syntax or second program representation.
Its constructors retain the actual carried cause and event list.

The slice retains each existing theorem's type and name.
An unused hypothesis binder in `ensure_masks` gains an underscore for the linter.
The hypothesis remains in the theorem type.

## Changed files

- `src/Effect4/Laws/Machine/PopTrace.lean`
- `src/Effect4/Laws/Machine/AnswerFlowPop.lean`
- `src/Effect4/Laws/Machine/AnswerFlowCausePop.lean`
- `Test/Dogfood/Proofs/HostTimeoutFrames.lean`
- `Test/Dogfood/Proofs/MachinePopTrace.lean`

## Verification

The following commands pass with `LEAN_NUM_THREADS=3`.
The build logs retain their measured job counts.

```text
lake build Effect4.Laws.Machine.AnswerFlowCausePop Test.Dogfood.Proofs.MachinePopTrace Test.Dogfood.Scenario.Timeout
Build completed successfully (1153 jobs).

lake build Test.Machine.AnswerFlow Test.Dogfood.Proofs.HostTimeoutNumberFormFamily
Build completed successfully (1090 jobs).

lake env lean /private/tmp/timeout-pop-trace-audit.lean
#axiom_audit: 203 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals

git diff --check
exit 0
```

The audit imports each changed proof module and the new reader.
It uses `#axiom_audit`, not Lean's axiom printer.
No behaviour gate is owed because no executable definition changes.

The new finite control uses an actual interrupted `asyncFinalizer` followed by an original success continuation.
Its pop consumes the original finalizer and a hook-injected restoring mask.
Its returned stack retains the original success continuation.
The control refuses the naive equation that concatenates actual popped frames and the returned stack into the original stack.
The readers apply the shared specification to this control and an actual selected success callback.
These finite controls establish no scenario history or host agreement.

## Measured size

The following output comes from `wc -l` before and after the code slice.

```text
module                                   before  after
HostTimeoutFlow                             226    226
HostTimeoutFrames                           599    596
AnswerFlowPop                               177    156
AnswerFlowCausePop                          176    183
existing consumer total                    1178   1161
new PopTrace                                         285
new MachinePopTrace reader                            40
```

The shared base adds one actual pop classification.
The source and semantic consumers remove their separate original-list classifications in the same commit.
The net line change remains positive because this slice establishes the shared base.

## Open obligations and limits

`Timeout.retries_declared` and `Timeout.cleanup_keeps` remain their original open goals.
The owner ruling remains unchanged: retry follows the timeout form's declared failure and completed selected cleanup.
The four-attempt bound remains unchanged.
The new stack specification supplies no history producer, numeric count relation, budget-drain law, or progress theorem.

The old source `SavedAt.loop` accepts arbitrary callbacks closed over all admitted cursor values.
Such a callback may return a new saved loop without a decreasing parameter.
A direct connector to inductive `AnswerFlow.SavedAt` therefore needs a shared recursive-contract seam or a bounded concrete loop instance.
The slice retains the exact source constructor family.
It adds neither a wider contract nor another scenario traversal.

The next numeric history producer uses shared interference and transport laws, `StackRegion`, `LiftPrefix`, and the landed stack ledger where applicable.
The stack ledger does not yet account for active current-code weights.
