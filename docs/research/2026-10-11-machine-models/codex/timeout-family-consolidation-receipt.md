# Timeout family consolidation receipt

The slice transports the exact Timeout saved-frame family through the shared native pop specification.
It does not convert that family into the inductive semantic saved contract.
The checked continuing-loop control still refuses that conversion.
The shared family interface admits its actual pop.

## Commits and ownership

Base: `09010b941`.
Code head: `232b1baec`.
Branch: `codex/timeout-answerflow-consolidation`.
The integration base remains `4bc3efc44`.
The slice reads the primary `AUDIT.md` section dated `2026-10-11 10:25`.

No executable definition, root import, gate footer, decision register, or Lake configuration changes.
The existing AnswerFlow and typed imports reach both new library modules.
The coordinator owns the existing `Test.Machine.AnswerFlowLoop` root import.

## Placement

| Declaration | Path | Concept and requirement | Proof role | Reach and consumer |
| --- | --- | --- | --- | --- |
| `Contracts.Path` | `src/Effect4/Laws/Contracts/FramePath.lean` | scope-lifetime-finalization R11 | shared ordered carrier | external edges over existing frames; typed registration and native pop families |
| `Contracts.Path.map`, `Contracts.Path.append`, `Contracts.Path.split` | same path | same concept | shared path laws | exact endpoints; existing typed and answer-flow composition |
| `PopTrace.Family` | `src/Effect4/Laws/Machine/PopTraceFamily.lean` | scope-lifetime-finalization R11; store-typing R4 | one-step contract | actual scratch, answer selection, carried cause, skip, and hook operations |
| `PopTrace.Family.trace`, `PopTrace.Family.popFrom` | same path | same concepts | shared transport | exact original trace and external frame path; semantic and source pop consumers |
| `AnswerFlow.stack_path`, `AnswerFlow.path_stack` | `src/Effect4/Laws/Machine/AnswerFlow.lean` | same concepts | instance connectors | unchanged semantic saved witnesses; native callback selection and older suffix |
| `HostTimeoutFrames.stack_path`, `HostTimeoutFrames.path_stack` | `Test/Dogfood/Proofs/HostTimeoutFrames.lean` | host-session-protocol R6 | instance connectors | exact Timeout saved witnesses, including loops; original stale-body proof chain |
| `AnswerFlowLoop.loop_pop` | `Test/Machine/AnswerFlowLoop.lean` | store-typing R4; scope-lifetime-finalization R11 | reader | actual forever-resuming unit loop; external-family interface |

The generic carrier extracts the existing typed frame path.
`Typed.Contracts.FramePath` specializes that carrier and retains its name, constructors, and three path-law types.
The shared carrier imports no program typing module.
AnswerFlow therefore introduces no import cycle through typed contracts.

The external edge remains a predicate on existing primitives.
The family contract contains no stored program syntax.
Its consumer chooses the observation and supplies each one-step closure law.
The semantic instance retains its actual cause predicate.
The source instance retains its restricted saved-frame witnesses and literal value-class equality.

Future-world, provided-exit, pending-cause and native-finalizer premises remain in their existing callback consumers.
The pop contract supplies none of those premises.
Its failure instance transports the cause actually carried past discarded handlers.
Its value instance retains the selected value's class.
The source loop creates its next source witness through the existing one-step callback law.
It does not recursively embed another semantic saved-contract proof.

## Replacement

The following statements retain their names and types:

- `AnswerFlow.popFrom_value_selected` and `AnswerFlow.popFrom_cause_selected`;
- `HostTimeoutFrames.pop_from` and its dependent continuation consumers;
- `AnswerFlow.ensure_stack`, `AnswerFlow.stack_append`, and `AnswerFlow.stack_mono`;
- `HostTimeoutFrames.stack_append`;
- the typed path's `map`, `append`, and `split`.

The three pop consumers remove their separate trace inductions.
`PopTrace.Family.trace` owns that transport once.
The existing source and semantic saved predicates remain unchanged.
The semantic mask hook uses `FrameFiber.ensure_stack_cases` instead of a private primitive-constructor census.
Stack append and future transport use the shared path laws.

## Verification

The following commands pass with `LEAN_NUM_THREADS=3`.

```text
lake build Effect4.Laws.Machine.PopTraceFamily Effect4.Laws.Program.Typed.HostWalk
Build completed successfully (485 jobs).

lake build Effect4.Laws.Machine.AnswerFlowCausePop Effect4.Laws.Program.Typed.HostWalk Test.Machine.AnswerFlow Test.Machine.AnswerFlowLoop Test.Dogfood.Proofs.HostTimeoutNumberFormFamily Test.Dogfood.Scenario.Timeout
Build completed successfully (1167 jobs).

lake env lean -DwarningAsError=true /private/tmp/timeout-family-audit.lean
#axiom_audit: 387 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals

git diff --check
exit 0
```

The audit covers every changed module and both new library modules.
Logs: `/private/tmp/timeout-family-build.log`, `/private/tmp/timeout-family-complete-build.log`, and `/private/tmp/timeout-family-audit.log`.
The final build follows an isolated retry after a prior overlapping failed build.
Only the successful final run supplies the retained result.
No behaviour gate is owed because executable code does not change.

## Size

The line count compares the ten changed Lean files with `09010b941`.

| Module group | Before | After | Change |
| --- | --- | --- | --- |
| shared path | 0 | 50 | +50 |
| shared pop family | 0 | 85 | +85 |
| existing typed and semantic modules | 1189 | 1179 | -10 |
| exact Timeout source frames | 596 | 608 | +12 |
| loop control and reader | 93 | 125 | +32 |
| total | 1878 | 2047 | +169 |

This slice increases total lines while removing duplicated proof transport.
The continuing-loop control checks why the external family seam is necessary.
The new shared declarations all have consumers in this slice.

## Remaining obligations

`Timeout.retries_declared` and `Timeout.cleanup_keeps` remain open.
The original `Timeout.stale_never_applies` proof still compiles.
The source pop assertion supplies no reached numeric history or progress result.
The next producer uses shared interference, transport, stack-region, prefix, and applicable ledger laws.
The slice establishes no host runtime agreement, termination, fairness, or retry progress.
