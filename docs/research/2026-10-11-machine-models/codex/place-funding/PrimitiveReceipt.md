# Shared primitive funding receipt

The shared interpretation has two actual callers.
Atomic.Cleanup.log_debits remains open.
The source opportunity theorem retains every existing source premise.

## Placement

1. Concept: scope-lifetime-finalization, R11.
   Reactive scheduling supplies the existing primitive producer.
2. Question: primitive funding serves Atomic.Cleanup.log_debits and the source opportunity history claim.
   SourceOpportunityPrimitive.primitive_debit consumes the shared interpretation.
   Atomic.WriterMachine.same_rows_debit consumes its unchanged-row connector.
3. Reach: NoQueue.local_debit reads actual state, trace, stored rows, and the returned acting row.
   PrimitiveInputs retains actual sync results, asynchronous replies, cancellation callbacks, and complex producer bounds.
   The primitive witness remains Moves.evaluatePrim_producer.
4. Limits: this interpretation supplies no source permission, initial funding, progress, or admitted history by itself.
   Atomic still needs its actual action and complete evaluator inputs.
   No original scenario statement changes.
5. Unlock: one primitive accounting interpretation replaces the source caller's repeated administrative arithmetic.
   The same unchanged-row connector serves Atomic frame and finalizer delegation.

## Source and statement scope

Base: 914916f0d. Source head: 79715d0cf.
Source paths:

- src/Effect4/Laws/Program/PlaceFunding/Primitive.lean
- src/Effect4/Laws/Program/SourceOpportunityPrimitive.lean
- Test/Dogfood/Scenario/Atomic/WriterMachine.lean

Primitive.lean adds 149 lines.
SourceOpportunityPrimitive.lean changes from 268 to 310 lines.
WriterMachine.lean changes from 232 to 239 lines.
The source slice adds 273 lines and removes 75 lines, net 198 lines.
The header comparison retains all 33 previous declarations without a change.
The new source_control, source_no_queue, and source_events instances also serve shared history funding.
No machine source, root import, register, or planned goal changes.

## Commands and evidence

Run from the machine-fields worktree:

```sh
LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.SourceOpportunityPrimitive Test.Dogfood.Scenario.Atomic.WriterMachine Test.Dogfood.Scenario.SourceOpportunity
LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/MachinePlacePrimitiveAudit.lean
python3 /private/tmp/MachinePrimitiveHeaderCheck.py
```

The final build passes 1156 jobs.
The audit passes 230 declarations within [propext, Quot.sound], with zero planned and zero modulo declarations.
PrimitiveBuild.log records the final acceptance build.
PrimitiveAudit.lean and PrimitiveAudit.log record the three-module proof audit.
PrimitiveHeaders.json records the exact header comparison.
PrimitiveHeaderCheck.py records its comparison procedure.
PrimitiveFirstFailure.log retains the first source-instance normalization failure.
PrimitiveSourceRetry.log retains that repaired caller build.

## Remaining obligation

Atomic's actual native action input remains open.
WriterMachine.action_debit still requires its local action bound.
The next slice must reuse the existing action producer and source action interpretation.
It must discharge actual program-slot permissions before the original log bound can close.
No whole-machine or outside-runtime agreement is claimed by these proof checks.
