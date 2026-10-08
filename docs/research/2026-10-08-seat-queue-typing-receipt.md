# Queue typing migration receipt

Queue typing passes with the generic tuple checkpoint. Public Queue behavior proofs remain under the value seat's ownership.

## Change

Base: `ce9a2ecbab229d8937ca9ce67272c126b667488e`.
Dependencies: checked model helper `47240976` and tuple checkpoint `62437bcb`.
Changed source: `src/Effect4/Laws/Modules/Queue/Typing.lean`.

The five step typing proofs consume `Step.typed` on the named operation data.
The size proof supplies the shared scope argument.
Every existing theorem header remains identical, including binder names and premises.

Formation helpers consume the existing `MessageTy` premises.
They share the message-node and offer-node reasoning previously held in Queue Ops.
They derive annotation formation without strengthening the existing message profile.

## Placement

Concept: store-typing, requirement R4.
Question: helpers of `step-language-typed`, consumed by Queue's existing step typing and public operation admission proofs.
Reach: `TypesEach` under the native atom table, existing `MessageTy`, and existing captured-source and scope premises.
Exclusions: these laws establish no behavior agreement, allocation, progress, liveness, or host execution.
Consumer: Queue operation typing and program admission on the R4 spine.

## Checks

`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Modules.Queue.Typing` passes before tuples: 536 jobs.
The same command passes after tuples: 537 jobs.

`LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true /private/tmp/queue-typing-trust.lean` passes.
The focused audit checks 82 declarations and permits only `propext` and `Quot.sound`.
It uses `ProofGraph.Audit.auditedFacts` and `ProofGraph.reachedAxiomsMany`.
It rejects forbidden declaration flags and unresolved audit entries.

A source comparison reports no changed existing theorem header.
`git diff --check` passes.

## Remaining integration

The direct Queue Ops and test build reaches the parallel public Queue behavior proofs.
Those old bodies refuse the migrated core at their previous proof sites.
The value seat replaces those bodies independently.
Six migrated scope proof bodies pass an isolated control; the Ops module check awaits that dependency.
No full sweep or host check runs in this slice.
