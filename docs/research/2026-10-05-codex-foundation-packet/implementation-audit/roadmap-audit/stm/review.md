# Transaction and literature corrections

Evidence status: source reading and eight finite history controls.
Proof role: design review of existing obligations.
Scope: the first transaction profile in rows 80, 84, 223, 224 and 226.
No Lean proof, target execution or new owner ruling occurs.

## Keep one program representation

Row 223 already selects an admitted fragment of `Eff`. It does not request a second program language or evaluator.
Use `TxBody` as an admission predicate or checked profile over that representation.
The profile permits pure terms, reads and writes of existing transactional cells, success, failure, retry and flat composition.
It excludes allocation, host effects, inner failure recovery, general loops and unresolved or reentrant calls.
The body grammar alone does not establish execution isolation.
The embedded-budget connector or complete driver continuation must exclude another fiber's step during an attempt.
The profile must exclude inline receiver reentry and mutable payload aliasing, including through transitively reached calls.
Keep ordered dynamic access and retry cleanup explicit.

The current owners are `atomic-attempt-isolation` in R4 and `atomic-attempt-agreement` in R10.
`Tools.Semantics.requirements` retains both as open parts.
Reuse their placements. Do not introduce a parallel transaction status record.
Their consumers are the first transfer and later retry-only alternatives under row 233.
The next concrete deliverable is an admission contract plus the embedded execution-bound premise.
No general opacity or Effect target agreement is established yet.

## Separate three rollback questions

Ordinary `Ref` operations update their cell directly.
`Ref.get`, `Ref.set` and `Ref.modify` in the pinned `Ref.ts` use synchronous access to `self.ref.current`.
Catching a later failure does not restore those earlier updates.
This is not a rule about the transaction journal.

Pinned `Effect.tx` accepts an ordinary `Effect` and introduces a journal only at the outermost boundary.
A nested `tx` returns the body under the existing transaction state.
`TxRef.modify` records the original version and tentative value in that shared journal.
At the outer boundary, a consistent success commits; failure discards; retry or inconsistent versions restart.
Thus a failure caught inside the transaction does not, by itself, create a local journal rollback boundary.
The first profile already excludes that recovery case.
Source anchors: `tx`, `isTransactionConsistent`, `commitTransaction`, `clearTransaction` in pinned `Effect.ts`, and `modify` in `TxRef.ts`.
These source readings do not execute the target or establish its whole behavior.

## Correct the STM citation

[Harris et al., Composable Memory Transactions](https://www.microsoft.com/en-us/research/wp-content/uploads/2005/01/2005-ppopp-composable.pdf) has two relevant exception rules.
The original 2005 body retains tentative effects when an inner exception is caught.
The retained August 18, 2006 post-publication appendix explicitly changes that rule.
Appendix A, XSTM2, discards caught-region writes before the handler, while preserving escaping allocation effects.
The pinned GHC 9.12.2 `catchSTM` reference supports the revised behavior.
Cite the appendix for local rollback; do not attribute that rule to the unchanged 2005 semantics.
This distinction reinforces the existing exclusion of inner recovery; it does not require changing the selected first profile.

## State opacity precisely

[Guerraoui and Kapalka, On the Correctness of Transactional Memory](https://kapalka.eu/files/opacity-ppopp08.pdf), section 5.2, Definition 1, uses a legal sequential completion.
It must respect real-time order between transactions, and each transaction must be legal in that completion.
Aborted and live attempts count. The discussion requires the criterion for each progressively generated history.
A transaction can observe its own tentative writes.
Different transactions need not share one literal prefix of the actual commit order.
Opacity does not require an application invariant after every individual write inside one transaction.
It prevents inconsistent combinations of other transactions' states from reaching the body.
It does not establish fairness, termination or rollback of external effects.

Eight finite controls test these distinctions in `opacity-controls.py`.
Mixed reads across one committed writer have no legal serial order, even when the reader aborts.
Coherent reads before or after the writer are positive controls.
An attempt may read its own tentative write while an application equality is temporarily false.
Other controls exclude aborted-write visibility and enforce transaction real-time order.
These are small history examples, not an opacity checker for Effect or a Lean proof.
The initial web fetch of the opacity PDF returns 403; search metadata and the rehashed retained PDF provide the source.

## Use the other citations at their actual scope

[Wu, Schrijvers and Hinze, Effect Handlers in Scope](https://people.cs.kuleuven.be/~tom.schrijvers/Research/papers/haskell2014.pdf) separates explicit syntactic scope from handler-order interactions.
That informs protected bodies and retained-behavior contracts.
It does not supply the Pool's lease identity or finalizer transition law; those need the pinned source and a project proof.

[Chappe et al., Choice Trees](https://paulhe.com/assets/ctrees-popl.pdf) separates external events from internal nondeterministic branching.
It provides simulation and bisimulation reasoning for the resulting transition systems.
This is a useful conceptual connection for observing concurrency.
It does not prove a Cache's eviction, cancellation or replacement-cleanup rule.
Use native Cache source for those requirements and the existing `Eff` model for their implementation.

## Remaining requirements

This review advances design detail for existing R4 and R10 open parts.
It leaves R1–R3, R5–R9 and R11–R13 obligations untouched.
Placement is not measured dependency or proof status.
The report remains a proposal until the coordinator places actual declarations and checks their proofs.
