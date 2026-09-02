# Sequencing and cleanup: model review and distinguishing cases

The proposed liberal-append equation fails, and the proposed state representation cannot express the required cleanup result. Keep the existing liberal and total conditions and the shipped auxiliary theorem, including its history and nonemptiness premise. Correct the missing connections instead of adding a public modality to hide them.

This review reasons only from the supplied packet. The witnesses below are finite deductions from its execution rules, not Lean proofs, host observations, or results from a search. No implementation, tool installation, execution, or repository modification was performed. Witness IDs are local to this document and are not claimed as entries in the project's register.

## The table contract under review

The observable table outcomes are refusal or successful return of a value. History is necessary execution context even though the final postcondition inspects only the returned value. Successful instructions append their answers. Table concatenation carries the full history through the prefix into the suffix.

The existing liberal condition requires `Q(v)` for each successful returned value; a refusing run satisfies it for every `Q`. The total condition additionally requires success. These definitions remain in force. Refusal here is not the separate stateful example's typed error `bad`.

The challenged equation quantifies over every prefix, suffix, and postcondition, starting with empty history. Its right side first applies the liberal condition to the prefix, then evaluates the suffix with fresh empty history. Consequently, a refusing prefix makes that entire right side true, and a refusing freshly restarted suffix can make it true after a successful prefix. These are two distinct faults.

The packet does not specify an empty table's returned value when its initial history is nonempty, nor provide the auxiliary theorem's exact signature. Do not fill those gaps by inventing public behavior. The following witnesses need neither missing fact. A future all-input proof must inspect those definitions and the existing theorem.

## Concrete sequencing witnesses

An elementary positive control should pass before the acceptance check is trusted: prefix `[emit 9]`, suffix `[emit 4]`, and `Q(v)` meaning `v = 4`. Concatenation returns 4 with history `[9, 4]`. Restarting this particular suffix also returns 4. Both liberal sides are true. This control alone would miss the defects below.

| ID | Inputs and quantifier instance | Left side: actual concatenation | Right side: proposed nesting | Forced correction |
| --- | --- | --- | --- | --- |
| C02-SEQ-01 | Initial history `[]`; prefix `[]`; suffix `[emit 9]`; `Q(v)` means `v = 4` | Concatenation is `[emit 9]`; it returns 9, so liberal is false | The empty prefix refuses from empty history, so liberal is true regardless of its nested postcondition | The unconditional law is false even before history-dependent suffixes are considered. Keep the auxiliary premise, or deliberately change the table contract; do not silently treat the empty table as a successful unit |
| C02-SEQ-02 | Initial history `[]`; prefix `[emit 9]`; suffix `[use 0]`; `Q(v)` means `v = 4` | Prefix produces `[9]`; `use 0` returns 9 and appends it, producing `[9, 9]`; liberal is false | The prefix succeeds; restarted `use 0` refuses from `[]`, so its liberal condition is true; outer liberal is true | The prefix is nonempty, so the shipped domain premise holds. That premise alone does not repair the equation: the suffix must receive the prefix history |
| C02-SEQ-03 | Initial history `[]`; prefixes `[emit 9, emit 4]` and `[emit 4]`; common suffix `[use 0]` | Both prefixes return 4, but their histories are `[9, 4]` and `[4]`; the suffix returns 9 and 4 respectively | A continuation receiving only the last prefix value cannot distinguish these histories; replacing history with `[4]` produces the wrong first result | Carry the whole history, not merely the last value. With `Q(v)` meaning `v = 4`, the actual liberal results are false and true |
| C02-SEQ-04 | Initial history `[]`; prefix `[emit 9]`; suffix `[use 0]`; use the total condition with `Q(v)` meaning `v = 9` | Concatenation succeeds with 9, so total is true | Fresh-history `use 0` refuses, so nested total is false | Replacing liberal with total does not repair lost history, and refusal's truth value differs between these two existing conditions |

In the first two witnesses, the right side is true and the left side false. Therefore even the sequencing implication from nested specifications to the composed specification fails for this proposed composition, not merely the equation's converse.

The repaired positive boundary for C02-SEQ-02 passes history `[9]` into `use 0`. It then returns 9. With `Q(v)` meaning `v = 4`, both correctly history-threaded liberal readings are false; with `Q(v)` meaning `v = 9`, both are true. No passing runtime test is claimed: these expectations follow directly from the packet.

## What can be kept and what needs a local proof

Reuse the existing shipped auxiliary sequencing theorem with its exact premise: the initial history is nonempty or the prefix is nonempty. Its suffix must receive the actual prefix-produced history. The packet does not supply a shipped public liberal-append theorem; neither this review nor a similar-looking paper rule creates one.

The smallest correction keeps the present table semantics and states a history-aware sequencing obligation only on that justified domain. An internal helper may expose the carried history needed for the proof while the public liberal condition keeps its current meaning. This is a connection to the existing predicate, not a new public logic.

Prove the operational split first: on the permitted domain, a refusing prefix stops the concatenation; a successful prefix gives the suffix its full resulting history. Then prove that this split gives the desired rule for the existing liberal predicate, explicitly considering prefix refusal, suffix refusal, and final success. State and prove the other direction separately if an equation is required. Reuse the shipped auxiliary result only to the extent its actual statement supports this argument.

The relationship “total means liberal plus success” must use the same outcomes, inputs, and history in both components. It does not allow a total sequencing result to be relabeled as a liberal theorem without the missing argument. Similarly, an existing monadic sequencing rule cannot make invalid empty tables into valid `return` programs.

If the product requires unconditional append, changing the empty-table contract is a separate semantic change: a successful neutral program needs an explicit result and history policy. Do not invent a default natural-number result simply to make a proof go through. Restricting the theorem to the shipped premise is the smallest correction justified by this packet.

The [supplied EffHOL adaptation record](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/references/effhol.md) describes the paper's sequencing rule as an implication and its realization theorem as conditional on an instance's typing, substitution, reduction, conversion, and deduction rules. The paper's modality can admit a false postcondition without giving termination. Those are paper results as summarized by that reference, not proofs about these tables. The original paper and artifact were not independently opened or built for this exercise. The local table modality, operational/history connection, correct rule direction, and all required instance laws remain local obligations.

## Cleanup exposes two independent defects

In the proposed semantic shape, a computation maps initial state to either an error or a value paired with final state. Its failure branch carries no final state. For the same initial state, both supplied bodies are therefore represented by exactly the same outcome: error `bad`.

Yet the specified cleanup distinguishes them. Setting state to 5 and failing must lead to error `bad` with final state 6. Setting state to 8 and failing must lead to error `bad` with final state 9. Any generic cleanup that receives only the proposed outcome and the same initial state receives identical information in the two cases. It cannot recover both different required states. This is lost information, not a difficult proof obligation that a catch implementation can discharge.

Separately, ordinary error-short-circuiting bind never executes its suffix after `bad`. Appending cleanup with that bind skips cleanup even if the representation is changed to retain state. Both defects need repairs.

| ID | Body and cleanup | Required observation | Wrong candidate distinguished |
| --- | --- | --- | --- |
| C02-STATE-01 | Start at 0. Compare “set 5; raise `bad`” with “set 8; raise `bad`.” Cleanup increments the body-left state once and retains `bad` | Failure `bad` with state 6, versus failure `bad` with state 9 | Both bodies become the identical error `bad` in the proposed carrier. No generic finalizer operating only on that retained information can meet both observations |
| C02-STATE-02 | Same two bodies, after changing only the carrier to retain failure state; append cleanup with ordinary short-circuiting bind | States 6 and 9 | The failing bind skips its suffix, leaving states 5 and 8. State retention alone is insufficient |
| C02-STATE-03 | Same initial state and bodies; catch `bad`, then run cleanup from the original initial state | States 6 and 9, still with `bad` | This alternative would increment 0 to 1 in both cases. Catching the error does not recover the state left by the body |
| C02-STATE-04 | Same bodies; run the increment twice | States 6 and 9 | The wrong results would be 7 and 10. The “once” requirement is observable and must be part of the finalizer law |

A positive finalization control is a body that returns a value after setting state to 5: cleanup should return that same value with state 6. For failure, the repaired controls are the two body results `(bad, 5)` and `(bad, 8)` carried into cleanup, yielding `(bad, 6)` and `(bad, 9)`. These tuple descriptions record expected observations; they are not proposed Lean implementation.

The smallest representation repair returns state on every modeled body exit: a computation maps initial state to a pair consisting of an error-or-value outcome and final state. Equivalently, both failure and success alternatives can explicitly contain state. This changes the result information; it does not require another free-program carrier. If cleanup registrations themselves can change during execution, they also must survive failure, though registration behavior is not specified in this packet.

The smallest operation repair is an exit-aware finalizer: run the body, retain its exit and state, run cleanup once from that state, then return the original exit together with the cleanup-left state. For this packet, cleanup is the terminating, nonfailing increment, so the result is fully specified for both body outcomes. Failing cleanup, interruption, multiple finalizers, and loops are outside these particular witnesses and would need explicit additional contracts before a broader claim.

Required local statements are: body outcomes retain their actual final state; cleanup receives that state on either body outcome; the increment occurs once; and the original value or `bad` is retained. A target connection must then relate those modeled exits and states to actual catch/finalizer execution. The supplied fact that a target can catch `bad` establishes neither that its handler receives failure-side state nor that cleanup runs once. Host behavior remains unverified.

## Evidence and next handoff

The supplied rules decisively contradict the proposed universal equation and distinguish the inadequate cleanup representations and implementations. No bounds beyond the explicit finite witnesses were explored, and no proof assistant or host checked them. No claim is made about other table instructions, schedules, or a live repository implementation.

A builder can receive the history/domain correction and the state-retaining, exit-aware finalization contract without choosing a new modality. Before implementation, a separate frozen battery should use these exact witnesses and positive controls against pinned definitions and signatures. An implementation cannot claim those checks passed until they run. Any later detector test must distinguish an intended semantic rejection from an unrelated parse or build failure.

No user decision is needed for the smallest correction: retain the existing semantics, history premise, and full history; retain state on failure; and make cleanup exit-aware. User input becomes necessary only if the intended product instead demands a changed empty-table meaning or a wider cleanup outcome policy. The missing exact auxiliary signature prevents asserting a new local theorem today, but does not block this review or its concrete witnesses.

## Sources and work limits

The packet and applicable instructions were read from [case 02](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/evaluations/cases/02-sequencing-and-cleanup.md), [AGENTS.md](/Users/pooks/Dev/lean4-effect4/AGENTS.md), and [COORDINATION.md](/Users/pooks/Dev/lean4-effect4/COORDINATION.md).

Skill and reference files used:

- [lean-reification-model](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/SKILL.md), [model record](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/assets/model-record.md), [representation decisions](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/references/representation.md), and [effects and logic](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-model/references/effects-and-logic.md).
- [lean-reification-breaker](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-breaker/SKILL.md), [attack catalogue](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-breaker/references/attacks.md), and [counterexample record](/Users/pooks/Dev/lean4-effect4/skills/lean-reification-breaker/assets/counterexample-record.md).
- [EffHOL adaptation record](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/references/effhol.md) and [evidence vocabulary](/Users/pooks/Dev/lean4-effect4/skills/lean-reification/references/evidence.md).

No workflow ambiguity blocked a useful result. Instructions about executable batteries, durable project IDs, and live project authority were treated as requirements for a later implementation handoff, not authorization to write tests or inspect the real implementation during this documentation-only exercise.
