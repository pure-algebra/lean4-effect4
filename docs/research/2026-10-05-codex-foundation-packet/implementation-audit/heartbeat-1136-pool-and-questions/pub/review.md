# PUB attempt-law review

Status: no new semantic defect or owner decision found in the bounded review.
PUB freeze: `6d83dd31a7d2674294f3e4429ea250a98a79e22d`, clean at the initial observation.
Main freeze: `2ee2aa91`; it contains the operations' first part, not the attempt-law commit.
All conclusions below name the committed seat source, not later work.

## Exact progress

Seven laws join the public operations' step terms to existing Queue model steps.
Four additional laws replace written capture premises with explicit minted-name scope premises.
They live in `src/Effect4/Laws/Modules/Queue/Ops.lean`, under `translation-simulation`, R10.
Their named consumer is the later run-level part of `queue-expansion-agrees`.
They do not state that a wrapper run reaches their premises.

| Declaration | Premises and observation |
| --- | --- |
| `take_attempt` | `MessageTy`, native atoms, first profile, requested take, injective table, aligned typed captured environment, captured identity/hint readings and types, and cell held with membership. One atomic update returns the model reply, exact ordered notification lists, next cell, and memberships. |
| `take_withdrawal` | The same environment and cell premises; profile, injective table, and captured identity. One update returns the model's wake list and next cell with memberships. |
| `offer_attempt` | Profile, requested offer, fresh pending-offer identity, typed environment, identity/hint/message readings and types, and held member cell. One update returns the model reply, wakes and next cell with memberships. It needs no table-injectivity premise because this step does not compare request identities. |
| `offer_withdrawal` | Profile, injective table, captured identity, typed environment, and held member cell. One update removes only the pending offer and returns the model's wakes and next cell with memberships. |
| `poll_attempt` | Profile, typed environment, aligned scope, and held member cell. One update returns the model reply, accepted-offer list and next cell with memberships. No request premise is needed. |
| `size_read` | Profile, aligned value environment, and held encoded cell. `Ref.get` leaves stores unchanged; the following term reads the model size. This statement does not add a membership conclusion. |
| `bounded_makes` | Positive capacity. The empty encoded state satisfies the profile; `Ref.make` appends that value and returns its fresh index. This statement does not prove allocation world extension or membership. |

The five update proofs derive their typing equation from the existing step typing theorem.
`Types.tree` connects that equation to the exact term returned by `step_updates`.
`step_keeps_cell` supplies reply and cell membership through `fold_typed_atomic_update`.
The proofs retain `MessageTy` and each source term's reading/type premises; they do not broaden to arbitrary `Ty` or arbitrary `TermSrc`.
The supplied `msg : Nat → Val` remains an encoding of model messages, not a new storage model.

## Reuse and capture

The proofs compose `takeStep_agrees` and siblings, `step_updates`, step typing, and `step_keeps_cell`.
Size reuses `cell_read`; construction uses `empty_profile` and the existing store equation.
No model transition or program definition changes in this commit.

`src/Effect4/Laws/Modules/Waiting.lean` adds reusable name-resolution facts.
The statement keeps two distinct conditions: the name is bound, and no later binder shadows it.
`captured_answer_in_row` and its typed twin preserve the name under the current-value binder and the fold's two binders.
The proof separates same-stem depth inequality from different first-byte stems.
It does not assert that every arbitrary stem spelling is collision-free.

The four minted forms retain bound-level values and types, aligned environments, model/profile premises, and cell membership.
The offered message remains a caller's term with an explicit reading and type.
The test's variable application additionally requires an unreserved source name and its resolved level.
These are conditional local theorems; they do not establish reachability, fresh allocation, or the stores/model relation of a running wrapper.

## Evidence boundaries

`Test/Program/QueueOps.lean` proves the unshadowing conditions at manually described wrapper scopes for every caller environment.
It then applies the attempt laws with those conditions discharged.
A separate finite battery extracts actual operation-row terms and compares them against those described scopes.
That comparison covers three caller-name lists at `.nat`, with one-binder-short and swapped-name controls.
The source keeps these comparisons as guards.
They must remain labelled finite when reporting the connection to actual operation trees.
They are not a universal theorem that extracts every operation's row at every type and scope.

The battery pins all eleven law statuses as `proved` and their axioms as `[propext, Quot.sound]`.
It also pins two shared capture-helper axiom outputs.
The reported empty `nearest` lists for the base laws do not mean they have no proof dependencies.
Their bodies visibly use the shared connector and existing model/typing proofs; the plan selects its displayed population.

`Test/Program/QueueSteps.lean` now proves both removal wrappers equal the shared pass by `rfl`.
Its red control compares another function of the same source type at a concrete scope.
This closes the earlier value-versus-type-only evidence gap without replacing the shared implementation.

## Saved checks

The retained narrow build accepts the two law modules and QueueOps battery.
The saved default build ends with 987 jobs, exit 0.
Its gate reports 737 modules, 87438 declarations, 24 planned goals, and 11 declarations depending on goals.
The printed semantic/test ceiling is `[propext, Quot.sound]`, with the named implementation exceptions.
These are seat-produced results, independently read and copied here; this monitor runs no Lean or build.
No new host or engine result is claimed by this commit.
The earlier Queue engine result remains finite R1/R4 root-exit evidence.

## Recommendation and pending work

Integrate the one-step laws with their current explicit premises and evidence labels.
No new owner ruling is indicated by this review.
The distinction between universal name-scope facts and finite operation-tree binding should remain in the receipt.
If a later run theorem needs a universal extraction connector, place and prove that connector for its actual consumer then.
No extra graph framework or blanket abstraction is needed now.

The seat explicitly schedules general whole-operation typing after the acceptance traces, hygiene controls, faces, truth programs, and engine additions.
That typing is still required acceptance work; the local attempt typing derivation does not replace it.
The whole-run Queue, mask, notification, and sufficient-budget obligations remain open as already assigned.

The Pool brief at main `2ee2aa91` already requires the shared reading, typing, and store connectors.
Its wake selects waiters when the helper runs; it does not reuse Queue's selected-request list as a selection made when posting.
Its protected-use and completed-close laws remain excluded from that first Pool slice.
The new generic captured-name helpers are a reuse candidate for Pool's eventual wrapper proofs, after PUB integration.
This requires no Pool scope change or new dispatch.

Completion criteria: exact statements and dependencies read, finite bindings separated, saved trust/build evidence retained, and original file identities verified.
No new advisory, repository change, compilation, generator, runtime run, installation, or seat interruption occurs.
