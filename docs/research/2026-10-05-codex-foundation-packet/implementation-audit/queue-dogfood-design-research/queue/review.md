# Queue steps: source review and proof reuse

Evidence: source inspection, retained probe output, and one finite Python name-resolution mirror.
Scope: the ratified QSTEPS slice and its immediate wrapper consumers.
Status: advisory. No Lean proof or repository acceptance ran in this review.

The tree moved from `6acbf790` to `09d35eaf` during review. The latter records row 255.
It ratifies all five design proposals. QSTEPS is not landed at this snapshot.
At the initial snapshot, the model lives under `Test/Program/`. No production Queue term module exists yet.
During final inspection, the coordinator starts moving the model into `Laws/Modules/Queue/`.
Those uncommitted edits are outside this review's acceptance scope.

## Recommendation: keep the design, fix authoring hygiene before promotion

The main structure is economical. One declared cell stores the state.
Existing pure terms compute its next value. One `Ref.modify` commits a mutating step.
The six model connectors remain separate from waiting, notification delivery and cancellation.
`sizeStep` stays a read, as the design table already states.

The probe's fixed fold names are safe only for the arguments its current closed callers supply.
They are unsuitable for the proposed public builders without a hygiene change.

Sources:

- `QueueSteps.enrolled`, `removeTaker`, `removeOffer`, `renewHint` and `isHead`, in
  `docs/research/2026-10-05-claude-lead/queue-readiness/QueueSteps.lean`.
- `Authoring.fold`, in `src/Effect4/Program/Authoring/Folds.lean`.
- `Names.resolve`, `Env.push`, `Env.mint`, `minted` and `var`, in
  `src/Effect4/Program/Authoring.lean`.

`fold` reads its body after appending its two names. `Names.resolve` selects the last matching name.
A caller supplies `field (var "e_t") "id"` for an outer request record.
Inside `enrolled`, that expression reads the current folded record instead.
A different request then appears enrolled because each current identity is compared with itself.
The corresponding `removeTaker` example uses outer `r_t` and removes every entry.
These inputs can stay well typed: both records carry the same identity type.
Scoping alone therefore cannot detect this capture.

The retained mirror has eight checks: two collision witnesses, distinct-name controls,
matching-identity controls, and reserved-name repair candidates.
It models the exact last-binding rule and fold environments. It does not elaborate Lean.
The current closed probe does not establish a failed production acceptance.

Smallest correction: add one authoring convenience, `foldWith`, using the existing minting pattern.
It receives its body as a Lean function over the accumulator and item terms.
It emits the existing `Term.fold`; it adds no stored syntax, binding form or loop engine.
Use it for the Queue helpers that place caller terms in fold bodies.
`accept` currently puts its caller terms in the list and initializer, outside its body.
There is no capture witness for those arguments, so do not report all fixed names as broken.

Reuse `var_push_minted` in `src/Effect4/Laws/Program/Author.lean` and the pattern of
`iterateWith_scoped` in `src/Effect4/Laws/Program/Authoring/Loops.lean`.
Keep one adversarial capture control with equal record types and unequal handle identities.
Also check nested use of the convenience; ordinary successful elaboration is insufficient.

Placement: authoring hygiene serves the scope and term-typing obligations of the Queue steps,
and their R10 `queue-expansion-agrees` connectors. It is not a new registry claim by itself.
Consumer: QSTEPS public step builders, then their wrapper.
Premises: caller terms satisfy the public authoring discipline; internal names use reserved minting.
Exclusions: this does not prove the state transition, delivery, fairness or target agreement.
Immediate prerequisite: the convenience's unchanged `Term.fold` elaboration contract.

## Reuse the current proof spine

| Consumer | Existing result | Small connector still needed |
| --- | --- | --- |
| Pure list passes | `fold_typed_atomic_update` and `ListFoldRules` in `Laws/Program/Typed/ListFold.lean` | Type each actual full-cell step term and state its exact reply/store pair |
| One atomic update | `ListFoldRules.step`, `refModify_implements`, `storeStep_typed` in the typed law graph | Connect step evaluation to the Queue state relation |
| Fresh request identity inside records | `HandleIdentityLaws.allocDeferred`, `freshDeferred`, `contained` | Prove the particular identity projection is among the cell value's contained handles |
| Straight programs of sync steps | `Straight` in `Program/Fragment.lean`, `run_eq_meaning` | Prove the constructed program is in `Straight`; retain its typing premises separately |
| Ordinary single-fiber loops | `iterateWith`, `forRange`, `foldRange`, `repeatWhile` and their scope lemmas | Use one existing loop form and prove `Looped` for its body |
| Finished ordinary loops | `Agreement.loopAgreement` in `Laws/Program/Agreement/Loop.lean` | Supply fragment membership and a finished budgeted meaning |
| Queue waiting wrapper | Current scheduler and waiting design | Prove posted delivery, cleanup and the named public observation |

`notMemberDeferred` concerns a list of raw Deferred values. Queue waiters are records.
Prefer `freshDeferred` on the typed whole cell and a contained-handle projection.
Do not add a second membership model just to bridge that shape difference.

The pure list fold is inside a sync operation. It does not turn that operation into an effect loop.
The existing straight fragment can therefore carry these atomic terms.
`Looped` adds ordinary iteration, including nested iteration, to the straight fragment.
It excludes masks, fiber operations, yielding and asynchronous rows.
The probe's waiting wrapper uses masks, posted helper forks and Deferred waits.
Neither straight nor ordinary-loop agreement covers that wrapper as a whole.
Its eight retained scenarios are finite machine evidence, not a wrapper simulation proof.

`loopAgreement` requires a finished budgeted denotation and supplies an existential sufficient fuel bound.
It does not prove termination, fairness or a constant step cost.
Retain frontier outcomes and stores when a budget ends.

Placement: reuse R4 store-typing facts beneath the six R10 step connectors.
The wrapper's law consumes those connectors and supplies the remaining scheduled observation relation.
No new Queue execution engine or general loop abstraction is justified by these consumers.

## The model move is now in progress

The brief still lists the model move after the relation and six planned goals.
Its phrase “if the owner's word asks for it” predates row 255.
At the final snapshot, the coordinator has already started the move before QSTEPS dispatch.
The new files are `Laws/Modules/Queue/{Model,Capacity,Profile}.lean`.
The Test batteries import that home and retain their controls.
This is the useful dependency order: it avoids a temporary Laws-to-Test import or a copied model.
The move is active work, not a new unresolved finding or an accepted integration.
Keep the brief's order aligned when dispatching; preserve the prior statements and their receipts.

Then land the full cell and step typing, the finite comparison controls, the relation and goals,
and proofs in the brief's stated order: size, withdrawals, offer, poll, take.
The moved model's existing profile closure and capacity laws remain distinct from those connectors.
Placement: translation-simulation, R10, `queue-expansion-agrees`, with the wrapper as consumer.
Exclusions: moving a theorem does not establish a new semantic claim.

## Pin the full cell's types, not only its field names

The design deliberately declares the full model's field inventory now.
That is useful, but it does not by itself fix the future cell type.
The research probe's offer hint is `Deferred<bool, never>`.
The abstract model answers batch offers with a remaining-message list through `Note.left`.
The full terminal phase also contains an end payload, while this slice parameterizes only message type `A`.

Before the cell declaration lands, record its actual `Ty` choices for offer replies and terminal payloads.
Either select the intended later reply shape now, or state the later representation change explicitly.
This is a contract clarification, not a demand to implement batches or terminal steps now.
The current probe is intentionally narrower; it is not a defect in accepted production code.

Consumer: later batch/termination steps and the waiting wrapper under the already selected single-cell representation.
Premises: invariant Ref and Deferred parameters and the declared full field inventory.
Observation: exact stored value and returned notification payload under the model relation.
Exclusions: no behavior outside `FirstProfile` is proved by retaining its fields.
Immediate prerequisite: the actual cell and hint `Ty` declaration in QSTEPS slice one.

## Evidence limits

The retained `QueueSteps.out` reports eight scenarios and 2,400 comparisons over 200 states.
It also reports 765 nodes and eleven folds for take, and 484 nodes and three folds for poll.
Those are the probe author's retained results; this monitor did not rerun them.
Repeated passes are ratified in row 255 and are not a current defect.
No local-binding syntax or premature optimization is recommended.

The review found no new model-profile omission. Previously repaired closure findings remain resolved.
It does not accept unfinished QSTEPS implementation, strengthen the admission bridge,
or identify an upstream Effect bug.
