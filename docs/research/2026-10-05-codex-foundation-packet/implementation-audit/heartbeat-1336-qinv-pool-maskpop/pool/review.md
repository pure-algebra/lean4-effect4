# Pool steps 1–3 review

## Scope and result

The reviewed main commit is `d4ea8243`. It includes merge `e212766f`, whose seat parent is `7f76f0b9`.
The model, profile, contract, scenarios, design, and import additions match the seat parent.
The scenario source also matches the previously reviewed `af7f6099` bytes.
Later active Pool typing and operation files are outside this review.

Source review finds no new model or proof defect. One contract sentence needs correction.
The saved coordinator build and integration checks pass. This review runs no Lean, compiler, generator, or runtime.

## One correction

`Test/contracts/pool.contract.md`, PP5 low-level control, says: “No public schedule reaches it”.
The sentence refers to an open pool with an idle item and two enrolled waiters.
That state is reachable in the already accepted PP3 scenario.
`Test/Program/PoolScenarios.lean` observes `snap [0] [] [] 2 false 1` after H returns, before its helper selects a waiter.
The same file describes this as a state of the profile.

Only posting count two at an open pool lies outside this public profile.
Keep the fixture's constructed-state label and the count-two exclusion. Remove the state-unreachability assertion.
This correction changes no model, premise, theorem, or accepted decision.
The witness is retained source and the saved successful build, not a new execution by this monitor.

## What the model establishes

`Effect4.Pool.Model.Profile` in `src/Effect4/Laws/Modules/Pool/Profile.lean` gives:

- Unique item stamps and unique available stamps.
- Exact correspondence between idle items and available stamps.
- Distinct live lease stamps, each below `next`.
- Distinct enrolled waiter identities.

The profile permits idle items beside waiters. It permits repeated resource values with distinct item stamps.
`initial_profile` also accepts an empty resource list. The structural invariant does not itself admit a public zero-size Pool.
The public positive-size requirement remains separate.

| Declaration | Exact scope | Placement |
| --- | --- | --- |
| `profile_closed` | Every one of five model transitions preserves `Profile`, assuming `Profile` initially. | store-typing, R4 |
| `lease_enrols_iff` | After lease, this identity is enrolled exactly when the pool is open and every item is borrowed. | store-typing, R4 |
| `select_takes_first` | Selection splits the current waiter list into its first `count` elements and remaining suffix. | reactive-scheduling, R12 |
| `giveBack_front` | A matching live lease returns its stamp to the available front and clears that exact lease. | scope-lifetime-finalization, R11 |
| `giveBack_once` | Immediately repeating the same return changes nothing and owes no wake. | scope-lifetime-finalization, R11 |
| `close_refuses` | Close sets `closing`, counts current waiters, and makes the following lease refuse. | scope-lifetime-finalization, R11 |

`giveBack_stale` gives an exact no-change result when no item holds the named lease.
`step_closing` preserves a true closing flag through every model transition.
`step_items` preserves the ordered item-stamp/resource projection.
These last two helpers support later history arguments. They do not prove those arguments by themselves.

The proofs use stamp uniqueness, exact idle membership, and existing list facts.
`giveBack_once` concerns two consecutive returns, not all histories with intervening operations.
`select_takes_first` concerns one atomic model selection, not callback execution or native live traversal.
Preserving resource values does not establish resource finalization or whole-run release.

## Next connecting proof route

The next useful consumer is the concrete lease-step agreement, already owned by the active Pool seat.
Its successful branch must connect an available stamp with an actual reply item.
`Profile.idle`, `Profile.stamps`, and `eq_of_stamp` already provide existence and identity uniqueness.
Use those facts when proving the `leased` filter lookup returns the selected item.

Proposed statement shape, not compiled here:

```text
Profile s → s.closing = false → s.available = i :: rest →
∃ it, it ∈ s.items ∧ it.stamp = i ∧ it.borrowed = false ∧
  (lease s id).2 = (false, some (it.leasedAs s.next))
```

This is a helper for the existing module-expansion obligation: translation-simulation, R10.
The consumer is the first-profile concrete lease transition's read/step agreement.
The observation is its exact answer and selected identity. The state invariant remains an R4 premise.
The immediate prerequisite is that consumer's placed statement and concrete state-reading relation.
It needs no injectivity of resource values. It excludes scheduling, delivery, cleanup, liveness, and whole-run agreement.
This is reuse guidance for current work, not a request for a separate implementation slice.

## Retained acceptance

The coordinator's `merge-pool-1/gates.sh` identifies each command and output file.
`gates.summary` records exit zero for build, gen-semantics, check-semantics, check-cases, check-docs, and conservativity.
`build.log` records a successful 994-job build and the following audit:

- 173 API/utility modules and 304 Laws-only modules.
- 744 modules and 88,303 declarations checked.
- Semantic/test axioms at `[propext, Quot.sound]`; the named implementation boundary retains its explicit exemptions.
- 24 planned goals and 11 declarations depending on goals; no other declaration reaches `sorryAx`.

The contract's guarded axiom output keeps each new root within `[propext, Quot.sound]`.
Its plan guards report the six placed roots proved and no next goals for that local selection.
This does not close the remaining Pool wrapper, typing, target, or whole-run obligations.
`check-semantics.log` records passing report, registry, traversal, and name controls.
`conservativity.log` ends with four of four clauses passing against `1d10d8aa`.
Its earlier refusals belong to deliberate self-test mutants; all 27 controls have expected outcomes.
The public transcript records merge completion and the coordinator's direction to continue with step four.

## Verification and exclusions

The source manifest retains frozen committed bytes. The evidence manifest retains complete saved logs and filtered public tool records.
No transcript reasoning content is included. The original transcript is identified only by path, size, and hash.
No saved acceptance command is rerun. No active repository file changes.
This review does not accept the active step-four work or claim a final Pool receipt.
