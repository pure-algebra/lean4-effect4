# S2 placement packet

The new claims serve R14 under `initial-algebras-folds`.
Their required properties are typed replacement, pending-fill construction, and publication agreement on the declared reference-free fragment.
The coordinator registers each pointer before production compilation.

| Pointer | Question and role | Reach | Exclusions | Consumer |
| --- | --- | --- | --- | --- |
| `kept_eq_certified` | kept-fill-reference; compatibility | Coherent source, nonroot address, reference-free base and filling; keepExact acceptance iff old certification | Root edits and arbitrary references | Original D1–D9 transport |
| `FillSet.add_wf` | pending-fill-construction; invariant | Every sealed FillSet, certified oracle, and submission list; conflict-free, incomparable, feed-certified entries | Admission and progress | Pending-fill tool operations and publication |
| `FillSet.publish_eq_materialize` | pending-fill-publication; compatibility | Matching snapshot/source, coherent anchor, positive base check, reference-free base and fillings, successful publication and Doc.step | Arbitrary reference composition and refused publication | Original materialization observation |

Names carry the prefix `Effect4.Program`.
All three are planned goals in `Laws/Program/FillSet.lean`.
No core constructor depends on those goals.
No row establishes native execution or host behavior.
The conditional agreement leaves every listed premise explicit.

`FillSetInternal.addEntry`, `addRaw`, and `FillSet.addOne` serve the construction claim.
The private constructor carries an exact submission-fold witness.
`FeedCertified` names the existing keepExact feed observation.
It defines no second checker or edit interpreter.

## Original D1–D9 laws

The original proofs and their premises remain in the same Laws owner.
Their old raw certification and materialization observations move to `Laws/Program/FillReference.lean`.
The names `certifiedB`, `Certified`, `materialize`, `MaterializeRefusal`, and `conflictAt` gain the `FillReference` owner.
Their bodies retain the original algorithms and refusal order.
The reference owner imports no production caller.
The new `kept_eq_certified` and `publish_eq_materialize` claims connect the executable replacements to those exact observations.

The boundary probes refute the versions lacking the reference-free premises.
The publication boundary additionally requires the initially positive base check.
Those corrections remain explicit and are not new operational feed refusals.

## Caller and refusal integration

The pending set opens only from a sealed Doc through `FillSet.open_`.
It stores the exact snapshot and source anchor.
The tool checks snapshot, base sketch, and application before publication.
Publication creates one address-ordered commit; the tool resets pending fills only after success.

Suggestions use the same keepExact feed.
A root candidate carries the actual module key used by root rechecking.
A nonroot candidate without a typed part key refuses before candidate construction.
That refusal has no invented commit-item index and no fabricated module key.
The formal checked trace remains the exact semantic dependency trace.
Runtime invocation counts, if measured, remain separate host evidence.

## Roots

Keep the existing FillSet Laws root import.
Its changed imports reach `Effect4.Laws.Program.FillReference`, so no additional direct root import is required.
The existing FillSetControls battery import reaches the added controls.
The coordinator owns global roots, central placement, and reached native exports.
No native wrapper is invented for an unreached Lean type.
