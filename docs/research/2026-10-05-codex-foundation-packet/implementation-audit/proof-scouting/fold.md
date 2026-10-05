# Fold and handle identity: proof scouting

Base: `4977c4f3db4db51903ed9437022fd0f27d6fa41f`.
Evidence: source inspection of existing declarations; no independent Lean check in this review.
The following three steps are proposed proof outlines, not checked new theorems.

Placement: `fold-typed-atomic-update` and `handle-identity-laws` are proposed claims in R4's open parts.
Their registry source is `tools/Tools/SemanticsRegistry.lean`.
Their concept is `store-typing`, with the membership and world-extension properties of `docs/core/semantics.md`.
The slice must place its planned goals before proving their helpers.

## 1. Close the identity atom's local obligations

Prerequisite: the ratified evaluator and typing rule admit two Ref handles or two Deferred handles, with independent payload types.

Existing shape facts in `src/Effect4/Laws/Program/Typed/Denotation.lean`:

- `fits_refOf_inv`: `Fits w v (.refOf A)` gives `∃ k, v = Val.cell k ∧ RefDeclared w k A`.
- `fits_deferredOf_inv`: `Fits w v (.deferredOf A E)` gives `∃ k, v = Val.promise k ∧ PromiseDeclared w k A E`.

Invert both arguments, then evaluate the registered kind and the two keys.
The output is a Boolean; no payload lookup or payload-type equality is required.
Reflexivity, symmetry and the exact key-equality result follow from that evaluator equation.

Close three existing interfaces, not only successful-result membership:

- `NativeAtom.Sound` / `NativeAtom.sound` in `src/Effect4/Laws/Program/Typed.lean`.
- `AtomFits` / `atomFits` in `src/Effect4/Laws/Program/Typed/Membership.lean`.
- `atom_progress` in `src/Effect4/Laws/Program/Typed/Denotation.lean`, which proves evaluation returns some value.

`AtomFits` assumes successful evaluation, so it cannot establish totality alone.
`atomFits_of_custom` is available if the two-family rule uses a custom scheme.

Dependency detail: the two inversion helpers currently live above the membership module.
Move their small statements down beside `Fits`, or factor lower helpers before reuse.
Do not import denotation into membership.

Placement: steps of `handle-identity-laws`, R4.
Immediate consumers: the atom cases of typed term progress and Queue withdrawal's comparison.
Observation: the Boolean result and exact same-kind key equality, for two values satisfying `Fits`.
Exclusions: arbitrary opaque handles, host-object identity, fairness and progress of the Queue.

## 2. Add one accumulator invariant to typed term progress

Existing statement, `Effect4.Program.Typed.evalTerm_progress`, in `Typed/Denotation.lean`:

```
sig.atomOf = nativeAtomTy → FitsAll w vals env →
  termTy sig env t = some ty →
  ∃ v, evalTerm vals t = some v ∧ Fits w v ty
```

Retain its fixed world during the pure fold.
Decode the input through `fits_list_iff` in `Typed/Membership.lean`:

```
Fits w xsValue (.list A) ↔
  ∃ xs, Val.asList? xsValue = some xs ∧ ∀ x ∈ xs, Fits w x A
```

This includes admitted list snapshots; do not assume the raw value is always `Val.list`.
Widen the initial value from `B0` to `B` using `fits_subN`.
Induct on the decoded list while maintaining `Fits w accumulator B`.
Append the accumulator and element with `envTyped_append` twice, in that order.
Apply the body's structural induction hypothesis, then `fits_subN` to its answer type.
The empty case returns the initial member without evaluating the body.

Extend the existing `argTy_weaken` / `termTy_weaken` equations in `Program/Typing/Rules.lean`.
They use the split environment `pre ++ post`, inserting at `pre.length`.
For the body, the tail is `post ++ [B, A]`; the insertion cut stays `pre.length`.
Use the same split for the evaluation-weakening equation.
This states the insertion bound structurally and works for nested folds.

Prerequisites: fold evaluation, the exact optional-accumulator checker rule, and the new atom cases from step 1.
Placement: steps of `fold-typed-atomic-update`, R4.
Consumer: T3b's `termMaps_of_typed`, then the template `syncRow_typed` Ref.modify case.
That helper is in T3b's branch and is not yet in this main snapshot.
Its later-world quantification combines `envTyped_mono` with typed term progress; do not add another store relation.

Observation: successful pure evaluation at `B`, unchanged captures, and equal results after environment insertion.
Exclusions: printed-code agreement, scheduling progress, and the Queue's transition invariant.
Atomicity uses the existing store-step connection; a pure fold needs no new machine loop.
`syncOpStep_eq_refStepOf` in `Laws/Machine/RefKernel.lean` is that connection.

## 3. Extend handle containment, then derive fresh-request exclusion

Extend `RawHandles.evalTerm_handles` in `src/Effect4/Laws/Machine/TermHandles.lean`:

```
evalTerm env t = some v →
  Store.Val.handles v ⊆ env.flatMap Store.Val.handles
```

For the fold, maintain this subset for its accumulator.
`asList_handles` puts each decoded element's handles inside the list value's handles.
The input and initial-value induction hypotheses put both inside the outer environment.
The body hypothesis adds only the current accumulator and element, so transitivity closes the step.
This proof needs successful evaluation, not typing, and preserves raw kind bytes and indices.

The existing consumers then remain useful:

- `RawHandles.evalTerm_registered` in `Laws/Program/Handles/Term.lean`.
- `termKernel_frames` and `RefKernel.Frames.keeps` in `Laws/Machine/RefKernel.lean`.

These carry the result through both the answer and writeback of Ref.modify.
They already handle nested values, rather than requiring a special list-of-handles judgment.

For freshness, use `fits_live` and `KindLive` in `Typed/Membership.lean`.
An old fitted value cannot contain a Ref key whose old `Ρ` lookup is none.
The Deferred argument uses the old `Π` lookup in exactly the same way.
Obtain the fresh-key premise from actual allocation and typed cell columns:

- `CellsTyped.promise_fresh` in `Typed/Adequacy.lean` supplies it for Deferred.
- `CellsTyped.addRef` proves the Ref freshness fact internally from `cells.heap`; extract that small fact if reused.
- `refMake_extension` and `deferredMake_extension` in `Typed/World.lean` supply allocation extension.
- `fits_mono` transports old membership along `World.leHost`.

Prerequisites: step 1's key-equality equation and step 2's successful typed fold evaluation.
Placement: handle-containment and fresh-allocation steps of `handle-identity-laws`, R4.
Consumer: Queue request enrollment and withdrawal; a newly allocated hint cannot match an earlier stored request.
Observation: absence of that fresh kind/key pair from earlier fitted values, and stable comparisons after world extension.
Exclusions: identity correspondence with JavaScript objects, order or multiplicity of handles, and allocation freshness from world order alone.
The target's identity correspondence remains a separate relation and acceptance obligation.
