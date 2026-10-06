# Final source review of the suspension-cleanup proof route

**Role:** adversarial proof-route review. **Evidence:** frozen source inspection.
**Scope:** `c22f908def0c2a881ae46040d0dbaaaa57991352`.
**Status:** the proposed laws and proof construction remain uncompiled.
No Lean command, compiler, generator, build, runtime probe or repository edit ran.

## Verdict

The review found no false advertised `Looped` cleanup law in `brief.md` or `statements.lean.txt`.
The proposed paired-carrier construction has a concrete source route into the existing algebra.
Its generated types and constructor equations still require checking in the allocated Lean slot.
That uncompiled proof detail is not a counterexample to the proposed theorem.

Two details must stay explicit during implementation.
First, the candidate homomorphism has seven components, not only its `Eff` component.
Second, constant outside behavior applies to excluded constructor heads, not every program outside `Looped`.

## Why the paired route is supported

`FoldOf.armOf` reduces the definition's case split at a constructor.
`FoldOf.reduceCases` reduces matchers and recursors; it does not generally unfold ordinary helper definitions.
`denoteB` passes an excluded node, including its children, to ordinary `leafB`.
For example, the uninterruptible arm retains its raw body inside `leafB (.uninterruptible body)`.
`FoldOf.convert` detects that surviving child occurrence after abstracting recursive calls.
Its `needsPara` branch then pairs each family's original value with its computed result.
These declarations are in `src/Effect4/Program/FoldOf.lean`.

The source therefore gives stronger support than merely guessing a paired carrier from the fallback's spelling.
The exact elaborated carrier remains uninspected, so the existing `#check` preflight stays necessary.
`Laws/Program/Folds/Denote.lean` already owns the generated algebra and uniqueness connector.
Its introductory prose describes the observation component without detailing this pairing.
Use the generated declaration type when filling the witness.

For fixed semantic budget `k`, supply these candidate components:

```text
Eff:             e ↦ (e, fun env => denoteB k (stripSuspends e) env)
Other six sorts: x ↦ (x, ())
```

The other sorts retain their original syntax, even though the cleanup fold visits those sorts.
Their generated observation component is `Unit` because `denoteB` has no member reading them.
This satisfies their original-syntax reconstruction equations.
It also supplies the correct original children when an excluded `Eff` head reconstructs its node.

The suspension equation is particularly direct:

```text
F (suspend b) = (suspend b, fun env => denoteB k (stripSuspends b) env)
alg.eff_suspend (F b) has the same two components.
```

The original suspension stays in the proof carrier's first component.
It is absent only from the program evaluated by the second component.
Putting the cleaned tree in the first component is a false alternative: `suspend (succeed v)` and `succeed v` are different raw constructors.
That alternative cannot be equated to the existing paired observer by uniqueness.
The actual proposed route avoids it.

## Outside-fragment cases

For a noncomposite excluded head, `Straight` returns false without reading its children.
Both its original and cleaned forms therefore reduce through `leafB` to `pure (some outsideExit)`.
Nonstructural leaf fields remain identical, including operation-carried terms.
A `perform` leaf has no rewritten structural child, so it remains the same raw operation.
The fallback equations needed by the candidate homomorphism are therefore source-supported.

However, `Looped e = false` does not imply `denoteB k e env = pure (some outsideExit)`.
A bind can write a cell before its continuation reaches an excluded head.
Its denotation retains the write and can also catch the outside failure.
Accordingly, prove the fallback only at excluded heads.
Use the ordinary bind, handler and finalizer equations for their surrounding composite programs.
The brief already says “at excluded constructors”; do not broaden that wording during proof work.

The candidate homomorphism requires equations on all raw syntax.
The advertised machine law still requires `Looped`.
Equality of the denotation's unsupported fallback does not establish scheduler or target agreement there.

## Loops and complete stores

`denoteB` removes an ordinary suspension without decrementing semantic budget.
`iterateStep` passes the same fixed budget to the body under `env ++ [cursor]`.
The candidate's observation component quantifies every environment, so outer captures and nested cursor environments are covered.
`iter_congr` is available if function equality needs an explicit connector.
The loop equation may already reduce directly after unfolding the cleanup and existing algebra.
This is a proof-engineering uncertainty, not a different semantic premise.

Equality of the resulting `Effects.Program` values implies equality after applying `runP` to every `Stores` value.
`thenB` retains state from an unfinished body and skips its continuation.
It also retains state before failure and before running a finalizer.
An unfinished finalizer retains its own writes.
Consequently, the proposed observation includes unfinished results and their full stores, without adding a store-reset assumption.

Semantic budget and machine fuel remain separate.
A semantic unfinished result supplies no same-fuel machine-frontier claim.
The proposed completed-run statement correctly requires a completed bounded meaning and separate sufficient fuel bounds.
Its machine roots use the empty table, empty environment and empty stores.

## Remaining check and filing

No statement amendment is required by this source review.
Before proving the candidate, inspect `denoteB.alg`, `denoteB.hom` and `denoteB.eq_cata` in Lean.
Fill all seven candidate components, check every constructor equation, then use `hom_eq_cata_eff` and project the observation.
Retain `Looped` on the public behavior statement and use the existing completed-run connector.

`final-route-review-receipt.json` records the reviewed proposal hashes and eight exact source hashes.
Seven sources matched the earlier packet snapshots; the additional `Program/Fragment.lean` source is retained beside this report.
No finite model tests were rerun for this source-only review.
