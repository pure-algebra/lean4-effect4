# Parameterized layer identity review

Check the connection between parameter contexts and memoized layer identity at `f00008ee`.
Keep production files and the active implementation unchanged.
The preceding review is `785b6b76`.

## Finish criteria

Check small admitted programs with distinct parameter bindings at one layer address.
Retain closed-layer and fresh-build controls.
Identify any mismatch between the admitted type and the observed exit.
Distinguish current path identity from proposed invocation unfolding.
Record commands, their results, source hashes, and the evidence limits.

## Placement

Concept: `store-typing`; property: a memo entry has its declared columns.
Claim: `denote-typed`; role: a control for the memo-cell invariant.
Consumers: `memoGet_implements`, `memoize_typed`, and `layerPointTyped_redirect`.
Reach: admitted parameterized definitions sharing a layer address through the memo map's parent chain.
Premises: checked source, fixed run decisions, finite compile and machine budgets.
Limits: finite observations establish neither general preservation nor outside-runtime agreement.
Unlock: choose the context contract required by CX1 and CX2, serving R4 and M6.

A second observation tests the proposed invocation-unfolding claim under `translation-simulation`.
Its consumer is CX4 and the later transport of library laws to reusable definitions.
It compares named successful exits only; path identity can change allocation and sharing.
No new theorem or program representation is proposed here.

```mermaid
flowchart LR
  P[Passed programs] --> L[Layer construction at one address]
  L --> M[Memo entry in an enclosing map]
  M --> H[Later caller reads the stored result]
  H --> T[Check declared columns and observed exits]
```

## The working scope condition

Concept: `residual-program-typing`; property: checked source formation.
Question: the working goal `layerRefsScoped_of_typeOf`, consumed by `sourceWF_of_typeOf` and `denote-typed`.
The probe copies the proposed predicate into its own namespace at the pinned source.
It tests the cached-error program and a closed shared layer accepted by the current checker.
The first refutation locates the missing source premise.
The closed-layer control distinguishes a safe finite run from the stronger proposed context equality.
Neither control proves general safety of closed layers or any admission repair.
Both serve R4 and the M5 to M7 dependency chain.


## Parameter-use fold probe

Concept: `initial-algebras-folds`; property: signature agreement determines fold agreement.
Question: a proposed helper for `denote-typed`, consumed by layer-check transport across parameter contexts.
Reuse `foldMap_layer` to collect parameter indices in an expanded layer.
Reuse `readsAlg` and `cata_layer_congr_on` for the later agreement proof.
The probe checks direct reads, invocation arguments, reference expansion, and closed layers.
Reach: finite layers in programs whose checker excludes nested definition blocks.
Limits: the collector proves neither dependency completeness nor compatible cached errors.
Unlock: derived context checks without repeated module declarations, serving R4 and R5.
