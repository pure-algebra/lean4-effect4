# Flow diagnostic precision contract

Status: FROZEN / RED, breaker-authored 2026-08-31

Implementation fence: `Effect4/Flow/Admission.lean`

Battery: `Effect4Test/Flow/DiagnosticPrecisionContract.lean`

Counterexample: `E4-FLOW-CE-016`

## Claim boundary

The admission packet already proves that every returned error names the first
failing admission clause. This packet closes the narrower proof edge that was
left open: the reported site and payload must be the exact first witness inside
that clause.

The contract adds proof predicates and three proof edges over the existing
`RawFlow`, `Diagnostic`, `FirstDiagnostic`, `CheckedFlow`, `diagnoseAt`, and
`admit` declarations. It adds no flow carrier, checker, program syntax, or
semantic evaluator. In particular, it does not expose or constrain private
checker helper names.

## Source-order convention

Every finite scan uses the authored `List` order. `FirstFailureAt` records an
index, the item found at that index, the failure carried by that item, and the
absence of any failure at every smaller source index.

Nested scans are lexicographic:

1. blocks are checked in `raw.blocks` order;
2. within a selected block, successors are checked in
   `RawTerm.successors` order; and
3. `choose` therefore checks its left successor before its right successor.

This is whole-document order. Reachability does not filter any of these scans.

## Public declaration DAG

Binder names may differ. Names, universes, argument roles, constructor order,
constructor premises, result indices, and theorem propositions are frozen by
the Lean battery.

### D0 — generic first source failure

```lean
structure FirstFailureAt
    (source : List alpha)
    (FailureAt : Nat -> alpha -> beta -> Prop)
    (index : Nat) (item : alpha) (failure : beta) : Prop where
  source_at : source[index]? = some item
  fails_at : FailureAt index item failure
  prior_clear : forall priorIndex priorItem,
    priorIndex < index ->
    source[priorIndex]? = some priorItem ->
    forall priorFailure, Not (FailureAt priorIndex priorItem priorFailure)
```

The failure relation receives the source index. This is required for duplicate
and adjacent-order failures, whose meaning depends on the prefix before the
current row. Quantifying `priorFailure` prevents a proof from excluding only
the payload eventually selected while ignoring a different earlier failure.

### D1 — the eleven ordered local term failures

```lean
inductive TermFailureValid
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty)
    (block : RawBlock Ty) : DiagnosticPayload Ty -> Prop
```

Its constructors, in order, are:

1. `retTypeMismatch` — `ret` input differs from `raw.resultTy`;
2. `jumpMissing` — the jump target does not resolve;
3. `jumpTypeMismatch` — the resolved target input differs from the source;
4. `performUnknownOperation` — operation lookup fails, regardless of target;
5. `performMissingTarget` — the operation resolves but its target does not;
6. `performRequestTypeMismatch` — both resolve and the request type differs;
7. `performAnswerTypeMismatch` — request typing passes and the answer target
   type differs;
8. `chooseMissingLeft` — the left child does not resolve, regardless of right;
9. `chooseMissingRight` — left resolves but right does not;
10. `chooseLeftTypeMismatch` — both resolve and the left input differs; and
11. `chooseRightTypeMismatch` — both resolve, left typing passes, and the right
    input differs.

The premises freeze precedence as well as classification. For example, an
unknown operation wins over a missing target, a missing right child wins over
a left type mismatch, and a left type mismatch wins over a right mismatch.
Each constructor fixes the exact expected/actual or missing-identity payload.

### D2 — validity of all thirteen admission diagnostics

```lean
inductive Diagnostic.Valid
    (alphabet : FlowAlphabet Ty) (raw : RawFlow Ty) :
    Diagnostic Ty -> Prop
```

The constructors cover all thirteen `AdmissionClause`s:

- `alphabetMismatch` fixes `.flow` and expected/actual alphabet IDs;
- `duplicateBlockId` uses the first block whose ID occurs in its prefix;
- `duplicateDecisionId` uses the first `choose` whose decision ID occurs in
  the preceding block prefix;
- `nonCanonicalBlockOrder` uses the first positive index whose predecessor is
  not strictly smaller;
- `emptyRoots` fixes `.flow/.none` and proves the root list is empty;
- `duplicateRoot` and `nonCanonicalRootOrder` use first root-row witnesses;
- `entryNotRoot` fixes the entry site and entry block-ID payload;
- `danglingRoot` uses the first unresolved root;
- `danglingSuccessor` nests `FirstFailureAt` over blocks and then successors;
- `unknownOperation` uses the first source block performing an unresolved
  operation;
- `entryMissing` and `entryTypeMismatch` are the two exact payload forms of
  the `entryTypeMismatch` clause; and
- `termTypeMismatch` nests block order around `TermFailureValid`.

The detailed constructor signatures in the battery are the semantic
definition. In particular, `.flow/.none` is valid only for `.emptyRoots` with
an actually empty root table. It is never a generic fallback witness.

### D3 — checker precision edges

```lean
theorem diagnoseAt_some_valid
    (found : diagnoseAt alphabet raw clause = some diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic

theorem FirstDiagnostic.valid
    (first : FirstDiagnostic alphabet raw diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic

theorem admit_error_valid
    (errored : admit alphabet raw = .error diagnostic) :
    Diagnostic.Valid alphabet raw diagnostic
```

`admit_error_valid` is the observational rule that excludes unrelated fallback
behavior. It constrains only the public result of `admit`; no test or theorem
mentions a private default value or private checker helper.

## Obligations and falsification

The implementation must prove the three edges without `sorry`, `admit`,
custom axioms, unsafe declarations, partial declarations, or
`Classical.choice`.

The retained positive witnesses require:

- a repeated decision ID to report the second `choose` block and that exact
  decision ID; and
- an unreachable earlier `choose` with two bad children to report the earlier
  block and its left mismatch, before the right mismatch and before a later
  block failure.

`E4-FLOW-CE-016` supplies the mutation attack. Replacing a real witness with
`Diagnostic { clause := duplicateDecisionId, site := flow, payload := none }`
cannot construct `Diagnostic.Valid`, and `admit_error_valid` prevents such a
value from being observed as an admission error.

## Trust and acceptance

The proof ceiling remains the repository allowlist `[propext, Quot.sound]`.
The breaker records the intended red state with:

```text
lake env lean Effect4Test/Flow/DiagnosticPrecisionContract.lean
```

It must fail first at the absent public `FirstFailureAt` declaration. After
implementation, acceptance additionally requires the default test root, fresh
axiom receipts for the three new proof edges, and a mutation run demonstrating
that an unrelated `.flow/.none` diagnostic fails the retained battery.
