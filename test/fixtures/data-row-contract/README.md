# Data.Row contract reaction fixtures

These four snippets are appended to the empty `Effect4/Data/Row.lean` stub in
separate throwaway Lake projects by
`scripts/test-data-row-contract-reactions.sh`.

They exercise only frozen absence guards:

| Fixture | Forbidden public route |
| --- | --- |
| `custom-row-order.lean.txt` | `Effect4.RowOrder` |
| `unchecked-of-list.lean.txt` | proof-free `Effect4.Row.ofList` |
| `append-route.lean.txt` | `Effect4.Row.append` masquerading as union |
| `denotation-claim.lean.txt` | data-level `normalization_preserves_denotation` |

Run the fixed checks from the repository root:

```text
lake env lean -DmaxErrors=10000 --json Effect4Test/Data/RowContract.lean
./scripts/test-data-row-contract-reactions.sh
```

The first command must exit 1 at the empty stub with exactly 118 errors, all
`lean.unknownIdentifier._namedError`, naming 34 distinct frozen declarations.
The second command repeats that census in a clean throwaway project and then
must report 4/4 forbidden routes rejected.

These fixtures do not stand in for semantic implementation mutants. Once the
production implementation exists, the builder's green battery proves the
equations; a post-build breaker pass may add implementation mutants without
weakening or replacing this red-phase receipt.
