# Data language proof report receipt

## Merge note

The proof report reads the compiled law graph and names the new claims.
Raw handle containment feeds straight-program result typing.
It does not directly establish scheduled-program progress or M7 handle validity.

Base: `50f32d1c`, descended from `82d34358`.
The commit containing this receipt supplies the resulting head.

## Changes

`Effect4.Laws` imports the record, formation, metadata and authoring laws.
The semantics registry adds `raw-formation`, `instantiated-formation`, `type-metadata-exact` and `straight-meaning-typed`.
The required properties appear in `docs/core/semantics.md`.
`generated/semantics.md` comes from the report producer.
The collection brief records the raw Schema tuple alias restriction.

## Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Laws Test.Program.TypedProgBindRed Test.Program.ProtocolPosts` | Passed; 603 jobs |
| `LEAN_NUM_THREADS=3 lake build semantics-report` | Passed; 32 jobs |
| `LEAN_NUM_THREADS=3 lake exe semantics-report /private/tmp/effect4-record-semantics-final` | Passed |
| `LEAN_NUM_THREADS=3 lake exe semantics-report /private/tmp/effect4-record-semantics-repeat` | Passed |
| `cmp generated/semantics.md /private/tmp/effect4-record-semantics-repeat/semantics.md` | Passed |

The first report invocation refused missing compiled law modules.
Building the required graph resolved that refusal.
The producer then reported each added claim as proved within the configured axiom ceiling.
The report retains inherited holes and assumption status from its compiled evidence.
No whole-library axiom gate or full battery ran.

## Proof placement

| Claim | Concept and role | Scope and consumer |
| --- | --- | --- |
| `raw-formation` | Subtyping Algebra; decidability | Raw record names and map keys; checked public admission |
| `instantiated-formation` | Residual Program Typing; compatibility | Successful row use checks substituted map keys; M5 |
| `type-metadata-exact` | Exact Codecs; compatibility | Raw type metadata in structural TypeScript expressions; record print/read laws |
| `straight-meaning-typed` | Residual Program Typing; fundamental property | Native straight programs checked in the empty environment, starting from empty stores; `ExitHasTy` |

Their witnesses retain the statements recorded in their source receipts.
The last claim registers the existing `Denote.meaning_typed` theorem; it introduces no new proof.
The metadata claim has no rendered-source parsing or target-execution conclusion.
Formation establishes neither inhabitance nor codec admission.
No claim establishes liveness.
