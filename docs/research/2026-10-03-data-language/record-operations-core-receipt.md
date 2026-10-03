# Record value and type operations: core receipt

The membership bridges remain uncommitted and unverified as a combined module.
This commit supplies the executable operations for the coordinator's term-constructor work.

Base: `82d34358e84f0e823be24ba895aa382092c1754c`.
Inherited helper commits: `ef94f22b` and `537f5508`.
Branch: `codex/record-operations`.

## Change

`src/Effect4/Machine/Record.lean` owns checked pairing, frame reading, construction, lookup, and overwrite.
Construction sorts whole name/value pairs after checking lengths and distinct names.
Lookup validates the whole frame before selecting a named value.
An outer `none` refuses a malformed frame.
An inner `none` reports an absent field.
Overwrite makes the replacement the first occurrence before canonicalization.

`src/Effect4/Program/Record.lean` owns operations on already computed argument types.
Construction checks duplicate names, unknown names, required fields, list lengths, and normalized subtyping.
Every input union alternative must support a field read or overwrite.
Overwrite makes its output field required at the replacement type.
The output may have a different field type and optional flag from the input.

`Program.recordParts?` moves unchanged from `src/Effect4/Program/Typed.lean` to `src/Effect4/Machine/Record.lean`.
Its declaration name and frame stay unchanged.
The original file gains an import for the new owner.

The core checker uses the definition of `Ty.subN` directly.
`Ty.subN` itself lives in `src/Effect4/Laws/Program/TypeAlgebra.lean`, which the core module cannot import.
The definition used here is `Ty.sub actual.normalize expected.normalize`.
Public program admission owns recursive declaration formation before these operations.

## Evidence

The pinned compiler is `leanprover/lean4:v4.33.1`.
`LEAN_NUM_THREADS=3 lake build Effect4.Laws.Program.Typed.RecordOperations` passed before the later bridge drafts.
That run compiled the two core operation modules and the unchanged `recordParts?` relocation.
It also compiled the first lookup membership helpers.
The later construction, union-read, and overwrite proofs are pending and stay outside this commit.

`LEAN_NUM_THREADS=3 lake env lean Test/Program/RecordOperations.lean` passed for the initial finite controls.
Those controls cover paired sorting, empty records, repeated names, unequal columns, malformed trailing columns, and presence distinctions.
They also cover required fields, unknown fields, subtyping, optional reads, union refusals, and overwrite result types.
`LEAN_NUM_THREADS=3 lake env lean Test/Program/RecordOperations.lean` also passed after retaining only its core imports.

No program progress, target execution, or host behavior follows from these finite controls.
This commit adds no theorem, so it has no new theorem axiom output.

## Integration and remaining work

The coordinator adds root imports and the test import at its assigned anchors.
The new `Ty` case sites are `Program.Record.fieldOf` and `Program.Record.setOf`.
The coordinator records their case policy and runs `make check-cases` after they enter the loaded root.
No generator input changes in this commit.

The pending bridges serve `denote-typed` through `evalTerm_progress`, as the brief records.
They must retain their executable-result equations and their `Fits` conclusions.
Term syntax, its traversals, its typing connection, and target wrappers remain the coordinator's work.
