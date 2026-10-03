# Structural type metadata receipt

The coordinator can use `writeTy` and `readTy` without a value-frame-size premise.
The two directions retain every raw type declaration, including its original field order.

Base: `41c82479e94851c222ee06443d2818243b943342`.
Checked code head: `404d893e62163e4d987489957075700b118a66a1`.
Branch: `codex/record-contracts`.
Worktree: `/Users/pooks/.codex/worktrees/record-contracts/lean4-effect4`.
This receipt is a documentation-only follow-up to the checked code commit.

## Changed files

- `src/Effect4/Codegen/Metadata.lean`
- `src/Effect4/Laws/Codegen/Metadata.lean`
- `Test/Codegen/Metadata.lean`
- `docs/research/2026-10-03-data-language/metadata-brief.md`
- This receipt

The TypeScript writer uses the generated `Store.Val` fold.
The target expression reader checks byte bounds and canonical natural digits.
The type layer reuses `Canonical.toVal` and `Canonical.ofVal`.
The implementation adds no stored program or type representation.
It changes no existing wire tags, generators, roots, or decisions.

## Proof placement

Concept: Exact Codecs & Data Plane Embeddings (`docs/core/semantics.md`).
Proposed semantics registry claim: `type-metadata-exact`.
Role: exact embedding.
The coordinator registers `Effect4.Codegen.Metadata.type_metadata_exact` as the witness.
Its two components are `readTy_writeTy` and `readTy_exact` in `src/Effect4/Laws/Codegen/Metadata.lean`.

The judgment is structural expression equality after reading and writing.
The source domain is every raw `Ty`.
There is no formation, normalization, closedness, scope, or `Val.WF` premise.
The lower value embedding is also exact for every raw `Store.Val`.

The consumer is the new record term TypeScript printer and reader.
The claim serves R2's exact representation boundary and R3's data language.
It does not establish rendered-source parsing, TypeScript assignment, JavaScript execution, or a program simulation.
The public host boundary remains unchanged.

## Verification

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4.Codegen.Metadata Effect4.Laws.Codegen.Metadata` | Passed. |
| `LEAN_NUM_THREADS=3 lake env lean Test/Codegen/Metadata.lean` | Passed, including the axiom queries below. |
| `python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/metadata-brief.md` | Passed before the checked code commit. |
| `git diff --cached --check` | Passed before the checked code commit. |

The first proof builds exposed notation rewrites and recursive size substitutions that needed explicit steps.
Those proof bodies were repaired without changing their statements or adding premises.

The focused test printed these axiom dependencies:

```text
writeValue: no axioms
readValue: [propext]
readValue_writeValue: [propext, Quot.sound]
readValue_exact: [propext, Quot.sound]
readTy_writeTy: [propext, Quot.sound]
readTy_exact: [propext, Quot.sound]
type_metadata_exact: [propext, Quot.sound]
```

These are kernel-checked universal theorems of structural TypeScript expression equality.
The concrete controls are finite Lean checks.
They cover distinct numeric types, raw duplicate and unsorted fields, optional declarations, oversized naturals, malformed digits, wrong tags and wrong arities.
All integers in the written natural digit arrays are byte-sized.
The controls include `2^64 + 1` and `2^128 + 257` without storing either as one target number.

No target compiler, JavaScript runtime, generator, full battery or full gate ran for this slice.
The shared Lean slot was explicitly returned to the coordinator after the successful focused test.

## Integration and remaining work

The coordinator adds the API, Laws and Test imports at its chosen anchors.
The coordinator registers the combined theorem under `type-metadata-exact`.
No hand traversal of `Val` needs a census exemption: the writer is its generated fold.
The coordinator records the structural target recognizers in the traversal census if that census requires them.

Record printing still needs its canonical wrapper, readable type annotation, and exact reader integration.
The later target checks must establish the wrapper's type assignment and the requested runtime observations.
The metadata theorem does not discharge those separate obligations.
