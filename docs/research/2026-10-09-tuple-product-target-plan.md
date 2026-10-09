# Binary product helper repair

Base: `eba00d7857d692c23e82431480f0170e3e092ca0`.
Branch: `codex/tuple-union-result`.
The coordinator investigates a shared target type repair for two-position `tuple`.
The final criterion requires every existing inference control to keep compiling.
The candidate fails that criterion, so the final slice retains finite controls only.
The source runtime values remain unchanged.

## Defect and contract

`StreamArray.independent` returns two union-valued pull answers.
`Ty.normalize` distributes its binary product into the union of all four tuple combinations.
The current generated helper instead returns a tuple whose two slots contain unions.
The pinned compiler refuses that tuple at the normalized emitted result annotation.

The repair applies `Wide` before distributing argument unions.
The result treats Boolean as one arm.
Two small nonrecursive type aliases separate Boolean arms from the other union arms.
This retains numeric and Boolean widening, string literals, and the exact types of nested values.
A two-position `tuple` returns the Cartesian product of those arms.
The `pair` helper retains its current public type and implementation.
Every other tuple arity retains its existing pointwise type.
The implementation returns the original rest tuple.
An internal implementation type signature does not become an exposed overload.
No caller cast, promised unknown result, TypeScript printer change, representation change, or compiler setting changes.

## Ownership

| Path | Change |
| --- | --- |
| `src/Effect4/Machine/Term.lean` | Candidate metadata restored to the original tracked bytes |
| `tools/Effect4Gen/PreludeAtoms.lean` | Candidate result aliases restored to the original tracked bytes |
| `harness/truth/prelude-atoms.gen.ts` | Candidate output restored to the original tracked bytes |
| `harness/truth/literals.typecheck.ts` | Binary union, arity, nested, literal, generic, and wrong-combination controls |
| `docs/research/2026-10-09-tuple-product-target-plan.md` | This plan |
| `docs/research/2026-10-09-tuple-product-target-receipt.md` | Producer, compiler, byte, runtime, and limit evidence |

The uniform atom generator reads the authoritative `NativeAtom.row.prelude` column.
The derived group owns the generated helper file.
Regenerate that group and inspect every generated diff against the one-output allowance.
The coordinator owns actual module caller regeneration and the changed compiled Term declaration audit.
The branch-joining seat owns `Stream.ArrayOps`; Claude owns the shared typed printer.

## Existing proof connection and limits

No Lean theorem changes or lands.
The source membership claim is `fits-normalize`, role compatibility, concept `store-typing`, requirement R4.
Its pointer is `Effect4.Program.Typed.fits_normalize` in `src/Effect4/Laws/Program/Typed/Membership.lean`.
The same file's `fits_normalize_prod` and `fits_normalize_tuple` serve that claim.
They equate normalized membership with the original product or tuple membership under the child normalization hypotheses.
`Ty.normalize_tuple_pair` in `src/Effect4/Program/Ty.lean` connects the two-position tuple to product normalization.

The target helper's Cartesian result follows the same binary value set.
Its direct-slot `Wide` rule remains the existing target profile restriction under decisions row 256.
Nested values retain their types; the helper performs no recursive widening.
Distributed result unions disrupt inferred `Ref.modify` result types.
The compiler accepts that tuple reader with an explicit downstream result type.
Preserving `pair` keeps existing `Ref.modify` readers and leaves its normalized-product limitation open.
An identity implementation plus finite compiler controls establishes no general target simulation theorem.
Generated metadata, source membership proofs, pinned compiler checks, and runtime controls remain separate evidence.

## Finishing criteria

Retain a negative fixture of each old helper signature.
Check all union combinations, wrong payloads, empty and single tuples, other arities, and nested generic tuples.
Retain the existing literal, Boolean, string, brand, readonly, and invariant-handle controls.
Run only pinned tsgo 7 with the release install.
Keep runtime object identities and value order unchanged.
Regenerate the exact producer output and verify repeat generation is byte-identical.
Run the appropriate narrow Lean build, the language check, and the explicit-path diff check.
Commit only the finite controls and research notes if no candidate satisfies both compiler observations.
Record the target connection that remains open.
