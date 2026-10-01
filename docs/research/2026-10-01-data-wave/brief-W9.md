# Seat W9: row 68's vectors over the wave's forms (commit 9)

Written 2026-10-01 by the coordinator from probe R's text. Base: main after commit 8 (the faces)
merges; named at dispatch. Read first: `README.md` here; row 68 (`docs/core/decisions.md`,
read-only); `tools/Tools/TyVectors.lean`, `tools/target/assignability.ts`, `generated/assignability.tsv`
(its header names the compiler, tsgo 7.0.0-dev.20260629.1), the Makefile's `check-target` and
`gen-assignability`; probe R's note Q3 "Row 68's record pairs" and
`docs/research/2026-10-01-type-language-probe/R/host/assignability/record-vectors.tsv`.

**The one thing.** The typing rule is checked against the target's compiler (row 68): a `record`
family of pairs generated from the real `Ty`, both readings of both directions, every disagreement
classified `incomplete`/`cut`/`defect`; a `defect` stops the commit.

## The work

1. Add the `record` family to `tools/Tools/TyVectors.lean`: R's 19 pairs (permutations, nested and
   tagged permutations, width and nested width, depth, the factor rule with and without literal
   discriminants, disjoint names, the empty record against `number` and against a record, record
   against tuple, `unknown`, `never`, a record against a string map, an option of permuted records)
   and the optional-key pairs under `exactOptionalPropertyTypes` (the optional flag exists since
   W0), tuples, maps, `app`, and the tagged-error class pairs. Add the written-order record arm as a
   second red control beside `subMutant` (it must be caught by the permutation pairs).
2. Expected from R's statement reading: 13 agree, 6 `incomplete` (width, nested width, the
   literal-discriminant decomposition, `{}` above `number` and above a record, a record below a
   string map), 0 `defect`. Run `make check-target` (both readings), then `make gen-assignability`
   to promote `generated/assignability.tsv`; commit the promoted file with the vectors.
3. Final: `LEAN_NUM_THREADS=4 lake build Effect4.Laws Test.All` green; `make check-target` green.

Rules: plan §4; one TypeScript compiler, tsgo 7 (the vendored preview the Makefile runs; log the
version); nothing pushed. Receipt `receipt-W9.md` here: the one thing first; the pairs with their
classifications; the control caught; the lines for row 68.
