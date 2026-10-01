# W1 follow-up: the filter-annotation mismatch is repaired

Reviewed `03403dc87123627214bc13f9b3d33aaeefcd8eb9` against parent `74dae8d2c906efde105cd0c012b7a300c38ec25e` in `/Users/pooks/Dev/lean4-effect4-seat-W1`. Scope: the 21:16 filter-annotation finding, its controls, and the exactness statements’ boundaries. Read-only committed source plus the draft receipt; no compiler, build, generator, or repository edits.

**No remaining issue found in this bounded follow-up. The previous mismatch is repaired in both the reader and the normalizer, with accepting and refusing controls.**

- `Schema/Bridge.lean:99–110` implements exactly the eight-key policy: documentation entries are removed; all others remain, in order. `normSAlg` now applies that same operation to both `check_filter` and `check_filterGroup` (`:145–146`), and `normCheck` is the actual check fold (`:153`). `ofSchema` compares `checks.map normCheck` to the entire bare-check lists (`:179–184`). This preserves the check id, payload, schemas, aborted flag and constructor; it does not revert to id-only comparison or flatten filter groups.
- The proof includes the repair. `normS_number` exposes precisely `checks.map normCheck` (`:265–268`), and the two successful number cases of `ofSchema_exact` rewrite with the reader’s normalized-check equality (`:486–497`). Thus the extra accepted documented checks are covered by the general theorem, not only a finite guard. Tuple-element and property metadata also receive the policy (`:113–118,142–143`); annotated tuple elements have matching reader guards and proof cases.
- Positive controls are in `Test/Codegen/SchemaGenerationContract.lean:319–331`: `documentedIsInt` reads as `int`, as `nat` beside the nonnegative check, and a documented nonnegative check also reads as `nat`. The normalizer equality to `schema .int` is checked directly. Negative controls (`:335–340`) refuse `arbitrary` on either check and `parseOptions.disableChecks` on `isInt`. `red_arbitraryIsInt` (`:342–349`) pins the wrong accepting claim as an expected error. `ge5` and `groupedInt` still refuse (`:308–309`); normalization changes no check payload or constructor. The general code also refuses any other unknown annotation key, since it survives `normAnn` and prevents equality with the bare checks.
- The known rc.112 `arbitrary` consequence is explicit (`rcIntDoc`, `:353–359`): the document with `arbitrary` refuses, the one with `expected` only reads. This follows the eight-key ruling and is not silently described as full rc.112 document admission.

The proof boundary remains correct: `Bridge.ofSchema_exact` concludes against raw `Bridge.schema` (`Bridge.lean:486`), and `ofSchema_exact'` is its named-normalizer form (`:601–604`). The module explicitly excludes the unrestricted normalizing public writer (`:25–30`); `Ty.schema` still normalizes (`:642–647`). Retraction retains `closed` and `reservedFree` (`:406–407,675–680`). JSON `encode` still checks decode-back success (`Schema/Codec.lean:277–288`); `Schema.decode_iff` (`Laws/Schema/Codec.lean:1052–1061`) is about that successful domain. The receipt explicitly leaves old/new encoder-domain equality unproved. No claim of codec totality over all typed values or of later constructor coverage was introduced.

## Exact names for an optional narrow fresh control

Import `Test.Codegen.SchemaGenerationContract` and open `Effect4`, `Effect4.Schema`, `Effect4.Schema.Bridge`, `Test.Codegen.SchemaGenerationContract`. Reuse:

- `documentedIsInt`, `arbitraryIsInt`, `rcIntDoc`, `ge5`, `groupedInt`.
- `Effect4.Schema.Bridge.normS_number`, `ofSchema_exact`, `ofSchema_exact'`, `ofSchema_schema`, `normS_schema`.
- `Effect4.Schema.encode_of_decode`, `decode_of_encode`, `decode_iff`.

The exact positive/refusal guard block is `Test/Codegen/SchemaGenerationContract.lean:327–340`. An optional extra finite control can use the same `Check.named` shape with a new key such as `notInPolicy`; its annotation must survive and the number must refuse. No new probe was run here.

Receipt provenance: not present in this commit’s tree; the worktree draft `docs/research/2026-10-01-data-wave/receipt-W1.md` was read at SHA-256 `db1950cf510939e940377ee1b7ace895337124861cab1ea5ebcc1780cc7ab33d`. It reports the annotation controls (`:133–148`), narrow builds and 847-declaration axiom sweep (`:162–172`), and scoped/open claims (`:245–270`) consistently with the inspected source. Those execution results are W1-reported, not independently rerun in this review.
