# Slice A1, in progress: rc.112's schema documents read into `Ty`

Status: work in progress on branch `wip/a1-document-json`, off `refactor/phase1-phase3`. Nothing
here is built yet. The owner paused development on 2026-10-15 before the first build.

## The one thing to know first

The code is written and unbuilt. Build it first, then fix what the build reports. It is not
imported by any root, so it changes nothing on the integration branch until it is wired in.

## What it is

Slice A1 of the interop exploration (`docs/research/2026-10-15-ocaml-interop-explore/README.md`
§7.7, §9; decisions row 396 (2)): a schema that Effect writes as JSON reads into `Ty`, exactly.

| File | What it holds |
| --- | --- |
| `src/Effect4/Data/JsonNorm.lean` | `normJ`, `sortE`, `keyBytes`, moved from `Schema/Codec.lean` with their namespace unchanged, so a `module` file can import them |
| `src/Effect4/Schema/Codec.lean` | the move's other half: the block removed, `Effect4.Data.JsonNorm` imported |
| `src/Effect4/Schema/DocumentJson.lean` | the writer (`writeAlg`, one algebra of the representation fold), the reader (`readRepresentation`, by `_tag`, within a depth), `admit` with `admit_exact` and `admit_congr`, `DocumentRefusal` with a JSON path |
| `src/Effect4/Schema/Prepare.lean` | references resolved in dependency order (repeated, missing and recursive keys refused, at the table), unions in `Ty`'s binary shape, `tyOfJson` |
| `src/Effect4/Laws/Schema/DocumentJson.lean` | the planned goal `admit_image` and `admit_complete`, proved modulo it |
| `Test/Schema/DocumentJson.lean` | readers and controls on small documents; the fixture's lines still to add |
| `Test/fixtures/schema-documents/effect-rpc-rc112.json` | rc.112's own documents for the RPC envelope and the to-do group (sha256 `ae815b4f…d748`) |
| `harness/schema-host/export-rpc.ts` | its producer: `bun --no-install run export-rpc.ts` from `harness/schema-host` reproduces the fixture byte for byte |
| `a1probe.lean` (this folder) | the probe that prints each fixture document's read, preparation and type |

## What is left, in order

1. `lake build Effect4.Schema.Prepare Effect4.Laws.Schema.DocumentJson Tools.JsonBridge`, and fix
   the errors. Watch the mutual structural recursion of `readRepresentation` and `readCheck` on
   their fuel, and the `simp` proofs of `admit_exact`.
2. Add `"~identifier"` to `Bridge.erasedKeys` (`src/Effect4/Schema/Bridge.lean`), with its note:
   it names a reference, and decides nothing.
3. Run the probe from the repository root:
   `lake env lean docs/research/2026-10-15-a1-wip/a1probe.lean`. Write each fixture document's
   observed result into the battery as a `#guard`. Parse the fixture inside each `#guard`: Lean's
   JSON parser reaches `Classical.choice`. The hand client's drift (`Int`, `Null`, `NullOr`) and
   the failure form are controls, not defects.
4. Wire the roots: `src/Effect4.lean` imports `Effect4.Schema.DocumentJson` and
   `Effect4.Schema.Prepare`; `src/Effect4/Laws.lean` imports `Effect4.Laws.Schema.DocumentJson`;
   `Test/All.lean` imports `Test.Schema.DocumentJson`.
5. The registry (`tools/ProofGraph/Registry.lean`, the exact-codecs block): the claims
   `document-json-exact` (pointer `Effect4.Representation.ofJson_exact`) and
   `document-json-complete` (pointer `Effect4.Schema.DocumentJson.admit_complete`); then
   `make gen-semantics`.
6. `#axiom_audit` over the new modules; `make check-ts`'s codec steps (`check-schema-codec`,
   `check-schema-ts`). The move of `normJ` rebuilds every importer of `Schema/Codec.lean`.
