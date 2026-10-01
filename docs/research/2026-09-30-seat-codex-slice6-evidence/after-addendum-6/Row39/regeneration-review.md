# Row 39 stage 4: selected declarations and final generation

**Run the fixed producer chain once after all four source slices.** The renderer move does not identify a new selected LCNF declaration or a private-name change, but it does invalidate the Makefile's Canonical/Node and core trace inputs. A chain run at stage 2 cannot be called the final fresh measurement after stages 3–4. Keeping stage 2 as a narrowly checked source checkpoint, with the row 39 producer verification explicitly pending, avoids both stale final evidence and two unnecessary complete cuts.

This is a static review. No compiler, generator, make command or repository edit was performed. The live source is the committed slice-1 tree (`f0591f36`) plus root's active slice-2 work; stage 4 was read from `/private/tmp/row39-series/04-of-shape/rendered/`.

## What moves, and what does not

Stage 4 moves eleven public names under the unchanged `Effect4.Store` namespace: nine executable definitions (`identifierKey`, `refKey`, `hexPattern`, `digestPattern`, `render`, `renderFields`, `renderCases`, `renderDef`, `ShapeDoc.document`) and two law theorems (`identifierKey_lawful`, `refKey_lawful`). The operational renderer block and the two key definitions are byte-identical to the current source. Only the two law proof bodies are restated. The new module contains zero `private` declarations. The original and relocated names, including namespace qualification, are unchanged; only their defining module changes.

Evidence: current `src/Effect4/Store/Domain/Shape.lean:385–464`; staged `src/Effect4/Schema/OfShape.lean:19–128`. The distinct string renderer `Effect4.Store.Shape.render` remains in Shape. The moved block introduces no change to the Shape/ShapeDoc carrier declarations, constructor signatures, canonical encoders or named derived instances.

The four current selected-declaration tables contain no moved name, its generated suffixes, or private name beginning `_private.Effect4.Store.Domain.Shape.` or `_private.Effect4.Schema.OfShape.`:

| Table | Selected rows | Matches |
| --- | ---: | ---: |
| `ocaml/gen/closure-api_engine.tsv` | 661 | 0 |
| `ocaml/gen/closure-api_gen.tsv` | 667 | 0 |
| `ocaml/gen/closure-fibers_gen.tsv` | 202 | 0 |
| `ocaml/gen/closure-machine_gen.tsv` | 38 | 0 |

These observations establish no selected-name reason to expect an LCNF diff from the move. They do **not** claim that post-move compiler output or declaration hashes have already been measured. The final fresh cut checks that remaining question. Row counts and file hashes are retained in `row39-stage4-generation-review.json`.

The actual LCNF roots remain `ocaml/gen/roots.json`: the fiber/machine roots, `Effect4.Api.run`/`replay`, the engine's named machine/compiler roots and its explicitly selected types. Stage 4 edits none of those declarations or the roots file. Its Api and Codegen edits add imports only.

## Actual generation inputs

`tools/Effect4Gen/manifest.json` selects carrier types, not `Store.render` or `ShapeDoc.document`. The Value group still selects `Store.Val`, `Kind`, `Shape`, `ShapeDoc`; those declarations stay in their old modules. The Schema group still imports `Derived.Json`, which reaches its unchanged carrier names through `Canonical → OfShape → Authoring → Document`. No manifest, guard, binder, wire-tag or algorithm edit follows from this topology.

`tools/Effect4Gen/Main.lean:907–911,999–1015` prints defining-module provenance for the **selected carrier seeds**. Moving renderer functions therefore does not change that provenance line for a selected carrier. The generator emits canonical shape/value machinery from those carriers; it does not serialize the moved renderer's proof term or defining module.

The Makefile is more conservative than selected-name analysis:

- `Makefile:96–112`: derived depends on Canonical and Node traces, among the other named traces. Stage 4 changes both import closures.
- `Makefile:121–125`: LCNF depends on the derived marker and the whole `Effect4.trace` core trace. Annotation and renderer changes can therefore make its marker stale even without a selected closure change.
- `Makefile:127–140`: eff, wire and cas depend on the core trace and their upstream markers; eff also reads the engine face. Hence a fresh derived/LCNF cut belongs before eff, wire and cas.
- `docs/GENERATED.md`, “The rule” and the derived/lcnf/cas rows, assigns freshness to this graph. The LCNF marker is deliberately absent from the automatic hermetic chain; running only `make gen-cas` does not perform the full named LCNF check.

The direct byte consumer of the move is CAS. `Store/Domain/Node.lean:324–346` constructs the meta-schema, genesis and schema addresses using `.document`. `OCaml5/Tools/CasGoldens.lean:215–224` emits the genesis, census entry and census schema observations, including `Canonical.document`. The final `gen-cas` comparison therefore matters even though the moved function text is unchanged. It checks actual domain schema/address bytes rather than merely the source-level names.

## Authority and minimal final sequence

Addendum 6 in the main checkout, `docs/research/2026-09-30-codex-brief-slice6-addendum-6.md:77–86`, says to land row 39 “as its own deletion series with narrow builds” and “no generator unless a generated group reads a deleted module (then the fixed order).” Slice 2 supplies that trigger: existing groups read Check/Image transitively. The wording does not require repeating the chain after every intermediate source checkpoint. Its deletion-series scope supports one final fixed-order measurement over all four source slices.

The original brief, `docs/research/2026-09-30-codex-brief-slice6-and-fixes.md:52–57`, keeps the producer order and the OCaml checks, and says generated changes travel with the change that caused them. Treat the source checkpoints and final verification commit as one explicitly unfinished row 39 series; retain the pre-series generated-byte baseline and attribute any final generated diff to the relevant source slice. Do not describe a source checkpoint as a completed regenerated integration or declare row 39 finished before those comparisons pass.

After slice 4's narrow source/tests and root build refresh, the single final generation command is:

```sh
LEAN_NUM_THREADS=1 make gen-derived gen-lcnf gen-eff gen-wire gen-cas
```

Then compare every actual generated diff against the retained pre-series baseline, and run the existing required `opam exec --switch=effect4 -- dune build` in `ocaml/` and `make check-ocaml`. There is no reason from this renderer move to add `make check-full`, regenerate architecture, or launch a second complete producer chain before the source series is finished.

Stage 2's existing schema host/byte check remains useful at that checkpoint: `scripts/check-schema-typescript-generation.sh:32–39` emits all three fixtures temporarily and compares them with the committed bytes. Stages 3–4 later change the producer's import closure, so the final series should retain a fresh schema-byte comparison too; the existing script is the bounded check, with no change to its three expected `.generated.ts` files unless an actual authorized behavior difference is measured.

Suggested checkpoint wording:

> Row 39 slice 2 is a source checkpoint. The named narrow build and existing schema host/byte checks passed. The full fixed-order generated-output verification is pending until the remaining annotation trim and renderer relocation are applied. No final byte-equality or completed row 39 claim is made at this checkpoint. The final source/verification commit will carry any regenerated differences from the retained pre-series baseline.

## Read-only scan commands and results

Run from `/Users/pooks/Dev/lean4-effect4-slice6`. These commands inspect source and committed closure tables; they do not invoke Lean or generation.

```sh
nl -ba Makefile | sed -n '94,140p'
nl -ba /Users/pooks/Dev/lean4-effect4/docs/research/2026-09-30-codex-brief-slice6-addendum-6.md | sed -n '77,90p'
nl -ba docs/research/2026-09-30-codex-brief-slice6-and-fixes.md | sed -n '52,58p'
```

The exact selected-name/auxiliary-prefix scan was:

```python
from pathlib import Path
import csv
root = Path('/Users/pooks/Dev/lean4-effect4-slice6')
names = ['Effect4.Store.' + name for name in [
    'identifierKey', 'identifierKey_lawful', 'refKey', 'refKey_lawful',
    'hexPattern', 'digestPattern', 'render', 'renderFields', 'renderCases',
    'renderDef', 'ShapeDoc.document']]
for path in sorted((root / 'ocaml/gen').glob('closure-*.tsv')):
    rows = list(csv.DictReader(path.open(), delimiter='\t'))
    hits = [row['lean'] for row in rows
            if any(row['lean'] == name or row['lean'].startswith(name + '.')
                   for name in names)
            or row['lean'].startswith((
                '_private.Effect4.Store.Domain.Shape.',
                '_private.Effect4.Schema.OfShape.'))]
    print(path.name, len(rows), hits)
```

Observed output:

```text
closure-api_engine.tsv 661 []
closure-api_gen.tsv 667 []
closure-fibers_gen.tsv 202 []
closure-machine_gen.tsv 38 []
```

The corresponding JSON record stores SHA-256 hashes of those exact four inputs. A source comparison separately asserted byte equality of the block beginning `/-! ## The spec: ShapeDoc.document -/` through the printer boundary, and of each annotation key definition; the two law bodies were deliberately excluded from the executable-byte comparison. The namespace remains `Effect4.Store`, and the relocated module contains zero lines beginning `private `.

Root's scheduling decision, recorded after this review: **one complete fixed-order chain after the final row 39 source slice; intermediate source checkpoints explicitly retain pending generation status.** This changes scheduling within the deletion series, not the required producer order or final comparison obligation.
