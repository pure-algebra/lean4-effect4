# D2 probe: one program in three JSON spellings

The program is the first request of `ocaml/engine/test/kit/tool-requests.jsonl`, its `program`
field, in `program.json`. Two commands print it:

    python3 /private/tmp/seams-lean-one.py lake env lean --run docs/research/2026-10-20-coherence-audit/probes/d2/D2.lean docs/research/2026-10-20-coherence-audit/probes/d2/program.json
    cd ts/eff && bun --no-install ../../docs/research/2026-10-20-coherence-audit/probes/d2/v.ts ../../docs/research/2026-10-20-coherence-audit/probes/d2/program.json

At `29f55957e` and later: the tagged print with arrays (`ShapeDoc.printTree`) is 485 bytes; the
tagged print with `cons` cells (`ShapeDoc.print`, under `Canonical.print`) is 558 bytes; face 7's
positional form (`toJson`, `ts/eff/json.gen.ts`) is 215 bytes.
