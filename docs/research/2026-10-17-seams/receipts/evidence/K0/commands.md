# K0 command records

The adjacent JSON files retain argument arrays, working directories, times, statuses, and log paths.

### array-host-final

```text
opam exec --switch=effect4 -- dune exec --root ocaml lcnf/test_array_conversion.exe
```

Exit: `0`.

### array-host

```text
opam exec --switch=effect4 -- dune exec --root ocaml lcnf/test_array_conversion.exe
```

Exit: `0`.

### audit-imports

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake build ProofGraph.AxiomAudit
```

Exit: `0`.

### axiom-audit-final

```text
python3 /private/tmp/seams-lean-one.py lake env lean -DwarningAsError=true scratch/seams/K0Audit.lean
```

Exit: `0`.

### axiom-audit

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true scratch/seams/K0Audit.lean
```

Exit: `1`.

### base-reader-audit

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake env lean scratch/seams/K0ReadersBaseAudit.lean
```

Exit: `1`.

### base-reader-build

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake env lean -o .lake/build/lib/lean/K0ReadersBase.olean scratch/seams/K0ReadersBase.lean
```

Exit: `0`.

### baseline

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake build Effect4.Store.Domain.Word Effect4.Store.Domain.Pin Effect4.Api Conform.Manifest.Readers Test.Store.NodeContract Test.Store.WordContract Test.Codegen.SchemaGenerationContract
```

Exit: `0`.

### batteries-touched

```text
python3 /private/tmp/seams-lean-one.py make batteries-touched BASE=c752e565b4e1afac95d1258b0a4a570b81bcdf81
```

Exit: `0`.

### check-ocaml-final-review

```text
python3 /private/tmp/seams-lean-one.py make check-ocaml
```

Exit: `0`.

### check-ocaml-final

```text
python3 /private/tmp/seams-lean-one.py make check-ocaml
```

Exit: `0`.

### check-ocaml

```text
python3 /private/tmp/seams-lean-one.py make check-ocaml
```

Exit: `2`.

### final-metadata-fixed

```text
python3 /private/tmp/seams-lean-one.py python3 /private/tmp/seams-k0-final-meta.py
```

Exit: `0`.

### final-metadata

```text
python3 /private/tmp/seams-lean-one.py python3 /private/tmp/seams-k0-final-meta.py
```

Exit: `1`.

### gen-cas-final

```text
python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only cas
```

Exit: `0`.

### gen-cas

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 python3 scripts/generate.py --only cas
```

Exit: `0`.

### gen-derived

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 python3 scripts/generate.py --only derived
```

Exit: `0`.

### gen-lcnf-final-review

```text
python3 /private/tmp/seams-lean-one.py python3 scripts/generate.py --only lcnf
```

Exit: `0`.

### gen-lcnf

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 python3 scripts/generate.py --only lcnf
```

Exit: `0`.

### gen-semantics-final

```text
python3 /private/tmp/seams-lean-one.py make gen-semantics
```

Exit: `0`.

### gen-semantics-make

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 make gen-semantics
```

Exit: `2`.

### gen-semantics

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 python3 scripts/generate.py --only semantics
```

Exit: `2`.

### isolated-native-check

```text
opam exec --switch=effect4 -- bash ocaml/engine/tools/gen-check.sh
```

Exit: `0`.

### lean-cuts

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake build Effect4.Api Effect4.Store.Domain.Word Effect4.Store.Domain.Pin Test.Store.NodeContract Test.Store.WordContract Test.Store.ProgramContent Test.Codegen.SchemaGenerationContract
```

Exit: `1`.

### mirror-red

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake env lean -DwarningAsError=true Test/Codegen/MirrorReaders.lean
```

Exit: `1`.

### narrow-2

```text
/Users/pooks/Dev/lean4-effect4/scratch/lean-slot.sh env LEAN_NUM_THREADS=3 lake build Effect4.Api Effect4.Store.Domain.Word Effect4.Store.Domain.Pin Test.Store.NodeContract Test.Store.WordContract Test.Store.ProgramContent Test.Codegen.SchemaGenerationContract Test.Codegen.MirrorReaders
```

Exit: `0`.

### narrow-final

```text
python3 /private/tmp/seams-lean-one.py lake build Effect4.Api Effect4.Laws.Program.Simulation.Evaluate Effect4.Store.Domain.Word Effect4.Store.Domain.Pin Conform.Manifest.Readers Test.Store.NodeContract Test.Store.WordContract Test.Store.ProgramContent Test.Codegen.SchemaGenerationContract Test.Codegen.MirrorReaders
```

Exit: `0`.

### ocaml-build

```text
opam exec --switch=effect4 -- dune build --root ocaml engine/bytes/test/test_math.exe engine/test/prop_trace.exe engine/test/test_log.exe engine/bench/bench_frame.exe
```

Exit: `0`.

### source-controls-final-2

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `1`.

### source-controls-final-3

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `0`.

### source-controls-final-4

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `0`.

### source-controls-final-review

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `0`.

### source-controls-final

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `1`.

### source-controls-fixed

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `0`.

### source-controls

```text
python3 docs/research/2026-10-17-seams/receipts/evidence/K0/controls.py
```

Exit: `1`.
