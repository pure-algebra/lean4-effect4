# Store interface receipt

## Landing and verification

Finishing criteria: one exchange owner, four observed operations, unchanged model statements, narrow build, axiom gate, and `make check-ocaml`.
No resident cache or native adapter is counted as finished.

Changed implementation paths:

- `src/Effect4/Tool/Exchange.lean`: the interface, its `Cas` instance, and generic exchange definitions.
- `src/Effect4/Laws/Tool/Exchange.lean`: six proof reductions expose concrete port operations.

Commands and checked results:

- `python3 /private/tmp/seams-lean-one.py lake build Effect4.Tool.Exchange Effect4.Laws.Tool.Exchange Test.Program.ExchangeControls`: passed, 1,157 jobs including cache hits.
- `python3 /private/tmp/seams-lean-one.py lake build Tools.StorePortAudit`: passed.
- Audit output: `492 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals`.
- The audit imports the core, its laws and `Test.Program.ExchangeControls`.
- `make check-ocaml` runs with `LAKE` and a temporary `PATH` wrapper routing every Lean invocation through `/private/tmp/seams-lean-one.py`.

Implementation commit: `b180c4cbd66e6e1f5dd57ae87ea24365bdfa7180`.
`make check-ocaml` exits 0.
Its recorded groups pass: native in 28.796 seconds, compiler in 159.268 seconds, and OCaml in 60.355 seconds.
These durations exclude the cold generation between the groups.
The generated files have no diff.
The sealing controls and `gen-check` pass.

Exact gate command:

```sh
PATH=/private/tmp/store-build-bin:$PATH make LAKE='python3 /private/tmp/seams-lean-one.py /Users/pooks/.elan/bin/lake' check-ocaml
```

The temporary `lake` wrapper contains:

```sh
#!/bin/sh
exec python3 /private/tmp/seams-lean-one.py /Users/pooks/.elan/bin/lake "$@"
```

`check-ocaml.log` retains the complete gate output.
`narrow-build.log`, `axiom-output.log`, and `replay-probe.log` retain their exact outputs.
`Audit.lean` contains the temporary audit module's source.
Copy it to temporary `tools/Tools/StorePortAudit.lean` to reproduce the audit command.
The receipt passes `python3 scripts/check-language.py --strict`.
No store law is claimed for an arbitrary `Port` instance.
No broad battery, whole-tree axiom gate, TypeScript gate, push or merge is run.
