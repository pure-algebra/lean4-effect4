# Checked product replay version controls

Base: `5768f8a3`.
The replay script now checks its compiler package, compiler executable and Effect package before compiling helper controls.
It requires `@typescript/native-preview` and tsgo `7.0.0-dev.20260629.1`.
Catalogue mode requires Effect `4.0.1`.
Helper-only mode also accepts Effect `4.0.0-rc.112`.

The finite controls reject a wrong compiler package, wrong executable, rc.112 catalogue package and unsupported helper package.
Each refusal occurs before helper compilation or execution.
The supported installations both pass again.
Their diagnostics, observations and candidate source remain byte-identical to the retained evidence.
Existing evidence outputs and earlier input manifests stay unchanged.
`source-sha256.json` updates the edited script's hash and records the new version controls.
No Lean source changes or Lake build runs.

Reproduce in fresh output directories:

```sh
python3 docs/research/2026-10-08-checked-product-print-evidence/version-controls.py
python3 docs/research/2026-10-08-checked-product-print-evidence/reproduce.py --install /Users/pooks/Dev/lean4-effect4/ts/release --out /tmp/checked-product-version-release-replay
python3 docs/research/2026-10-08-checked-product-print-evidence/reproduce.py --install /Users/pooks/Dev/lean4-effect4/ts/eff --out /tmp/checked-product-version-pin-replay --helpers-only
```

The retained `version-controls.log` records the four refusals.
This check validates version declarations and the executable's report; it does not certify arbitrary installation contents.
The existing public module connection remains open.
