# Compiler object commands receipt

The coordinator must retain the tool-audit limitation below. The battery audit passes; the combined compiler audit reports String and FilePath dependencies.

## Scope

This slice saves admitted program objects and opens their files without selecting an application.
It reads compiler inspections directly, without opening a tool document.
It adds no theorem or admission rule.

The branch is `codex/program-object-cli`.
The base is `40770f079d8d7594021691e0f0b1d39025b211e0`.
The implementation head is `268283aa27a556a3fc47a7c49f80baa4ec9286c7`.

Dependencies were cherry-picked before implementation:

| Original commit | Local commit |
| --- | --- |
| `30e263cbb` | `7de1559b1` |
| `e45087eeb` | `336e477d1` |
| `578c63e9c` | `a0fcffe64` |

## Changed files

- `tools/Compiler/Check.lean` prints the generated certificate.
- `tools/Compiler/Inspect.lean` reads the address table, rows, program and surface directly.
- `tools/Compiler/Main.lean` adds `check --out FILE.obj` and `open FILE.obj`.
- `Test/Codegen/CompilerEmit.lean` updates six calls for the inspection signature.
- `scripts/check-program-object.py` retains executable positive and negative controls.

The command parses check options before checking or writing.
It rejects one output path for multiple programs.
An admission refusal leaves an existing output file unchanged.
File errors return exit code 1; usage errors return exit code 2.

## Verification

Run from the branch's worktree:

```sh
LEAN_NUM_THREADS=3 lake build effect4 Test.Codegen.CompilerEmit Effect4.Tool.Serve ProofGraph.AxiomAudit
python3 scripts/check-program-object.py
LEAN_NUM_THREADS=3 lake build ProofGraph.ClosureAudit
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-program-domain-landing/cli-checks.lean
LEAN_NUM_THREADS=3 lake env lean docs/research/2026-10-21-program-domain-landing/cli-audit.lean
python3 -m py_compile scripts/check-program-object.py
git diff --check
```

The focused build succeeds: 1605 jobs.
The control script passes eight groups:

1. Saving preserves certificate JSON and repeats identical bytes.
2. Saving preserves the text output.
3. Opening works outside the project without a group, source file or prelude lookup.
4. Nine usage controls preserve the existing output.
5. Input and output file errors return controlled failures.
6. Version, specification, bare-node, truncated, empty and ill-typed inputs preserve generated refusal details.
7. Admission refusal leaves an existing object untouched.
8. Four direct readings match the prior tool-query results in text and JSON.

The closure tool build succeeds: three jobs.
Python syntax and whitespace checks pass.

The battery audit reports:

```text
#axiom_audit: 72 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
#closure_audit: 304 declarations; none binds a table before a returned closure
```

The combined compiler audit exits 1.
It reports 27 of 376 declarations reaching `Classical.choice`.
The retained [diagnostics](cli-tool-axiom-audit.txt) name String rendering, String parsing and FilePath operations.
The new `Compiler.CheckOptions.read` reaches that axiom through `String.startsWith`.
Compiler tools lie outside the Effect4/Test library gate.
This receipt does not claim that the combined audit passes.

The ten files in [cli-baseline](cli-baseline/) retain the previous executable's check and inspection outputs.
Every current output matches its retained bytes.
The baseline executable came from the owner checkout before this slice.
This receipt does not claim that executable was rebuilt at the base.

Reproduce the comparison:

```sh
python3 - <<'PY'
from pathlib import Path
import subprocess
root = Path.cwd()
baseline = root / 'docs/research/2026-10-21-program-domain-landing/cli-baseline'
binary = root / '.lake/build/bin/effect4'
for reading in ['check', 'types', 'rows', 'graph', 'surface']:
    args = [str(binary), 'check', '--group', 'todo'] if reading == 'check' else [
        str(binary), 'inspect', '--group', 'todo', '--what', reading]
    for form in ['txt', 'json']:
        result = subprocess.run(args + (['--json'] if form == 'json' else []),
                                capture_output=True, check=True)
        assert not result.stderr
        assert result.stdout == (baseline / f'{reading}.{form}').read_bytes()
        print(f'PASS baseline {reading}.{form}')
PY
```

## Remaining work and evidence limits

The coordinator integrates this commit and runs the affected behavior gates.
This slice does not run TypeScript or OCaml targets.
The controls are finite checks of CLI behavior and output agreement.
They establish no target-execution theorem.

The code catches write failures, but promises no atomic recovery after an operating-system write fails.
The no-write guarantee applies to usage errors and admission refusals.
The existing compiler battery's introductory comment still describes the old tool-query route.
Its assigned changes cover call signatures only.
