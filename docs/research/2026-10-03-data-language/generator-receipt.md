# Generator bootstrap receipt

The early generator now builds before the generated Effect4 modules.
This removes decision row 194's tooling prerequisite for adding program constructors.
Hand-written consumers still require their own repairs when a constructor changes.

Base: `82d34358e84f0e823be24ba895aa382092c1754c`.
Implementation commit: `c1bc710b`.
Branch: `codex/data-language-wave`.

## Changes

`git show --stat c1bc710b` lists the exact changed files.
The slice separates early generators from catalogue generators.
Lean parses source imports; the manifest declares generated modules' imports.
Generation orders outputs before their consumers and refuses missing or cyclic dependency evidence.
Make checks source freshness before generation instead of requiring a full build.
Missing derived and variance outputs trigger their producers.
Check mode requires fresh output and refuses repository destination aliases.
Existing generated changes alter only five reproduction-command headers.

## Verification

| Command | Result and evidence scope |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build effect4gen Effect4Gen.Driver` | Passed; the early executable imports no Effect4 library module |
| `LEAN_NUM_THREADS=3 lake env lean --run tools/Effect4Gen/Driver.lean --plan` | Parsed the live source graph; the planner ordered six dependency stages |
| `python3 scripts/test-derived-plan.py` | Passed 13 finite controls, including catalogue dependencies, missing evidence, cycles, stale output and check-mode refusal |
| `LEAN_NUM_THREADS=3 python3 scripts/check-generator-bootstrap.py` | Passed; a new scratch constructor broke old generated companions, regeneration repaired them, and repeat output matched |
| `LEAN_NUM_THREADS=3 python3 scripts/generate.py --only derived` | Passed all derived stages and the final generated-module build |
| `LEAN_NUM_THREADS=3 make gen-derived` | Passed; all 26 manifest outputs matched the preceding generation byte for byte |
| `make gen-derived` again | No producer ran; the command took 0.126 seconds in this observation |
| `python3 scripts/check-language.py --strict docs/research/2026-10-03-data-language/generator-brief.md` | Passed |
| `git diff --check` | Passed |

The first driver build found a mutable-variable naming error, which the implementation repairs.
The successful build above checks the repaired source.
The changed generator tools lie outside the audited Effect4 and Test libraries.
This slice adds no library theorem, semantic obligation or trust exemption.
It changes no generated declaration body or constructor ordinal.
No whole-repository sweep or target execution check ran.

The source-input Make rule is deliberately conservative and may regenerate after an unrelated Lean source change.
The unchanged target skips its producers.
Later generation stages remain research work; this receipt makes no performance claim beyond the recorded observation.
