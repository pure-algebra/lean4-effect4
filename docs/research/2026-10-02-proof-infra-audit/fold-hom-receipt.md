# Checked List.foldl_hom replacements

All four replacements below compiled unchanged in one isolated file. Exit 0 in 0.396 seconds; each theorem reports exactly `[propext]`. The original quantified variables, constructor types, hypotheses, and equation directions are preserved. The only declaration-level differences in the probe are its fresh namespace and public visibility for easy axiom printing. No production or scratch files were edited.

Source checkout: `/Users/pooks/Dev/lean4-effect4-seat-L`; HEAD `f654f2f78ab2219ff1886ae67022b70d7f107df3`. The three ExpandFix helpers are working-tree additions, not present at that HEAD. Source hashes before and after checking agree.

| Original source | Replace its equation clauses with |
| --- | --- |
| `scratch/L3.lean:688–691`, `foldl_shift` | `:= by` / `intro L x` / `exact List.foldl_hom g (fun _ _ => rfl)` |
| `src/Effect4/Laws/Program/ExpandFix.lean:184–192`, `lrounds_one` | `:= by` / `intro C hC xs a` / `exact List.foldl_hom C (fun x _ => hC x)` |
| `src/Effect4/Laws/Program/ExpandFix.lean:206–214`, `lrounds_body` | `:= by` / `intro C hC xs e` / `exact List.foldl_hom C (fun x _ => hC x)` |
| `src/Effect4/Laws/Program/ExpandFix.lean:223–227`, `lrounds_mergeAll` | `:= by` / `intro xs ls` / `exact List.foldl_hom LayerTerm.mergeAll (fun _ _ => rfl)` |

Each slash in the table marks a newline. Full pasteable declarations are in `FoldHomReplacements.lean` beside this note. Keep `private` and the original namespaces in production.

The library theorem is Lean 4.33.1 `Init/Data/List/Lemmas.lean:2812–2814`: a map commuting with each accumulator update commutes with the whole left fold. The `hC` premises of the two generic constructor helpers remain explicit; no commutation is inferred without them. `mergeAll` commutation is definitional for this one-round expansion. This validates small proof consolidation only, not a new expansion correctness property, all L3 obligations, or the other binary/mixed helper inductions.

Command (Python subprocess enforced a 60-second timeout; only one compiler process ran):

```sh
cd /Users/pooks/Dev/lean4-effect4-seat-L
LEAN_PATH=/Users/pooks/Dev/lean4-effect4-seat-L/.lake/build/lib/lean LEAN_NUM_THREADS=1 /Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean -j1 -M2048 -DwarningAsError=true /private/tmp/codex-second-eyes-2026-10-01/proof-infra-audit/fold-hom-controls/FoldHomReplacements.lean
```

The probe imports only `Effect4.Program.Refs`, using existing prepared artifacts. No Lake build, artifact generation, installation, complete freshness check, or whole-project trust gate ran. This confirms the exact four statements against that prepared import environment. The compiler and direct import artifact hashes below pin the checked environment; it is not a claim to have rebuilt its transitive closure.

`compile.log` retains all output. `receipt.json` retains argv, cwd, environment overrides, timeout, exit code, elapsed time, and hashes. SHA256:

- `/Users/pooks/Dev/lean4-effect4-seat-L/scratch/L3.lean`: `0a4f8139380417495967a74788a403d5fb1589b65efbf3dc2ccb17c251974716`
- `/Users/pooks/Dev/lean4-effect4-seat-L/src/Effect4/Laws/Program/ExpandFix.lean`: `f23b64b2ec798bc0a9dc727b677ad83b6fcff69e11afd9b7a7460d0a7094eae4`
- `/Users/pooks/Dev/lean4-effect4-seat-L/src/Effect4/Program/Refs.lean`: `d0c4f64ccca5e412162545d942454605c08b082bfd98372a2cfc054b8c4a14b6`
- `/Users/pooks/Dev/lean4-effect4-seat-L/.lake/build/lib/lean/Effect4/Program/Refs.olean`: `046d3c69025eea614278b8cce26cdb28eb0b32cd6e9804dfb71a351dfd708f05`
- `/Users/pooks/Dev/lean4-effect4-seat-L/.lake/build/ir/Effect4/Program/Refs.setup.json`: `53fb88ae54c400369f04ffd3e2ca1fca682853b749d8b3cb598b9c1d74f93dc7`
- `/private/tmp/codex-second-eyes-2026-10-01/proof-infra-audit/fold-hom-controls/FoldHomReplacements.lean`: `1c48aa52c7d8722c167a5d5a9cf7ff53b0aef7e0e18c97c1ed689ea620ce12fb`
- `/Users/pooks/.elan/toolchains/leanprover--lean4---v4.33.1/bin/lean`: `1b370cfcbf44e80d1b004ab1b1ab9a4c73951f9f7c242140bcff9bc577576554`

## Independent import verification

After compilation, `python3 /private/tmp/codex-second-eyes-2026-10-01/proof-infra-audit/fold-hom-controls/check-provenance.py` passed: all 23 project sources in `Refs` and its resolved import closure match the saved Lake source hashes; all 23 imported artifacts match saved output hashes. `provenance.json` retains the identities. Copied traces retain old checkout paths for some sources; the check maps each to the same logical path in seat L and compares the current seat source bytes, rather than trusting the original checkout. No compiler or build was run for this supplemental check.
