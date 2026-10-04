# OCaml idioms receipt

Before merging: regenerate the LCNF group on the merged source head. The API and
engine outputs committed at this slice's base were already stale after the layer
changes. This commit includes their regeneration; the full generated Git diff is
not solely the cleanup. Preserve both this slice's `lcnf-idioms` case and the
coordinator's `extras-structure` case in `scripts/test-generators.py`.

Base: `71b1c9c1190ba9a633b8e97ef7c8796258f78658`.
Code commit: `93c3dfad65918de0a318563f26f6a19ad70f60c8`.
Branch: `codex/ocaml-idioms`.
Worktree: `/Users/pooks/.codex/worktrees/ocaml-idioms/lean4-effect4`.
Evidence: `/private/tmp/codex-second-eyes-2026-10-01/ocaml-cleanup/`.

## Changes and scope

- `src/OCaml5/Lcnf/Translate.lean` eliminates only `let x = rhs in x`, after
  translating both sides and recording the existing metadata, dependencies and
  refusals. No substitution, duplicated evaluation or reordering is introduced.
- `src/OCaml5/Ml/Render.lean` omits indentation on empty module declarations,
  retaining the newline and preserving nonempty/raw declarations.
- The producer regenerated `ocaml/gen/{fibers_gen,machine_gen,api_gen}.ml`,
  `ocaml/engine/api_engine.ml` and the two changed API closure manifests.
- `ocaml/eff/eff_frame.ml` uses `String.is_valid_utf_8` and `Buffer.add_buffer`.
  Payload callbacks still run once before writing the enclosing frame; copied
  payload contents remain independent of later mutations to the child buffer.
- Frame-window checks in that file and `ocaml/engine/e4_be.ml` reject invalid
  positions without overflowing integer addition before unsafe reads. Valid
  frames and the distinct checked/unchecked reader interfaces remain unchanged.
- Regression coverage lives in `Test/fixtures/generators/GenFix/Lower/Idioms.lean`,
  `Test/fixtures/generators/ocaml/idioms/`, `scripts/test-generators.py`,
  `ocaml/eff/test/{dune,test_frame.ml}` and `ocaml/engine/test/test_math.ml`.

At the same verified Lean source base, old versus simplified generation removed
5,738 lines: fibers 528, machine 79, API 2,541, engine 2,590. Exported declaration
headers and source LCNF signature comments were unchanged. The reduction is about
15% of those generated files; no runtime speedup was measured.

## Verification

Tools: Lean 4.33.1, installed OCaml 5.1.1 and Dune 3.24.2 in the existing `effect4`
switch. No installation or shared-switch change. Imported sources and artifacts
were checked against Lake traces: 128 sources and 128 artifacts, both before the
old-generator comparison and after the fresh producer build. Records are
`input-provenance.json` and `final-input-provenance.json` in the evidence directory.

From the worktree root, all exit 0:

```sh
LEAN_NUM_THREADS=1 timeout 180 lake --no-cache build OCaml5.Lcnf.Translate OCaml5.Tools.LcnfGen
LEAN_NUM_THREADS=1 timeout 180 lake --no-cache build OCaml5.Ml.Render OCaml5.Tools.LcnfGen
LEAN_NUM_THREADS=1 EFFECT4_GEN_TIMEOUT=180 python3 scripts/generate.py --only lcnf
```

The producer prepared Effect4 and the generator's dependencies; no Laws/Test root
sweep was run. Processes were sequential. Direct Lean controls used one thread,
4096 MB and a 180-second timeout; Lake used the repository's configured memory
limit. The final producer reported no missing names, diagnostics or frontier.

The permanent `lcnf-idioms` case was invoked through the existing harness Context
using saved `run-generator-checks.py`, first against the old generator (`red`),
then the repaired generator (`green`). The old output was rejected for a redundant
return binding; the repaired output and runtime checks passed. The existing
`lcnf-zipidx` case also passed. Exact subprocess commands are in `commands.jsonl`.
The new controls cover 101 inputs, callback count/order, exception short-circuiting,
shadowing, both branches, retained arithmetic bindings and physical sharing of an
allocated variant. Six matcher controls verify that the output check does not
confuse `let x = rhs in x + 1` with the exact identity continuation.

All four outputs were generated twice byte-for-byte. Final official generation
matched those outputs, with only the exact empty-line indentation correction in
the engine functor. `final-generated-hashes.json` pins all final outputs and
closure manifests; `generated-size.json` records the controlled size comparison.

From `ocaml/`, all exit 0 (each bounded to 180 seconds by `check-ocaml.py`):

```sh
opam exec --switch=effect4 -- dune build -j 1
opam exec --switch=effect4 -- dune runtest -j 1 eff gen
./_build/default/engine/test/test_math.exe
./_build/default/engine/test/test_engine.exe
E4_LEAN_CORPUS=../.lake/corpus ./_build/default/engine/test/test_diff.exe
```

The last run checked 472 programs, 2,960 tapes, 65,712 positions and 131,424
projection comparisons, with zero divergences, refused tapes or raised tapes.
Its 32 checks passed. The separate, non-gating comparison against recorded
`harness/truth/corpus.json` still reports the same two preexisting differences,
`pAcquire` and `pProvide`, as the old-generator baseline. Those differences were
not repaired by this slice; the zero-divergence count belongs to the engine corpus.

New frame tests passed 136 controls; existing Eff/wire tests also passed. The
isolated old/new comparison covered 1,227,857 UTF-8 inputs (including all Unicode
scalar encodings), 555,331 ordinary frame windows and 1,000 payloads, with no
mismatches. Extreme offsets were tested only against the repaired readers, never
the unsafe baseline. `handwritten-receipt.md` retains the exact commands and logs.
Root integration then built and ran the real linked engine tests as listed above.

Two focused reviewers checked the source changes and boundaries; the final
reviewed hashes match the committed sources. `git diff --check` passed. This is
finite compiler/host evidence, not a new Lean correctness theorem, axiom receipt,
or proof of universal runtime equivalence. No full trust gate was needed or run.

## Integration

Merge the source and test changes, retain both new generator cases, then run
`python3 scripts/generate.py --only lcnf` on the prepared merged tree. Resolve
generated-file conflicts through that producer. Run the focused generator cases
and OCaml checks above against those fresh bytes. Claude's observed head during
packaging was `8e6799741d9280ce9459257f99df385098a4a9aa`, with active data-wave
work; its files and caches were not edited by this task.

No push or integration merge was performed. This slice does not change the
representation, numeric profile, public OCaml API, or the still-open general
lowering correctness boundary. Further cleanup can follow concrete consumers;
this receipt requests no new owner decision.
