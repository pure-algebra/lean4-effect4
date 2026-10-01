# CI and checking refactor: proposals (2026-09-13)

Companion to `2026-09-13-plan-and-gates-review.md` §4, which measured the cost. This note
says what to build instead, drawing on how compiler projects actually organize this, and
ends with a recommendation and a first week.

## 1. What the practice is

Five projects, read today, agree on a small number of habits.

**Lean 4 itself** (`tests/README.md`). Tests are "piles": a directory where every file is one
test, and the expected output lives beside the input as `<file>.out.expected`. A change in
output is reviewed and accepted one file at a time with `fix_expected.py`. Directories that
need a custom runner have a `run_test.sh`. The whole suite runs through `make test` (ctest)
in parallel. One rule is absolute: a test may not write into the checked-in source tree.

**rustc** (`tests/ui`). A test is a source file plus a `.stderr` snapshot beside it. The
expectation is also stated inside the source with `//~ ERROR message` on the offending line,
so the file documents what it checks. Snapshots are regenerated with `--bless` and inspected.
Output is normalized before comparison (paths become `$DIR`). Suites run in tiers
(`--pass check` is the fast half).

**dune** (the OCaml half of this repo already uses it). `dune runtest` builds every test
target; a `diff` action compares an expected file with a generated one; `dune promote` copies
the new output into the source tree when the change is intended. The build system decides
what is stale from its own dependency graph. A generated file kept in the source tree is
nothing more than an expect test of the rule that produces it.

**LLVM lit and FileCheck.** Each test file carries its own `RUN:` command and `CHECK:`
patterns; the runner is generic and parallel; there is no central table of tests.

**lambdaclass/concrete**, a language written in Lean 4. A `Makefile` is the index of about
210 targets, each a one-line call to a script under `scripts/tests/check_*.sh`, with
`make build` = `lake build`. Tiers: `run_tests.sh`, `run_tests.sh --full`, "fast surface
gates". Git hooks: `pre-push` runs the fast gates plus the gates for the areas the diff
touched; `pre-push-full` runs everything, about twenty minutes. CI (`lean_action_ci.yml`): one
`build` job with `.lake/build` cached, then a dozen gate jobs in parallel with `needs: build`,
a nightly fuzz campaign and a weekly proof replay from a fresh checkout. Golden baselines
have an accept step; a `check_docs_drift.sh` refuses docs that name artifacts that do not
exist; a `check_doc_snippets.sh` compiles every code block in the docs.

**The convention for committed generated files** (Go, Bazel, most monorepos): run the
generator in CI and fail on `git diff --exit-code`. Nobody stores per-file provenance labels
in the tree; the drift check is the diff, and staleness during development is the build
tool's job.

Against that, what this repository has built by hand is: a fingerprint label beside each of
290 generated files, four private implementations of "skip if inputs unchanged", a serial
list of eighteen checks, and a hand-maintained 620-row table of every generated file. Each of
those is a substitute for something a build system or CI already does.

## 2. Three proposals

### Proposal A. Make as the index and the graph; Lake, dune and bun underneath

This is the concrete shape, with one addition: the generated files become real Make rules
with real prerequisites, so Make's own staleness logic replaces the label files.

**Layout.**

```
Makefile                      the only entry point a person types
scripts/gen/*.sh              one script per generator group (twelve), each writes its files
scripts/check/*.sh            one script per check, unchanged in substance
tests/                        (see Proposal C)
.github/workflows/ci.yml      build job, parallel check jobs, nightly, weekly
```

**The Makefile, in outline.**

```make
LAKE ?= lake
.DEFAULT_GOAL := check

build:                                   ## lake build (serial; the one Lean build)
	$(LAKE) build

# ---- generated files: real rules, real prerequisites -------------------------
# Each group depends on the compiled generator (Lake keeps its trace) and on the
# outputs of the groups it reads. Make decides what is stale from mtimes; there
# are no label files. `make gen` runs everything that is out of date, in order,
# and `make -j gen` runs independent groups in parallel.
EFF_GEN   := .lake/build/lib/lean/OCaml5/Tools/EffGen.olean
ocaml/eff/eff_native.ml ocaml/eff/eff_manifest.txt: $(EFF_GEN) | build
	scripts/gen/eff.sh
ts/eff/eff.gen.ts ts/eff/wire.gen.ts: .lake/build/lib/lean/Tools/TsGen.olean | build
	scripts/gen/ts.sh
ts/eff/ingest/README.md: ts/eff/eff.gen.ts ts/eff/forms.gen.ts ts/eff/taxonomy.gen.ts
	bun ts/eff/ingest/render-readme.ts
harness/truth/corpus.json harness/truth/generated/%.ts: $(TRUTH_LEAN) harness/truth/prelude.ts | build
	scripts/gen/truth.sh                 # the deterministic half; the rc.112 comparison is a check
gen: <every generated file>              ## regenerate what is stale

# ---- drift: the CI convention ------------------------------------------------
check-gen: gen                           ## fail if regeneration changed a committed file
	git diff --exit-code --stat -- ocaml ts harness/truth src/Effect4/Program/Fold.lean ...

# ---- tiers -------------------------------------------------------------------
check: build check-gen check-axioms check-cases check-lean       ## after every change, < 5 min after build
check-host: check check-truth check-target check-ocaml           ## per slice
check-full: check-host check-ingest check-citations check-streams check-schema-ts  ## per wave / nightly

promote:                                 ## accept golden and expected-output changes (dune promote)
	scripts/promote.sh
```

The check targets are the existing scripts with their private caches removed; Make skips a
rule when its prerequisites are older than its target, and CI never skips. Parallelism is
`make -j4 check-full`; the single Lean *build* stays serial by being the one `build` target
everything orders after. Runs of `lake env lean --run` do not rebuild and can overlap; if
memory forbids that on the 16 GB machine, a `flock` in the two scripts that run Lean is one
line.

**CI (`.github/workflows/ci.yml`).** One `build` job that restores `.lake/build` from cache and
runs `make build`; then `check-gen`, `check-lean`, `check-host`, `check-ocaml` as separate
jobs with `needs: build` in parallel; `check-full` on a nightly cron; the axiom audit and
proof replay weekly from a fresh checkout with no cache, as concrete does. The current single
job that runs everything in sequence becomes the graph.

**What gets deleted.** The 290 `.cut-from` files and the 62 first-line labels;
`scripts/lib/stamp.sh`, the Python stamps in `check_generated.py`, `check-truth.py`,
`check-source-citations.py`; `generate.py`'s ordering and its `is_family_clean`; the 266
sidecar rows and most of the 354 artifact rows in `docs/GENERATED.md`, which shrinks to one
paragraph per group naming its generator and its consumers. The `generated-stale` and
`generated` checks collapse into `check-gen`.

**Cost.** About one week for the Makefile, the twelve `gen` scripts (mostly renames of what
`generate.py` calls), the CI split, and the deletions. Risk is low because every existing
check script keeps its body.

**What it does not do.** It does not know Lean's import graph. A Make rule depends on the
generator's `.olean`, which Lake rebuilds when anything the generator imports changes, so
staleness is correct but coarse: a change deep in `src/Effect4` marks every group stale. That
is also true today, and it is harmless once regeneration is cheap and produces no diff noise.

### Proposal B. Lake-native: the generators as Lake targets

The Lean-first version. The build file moves from `lakefile.toml` to `lakefile.lean`, and
each generator group becomes a custom target whose inputs are declared, so Lake's traces
decide staleness exactly and Lake's job system runs independent groups in parallel.

```lean
import Lake
open Lake DSL

package effect4

input_file truthPrelude where path := "harness/truth/prelude.ts"

/-- The OCaml `eff` projection: EffGen's closure is the input; the files are the output. -/
target genEff (pkg) : Unit := do
  let gen ← fetch <| pkg.target ``OCaml5.Tools.EffGen  -- the compiled generator, traced
  let job ← gen.await
  buildFileAfterDep (pkg.dir / "ocaml/eff/eff_native.ml") job fun _ => do
    proc { cmd := "lake", args := #["env", "lean", "-M4096", "--run", "src/OCaml5/Tools/EffGen.lean", "ocaml/eff"] }

@[test_driver]
script check (args) do
  -- runs the tiers; `lake test` is the entry point
  ...
```

`lake build genEff` regenerates one group; `lake build gen` all of them; `lake test` runs
the tiers through the test driver; CI is `lake build && lake test`.

**Where it fits.** For the Lean-to-Lean generators (the derived `Canonical` instances, the
typing specs, the generated fold, the printed corpus) this is exactly right: inputs and
outputs are Lean modules, Lake already has the trace of every input, and the generated Lean
file is consumed by Lake anyway. The `Effect4Gen` and `Conform` tool roots would become
targets instead of `--run` invocations orchestrated by Python.

**Where it does not.** For the groups whose producer or consumer is bun or dune (the truth
harness, the TypeScript tables, the ingest README, the OCaml goldens), Lake is a worse `make`:
the custom-target API (`FetchM (Job α)`, `buildFileAfterDep`) is the least documented part of
Lake, the diagnostics when a target's body fails are poor, and every host tool would be
invoked through `proc` from Lean with no benefit over a shell line. Nobody outside the Lean
core team runs bun through Lake.

**Cost.** Three to five days for the Lean-side groups, with a learning curve and the risk of
fighting Lake's API for a week. Doing all twelve groups in Lake would double that.

### Proposal C. The tests themselves, laid out as piles with expected output

Independent of A and B. It changes what a test *is*, in line with Lean 4 and rustc.

```
tests/
  lean/           must-compile batteries: today's Test/**/*.lean with their #guard lines (Lean's "elab pile"; unchanged)
  expect/         one Lean input file per case + <case>.expected beside it: the printed program, the printed type,
                  the wire bytes in hex, the OCaml .ty line; a generic runner; `make promote` accepts changes
  refuse/         one Lean file per counterexample with the expectation inline:
                  -- REFUSE: E4-CHECK-CE-013 admission.registration
                  the runner checks the verdict; Test/Counterexamples/REGISTER.md is generated from these files
  truth/          the rc.112 differential (its own run_test.sh)
  foreign/        the ingest census (its own run_test.sh; the full run is nightly)
  ocaml/          dune runtest
  compat/         the alphabet snapshot (families.json) and its check, run in `make check`
```

Three things this buys. Counts stop being `#guard` lines that need an edit and a rebuild:
`tests/expect/corpus-counts.expected` holds the counts and the per-program verdicts, and the
diff of that file is exactly the report DI-60 asks for. The 402-row counterexample register
stops being hand-maintained: each refusal is a file that states its own expectation next to
the program, like rustc's `//~ ERROR`, and the table is produced from them. And a golden that
moves is accepted with one command after inspection, the way dune and Lean do it, instead of
by regenerating and hoping the byte comparison agrees.

The catch-all policy (`cases-policy.json`) moves to the site as an attribute in the same
change: `@[cases_policy default (cover := [never, unit, …])]` on the function, read by the
existing Conform scan from the compiled environment; the JSON is emitted from the attributes
for the record, or dropped.

**Cost.** Two to three days for the runner, the expect pile for the 48 goldens and the 34
printed programs, and the counts file; the counterexample migration is mechanical but long
(402 rows) and can be done pile by pile.

## 3. Comparison

| | A. Make on top | B. Lake-native | C. Test piles |
| --- | --- | --- | --- |
| removes the label files and the four caches | yes | yes (for the Lean groups) | no |
| parallel checks and tiers | yes, `-j` and targets | yes, Lake jobs and the driver | orthogonal |
| exact staleness for Lean-to-Lean generators | coarse (olean mtime) | exact (traces) | — |
| host tools (bun, dune, tsc) | natural | awkward | — |
| CI shape | build job + parallel jobs + nightly | `lake test` | — |
| what a newcomer needs to know | `make help` | Lake's target API | the pile conventions |
| cost | ≈ 1 week | 3–5 days for the Lean groups | 2–3 days + migration |
| precedent | concrete, Lean 4's own `make test`, every monorepo | Lean core, Mathlib's `lake exe` tools | Lean 4, rustc, dune |

## 4. Recommendation

Do A and C together, and B later for the Lean-to-Lean generators only.

A because it is the layered practice everyone converges on: Lake builds Lean, dune builds
OCaml, bun runs TypeScript, and one `Makefile` is the graph and the index across them, with
`git diff --exit-code` as the drift check. It deletes the most homegrown machinery for the
least risk, and concrete shows the exact shape working for a language written in Lean 4.

C because the goal is the language, and the tests should read as statements about the
language: one file per construct or per refusal that says what it expects, with the
expected output beside it. That is also what makes "is construct X coherent" answerable by
opening one file.

B is worth doing for the derived instances, the specs and the fold once A has settled,
because there Lake's traces give exact staleness and the outputs are Lean modules Lake
consumes anyway. Forcing bun and dune through Lake would trade a shell line for Lean code
with worse diagnostics.

Two things to keep from the current design, because they are right: the axiom audit over the
module closure as a build-time gate, and the "declared red" list that fails in both
directions. Two rulings to amend: DI-32/DI-33 (provenance stamps and the named order) become
"generated files are expect tests; drift is `git diff`; order is the Makefile's graph"; DI-54
(two typing faces) becomes one algorithmic face plus `HasTy` and the TypeScript oracle, with
the hand-written OCaml checker retired.

## 5. The first week, concretely

| day | operation | result |
| --- | --- | --- |
| 1 | write `Makefile` with `build`, the twelve `gen` rules, `check-gen`, the three tiers, `promote`, `help`; move `generate.py`'s twelve commands into `scripts/gen/*.sh` | `make gen` regenerates in the right order; `make -j4 gen` in parallel |
| 2 | delete the 290 `.cut-from` files and the 62 first-line labels; delete `stamp.sh` and the three Python caches; strip the cache logic from each check script; `docs/GENERATED.md` to one paragraph per group | commits stop carrying 289 label files; `make check-gen` is the drift check |
| 3 | split `.github/workflows/lean_action_ci.yml` into a `build` job with the `.lake/build` cache, parallel `check-*` jobs with `needs: build`, a nightly `check-full`, a weekly no-cache proof replay | CI mirrors the tiers |
| 4 | `tests/expect/` runner and `make promote`; the 48 OCaml `.ty` goldens and the 34 printed programs move to it; `corpus-counts.expected` replaces the numeric `#guard` pins | goldens accepted by one command; DI-60's report is a diff |
| 5 | the catch-all policy as a tool-root attribute; retire `eff_typing.ml` and `eff_typed`; wire the compatibility snapshot into `make check` with a re-promoted `families.json` | no JSON edit per `match`; one typing face; the freeze has teeth |

After that week, a slice's checking cost should be the build plus about five minutes, a
typing commit about 30 files, and `make help` the only thing a new seat has to read.
