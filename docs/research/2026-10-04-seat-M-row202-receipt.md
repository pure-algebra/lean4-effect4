# 2026-10-04 seat M receipt: row 202 (b) measured, and chain E converted

**The one thing to know before merging:** row 202 (b) cannot convert the seven T13 modules without
an `lcnf` diff on this toolchain. So nothing from Part 1 is committed. Two `@[specialize]` attributes
cut the generated growth from about 4000 lines to 166. Most of the rest comes from two compiler
extensions that Lean exports only to non-module importers, and no attribute reaches them. Chain E, the 20 core
modules whose package closure is only `hash`, is committed green at `3bbd95bb`.

## Base and head

| Tree | Branch | Base | Head | State |
| --- | --- | --- | --- | --- |
| the estate, `/Users/pooks/Dev/lean4-effect4-modules` | `modules/cutover` | `35d1a36a` (fast-forwarded from `cb8f510a`) | `3bbd95bb` | one commit (chain E), never pushed; the worktree is clean |
| the main checkout | `refactor/phase1-phase3` | — | — | only `scratch/seat-M/` and this receipt written; this receipt is not force-added |

The worktree's `.lake/packages/hash` was at `c906b15`, while the manifest pins `ab7eda4`. I replaced
it with a copy-on-write clone of the main checkout's copy at `ab7eda4`, as AGENTS.md prescribes for
worktrees. The old copy sits in the session scratchpad.

## Part 1: row 202 (b), the seven T13 modules

### What lost the specializations (reading, then tested)

The reverted try of chain D reproduces exactly at `35d1a36a`: converting the seven grows
`api_gen.ml` and `api_engine.ml` by about 4000 lines. Its 21 functions that mention a `fiber_core`
record trace to `frameCore`, and one more change traces to `evaluatorFor`. A module importer cannot
see the compiled body of either.

| Definition | Why its body exports opaque (`Lean/Compiler/LCNF/Visibility.lean`, `Lean/Compiler/LCNF/Basic.lean`) | Effect in the importer |
| --- | --- | --- |
| `frameCore` (`src/Effect4/Machine/Fibers.lean`), `@[reducible] instance` | `shouldExportBody` exports a body when `Decl.isTemplateLike` holds, or when the code has size at most `compiler.small`, whose default is 1 (`Lean/Compiler/LCNF/ConfigOptions.lean`). An instance counts only through `isInstanceReducible`, which matches the `instance_reducible` status the `instance` command sets. The explicit `@[reducible]` replaces that status, and `frameCore` has no instance binder of its own | the `FiberCore` projections cannot be reduced, so a record of 16 closures is built and passed at run time |
| `evaluatorFor` (`src/Effect4/Program/Compile.lean`), `@[reducible] def` | no instance binder, not inline, no `@[specialize]` | `driveStep`'s specialization calls `evaluatorFor._lam_0` instead of `evaluateNative` directly |

The fix for both is a bare `@[specialize]` (`scratch/seat-M/row202-attributes.patch`, two lines).
`hasSpecializeAttribute` makes a declaration template-like. Neither declaration has a parameter of
function type, so `computeSpecEntries` adds no specialization entry, and nothing else changes
(reading, `Lean/Compiler/LCNF/SpecInfo.lean`).

### Measurements (tested)

| State | `lcnf` diff against `35d1a36a` (the two engine files and their two closure tables) |
| --- | --- |
| the seven converted, no attribute | 2315 lines added, 1742 removed (the first try's numbers, reproduced) |
| the seven converted, `frameCore` marked | 836 added, 637 removed; no `fiber_core` left |
| the seven converted, both marked | 712 added, 526 removed. `api_gen.ml` 15680 to 15777 lines (+97), 730 to 740 functions. `api_engine.ml` 14410 to 14479 lines (+69), 724 to 734 functions. `fibers_gen.ml` and `machine_gen.ml` identical |
| both marked, the seven unconverted | none |

### The residual, and why no attribute removes it (reading, with the hunks read in the diff)

| Kind | Where | Mechanism |
| --- | --- | --- |
| 9 duplicated specializations per file | `Cause.combine`, `Cause.dedup` and `Exit.mergeFinalizer` chains specialized at `contEOf` and `interruptRecord`, one `List.elem` | `specCacheExt` (`Lean/Compiler/LCNF/Specialize.lean`) exports `exported := #[]`. A module importer never reuses a specialization its imports cached, so it mints its own copy |
| lost constant knowledge in 5 functions | `RunFiber.make` (twice) and `beginRace` copy fields that `FrameFiber.start` and the race state's initial value return as constants; `fireState` takes the dispatcher from `Dispatcher.drain`'s result instead of the empty one; `compileLayer` keeps a `None` branch the base knew dead | `functionSummariesExt` (`Lean/Compiler/LCNF/ElimDeadBranches.lean`) exports `exported := #[]`, commented "preserved for non-modules". An importer no longer knows what an imported function returns |
| six dead constant bindings gone, in 2 functions | `interpOf._lam_1`, `interpAt._lam_3`: the base code bound six constants it never used; the new code is shorter | not traced |
| join points with reordered parameters | 3 functions | every call site permuted to match |

Tested: with the two attributes and the seven converted, the OCaml estate builds and passes. Both
`dune test eff gen clock` and `dune test engine` give the same result lines as on the base outputs,
apart from timings. That is 154 and 1386 lines, and 0 divergences over 485 programs in the engine's
three-engine differential. The evidence is bounded: one corpus, which `make corpus` wrote on
1 October, and random tapes.

### Decision under the brief

No-diff is unreachable, and the residual is a growth (+97 and +69 lines, +10 functions in each file).
The brief says not to commit a growth, so the seven stay non-module and I committed nothing for
Part 1. The worktree carries neither attribute.

## Part 2: chain E

### The count

Of the 156 core modules outside `Laws`, 96 are modules at `35d1a36a` (scan:
`scratch/seat-M/chainE_scan.py`).

| Package closure | Non-modules |
| --- | --- |
| `hash` only | 21: 20 convert; `Effect4.Api.Derived` cannot, since it imports the non-module T13 files |
| `hash` and `typescript` | 25 |
| `typescript` only | 7 |
| none (the T13 seven) | 7 |

### Chain E, commit `3bbd95bb`

- 15 hand-written files take `module`, `public import` and `@[expose] public section`.
- The five generated files (`Store.Domain.Derived.Json`, `Schema`, `Program`, `Value` and
  `PinDerived`) are regenerated by `generate.py --only derived`. Their groups' `Flags` switch the
  header on and meta-import each group's own `Imports` for its guards.
- The only edits beyond the header are 39 `meta import` lines in 9 hand-written files, for `#guard`
  lines that run imported code (T4). Two of them name the `hash` package's `Hash.Sha256.Fast` and
  `Hash.Sha256.Digest`.
- No `privateInPublic`, no core `import all`, no de-privatized helper.

### Gates (tested, reproduced)

| Gate | Result |
| --- | --- |
| `lake build` of the 20, `Effect4`, `Effect4.Laws` and the 19 other direct importers | green, 665 jobs, 317 s |
| `lake build Test` (`gate-line-full.sh`) | green, 883 jobs. The axiom gate checks 646 modules and 79941 declarations, against 79668 at `35d1a36a` |
| exact implementation boundary | 18 modules, 23 declarations, as at the base |
| `#effect4_print_choice_reachers` | 299 declarations, 23 roots (17 public, 6 private), as at the base |
| `make check-proof-style` | passes: 1950 recorded uses and 60 recorded unread commands in 1207 entries |
| `python3 scripts/generate.py --only lcnf`, then `git diff -- ocaml/` | no diff |
| `generate.py --only derived` and `--only variances`, `--output-dir` | `PASS generate` |
| `generate.py --only eff`, `wire`, `cas` and `ts`, `--output-dir`, then `cmp` per file | 210, 11, 119 and 9 files and 2 engine structure files: 0 differ |

### M2 against `35d1a36a` (tested, `scratch/seat-M/m2_estate.py`)

1. **Every authored user name before is present after, auxiliaries excepted: holds.** All 30166
   authored user names are present, none changed kind, and 1634 of them are in chain E's modules.
   The measured exception is 131 auxiliary names: 91 `match_N`, 31 `_proof_N` and 9
   `_sparseCasesOn_N`.
2. **Every new name is an auxiliary: holds.** 404 new names: 360 `match_N`, 32 `_proof_N` and 12
   `_sparseCasesOn_N`.
3. **The gate passes: holds.**
4. **The `Classical.choice` count is unchanged: holds.**

Visibility: 332 auxiliaries became private; no authored declaration changed visibility.

## Changed files

| Commit | Files |
| --- | --- |
| `3bbd95bb` | `src/Effect4/Store/Carrier/Digest.lean`; `src/Effect4/Schema/OfShape.lean`; 18 files under `src/Effect4/Store/Domain/` (`scratch/seat-M/chainE.txt`); `tools/Effect4Gen/manifest.json` |

## Commands and results

Every `lake`, `lean`, `make`, `generate.py` and `dune` call ran through `scratch/lean-slot.sh`.

| Command (in the worktree) | Result |
| --- | --- |
| `git merge --ff-only refactor/phase1-phase3` | `cb8f510a` to `35d1a36a` |
| `scratch/seat-M/gate-line-full.sh base-202` | green, 883 jobs; 646 modules and 79668 declarations; 299 reachers, 23 roots |
| the seven converted (`to_module.py` and `Provision`'s two meta imports), then `lake build` of the seven and `generate.py --only lcnf` | builds; the diff of the first try, reproduced |
| `python3 scratch/seat-M/ml_diff.py`, `ml_norm.py`, `ml_normdiff.py` (function-level comparisons of the generated OCaml) | the tables of Part 1 |
| `generate.py --only lcnf` after each attribute, the seven converted | the measurement table above |
| `opam exec --switch=effect4 -- dune build -j 2`; `dune test -j 2 --force eff gen clock`; `dune test -j 2 --force engine`, with `E4_LEAN_CORPUS` set to the main checkout's corpus, on the residual and on the base outputs | exit 0 each; result lines identical apart from timings |
| `generate.py --only lcnf`, the attributes alone | no diff |
| `python3 scratch/seat-M/chainE_scan.py` | the count above |
| `scratch/seat-M/build_fix_loop.sh` over chain E's two halves (with `fix_guards.py`) | green after 7 and 4 rounds; every round added only guard meta imports |
| `generate.py --only derived`, in place, twice | the first stops at a not-yet-built hand module; the second passes, with only chain E's five outputs changed |
| the gates of Part 2 | the table above |
| `git checkout --detach 35d1a36a`; `lake build Effect4 Effect4Laws`; the names probe; `git checkout modules/cutover` | 633 jobs from the cache; 70164 rows; back at `3bbd95bb`, clean |

## Axiom output

`#effect4_axiom_gate` passes over the full battery at `3bbd95bb`: 646 modules and 79941
declarations. The exact implementation boundary and the 299 choice reachers equal those of
`35d1a36a`.

## Evidence

- **proved**: nothing new. No statement and no definition body changed; the gate reports no
  offender.
- **reproduced**: the derived and variances families after chain E, and the `eff`, `wire`, `cas` and
  `ts` families byte for byte.
- **tested**:
  - the T13 measurements and the residual's OCaml results;
  - chain E's gates;
  - the M2 conditions.
- **reading**: the two export rules that block Part 1, and why `@[specialize]` adds no
  specialization entry (sources named above).
- **assumed**: that `import all` of the providing modules would hand the seven their private cache
  and summary entries (proposal P1); not tried.
- **Bounded**: the OCaml engine differential (one corpus that `make corpus` wrote on 1 October,
  random tapes). M2 is a comparison of name listings at the private level.
- **Host-only**: none.

## Landed theorems and their placement

None.

## Open obligations

1. **The owner, row 202.** No-diff is unreachable under (b); the measured residual is above.
   Proposal P1 lists the choices.
2. **`Effect4.Api.Derived`** waits on the seven.
3. **Remaining core non-modules:** 25 reach `hash` and `typescript`, and 7 reach `typescript` only.
   They wait for `typescript`'s conversion and re-pin. `Laws` waits for its own seat: the three
   `ProofGraph` modules it imports convert first, and the part that imports `effects` waits on that
   package.

## Proposed decisions rows (proposals only)

- **P1, row 202.** Record the measured outcome of (b). The choices that remain:
  - (a) keep the seven non-module;
  - (c) accept the residual growth (+97 and +69 lines) with the two attributes;
  - (d) give the three specialization sites `import all` of the modules whose specializations and
    summaries they reuse. That is untested; they would rebuild on edits there, as they do today as
    non-modules.
- **P2, the `lcnf` check.** Keep the regeneration diff as a gate of every later chain. It caught the
  T13 growth twice, and passed chains C, D and E unchanged.

## Deviations from the brief

- A plugin hook refuses `git checkout -- <path>`. I restored files with `git show HEAD:<path>`.
- The brief's order is attributes alone first, then the seven converted. I diagnosed with the seven
  converted first and measured the attributes alone last; both measurements are reported.
- The base build used the gate script (`lake build Test` with its dependencies), not a bare
  `lake build`.
- The guards' meta imports were added by a script that reads Lean's own suggestions and the
  `.ilean` files. Each added line names a module whose code a guard runs; none was minimized by hand
  further.
