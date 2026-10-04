# 2026-10-04 seat M receipt: the module-system cutover of `hash` and of 96 package-free core modules

**The one thing to know before merging:** 96 of the 103 package-free `src/Effect4` modules
outside `Laws` are modules now. The gate passes over the full battery. Seven stay non-module
(T13). `Program.Typed`, `Program.Compile` and `Program.Admit` specialize the machine's functions.
As modules, in a reverted try, they lost those specializations, and the `lcnf` cut grew by about
4000 lines. Their
importers `Program.Admission`, `Program.Provision`, `Schema.Codec` and `Api.Frontier` stay with
them. The amended M2 holds: every authored user name is present after the conversion, auxiliaries
excepted, and the measured exception is 168 renumbered auxiliary names.

History of the night: after `hash` the wave stopped, because M2's count equality failed (the
audit counts include auxiliaries). The coordinator then ruled option 1 below into row 200
(`d8faeae2`) and started Part 2, which ran to the end.

## Base and head

| Tree | Branch | Base | Head | State |
| --- | --- | --- | --- | --- |
| `hash`, `/Users/pooks/Dev/lean4-hash` | `module-system` | `c906b15` (`main`, the estate's pin) | `13ee594` | one commit, local only, never pushed; its re-pin accepted by the coordinator |
| the estate, `/Users/pooks/Dev/lean4-effect4-modules` | `modules/cutover` | `97983cf6` (the coordinator's repaired head; first `d2bbbaf5`, then `407ed498`, each before any edit of mine) | `970246cd` | eight commits, never pushed; the worktree is clean |
| the main checkout | `refactor/phase1-phase3` | — | — | only `scratch/seat-M/` and this receipt written; the coordinator force-added an earlier version of this receipt at `d8faeae2` |

The estate commits, in order:

1. `88d9881b`, `a759f909` and `3225b1e6`: the tooling prerequisites (a), (b) and (c);
2. `d8bb17a4`, `81b8618f`, `adb9717c` and `fe5ed57c`: chains A, B, C and D;
3. `970246cd`: the Makefile's variances sources.

# Part 1: `hash`

## The M2 stop after `hash`, and the owner's options

The brief defines M2 as "the audit lines are unchanged" and stops the wave when M1, M2 or M3
contradicts the note's prediction. The note's §3(e) predicts that the gate's line and the pinned
audit lines stay equal. They did not, so the wave stopped after `hash` until the coordinator's
ruling (option 1, below).

What the measurement shows instead (tested, `scratch/seat-M/m3_diff.py` and `audit_replay.py`
over the two name listings):

- every one of the 1342 user names of the `Hash` modules is present after the conversion, with
  its kind;
- no authored declaration changed its name, kind or visibility;
- 207 auxiliaries became private names: 203 `_proof_N` theorems and 4 `match_N` matchers (T9);
- 9 auxiliaries are new: an exported term now uses a fresh public copy where it used to share
  an auxiliary that is now private. `scratch/seat-M/aux_refs_probe.lean` shows it on both builds
  (`aux-refs.txt`):
  - `Hash.Algorithm.outputBytes` used the matcher of the derived `Repr` instance,
    `instReprAlgorithm.repr.match_1`; that matcher is now private, and `outputBytes` uses a new
    `outputBytes.match_1`;
  - the statement of `Hash.Sha3.Bridge.iota_bridge` used `iota_bridge._proof_1`; it now uses a new
    `iota_bridge._proof_2`, and `_proof_1` is private;
  - the bodies of `Hash.Sha3.Spec.zsub` and `bitsOfState` now use renumbered copies (`_proof_2`;
    `_proof_2` to `_proof_4`);
- each count change is exactly this:
  - the sha256 audit drops private names (`Name.isInternal`), so it loses 3 matchers and gains 1;
  - the sha3 audit counts private names under their user names, so it gains the 5 new auxiliary
    theorems of its modules;
  - the HashTest gate counts every constant, so it gains all 9.

The estate's gate counts every constant of its audited modules too (`auditedFacts`,
`tools/ProofGraph/Audit.lean`, reads `moduleData.constNames` with no filter). So the line that
Part 2 plans to compare would move for the same reason. An equality test cannot tell this drift
from a loss of coverage.

Options for the owner:

1. **Amend M2 and relaunch Part 2 (recommended, and ruled).** The amended M2 has four conditions:
   - every user name before the conversion is present after it;
   - every name present only after it is an auxiliary (`_proof_N`, `match_N`, equation lemmas);
   - the gate passes;
   - its choice count is unchanged.

   Under this test `hash` passes. The scripts that run it are in `scratch/seat-M/`.
2. **Make the audits count authored declarations only.** Filter auxiliaries with Lean's own
   predicates in the hash audits and the estate gate, so that the counts stay invariant under
   the conversion. This touches the hash audits and `Test/Audit/AxiomGate.lean`.
3. **Keep M2 as count equality.** Then no package or estate chain can pass M2, and the cutover
   stops.

On the `hash` branch I re-pinned both audit lines, with the auxiliaries named in each verified
root, so that the branch builds green. Accepting that re-pin is part of option 1.

## The coordinator's defaults, as applied

| Default | What `hash` needed | Count |
| --- | --- | --- |
| `@[expose] public section` for definition and theorem files | the section after the module docstring in every converted file with declarations; the three import-only roots (`Hash.lean`, `Hash/Sha256.lean`, `Hash/Sha3.lean`) have none | 23 of 26 files |
| a `#guard` over imported code stays and gets its `meta import` | a plain `meta import` of the module whose code the guard runs; Lean's message suggests `public meta import`, which would put that module's `.ir` into every importer's trace (T14) | 6 lines in 3 files, for 14 guards; the 5 guards of `Hash.Sha3.Impl` run their own module's code and core only, and need none |
| `backward.privateInPublic` per declaration | the helper gets `set_option backward.privateInPublic true in`; each caller gets that and `set_option backward.privateInPublic.warn false in`; nothing in a lakefile | 8 helpers and 10 callers in 3 files; no helper de-privatized: `hash` has no exemption list (ruling R-11), and keeping the names keeps M3 and the sha256 audit stable |
| audit roots, tests and gates stay non-module | `Hash/Verified.lean`, `Hash/Sha256/Verified.lean`, `Hash/Sha3/Verified.lean`, both `Kats`, both `Audit`, `KeccakProbe`, `BridgeEvidence`, `HashTest`, `HashGates`, `hashbin` | all stay non-module |

## Changed files

`hash`, one commit on `module-system`:

| File | Change |
| --- | --- |
| the 26 files of the closure of `Hash.lean` (`Hash.lean`, `Hash/Algorithm.lean`, `Hash/Sha256.lean`, `Hash/Sha3.lean`, 11 under `Hash/Sha256/`, 11 under `Hash/Sha3/`) | `module`; 60 `import` lines become `public import`; `@[expose] public section` in 23 files |
| `Hash/Sha256/Hex.lean` | `privateInPublic`: helpers `digitTable`, `decodeAux`, `asciiChars`; callers `digit`, `digitValue?`, `decodeChars?`, `decode?`, and the theorem `decodeAux_encodeCharsOfList`, whose statement names `decodeAux` |
| `Hash/Sha3/Hex.lean` | `privateInPublic`: helpers `digit`, `decodeDigit?`, `encodeList`, `decodeList?`; callers `encode`, `decode?` |
| `Hash/Sha3/Fast.lean` | `privateInPublic`: helper `at5`; callers `theta`, `rhoPi`, `chi`; `import all Init.Data.Nat.Fold` for the `rfl` in `keccakF_abs` |
| `Hash/Sha256/Bridge.lean` | `import all` of `Init.Data.Vector.Basic`, `Init.Data.Array.DecidableEq` and `Init.Data.Array.Basic` for the `decide` in `sha256_ne_sha224_iv` |
| `Hash/Sha256/Sha224.lean` | `meta import` of `Hash.Sha256.Digest` and `Hash.Sha256.Fast` for 5 guards; `import all Init.Data.Nat.Fold` for the `decide +kernel` in `sha256_ne_hashWith_sha224IV` |
| `Hash/Sha256/Api.lean` | `meta import` of `Hash.Sha256.Digest` and `Hash.Sha256.Fast` for 5 guards |
| `Hash/Sha3/Api.lean` | `meta import` of `Hash.Sha3.Digest` and `Hash.Sha3.Fast` for 4 guards |
| `Hash/Sha256/Verified.lean`, `Hash/Sha3/Verified.lean` (non-module) | the pinned lines re-pinned to 420 and 576; the docstrings name the auxiliaries that account for the change |
| `Hash/Verified.lean` (non-module) | the docstring's two counts updated |

The estate's changed files are in Part 2. The main checkout: this receipt, and the scripts, probes
and logs under
`scratch/seat-M/`.

## Commands and results

Every `lake` and `lean` invocation ran through `scratch/lean-slot.sh`, which sets
`LEAN_NUM_THREADS=2`. Every `hash` build ran with `LAKE_ARTIFACT_CACHE=false` (see Deviations).
`hash-build.sh` is `lake build` of the ten default targets, named one by one, under `/usr/bin/time -l`.

| # | Command (in `/Users/pooks/Dev/lean4-hash` unless named) | Result |
| --- | --- | --- |
| 1 | `git checkout -b module-system` | `Switched to a new branch 'module-system'`, at `c906b15` |
| 2 | `lean-slot.sh scratch/seat-M/hash-build.sh` (baseline, cold, no `.lake` before) | `Build completed successfully (104 jobs).`; 92.13 s real, 140.56 s user, 30.79 s sys |
| 3 | `du -sk .lake/build` | `38300` |
| 4 | `lean-slot.sh lake env lean --run scratch/seat-M/hash_names_probe.lean Hash.Verified Hash private` (and `exported`) | exit 0; 1342 rows (1000 public, 342 private); 1348 rows in the exported files (6 equation lemmas realized in two modules) |
| 5 | `lean-slot.sh scratch/seat-M/m1-hash.sh baseline` | the M1 table below, non-module rows |
| 6 | `python3 scratch/seat-M/to_module.py` over the 26 files | `converted` × 26 |
| 7 | `lean-slot.sh lake build Hash`, six times, with the fix rounds `hash-fix1.sh`, `hash-fix2.sh`, `hash-fix3.sh` and one `import all` between them | round 1: 4 modules fail (T7 × 3, T3 × 1); round 2: `Sha256.Bridge` (T3), `Sha3.Api` (T4); round 3: `Sha3.Api`, `Sha256.Api` (T4); round 4: `Sha224` (T3), `Sha3.Verified` (pin); round 6: only the two pins fail |
| 8 | `lean-slot.sh lake env lean --run scratch/seat-M/t3_probe.lean Hash.Sha256.Api <roots>` | 336 definitions in the closure of the SHA-256 computation; core definitions without an exported body in `Init.Data.Nat.Fold`, `Init.Data.Nat.Bitwise.Basic`, `Init.Data.Repr` and two `Init.Prelude` internals |
| 9 | `lean-slot.sh lake build Hash.Sha256.Sha224` after `import all Init.Data.Nat.Fold` | `Build completed successfully (11 jobs).` |
| 10 | `lean-slot.sh scratch/seat-M/hash-build.sh` (converted, cold, after the re-pin) | `Build completed successfully (104 jobs).`; 131.82 s real, 183.63 s user, 47.59 s sys |
| 11 | `lean-slot.sh scratch/seat-M/m1-hash.sh converted` | the M1 table below, module rows |
| 12 | the probe of row 4 over `Hash,Hash.Sha256.Kats,Hash.Sha256.Audit,Hash.Sha3.Kats,Hash.Sha3.KeccakProbe,Hash.Sha3.BridgeEvidence,Hash.Sha3.Audit`, both modes, while the two pins still failed; rerun at the head over `Hash.Verified` | exit 0; 1351 rows (802 public, 549 private); the rerun's listing is byte-identical |
| 13 | `python3 scratch/seat-M/m3_diff.py`, `audit_replay.py`, `m3_exported.py` | the M2 and M3 sections below |
| 14 | `lean-slot.sh scratch/seat-M/hash-exes.sh` | `hash_sha256 --self-test`, `hash_sha3_512sum --self-test`, `hash_selftest`, `hash_vendorseal`, `hash_citations`: exit 0, each prints its `PASS` line |
| 15 | `lean-slot.sh env TMPDIR=<scratchpad> LAKE_ARTIFACT_CACHE=false /usr/bin/time -p lake exe hash_trustselftest` | `PASS trust self-test: every planted declaration was rejected for its stated reason and every control was accepted`; the `sorry` and `native_decide` plants land in the module root `Hash.lean` and are rejected with their expected diagnostics |
| 16 | `git add` of the 29 paths; `git commit` | `30322ba`; amended after row 17 to add M4's numbers: `13ee594`, the same tree (`git diff 30322ba 13ee594` is empty) |
| 17 | `lean-slot.sh scratch/seat-M/m4-timing.sh` | four cold builds, alternating; M4 below |
| 18 | `python3 scratch/seat-M/estate_scan.py` (reads `/Users/pooks/Dev/lean4-effect4-modules/src`, no Lean) | 425 modules, 156 outside `Laws`, 103 of them reaching no package; the forecast below |
| 19 | `lean-slot.sh bash -c "LEAN_PATH=<baseline build>/lib/lean lean --run scratch/seat-M/aux_refs_probe.lean Hash.Verified <names>; LEAN_PATH=.lake/build/lib/lean lean --run …"` | exit 0; the auxiliaries each named declaration uses, per build (`aux-refs.txt`); the baseline build is run 3's, kept in the session scratchpad |

## M1 to M5

### M1, the payoff: holds (tested)

`scratch/seat-M/m1-hash.sh` edits `Hash.Sha256.Bridge`, rebuilds it alone, hashes each of its
artifacts with `shasum -a 256`, and runs `lake build --no-build Hash.Sha256.Api`. `Api` imports
`Bridge` with `public import`; its guards' `meta import`s name `Digest` and `Fast`, not `Bridge`.
Each edit is undone from a copy and `Bridge` rebuilt before the next one. Hashes are the first 8
hex digits.

| Edit | Tree | `.olean` | `.olean.server` | `.olean.private` | `.ir` | `--no-build Hash.Sha256.Api` |
| --- | --- | --- | --- | --- | --- | --- |
| none (as built) | non-module | `9eae3631` | — | — | — | exit 0 |
| a proof: `rfl` to `exact Eq.trans rfl rfl` in `bitsOfBytes_flatMap` | non-module | `4c11a372` | — | — | — | exit 3 |
| a docstring: one word, no line shift | non-module | `6d0e5c5c` | — | — | — | exit 3 |
| a statement (red control): binder `ys` to `zs` in `bitsOfBytes_append` | non-module | `6ec06752` | — | — | — | exit 3 |
| none (as built) | module | `29ab84a0` | `2df5d606` | `f418b2f7` | `3122770a` | exit 0 |
| the same proof edit | module | `29ab84a0` (same) | `2df5d606` (same) | `6be9ab7f` | `3122770a` (same) | exit 0 |
| the same docstring edit | module | `29ab84a0` (same) | `cf53027b` | `6e0465d3` | `3122770a` (same) | exit 0 |
| the same statement edit (red control) | module | `08619589` | `2df5d606` (same) | `f418b2f7` (same) | `3122770a` (same) | exit 3 |

After every undo, every hash returns to its "as built" row and the importer's `--no-build`
exits 0, in both trees. So the parts are deterministic across rebuilds (tested, 6 rebuilds).
`hash` carries no uniform-export extension of its own, so the note's repeat of M1 on a `Laws`
chain with `@[semantics]` and `@[aesop]` remains owed.

### M2, the gate's coverage: contradicts the prediction (tested)

| Line | Before (`c906b15`) | After (module) |
| --- | --- | --- |
| `Hash.Sha256.Verified`, pinned | `sha256 axiom audit: 422 declarations across 12 modules; …; 0 reach Classical.choice; 0 offenders` | `… 420 declarations across 12 modules; …; 0 reach Classical.choice; 0 offenders` |
| `Hash.Sha3.Verified`, pinned | `sha3 axiom audit: 571 declarations across 14 modules; …; 45 reach Classical.choice; 0 offenders` | `… 576 declarations across 14 modules; …; 45 reach Classical.choice; 0 offenders` |
| `HashTest.lean`, `#hash_axiom_gate`, unpinned | `checked 47 modules and 1618 declarations (223 in the HashGates tooling tree); …; 122 declaration(s) reach Classical.choice; 0 offenders` | `checked 47 modules and 1627 declarations (223 …); …; 122 …; 0 offenders` |

`scratch/seat-M/audit_replay.py` applies each audit's own filter to the two name listings and
reproduces both moves name by name (`m2-hash-audit-replay.txt`):

| Audit | Names lost | Names gained |
| --- | --- | --- |
| sha256 (drops every private name) | `Fast.H0_eq.match_1_2`, `Fast.H0_224_eq.match_1_1`, `instReprAlgorithm.repr.match_1`, now private | `Algorithm.outputBytes.match_1`, new |
| sha3 (counts private names by user name) | none | `Bridge.iota_bridge._proof_2`, `Bridge.xor_abs_bridge._proof_2`, `Spec.bitsOfState._proof_4`, `Spec.zsub._proof_2`, `Theorems.rcv_eq_lfsr._proof_2`, all new |
| HashTest gate (counts every constant) | none | the 9 new auxiliaries |

The gate and both audits still pass with 0 offenders, and no choice count moved. The audits do
not reach less. A matcher that the sha256 audit no longer lists is still inside the axiom closure
of the declaration that uses it (`collectAxioms` follows constants; reading).

### M3, public names: holds for authored declarations (tested)

| Listing (private level, modules under `Hash`) | Before | After |
| --- | --- | --- |
| constants | 1342 (1000 public, 342 private) | 1351 (802 public, 549 private) |
| user names (private prefix removed) | 1342 | 1351: all 1342 present, 9 new |
| kind changes | — | 0 |
| public to private | — | 207: 203 `_proof_N` theorems, 4 `match_N` matchers, all auxiliaries (T9) |
| new names | — | 9 auxiliaries: 7 `_proof_N`, 2 `match_1` |

The exported part of each of the 26 converted modules, read alone (`readModuleData`), holds
every public name of the private level: 0 missing. In it, 310 theorems are axioms, as §3(b)
predicts. The 137 theorems exported with their proofs are generated: 128 equation lemmas, 3
`congr_simp`, 2 splitters, and 4 `_proof_N` of the `privateInPublic` helpers. Two definitions are
exported without a body: the two derived `instReprAlgorithm.repr` helpers, which the `Repr`
handler marks `@[no_expose]`. One oddity (tested, finite probe): `Hash.Sha3.Roundtrips` exports the private
equation lemmas `lowBits.eq_1` and `packedBits.eq_1`, but not the private definitions they name.

### M4, disk and time (tested; the times are bounded)

| Measure | Before (`c906b15`) | After (module) |
| --- | --- | --- |
| `du -sk .lake/build`, cold build of the default targets | 38300 KB | 39512 KB (+3.2%) |
| files in `.lake/build` | 568 | 777: four new parts and their `.hash` files for each converted module, and one `trace.nobuild` |
| `.olean` bytes of the 26 converted modules | 12,739,456, one part | 12,404,424 (−2.6%): exported 1,627,120, server 234,160, private 10,543,144 |
| their `.ir` and `.ir.sig` bytes | — | 633,304 and 4,576 |
| their `.c` bytes | 728,462 | 780,727 (+7.2%) |
| the toolchain's artifact cache (`du -sk`) | 4,208,216 KB | 5,371,304 KB, grown by other lanes: this seat's builds neither read nor wrote it |

A module importer loads only the exported part: 13% of the old `.olean` bytes for these modules.
Whether its import time falls in proportion was not measured.

Cold builds of the ten default targets, alternating, `LEAN_NUM_THREADS=2`, cache off:

| Run | Converted: real, user (s) | Baseline: real, user (s) | The 26 converted modules' compile time, converted against baseline (s) |
| --- | --- | --- | --- |
| 1 | 131.82, 183.63 | 92.13, 140.56 | 23.28 against 17.67 |
| 2 | 83.73, 162.48 (other slot busy) | 92.10, 188.52 | 18.08 against 22.20 |
| 3 | 77.14, 174.94 | 77.74, 179.90 | 20.06 against 21.12 |

Within this noise the conversion shows no time cost and no time gain on a cold build. The first
run's gap does not survive repetition. `Hash.Sha3.KeccakProbe`, which imports nothing of the
package, took 14 s in run 1's baseline and 22 s in its converted build. The payoff that holds is
M1's: an edit to a proof or a docstring no longer rebuilds a module importer.

### M5, the breakage census (tested)

19 of the 26 files needed only the mechanical header. By cause:

| Cause | Lines | Files | What it served |
| --- | --- | --- | --- |
| `backward.privateInPublic` (T7) | 28 `set_option` lines | 3 | 18 declarations: 8 private helpers, and 10 declarations whose exported body or statement names one (9 definitions, 1 theorem statement) |
| `meta import` for a guard (T4) | 6 | 3 | 14 `#guard` commands that run imported code |
| core `import all` (T3) | 5 | 3 | 3 proofs that reduce a core definition with no exported body: `decide` (`Init.Data.Vector.Basic`, `Init.Data.Array.DecidableEq`, `Init.Data.Array.Basic`), `rfl` and `decide +kernel` (`Init.Data.Nat.Fold`) |
| re-pinned audit line (M2) | 2 | 2 non-module | the two `#guard_msgs` pins |
| split, de-privatized helper, `meta` section, `meta initialize`, proof text, statement | 0 | 0 | — |

T3 is real but narrow here. Three proofs broke, against 50 `decide`, 161 `rfl` and 33 `unfold`
or `delta` lines in the 26 files (text counts). The blocking core definitions were a derived `DecidableEq`, the `Array`
equality decision and `Nat.fold`. For the kernel `decide`, `t3_probe.lean` listed 16 candidate
core definitions in the closure. Only `Nat.fold` had to be opened (tested by the build). The
elaborator's `whnf` reduces `Nat.land`, `Nat.lor` and `Nat.xor` natively (`Lean/Meta/WHNF.lean`,
reading). The kernel's own list is not in the toolchain's sources, so for the kernel this is
assumed.

## Part 1 scope

- Converted: the `hash` library closure, 26 modules, in one commit (`13ee594`).
- `hash` produces no `lcnf` output, so Part 1 has no LCNF diff.

# Part 2: the estate

## Base, branch and commits

- Worktree `/Users/pooks/Dev/lean4-effect4-modules`, branch `modules/cutover`, rebased onto the
  coordinator's repaired head `97983cf6` (the battery repair `bf60f896`). Head `970246cd`.
- Tooling prerequisites, one commit each: `88d9881b` (a), `a759f909` (b), `3225b1e6` (c).
- The Makefile's variances sources, after a Codex advisory finding: `970246cd`.

## M2 baseline (tested)

Before the repair, at `407ed498`, three contract batteries were red: `Test.Api.HostSessionContract`
and `Test.Api.KeyedHostContract` ("Fields missing: `formed`") and `Test.Program.NativeAtomContract`
(the pinned atom list). Four batteries import them: `Test.Api.RunnerContract`,
`Test.Counterexamples.Machine.Runtime.HostReservedDefect`, `Test.Program.GuardFoldLift` and
`Test.Run.RunContract`. A reduced measurement set those seven aside, never committed
(`scratch/seat-M/gate-line.sh`). After the repair the full battery is green. The baseline below is
over the full battery (`scratch/seat-M/gate-line-full.sh`). That script appends
`#effect4_print_choice_reachers` after the gate and restores `Test/All.lean`.

| Measure | Reduced set, `407ed498` | Full battery, `97983cf6` and (a), (b) |
| --- | --- | --- |
| `lake build Test` | green, 7 batteries aside | green, 877 jobs |
| library-root gate | 156 API/utility modules, 269 Laws-only modules | the same |
| axiom gate | checked 634 modules and 78469 declarations | checked 641 modules and 79191 declarations |
| exact implementation boundary | 17 modules, 23 declarations | the same |
| choice reachers | 295 declarations, 23 roots (17 public, 6 private) | the same |
| constants of the `Effect4` modules (private level, `hash_names_probe.lean` over `Effect4,Effect4.Laws`) | 69708 | 69708, byte-identical listing |

## Tooling prerequisites (tested and reproduced)

| Commit | Change | Evidence |
| --- | --- | --- |
| `88d9881b` | `#effect4_axiom_gate` throws when its environment's header is a module | tested: the gate passes with the same line. No red control: a module cannot import the non-module gate module, and `Environment` has a private constructor, so a test cannot fake a module header |
| `a759f909` | `Effect4Gen.Check.fileImports` reads the header with `Lean.Elab.parseImports`; leaves out the implicit `Init`; refuses a header that does not parse | tested: the new guard agrees on `Effect4.Store.Domain.Derived.Json` and on a scratch copy with a module header; the old guard agrees on the first and throws "the given files import nothing" on the second; `Test.Store.DerivedCheck` builds |
| `3225b1e6` | `Tools.GeneratedStamp.moduleText` and `moduleFlags`; `--module` and `--meta-imports` in the eight Effect4Gen emitters, through a group's existing `Flags`; `--module` in `Tools.Variances`, through the manifest's top-level `VariancesFlags` and `scripts/generate.py` | reproduced: `generate.py --only derived --output-dir` and `--only variances --output-dir` pass with every switch off; tested with the switch on, into scratch files |

## Chains (each tested by its build, the ratchet, the LCNF diff and check-mode regeneration)

Every chain was converted bottom-up from the import layering of the 103 package-free modules
(`scratch/seat-M/estate-dag.json`). It was then built with `Effect4`, `Effect4.Laws` and every
other direct importer. After each chain: `python3 scripts/generate.py --only lcnf` and `git diff`,
`lake env lean Test/Audit/ProofStyle.lean`, and `generate.py --only variances` and `--only derived`
in check mode, all through the lock.

| Chain | Layers | Modules | Commit | Build of chain, Effect4, Laws and importers | LCNF diff | Ratchet | Check-mode regeneration |
| --- | --- | --- | --- | --- | --- | --- | --- |
| A | 0 to 2 | 30 (2 generated) | `d8bb17a4` | green, 670 jobs, 511 s | changed, explained and committed (below) | passes | `variances` and `derived` pass |
| B | 3 to 9 | 27 (3 generated) | `81b8618f` | green, 644 jobs, 459 s | changed, explained, tested and committed (below) | passes | `variances` and `derived` pass |
| C | 10 to 18 | 21 (6 generated) | `adb9717c` | green, 672 jobs, 373 s | none | passes | `variances` and `derived` pass |
| D, first try | 19 to 23 | 25 (2 generated) | not committed | green, 667 jobs, 360 s | api_gen.ml and api_engine.ml changed by about 4000 lines: stopped (T13) | passes | pass |
| D | 19 to 23 | 18 (2 generated) | `fe5ed57c` | green, 339 s | none | passes | `variances` and `derived` pass |

Chain A's LCNF change, read in the diff. The specializations of `annotateEntries` lose their
`_private.…0.` prefix, so their OCaml names change. One join point of `frame_fiber_resume_cause`
takes its parameters in another order, with every use permuted to match.
With the old names mapped to the new, `machine_gen.ml`, `api_gen.ml` and `api_engine.ml` are
identical, and `fibers_gen.ml` differs only in that join point's 18 lines. A trace of the join
point's two call sites shows the same five calls on the same values before and after.

Chain B's LCNF change, read in the diff. `opam exec --switch=effect4 -- dune build` and
`dune test eff gen clock` then pass (tested). Later, `dune test engine` ran twice against the main
checkout's printed corpus of 1 October: once with the committed outputs and once with those of
`97983cf6`. Both give the same 1353 PASS lines and 0 failures. Its three-engine differential finds
0 divergences over 66 goldens, 11 truth programs and 408 corpus programs. That evidence is tested
and bounded: one older corpus, random tapes. Three kinds:

- a specialization of `List.filterTR.loop` is named after the module that now makes it,
  `RunMachine.disarm` instead of `Supervision.raceComplete`. The old one is emitted again for its
  own module;
- three record updates copy fields from a call's result, where the old code wrote the constants
  that call returns. The callee's LCNF body no longer crosses the module boundary (T13).
  The callees are `frame_fiber_start`, `supervision_race_all_state_initial` and
  `wake_list_run_batch`. Reading their generated bodies, each returns exactly those constants;
- two more join points take their parameters in another order, with their call sites permuted to
  match.

Chain D's first try is the one T13 stop of the night. With all 25 modules converted, the cut of
`Effect4.Api.run` and `Effect4.Api.replay` grew by about 2300 lines in `api_gen.ml`. It grew as
much in `api_engine.ml`. A `fiber_core` record of closures now travels at run time, where the old
code specialized it away. The closure tables trace the changed entries to specializations made in
`Effect4.Program.Compile` (`causeOf`, `contEOf`, `exitScoped`), `Effect4.Program.Admit`
(`replayCheckedFrom`) and `Effect4.Program.Typed` (`Val.hasTy`, `externalHandleTarget`). These three
specialize the machine's functions at concrete arguments. As modules they read only the exported
LCNF bodies of their imports. `shouldExportBody` limits those to template-like or small exposed
definitions, so the specializations are lost. That mechanism is reading
(`Lean/Compiler/LCNF/Visibility.lean`); the names in the tables are tested. I could not show a
change of this size harmless. So I reverted those three and the four chain-D modules that import
them: `Program.Admission`, `Program.Provision`, `Schema.Codec` and `Api.Frontier`. With them
non-module, the `lcnf` family regenerates without a diff.

## M2 at the end (tested)

The same full-battery measurement as the baseline (`gate-line-full.sh`), at `fe5ed57c`:

| Measure | Before, `97983cf6` and (a), (b) | After, `fe5ed57c` |
| --- | --- | --- |
| `lake build Test` | green, 877 jobs | green, 877 jobs |
| library-root gate | 156 API/utility modules, 269 Laws-only modules | the same |
| axiom gate | checked 641 modules and 79191 declarations | checked 641 modules and 79581 declarations (+390) |
| exact implementation boundary | 17 modules, 23 declarations | the same |
| choice reachers | 295 declarations, 23 roots (17 public, 6 private) | the same |
| `Effect4` constants, private level | 69708 (51968 public, 17740 private) | 70092 (51480 public, 18612 private) |

The amended M2, condition by condition (`scratch/seat-M/m2_estate.py` and a classification of every
absent and new name, `m2-estate.txt`):

1. **Every authored user name before the conversion is present after it, auxiliaries excepted:
   holds.** All 30133 authored user names are present, and none changed kind; 12343 of them are in
   the 96 converted modules. The measured exception: 168 auxiliary user names are absent after,
   108 `_proof_N` and 60 `match_N` or their equation lemmas. They are renumbered across the public
   and private boundary, as in `hash`. The coordinator is amending row 200's wording to this form.
2. **Every new name is an auxiliary: holds.** 552 new names, all auxiliaries: 429 `match_N`, 111
   `_proof_N`, 6 `_sparseCasesOn_N` and 6 `eq_N`, `eq_def` or `match_N_N`.
3. **The gate passes: holds** (the table above).
4. **Its `Classical.choice` count is unchanged: holds.** `#effect4_print_choice_reachers` gives 295
   declarations and 23 roots before and after. The gate line's exemption counts are unchanged.

Visibility: 522 auxiliaries became private. Three authored declarations became public, the three
de-privatized helpers below, and so did three of their auxiliaries.

## M1 on a converted core chain (tested)

`scratch/seat-M/m1-estate.sh` and `m1-estate-b.sh` edit `Effect4.Machine.Cause` (chain A). The module
importer is `Effect4.Machine.Exit`, which has only `public import Effect4.Machine.Cause`. Hashes are
the first 16 hex digits.

| Edit | `.olean` | `.olean.server` | `.olean.private` | `.ir` | `--no-build Effect4.Machine.Exit` |
| --- | --- | --- | --- | --- | --- |
| none (as built) | `216225edd36b54f3` | `28c17122f152badf` | `260068103066fb80` | `c00a471d3ca22945` | exit 0 |
| a proof that is not an `rfl` proof: `keys_nodup`, `self.keysNodup` to `id self.keysNodup` | same | `64ac8119366170f8` | `cb59c42a0eb97b3a` | same | exit 0 |
| an `rfl` proof made a non-`rfl` one: `keys_eq`, `rfl` to `Eq.trans rfl rfl` | `31eaf29717181051` | `ade1e31847b40143` | `ca54f50d8376f975` | same | exit 3 |
| a docstring, one word | same | `34171d9df023c575` | `bf10be58e9545397` | same | exit 0 |
| a statement (red control): binder `key` to `k` in `lookup_eq` | `902230690f99b777` | `095969b5ffbfeccd` | `571e0ea322a2d1d8` | same | exit 3 |

Every undo returns every hash to its first row, and the importer to exit 0. The payoff holds for a
proof edit. One qualification, by reading `inferDefEqAttr` (`Lean/DefEqAttrib.lean`). A theorem
proved by `rfl` is tagged `@[defeq]` and `@[backward_defeq]` for `dsimp`. The tags of a public
theorem are exported. So turning an `rfl` proof into another proof, or the reverse, changes the
exported part and rebuilds module importers, by design.

## M5, the breakage census of the estate (tested, from the diff `97983cf6..fe5ed57c`)

76 of the 96 converted files needed only the header, the 13 generated files among them (their
switches carry their guards' meta imports). By cause:

| Cause | Lines | Files | What it served |
| --- | --- | --- | --- |
| `backward.privateInPublic` (T7) | 51 `set_option` lines | 10 | 29 private helpers and 22 declarations whose exported body or statement names one |
| de-privatized helper | 3 | 2 | `annotateEntries` (a public statement and its proofs must share one matcher for `rw` to apply); `Representation.beq_iff` and `Check.beq_iff` (`privateInPublic` did not export these private theorems of a mutual structural block) |
| core `import all` (T3) | 5 | 5 | `Init.Data.String.Defs` (`String.toUTF8`) in four files, `Init.Data.Nat.ToString` (`Nat.ofDigitChars`) in one |
| `meta import` for a guard (T4) | 21 | 13 | 11 lines in 5 hand-converted files; 10 lines written by the generators' `--meta-imports` |
| `public meta section` and `public meta import` | 2 and 2 | 2 | `Program.FoldOf` (all elaborator code); `Program.Authoring.Sugar` (runtime part exposed, the `eff` macro in a nested meta section) |
| kept non-module (T13) | — | 7 | the specialization sites `Program.Typed`, `Program.Compile`, `Program.Admit`, and their importers |
| split, `meta initialize`, proof text, statement | 0 | 0 | — |

Predicted against needed, for the scan's trap candidates (the scan is a text count, so an upper
bound):

| Construct | Scan of the 103 | Needed in the 96 |
| --- | --- | --- |
| private definitions (T7) | 71 in 15 files | 29 helper sites exported and 3 declarations de-privatized, in 10 files |
| `#guard` lines (T4) | 337 in 23 files | 21 `meta import` lines in 13 files |
| `decide`, `rfl`, `unfold` or `delta` (T3) | 257, 1734, 201 | 5 `import all` lines for `String.toUTF8` and `Nat.ofDigitChars` |
| meta code | 2 files | 2 files with a meta section |
| generated files | 13 | 13, all through their switches |

## Chains left

- The seven package-free modules kept non-module (T13): `Effect4.Program.Typed`,
  `Effect4.Program.Compile`, `Effect4.Program.Admit`, `Effect4.Program.Admission`,
  `Effect4.Program.Provision`, `Effect4.Schema.Codec`, `Effect4.Api.Frontier`.
- Outside this brief: the 53 core modules that reach a package, all 269 `Laws` modules, and the
  three `ProofGraph` modules that `Laws` imports. The 53 wait for `typescript` and `effects` to be
  converted and re-pinned, and for `hash` to be pushed and re-pinned.

## Changed files of Part 2

| Commit | Files |
| --- | --- |
| `88d9881b` | `Test/Audit/AxiomGate.lean` |
| `a759f909` | `tools/Effect4Gen/Check.lean` |
| `3225b1e6` | `scripts/generate.py`; `tools/Effect4Gen/{Atoms,Authoring,Fold,Forms,LayerView,Main,Rows,View}.lean`; `tools/Effect4Gen/manifest.json`; `tools/Tools/GeneratedStamp.lean`; `tools/Tools/Variances.lean` |
| `d8bb17a4` | 30 `src/Effect4` files (`scratch/seat-M/chainA.txt`); `tools/Effect4Gen/manifest.json`; 8 `lcnf` outputs under `ocaml/gen/` and `ocaml/engine/` |
| `81b8618f` | 27 `src/Effect4` files (`chainB.txt`); the manifest; 7 `lcnf` outputs |
| `adb9717c` | 21 `src/Effect4` files (`chainC.txt`); the manifest |
| `fe5ed57c` | 18 `src/Effect4` files (`chainD2.txt`); the manifest |
| `970246cd` | `Makefile`: `tools/Effect4Gen/manifest.json` joins `VARIANCE_SOURCES` (a Codex advisory finding, relayed by the coordinator) |

No file under `src/Effect4/Laws/**`, `tools/ProofGraph/**`, `tools/Tools/Semantics*.lean`,
`docs/core/**`, `AGENTS.md`, `lakefile.toml` or the root import files changed. `Test/All.lean` and
seven batteries were changed for measurements only, restored each time, and never committed.

## Commands of Part 2 and their results

Every `lake`, `lean`, `python3 scripts/generate.py` and `dune` call ran through
`scratch/lean-slot.sh`.

| Command (in the worktree) | Result |
| --- | --- |
| `lake build Test` at `407ed498` | red: 3 contract batteries (repaired by the coordinator at `bf60f896`) |
| `scratch/seat-M/gate-line.sh before` and `after-a` (7 batteries set aside) | green; the reduced-set column above |
| `scratch/seat-M/gate-line-full.sh base-full` at `97983cf6` and (a), (b) | green, 877 jobs; the baseline column above |
| `lake env lean --run scratch/seat-M/hash_names_probe.lean Effect4,Effect4.Laws Effect4 private` | 69708 rows before, 70092 after |
| `lake build Test.Audit.AxiomGate`; `lake build Effect4Gen.Check Test.Store.DerivedCheck` | green |
| the guard controls of (b) (`scratch/seat-M/guard-control/`) | new guard agrees twice; old guard throws on the module-header copy |
| `lake build effect4gen effect4gen-catalogue Tools.Variances Tools.GeneratedStamp` | green, 234 jobs |
| `python3 scripts/generate.py --only derived` and `--only variances`, both `--output-dir`, after (c) and after each chain | `PASS generate` every time |
| `python3 scripts/generate.py --only lcnf` at the base, then after each chain, and `git diff -- ocaml/` | no diff at the base; diffs after A, B and the first D (above); none after C and D |
| per chain: `lake build <chain> Effect4 Effect4.Laws <other direct importers>` | green: 670, 644, 672, 667 (first D) jobs; D again green |
| per chain: `lake env lean Test/Audit/ProofStyle.lean` | passes; 1950 recorded occurrences in 1153 entries, 60 unread commands, every time |
| `opam exec --switch=effect4 -- dune build -j 2`; `dune test -j 2 eff gen clock` (after chain B) | exit 0; `test_eff: 555 checks, 0 failures`, G0 runs `p42`, `pFork`, `pAwait` |
| `lake env .lake/build/bin/effect4gen …` and `effect4gen-catalogue …` with `--module` | the 13 generated files, each reproduced by the next check-mode `derived` or `variances` run |
| `scratch/seat-M/gate-line-full.sh after-full` at `fe5ed57c` | green, 877 jobs; the "after" column above |
| `python3 scratch/seat-M/m2_estate.py` and the absent-and-new classification | the M2 conditions above |
| `E4_LEAN_CORPUS=<main checkout>/.lake/corpus opam exec --switch=effect4 -- dune test -j 2 --force engine`, with the committed `lcnf` outputs (A) and with those of `97983cf6` restored for the run (B) | A and B each: 1353 PASS lines, 28 sections with 0 failures; the three-engine differential over 66 goldens, 11 truth programs and 408 Lean-corpus programs finds 0 divergences |
| `make gen-variances`; `touch tools/Effect4Gen/manifest.json`; `make -q .lake/gen/variances`, before and after the Makefile fix | exit 0 before the fix (the defect), exit 1 after; exit 0 again after regenerating |
| `python3 scripts/generate.py --only eff`, `wire`, `cas` and `ts`, each with `--output-dir`, at `970246cd`, then `cmp` of every emitted file against the tree (those routes do not compare by themselves) | `eff` 210 files and its 2 engine structure files, `wire` 11, `cas` 119, `ts` 9: 0 differ |
| `scratch/seat-M/m1-estate.sh estate` and `m1-estate-b.sh estate-b` | the M1 table above |

## Gate lines before and after (both parts)

| Gate | Before | After |
| --- | --- | --- |
| `hash`, `#hash_axiom_gate` (HashTest) | checked 47 modules and 1618 declarations; 122 reach `Classical.choice`; 0 offenders | checked 47 modules and 1627 declarations; 122; 0 offenders |
| `hash`, sha256 audit (pinned) | 422 declarations across 12 modules; 0 reach `Classical.choice` | 420 across 12; 0 (re-pinned) |
| `hash`, sha3 audit (pinned) | 571 declarations across 14 modules; 45 reach `Classical.choice` | 576 across 14; 45 (re-pinned) |
| the estate, `#effect4_axiom_gate` (`Test/All.lean`) | checked 641 modules and 79191 declarations; boundary 17 modules, 23 declarations | checked 641 modules and 79581 declarations; boundary 17 and 23 |
| the estate, `#effect4_print_choice_reachers` | 295 declarations, 23 roots (17 public, 6 private) | the same |

## Axiom output

`hash`: the HashTest gate passes after the conversion with 0 offenders. 122 declarations reach
`Classical.choice`, as before. Both family audits pass with 0 offenders and choice counts 0 and 45.
The estate: `#effect4_axiom_gate` passes over the full battery at `fe5ed57c` (the table above). The
choice reachers and the exact implementation boundary are those of `97983cf6`.

## Evidence

- **proved**: nothing new. No statement changed, so every theorem keeps its proof; the kernel
  accepted every rebuilt module, and both gates report 0 offenders.
- **reproduced**: the 25 derived outputs and `TyVariance` (check-mode `generate.py`, after (c) and
  after every chain), including the 13 generated files converted through their switches. At the
  head, the `eff`, `wire`, `cas` and `ts` families too: every emitted file equals the tree's. Only
  `readme` was not run; it needs the host runtime.
- **tested**:
  - M1 to M5 in both parts as tabled, and the amended M2's four conditions;
  - the five `hash` executable gates and its trust self-test;
  - the tooling controls of (a), (b) and (c);
  - per chain, the LCNF regeneration and diff, and the proof-style ratchet;
  - `dune build` and `dune test eff gen clock` after chain B, and `dune test engine` with the
    committed and the base `lcnf` outputs (bounded);
  - the variances freshness fix, by a manifest-only edit under `make -q`, before and after.
- **reading**: the mechanisms named here. `addDeclCore` (`Lean/AddDecl.lean`) exports a theorem as an
  axiom and a `privateInPublic` declaration as is. `resolvePrivateName` and `checkPrivateInPublic`
  (`Lean/ResolveName.lean`) give the T7 refusal and its warning. `inferDefEqAttr`
  (`Lean/DefEqAttrib.lean`) tags `rfl` theorems. The core modules' exposure comes from their
  headers. The estate gate's count comes from `auditedFacts` (`tools/ProofGraph/Audit.lean`). The
  meaning of chains A's and B's LCNF hunks comes from reading the diffs.
- **assumed**:
  - the rule inside Lean that mints a second copy of an auxiliary (the probes show the copies);
  - the kernel's native `Nat` operations;
  - for chain D's first try, that the lost specializations come from `shouldExportBody`. Its
    source was read, but not traced declaration by declaration.
- **Bounded**: `hash`'s M4 times (two threads, a shared machine). The OCaml `engine` differential ran
  against one older printed corpus with random tapes. M1 in the estate covers one module and one
  importer. The scan's counts are text counts.
- **Host-only**: none.

## Landed theorems and their placement

None. No theorem was stated, and no statement or definition body changed. Proofs changed text
nowhere; they gained header imports (`import all`), and declarations gained `set_option` wrappers.

## Open obligations

1. **Row 200's M2 wording**: the coordinator is amending it to "every authored user name". The
   estate's measured exception, 168 renumbered auxiliary names, is stated in M2 at the end.
2. **The seven T13 modules**: decide how the specialization sites convert. The options:
   - keep them non-module;
   - let the machine's specialized definitions export their LCNF bodies, then measure the `lcnf`
     diff again. `@[specialize]` or `@[inline]` makes a body template-like for `shouldExportBody`;
   - accept the larger, slower generated engine.
3. **The `privateInPublic` escape**: 22 declarations in the estate and 10 in `hash` reach exported
   private helpers. An edit to a helper rebuilds the importers, as an exposed body does. De-privatizing
   later renames the helpers and, in `hash`, moves the sha256 audit count again.
4. **`hash`**: update the prose that still states 422 and 571: `README.md`, `AGENTS.md`,
   `docs/EXTRACTION-RECORD.md`, and the docstrings of `Hash/Sha256/Audit.lean` and
   `Hash/Sha3/Audit.lean`. Then push and re-pin, which belong to the coordinator.
5. **M1 on a `Laws` chain** with `@[semantics]` and `@[aesop]`: owed with the `Laws` conversion.
6. **Not run**: `leanchecker` in any form (the brief forbids a bare run).

## Proposed decisions rows (proposals only)

- **P1, row 200's M2 (the coordinator is amending it).** "Every authored user name before the
  conversion is present after it." For the measurement, an auxiliary is a name with a component
  that Lean's naming gives auxiliaries: `Name.isInternal`, `match_N`, `eq_N`, `eq_def`, `proof_N`,
  `splitter`, `congr_simp` and `else_eq`.
- **P2, the T13 modules.** The specialization sites stay non-module until a measured LCNF diff
  allows them; the same check guards every later chain. Owner.
- **P3, the estate gate's line.** The line reports authored and auxiliary declarations as two
  numbers, and M2 compares the authored one. Coordinator.
- **P4, an `rfl` proof is interface.** Recorded beside M1: changing a theorem's proof between `rfl`
  and anything else rebuilds module importers, because the `@[defeq]` tags are exported. Coordinator.

## Deviations from the brief

- One `lake env printenv LAKE_CACHE_DIR` ran in `hash` outside the lock, before the first build.
  It reads the TOML configuration and builds nothing.
- Every `hash` build ran with `LAKE_ARTIFACT_CACHE=false`. Lake reads the artifact cache by default
  even where no package enables it (`Package.isArtifactCacheReadable`, `Lake/Config/Monad.lean`).
  Without the flag the baseline could have been restored, not built.
- `hash`'s M4 ran at `LEAN_NUM_THREADS=2`, the lock's bound, not the note's 3.
- The `hash` default targets were named one by one. Its trust self-test runs its own `lake build`
  without targets inside its throwaway copy, by its design, within one slot.
- The re-pin of the two `hash` audit lines is beyond the brief's file list; the coordinator accepted
  it.
- The `hash` commit message was amended once, to add M4's later pairs, before anything else read it.
- The emitter switch uses the manifest's existing per-group `Flags` field, not a new field. The
  `Variances` producer has no group, so it reads a new top-level `VariancesFlags`.
- The built emitters, run through `lake env`, wrote the 13 generated files in place. So a chain
  needed no rebuild of the generator executables first. Check-mode `generate.py` then reproduced
  each file.
- After chains A and B the LCNF outputs changed. I judged both changes explained and harmless, and
  committed the regenerated outputs with their chains, as AGENTS.md asks for a producer's changed
  output. Chain D's change I could not show harmless, so I reverted those seven modules.
- (a) landed without a red-control fixture, for the reason given in its row.
