# 2026-10-04 seat M receipt: the module-system cutover, stopped at the hash gate

**The one thing to know before merging:** the wave stopped after `hash`, as the brief's gate
requires. M2 contradicts the prediction of the reference scout's modules note. The pinned
audit counts moved (sha256 from 422 to 420, sha3 from 571 to 576), and the HashTest gate count
moved from 1618 to 1627. Every difference is an auxiliary declaration that the module system makes
private or mints anew. No authored declaration is lost, and M1 and M3 hold. Part 2 did not start:
the estate worktree has no commit and no edit.

## Base and head

| Tree | Branch | Base | Head | State |
| --- | --- | --- | --- | --- |
| `hash`, `/Users/pooks/Dev/lean4-hash` | `module-system` | `c906b15` (`main`, the estate's pin) | `13ee594` | one commit, local only, never pushed |
| the estate, `/Users/pooks/Dev/lean4-effect4-modules` | `modules/cutover` | `d2bbbaf5` | `d2bbbaf5` | untouched: no edit, no build, no commit |
| the main checkout | `refactor/phase1-phase3` | — | — | only `scratch/seat-M/` and this receipt written; this receipt is not force-added |

## The gate decision, and the owner's options

The brief defines M2 as "the audit lines are unchanged" and stops the wave when M1, M2 or M3
contradicts the note's prediction. The note's §3(e) predicts that the gate's line and the pinned
audit lines stay equal. They did not, so the wave stops here.

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

1. **Amend M2 and relaunch Part 2 (recommended).** The amended M2 has four conditions:
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

The estate: no file. The main checkout: this receipt, and the scripts, probes and logs under
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

## Gate lines before and after

The three `hash` lines are in the M2 table above. The estate's gate line was not measured: Part 2
did not start, so neither its baseline build of `Test` nor its closing one ran.

## LCNF diffs

None. Part 2 did not run, and `hash` produces no `lcnf` output.

## Chains converted and chains left

- Converted: the `hash` library closure, 26 modules, in one commit.
- Left, all of Part 2:
  - the tooling prerequisites: (a) the gate's module-root refusal, (b) `fileImports` through
    `Lean.Elab.parseImports`, (c) the emitters' module header behind a manifest field;
  - the 103 `src/Effect4` modules outside `Laws` that reach no package;
  - the estate's closing M2 and its M1.

What Part 2 would meet, from a text scan of the worktree (`scratch/seat-M/estate_scan.py`,
reading-level counts by `grep`-style patterns, so upper bounds; per module in
`estate-free-modules.tsv`). The `hash` column gives the edits each construct cost there.

| Construct (trap) | `hash`, 26 files | Estate, the 103 package-free modules outside `Laws` |
| --- | --- | --- |
| private definitions (T7) | 10 in 4 files; 18 `privateInPublic` sites in 3 files | 71 in 15 files |
| `#guard` lines (T4) | 19 in 4 files; 6 `meta import`s in 3 files | 337 in 23 files |
| `decide`, `rfl`, `unfold` or `delta` (T3 candidates) | 50, 161, 33; 3 proofs broke, 5 `import all`s | 257, 1734, 201, in 36, 60, 34 files |
| `deriving` clauses | 2 | 200 in 54 files |
| meta code (`elab`, `macro`, `syntax`) | 0 | 2 files |
| generated files (converted only through their emitters) | 0 | 13 |

The scan reproduces the verifier's counts: 425 `Effect4` modules, 156 outside `Laws`, 103 of
them reaching no package.

## Axiom output

The HashTest gate after the conversion: 47 modules and 1627 declarations, 122 of them reaching
`Classical.choice`, 0 offenders. The two family audits after: 0 offenders, choice counts 0 and 45
as before. The estate's axiom gate did not run, since no estate file changed.

## Evidence

- **proved**: nothing new. The `hash` theorems are unchanged in statement and accepted by the
  kernel under the package ceiling, and the gate's 0 offenders covers them.
- **tested**: M1, M2, M3, M4 and M5 as tabled; the five executable gates; the trust self-test;
  the M2 attribution, which `audit_replay.py` reproduces from the listings.
- **reading**: the mechanisms named here. `addDeclCore` (`Lean/AddDecl.lean`) exports a theorem as
  an axiom and a `privateInPublic` declaration as is. `resolvePrivateName` and
  `checkPrivateInPublic` (`Lean/ResolveName.lean`) give the T7 refusal and its warning. The
  exposure of `Init.Data.Vector.Basic`, `Init.Data.Array.Basic`, `Init.Data.Array.DecidableEq`,
  `Init.Data.Nat.Fold` and `Init.Data.List.Basic` comes from their headers. The estate gate's
  count comes from `auditedFacts` (`tools/ProofGraph/Audit.lean`).
- **assumed**: the rule inside Lean that mints the second copy of an auxiliary. The probes show
  the copies, but that rule was not read in Lean's source. Also assumed: the kernel's native `Nat`
  operations (above).
- **Bounded**: M4's times. Two threads, a machine shared with the coordinator's lane, load
  averages 4.7 to 8.4 on 8 cores, the other lock slot busy for some runs. M3 covers the `Hash`
  modules only. The estate forecast is a text scan.
- **Host-only**: none.

## Landed theorems and their placement

None. No theorem was stated or changed. The conversion changed no statement and no definition
body; three proofs gained header imports, and none had its text changed.

## Open obligations

1. **The owner**: choose an option of "The gate decision" above, then relaunch Part 2 or end
   the cutover. Part 2 must not start under the unamended M2.
2. **`hash`, if the re-pin is accepted**: update the prose that still states 422 and 571, which
   I did not edit. That is `README.md`, `AGENTS.md`, `docs/EXTRACTION-RECORD.md` (two tables
   and the pinned lines), and the docstrings of `Hash/Sha256/Audit.lean` and
   `Hash/Sha3/Audit.lean`.
3. **`hash` upstream**: a push to `pure-algebra/lean4-hash`, a new `rev` in the estate's
   `lakefile.toml` and the manifest belong to the coordinator. Nothing was pushed.
4. **The `privateInPublic` escape**: 18 declarations carry it. Their helpers sit in the exported
   part as is, so an edit to a helper rebuilds the importers. De-privatizing them later renames 8
   declarations and moves the sha256 audit count again.
5. **M1 on a `Laws` chain** with `@[semantics]` and `@[aesop]`, which the note asks for: owed,
   with Part 2.
6. **Part 2's tooling prerequisites** (a), (b) and (c) do not depend on M2's criterion, so they
   could run before the owner decides. The brief stops all of Part 2, so I did not start them.
7. **Not run**: `leanchecker` in any form (the brief forbids a bare run). `hash`'s
   `lake test` is the `HashVerified` build, which every default-target build above includes.

## Proposed decisions rows (proposals only)

- **P1, amending row 200's M2.** M2 passes on the four conditions of option 1 above. The raw
  count is reported, not compared. Owner.
- **P2, the `hash` re-pin.** Accept 420 and 576 on `module-system` and update the `hash` prose,
  or change both family audits to count authored declarations only. Owner, with the `hash`
  maintainers.
- **P3, the estate gate's line.** The line reports authored and auxiliary declarations as two
  numbers, and M2 compares the authored one. Lean's predicates and the `_proof_N` and `match_N`
  spellings name the auxiliaries. Coordinator.

## Deviations from the brief

- One `lake env printenv LAKE_CACHE_DIR` ran in `hash` outside the lock, before the first build.
  It reads the TOML configuration and builds nothing. Every later call went through the lock.
- Every `hash` build ran with `LAKE_ARTIFACT_CACHE=false`. Lake reads the artifact cache by
  default even where no package enables it (`Package.isArtifactCacheReadable`,
  `Lake/Config/Monad.lean`), and the estate stores `hash`'s artifacts there. Without the flag the
  baseline could have been restored, not built.
- M4 ran at `LEAN_NUM_THREADS=2`, the lock's bound, not the note's 3.
- The default targets were named one by one, never a bare `lake build`. The trust self-test runs
  its own `lake build` without targets inside its throwaway copy, by its design, within one slot.
- The re-pin of the two `hash` audit lines is beyond the brief's file list. It is the only way
  the branch builds green, and the commit message says so.
- The commit message was amended once, to add M4's later pairs, before anything else read it.
- The estate scan read the worktree's sources without building or editing anything.
