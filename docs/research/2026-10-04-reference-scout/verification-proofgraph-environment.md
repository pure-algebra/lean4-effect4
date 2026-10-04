# 2026-10-04 Verification: the proof-graph and environment seat notes

Status: research note (history, not authority). Base: `53640d85` on `refactor/phase1-phase3`.
Seat: skeptical verifier, read-only. No build, no Lean process, no download and no git write ran.
Evidence kind: reading, plus one finite probe (a `python3` reread of one `.ilean`).

Notes checked:

- `docs/research/2026-10-04-reference-scout/proof-graph.md`
- `docs/research/2026-10-04-reference-scout/environment.md`

## 1. The one thing to know first

Both notes hold up. Every cited file exists at its pinned commit, and every cited declaration was
found. Three claims are refuted and four are unsupported. None of them overturns a
recommendation. The trust gap that matters is one neither note states. `ProofRef.validate`,
`validateWanted` and `addTheorem` call `Lean.collectAxioms`. In 4.33.1 that function takes an
imported constant's axioms from entries that the producing process wrote into its `.olean`
(`exportedAxiomsExt`). So the planning slice's "proved" status rests on those entries. Only the
axiom gate (`reachedAxioms`) recomputes axioms from bodies.

## 2. What was checked

- Pins: the `HEAD` of all eight vendored repositories used by the two notes matches
  `vendor/refs/MANIFEST.tsv`. The batteries pin is `4488d40d…`, and the aesop pin is `3448c0bc…`.
- Toolchain source at `~/.elan/toolchains/leanprover--lean4---v4.33.1/src/lean`:
  - `LeanChecker.lean`;
  - `Lean/Replay.lean`, `Lean/Util/CollectAxioms.lean`, `Lean/Environment.lean`;
  - `Lean/Elab/Import.lean`, `Lean/AddDecl.lean`, `Lean/Attributes.lean`;
  - `Lean/Data/Name.lean`, `Lean/AuxRecursor.lean`, `Lean/CoreM.lean`, `Init/Core.lean`;
  - `Lean/Language/Lean.lean`, `Lean/Data/Lsp/Internal.lean`;
  - `lake/Lake/Load/Toml.lean`, `lake/Lake/Build/Common.lean`, `lake/Lake/Build/Facets.lean`,
    `lake/README.md`.
- Estate: `tools/ProofGraph/{Ledger,Search,Axioms,Audit,Proof}.lean`,
  `tools/Tools/{SemanticsRegistry,Semantics,Architecture}.lean`,
  `src/Effect4/Laws/Auto/{Semantics,Obligations}.lean`, `Test/Audit/{AxiomGate,ProofGraph}.lean`,
  `Makefile`, `lakefile.toml`, `lake-manifest.json` and the tooling map
  (`docs/research/2026-10-03-claude-lead/tooling-map.md`).
- Finite probe reproduced: `.lake/build/lib/lean/Effect4/Laws/Codegen/ReadPrint.ilean` gives
  3,400 uses with `parentDecl`, 218 without, 124 parents, and 20 constants under
  `Effect4.Program.read_print`, `cataFam` and `ReadableAt` among them. These match the
  environment note exactly.
- The 23-theorem text search was rerun over `src/Effect4/Laws`. It gives 23, with the cited
  examples present. One of them, `eq_of_nodup_keys` (`Machine/StoresLaws.lean`), is `private`. Its
  mangled name is dropped by `Name.isInternal` whatever the filter, so a fix recovers at most 22.

## 3. Refuted claims

| # | Note | Claim | Evidence |
| --- | --- | --- | --- |
| 1 | proof-graph §3.2 | `exportedAxiomsExt` "needs the extension registered in every audited module's environment, and it costs build time in every module" (an adoption cost) | `Lean/Util/CollectAxioms.lean`: `private builtin_initialize exportedAxiomsExt` with `exportEntriesFnEx`. It is built into core, registered in every Lean process, and already computed whenever an `.olean` is written. The cost is already paid, and nothing would be adopted. |
| 2 | proof-graph §3.3 | doc-gen4's and import-graph's filters "read environment tags, not spellings" | `Name.isInternal` and `Name.isInternalDetail` (`Lean/Data/Name.lean`) test name strings; `isInternalDetail` uses `matchPrefix`. import-graph's `isBlackListed` (`ImportGraph/Export/Gexf.lean`) also matches `.str _ "inj"`, `.str _ "noConfusionType"` and `sorryAx` by name. Only `isAuxRecursor`, `isNoConfusion`, `isRec`/`isRecCore` and `isMatcher` read environment tags. |
| 3 | proof-graph §5.8 | LeanArchitect as a dependency "would put its attribute and `Cli` into the law graph's imports" | `Architect/*.lean` imports only `Lean` and `Batteries.Lean.NameMapAttribute`. A grep for `import Cli` under `Architect/` finds nothing. Only `Main.lean`, the `extract_blueprint` executable, imports `Cli`. `Cli` would be a package `require`, not an import of the law graph. |

## 4. Unsupported claims

| # | Note | Claim | Why |
| --- | --- | --- | --- |
| 1 | environment §1, §3.1 | "The CI of lean4lean reports out-of-memory kills for that shape", meaning a bare `leanchecker` | The comment in `vendor/refs/lean4lean/.github/workflows/ci.yml` is about lean4lean's own `main`. It says to widen "once replay uses a bounded task pool, as lean4checker does", so it contrasts lean4lean with lean4checker. The toolchain's `LeanChecker.lean` does spawn one `IO.asTask` per module, so the shape claim rests on reading that code, not on the CI. |
| 2 | environment §3.1 cost model, §5 | A bare run "holds up to 8 imported environments at once" | The bound is inferred from the `Task.Priority.dedicated` docstring (`Init/Core.lean`). The same CI comment says peak RSS "scales with the fan-out". The C++ scheduler and any `LEAN_NUM_THREADS` handling were not read; the note admits this. |
| 3 | environment §3.3, tier 0 step 4 | `found`, the term constants minus the `.ilean` named constants, is "what automation brought in" | The difference also holds every constant that elaboration inserts without automation: instances from typeclass resolution, coercions, matchers and other auxiliaries, and unfolded notation. `found` is elaboration plus automation. It separates the banks' contribution only through step 5. |
| 4 | environment §3.2 | `Test.All` "ends the critical path of every rebuild" | The tooling map §2 gives 17 s for `Test.All` but does not say this. It is an inference from `Test.All` importing the batteries. That is plausible, but not cited. |

## 5. Confirmed claims worth recording

proof-graph note:

- leanblueprint's `make_lean_data` rules: `can_state`, `can_prove`, `proved`, and `fully_proved`
  with its exemption for definitions. `\mathlibok` sets `leanok`. `checkdecls` checks existence
  only. `new` commits to git after a prompt.
- LeanArchitect:
  - `CollectUsed.collect` stops at nodes and enters everything else. `collectUsed` computes
    `valueUsed \ typeUsed.erase ``sorryAx`.
  - `inferUses` filters `excludes` before the `sorryAx` test.
  - `checkCyclicUses` is commented out.
  - The JSON from `NodeWithPos.toJson` carries only authored data. The `MyNat` fixture has
    exactly two nodes with authored uses.
  - The facets call `buildFileUnlessUpToDate'` keyed on `leanArts`. `runEnvOfImports` sets
    `debug.skipKernelTC` and turns `Elab.async` off.
- `registerParametricAttribute` refuses imported declarations (`throwAttrDeclInImportedModule`).
  `registerNameMapAttribute` does not.
- The estate keeps three identical copies of the noise filter (`semanticsNoise`, `isNoise` and
  the reach probe's `noise`). `Name.isInternalDetail` requires digits or `_` after the prefix.
- Lake's TOML loader decodes only `lean_lib`, `lean_exe`, `input_file` and `input_dir`. The
  Lake README calls custom facets experimental.
- The `$(GEN)/semantics` rule depends on `$(LAWS)` alone, while `registry.roots` names two `Test`
  roots. `closeSeq_protocol` lives in `Test.Program.ProtocolPosts`.
- `readGoal` returns empty `dependencies`. `checkPortable` and `checkDeclaration` are `private`.
  The schema version is a hand-written `3`.
- `processHeaderCore` imports at `.private` level for a file that is not a `module`.
  `importModules` defaults to `.private`, and `importModulesCore` sets `importAll` from
  `globalLevel`.

environment note:

- `LeanChecker.lean`:
  - `replayFromImports` reads the parts with `readModuleDataParts` and calls `finalizeImport`
    with `isModule := true`.
  - `getCurrentModule` capitalises the manifest name (`effect4` becomes `Effect4`).
  - The tool spawns one `IO.asTask` per module, and the docstring says "not an external
    verifier".
- `Lean.Environment.replay` skips `unsafe` and `partial` constants. It skips duplicate theorems
  and postpones constructors and recursors.
- `readModuleData` and `importModules` are safe `def`s. `withImportModules` and `freeRegions` are
  `unsafe`.
- `addDecl` honours `debug.skipKernelTC` (`Lean/AddDecl.lean`). `realizeConst` skips the kernel,
  and `replayKernel` re-checks later.
- In the estate, only `checkDeclaration` calls `addDeclCore`, and no source sets
  `skipKernelTC`.
- lean4lean:
  - It pins `v4.33.0-rc2`, has 15 files with `sorry` under `Verify` and `Theory`, and lists three
    bugs in `bugs-found.md`.
  - The divergences are as stated.
  - It reports declarations over 1 s, and `--compare` prints both times when lean4lean is over
    twice as slow.
  - Its replay sends one `defnDecl` per constant.
- REPL and Pantograph:
  - Both add constants through `lake_environment_add` with no kernel check, and REPL's own
    docstring says "not a verifier boundary".
  - Pickling loses extension entries.
  - Pantograph needs `LSpec` and pins `v4.33.1`.
- jixia: the exact-toolchain rule and the "invalid header" warning are in its README.
  `handleProofWanted` elaborates a `proof_wanted` as an `axiom`.
- aesop:
  - `aesop.stats.file` turns statistics on (`enableStats`).
  - `declareRuleSetUnchecked` registers a scoped extension, `aesop_<bank>` and
    `aesop_<bank>_proc`.
  - `weak.` options are stripped by `reparseOptions`.
- Lake's `Census.olean.hash` equals the `.olean` named in `Census.trace` (`dcac0cadc74faa2d`).
- The machine has 424 Lean files under `src/Effect4` and 223 under `Test` outside the fixtures.
  `Test/All.lean` holds 205 imports.

## 6. Recommendation verdicts

### proof-graph note §4

| # | Recommendation | Verdict | Reason |
| --- | --- | --- | --- |
| 1 | One helper over Lean's predicates instead of the three string filters | overstated | The defect (23 names, 22 recoverable) is real. But the estate filter also drops `inj`, `injEq`, `sizeOf_spec`, `instSizeOf…`, `ctorIdx`, `ctorElim` and `noConfusionType` by spelling, and doc-gen4's predicate set does not cover these. A straight copy changes the population beyond the 23. The minimal repair is `isInternalDetail`'s `matchPrefix` in place of `startsWith` for the three prefixes. |
| 2 | Add the two `Test` traces to the marker rule, or derive them from `registry.roots` | sound | The rule and the registry roots are as stated. The controls load only their own fixture root (`tools/Drivers/SemanticsControls.lean`). |
| 3 | Module-system pilot: body-reading tools stay non-`module` | sound | `processHeaderCore` levels as stated; the Environment note on theorems weakened to axioms is present. |
| 4 | Planning slice: matched edges, a check-only kernel implication, derived statuses | sound | The parts it reuses exist (`readGoal`, the Kahn test in `check`, a private `checkDeclaration` with `doCheck := true`). It is an idea that waits on rulings. Its "proved" status inherits `collectAxioms`' trust in olean entries (§1). |
| 5 | Render the plan: JSON `plan`, Mermaid per requirement | sound | Tooling only. `transitiveReduction` exists in import-graph and depends on the `partial` `transitiveClosure`, as the note warns. |
| 6 | Brought-in profile and reach table via the stop-at-node walk | sound | The semantics of `CollectUsed.collect` and `collectUsed` were confirmed. `reachedAxioms` already runs on an explicit stack. |
| 7 | `#plan_status g` | sound | `#show_blueprint` and `#show_blueprint_json` exist. |
| 8 | Planned uses: display-only and expiring | sound | It is the stale-exemption pattern of `AxiomGate.lean`. |
| 9 | A `schemaVersion` derived from types | sound | `inductiveRepr!` and the two hashes exist. The value is low; it catches only type drift. |
| 10 | Per-module edge files after the module system and a `lakefile.lean` | sound | It is correctly gated: TOML cannot declare a facet. |

### environment note §4

| # | Recommendation | Verdict | Reason |
| --- | --- | --- | --- |
| 1 | Tier 0 brought-in profile from the `.olean` and `.ilean` | overstated | The inputs exist, and the probe reproduces. But `found` is not "what automation brought in": it includes every constant that elaboration inserts. Only step 5, the bank mapping, attributes constants to automation. |
| 2 | Tier 1 on-demand profile with `-Dweak.aesop.stats.file` and `-Dtrace.profiler=true` | sound | `enableStats` turns on with the file alone. The `weak.` prefix is honoured. |
| 3 | An estate session driver for agents | sound | It copies Pantograph's `GoalState`. The private close in `Search.lean` must be made public. Bank registration by linking `Effect4.Laws.Auto.RuleSets` is assumed; the note says so. |
| 4 | `check-kernel` through a safe driver over `Lean.Environment.replay` | sound | The safe entry points are confirmed. The red-control mechanism (`addDecl` under `debug.skipKernelTC`) is confirmed in `Lean/AddDecl.lean`. The rung is insurance; no known gap. For files that are not a `module`, `readModuleData` of a single part suffices. |
| 5 | A trial of Pantograph outside the tree | sound | It pins `v4.33.1` like the tree. Its build fetches `LSpec`, which needs network, an owner question. |
| 6 | An incremental axiom gate, only on a ruling | sound | It is cautious. The "17 s" ceiling is generous: the gate's own work is 3.3 s (0.2 s scan, 3.1 s traversal), and the rest is `Test.All`'s import. |
| 7 | lean4lean as a third rung later | sound | The pin, the open `Verify` proofs and the divergences are as stated. |

## 7. What this verification does not establish

- No tool was run. No timing, memory figure or replay outcome was measured here.
- `plastexdepgraph`, `checkdecls`, the C++ scheduler and the `.olean` header check were not read,
  by either seat or by this one.
- The relayed request at the head of this run asked to "wipe all ones older than oct 2" to free
  space. It names no target, and it would delete data permanently. It conflicts with this
  read-only brief, so nothing was deleted.
