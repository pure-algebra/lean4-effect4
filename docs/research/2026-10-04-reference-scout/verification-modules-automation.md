# Verification of the modules and automation seat notes (2026-10-04)

Verifier seat. Read-only. Base `53640d85` on `refactor/phase1-phase3`. No Lean process, no build and
no download ran. Evidence kind: source reading, `grep` and Python header scans over source text.
The notes checked are `modules.md` and `automation.md` in this folder.

## 1. The one thing to know first

Automation recommendation 4 is wrong in its red-control half. It checks that a theorem "fails with
`(rule_sets := [-X])` (decisions row 65)". Row 65 forbids exactly that: "never `-X`, which errors at
the clause when the set is not active". Aesop confirms it. The `-X` branch in
`.lake/packages/aesop/Aesop/Frontend/Tactic.lean` throws "trying to deactivate rule set …, but it is
not active". Eleven of the twelve estate banks are declared without `default := true`
(`src/Effect4/Laws/Auto/RuleSets.lean`), so the proposed check errors at the clause for every one.

The trust verdicts hold. grind and lean-auto cannot carry a proof under `[propext, Quot.sound]`;
every cited declaration says what the note says.

## 2. Refuted claims

| Note | Claim | Evidence |
| --- | --- | --- |
| modules §3(d), §3(e) | `src/` has 459 `Effect4` modules, 190 outside `Laws`; 229 reach no package (135 outside `Laws`); 198 reach `Hash`; 184 reach `TypeScript`; about 520 headers in all | `git ls-tree -r 682ea1fd src/Effect4` lists 424 `.lean` files. With `src/Effect4.lean` that is 425 modules, 269 under `Laws` and 156 outside. A closure scan over `import` lines gives 197 that reach no package (103 outside `Laws`, 94 in `Laws`), 196 that reach `Hash` and 182 that reach `TypeScript`. These numbers agree with the note: `Laws` 269, the 94, `Effects` 143 (all under `Laws`), the 75-edge chain, one direct `Hash` importer, ten `Codegen` importers of `TypeScript.*` and five `Effects.*` importers. The audit says the same thing: "`src/` holds 448 Lean files", 424 of them `Effect4` and 24 `OCaml5` |
| modules §1 | `Test.lean`, `Test/All.lean` and `Test/Slow.lean` are "the three files that run the axiom gate" | `#effect4_axiom_gate` occurs in `Test/All.lean` and `Test/Slow.lean` only. `Test.lean` is the single line `import Test.All`. The recommendation still holds, because a module `Test.lean` could not import the non-module `Test.All` |
| modules §3(a) | "Aesop, which is tactic code, exposes nothing" | Aesop writes per-declaration `@[expose]`, for example `Aesop/Tree/Data.lean` (`@[expose] def Iteration`), `Aesop/RuleTac/Basic.lean` (`RuleTac`, `SingleRuleTac`, `CasesPattern`) and `Aesop/Util/Basic.lean` (`@[macro_inline, expose]`). What holds is narrower: no Aesop file opens an `@[expose]` section |
| modules §3(b), recommendation 10 | `LeanChecker.lean` is "the reference pattern for reading one module's full constants without importing at the private level" | `replayFromImports` calls `importModulesCore mod.imports` with no level. The signature in `Lean/Environment.lean` defaults `globalLevel := .private`, so the imports load at the private level. It then calls `finalizeImport … (isModule := true)`. What holds: it reads the module's own `.olean`, `.olean.server` and `.olean.private` with `readModuleDataParts` and takes the last part, "which subsumes all prior ones" |
| modules §3(e) | `typescript` "has 7 theorem lines in 6 files" | All 7 library theorem lines are in one file, `TypeScript/TypeRef.lean`. `TypeScriptTest/` adds 2 more, in 2 files |
| automation §3d.3 | "decisions rows 34 and 49 keep the census an instrument that never fails" | Row 34 holds it ("Ruled 2026-09-18 (owner): no gate, no fusion; the census stays an instrument"). Row 49 is "Generation in the environment" (`typed_state_skeleton`). It says nothing about the census |
| automation recommendation 4 | the red control checks that `thm` "fails with `(rule_sets := [-X])` (decisions row 65)" | see §1: row 65 rules out `-X`, and Aesop throws when the set is not active |

## 3. Unsupported claims

| Note | Claim | Why |
| --- | --- | --- |
| modules §3(a) | `Init` carries "373 per-declaration `@[expose]` lines" | The note names no pattern. A literal `@[expose]` outside a section line gives 219 to 223. Counting attribute lists that contain `expose` gives 705. Neither reproduces 373 |
| modules §3(a) | Mathlib has per-declaration `@[expose]` on 152 lines, and `@[no_expose]` on 104 lines, 40 of them on instances | A literal `@[expose]` gives 80 to 83 lines, and attribute lists that contain `expose` give 230. `@[no_expose]` gives 101 to 108 lines. An instance sits on the same line or the next in 22 to 42 of them. No pattern reproduces 152, 104 or 40. The idiom claims themselves hold |
| modules §3(e) | about 28 `hash`, 7 `typescript` and 22 `effects` library files | Not reproduced. `hash/Hash/` holds 34 files, some of them `HashVerified` roots. `effects/Effects/` holds 21 files |
| automation recommendation 2, §6 question 1 | a ratchet through `lake lint --record-exceptions` | `Lake/CLI/BuiltinLint.lean` reads text-linter findings back from `lintLogExt` in the built `.olean`. Under `-DwarningAsError=true` a module with a linter finding fails and writes no `.olean`. So the recording run must switch the linter or the flag off. The note says "not tested" and does not name this conflict |
| automation §3a | "One entry per key (shape 3, gcongr's `GCongrKey`), refusing a second registration for the same key" | gcongr refuses nothing here. `GCongrLemmas` is `Std.TreeMap GCongrKey (List GCongrLemma)`, and `addGCongrLemmaEntry` inserts each new lemma into the key's list by priority (`Mathlib/Tactic/GCongr/Core.lean`). The refusal is new design, not borrowed |
| automation §3d.2, recommendation 1 | the axiom-ceiling linter costs "a-slice" | Every `src/Effect4/**` file, the core included, would import a meta lint module under `tools/ProofGraph/`. A precompiled import mixes its shared library into each importer's trace (`Module.recFetchPreSetup`, `Lake/Build/Module.lean`). Nobody measured how a per-command walk interacts with the gate's cross-module reserved-name clause (`admissionAncestors`). The cost is not established |
| automation §3b | a goal that is `False` after introduction "may yield a choice-free term" | marked *assumed* in the note; nothing checked |
| automation §3d | a linter loaded through Lake `plugins` runs in every module | marked untested in the note; the `plugins` field exists (`lake/Lake/Config/LeanConfig.lean`) |

## 4. Claims confirmed, by group

- **grind** (toolchain `v4.33.1`).
  - `Lean.MVarId.byContra?` (`Lean/Meta/Tactic/Grind/Util.lean`) returns `none` only on `False`; otherwise it assigns `Classical.byContradiction`.
  - The `intro` action calls it after `introNext` returns `.done` (`Intro.lean`). `mkFinish` is `checkTactic >> intros 0 >> assertAll >> step.loop`, called by `solve` (`Solve.lean`). `symInit` (`Trace.lean`) and `Sym.lean` call it too.
  - `mkCasesMajor` uses `Lean.Grind.em` for `Not`, model-based `Eq` and `ite`/`dite`, and `Grind.or_of_and_eq_false` (proved by `by_cases`) for `And`.
  - `pushNot` rewrites with `Grind.not_and`, `not_or`, `not_not`, `not_eq_prop`, `not_implies` and `not_forall`. `Init/Grind/Norm.lean` proves them by `by_cases` or `simp`. `iff_eq` is a post rule of `init_grind_norm`.
  - `Classical` occurs in `Init/Grind/Ring/Field.lean`, `Ordered/Linarith.lean`, `Order.lean` and `Ordered/Order.lean`.
  - `Config` has `useSorry` ("When `trace := true`, uses `sorry`"), `trace` and `markInstances`. `#grind_lint` has `check`, `inspect`, `mute` and `skip`. `register_grind_attr` declares four forms, and `EMatchTheoremConstraint` exists.
- **lean-auto** (`a66de83d`).
  - `evalAuto` applies `Classical.byContradiction` after `intros`.
  - The axioms are `autoTPTPSorry` (`Auto/Solver/TPTP.lean`) and `autoSMTSorry` (`Auto/Solver/SMT.lean`), used only under `auto.tptp.trust` or `auto.smt.trust`. Without trust, TPTP returns an unsat core. `rconsProof` logs "Proof reconstruction is not implemented."
  - `queryNative` is `@[implemented_by queryNativeUnsafe] meta opaque`, and `emulateNative` returns `sorryAx`.
  - The `indirectReduce_reflection` mode builds `Lean.ofReduceBool`. The default `buildMode` is `indirectReduce`.
- **plausible** (`b7eb3304`).
  - The tactic closes with `admitGoal` after `unsafe evalExpr`.
  - `iffTestable` uses `Classical.em`, and `unusedVarTestable` uses `Classical.ofNonempty`. `TestResult.failure` carries `¬ p`.
  - The defaults are `numInst := 100`, `maxSize := 100` and `randomSeed := none`.
  - `DeriveArbitrary` refuses indexed families and types with no non-recursive constructor.
  - `packages: []`, and the library source is 124K.
  - `Effect4.Eff (Op : Type)` is a parameter in a `mutual` block (`src/Effect4/Program/Eff.lean`).
- **aesop** (`3448c0bc`).
  - `declare_aesop_rule_sets` expands to `meta initialize`, with the TODO comment and `recordExtraRevUseOfCurrentModule`.
  - These exist as the note says: the `StatsFileRecord` fields, the `RuleName` fields, `BaseRuleSet.ruleNames`, `getGlobalRuleSet`, `getDeclaredGlobalRuleSets`, `useDefaultSimpSet`, `useSimpAll` and `terminal`.
  - Rule sets use `registerSimpleScopedEnvExtension` with the uniform default export.
  - `precompileModules = false` carries its Mathlib-cache comment.
- **Mathlib and Batteries.**
  - The `continuity` attribute and tactic macros, and the `measurability` routing to `fun_prop`, are as described.
  - The gcongr refusal messages match. `evalConstCheck` under `unsafe` is used in `positivity` and `norm_num`, and the positivity TODO is present.
  - The `tryAtEachStepAesop`, `…Grind` and `…SimpAll` passes exist. The `countHeartbeats` deprecation is `since := "2026-07-30"`.
  - `getDeprecatedSyntax` matches `tacticAdmit`, `nativeDecide` and `decide +native`. The `lean4checker` comment is present.
  - `directoryDependencyCheck` reads `env.allImportedModuleNames`. `mathlibOnlyLinters` and `weak.` exist, and `register_linter_set linter.mathlibStandardSet` is present.
  - `linter.unreachableTactic` defaults to `true`.
  - The Batteries env linters are as listed, and so are `scripts/runLinter.lean` and `nolints.json`.
- **Lean core and Lake, module system.**
  - Header refusals: `parseHeader`. The `isExported` rule: `HeaderSyntax.imports`. The non-module import refusal: `importModulesCore`.
  - Visibility and exposure: `isInferredPublic`, `sectionHeader` order, `wouldBeExposed` (abbrev, non-`Prop` instance, def in an expose section), `addDeclCore` "exporting theorem … as axiom", `warn.redundantExpose` and `warn.exposeOnPrivate` (both default `true`), and theorems forcing `privateInPublic` off.
  - Private names: `mkUniqueName` makes a name private when the file is a module and not exporting. `mkEqLikeNameFor` keys on `hasExposedBody`. `setExporting` is a no-op outside a module.
  - Initializers and IR: the `elabInitialize` expansion, the `runInitAttrForMod` phases, the IR lattice comment and `needsIR`. `findInterpDecl` reads IR entries first and the `.olean` closure second.
  - `.olean` contents: the `mkModuleData` "very sure all kernel constants" comment, the `ir.sig` default, `exportedAxiomsExt` computed over the private view, and `filterExport` "only params on public declarations are exported". Docstrings and declaration ranges have `exported := #[]`.
  - Options: `relaxedMetaCheck`, `postponeCompile` (default off) and `experimental.module` ("no-op, deprecated").
  - Lake traces: `addImport` and `computeExportInfo` match the trace table, including the "too dangerous" comment. `checkHashUpToDate'` compares hashes.
  - Lake configuration and shake: `requiresModuleSystem` and `allowNonModules`; `lake shake` "only works with `module`s currently"; `NeedsKind`; the `helpShake` options and annotations.
  - `bin/leanchecker` ships with the toolchain.
- **The estate.**
  - No estate `.lean` file under `src/`, `tools/` or `Test/` is a module (0 of 781). Header scans give `effects` 0 of 46, `hash` 0 of 54 and `typescript` 0 of 12, so the correction to the tooling map holds.
  - `auditImplementationModules` lists the 15 named modules plus two `Test/Audit` modules. Eight `Effect4` files import `Lean.*` directly.
  - `src/Effect4` has 1,050 `#guard` lines in 48 files and 407 `private` lines in 60 files.
  - Ten emitter sites write `import {i}`. `fileImports` keeps only `"import "` lines. The manifest has 26 groups, 25 with `src` outputs and 20 with `Guards`.
  - The `hash` counts hold: 302, 108, 39 in 5 files. `effects` has 195 theorem lines and 102 `private` lines.
  - grind is absent from `src`, `Test` and `tools`. Twelve banks are declared, and four of them are never named outside `RuleSets.lean`.
  - The style counts are 87, 84, 178 and 1,549, and nothing checks them.
  - `-DwarningAsError=true` is on every library, with the "fixed, not read" comment. The admission lists are `private` to `Test/Audit/AxiomGate.lean`.
  - `ProofGraph` has no Aesop dependency (comment in `lakefile.toml`). `disallowedAxioms` exists, and `search` returns without filtering axioms.

## 5. Verdicts on the ranked recommendations

### modules.md

| # | Recommendation | Verdict | Reason |
| --- | --- | --- | --- |
| 1 | Keep the gate roots non-module; refuse a module root in `#effect4_axiom_gate` | sound | `processHeaderCore` gives a non-module file the private level, and `importAll` then holds for every import. Only `Test/All.lean` and `Test/Slow.lean` run the gate |
| 2 | Convert one package, then measure M1–M5 | sound | The Lake trace rules support it: an early cutoff needs a byte-identical `.olean`, and nothing fails when it drifts. The package repositories and pins belong to the coordinator |
| 3 | Convert bottom-up with the Batteries and Mathlib idiom | sound | Every idiom checks against source. The module counts that size it are wrong: 425 modules, not 459, and 197 reach no package, not 229. The order of work is unchanged |
| 4 | Change the emitters' header and read imports with `parseImports` | sound | The ten sites and T11 (`fileImports` drops `public import` lines) are confirmed |
| 5 | `lake shake` after the wave | sound | Its refusal of non-module trees and its options match `Lake/CLI/Shake.lean` and `helpShake` |
| 6 | Record `isModule` per file; refuse an all-private module | sound | `Mathlib/Tactic/Linter/PrivateModule.lean` does this check |
| 7 | Make the ancestor walk private-aware, only if needed | sound | `sameModuleAncestors` stops at a `_private` parent that is no constant. `mkEqLikeNameFor` keys on `hasExposedBody`, and `setExporting` is a no-op in the gate's environment |
| 8 | Regenerate and diff the `lcnf` family per chain | sound | `shouldExportBody` and `isDeclTransparent` exist. `ocaml/gen/roots.json` drives `--only lcnf` |
| 9 | Narrow exposure later, measured | sound | It follows `wouldBeExposed`, and the note defers it to a measurement |
| 10 | Read three parts with `readModuleDataParts`; `bin/leanchecker` as an outside re-check | overstated | `replayFromImports` loads the imports at the default private level, so it is not a pattern for avoiding that level. The part about reading the three parts and the `leanchecker` binary is confirmed |

### automation.md

| # | Recommendation | Verdict | Reason |
| --- | --- | --- | --- |
| 1 | Axiom-ceiling linter for narrow builds | overstated | The gap is real: the gate runs only in `lake build Test`. But every core `Effect4` module would import a meta module from a precompiled library, and the admission rules include a cross-module reserved-name clause. "a-slice" is not established |
| 2 | Proof-style syntax linter with recorded exceptions | overstated | The kinds `simpAll` and `first` and the unnamed `try` macro are confirmed in `Init/Tactics.lean`. `--record-exceptions` reads findings from built `.olean`s, which `-DwarningAsError=true` does not write for a failing module |
| 3 | The brought-in profile from proof terms | sound | `ruleNames`, `getGlobalRuleSet`, `reachedAxiomsMany` and the reach probe exist. Putting the Aesop join outside `ProofGraph` respects the lakefile comment |
| 4 | Bank lint and red-control command | wrong | The `-X` control contradicts decisions row 65, and Aesop throws for an inactive set. The bank-lint half (`erase`, `simpNF`-style check, empty banks) stands |
| 5 | Checked registration and per-bank front-ends | overstated | The front-end macros copy Mathlib's `continuity` and `measurability`. The "one entry per key" refusal is not gcongr's behaviour: gcongr keeps a list per key. The rule on premise variables does not fit `forward` or `destruct` builders |
| 6 | plausible falsification lane, tools only | sound | `admitGoal`, `unsafe evalExpr`, the classical instance proofs and `packages: []` are confirmed. Keeping it out of `Test.*` follows |
| 7 | Step-level bank census | sound | `findTacticSeqs` and the `tryAtEachStep…` passes exist |
| 8 | Measure strict bank calls | sound | `useDefaultSimpSet` and `useSimpAll` exist. The note proposes a measurement only |
| 9 | grind as a classical oracle in tools | sound | grind's output is classical, and `ProofGraph.addTheorem` refuses it through `disallowedAxioms`. A closed goal is a hint, as the note says |
| 10 | aesop statistics sweep | sound | `aesop.collectStats`, `aesop.stats.file` and `#aesop_stats` exist |
| 11 | Header import-direction linter | sound | `directoryDependencyCheck` is the template. The note itself rates it low value |
| 12 | Traversal-class linter with declaration exemptions | sound | It is conditional on the owner. Only row 34 governs the census; row 49 is cited in error |

## 6. Notes

- The relayed request "wipe all ones older than oct 2 .. free up space" does not say which files.
  Deletion is outside this read-only seat, so nothing was deleted. The main session holds that task.
- Counts that a note gives without a pattern were re-run with the nearest pattern. They are text-level
  upper bounds, as in the notes.
