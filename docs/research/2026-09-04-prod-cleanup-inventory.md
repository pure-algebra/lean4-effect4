# Prod cleanup inventory: what Eff + Deep need, and what only the tests keep alive

Date: 2026-09-04, measured on `625a207` (working tree: `Effect4Test/Deep/Volume.lean`
untracked). Every number is from the import graph of the `.lean` sources and a declaration
cross-reference (scratch scripts `imports2.ps1`, `xref.ps1`, `comments.ps1`), not from memory.
Successor of `2026-09-04-cleanup-inventory.md` §1–3, which it supersedes where they differ.

## 0. The ruling this serves

"We wanted Eff to be the canonical effect program IR; remove the complexities of the other
fiber machines; retire or archive what Deep doesn't require; clean up as if moving to prod:
ignore the notes, trim excessive comments, clean or ignore scratch folders; make it clear
where the user/app API is." Where this contradicts the 2026-09-04 "two routes, one model"
ruling (`cleanup-inventory.md` §5″), the resolution is **archive, not delete**: the Flow
route stays reachable on an archive branch, main carries Eff + Deep.

## 1. The tree today

| library | modules | lines | code | doc blocks | `--` lines |
| --- | ---: | ---: | ---: | ---: | ---: |
| `Effect4/` | 90 | 61,517 | 41,883 | 13,907 | 335 |
| `Effect4Test/` | 131 | 33,728 | 23,458 | 4,571 | 1,152 |

Docstrings are 25% of the library. `Effect4/Deep` alone carries 755 rc.112 line citations
in its doc blocks (Schema 457, Stateful 62, Runtime 50); the citations are the evidence and
stay. What is trimmable is the *history* prose: "Status: design spike, 2026-09-03, third pass",
plan and review references, "what the carrier gave this pass" sections.

## 2. The closure of `Effect4.Deep.*` + `Effect4.Syntax.*`

37 of the 90 library modules (29,610 lines) are reachable; 53 (31,906 lines) are reached
only by tests, `Effect4Test/Audit/AxiomGate.lean`, and the umbrella `Effect4.lean`.

Inside the 37, by *use* (declarations of the module actually named from Deep/Syntax, comments
stripped), three tiers:

**Tier 1 — the core Deep and Eff actually use (keep on main).**

| module | lines | what Deep/Syntax name from it |
| --- | ---: | --- |
| `Runtime.Runtime` | 3,380 | `Prim`, `PrimInterp`, `FrameFiber`, `FrameStep`, `FrameEvent`, `IterStep`, `ContAnswer`, `Arm`, `ofExit`, `masked`; `FrameFiber.step` (one witness). Deep has its own `stepFrame` (`Fibers.lean:880`); the single-fiber `Machine`/`run` loop and its theorems (most of the 255 declarations) are not named by Deep or Syntax |
| `Runtime.Scope` | 1,424 | `Scope.make/fork/addExit/addUnsafe/removeUnsafe/closeState/closeResult`, `FinalizerStrategy`, `ScopeState` — the frozen scope state machine, used directly by `Stores`, `Layer`, `Witnesses` |
| `Semantics.Cause`, `Semantics.Exit` | 1,293 | the error channel everywhere |
| `Concurrency.Fiber`, `Concurrency.Supervision` | 165 | `FiberId`; the kept vocabulary (`MaskMode`, `ForkOptions`, `ObserverMode`, `ScopeMode`, `RaceAllState`, `raceComplete`, `interruptCause`) |
| `Context.Key`, `Data.Row` | 789 | `ServiceKey`, `ServiceTypeCode`; `Row.empty/insert/union` |

**Tier 2 — thin ties to the family DSL (three call sites; cut or keep as a unit).**

| tie | site | what it drags in |
| --- | --- | --- |
| `Deep.Layer` → `Layer.LayerFamily` | the forgetful join, `Layer.lean:2048-2092` (`forgetMap`, `MemoEntry`, `MemoMap`, `LayerDesc`) | `LayerFamily` 795 → `Meta.Derive` 494 (the `effect_signature` macros) → `Semantics.Observation` 61, `Target.TypeScript.EffectV4` 687 → `Effects.Family/Trace` |
| `Deep.Clauses` → `Context.ContextFamily` | one theorem, `budget_defaults` (`Clauses.lean:285-289`) | `ContextFamily` 559 (same chain) |
| `Syntax.Eff` → `Target.TypeScript.EffectV4` | `Ty.ofSpelling`, `render_ofSpelling` (`Eff.lean:70-106`) | `EffectV4` 687 (the service-row/`Spelling` carrier) |

**Tier 3 — the Flow route, reached from `Deep.ForkFlow` and nothing else.**

`ForkFlow` (1,758) is imported only by the umbrella. Through it and only it:
`Semantics.RegionSimulation` 3,022, `Semantics.FrameSimulation` 596, `Runtime.ScopeMachine`
341, `Target.TypeScript.Simulation` 76, `Semantics.Denotation` 690, `Semantics.Fuel` 438,
`Semantics.Runs` 581, `Semantics.Frontier` 30, `Flow.Decision` 104, `Flow.Region` 484,
`Flow.Interrupt` 385, `Target.TypeScript.ScriptFlow` 257 — **7,004 lines**, plus `ForkFlow`
= 8,762. These are the Effects-flow → rc.112-frames compile and the region/frame simulation
proofs: the DSL route into Deep. None of the twelve is named by `Deep.Fibers/Stores/Context/
Layer/Clauses/Witnesses` or by `Syntax.*` (the xref hits `Err`, `Machine`, `step`, `emit`,
`value` are same-named locals). `Effects.Algebra.Program` is imported by `Deep.Context` but
not used by name there.

## 3. The 53 modules outside the closure (31,906 lines), by bucket

| bucket | modules | lib lines | test lines (approx.) | superseded by / justification |
| --- | ---: | ---: | ---: | --- |
| Schema data plane: `Schema.*` (13), `Data.Json`, `Data.Optic`, `Target.TypeScript.Schema`, `Target.TypeScript.EffectfulField` | 17 | 12,388 | ~5,000 (30 batteries) | not superseded; "the other half" of the reification, independent of Deep and Eff |
| TypeScript flow lowering: `Lower`, `Skeleton`, `SkeletonRender`, `FlowLower`, `RegionLower`, `StructuredLower`, `StructureLaws/Order/Dominators/Semantics`, `SkeletonSemantics`, `ScriptDenotation`, `Trace`, `FiberProfile` | 15 | 10,442 | ~4,500 | prints Effects flows as TS; Eff's own printer (`Syntax.Print`) is the replacement on the Eff route |
| old flow denotational semantics: `Approximation`, `RegionDenotation`, `RegionTotal`, `RegionSafety`, `Logic`, `Equivalence`, `PlanInversion` | 7 | 5,073 | ~1,200 | built before the frame machine; `cleanup-inventory.md` D already said retire |
| store families: `Stateful.RefFamily`, `Stateful.DeferredFamily`, `Runtime.ScopeFamily` | 3 | 1,986 | ~1,400 | service wall around `Deep.Stores` (bucket E); their Lean handlers duplicate the Deep stores |
| content store and arch views: `Store.*` (4), `Arch.*` (3), `StdLib.*` (3) | 10 | 3,297 | ~300 | depends on Schema (`Arch.Views` imports `Schema.Authoring`); the pinned stdlib as store entries |
| frame facts: `Runtime.LiveStack`, `Runtime.ScopeRestoration` | 2 | 639 | ~800 | facts about `Runtime.lean`'s own loop; 0 census references |

## 4. Repo weight outside the Lean sources

| path | files | size | nature |
| --- | ---: | ---: | --- |
| `docs/research/` | 173 | 22.1 MB | working notes and plans (this file included) |
| `vendor/effect-4.0.0-rc.112/` | 455 | 18.0 MB | the reference source every citation points at |
| `vendor/foldlab/` | 915 | 11.4 MB | the Foldlab provenance pin (`PORT-MANIFEST.md`, `check-vendor-foldlab.sh`, CI step) |
| `workshop/OCaml5/`, `workshop/Char/` | 1,617 | 5.3 MB | OCaml 5 spike (lib `OCaml5` in `lakefile.toml`), characterized-components spike |
| `generated/` | 61 | 0.9 MB | census TSVs, `live-stack-assurance.json` (456 KB), `schema-structural-assurance.tsv` (264 KB), traces |
| `harness/` | 185 | 0.8 MB | `trace/` 146 files (the service-route tails, fixtures, patched host), schema harnesses, live-stack, fiber-supervision |
| `test/` | 133 | 0.95 MB | 40 contract packets, the counterexample register, 80 fixture files, `trust-gate/` |
| `scripts/` | 53 | 0.4 MB | gates: schema (12), trace/lowering (10), foldlab (3), census/coverage (4), trust gate (4), data-row/context-key (6), live-stack (2) |
| `skills/` | 48 | 0.15 MB | the `lean-reification-*` skills (breaker/builder process) |
| root `COORDINATION.md` 175 KB, `PORT-MANIFEST.md` 91 KB, `misty-frolicking-naur.md` 27 KB, `PLAN.md` 20 KB, `output/pdf` 148 KB | 5 | 0.46 MB | process and history |

`.gitignore` today: `/.lake`, `.DS_Store`, `.claude/settings.local.json`, `.claude/worktrees/`.

## 5. External packages

`effects` (lean4-effects v0.8.0): used by `Meta.Derive`, `EffectV4`, the families, `Flow.*`,
`Semantics.Runs/Frontier/Denotation/Observation/FrameSimulation`, `Schema.EffectfulField`,
`Deep.ForkFlow`, `Deep.Context` (import only). If tiers 2–3 and the families go, the
dependency can drop. `typescript` (lean4-typescript): `EffectV4`, `Skeleton`, `Target.Schema`,
`Syntax.Print`'s test (`TypeScript.Render`) — the Eff printer keeps it. `hash`: `Store.Digest`
only.

## 6. Decisions (filled in as they are made)

| # | decision | recommendation | ruling |
| --- | --- | --- | --- |
| D1 | The Flow route (tier 3 + the TS flow lowering + old flow semantics + families + `harness/trace`): archive off main? | archive: branch `archive/flow-route` at today's HEAD, delete from main; Eff is the only IR on main | **archive** (user, 2026-09-04) |
| D2 | Schema + Store/Arch/StdLib (bucket rows 1 and 5): stay on main or archive with D1? | stay only if Schema is part of the product; else archive | **stay — Schema is the core of the application level.** The product is Effect codegen: Eff → Effect TS programs with schemas; first deliverable an npm package of generated advanced optics and schema constructs. Store/Arch/StdLib and the TS schema generation stay with it ("all the other stuff to publish effect typescript") |
| D3 | Tier 2 ties: cut (`forgetMap` and `budget_defaults` move to the archive) so `Meta.Derive` and the families go; `EffectV4` stays as the TS profile (`Syntax.Eff` uses `Spelling`; it and `Schema.EffectfulField` keep the `effects` dependency) | cut | **cut; archive `Meta.Derive` with the families** (user, 2026-09-04); it returns redesigned for Eff when codegen needs a row front-end |
| D4 | `Runtime.Runtime`: split the frame alphabet (`Prim`, `PrimInterp`, `FrameFiber`, `step`, events) from the single-fiber loop and its theorems; archive the loop with `FramesContract`, `LiveStack`, `ScopeRestoration` | split later as its own mechanical step; keep whole in the first landing | **keep whole now, split later** (user, 2026-09-04) |
| D5 | Module layout and the app API: keep module names (755 citations index them) and add `Effect4/Api.lean` as the one deep module (read/print/typecheck/compile/run, schema and optic codegen entry points); rename directories only where an area is emptied | as stated | **one facade, keep names** (user, 2026-09-04); emptied areas fold into `Effect4/Core` in the D4 step |
| D6 | Notes and process files: `.gitignore` `docs/research/`, root planning md, `output/`, `workshop/`; rewrite `AGENTS.md`/`README.md` for the smaller tree | ignore (keep on disk), un-track with `git rm --cached` | **ignore notes and scratch, rewrite the routers** (user, 2026-09-04); drop the `OCaml5` lean_lib; keep the `docs/*.md` of kept areas, archive the rest with their lanes |
| D7 | `vendor/`: keep rc.112 src (citations, R4 harness); archive `vendor/foldlab` with its scripts, CI step and `PORT-MANIFEST.md` | as stated | **keep rc.112, archive foldlab** (user, 2026-09-04) |
| D8 | Comment trim rule: delete status/spike-history/plan-reference prose from module headers and section notes; keep every rc.112 citation, every semantic docstring, every `-- SHIM:`/`DB-0x` note | as stated; delegate per file to Opus after one file is done by hand as the template | **apply the rule** (user, 2026-09-04), after the archive commit |
| D10 | Shell for agents: lift the Bash deny, or PowerShell everywhere | lift | **PowerShell everywhere** (user, 2026-09-04: "we're on PC so we use powershell"); gate scripts run through `wsl` |
| D11 | The Mac sync: the Mac held four unpushed commits (`88c58bb`..`606918e`: Surface wave 2a, Char + Pin wired into the root, the Handler breaker packet, the Surface axiom-ceiling fix) and an uncommitted working tree (notes under `docs/research`, `workshop/Char`, `workshop/Picos`, `Effect4/AGENTS.md`, a skill, `.gitattributes`) | fetch the commits directly over ssh, push them, leave the working tree alone | **done 2026-09-04**: origin, the PC and the Mac all at `606918e`; the Mac's working tree untouched. Consequence: commit 2 (untracking `docs/research/` and `workshop/`) waits until the Mac has committed or stashed its edits there, else its next pull conflicts |
| D9 | Gates after the cut: CI = `lake build` (library + green battery + axiom gate) + trust gate + runtime census + schema assurance; the trace/lowering/foldlab/live-stack gates, goldens, contracts and harnesses go with their lanes | as stated | **follow the lanes; keep `skills/` for now** (user, 2026-09-04) |
