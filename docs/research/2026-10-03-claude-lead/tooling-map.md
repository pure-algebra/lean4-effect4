# Tooling for the next wave: a measured map

Base: `394bc602`, last revised 2026-10-03. Author: Claude, lead. Status: a proposal for the owner,
updated in place as its items land. It lands no planned work. The commands behind the numbers are
at the end.

**The one thing to know.** The tooling decides what gets proved and what gets skipped. A slow check
does not run, and a check that does not run catches nothing. This session found three checks that
had failed unnoticed:

- `make check-gen`, since `0821bb2d` (fixed in `089d9d97`);
- `make check-semantics`, since `e8222420` (fixed in `bca33ff6`);
- `make check-tools`, since `f0591f36` (fixed in `580261d6`).

So this map starts with speed, then visibility, then documents.

## 1. The planned work, read as tooling needs

The owner's plan has five obligations and one vertical example. Its order of dependence starts with
formation and parameter scope, then shared type and value contracts. It ends with typed program
authoring, host-session typing and an LCNF lowering checked against named observations.

| Planned obligation | What it produces | What it needs from the tooling |
| --- | --- | --- |
| P1 formation | a validity judgment, its checker and their agreement | a place for the judgment; reachability of the checker from public program admission (2.5) |
| P2 value operations | access, lookup and indexing over the membership rules | coverage of every face per constructor (2.4); a proof bank when it starts |
| P3 Schema and codecs | Schema descriptions and codec exactness on stated domains | the coverage table; codec claims labelled with their domain |
| P4 session typing | six session operations that keep the typed correspondence | one general goal per operation, placed before work (2.9) |
| P5 behavioural contracts | input/output relations under named assumptions | claims that carry their fragment and observation as fields (2.1) |
| PX the profile record | construction, access, publication, round trip, reply | controls recorded as data, shown per claim (2.8) |

## 2. The state, measured

| What | Before | Now | Commits |
| --- | --- | --- | --- |
| `Laws/Machine/Handles` in a full build | 153 s | 13 s | `8bb23308` |
| the same, compiled alone under load | 107 s, tactic interpreted | 66 s, tactic native | `580261d6` |
| `Test.All`, where the axiom gate runs | about 45 s | 17 s | `580261d6`, `834bf7bb` |
| the gate's declaration scan, one process | 33 s | 0.2 s | `580261d6` |
| the gate's axiom traversal, one process | 7.1 s | 3.1 s | `580261d6` |
| the derived generation group | 301 s | 39 s | `089d9d97`, `2f8da42d` |
| the semantics report | 27 s | 7 s | `e8222420`, `bca33ff6` |
| the semantics controls | 57 s | 5 s | `e8222420`, `bca33ff6` |
| a fresh worktree's first build | 318 s, 807 jobs built | about 1 s, 815 jobs restored | 1.3 below |
| `Laws/Program/TyView` (generated), on a quiet machine | 48 s | 14 s | 1.11 below |
| `Test.Store.DerivedCheck`, the projection guard | 33 s, guard interpreted | 9.4 s, guard native | 1.12 below |

Four more facts bound the next steps:

- **A build from scratch is bounded by total work.** One build of every module, measured at
  `edc4da72` under load (load average 15 to 27, swap 6.4 of 7.2 GB used by other processes):

  | Measure | Seconds |
  | --- | ---: |
  | wall time, 607 modules | 1451 |
  | summed module time | 4226 |
  | summed time divided by the 3 parallel jobs | 1409 |
  | critical path, 71 modules | 534 |

  The wall time is the summed work divided by the job count. The critical path is far below it,
  so more jobs or less work would shorten the build, and shorter chains would not. The Laws
  modules of `Effect4.Laws.Program` take 42% of the work, and the batteries under `Test` take 20%.
- **Load inflates module times three- to fivefold.** `Laws/Program/Handles/Hooks` took 84 s and
  51 s in loaded builds. On a quiet machine it took 16 s: 4.4 s of import and 10.2 s over about
  220 simp calls.
- **An edit rebuilds every module that imports it.** None of the tree's files uses Lean's module
  system, so a changed proof changes the `.olean` that importers trace. Measured from the same
  build:

  | Edit in | Median modules rebuilt after it | Median work |
  | --- | ---: | ---: |
  | a Laws module | 11 | 80 s |
  | a Store module | 249 | 1819 s |
  | a Program module | 282 | 2063 s |
  | a Machine module | 433 | 3214 s |
- **Memory.** A bare `lake build` runs one compilation per core and swaps this 16 GB machine.
  `AGENTS.md` now bounds every Lake call at `LEAN_NUM_THREADS=3` (`6437547c`).
- **Disk.** 14 GB of 460 GB are free. A worktree that builds its own outputs takes 3 GB in
  `.lake`. A worktree restored from the artifact cache shares its outputs with the cache as hard
  links, not copies.

## 3. The items, with their status

### Lane 1 — checks fast enough to run on every change

- **1.1 Derived generation: landed** (`089d9d97`, `2f8da42d`). One compiled executable runs every
  row in one process. Open: the bootstrap property, which `2f8da42d` broke for `TyEq`. The design
  note `staged-generation.md` (`a2d6146d`) measures the prerequisites and proposes a pilot.
- **1.2 The thread bound: landed** in `AGENTS.md` (`6437547c`). Open: choosing 3, 4 or 5 by one
  measured full build each, on a quiet machine.
- **1.3 Lake's artifact cache across worktrees: landed.** `lakefile.toml` sets
  `enableArtifactCache` and `restoreAllArtifacts`. A build stores each output under its content
  hash in the toolchain's cache. A later build with matching inputs restores that output as a hard
  link. Measured in two probe worktrees:
  - a fresh worktree, with its dependency packages cloned copy-on-write, restored all 815 jobs in
    about a second;
  - without `restoreAllArtifacts`, the outputs stay in the cache only, and `lake env lean` cannot
    find them;
  - a one-module change rebuilt that module and the axiom gate (18 s), and left the other
    worktree's copy unchanged;
  - reverting the change restored the earlier outputs in a second;
  - against an empty cache, a built worktree rebuilt nothing and re-seeded the cache with hard
    links.

  So `lake cache clean` is a safe prune, and `make status` shows the cache's size and the part
  that no worktree uses. Limit: the cache holds only the states that a worktree has built since
  the setting landed. Cloning `.lake` itself does not work: Lake rebuilt every job.
- **1.4 Native tactic and gate code: landed** (`580261d6`, `834bf7bb`). Two small libraries are
  precompiled: `Effect4Tactics` and `ProofGraphNative`.
- **1.5 Compiled report drivers: landed** (`bca33ff6`): `semantics-report`, `semantics-controls`
  and `architecture-map`.
- **1.6 The build profile: landed** (`43866b84`): `make build-profile`, and one line in `make status`.
- **1.7 `Hooks` on the critical path: closed, no change.** On a quiet machine the module takes
  16 s, and no simp call takes more than 0.6 s. Its 84 s was load.
- **1.8 An incremental axiom gate: for the owner.** The gate traverses every declaration at the end
  of the build. A check per module would run in parallel and only for rebuilt modules. It changes
  the trust architecture, so it needs a ruling.
- **1.9 Compiled generation drivers: measured, not landed.** The six interpreted drivers of
  `scripts/generate.py` and `make corpus` were built as executables and timed against
  `lean --run` on a quiet machine. Both forms wrote byte-identical outputs.

  | Driver | Interpreted | Compiled |
  | --- | ---: | ---: |
  | variances | 1.9 s | 2.4 s |
  | effgen | 3.2 s | 2.7 s |
  | effwire | 2.3 s | 2.7 s |
  | casgoldens | 1.8 s | 0.6 s |
  | tsgen | 6.1 s | 2.6 s |
  | corpus | 2.1 s | 2.4 s |

  The gain is under 4 s for each driver. Five of the six executables link between 41 and 99
  Effect4 modules. After a core change, each rebuilt module among them would be compiled to C
  object code again before the next run. The report drivers of 1.5 differ. They load their
  environment at run time, and their executables link at most one Effect4 module, the semantics
  attribute (`Effect4.Laws.Auto.Semantics`).
- **1.10 Lean's module system: for the owner.** In Lake 4.33 a `module` file that imports
  another `module` traces only the public part of the import's `.olean`. Theorem proofs and
  definition bodies without `@[expose]` sit in the private part, so editing them would rebuild
  no importer. That removes most of the rebuild costs in §2. The costs:
  - Lean refuses a non-module import from a module, so adoption runs bottom-up. Three of the
    owner's packages come first: `effects` (3 of 46 files are modules), `hash` (3 of 54) and
    `typescript` (0 of 12). In the tree, `Store/Carrier/Digest` imports `hash`, and
    `Laws/Program/Denote` and `Sched` import `effects`, so nothing above them can convert first.
  - The packages' idiom keeps today's meaning: `module`, `public import` for each import, and
    `@[expose] public section`, which leaves every definition unfoldable by its importers. Only
    theorem proofs become private, and proof edits are the common change in the Laws graph.
  - A definition that an importer unfolds (`rfl`, `decide`, `simp` by its equations) stays
    exposed, so an edit to it still rebuilds its importers.
  - Tactic and generator code that a file runs needs a `meta import`.
  - The axiom gate needs proof bodies. Lake hands a non-module importer such as `Test.All` every
    part of each import, the private part included (`ModuleImportInfo.addImport`). The pilot must
    check that the gate still reaches every proof.
  - It touches every file header, so it needs a research note, a pilot on one leaf chain, and a
    ruling.

  **Owner, 2026-10-03: no pilot for now** ("these savings are adequate for now"). The analysis
  stays here as the record.
- **1.11 The slowest modules, profiled on a quiet machine.** The 40 slowest modules of the loaded
  build took 860 s here, against 1540 s there (`-Dprofiler=true`, one module at a time). Simp leads
  Lean's profile categories, then aesop. Most of these modules already write `simp only`, so a
  general rewrite of simp calls saves little. The time sits in about twenty proofs. Each splits into
  many cases and runs aesop or a `first | …` fallback in every case. Their elaboration tasks, from
  `-Dtrace.profiler=true` (tasks run in parallel and can wait on each other, so the times overlap):

  | Proof | Module | Task s | Shape |
  | --- | --- | ---: | --- |
  | the four `sameHead` laws (generated) | `Laws/Program/TyView` | 97 together | 784 cases each, aesop in each: fixed |
  | `readLeaf_print` | `Laws/Codegen/ReadPrint` | 39 | `cases v`, then aesop per case |
  | `raceSites_contAOf` | `Laws/Program/Guard/RaceSites` | 34 | `try first \| …` in every case |
  | `match_apart` | `Laws/Codegen/ReadPrint` | 31 | a split, then aesop per branch |
  | `readCapture_print` | `Laws/Codegen/ReadPrint` | 29 | |
  | `interpOf_keyBounded` | `Laws/Program/Handles/Hooks` | 23 | |
  | `evaluatePrim_pending` | `Laws/Program/Guard/ReturnFields` | 22 | |
  | `readLeaf_exact` | `Laws/Codegen/Read` | 16 | aesop near the heartbeat limit: it timed out when traced |
  | `driveStep_grows` | `Laws/Machine/Approximation` | 9 | the hop macros' `first \| …` chains (4.4) |

  - The four `sameHead` laws took one template change in `tools/Effect4Gen/View.lean`.
    `fun_cases` on `sameHead` splits by its arms, and `simp only` closes each case whose heads
    differ before aesop runs. The four now take about 4 s, and `TyView` builds in 14 s. Axioms:
    `propext` and `Quot.sound`.
  - The other proofs are rewrites, one at a time. They are recorded here, not done.
  - `Store/Domain/Derived/Schema` (generated) spends 13 s proving the unfolding equation of the
    `rawRepresentation` decoder and 9 s on its match splitter. `Derived/Program` has the same cost
    for `rawEff` and `rawTy`. The decoder's shape is the lever, with the staged-generation research.
  - Lean builds an equation lemma or a match splitter in the module that first needs it, and a
    splitter built outside its definition's module is private to the module that built it. Among
    the traced modules, `Node.child`'s splitter was built twice (13 s), `contAOf`'s three times
    (10 s), and `compileEff.eq_def` twice (7 s).
  - `Test.Program.AgreementContract` and `Test.Store.NodeContract` spend 20 s and 11 s
    interpreting Effect4 code in `#guard`s. Precompiling the core would compile every module to C.
- **1.12 The projection guard, compiled: landed.** `Test.Store.DerivedCheck` runs the guard over
  the four generated files in an `#eval`. Interpreted, the guard took 30 s of the module's 33 s.
  The library `Effect4GenNative` precompiles `Effect4Gen.Check` and `Tools.WireTags`, which import
  only Lean, the way `ProofGraphNative` does (1.4). The module builds in 9.4 s.

  Finding: `lake build Effect4Gen` fails, with or without this change. The library's glob takes
  the twenty guard files under `tools/Effect4Gen/guards/`. They are appended to generated files and
  do not elaborate alone.

### Lane 2 — obligations and progress visible from the tree

None of these has landed. Each serves the planned work directly.

- **2.1 Placement as data.** A registry claim gains the five parts of the placement rule as fields.
  The report shows them and refuses a claim that lacks one.
- **2.2 Judgments as entries.** Each of the seven judgments gets its proposition, its checker and
  its agreement claims. An unproved connection shows as a gap, never as an implication.
- **2.3 Workstreams as data.** The plan's order and the vertical example become semantics registry
  entries.
  The report draws the graph, and `make status` names the frontier.
- **2.4 The support matrix.** Constructors by faces, each cell implemented, refused by name, caught
  by a catch-all, or absent. Example: the JSON encoder has no arm for `record` or eight other
  constructors.
- **2.5 Entry-point reachability.** Which checkers each public entry point reaches in its call
  graph. The report labels it syntactic reachability. It never claims that a path enforces a check
  (Codex).
- **2.6 Proofs to nowhere.** The library theorems that no claim, test or runtime definition reaches.
- **2.7 Briefs from the tree.** `make brief CLAIM=<id>` assembles the facts a brief now restates by
  hand.
- **2.8 Controls as data.** A fixture is recorded as an accepting or refusing control of a claim.
- **2.9 Obligation families.** One general goal per operation of a family, never a per-constructor
  transport.

### Lane 3 — documents short and true

- **3.1 Controlled English: landed** (`6437547c`, `1461f5bf`, `afcff997`, `0b790321`). The language
  seat wrote the writing rules, the dictionary, `make check-language` and the `AGENTS.md` rewrite.
- **3.2 Line citations: landed** (`16f96c6d`, `eb00182d`). `check-language.py --fix` drops a line
  number where the text names the cited declaration. It rewrote 453 citations in 13 documents,
  and the findings fell from 671 to 213. It lists the 194 it left with their reasons. History
  alone never writes a name: one citation in `docs/core/semantics.md` was wrong on the day it was
  written.
- **3.3 One list of required properties.** Generate `semantics.md`'s property lists from the
  registry. Open.
- **3.4 `STATE.md` as an entry point.** A proposal for the owner, open.
- **3.5 Status words in the registers.** A fixed first word per status cell. Open.
- **3.6 No counts in authored text: landed** for the two stale constructor counts (`87878f5d`).
- **3.7 The committed semantics report.** Decide whether the statements it shows in Lean's display
  stay committed.

### Lane 4 — proof automation for the planned work

- **4.1** New carriers declare their key traversals with `attribute [keys_norm]` (landed).
- **4.2** A value-operations proof bank, entered with P2, after `#auto_census`.
- **4.3** One shape for checker agreement, written once for formation and reused.
- **4.4** The trace, hop and queue macros stay unless the build profile shows a cost.

## 4. Order

1. **Landed today:** 1.1's speed, 1.2's rule, 1.3–1.6, 1.12, 3.1, 3.2, 3.6, the `TyView` template
   of 1.11, and the three repaired checks. 1.7 closed with no change, and 1.9 was measured and
   dropped. The module system (1.10) waits: the owner declined a pilot for now.
2. **Next:** the staged-generation decision with Codex and the owner, then its pilot. One measured
   build at 4 jobs on a quiet machine (1.2). The proofs of 1.11, each when its module is next
   touched.
3. **The visibility core:** 2.1–2.5, entering the plan's order and the vertical example as data.
4. **Documents:** the 194 citations 3.2 left, then 3.3–3.5 and 3.7.
5. **With the planned work:** 2.7 before the first brief, 2.8 with the vertical example, 2.9 with
   P4, and 2.6 as a cleanup pass.

## 5. Decisions for the owner

1. Staged generation: the questions of `staged-generation.md` §5.
2. Placement as data in the registry, which amends `AGENTS.md`'s placement rule (2.1).
3. The shape of `STATE.md` (3.4).
4. The status words of the registers (3.5).
5. What `generated/semantics.md` keeps (3.7).
6. Whether the language checker joins `make check` once the documents meet it.
7. An incremental axiom gate (1.8).
8. Lean's module system across the tree and the three packages it needs first (1.10): ruled
   2026-10-03, no pilot for now.

## Commands

- Generation timings: `python3 scripts/generate.py --only <group>`, timed per group.
- The critical path: `make build-profile`, from the log `make build` writes.
- The gate's scans: one `lake env lean --run` process that loads `Effect4.Laws` and times both
  routes.
- A fresh worktree: `git worktree add --detach <dir> HEAD`, then a timed `lake build`.
- Memory: `ps`, `vm_stat` and `sysctl vm.swapusage` during a bare `lake build`.
