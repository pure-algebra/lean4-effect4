# Tooling for the next wave: a measured map

Base: `394bc602`, revised at `43866b84`. Author: Claude, lead. Status: a proposal for the owner,
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
| a fresh worktree's first build | — | 318 s, 807 jobs | — |

Three more facts bound the next steps:

- **The critical path.** The last profiled rebuild (`make build-profile`) spent 190 s on its critical
  path, through the `Handles` chain. `Laws/Program/Handles/Hooks` took 84 s of it, under load.
- **Memory.** A bare `lake build` runs one compilation per core and swaps this 16 GB machine.
  `AGENTS.md` now bounds every Lake call at `LEAN_NUM_THREADS=3` (`6437547c`).
- **Disk.** 14 GB of 460 GB are free, and each worktree's `.lake` takes 3 GB.

## 3. The items, with their status

### Lane 1 — checks fast enough to run on every change

- **1.1 Derived generation: landed** (`089d9d97`, `2f8da42d`). One compiled executable runs every
  row in one process. Open: the bootstrap property, which `2f8da42d` broke for `TyEq`. The design
  note `staged-generation.md` (`a2d6146d`) measures the prerequisites and proposes a pilot.
- **1.2 The thread bound: landed** in `AGENTS.md` (`6437547c`). Open: choosing 3, 4 or 5 by one
  measured full build each, on a quiet machine.
- **1.3 Lake's artifact cache across worktrees: in measurement.** Lake 4.33 has a local
  content-addressed cache (`enableArtifactCache`, `LAKE_ARTIFACT_CACHE`). Cloning `.lake` does not
  work: Lake rebuilt every job.
- **1.4 Native tactic and gate code: landed** (`580261d6`, `834bf7bb`). Two small libraries are
  precompiled: `Effect4Tactics` and `ProofGraphNative`.
- **1.5 Compiled report drivers: landed** (`bca33ff6`): `semantics-report`, `semantics-controls`
  and `architecture-map`.
- **1.6 The build profile: landed** (`43866b84`): `make build-profile`, and one line in `make status`.
- **1.7 `Hooks` on the critical path: next.** Simp takes about 80% of its time. The module makes 124
  explicit `simp only` calls and 95 `sub_tac` calls. Profile it on a quiet machine before changing
  either.
- **1.8 An incremental axiom gate: for the owner.** The gate traverses every declaration at the end
  of the build. A check per module would run in parallel and only for rebuilt modules. It changes
  the trust architecture, so it needs a ruling.

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
- **3.2 Line citations.** The language checker's `line-cite` rule finds them. Open: a fix mode that
  drops the line number.
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

1. **Landed today:** 1.1's speed, 1.2's rule, 1.4–1.6, 3.1, 3.6, and the three repaired checks.
2. **Next:** the staged-generation decision with Codex and the owner, then its pilot; 1.7; 1.3's
   result.
3. **The visibility core:** 2.1–2.5, entering the plan's order and the vertical example as data.
4. **Documents:** 3.2–3.5 and 3.7.
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

## Commands

- Generation timings: `python3 scripts/generate.py --only <group>`, timed per group.
- The critical path: `make build-profile`, from the log `make build` writes.
- The gate's scans: one `lake env lean --run` process that loads `Effect4.Laws` and times both
  routes.
- A fresh worktree: `git worktree add --detach <dir> HEAD`, then a timed `lake build`.
- Memory: `ps`, `vm_stat` and `sysctl vm.swapusage` during a bare `lake build`.
