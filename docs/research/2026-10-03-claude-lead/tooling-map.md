# Tooling for the next wave: a measured map

Base: `394bc602` on `refactor/phase1-phase3`. Author: Claude, lead. Status: a proposal for the owner.
It lands no planned work. Every number below has a command behind it; the commands are at the end.

**The one thing to know.** The tooling decides what gets proved and what gets skipped. This session
found its own example: the cleanup commit `0821bb2d` removed the axiom-print receipts from 25 generated
files but not from their generators. `make check-gen` would have refused it, but nobody ran it,
because the derived group alone took about five minutes. A slow check is a check that does not run.
So this map starts with speed, then visibility, then documents.

## 1. The planned work, read as tooling needs

The owner's plan (the 2026-10-03 Codex organisation, pasted in the session) has five obligations
and one vertical example. Its dependency order is: formation, parameter scope and profile rules →
shared type and value contracts → record/option/tuple/map operations and Schema descriptions with
exact JSON codecs → typed program authoring, native Schema agreement and actual host-session typing
→ lowering against named observations.

| Planned obligation | What it will produce | What it needs from the tooling |
| --- | --- | --- |
| P1 formation before information is discarded | a validity judgment under a declaration table and a parameter context, its checker, agreement, preservation by normalization and by permitted substitution | a place for the judgment and its agreement claim; a measured answer to "is the checker on the public admission path?" (§3, 2.5) |
| P2 shared value laws, then operations | field access, optional lookup, tuple indexing, map lookup over the existing membership rules, feeding term progress and handle provenance | per-constructor coverage of every face (§3, 2.4); `keys_norm` for new carriers (landed); a value-operations proof bank when the work starts |
| P3 Schema descriptions and codecs | complete Schema construction and codec exactness on stated domains | the same coverage table; codec claims labelled with their domain; controls |
| P4 actual session typing | load, parking, binding, cancellation, application and retirement keep the typed correspondence | one general goal per operation family, placed before work (§3, 2.9); reachability of the admission checks from the session path |
| P5 behavioural contracts for transformations | named input/output relations, assumptions, fragment, observation | claims with fragment and observation as fields, so a contract cannot be stated without them |
| PX the profile record (`id`, optional `nickname`) | construction, access, Schema publication, JSON round trip, host reply, and four control pairs | controls recorded as data and shown per claim (§3, 2.8) |

## 2. The state today, measured

| What | Measurement |
| --- | --- |
| `Laws/Machine/Handles` | 153 s → 13 s in a full build (`sub_tac` decided by reflection, `8bb23308`); 14.7 s of its time is the interpreter running the tactic |
| axiom gate | 57 s → 23 s (`14d46367`); `Test.All`, where it runs, is about 45 s at the end of the critical path |
| critical path to `Test.All` | about 286 s over 71 modules (estimate: 190 modules had no measured time); summed module time about 1,940 s |
| full build in a fresh worktree | 318 s wall for 807 jobs at moderate load; a copy-on-write clone of `.lake` is not reused (Lake rebuilt everything) |
| parallelism | `make` exports `LEAN_NUM_THREADS=3`, which bounds Lake to three compilations at once; a direct `lake build` runs eight (one per core). At about 1.4 GB per process plus the desktop, eight swap on this 16 GB machine: 6.4 of 7 GB swap in use, and one module took 263 s that takes 21 s unswapped |
| generation, Lean-only groups | variances 4 s, eff 25 s, wire 4 s, cas 3 s, ts 13 s, semantics 12 s; derived 301 s before today's fix (111 module recompilations) and 176–258 s after it with zero recompilations: 129 `lake` calls at 0.4 s each and 27 interpreted generator runs at 6–8 s each |
| disk | 14 GB free of 460 GB; every worktree's `.lake` is 3 GB |
| obligations | 0 open ledger goals in the library (the four `#proof_wanted` in `Test/Audit` test the ledger itself); 77 registry claims: 71 proved, 4 absent, 1 refuted, 1 assumed |
| instruments | 15 censuses and gates exist (`docs/research/2026-10-01-metaprogramming-audit/audit.md`, "Surface inventory"); all but the axiom gate print when run by hand, and none feeds a summary |
| documents | 215 stale references repaired today (`394bc602`); of 126 `name (file:line)` citations, 39 point at the wrong line and 11 name a declaration absent from the cited file; `STATE.md` is 799 lines, about 600 of them dated narrative, with two sections listing owner decisions |

## 3. The improvements

Each item names what it serves (P1–P5, PX, or the build) and when it is done.

### Lane 1 — checks fast enough to run on every change

- **1.1 Derived generation.** Landed today: the generators no longer emit the removed receipts, they
  write the committed layout, and the Makefile lists the shared producer inputs. Next: one `lake build`
  for every row's imports, then all rows in one generator process over the union of their imports
  (one environment load), falling back to the staged order only when an output changed; per-row
  markers, so a core edit re-runs only the rows that read it. *Done when* `make check-gen` with
  unchanged inputs takes seconds. Serves: the build, every P-item.
- **1.2 One parallelism setting for every entry point.** Direct `lake build` calls, which `AGENTS.md`
  prescribes for narrow builds, bypass `LEAN_NUM_THREADS=3` and swap. Put the setting where every
  shell sees it, then choose 3, 4 or 5 by one measured full build each with the build profile (1.6).
  *Done when* no direct build swaps and the chosen value is recorded with its measurement.
- **1.3 Lake's artifact cache across worktrees.** Lake 4.33 has a local, offline, content-addressed
  artifact cache (`enableArtifactCache` in the package configuration, or `LAKE_ARTIFACT_CACHE`), meant
  for "multiple copies of large projects". Every seat and every Codex worktree pays a full build and
  3 GB today. *Done when* a fresh worktree reaches a green `lake build` from the cache, measured.
- **1.4 Native tactic and gate code.** `precompileModules` on a small library holding `SubsetTac` and
  `ListSubset` (later the census commands); the gate's loops moved into the `ProofGraph` library,
  which imports only Lean and Batteries, and that library precompiled. *Done when* `Handles` and
  `Test.All` are re-measured with native code and the lakefile change is ruled.
- **1.5 Compiled report and generator drivers.** The drivers run interpreted under `lean --run`. Their
  compile-time imports are small (the semantics driver: Lean, `Batteries.Util.ProofWanted` and four
  tool modules; the environment is loaded at run time), so `lean_exe` targets are cheap. *Done when*
  the semantics report and one generator are timed both ways.
- **1.6 Build profile.** `make build-profile`: per-module times from Lake's output joined with the import
  graph give the critical path and the slowest modules, written under `.lake/gen`; `make status`
  shows the critical path in seconds. It steers module splits (the typed-state chain from `Membership`
  to `Commands.Clauses.Park`) and 1.2's choice.

### Lane 2 — obligations and progress visible from the tree

- **2.1 Placement as data.** The registry's claim gains the five parts of `AGENTS.md`'s placement rule as
  fields: concept (present), consumer, reach (judgment, observation, fragment, hypotheses), what it
  does not establish, and what it serves (R1–R13 or a workstream). The report prints them and refuses
  a claim that lacks one. Receipts and briefs then cite the claim id instead of restating placement.
  Serves every P-item.
- **2.2 Judgments as entries.** Each judgment of the vocabulary (well formed, canonical, membership,
  inhabitance, profile support, codec admission, reply admission) gets its proposition, its checker
  if one exists, and its agreement claims. The report shows which checkers have an agreement theorem
  and which connections between judgments are proved; an unproved connection shows as a gap, never as
  an implication. Serves P1, P3, P4.
- **2.3 Workstreams as data.** The plan's dependency order and the vertical example become registry
  entries with dependencies and claims. The report draws the graph with done/total per node, and
  `make status` prints the frontier: the workstreams whose dependencies are done. This replaces the
  hand-kept "next" lists, which drift. Serves the whole plan.
- **2.4 The support matrix.** Constructors by faces: membership clause, shape check, JSON encode and
  decode, Schema face, TypeScript rendering, OCaml mirror, subtyping, formation. Each cell is
  implemented, refused by name, caught by a catch-all, or absent, computed from the face tables and
  from the matchers (the exhaustiveness inventory already reads them). Today, for example, the JSON
  encoder has no arm for `record`, `map`, `tuple`, `app`, `null`, `undefined`, `number`, `bytes` or `int`,
  which fall to its catch-all, and the Schema face refuses eight constructors by name. Serves P2, P3,
  profile support and lowering.
- **2.5 Entry-point reachability.** Which checkers each public entry point reaches in its call graph
  (`Author.build`, `Built.rebuild`, the admission functions, the session's preflight and acceptance,
  `Schema.decode`, `Run`), labelled as syntactic reachability. The plan's "the formation helpers are not
  yet connected to public admission" becomes a cell that flips when a call lands. A reachable checker
  does not establish that every successful public path enforces it: that stronger admission-path claim
  stays a theorem or a pair of controls of P1 and P4 (Codex). Serves P1, P4.
- **2.6 Proofs to nowhere.** The library theorems that no claim, no test and no runtime definition
  reaches, listed by module. Each is deleted or earns a claim. Serves focus and build time.
- **2.7 Briefs from the tree.** `make brief CLAIM=<id>`: the placement, the printed statement, the
  definitions it mentions with their locations, existing theorems about them, the decisions rows and
  counterexamples of its concept, its controls. The coordinator writes only the intent.
- **2.8 Controls as data.** A command records a fixture as an accepting or refusing control of a claim;
  the report lists the controls per claim. The vertical example's four pairs (duplicate against
  reordered fields; an absent nickname against a present invalid one; strict decoding against an
  adapter that drops extra fields; a correctly typed reply against one naming the wrong waiting call)
  become its measured checklist. Serves PX.
- **2.9 Obligation families.** For an invariant over an operation family, one general goal per
  operation, placed with its fields before work starts, never a per-constructor transport (the owner's
  "general over casework"). First use: P4's six session operations.

### Lane 3 — documents short and true

- **3.1 Controlled English.** In flight on its own seat: writing rules adapted from ASD-STE100, one
  dictionary with one meaning per term, a linter that reads the dictionary from the specification, and
  `AGENTS.md` rewritten to the rules.
- **3.2 Citation lines.** `check-docs` checks `name (file:line)`: the name is declared in that file, at
  that line. It reports the current line, and a fix mode rewrites it or drops the line number.
- **3.3 One list of required properties.** The "Required Properties and Obligations" lists of
  `docs/core/semantics.md` repeat the registry's claims by hand and hold 32 of the stale citations.
  Generate them from the registry, and keep the literature and adaptation prose written by hand.
- **3.4 `STATE.md` as an entry point.** A proposal for the owner: what this is; `make status` for what is
  true; the authority map in `AGENTS.md` rather than a second documents table; "next" from 2.3; the owner's
  decisions generated from the open owner rows of `docs/core/decisions.md`; the dated narrative left to
  git history.
- **3.5 Status words in the registers.** A decisions or design-issues row's status opens with one word
  from a fixed set (open, ruled, landed, superseded, closed); a check refuses others. Today 29
  decisions rows and 4 design-issue rows have none, so `make status` counts them as "other".
- **3.6 No counts in authored text.** Counts belong to tools. Today's examples, both fixed: the registry
  and `system-map.md` said `Ty` has 20 constructors; it has 28.
- **3.7 The committed semantics report.** `generated/semantics.md` is 1,254 lines, most of them printed
  statements. Decide whether those stay committed (statement changes visible in review) or move under
  `.lake/gen` (the committed file keeps the tables).

### Lane 4 — proof automation for the planned work

- **4.1** New carriers declare their key traversals with `attribute [keys_norm]`; `sub_tac` and
  `mem_tac` then decide their inclusions (landed).
- **4.2** A value-operations proof bank, entered with P2, after `#auto_census` shows what the search
  already closes.
- **4.3** One shape for checker agreement (a Boolean checker, its judgment, both directions), written
  once for formation and reused for profile support and codec admission.
- **4.4** The trace, hop and queue macro families have at most 19 call sites each and are off the
  critical path; replace them only if the build profile shows a cost.

## 4. Order

1. **Now, small.** 1.1's first part, the status fixes and Codex's three findings (landed with this
  note); 1.2; 3.2; 3.5; 3.6.
2. **The visibility core.** 2.1–2.5, entering the plan's order and the vertical example as data.
3. **Speed, measured first.** 1.3–1.6: each experiment, then its landing.
4. **Documents.** Merge 3.1; 3.3; the 3.4 proposal; 3.7.
5. **With the planned work.** 2.7 before the first brief; 2.8 with the vertical example; 2.9 with P4;
  2.6 as a cleanup pass.

## 5. Decisions for the owner

1. The lakefile: the artifact cache, a precompiled tactic library, compiled driver targets (after 1.3–1.5).
2. Placement as data in the registry, which amends `AGENTS.md`'s placement rule (2.1).
3. The shape of `STATE.md` (3.4).
4. The status words of the registers (3.5).
5. What `generated/semantics.md` keeps (3.7).
6. Whether the language linter joins `make check` once the documents meet it (3.1).

## 6. What this does not do

It changes no judgment, theorem statement or runtime definition, and it starts none of P1–P5. The
numbers in §2 were taken under varying machine load; each experiment in Lane 1 is re-measured before
its landing.

## Commands

- Generation timings: `python3 scripts/generate.py --only <group>` per group, wall time by `date +%s`.
- Lake overhead: `/usr/bin/time -p lake build Tools.GeneratedStamp` (no-op).
- Fresh worktree: `git worktree add --detach <dir> HEAD`, `cp -c -R .lake <dir>/.lake`, `/usr/bin/time -p lake build`.
- Critical path: per-module times from `lake build` logs joined with `import` lines (one-off script).
- Citations: a one-off script matching `` `name` (`path:line`) `` against declarations in `path`.
- Memory: `ps`, `vm_stat`, `sysctl vm.swapusage` during a direct `lake build`.
