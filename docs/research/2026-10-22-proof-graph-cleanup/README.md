# The proof graph cleanup (2026-10-22)

The owner asked on 2026-10-22, by voice, for a cleanup of the proof graph: cut, streamline,
clarity and organization. This note holds the census (§1 to §5) and the proposal (§6). It also
holds the receipt of the cuts that need no ruling (§7), and the proposals that need one (§8).

Base: `afe86b819`. Every number below comes from a command quoted beside it. The scratch scripts
that join the outputs ran in the session's scratch folder and are not part of the tree.

## 1. The semantics registry

### 1.1 Counts

The semantics registry (`tools/ProofGraph/Registry.lean`) holds 10 concepts, 320 claims, 24 cuts and 14
requirements. `grep -c "pointer := \.<kind>"` counts the pointer kinds:

| Pointer | Claims |
| --- | --- |
| `.witness` | 314 |
| `.absent` | 4 |
| `.assumed` | 1 |
| `.refutedBy` | 1 |

The semantics report (`lake exe semantics-report`, run once in §4.4) derives the statuses: 309
proved, 2 modulo, 3 goal, 1 refuted, 4 absent, 1 assumed.

| Concept | Claims |
| --- | --- |
| `initial-algebras-folds` | 62 |
| `translation-simulation` | 59 |
| `exact-codecs` | 50 |
| `host-session-protocol` | 33 |
| `store-typing` | 31 |
| `reactive-scheduling` | 25 |
| `residual-program-typing` | 21 |
| `scope-lifetime-finalization` | 16 |
| `subtyping-algebra` | 13 |
| `context-requirements` | 10 |

| Role | Claims |
| --- | --- |
| `compatibility` | 152 |
| `preservation` | 64 |
| `simulation` | 32 |
| `inversion` | 21 |
| `fundamentalProperty` | 13 |
| `decidability` | 12 |
| `adequacy` | 8 |
| `monotonicity`, `progress` | 5 each |
| `canonicalForms`, `substitution`, `weakening` | 2 each |
| `transitivity`, `antisymmetry` | 1 each |

### 1.2 Stale pointers

No pointer is stale. The report checks every `.witness` against the loaded roots: each name is a
theorem, its statement is closed, and its axioms stay within `[propext, Quot.sound]`. The run
refused on two other things:

- rows 443, 444 and 445 of `docs/core/decisions.md` have three cells, not six
  (`decisions:575: malformed decision row 443`, and the same for 444 and 445);
- `Effect4.Laws.Program.Handler` is a default module of three concepts
  (`concept context-requirements: duplicate default module Effect4.Laws.Program.Handler`).

The register is the coordinator's file, so the first finding is a proposal (§8). The second is
repaired in §7.

### 1.3 Duplicates

Two theorems stand under more than one claim id:

| Theorem | Claim ids |
| --- | --- |
| `Effect4.Schema.decode_iff` | `decode-iff`, `record-codec-layout` |
| `Effect4.Program.Typed.m7_proved` | `m7-exits-typed`, `m7-stores-typed`, `m7-never-halts` |

No two claims point at two theorems with one statement. The report's statement texts are pairwise
distinct across the 314 witnesses.

### 1.4 Consumers and titles

Sixteen claim ids appear in no file but the registry (`grep` of each id over `src`, `docs/core`,
`tools` and `Test`, the registry excluded). They are the typed-state steps (`load-typed-checked`,
`step-wake-preserves`, …) and the Queue and Semaphore model claims. A claim needs no consumer of
its id: its consumer is its requirement. So this is a finding about prose, not a defect.

The titles are long and mix the statement with its history. The median title has 193
characters, the longest 2,683, and 103 exceed 300. Fifty titles name a slice, a seat, a wave or a
phase. Forty-eight titles have no verb: they name a topic ("Normalization idempotence") instead
of stating a fact.

### 1.5 The tools

| Module | Lines | What it is for | What runs it |
| --- | --- | --- | --- |
| `Audit` | 127 | the gate's environment scans | the axiom gate |
| `Axioms` | 145 | the memoized axiom walk | the gate, `#axiom_audit`, the report |
| `AxiomAudit` | 83 | `#axiom_audit` over named modules | seats; `Test/Audit/ProofGraph.lean` |
| `ClosureAudit` | 81 | `#closure_audit`, no table before a returned closure | `Test/Audit/ClosureAudit.lean` |
| `Declared` | 45 | declared facts from Rocq | `Effect4.Laws.Run.Tree` |
| `Goal`, `GoalTag` | 113 | planned goals, their tag and standing | the law graph, the gate |
| `Plan` | 206 | the planning graph, `#plan_status` | the report; `Test/Audit/ProofGraphPlan.lean` |
| `Population` | 52 | authored declarations as against auxiliaries | the plan, the censuses |
| `Proof` | 84 | checked theorem references | `Plan`, `Why`, `Search` |
| `Registry` | 1,706 | concepts, claims, cuts, requirements | the report, `Effect4.Laws.Author.Explain` |
| `Search` | 145 | speculative proof search, rolled back | `#auto_census`, `Effect4.Laws.Auto.Frames` |
| `Sketch` | 96 | `proof_sketch` | `Effect4.Laws.Auto.Obligations`; controls |
| `StatementCensus` | 277 | `#statement_census`, duplicate statements | only its controls |
| `Summary` | 153 | checks the walk's answers against a captured graph | `#axiom_audit checked` |
| `Why` | 286 | `#why`, `#goal_impact`, the gate's causes | the axiom gate; controls |

`grep` of each module's importers over `src`, `tools`, `Test` and `Conform` gives the last
column. One tool is run by nothing but its own controls: `#statement_census`. It is the tool that
answers §2.4, so §6 wires it into `make status` instead of deleting it.

## 2. The law graph

### 2.1 Size by folder

`find src/Effect4/Laws -name '*.lean' | wc -l` gives 880 modules, and `cat … | wc -l` 295,406
lines.

| Folder | Modules | Lines |
| --- | --- | --- |
| `Program` (17 subfolders and 217 files at its top) | 615 | 188,163 |
| `Machine` | 101 | 39,755 |
| `Codegen` | 22 | 21,904 |
| `Library` | 48 | 14,117 |
| `Run` | 11 | 6,180 |
| `Api` | 23 | 6,084 |
| `Step` | 17 | 5,583 |
| `Store` | 7 | 3,141 |
| `Schema` | 5 | 2,501 |
| `Auto` | 15 | 2,243 |
| `Tool` | 4 | 1,304 |
| `Slice` | 1 | 1,022 |
| `Author` | 1 | 424 |
| `Effects` | 2 | 371 |
| `Data` | 3 | 299 |
| `Contracts` | 2 | 141 |

The largest `Program` subfolders are `Typed` (65 modules, 47,066 lines) and `Guard` (42, 15,665).
Then come `AnswerSlots` (95, 10,697), `Agreement` (13, 10,054), `Typing` (20, 9,049) and
`ReleaseCustody` (42, 8,913).

### 2.2 What no claim reaches

A module is reached when a seed imports it, directly or through other law modules. A seed is a
claim's witness, a plan node, a placed theorem or a concept's default module. A module outside
the law graph (a battery, a tool, `Conform`) is a seed too. The seeds come from the report's JSON; the closure from a parse of
every `import` line.

| Measure | Modules | Lines |
| --- | --- | --- |
| law modules | 880 | 295,406 |
| reached | 684 | 271,918 |
| not reached | 196 | 23,488 |
| imported by the root alone (leaves) | 57 | 6,704 |

The 196 unreached modules have 37 tops: modules that no other unreached module imports. They fall
into four groups.

1. **The scenario residue: 145 modules, 16,797 lines.** Fourteen tops head docstrings that name
   their consumers: `QueueWorkers.jobs_step`, `Workers.Assertions.logs_step`, Atomic's
   `shop_stages`, Timeout's numeric history. No declaration of those names exists in the tree. Row
   410 (3) retired the scenario claim and proof modules on 2026-10-16 (275 modules,
   `git:f328e0dbcdab96e22e9492e8dfe5f6785371af32:Test/Dogfood/Proofs`). These law modules were
   their premises. They hold 94 of the 95 modules of `Program/AnswerSlots`, 14 of `ReleaseWriter`
   and 14 `Machine/AnswerFlow*` modules.
2. **A route to a live goal: 26 modules, 3,819 lines.** `Effect4.Laws.Program.FinalizerSourceHistory`
   names the planned goal `once_placed_outside_census` (R11) as its consumer. Ten of its modules
   are shared with group 1. It stays.
3. **Instruments: 4 modules, 735 lines.** `#bank_census`, `#exhaustive_gate`, `#traversal_census` and the
   clock statement list (`Effect4.Laws.Machine.Clock`) are commands, not theorems.
4. **Proved laws with no claim: 21 modules, 2,137 lines.** They hold the supervision table's agreement
   with the machine (`Effect4.Laws.Api.Supervision`, 803 lines) and the shared control algebra
   (`Effect4.Laws.Program.DenoteCtl`, row 344). They also hold the memo layer sharing
   (`LayerSharing`, DI-71), the fold connectors (`Folds/*`, `Typing.FoldAgreement`,
   `Store.Folds.Val`) and the Stream laws. Each states a real fact that a ruling or the traversal census names.

### 2.3 The largest modules

`wc -l`, then the concept placements that the report records for the module:

| Lines | Module | Concepts placed |
| --- | --- | --- |
| 8,233 | `Codegen/PrintTyped` | none placed; 9 tags at `exact-codecs` |
| 6,785 | `Machine/Handles` | none |
| 5,149 | `Program/Typed/Membership` | `store-typing` 252 |
| 3,997 | `Program/Guard/Core` | none |
| 3,591 | `Program/Typed/Denotation` | none placed; 3 tags at `residual-program-typing` |
| 3,560 | `Program/Typed/Commands/Bookkeeping` | none |
| 3,234 | `Program/Agreement/Machine` | `translation-simulation` 187 |
| 2,976 | `Run/CallTree` | none placed; 3 tags at `translation-simulation` |
| 2,718 | `Program/Typed/Commands/Evaluate` | none placed; 3 tags at `scope-lifetime-finalization` |
| 2,604 | `Codegen/ReadLeaf` | none |
| 2,490 | `Codegen/ReadPrint` | `exact-codecs` 123 |
| 2,443 | `Machine/MaskRuns` | `scope-lifetime-finalization` 116 |
| 2,393 | `Program/SourceTable` | none placed; 90 tags at `initial-algebras-folds` |
| 2,320 | `Machine/StoresLaws` | none |
| 2,163 | `Machine/Clauses` | none |
| 2,079 | `Program/Typed` | none |
| 2,073 | `Program/Agreement` | none |
| 2,007 | `Program/Typed/Commands/Clauses/Park` | none placed; 1 tag |
| 1,937 | `Program/Typed/Assembly` | `residual-program-typing` 114 |
| 1,907 | `Program/Typed/LayerArm` | none placed; 1 tag |

The report places 2,945 theorems (2,573 inherited from a default module, 372 tagged) in 69 law
modules. So 811 of the 880 law modules hold no placed theorem. A large module is one concept
where a placement exists. Where none exists, its concept is unread.

### 2.4 Duplicate statements

`#statement_census` over all 880 law modules (`lake env lean`, 40 s) reports 16,251 theorems
and 31 groups of two or more theorems with one normalized statement. Eleven groups touch a module
of §2.2's group 1 or 4. The other twenty are in reached modules, mostly a general lemma beside a
local copy (`Agreement.resolve_of_at` beside `SourceScope.resolve_at`).

`#auto_census … using aesop` over the five largest modules (one `lake env lean` run):

| Module | Theorems | Closed by `aesop` alone | Lines those proofs take |
| --- | --- | --- | --- |
| `Codegen/PrintTyped` | 346 | 35 | 161 |
| `Machine/Handles` | 393 | 40 | 99 |
| `Program/Typed/Membership` | 247 | 8 | 27 |
| `Program/Guard/Core` | 312 | 10 | 43 |
| `Program/Typed/Denotation` | 118 | 2 | 11 |

The run took 84 s. The search closes 95 of 1,416 theorems, whose proofs take 341 lines. The
rewrite would save under 341 lines: little, so §6 does not propose it.

### 2.5 Fallback tactics and long proofs

A scan of `src/` with comments stripped counts 57 `simp_all`, 153 `first |` and 119 `try`. The
law graph holds 47, 134 and 116 of them in 61 files. The core holds 10, 19 and 3 in 14 files.
The rule bans them in touched proofs only, so §7 removes none that it does not touch.

Thirty-one theorems span more than 200 lines, 8,752 lines together. The longest are
`evaluate_rel` (562, `Program/Simulation/Evaluate`), `localRun_compileB` (422,
`Program/Agreement/Loop`), `localRun_compile` (384, `Program/Agreement`) and `walk_rel` (358,
`Program/Simulation/Walk`).

### 2.6 Docstring citations of research notes

The law graph cites a bare `docs/research/…` path 160 times in 118 modules. Only 3 of the 98
cited notes are tracked. Eighty-six have a deletion in Git and can cite `git:<rev>:<path>`. Nine
were never tracked. `make check-sweep` repairs Markdown only, so no gate sees these.

## 3. The planned goals

`grep -rn "^proof_goal\|^declared"` finds seven goals and one declared fact. The plan's `next`
list (the report) has the same eight.

| Goal | Module | Concept, requirement | Claim | What rests on it |
| --- | --- | --- | --- | --- |
| `ofJson_image` | `Laws/Schema/DocumentJson` | `exact-codecs`, R3 | `document-json-complete` | `ofJson_complete` (modulo) |
| `once_placed_outside_census` | `Laws/Program/FinalizerRun` | `scope-lifetime-finalization`, R11 | `once-placed-finalizer` | `once_placed_pushes_once` (modulo) |
| `wrap_tensor` | `Laws/Program/Handler` | `host-session-protocol`, R6 | `imposed-wrap-tensor` | nothing |
| `explain_replays` | `Laws/Program/CheckAgreement` | `initial-algebras-folds`, R14 | `checker-explanation-replays` | nothing |
| `Doc.revert_program` | `Laws/Program/SourceDocument` | `initial-algebras-folds`, R14 | `source-document-revert` | nothing |
| `rows_divergence_adequate` | `Laws/Run/Outcome` | `host-session-protocol`, R12 | none | nothing |
| `ofProgram_eq_denoteRowsB` | `Laws/Run/Tree` | `translation-simulation`, R6 | none | nothing |
| `ofProgram_approx` (declared) | `Laws/Run/Tree` | `translation-simulation`, R12 | none | nothing |

No proved claim rests on a goal. Two theorems are proved modulo one. Three goals stand at a
requirement without a claim: their consumer is the requirement row.

The four `.absent` pointers wait on these:

| Claim | Waits on |
| --- | --- |
| `store-safety` | nothing: row 139 rules typing in place of progress |
| `scheduler-progress` | an operational progress statement (R12) |
| `fair-scheduling` | weak fairness (R12, row 86) |
| `document-json-fold-retraction` | a carrier below `Classical.choice`: `Tools.Document.Json.Document.ofJson_json` reaches it |

## 4. The gates

### 4.1 The axiom gate's exemptions

`Test/Audit/AxiomGate.lean` names 22 modules (`auditImplementationModules`), 42 exact
declarations (`choiceImplementationDeclarations`) and 6 private declarations. Each module entry
carries its reason in a comment: a command elaborator, a tactic, an aesop rule-set initializer,
or a deriving handler. Each exact entry is a `String` renderer or an `#explain` reader. The gate
refuses an entry that no longer reaches `Classical.choice`, so no entry is stale by
construction. This seat does not touch the gate.

### 4.2 The library-root and module-closure gates

Both live in `#effect4_axiom_gate`. The library-root gate asks that every `src/Effect4` source be
in the import closure of `Effect4` or `Effect4.Laws`, and that `Effect4` never reach the law
graph. The module-closure gate asks that every battery be reached from `Test.All`. Both read the
closure, never the root's list. `make build` runs `scripts/wire-roots.py`, which imports the
smallest set of orphan tops. So the root needs to name only the law graph's tops.

### 4.3 `make status`

`make status` (5 s) at the base, with the registry unchanged:

```text
claims    262 proved · 4 modulo · 18 goal · 3 absent · 1 refuted · 1 assumed  (generated/semantics.md)
goals     7 open planned goal(s) (proof_goal)
plan      requirements 14 open; 23 next goal(s): ofJson_image ofProgram_eq_denoteRowsB …
```

The claims and plan lines read the committed `generated/semantics.md`, last written 2026-10-20.
The measured truth is 320 claims (309 proved, 3 goal) and 8 next goals. The status is stale in
both lines.

### 4.4 `gen-semantics`

One run, after the two repairs of §1.2 made in a scratch copy:

| Step | Wall time |
| --- | --- |
| `lake build semantics-report` (roots restored from the cache) | 10.5 s |
| `lake exe semantics-report` | 30.3 s |
| of which the import and the claim checks (a run refused after the claims) | 13.3 s |
| of which the plan walk and the rendering | about 17 s |

The report writes 780 KB of Markdown and 3.9 MB of JSON. No step is slow. The pause of
2026-10-19 measured a cold build of the battery roots, which the cache now restores. The report
fails today only on the register's three malformed rows.

## 5. The root

`src/Effect4/Laws.lean` has 425 imports and 13 comment lines. Its folder sequence has 103 runs
(`awk` over the third name component, then `uniq`): Machine, Program, Api, Machine, Program, and so on.
The order is the order of landing. Its comments name slices and rows ("M3: carried driver
guards"). It is history, not structure.

Only 57 of the 425 are tops. The other 368 are imported by another law module, so the root's
line adds nothing to the build.

## 6. The proposal

In priority order, with what each buys.

1. **Repair the semantics registry** (§1.2, §1.3). Remove the handler module from two default lists. Merge
   `record-codec-layout` into `decode-iff` and the three M7 ids into `m7-proved`. Rewrite the 48
   verbless titles as statements, and drop slice names from titles. One theorem then has one claim.
2. **Cut the scenario residue** (§2.2 group 1): 145 modules, 16,797 lines, one commit. Their
   consumers retired with row 410 on 2026-10-16. Nothing outside the root imports them.
3. **Merge the duplicate theorems** of §2.4 that lie outside the cut, where a merge builds.
4. **Rewrite the root as tops by concept.** After the cut, the root names only the tops, under
   one section head per concept of `docs/core/semantics.md` and one for instruments. A reader
   finds the entry of a concept in one place. `wire-roots.py` keeps the form.
5. **Order the registry's claims by concept**, in the concepts' order.
6. **Regenerate `generated/semantics.md`** so `make status` reads the truth. The run takes 41 s.
7. **Wire `#statement_census` into `make status`** as a count of duplicate groups.

Proposals that need a ruling are in §8.

## 7. Receipt

**The one thing to know before merging.** The law graph loses 145 modules (16,797 lines): the
premises of the scenario proofs that row 410 retired. The register's rows 443 to 445 have three
cells instead of six, so `make gen-semantics` refuses until the coordinator repairs them. The
committed `generated/semantics.md` was written from a scratch copy with those three rows repaired.

Base `afe86b819`, head: the commit that adds this section. Branch
`claude/proof-graph-cleanup-183b12`.

### 7.1 The commits

| Commit | What | Files | Lines added, removed |
| --- | --- | --- | --- |
| `377093d2d` | this note, §1 to §6 | 1 | +359 |
| `d7322e5b1` | cut of the scenario residue: 145 modules | 146 | −16,827 |
| `b7ce5d824` | eleven duplicate theorems merged | 14 | +18, −102 |
| `cecaae3ee` | the semantics registry: one claim per theorem, 141 titles, concept order | 4 | +343, −373 |
| `174d6e617` | the root: 112 tops under the ten concepts | 1 | +116, −401 |
| `75d3cd5d8` | `make statement-census`, read by `make status` | 2 | +34, −1 |
| `968b22974` | `generated/semantics.md` regenerated | 1 | +1,201, −783 |

`git diff --shortstat afe86b819 HEAD -- src/Effect4/Laws src/Effect4/Laws.lean` gives 161
files, +135, −17,331. The law graph now has 735 modules and 278,525 lines (from 880 and
295,406).

The eleven merged copies, each with its uses rerouted:

| Removed | Kept |
| --- | --- |
| `Effect4.Program.effTy_scoped` | `Conform.Effect4.Typing.effTy_scoped` |
| `Effect4.Api.race?_updateRace_same` | `RunMachine.race?_updateRace_same`, its bank entry kept |
| `Sched.listRel_mem_left` | `Effect4.ListRel.mem_right` |
| `Guard.OuterDriver.timer_clockStep_keys` | `Guard.timer_clockStep_keys`, its bank entry kept |
| `Effect4.Run.modify_nextToken` | `Guard.nextToken_modify` |
| `CommandDebit.update_race_ids` | `RunMachine.race_ids_update` |
| `StackRegion.other_edit_stack`, `other_edits_stack` | `Moves.OtherEdit.stack`, `Moves.OtherEdits.stack` |
| `PlaceFunding.zero_allowance` | `PlaceFunding.commandAllowance_zero` |
| `OuterFrames.fields`, no use | `AdministrativeKept.same_fibers` |
| `Sequencing.acquired_registration`, no use | `Agreement.contAOf_acquired` |

One merge was not forced. `Check.ok_bind` is a `simp` lemma of `CheckAgreement`, and the census
counts no `simp` use, so its removal broke the build; it stays.

### 7.2 Commands and results

| Command | Result |
| --- | --- |
| `LEAN_NUM_THREADS=3 lake build Effect4Laws` after each Lean commit | 1,279 jobs, success |
| `python3 scripts/wire-roots.py --check` after the cut and the root | `PASS roots: every module is reached by its root` |
| `lake build ProofGraph.Registry semantics-report Effect4.Laws.Author.Explain Effect4.Laws.Schema.Codec` | 348 jobs, success |
| `lake exe semantics-report` (scratch register) | 317 claims: 306 proved, 2 modulo, 3 goal, 1 refuted, 4 absent, 1 assumed; 18 s |
| `make statement-census` | 15 groups in 15,338 theorems of 735 modules; 34 s |
| `make batteries-touched BASE=afe86b819` | 2 batteries (`Test.Program.StackRegion`, `Test.Codegen.DataCodec`), 1,048 jobs, success |
| `make status` | the lines below |

```text
claims    306 proved · 2 modulo · 3 goal · 4 absent · 1 refuted · 1 assumed  (generated/semantics.md)
goals     7 open planned goal(s) (proof_goal)
plan      requirements 14 open; 8 next goal(s): ofJson_image wrap_tensor ofProgram_eq_denoteRowsB …
duplicate 15 group(s) of theorems with one statement, in 15338 theorems of 735 law modules; fresh
```

### 7.3 The axiom output

`#axiom_audit` over the sixteen touched law modules (`lake env lean`, 8.5 s):

```text
#axiom_audit: 1301 declarations within [propext, Quot.sound], 0 of them modulo planned goals; 0 planned goals
```

The modules are `ScopedTyping`, `Api.Supervision`, `Table.Agreement`, `Guard.OuterDriver`,
`Run.Journal`, `ReleaseCustody.CommandRaceDebit`, `StackRegion`, `StackRegionCommands`,
`ReleaseCustody.NativeStacks`, `ReleaseCustody.CommandSequencing`, `PlaceFunding.Run`,
`PlaceFunding.Flow`, `ReleaseCustody.OuterFrames`, `ReleaseCustody.Sequencing`, `Schema.Codec` and
the root. The axiom gate's file is untouched, so the whole-tree gate did not run.

### 7.4 What stays open

- No behaviour gate runs: the change reaches no generated file, no TypeScript and no OCaml.
- Fifteen duplicate groups remain. Each is an instance beside a lemma, a structure's hook, a helper
  and its wrapper, or a copy that its users cannot replace.
- No `simp_all`, `first |` or `try` was in a touched proof, so the counts of §2.5 stand.
- The research-note citations of §2.6 are unrepaired (§8, item 6).
- The evidence is all local: Lean builds, the report and the census. Nothing is bounded or host-only.

## 8. Proposals that need a ruling

Each item changes meaning or moves more than one folder. None is landed.

1. **A concept for typed editing, and the handler's home.** `docs/core/semantics.md` §2.11 defines
   an eleventh concept, `typed-editing` (row 414 (5)). The semantics registry lacks it,
   since row 418 (6) paused the report. The report now runs in 18 s, so the pause has no cause. Proposal: add the
   concept and move the editing claims to it (`source-document-*`, `checker-*`,
   `sketch-*`). The handler claims stay under `host-session-protocol`. A handler is a service
   block read by a fold, and its laws are session and provision laws, so no new concept is needed.
2. **`generated/semantics.md` lives.** It is the input of `make status`, and a run costs 18 s
   after the roots build. Proposal: end the pause of rows 418 (6) and 2026-10-18. The coordinator
   repairs rows 443, 444 and 445 to six cells, and `make gen-semantics` runs at each landing that
   touches the registry or the law graph.
3. **Place or cut the 21 proved modules that no claim reaches** (§2.2, group 4, 2,137 lines).
   - Place with a claim: `Api.Supervision` (796 lines, the fork table agrees with the run's
     ledger), `Program.DenoteCtl` (285, row 344's control algebra), `Program.LayerSharing` (291,
     DI-71).
   - Keep as the traversal census's evidence: the fold connectors under `Program/Folds`,
     `Typing.FoldAgreement`, `Store.Folds.Val` and `Machine.Folds`.
   - Cut, 480 lines: `Typed.ForkSource` (75), `Store.CanonicalSpec` (29), `Api.Fuel` (28),
     `Library.Stream.{Ops,Steps,Typing}` (155), `Data.ListRelConnectors` (51),
     `Program.FiberSumConnect` (70), `Program.LedgerFinalizer` (72). Their docstrings name
     consumers that are gone or never landed.
4. **Split the two largest modules by namespace.** `Codegen/PrintTyped` (8,233 lines) holds four
   namespaces: `Templates`, `EraseTermTypes`, `PrintEliminators` and the printer's own lemmas.
   `Machine/Handles` (6,785 lines) holds the handle sets, the stores, the evaluator transport and
   the stores' instance. Each split moves declarations without a change of name or statement, by
   a new module beside the old with the callers moved. The cost is one rebuild of each module's
   dependents (9 and 413 modules, the batteries included).
5. **The Rocq lane.** Thirty-one proofs exceed 200 lines (§2.5), and every one is proved in Lean.
   Row 411 sends hard proofs to Rocq, but moving a proved Lean proof drops the kernel's check for
   a citation. Proposal: no proved theorem moves. The candidates are the open goals over Lean's
   code: `ofProgram_eq_denoteRowsB`, beside the declared `ofProgram_approx`, and
   `rows_divergence_adequate`.
6. **Repair the 157 research-note citations in law docstrings** (§2.6). Eighty-six notes have a
   last revision in Git, so the repair writes `git:<rev>:<path>`. Nine were never tracked, so their
   citations go. The edit is to docstrings only. Its cost is one rebuild of most of the law graph,
   so it belongs with the next change that rebuilds it, such as item 4.
7. **Defaults by folder.** The report places theorems in 69 of the 735 law modules. A concept's
   `defaultModules` names modules one by one. Proposal: let a default name a module prefix, so
   each folder of the law graph has one concept and the report places every theorem. This changes
   `tools/ProofGraph/Registry.lean` and `tools/Tools/Semantics.lean`, the second seat's file.

**Proposed decisions row 446**, the proof graph cleanup of 2026-10-22. Parts (1) to (4) are
landed, and parts (5) to (9) wait for the owner.

1. The scenario residue is cut: 145 modules, 16,797 lines. Row 410 (3) retired its consumers.
2. One claim stands per theorem, and a claim's title states its fact.
3. The law root names the tops under the concepts.
4. `make statement-census` measures duplicate statements, and `make status` reads it.
5. `gen-semantics` is unpaused (item 2), and rows 443 to 445 get their six cells.
6. `typed-editing` enters the semantics registry (item 1).
7. The 480 lines of item 3 are cut, and three modules gain a claim.
8. The module splits and the citation repair land together (items 4 and 6).
9. No proved Lean theorem moves to Rocq (item 5).

**Message to the coordinator.**

- The law graph lost 145 modules and 16,797 lines: the premises of row 410's retired scenarios.
- Repair rows 443 to 445 of the register (three cells each are missing), or `make gen-semantics` refuses.
- The registry has 317 claims, one per theorem, with titles that state their facts.
- `make status` reads the truth again: 306 proved, 3 goals, 15 duplicate groups.
- Owner rulings: unpause the report, a `typed-editing` concept, the 480-line cut, the module splits.
