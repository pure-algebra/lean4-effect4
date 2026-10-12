# Backlog queue: clean fixes and small probes (2026-10-12)

A read-only scout of the backlog at `68856e778` on `refactor/phase1-phase3`. It ranks items that
are clean to fix now, or that a small read-only probe can decide. The owner's two tests
(2026-10-12) order it: does the item change an outcome of a real run, and does the proof graph
need it? Hygiene comes after both.

Out of scope: the typed-context migration (decisions row 349) and the release's context merge.
Also out: the retired restore slot (`2026-10-12-restore-slot-scout.md`, in the land-context
worktree), the proof-style ratchet (`Test/Audit/ProofStyle.lean`) and the corpus disagreements.

## Know this first

- **`make status` misreads the semantics report.** It prints `claims none`, `plan no rows` and
  `2 open planned goal(s)`. The report's format v6 (decisions row 353, `707b9a01e`) wraps claim
  and requirement names in code spans and drops the bold from `Next goals`. The three parsers of
  `scripts/status.py` match nothing. `docs/STATE.md` sends every reader to `make status` for
  counts, so the plan is invisible there. The fix is Python only (item A1).
- **The disk is at 97%.** `df` reports 14 GiB free. `make status` reports 11.2 GB of Lake's cache
  used by no build directory. Four worktrees of merged branches hold about 8 GB more (item A5).
  A narrow build during the context merge can fail on space.
- **One planned goal is cheap, and only by restatement.** `once_placed_pushes_once` has a general
  law beside it, `SourceScope.Opportunities.history_budget`, whose premises are a source census.
  The Atomic scenario already proves its own bound that way (item B2).
- **No marker comment names a fix.** `grep` finds no `TODO` or `FIXME` in `src/`, `scripts/`,
  `tools/`, `harness/`, `ocaml/`, `ts/` or `Test/`. The hits are `mktemp` templates.
- **The document gates pass.** `python3 -I scripts/check-docs.py` resolves every reference in 84
  documents. `check-language`'s self-test and its strict run on the specification and `AGENTS.md`
  pass.

## Queue A: fix now, with no Lean build

| # | Item | Why it matters | Files | Lean build | Size | Ruling |
| --- | --- | --- | --- | --- | --- | --- |
| A1 | Repair the three report parsers of `scripts/status.py` for format v6. `claims()` wants 6 cells and a bare name; the table has 5 cells and a code span. `plan_rows()` wants a bare `R\d+`. `plan_next()` wants `**Next goals**`. Also let `planned_goals()` match an attribute on the goal's own line (`@[semantics …] proof_goal G`), which AGENTS.md shows as the form. Make an empty parse a `StatusError`, so the next format change fails loudly. The same break was found and repaired on 2026-10-05 (`docs/research/2026-10-05-claude-lead/landing-review.md`), so the refusal is the real fix. | Proof graph: the measured view of claims, requirement rows and next goals. A corrected parse in this probe reads 207 proved, 1 modulo, 1 wanted, 1 assumed, 1 refuted and 3 absent claims, 14 open requirements, and 10 next goals. These are a probe's numbers, not the tool's. | `scripts/status.py` | none | about 25 lines | none |
| A2 | Refresh the status cells of `docs/core/system-map.md` §8 from the plan rows of `generated/semantics.md`. This is `docs/STATE.md`'s next item 2. R10 still reads "undelivered: no form has a behaviour law". The plan lists twenty form typing lemmas (`andThenEffect_typed` and others) and the Latch, Pool and PubSub step agreement laws as proved. R11 reads "the whole run open", while `StackLedger.funded_reachable` and `FinalizerRun.starts_le_pushes` are proved. R12, R13 and R14 lag the same way. R4 should cite row 342 for `Ref.make`. The header still names `0c534f06`. | Proof graph: §8 says it owns status, and it states that the derived status wins where they differ. Readers act on the prose. | `docs/core/system-map.md` | none | medium: six cells | none |
| A3 | Close the register lag. `docs/DESIGN-ISSUES.md` DI-95 still reads `open`. `02f72b054` (2026-10-03) made `Codec.isSupported` the field of the generated `wireAlgebra`, with `.refused` arms at `refOf`, `deferredOf`, `var` and `unknown`, and decisions row 129 already says "DI-95 landed". The row's unescaped `|` inside code spans also breaks the table: `status.py` counts DI-95 as `other`. In `docs/STATE.md`, "The type interface" still says `mul` answers outside the profile; `E4-RUN-CE-047` is REPAIRED (2026-10-11). | Hygiene: two authority documents state a fault that the tree no longer has. | `docs/DESIGN-ISSUES.md`, `docs/STATE.md` | none | two sentences and one row | none |
| A4 | Rewrite the line citations of the authority documents by hand. `check-language` counts 202 line-cite findings. A dry run of `line_cites.Fixer` in this probe rewrites none: each needs a person to confirm the declaration. Start with the citations whose file moved: `Ty.sub_le_subN` and `CodeInert` (`Test/Counterexamples/REGISTER.md`), `normalizeFVarIds` (`ocaml/gen/NOTES.md`) and `explainEff` (`docs/core/traversal-census.md`, now folded into `Program.check`). | Hygiene: a pointer that names a wrong file misleads a seat. | `docs/core/decisions.md` (69, the coordinator's), `docs/DESIGN-BASIS.md` (40), `docs/design/string-diagrams-notes.md` (30), `docs/design/design-language.md` (26), and seven more | none | medium, mechanical | decisions.md is the coordinator's |
| A5 | Free disk space. Run `lake cache clean` when no `lake` runs anywhere; it rebuilds nothing. Remove the worktrees of merged branches after `git status --ignored` in each: `codex/last-planned-goals` (3.1 GB, 5 uncommitted paths), `codex/machine-fields` (2.3 GB), `claude/brave-ishizaka-7a3804` and `claude/stoic-brahmagupta-c7361f` (1.5 GB each). `du` counts hard-linked cache outputs, so the space freed may be less. | Runtime of the work: a build that fails on space stops a landing. | none tracked | none | minutes | owner or coordinator: two are Codex's worktrees |
| A6 | Exempt `generated/` from the language report, or fix its prose at the source. `generated/semantics.md` carries 221 findings, and no hand edit can fix a generated file. | Hygiene: the report's second-largest entry is noise. | `scripts/lib/doc_refs.py` (exempt), or `tools/Tools/SemanticsDisplay.lean` and the registry texts (fix) | none to exempt; tools build to fix | small to exempt | none |

## Queue B: Lean items

| # | Item | Why it matters | Files | Lean build | Size | Ruling |
| --- | --- | --- | --- | --- | --- | --- |
| B1 | Move the nine legacy host fixtures of the truth lane to the keyed lane (decisions row 343 (8), option (b), ruled). Today `signedHostPark` signs them as `HC-2`: their exits agree, and each host call parks where rc.112 answers inline. **Probe first, read-only:** the keyed lane binds `Host` and `Kv` only (`harness/truth/session/keyed-bindings.ts`). `pKv` is close to the lane's existing `kv` fixture. The five SQLite fixtures need a SQLite binding. `pAcquireHandle`, `pJoinedFirstNumber` and `pJoinedFirstString` need a reading of their tapes. | Runtime outcome: nine signed divergences become compared runs. | `harness/truth/session/Keyed.lean`, `harness/truth/session/keyed-bindings.ts`, `harness/truth/run-truth.ts` (`HOST_PARK_SIGNED`), `scripts/check-truth.py` (the count of nine) | `Keyed.lean` is elaborated by `check-host-protocol`; no library module rebuilds | small for `pKv`; medium for the SQLite five | none for (b) |
| B2 | Restate `FinalizerRun.once_placed_pushes_once` over the source census, then prove it. The goal takes `OncePlaced` and `Guard.Reachable` only. `history_budget` (`src/Effect4/Laws/Program/SourceOpportunityHistory.lean`) bounds the same count from `Fragment`, `ClearFinalizers`, `ClearLoops`, `SequentialSource`, `RaceFreeSource` and `Run.HistoryOf`. `exit_registrations_le_recorded` reads the trace count. `Test/Dogfood/Scenario/Atomic/Cleanup.lean` (`cleaned`) shows the selector rewrite. No import cycle: `SourceOpportunityHistory`'s closure does not reach `FinalizerRun`. **Probe first:** does `OncePlaced` alone imply the census premises, or is the stated goal stronger than any route? `FinalizerRun`'s header and the goal's docstring name the Atomic cleanup claim as its consumer. Atomic now reads `SourceOpportunity.atomic_registrations_once` instead, and that file's header names the goal as its consumer. Correct the three with the restatement. | Proof graph: one of the two library goals, and the claim `once-placed-finalizer` (R11, `wanted`). No proof downstream waits on it now. | `src/Effect4/Laws/Program/FinalizerRun.lean`, `Test/Dogfood/Scenario/SourceOpportunity.lean` (header) | `FinalizerRun`, `LedgerFinalizer`, the `Effect4.Laws` root, `Atomic.Cleanup`, `Atomic.WriterPhase` | small: about 30 lines | coordinator: the restatement changes a registry claim's carrier (built program and history in place of program and reachability) |
| B3 | Give `tools/Tools/Graph` its own area at height 0 (decisions row 345 (2)(b), ruled). `areaOf` takes the longest prefix, so the folder now falls under `tools/Tools` at height 2. `tools/ProofGraph/Summary.lean` and `tools/ProofGraph/Why.lean` (height 0) import it, which `allowed` reads as an upward import. Declare it with `detail := false`: a detail area rolls its edges up to `tools/Tools`. The folder's only outside import is `Lean.Elab.Tactic.Omega`. | Hygiene: two false findings on the architecture map. | `tools/Tools/ArchitectureRoles.lean` | `Tools.ArchitectureRoles`, `Tools.Architecture`, `Tools.Exposure`, `Test.Audit.Exposure` | one table row | none |
| B4 | Probe the seven harness packets that no `make` target runs: `ref-catalogue`, `pull-protocol`, `codegen-bindings`, `partitioned-bookkeeping`, `module-catalogue`, `authoring-branches` and `channel-transforms`. Each `run.py` elaborates a `Produce.lean` or `Emit.lean` and compares its emitted TypeScript with Effect 4.0.1 under tsgo 7. `20f6293f1` shows the risk: `harness/truth/Truth.lean` stopped compiling after an appended constructor, and only a sweep found it. Run each once with `--skip-build` at the next sweep. | Runtime outcome: finite comparisons with the release, now unobserved. | `harness/*/run.py`, `harness/*/Produce.lean` | `lake env lean` per packet, no library rebuild | one sweep run | owner: keep as receipts, wire, or retire. `AGENTS.md` owes no run beyond `make check-full`'s targets, so wiring adds a gate |
| B5 | Read the seven `simp only [evaluatePrim, current]` arms of `Test/Dogfood/Proofs/HostTimeoutLocalSteps.lean` from the clause bank (`src/Effect4/Laws/Machine/Clauses.lean`). The audit of 2026-10-11 flags it as a small regression. | Proof graph: consolidation of the Timeout chain. | `Test/Dogfood/Proofs/HostTimeoutLocalSteps.lean` | that file and its Timeout dependents | small | none; inside the goals lane |
| B6 | Cut the machine's dead data (R1, R3, R7 of `docs/research/2026-10-11-machine-models/README.md`). No machine module outside `Laws` builds `Resume.continueWith`; it has one match arm in `Fibers.lean`. The README lists the rest by `grep`: `Dispatcher.armed`, `Pending.waitingOn`, five `RaceAllState` fields, `Race.settled`, the budget copy and the scheduled wake branch. Each cut needs its consumers checked. | Proof graph: fewer clauses in `PendingOk` and its relatives. No run changes. | `src/Effect4/Machine/Fibers.lean` and the laws that case on them | the whole tree, the OCaml route and its generated files | medium | none; do it after the context merge, not beside it |
| B7 | Decisions row 344's C4b: move the callers of the six call-tree meanings to `denoteCtl`, then delete the copies. | Proof graph: one meaning per question. | `src/Effect4/Laws/Program/DenoteCtl.lean` and its callers | a large part of `Effect4.Laws` | medium | none |
| B8 | Decisions row 345 (2)(d): the generator emits the children-induction lemma for nested families and retires two hand lemmas. | Proof graph: one generated law in place of two hand ones. | `tools/Effect4Gen/`, the generated families | generator, regeneration and their dependents | medium | none (ruled) |

## The open planned goals

`grep -rn proof_goal src/Effect4/Laws` finds two library goals. The plan's ten next goals add the
eight application goals under `Test/Dogfood/Scenario/`. `Gate.lean`'s `pending` and `hidden` and
the `Test/Audit/` goals are controls of the instrument.

| Goal | Path | Placement | Consumer, by its docstring | Cheap? |
| --- | --- | --- | --- | --- |
| `once_placed_pushes_once` | `src/Effect4/Laws/Program/FinalizerRun.lean` | scope-lifetime-finalization, R11 | the Atomic cleanup-log claim; it now bypasses the goal | yes, by restatement (B2) |
| `request_leads` | `src/Effect4/Laws/Run/CallTree.lean` | translation-simulation, R6 | `request_in_tree`, then `Routing.unauthorized_calls_nothing` | no: an operational prefix over every budget cut and control decision |
| `log_debits` | `Test/Dogfood/Scenario/Atomic/Cleanup.lean` | scope-lifetime-finalization, R11 | `cleaned` | no: the goals lane states it as a ledger instance (`CODEX-PROMPT.md`, item 3) |
| `logs_step` | `Test/Dogfood/Scenario/Workers/Assertions.lean` | scope-lifetime-finalization, R11 | `step`, then `history` | no: as `log_debits` |
| `logs_history` | `Test/Dogfood/Scenario/QueueWorkers/Assertions.lean` | scope-lifetime-finalization, R11 | `cleanup_step`, then `releases_once` | no: as `log_debits` |
| `jobs_step` | `Test/Dogfood/Scenario/QueueWorkers/Assertions.lean` | translation-simulation, R10 | `jobs_boundary` | no: needs the queue cell's writer census |
| `rest_step` | `Test/Dogfood/Scenario/QueueWorkers/Assertions.lean` | reactive-scheduling, R12 | `rest_script` | no: needs delivery custody and wake-to-wait correspondence |
| `shop_stages` | `Test/Dogfood/Scenario/Atomic/Store.lean` | store-typing, R4 | `Atomic.counted`, `Atomic.committed` | no: per-fiber positions through the residual law |
| `retries_declared` | `Test/Dogfood/Scenario/Timeout.lean` | translation-simulation, R10 | the timeout scenario | no: the Timeout chain (row 351) |
| `cleanup_keeps` | `Test/Dogfood/Scenario/Timeout.lean` | scope-lifetime-finalization, R11 | the timeout scenario | no: the Timeout chain |

## The language report, by document

`python3 scripts/check-language.py` reports 1916 findings in 69 of 84 documents: length 1442,
qualifier 175, avoid 95, filler 2, line-cite 202, anchor 0. The documents with most findings:

| Document | Total | Length | Qualifier | Avoid | Line-cite |
| --- | --- | --- | --- | --- | --- |
| `docs/DESIGN-BASIS.md` | 312 | 240 | 24 | 8 | 40 |
| `generated/semantics.md` | 221 | 198 | 15 | 8 | 0 |
| `docs/core/decisions.md` | 105 | 13 | 1 | 22 | 69 |
| `docs/core/traversal-census.md` | 96 | 92 | 1 | 1 | 2 |
| `docs/core/semantics.md` | 90 | 61 | 13 | 7 | 9 |
| `docs/design/design-language.md` | 88 | 57 | 5 | 0 | 26 |
| `Test/contracts/schema-payload.contract.md` | 78 | 66 | 9 | 3 | 0 |
| `docs/design/string-diagrams-notes.md` | 67 | 36 | 1 | 0 | 30 |
| `Test/contracts/faces.contract.md` | 56 | 49 | 7 | 0 | 0 |
| `docs/core/system-map.md` | 40 | 33 | 2 | 5 | 0 |
| `docs/DESIGN-ISSUES.md` | 39 | 21 | 2 | 7 | 9 |

The Makefile reports these and refuses none until a later slice normalises them. Length findings
are prose rewrites with no outcome on a run, so they rank last.

## Decisions and design issues

`make status` counts 50 open decisions rows and 6 open design issues. Most open rows date from
September, and several wait on a program that needs them (rows 1, 118 and 124).
Of the October rows, three name work that is not started: row 344's C4b (B7), row 346's repair A
and row 348. Repair A changes the checker's order, on which M7 stands, and row 348 waits on the
reachability law. Neither is a small fix. Row 353 leaves two items: `html-h7` merges into
lean4-whatwg's `main`, which is the owner's push, and the architecture map's hand-written HTML
becomes a document. The open design issues DI-01, DI-04, DI-05, DI-06, DI-16 and DI-46 are
representation questions with no run that depends on them now.

## Ranked: the top eight

1. A1, `scripts/status.py`: the plan view, no Lean, about 25 lines.
2. B1, the nine host fixtures to the keyed lane: a runtime outcome; probe `pKv` first.
3. B2, `once_placed_pushes_once` by `history_budget`: one library goal, with a coordinator ruling.
4. A2, `docs/core/system-map.md` §8 from the plan rows: STATE's next item 2.
5. A5, disk space: 14 GiB free; a cache clean and four merged worktrees.
6. B4, the seven unwired harness packets: one sweep run, then keep, wire or retire.
7. B3, `tools/Tools/Graph` at height 0: one row, four tool modules.
8. A3, DI-95 landed and STATE's `E4-RUN-CE-047` sentence: two sentences and one row.

## How this was measured

Every command ran read-only at `68856e778`. None built Lean.

| Command | Result |
| --- | --- |
| `python3 scripts/status.py --why` | runs no Lean (`make -pn help` only); `claims none`, `plan no rows`, `goals 2`; 50 open decisions, 6 open issues; 457 Lean sources changed since the last battery build; the generated groups stale on `tools/Effect4Gen/manifest.json`, with no committed generated file differing |
| `python3 -I scripts/check-docs.py` | PASS, 84 documents |
| `python3 scripts/check-language.py` | 1916 findings, as above |
| `python3 scripts/check-language.py --self-test` | PASS, 48 of 48 controls |
| `python3 scripts/check-language.py --strict docs/core/controlled-english.md AGENTS.md` | PASS |
| a dry run of `line_cites.Fixer.fix` over eleven documents, writing nothing | 0 rewritten |
| `grep` for `TODO` and `FIXME` over the tracked sources | no marker that names a fix |
| `grep -rn proof_goal src/` | two goals |
| `df -h` and `du -sh` on four worktrees | 14 GiB free; 3.1, 2.3, 1.5 and 1.5 GB |
| `git merge-base --is-ancestor` on each worktree's branch | four merged into HEAD |

The corrected parse in A1 and the fixer's dry run are probes of this note, not the tools'
reports. No item here is evidence of a theorem. The planned goals' cheapness is read from their
docstrings and their neighbours' proofs, not from a build.
