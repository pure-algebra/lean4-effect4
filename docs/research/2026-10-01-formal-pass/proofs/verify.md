# Verify: seat PROOFS of the 2026-10-01 formal pass

Adversarial verifier of `note.md` in this folder. Tree: `refactor/phase1-phase3` at `ea5b28b5`
(`src/` and `Test/` unchanged since `d20f3292`; the oleans built at 03:51–03:59 were used as they
are). No tracked file was edited; no `lake build`, generator, `git add` or commit was run; the
slice-6 worktree was not touched. Every probe compiled alone through the one-compiler lock
(`serial.sh lake env lean -M6144 -DwarningAsError=true <probe>`), through
`verify-probes/verify-rerun.sh`, which writes the probe's sha256, the head, the exit code, the
wall time and the peak memory into `verify-logs/verify-rerun-<name>.log`.

Evidence words as the brief defines them: **proved** (a kernel theorem compiled here, axioms
printed at `[propext, Quot.sound]` or less), **tested** (a finite check run here), **reading**
(code or notes read, not run), **assumed**. Literature: **read** (a named note or this verifier
read it), **by name**, **assumed**. Short paths are under `src/Effect4/`.

## The one thing first

**G1's diagnosis is right, and the ledger is in worse shape than the seat says. But the repair it
proposes cannot be instantiated in the tree's lift. Use a split keyed on `running` instead, and
send it to Codex before H1's statements land.**

- *Right.* Probe A re-runs (20 theorems at `[propext, Quot.sound]`). At budget 6 a checked,
  host-free run reaches a cut machine on which no world types the root's code slot, and through
  `replayEval_lift` the ledger's `typedState_load` and `decision_preserves` are jointly false there.
- *Worse.* M5 alone is false at HEAD. It fails for the typed corpus's own `awaitFiber.value`
  entry (`Test/Program/TypedCorpus.lean:62`). This is proved on the denotation itself
  (`verify-probes/VerifyAwaitLoad.lean`, `typedState_load_false`), so the seat's reading-level
  step is now proved. Seat TYPES reports M5 false by a second route (`types/note.md`, TY-01;
  reading, not re-run here).
- *Wrong repair.* The seat proposes a `J` with no code typing and an `I` that holds row 133's
  queue-relative clause, and keeps `stepDecisionState_lift` unchanged. That cannot be
  instantiated. `DecisionLift.evaluate` (`Laws/Machine/Lift.lean:316`) must derive `I` at the fresh
  queue `[evaluate id, drainDue]` from `J` alone, and at the window machine no `finish` is queued.
  This is proved for every `J` that holds at the cut and every `I` with the seat's code clause
  (`VerifySplit.seat_split_not_decisionLift`).
- *The repair that works.* The window fiber is `running` (proved). No settled replay result in the
  typed corpus has a running fiber (tested: 0 of 13,078 results, and 0 of 51,064 over the
  interleaving pairs). So the tree's `DecisionLift` can stay unchanged:
  - `J` types the code of every fiber that is neither exited nor running;
  - `I` types each running fiber by the queued command that continues it: `loop`/`deliver` by
    `SavedOk`, `finish` by row 133, and the race and interrupt commands by their installed code.
- *Timing.* Addendum 6, item H1.1 has Codex restating the code clause "only while no `finish`
  for it is queued". On a machine-only `TypedState`, read at the empty queue, that clause is
  refuted by probe A at budget 6.

## Verdicts

| id | verdict | evidence |
| --- | --- | --- |
| ACC-1 | partly | Re-read every cited line (reading). The labelled-transition frame, the decision layer, the residue dropped at a cut, the host as oracle, and M5/M6/M7 as initiation, consecution and transfer along `run_eq_ref` are all accurate. Three errors. (1) "The typed state is a Kripke predicate" is false: `WorldValid` requires exact support (`Typed/Validity.lean:19-34`), so the typed state is not upward closed (proved, `VerifySplit.worldValid_not_upward_closed`). Only the value, code and Kripke-amended stack judgments are monotone, as in TAPL, where store typing needs `dom Σ = dom μ` (by name). (2) M5's "one real lemma", denotation typing, is false at HEAD (proved, `VerifyAwaitLoad`). (3) The statements omit Σ_app and `w.serviceTy`, rows 111–112 (reading) |
| ACC-2 | partly | Most of the vocabulary matches the named sources (by name): Wright–Felleisen preservation with TAPL §13.5's store-typing extension; Harper's typing of K-machine states `k ▷ e` as `SavedOk`; a lock-step bisimulation for `run_eq_ref`; data refinement and forward simulation for `Projects`/`Refines` (`Laws/Machine/Refinement.lean:19-37`, reading); history variables; Hazel's handler rule. Four corrections. (1) "Budgets plus `Suffices` replace CompCert's stuttering measure" is a loose analogy. A CompCert measure exists to preserve divergence; budgets make every statement finitary and claim nothing about divergence (core-math note §8, read). (2) The Kripke wording, as in ACC-1. (3) Bisimulation is Jacobs ch. 3 (Theorem 3.4.1 in the 2026-09-05 review, read), not ch. 2. (4) The fork ledger is read by an observation, `Api/Supervision.lean:226` (reading), so it is an auxiliary state that transitions do not read; that is a history variable in the A–L sense only for the refinement |
| G1 | partly | The refutation is proved: re-run of `StaleCode.lean`, and `VerifySplit` re-proves `m6_stuck_none` and the window. It is fundamental for the declared statements. But the capstone was already documented false on host-free programs (`Typed/Assembly.lean:232-233`; system map §2 row 5), so the new content is narrower: row 133's ruled repair, stated machine-only, is still false at cuts. The amendment fails (proved, `seat_split_not_decisionLift`). The working split is keyed on `running` (proved at the window, `running_clause_vacuous_at_m6`; tested on the corpus, see above). The drop on probe A's path is `advanceState`'s `(d.1, false)` (`Machine/Fibers.lean:2080`), not `loop` (`:2139-2140`); both drop the residue |
| G2 | partly | Proved: re-run of seat ALGEBRA's `P2KripkeTyping.lean`. The file is now sha `8ac3ae15…`, not the `ef61e87e…` the seat cites; the cited theorems still pass, among 16. This duplicates ALGEBRA's finding. That a ledger step is *false* is reading: no probe builds a typed state and an allocating step that refute `StepPreserves`. The amendment changes `FrameAccepts`, the slice-5 contract of decisions row 48 (ruled 2026-09-20, amended 2026-09-23). It strengthens that contract and does not redesign it, but the owner's row should be cited. The `ResumeOk` and freshness remark holds (`Typed/Contracts.lean:71-75`, reading) |
| G3 | partly | The substance is right and its evidence is wrong. The budget-7 replay is a *fuel frontier*, not a finished run (proved, `budget7_is_fuel_frontier`, `budget7_not_finished`); this is the conflation `E4-APPROX-CE-002` registered. A finished replay comes at budget 9, where the stale `Fail` persists and the capstone is false (proved, `finished9`, `m9_root_stale`, `capstone_false_finished9`). So an exited-fiber exemption is needed at settled points too. Tested on the corpus, the untypable stale slot is narrow: among 5,180 finished runs, 0 roots hold a `pure` slot that fails the shape check, 5 U-01 stale slots still fit, and all 1,781 `unguard`/`finishFinalizer` slots carry payloads that pass. The reachable instance needs U-01 plus an error-removing catch. ID `E4-TYPED-CE-009` is also seat TYPES' proposal |
| G4 | partly | Proved: re-run of `HaltTyped.lean`; `TypedState` never reads `stuck`. But the plan already requires this: post-Phase C §6 I asks for "no unknownFiber/unknownScope/unknownRace halting as distinct consequences of the required stronger state properties", and row 52's own rationale names the liveness facts (reading). So this is rigor, not a new fundamental gap; system map R9's one line understates it. Scope liveness also touches the store rows: their pre is `True` (`Typed/Residual.lean:49`) and a store frontier answers `unit` (`Laws/Program/EvaluateR.lean:304`; native `Machine/Fibers.lean:1169-1171`) (proved, `VerifyPosts.scopeIsClosed_*`). Halting sites re-read, with `:1013` and `:1023` added |
| G5 | partly | Proved locally: re-run of `FrameCategory.lean`. The definitions are local to the probe. The gap is not new: row 117 (open) and audit §1 (`AuditH2`) already state it, including "no presence premise". The seat's contract (a presence clause per position, a side condition that keeps the requirement row monotone, restored contexts) is a design proposal for an open owner row, to be ruled by the owner. The coeffect reading is apt (by name): Petricek, Orchard and Mycroft 2014, the implicit-parameter instance of flat coeffects |
| G6a | confirmed | Upgraded from reading to proved: M5 is false at fuel 5 for `TypedCorpus.lean:62` (`VerifyAwaitLoad.typedState_load_false`, `root_code_refused`, at `[propext, Quot.sound]`). The route runs guard → fork (certified at the checked `pure nat`) → `unguard` → construction at `[]` → await. The post admits `nat 5`, and the continuation passes it on at `exitOf nat never`. Codex's H1 candidate already types the *token* by the encoded exit (`observerDeliveredType`), but its `implementation.patch` has no `fiberPost` hunk (tested by grep). The amendment matches the checker (`Program/Checker.lean:196`) |
| G6b | confirmed | Proved: re-run of `CloseScopePost.lean`. More: `closeIter`'s post (`Typed/Residual.lean:160`) is wrong the same way. The walk answers its own merged exit, `success unit` when no finalizer fails (proved, `VerifyPosts.closeSeq_done`, `closeIter_post_excludes`), and close code reaches it for two or more finalizers through `closeWalkR` (`Laws/Program/InterpR.lean:149-163`, reading). "A success or a clean failure" is plausible and unverified; it assumes finalizers fail only with defects or interrupts |
| G6c | partly | The three mismatches are confirmed (proved: re-run of `StorePostAdequacy.lean`). The proposed adequacy obligation is wrong in three ways. (1) It is false as stated at `refModify`/`refModifySome`: the pre admits a cell at any type (`Typed/Residual.lean:41-43`) while the post says `nat` (proved, `VerifyPosts.adequacy_false_refModify`). (2) It misses `memoRelease`, whose post says `unit` while the last release answers the layer scope (proved, `memoRelease_*`, `memo_admitted`, `memo_next_untyped`). (3) It does not see the frontier arm, where a store `none` answers `unit` (proved, `scopeIsClosed_*`). The scout skipped these rows (tested here). ID `E4-SCHED-CE-019` is already allocated by addendum 6, item H1.3 |
| R1 | confirmed | Reading: `Laws/Program/RuntimeR.lean:203-216`; `Laws/Program/Typed/Admission.lean:27-29`; no M7 declaration (tested by grep). Post-Phase C §6 I already asks for this ("state empty host table, initial context, budgets, decision domain…"); the gap is only that nothing is declared |
| R2 | confirmed | Reading: `Typed/Sources.lean:29,53-54`; `StoresOk.c5 : True` (printed); `capture_lookup`'s `hex` (`Typed/Assembly.lean:131-133`); a release on a closed scope through `acquireInR` (`Laws/Program/InterpR.lean:116-123`). Post-Phase C §5.1 item 5 already flags it ("a generated `True` from a refusal is not an established semantic clause") |
| R3 | confirmed | Reading: `DecisionLift` has 13 fields (`Laws/Machine/Lift.lean:308-355`); the lift seat's `M6Edits` (`2026-09-30-pass/lift/Lift.lean:849-871`). The edit obligations must be stated over the new `J`, not over today's `TypedState` |
| R4 | confirmed | Reading: `Guard.Reachable` is native, table-aware, takes a budget per decision and continues past frontiers (`Laws/Program/Guard/Core.lean:32-46`); `RReachable` is the reference at one budget and stops at the first frontier. The H1 candidate imports `Guard.Core` (read). The bridge is plausible: `Api.replay`'s machine is a `Guard.Reachable` prefix at constant budget, and `replay_rel` gives `BMeans` (reading) |
| R5 | confirmed | Reading: `ProgramSource` has only `program` and `table` (`Admission.lean:27-29`); row 114 makes the lawfulness evidence travel on the source |
| R6 | confirmed | Reading: `meaning_never_wrong` (`Laws/Program/MeaningSound.lean:746-749`) states independence from the wrong-shape parameter, and its header (`:12-16`) gives the reason |
| R7 | confirmed | Reading: system map rows R11 and R12; audit §5. Abadi–Lamport 1995 by name |
| T1 | confirmed | Tested by grep: 23 open `#proof_wanted` (`Assembly.lean` 21, `Residual.lean:455` 1, `Guard/Handshake.lean:26` 1). `typedProg_mono` is proved in ALGEBRA's current probe (re-run) |
| T2 | confirmed | Reading: `REGISTER.md:197` records `E4-PROV-CE-005` REPAIRED 2026-10-01, and `Assembly.lean:232` still lists it |
| T3 | confirmed | Tested by grep: hand inductions in `Guard/OuterDriver.lean:102,172,279`, `Guard/Single.lean:113,202,238,277,358,478` and `Guard/Decision.lean:69`; `foldl_lift` at `Guard/Core.lean:62`. Guard is 38 files and 14,674 lines (the seat says 14,687); Simulation is 8 files and 6,324 lines. Controls in `src/`: `World.lean` `worldGood`/`worldBad`/`heapNotMonotone`, and `Contracts.Example` |
| T4 | confirmed | Reading: `Effect4.Program.Denote.ExitOk` (`MeaningSound.lean:324`); Codex's H2 defines `ExitOk (w : World) (ty : EffTy) (ex : ExitV)` (`2026-09-30-seat-codex-slice6-evidence/H2/PartOne.lean:39`); `Typed/Assembly.lean:24` opens `Effect4.Program.Denote`, so the short name will be ambiguous there. "M7" also labels the store frontier (`Machine/Stores.lean:1962-1963`) |
| CONF-1 | confirmed | Proved: re-run of `FrameCategory.lean`; `stackAccepts_append`, `_split`, `_id`, `_push` at `[propext]`. One nuance: `StackAccepts` is the free category's hom-*relation*, because the middle types are existential (decisions row 48), so it is the category's image in relations. The laws are the same. `WalkTyped (_, some ex)` drops the frame (`Typed/Stack.lean:39-42`, reading) |
| CONF-2 | partly | The lift family is the right induction principle (reading). But `Guarded` does not by itself support a `J` weaker than the machine content of `I`: the loop-entry fields (`evaluate`, `task`, `clockSome`, `answer`, `Laws/Machine/Lift.lean:316-354`) derive `I` from `J` at fresh queues. That fails for the seat's `J` (proved) and holds for the split keyed on `running` |
| WRONG-1 | partly | Right that the pass synthesis's six parts (§2.4) do not suffice: probe A and `VerifyAwaitLoad` refute that (proved), and seat TYPES' M5 probe agrees (reading). Right that `TypedState` cannot exclude a halt (probe C re-run). But the synthesis claims only the *implication* is proved and says "the premises remain to prove"; the implication holds. And "TypedState cannot be the lift's J once row 133 lands" holds only for a `TypedState` that types the code of running fibers |

## What the seat missed

1. **The proposed split breaks the decision lift's entry premises** (proved,
   `seat_split_not_decisionLift`). Any cut-tolerant `J` must still give `I` at every fresh queue.
   Row 133's clause relaxes a machine fact relative to queued commands, which is the kind of
   clause that breaks this (reading). The other queue facts of rows 106 and 133 (`RCmdOk` on queued
   commands, observer delivery, registration) are trivially true of a fresh queue and are
   harmless.
   - **Smallest repair, the lift unchanged.** `J` = today's typed state with the code clause
     restricted to fibers that are neither exited nor running, plus `stuck = none` (G4). `I` =
     `J`, plus each running fiber typed by the queued command that continues it, plus the queue
     facts.
   - **Evidence.** The window fiber is running, and the running-keyed code clause holds at the
     window at every world (proved; the rest of that `J` is the seat's own `J`). No settled corpus
     result has a running fiber (tested, 13,078 + 51,064). The scans count running fibers only;
     that the non-running fibers of a cut machine type is reading: resume, the middleware
     re-entry and an interrupt unpark each leave non-running code typed by `ResumeOk`, its exit
     or a clean failure.
   - **The alternative.** A receipt-dependent lift: a strong `S` at true receipts and a weak `J`
     at cuts. It changes `Laws/Machine/Lift.lean`.
2. **M5 is false at HEAD for a typed-corpus program**, proved on the denotation itself
   (`VerifyAwaitLoad`). Every corpus program in the `forkValue` context follows the same route
   (reading). Seat TYPES reports M5 false independently (`types/note.md`, TY-01: `Fits` against
   the checker's normalized order; reading, not re-run here). These are two refutations, and they
   need two register IDs; both seats propose `E4-TYPED-CE-009`.
3. **Budget 7 is a fuel frontier, not a finished run** (proved). This repeats the conflation
   `E4-APPROX-CE-002` registered (`Test/contracts/machine-approximation.contract.md:141`).
   `finished7m` is a machine predicate. The finished refutation needs budget ≥ 9 (proved).
4. **Three more protocol rows fail their handler, and the frontier arm is unaccounted for**
   (proved, `VerifyPosts.lean`): `memoRelease`, `refModify`/`refModifySome` (the pre is too weak
   for the `nat` post), and `closeIter`. Store frontiers answer `unit` while the scope rows' pre
   is `True`. The seat's per-row adequacy obligation, as written, is false at `refModify` and
   blind to the frontier arm.
5. **ID collisions.** `E4-SCHED-CE-019` is allocated by addendum 6, item H1.3 ("a fiber is typed
   by its queued finish"). `E4-TYPED-CE-009` is proposed by both PROOFS and TYPES.
6. **Timing against Codex's H1** (addendum 6, item 1, in flight; statements only). The cut
   problem must reach Codex before the restated `TypedState`/`QueueOk` statements land. The note
   cites row 133 but not addendum 6, which carries the instruction.
7. **The reachable stale slot is narrow** (tested).
   - Among 105,051 fuel frontiers of the typed corpus (budgets 0–40, four tapes), 4,640 root
     windows (running, not exited, `pure` code, empty stack) all pass the shape check; over the
     interleaving pairs (budgets 0–30), all 11,230 windows among 645,511 frontiers pass.
   - Among 5,180 finished runs, no root slot fails the shape check.
   - The only reachable untypable case found is probe A's construction: U-01, plus a catch that
     removes the error column.
   - So the M6 proof effort should not expect H1-type staleness to be common; Codex's H1 witness
     is a constructed state.
8. **Several gaps the seat files are already plan requirements** (reading).
   - Post-Phase C §5.1 item 5 already covers R2; §6 I covers R1 and G4; §5.3 states protocol
     adequacy ("a postcondition must relate the actual operation to the actual answer").
   - The 2026-09-05 papers review A2 proposed the handler judgment as `Implements` (read). It
     never landed.
   - The generic `Protocol.Typed` (`Laws/Effects/Protocol.lean:45-50`) has no adequacy theorem.
     `TypedProg` is not an instance of it; the model-probe synthesis says "Ψ_S ⊕ Ψ_F no longer
     builds the concrete typing judgment".
   - The natural home for the adequacy obligation is therefore one generic theorem, with an
     instance per row.
9. **Rows 111–112 are absent from the M5–M7 statements**: the signature parameter, and
   `w.serviceTy` as a static world component tied to the source in `TypedState` (reading).
10. **The re-run ALGEBRA probe changed** after the seat's re-run (sha `8ac3ae15…` against the
    cited `ef61e87e…`); the cited theorems still pass (proved, re-run).
11. **A cost for probe authors.** `decide +kernel` on a *false* replay claim exhausted memory
    (exit 137 after 126 s at 3.5 GB; `verify-probes/VerifyRedOOM.lean`). Refutations of replay
    facts must therefore be proved as positive negations.

## Probes and commands

All run from `/Users/pooks/Dev/lean4-effect4` as
`bash proofs/verify-probes/verify-rerun.sh <absolute probe> <name>`, which calls
`serial.sh lake env lean -M6144 -DwarningAsError=true <probe>`. Logs are in `verify-logs/`.

| probe | result | what it shows |
| --- | --- | --- |
| seat `probes/StaleCode.lean` | exit 0, 20 at `[propext, Quot.sound]` | the seat's A, re-run byte-identical |
| seat `FrameCategory`, `HaltTyped`, `StorePostAdequacy`, `AwaitValuePost`, `CloseScopePost` | exit 0, axioms as the seat reports | re-runs |
| seat `PostScout`, `WindowScout4`, `PrintTypedState` | exit 0, same output (the print is identical to `logs/print-typed-state.log`, tested by `diff`) | re-runs |
| ALGEBRA `probes/P2KripkeTyping.lean` (sha `8ac3ae15…`) | exit 0, 16 at `[propext, Quot.sound]` | G2, T1 |
| `verify-probes/VerifySplit.lean` | exit 0, 13 at `[propext, Quot.sound]` | `seat_split_not_decisionLift`, `m6_root_running`, `running_clause_vacuous_at_m6`, `budget7_is_fuel_frontier`, `budget7_not_finished`, `finished9`, `capstone_false_finished9`, `worldValid_not_upward_closed` |
| `verify-probes/VerifyAwaitLoad.lean` | exit 0, 6 at `[propext, Quot.sound]` | `typedState_load_false`, `root_code_refused` |
| `verify-probes/VerifyPosts.lean` | exit 0, 13 at most `[propext, Quot.sound]` | `memoRelease`, `refModify`, `closeIter` and frontier-arm red controls |
| `verify-probes/VerifyRedOOM.lean` | exit 137 by design (126 s, 3.5 GB) | false replay claims under `decide +kernel` |
| `verify-probes/VerifyScout1.lean` | exit 0 | probe A's 13 budgets × 6 prefixes: running fibers only at fuel frontiers; budget 7 with the full tape is `frontier-fuel`, budgets ≥ 9 `finished` |
| `verify-probes/VerifyScout2.lean`, `VerifyScout2Pairs.lean` | exit 0 | 0 settled results with a running fiber (13,078 and 51,064); store rows the seat skipped |
| `verify-probes/VerifyScout3.lean` | exit 0 | finished runs: root code-slot categories `[3394, 5, 0, 1781, 0]`; marker payloads 1,781/0 bad |
| `verify-probes/VerifyScout4.lean`, `VerifyScout4Pairs.lean` | exit 0 | untypable window shapes at fuel frontiers: 0 of 4,640 (corpus), 0 of 11,230 (pairs) |
| `verify-probes/VerifyScout5.lean` | exit 0 | the denoted root of `awaitFiber.value`, step by step |

Pairs window scan (`VerifyScout4Pairs.lean`, budgets 0–30, four tapes): 645,511 fuel frontiers,
11,230 root windows, 0 that fail the shape check (exit 0, 119 s).

## For the coordinator: rows to allocate (proposals only; no register edited)

| proposal | content |
| --- | --- |
| decisions row | M6's machine-only predicate is keyed on `running`: the code clause covers fibers neither exited nor running; running fibers are typed in the configuration predicate by the queued command that continues them (row 133 for `finish`). `DecisionLift` unchanged. Red control `VerifySplit.seat_split_not_decisionLift`; positive control `running_clause_vacuous_at_m6` |
| register (fresh ID; not `E4-TYPED-CE-009`) | "M5 loads every checked program into a typed state": the await-by-value post reads the answer column. Witness `verify-probes/VerifyAwaitLoad.lean` (`typedState_load_false`, the corpus's `awaitFiber.value`) |
| register (fresh ID; not `E4-SCHED-CE-019`) | "Every protocol row is fulfilled by its handler": witnesses the seat's `StorePostAdequacy.lean`, `CloseScopePost.lean`, `AwaitValuePost.lean` and this folder's `VerifyPosts.lean` (`memoRelease`, `refModify`, `closeIter`, the frontier arm) |
| register (fresh ID) | the seat's probe A at budgets 6 and 9 (`StaleCode.lean`; `VerifySplit.capstone_false_finished9`) |
| brief text | one generic adequacy theorem for `Protocol.Typed` (the 2026-09-05 review's `Implements`), instantiated per row, with the frontier arm covered and the scope rows' pre carrying scope liveness |

