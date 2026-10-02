# The open obligations, placed in the theory (2026-10-02)

**The one thing.** This note places every open proof obligation on the M5 → M6 → M7 spine in the theory
we have already built. It also places the sub-steps of the slice in flight (the layer family) and
Codex's two finished slices. For each it gives:
- the concept and property in `docs/core/semantics.md`;
- the question it answers (a ledger goal or a registry claim, with its role);
- what it proves once closed;
- what it does not prove;
- what it unlocks.

The owner's standing rule (AGENTS.md, Trust, 2026-10-02) is that nothing is worked until it has such
a row. Any lemma below is a step of a named row.

Status is measured, not written here: `generated/semantics.md` and the ledger lines that
`lake build` prints. The ledger counts quoted here are as of `claude/proofs` at `9a2b7651`:
- M3bAssembly: 3 open, 2 proved;
- M6Ledger: 7 open, 13 proved;
- M6Edits: 1 open, 12 proved;
- M7: 4 open.

Evidence words: **proved**, **tested**, **reading**, **assumed**.

## 0. The structures this note reads

| Structure | What it owns | Where |
| --- | --- | --- |
| The ten concepts, their literature, cuts and required properties | meaning | `docs/core/semantics.md` §2; §1.2 says what each kind of evidence licenses |
| Claims, with role and status | the selected questions and their evidence | `tools/Tools/SemanticsRegistry.lean` → `generated/semantics.{json,md}` |
| The ledger | the declared questions (`#proof_wanted`, `#obligation_proved`, `#typed_state_obligations … ceiling`) | `src/Effect4/Laws/Program/Typed/Assembly.lean:1662-1913` and beside each scope |
| Cuts | where a question applies | `docs/core/decisions.md` (rows) |
| Refutations and contests | the attacked statements | `Test/Counterexamples/REGISTER.md` |
| Requirements and arrows | why the spine matters | `docs/core/system-map.md` (R1–R13, K1–K5) |
| Placement of declarations | the primary concept of each theorem | `@[semantics "<concept>"]` and `#semantics_census` (`Laws/Auto/Semantics.lean`) |
| Reference graph and work order | which declaration uses which; authored prerequisites | Codex's proofMap (`Tools.ProofMapSelection`; branch `codex/proof-feature-graph`, to integrate) |

Roles in the report:
- `fundamentalProperty`: the judgment's own soundness theorem;
- `preservation`: subject reduction, an invariant kept by a step;
- `compatibility`: a typing rule admissible for a composite;
- `inversion`: canonical forms;
- `simulation`: equal observation on a fragment;
- `adequacy`: the observed run is typed;
- `progress`: a successor exists. The register uses it for `M7.never_halts`, but that is the invariant
  consequence `stuck = none`, not successor existence (row 139).

## 1. The spine

```
M5   DenotesTyped root                         (M3bAssembly.denoteR_typed)
       │  loadsTyped_of_denotesTyped_typed      (Commands/Finish.lean, proved)
       ▼
     LoadsTyped root rootTy fuel fuel          (M3bAssembly.typedState_load)
                                                    ╲
M6a  StepPreserves root rootTy cmd, 18 commands       ╲
     + the decision edits (M6Edits)                     ╲  reachable_of_ledger (proved)
       │  stepKeeps_of_stepPreserves, DecisionLift       ▼
       ▼                                          M6c ReachableTyped     (M6Ledger.typedState_reachable)
M6b  DecisionKeeps root rootTy fuel d                  │  m7_of_capstone: replay_rel (run_eq_ref's relation),
     (M6Ledger.decision_preserves)  ─────────────────▶ │  obsTyped_of_machineTyped, replay_stuck_eq (proved)
                                                       ▼
M7   M7Exits / M7Stores / M7NoHalt on M7Fragment   (M7.exits_typed / stores_typed / never_halts)
     m7_of_ledger proves the implication (claim m7-route, proved).
     ExitHandlesValid (M7.exitHandles_valid) stands apart: the exit connector's premise (row 180).
```

| Goal | Concept (semantics.md) | Role | What it says once proved | Kept as hypotheses | What it does not give | Consumer |
| --- | --- | --- | --- | --- | --- | --- |
| `M3bAssembly.denoteR_typed` (claim `denote-typed`) | residual-program-typing (§2.2) | fundamentalProperty | At a program with well-formed references, every checked point's denotation is a `TypedProg` at its certificate, at every world whose service table is the source's. | `layerRefsWF` (row 170); the world's service table (row 175); `PointTyped` with the completed view (row 175) | anything about the machine or a run; bind closure (refuted, `E4-TYPED-CE-030`); which host answers arrive | `typedState_load` |
| `M3bAssembly.denoteR_typed_provideLayer` (`ProvideLayerArm root`) | residual-program-typing, with context-requirements (§2.8) | the one missing arm of the fundamental property | A typed `provideLayer` point at fuel `f + 1` denotes a typed program, given every node at fuel ≤ `f`. | the induction hypothesis (`childDenotes_upto`'s form) | the arms already proved | `denotesTyped_of_provideLayer` → `denoteR_typed` |
| `M3bAssembly.typedState_load` (`LoadsTyped`) | residual-program-typing → reactive-scheduling | preservation (initialization) | A lawful, checked, closed source with an empty requirement row loads into `J`. | `LawfulSource`, a closed type, the empty row (row 117) | anything after the load | `reachable_of_ledger` |
| `M6Ledger.step_*` (7 open: `loop`, `deliver`, `launch`, `registrationDone`, `wake`, with `decision_preserves` and `typedState_reachable` below) | reactive-scheduling (§2.4) | preservation | One dispatched command keeps `I = J + ReadCode + QueueOk` at some later world (`StepPreserves`). | `m.stuck = none` at dispatch | **progress** (`scheduler-progress` is absent; row 139); fairness (`fair-scheduling` is absent; R12, row 86); termination | `stepKeeps_of_stepPreserves` → `decision_preserves` |
| `M6Edits.clockSome` | reactive-scheduling | preservation | The clock edit with a due time keeps `J`. | — | as above | `decision_preserves` |
| `M6Ledger.decision_preserves` (`DecisionKeeps`) | reactive-scheduling, host-session-protocol (§2.9) | preservation | One tape decision keeps `J` when its host answer, if any, is admitted (`AnswerOk`). | `AnswerOk`; that the host answers at all is an assumption (`host-progress`, assumed) | host progress | `reachable_of_ledger` |
| `M6Ledger.typedState_reachable` (`ReachableTyped`) | reactive-scheduling | preservation (the capstone invariant) | Every machine an answer-free tape reaches is in `J`. | answer-free tapes (repairs `E4-SCHED-CE-015`) | liveness | `m7_of_capstone` |
| `M7.exits_typed`, `stores_typed`, `never_halts` | translation-simulation (§2.10) | adequacy / "progress" | On `M7Fragment`, the frame machine's observed exits fit, its stores fit, and it never halts. | `M7Fragment`: lawful, `root.table = []`, checked, closed, empty row, answer-free | non-empty host tables (R6, DI-57); TypeScript or OCaml execution; Lean compiler lowering; termination | the end of the spine (R1) |
| `M7.exitHandles_valid` | translation-simulation | preservation | Recorded exits name only live handles. | registered handle bytes (row 180) | it does not yet follow from `J`: `Live` admits scope and memo handles unchecked | the exit connector `exitOk_of_fitsExit` |

The utility, in one line: M7 is the first statement that a run of a checked program, as the frame
machine executes it, is typed. Every row above is a premise of it through a proved route theorem, and
nothing else on this list is needed for M7.

## 2. The slice in flight: the layer family (`ProvideLayerArm`)

Why the arm is not one lemma: Seat L's controls (`c1c05314`, proved) showed `ProvideLayerArm` is false
as stated at three programs. At each, the run answers `badShapeExit`, which no `TypedProg` derivation
admits. The arm can only be proved after three representation repairs. Each repair is placed below by
the goal it serves.

| Step | What changes | Concept and kind | Why the goal needs it | What it does not prove | State |
| --- | --- | --- | --- | --- | --- |
| L0, row 176 (b) | Built contexts answer the fiber-context image `Val.context`; every reader is `Val.context?`. | store-typing: `Ty.context` gets one value image, so `fits_context_inv` (an inversion lemma) is the only canonical form | The memo hit read the built context with the old decoder and refused it (`E4-TYPED-CE-023`, `old_memo_refuted`) | the arm itself | landed `f8571cf0`, merged `9a2b7651` |
| L1, proposed row 185 (`E4-TYPED-CE-031`) | `orDie` resolves its inner layer, a reference included, in both machines. The frame machine's resolver is now fuel-indexed (`resolveLayerWith`/`resolveLayerZero`), mirroring `denoteLayerWith`/`denoteLayerZero`, because a reference's hop can land on an `orDie` over another reference. | translation-simulation: the structural pass of `run_eq_ref` (`layer_intro`, `layerBuild_intro`) must stay proved across the change. Also rc.112 transcription: `Layer.ts:3327-3328` builds `self` whatever layer it is. | With the inner reference refused, a checked, well-formed program denotes `badShapeExit` (`orDie_arm_refuted`, `orDie_denotes_refuted`) | that `orDie` is typed: that is L3's `orDie` arm | in progress on `seat/L`: core and agreement edits written; `Effect4.Program.Compile` builds; `Effect4.Laws` failed at the hop and is being re-proved |
| L2a, proposed row 186 | A typing for layer-node points replaces `BodyTyped.layerBuild`'s `PointTyped` premise. | residual-program-typing: a fork's pre must be satisfiable | Today the premise holds at no layer point (`layerBuild_untyped`), so every merge sibling's pre is false (`merge_arm_refuted_today`) | — | next |
| L2b, proposed row 186 | The merge's exits are read through `Val.asList?`, so the fiber snapshot is a list; the empty snapshot is `[]`. | inversion: the reader must be total on every value the post `Fits … (.list (.exitOf a e))` admits, the snapshot case included | `contextsOf` answers `none` on the snapshot, and the merge refuses | — | next |
| L2c, proposed row 186 | A sibling that failed with an empty cause fails the merge with that cause. | inversion: `CauseFits` of the empty cause is vacuous, so the type admits it and the reader must not refuse it | `reasonsOfVal` answers `[]`, and the merge refuses | — | next |
| L3 | One typing lemma per `denoteLayer` constructor (`succeed`, `fresh`, `orDie`, `effect`, `effectDiscard`, `provide`, `provideMerge`, `merge`, `mergeAll`, `ref`), memo hit and miss included, plus the `provideLayerR` protocol (scope made, build, body under the built context, scope closed). | residual-program-typing, as compatibility lemmas (`guardBind_typed`, `seq_typed`, `catchGuard_typed`, `onExit_typed`). context-requirements gives the built context its row: `provide_discharges`, and `ServicesFit` for the body. | It is the arm | memo sharing as an observation (`layer-sharing-contract` is a separate claim) | after L1 and L2 |
| L4 | `#obligation_proved` for `denoteR_typed_provideLayer`, then `denoteR_typed` (`denotesTyped_of_provideLayer`), then `typedState_load` (`loadsTyped_of_denotesTyped_typed`). The `M3bAssembly` ceiling goes from 3 to 0. The claim `denote-typed` reads proved; no claim names `typedState_load` yet, so a `load-typed` claim is proposed beside `load-typed-layer-free`. | — | closes M5 and the load, the first two premises of M7 | M6 | after L3 |

## 3. M6, the clauses each open command needs (decisions row 134)

| Goal | The `I` clause it reads or must keep | Contest |
| --- | --- | --- |
| `step_registrationDone` | (d): race keys disjoint from the observer keys, stored and queued | — |
| `step_launch` | (e): fresh ids | — |
| `step_wake`, `M6Edits.clockSome` | (a) timers; (b) waiters | — |
| `step_loop`, `step_deliver` | (b) the waiter column; the fiber's code step, typed by `TypedProg`'s clauses through the proved `M3bAdequacy` lemmas (`storeStep_typed`, `answerFrame_typed`, `seqFrame_typed`, …; reading) | `E4-TYPED-CE-012` (repaired, row 135); `E4-TYPED-CE-025` (seeded: completing a Deferred owes its waiters tokens no clause relates; row 134 (b)) |
| `decision_preserves` | all of the above, plus the decision edits | — |
| `typedState_reachable` | `typedState_load` and `decision_preserves` (`reachable_of_ledger`, proved) | — |

Clause (c), `exitDone` and `finish`, is proved (`c719c255`).

## 4. Codex's two slices (to integrate at the next safe boundary)

| Slice | Placement | What it proves | What it does not prove | Utility |
| --- | --- | --- | --- | --- |
| `codex/park-handshake` `96a70052` | reactive-scheduling; ledger scope `M4Handshake` (goal `parkHandshake_reachable`, statement unchanged) | Proved (per its receipt): on every `Guard.Reachable` machine, resuming a parked fiber with a mismatched token leaves the observation (exits, stores) unchanged. The guard-or-inert property follows from unique fiber ids. | pending ownership; captured batches; due-work typing; progress; fairness | closes the `M4Handshake` scope (0 open). It is not on the M7 spine, and no later theorem uses it. |
| `codex/proof-feature-graph` `5d247978` | tooling; no concept, and no evidence of its own | It validates names, witnesses and authored prerequisites. The selected proofMap shows proof-body, definition-body and statement references, and authored goal prerequisites and work order. | that any goal is entailed; completeness (the selection excludes `M4Handshake`) | It is where this note's spine and work order become data that the producer checks, instead of prose. |

## 5. Not started without a row

- Helpers are named by the row they serve. In this slice: `resolveLayerWith_keys`,
  `raceSites_resolveLayerWith` and `resolveLayerTerm_orDie` serve L1, through the agreement and the
  handle and race-site laws that `run_eq_ref` and `M6`'s `QueueOk` read.
- Reconfirming a proved lemma is not a step. A lemma is re-proved only when a representation change
  breaks it, and then it is listed under the step that broke it (here, L1).
