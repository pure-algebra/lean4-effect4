# Review: the Rocq side of `effect4_of_ocaml`

Reviewer: Claude, 2026-09-02. Subject: `/Users/pooks/Dev/effect4_of_ocaml` (read-only).
Scope: `rocq/*.v`, the evidence they cite, and their relation to the Lean models.

**Re-check performed.** No `rocq`/`coqc` on `PATH` and `ROCQ_BIN` unset, but
`evidence/itree.json` names a working installation at
`/Users/pooks/Dev/foldlab/annex/coq/.opamroot/estate/bin/rocq` (Rocq 9.1.1,
OCaml 4.14.4), with `coq-itree` under its `lib/coq/user-contrib`. I copied all
seven `.v` files to a scratch directory and recompiled every one from scratch.
All seven compile clean, and every `Print Assumptions` output below is one I
observed myself, not one read from JSON.

---

## 1. What is proved, and whether the README is supported

| File | Proved | Assumptions |
| --- | --- | --- |
| `Effect4Probe.v` | 11 receipts: two decision-procedure reflections (`check_expr_reflects_scope` :200, `check_term_reflects_scope` :209), `eval_deterministic` :220, two `Ensuring` equations :225/:230, four closed evaluation examples :277-295, one admission example :269 | all 11 **closed under the global context** |
| `AlgebraProbe.v` | the three monad laws for a `pure`/`vis` tree (:24, :28, :36) | `bind_pure_left` closed; `bind_pure_right` and `bind_associative` use **`functional_extensionality_dep`** |
| `SimulationCertificate.v` | `validate_bisimilar` :134 — a checked finite certificate implies coinductive **strong bisimilarity** (:109) of the two entry vertices; plus `check_pair_sound` :82 and `closed_relation_bisimilar` :119 (a genuine `cofix`) | all 5 **closed** |
| `WeakSimulationProbe.v` | `eutt eq (silent_steps n t) t` :15, the same under `ITree.bind` :23, and `Ret v ≁ spin` in both directions :28/:32 | all 4 **closed** (ITree/Paco axioms are not reached by these four) |
| `MachineProbe.v` | six universal theorems: `step_preserves_meaning` :189, `finished_run_correct` :219, `step_decreases_weight` :243, `enough_fuel_finishes` :258, `machine_agrees_with_eval` :292, `resume_frontier` :271; plus two frontier examples :308/:314 | all 8 **closed** |
| `CellExecutionCertificate.v` | five: `check_cell_sound` :106, `cell_eval_agrees_core` :128, `produce_cell_checks` :143, `produce_cell_complete` :157, `certified_outcome` :170 | all 5 **closed** |
| `CallbackProtocol.v` | twelve, notably `callback_step_iff` :155 (the relation and the function coincide), `callback_at_most_once` :296 (body/cleanup/abort each fire ≤ 1 over any finite tape), `pending_without_reply` :348 | all 16 receipts **closed** |

### Claim audit

- **"Six universal machine proofs require no added axioms"** (`README.md:14`) — **supported**, verbatim. All six print *Closed under the global context*, and all six quantify over arbitrary terms, services, environments and initial states.

  Two framing caveats. First, `meaning` (`MachineProbe.v:72`) is *defined by* `eval`, so `step_preserves_meaning` and `machine_agrees_with_eval` relate two Rocq artefacts to each other; they carry no information about Effect TS, the OCaml 5 handlers, or the extraction. Second, `README.md:14` places that sentence immediately after "875 cases agree with the structured interpreter and Effect TypeScript", which invites the reading that the proofs cover the differential runs. They do not. One clause would fix it.

- **"Five new Rocq proofs have no added axioms"** (`README.md:19`) — **supported**; `CellExecutionCertificate.v` has exactly five theorems and all five are closed.

- **"It checks both transition directions on finite graphs, including cyclic graphs"** (`README.md:12`) — **supported and load-bearing.** `check_pair` (`SimulationCertificate.v:54-62`) has two `forallb`s, forward (:59) and backward (:60); `local_simulation` (:72-80) quantifies both ways; `bisimilar` (:109) is `CoInductive` and `closed_relation_bisimilar` (:119) is a real guarded `cofix`, which is what makes the cyclic cases (`lean-cycles-one-to-two`, `infinite-same-labelled-cycle` in `evidence/simulation.json`) mean anything. This is the strongest single result in the workspace.

  Two precision flags. (a) The proved relation is *bisimulation*, not simulation; "simulation-certificate checker" understates it and the theorem name `validate_bisimilar` should win. (b) **There is no completeness theorem.** Nothing licenses reading a rejection as a refutation. The eight `expected:false / accepted:false` rows in `evidence/simulation.json` are OCaml *search* failures over an unverified search, not proofs of non-bisimilarity — and the file's own limitations list does not say so either. `README.md:12` should say that rejection is evidence, acceptance is proof.

- **ITree silent-step results** (`README.md:13`) — **supported**, and `evidence/itree.json`'s `notClaimed` field is honest. But these are three-to-four-line corollaries of library lemmas (`tau_eutt`, `eutt_Ret_spin_abs`, `eutt_spin_Ret_abs`); the value is the *viability finding* — that the necessary weak-simulation distinctions are available axiom-free at Rocq 9.1.1 with ITree 5.2.1 — not the theorems.

- **`evidence/verification.json` `limits`**: "11 core theorem/lemma/example receipts have no axioms; two generic algebra laws use functional extensionality" — **accurate**; I reproduced exactly that split.

### Other findings

- **`README.md` is stale.** `rocq/CallbackProtocol.v` is the largest (17 KB) and newest Rocq file, with a frozen contract (`docs/CALLBACK-PROTOCOL-CONTRACT.md`) and its own evidence, yet it appears in neither the numbered list (`README.md:11-18`) nor "Run the checks" (`README.md:25-38`, which omits `build-callback-protocol.sh`, `check-callback-protocol.mjs`, `probe-callback-source.mjs`).
- **Axiom counts are not comparable across kernels.** `functional_extensionality_dep` is an added axiom in Rocq; in Lean 4 `funext` is a theorem from `Quot.sound`. A Lean restatement of `bind_associative` would report `[propext, Quot.sound]` and look *worse* while assuming *less*. Any table that puts "axiom-free Rocq receipts" beside "Lean uses `propext`, `Quot.sound`" (e.g. `docs/BOOTSTRAP-RESULTS.md:369-375`) should say this.
- **`eval_deterministic`** (`Effect4Probe.v:220-223`) is vacuous: it restates that `eval` is a function, and is proved by `congruence`. It should not be counted among the eleven receipts.
- **Magic constants inside the model.** `CallbackProtocol.v:58` bakes `Offered (Value 99)` into `abort_events` and `:70` bakes `Failure [Die 91]` into the `DieCancel` branch. These are fixture values living in a semantic definition; a differential test cannot then distinguish "the model is right" from "the model was fitted to the observations". They should be config fields.
- **Inconsistent Lean pins.** `evidence/callback-protocol.json` snapshots lean4-effect4 at `5173288`, while `effects5.json` and `cell-execution.json` snapshot `c951711`. Not wrong, but a reader comparing packets needs to know they are not the same checkout.
- `eval_expr` (`Effect4Probe.v:49`) takes `state` and `ambient` parameters it never uses.

---

## 2. Relation to the Lean models

**Same object: the frame machine.** `MachineProbe.configuration` (:27-32) and `Effect4.FrameFiber` (`Runtime/Runtime.lean:221`) are the same design — a `current` control, a first-order frame stack, a *total* one-step function, and a fuel-bounded runner whose exhaustion is a live frontier and never a failure. `MachineProbe.run_result` (:139) and `Effect4.FrameStep` are the same three-way answer. Both repos wrote the same DB-04 ruling independently (`docs/MACHINE-PROOF-CONTRACT.md` "Exhaustion is not an Effect failure"; `docs/FRAMES-DAG.md` separation 6).

**Where they diverge, and whether it matters.**

| | Rocq `MachineProbe` | Lean `FrameFiber` | Matters? |
| --- | --- | --- | --- |
| Frame payload | `ThenFrame/CatchFrame/EnsureFrame` carry a captured `environment` and a `term` (:17-21) | stack is `List Prim`; continuations are *nominal* `ν`, bodies are subterms, no environment | **Yes.** DB-02 and `FRAMES-DAG` separations 4-5 forbid stored environments. The Rocq machine is not liftable as-is. |
| Cleanup | `EnsureFrame`/`RestoreFrame` pair, unconditional | `Prim.onExit body finalizer finalizerInterruptible` plus the `contAll` hook and `Prim.ensure` masking | **Yes.** Rocq models a strictly weaker `ensuring`. |
| Interruption | none (an `Interrupt n` reason is just a third failure tag; `first_fail` :77 ignores it) | `interruptible`, `interruptedCause`, `deferredInterrupt`, and the fused `getCont`/`exitFailCause` skip loop (separation 8) | **Yes.** The hardest part of rc.112 is entirely absent on the Rocq side. |
| Types | everything is `nat`: values, errors, defects, interruptor ids, service keys, trace tokens | `Prim ν σ β ε δ ι α`, `Exit`, `Cause` | Yes for parity claims, no for the machine metatheory. |
| State | one `nat` cell in the configuration | none — state is a service at the `Effects.Family` level | Yes: the Rocq machine conflates runtime and service layers. |

**Scope.** `Effect4.Scope` (`Runtime/Scope.lean:86`) is a finalizer *table* with a strategy, keys, `closeOrder` reversal (:785), an `Exit.asVoidAll` merge (:796), and idempotent close. `MachineProbe`'s `EnsureFrame` is a single anonymous cleanup term. They are not the same object and the Rocq packet should stop implying they model the same thing; the honest statement is that `Ensuring` is the *degenerate one-entry sequential* case of `Scope.close`.

**Trace alphabet.** `CellExecutionCertificate.cell_event` (`:10-12`, `ReadCell`/`WriteCell`) is very nearly `Effects.Trace.Event.op`/`.answer` (`Trace.lean:70-80`) over a two-name Cell family, and `docs/CELL-EXECUTION-CONTRACT.md` says so explicitly. That is a genuine overlap and the cleanest bridge candidate in the workspace. The gaps: Rocq has no `decide`, `enter`/`leave`, `finalizer`, `done` or `frontier` rows, and — importantly — no `Mask` discipline, so it has no analogue of `project_project` / `agree_of_agree_m2` (`Trace.lean:138`, :158) and cannot state agreement *under a named mask*, which is the only form of agreement `TRACE-DAG` accepts. `Effect4Probe`'s own `out_trace : list nat` (:40) is not this alphabet and should not be conflated with it.

**Flow v2.** `SimulationCertificate.graph` (`:11-14`) is a flat, densely indexed LTS with `word` labels. `RawFlow` (`Flow/Raw.lean:17`) has typed block parameters, four terminator forms, eight WF clauses (`FlowWF` :188) and the decidable `cyclesChoose` with a *two-directional* `cyclesChoose_iff` (:521, :526) — Rocq has nothing of comparable strength there. Crucially the Flow v2 packet declares **no execution semantics** (`flow-v2.contract.md:44-48`), so the projection in `test/FlowExport.lean` invents the transition structure the certificate checker consumes. That projection is unproved (`evidence/simulation.json` limitations; `docs/OCAML-ROCQ-PARITY-ANALYSIS.md:210`). The runner that *would* give Flow a transition system already exists downstream at `Effect4/Semantics/Runs.lean:140` — the export should target it, not a hand-rolled projection.

---

## 3. Worth porting, ranked

1. **`enough_fuel_finishes` + `step_decreases_weight` for `fuelFor`.** `Effect4/Semantics/Runs.lean:157` defines `fuelFor` with a docstring arguing it always suffices — and no theorem. `MachineProbe.v:243`/`:258` is exactly that argument done properly: a syntactic weight, a strict decrease per step, and "weight ≤ fuel ⇒ finished". Lean has `run_fuel_mono` (:407, more fuel changes nothing) but not the converse. Highest value, smallest distance.
2. **`resume_frontier` (`MachineProbe.v:271`).** `run fuel c = Frontier p → run extra p = run (fuel+extra) c`. Lean's `FrameFiber.run` has only its three unfolding equations (`Runtime.lean:2022-2043`) and no additivity law, so today a Lean frontier cannot be resumed *as a theorem*. This is what makes a frontier a real suspension rather than a shrug, and it is the DB-04 ruling's missing half.
3. **Finite certificates checked independently.** The pattern — untrusted search produces a small closed relation, a *proved* checker turns acceptance into a coinductive theorem — is the right shape for the open `TRACE-DAG` `semantics` edge. Port the idea, not the file: state it over `Effect4/Semantics/Runs.lean`'s `Next`/`RunResult` and `Effects.Trace.Event`, with a mask parameter, so acceptance yields agreement *under `m1`* rather than raw label equality. Add the completeness half Rocq lacks.
4. **The ITree silent-step treatment.** The Flow runner's `Plan`/`step` (`Runs.lean:85`, :116) already produces administrative transitions that no mask keeps; any future simulation theorem must quotient them. `WeakSimulationProbe.v:15`/:23 is the minimal statement of what that quotient must satisfy (hide finitely many, never identify divergence with return). Adopt the *obligation*, in Lean, before writing the bridge.
5. **`callback_step_iff` (`CallbackProtocol.v:155`).** A relational spec and its executable function proved coincident. `Effect4/Semantics/Step.lean` is a stub and DB-03 requires nondeterminism to be relational while `FrameFiber.step` is total; this iff-pattern is how those two are reconciled without minting a second machine.
6. **The `Credits` invariant style (`CallbackProtocol.v:209-212`).** "count of observable events + a bit of live capability ≤ 1", preserved by every step, then instantiated at `initialize`. This is a clean way to state at-most-once finalizer/abort obligations over arbitrary tapes, and it maps onto `Scope`'s idempotent-close and `Prim.onExit` obligations.
7. Low value: `AlgebraProbe.v` — Lean's `Effects/Algebra/Laws.lean` already owns these laws over a real `Signature`, and the funext dependence is a Rocq artefact.

---

## 4. Next steps for Codex (Rocq side)

1. Add a `weight`-analogue and an `enough_fuel_finishes` for the *Flow* runner, then hand the statement over as a Lean obligation on `Effect4/Semantics/Runs.lean:157`'s `fuelFor` — that is the concrete bridge this workspace can pay for.
2. Prove completeness for the certificate checker in `rocq/SimulationCertificate.v` (bisimilar entries ⇒ some checkable finite certificate exists, on finite graphs), so rejections become evidence rather than search failures.
3. Rename `validate`/`local_simulation` in `rocq/SimulationCertificate.v` to say *bisimulation*, and amend `README.md:12` to distinguish proved acceptance from unproved rejection.
4. Add a mask parameter to `rocq/SimulationCertificate.v`'s `check_pair` so a certificate can be checked *under a projection*, matching `Effects/Trace.lean`'s `Mask` discipline instead of demanding raw label equality.
5. Re-target `test/FlowExport.lean` at `Effect4/Semantics/Runs.lean`'s `step`/`Next` rather than a bespoke control-flow projection, and state the projection lemma as an explicit open obligation.
6. Lift `CallbackProtocol.v:58` and `:70`'s hardcoded `99` and `91` into `callback_config` fields so the model is not fitted to its own fixtures.
7. Add an interruption bit and a maskable `EnsureFrame` to `rocq/MachineProbe.v`, or state plainly in `docs/MACHINE-PROOF-CONTRACT.md` that the packet models `ensuring` without interruption and is therefore not a model of rc.112 cleanup.
8. Add `rocq/CallbackProtocol.v` and its three scripts to `README.md`'s numbered list and "Run the checks", and add one clause to `README.md:14` scoping the six machine proofs to the Rocq interpreter.

**Discard or de-emphasize.** `Effect4Probe.eval_deterministic` (:220) — vacuous, and it inflates the receipt count. `AlgebraProbe.v` — superseded by Lean's own algebra laws; keep it only as the recorded note that Rocq needs funext where Lean does not. The `expected:false` rows of `evidence/simulation.json` — keep them as regression fixtures, but stop presenting them alongside the proved acceptances as if both had the same status. And `Effect4Probe`'s `out_trace : list nat` should not be described anywhere as a trace in the `Effects.Trace` sense; only `cell_event` has a claim to that.
