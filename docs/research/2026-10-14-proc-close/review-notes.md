# The coordinator's notes on Gemini's review of the close-out

Status: review notes (history, not authority). From the coordinator, 2026-10-14. The review is
`gemini-review.md` at `9c33e825c`; decisions row 383 records the rulings it led to.

## 1. The one thing to know

The review's three main findings hold, and its probe reproduces. Several of its names and paths
are wrong, and two of its proposals contradict the tree or a ruling. The corrected plan is
`prompt.md` (rewritten after this review).

## 2. What holds, checked against the tree

| Finding | Check | Result |
| --- | --- | --- |
| The two modules' definition blocks lie outside `BlockRows` | the probe, re-run by the coordinator: `lean-slot.sh lake env lean docs/research/2026-10-14-proc-close/probes/Probes.lean` | exit 0; every `#guard` passes; `[false, false, false, true]` for the Queue's four bodies, `[false, false, true]` for Semaphore's three |
| An invocation and its inlining agree at no single budget | the probe's controls A and B | both pass: the inlining at `k` cuts where the invocation at `k + 1` answers, and the inlining at `k + 1` answers where the invocation at `k + 1` cuts |
| The tops the plan builds on are proved | the probe's 14 `#plan_status` lines | each reports `proved; nearest []` |
| The definition connectors differ from the expansion claims | `tools/ProofGraph/Registry.lean`: the open parts of `queue-expansion-agrees` and `semaphore-expansion-agrees` relate the expansion to the model | confirmed |
| CX4 is proved | `call_arm`, `invoke_arm`, `param_arm` and `hop_typed` in `src/Effect4/Laws/Program/Typed/Denotation.lean` | confirmed |
| HO-5 is a planned slice | `docs/research/2026-10-09-program-parameters.md`: "HO-5: Pool and Semaphore services", a method with parameters | confirmed |

## 3. What the review gets wrong

| The review says | The tree says |
| --- | --- |
| define `Eff.relocate` and `Eff.shift` as new folds (F7) | `Eff.weaken` exists, generated (`src/Effect4/Program/Fold.lean`, with `weaken_eq_cata_eff`), and `check_weaken` types it (`src/Effect4/Program/Typing.lean`). Only parameter substitution is new. A second shift would duplicate a representation |
| G10 is `layer_refines` | G10 is SynchronizedRef's claim from Semaphore's claim alone (row 382 (3)) |
| row 382 (1) is `H9Blocks` and the to-do | row 382 (1) is contextual refinement of a module's model |
| row 382 (2) introduces `ModuleDecl` | no such declaration exists; the module form of row 331 (6) is still to be designed |
| the module form comes before closures (its stages 4 and 5) | the module form is a record of closures (rows 381 (3), 382 (2)), so closures come first |
| `RefinesB` relates two programs | right for G7, too narrow for row 382 (1): a module's model is a handler, not a program. The order is defined on meaning trees, and `RefinesB` is its pullback (row 383 (1)) |
| `Point.call : Option CallReturn` | `call : CallId` (`src/Effect4/Program/Compile.lean`) |
| `SynchronizedRef.withLock` | no such operation; SynchronizedRef's `modify` uses `Semaphore.withPermits` (`src/Effect4/Library/SynchronizedRef/Ops.lean`) |
| `Effects.Program.Approx` in `src/Effect4/Laws/Machine/Program.lean` | it lives in the `effects` package, `Effects/Coalgebra/System.lean` |
| `hop_typed` in `StackCertificates.lean`; `PointTyped` in `Residual.lean`; `admittedErrTy` in `Definitions.lean` | `Typed/Denotation.lean`; `Typed/Admission.lean`; `Eff.lean` |
| CX3 under `type-system` | no concept has that id; `check_replace`, its neighbour, is placed under `initial-algebras-folds` (R14) |

## 4. What the corrected plan keeps from the review

- The budget sandwich as the step law of G7, and the convergence form as its statement.
- The congruence cases by rung: the block fragment now, SCOPE-1's constructors, CONC-1's.
- The two new connector claims, composed with the expansion claims by transitivity.
- HO-5 and PROC-7 before the module form.
- One stage for closures, the activation stack and SCOPE-1's stage 0.

## 5. Round 2: Gemini's review of the mathematics

The review is `gemini-math-review.md` at `96bc22eaf`. The coordinator re-ran its probe:
`lean-slot.sh lake env lean docs/research/2026-10-14-proc-close/probes/MathProbes.lean`, exit 0,
no error, no warning, no `sorry`. Decisions row 385 records the rulings.

### 5.1 What holds, checked against the tree

| Finding | Check |
| --- | --- |
| `Step.Lift` relates two finished steps only at one equal value, so `IsSim` cannot relate an implementation's stores to a model's state | `Effects/Coalgebra/Step.lean`: `Lift.done (value : A)` on both sides |
| `System.peel` always steps, so a budget cut becomes a finished value, not a cut | `Effects/Coalgebra/Run.lean`: `peel … := fun state => some (Program.peel …)` |
| the prototype order (`PeelStepRel`, `PeelSim`) composes and is sound for every host | the probe's `PeelSim.comp` and `PeelSim.sound_host` compile |
| a client can compare handles only by `sameHandle`: equality and arithmetic refuse them | `NativeAtom.eval` (`src/Effect4/Machine/Term.lean`): `.eq` goes through `intEq`, which answers `none` on a handle; the probe's `sameHandle_renaming_invariant` |
| waiting has three transitions (attempt, signal, withdrawal) and two wrappers; a `waitRetry` wake reserves nothing | `src/Effect4/Library/Waiting.lean`; the probe's model runs for the Queue and Semaphore |
| Semaphore admits barging: `takeIfAvailable` can take the permit before a woken waiter retries | the probe's Semaphore run (row 259) |
| one generic step agreement can hold an existing one unchanged | the probe's `refObjectSpec_stepsAgree`, from `ref_steps_agree`; shown for Ref only |
| the queue-workers claims rest on three planned goals | the probe's `#plan_status`: `jobs_step`, `rest_step`, `logs_history` |
| the masks are outside the block meaning today | `blockAlgB` answers `outsideExit` for them; SCOPE-1's stage 1 already plans them |

### 5.2 What the review gets wrong

| The review says | The tree says |
| --- | --- |
| `call_arm`, `invoke_arm` and `param_arm` are open goals in `Typed/BlockArms.lean` | no such file exists; the three are proved in `Typed/Denotation.lean` (round 1's own `#plan_status`) |
| a numbering G1 to G9 (closures, `ModuleDecl`, a Queue module, a Semaphore module) | the tree's G7 to G10 are the inlining law, `check_subst`, `resolve_typed` and SynchronizedRef's claim; the review's numbering is its own |
| its restatement of §3's eleven corrections | several are restated wrongly (for example "`ModuleDecl` is a new structure that G6 introduces"; §3 says no such declaration exists) |
| Latch's await uses `waitAnswer` | no Latch module uses the shared wrapper (`src/Effect4/Library/Latch/` has no use of it) |
| the masks block G8 and G9 | G8 (`check_subst`) and G9 (`resolve_typed`) are typing statements; only G10 needs the masks |
| close the many-fiber claims directly on the machine | that is a proof per program, with a program's own invariants (the review itself names one for the crew). The generic theorems on the meaning stay, and the direct proofs are the control route |
| no logical relation for higher-order state is needed, because values hold no closures | true today; D2 adds closures. D2's closures are first-order data (a code address and captured values), so the first-order argument should extend: D2 must show it |
