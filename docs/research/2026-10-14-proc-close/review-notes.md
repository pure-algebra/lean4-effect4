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
