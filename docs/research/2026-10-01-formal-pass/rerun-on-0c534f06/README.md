# The formal pass's load-bearing probes rerun on the merged tree (`0c534f06`)

Written 2026-10-01 by the coordinator, after Codex's G, H1, H2 part one and row 39 merged at
`0c534f06` (the seats and verifiers wrote against `ea5b28b5`, whose sources are `c42f4a46`'s).
Each probe was compiled alone through the one-compiler lock with
`lake env lean -M6144 -DwarningAsError=true <probe>` (`run.sh`; logs beside this note).

**The one thing.** Seven of the nine fail to elaborate on the merged tree, and every first error
is a shape mismatch, not a refuted theorem: H1 changed `TypedState` (the `CodeInert` clause, the
scheduler and observer facts, `StepPreserves` under `m.stuck = none`) and H2 moved the typed exit
positions from `FitsExit` to `ExitOk`, so the probes' constructions of typed states and their
`change`/`rewrite` patterns no longer match. The two that need neither (the amended `Fits` model
over `Membership.lean` and `TypeAlgebra.lean`; the `ExitOk` overload check) pass unchanged. So
every finding the synthesis carries into a landing seat is re-established on the merged tree
first, by that seat, before its repair; the findings themselves are not contradicted by the merge
(nothing in G, H1, H2 part one or row 39 touches the raw-order comparison inside `Fits`, the
one-world frame clauses, the await-by-value post, or the residue dropped at a budget cut).

| Probe | exit | errors | axiom lines | first error |
| --- | ---: | ---: | ---: | --- |
| `algebra/probes/P2KripkeTyping.lean` | 1 | 8 | 16 | Application type mismatch: The argument |
| `algebra/verify-StepLoop.lean` | 1 | 30 | 17 | Tactic `rewrite` failed: Did not find an occurrence of the pattern |
| `proofs/probes/StaleCode.lean` | 1 | 1 | 20 | Application type mismatch: The argument |
| `proofs/verify-probes/VerifyAwaitLoad.lean` | 1 | 4 | 6 | Type mismatch |
| `proofs/verify-probes/VerifySplit.lean` | 1 | 2 | 13 | Application type mismatch: The argument |
| `types/M5CounterProbe.lean` | 1 | 1 | 7 | 'change' tactic failed, pattern |
| `types/verify-CapstoneProbe.lean` | 1 | 1 | 5 | 'change' tactic failed, pattern |
| `types/verify-AmendedFitsProbe.lean` | 0 | 0 | 10 | (none) |
| `organization/verify-ExitOkOverload.lean` | 0 | 0 | 0 | (none) |

**What survives as-is, by theorem (from the axiom lines in the logs).** The machine-level facts
elaborate at the ceiling on the merged tree: probe A's `reach6`, `window6`, `finished7`,
`residue6_shape`, `residue6_machine`, `exitsTyped6/7`, `admitted_noAnswer`; the verifier's
`m6_stuck_none`, `m6_root_running`, `running_clause_vacuous_at_m6`, `budget7_is_fuel_frontier`,
`finished9`, `m9_root_stale`, `worldValid_not_upward_closed`; the types seat's `prog3_typed`,
`child_cert`, `leaf_false`, `fiber_inv`; the capstone-implies-load bridge; the algebra seat's
Kripke-closed judgment with `stackAcceptsK_mono`, `stackAcceptsK_now`, `frameAcceptsK_mono`,
`storePre_mono`, `envTyped_mono`. What fails is each probe's last step, the one that unfolds the
typed state or a typed exit position by its old shape (`untyped_of_stale` and everything after
it; `root_code_refused`; `m5_false`; `stackAccepts_not_mono`'s bad-frame construction;
`typedProg_mono`'s guard case), so those theorems print `sorryAx`. Re-establishing them is a
restatement against `CodeInert`, the scheduler facts and `ExitOk`, not a new argument: the
window fiber is running, not halted, and has no queued `finish`, so H1's clause still types it by
its stale code; H2's `ExitOk` strengthens the exit positions and weakens nothing the
counterexamples rely on.
