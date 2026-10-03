# T obligations after the API tranche

This is a checked-source disposition, not a replacement for the central semantics registry.
Base `8913519b` already contains Claude's T1/T2 work. The present tranche adds useful bounded
T4/T5 connections and progress prerequisites; it closes no additional full T item.

| Item | Verified reach and remaining work |
| --- | --- |
| T1 | Already proved: `Typed.exits_hasTy` and `root_exit_hasTy` in `Laws/Program/Typed/Results.lean`. Checked program, ghost `AdmittedTape`, existing empty-table runtime/reference connection, and recorded exits. Does not assert an exit exists. |
| T2 | Already proved: `exitHandles_valid` in `Typed/Commands/Clauses/All.lean`, registered against unchanged M7. `ExitHandlesValid` retains lawful/checked source and `RReachable` (answer-free reference reachability); requirement rows need not be closed. This is validity of recorded successes, not host admission. |
| T3 | Open. The new runnable reader, `Run.work`, exact selection laws and checked one-control helper expose useful premises and consumers. They do not prove an enabled successor, no lost wakeups, termination, or a successful verdict at arbitrary fuel. |
| T4 | Existing `reachable_typed` / `obs_typed` require ghost admission. The new successful-session connector follows executable preflight/receipt on a non-stuck machine to the actual prepared value and establishes membership only for shape-decided answer columns. Token/world correspondence, capability-bearing columns, failures and residual-machine connection remain. The retained reserved-defect counterexample blocks a blanket admission-to-ExitOk assertion. |
| T5 | New `Denote.StraightEq` supports composition and actual execution comparison for exit plus complete stores on `Straight`, at independently sufficient budgets. Loops, scheduling, nonempty host tables, traces, a general preorder and arbitrary contexts remain outside it. |
| T6 | One-close `ScopeMachine.runState_complete` is existing local evidence. The requested run-wide finalizer identity/order invariant remains open. |
| T7 | Finite scheduling/flush results retain their explicit ready/uniqueness/budget hypotheses. General liveness still needs the appropriate scheduler and environment fairness assumptions. |
| T8 | The typed invariant still admits `missingService`; service presence must be connected through captured/saved frames under decision 117 before the stronger claim. |
| T9 | `run_eq_ref` in `Laws/Program/RuntimeR.lean` remains an empty-table/default-oracle connection. A table-aware reference/preparation relation is needed before exporting that connection to the host session. |

## Next work supported by the landed APIs

1. Resolve the exact permitted host-failure contract using the retained `badName`
   discriminator, then connect session associations to the typed token declarations.
   Reuse the accepted-success preparation theorem rather than duplicating admission.
2. State T3 over enabled machine work with explicit fuel and waiting conditions; the new
   selection theorem provides the concrete scheduler-side consumer. Keep environment
   responsiveness and eventual completion separate from one-step progress.
3. Extend semantic comparisons from the existing straight relation only after naming the
   observations for loops, scheduling and host answers. The current composition proof is a
   reusable base for source rewrites and future lowering; it makes no target claim.

Code-valued services still require the first-order clause representation and handler typing
rule described in the foundations plan. Nothing in this tranche stores Lean handlers as
program syntax or changes program-kind rows from their existing frontier behavior.
