# Foundations slice 5 preflight stop receipt

The coordinator must resolve CE-010/011/012 before slice 5 can proceed. A checker-typed
sleep reaches a cleanup stack that the frozen contracts cannot admit. The counterexamples
are checked; the production proof contracts were restored to the reviewed base. No M4
proof, new production obligation or replacement semantic rule is claimed by this checkpoint.

## Base, head and scope

- Base: `fc638550f1b1790b016324661ccfaae8d34bd30d` (reviewed divergence integration and retarget).
- Checked counterexample head: `2a00ce296a17dbef84197d8b8d84e8dbec0884ee`.
- Branch/worktree: `codex/foundations-slice-5`, `/private/tmp/effect4-foundations-slice-5`.
- The following documentation commit adds this receipt, the proposed amendment and evidence.
- Nothing was pushed. Reporting U-01 upstream remains the owner's action.

The source commit changes exactly `Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean`,
its import in `Test/All.lean`, and three rows in `Test/Counterexamples/REGISTER.md`.
`src/`, generated output, the host harness and OCaml are byte-identical to the base.

## Result and smallest amendment

[The proposed amendment](2026-09-23-foundations-slice5-contract-amendment.md) gives the exact
old/new async cause quantifier, the single guard protocol row to reopen, the control-admission
boundary to repair, and the positive and negative acceptance cases. This is an owner proposal,
not an amendment silently applied to a frozen theorem.

The ordinary program `.perform .sleep (.lit (.nat 1))` checks at Unit/never, parks at token 0
with exactly the async cleanup and identity answer frames, and returns Unit when its timer
fires. Those are bounded controls. `sleep_stack_rejected` proves that no intermediate types
make those two frames compose under the frozen async hook clause, at any world. It is not
merely a failed search for a proof or a hand-constructed unreachable frame.

The three retained failures are:

- CE-010: an interrupt-containing cause may also carry an untyped Fail, but the hook's
  quantifier demands a typed cancellation for all such causes.
- CE-011: the `guard_` post is `True`, so protocol typing must accept a failure reply to an
  `onSuccess` guard. A correctly typed interrupt-only input does not fix this problem.
- CE-012: `ControlAdmitted` quantifies over all store replies even when the operation's post
  excludes them. It therefore rejects generated sleep cancellation independently of CE-011.

The generic no-run-premise `popR_typed` payload is not refuted by this result. Its actual
source/hook admission is blocked. A theorem under impossible hook premises cannot substitute
for admitting the reachable sleep case.

## Statements and gates

| Surface | Before | This checkpoint |
| --- | --- | --- |
| Production `FrameAccepts`, `SavedOk`, `ResumeOk` | original slice 2 interfaces | byte-identical; the R3 attempt is retained as evidence only |
| Production `frameProtocols` | `True` stubs | byte-identical; no impossible concrete hook clause promoted |
| Production `Ψ_F`, `ControlAdmitted`, `TypedProg` | M3a definitions | byte-identical; their admission gaps are proved in the counterexample module |
| `Typed.M4Stack` / `Typed.M5Hooks` | absent | absent; a checked declaration prototype with ceilings 4 and 1 is retained outside the production graph, then withdrawn because preflight failed |
| Assembly, Keeps, M6 | not landed | not started after the stop; no forecast count reported |
| U-01 and runtime agreement | integrated divergence | unchanged |
| Unique production obligation ledger | 342 total, 333 proved, 9 open | 342 total, 333 proved, 9 open; 262 paired, 80 without a namesake, 0 mismatches |

Every declaration compiled from the new counterexample module, including auxiliaries, was
checked by `Audit.lean`: 33 declarations at `[propext, Quot.sound]`. The complete per-declaration
output is `ledger-and-axioms-2.log` and the extracted list is `axioms.json`. The twelve named
proofs are also in that audit; the test source prints its central axiom reports. No trust
exception, `sorry` or native proof evaluator was added.

## Evidence and commands

Evidence root: `2026-09-23-foundations-slice5-evidence/`. `run-check.py` retains the full output,
working directory, `LEAN_NUM_THREADS=1`, command, elapsed time and exit code in `commands.jsonl`.
Logs are stored with the `.gz` suffix; `compressed-logs.json` maps the original names
below to their compressed files and checksums. Failed attempts remain diagnostic evidence only. `counterexamples.log` is the fresh successful
build of the final retained file against the restored base; `ledger-and-axioms-2.log` is the
successful complete module-axiom and production-ledger audit.

| log | exact command | exit |
| --- | --- | --- |
| `contracts.log` | `lake build Effect4.Laws.Program.Typed.Contracts Effect4.Laws.Program.Typed.Residual` | 1 |
| `contracts-2.log` | `lake build Effect4.Laws.Program.Typed.Contracts Effect4.Laws.Program.Typed.Residual` | 1 |
| `stack-statements.log` | `lake build Effect4.Laws.Program.Typed.Stack` | 1 |
| `stack-statements-2.log` | `lake build Effect4.Laws.Program.Typed.Stack` | 1 |
| `stack-statements-3.log` | `lake build Effect4.Laws.Program.Typed.Stack` | 1 |
| `stack-statements-4.log` | `lake build Effect4.Laws.Program.Typed.Stack` | 0 |
| `async-hook-preflight.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/AsyncHookProbe.lean` | 1 |
| `async-hook-preflight-2.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/AsyncHookProbe.lean` | 1 |
| `async-hook-preflight-3.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/AsyncHookProbe.lean` | 0 |
| `restored-residual.log` | `lake build Effect4.Laws.Program.Typed.Residual` | 0 |
| `async-hook-preflight-4.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/AsyncHookProbe.lean` | 1 |
| `async-hook-preflight-5.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/AsyncHookProbe.lean` | 1 |
| `counterexamples.log` | `lake build Test.Counterexamples.Machine.Semantics.AsyncHookContract` | 0 |
| `ledger-and-axioms.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/Audit.lean` | 1 |
| `ledger-and-axioms-2.log` | `lake env lean docs/research/2026-09-23-foundations-slice5-evidence/Audit.lean` | 0 |
| `production-unchanged.log` | `git diff --exit-code fc638550f1b1790b016324661ccfaae8d34bd30d -- src generated harness ocaml` | 0 |
| `diff-check.log` | `git diff --check` | 0 |

The original prototype compiled its R3 interfaces and four open stack statements plus one
open hook statement before the semantic preflight refuted admission. Those files are saved
under `attempted/` with `.txt` suffixes and are not library sources. The intermediate parsing,
namespace, positivity and elaboration failures are retained and confer no evidence. The
final test reproduces the counterexamples without importing that prototype.

`production-unchanged.log` verifies the production and generated file fence. `diff-check.log`
records the whitespace check. No new full sweep was run: the slice stopped before any
production implementation, and the new module plus its exact axiom/ledger audit were checked.
The divergence's four full acceptance checks remain the earlier implementation's evidence;
this receipt does not present them as a slice 5 completion run.

The nine historical open names are unchanged:

- `Effect4.Api.M1Origin.source_fork_site`
- `Effect4.Api.TraceFacts.M1Trace.step_agrees`
- `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`
- `Effect4.Api.TraceFacts.M1Trace.reachable_agrees`
- `Effect4.Api.M1Origin.source_two_race_sites`
- `Effect4.Api.M1Origin.source_forkScoped_site`
- `Effect4.Api.M1Origin.source_race_site`
- `Effect4.Api.M1Origin.source_forkIn_site`
- `Effect4.Run.M1Trace.observe_replace_trace`

## Handoff

The slice 5 brief §1 requires a stop on a checked false frozen contract or a reachable case
that it refuses. Continuing needs the bounded proof-contract amendment above, including
`Typed/Admission.lean` and the named `Ψ_F.guard_` row that the current write fence excludes.
There is no requested runtime amendment and no proposal for a run premise. After a ruling,
fast-forward this branch to the coordinator's recorded head, freeze/check the replacement
contracts, and resume the original hard proofs, assembly, M6 declarations and packet checks.
