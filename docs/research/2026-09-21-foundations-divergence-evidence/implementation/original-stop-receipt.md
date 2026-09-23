# Foundations divergence receipt: stopped at E4-SCHED-CE-009

The divergence is not implemented. The unchanged compiled failure consumer cannot return
an updated failure in the same step: it retains the exit supplied before the stack walk.
The packet's explicit stop condition applies. E4-SCHED-CE-009 is retained as a checked
counterexample; slice 5 has not started. The coordinator must approve the consumer changes
in the amendment below before the runtime work resumes.

## Base, delivery and scope

- Base: `439f27f368465355b24428690fec9215027d2052`, the packet's final-text commit.
- Verified code head: `18373ad39ef28b9f8c6fd2440067c2827dbd0fde` (counterexample and evidence).
  The following documentation commit adds this receipt; neither commit changes runtime code.
- Branch: `codex/foundations-divergence`.
- Worktree: `/private/tmp/effect4-foundations-divergence`.
- No runtime source, generated output, pinned expectation, obligation declaration, gate
  ceiling, owner register, `docs/STATE.md` or `README.md` changed. Nothing was pushed or
  merged. The runtime still has the old escape behavior.

Authority: the [divergence brief](2026-09-21-codex-brief-foundations-divergence-slice.md)
§5 says: “If the frame machine's walk cannot carry the sanitized exit without a second
change to the evaluator, stop, retain the case as `E4-SCHED-CE-009`, and report.”
Its §1 permits only the runtime changes in §2. The amendment here is a proposal,
not an additional ruling or authorization.

## Checked obstruction

`FramePop` has `answer`, `popped`, `events` and `fiber`; it does not carry a delivered exit.
`popFrom` and `passPushed` receive a demand and skip flag, not the exit being delivered.
The current primitive is present in `fiber.current`, but the consumers keep separate exit
arguments. Merely changing that current primitive does not change those arguments.

The counterexample is
[`InterruptCarrier.lean`](../../Test/Counterexamples/Machine/Semantics/InterruptCarrier.lean):

| Statement | What it establishes | Axioms |
| --- | --- | --- |
| `original_ne_sanitized` | `Fail 42` and the recorded interrupt are distinct causes | none |
| `finished_uses_supplied_exit` | For every native interpreter, saved frame, cause and optional supplied exit, any terminal result of `resumeCause` equals the supplied exit, or the original cause when no exit was supplied | `[propext]` |
| `cannot_finish_sanitized` | For every saved frame, the unchanged consumer cannot finish with the interrupt when its supplied exit is `Fail 42` | `[propext]` |
| `sanitized_current_is_ignored` | An exhausted frame whose current code already contains the interrupt still returns the supplied `Fail 42` | `[propext]` |
| `masked_catch_returns_original` | A mask restoration followed by the preempted catch finishes with the original failure | `[propext]` |
| `remasked_handler_receives_original` | When a later mask permits another handler to run, the unchanged consumer passes the original cause even if current code already carries the interrupt | `[propext]` |

`finished_uses_supplied_exit` unfolds `resumeCause` alone and leaves `getCont` opaque.
Thus changing which result the walk returns does not repair its terminal branch.
The existing `deferred` and `replacement` answers produce a running frame, not the required
terminal result in that step. This is a statement about that consumer and step; it is not a
claim that every possible redesign is impossible.

The local saved-state equations do not claim source reachability. E4-SCHED-CE-008 remains
the separate reachable-program witness. Its fixtures and CE-006/007 are unchanged because
no runtime fix landed.

Three consumers retain the old exit:

| Consumer | Source at base | Use outside the walk |
| --- | --- | --- |
| `FrameFiber.resumeCause` | `src/Effect4/Machine/Frames.lean:2423` | Terminal exit and yielded event; `armE` arguments; finalizer events |
| `evaluatePrim.finalizerOr` | `src/Effect4/Machine/Fibers.lean:1154` | `finalizerProgram`, restoring continuation and finalizer event |
| `Program.exitScoped` | `src/Effect4/Program/Compile.lean:1606` | `storesCloseScopeUnsafe`, finalizer event and restored exit |

The first row is established by the Lean theorems. The latter two are source-inspection
findings, not new universal theorems.

## Smallest proposed amendment

Authorize the following additional plumbing within the divergence slice:

1. Pass the delivered failure into the compiled walk and expose its updated value in the
   returned pop result. `FramePop` is the proposed explicit carrier; the exit supplied to
   the walk is authoritative, rather than an inference from unrelated current code.
2. At an answering failure arm discarded under preemption, update that carried failure
   with `Cause.combine (stripFail cause) ic`. Continue the same walk with it. A guard miss
   leaves it unchanged. This is the already ruled sanitization, not a different rule.
3. Update `FrameFiber.resumeCause`, `evaluatePrim.finalizerOr` and `Program.exitScoped` to
   use the returned failure consistently when finishing, invoking the next handler,
   constructing cleanup, recording its exit, and restoring it. The amended fence must
   therefore include `Machine/Fibers.lean` and `Program/Compile.lean`, as well as the
   additional consumer code in `Machine/Frames.lean`.
4. Permit the corresponding statement adjustments for carrier threading and the affected
   consumer agreement proofs, including `Laws/Program/Simulation/Walk.lean` and
   `Deliver.lean`. Keep the final `RuntimeR.run_eq_ref` observation and trust ceiling
   unchanged. Regenerate the affected representations and OCaml only through their
   existing producers, as the packet already requires.

The amendment must account for terminal delivery, a later re-masked handler, finalizers
and scoped cleanup. Replacing the skipped frame with another executable failure is not
a substitute: it adds a running result where the specified walk finishes in the same
step. All other runtime behavior remains under the original fence.

## Verification and evidence

Evidence directory: [`2026-09-21-foundations-divergence-evidence/`](2026-09-21-foundations-divergence-evidence/).
All Lean commands ran with `LEAN_NUM_THREADS=1` from the assigned worktree.

| Command | Exit | Evidence |
| --- | --- | --- |
| `lake env lean -M4096 -DwarningAsError=true docs/research/2026-09-21-foundations-divergence-evidence/CarrierRed.lean` | 1, expected | `carrier-red.log`: the desired equality fails |
| `lake env lean -M4096 -DwarningAsError=true Test/Counterexamples/Machine/Semantics/InterruptCarrier.lean` | 0 | `carrier-green.log`: all six theorem axiom reports |
| `lake build Test.Counterexamples.Machine.Semantics.InterruptCarrier` | 0 | `narrow-build.log`: 275 jobs, including the newly compiled counterexample |
| `lake build Test.All` | 0 | `test-all.log.gz`: 702 jobs; the modified test root was freshly compiled |
| `lake env lean -M4096 -DwarningAsError=true docs/research/2026-09-21-foundations-divergence-evidence/Audit.lean` | 0 | `audit.log`: exact proposition checks, current unique ledger and every open name |
| `git diff --check` | 0 | `diff-check.log` |
| `git diff --exit-code HEAD -- src generated ocaml harness docs/core/decisions.md docs/STATE.md README.md` | 0 | `runtime-unchanged.log` |

The fresh `Test.All` gate checked **485 modules and 67,199 declarations**. Every semantic
and test declaration remains within `[propext, Quot.sound]`; the existing metaprogramming
exceptions remain 15 modules and 29 named declarations. The root gate reports 138
API/utility modules and 204 Laws-only modules, every library source reachable, with no
Laws import from `Effect4`.

The unique production ledger is **342 total; 333 proved; 9 open**, at ceiling 9, unchanged
by this work. No proof-obligation declaration or ceiling was added, removed or amended.
The exact open names printed by this run are:

- `Effect4.Api.M1Origin.source_fork_site`
- `Effect4.Api.TraceFacts.M1Trace.step_agrees`
- `Effect4.Program.Guard.M4Handshake.parkHandshake_reachable`
- `Effect4.Api.TraceFacts.M1Trace.reachable_agrees`
- `Effect4.Api.M1Origin.source_two_race_sites`
- `Effect4.Api.M1Origin.source_forkScoped_site`
- `Effect4.Api.M1Origin.source_race_site`
- `Effect4.Api.M1Origin.source_forkIn_site`
- `Effect4.Run.M1Trace.observe_replace_trace`

A diagnostic audit importing the whole test root counted 344 statements because
`Test/Machine/Runtime/ArenaContract.lean` declares the two existing test-only obligations
`Effect4.Machine.ArenaRed.Obligations.inserting_poke_fails_absent` and
`Effect4.Machine.ArenaRed.Obligations.scopes_fail_dense`. That output is retained as
`audit-test-inclusive.log`; it is not the production count. `Audit.lean` uses the same
production import scope as the previous foundations receipts, while the full trust and
module-closure gate runs in `Test.All`.

The red control attempts the desired terminal equality with an already sanitized current
primitive and fails. The green controls prove the opposite behavior and the universal
consumer property. The failed proof-development attempt is retained separately and is not
proof evidence: its temporary `sorryAx` output came from an elaboration failure, not an
accepted declaration. The first audit attempt omitted the full test root and was correctly
rejected by the unchanged module-closure gate; verification then used `Test.All`.

No generated file was regenerated, and no expected value was flipped. `make gen`,
`make check`, `make check-ocaml`, `make check-truth` and `make check-census` are not claimed
for an unimplemented divergence. The counterexample is wired into `Test/All.lean`; its
registered row records the additional consumer scope that must be approved.


## Changed files

- `Test/Counterexamples/Machine/Semantics/InterruptCarrier.lean`: the six checked statements.
- `Test/All.lean`: one import, immediately after `InterruptEscape`.
- `Test/Counterexamples/REGISTER.md`: one new row, E4-SCHED-CE-009.
- `docs/research/2026-09-21-foundations-divergence-evidence/`: the red input, ledger audit,
  build and axiom output, diagnostic attempts, and unchanged-runtime checks.
- This receipt.

The full test build log is stored as gzip to preserve its raw tabular output, including
trailing empty TSV columns, without introducing whitespace errors in the patch.
Decompress with `gzip -dc docs/research/2026-09-21-foundations-divergence-evidence/test-all.log.gz`.
The uncompressed SHA-256 is `eec2d2b2655594722f0b67b85cb984963c236a16655727b3cd78703e969bfb92`.
The compressed file was round-tripped byte for byte.
