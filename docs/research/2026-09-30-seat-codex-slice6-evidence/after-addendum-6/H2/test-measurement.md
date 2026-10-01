# H2 unchanged-test measurement

Root’s retained compiler logs currently locate 76 diagnostics in 43 existing theorem bodies. Of these, 41 have candidate body changes; 2 are downstream callers deliberately left unchanged by the candidate. These are observed compiler locations, not inferred permission exceptions.

| Stage | Exit | Diagnostics in unchanged tests | Distinct theorem bodies |
| --- | --- | --- | --- |
| unchanged-tests | 1 | 40 | 30 |
| unchanged-dependent-tests | 1 | 16 | 6 |
| unchanged-dependent-tests-2 | 1 | 20 | 7 |

The two additional caller diagnostics are `H1TerminalAmendment.typed` (line1247) and `typed_queued` (line1350). Both consume `saved_typed`, whose statement changes from FitsExit to ExitOk. They remain part of the measured failure inventory; successful recompilation after that helper statement migration must establish that no body repair is needed.

Failed elaboration emits some `#print axioms` records containing `sorryAx`. Those records are retained as diagnostics and are **not proof evidence**. Import-blocked files are reported separately and counted only after their unchanged contents reach elaboration.

## By theorem

| Existing theorem | Diagnostic line(s) | Candidate body changes |
| --- | --- | --- | --- |
| `Test.Counterexamples.AsyncHookContract.cancellation_exit` | 69, 70 | yes |
| `Test.Counterexamples.AsyncHookContract.sleep_stack_rejected` | 90 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.EarlyDecision.mFired_not_typed` | 1020 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.EarlyStep.mEnd_not_typed` | 901 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1.await_delivery_typed` | 368 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1.bad_generated_command_rejected` | 323 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1.finished_untyped` | 287 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1.halted_bad_exit_rejected` | 297 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1.join_delivery_typed` | 363 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1.loaded_code` | 108 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.callback_typed` | 1723, 1723 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.old_typed` | 1788 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.output_not_typed` | 1876 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.raw_output_untyped` | 2104 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.typed` | 1748 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1TerminalAmendment.result_not_typed` | 1318 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1TerminalAmendment.saved_typed` | 1231, 1233 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1TerminalAmendment.typed` | 1247 | no: called helper statement changes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.H1TerminalAmendment.typed_queued` | 1350 | no: called helper statement changes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.command_payload` | 738 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.emitted_refused` | 781 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.loaded_code` | 639 | yes |
| `Test.Counterexamples.Machine.Semantics.M6Capstone.bad_not_typed` | 42 | yes |
| `Test.Counterexamples.Machine.Semantics.ValueMembership.getProg_typedF` | 939, 939, 944, 965, 974, 974 | yes |
| `Test.Counterexamples.Machine.Semantics.ValueMembership.refProg_typedF` | 919, 919 | yes |
| `Test.Counterexamples.TrivialPosts.joinAll_typed` | 59 | yes |
| `Test.Counterexamples.TrivialPosts.joinsFiber_typed` | 97, 97 | yes |
| `Test.Counterexamples.TrivialPosts.modify_typed` | 72 | yes |
| `Test.Program.LoadedAdmission.fork_admitted` | 54, 48 | yes |
| `Test.Program.LoadedAdmission.lookup_typed` | 118, 119, 121, 121, 122, 122 | yes |
| `Test.Program.LoadedAdmission.memoAwait_typed` | 179, 179 | yes |
| `Test.Program.LoadedAdmission.service_admitted` | 130, 135, 148, 148 | yes |
| `Test.Program.TypedControl.cancel_typed` | 55, 58 | yes |
| `Test.Program.TypedControl.leakyGuard_rejected` | 139 | yes |
| `Test.Program.TypedControl.natCatch_typed` | 90, 90, 98, 98 | yes |
| `Test.Program.TypedControl.natToBool_typed` | 111, 111, 114, 119, 119 | yes |
| `Test.Program.TypedControl.sleep_stack_accepted` | 75, 76, 76 | yes |
| `Test.Program.TypedControl.unguard_payload_rejected` | 146 | yes |
| `Test.Program.TypedResidual.finishFinalizer_inversion_rejects_unadmitted` | 93 | yes |
| `Test.Program.TypedResidual.unguard_inversion_rejects_unadmitted` | 83 | yes |
| `Test.Program.TypedStack.catch_accepted` | 30, 30 | yes |
| `Test.Program.TypedStack.catch_walk` | 46, 46 | yes |
| `Test.Program.TypedStack.preempted_walk` | 64, 64 | yes |

Two candidate adaptations have no initial compiler diagnostic:

- `Test.Program.TypedControl.cancel_interrupt_typed` initially calls the old `cancel_typed` signature successfully. Its added shape argument follows the required helper statement amendment.
- `Test.Program.TypedStack.wrong_middle` initially proves its explicitly written FitsExit-stack statement. Migrating that statement to ExitOk requires the candidate payload construction and projection.

Thus 43 observed failing bodies and 43 repaired bodies are different sets: 41 overlap, two observed callers need only the helper statement repair, and two further body adaptations follow statement migrations.

Exact commands, per-diagnostic source paths, import failures, and excluded failed-elaboration axiom prints are in `test-measurement.json`; original outputs are copied into `measurement-evidence/`. This seat only read root’s logs and wrote temporary reports.
