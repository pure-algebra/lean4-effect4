# Proposed owner amendment: H2 test migration

Two extra existing bodies are measured failures, with checked false-statement counterexamples. Twenty-five is the inventory of proposed test migrations, **not** a measured failure count. The separate proposed patch has not been compiled or applied. All eight input hashes still match the live tree.

Retain the eight named production-body repairs. Permit the two helper statement amendments below, and local ExitOk proof migrations in the 25 named test bodies in this table, only where fresh compiler attribution establishes the need. Permit the separately listed new adapters and controls. Report every actual body repair. An existing-body failure outside this inventory stops H2 again. Keep base Membership, runtime behavior, historical reviewed judgments and the held missingService clause unchanged.

- `TypedControl.cancel_typed`: retain clean and add `shape : NoShapeDefect (EffTy.pure .unit) (.failure cause)`. No interrupt-only restriction.
- `LoadedAdmission.lookup_typed`: add `isContext : ∃ ctx, Val.context? v = some ctx`, retaining the existing ServicesFit implication. No key-presence premise.

Direct callers: cancel_interrupt_typed and sleep_stack_accepted call cancel_typed; service_admitted calls lookup_typed. Three further statements only substitute ExitOk in the stack relation: sleep_stack_accepted, catch_accepted and wrong_middle. Other existing statements remain unchanged.

| File | Proposed existing bodies |
| --- | --- |
| `Test/Program/TypedResidual.lean` | `unguard_inversion_rejects_unadmitted`, `finishFinalizer_inversion_rejects_unadmitted` |
| `Test/Counterexamples/Machine/Semantics/AsyncHookContract.lean` | `cancellation_exit`, `sleep_stack_rejected` |
| `Test/Counterexamples/Machine/Semantics/TrivialPosts.lean` | `joinAll_typed`, `modify_typed`, `joinsFiber_typed` |
| `Test/Program/TypedControl.lean` | `cancel_typed`, `cancel_interrupt_typed`, `sleep_stack_accepted`, `natCatch_typed`, `natToBool_typed`, `leakyGuard_rejected`, `unguard_payload_rejected` |
| `Test/Program/TypedStack.lean` | `catch_accepted`, `catch_walk`, `preempted_walk`, `wrong_middle` |
| `Test/Counterexamples/Machine/Semantics/ValueMembership.lean` | `refProg_typedF`, `getProg_typedF` |
| `Test/Counterexamples/Machine/Semantics/M6Capstone.lean` | `bad_not_typed` |
| `Test/Program/LoadedAdmission.lean` | `fork_admitted`, `lookup_typed`, `service_admitted`, `memoAwait_typed` |

New declarations are separate: four TypedControl adapters, LoadedAdmission.context_of_fits, and fourteen declarations in Test/Program/H2PartOne.lean. The exact names and bodies are in PROPOSED-test-migrations/PROPOSED-test-migrations.patch. These are proposed local proof/control additions, not broader implementation authority. The patch is retained for review; the measured stop prevents applying it now.

Suggested validation after approval: apply the checked eight-body library change, run narrow production builds and actual ceiling prints, then compile the named direct test consumers with fresh per-body error attribution before each permitted repair. Run all named controls and print every changed/new theorem's axioms. Preserve the earlier counterexamples independently. Do not infer whole-machine safety or mark part two repaired.
