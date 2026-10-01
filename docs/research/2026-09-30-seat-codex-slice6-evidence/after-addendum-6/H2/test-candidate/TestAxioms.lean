import Test.Program.TypedResidual
import Test.Counterexamples.Machine.Semantics.AsyncHookContract
import Test.Counterexamples.Machine.Semantics.TrivialPosts
import Test.Program.TypedControl
import Test.Program.TypedStack
import Test.Counterexamples.Machine.Semantics.ValueMembership
import Test.Counterexamples.Machine.Semantics.M6Capstone
import Test.Program.LoadedAdmission
import Test.Program.H2PartOne

#print axioms Test.Program.TypedResidual.unguard_inversion_rejects_unadmitted
#print axioms Test.Program.TypedResidual.finishFinalizer_inversion_rejects_unadmitted
#print axioms Test.Counterexamples.AsyncHookContract.cancellation_exit
#print axioms Test.Counterexamples.AsyncHookContract.sleep_stack_rejected
#print axioms Test.Counterexamples.TrivialPosts.joinAll_typed
#print axioms Test.Counterexamples.TrivialPosts.modify_typed
#print axioms Test.Counterexamples.TrivialPosts.joinsFiber_typed
#print axioms Test.Program.TypedControl.cancel_typed
#print axioms Test.Program.TypedControl.cancel_interrupt_typed
#print axioms Test.Program.TypedControl.sleep_stack_accepted
#print axioms Test.Program.TypedControl.natCatch_typed
#print axioms Test.Program.TypedControl.natToBool_typed
#print axioms Test.Program.TypedControl.leakyGuard_rejected
#print axioms Test.Program.TypedControl.unguard_payload_rejected
#print axioms Test.Program.TypedStack.catch_accepted
#print axioms Test.Program.TypedStack.catch_walk
#print axioms Test.Program.TypedStack.preempted_walk
#print axioms Test.Program.TypedStack.wrong_middle
#print axioms Test.Counterexamples.Machine.Semantics.ValueMembership.refProg_typedF
#print axioms Test.Counterexamples.Machine.Semantics.ValueMembership.getProg_typedF
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.bad_not_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1.loaded_code
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1.finished_untyped
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1.halted_bad_exit_rejected
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1.bad_generated_command_rejected
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1.join_delivery_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1.await_delivery_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.loaded_code
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.command_payload
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.OldObserve.emitted_refused
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.EarlyStep.mEnd_not_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.EarlyDecision.mFired_not_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1TerminalAmendment.saved_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1TerminalAmendment.result_not_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.callback_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.old_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.output_not_typed
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.raw_output_untyped
#print axioms Test.Program.LoadedAdmission.fork_admitted
#print axioms Test.Program.LoadedAdmission.lookup_typed
#print axioms Test.Program.LoadedAdmission.service_admitted
#print axioms Test.Program.LoadedAdmission.memoAwait_typed
#print axioms Test.Program.TypedControl.natErr_exitOk
#print axioms Test.Program.TypedControl.exitOk_nat
#print axioms Test.Program.TypedControl.natErr_shape
#print axioms Test.Program.TypedControl.exitOk_unit
#print axioms Test.Program.LoadedAdmission.context_of_fits
#print axioms Test.Counterexamples.Machine.Semantics.M6Capstone.H1HaltAmendment.oldSaved_of_saved
#print axioms Test.Program.H2PartOne.base_badName_still_fits
#print axioms Test.Program.H2PartOne.clean_still_allows_badName
#print axioms Test.Program.H2PartOne.badName_refused
#print axioms Test.Program.H2PartOne.notImplemented_refused
#print axioms Test.Program.H2PartOne.bad_current_code_refused
#print axioms Test.Program.H2PartOne.notImplemented_current_code_refused
#print axioms Test.Program.H2PartOne.ordinary_die_shape
#print axioms Test.Program.H2PartOne.user_die_admitted
#print axioms Test.Program.H2PartOne.user_current_code_admitted
#print axioms Test.Program.H2PartOne.missingService_admitted_at_any_type
#print axioms Test.Program.H2PartOne.missingService_empty_admitted
#print axioms Test.Program.H2PartOne.missingService_nonempty_admitted
#print axioms Test.Program.H2PartOne.missingService_current_code_admitted
#print axioms Test.Program.H2PartOne.interrupt_admitted
