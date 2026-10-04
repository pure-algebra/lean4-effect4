import Effect4.Laws.Program.Typed.Commands.Clauses.All
import Effect4.Laws.Program.Progress
import Effect4.Laws.Program.Handles.Term
import Effect4.Laws.Machine.Witnesses
import Test.Program.ProtocolPosts

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Typed

-- Machine/Stores.lean
#print axioms FnName.updateTerm_agrees
#print axioms FnName.updateSomeTerm_agrees
#print axioms FnName.modifyTerm_agrees
#print axioms FnName.modifySomeTerm_agrees
#print axioms refStep_update
#print axioms refStep_update_applies_once
#print axioms refStep_modify
#print axioms refStep_modifySome_none
#print axioms refStep_modifySome_eq_modify
#print axioms refStep_updateSomeAndGet_some
#print axioms refStep_updateSomeAndGet_none
#print axioms updateSomeAndGet_ne_getAndUpdateSome
-- Laws/Machine/TermHandles.lean (moved, names kept)
#print axioms Effect4.Program.Typed.zipNames_columns
#print axioms Effect4.Program.Typed.recordParts?_eq_some
#print axioms Effect4.Program.Val.tupleAt?_mem
#print axioms Effect4.Program.tupleAt_handles
#print axioms Effect4.Program.RecordHandles.build
#print axioms Effect4.Program.RecordHandles.read
#print axioms Effect4.Program.RecordHandles.set
#print axioms Effect4.Program.RawHandles.lit_toVal_handles
#print axioms Effect4.Program.RawHandles.valOfErr_handles
#print axioms Effect4.Program.RawHandles.queryTag_handles
#print axioms Effect4.Program.RawHandles.queryError_handles
#print axioms Effect4.Program.RawHandles.handles_list
#print axioms Effect4.Program.RawHandles.asList_handles
#print axioms Effect4.Program.RawHandles.nativeAtom_handles
#print axioms Effect4.Program.RawHandles.evalTerm_handles
#print axioms Effect4.Program.RawHandles.evalTerms_handles
-- Laws/Machine/RefKernel.lean
#print axioms refStep_eq_refStepOf
#print axioms RefKernel.Frames.keeps
#print axioms mem_flatMap_handles
#print axioms ofOption_ident_handles
#print axioms ofTuple2_ident_handles
#print axioms termKernel_frames
#print axioms SyncOp.refKernel_handles
-- Laws/Machine/StoresLaws.lean
#print axioms SyncOp.validIn_mono
#print axioms Val.validIn_framesClosed
#print axioms SyncOp.refArgs_validIn
#print axioms SyncOp.refKernel_validIn
#print axioms syncOpStep_isSome_of_kernel
#print axioms syncOpStep_isSome_of_valid
#print axioms refStep_valid
#print axioms syncOpStep_wf
-- Laws/Machine/Handles.lean
#print axioms Val.keys_subset_of_handles
#print axioms Val.keys_framesClosed
#print axioms SyncOp.refArgs_keys
#print axioms SyncOp.refKernel_keys
#print axioms refStep_keys
-- Laws/Program/Handles/Term.lean (proofs now read Val.keys_subset_of_handles)
#print axioms Effect4.Program.nativeAtom_keys
#print axioms Effect4.Program.RecordHandles.build_keys
#print axioms Effect4.Program.RecordHandles.read_keys
#print axioms Effect4.Program.RecordHandles.set_keys
#print axioms Effect4.Program.RawHandles.evalTerm_registered
-- Laws/Machine/Witnesses.lean
#print axioms Effect4.Machine.Witnesses.w7_update_answers_void
#print axioms Effect4.Machine.Witnesses.w7_modify_some_writes_back_the_read
#print axioms Effect4.Machine.Witnesses.w7_update_some_and_get_rereads
-- Typed/Residual.lean
#print axioms TermMaps.mono
#print axioms storePre_mono
-- Typed/Adequacy.lean
#print axioms CellsTyped.wf_step
#print axioms kernel_step
#print axioms termKernel_typed
#print axioms decode_option
#print axioms decode_pair
#print axioms decode_pairOption
#print axioms kernel_typed
#print axioms kernel_cellImplements
#print axioms refUpdate_implements
#print axioms refGetAndUpdate_implements
#print axioms refUpdateAndGet_implements
#print axioms refUpdateSome_implements
#print axioms refGetAndUpdateSome_implements
#print axioms refUpdateSomeAndGet_implements
#print axioms refModify_implements
#print axioms refModifySome_implements
-- Typed/Denotation.lean
#print axioms modify_nat
#print axioms modifySome_nat
#print axioms fits_total
#print axioms fits_partialUpdate
#print axioms nat_of_equiv
#print axioms fits_toOption
#print axioms updateTerm_maps
#print axioms updateSomeTerm_maps
#print axioms modifyTerm_maps
#print axioms modifySomeTerm_maps
#print axioms syncRow_typed
-- Progress.lean
#print axioms Denote.StoreFits.step
#print axioms kernel_term_agrees
#print axioms progress
-- Clauses
#print axioms clause_kernel
#print axioms storeClauses
#print axioms deliver_preserves
#print axioms reachable_typed
-- Test/Program/ProtocolPosts.lean, the restated Modify section
#print axioms Test.Program.ProtocolPosts.Modify.refModify_bool_frontier
#print axioms Test.Program.ProtocolPosts.Modify.refModifySome_bool_answer
#print axioms Test.Program.ProtocolPosts.Modify.adequacy_false_refModify
#print axioms Test.Program.ProtocolPosts.Modify.refModify_pre_refuses
#print axioms Test.Program.ProtocolPosts.Modify.refModifySome_pre_refuses
#print axioms Test.Program.ProtocolPosts.Modify.refModifySome_bool_typed
#print axioms Test.Program.ProtocolPosts.Modify.modify_other_type_pre
#print axioms Test.Program.ProtocolPosts.Modify.modify_other_type_step
#print axioms Test.Program.ProtocolPosts.Modify.modify_other_type_post
#print axioms Test.Program.ProtocolPosts.Modify.termMaps_oneWorld_not_mono
#print axioms Test.Program.ProtocolPosts.Modify.termMaps_initial_refuses
