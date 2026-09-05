import Effect4.Machine.Exit
import Effect4.Machine.Scope

/-!
# Scope runtime kernel dependency report

Every authored public theorem named by `Test/contracts/scope.contract.md` is
listed exactly once, in contract order. The accepted ceiling is no dependency,
`propext`, or `propext` with `Quot.sound`; `Classical.choice` and
project-local axioms are not admitted.

This report is breaker-owned and red until the fenced declarations exist.
-/


/-! ## S0 — the finalizer strategy label (census: scope.make, scope.close-parallel) -/

#print axioms Effect4.FinalizerStrategy.all_nodup
#print axioms Effect4.FinalizerStrategy.mem_all
#print axioms Effect4.FinalizerStrategy.cases_receipt

/-! ## S1 — the scope state machine (census: scope.states) -/

#print axioms Effect4.ScopeState.cases_receipt
#print axioms Effect4.ScopeState.entries_empty
#print axioms Effect4.ScopeState.entries_openEmpty
#print axioms Effect4.ScopeState.entries_openInline
#print axioms Effect4.ScopeState.entries_openMap
#print axioms Effect4.ScopeState.entries_closed
#print axioms Effect4.ScopeState.isOpen_empty
#print axioms Effect4.ScopeState.isOpen_openEmpty
#print axioms Effect4.ScopeState.isOpen_openInline
#print axioms Effect4.ScopeState.isOpen_openMap
#print axioms Effect4.ScopeState.isOpen_closed
#print axioms Effect4.ScopeState.isClosed_eq
#print axioms Effect4.ScopeState.closingExit_closed
#print axioms Effect4.ScopeState.closingExit_of_not_closed
#print axioms Effect4.ScopeState.openEmpty_ne_openMap_nil

/-! ## S2 — the scope carrier and its observations (census: scope.states, scope.make) -/

#print axioms Effect4.Scope.make_strategy
#print axioms Effect4.Scope.make_state
#print axioms Effect4.Scope.make_finalizers
#print axioms Effect4.Scope.makeDefault_eq
#print axioms Effect4.Scope.makeDefault_strategy
#print axioms Effect4.Scope.finalizers_eq
#print axioms Effect4.Scope.finalizerKeys_eq
#print axioms Effect4.Scope.finalizerCount_eq
#print axioms Effect4.Scope.finalizerCount_not_open
#print axioms Effect4.Scope.key_freshness_refused

/-! ## S3 — the keyed insertion-ordered finalizer table (census: scope.add-finalizer,
scope.remove-finalizer) -/

#print axioms Effect4.Scope.tableInsert_new
#print axioms Effect4.Scope.tableInsert_existing
#print axioms Effect4.Scope.tableInsert_keys_of_mem
#print axioms Effect4.Scope.tableInsert_nodup
#print axioms Effect4.Scope.tableRemove_eq
#print axioms Effect4.Scope.tableRemove_keys
#print axioms Effect4.Scope.tableRemove_nodup

/-! ## S4 — registration (census: scope.add-finalizer, scope.add-after-closed) -/

#print axioms Effect4.Scope.addUnsafe_strategy
#print axioms Effect4.Scope.addUnsafe_empty
#print axioms Effect4.Scope.addUnsafe_openEmpty
#print axioms Effect4.Scope.addUnsafe_openInline
#print axioms Effect4.Scope.addUnsafe_openMap
#print axioms Effect4.Scope.addUnsafe_closed
#print axioms Effect4.Scope.addUnsafe_promotes
#print axioms Effect4.Scope.addUnsafe_finalizers
#print axioms Effect4.Scope.addUnsafe_keys_nodup
#print axioms Effect4.Scope.addExit_open
#print axioms Effect4.Scope.addExit_closed
#print axioms Effect4.Scope.addExit_closed_registers_nothing

/-! ## S5 — removal (census: scope.remove-finalizer) -/

#print axioms Effect4.Scope.removeUnsafe_strategy
#print axioms Effect4.Scope.removeUnsafe_inline_hit
#print axioms Effect4.Scope.removeUnsafe_inline_miss
#print axioms Effect4.Scope.removeUnsafe_openMap
#print axioms Effect4.Scope.removeUnsafe_not_open
#print axioms Effect4.Scope.removeUnsafe_keys
#print axioms Effect4.Scope.removeUnsafe_keys_nodup

/-! ## S6 — closing (census: scope.close-state-first, scope.close-lifo,
scope.close-sequential, scope.close-parallel, scope.close-merge,
rule.scope-close-lifo-state-first) -/

#print axioms Effect4.Scope.close_eq
#print axioms Effect4.Scope.close_state_independent_of_run
#print axioms Effect4.Scope.closeState_state
#print axioms Effect4.Scope.closeState_strategy
#print axioms Effect4.Scope.closeState_finalizers
#print axioms Effect4.Scope.closeState_isClosed
#print axioms Effect4.Scope.closeState_idempotent
#print axioms Effect4.Scope.close_closingExit
#print axioms Effect4.Scope.close_idempotent
#print axioms Effect4.Scope.close_twice
#print axioms Effect4.Scope.close_reentrant_add
#print axioms Effect4.Scope.closeOrder_eq
#print axioms Effect4.Scope.closeOrder_last_first
#print axioms Effect4.Scope.closeExits_eq
#print axioms Effect4.Scope.closeExits_reverse
#print axioms Effect4.Scope.closeExits_length
#print axioms Effect4.Scope.closeResult_nil
#print axioms Effect4.Scope.closeResult_single
#print axioms Effect4.Scope.closeResult_many
#print axioms Effect4.Scope.closeResult_reasons
#print axioms Effect4.Scope.closeResult_closed
#print axioms Effect4.Scope.close_strategy_irrelevant

/-! ## S7 — scope fork linkage (census: scope.fork-linkage) -/

#print axioms Effect4.Scope.fork_closed_parent
#print axioms Effect4.Scope.fork_closed_parent_child_exit
#print axioms Effect4.Scope.fork_open_parent
#print axioms Effect4.Scope.fork_child_finalizers
#print axioms Effect4.Scope.fork_parent_finalizers
#print axioms Effect4.Scope.fork_child_strategy
#print axioms Effect4.Scope.fork_shared_key
#print axioms Effect4.Scope.fork_detach

/-! ## S8 — the two brackets (census: scope.scoped, scope.acquire-release) -/

#print axioms Effect4.Scope.addAll_nil
#print axioms Effect4.Scope.addAll_cons
#print axioms Effect4.Scope.addAll_finalizers
#print axioms Effect4.Scope.make_addAll_finalizers
#print axioms Effect4.Scope.runScoped_eq
#print axioms Effect4.Scope.runScoped_fresh_scope
#print axioms Effect4.Scope.runScoped_state
#print axioms Effect4.Scope.runScoped_strategy
#print axioms Effect4.Scope.runScoped_empty
#print axioms Effect4.Scope.runScoped_lifo
#print axioms Effect4.Scope.acquireRelease_failure
#print axioms Effect4.Scope.acquireRelease_success
#print axioms Effect4.Scope.acquireRelease_registers
#print axioms Effect4.Scope.acquireRelease_closed_ambient
