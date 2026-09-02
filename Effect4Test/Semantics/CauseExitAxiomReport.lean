import Effect4.Semantics.Cause
import Effect4.Semantics.Exit

/-!
# Cause and Exit kernel dependency report

Every authored public theorem named by `test/contracts/cause-exit.contract.md`
is listed exactly once, in contract order. The accepted ceiling is no
dependency, `propext`, or `propext` with `Quot.sound`; `Classical.choice` and
project-local axioms are not admitted.

This report is breaker-owned and red until the fenced declarations exist.
-/

/-! ## A1 — annotations (census: cause.annotations) -/

#print axioms Effect4.ReasonAnnotations.keys_eq
#print axioms Effect4.ReasonAnnotations.keys_nodup
#print axioms Effect4.ReasonAnnotations.lookup_eq
#print axioms Effect4.ReasonAnnotations.ext
#print axioms Effect4.ReasonAnnotations.empty_entries
#print axioms Effect4.ReasonAnnotations.lookup_empty
#print axioms Effect4.ReasonAnnotations.annotate_entries
#print axioms Effect4.ReasonAnnotations.annotate_empty
#print axioms Effect4.ReasonAnnotations.annotate_keys
#print axioms Effect4.ReasonAnnotations.lookup_annotate_kept
#print axioms Effect4.ReasonAnnotations.lookup_annotate_new
#print axioms Effect4.ReasonAnnotations.lookup_annotate_overwrite
#print axioms Effect4.ReasonAnnotations.lookup_annotate_absent
#print axioms Effect4.ReasonAnnotations.order_retained
#print axioms Effect4.Reason.host_memory_refused

/-! ## A2 — the reason tag alphabet (census: exit.reason-alphabet) -/

#print axioms Effect4.ReasonTag.all_nodup
#print axioms Effect4.ReasonTag.mem_all
#print axioms Effect4.ReasonTag.cases_receipt

/-! ## A3 — reasons (census: cause.reason-fail, cause.reason-die,
cause.reason-interrupt, exit.reason-alphabet) -/

#print axioms Effect4.Reason.tag_fail
#print axioms Effect4.Reason.tag_die
#print axioms Effect4.Reason.tag_interrupt
#print axioms Effect4.Reason.annotations_fail
#print axioms Effect4.Reason.annotations_die
#print axioms Effect4.Reason.annotations_interrupt
#print axioms Effect4.Reason.error_fail
#print axioms Effect4.Reason.error_die
#print axioms Effect4.Reason.error_interrupt
#print axioms Effect4.Reason.defect_fail
#print axioms Effect4.Reason.defect_die
#print axioms Effect4.Reason.defect_interrupt
#print axioms Effect4.Reason.fail_inj
#print axioms Effect4.Reason.die_inj
#print axioms Effect4.Reason.interrupt_inj
#print axioms Effect4.Reason.cases_receipt
#print axioms Effect4.Reason.tag_mem_all
#print axioms Effect4.Reason.annotate_tag
#print axioms Effect4.Reason.annotate_annotations

/-! ## A4 — the flat cause (census: cause.flat-reasons,
rule.cause-has-no-structure) -/

#print axioms Effect4.Cause.ext
#print axioms Effect4.Cause.eq_iff
#print axioms Effect4.Cause.eq_iff_pointwise
#print axioms Effect4.Cause.empty_reasons
#print axioms Effect4.Cause.fail_reasons
#print axioms Effect4.Cause.die_reasons
#print axioms Effect4.Cause.interrupt_reasons
#print axioms Effect4.Cause.annotate_reasons

/-! ## A5 — first-occurrence deduplication (census: cause.combine-union) -/

#print axioms Effect4.Cause.dedup_nil
#print axioms Effect4.Cause.dedup_cons
#print axioms Effect4.Cause.mem_dedup
#print axioms Effect4.Cause.dedup_nodup
#print axioms Effect4.Cause.dedup_of_nodup

/-! ## A6 — causeCombine (census: cause.combine-union,
rule.cause-has-no-structure) -/

#print axioms Effect4.Cause.combine_empty_left
#print axioms Effect4.Cause.combine_empty_right
#print axioms Effect4.Cause.combine_reasons
#print axioms Effect4.Cause.mem_combine
#print axioms Effect4.Cause.combine_no_new_reason
#print axioms Effect4.Cause.combine_order
#print axioms Effect4.Cause.combine_nodup
#print axioms Effect4.Cause.combine_self

/-! ## A7 — causeSquash (census: cause.squash) -/

#print axioms Effect4.Squashed.cases_receipt
#print axioms Effect4.Cause.squash_error
#print axioms Effect4.Cause.squash_defect
#print axioms Effect4.Cause.squash_interrupted
#print axioms Effect4.Cause.squash_empty
#print axioms Effect4.Cause.squash_emptyCause_iff
#print axioms Effect4.Cause.squash_fail
#print axioms Effect4.Cause.squash_die
#print axioms Effect4.Cause.squash_interrupt
#print axioms Effect4.Cause.squash_fail_over_die

/-! ## A8 — exits (census: exit.success-failure, cause.finalizer-merge,
scope.exit-as-void-all) -/

#print axioms Effect4.Exit.cases_receipt
#print axioms Effect4.Exit.success_ne_failure
#print axioms Effect4.Exit.success_inj
#print axioms Effect4.Exit.failure_inj
#print axioms Effect4.Exit.void_eq
#print axioms Effect4.Exit.isSuccess_success
#print axioms Effect4.Exit.isSuccess_failure
#print axioms Effect4.Exit.cause_success
#print axioms Effect4.Exit.cause_failure
#print axioms Effect4.Exit.causeReasons_success
#print axioms Effect4.Exit.causeReasons_failure
#print axioms Effect4.Exit.mergeFinalizer_success
#print axioms Effect4.Exit.mergeFinalizer_success_failure
#print axioms Effect4.Exit.mergeFinalizer_failure_success
#print axioms Effect4.Exit.mergeFinalizer_failure_failure
#print axioms Effect4.Exit.restoreAfterFinalizer_success_finalizer
#print axioms Effect4.Exit.restoreAfterFinalizer_failure_failure
#print axioms Effect4.Exit.restoreAfterFinalizer_success_failure
#print axioms Effect4.Exit.asVoidAll_reasons
#print axioms Effect4.Exit.asVoidAll_nil
#print axioms Effect4.Exit.asVoidAll_all_success
#print axioms Effect4.Exit.asVoidAll_failure
#print axioms Effect4.Exit.asVoidAll_empty_cause
#print axioms Effect4.Exit.asVoidAll_keeps_duplicates
