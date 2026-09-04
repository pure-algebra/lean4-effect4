import Lean
import Lean.Util.CollectAxioms
import Effect4.Concurrency.Supervision
import Effect4.Semantics.Cause
import Effect4.Semantics.Exit
import Effect4.Runtime.Scope
import Effect4.Runtime.Runtime
import Effect4.Deep.Clauses
import Effect4.Deep.Stores
import Effect4.Deep.Layer
import Effect4.Deep.Witnesses
import Effect4.Context.ContextFamily

/-!
# Effect v4 fiber runtime coverage

This test-only checker joins the mechanical behaviour census of the pinned
`effect@4.0.0-rc.112` fiber runtime (`generated/effect-runtime-census.tsv`,
produced by `scripts/generate-effect-runtime-census.sh`) to the Lean
declarations that witness those behaviours.

The census keys are *observed runtime behaviours*, never "function X exists".
This module holds the frozen row list — one row per census id, carrying the
`PORT-MANIFEST.md` disposition, the declared coverage state, and the witness
declarations with their expected kernel dependency receipts. It fails the
build on a missing witness, a witness that is not a theorem, an axiom receipt
drift, a duplicate id, or an inconsistent disposition/coverage pairing.

Exact witness statements are frozen by the `#check (@name : proposition)`
ascriptions in the `StatementSnapshot` section below.
`scripts/check-effect-runtime-census.sh` cross-checks that the snapshot
names and the emitted witness rows are the same list, in the same order, so
the ascriptions cannot be deleted without failing the gate.

Nothing here adds to or removes from the `Effect4` surface. Since
2026-09-04 the fiber rows are witnessed by the reference machine
(`Effect4/Deep/Clauses.lean`, `Witnesses.lean`, `Stores.lean`, `Layer.lean`)
and the frame machine (`Effect4/Runtime/Runtime.lean`); the retired
scheduler and supervision calculi cite nothing here any more.
-/

open Lean Elab Command

namespace Effect4Test.Audit.RuntimeCoverage

universe u v

section StatementSnapshot

open Effect4

/-! The exact proposition each witness proves, frozen by ascription. A drift in
any statement is a `type mismatch` at the offending line. -/

/-! The Cause/Exit model witnesses. Statements are transcribed from the frozen
ascriptions of `Effect4Test/Semantics/CauseExitContract.lean`. -/

#check (@Effect4.Cause.eq_iff : forall {ε δ ι α : Type u} (left right : Cause ε δ ι α),
  left = right <-> left.reasons = right.reasons)

#check (@Effect4.Cause.ext : forall {ε δ ι α : Type u} {left right : Cause ε δ ι α},
  left.reasons = right.reasons -> left = right)

#check (@Effect4.Cause.eq_iff_pointwise :
  forall {ε δ ι α : Type u} (left right : Cause ε δ ι α),
    left = right <->
      (left.reasons.length = right.reasons.length /\
        forall index : Nat, left.reasons[index]? = right.reasons[index]?))

#check (@Effect4.Cause.combine_no_new_reason : forall {ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (self that : Cause ε δ ι α),
  reason ∈ (Cause.combine self that).reasons ->
    reason ∈ self.reasons \/ reason ∈ that.reasons)

#check (@Effect4.Reason.error_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).error? = some error)

#check (@Effect4.Reason.annotations_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).annotations = annotations)

#check (@Effect4.Reason.fail_inj : forall {ε δ ι α : Type u} (leftError rightError : ε)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.fail leftError leftAnnotations : Reason ε δ ι α) =
      Reason.fail rightError rightAnnotations <->
    leftError = rightError /\ leftAnnotations = rightAnnotations)

#check (@Effect4.Reason.defect_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).defect? = some defect)

#check (@Effect4.Reason.annotations_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).annotations = annotations)

#check (@Effect4.Reason.die_inj : forall {ε δ ι α : Type u} (leftDefect rightDefect : δ)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.die leftDefect leftAnnotations : Reason ε δ ι α) =
      Reason.die rightDefect rightAnnotations <->
    leftDefect = rightDefect /\ leftAnnotations = rightAnnotations)

#check (@Effect4.Cause.interrupt_reasons : forall {ε δ ι α : Type u}
  (interruptor : Option ι),
  (Cause.interrupt interruptor : Cause ε δ ι α).reasons =
    [Reason.interrupt interruptor ReasonAnnotations.empty])

#check (@Effect4.Reason.annotations_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι) (annotations : ReasonAnnotations α),
  (Reason.interrupt interruptor annotations : Reason ε δ ι α).annotations =
    annotations)

#check (@Effect4.Reason.interrupt_inj : forall {ε δ ι α : Type u}
  (leftInterruptor rightInterruptor : Option ι)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.interrupt leftInterruptor leftAnnotations : Reason ε δ ι α) =
      Reason.interrupt rightInterruptor rightAnnotations <->
    leftInterruptor = rightInterruptor /\
      leftAnnotations = rightAnnotations)

#check (@Effect4.Cause.combine_empty_left : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (that : Cause ε δ ι α),
  Cause.combine Cause.empty that = that)

#check (@Effect4.Cause.combine_empty_right : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α),
  Cause.combine self Cause.empty = self)

#check (@Effect4.Cause.combine_reasons : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons ≠ [] -> that.reasons ≠ [] ->
  (Cause.combine self that).reasons =
    Cause.dedup (self.reasons ++ that.reasons))

#check (@Effect4.Cause.mem_combine : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (self that : Cause ε δ ι α),
  reason ∈ (Cause.combine self that).reasons <->
    reason ∈ self.reasons \/ reason ∈ that.reasons)

#check (@Effect4.Cause.combine_self : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α),
  self.reasons.Nodup -> Cause.combine self self = self)

#check (@Effect4.Cause.combine_order : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons.Nodup -> that.reasons.Nodup ->
  (Cause.combine self that).reasons =
    self.reasons ++
      that.reasons.filter (fun reason => decide (reason ∉ self.reasons)))

#check (@Effect4.Cause.dedup_cons : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (rest : List (Reason ε δ ι α)),
  Cause.dedup (reason :: rest) =
    reason :: (Cause.dedup rest).filter (fun other => decide (other ≠ reason)))

#check (@Effect4.Cause.mem_dedup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (list : List (Reason ε δ ι α)),
  reason ∈ Cause.dedup list <-> reason ∈ list)

#check (@Effect4.Cause.dedup_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (list : List (Reason ε δ ι α)), (Cause.dedup list).Nodup)

#check (@Effect4.Cause.dedup_of_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (list : List (Reason ε δ ι α)), list.Nodup -> Cause.dedup list = list)

#check (@Effect4.Exit.mergeFinalizer_failure_failure : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (cause finalizerCause : Cause ε δ ι α),
  Exit.mergeFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause))

#check (@Effect4.Exit.restoreAfterFinalizer_failure_failure :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (cause finalizerCause : Cause ε δ ι α),
  Exit.restoreAfterFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause))

#check (@Effect4.Exit.mergeFinalizer_success_failure : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (value : β) (finalizerCause : Cause ε δ ι α),
  Exit.mergeFinalizer (Exit.success value) (Exit.failure finalizerCause) =
    Exit.failure finalizerCause)

#check (@Effect4.Exit.restoreAfterFinalizer_success_failure :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (value : β) (finalizerCause : Cause ε δ ι α),
  Exit.restoreAfterFinalizer (Exit.success value : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure finalizerCause)

#check (@Effect4.Cause.squash_error : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (error : ε) (rest : List ε),
  self.reasons.filterMap Reason.error? = error :: rest ->
    self.squash = Squashed.error error)

#check (@Effect4.Cause.squash_defect : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (defect : δ) (rest : List δ),
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = defect :: rest ->
    self.squash = Squashed.defect defect)

#check (@Effect4.Cause.squash_interrupted : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α),
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = [] ->
  self.reasons ≠ [] ->
    self.squash = Squashed.interruptedWithoutError)

#check (@Effect4.Cause.squash_emptyCause_iff : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α),
  self.squash = Squashed.emptyCause <-> self.reasons = [])

#check (@Effect4.Cause.squash_fail_over_die : forall {ε δ ι α : Type u} (error : ε)
  (defect : δ) (dieAnnotations failAnnotations : ReasonAnnotations α),
  (Cause.mk [Reason.die defect dieAnnotations,
      Reason.fail error failAnnotations] : Cause ε δ ι α).squash =
    Squashed.error error)

#check (@Effect4.ReasonAnnotations.keys_nodup : forall {α : Type u} (self : ReasonAnnotations α),
  self.keys.Nodup)

#check (@Effect4.Reason.annotate_annotations : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α) (extra : ReasonAnnotations α) (overwrite : Bool),
  (reason.annotate extra overwrite).annotations =
    reason.annotations.annotate extra overwrite)

#check (@Effect4.Reason.host_memory_refused :
  forall {ε α : Type u} (recall : ε -> ReasonAnnotations α) (left right : ε),
    left = right -> recall left = recall right)

#check (@Effect4.ReasonAnnotations.annotate_entries :
  forall {α : Type u} (self extra : ReasonAnnotations α) (overwrite : Bool),
    (self.annotate extra overwrite).entries =
      self.entries.map (fun entry =>
        if overwrite = true then
          match extra.lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) ++
      extra.entries.filter (fun entry => decide (entry.fst ∉ self.keys)))

#check (@Effect4.ReasonAnnotations.lookup_annotate_kept :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α),
    self.lookup key = some value ->
    (self.annotate extra false).lookup key = some value)

#check (@Effect4.ReasonAnnotations.lookup_annotate_overwrite :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α),
    extra.lookup key = some value ->
    (self.annotate extra true).lookup key = some value)

#check (@Effect4.Exit.cases_receipt : forall {β ε δ ι α : Type u}
  (self : Exit β ε δ ι α),
  (exists value, self = Exit.success value) \/
  (exists cause, self = Exit.failure cause))

#check (@Effect4.Exit.success_ne_failure : forall {β ε δ ι α : Type u} (value : β)
  (cause : Cause ε δ ι α),
  (Exit.success value : Exit β ε δ ι α) ≠ Exit.failure cause)

#check (@Effect4.Exit.success_inj : forall {β ε δ ι α : Type u} (left right : β),
  (Exit.success left : Exit β ε δ ι α) = Exit.success right <-> left = right)

#check (@Effect4.Exit.failure_inj : forall {β ε δ ι α : Type u}
  (left right : Cause ε δ ι α),
  (Exit.failure left : Exit β ε δ ι α) = Exit.failure right <-> left = right)

#check (@Effect4.Exit.cause_failure : forall {β ε δ ι α : Type u}
  (cause : Cause ε δ ι α),
  (Exit.failure cause : Exit β ε δ ι α).cause? = some cause)

#check (@Effect4.ReasonTag.all_nodup : ReasonTag.all.Nodup)

#check (@Effect4.ReasonTag.mem_all : forall tag : ReasonTag, tag ∈ ReasonTag.all)

#check (@Effect4.ReasonTag.cases_receipt : forall tag : ReasonTag,
  tag = ReasonTag.fail \/ tag = ReasonTag.die \/ tag = ReasonTag.interrupt)

#check (@Effect4.Reason.cases_receipt : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α),
  (exists error annotations, reason = Reason.fail error annotations) \/
  (exists defect annotations, reason = Reason.die defect annotations) \/
  (exists interruptor annotations,
    reason = Reason.interrupt interruptor annotations))

#check (@Effect4.Reason.tag_mem_all : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α), reason.tag ∈ ReasonTag.all)

#check (@Effect4.Exit.asVoidAll_reasons : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)),
  (Exit.asVoidAll exits).causeReasons = exits.flatMap Exit.causeReasons)

#check (@Effect4.Exit.asVoidAll_failure : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)) (reason : Reason ε δ ι α)
  (rest : List (Reason ε δ ι α)),
  exits.flatMap Exit.causeReasons = reason :: rest ->
    Exit.asVoidAll exits = Exit.failure (Cause.mk (reason :: rest)))

#check (@Effect4.Exit.asVoidAll_all_success : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)),
  (forall exit, exit ∈ exits -> exists value, exit = Exit.success value) ->
    Exit.asVoidAll exits = Exit.success ())

#check (@Effect4.Exit.void_eq : forall {ε δ ι α : Type u},
  (Exit.void : Exit Unit ε δ ι α) = Exit.success ())

/-! The Scope model witnesses. Statements are transcribed from the frozen
ascriptions of `Effect4Test/Runtime/ScopeContract.lean`. -/

#check (@Effect4.ScopeState.cases_receipt :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state = Effect4.ScopeState.empty \/
      state = Effect4.ScopeState.openEmpty \/
        (exists key finalizer, state = Effect4.ScopeState.openInline key finalizer) \/
          (exists table, state = Effect4.ScopeState.openMap table) \/
            (exists exit, state = Effect4.ScopeState.closed exit))

#check (@Effect4.ScopeState.entries_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.empty : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

#check (@Effect4.ScopeState.entries_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

#check (@Effect4.ScopeState.entries_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (key : κ) (finalizer : φ),
    (Effect4.ScopeState.openInline key finalizer :
      Effect4.ScopeState κ φ β ε δ ι α).entries = [(key, finalizer)])

#check (@Effect4.ScopeState.entries_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (table : List (κ × φ)),
    (Effect4.ScopeState.openMap table : Effect4.ScopeState κ φ β ε δ ι α).entries = table)

#check (@Effect4.ScopeState.entries_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).entries = [])

#check (@Effect4.ScopeState.isOpen_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.empty : Effect4.ScopeState κ φ β ε δ ι α).isOpen = false)

#check (@Effect4.ScopeState.isOpen_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)

#check (@Effect4.ScopeState.isOpen_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (key : κ) (finalizer : φ),
    (Effect4.ScopeState.openInline key finalizer :
      Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)

#check (@Effect4.ScopeState.isOpen_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (table : List (κ × φ)),
    (Effect4.ScopeState.openMap table : Effect4.ScopeState κ φ β ε δ ι α).isOpen = true)

#check (@Effect4.ScopeState.isOpen_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).isOpen = false)

#check (@Effect4.ScopeState.isClosed_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state.isClosed = true <-> exists exit, state = Effect4.ScopeState.closed exit)

#check (@Effect4.ScopeState.closingExit_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
    (Effect4.ScopeState.closed exit : Effect4.ScopeState κ φ β ε δ ι α).closingExit? =
      some exit)

#check (@Effect4.ScopeState.closingExit_of_not_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (state : Effect4.ScopeState κ φ β ε δ ι α),
    state.isClosed = false -> state.closingExit? = none)

#check (@Effect4.ScopeState.openEmpty_ne_openMap_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.ScopeState.openEmpty : Effect4.ScopeState κ φ β ε δ ι α) ≠
      Effect4.ScopeState.openMap [])

#check (@Effect4.Scope.finalizers_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizers = self.state.entries)

#check (@Effect4.Scope.finalizerKeys_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizerKeys = self.finalizers.map Prod.fst)

#check (@Effect4.Scope.finalizerCount_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.finalizerCount = self.finalizers.length)

#check (@Effect4.Scope.finalizerCount_not_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.isOpen = false -> self.finalizerCount = 0)

#check (@Effect4.FinalizerStrategy.all_nodup : Effect4.FinalizerStrategy.all.Nodup)

#check (@Effect4.FinalizerStrategy.mem_all :
  forall strategy : Effect4.FinalizerStrategy, strategy ∈ Effect4.FinalizerStrategy.all)

#check (@Effect4.Scope.make_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).strategy = strategy)

#check (@Effect4.Scope.make_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).state =
      Effect4.ScopeState.empty)

#check (@Effect4.Scope.make_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (strategy : Effect4.FinalizerStrategy),
    (Effect4.Scope.make strategy : Effect4.Scope κ φ β ε δ ι α).finalizers = [])

#check (@Effect4.Scope.makeDefault_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.makeDefault : Effect4.Scope κ φ β ε δ ι α) =
      Effect4.Scope.make Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.makeDefault_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.makeDefault : Effect4.Scope κ φ β ε δ ι α).strategy =
      Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.key_freshness_refused :
  forall {κ : Type u} {γ : Type u} (mint : γ -> κ) (left right : γ),
    left = right -> mint left = mint right)

#check (@Effect4.Scope.tableInsert_new : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∉ table.map Prod.fst ->
    Effect4.Scope.tableInsert table key finalizer = table ++ [(key, finalizer)])

#check (@Effect4.Scope.tableInsert_existing : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∈ table.map Prod.fst ->
    Effect4.Scope.tableInsert table key finalizer =
      table.map (fun entry => if entry.fst = key then (key, finalizer) else entry))

#check (@Effect4.Scope.tableInsert_keys_of_mem : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  key ∈ table.map Prod.fst ->
    (Effect4.Scope.tableInsert table key finalizer).map Prod.fst = table.map Prod.fst)

#check (@Effect4.Scope.tableInsert_nodup : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ) (finalizer : φ),
  (table.map Prod.fst).Nodup ->
    ((Effect4.Scope.tableInsert table key finalizer).map Prod.fst).Nodup)

#check (@Effect4.Scope.addUnsafe_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    (self.addUnsafe key finalizer).strategy = self.strategy)

#check (@Effect4.Scope.addUnsafe_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.empty ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openInline key finalizer)

#check (@Effect4.Scope.addUnsafe_openEmpty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openEmpty ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openInline key finalizer)

#check (@Effect4.Scope.addUnsafe_openInline :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (existing finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey existing ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openMap
          (Effect4.Scope.tableInsert [(existingKey, existing)] key finalizer))

#check (@Effect4.Scope.addUnsafe_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openMap table ->
      (self.addUnsafe key finalizer).state =
        Effect4.ScopeState.openMap (Effect4.Scope.tableInsert table key finalizer))

#check (@Effect4.Scope.addUnsafe_promotes :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (existing finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey existing -> existingKey ≠ key ->
      (self.addUnsafe key finalizer).finalizers =
        [(existingKey, existing), (key, finalizer)])

#check (@Effect4.Scope.addUnsafe_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = false -> key ∉ self.finalizerKeys ->
      (self.addUnsafe key finalizer).finalizers = self.finalizers ++ [(key, finalizer)])

#check (@Effect4.Scope.addUnsafe_keys_nodup :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.finalizerKeys.Nodup -> (self.addUnsafe key finalizer).finalizerKeys.Nodup)

#check (@Effect4.Scope.addUnsafe_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = true -> self.addUnsafe key finalizer = self)

#check (@Effect4.Scope.addExit_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.isClosed = false ->
      Effect4.Scope.addExit run self key finalizer =
        (self.addUnsafe key finalizer, Effect4.Exit.void))

#check (@Effect4.Scope.addExit_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ)
    (exit : Effect4.Exit β ε δ ι α),
    self.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.addExit run self key finalizer = (self, run finalizer exit))

#check (@Effect4.Scope.addExit_closed_registers_nothing :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ)
    (exit : Effect4.Exit β ε δ ι α),
    self.state = Effect4.ScopeState.closed exit ->
      (Effect4.Scope.addExit run self key finalizer).fst.finalizers = [])

#check (@Effect4.Scope.tableRemove_eq : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  Effect4.Scope.tableRemove table key =
    table.filter (fun entry => decide (entry.fst ≠ key)))

#check (@Effect4.Scope.tableRemove_keys : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  key ∉ (Effect4.Scope.tableRemove table key).map Prod.fst)

#check (@Effect4.Scope.tableRemove_nodup : forall {κ φ : Type u} [DecidableEq κ]
  (table : List (κ × φ)) (key : κ),
  (table.map Prod.fst).Nodup ->
    ((Effect4.Scope.tableRemove table key).map Prod.fst).Nodup)

#check (@Effect4.Scope.removeUnsafe_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    (self.removeUnsafe key).strategy = self.strategy)

#check (@Effect4.Scope.removeUnsafe_inline_hit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openInline key finalizer ->
      (self.removeUnsafe key).state = Effect4.ScopeState.openEmpty)

#check (@Effect4.Scope.removeUnsafe_inline_miss :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (existingKey key : κ) (finalizer : φ),
    self.state = Effect4.ScopeState.openInline existingKey finalizer -> existingKey ≠ key ->
      self.removeUnsafe key = self)

#check (@Effect4.Scope.removeUnsafe_openMap :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (table : List (κ × φ)) (key : κ),
    self.state = Effect4.ScopeState.openMap table ->
      (self.removeUnsafe key).state =
        Effect4.ScopeState.openMap (Effect4.Scope.tableRemove table key))

#check (@Effect4.Scope.removeUnsafe_not_open :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    self.isOpen = false -> self.removeUnsafe key = self)

#check (@Effect4.Scope.removeUnsafe_keys :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    key ∉ (self.removeUnsafe key).finalizerKeys)

#check (@Effect4.Scope.removeUnsafe_keys_nodup :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (key : κ),
    self.finalizerKeys.Nodup -> (self.removeUnsafe key).finalizerKeys.Nodup)

#check (@Effect4.Scope.close_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.close run self exit =
      (Effect4.Scope.closeState self exit, Effect4.Scope.closeResult run self exit))

#check (@Effect4.Scope.close_state_independent_of_run :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (leftRun rightRun : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.close leftRun self exit).fst =
      (Effect4.Scope.close rightRun self exit).fst)

#check (@Effect4.Scope.closeState_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeState self exit).state = Effect4.ScopeState.closed exit)

#check (@Effect4.Scope.closeState_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).strategy = self.strategy)

#check (@Effect4.Scope.closeState_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).finalizers = [])

#check (@Effect4.Scope.closeState_isClosed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeState self exit).isClosed = true)

#check (@Effect4.Scope.closeState_idempotent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.closeState self exit = self)

#check (@Effect4.Scope.close_closingExit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeState self exit).closingExit? = some exit)

#check (@Effect4.Scope.close_idempotent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.close run self exit = (self, Effect4.Exit.void))

#check (@Effect4.Scope.close_twice :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (first second : Effect4.Exit β ε δ ι α),
    Effect4.Scope.close run (Effect4.Scope.close run self first).fst second =
      ((Effect4.Scope.close run self first).fst, Effect4.Exit.void))

#check (@Effect4.Scope.close_reentrant_add :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (key : κ)
    (finalizer : φ),
    self.isClosed = false ->
      Effect4.Scope.addExit run (Effect4.Scope.closeState self exit) key finalizer =
        (Effect4.Scope.closeState self exit, run finalizer exit))

#check (@Effect4.Scope.closeResult_closed :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = true -> Effect4.Scope.closeResult run self exit = Effect4.Exit.void)

#check (@Effect4.Scope.closeOrder_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α),
    self.closeOrder = (self.finalizers.map Prod.snd).reverse)

#check (@Effect4.Scope.closeOrder_last_first :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Scope κ φ β ε δ ι α)
    (table : List (κ × φ)) (key : κ) (finalizer : φ),
    self.finalizers = table ++ [(key, finalizer)] ->
      self.closeOrder = finalizer :: (table.map Prod.snd).reverse)

#check (@Effect4.Scope.closeExits_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.closeExits run self exit =
      self.closeOrder.map (fun finalizer => run finalizer exit))

#check (@Effect4.Scope.closeExits_reverse :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.closeExits run self exit =
      self.finalizers.reverse.map (fun entry => run entry.snd exit))

#check (@Effect4.Scope.runScoped_lifo :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (registrations.map Prod.fst).Nodup ->
      Effect4.Scope.closeExits run
          ((Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
            Effect4.Scope κ φ β ε δ ι α).addAll registrations) bodyExit =
        registrations.reverse.map (fun entry => run entry.snd bodyExit))

#check (@Effect4.Scope.closeExits_length :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.closeExits run self exit).length = self.finalizers.length)

#check (@Effect4.Scope.closeResult_reasons :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.isClosed = false ->
      (Effect4.Scope.closeResult run self exit).causeReasons =
        (Effect4.Scope.closeExits run self exit).flatMap Effect4.Exit.causeReasons)

#check (@Effect4.FinalizerStrategy.cases_receipt :
  forall strategy : Effect4.FinalizerStrategy,
    strategy = Effect4.FinalizerStrategy.sequential \/
      strategy = Effect4.FinalizerStrategy.parallel)

#check (@Effect4.Scope.close_strategy_irrelevant :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (state : Effect4.ScopeState κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.close run
        ({ strategy := Effect4.FinalizerStrategy.parallel, state := state } :
          Effect4.Scope κ φ β ε δ ι α) exit).snd =
      (Effect4.Scope.close run
        ({ strategy := Effect4.FinalizerStrategy.sequential, state := state } :
          Effect4.Scope κ φ β ε δ ι α) exit).snd)

#check (@Effect4.Scope.closeResult_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α),
    self.finalizers = [] -> Effect4.Scope.closeResult run self exit = Effect4.Exit.void)

#check (@Effect4.Scope.closeResult_single :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α) (key : κ)
    (finalizer : φ),
    self.isClosed = false -> self.finalizers = [(key, finalizer)] ->
      Effect4.Scope.closeResult run self exit = run finalizer exit)

#check (@Effect4.Scope.closeResult_many :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u}
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (self : Effect4.Scope κ φ β ε δ ι α) (exit : Effect4.Exit β ε δ ι α)
    (first second : Effect4.Exit Unit ε δ ι α) (rest : List (Effect4.Exit Unit ε δ ι α)),
    self.isClosed = false ->
      Effect4.Scope.closeExits run self exit = first :: second :: rest ->
        Effect4.Scope.closeResult run self exit =
          Effect4.Exit.asVoidAll (first :: second :: rest))

#check (@Effect4.Scope.fork_closed_parent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) (exit : Effect4.Exit β ε δ ι α),
    parent.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.fork parent strategy key closeChild detachFromParent =
        (parent, ({ strategy := strategy, state := Effect4.ScopeState.closed exit } :
          Effect4.Scope κ φ β ε δ ι α)))

#check (@Effect4.Scope.fork_closed_parent_child_exit :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ) (exit : Effect4.Exit β ε δ ι α),
    parent.state = Effect4.ScopeState.closed exit ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.closingExit? =
        some exit)

#check (@Effect4.Scope.fork_open_parent :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      Effect4.Scope.fork parent strategy key closeChild detachFromParent =
        (parent.addUnsafe key closeChild,
          (Effect4.Scope.make strategy :
            Effect4.Scope κ φ β ε δ ι α).addUnsafe key detachFromParent))

#check (@Effect4.Scope.fork_child_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.finalizers =
        [(key, detachFromParent)])

#check (@Effect4.Scope.fork_parent_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false -> key ∉ parent.finalizerKeys ->
      (Effect4.Scope.fork parent strategy key closeChild detachFromParent).fst.finalizers =
        parent.finalizers ++ [(key, closeChild)])

#check (@Effect4.Scope.fork_child_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    (Effect4.Scope.fork parent strategy key closeChild detachFromParent).snd.strategy =
      strategy)

#check (@Effect4.Scope.fork_shared_key :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false ->
      key ∈ (Effect4.Scope.fork parent strategy key closeChild
          detachFromParent).fst.finalizerKeys /\
        key ∈ (Effect4.Scope.fork parent strategy key closeChild
          detachFromParent).snd.finalizerKeys)

#check (@Effect4.Scope.fork_detach :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (parent : Effect4.Scope κ φ β ε δ ι α) (strategy : Effect4.FinalizerStrategy)
    (key : κ) (closeChild detachFromParent : φ),
    parent.isClosed = false -> key ∉ parent.finalizerKeys ->
      ((Effect4.Scope.fork parent strategy key closeChild
        detachFromParent).fst.removeUnsafe key).finalizers = parent.finalizers)

#check (@Effect4.Scope.addAll_nil :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α), self.addAll [] = self)

#check (@Effect4.Scope.addAll_cons :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (entry : κ × φ) (rest : List (κ × φ)),
    self.addAll (entry :: rest) = (self.addUnsafe entry.fst entry.snd).addAll rest)

#check (@Effect4.Scope.addAll_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (self : Effect4.Scope κ φ β ε δ ι α) (registrations : List (κ × φ)),
    self.isClosed = false ->
      (self.finalizerKeys ++ registrations.map Prod.fst).Nodup ->
        (self.addAll registrations).finalizers = self.finalizers ++ registrations)

#check (@Effect4.Scope.make_addAll_finalizers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (strategy : Effect4.FinalizerStrategy) (registrations : List (κ × φ)),
    (registrations.map Prod.fst).Nodup ->
      ((Effect4.Scope.make strategy :
        Effect4.Scope κ φ β ε δ ι α).addAll registrations).finalizers = registrations)

#check (@Effect4.Scope.runScoped_eq :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.runScoped run registrations bodyExit =
      Effect4.Scope.close run
        ((Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
          Effect4.Scope κ φ β ε δ ι α).addAll registrations) bodyExit)

#check (@Effect4.Scope.runScoped_fresh_scope :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u},
    (Effect4.Scope.make Effect4.FinalizerStrategy.sequential :
      Effect4.Scope κ φ β ε δ ι α) =
      { strategy := Effect4.FinalizerStrategy.sequential,
        state := Effect4.ScopeState.empty })

#check (@Effect4.Scope.runScoped_state :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.runScoped run registrations bodyExit).fst.state =
      Effect4.ScopeState.closed bodyExit)

#check (@Effect4.Scope.runScoped_strategy :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (registrations : List (κ × φ)) (bodyExit : Effect4.Exit β ε δ ι α),
    (Effect4.Scope.runScoped run registrations bodyExit).fst.strategy =
      Effect4.FinalizerStrategy.sequential)

#check (@Effect4.Scope.runScoped_empty :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (bodyExit : Effect4.Exit β ε δ ι α),
    Effect4.Scope.runScoped run ([] : List (κ × φ)) bodyExit =
      (({ strategy := Effect4.FinalizerStrategy.sequential,
            state := Effect4.ScopeState.closed bodyExit } :
          Effect4.Scope κ φ β ε δ ι α),
        Effect4.Exit.void))

#check (@Effect4.Scope.acquireRelease_failure :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ)
    (cause : Effect4.Cause ε δ ι α),
    Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.failure cause) =
      (ambient, Effect4.Exit.void))

#check (@Effect4.Scope.acquireRelease_success :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β),
    Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.success value) =
      Effect4.Scope.addExit run ambient key release)

#check (@Effect4.Scope.acquireRelease_registers :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β),
    ambient.isClosed = false -> key ∉ ambient.finalizerKeys ->
      (Effect4.Scope.acquireRelease run ambient key release
        (Effect4.Exit.success value)).fst.finalizers =
          ambient.finalizers ++ [(key, release)])

#check (@Effect4.Scope.acquireRelease_closed_ambient :
  forall {κ φ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq κ]
    (run : φ -> Effect4.Exit β ε δ ι α -> Effect4.Exit Unit ε δ ι α)
    (ambient : Effect4.Scope κ φ β ε δ ι α) (key : κ) (release : φ) (value : β)
    (exit : Effect4.Exit β ε δ ι α),
    ambient.state = Effect4.ScopeState.closed exit ->
      Effect4.Scope.acquireRelease run ambient key release (Effect4.Exit.success value) =
        (ambient, run release exit))


/-! Supervision controller receipts. Source interpretation remains open in
SUPERVISION-PG-RC112; every joined runtime row is partial. -/

#check (@Effect4.Supervision.MaskMode.cases_receipt :
  forall mode : Effect4.Supervision.MaskMode, mode = .interruptible ∨ mode = .uninterruptible ∨ mode = .inherit)

#check (@Effect4.Supervision.ObserverMode.cases_receipt :
  forall mode : Effect4.Supervision.ObserverMode, mode = .awaitValue ∨ mode = .joinEffect)

#check (@Effect4.Supervision.ScopeMode.cases_receipt :
  forall mode : Effect4.Supervision.ScopeMode, mode = .forkIn ∨ mode = .fiberRunIn)

#check (@Effect4.Supervision.interruptCause_eq :
  forall {ε δ ι α : Type u} (encode : Effect4.FiberId -> ι) (requester : Option Effect4.FiberId) (annotations : Effect4.ReasonAnnotations α), (Effect4.Supervision.interruptCause encode requester annotations : Effect4.Cause ε δ ι α) = Effect4.Cause.annotate (Effect4.Cause.interrupt (requester.map encode)) annotations false)

#check (@Effect4.Supervision.RaceAllState.initial_eq :
  forall {β : Type v} {ε δ ι α : Type u}, forall entrants : List Effect4.FiberId, (Effect4.Supervision.RaceAllState.initial entrants : Effect4.Supervision.RaceAllState β ε δ ι α) = {unstarted := entrants, starting := none, live := [], remaining := entrants.length, failures := [], winner := none, accepted := none, cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false})

#check (@Effect4.Supervision.raceComplete_unknown :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α), child ∉ s.live -> Effect4.Supervision.raceComplete s child exit = s)

#check (@Effect4.Supervision.raceComplete_after_accepted :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (exit accepted : Effect4.Exit β ε δ ι α), child ∈ s.live -> s.accepted = some accepted -> Effect4.Supervision.raceComplete s child exit = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ exit.causeReasons, cleanup := s.cleanup.map (fun wait => if child ∈ Effect4.Supervision.WaitState.pending wait then {wait with published := wait.published ++ [child]} else wait)})

#check (@Effect4.Supervision.raceComplete_success :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (value : β), child ∈ s.live -> s.accepted = none -> Effect4.Supervision.raceComplete s child (.success value) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, winner := some (child, value), accepted := some (.success value), cleanupNeeded := !(s.live.filter (fun id => decide (id ≠ child))).isEmpty, requests := [], cleanup := none, cleanupRequested := false})

#check (@Effect4.Supervision.raceComplete_failure_last :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> s.remaining ≤ 1 -> Effect4.Supervision.raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons, accepted := some (.failure ⟨s.failures ++ cause.reasons⟩), cleanupNeeded := false, requests := [], cleanup := none, cleanupRequested := false})

#check (@Effect4.Supervision.raceComplete_failure_pending :
  forall {β : Type v} {ε δ ι α : Type u}, forall (s : Effect4.Supervision.RaceAllState β ε δ ι α) (child : Effect4.FiberId) (cause : Effect4.Cause ε δ ι α), child ∈ s.live -> s.accepted = none -> 1 < s.remaining -> Effect4.Supervision.raceComplete s child (.failure cause) = {s with live := s.live.filter (fun id => decide (id ≠ child)), remaining := s.remaining - 1, failures := s.failures ++ cause.reasons})

/-! The frame-machine witnesses. Statements are transcribed from the frozen
ascriptions of `Effect4Test/Runtime/FramesContract.lean`.

The `Effect4.Prim` and `Effect4.FrameFiber` telescopes carry seven type
parameters, and many of these statements quantify over all seven while naming
only some. The binder names are part of the frozen statement, so they are
transcribed as written rather than renamed to `_ν` to please the
unused-variable linter; the option below is scoped to this section. -/

set_option linter.unusedVariables false

#check (@Effect4.Arm.all_nodup : List.Nodup Effect4.Arm.all)

#check (@Effect4.Arm.mem_all : ∀ (arm : Effect4.Arm), arm ∈ Effect4.Arm.all)

#check (@Effect4.Arm.cases_receipt :
  ∀ (arm : Effect4.Arm), arm = Effect4.Arm.contA ∨ arm = Effect4.Arm.contE ∨ arm =
  Effect4.Arm.contAll)

#check (@Effect4.Arm.demandable_eq :
  Effect4.Arm.demandable = [Effect4.Arm.contA, Effect4.Arm.contE])

#check (@Effect4.Arm.contAll_not_demandable : ¬Effect4.Arm.contAll ∈ Effect4.Arm.demandable)

#check (@Effect4.Prim.cases_receipt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α), (∃
  value, self = Effect4.Prim.success value) ∨ (∃ cause, self = Effect4.Prim.failure cause) ∨ (∃
  thunk, self = Effect4.Prim.sync thunk) ∨ (∃ thunk, self = Effect4.Prim.suspend thunk) ∨ (∃
  thunk, self = Effect4.Prim.withFiber thunk) ∨ (∃ error, self = Effect4.Prim.yieldableError
  error) ∨ (∃ generator cursor, self = Effect4.Prim.iterator generator cursor) ∨ (∃ body
  onValue, self = Effect4.Prim.onSuccess body onValue) ∨ (∃ body onCause, self =
  Effect4.Prim.onFailure body onCause) ∨ (∃ body onValue onCause, self =
  Effect4.Prim.onSuccessAndFailure body onValue onCause) ∨ (∃ body, self =
  Effect4.Prim.exitFrame body) ∨ (∃ body finalizer flag, self = Effect4.Prim.onExit body
  finalizer flag) ∨ (∃ flag, self = Effect4.Prim.setInterruptible flag) ∨ (∃ loop cursor, self =
  Effect4.Prim.whileLoop loop cursor) ∨ (∃ priority, self = Effect4.Prim.yieldNowWith priority)
  ∨ (∃ register withSignal cancel, self = Effect4.Prim.async register withSignal cancel) ∨ ∃
  onInterrupt, self = Effect4.Prim.asyncFinalizer onInterrupt)

#check (@Effect4.FrameFiber.start_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (current : Effect4.Prim ν σ β ε δ ι α),
  Effect4.FrameFiber.start current = Effect4.FrameFiber.mk current [] Bool.true Option.none
  Bool.false)

#check (@Effect4.FrameFiber.pendingCause_some :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (cause : Effect4.Cause ε δ ι α), self.interruptedCause = Option.some cause →
  Effect4.FrameFiber.pendingCause self = cause)

#check (@Effect4.FrameFiber.pendingCause_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptedCause = Option.none → Effect4.FrameFiber.pendingCause self =
  Effect4.Cause.empty)

#check (@Effect4.FrameFiber.masked_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.masked self = !self.interruptible)

#check (@Effect4.FrameFiber.interrupted_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.interrupted self = (self.interruptible && Option.isSome
  self.interruptedCause))

#check (@Effect4.FrameEvent.poppedFrames_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FrameEvent.poppedFrames [] = [])

#check (@Effect4.FrameEvent.poppedFrames_cons_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (rest :
  List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.poppedFrames
  (Effect4.FrameEvent.popped frame :: rest) = frame :: Effect4.FrameEvent.poppedFrames rest)

#check (@Effect4.FrameEvent.finalizersRun_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}, Effect4.FrameEvent.finalizersRun [] = [])

#check (@Effect4.FrameEvent.finalizersRun_cons_ran :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (finalizer : ν) (exit : Effect4.Exit β ε δ ι
  α) (rest : List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.finalizersRun
  (Effect4.FrameEvent.ranFinalizer finalizer exit :: rest) = finalizer ::
  Effect4.FrameEvent.finalizersRun rest)

#check (@Effect4.FrameEvent.finalizersRun_cons_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (rest :
  List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameEvent.finalizersRun
  (Effect4.FrameEvent.popped frame :: rest) = Effect4.FrameEvent.finalizersRun rest)

#check (@Effect4.Prim.hasArm_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α) (arm :
  Effect4.Arm), Effect4.Prim.hasArm self arm = List.contains (Effect4.Prim.arms self) arm)

#check (@Effect4.Prim.isFrame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.isFrame self = !List.isEmpty (Effect4.Prim.arms self))

#check (@Effect4.Prim.isFrame_iff :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.isFrame self = Bool.true ↔ Effect4.Prim.arms self ≠ [])

#check (@Effect4.Prim.arms_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  : ν), Effect4.Prim.arms (Effect4.Prim.onSuccess body onValue) = [Effect4.Arm.contA])

#check (@Effect4.Prim.arms_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onCause
  : ν), Effect4.Prim.arms (Effect4.Prim.onFailure body onCause) = [Effect4.Arm.contE])

#check (@Effect4.Prim.arms_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  onCause : ν), Effect4.Prim.arms (Effect4.Prim.onSuccessAndFailure body onValue onCause) =
  [Effect4.Arm.contA, Effect4.Arm.contE])

#check (@Effect4.Prim.arms_exitFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α),
  Effect4.Prim.arms (Effect4.Prim.exitFrame body) = [Effect4.Arm.contA, Effect4.Arm.contE])

#check (@Effect4.Prim.arms_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool), Effect4.Prim.arms (Effect4.Prim.onExit body finalizer flag) =
  [Effect4.Arm.contA, Effect4.Arm.contE, Effect4.Arm.contAll])

#check (@Effect4.Prim.arms_setInterruptible :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool), Effect4.Prim.arms
  (Effect4.Prim.setInterruptible flag) = [Effect4.Arm.contAll])

#check (@Effect4.Prim.arms_whileLoop :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (loop : ν) (cursor : β), Effect4.Prim.arms
  (Effect4.Prim.whileLoop loop cursor) = [Effect4.Arm.contA])

#check (@Effect4.Prim.arms_iterator :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (generator : ν) (cursor : β),
  Effect4.Prim.arms (Effect4.Prim.iterator generator cursor) = [Effect4.Arm.contA])

#check (@Effect4.Prim.non_frames_have_no_arms :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (value : β) (cause : Effect4.Cause ε δ ι α)
  (thunk : σ) (error : ε) (priority : Nat) (register : ν) (withSignal : Bool) (cancel : Option
  ν), Effect4.Prim.arms (Effect4.Prim.success value) = [] ∧
  Effect4.Prim.arms (Effect4.Prim.failure cause) = [] ∧ Effect4.Prim.arms (Effect4.Prim.sync
  thunk) = [] ∧ Effect4.Prim.arms (Effect4.Prim.suspend thunk) = [] ∧ Effect4.Prim.arms
  (Effect4.Prim.withFiber thunk) = [] ∧ Effect4.Prim.arms (Effect4.Prim.yieldableError error) =
  [] ∧ Effect4.Prim.arms (Effect4.Prim.yieldNowWith priority) = [] ∧ Effect4.Prim.arms
  (Effect4.Prim.async register withSignal cancel) = [])

#check (@Effect4.Prim.ofExit_asExit? :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.asExit? (Effect4.Prim.ofExit exit) = Option.some exit)

#check (@Effect4.Prim.asExit?_success :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (value : β), Effect4.Prim.asExit?
  (Effect4.Prim.success value) = Option.some (Effect4.Exit.success value))

#check (@Effect4.Prim.asExit?_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (cause : Effect4.Cause ε δ ι α),
  Effect4.Prim.asExit? (Effect4.Prim.failure cause) = Option.some (Effect4.Exit.failure cause))

#check (@Effect4.Prim.asExit?_eq_some :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.Prim ν σ β ε δ ι α) (exit :
  Effect4.Exit β ε δ ι α), Effect4.Prim.asExit? self = Option.some exit → self =
  Effect4.Prim.ofExit exit)

#check (@Effect4.Prim.ofExit_isFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.isFrame (Effect4.Prim.ofExit exit) = Bool.false)

#check (@Effect4.Prim.ensure_of_no_contAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.false
  → Effect4.Prim.ensure frame fiber = (fiber, Option.none))

#check (@Effect4.Prim.ensure_onExit_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true →
  Effect4.Prim.ensure (Effect4.Prim.onExit body finalizer Bool.false) fiber =
  (Effect4.FrameFiber.mk fiber.current (Effect4.Prim.setInterruptible Bool.true :: fiber.stack)
  Bool.false fiber.interruptedCause fiber.deferredInterrupt, Option.none))

#check (@Effect4.Prim.ensure_onExit_told_not_to :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.ensure
  (Effect4.Prim.onExit body finalizer Bool.true) fiber = (fiber, Option.none))

#check (@Effect4.Prim.ensure_onExit_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible
  = Bool.false → Effect4.Prim.ensure (Effect4.Prim.onExit body finalizer flag) fiber = (fiber,
  Option.none))

#check (@Effect4.Prim.ensure_onExit_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (fiber : Effect4.FrameFiber ν σ β ε δ ι α), (Effect4.Prim.ensure
  (Effect4.Prim.onExit body finalizer flag) fiber).snd = Option.none)

#check (@Effect4.Prim.ensure_setInterruptible_flag :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.setInterruptible flag) fiber).fst.interruptible
  = flag)

#check (@Effect4.Prim.ensure_setInterruptible_stack :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), (Effect4.Prim.ensure (Effect4.Prim.setInterruptible flag) fiber).fst.stack =
  fiber.stack)

#check (@Effect4.Prim.ensure_setInterruptible_substitutes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (cause : Effect4.Cause ε δ ι α) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptedCause = Option.some cause →
  Effect4.Prim.ensure (Effect4.Prim.setInterruptible Bool.true) fiber = (Effect4.FrameFiber.mk
  fiber.current fiber.stack Bool.true fiber.interruptedCause fiber.deferredInterrupt,
  Option.some (Effect4.Prim.failure cause)))

#check (@Effect4.Prim.ensure_setInterruptible_false_no_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.Prim.ensure (Effect4.Prim.setInterruptible Bool.false) fiber).snd = Option.none)

#check (@Effect4.Prim.ensure_setInterruptible_no_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (flag : Bool) (fiber : Effect4.FrameFiber ν σ
  β ε δ ι α), fiber.interruptedCause = Option.none → Effect4.Prim.ensure
  (Effect4.Prim.setInterruptible flag) fiber = (Effect4.FrameFiber.mk fiber.current fiber.stack
  flag fiber.interruptedCause fiber.deferredInterrupt, Option.none))

#check (@Effect4.Prim.answerOf_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame next : Effect4.Prim ν σ β ε δ ι α)
  (demand : Effect4.Arm), Effect4.Prim.answerOf frame demand (Option.some next) = Option.some
  (Effect4.ContAnswer.replacement next))

#check (@Effect4.Prim.answerOf_arm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (demand
  : Effect4.Arm), Effect4.Prim.hasArm frame demand = Bool.true → Effect4.Prim.answerOf frame
  demand Option.none = Option.some (Effect4.ContAnswer.frame frame))

#check (@Effect4.Prim.answerOf_missing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α) (demand
  : Effect4.Arm), Effect4.Prim.hasArm frame demand = Bool.false → Effect4.Prim.answerOf frame
  demand Option.none = Option.none)

#check (@Effect4.Prim.answerOf_frame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame answering : Effect4.Prim ν σ β ε δ ι
  α) (demand : Effect4.Arm) (replacement : Option (Effect4.Prim ν σ β ε δ ι α)),
  Effect4.Prim.answerOf frame demand replacement = Option.some (Effect4.ContAnswer.frame
  answering) → answering = frame ∧ Effect4.Prim.hasArm frame demand = Bool.true)

#check (@Effect4.Prim.armA_isSome :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (frame : Effect4.Prim ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε δ ι
  α)), Option.isSome (Effect4.Prim.armA interp frame value provided) = Effect4.Prim.hasArm frame
  Effect4.Arm.contA)

#check (@Effect4.Prim.armE_isSome :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (frame : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), Option.isSome (Effect4.Prim.armE interp frame cause provided) =
  Effect4.Prim.hasArm frame Effect4.Arm.contE)

#check (@Effect4.Prim.armA_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onSuccess body onValue)
  value provided = Option.some (interp.contA onValue value, []))

#check (@Effect4.Prim.armA_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onSuccessAndFailure body
  onValue onCause) value provided = Option.some (interp.contA onValue value, []))

#check (@Effect4.Prim.armE_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause : ν) (cause : Effect4.Cause ε δ ι α) (provided
  : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.onFailure body
  onCause) cause provided = Option.some (interp.contE onCause cause, []))

#check (@Effect4.Prim.armE_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (cause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) cause provided = Option.some
  (interp.contE onCause cause, []))

#check (@Effect4.Prim.armE_onSuccess_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue : ν) (cause : Effect4.Cause ε δ ι α) (provided
  : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.onSuccess body
  onValue) cause provided = Option.none)

#check (@Effect4.Prim.armA_onFailure_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onFailure body onCause)
  value provided = Option.none)

#check (@Effect4.Prim.armA_setInterruptible_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (flag : Bool) (value : β) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA
  interp (Effect4.Prim.setInterruptible flag) value provided = Option.none)

#check (@Effect4.Prim.armE_setInterruptible_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (flag : Bool) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι α)),
  Effect4.Prim.armE interp (Effect4.Prim.setInterruptible flag) cause provided = Option.none)

#check (@Effect4.Prim.armE_whileLoop_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor : β) (cause : Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β
  ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.whileLoop loop cursor) cause provided =
  Option.none)

#check (@Effect4.Prim.armE_iterator_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor : β) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), Effect4.Prim.armE interp (Effect4.Prim.iterator generator cursor)
  cause provided = Option.none)

#check (@Effect4.Prim.armA_exitFrame_provided :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (value : β) (exit : Effect4.Exit β ε δ ι α),
  Effect4.Prim.armA interp (Effect4.Prim.exitFrame body) value (Option.some exit) = Option.some
  (Effect4.Prim.success (interp.reifyExit exit), []))

#check (@Effect4.Prim.armA_exitFrame_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (value : β), Effect4.Prim.armA interp
  (Effect4.Prim.exitFrame body) value Option.none = Option.some (Effect4.Prim.success
  (interp.reifyExit (Effect4.Exit.success value)), []))

#check (@Effect4.Prim.armE_exitFrame_provided :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (exit : Effect4.Exit β
  ε δ ι α), Effect4.Prim.armE interp (Effect4.Prim.exitFrame body) cause (Option.some exit) =
  Option.some (Effect4.Prim.success (interp.reifyExit exit), []))

#check (@Effect4.Prim.armE_exitFrame_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α), Effect4.Prim.armE
  interp (Effect4.Prim.exitFrame body) cause Option.none = Option.some (Effect4.Prim.success
  (interp.reifyExit (Effect4.Exit.failure cause)), []))

#check (@Effect4.Prim.armA_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value : β) (exit :
  Effect4.Exit β ε δ ι α), Effect4.Prim.armA interp (Effect4.Prim.onExit body finalizer flag)
  value (Option.some exit) = Option.some (Effect4.Prim.ofExit
  (Effect4.Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)), []))

#check (@Effect4.Prim.armE_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (cause : Effect4.Cause ε
  δ ι α) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.armE interp (Effect4.Prim.onExit body
  finalizer flag) cause (Option.some exit) = Option.some (Effect4.Prim.ofExit
  (Effect4.Exit.restoreAfterFinalizer exit (interp.finalizerExit finalizer exit)), []))

#check (@Effect4.Prim.onExit_finalizer_success_restores :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value : β) (exit :
  Effect4.Exit β ε δ ι α), interp.finalizerExit finalizer exit = Effect4.Exit.success () →
  Effect4.Prim.armA interp (Effect4.Prim.onExit body finalizer flag) value (Option.some exit) =
  Option.some (Effect4.Prim.ofExit exit, []))

#check (@Effect4.Prim.onExit_finalizer_failure_merges :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (cause finalizerCause :
  Effect4.Cause ε δ ι α), interp.finalizerExit finalizer (Effect4.Exit.failure cause) =
  Effect4.Exit.failure finalizerCause → Effect4.Prim.armE interp (Effect4.Prim.onExit body
  finalizer flag) cause (Option.some (Effect4.Exit.failure cause)) = Option.some
  (Effect4.Prim.failure (Effect4.Cause.combine cause finalizerCause), []))

#check (@Effect4.Prim.onExit_success_finalizer_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag : Bool) (value produced : β)
  (finalizerCause : Effect4.Cause ε δ ι α), interp.finalizerExit finalizer (Effect4.Exit.success
  produced) = Effect4.Exit.failure finalizerCause → Effect4.Prim.armA interp
  (Effect4.Prim.onExit body finalizer flag) value (Option.some (Effect4.Exit.success produced))
  = Option.some (Effect4.Prim.failure finalizerCause, []))

#check (@Effect4.Prim.onExit_arm_is_per_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body other : Effect4.Prim ν σ β ε δ ι α) (finalizer : ν) (flag otherFlag : Bool) (value :
  β) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp (Effect4.Prim.onExit
  body finalizer flag) value provided = Effect4.Prim.armA interp (Effect4.Prim.onExit other
  finalizer otherFlag) value provided)

#check (@Effect4.Prim.onSuccess_arm_is_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (left right : ν) (value : β) (provided : Option
  (Effect4.Exit β ε δ ι α)), interp.contA left value ≠ interp.contA right value →
  Effect4.Prim.armA interp (Effect4.Prim.onSuccess body left) value provided ≠ Effect4.Prim.armA
  interp (Effect4.Prim.onSuccess body right) value provided)

#check (@Effect4.Prim.onFailure_arm_is_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (left right : ν) (cause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), interp.contE left cause ≠ interp.contE right
  cause → Effect4.Prim.armE interp (Effect4.Prim.onFailure body left) cause provided ≠
  Effect4.Prim.armE interp (Effect4.Prim.onFailure body right) cause provided)

#check (@Effect4.Prim.onSuccessAndFailure_arms_are_per_instance :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue onCause : ν) (value : β) (cause :
  Effect4.Cause ε δ ι α) (provided : Option (Effect4.Exit β ε δ ι α)), Effect4.Prim.armA interp
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) value provided = Option.some
  (interp.contA onValue value, []) ∧ Effect4.Prim.armE interp (Effect4.Prim.onSuccessAndFailure
  body onValue onCause) cause provided = Option.some (interp.contE onCause cause, []))

#check (@Effect4.Prim.armA_whileLoop_continue :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)), interp.loopTest
  loop (interp.loopStep loop value) = Bool.true → Effect4.Prim.armA interp
  (Effect4.Prim.whileLoop loop cursor) value provided = Option.some (interp.loopBody loop
  (interp.loopStep loop value), [Effect4.Prim.whileLoop loop (interp.loopStep loop value)]))

#check (@Effect4.Prim.armA_whileLoop_stop :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (loop : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)), interp.loopTest
  loop (interp.loopStep loop value) = Bool.false → Effect4.Prim.armA interp
  (Effect4.Prim.whileLoop loop cursor) value provided = Option.some (Effect4.Prim.success
  (interp.loopDone loop), []))

#check (@Effect4.Prim.armA_iterator_done :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value result : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  (interp.iterNext generator value).snd = Effect4.IterStep.done result → Effect4.Prim.armA
  interp (Effect4.Prim.iterator generator cursor) value provided = Option.some
  (Effect4.Prim.success result, []))

#check (@Effect4.Prim.armA_iterator_halt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value : β) (cause : Effect4.Cause ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), (interp.iterNext generator value).snd = Effect4.IterStep.halt cause
  → Effect4.Prim.armA interp (Effect4.Prim.iterator generator cursor) value provided =
  Option.some (Effect4.Prim.failure cause, []))

#check (@Effect4.Prim.armA_iterator_resume :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (generator : ν) (cursor value : β) (next : Effect4.Prim ν σ β ε δ ι α) (provided : Option
  (Effect4.Exit β ε δ ι α)), (interp.iterNext generator value).snd = Effect4.IterStep.resume
  next → Effect4.Prim.armA interp (Effect4.Prim.iterator generator cursor) value provided =
  Option.some (next, [Effect4.Prim.iterator generator cursor]))

#check (@Effect4.Prim.iteratorFolded_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α) (generator : ν) (cursor value :
  β), Effect4.Prim.iteratorFolded interp (Effect4.Prim.iterator generator cursor) value =
  (interp.iterNext generator value).fst)

#check (@Effect4.Prim.iterator_folds_inline :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (left right : Effect4.PrimInterp ν σ β ε
  δ ι α) (generator : ν) (cursor value : β) (provided : Option (Effect4.Exit β ε δ ι α)),
  (left.iterNext generator value).snd = (right.iterNext generator value).snd → Effect4.Prim.armA
  left (Effect4.Prim.iterator generator cursor) value provided = Effect4.Prim.armA right
  (Effect4.Prim.iterator generator cursor) value provided)

#check (@Effect4.Prim.finalizerEvents_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α)
  (finalizer : ν) (flag : Bool) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents
  (Effect4.Prim.onExit body finalizer flag) exit = [Effect4.FrameEvent.ranFinalizer finalizer
  exit])

#check (@Effect4.Prim.finalizerEvents_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  : ν) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents (Effect4.Prim.onSuccess
  body onValue) exit = [])

#check (@Effect4.Prim.finalizerEvents_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (body : Effect4.Prim ν σ β ε δ ι α) (onCause
  : ν) (exit : Effect4.Exit β ε δ ι α), Effect4.Prim.finalizerEvents (Effect4.Prim.onFailure
  body onCause) exit = [])

#check (@Effect4.FrameFiber.getCont_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.true → Effect4.FrameFiber.getCont self
  demand Bool.false = Effect4.FramePop.mk (Effect4.ContAnswer.deferred
  (Effect4.FrameFiber.pendingCause self)) [] [Effect4.FrameEvent.deferred
  (Effect4.FrameFiber.pendingCause self)] (Effect4.FrameFiber.mk self.current self.stack
  self.interruptible self.interruptedCause Bool.false))

#check (@Effect4.FrameFiber.getCont_deferred_pops_nothing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.true → (Effect4.FrameFiber.getCont self
  demand Bool.false).popped = [])

#check (@Effect4.FrameFiber.getCont_eq_popFrom :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.deferredInterrupt = Bool.false →
  Effect4.FrameFiber.getCont self demand skip = Effect4.FrameFiber.popFrom demand skip
  self.stack (Effect4.FrameFiber.mk self.current [] self.interruptible self.interruptedCause
  Bool.false))

#check (@Effect4.FrameFiber.getCont_skip_clears_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), Effect4.FrameFiber.getCont self demand Bool.true =
  Effect4.FrameFiber.popFrom demand Bool.true self.stack (Effect4.FrameFiber.mk self.current []
  self.interruptible self.interruptedCause Bool.false))

#check (@Effect4.FrameFiber.getCont_empty_stack :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool), self.deferredInterrupt = Bool.false → self.stack = [] →
  Effect4.FrameFiber.getCont self demand skip = Effect4.FramePop.mk Effect4.ContAnswer.empty []
  [] (Effect4.FrameFiber.mk self.current [] self.interruptible self.interruptedCause
  Bool.false))

#check (@Effect4.FrameFiber.popFrom_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.FrameFiber.popFrom demand skip [] fiber =
  Effect4.FramePop.mk Effect4.ContAnswer.empty [] [] fiber)

#check (@Effect4.FrameFiber.popFrom_answer_answer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).answer = answer)

#check (@Effect4.FrameFiber.popFrom_answer_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).popped = [frame])

#check (@Effect4.FrameFiber.popFrom_answer_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).events =
  Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd)

#check (@Effect4.FrameFiber.popFrom_answer_fiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α) (answer : Effect4.ContAnswer ν σ β ε δ ι α),
  Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure frame fiber).snd = Option.some answer
  → (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure frame fiber).fst) = Bool.false
  → (Effect4.FrameFiber.popFrom demand skip (frame :: rest) fiber).fiber = have __src :=
  (Effect4.Prim.ensure frame fiber).fst; Effect4.FrameFiber.mk __src.current
  ((Effect4.Prim.ensure frame fiber).fst.stack ++ rest) __src.interruptible
  __src.interruptedCause __src.deferredInterrupt)

#check (@Effect4.FrameFiber.popFrom_continue_answer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).answer = (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).answer)

#check (@Effect4.FrameFiber.popFrom_continue_popped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).popped = frame :: (Effect4.FrameFiber.continueFrom demand skip frame rest
  fiber).popped)

#check (@Effect4.FrameFiber.popFrom_continue_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).events = Effect4.Prim.passEvents frame (Effect4.Prim.ensure frame fiber).snd ++
  (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).events)

#check (@Effect4.FrameFiber.popFrom_continue_fiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frame :
  Effect4.Prim ν σ β ε δ ι α) (rest : List (Effect4.Prim ν σ β ε δ ι α)) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), Effect4.Prim.answerOf frame demand (Effect4.Prim.ensure
  frame fiber).snd = Option.none ∨ (skip && Effect4.FrameFiber.interrupted (Effect4.Prim.ensure
  frame fiber).fst) = Bool.true → (Effect4.FrameFiber.popFrom demand skip (frame :: rest)
  fiber).fiber = (Effect4.FrameFiber.continueFrom demand skip frame rest fiber).fiber)

#check (@Effect4.FrameFiber.popFrom_answer_hasArm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (frame :
  Effect4.Prim ν σ β ε δ ι α), (Effect4.FrameFiber.popFrom demand skip frames fiber).answer =
  Effect4.ContAnswer.frame frame → Effect4.Prim.hasArm frame demand = Bool.true)

#check (@Effect4.FrameFiber.getCont_answer_hasArm :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (frame : Effect4.Prim ν σ β ε δ ι α),
  (Effect4.FrameFiber.getCont self demand skip).answer = Effect4.ContAnswer.frame frame →
  Effect4.Prim.hasArm frame demand = Bool.true)

#check (@Effect4.FrameFiber.passEvents_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α)
  (replacement : Option (Effect4.Prim ν σ β ε δ ι α)), Effect4.Prim.hasArm frame
  Effect4.Arm.contAll = Bool.true → Effect4.FrameEvent.ranContAll frame ∈
  Effect4.Prim.passEvents frame replacement)

#check (@Effect4.FrameFiber.passEvents_poppedFrames :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (frame : Effect4.Prim ν σ β ε δ ι α)
  (replacement : Option (Effect4.Prim ν σ β ε δ ι α)), Effect4.FrameEvent.poppedFrames
  (Effect4.Prim.passEvents frame replacement) = [frame])

#check (@Effect4.FrameFiber.popFrom_popped_eq_events :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.popFrom demand skip frames fiber).popped = Effect4.FrameEvent.poppedFrames
  (Effect4.FrameFiber.popFrom demand skip frames fiber).events)

#check (@Effect4.FrameFiber.popFrom_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (demand : Effect4.Arm) (skip : Bool) (frames
  : List (Effect4.Prim ν σ β ε δ ι α)) (fiber : Effect4.FrameFiber ν σ β ε δ ι α) (frame :
  Effect4.Prim ν σ β ε δ ι α), Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.true → frame
  ∈ (Effect4.FrameFiber.popFrom demand skip frames fiber).popped → Effect4.FrameEvent.ranContAll
  frame ∈ (Effect4.FrameFiber.popFrom demand skip frames fiber).events)

#check (@Effect4.FrameFiber.getCont_ranContAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (skip : Bool) (frame : Effect4.Prim ν σ β ε δ ι α),
  self.deferredInterrupt = Bool.false → Effect4.Prim.hasArm frame Effect4.Arm.contAll =
  Bool.true → frame ∈ (Effect4.FrameFiber.getCont self demand skip).popped →
  Effect4.FrameEvent.ranContAll frame ∈ (Effect4.FrameFiber.getCont self demand skip).events)

#check (@Effect4.FrameFiber.getCont_skip_of_no_pending_cause :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm), self.deferredInterrupt = Bool.false → self.interruptedCause =
  Option.none → Effect4.FrameFiber.getCont self demand Bool.true = Effect4.FrameFiber.getCont
  self demand Bool.false)

#check (@Effect4.FrameFiber.interrupt_skips_every_handler :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (demand : Effect4.Arm) (cause : Effect4.Cause ε δ ι α), self.interruptible = Bool.true →
  self.interruptedCause = Option.some cause → (∀ (frame : Effect4.Prim ν σ β ε δ ι α), frame ∈
  self.stack → Effect4.Prim.hasArm frame Effect4.Arm.contAll = Bool.false) →
  (Effect4.FrameFiber.getCont self demand Bool.true).answer = Effect4.ContAnswer.empty)

#check (@Effect4.FrameFiber.getCont_mask_stops_skip :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (skip : Bool) (rest : List (Effect4.Prim ν σ β ε δ ι α)), self.deferredInterrupt = Bool.false
  → self.stack = Effect4.Prim.setInterruptible Bool.false :: rest → (Effect4.FrameFiber.getCont
  self Effect4.Arm.contE skip).answer = (Effect4.FrameFiber.getCont (Effect4.FrameFiber.mk
  self.current rest Bool.false self.interruptedCause Bool.false) Effect4.Arm.contE skip).answer)

#check (@Effect4.FrameFiber.resumeValue_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).answer =
  Effect4.ContAnswer.empty → Effect4.FrameFiber.resumeValue interp self value provided =
  (Effect4.FrameStep.finished (Option.getD provided (Effect4.Exit.success value)),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).events ++
  [Effect4.FrameEvent.yielded (Option.getD provided (Effect4.Exit.success value))]))

#check (@Effect4.FrameFiber.resumeValue_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (cause : Effect4.Cause ε δ ι α), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).answer = Effect4.ContAnswer.deferred cause → Effect4.FrameFiber.resumeValue interp
  self value provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont
  self Effect4.Arm.contA Bool.false).fiber; Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
  __src.stack __src.interruptible __src.interruptedCause __src.deferredInterrupt),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).events))

#check (@Effect4.FrameFiber.resumeValue_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (next : Effect4.Prim ν σ β ε δ ι α), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contA Bool.false).answer = Effect4.ContAnswer.replacement next →
  Effect4.FrameFiber.resumeValue interp self value provided = (Effect4.FrameStep.running (have
  __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).fiber;
  Effect4.FrameFiber.mk next __src.stack __src.interruptible __src.interruptedCause
  __src.deferredInterrupt), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).events))

#check (@Effect4.FrameFiber.resumeValue_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β) (provided : Option (Effect4.Exit β ε
  δ ι α)) (frame next : Effect4.Prim ν σ β ε δ ι α) (pushed : List (Effect4.Prim ν σ β ε δ ι
  α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contA Bool.false).answer =
  Effect4.ContAnswer.frame frame → Effect4.Prim.armA interp frame value provided = Option.some
  (next, pushed) → Effect4.FrameFiber.resumeValue interp self value provided =
  (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).fiber; Effect4.FrameFiber.mk next (pushed ++ (Effect4.FrameFiber.getCont self
  Effect4.Arm.contA Bool.false).fiber.stack) __src.interruptible __src.interruptedCause
  __src.deferredInterrupt), (Effect4.FrameFiber.getCont self Effect4.Arm.contA
  Bool.false).events ++ Effect4.Prim.finalizerEvents frame (Option.getD provided
  (Effect4.Exit.success value)) ++ List.map Effect4.FrameEvent.pushed pushed))

#check (@Effect4.FrameFiber.resumeCause_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE
  Bool.true).answer = Effect4.ContAnswer.empty → Effect4.FrameFiber.resumeCause interp self
  cause provided = (Effect4.FrameStep.finished (Option.getD provided (Effect4.Exit.failure
  cause)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).events ++
  [Effect4.FrameEvent.yielded (Option.getD provided (Effect4.Exit.failure cause))]))

#check (@Effect4.FrameFiber.resumeCause_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause deferredCause : Effect4.Cause ε δ ι α)
  (provided : Option (Effect4.Exit β ε δ ι α)), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).answer = Effect4.ContAnswer.deferred deferredCause →
  Effect4.FrameFiber.resumeCause interp self cause provided = (Effect4.FrameStep.running (have
  __src := (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).fiber;
  Effect4.FrameFiber.mk (Effect4.Prim.failure deferredCause) __src.stack __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events))

#check (@Effect4.FrameFiber.resumeCause_replacement :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)) (next : Effect4.Prim ν σ β ε δ ι α),
  (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).answer =
  Effect4.ContAnswer.replacement next → Effect4.FrameFiber.resumeCause interp self cause
  provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).fiber; Effect4.FrameFiber.mk next __src.stack __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events))

#check (@Effect4.FrameFiber.resumeCause_frame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α) (provided :
  Option (Effect4.Exit β ε δ ι α)) (frame next : Effect4.Prim ν σ β ε δ ι α) (pushed : List
  (Effect4.Prim ν σ β ε δ ι α)), (Effect4.FrameFiber.getCont self Effect4.Arm.contE
  Bool.true).answer = Effect4.ContAnswer.frame frame → Effect4.Prim.armE interp frame cause
  provided = Option.some (next, pushed) → Effect4.FrameFiber.resumeCause interp self cause
  provided = (Effect4.FrameStep.running (have __src := (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).fiber; Effect4.FrameFiber.mk next (pushed ++
  (Effect4.FrameFiber.getCont self Effect4.Arm.contE Bool.true).fiber.stack) __src.interruptible
  __src.interruptedCause __src.deferredInterrupt), (Effect4.FrameFiber.getCont self
  Effect4.Arm.contE Bool.true).events ++ Effect4.Prim.finalizerEvents frame (Option.getD
  provided (Effect4.Exit.failure cause)) ++ List.map Effect4.FrameEvent.pushed pushed))

#check (@Effect4.FrameFiber.step_success :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (value : β), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.success value) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = Effect4.FrameFiber.resumeValue interp
  (Effect4.FrameFiber.mk (Effect4.Prim.success value) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) value (Option.some (Effect4.Exit.success
  value)))

#check (@Effect4.FrameFiber.step_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (cause : Effect4.Cause ε δ ι α),
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.failure cause) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt) =
  Effect4.FrameFiber.resumeCause interp (Effect4.FrameFiber.mk (Effect4.Prim.failure cause)
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt) cause (Option.some
  (Effect4.Exit.failure cause)))

#check (@Effect4.FrameFiber.step_sync :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.sync thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = Effect4.FrameFiber.resumeValue interp
  (Effect4.FrameFiber.mk (Effect4.Prim.sync thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) (interp.syncValue thunk) Option.none)

#check (@Effect4.FrameFiber.step_suspend :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.suspend thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_withFiber :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (thunk : σ), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.withFiber thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (interp.suspendBody thunk) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_yieldableError :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (error : ε), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.yieldableError error) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.fail error)) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_onSuccess :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onSuccess body
  onValue) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onSuccess body onValue ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccess body onValue)]))

#check (@Effect4.FrameFiber.step_onFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onCause :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onFailure body
  onCause) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onFailure body onCause ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onFailure body onCause)]))

#check (@Effect4.FrameFiber.step_onSuccessAndFailure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (onValue
  onCause : ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.onSuccessAndFailure body onValue onCause) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk body (Effect4.Prim.onSuccessAndFailure body onValue onCause ::
  self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onSuccessAndFailure body onValue onCause)]))

#check (@Effect4.FrameFiber.step_exitFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α),
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.exitFrame body) self.stack
  self.interruptible self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk body (Effect4.Prim.exitFrame body :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed
  (Effect4.Prim.exitFrame body)]))

#check (@Effect4.FrameFiber.step_onExit :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (finalizer :
  ν) (flag : Bool), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.onExit
  body finalizer flag) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk body
  (Effect4.Prim.onExit body finalizer flag :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed (Effect4.Prim.onExit
  body finalizer flag)]))

#check (@Effect4.FrameFiber.step_setInterruptible_not_evaluable :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (flag : Bool), Effect4.FrameFiber.step interp
  (Effect4.FrameFiber.mk (Effect4.Prim.setInterruptible flag) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt) = (Effect4.FrameStep.running
  (Effect4.FrameFiber.mk (Effect4.Prim.failure (Effect4.Cause.die interp.notImplemented))
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_whileLoop_true :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (loop : ν) (cursor : β), interp.loopTest loop
  cursor = Bool.true → Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.whileLoop loop cursor) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk (interp.loopBody
  loop cursor) (Effect4.Prim.whileLoop loop cursor :: self.stack) self.interruptible
  self.interruptedCause self.deferredInterrupt), [Effect4.FrameEvent.pushed
  (Effect4.Prim.whileLoop loop cursor)]))

#check (@Effect4.FrameFiber.step_whileLoop_false :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (loop : ν) (cursor : β), interp.loopTest loop
  cursor = Bool.false → Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk
  (Effect4.Prim.whileLoop loop cursor) self.stack self.interruptible self.interruptedCause
  self.deferredInterrupt) = (Effect4.FrameStep.running (Effect4.FrameFiber.mk
  (Effect4.Prim.success (interp.loopDone loop)) self.stack self.interruptible
  self.interruptedCause self.deferredInterrupt), []))

#check (@Effect4.FrameFiber.step_iterator :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (generator : ν) (cursor : β) (next : Effect4.Prim
  ν σ β ε δ ι α) (pushed : List (Effect4.Prim ν σ β ε δ ι α)), Effect4.Prim.armA interp
  (Effect4.Prim.iterator generator cursor) cursor Option.none = Option.some (next, pushed) →
  Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.iterator generator cursor)
  self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk next (pushed ++ self.stack)
  self.interruptible self.interruptedCause self.deferredInterrupt), List.map
  Effect4.FrameEvent.pushed pushed))

#check (@Effect4.FrameFiber.step_ofExit_finishes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (exit : Effect4.Exit β ε δ ι α), Effect4.FrameFiber.step interp (Effect4.FrameFiber.start
  (Effect4.Prim.ofExit exit)) = (Effect4.FrameStep.finished exit, [Effect4.FrameEvent.yielded
  exit]))

#check (@Effect4.FrameFiber.run_zero :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α), Effect4.FrameFiber.run interp 0 self =
  (Effect4.FrameStep.running self, []))

#check (@Effect4.FrameFiber.run_succ_finished :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (fuel : Nat) (exit : Effect4.Exit β ε δ ι α)
  (events : List (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameFiber.step interp self =
  (Effect4.FrameStep.finished exit, events) → Effect4.FrameFiber.run interp (fuel + 1) self =
  (Effect4.FrameStep.finished exit, events))

#check (@Effect4.FrameFiber.run_succ_running :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self next : Effect4.FrameFiber ν σ β ε δ ι α) (fuel : Nat) (events : List
  (Effect4.FrameEvent ν σ β ε δ ι α)), Effect4.FrameFiber.step interp self =
  (Effect4.FrameStep.running next, events) → Effect4.FrameFiber.run interp (fuel + 1) self =
  ((Effect4.FrameFiber.run interp fuel next).fst, events ++ (Effect4.FrameFiber.run interp fuel
  next).snd))

#check (@Effect4.FrameFiber.uninterruptible_already_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.false → Effect4.FrameFiber.uninterruptible self = self)

#check (@Effect4.FrameFiber.uninterruptible_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.true → Effect4.FrameFiber.uninterruptible self =
  Effect4.FrameFiber.mk self.current (Effect4.Prim.setInterruptible Bool.true :: self.stack)
  Bool.false self.interruptedCause self.deferredInterrupt)

#check (@Effect4.FrameFiber.uninterruptibleMask_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.uninterruptibleMask self = Effect4.FrameFiber.uninterruptible self)

#check (@Effect4.FrameFiber.setFiberInterruptible_flag :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.setFiberInterruptible self).fst.interruptible = Bool.true)

#check (@Effect4.FrameFiber.setFiberInterruptible_pushes :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  (Effect4.FrameFiber.setFiberInterruptible self).fst.stack = Effect4.Prim.setInterruptible
  Bool.false :: self.stack)

#check (@Effect4.FrameFiber.setFiberInterruptible_immediate_failure :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α)
  (cause : Effect4.Cause ε δ ι α), self.interruptedCause = Option.some cause →
  (Effect4.FrameFiber.setFiberInterruptible self).snd = Option.some (Effect4.Prim.failure
  cause))

#check (@Effect4.FrameFiber.setFiberInterruptible_no_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptedCause = Option.none → (Effect4.FrameFiber.setFiberInterruptible self).snd =
  Option.none)

#check (@Effect4.FrameFiber.interruptibleRegion_already :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.true → Effect4.FrameFiber.interruptibleRegion self = (self,
  Option.none))

#check (@Effect4.FrameFiber.interruptibleRegion_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  self.interruptible = Bool.false → Effect4.FrameFiber.interruptibleRegion self =
  Effect4.FrameFiber.setFiberInterruptible self)

#check (@Effect4.FrameFiber.restoreAcquire_asked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.restoreAcquire self Bool.true = Effect4.FrameFiber.interruptibleRegion
  self)

#check (@Effect4.FrameFiber.restoreAcquire_not_asked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (self : Effect4.FrameFiber ν σ β ε δ ι α),
  Effect4.FrameFiber.restoreAcquire self Bool.false = (self, Option.none))

#check (@Effect4.Prim.scopedFrame_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (body : Effect4.Prim ν σ β ε δ ι α) (closeScope : ν),
  Effect4.Prim.scopedFrame body closeScope = Effect4.Prim.onExit body closeScope Bool.false)

#check (@Effect4.Prim.scopedFrame_finalizer_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] (body : Effect4.Prim ν σ β ε δ ι α) (closeScope : ν) (fiber :
  Effect4.FrameFiber ν σ β ε δ ι α), fiber.interruptible = Bool.true → Effect4.Prim.ensure
  (Effect4.Prim.scopedFrame body closeScope) fiber = (Effect4.FrameFiber.mk fiber.current
  (Effect4.Prim.setInterruptible Bool.true :: fiber.stack) Bool.false fiber.interruptedCause
  fiber.deferredInterrupt, Option.none))

#check (@Effect4.FrameFiber.step_scopedFrame :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε] [inst_1 : DecidableEq
  δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι
  α) (self : Effect4.FrameFiber ν σ β ε δ ι α) (body : Effect4.Prim ν σ β ε δ ι α) (closeScope :
  ν), Effect4.FrameFiber.step interp (Effect4.FrameFiber.mk (Effect4.Prim.scopedFrame body
  closeScope) self.stack self.interruptible self.interruptedCause self.deferredInterrupt) =
  (Effect4.FrameStep.running (Effect4.FrameFiber.mk body (Effect4.Prim.onExit body closeScope
  Bool.false :: self.stack) self.interruptible self.interruptedCause self.deferredInterrupt),
  [Effect4.FrameEvent.pushed (Effect4.Prim.onExit body closeScope Bool.false)]))

#check (@Effect4.Prim.withFiber_refused :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq
  ι] [DecidableEq α] {ϑ : Type u} (resolve : Effect4.FrameFiber ν σ β ε δ ι α → ϑ) (left right :
  Effect4.FrameFiber ν σ β ε δ ι α), left = right → resolve left = resolve right)

#check (@Effect4.Prim.yieldableError_host_class_refused :
  ∀ {ε : Type u} [DecidableEq ε] {ϑ : Type u} (host : ε → ϑ) (left right : ε), left = right →
  host left = host right)


/-! The reference machine's clauses (`Effect4/Deep/Clauses.lean`), the stores
(`Effect4/Deep/Stores.lean`), the Layer model (`Effect4/Deep/Layer.lean`), the runtime's
`AsyncFinalizer` frame and the context family's two defaults, joined on 2026-09-04. Printed
by the elaborator with full names and re-elaborated here, so a drift is a type mismatch. -/

#check (@Effect4.Deep.runloopTop_deferred :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.frame.deferredInterrupt = Bool.true →
      Effect4.Deep.runloopTop f =
        { id := f.id,
          frame :=
            have __src := f.frame;
            { current := Effect4.Prim.failure f.frame.pendingCause, stack := __src.stack,
              interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
              deferredInterrupt := Bool.false },
          running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
          currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
          yieldOverride := f.yieldOverride, observers := f.observers, children := f.children, dispatcher := f.dispatcher,
          context := f.context })

#check (@Effect4.Deep.runloopTop_idle :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.frame.deferredInterrupt = Bool.false → Effect4.Deep.runloopTop f = f)

#check (@Effect4.Deep.runloopTop_clears :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    (Effect4.Deep.runloopTop f).frame.deferredInterrupt = Bool.false)

#check (@Effect4.Deep.iteration_evaluates :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool),
    Effect4.Deep.injectYield m (Effect4.Deep.countOp (Effect4.Deep.runloopTop f)) yielding = Option.none →
      Effect4.Deep.iteration interp m f yielding =
        Effect4.Deep.evaluatePrim interp m (Effect4.Deep.countOp (Effect4.Deep.runloopTop f)) yielding)

#check (@Effect4.Deep.interruptRecord_parked_applies :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.exit = Option.none →
      f.frame.interruptible = Bool.true →
        f.running = Bool.false →
          (Effect4.Deep.interruptRecord interp interruptor extra f).snd = Bool.true ∧
            (Effect4.Deep.interruptRecord interp interruptor extra f).fst.parked = Effect4.Deep.Parked.notParked ∧
              (Effect4.Deep.interruptRecord interp interruptor extra f).fst.pending = [])

#check (@Effect4.Prim.armE_asyncFinalizer_interrupt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.PrimInterp ν σ β ε δ ι α) (onInterrupt : ν) (cause : Effect4.Cause ε δ ι α)
    (provided : Option (Effect4.Exit β ε δ ι α)),
    cause.hasInterrupts = Bool.true →
      Effect4.Prim.armE interp (Effect4.Prim.asyncFinalizer onInterrupt) cause provided =
        Option.some (interp.cancelThenFail onInterrupt cause, []))

#check (@Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (onInterrupt : ν) (cause : Effect4.Cause ε δ ι α) (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
    fiber.stack = [] →
      fiber.interruptible = Bool.true →
        fiber.interruptedCause = Option.some cause →
          (Effect4.FrameFiber.popFrom Effect4.Arm.contA Bool.false [Effect4.Prim.asyncFinalizer onInterrupt]
                  fiber).answer =
              Effect4.ContAnswer.replacement (Effect4.Prim.failure cause) ∧
            (Effect4.FrameFiber.popFrom Effect4.Arm.contA Bool.false [Effect4.Prim.asyncFinalizer onInterrupt]
                  fiber).popped =
              [Effect4.Prim.asyncFinalizer onInterrupt, Effect4.Prim.setInterruptible Bool.true])

#check (@Effect4.Deep.countOp_count :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    (Effect4.Deep.countOp f).currentOpCount = f.currentOpCount + 1)

#check (@Effect4.Deep.drive_evaluate_enters :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (id : Effect4.FiberId) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some f →
        f.exit = Option.none →
          f.running = Bool.false →
            Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.evaluate id :: rest) =
              Effect4.Deep.drive interp fuel
                ((m.update
                      { id := f.id, frame := f.frame, running := Bool.true, parked := Effect4.Deep.Parked.notParked,
                        pending := f.pending, finalizing := f.finalizing, exit := f.exit, currentOpCount := 0,
                        maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
                        yieldOverride := f.yieldOverride, observers := f.observers, children := f.children,
                        dispatcher := f.dispatcher, context := f.context }).emit
                  [Effect4.Deep.RunEvent.started id])
                (Effect4.Deep.Cmd.loop id Bool.false :: rest))

#check (@Effect4.Deep.drive_evaluate_exited :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (id : Effect4.FiberId) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some f →
        f.exit.isSome = Bool.true →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.evaluate id :: rest) =
            Effect4.Deep.drive interp fuel m rest)

#check (@Effect4.Deep.drive_evaluate_running :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (id : Effect4.FiberId) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some f →
        f.running = Bool.true →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.evaluate id :: rest) =
            Effect4.Deep.drive interp fuel m rest)

#check (@Effect4.Deep.injectYield_latched :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ), Effect4.Deep.injectYield m f Bool.true = Option.none)

#check (@Effect4.Deep.injectYield_fires :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.preventYield = Bool.false →
      Effect4.Deep.yieldVerdict f = Bool.true →
        ∃ it,
          Effect4.Deep.injectYield m f Bool.false = Option.some it ∧
            it.yielding = Bool.true ∧
              it.outcome = Effect4.Deep.Outcome.parked ∧
                it.fiber.parked = Effect4.Deep.Parked.withGuard m.nextToken ∧
                  it.fiber.yieldOverride = Option.none ∧
                    it.fiber.dispatcher =
                        f.dispatcher.enqueue 0 (Effect4.Deep.Task.resume f.id m.nextToken f.frame.current) ∧
                      it.machine.nextToken = m.nextToken + 1)

#check (@Effect4.Deep.iteration_injected :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (it : Effect4.Deep.Iter ν σ β ε δ ι α χ St),
    Effect4.Deep.injectYield m (Effect4.Deep.countOp (Effect4.Deep.runloopTop f)) yielding = Option.some it →
      Effect4.Deep.iteration interp m f yielding = it)

#check (@Effect4.Deep.drive_loop_parked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (id : Effect4.FiberId) (yielding : Bool) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some f →
        (Effect4.Deep.iteration interp m f yielding).outcome = Effect4.Deep.Outcome.parked →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.loop id yielding :: rest) =
            Effect4.Deep.drive interp fuel
              ((Effect4.Deep.iteration interp m f yielding).machine.update
                (have __src := (Effect4.Deep.iteration interp m f yielding).fiber;
                { id := __src.id, frame := __src.frame, running := Bool.false, parked := __src.parked,
                  pending := __src.pending, finalizing := __src.finalizing, exit := __src.exit,
                  currentOpCount := __src.currentOpCount, maxOpsBeforeYield := __src.maxOpsBeforeYield,
                  preventYield := __src.preventYield, yieldOverride := __src.yieldOverride, observers := __src.observers,
                  children := __src.children, dispatcher := __src.dispatcher, context := __src.context }))
              ((Effect4.Deep.iteration interp m f yielding).nested ++ rest))

#check (@Effect4.Deep.drive_loop_continues :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (id : Effect4.FiberId) (yielding : Bool) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some f →
        (Effect4.Deep.iteration interp m f yielding).outcome = Effect4.Deep.Outcome.continue_ →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.loop id yielding :: rest) =
            Effect4.Deep.drive interp fuel
              ((Effect4.Deep.iteration interp m f yielding).machine.update
                (Effect4.Deep.iteration interp m f yielding).fiber)
              ((Effect4.Deep.iteration interp m f yielding).nested ++
                  [Effect4.Deep.Cmd.loop id (Effect4.Deep.iteration interp m f yielding).yielding] ++
                rest))

#check (@Effect4.Deep.start_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (parent : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (child : Effect4.FiberId),
    Effect4.Deep.start m parent child Bool.true = (m, parent, [Effect4.Deep.Cmd.evaluate child]) ∧
      Effect4.Deep.start m parent child Bool.false =
        (m.emit [Effect4.Deep.RunEvent.scheduledTask parent.id 0 (Effect4.Deep.Task.start child)],
          { id := parent.id, frame := parent.frame, running := parent.running, parked := parent.parked,
            pending := parent.pending, finalizing := parent.finalizing, exit := parent.exit,
            currentOpCount := parent.currentOpCount, maxOpsBeforeYield := parent.maxOpsBeforeYield,
            preventYield := parent.preventYield, yieldOverride := parent.yieldOverride, observers := parent.observers,
            children := parent.children, dispatcher := parent.dispatcher.enqueue 0 (Effect4.Deep.Task.start child),
            context := parent.context },
          []))

#check (@Effect4.Deep.runFork_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (program : Effect4.Prim ν σ β ε δ ι α) (context : χ),
    Effect4.Deep.runFork interp fuel m program context =
      (Effect4.Deep.drive interp fuel
          {
            fibers :=
              m.fibers ++
                [Effect4.Deep.RunFiber.make { value := m.nextId } program Bool.true (interp.budgetOf context) context],
            races := m.races, nextId := m.nextId + 1, nextToken := m.nextToken, nextRace := m.nextRace,
            middlewareInstalled := m.middlewareInstalled, state := m.state, trace := m.trace, stuck := m.stuck }
          [Effect4.Deep.Cmd.evaluate { value := m.nextId }, Effect4.Deep.Cmd.drainDue],
        { value := m.nextId }))

#check (@Effect4.Deep.interruptRecord_records :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.exit = Option.none →
      (Effect4.Deep.interruptRecord interp interruptor extra f).fst.frame.interruptedCause =
        Option.some (Effect4.Deep.interruptCauseOf interp interruptor extra f))

#check (@Effect4.Deep.interruptRecord_running_defers :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.exit = Option.none →
      f.frame.interruptible = Bool.true →
        f.running = Bool.true →
          (Effect4.Deep.interruptRecord interp interruptor extra f).snd = Bool.false ∧
            (Effect4.Deep.interruptRecord interp interruptor extra f).fst.frame.deferredInterrupt = Bool.true)

#check (@Effect4.Deep.interruptRecord_idle_applies :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.exit = Option.none →
      f.frame.interruptible = Bool.true →
        f.running = Bool.false →
          (Effect4.Deep.interruptRecord interp interruptor extra f).snd = Bool.true ∧
            (Effect4.Deep.interruptRecord interp interruptor extra f).fst.parked = Effect4.Deep.Parked.notParked ∧
              (Effect4.Deep.interruptRecord interp interruptor extra f).fst.pending = [] ∧
                (Effect4.Deep.interruptRecord interp interruptor extra f).fst.frame.current =
                  Effect4.Prim.failure (Effect4.Deep.interruptCauseOf interp interruptor extra f))

#check (@Effect4.Deep.interruptRecord_masked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.exit = Option.none →
      f.frame.interruptible = Bool.false →
        (Effect4.Deep.interruptRecord interp interruptor extra f).snd = Bool.false ∧
          (Effect4.Deep.interruptRecord interp interruptor extra f).fst.frame.deferredInterrupt =
              f.frame.deferredInterrupt ∧
            (Effect4.Deep.interruptRecord interp interruptor extra f).fst.frame.current = f.frame.current)

#check (@Effect4.Deep.spawn_daemon_untracked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (parent : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (program : Effect4.Prim ν σ β ε δ ι α)
    (options : Effect4.Supervision.ForkOptions),
    options.daemon = Bool.true → (Effect4.Deep.spawn interp m parent program options).snd.fst.children = parent.children)

#check (@Effect4.Deep.spawnChild_fields :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (parent : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (program : Effect4.Prim ν σ β ε δ ι α) (options : Effect4.Supervision.ForkOptions),
    (Effect4.Deep.spawnChild interp m parent program options).id = { value := m.nextId } ∧
      (Effect4.Deep.spawnChild interp m parent program options).context = parent.context ∧
        ((Effect4.Deep.spawnChild interp m parent program options).frame.interruptible =
            match options.maskMode with
            | Effect4.Supervision.MaskMode.interruptible => Bool.true
            | Effect4.Supervision.MaskMode.uninterruptible => Bool.false
            | Effect4.Supervision.MaskMode.inherit => parent.frame.interruptible) ∧
          (Effect4.Deep.spawnChild interp m parent program options).observers =
            if options.daemon = Bool.true then [] else [Effect4.Deep.Observer.untrackChild parent.id])

#check (@Effect4.Deep.interruptRecord_exited :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.exit.isSome = Bool.true → Effect4.Deep.interruptRecord interp interruptor extra f = (f, Bool.false))

#check (@Effect4.Deep.interruptRecord_accumulates :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (interruptor : Option Effect4.FiberId)
    (extra : Effect4.ReasonAnnotations α) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (previous : Effect4.Cause ε δ ι α),
    f.exit = Option.none →
      f.frame.interruptedCause = Option.some previous →
        (Effect4.Deep.interruptRecord interp interruptor extra f).fst.frame.interruptedCause =
          Option.some
            (previous.combine
              ((Effect4.Supervision.interruptCause interp.encodeFiber interruptor (interp.stackAnnotations f.id)).annotate
                extra Bool.false)))

#check (@Effect4.Deep.yieldVerdict_default :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    f.yieldOverride = Option.none →
      Effect4.Deep.yieldVerdict f = Decidable.decide (f.currentOpCount ≥ f.maxOpsBeforeYield))

#check (@Effect4.Deep.yieldVerdict_override :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (verdict : Bool),
    f.yieldOverride = Option.some verdict → Effect4.Deep.yieldVerdict f = verdict)

#check (@Effect4.Deep.injectYield_no_verdict :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool),
    Effect4.Deep.yieldVerdict f = Bool.false → Effect4.Deep.injectYield m f yielding = Option.none)

#check (@Effect4.Deep.Dispatcher.enqueue_same_bucket :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) (priority : Nat)
    (task : Effect4.Deep.Task ν σ β ε δ ι α) (bucket : Effect4.Deep.Bucket ν σ β ε δ ι α)
    (rest : List (Effect4.Deep.Bucket ν σ β ε δ ι α)),
    d.buckets = bucket :: rest →
      bucket.priority = priority →
        (d.enqueue priority task).buckets = { priority := bucket.priority, tasks := bucket.tasks ++ [task] } :: rest)

#check (@Effect4.Deep.Dispatcher.enqueue_lower_priority :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) (priority : Nat)
    (task : Effect4.Deep.Task ν σ β ε δ ι α) (bucket : Effect4.Deep.Bucket ν σ β ε δ ι α)
    (rest : List (Effect4.Deep.Bucket ν σ β ε δ ι α)),
    d.buckets = bucket :: rest →
      bucket.priority ≠ priority →
        priority < bucket.priority →
          (d.enqueue priority task).buckets = { priority := priority, tasks := [task] } :: bucket :: rest)

#check (@Effect4.Deep.Dispatcher.enqueue_empty :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (priority : Nat) (task : Effect4.Deep.Task ν σ β ε δ ι α),
    (Effect4.Deep.Dispatcher.empty.enqueue priority task).buckets = [{ priority := priority, tasks := [task] }])

#check (@Effect4.Deep.Dispatcher.enqueue_arms :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α) (priority : Nat)
    (task : Effect4.Deep.Task ν σ β ε δ ι α), (d.enqueue priority task).armed = Bool.true)

#check (@Effect4.Deep.Dispatcher.drain_disarms :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α),
    d.drain.snd.armed = Bool.false)

#check (@Effect4.Deep.Dispatcher.drain_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [DecidableEq ε]
    [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (d : Effect4.Deep.Dispatcher ν σ β ε δ ι α),
    d.drain = ((List.map Effect4.Deep.Bucket.tasks d.buckets).flatten, Effect4.Deep.Dispatcher.empty))

#check (@Effect4.Deep.fire_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (owner : Effect4.FiberId) (o : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    m.fiber? owner = Option.some o →
      Effect4.Deep.stepDecision.fire interp fuel m owner =
        List.foldl
          (fun m task =>
            have m := m.emit [Effect4.Deep.RunEvent.ranTask owner task];
            match task with
            | Effect4.Deep.Task.start child =>
              Effect4.Deep.drive interp fuel m [Effect4.Deep.Cmd.evaluate child, Effect4.Deep.Cmd.drainDue]
            | Effect4.Deep.Task.resume target token answer =>
              Effect4.Deep.drive interp fuel m [Effect4.Deep.Cmd.resume target token answer, Effect4.Deep.Cmd.drainDue])
          (m.update
            { id := o.id, frame := o.frame, running := o.running, parked := o.parked, pending := o.pending,
              finalizing := o.finalizing, exit := o.exit, currentOpCount := o.currentOpCount,
              maxOpsBeforeYield := o.maxOpsBeforeYield, preventYield := o.preventYield, yieldOverride := o.yieldOverride,
              observers := o.observers, children := o.children, dispatcher := o.dispatcher.drain.snd,
              context := o.context })
          o.dispatcher.drain.fst)

#check (@Effect4.Deep.flushAll_idle :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St),
    List.filter (fun f => f.dispatcher.armed) m.fibers = [] →
      Effect4.Deep.stepDecision.flushAll interp fuel (rounds + 1) m = m)

#check (@Effect4.Deep.flushAll_round :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel rounds : Nat)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St),
    (List.map Effect4.Deep.RunFiber.id (List.filter (fun f => f.dispatcher.armed) m.fibers)).isEmpty = Bool.false →
      m.stuck = Option.none →
        Effect4.Deep.stepDecision.flushAll interp fuel (rounds + 1) m =
          Effect4.Deep.stepDecision.flushAll interp fuel rounds
            (List.foldl (Effect4.Deep.stepDecision.fire interp fuel) m
              (List.map Effect4.Deep.RunFiber.id (List.filter (fun f => f.dispatcher.armed) m.fibers))))

#check (@Effect4.Deep.evaluatePrim_yieldNowWith :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (priority : Nat),
    have g :=
      { id := f.id,
        frame :=
          have __src := f.frame;
          { current := Effect4.Prim.yieldNowWith priority, stack := __src.stack, interruptible := __src.interruptible,
            interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
        running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
        currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
        yieldOverride := f.yieldOverride, observers := f.observers, children := f.children, dispatcher := f.dispatcher,
        context := f.context };
    have it := Effect4.Deep.evaluatePrim interp m g yielding;
    it.outcome = Effect4.Deep.Outcome.parked ∧
      it.fiber.parked = Effect4.Deep.Parked.withGuard m.nextToken ∧
        it.fiber.frame.current = Effect4.Prim.success interp.voidValue ∧
          it.fiber.dispatcher =
              f.dispatcher.enqueue priority
                (Effect4.Deep.Task.resume f.id m.nextToken (Effect4.Prim.success interp.voidValue)) ∧
            it.machine.nextToken = m.nextToken + 1 ∧ it.nested = [])

#check (@Effect4.Deep.drive_resume_wrong_token :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (id : Effect4.FiberId) (token guard : Nat)
    (answer : Effect4.Prim ν σ β ε δ ι α) (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some t →
        t.parked = Effect4.Deep.Parked.withGuard guard →
          guard ≠ token →
            Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.resume id token answer :: rest) =
              Effect4.Deep.drive interp fuel m rest)

#check (@Effect4.Deep.drive_resume_guard :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (id : Effect4.FiberId) (token : Nat) (answer : Effect4.Prim ν σ β ε δ ι α) (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some t →
        t.parked = Effect4.Deep.Parked.withGuard token →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.resume id token answer :: rest) =
            Effect4.Deep.drive interp fuel
              ((m.update
                    { id := t.id,
                      frame :=
                        have __src := t.frame;
                        { current := answer, stack := __src.stack, interruptible := __src.interruptible,
                          interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
                      running := t.running, parked := Effect4.Deep.Parked.notParked,
                      pending := List.filter (fun p => Decidable.decide (p.token ≠ token)) t.pending,
                      finalizing := t.finalizing, exit := t.exit, currentOpCount := t.currentOpCount,
                      maxOpsBeforeYield := t.maxOpsBeforeYield, preventYield := t.preventYield,
                      yieldOverride := t.yieldOverride, observers := t.observers, children := t.children,
                      dispatcher := t.dispatcher, context := t.context }).emit
                [Effect4.Deep.RunEvent.resumedWith id token answer])
              (Effect4.Deep.Cmd.evaluate id :: rest))

#check (@Effect4.Deep.drive_resume_not_parked :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (id : Effect4.FiberId) (token : Nat)
    (answer : Effect4.Prim ν σ β ε δ ι α) (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    m.stuck = Option.none →
      m.fiber? id = Option.some t →
        t.parked = Effect4.Deep.Parked.notParked →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.resume id token answer :: rest) =
            Effect4.Deep.drive interp fuel m rest)

#check (@Effect4.Deep.budget_defaults :
  ∀ (store : Effect4.ContextFamily.ContextStore),
    store.ambient = Option.none →
      (store.referenceValue Effect4.ContextFamily.Reference.maxOpsBeforeYield).getD 2048 = 2048 ∧
        ((store.referenceValue Effect4.ContextFamily.Reference.preventSchedulerYield).getD 0 != 0) = Bool.false)

#check (@Effect4.ContextFamily.maxOps_default :
  ∀ (store : Effect4.ContextFamily.ContextStore),
    store.ambient = Option.none →
      (store.referenceValue Effect4.ContextFamily.Reference.maxOpsBeforeYield).getD 2048 = 2048)

#check (@Effect4.Deep.injectYield_prevented :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool),
    f.preventYield = Bool.true → Effect4.Deep.injectYield m f yielding = Option.none)

#check (@Effect4.ContextFamily.preventYield_default :
  ∀ (store : Effect4.ContextFamily.ContextStore),
    store.ambient = Option.none →
      ((store.referenceValue Effect4.ContextFamily.Reference.preventSchedulerYield).getD 0 != 0) = Bool.false)

#check (@Effect4.Deep.stepDecision_abort :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (annotations : Effect4.ReasonAnnotations α) (target : Effect4.FiberId) (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    m.fiber? target = Option.some t →
      Effect4.Deep.stepDecision interp fuel m (Effect4.Deep.RunDecision.interruptFrom Option.none annotations target) =
        have r := Effect4.Deep.interruptRecord interp Option.none annotations t;
        have m := m.emit [Effect4.Deep.RunEvent.interruptRecorded Option.none target];
        have m :=
          if (r.fst.frame.deferredInterrupt && r.fst.running) = Bool.true then
            m.emit [Effect4.Deep.RunEvent.interruptDeferred target]
          else m;
        have m := m.update r.fst;
        if r.snd = Bool.true then
          Effect4.Deep.drive interp fuel m [Effect4.Deep.Cmd.evaluate target, Effect4.Deep.Cmd.drainDue]
        else m)

#check (@Effect4.Deep.runCallback_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (program : Effect4.Prim ν σ β ε δ ι α) (context : χ) (key : Nat),
    Effect4.Deep.runCallback interp fuel m program context key =
      (Effect4.Deep.drive interp fuel
          {
            fibers :=
              m.fibers ++
                [have __src :=
                    Effect4.Deep.RunFiber.make { value := m.nextId } program Bool.true (interp.budgetOf context) context;
                  { id := __src.id, frame := __src.frame, running := __src.running, parked := __src.parked,
                    pending := __src.pending, finalizing := __src.finalizing, exit := __src.exit,
                    currentOpCount := __src.currentOpCount, maxOpsBeforeYield := __src.maxOpsBeforeYield,
                    preventYield := __src.preventYield, yieldOverride := __src.yieldOverride,
                    observers := [Effect4.Deep.Observer.callback key], children := __src.children,
                    dispatcher := __src.dispatcher, context := __src.context }],
            races := m.races, nextId := m.nextId + 1, nextToken := m.nextToken, nextRace := m.nextRace,
            middlewareInstalled := m.middlewareInstalled, state := m.state, trace := m.trace, stuck := m.stuck }
          [Effect4.Deep.Cmd.evaluate { value := m.nextId }, Effect4.Deep.Cmd.drainDue],
        { value := m.nextId }))

#check (@Effect4.Deep.fireObserver_callback :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId) (exit : Effect4.Exit β ε δ ι α)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (nested : List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (key : Nat),
    Effect4.Deep.fireObserver interp id exit (m, nested) (Effect4.Deep.Observer.callback key) =
      ((m.emit [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.callback key)]).emit
          [Effect4.Deep.RunEvent.callback key exit],
        nested))

#check (@Effect4.Deep.promiseOutcome_eq :
  ∀ {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (value : β) (cause : Effect4.Cause ε δ ι α),
    Effect4.Deep.promiseOutcome (Effect4.Exit.success value) = Except.ok value ∧
      Effect4.Deep.promiseOutcome (Effect4.Exit.failure cause) = Except.error cause.squash)

#check (@Effect4.Deep.promiseOutcome_failure :
  ∀ {β : Type v} {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (cause : Effect4.Cause ε δ ι α),
    Effect4.Deep.promiseOutcome (Effect4.Exit.failure cause) = Except.error cause.squash)

#check (@Effect4.Deep.runSyncExit_exited :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (program : Effect4.Prim ν σ β ε δ ι α) (context : χ) (exit : Effect4.Exit β ε δ ι α),
    ((Effect4.Deep.stepDecision interp fuel (Effect4.Deep.runFork interp fuel m program context).fst
                  Effect4.Deep.RunDecision.flush).fiber?
              (Effect4.Deep.runFork interp fuel m program context).snd).bind
          Effect4.Deep.RunFiber.exit =
        Option.some exit →
      (Effect4.Deep.runSyncExit interp fuel m program context).snd = exit)

#check (@Effect4.Deep.runSyncExit_survives :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (program : Effect4.Prim ν σ β ε δ ι α) (context : χ),
    ((Effect4.Deep.stepDecision interp fuel (Effect4.Deep.runFork interp fuel m program context).fst
                  Effect4.Deep.RunDecision.flush).fiber?
              (Effect4.Deep.runFork interp fuel m program context).snd).bind
          Effect4.Deep.RunFiber.exit =
        Option.none →
      (Effect4.Deep.runSyncExit interp fuel m program context).snd =
        Effect4.Exit.failure (Effect4.Cause.die interp.asyncFiberError))

#check (@Effect4.Deep.spawn_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (parent : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (program : Effect4.Prim ν σ β ε δ ι α) (options : Effect4.Supervision.ForkOptions),
    Effect4.Deep.spawn interp m parent program options =
      (({ fibers := m.fibers ++ [Effect4.Deep.spawnChild interp m parent program options], races := m.races,
              nextId := m.nextId + 1, nextToken := m.nextToken, nextRace := m.nextRace,
              middlewareInstalled := m.middlewareInstalled, state := m.state, trace := m.trace, stuck := m.stuck }
            : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St).emit
          [Effect4.Deep.RunEvent.forked parent.id { value := m.nextId } options.daemon],
        { id := parent.id, frame := parent.frame, running := parent.running, parked := parent.parked,
          pending := parent.pending, finalizing := parent.finalizing, exit := parent.exit,
          currentOpCount := parent.currentOpCount, maxOpsBeforeYield := parent.maxOpsBeforeYield,
          preventYield := parent.preventYield, yieldOverride := parent.yieldOverride, observers := parent.observers,
          children := if options.daemon = Bool.true then parent.children else parent.children ++ [{ value := m.nextId }],
          dispatcher := parent.dispatcher, context := parent.context },
        { value := m.nextId }))

#check (@Effect4.Deep.evaluatePrim_join_done :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (target : Effect4.FiberId) (mode : Effect4.Supervision.ObserverMode)
    (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit : Effect4.Exit β ε δ ι α),
    interp.parkOf (Effect4.Prim.sync thunk) = Option.some (Except.ok (Effect4.Deep.ParkKind.join target mode)) →
      m.fiber? target = Option.some t →
        t.exit = Option.some exit →
          have g :=
            { id := f.id,
              frame :=
                have __src := f.frame;
                { current := Effect4.Prim.sync thunk, stack := __src.stack, interruptible := __src.interruptible,
                  interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
              running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
              currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield,
              preventYield := f.preventYield, yieldOverride := f.yieldOverride, observers := f.observers,
              children := f.children, dispatcher := f.dispatcher, context := f.context };
          Effect4.Deep.evaluatePrim interp m g yielding =
            { machine := m,
              fiber :=
                { id := g.id,
                  frame :=
                    have __src := g.frame;
                    { current := interp.exitValue exit mode, stack := __src.stack, interruptible := __src.interruptible,
                      interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
                  running := g.running, parked := g.parked, pending := g.pending, finalizing := g.finalizing,
                  exit := g.exit, currentOpCount := g.currentOpCount, maxOpsBeforeYield := g.maxOpsBeforeYield,
                  preventYield := g.preventYield, yieldOverride := g.yieldOverride, observers := g.observers,
                  children := g.children, dispatcher := g.dispatcher, context := g.context },
              yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := [] })

#check (@Effect4.Deep.evaluatePrim_join_live :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (target : Effect4.FiberId) (mode : Effect4.Supervision.ObserverMode)
    (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    interp.parkOf (Effect4.Prim.sync thunk) = Option.some (Except.ok (Effect4.Deep.ParkKind.join target mode)) →
      m.fiber? target = Option.some t →
        t.exit = Option.none →
          have g :=
            { id := f.id,
              frame :=
                have __src := f.frame;
                { current := Effect4.Prim.sync thunk, stack := __src.stack, interruptible := __src.interruptible,
                  interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
              running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
              currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield,
              preventYield := f.preventYield, yieldOverride := f.yieldOverride, observers := f.observers,
              children := f.children, dispatcher := f.dispatcher, context := f.context };
          Effect4.Deep.evaluatePrim interp m g yielding =
            {
              machine :=
                (({ fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken + 1,
                          nextRace := m.nextRace, middlewareInstalled := m.middlewareInstalled, state := m.state,
                          trace := m.trace, stuck := m.stuck } : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St).update
                      { id := t.id, frame := t.frame, running := t.running, parked := t.parked, pending := t.pending,
                        finalizing := t.finalizing, exit := t.exit, currentOpCount := t.currentOpCount,
                        maxOpsBeforeYield := t.maxOpsBeforeYield, preventYield := t.preventYield,
                        yieldOverride := t.yieldOverride,
                        observers := t.observers ++ [Effect4.Deep.Observer.resumeAwait g.id m.nextToken mode],
                        children := t.children, dispatcher := t.dispatcher, context := t.context }).emit
                  [Effect4.Deep.RunEvent.parkedOn g.id m.nextToken],
              fiber :=
                g.park
                  { token := m.nextToken, waitingOn := Option.some target, remaining := 0, collected := [],
                    resumeWith := Effect4.Deep.Resume.void, failFast := Bool.false, outstanding := [] },
              yielding := yielding, outcome := Effect4.Deep.Outcome.parked, nested := [] })

#check (@Effect4.Deep.evaluatePrim_join_unknown :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (thunk : σ) (target : Effect4.FiberId) (mode : Effect4.Supervision.ObserverMode),
    interp.parkOf (Effect4.Prim.sync thunk) = Option.some (Except.ok (Effect4.Deep.ParkKind.join target mode)) →
      m.fiber? target = Option.none →
        have g :=
          { id := f.id,
            frame :=
              have __src := f.frame;
              { current := Effect4.Prim.sync thunk, stack := __src.stack, interruptible := __src.interruptible,
                interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
            running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
            currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
            yieldOverride := f.yieldOverride, observers := f.observers, children := f.children,
            dispatcher := f.dispatcher, context := f.context };
        (Effect4.Deep.evaluatePrim interp m g yielding).outcome =
          Effect4.Deep.Outcome.stuck (Effect4.Deep.Stuck.unknownFiber target))

#check (@Effect4.Deep.withFiber_snapshotChildren :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding Effect4.Deep.WithFiberAction.snapshotChildren =
      { machine := m,
        fiber :=
          { id := f.id,
            frame :=
              have __src := f.frame;
              { current := Effect4.Prim.success (interp.fibersValue f.children), stack := __src.stack,
                interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                deferredInterrupt := __src.deferredInterrupt },
            running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
            currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
            yieldOverride := f.yieldOverride, observers := f.observers, children := f.children,
            dispatcher := f.dispatcher, context := f.context },
        yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := [] })

#check (@Effect4.Deep.withFiber_awaitNewChildren :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (snapshot : List Effect4.FiberId),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.awaitNewChildren snapshot) =
      have r :=
        Effect4.Deep.countdownPark interp m f (List.filter (fun c => !snapshot.contains c) f.children)
          Effect4.Deep.Resume.void;
      { machine := r.fst, fiber := r.snd.fst, yielding := yielding,
        outcome :=
          match r.fst.stuck with
          | Option.some why => Effect4.Deep.Outcome.stuck why
          | Option.none => if r.snd.snd = Bool.true then Effect4.Deep.Outcome.parked else Effect4.Deep.Outcome.continue_,
        nested := [] })

#check (@Effect4.Deep.withFiber_runIn :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (target : Effect4.FiberId) (scope key : Nat),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.runIn target scope key) =
      have r :=
        Effect4.Deep.linkScope interp m Effect4.Supervision.ScopeMode.fiberRunIn scope key target (Option.some target)
          Effect4.ReasonAnnotations.empty;
      { machine := r.fst,
        fiber :=
          { id := f.id,
            frame :=
              have __src := f.frame;
              { current := Effect4.Prim.success interp.voidValue, stack := __src.stack,
                interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                deferredInterrupt := __src.deferredInterrupt },
            running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
            currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
            yieldOverride := f.yieldOverride, observers := f.observers, children := f.children,
            dispatcher := f.dispatcher, context := f.context },
        yielding := yielding,
        outcome :=
          match r.fst.stuck with
          | Option.some why => Effect4.Deep.Outcome.stuck why
          | Option.none => Effect4.Deep.Outcome.continue_,
        nested := r.snd })

#check (@Effect4.Deep.linkScope_closed :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (mode : Effect4.Supervision.ScopeMode) (scope key : Nat) (target : Effect4.FiberId)
    (interruptor : Option Effect4.FiberId) (extra : Effect4.ReasonAnnotations α) (exit : Effect4.Exit β ε δ ι α)
    (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    interp.scopeStatus scope m.state = Option.some (Option.some exit) →
      m.fiber? target = Option.some t →
        Effect4.Deep.linkScope interp m mode scope key target interruptor extra =
          have r := Effect4.Deep.interruptRecord interp interruptor extra t;
          ((m.update r.fst).emit
              [Effect4.Deep.RunEvent.scopeClosedOnLink scope target,
                Effect4.Deep.RunEvent.interruptRecorded interruptor target],
            if r.snd = Bool.true then [Effect4.Deep.Cmd.evaluate target] else []))

#check (@Effect4.Deep.linkScope_unknown :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (mode : Effect4.Supervision.ScopeMode) (scope key : Nat) (target : Effect4.FiberId)
    (interruptor : Option Effect4.FiberId) (extra : Effect4.ReasonAnnotations α),
    interp.scopeStatus scope m.state = Option.none →
      Effect4.Deep.linkScope interp m mode scope key target interruptor extra =
        (m.halt (Effect4.Deep.Stuck.unknownScope scope), []))

#check (@Effect4.FrameFiber.step_async_frontier :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} [inst : DecidableEq ε]
    [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α] (interp : Effect4.PrimInterp ν σ β ε δ ι α)
    (self : Effect4.FrameFiber ν σ β ε δ ι α) (register : ν) (withSignal : Bool) (cancel : Option ν),
    Effect4.FrameFiber.step interp
        { current := Effect4.Prim.async register withSignal cancel, stack := self.stack,
          interruptible := self.interruptible, interruptedCause := self.interruptedCause,
          deferredInterrupt := self.deferredInterrupt } =
      (Effect4.FrameStep.running
          { current := Effect4.Prim.async register withSignal cancel, stack := self.stack,
            interruptible := self.interruptible, interruptedCause := self.interruptedCause,
            deferredInterrupt := self.deferredInterrupt },
        []))

#check (@Effect4.Prim.armE_asyncFinalizer_no_interrupt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.PrimInterp ν σ β ε δ ι α) (onInterrupt : ν) (cause : Effect4.Cause ε δ ι α)
    (provided : Option (Effect4.Exit β ε δ ι α)),
    cause.hasInterrupts = Bool.false →
      Effect4.Prim.armE interp (Effect4.Prim.asyncFinalizer onInterrupt) cause provided =
        Option.some (Effect4.Prim.failure cause, []))

#check (@Effect4.Prim.ensure_asyncFinalizer_masks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν)
    (fiber : Effect4.FrameFiber ν σ β ε δ ι α),
    fiber.interruptible = Bool.true →
      (Effect4.Prim.asyncFinalizer onInterrupt).ensure fiber =
        ({ current := fiber.current, stack := Effect4.Prim.setInterruptible Bool.true :: fiber.stack,
            interruptible := Bool.false, interruptedCause := fiber.interruptedCause,
            deferredInterrupt := fiber.deferredInterrupt },
          Option.none))

#check (@Effect4.Prim.arms_asyncFinalizer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u} (onInterrupt : ν),
    (Effect4.Prim.asyncFinalizer onInterrupt).arms = [Effect4.Arm.contE, Effect4.Arm.contAll])

#check (@Effect4.Prim.hasArm_asyncFinalizer_contA_false :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α : Type u}
    (onInterrupt : ν), (Effect4.Prim.asyncFinalizer onInterrupt).hasArm Effect4.Arm.contA = Bool.false)

#check (@Effect4.Deep.closeSeqChain_order :
  ∀ (fin : Effect4.Deep.FinName) (rest : List Effect4.Deep.FinName)
    (exit : Effect4.Deep.ExitV)
    (captured : List (Effect4.Reason Effect4.Deep.Err Effect4.Deep.Defect Effect4.FiberId Effect4.Deep.Ann)),
    Effect4.Deep.closeSeqChain (fin :: rest) exit captured =
      Effect4.Prim.onSuccessAndFailure (Effect4.Deep.finProgram fin exit) (Effect4.Deep.Name.closeSeq rest exit captured)
        (Effect4.Deep.Name.closeSeq rest exit captured))

#check (@Effect4.Deep.closeSeqChain_captures :
  ∀ (rest : List Effect4.Deep.FinName) (exit : Effect4.Deep.ExitV)
    (captured : List (Effect4.Reason Effect4.Deep.Err Effect4.Deep.Defect Effect4.FiberId Effect4.Deep.Ann))
    (cause : Effect4.Deep.CauseV),
    Effect4.Deep.contEOf (Effect4.Deep.Name.closeSeq rest exit captured) cause =
      Effect4.Deep.closeSeqChain rest exit (captured ++ cause.reasons))

#check (@Effect4.Deep.closeParChain_forks_immediate_daemon :
  ∀ (fin : Effect4.Deep.FinName) (rest : List Effect4.Deep.FinName)
    (exit : Effect4.Deep.ExitV) (forked : List Effect4.FiberId),
    Effect4.Deep.closeParChain Bool.true (fin :: rest) exit forked =
      (Effect4.Prim.withFiber
            (Effect4.Deep.Thunk.act
              (Effect4.Deep.ActionName.fork (Effect4.Deep.ProgName.finalizerOf fin exit)
                { startImmediately := Bool.true, daemon := Bool.true,
                  maskMode := Effect4.Supervision.MaskMode.interruptible }))).onSuccess
        (Effect4.Deep.Name.closePar rest exit forked Bool.true))

#check (@Effect4.Deep.closeParChain_awaits_all :
  ∀ (exit : Effect4.Deep.ExitV) (forked : List Effect4.FiberId),
    Effect4.Deep.closeParChain Bool.true [] exit forked =
      (Effect4.Prim.withFiber (Effect4.Deep.Thunk.act (Effect4.Deep.ActionName.awaitAll forked))).onSuccess
        Effect4.Deep.Name.mergeAwaitedExits)

#check (@Effect4.Deep.closeSeqChain_merges :
  ∀ (exit : Effect4.Deep.ExitV)
    (captured : List (Effect4.Reason Effect4.Deep.Err Effect4.Deep.Defect Effect4.FiberId Effect4.Deep.Ann)),
    Effect4.Deep.closeSeqChain [] exit captured = Effect4.Prim.ofExit (Effect4.Deep.voidAllOf captured))

#check (@Effect4.Deep.scopeLinkFiber_name :
  ∀ (scope key : Nat) (fiber : Effect4.FiberId) (state : Effect4.Deep.Stores)
    (entry : Effect4.Deep.ScopeEntry),
    state.scopes.entryAt scope = Option.some entry →
      Effect4.Deep.stores.scopeLinkFiber Effect4.Supervision.ScopeMode.forkIn scope key fiber state =
        Option.some
          { refs := state.refs, deferreds := state.deferreds,
            scopes := (state.scopes.addFinalizer scope key (Effect4.Deep.FinName.interruptFiber fiber Bool.true)).fst,
            nextName := state.nextName })

#check (@Effect4.Deep.scopeStore_forkChild_names :
  ∀ (self : Effect4.Deep.ScopeStore) (parentKey childKey sharedKey : Nat)
    (strategy : Effect4.FinalizerStrategy) (parent : Effect4.Deep.ScopeEntry),
    self.entryAt parentKey = Option.some parent →
      Effect4.Scope.closingExit? parent.scope = Option.none →
        (self.forkChild parentKey childKey sharedKey strategy).entries =
          (self.setEntry
                { key := parent.key,
                  scope :=
                    Effect4.Scope.addUnsafe parent.scope sharedKey
                      (Effect4.Deep.FinName.closeChildScope childKey) }).entries ++
            [{ key := childKey,
                scope :=
                  (Effect4.Scope.make strategy).addUnsafe sharedKey
                    (Effect4.Deep.FinName.detachFromParent parentKey sharedKey) }])

#check (@Effect4.Deep.Layers.scoped_installs_and_restores :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (body : Effect4.Deep.Layers.ProgName) (prev : Effect4.Deep.Env.Ctx) (scope : Nat) (value : Effect4.Deep.Env.Val)
    (exit : Effect4.Deep.Env.ExitV),
    Effect4.Deep.Layers.scopedProgram body =
        Effect4.Prim.onSuccess (Effect4.Deep.Layers.act Effect4.Deep.Layers.ActionName.getContext)
          (Effect4.Deep.Layers.Name.scopedThen body) ∧
      Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.scopedThen body) (Effect4.Deep.Env.encode prev) =
          Effect4.Prim.onSuccess
            (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.scopeMake Effect4.FinalizerStrategy.sequential))
            (Effect4.Deep.Layers.Name.scopedInstall body prev) ∧
        Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.scopedInstall body prev)
              (Effect4.Deep.Env.Val.scopeHandle scope) =
            Effect4.Prim.onSuccess
              (Effect4.Deep.Layers.act
                (Effect4.Deep.Layers.ActionName.setContext
                  (Effect4.Deep.Env.Context.addV prev Effect4.Deep.Env.scopeKey
                    (Effect4.Deep.Env.Val.scopeHandle scope))))
              (Effect4.Deep.Layers.Name.scopedBody body prev scope) ∧
          Effect4.Deep.Env.ambientScope
                (Effect4.Deep.Env.Context.addV prev Effect4.Deep.Env.scopeKey (Effect4.Deep.Env.Val.scopeHandle scope)) =
              Option.some scope ∧
            Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.scopedBody body prev scope) value =
                Effect4.Prim.scopedFrame (Effect4.Deep.Layers.progOf table body)
                  (Effect4.Deep.Layers.Name.finalizerName (Effect4.Deep.Layers.FinName.scopedExit prev scope)) ∧
              (Effect4.Deep.Layers.interp table).finalizerProgram
                    (Effect4.Deep.Layers.Name.finalizerName (Effect4.Deep.Layers.FinName.scopedExit prev scope)) exit =
                  Option.some
                    (Effect4.Prim.onSuccess (Effect4.Deep.Layers.act (Effect4.Deep.Layers.ActionName.setContext prev))
                      (Effect4.Deep.Layers.Name.thenClose scope exit)) ∧
                Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.thenClose scope exit) value =
                  Effect4.Deep.Layers.act (Effect4.Deep.Layers.ActionName.closeScope scope exit))

#check (@Effect4.Deep.Layers.acquireRelease_captured_context :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (acquire : Effect4.Deep.Layers.ProgName) (release : Nat) (ctx : Effect4.Deep.Env.Ctx) (scope : Nat)
    (value : Effect4.Deep.Env.Val) (exit : Effect4.Deep.Env.ExitV),
    Effect4.Deep.Layers.acquireReleaseProgram acquire release Bool.true =
        Effect4.Prim.onSuccess (Effect4.Deep.Layers.act Effect4.Deep.Layers.ActionName.getContext)
          (Effect4.Deep.Layers.Name.acquireWith acquire release Bool.true) ∧
      Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.acquireWith acquire release Bool.true)
            (Effect4.Deep.Env.encode ctx) =
          Effect4.Deep.Layers.act
            (Effect4.Deep.Layers.ActionName.setInterruptible (acquire.acquireMasked release ctx Bool.true) Bool.false) ∧
        Effect4.Deep.Layers.progOf table (acquire.acquireMasked release ctx Bool.true) =
            Effect4.Prim.onSuccess (Effect4.Deep.Layers.serviceProgram Effect4.Deep.Env.scopeKey)
              (Effect4.Deep.Layers.Name.acquireInScope acquire release ctx Bool.true) ∧
          Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.acquireInScope acquire release ctx Bool.true)
                (Effect4.Deep.Env.Val.scopeHandle scope) =
              Effect4.Prim.onSuccess
                (Effect4.Deep.Layers.act (Effect4.Deep.Layers.ActionName.setInterruptible acquire Bool.true))
                (Effect4.Deep.Layers.Name.registerRelease scope release ctx) ∧
            Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.acquireInScope acquire release ctx Bool.false)
                  (Effect4.Deep.Env.Val.scopeHandle scope) =
                Effect4.Prim.onSuccess (Effect4.Deep.Layers.progOf table acquire)
                  (Effect4.Deep.Layers.Name.registerRelease scope release ctx) ∧
              Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.registerRelease scope release ctx) value =
                  Effect4.Prim.onSuccess
                    (Effect4.Deep.Layers.scopeAddProgram scope (Effect4.Deep.Layers.FinName.releaseWith release ctx))
                    (Effect4.Deep.Layers.Name.constant value) ∧
                Effect4.Deep.Layers.finProgram (Effect4.Deep.Layers.FinName.releaseWith release ctx) exit =
                  Effect4.Deep.Layers.updateContextProgram (Effect4.Deep.Env.ContextUpdate.provide ctx)
                    (Effect4.Deep.Layers.ProgName.releaseOf release))

#check (@Effect4.Deep.refStep_make :
  ∀ (heap : Effect4.Deep.RefHeap) (a : Effect4.Deep.Val),
    Effect4.Deep.refStep (Effect4.Deep.SyncOp.refMake a) heap =
      Option.some (Effect4.Deep.Val.cell { index := List.length heap }, heap ++ [a]))

#check (@Effect4.Deep.refMake_twice_distinct :
  ∀ (heap : Effect4.Deep.RefHeap) (a b : Effect4.Deep.Val),
    Option.map Prod.fst (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refMake a) heap) ≠
      (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refMake a) heap).bind fun step =>
        Option.map Prod.fst (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refMake b) step.snd))

#check (@Effect4.Deep.refStep_get :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey) (a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refGet cell) heap = Option.some (a, heap))

#check (@Effect4.Deep.refStep_get_after_set :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey)
    (v a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Option.map Prod.fst (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refGet cell) (Effect4.Deep.refPoke heap cell v)) =
        Option.some v)

#check (@Effect4.Deep.refStep_set :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey) (v a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refSet cell v) heap =
        Option.some (Effect4.Deep.Val.cell cell, Effect4.Deep.refPoke heap cell v))

#check (@Effect4.Deep.set_answer_ne_update_answer :
  ∀ (cell : Effect4.Deep.RefKey),
    Effect4.Deep.Val.cell cell ≠ Effect4.Deep.Val.unit)

#check (@Effect4.Deep.refStep_set_answers_self :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey)
    (v a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Option.map Prod.fst (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refSet cell v) heap) =
          Option.some (Effect4.Deep.Val.cell cell) ∧
        Option.map Prod.snd (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refSet cell v) heap) =
          Option.some (Effect4.Deep.refPoke heap cell v))

#check (@Effect4.Deep.refStep_getAndSet :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey) (v a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refGetAndSet cell v) heap =
        Option.some (a, Effect4.Deep.refPoke heap cell v))

#check (@Effect4.Deep.refStep_setAndGet :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey) (v a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refSetAndGet cell v) heap =
        Option.some (v, Effect4.Deep.refPoke heap cell v))

#check (@Effect4.Deep.refStep_update :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey) (f : Effect4.Deep.FnName)
    (a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refUpdate cell f) heap =
        Option.some (Effect4.Deep.Val.unit, Effect4.Deep.refPoke heap cell (f.total a)))

#check (@Effect4.Deep.refStep_update_applies_once :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey)
    (a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      a = Effect4.Deep.Val.nat 0 →
        Option.map Prod.snd (Effect4.Deep.refStep (Effect4.Deep.SyncOp.refUpdate cell Effect4.Deep.FnName.incr) heap) =
          Option.some (Effect4.Deep.refPoke heap cell (Effect4.Deep.Val.nat 1)))

#check (@Effect4.Deep.refStep_modify :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey) (f : Effect4.Deep.FnName)
    (a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refModify cell f) heap =
        Option.some ((f.modify a).fst, Effect4.Deep.refPoke heap cell (f.modify a).snd))

#check (@Effect4.Deep.refStep_modifySome_eq_modify :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey)
    (pf : Effect4.Deep.FnName) (a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refModifySome cell pf) heap =
        Option.some ((pf.modifySome a).fst, Effect4.Deep.refPoke heap cell ((pf.modifySome a).snd.getD a)))

#check (@Effect4.Deep.refStep_modifySome_none :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey)
    (a : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      Effect4.Deep.refStep (Effect4.Deep.SyncOp.refModifySome cell Effect4.Deep.FnName.noChange) heap =
        Option.some (a, Effect4.Deep.refPoke heap cell a))

#check (@Effect4.Deep.refStep_updateSomeAndGet_some :
  ∀ (heap : Effect4.Deep.RefHeap) (cell : Effect4.Deep.RefKey)
    (pf : Effect4.Deep.FnName) (a a' : Effect4.Deep.Val),
    Effect4.Deep.refPeek heap cell = Option.some a →
      pf.partialUpdate a = Option.some a' →
        Effect4.Deep.refStep (Effect4.Deep.SyncOp.refUpdateSomeAndGet cell pf) heap =
          Option.map (fun fresh => (fresh, Effect4.Deep.refPoke heap cell a'))
            (Effect4.Deep.refPeek (Effect4.Deep.refPoke heap cell a') cell))

#check (@Effect4.Deep.deferredStore_make :
  ∀ (self : Effect4.Deep.DeferredStore),
    self.make =
      ({ index := self.cells.length },
        { cells := self.cells ++ [{ completion := Option.none, waiters := [] }], due := self.due }))

#check (@Effect4.Deep.deferredStore_isDone :
  ∀ (self : Effect4.Deep.DeferredStore) (cell : Effect4.Deep.DeferredKey)
    (c : Effect4.Deep.DeferredCell), self.cellAt cell = Option.some c → self.isDone cell = Option.some c.completion.isSome)

#check (@Effect4.Deep.awaitDeferred_is_a_park :
  ∀ (cell : Effect4.Deep.DeferredKey),
    Effect4.Deep.progOf (Effect4.Deep.ProgName.awaitDeferred cell) =
      Effect4.Prim.async (Effect4.Deep.Name.registerAwait cell) Bool.true
        (Option.some (Effect4.Deep.Name.cancelAwait cell)))

#check (@Effect4.Deep.deferredStore_register_pending :
  ∀ (self : Effect4.Deep.DeferredStore) (cell : Effect4.Deep.DeferredKey)
    (c : Effect4.Deep.DeferredCell) (waiter : Effect4.FiberId) (token : Nat),
    self.cellAt cell = Option.some c →
      c.completion = Option.none →
        self.register cell waiter token =
          (self.setCell cell { completion := c.completion, waiters := c.waiters ++ [(waiter, token)] }, Option.none))

#check (@Effect4.Deep.deferredStore_register_done :
  ∀ (self : Effect4.Deep.DeferredStore) (cell : Effect4.Deep.DeferredKey)
    (c : Effect4.Deep.DeferredCell) (e : Effect4.Deep.Program) (waiter : Effect4.FiberId) (token : Nat),
    self.cellAt cell = Option.some c →
      c.completion = Option.some e → self.register cell waiter token = (self, Option.some e))

#check (@Effect4.Deep.deferredStore_complete_done :
  ∀ (self : Effect4.Deep.DeferredStore) (cell : Effect4.Deep.DeferredKey)
    (c : Effect4.Deep.DeferredCell) (e e' : Effect4.Deep.Program),
    self.cellAt cell = Option.some c → c.completion = Option.some e → self.complete cell e' = (self, Bool.false))

#check (@Effect4.Deep.deferredStore_complete_pending :
  ∀ (self : Effect4.Deep.DeferredStore) (cell : Effect4.Deep.DeferredKey)
    (c : Effect4.Deep.DeferredCell) (e : Effect4.Deep.Program),
    self.cellAt cell = Option.some c →
      c.completion = Option.none →
        self.complete cell e =
          (have __src := self.setCell cell { completion := Option.some e, waiters := [] };
            { cells := __src.cells, due := self.due ++ List.map (fun w => (w.fst, w.snd, e)) c.waiters },
            Bool.true))

#check (@Effect4.Deep.deferredStore_complete_stores_argument :
  ∀ (self : Effect4.Deep.DeferredStore)
    (cell : Effect4.Deep.DeferredKey) (c : Effect4.Deep.DeferredCell) (e : Effect4.Deep.Program),
    self.cellAt cell = Option.some c →
      c.completion = Option.none →
        Option.map Effect4.Deep.DeferredCell.completion ((self.complete cell e).fst.cellAt cell) =
          Option.some (Option.some e))

#check (@Effect4.Deep.deferredStore_waiter_receives_stored :
  ∀ (self : Effect4.Deep.DeferredStore)
    (cell : Effect4.Deep.DeferredKey) (c : Effect4.Deep.DeferredCell) (e : Effect4.Deep.Program)
    (waiter : Effect4.FiberId) (token : Nat),
    self.cellAt cell = Option.some c →
      c.completion = Option.none →
        c.waiters = [(waiter, token)] → (self.complete cell e).fst.due = self.due ++ [(waiter, token, e)])

#check (@Effect4.Deep.doneWith_shared :
  ∀ (exit : Effect4.Deep.ExitV),
    Effect4.Prim.asExit? (Effect4.Deep.completionPrim (Effect4.Deep.Completion.ofExit exit)) = Option.some exit)

#check (@Effect4.Deep.completionPrim_ofExit :
  ∀ (exit : Effect4.Deep.ExitV),
    Effect4.Deep.completionPrim (Effect4.Deep.Completion.ofExit exit) = Effect4.Prim.ofExit exit)

#check (@Effect4.Deep.interruptDeferred_delegates :
  ∀ (cell : Effect4.Deep.DeferredKey) (id : Effect4.FiberId),
    Effect4.Deep.contAOf (Effect4.Deep.Name.interruptWith cell) (Effect4.Deep.Val.fiber id) =
      Effect4.Prim.sync (Effect4.Deep.Thunk.op (Effect4.Deep.SyncOp.deferredInterruptWith cell id)))

#check (@Effect4.Deep.interruptWith_is_completion :
  ∀ (st : Effect4.Deep.Stores) (cell : Effect4.Deep.DeferredKey)
    (interruptor : Effect4.FiberId),
    Effect4.Deep.syncOpStep (Effect4.Deep.SyncOp.deferredInterruptWith cell interruptor) st =
      Effect4.Deep.syncOpStep
        (Effect4.Deep.SyncOp.deferredCompleteWith cell
          (Effect4.Deep.Completion.ofExit (Effect4.Exit.failure (Effect4.Cause.interrupt (Option.some interruptor)))))
        st)

#check (@Effect4.Deep.intoDeferred_spelling :
  ∀ (body : Effect4.Deep.ProgName) (cell : Effect4.Deep.DeferredKey),
    Effect4.Deep.progOf (body.intoDeferred cell) =
      Effect4.Prim.withFiber
        (Effect4.Deep.Thunk.act (Effect4.Deep.ActionName.setInterruptible (body.intoBody cell) Bool.false)))

#check (@Effect4.Deep.deferredPoll_no_write :
  ∀ (st : Effect4.Deep.Stores) (cell : Effect4.Deep.DeferredKey),
    Option.map Prod.fst (Effect4.Deep.syncOpStep (Effect4.Deep.SyncOp.deferredPoll cell) st) =
      Option.map (fun x => st) (st.deferreds.poll cell))

#check (@Effect4.Deep.Layers.fromBuildUnsafe_no_scope :
  ∀ (services : List (Effect4.ServiceKey × Effect4.Deep.Env.Val))
    (scope : Nat),
    Effect4.Deep.Layers.constructionProgram (Effect4.Deep.Layers.Construction.succeedContext services) scope =
      Effect4.Prim.success (Effect4.Deep.Env.encode (Effect4.Deep.Layers.ctxOfList services)))

#check (@Effect4.Deep.Layers.fromBuild_forks_child :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer inner : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId) (scope : Nat),
    table[layer.index]? = Option.some (Effect4.Deep.Layers.LayerDesc.childScope inner) →
      Effect4.Deep.Layers.layerBuildProgram table layer memoMap scope =
        Effect4.Prim.onSuccess
          (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.scopeFork scope Effect4.FinalizerStrategy.sequential))
          (Effect4.Deep.Layers.Name.fromBuildThen (Effect4.Deep.Layers.LayerDesc.childScope inner) layer memoMap))

#check (@Effect4.Deep.Layers.fromBuild_closes_on_failure :
  ∀ (child : Nat) (cause : Effect4.Deep.Env.CauseV),
    Effect4.Deep.Layers.finProgram (Effect4.Deep.Layers.FinName.closeChildOnFailure child) (Effect4.Exit.failure cause) =
      Effect4.Deep.Layers.act (Effect4.Deep.Layers.ActionName.closeScope child (Effect4.Exit.failure cause)))

#check (@Effect4.Deep.Layers.buildWithMemoMap_installs :
  ∀ (memoMap : Effect4.Deep.Layers.MemoMapId)
    (prev : Effect4.Deep.Env.Ctx),
    Effect4.Deep.Layers.currentMemoMapOf
        ((Effect4.Deep.Env.ContextUpdate.provideService Effect4.Deep.Env.currentMemoMapKey
              (Effect4.Deep.Env.Val.memoMap memoMap.index)).apply
          prev) =
      Option.some memoMap)

#check (@Effect4.Deep.Layers.buildWithMemoMap_provides :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId) (scope : Nat),
    Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.buildWithMemoMap layer memoMap scope) =
      Effect4.Deep.Layers.updateContextProgram
        (Effect4.Deep.Env.ContextUpdate.provideService Effect4.Deep.Env.currentMemoMapKey
          (Effect4.Deep.Env.Val.memoMap memoMap.index))
        (Effect4.Deep.Layers.ProgName.buildAdding layer memoMap scope))

#check (@Effect4.Deep.Layers.memoBuild_allocates :
  ∀ (layer : Effect4.Deep.Layers.LayerId)
    (memoMap : Effect4.Deep.Layers.MemoMapId) (st : Effect4.Deep.Layers.St),
    Effect4.Deep.Layers.syncStep (Effect4.Deep.Layers.SyncOp.memoBuild layer memoMap) st =
      Option.some
        ({ memo := st.memo.insertEntry memoMap layer (Effect4.Deep.Layers.memoBuildEntry layer memoMap st),
            scopes := st.scopes.make st.nextName Effect4.FinalizerStrategy.sequential, deferreds := st.deferreds.make.snd,
            nextName := st.nextName + 1 },
          Effect4.Deep.Env.Val.scopeHandle st.nextName))

#check (@Effect4.Deep.Layers.memoBuild_entry :
  ∀ (layer : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId)
    (st : Effect4.Deep.Layers.St),
    (Effect4.Deep.Layers.memoBuildEntry layer memoMap st).observers = 1 ∧
      (Effect4.Deep.Layers.memoBuildEntry layer memoMap st).effect =
          Effect4.Prim.async (Effect4.Deep.Layers.Name.registerAwait st.deferreds.make.fst) Bool.true
            (Option.some (Effect4.Deep.Layers.Name.cancelAwait st.deferreds.make.fst)) ∧
        (Effect4.Deep.Layers.memoBuildEntry layer memoMap st).finalizer =
          Effect4.Deep.Layers.FinName.memoEntry layer memoMap)

#check (@Effect4.Deep.Layers.memoRelease_last :
  ∀ (layer : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId)
    (st : Effect4.Deep.Layers.St) (entry : Effect4.Deep.Layers.MemoEntry),
    st.memo.entryAt memoMap layer = Option.some entry →
      entry.observers ≤ 1 →
        Effect4.Deep.Layers.syncStep (Effect4.Deep.Layers.SyncOp.memoRelease layer memoMap) st =
          Option.some
            ({ memo := st.memo.deleteEntry memoMap layer, scopes := st.scopes, deferreds := st.deferreds,
                nextName := st.nextName },
              Effect4.Deep.Env.Val.scopeHandle entry.layerScope))

#check (@Effect4.Deep.Layers.memoRelease_decrements :
  ∀ (layer : Effect4.Deep.Layers.LayerId)
    (memoMap : Effect4.Deep.Layers.MemoMapId) (st : Effect4.Deep.Layers.St) (entry : Effect4.Deep.Layers.MemoEntry),
    st.memo.entryAt memoMap layer = Option.some entry →
      1 < entry.observers →
        Effect4.Deep.Layers.syncStep (Effect4.Deep.Layers.SyncOp.memoRelease layer memoMap) st =
          Option.some
            ({
                memo :=
                  st.memo.updateEntry memoMap layer fun e =>
                    { observers := e.observers - 1, effect := e.effect, layerScope := e.layerScope,
                      deferred := e.deferred, finalizer := e.finalizer },
                scopes := st.scopes, deferreds := st.deferreds, nextName := st.nextName },
              Effect4.Deep.Env.Val.unit))

#check (@Effect4.Deep.Layers.memoGet_hit :
  ∀ (layer : Effect4.Deep.Layers.LayerId)
    (memoMap owner : Effect4.Deep.Layers.MemoMapId) (st : Effect4.Deep.Layers.St) (entry : Effect4.Deep.Layers.MemoEntry),
    st.memo.get layer memoMap = Option.some (owner, entry) →
      Effect4.Deep.Layers.syncStep (Effect4.Deep.Layers.SyncOp.memoGet layer memoMap) st =
        Option.some
          ({
              memo :=
                st.memo.updateEntry owner layer fun e =>
                  { observers := e.observers + 1, effect := e.effect, layerScope := e.layerScope, deferred := e.deferred,
                    finalizer := e.finalizer },
              scopes := st.scopes, deferreds := st.deferreds, nextName := st.nextName },
            (Effect4.Deep.Env.Val.promise entry.deferred.index).pair (Effect4.Deep.Env.Val.memoMap owner.index)))

#check (@Effect4.Deep.Layers.memoize_hit :
  ∀ (table : Effect4.Deep.Layers.LayerTable) (layer : Effect4.Deep.Layers.LayerId)
    (memoMap : Effect4.Deep.Layers.MemoMapId) (scope : Nat) (c : Effect4.Deep.Layers.Construction) (cell owner : Nat),
    Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.memoize layer memoMap scope c)
        ((Effect4.Deep.Env.Val.promise cell).pair (Effect4.Deep.Env.Val.memoMap owner)) =
      Effect4.Prim.onSuccess
        (Effect4.Deep.Layers.scopeAddProgram scope (Effect4.Deep.Layers.FinName.memoEntry layer { index := owner }))
        (Effect4.Deep.Layers.Name.awaitPromise { index := cell }))

#check (@Effect4.Deep.Layers.MemoWorld.get_parent :
  ∀ (w : Effect4.Deep.Layers.MemoWorld) (layer : Effect4.Deep.Layers.LayerId)
    (id parent : Effect4.Deep.Layers.MemoMapId) (m : Effect4.Deep.Layers.MemoMap),
    w.entryAt id layer = Option.none →
      w.mapAt id = Option.some m → m.parent = Option.some parent → w.get layer id = w.lookup layer (List.length w) parent)

#check (@Effect4.Deep.Layers.getOrElseMemoize_shape :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId) (scope : Nat)
    (c : Effect4.Deep.Layers.Construction) (cell : Effect4.Deep.Layers.DeferredKey) (value : Effect4.Deep.Env.Val),
    Effect4.Deep.Layers.getOrElseMemoizeProgram layer memoMap scope c =
        Effect4.Prim.suspend
          (Effect4.Deep.Layers.Thunk.body (Effect4.Deep.Layers.ProgName.memoLookup layer memoMap scope c)) ∧
      Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.memoLookup layer memoMap scope c) =
          Effect4.Prim.onSuccess (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.memoGet layer memoMap))
            (Effect4.Deep.Layers.Name.memoize layer memoMap scope c) ∧
        Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.awaitPromise cell) value =
            Effect4.Prim.async (Effect4.Deep.Layers.Name.registerAwait cell) Bool.true
              (Option.some (Effect4.Deep.Layers.Name.cancelAwait cell)) ∧
          Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.memoize layer memoMap scope c)
              Effect4.Deep.Env.Val.unit =
            Effect4.Deep.Layers.memoBuildProgram layer memoMap scope c)

#check (@Effect4.Deep.Layers.forkOrCreate :
  ∀ (ctx : Effect4.Deep.Env.Ctx) (id : Nat)
    (parent : Option Effect4.Deep.Layers.MemoMapId) (st : Effect4.Deep.Layers.St),
    Effect4.Deep.Layers.currentMemoMapOf
          (Effect4.Deep.Env.Context.addV ctx Effect4.Deep.Env.currentMemoMapKey (Effect4.Deep.Env.Val.memoMap id)) =
        Option.some { index := id } ∧
      Effect4.Deep.Layers.currentMemoMapOf Effect4.Deep.Env.Context.empty = Option.none ∧
        Effect4.Deep.Layers.syncStep (Effect4.Deep.Layers.SyncOp.memoFork parent) st =
          Option.some
            ({ memo := st.memo ++ [{ id := { index := st.nextName }, parent := parent, entries := [] }],
                scopes := st.scopes, deferreds := st.deferreds, nextName := st.nextName + 1 },
              Effect4.Deep.Env.Val.memoMap st.nextName))

#check (@Effect4.Deep.Layers.build_uses_ambient_scope :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer : Effect4.Deep.Layers.LayerId) (ctx : Effect4.Deep.Env.Ctx) (id scope : Nat),
    Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.build layer) =
        Effect4.Prim.onSuccess (Effect4.Deep.Layers.act Effect4.Deep.Layers.ActionName.getContext)
          (Effect4.Deep.Layers.Name.buildFromContext layer) ∧
      Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.buildFromContext layer) (Effect4.Deep.Env.encode ctx) =
          Effect4.Prim.onSuccess
            (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.memoFork (Effect4.Deep.Layers.currentMemoMapOf ctx)))
            (Effect4.Deep.Layers.Name.withMemoMapThen layer (Effect4.Deep.Env.ambientScope ctx)) ∧
        Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.withMemoMapThen layer Option.none)
              (Effect4.Deep.Env.Val.memoMap id) =
            Effect4.Prim.failure (Effect4.Cause.die (Effect4.Deep.Env.Defect.serviceNotFound Effect4.Deep.Env.scopeKey)) ∧
          Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.withMemoMapThen layer (Option.some scope))
              (Effect4.Deep.Env.Val.memoMap id) =
            Effect4.Deep.Layers.buildWithMemoMapProgram layer { index := id } scope)

#check (@Effect4.Deep.Layers.buildWithScope_forks_memo :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer : Effect4.Deep.Layers.LayerId) (scope : Nat) (ctx : Effect4.Deep.Env.Ctx),
    Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.buildWithScopeFromContext layer scope)
        (Effect4.Deep.Env.encode ctx) =
      Effect4.Prim.onSuccess
        (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.memoFork (Effect4.Deep.Layers.currentMemoMapOf ctx)))
        (Effect4.Deep.Layers.Name.withMemoMapThen layer (Option.some scope)))

#check (@Effect4.Deep.Layers.mergeAll_scopes :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer self : Effect4.Deep.Layers.LayerId) (layers rest : List Effect4.Deep.Layers.LayerId)
    (l : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId) (scope child parent : Nat)
    (forked : List Effect4.FiberId) (exits : List Effect4.Deep.Env.ExitV),
    table[layer.index]? = Option.some (Effect4.Deep.Layers.LayerDesc.mergeAll layers) →
      Effect4.Deep.Layers.layerBuildProgram table layer memoMap scope =
          Effect4.Prim.onSuccess
            (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.scopeFork scope Effect4.FinalizerStrategy.sequential))
            (Effect4.Deep.Layers.Name.fromBuildThen (Effect4.Deep.Layers.LayerDesc.mergeAll layers) layer memoMap) ∧
        Effect4.Deep.Layers.innerBuildProgram table (Effect4.Deep.Layers.LayerDesc.mergeAll layers) self memoMap child =
            Effect4.Prim.onSuccess
              (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.scopeFork child Effect4.FinalizerStrategy.parallel))
              (Effect4.Deep.Layers.Name.mergeChildren layers memoMap) ∧
          Effect4.Deep.Layers.mergeForkAll memoMap parent (l :: rest) forked =
              Effect4.Prim.onSuccess
                (Effect4.Deep.Layers.syncOp
                  (Effect4.Deep.Layers.SyncOp.scopeFork parent Effect4.FinalizerStrategy.sequential))
                (Effect4.Deep.Layers.Name.mergeForkOne l rest memoMap parent forked) ∧
            Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.mergeForkOne l rest memoMap parent forked)
                  (Effect4.Deep.Env.Val.scopeHandle child) =
                Effect4.Prim.onSuccess
                  (Effect4.Deep.Layers.act
                    (Effect4.Deep.Layers.ActionName.fork (Effect4.Deep.Layers.ProgName.layerBuild l memoMap child)
                      { startImmediately := Bool.true, daemon := Bool.false,
                        maskMode := Effect4.Supervision.MaskMode.inherit }))
                  (Effect4.Deep.Layers.Name.mergeForkNext rest memoMap parent forked) ∧
              Effect4.Deep.Layers.mergeForkAll memoMap parent [] forked =
                  Effect4.Prim.onSuccess
                    (Effect4.Deep.Layers.act (Effect4.Deep.Layers.ActionName.awaitAllFailFast forked))
                    Effect4.Deep.Layers.Name.mergeContexts ∧
                Effect4.Deep.Layers.contAOf table Effect4.Deep.Layers.Name.mergeContexts
                    (Effect4.Deep.Layers.exitsVal exits) =
                  Effect4.Deep.Layers.mergeExitContexts exits)

#check (@Effect4.Deep.Layers.provide_dependency_first :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer self that : Effect4.Deep.Layers.LayerId) (mode : Effect4.Deep.Layers.CombineMode)
    (memoMap : Effect4.Deep.Layers.MemoMapId) (scope child : Nat) (ctx merged : Effect4.Deep.Env.Ctx),
    table[layer.index]? = Option.some (Effect4.Deep.Layers.LayerDesc.provideWith self that mode) →
      Effect4.Deep.Layers.layerBuildProgram table layer memoMap scope =
          Effect4.Prim.onSuccess
            (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.scopeFork scope Effect4.FinalizerStrategy.sequential))
            (Effect4.Deep.Layers.Name.fromBuildThen (Effect4.Deep.Layers.LayerDesc.provideWith self that mode) layer
              memoMap) ∧
        Effect4.Deep.Layers.innerBuildProgram table (Effect4.Deep.Layers.LayerDesc.provideWith self that mode) layer
              memoMap child =
            Effect4.Prim.onSuccess (Effect4.Deep.Layers.layerBuildProgram table that memoMap child)
              (Effect4.Deep.Layers.Name.provideThen self memoMap child mode) ∧
          Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.provideThen self memoMap child mode)
                (Effect4.Deep.Env.encode ctx) =
              Effect4.Prim.onSuccess
                (Effect4.Deep.Layers.updateContextProgram (Effect4.Deep.Env.ContextUpdate.provide ctx)
                  (Effect4.Deep.Layers.ProgName.layerBuild self memoMap child))
                (Effect4.Deep.Layers.Name.combineWith mode ctx) ∧
            Effect4.Deep.Layers.contAOf table
                  (Effect4.Deep.Layers.Name.combineWith Effect4.Deep.Layers.CombineMode.provide ctx)
                  (Effect4.Deep.Env.encode merged) =
                Effect4.Prim.success (Effect4.Deep.Env.encode merged) ∧
              Effect4.Deep.Layers.contAOf table
                  (Effect4.Deep.Layers.Name.combineWith Effect4.Deep.Layers.CombineMode.provideMerge ctx)
                  (Effect4.Deep.Env.encode merged) =
                Effect4.Prim.success (Effect4.Deep.Env.encode (Effect4.Deep.Env.Context.merge ctx merged)))

#check (@Effect4.Deep.Layers.fresh_drops_memoization :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer inner : Effect4.Deep.Layers.LayerId) (memoMap : Effect4.Deep.Layers.MemoMapId) (scope id : Nat),
    table[layer.index]? = Option.some (Effect4.Deep.Layers.LayerDesc.fresh inner) →
      Effect4.Deep.Layers.layerBuildProgram table layer memoMap scope =
          Effect4.Prim.onSuccess (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.memoFork Option.none))
            (Effect4.Deep.Layers.Name.freshThen inner scope) ∧
        Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.freshThen inner scope)
            (Effect4.Deep.Env.Val.memoMap id) =
          Effect4.Deep.Layers.layerBuildProgram table inner { index := id } scope)

#check (@Effect4.Deep.Layers.launch_holds_scope :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer : Effect4.Deep.Layers.LayerId) (fiber : Effect4.FiberId) (token : Nat) (st : Effect4.Deep.Layers.St),
    Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.launch layer) =
        Effect4.Deep.Layers.scopedProgram (Effect4.Deep.Layers.ProgName.buildThenNever layer) ∧
      Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.buildThenNever layer) =
          Effect4.Prim.onSuccess (Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.build layer))
            (Effect4.Deep.Layers.Name.seq Effect4.Deep.Layers.ProgName.never) ∧
        Effect4.Deep.Layers.progOf table Effect4.Deep.Layers.ProgName.never =
            Effect4.Prim.async Effect4.Deep.Layers.Name.neverRegister Bool.false Option.none ∧
          (Effect4.Deep.Layers.interp table).registerAsync Effect4.Deep.Layers.Name.neverRegister fiber token st =
            (st, Option.none))

#check (@Effect4.Deep.Layers.provideLayer_scope :
  ∀ (table : Effect4.Deep.Layers.LayerTable)
    (layer : Effect4.Deep.Layers.LayerId) (isLocal : Bool) (body : Effect4.Deep.Layers.ProgName) (scope : Nat)
    (ctx : Effect4.Deep.Env.Ctx) (exit : Effect4.Deep.Env.ExitV),
    Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.provideLayer layer isLocal body) =
        Effect4.Prim.suspend
          (Effect4.Deep.Layers.Thunk.body (Effect4.Deep.Layers.ProgName.scopedWithAlloc layer isLocal body)) ∧
      Effect4.Deep.Layers.progOf table (Effect4.Deep.Layers.ProgName.scopedWithAlloc layer isLocal body) =
          Effect4.Prim.onSuccess
            (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.scopeMake Effect4.FinalizerStrategy.sequential))
            (Effect4.Deep.Layers.Name.provideLayerWith layer isLocal body) ∧
        Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.provideLayerWith layer Bool.true body)
              (Effect4.Deep.Env.Val.scopeHandle scope) =
            ((Effect4.Prim.onSuccess (Effect4.Deep.Layers.syncOp (Effect4.Deep.Layers.SyncOp.memoFork Option.none))
                      (Effect4.Deep.Layers.Name.withMemoMapThen layer (Option.some scope))).onSuccess
                  (Effect4.Deep.Layers.Name.provideLayerBody body)).onExit
              (Effect4.Deep.Layers.Name.finalizerName (Effect4.Deep.Layers.FinName.closeScopeWith scope)) Bool.false ∧
          Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.provideLayerWith layer Bool.false body)
                (Effect4.Deep.Env.Val.scopeHandle scope) =
              ((Effect4.Prim.onSuccess (Effect4.Deep.Layers.act Effect4.Deep.Layers.ActionName.getContext)
                        (Effect4.Deep.Layers.Name.buildWithScopeFromContext layer scope)).onSuccess
                    (Effect4.Deep.Layers.Name.provideLayerBody body)).onExit
                (Effect4.Deep.Layers.Name.finalizerName (Effect4.Deep.Layers.FinName.closeScopeWith scope)) Bool.false ∧
            Effect4.Deep.Layers.contAOf table (Effect4.Deep.Layers.Name.provideLayerBody body)
                  (Effect4.Deep.Env.encode ctx) =
                Effect4.Deep.Layers.updateContextProgram (Effect4.Deep.Env.ContextUpdate.provide ctx) body ∧
              Effect4.Deep.Layers.finProgram (Effect4.Deep.Layers.FinName.closeScopeWith scope) exit =
                Effect4.Deep.Layers.act (Effect4.Deep.Layers.ActionName.closeScope scope exit))


/-! Second pass, 2026-09-04: the exit path, the observers, the races and the fork arms of the
reference machine (`Effect4/Deep/Clauses.lean`), and the concrete witnesses over it
(`Effect4/Deep/Witnesses.lean`), whose statements decide by evaluation. -/

#check (@Effect4.Deep.exitFiber_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit : Effect4.Exit β ε δ ι α),
    Effect4.Deep.exitFiber interp m f exit =
      if (m.middlewareInstalled && f.finalizing.isNone && !f.children.isEmpty) = Bool.true then
        Effect4.Deep.exitInterruptChildren interp m f exit
      else Effect4.Deep.exitStore interp m f exit)

#check (@Effect4.Deep.exitFiber_no_middleware :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (exit : Effect4.Exit β ε δ ι α),
    m.middlewareInstalled = Bool.false → Effect4.Deep.exitFiber interp m f exit = Effect4.Deep.exitStore interp m f exit)

#check (@Effect4.Deep.exitStore_fields :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Deep.exitStore interp m f exit).snd.fst.exit = Option.some exit ∧
      (Effect4.Deep.exitStore interp m f exit).snd.fst.finalizing = Option.none ∧
        (Effect4.Deep.exitStore interp m f exit).snd.fst.frame.stack = [] ∧
          (Effect4.Deep.exitStore interp m f exit).snd.fst.children = [] ∧
            (Effect4.Deep.exitStore interp m f exit).snd.fst.parked = Effect4.Deep.Parked.notParked ∧
              (Effect4.Deep.exitStore interp m f exit).snd.fst.pending = [] ∧
                (Effect4.Deep.exitStore interp m f exit).snd.fst.context = interp.emptyContext ∧
                  (Effect4.Deep.exitStore interp m f exit).snd.fst.observers = [] ∧
                    (Effect4.Deep.exitStore interp m f exit).snd.snd.fst = Bool.false)

#check (@Effect4.Deep.exitStore_fires :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Deep.exitStore interp m f exit).snd.snd.snd =
      (List.foldl (Effect4.Deep.fireObserver interp f.id exit)
          ((m.update (Effect4.Deep.exitStore.stored interp f exit)).emit [Effect4.Deep.RunEvent.exited f.id exit], [])
          f.observers).snd)

#check (@Effect4.Deep.fireObserver_resumeAwait :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (waiter : Effect4.FiberId)
    (token : Nat) (mode : Effect4.Supervision.ObserverMode),
    Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.resumeAwait waiter token mode) =
      (acc.fst.emit [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.resumeAwait waiter token mode)],
        acc.snd ++ [Effect4.Deep.Cmd.resume waiter token (interp.exitValue exit mode)]))

#check (@Effect4.Deep.stepDecision_installMiddleware :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St),
    Effect4.Deep.stepDecision interp fuel m Effect4.Deep.RunDecision.installMiddleware =
      { fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken, nextRace := m.nextRace,
        middlewareInstalled := Bool.true, state := m.state, trace := m.trace, stuck := m.stuck })

#check (@Effect4.Deep.withFiber_fork :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Effect4.Prim ν σ β ε δ ι α)
    (options : Effect4.Supervision.ForkOptions),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.fork program options) =
      have s := Effect4.Deep.spawn interp m f program options;
      have t := Effect4.Deep.start s.fst s.snd.fst s.snd.snd options.startImmediately;
      { machine := t.fst,
        fiber :=
          have __src := t.snd.fst;
          { id := __src.id,
            frame :=
              have __src := t.snd.fst.frame;
              { current := Effect4.Prim.success (interp.fiberValue s.snd.snd), stack := __src.stack,
                interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                deferredInterrupt := __src.deferredInterrupt },
            running := __src.running, parked := __src.parked, pending := __src.pending, finalizing := __src.finalizing,
            exit := __src.exit, currentOpCount := __src.currentOpCount, maxOpsBeforeYield := __src.maxOpsBeforeYield,
            preventYield := __src.preventYield, yieldOverride := __src.yieldOverride, observers := __src.observers,
            children := __src.children, dispatcher := __src.dispatcher, context := __src.context },
        yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := t.snd.snd })

#check (@Effect4.Deep.Witnesses.w1_deferred_join_child :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w1DeferredJoin 1 =
      Option.some (Effect4.Exit.success (Effect4.Deep.Val.nat 42)) ∧
    Effect4.Deep.Witnesses.fiberCount Effect4.Deep.Witnesses.w1DeferredJoin = 2)

#check (@Effect4.Deep.Witnesses.w1_deferred_start_is_a_task :
  Effect4.Deep.Witnesses.exitOf
        (Effect4.Deep.Witnesses.replay Effect4.Deep.Stores.empty
          ((Effect4.Deep.ProgName.value (Effect4.Deep.Val.nat 42)).forkThen Effect4.Deep.Witnesses.deferredChild
            Effect4.Supervision.ObserverMode.joinEffect)
          [Effect4.Deep.RunDecision.evaluate { value := 0 }])
        1 =
      Option.none ∧
    Effect4.Deep.Witnesses.armedOf
        (Effect4.Deep.Witnesses.replay Effect4.Deep.Stores.empty
          ((Effect4.Deep.ProgName.value (Effect4.Deep.Val.nat 42)).forkThen Effect4.Deep.Witnesses.deferredChild
            Effect4.Supervision.ObserverMode.joinEffect)
          [Effect4.Deep.RunDecision.evaluate { value := 0 }])
        0 =
      Option.some Bool.true)

#check (@Effect4.Deep.Witnesses.w5_middleware_interrupts_children :
  Effect4.Deep.Witnesses.exitOf
        Effect4.Deep.Witnesses.w5WithMiddleware 1 =
      Option.some (Effect4.Deep.Witnesses.interruptedBy { value := 0 } { value := 1 }) ∧
    Effect4.Deep.Witnesses.childrenInterruptedRows Effect4.Deep.Witnesses.w5WithMiddleware = [(0, [1])] ∧
      Effect4.Deep.Witnesses.interruptRows Effect4.Deep.Witnesses.w5WithMiddleware = [(Option.some 0, 1)] ∧
        Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w5WithMiddleware 0 =
          Option.some (Effect4.Exit.success Effect4.Deep.Val.unit))

#check (@Effect4.Deep.exitFiber_no_children :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit : Effect4.Exit β ε δ ι α),
    f.children = [] → Effect4.Deep.exitFiber interp m f exit = Effect4.Deep.exitStore interp m f exit)

#check (@Effect4.Deep.exitInterruptChildren_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (exit : Effect4.Exit β ε δ ι α),
    Effect4.Deep.exitInterruptChildren interp m f exit =
      have r := Effect4.Deep.interruptEach interp f.id f.children (m, []);
      have p :=
        Effect4.Deep.countdownPark interp (r.fst.emit [Effect4.Deep.RunEvent.childrenInterrupted f.id f.children])
          { id := f.id, frame := f.frame, running := f.running, parked := f.parked, pending := f.pending,
            finalizing := Option.some exit, exit := f.exit, currentOpCount := f.currentOpCount,
            maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield, yieldOverride := f.yieldOverride,
            observers := f.observers, children := f.children, dispatcher := f.dispatcher, context := f.context }
          f.children (Effect4.Deep.Resume.continueWith (interp.restoreName exit));
      (p.fst, p.snd.fst, p.snd.snd, r.snd))

#check (@Effect4.Deep.exitInterruptChildren_interrupts :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Deep.exitInterruptChildren interp m f exit).snd.snd.snd =
      (Effect4.Deep.interruptEach interp f.id f.children (m, [])).snd)

#check (@Effect4.Deep.Witnesses.w5_no_middleware_leaves_children :
  Effect4.Deep.Witnesses.exitOf
        Effect4.Deep.Witnesses.w5WithoutMiddleware 1 =
      Option.none ∧
    Effect4.Deep.Witnesses.childrenInterruptedRows Effect4.Deep.Witnesses.w5WithoutMiddleware = [] ∧
      Effect4.Deep.Witnesses.interruptRows Effect4.Deep.Witnesses.w5WithoutMiddleware = [] ∧
        Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w5WithoutMiddleware 0 =
          Option.some (Effect4.Exit.success Effect4.Deep.Val.unit))

#check (@Effect4.Deep.withFiber_forkIn :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (program : Effect4.Prim ν σ β ε δ ι α)
    (options : Effect4.Supervision.ForkOptions) (scope key : Nat),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding
        (Effect4.Deep.WithFiberAction.forkIn program options scope key) =
      have s :=
        Effect4.Deep.spawn interp m f program
          { startImmediately := options.startImmediately, daemon := Bool.true, maskMode := options.maskMode };
      have l :=
        Effect4.Deep.linkScope interp s.fst Effect4.Supervision.ScopeMode.forkIn scope key s.snd.snd
          (Option.some s.snd.fst.id) (interp.stackAnnotations s.snd.fst.id);
      have t := Effect4.Deep.start l.fst s.snd.fst s.snd.snd options.startImmediately;
      { machine := t.fst,
        fiber :=
          have __src := t.snd.fst;
          { id := __src.id,
            frame :=
              have __src := t.snd.fst.frame;
              { current := Effect4.Prim.success (interp.fiberValue s.snd.snd), stack := __src.stack,
                interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                deferredInterrupt := __src.deferredInterrupt },
            running := __src.running, parked := __src.parked, pending := __src.pending, finalizing := __src.finalizing,
            exit := __src.exit, currentOpCount := __src.currentOpCount, maxOpsBeforeYield := __src.maxOpsBeforeYield,
            preventYield := __src.preventYield, yieldOverride := __src.yieldOverride, observers := __src.observers,
            children := __src.children, dispatcher := __src.dispatcher, context := __src.context },
        yielding := yielding,
        outcome :=
          match t.fst.stuck with
          | Option.some why => Effect4.Deep.Outcome.stuck why
          | Option.none => Effect4.Deep.Outcome.continue_,
        nested := l.snd ++ t.snd.snd })

#check (@Effect4.Deep.linkScope_open :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (mode : Effect4.Supervision.ScopeMode) (scope key : Nat) (target : Effect4.FiberId)
    (interruptor : Option Effect4.FiberId) (extra : Effect4.ReasonAnnotations α) (state : St),
    interp.scopeStatus scope m.state = Option.some Option.none →
      interp.scopeLinkFiber mode scope key target m.state = Option.some state →
        Effect4.Deep.linkScope interp m mode scope key target interruptor extra =
          ((({ fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken, nextRace := m.nextRace,
                      middlewareInstalled := m.middlewareInstalled, state := state, trace := m.trace,
                      stuck := m.stuck } : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St).modify
                  target fun t =>
                  { id := t.id, frame := t.frame, running := t.running, parked := t.parked, pending := t.pending,
                    finalizing := t.finalizing, exit := t.exit, currentOpCount := t.currentOpCount,
                    maxOpsBeforeYield := t.maxOpsBeforeYield, preventYield := t.preventYield,
                    yieldOverride := t.yieldOverride,
                    observers := t.observers ++ [Effect4.Deep.Observer.dropScopeFinalizer scope key],
                    children := t.children, dispatcher := t.dispatcher, context := t.context }).emit
              [Effect4.Deep.RunEvent.scopeLinked mode scope key target],
            []))

#check (@Effect4.Deep.fireObserver_dropScopeFinalizer :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (scope key : Nat)
    (state : St),
    interp.dropFinalizer scope key acc.fst.state = Option.some state →
      Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.dropScopeFinalizer scope key) =
        (have __src :=
            acc.fst.emit [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.dropScopeFinalizer scope key)];
          { fibers := __src.fibers, races := __src.races, nextId := __src.nextId, nextToken := __src.nextToken,
            nextRace := __src.nextRace, middlewareInstalled := __src.middlewareInstalled, state := state,
            trace := __src.trace, stuck := __src.stuck },
          acc.snd))

#check (@Effect4.Deep.withFiber_closeScope :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (scope : Nat) (exit : Effect4.Exit β ε δ ι α)
    (state : St) (program : Effect4.Prim ν σ β ε δ ι α),
    interp.closeScope scope exit f.frame.interruptible f.id m.state = Option.some (state, program) →
      Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.closeScope scope exit) =
        {
          machine :=
            { fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken, nextRace := m.nextRace,
              middlewareInstalled := m.middlewareInstalled, state := state, trace := m.trace, stuck := m.stuck },
          fiber :=
            { id := f.id,
              frame :=
                have __src := f.frame;
                { current := program, stack := __src.stack, interruptible := __src.interruptible,
                  interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
              running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
              currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield,
              preventYield := f.preventYield, yieldOverride := f.yieldOverride, observers := f.observers,
              children := f.children, dispatcher := f.dispatcher, context := f.context },
          yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := [] })

#check (@Effect4.Deep.Witnesses.w6_link_then_close :
  Effect4.Deep.Witnesses.scopeRows Effect4.Deep.Witnesses.w6LinkThenClose =
      [[0, 0, 0, 100, 1]] ∧
    Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6LinkThenClose 1 =
        Option.some (Effect4.Deep.Witnesses.interruptedBy { value := 0 } { value := 1 }) ∧
      Effect4.Deep.Witnesses.scopeKeys Effect4.Deep.Witnesses.w6LinkThenClose 0 = Option.some [] ∧
        Effect4.Deep.Witnesses.scopeClosed Effect4.Deep.Witnesses.w6LinkThenClose 0 = Option.some Bool.true ∧
          Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6LinkThenClose 0 =
            Option.some (Effect4.Exit.success Effect4.Deep.Val.unit))

#check (@Effect4.Deep.Witnesses.w6_closed_scope_interrupts_now :
  Effect4.Deep.Witnesses.scopeRows
        Effect4.Deep.Witnesses.w6ClosedScope =
      [[1, 1, 1]] ∧
    Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6ClosedScope 1 =
        Option.some
          (Effect4.Deep.Witnesses.interruptedWith { value := 0 } { value := 1 }
            (Effect4.Deep.stores.stackAnnotations { value := 0 })) ∧
      Option.map Effect4.Deep.Witnesses.causeKeys (Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6ClosedScope 1) =
        Option.some [["stack1", "stack0"]])

#check (@Effect4.Deep.Witnesses.w6_child_exit_drops_key :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6DropsKey 1 =
      Option.some (Effect4.Exit.success (Effect4.Deep.Val.nat 3)) ∧
    Effect4.Deep.Witnesses.scopeKeys Effect4.Deep.Witnesses.w6DropsKey 0 = Option.some [])

#check (@Effect4.Deep.withFiber_forkScoped_ambient :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Effect4.Prim ν σ β ε δ ι α) (options : Effect4.Supervision.ForkOptions) (key scope : Nat),
    interp.ambientScope f.context = Option.some scope →
      Effect4.Deep.evaluatePrim.withFiber interp m f yielding
          (Effect4.Deep.WithFiberAction.forkScoped program options key) =
        have s :=
          Effect4.Deep.spawn interp m f program
            { startImmediately := options.startImmediately, daemon := Bool.true, maskMode := options.maskMode };
        have l :=
          Effect4.Deep.linkScope interp s.fst Effect4.Supervision.ScopeMode.forkIn scope key s.snd.snd
            (Option.some s.snd.fst.id) (interp.stackAnnotations s.snd.fst.id);
        have t := Effect4.Deep.start l.fst s.snd.fst s.snd.snd options.startImmediately;
        { machine := t.fst,
          fiber :=
            have __src := t.snd.fst;
            { id := __src.id,
              frame :=
                have __src := t.snd.fst.frame;
                { current := Effect4.Prim.success (interp.fiberValue s.snd.snd), stack := __src.stack,
                  interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                  deferredInterrupt := __src.deferredInterrupt },
              running := __src.running, parked := __src.parked, pending := __src.pending, finalizing := __src.finalizing,
              exit := __src.exit, currentOpCount := __src.currentOpCount, maxOpsBeforeYield := __src.maxOpsBeforeYield,
              preventYield := __src.preventYield, yieldOverride := __src.yieldOverride, observers := __src.observers,
              children := __src.children, dispatcher := __src.dispatcher, context := __src.context },
          yielding := yielding,
          outcome :=
            match t.fst.stuck with
            | Option.some why => Effect4.Deep.Outcome.stuck why
            | Option.none => Effect4.Deep.Outcome.continue_,
          nested := l.snd ++ t.snd.snd })

#check (@Effect4.Deep.withFiber_forkScoped_none :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (program : Effect4.Prim ν σ β ε δ ι α) (options : Effect4.Supervision.ForkOptions) (key : Nat),
    interp.ambientScope f.context = Option.none →
      Effect4.Deep.evaluatePrim.withFiber interp m f yielding
          (Effect4.Deep.WithFiberAction.forkScoped program options key) =
        { machine := m,
          fiber :=
            { id := f.id,
              frame :=
                have __src := f.frame;
                { current := Effect4.Prim.failure (Effect4.Cause.die interp.notImplemented), stack := __src.stack,
                  interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                  deferredInterrupt := __src.deferredInterrupt },
              running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
              currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield,
              preventYield := f.preventYield, yieldOverride := f.yieldOverride, observers := f.observers,
              children := f.children, dispatcher := f.dispatcher, context := f.context },
          yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := [] })

#check (@Effect4.Deep.withFiber_raceAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (entrants : List (Effect4.Prim ν σ β ε δ ι α)),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.raceAll entrants) =
      have raceId := m.nextRace;
      have token := m.nextToken;
      have m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St :=
        { fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken + 1,
          nextRace := m.nextRace + 1, middlewareInstalled := m.middlewareInstalled, state := m.state, trace := m.trace,
          stuck := m.stuck };
      have e := List.foldl (Effect4.Deep.raceEntrant interp raceId) (m, f, []) entrants;
      have race : Effect4.Deep.Race β ε δ ι α :=
        { id := raceId, host := e.snd.fst.id, token := token, state := Effect4.Supervision.RaceAllState.initial e.snd.snd,
          settled := Bool.false };
      have m :=
        (have __src := e.fst;
            ({ fibers := __src.fibers, races := e.fst.races ++ [race], nextId := __src.nextId,
               nextToken := __src.nextToken, nextRace := __src.nextRace, middlewareInstalled := __src.middlewareInstalled,
               state := __src.state, trace := __src.trace, stuck := __src.stuck }
              : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)).emit
          [Effect4.Deep.RunEvent.raceStarted raceId e.snd.fst.id e.snd.snd];
      have g :=
        e.snd.fst.park
          { token := token, waitingOn := Option.none, remaining := 0, collected := [],
            resumeWith := Effect4.Deep.Resume.void, failFast := Bool.false, outstanding := [] };
      { machine := m.emit [Effect4.Deep.RunEvent.parkedOn g.id token], fiber := g, yielding := yielding,
        outcome := Effect4.Deep.Outcome.parked, nested := List.map (Effect4.Deep.Cmd.launch raceId) e.snd.snd })

#check (@Effect4.Deep.raceEntrant_options :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (raceId : Nat)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × Effect4.Deep.RunFiber ν σ β ε δ ι α χ × List Effect4.FiberId)
    (program : Effect4.Prim ν σ β ε δ ι α),
    Effect4.Deep.raceEntrant interp raceId acc program =
      have s :=
        Effect4.Deep.spawn interp acc.fst acc.snd.fst program
          { startImmediately := Bool.true, daemon := Bool.true, maskMode := Effect4.Supervision.MaskMode.inherit };
      (s.fst.modify s.snd.snd fun c =>
          { id := c.id, frame := c.frame, running := c.running, parked := c.parked, pending := c.pending,
            finalizing := c.finalizing, exit := c.exit, currentOpCount := c.currentOpCount,
            maxOpsBeforeYield := c.maxOpsBeforeYield, preventYield := c.preventYield, yieldOverride := c.yieldOverride,
            observers := c.observers ++ [Effect4.Deep.Observer.raceCallback raceId], children := c.children,
            dispatcher := c.dispatcher, context := c.context },
        s.snd.fst, acc.snd.snd ++ [s.snd.snd]))

#check (@Effect4.Deep.drive_launch_runs :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (raceId : Nat) (entrant : Effect4.FiberId) (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α))
    (race : Effect4.Deep.Race β ε δ ι α),
    m.stuck = Option.none →
      m.race? raceId = Option.some race →
        race.state.accepted = Option.none →
          Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.launch raceId entrant :: rest) =
            Effect4.Deep.drive interp fuel
              ((m.updateRace
                    { id := race.id, host := race.host, token := race.token,
                      state :=
                        have __src := race.state;
                        { unstarted := List.filter (fun e => Decidable.decide (e ≠ entrant)) race.state.unstarted,
                          starting := __src.starting, live := race.state.live ++ [entrant], remaining := __src.remaining,
                          failures := __src.failures, winner := __src.winner, accepted := __src.accepted,
                          cleanupNeeded := __src.cleanupNeeded, requests := __src.requests, cleanup := __src.cleanup,
                          cleanupRequested := __src.cleanupRequested },
                      settled := race.settled }).emit
                [Effect4.Deep.RunEvent.raceLaunched raceId entrant])
              (Effect4.Deep.Cmd.evaluate entrant :: rest))

#check (@Effect4.Deep.drive_launch_skipped :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (fuel : Nat) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (raceId : Nat) (entrant : Effect4.FiberId) (rest : List (Effect4.Deep.Cmd ν σ β ε δ ι α))
    (race : Effect4.Deep.Race β ε δ ι α) (accepted : Effect4.Exit β ε δ ι α) (e : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    m.stuck = Option.none →
      m.race? raceId = Option.some race →
        race.state.accepted = Option.some accepted →
          m.fiber? entrant = Option.some e →
            Effect4.Deep.drive interp (fuel + 1) m (Effect4.Deep.Cmd.launch raceId entrant :: rest) =
              have r := Effect4.Deep.interruptRecord interp (Option.some race.host) Effect4.ReasonAnnotations.empty e;
              Effect4.Deep.drive interp fuel
                ((m.update r.fst).emit
                  [Effect4.Deep.RunEvent.raceSkipped raceId entrant,
                    Effect4.Deep.RunEvent.interruptRecorded (Option.some race.host) entrant])
                ((if r.snd = Bool.true then [Effect4.Deep.Cmd.evaluate entrant] else []) ++ rest))

#check (@Effect4.Deep.fireObserver_raceCallback_pending :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (raceId : Nat)
    (race : Effect4.Deep.Race β ε δ ι α),
    acc.fst.race? raceId = Option.some race →
      (Effect4.Supervision.raceComplete race.state id exit).accepted = Option.none →
        Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.raceCallback raceId) =
          ((acc.fst.emit [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.raceCallback raceId)]).updateRace
              { id := race.id, host := race.host, token := race.token,
                state := Effect4.Supervision.raceComplete race.state id exit, settled := race.settled },
            acc.snd))

#check (@Effect4.Deep.fireObserver_raceCallback_settles :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (raceId : Nat)
    (race : Effect4.Deep.Race β ε δ ι α) (accepted : Effect4.Exit β ε δ ι α),
    acc.fst.race? raceId = Option.some race →
      (Effect4.Supervision.raceComplete race.state id exit).accepted = Option.some accepted →
        race.settled = Bool.false →
          Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.raceCallback raceId) =
            have state := Effect4.Supervision.raceComplete race.state id exit;
            have race :=
              { id := race.id, host := race.host, token := race.token, state := state, settled := race.settled };
            Effect4.Deep.settleRace interp
              ((acc.fst.emit
                    [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.raceCallback raceId)]).updateRace
                race)
              acc.snd raceId race state accepted)

#check (@Effect4.Deep.fireObserver_raceCallback_late :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (raceId : Nat)
    (race : Effect4.Deep.Race β ε δ ι α),
    acc.fst.race? raceId = Option.some race →
      race.settled = Bool.true →
        Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.raceCallback raceId) =
          ((acc.fst.emit [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.raceCallback raceId)]).updateRace
              { id := race.id, host := race.host, token := race.token,
                state := Effect4.Supervision.raceComplete race.state id exit, settled := race.settled },
            acc.snd))

#check (@Effect4.Deep.resumePrim_continueWith :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (name : ν) (exits : List (Effect4.Exit β ε δ ι α)),
    Effect4.Deep.countdownPark.resumePrim interp (Effect4.Deep.Resume.continueWith name) exits =
      (Effect4.Prim.success (interp.exitsValue exits)).onSuccess name)

#check (@Effect4.Deep.Witnesses.w3_empty_is_a_frontier :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w3EmptyPending 0 =
      Option.none ∧
    Effect4.Deep.Witnesses.parkedOf Effect4.Deep.Witnesses.w3EmptyPending 0 =
        Option.some (Effect4.Deep.Parked.withGuard 0) ∧
      Effect4.Deep.Witnesses.fiberCount Effect4.Deep.Witnesses.w3EmptyPending = 1)

#check (@Effect4.Deep.Witnesses.w3_empty_until_interrupted :
  Effect4.Deep.Witnesses.exitOf
      Effect4.Deep.Witnesses.w3EmptyInterrupted 0 =
    Option.some (Effect4.Deep.Witnesses.interruptedBy { value := 0 } { value := 0 }))

#check (@Effect4.Deep.Witnesses.w3_immediate_success_stops_launch :
  Effect4.Deep.Witnesses.exitOf
        Effect4.Deep.Witnesses.w3StopsLaunch 0 =
      Option.some (Effect4.Exit.success (Effect4.Deep.Val.nat 1)) ∧
    Effect4.Deep.Witnesses.raceRows Effect4.Deep.Witnesses.w3StopsLaunch = [[0, 0, 1], [2, 0], [1, 0, 2]] ∧
      Effect4.Deep.Witnesses.fiberCount Effect4.Deep.Witnesses.w3StopsLaunch = 3 ∧
        Effect4.Deep.Witnesses.interruptRows Effect4.Deep.Witnesses.w3StopsLaunch = [(Option.some 0, 2)] ∧
          Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w3StopsLaunch 2 =
            Option.some (Effect4.Deep.Witnesses.interruptedBy { value := 0 } { value := 2 }))

#check (@Effect4.Deep.Witnesses.w3_failure_allows_next_launch :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w3NextLaunch
        0 =
      Option.some (Effect4.Exit.success (Effect4.Deep.Val.nat 9)) ∧
    Effect4.Deep.Witnesses.raceRows Effect4.Deep.Witnesses.w3NextLaunch = [[0, 0, 1], [0, 0, 2], [2, 0]])

#check (@Effect4.Deep.Witnesses.w3_all_failures_retain_order :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w3AllFail 0 =
    Option.some
      (Effect4.Exit.failure
        {
          reasons :=
            [Effect4.Reason.fail (Effect4.Deep.Err.tag 1) Effect4.ReasonAnnotations.empty,
              Effect4.Reason.fail (Effect4.Deep.Err.tag 2) Effect4.ReasonAnnotations.empty] }))

#check (@Effect4.Deep.withFiber_interrupt :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (target : Effect4.FiberId),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.interrupt target) =
      Effect4.Deep.evaluatePrim.interruptThenJoin interp m f yielding target (Option.some f.id))

#check (@Effect4.Deep.interruptThenJoin_eq :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool) (target : Effect4.FiberId)
    (interruptor : Option Effect4.FiberId) (t : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    m.fiber? target = Option.some t →
      Effect4.Deep.evaluatePrim.interruptThenJoin interp m f yielding target interruptor =
        have r := Effect4.Deep.interruptRecord interp interruptor Effect4.ReasonAnnotations.empty t;
        have m := (m.update r.fst).emit [Effect4.Deep.RunEvent.interruptRecorded interruptor target];
        have p := Effect4.Deep.countdownPark interp m f [target] Effect4.Deep.Resume.void;
        { machine := p.fst, fiber := p.snd.fst, yielding := yielding,
          outcome := if p.snd.snd = Bool.true then Effect4.Deep.Outcome.parked else Effect4.Deep.Outcome.continue_,
          nested := if r.snd = Bool.true then [Effect4.Deep.Cmd.evaluate target] else [] })

#check (@Effect4.Deep.interruptThenJoin_unknown :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : Effect4.FiberId) (interruptor : Option Effect4.FiberId),
    m.fiber? target = Option.none →
      Effect4.Deep.evaluatePrim.interruptThenJoin interp m f yielding target interruptor =
        { machine := m, fiber := f, yielding := yielding,
          outcome := Effect4.Deep.Outcome.stuck (Effect4.Deep.Stuck.unknownFiber target), nested := [] })

#check (@Effect4.Deep.withFiber_interruptScoped_self :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.interruptScoped f.id) =
      { machine := m,
        fiber :=
          { id := f.id,
            frame :=
              have __src := f.frame;
              { current := Effect4.Prim.success interp.voidValue, stack := __src.stack,
                interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                deferredInterrupt := __src.deferredInterrupt },
            running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
            currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
            yieldOverride := f.yieldOverride, observers := f.observers, children := f.children,
            dispatcher := f.dispatcher, context := f.context },
        yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := [] })

#check (@Effect4.Deep.withFiber_interruptScoped_other :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (target : Effect4.FiberId),
    target ≠ f.id →
      Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.interruptScoped target) =
        Effect4.Deep.evaluatePrim.interruptThenJoin interp m f yielding target (Option.some f.id))

#check (@Effect4.Deep.Witnesses.w2_delivered_at_unmask :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w2 1 =
    Option.some (Effect4.Deep.Witnesses.interruptedBy { value := 0 } { value := 1 }))

#check (@Effect4.Deep.Witnesses.w2_recorded_once :
  Effect4.Deep.Witnesses.interruptRows Effect4.Deep.Witnesses.w2 =
    [(Option.some 0, 1)])

#check (@Effect4.Deep.Witnesses.w2_masked_interrupt_does_not_apply :
  Effect4.Deep.Witnesses.exitOf
      (Effect4.Deep.Witnesses.replay Effect4.Deep.Stores.empty
        (Effect4.Deep.Witnesses.w2Child.forkOnly Effect4.Deep.Witnesses.immediateChild)
        [Effect4.Deep.RunDecision.evaluate { value := 0 },
          Effect4.Deep.RunDecision.interruptFrom (Option.some { value := 0 }) Effect4.ReasonAnnotations.empty
            { value := 1 }])
      1 =
    Option.none)

#check (@Effect4.Deep.Witnesses.w6_self_interruptor_skipped :
  Effect4.Deep.Witnesses.interruptRows
        Effect4.Deep.Witnesses.w6SelfInterruptorSkipped =
      [] ∧
    Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6SelfInterruptorSkipped 0 =
      Option.some (Effect4.Exit.success Effect4.Deep.Val.unit))

#check (@Effect4.Deep.withFiber_interruptAll :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (targets : List Effect4.FiberId) (interruptor : Option Effect4.FiberId),
    Effect4.Deep.evaluatePrim.withFiber interp m f yielding
        (Effect4.Deep.WithFiberAction.interruptAll targets interruptor) =
      have r := Effect4.Deep.interruptEach interp (interruptor.getD f.id) targets (m, []);
      have p := Effect4.Deep.countdownPark interp r.fst f targets Effect4.Deep.Resume.void;
      { machine := p.fst, fiber := p.snd.fst, yielding := yielding,
        outcome :=
          match p.fst.stuck with
          | Option.some why => Effect4.Deep.Outcome.stuck why
          | Option.none => if p.snd.snd = Bool.true then Effect4.Deep.Outcome.parked else Effect4.Deep.Outcome.continue_,
        nested := r.snd })

#check (@Effect4.Deep.interruptEach_nil :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (who : Effect4.FiberId)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    Effect4.Deep.interruptEach interp who [] acc = acc)

#check (@Effect4.Deep.interruptEach_cons :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (who t : Effect4.FiberId) (ts : List Effect4.FiberId)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)),
    Effect4.Deep.interruptEach interp who (t :: ts) acc =
      Effect4.Deep.interruptEach interp who ts
        (match acc.fst.fiber? t with
        | Option.none => acc
        | Option.some g =>
          have r := Effect4.Deep.interruptRecord interp (Option.some who) Effect4.ReasonAnnotations.empty g;
          ((acc.fst.update r.fst).emit [Effect4.Deep.RunEvent.interruptRecorded (Option.some who) t],
            acc.snd ++ if r.snd = Bool.true then [Effect4.Deep.Cmd.evaluate t] else [])))

#check (@Effect4.Deep.interruptEach_known :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (who t : Effect4.FiberId) (ts : List Effect4.FiberId)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α))
    (g : Effect4.Deep.RunFiber ν σ β ε δ ι α χ),
    acc.fst.fiber? t = Option.some g →
      Effect4.Deep.interruptEach interp who (t :: ts) acc =
        Effect4.Deep.interruptEach interp who ts
          (have r := Effect4.Deep.interruptRecord interp (Option.some who) Effect4.ReasonAnnotations.empty g;
          ((acc.fst.update r.fst).emit [Effect4.Deep.RunEvent.interruptRecorded (Option.some who) t],
            acc.snd ++ if r.snd = Bool.true then [Effect4.Deep.Cmd.evaluate t] else [])))

#check (@Effect4.Deep.fireObserver_countdown_last :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (waiter : Effect4.FiberId)
    (token : Nat) (w : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (p : Effect4.Deep.Pending ν β ε δ ι α),
    acc.fst.fiber? waiter = Option.some w →
      List.find? (fun q => Decidable.decide (q.token = token)) w.pending = Option.some p →
        p.failFast = Bool.false →
          p.remaining ≤ 1 →
            Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.countdown waiter token) =
              ((acc.fst.emit
                      [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.countdown waiter token)]).update
                  { id := w.id, frame := w.frame, running := w.running, parked := w.parked,
                    pending :=
                      List.map
                        (fun q =>
                          if q.token = token then
                            { token := q.token, waitingOn := q.waitingOn, remaining := 0,
                              collected := p.collected ++ [exit], resumeWith := q.resumeWith, failFast := q.failFast,
                              outstanding := [] }
                          else q)
                        w.pending,
                    finalizing := w.finalizing, exit := w.exit, currentOpCount := w.currentOpCount,
                    maxOpsBeforeYield := w.maxOpsBeforeYield, preventYield := w.preventYield,
                    yieldOverride := w.yieldOverride, observers := w.observers, children := w.children,
                    dispatcher := w.dispatcher, context := w.context },
                acc.snd ++
                  [Effect4.Deep.Cmd.resume waiter token
                      (Effect4.Deep.countdownPark.resumePrim interp p.resumeWith (p.collected ++ [exit]))]))

#check (@Effect4.Deep.fireObserver_countdown_more :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (waiter : Effect4.FiberId)
    (token : Nat) (w : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (p : Effect4.Deep.Pending ν β ε δ ι α),
    acc.fst.fiber? waiter = Option.some w →
      List.find? (fun q => Decidable.decide (q.token = token)) w.pending = Option.some p →
        p.failFast = Bool.false →
          ¬p.remaining ≤ 1 →
            Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.countdown waiter token) =
              ((acc.fst.emit
                      [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.countdown waiter token)]).update
                  { id := w.id, frame := w.frame, running := w.running, parked := w.parked,
                    pending :=
                      List.map
                        (fun q =>
                          if q.token = token then
                            { token := q.token, waitingOn := q.waitingOn, remaining := q.remaining - 1,
                              collected := p.collected ++ [exit], resumeWith := q.resumeWith, failFast := q.failFast,
                              outstanding := List.filter (fun t => Decidable.decide (t ≠ id)) p.outstanding }
                          else q)
                        w.pending,
                    finalizing := w.finalizing, exit := w.exit, currentOpCount := w.currentOpCount,
                    maxOpsBeforeYield := w.maxOpsBeforeYield, preventYield := w.preventYield,
                    yieldOverride := w.yieldOverride, observers := w.observers, children := w.children,
                    dispatcher := w.dispatcher, context := w.context },
                acc.snd))

#check (@Effect4.Deep.Witnesses.w5_await_all_children_awaits_only_new :
  Effect4.Deep.Witnesses.exitOf
        Effect4.Deep.Witnesses.w5AwaitAllChildren 2 =
      Option.some (Effect4.Exit.success (Effect4.Deep.Val.nat 5)) ∧
    Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w5AwaitAllChildren 1 = Option.none ∧
      Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w5AwaitAllChildren 0 =
        Option.some (Effect4.Exit.success Effect4.Deep.Val.unit))

#check (@Effect4.Deep.Witnesses.w12_awaitAll_answers_the_exits :
  Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w12AwaitAll
      0 =
    Option.some
      (Effect4.Exit.success
        (Effect4.Deep.stores.exitsValue
          [Effect4.Exit.success (Effect4.Deep.Val.nat 4),
            Effect4.Exit.failure (Effect4.Cause.fail (Effect4.Deep.Err.tag 5))])))

#check (@Effect4.Deep.Witnesses.w6_runIn_closed_scope_uses_no_caller_annotations :
  Effect4.Deep.Witnesses.scopeRows
        Effect4.Deep.Witnesses.w6ClosedRunIn =
      [[1, 1, 1]] ∧
    Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6ClosedRunIn 1 =
        Option.some (Effect4.Deep.Witnesses.interruptedBy { value := 1 } { value := 1 }) ∧
      Option.map Effect4.Deep.Witnesses.causeKeys (Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6ClosedRunIn 1) =
          Option.some [["stack1"]] ∧
        Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6ClosedRunIn 0 =
          Option.some (Effect4.Exit.success Effect4.Deep.Val.unit))

#check (@Effect4.Deep.fireObserver_untrackChild :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (id : Effect4.FiberId)
    (exit : Effect4.Exit β ε δ ι α)
    (acc : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St × List (Effect4.Deep.Cmd ν σ β ε δ ι α)) (parent : Effect4.FiberId),
    Effect4.Deep.fireObserver interp id exit acc (Effect4.Deep.Observer.untrackChild parent) =
      ((acc.fst.emit [Effect4.Deep.RunEvent.observerFired id (Effect4.Deep.Observer.untrackChild parent)]).modify parent
          fun p =>
          { id := p.id, frame := p.frame, running := p.running, parked := p.parked, pending := p.pending,
            finalizing := p.finalizing, exit := p.exit, currentOpCount := p.currentOpCount,
            maxOpsBeforeYield := p.maxOpsBeforeYield, preventYield := p.preventYield, yieldOverride := p.yieldOverride,
            observers := p.observers, children := List.filter (fun c => Decidable.decide (c ≠ id)) p.children,
            dispatcher := p.dispatcher, context := p.context },
        acc.snd))

#check (@Effect4.Deep.exitFiber_children :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit : Effect4.Exit β ε δ ι α),
    m.middlewareInstalled = Bool.true →
      f.finalizing = Option.none →
        f.children.isEmpty = Bool.false →
          Effect4.Deep.exitFiber interp m f exit = Effect4.Deep.exitInterruptChildren interp m f exit)

#check (@Effect4.Deep.exitInterruptChildren_finalizing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ)
    (exit : Effect4.Exit β ε δ ι α),
    (Effect4.Deep.exitInterruptChildren interp m f exit).snd.fst.finalizing = Option.some exit)

#check (@Effect4.Deep.exitFiber_finalizing :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u} {St : Type (max u v)}
    [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι] [inst_3 : DecidableEq α]
    (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St) (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St)
    (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (exit body : Effect4.Exit β ε δ ι α),
    f.finalizing = Option.some body → Effect4.Deep.exitFiber interp m f exit = Effect4.Deep.exitStore interp m f exit)

#check (@Effect4.Deep.withFiber_closeScope_unknown :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (scope : Nat) (exit : Effect4.Exit β ε δ ι α),
    interp.closeScope scope exit f.frame.interruptible f.id m.state = Option.none →
      Effect4.Deep.evaluatePrim.withFiber interp m f yielding (Effect4.Deep.WithFiberAction.closeScope scope exit) =
        { machine := m, fiber := f, yielding := yielding,
          outcome := Effect4.Deep.Outcome.stuck (Effect4.Deep.Stuck.unknownScope scope), nested := [] })

#check (@Effect4.Deep.Witnesses.w6_sequential_captures_and_merges :
  Effect4.Deep.Witnesses.exitOf
        Effect4.Deep.Witnesses.w6Sequential 0 =
      Option.some
        (Effect4.Exit.failure
          { reasons := [Effect4.Reason.fail (Effect4.Deep.Err.tag 2) Effect4.ReasonAnnotations.empty] }) ∧
    Effect4.Deep.Witnesses.fiberCount Effect4.Deep.Witnesses.w6Sequential = 1 ∧
      Effect4.Deep.Witnesses.scopeClosed Effect4.Deep.Witnesses.w6Sequential 3 = Option.some Bool.true)

#check (@Effect4.Deep.Witnesses.w6_parallel_forks_and_merges :
  Effect4.Deep.Witnesses.fiberCount
        Effect4.Deep.Witnesses.w6Parallel =
      3 ∧
    Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6Parallel 1 =
        Option.some
          (Effect4.Exit.failure
            { reasons := [Effect4.Reason.fail (Effect4.Deep.Err.tag 4) Effect4.ReasonAnnotations.empty] }) ∧
      Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6Parallel 2 =
          Option.some (Effect4.Exit.success Effect4.Deep.Val.unit) ∧
        Effect4.Deep.Witnesses.exitOf Effect4.Deep.Witnesses.w6Parallel 0 =
            Option.some
              (Effect4.Exit.failure
                { reasons := [Effect4.Reason.fail (Effect4.Deep.Err.tag 4) Effect4.ReasonAnnotations.empty] }) ∧
          Effect4.Deep.Witnesses.scopeClosed Effect4.Deep.Witnesses.w6Parallel 4 = Option.some Bool.true)

#check (@Effect4.Deep.evaluatePrim_async_immediate :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (register : ν) (withSignal : Bool) (cancel : Option ν) (state : St) (next : Effect4.Prim ν σ β ε δ ι α),
    interp.registerAsync register f.id m.nextToken m.state = (state, Option.some next) →
      have g :=
        { id := f.id,
          frame :=
            have __src := f.frame;
            { current := Effect4.Prim.async register withSignal cancel, stack := __src.stack,
              interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
              deferredInterrupt := __src.deferredInterrupt },
          running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
          currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
          yieldOverride := f.yieldOverride, observers := f.observers, children := f.children, dispatcher := f.dispatcher,
          context := f.context };
      Effect4.Deep.evaluatePrim interp m g yielding =
        {
          machine :=
            { fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken + 1,
              nextRace := m.nextRace, middlewareInstalled := m.middlewareInstalled, state := state, trace := m.trace,
              stuck := m.stuck },
          fiber :=
            { id := g.id,
              frame :=
                have __src := g.frame;
                { current := next, stack := __src.stack, interruptible := __src.interruptible,
                  interruptedCause := __src.interruptedCause, deferredInterrupt := __src.deferredInterrupt },
              running := g.running, parked := g.parked, pending := g.pending, finalizing := g.finalizing, exit := g.exit,
              currentOpCount := g.currentOpCount, maxOpsBeforeYield := g.maxOpsBeforeYield,
              preventYield := g.preventYield, yieldOverride := g.yieldOverride, observers := g.observers,
              children := g.children, dispatcher := g.dispatcher, context := g.context },
          yielding := yielding, outcome := Effect4.Deep.Outcome.continue_, nested := [Effect4.Deep.Cmd.drainDue] })

#check (@Effect4.Deep.evaluatePrim_async_parks :
  ∀ {ν σ : Type u} {β : Type v} {ε δ ι α χ : Type u}
    {St : Type (max u v)} [inst : DecidableEq ε] [inst_1 : DecidableEq δ] [inst_2 : DecidableEq ι]
    [inst_3 : DecidableEq α] (interp : Effect4.Deep.RunInterp ν σ β ε δ ι α χ St)
    (m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St) (f : Effect4.Deep.RunFiber ν σ β ε δ ι α χ) (yielding : Bool)
    (register : ν) (withSignal : Bool) (cancel : Option ν) (state : St),
    interp.registerAsync register f.id m.nextToken m.state = (state, Option.none) →
      have g :=
        { id := f.id,
          frame :=
            have __src := f.frame;
            { current := Effect4.Prim.async register withSignal cancel, stack := __src.stack,
              interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
              deferredInterrupt := __src.deferredInterrupt },
          running := f.running, parked := f.parked, pending := f.pending, finalizing := f.finalizing, exit := f.exit,
          currentOpCount := f.currentOpCount, maxOpsBeforeYield := f.maxOpsBeforeYield, preventYield := f.preventYield,
          yieldOverride := f.yieldOverride, observers := f.observers, children := f.children, dispatcher := f.dispatcher,
          context := f.context };
      Effect4.Deep.evaluatePrim interp m g yielding =
        have token := m.nextToken;
        have m : Effect4.Deep.RunMachine ν σ β ε δ ι α χ St :=
          { fibers := m.fibers, races := m.races, nextId := m.nextId, nextToken := m.nextToken + 1,
            nextRace := m.nextRace, middlewareInstalled := m.middlewareInstalled, state := state, trace := m.trace,
            stuck := m.stuck };
        have g :=
          if (withSignal || cancel.isSome) = Bool.true then
            { id := g.id,
              frame :=
                have __src := g.frame;
                { current := __src.current,
                  stack :=
                    Effect4.Prim.asyncFinalizer (interp.cancelName (cancel.getD interp.abortName) g.id token) ::
                      g.frame.stack,
                  interruptible := __src.interruptible, interruptedCause := __src.interruptedCause,
                  deferredInterrupt := __src.deferredInterrupt },
              running := g.running, parked := g.parked, pending := g.pending, finalizing := g.finalizing, exit := g.exit,
              currentOpCount := g.currentOpCount, maxOpsBeforeYield := g.maxOpsBeforeYield,
              preventYield := g.preventYield, yieldOverride := g.yieldOverride, observers := g.observers,
              children := g.children, dispatcher := g.dispatcher, context := g.context }
          else g;
        have g :=
          g.park
            { token := token, waitingOn := Option.none, remaining := 0, collected := [],
              resumeWith := Effect4.Deep.Resume.void, failFast := Bool.false, outstanding := [] };
        { machine := m.emit [Effect4.Deep.RunEvent.parkedOn g.id token], fiber := g, yielding := yielding,
          outcome := Effect4.Deep.Outcome.parked, nested := [] })

end StatementSnapshot

/-! ## The frozen census join -/

/-- One census row. `id` and `kind` must match `generated/effect-runtime-census.tsv`
exactly; the cross-check lives in `scripts/check-effect-runtime-census.sh`. -/
private structure Row where
  /-- Stable kebab id, identical to the census row id. -/
  id : String
  /-- Census kind, identical to the census row kind. -/
  kind : String
  /-- `PORT-MANIFEST.md` disposition vocabulary. -/
  disposition : String
  /-- `green`, `partial` or `absent`. -/
  coverage : String
  /-- Witness declarations with their expected canonical axiom receipt. -/
  witnesses : List (Name × String)

private def w (name : Name) (axioms : String) : Name × String := (name, axioms)

/-- Manifest dispositions that place a row outside the coverage denominator. -/
private def excludedDispositions : List String :=
  ["excludedInternal", "targetOnly", "evidenceOnly"]

private def knownDispositions : List String :=
  [ "owned", "split", "downstreamAdapter", "separateCalculus", "derivedExpansion"
  , "foreignBoundary", "targetOnly", "evidenceOnly", "excludedInternal" ]

private def knownKinds : List String :=
  [ "op", "frame-arm", "checkpoint", "interrupt", "fork", "scope", "scheduler"
  , "exit", "cause", "entry", "rule", "ref", "deferred", "layer" ]

private def knownCoverage : List String := ["green", "partial", "absent"]

private def censusRows : List Row :=
  [ { id := "op.Success", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.getCont_empty_stack "propext"
        , w `Effect4.FrameFiber.resumeValue_empty "propext"
        , w `Effect4.FrameFiber.resumeValue_frame "propext"
        , w `Effect4.FrameFiber.step_success "propext"
        , w `Effect4.FrameFiber.step_ofExit_finishes "propext" ] }
  , { id := "op.Failure", kind := "op", disposition := "separateCalculus", coverage := "partial"
      -- missing clause: "annotates the cause with the current stack frame" needs a fiber Context and a StackTrace service key
    , witnesses :=
        [ w `Effect4.FrameFiber.interrupt_skips_every_handler "propext,Quot.sound"
        , w `Effect4.FrameFiber.resumeCause_empty "propext"
        , w `Effect4.FrameFiber.resumeCause_frame "propext"
        , w `Effect4.FrameFiber.step_failure "propext" ] }
  , { id := "op.WithFiber", kind := "op", disposition := "foreignBoundary", coverage := "green"
      -- the raw FiberImpl host-identity clause is closed by refusal, not by a model
    , witnesses :=
        [ w `Effect4.FrameFiber.step_withFiber "propext"
        , w `Effect4.Prim.withFiber_refused "none" ] }
  , { id := "op.YieldableError", kind := "op", disposition := "foreignBoundary", coverage := "green"
      -- the host Error subclass identity clause is closed by refusal, not by a model
    , witnesses :=
        [ w `Effect4.FrameFiber.step_yieldableError "propext"
        , w `Effect4.Prim.yieldableError_host_class_refused "none" ] }
  , { id := "op.Sync", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.step_sync "propext" ] }
  , { id := "op.Suspend", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.step_suspend "propext" ] }
  , { id := "op.Yield", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.evaluatePrim_yieldNowWith "propext,Quot.sound" ] }
  , { id := "op.Async", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.step_async_frontier "propext"
        , w `Effect4.Deep.evaluatePrim_async_immediate "propext,Quot.sound"
        , w `Effect4.Deep.evaluatePrim_async_parks "propext,Quot.sound" ] }
  , { id := "op.AsyncFinalizer", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armE_asyncFinalizer_interrupt "propext"
        , w `Effect4.Prim.armE_asyncFinalizer_no_interrupt "propext"
        , w `Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push "propext"
        , w `Effect4.Prim.ensure_asyncFinalizer_masks "propext" ] }
  , { id := "op.Iterator", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_iterator_done "propext"
        , w `Effect4.Prim.armA_iterator_halt "propext"
        , w `Effect4.Prim.armA_iterator_resume "propext"
        , w `Effect4.Prim.iteratorFolded_eq "none"
        , w `Effect4.Prim.iterator_folds_inline "propext"
        , w `Effect4.FrameFiber.step_iterator "propext" ] }
  , { id := "op.OnSuccess", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_onSuccess "none"
        , w `Effect4.Prim.onSuccess_arm_is_per_instance "none"
        , w `Effect4.FrameFiber.step_onSuccess "propext" ] }
  , { id := "op.OnFailure", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armE_onFailure "none"
        , w `Effect4.Prim.onFailure_arm_is_per_instance "none"
        , w `Effect4.FrameFiber.step_onFailure "propext" ] }
  , { id := "op.OnSuccessAndFailure", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_onSuccessAndFailure "none"
        , w `Effect4.Prim.armE_onSuccessAndFailure "none"
        , w `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance "none"
        , w `Effect4.FrameFiber.step_onSuccessAndFailure "propext" ] }
  , { id := "op.Exit", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_exitFrame_provided "none"
        , w `Effect4.Prim.armA_exitFrame_none "none"
        , w `Effect4.Prim.armE_exitFrame_provided "none"
        , w `Effect4.Prim.armE_exitFrame_none "none"
        , w `Effect4.FrameFiber.step_exitFrame "propext" ] }
  , { id := "op.OnExit", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.ensure_onExit_masks "propext"
        , w `Effect4.Prim.ensure_onExit_told_not_to "propext"
        , w `Effect4.Prim.ensure_onExit_already_masked "propext"
        , w `Effect4.Prim.armA_onExit "none"
        , w `Effect4.Prim.armE_onExit "none"
        , w `Effect4.Prim.onExit_finalizer_success_restores "none"
        , w `Effect4.Prim.onExit_finalizer_failure_merges "none"
        , w `Effect4.Prim.onExit_success_finalizer_failure "none"
        , w `Effect4.Prim.finalizerEvents_onExit "none"
        , w `Effect4.Prim.finalizerEvents_onSuccess "none"
        , w `Effect4.Prim.finalizerEvents_onFailure "none"
        , w `Effect4.FrameFiber.step_onExit "propext" ] }
  , { id := "op.SetInterruptible", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_setInterruptible "none"
        , w `Effect4.Prim.ensure_setInterruptible_flag "propext"
        , w `Effect4.Prim.ensure_setInterruptible_stack "propext"
        , w `Effect4.Prim.ensure_setInterruptible_substitutes "propext"
        , w `Effect4.Prim.ensure_setInterruptible_false_no_replacement "propext"
        , w `Effect4.Prim.ensure_setInterruptible_no_pending "propext"
        , w `Effect4.Prim.armA_setInterruptible_none "none"
        , w `Effect4.Prim.armE_setInterruptible_none "none"
        , w `Effect4.FrameFiber.step_setInterruptible_not_evaluable "propext" ] }
  , { id := "op.While", kind := "op", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.armA_whileLoop_continue "propext"
        , w `Effect4.Prim.armA_whileLoop_stop "propext"
        , w `Effect4.FrameFiber.step_whileLoop_true "propext"
        , w `Effect4.FrameFiber.step_whileLoop_false "propext" ] }
  , { id := "frame-arm.OnSuccess", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onSuccess "none"
        , w `Effect4.Prim.armA_isSome "propext"
        , w `Effect4.Prim.armE_isSome "none"
        , w `Effect4.Prim.armE_onSuccess_none "none"
        , w `Effect4.Prim.onSuccess_arm_is_per_instance "none" ] }
  , { id := "frame-arm.OnFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onFailure "none"
        , w `Effect4.Prim.armA_onFailure_none "none"
        , w `Effect4.Prim.onFailure_arm_is_per_instance "none" ] }
  , { id := "frame-arm.OnSuccessAndFailure", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onSuccessAndFailure "none"
        , w `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance "none" ] }
  , { id := "frame-arm.Exit", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_exitFrame "none"
        , w `Effect4.Prim.ensure_of_no_contAll "none" ] }
  , { id := "frame-arm.OnExit", kind := "frame-arm", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_onExit "none"
        , w `Effect4.Prim.ensure_onExit_masks "propext"
        , w `Effect4.Prim.ensure_onExit_told_not_to "propext"
        , w `Effect4.Prim.ensure_onExit_already_masked "propext"
        , w `Effect4.Prim.ensure_onExit_no_replacement "propext"
        , w `Effect4.Prim.onExit_arm_is_per_frame "none" ] }
  , { id := "frame-arm.SetInterruptible", kind := "frame-arm", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_setInterruptible "none"
        , w `Effect4.Prim.ensure_setInterruptible_substitutes "propext"
        , w `Effect4.Prim.answerOf_replacement "none"
        , w `Effect4.Prim.armA_setInterruptible_none "none"
        , w `Effect4.Prim.armE_setInterruptible_none "none"
        , w `Effect4.FrameFiber.resumeValue_replacement "propext"
        , w `Effect4.FrameFiber.resumeCause_replacement "propext" ] }
  , { id := "frame-arm.AsyncFinalizer", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_asyncFinalizer "none"
        , w `Effect4.Prim.hasArm_asyncFinalizer_contA_false "none" ] }
  , { id := "frame-arm.While", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_whileLoop "none"
        , w `Effect4.Prim.armE_whileLoop_none "none"
        , w `Effect4.FrameFiber.step_whileLoop_true "propext" ] }
  , { id := "frame-arm.Iterator", kind := "frame-arm", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.arms_iterator "none"
        , w `Effect4.Prim.armE_iterator_none "none"
        , w `Effect4.FrameFiber.step_iterator "propext" ] }
  , { id := "checkpoint.runloop-top", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.runloopTop_deferred "propext"
        , w `Effect4.Deep.runloopTop_idle "propext"
        , w `Effect4.Deep.runloopTop_clears "propext"
        , w `Effect4.Deep.iteration_evaluates "propext,Quot.sound" ] }
  , { id := "checkpoint.getcont-deferred", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.pendingCause_some "none"
        , w `Effect4.FrameFiber.pendingCause_none "none"
        , w `Effect4.FrameFiber.getCont_deferred "propext"
        , w `Effect4.FrameFiber.getCont_deferred_pops_nothing "propext"
        , w `Effect4.FrameFiber.getCont_skip_clears_deferred "propext"
        , w `Effect4.FrameFiber.resumeValue_deferred "propext"
        , w `Effect4.FrameFiber.resumeCause_deferred "propext" ] }
  , { id := "checkpoint.post-yield-cancel", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.interruptRecord_parked_applies "propext,Quot.sound"
        , w `Effect4.Prim.armE_asyncFinalizer_interrupt "propext"
        , w `Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push "propext" ] }
  , { id := "checkpoint.exit-failcause-skip", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.popFrom_continue_answer "propext"
        , w `Effect4.FrameFiber.getCont_skip_of_no_pending_cause "propext,Quot.sound"
        , w `Effect4.FrameFiber.interrupt_skips_every_handler "propext,Quot.sound" ] }
  , { id := "checkpoint.set-fiber-interruptible", kind := "checkpoint", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.FrameFiber.setFiberInterruptible_flag "none"
        , w `Effect4.FrameFiber.setFiberInterruptible_pushes "none"
        , w `Effect4.FrameFiber.setFiberInterruptible_immediate_failure "propext"
        , w `Effect4.FrameFiber.setFiberInterruptible_no_pending "propext"
        , w `Effect4.FrameFiber.interruptibleRegion_already "propext"
        , w `Effect4.FrameFiber.interruptibleRegion_masked "propext" ] }
  , { id := "checkpoint.set-interruptible-contall", kind := "checkpoint", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.ensure_setInterruptible_substitutes "propext"
        , w `Effect4.Prim.answerOf_replacement "none"
        , w `Effect4.FrameFiber.resumeValue_replacement "propext"
        , w `Effect4.FrameFiber.resumeCause_replacement "propext" ] }
  , { id := "interrupt.unsafe-entry", kind := "interrupt", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.interruptRecord_exited "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_records "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_running_defers "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_idle_applies "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_masked "propext,Quot.sound" ] }
  , { id := "interrupt.accumulate", kind := "interrupt", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.interruptCause_eq "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_accumulates "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_idle_applies "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_running_defers "propext,Quot.sound"
        , w `Effect4.Deep.runloopTop_deferred "propext"
        , w `Effect4.FrameFiber.pendingCause_some "none" ] }
  , { id := "fork.unsafe", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.MaskMode.cases_receipt "propext"
        , w `Effect4.Deep.spawn_eq "none"
        , w `Effect4.Deep.spawnChild_fields "propext"
        , w `Effect4.Deep.spawn_daemon_untracked "propext" ] }
  , { id := "fork.child", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.exitFiber_eq "propext,Quot.sound"
        , w `Effect4.Deep.exitFiber_no_middleware "propext,Quot.sound"
        , w `Effect4.Deep.exitStore_fields "propext,Quot.sound"
        , w `Effect4.Deep.exitStore_fires "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_resumeAwait "propext,Quot.sound"
        , w `Effect4.Deep.stepDecision_installMiddleware "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_fork "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w1_deferred_join_child "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w1_deferred_start_is_a_task "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w5_middleware_interrupts_children "propext,Quot.sound" ] }
  , { id := "fork.detach", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.spawn_daemon_untracked "propext"
        , w `Effect4.Deep.spawnChild_fields "propext"
        , w `Effect4.Deep.start_eq "none"
        , w `Effect4.Deep.exitFiber_no_children "propext,Quot.sound"
        , w `Effect4.Deep.exitInterruptChildren_eq "propext,Quot.sound"
        , w `Effect4.Deep.exitInterruptChildren_interrupts "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w5_no_middleware_leaves_children "propext,Quot.sound" ] }
  , { id := "fork.in", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.ScopeMode.cases_receipt "propext"
        , w `Effect4.Deep.withFiber_forkIn "propext,Quot.sound"
        , w `Effect4.Deep.linkScope_open "propext,Quot.sound"
        , w `Effect4.Deep.linkScope_closed "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_dropScopeFinalizer "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_closeScope "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_link_then_close "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_closed_scope_interrupts_now "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_child_exit_drops_key "propext,Quot.sound" ] }
  , { id := "fork.scoped", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.withFiber_forkScoped_ambient "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_forkScoped_none "propext,Quot.sound" ] }
  , { id := "fork.race-all", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.RaceAllState.initial_eq "none"
        , w `Effect4.Supervision.raceComplete_unknown "propext"
        , w `Effect4.Supervision.raceComplete_after_accepted "propext,Quot.sound"
        , w `Effect4.Supervision.raceComplete_success "propext,Quot.sound"
        , w `Effect4.Supervision.raceComplete_failure_last "propext,Quot.sound"
        , w `Effect4.Supervision.raceComplete_failure_pending "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_raceAll "propext,Quot.sound"
        , w `Effect4.Deep.raceEntrant_options "none"
        , w `Effect4.Deep.drive_launch_runs "propext,Quot.sound"
        , w `Effect4.Deep.drive_launch_skipped "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_raceCallback_pending "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_raceCallback_settles "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_raceCallback_late "propext,Quot.sound"
        , w `Effect4.Deep.resumePrim_continueWith "none"
        , w `Effect4.Deep.Witnesses.w3_empty_is_a_frontier "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w3_empty_until_interrupted "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w3_immediate_success_stops_launch "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w3_failure_allows_next_launch "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w3_all_failures_retain_order "propext,Quot.sound" ] }
  , { id := "fork.await-all-children", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.withFiber_snapshotChildren "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_awaitNewChildren "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_countdown_last "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_countdown_more "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w5_await_all_children_awaits_only_new "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w12_awaitAll_answers_the_exits "propext,Quot.sound" ] }
  , { id := "fork.fiber-run-in", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.ScopeMode.cases_receipt "propext"
        , w `Effect4.Deep.withFiber_runIn "propext,Quot.sound"
        , w `Effect4.Deep.linkScope_closed "propext,Quot.sound"
        , w `Effect4.Deep.linkScope_unknown "propext,Quot.sound"
        , w `Effect4.Deep.linkScope_open "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_runIn_closed_scope_uses_no_caller_annotations "propext,Quot.sound" ] }
  , { id := "fork.join", kind := "fork", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.ObserverMode.cases_receipt "propext"
        , w `Effect4.Deep.evaluatePrim_join_done "propext,Quot.sound"
        , w `Effect4.Deep.evaluatePrim_join_live "propext,Quot.sound"
        , w `Effect4.Deep.evaluatePrim_join_unknown "propext,Quot.sound" ] }
  , { id := "fork.await", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.ObserverMode.cases_receipt "propext"
        , w `Effect4.Deep.evaluatePrim_join_done "propext,Quot.sound"
        , w `Effect4.Deep.evaluatePrim_join_live "propext,Quot.sound" ] }
  , { id := "fork.interrupt", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Supervision.interruptCause_eq "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_interrupt "propext,Quot.sound"
        , w `Effect4.Deep.interruptThenJoin_eq "propext,Quot.sound"
        , w `Effect4.Deep.interruptThenJoin_unknown "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_interruptScoped_self "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_interruptScoped_other "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w2_delivered_at_unmask "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w2_recorded_once "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w2_masked_interrupt_does_not_apply "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_self_interruptor_skipped "propext,Quot.sound" ] }
  , { id := "fork.interrupt-all", kind := "fork", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.withFiber_interruptAll "propext,Quot.sound"
        , w `Effect4.Deep.interruptEach_nil "propext,Quot.sound"
        , w `Effect4.Deep.interruptEach_cons "propext,Quot.sound"
        , w `Effect4.Deep.interruptEach_known "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_countdown_last "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_countdown_more "propext,Quot.sound" ] }
  , { id := "scope.states", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.ScopeState.cases_receipt "none"
        , w `Effect4.ScopeState.entries_empty "none"
        , w `Effect4.ScopeState.entries_openEmpty "none"
        , w `Effect4.ScopeState.entries_openInline "none"
        , w `Effect4.ScopeState.entries_openMap "none"
        , w `Effect4.ScopeState.entries_closed "none"
        , w `Effect4.ScopeState.isOpen_empty "none"
        , w `Effect4.ScopeState.isOpen_openEmpty "none"
        , w `Effect4.ScopeState.isOpen_openInline "none"
        , w `Effect4.ScopeState.isOpen_openMap "none"
        , w `Effect4.ScopeState.isOpen_closed "none"
        , w `Effect4.ScopeState.isClosed_eq "none"
        , w `Effect4.ScopeState.closingExit_closed "none"
        , w `Effect4.ScopeState.closingExit_of_not_closed "none"
        , w `Effect4.ScopeState.openEmpty_ne_openMap_nil "none"
        , w `Effect4.Scope.finalizers_eq "none"
        , w `Effect4.Scope.finalizerKeys_eq "none"
        , w `Effect4.Scope.finalizerCount_eq "none"
        , w `Effect4.Scope.finalizerCount_not_open "none" ] }
  , { id := "scope.make", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FinalizerStrategy.all_nodup "none"
        , w `Effect4.FinalizerStrategy.mem_all "propext"
        , w `Effect4.Scope.make_strategy "none"
        , w `Effect4.Scope.make_state "none"
        , w `Effect4.Scope.make_finalizers "none"
        , w `Effect4.Scope.makeDefault_eq "none"
        , w `Effect4.Scope.makeDefault_strategy "none" ] }
  , { id := "scope.add-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.key_freshness_refused "none"
        , w `Effect4.Scope.tableInsert_new "propext,Quot.sound"
        , w `Effect4.Scope.tableInsert_existing "propext,Quot.sound"
        , w `Effect4.Scope.tableInsert_keys_of_mem "propext,Quot.sound"
        , w `Effect4.Scope.tableInsert_nodup "propext,Quot.sound"
        , w `Effect4.Scope.addUnsafe_strategy "none"
        , w `Effect4.Scope.addUnsafe_empty "none"
        , w `Effect4.Scope.addUnsafe_openEmpty "none"
        , w `Effect4.Scope.addUnsafe_openInline "none"
        , w `Effect4.Scope.addUnsafe_openMap "none"
        , w `Effect4.Scope.addUnsafe_promotes "propext,Quot.sound"
        , w `Effect4.Scope.addUnsafe_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.addUnsafe_keys_nodup "propext,Quot.sound" ] }
  , { id := "scope.add-after-closed", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.addUnsafe_closed "none"
        , w `Effect4.Scope.addExit_open "none"
        , w `Effect4.Scope.addExit_closed "none"
        , w `Effect4.Scope.addExit_closed_registers_nothing "none" ] }
  , { id := "scope.remove-finalizer", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.tableRemove_eq "none"
        , w `Effect4.Scope.tableRemove_keys "propext,Quot.sound"
        , w `Effect4.Scope.tableRemove_nodup "propext"
        , w `Effect4.Scope.removeUnsafe_strategy "none"
        , w `Effect4.Scope.removeUnsafe_inline_hit "none"
        , w `Effect4.Scope.removeUnsafe_inline_miss "none"
        , w `Effect4.Scope.removeUnsafe_openMap "none"
        , w `Effect4.Scope.removeUnsafe_not_open "none"
        , w `Effect4.Scope.removeUnsafe_keys "propext,Quot.sound"
        , w `Effect4.Scope.removeUnsafe_keys_nodup "propext" ] }
  , { id := "scope.close-state-first", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.close_eq "none"
        , w `Effect4.Scope.close_state_independent_of_run "none"
        , w `Effect4.Scope.closeState_state "none"
        , w `Effect4.Scope.closeState_strategy "none"
        , w `Effect4.Scope.closeState_finalizers "none"
        , w `Effect4.Scope.closeState_isClosed "none"
        , w `Effect4.Scope.closeState_idempotent "none"
        , w `Effect4.Scope.close_closingExit "none"
        , w `Effect4.Scope.close_idempotent "none"
        , w `Effect4.Scope.close_twice "none"
        , w `Effect4.Scope.close_reentrant_add "none"
        , w `Effect4.Scope.closeResult_closed "none" ] }
  , { id := "scope.close-lifo", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.closeOrder_eq "none"
        , w `Effect4.Scope.closeOrder_last_first "propext"
        , w `Effect4.Scope.closeExits_eq "none"
        , w `Effect4.Scope.closeExits_reverse "propext"
        , w `Effect4.Scope.runScoped_lifo "propext,Quot.sound" ] }
  , { id := "scope.close-sequential", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.closeExits_eq "none"
        , w `Effect4.Scope.closeExits_length "propext"
        , w `Effect4.Scope.closeResult_reasons "propext"
        , w `Effect4.Deep.closeSeqChain_order "none"
        , w `Effect4.Deep.closeSeqChain_captures "propext"
        , w `Effect4.Deep.withFiber_closeScope "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_closeScope_unknown "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_sequential_captures_and_merges "propext,Quot.sound" ] }
  , { id := "scope.close-parallel", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.FinalizerStrategy.cases_receipt "none"
        , w `Effect4.Scope.close_strategy_irrelevant "none"
        , w `Effect4.Deep.closeParChain_forks_immediate_daemon "none"
        , w `Effect4.Deep.closeParChain_awaits_all "none"
        , w `Effect4.Deep.withFiber_fork "propext,Quot.sound"
        , w `Effect4.Deep.spawnChild_fields "propext"
        , w `Effect4.Deep.Witnesses.w6_parallel_forks_and_merges "propext,Quot.sound" ] }
  , { id := "scope.close-merge", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.closeResult_nil "none"
        , w `Effect4.Scope.closeResult_single "none"
        , w `Effect4.Scope.closeResult_many "none"
        , w `Effect4.Scope.closeResult_reasons "propext"
        , w `Effect4.Deep.closeSeqChain_merges "none"
        , w `Effect4.Deep.closeParChain_awaits_all "none"
        , w `Effect4.Deep.fireObserver_countdown_last "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_countdown_more "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w6_parallel_forks_and_merges "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w12_awaitAll_answers_the_exits "propext,Quot.sound" ] }
  , { id := "scope.exit-as-void-all", kind := "scope", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Exit.asVoidAll_reasons "none"
        , w `Effect4.Exit.asVoidAll_failure "none"
        , w `Effect4.Exit.asVoidAll_all_success "propext"
        , w `Effect4.Exit.void_eq "none" ] }
  , { id := "scope.fork-linkage", kind := "scope", disposition := "separateCalculus", coverage := "green"
      -- missing clause: that the linked names are scopeClose(child, exit) and scopeRemoveFinalizerUnsafe(parent, key) needs a scope store
    , witnesses :=
        [ w `Effect4.Scope.fork_closed_parent "none"
        , w `Effect4.Scope.fork_closed_parent_child_exit "none"
        , w `Effect4.Scope.fork_open_parent "none"
        , w `Effect4.Scope.fork_child_finalizers "none"
        , w `Effect4.Scope.fork_parent_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.fork_child_strategy "none"
        , w `Effect4.Scope.fork_shared_key "propext,Quot.sound"
        , w `Effect4.Scope.fork_detach "propext,Quot.sound"
        , w `Effect4.Deep.scopeLinkFiber_name "propext"
        , w `Effect4.Deep.scopeStore_forkChild_names "propext" ] }
  , { id := "scope.scoped", kind := "scope", disposition := "separateCalculus", coverage := "green"
      -- missing clauses: "installs a fresh scope in the fiber context" and "restoring the previous context first"
    , witnesses :=
        [ w `Effect4.Scope.addAll_nil "none"
        , w `Effect4.Scope.addAll_cons "none"
        , w `Effect4.Scope.addAll_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.make_addAll_finalizers "propext,Quot.sound"
        , w `Effect4.Scope.runScoped_eq "none"
        , w `Effect4.Scope.runScoped_fresh_scope "none"
        , w `Effect4.Scope.runScoped_state "none"
        , w `Effect4.Scope.runScoped_strategy "none"
        , w `Effect4.Scope.runScoped_empty "none"
        , w `Effect4.Scope.runScoped_lifo "propext,Quot.sound"
        , w `Effect4.Prim.scopedFrame_eq "none"
        , w `Effect4.Prim.scopedFrame_finalizer_masked "propext"
        , w `Effect4.FrameFiber.step_scopedFrame "propext"
        , w `Effect4.Deep.Layers.scoped_installs_and_restores "propext,Quot.sound" ] }
  , { id := "scope.acquire-release", kind := "scope", disposition := "separateCalculus", coverage := "green"
      -- missing clause: "with the captured context" needs a Context carrier
    , witnesses :=
        [ w `Effect4.Scope.acquireRelease_failure "none"
        , w `Effect4.Scope.acquireRelease_success "none"
        , w `Effect4.Scope.acquireRelease_registers "propext,Quot.sound"
        , w `Effect4.Scope.acquireRelease_closed_ambient "none"
        , w `Effect4.FrameFiber.uninterruptible_already_masked "propext"
        , w `Effect4.FrameFiber.uninterruptible_masks "propext"
        , w `Effect4.FrameFiber.uninterruptibleMask_eq "none"
        , w `Effect4.FrameFiber.interruptibleRegion_already "propext"
        , w `Effect4.FrameFiber.interruptibleRegion_masked "propext"
        , w `Effect4.FrameFiber.restoreAcquire_asked "none"
        , w `Effect4.FrameFiber.restoreAcquire_not_asked "none"
        , w `Effect4.Deep.Layers.acquireRelease_captured_context "propext,Quot.sound" ] }
  , { id := "scheduler.should-yield", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.yieldVerdict_default "propext"
        , w `Effect4.Deep.yieldVerdict_override "propext"
        , w `Effect4.Deep.injectYield_no_verdict "propext" ] }
  , { id := "scheduler.priority-buckets", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Dispatcher.enqueue_same_bucket "propext"
        , w `Effect4.Deep.Dispatcher.enqueue_lower_priority "propext"
        , w `Effect4.Deep.Dispatcher.enqueue_empty "none" ] }
  , { id := "scheduler.dispatcher-arming", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Dispatcher.enqueue_arms "none"
        , w `Effect4.Deep.Dispatcher.drain_disarms "none" ] }
  , { id := "scheduler.run-tasks-drain-once", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Dispatcher.drain_eq "none"
        , w `Effect4.Deep.Dispatcher.drain_disarms "none"
        , w `Effect4.Deep.fire_eq "propext,Quot.sound" ] }
  , { id := "scheduler.flush", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.flushAll_idle "propext,Quot.sound"
        , w `Effect4.Deep.flushAll_round "propext,Quot.sound" ] }
  , { id := "scheduler.yield-now-resume-guard", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.evaluatePrim_yieldNowWith "propext,Quot.sound"
        , w `Effect4.Deep.drive_resume_wrong_token "propext,Quot.sound"
        , w `Effect4.Deep.drive_resume_guard "propext,Quot.sound"
        , w `Effect4.Deep.drive_resume_not_parked "propext,Quot.sound" ] }
  , { id := "scheduler.max-ops-default", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.budget_defaults "propext,Quot.sound"
        , w `Effect4.ContextFamily.maxOps_default "propext" ] }
  , { id := "scheduler.prevent-yield-default", kind := "scheduler", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.injectYield_prevented "propext"
        , w `Effect4.ContextFamily.preventYield_default "propext,Quot.sound" ] }
  , { id := "scheduler.host-loop", kind := "scheduler", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "exit.success-failure", kind := "exit", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Exit.cases_receipt "none"
        , w `Effect4.Exit.success_ne_failure "none"
        , w `Effect4.Exit.success_inj "none"
        , w `Effect4.Exit.failure_inj "none"
        , w `Effect4.Exit.cause_failure "none"
        , w `Effect4.Prim.ofExit_asExit? "none"
        , w `Effect4.Prim.asExit?_success "none"
        , w `Effect4.Prim.asExit?_failure "none"
        , w `Effect4.Prim.asExit?_eq_some "propext"
        , w `Effect4.Prim.ofExit_isFrame "none"
        , w `Effect4.FrameFiber.step_ofExit_finishes "propext"
        , w `Effect4.FrameFiber.run_zero "propext"
        , w `Effect4.FrameFiber.run_succ_finished "propext"
        , w `Effect4.FrameFiber.run_succ_running "propext" ] }
  , { id := "exit.reason-alphabet", kind := "exit", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.ReasonTag.all_nodup "none"
        , w `Effect4.ReasonTag.mem_all "propext"
        , w `Effect4.ReasonTag.cases_receipt "none"
        , w `Effect4.Reason.cases_receipt "none"
        , w `Effect4.Reason.tag_mem_all "propext" ] }
  , { id := "cause.flat-reasons", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.eq_iff "none"
        , w `Effect4.Cause.ext "none"
        , w `Effect4.Cause.eq_iff_pointwise "propext"
        , w `Effect4.Cause.combine_no_new_reason "propext" ] }
  , { id := "cause.reason-fail", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Reason.error_fail "none"
        , w `Effect4.Reason.annotations_fail "none"
        , w `Effect4.Reason.fail_inj "none" ] }
  , { id := "cause.reason-die", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Reason.defect_die "none"
        , w `Effect4.Reason.annotations_die "none"
        , w `Effect4.Reason.die_inj "none" ] }
  , { id := "cause.reason-interrupt", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.interrupt_reasons "none"
        , w `Effect4.Reason.annotations_interrupt "none"
        , w `Effect4.Reason.interrupt_inj "none" ] }
  , { id := "cause.combine-union", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.combine_empty_left "none"
        , w `Effect4.Cause.combine_empty_right "none"
        , w `Effect4.Cause.combine_reasons "none"
        , w `Effect4.Cause.mem_combine "propext"
        , w `Effect4.Cause.combine_self "propext,Quot.sound" ] }
  , { id := "cause.finalizer-merge", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Exit.mergeFinalizer_failure_failure "none"
        , w `Effect4.Exit.restoreAfterFinalizer_failure_failure "none"
        , w `Effect4.Exit.mergeFinalizer_success_failure "none"
        , w `Effect4.Exit.restoreAfterFinalizer_success_failure "none" ] }
  , { id := "cause.squash", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.squash_error "none"
        , w `Effect4.Cause.squash_defect "none"
        , w `Effect4.Cause.squash_interrupted "none"
        , w `Effect4.Cause.squash_emptyCause_iff "none"
        , w `Effect4.Cause.squash_fail_over_die "none" ] }
  , { id := "cause.union-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.combine_empty_left "none"
        , w `Effect4.Cause.combine_empty_right "none"
        , w `Effect4.Cause.combine_reasons "none"
        , w `Effect4.Cause.combine_order "propext,Quot.sound" ] }
  , { id := "cause.dedupe-first-occurrence", kind := "cause", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.dedup_cons "none"
        , w `Effect4.Cause.mem_dedup "propext"
        , w `Effect4.Cause.dedup_nodup "propext"
        , w `Effect4.Cause.dedup_of_nodup "propext,Quot.sound" ] }
  , { id := "cause.annotations", kind := "cause", disposition := "foreignBoundary", coverage := "green"
      -- the WeakMap host-identity clause is closed by refusal, not by a model
    , witnesses :=
        [ w `Effect4.ReasonAnnotations.keys_nodup "none"
        , w `Effect4.Reason.annotate_annotations "propext,Quot.sound"
        , w `Effect4.Reason.host_memory_refused "none"
        , w `Effect4.ReasonAnnotations.annotate_entries "propext,Quot.sound"
        , w `Effect4.ReasonAnnotations.lookup_annotate_kept "propext,Quot.sound"
        , w `Effect4.ReasonAnnotations.lookup_annotate_overwrite "propext,Quot.sound" ] }
  , { id := "entry.run-fork-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.runFork_eq "propext,Quot.sound" ] }
  , { id := "entry.abort-signal", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.stepDecision_abort "propext,Quot.sound" ] }
  , { id := "entry.run-callback-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.runCallback_eq "propext,Quot.sound"
        , w `Effect4.Deep.fireObserver_callback "propext,Quot.sound" ] }
  , { id := "entry.run-promise-exit-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.promiseOutcome_eq "none" ] }
  , { id := "entry.run-promise-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.promiseOutcome_failure "none" ] }
  , { id := "entry.run-sync-exit-with", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.runSyncExit_exited "propext,Quot.sound"
        , w `Effect4.Deep.runSyncExit_survives "propext,Quot.sound" ] }
  , { id := "entry.async-fiber-error", kind := "entry", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.runSyncExit_survives "propext,Quot.sound" ] }
  , { id := "entry.with-error-reporting", kind := "entry", disposition := "targetOnly", coverage := "absent", witnesses := [] }
  , { id := "rule.frames-are-primitives", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Arm.all_nodup "none"
        , w `Effect4.Arm.mem_all "propext"
        , w `Effect4.Arm.cases_receipt "none"
        , w `Effect4.Arm.demandable_eq "none"
        , w `Effect4.Arm.contAll_not_demandable "propext"
        , w `Effect4.Prim.cases_receipt "none"
        , w `Effect4.FrameFiber.start_eq "none"
        , w `Effect4.FrameFiber.masked_eq "none"
        , w `Effect4.FrameFiber.interrupted_eq "none"
        , w `Effect4.FrameEvent.poppedFrames_nil "none"
        , w `Effect4.FrameEvent.poppedFrames_cons_popped "none"
        , w `Effect4.FrameEvent.finalizersRun_nil "none"
        , w `Effect4.FrameEvent.finalizersRun_cons_ran "none"
        , w `Effect4.FrameEvent.finalizersRun_cons_popped "none"
        , w `Effect4.Prim.hasArm_eq "none"
        , w `Effect4.Prim.isFrame_eq "none"
        , w `Effect4.Prim.isFrame_iff "propext"
        , w `Effect4.Prim.non_frames_have_no_arms "none"
        , w `Effect4.Prim.answerOf_replacement "none"
        , w `Effect4.Prim.answerOf_arm "propext"
        , w `Effect4.Prim.answerOf_missing "propext"
        , w `Effect4.Prim.answerOf_frame_eq "propext"
        , w `Effect4.Prim.armA_isSome "propext"
        , w `Effect4.Prim.armE_isSome "none"
        , w `Effect4.FrameFiber.getCont_eq_popFrom "propext"
        , w `Effect4.FrameFiber.getCont_empty_stack "propext"
        , w `Effect4.FrameFiber.popFrom_nil "propext"
        , w `Effect4.FrameFiber.popFrom_answer_answer "propext"
        , w `Effect4.FrameFiber.popFrom_answer_popped "propext"
        , w `Effect4.FrameFiber.popFrom_answer_events "propext"
        , w `Effect4.FrameFiber.popFrom_answer_fiber "propext"
        , w `Effect4.FrameFiber.popFrom_continue_answer "propext"
        , w `Effect4.FrameFiber.popFrom_continue_popped "propext"
        , w `Effect4.FrameFiber.popFrom_continue_events "propext"
        , w `Effect4.FrameFiber.popFrom_continue_fiber "propext"
        , w `Effect4.FrameFiber.popFrom_answer_hasArm "propext"
        , w `Effect4.FrameFiber.getCont_answer_hasArm "propext"
        , w `Effect4.FrameFiber.passEvents_ranContAll "propext"
        , w `Effect4.FrameFiber.passEvents_poppedFrames "propext,Quot.sound"
        , w `Effect4.FrameFiber.popFrom_popped_eq_events "propext,Quot.sound"
        , w `Effect4.FrameFiber.popFrom_ranContAll "propext"
        , w `Effect4.FrameFiber.getCont_ranContAll "propext" ] }
  , { id := "rule.interrupt-bypasses-handlers", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Prim.ensure_setInterruptible_flag "propext"
        , w `Effect4.FrameFiber.interrupt_skips_every_handler "propext,Quot.sound"
        , w `Effect4.FrameFiber.getCont_mask_stops_skip "propext"
        , w `Effect4.FrameFiber.step_failure "propext" ] }
  , { id := "rule.yield-is-overloaded", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.drive_loop_parked "propext,Quot.sound"
        , w `Effect4.Deep.drive_loop_continues "propext,Quot.sound" ] }
  , { id := "rule.only-fork-child-tracks", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.spawn_daemon_untracked "propext"
        , w `Effect4.Deep.spawnChild_fields "propext"
        , w `Effect4.Deep.withFiber_fork "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_forkIn "propext,Quot.sound"
        , w `Effect4.Deep.withFiber_forkScoped_ambient "propext,Quot.sound"
        , w `Effect4.Deep.raceEntrant_options "none"
        , w `Effect4.Deep.fireObserver_untrackChild "propext,Quot.sound" ] }
  , { id := "rule.children-interrupted-after-exit", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.exitFiber_eq "propext,Quot.sound"
        , w `Effect4.Deep.exitFiber_children "propext,Quot.sound"
        , w `Effect4.Deep.exitInterruptChildren_eq "propext,Quot.sound"
        , w `Effect4.Deep.exitInterruptChildren_finalizing "propext,Quot.sound"
        , w `Effect4.Deep.exitInterruptChildren_interrupts "propext,Quot.sound"
        , w `Effect4.Deep.resumePrim_continueWith "none"
        , w `Effect4.Deep.exitFiber_finalizing "propext,Quot.sound"
        , w `Effect4.Deep.Witnesses.w5_middleware_interrupts_children "propext,Quot.sound" ] }
  , { id := "rule.scope-close-lifo-state-first", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Scope.close_state_independent_of_run "none"
        , w `Effect4.Scope.closeState_finalizers "none"
        , w `Effect4.Scope.close_reentrant_add "none"
        , w `Effect4.Scope.closeOrder_last_first "propext"
        , w `Effect4.Scope.closeExits_reverse "propext" ] }
  , { id := "rule.cause-has-no-structure", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Cause.mem_combine "propext"
        , w `Effect4.Cause.combine_order "propext,Quot.sound"
        , w `Effect4.Cause.combine_no_new_reason "propext"
        , w `Effect4.Cause.ext "none" ] }
  , { id := "rule.start-is-asymmetric", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.start_eq "none"
        , w `Effect4.Deep.runFork_eq "propext,Quot.sound" ] }
  , { id := "rule.record-and-apply-separate", kind := "rule", disposition := "owned", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.interruptRecord_records "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_running_defers "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_idle_applies "propext,Quot.sound"
        , w `Effect4.Deep.interruptRecord_masked "propext,Quot.sound" ] }
  , { id := "rule.budget-per-runloop-entry", kind := "rule", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.countOp_count "none"
        , w `Effect4.Deep.drive_evaluate_enters "propext,Quot.sound"
        , w `Effect4.Deep.drive_evaluate_exited "propext,Quot.sound"
        , w `Effect4.Deep.drive_evaluate_running "propext,Quot.sound"
        , w `Effect4.Deep.injectYield_latched "propext"
        , w `Effect4.Deep.injectYield_fires "propext"
        , w `Effect4.Deep.iteration_injected "propext,Quot.sound" ] }
    -- The Ref and Deferred rows are carried by the reference machine's stores
    -- (`Effect4/Deep/Stores.lean`) and the Layer rows by its Layer model
    -- (`Effect4/Deep/Layer.lean`) since 2026-09-04. The five `derivedExpansion`
    -- rows are the ones the pinned source itself defines in terms of another
    -- pinned operation; the rest are `separateCalculus`.
  , { id := "ref.make", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_make "propext"
        , w `Effect4.Deep.refMake_twice_distinct "propext" ] }
  , { id := "ref.get", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_get "propext"
        , w `Effect4.Deep.refStep_get_after_set "propext" ] }
  , { id := "ref.set-void-returns-cell", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_set "propext"
        , w `Effect4.Deep.set_answer_ne_update_answer "none" ] }
  , { id := "ref.cell-set-returns-self", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_set_answers_self "propext" ] }
  , { id := "ref.get-and-set", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_getAndSet "propext" ] }
  , { id := "ref.set-and-get-assignment", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_setAndGet "propext" ] }
  , { id := "ref.update", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_update "propext"
        , w `Effect4.Deep.refStep_update_applies_once "propext" ] }
  , { id := "ref.modify", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_modify "propext" ] }
  , { id := "ref.modify-some-no-reread", kind := "ref", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_modifySome_eq_modify "propext"
        , w `Effect4.Deep.refStep_modifySome_none "propext" ] }
  , { id := "ref.update-some-and-get-reread", kind := "ref", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.refStep_updateSomeAndGet_some "propext" ] }
  , { id := "deferred.make", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredStore_make "none" ] }
  , { id := "deferred.is-done", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredStore_isDone "propext" ] }
  , { id := "deferred.await", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.awaitDeferred_is_a_park "none"
        , w `Effect4.Deep.deferredStore_register_pending "propext"
        , w `Effect4.Deep.deferredStore_register_done "propext" ] }
  , { id := "deferred.single-completion", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredStore_complete_done "propext" ] }
  , { id := "deferred.completion-order", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredStore_complete_pending "propext" ] }
  , { id := "deferred.complete-with-stores-effect", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredStore_complete_stores_argument "propext"
        , w `Effect4.Deep.deferredStore_waiter_receives_stored "propext" ] }
  , { id := "deferred.done-is-complete-with", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.doneWith_shared "none"
        , w `Effect4.Deep.completionPrim_ofExit "none" ] }
  , { id := "deferred.complete-runs-once", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredStore_complete_done "propext" ] }
  , { id := "deferred.into-uninterruptible", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.intoDeferred_spelling "none" ] }
  , { id := "deferred.interrupt", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.interruptDeferred_delegates "propext" ] }
  , { id := "deferred.interrupt-with", kind := "deferred", disposition := "derivedExpansion", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.interruptWith_is_completion "propext" ] }
  , { id := "deferred.poll", kind := "deferred", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.deferredPoll_no_write "propext" ] }
  , { id := "layer.from-build-unsafe", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.fromBuildUnsafe_no_scope "propext,Quot.sound" ] }
  , { id := "layer.from-build-child-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.fromBuild_forks_child "propext,Quot.sound"
        , w `Effect4.Deep.Layers.fromBuild_closes_on_failure "none" ] }
  , { id := "layer.build-with-memo-map-service", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.buildWithMemoMap_installs "propext,Quot.sound"
        , w `Effect4.Deep.Layers.buildWithMemoMap_provides "propext,Quot.sound" ] }
  , { id := "layer.memo-build-once", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.memoBuild_allocates "propext"
        , w `Effect4.Deep.Layers.memoBuild_entry "none" ] }
  , { id := "layer.memo-finalizer-last-observer", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.memoRelease_last "propext"
        , w `Effect4.Deep.Layers.memoRelease_decrements "propext" ] }
  , { id := "layer.memo-reuse-observer-count", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.memoGet_hit "propext"
        , w `Effect4.Deep.Layers.memoize_hit "propext,Quot.sound" ] }
  , { id := "layer.memo-map-parent-lookup", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.MemoWorld.get_parent "propext" ] }
  , { id := "layer.memo-get-or-else", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.getOrElseMemoize_shape "propext,Quot.sound" ] }
  , { id := "layer.current-memo-map-fork-or-create", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.forkOrCreate "propext,Quot.sound" ] }
  , { id := "layer.build-uses-ambient-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.build_uses_ambient_scope "propext,Quot.sound" ] }
  , { id := "layer.build-with-scope-still-forks-memo", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.buildWithScope_forks_memo "propext,Quot.sound" ] }
  , { id := "layer.merge-parallel-scopes", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.mergeAll_scopes "propext,Quot.sound" ] }
  , { id := "layer.provide-dependency-first", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.provide_dependency_first "propext,Quot.sound" ] }
  , { id := "layer.fresh-drops-memoization", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.fresh_drops_memoization "propext,Quot.sound" ] }
  , { id := "layer.launch-holds-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.launch_holds_scope "propext,Quot.sound" ] }
  , { id := "layer.provide-effect-scope", kind := "layer", disposition := "separateCalculus", coverage := "green"
    , witnesses :=
        [ w `Effect4.Deep.Layers.provideLayer_scope "propext,Quot.sound" ] }
  ]

/-- The witness names frozen by `StatementSnapshot`, in snapshot order.
`scripts/check-effect-runtime-census.sh` compares this list, as emitted, with
the `#check (@…` occurrences in this file, so a deleted ascription fails. -/
private def snapshotWitnesses : List Name :=
  [ `Effect4.Cause.eq_iff
  , `Effect4.Cause.ext
  , `Effect4.Cause.eq_iff_pointwise
  , `Effect4.Cause.combine_no_new_reason
  , `Effect4.Reason.error_fail
  , `Effect4.Reason.annotations_fail
  , `Effect4.Reason.fail_inj
  , `Effect4.Reason.defect_die
  , `Effect4.Reason.annotations_die
  , `Effect4.Reason.die_inj
  , `Effect4.Cause.interrupt_reasons
  , `Effect4.Reason.annotations_interrupt
  , `Effect4.Reason.interrupt_inj
  , `Effect4.Cause.combine_empty_left
  , `Effect4.Cause.combine_empty_right
  , `Effect4.Cause.combine_reasons
  , `Effect4.Cause.mem_combine
  , `Effect4.Cause.combine_self
  , `Effect4.Cause.combine_order
  , `Effect4.Cause.dedup_cons
  , `Effect4.Cause.mem_dedup
  , `Effect4.Cause.dedup_nodup
  , `Effect4.Cause.dedup_of_nodup
  , `Effect4.Exit.mergeFinalizer_failure_failure
  , `Effect4.Exit.restoreAfterFinalizer_failure_failure
  , `Effect4.Exit.mergeFinalizer_success_failure
  , `Effect4.Exit.restoreAfterFinalizer_success_failure
  , `Effect4.Cause.squash_error
  , `Effect4.Cause.squash_defect
  , `Effect4.Cause.squash_interrupted
  , `Effect4.Cause.squash_emptyCause_iff
  , `Effect4.Cause.squash_fail_over_die
  , `Effect4.ReasonAnnotations.keys_nodup
  , `Effect4.Reason.annotate_annotations
  , `Effect4.Reason.host_memory_refused
  , `Effect4.ReasonAnnotations.annotate_entries
  , `Effect4.ReasonAnnotations.lookup_annotate_kept
  , `Effect4.ReasonAnnotations.lookup_annotate_overwrite
  , `Effect4.Exit.cases_receipt
  , `Effect4.Exit.success_ne_failure
  , `Effect4.Exit.success_inj
  , `Effect4.Exit.failure_inj
  , `Effect4.Exit.cause_failure
  , `Effect4.ReasonTag.all_nodup
  , `Effect4.ReasonTag.mem_all
  , `Effect4.ReasonTag.cases_receipt
  , `Effect4.Reason.cases_receipt
  , `Effect4.Reason.tag_mem_all
  , `Effect4.Exit.asVoidAll_reasons
  , `Effect4.Exit.asVoidAll_failure
  , `Effect4.Exit.asVoidAll_all_success
  , `Effect4.Exit.void_eq
  , `Effect4.ScopeState.cases_receipt
  , `Effect4.ScopeState.entries_empty
  , `Effect4.ScopeState.entries_openEmpty
  , `Effect4.ScopeState.entries_openInline
  , `Effect4.ScopeState.entries_openMap
  , `Effect4.ScopeState.entries_closed
  , `Effect4.ScopeState.isOpen_empty
  , `Effect4.ScopeState.isOpen_openEmpty
  , `Effect4.ScopeState.isOpen_openInline
  , `Effect4.ScopeState.isOpen_openMap
  , `Effect4.ScopeState.isOpen_closed
  , `Effect4.ScopeState.isClosed_eq
  , `Effect4.ScopeState.closingExit_closed
  , `Effect4.ScopeState.closingExit_of_not_closed
  , `Effect4.ScopeState.openEmpty_ne_openMap_nil
  , `Effect4.Scope.finalizers_eq
  , `Effect4.Scope.finalizerKeys_eq
  , `Effect4.Scope.finalizerCount_eq
  , `Effect4.Scope.finalizerCount_not_open
  , `Effect4.FinalizerStrategy.all_nodup
  , `Effect4.FinalizerStrategy.mem_all
  , `Effect4.Scope.make_strategy
  , `Effect4.Scope.make_state
  , `Effect4.Scope.make_finalizers
  , `Effect4.Scope.makeDefault_eq
  , `Effect4.Scope.makeDefault_strategy
  , `Effect4.Scope.key_freshness_refused
  , `Effect4.Scope.tableInsert_new
  , `Effect4.Scope.tableInsert_existing
  , `Effect4.Scope.tableInsert_keys_of_mem
  , `Effect4.Scope.tableInsert_nodup
  , `Effect4.Scope.addUnsafe_strategy
  , `Effect4.Scope.addUnsafe_empty
  , `Effect4.Scope.addUnsafe_openEmpty
  , `Effect4.Scope.addUnsafe_openInline
  , `Effect4.Scope.addUnsafe_openMap
  , `Effect4.Scope.addUnsafe_promotes
  , `Effect4.Scope.addUnsafe_finalizers
  , `Effect4.Scope.addUnsafe_keys_nodup
  , `Effect4.Scope.addUnsafe_closed
  , `Effect4.Scope.addExit_open
  , `Effect4.Scope.addExit_closed
  , `Effect4.Scope.addExit_closed_registers_nothing
  , `Effect4.Scope.tableRemove_eq
  , `Effect4.Scope.tableRemove_keys
  , `Effect4.Scope.tableRemove_nodup
  , `Effect4.Scope.removeUnsafe_strategy
  , `Effect4.Scope.removeUnsafe_inline_hit
  , `Effect4.Scope.removeUnsafe_inline_miss
  , `Effect4.Scope.removeUnsafe_openMap
  , `Effect4.Scope.removeUnsafe_not_open
  , `Effect4.Scope.removeUnsafe_keys
  , `Effect4.Scope.removeUnsafe_keys_nodup
  , `Effect4.Scope.close_eq
  , `Effect4.Scope.close_state_independent_of_run
  , `Effect4.Scope.closeState_state
  , `Effect4.Scope.closeState_strategy
  , `Effect4.Scope.closeState_finalizers
  , `Effect4.Scope.closeState_isClosed
  , `Effect4.Scope.closeState_idempotent
  , `Effect4.Scope.close_closingExit
  , `Effect4.Scope.close_idempotent
  , `Effect4.Scope.close_twice
  , `Effect4.Scope.close_reentrant_add
  , `Effect4.Scope.closeResult_closed
  , `Effect4.Scope.closeOrder_eq
  , `Effect4.Scope.closeOrder_last_first
  , `Effect4.Scope.closeExits_eq
  , `Effect4.Scope.closeExits_reverse
  , `Effect4.Scope.runScoped_lifo
  , `Effect4.Scope.closeExits_length
  , `Effect4.Scope.closeResult_reasons
  , `Effect4.FinalizerStrategy.cases_receipt
  , `Effect4.Scope.close_strategy_irrelevant
  , `Effect4.Scope.closeResult_nil
  , `Effect4.Scope.closeResult_single
  , `Effect4.Scope.closeResult_many
  , `Effect4.Scope.fork_closed_parent
  , `Effect4.Scope.fork_closed_parent_child_exit
  , `Effect4.Scope.fork_open_parent
  , `Effect4.Scope.fork_child_finalizers
  , `Effect4.Scope.fork_parent_finalizers
  , `Effect4.Scope.fork_child_strategy
  , `Effect4.Scope.fork_shared_key
  , `Effect4.Scope.fork_detach
  , `Effect4.Scope.addAll_nil
  , `Effect4.Scope.addAll_cons
  , `Effect4.Scope.addAll_finalizers
  , `Effect4.Scope.make_addAll_finalizers
  , `Effect4.Scope.runScoped_eq
  , `Effect4.Scope.runScoped_fresh_scope
  , `Effect4.Scope.runScoped_state
  , `Effect4.Scope.runScoped_strategy
  , `Effect4.Scope.runScoped_empty
  , `Effect4.Scope.acquireRelease_failure
  , `Effect4.Scope.acquireRelease_success
  , `Effect4.Scope.acquireRelease_registers
  , `Effect4.Scope.acquireRelease_closed_ambient
  , `Effect4.Supervision.MaskMode.cases_receipt
  , `Effect4.Supervision.ObserverMode.cases_receipt
  , `Effect4.Supervision.ScopeMode.cases_receipt
  , `Effect4.Supervision.interruptCause_eq
  , `Effect4.Supervision.RaceAllState.initial_eq
  , `Effect4.Supervision.raceComplete_unknown
  , `Effect4.Supervision.raceComplete_after_accepted
  , `Effect4.Supervision.raceComplete_success
  , `Effect4.Supervision.raceComplete_failure_last
  , `Effect4.Supervision.raceComplete_failure_pending
  , `Effect4.Arm.all_nodup
  , `Effect4.Arm.mem_all
  , `Effect4.Arm.cases_receipt
  , `Effect4.Arm.demandable_eq
  , `Effect4.Arm.contAll_not_demandable
  , `Effect4.Prim.cases_receipt
  , `Effect4.FrameFiber.start_eq
  , `Effect4.FrameFiber.pendingCause_some
  , `Effect4.FrameFiber.pendingCause_none
  , `Effect4.FrameFiber.masked_eq
  , `Effect4.FrameFiber.interrupted_eq
  , `Effect4.FrameEvent.poppedFrames_nil
  , `Effect4.FrameEvent.poppedFrames_cons_popped
  , `Effect4.FrameEvent.finalizersRun_nil
  , `Effect4.FrameEvent.finalizersRun_cons_ran
  , `Effect4.FrameEvent.finalizersRun_cons_popped
  , `Effect4.Prim.hasArm_eq
  , `Effect4.Prim.isFrame_eq
  , `Effect4.Prim.isFrame_iff
  , `Effect4.Prim.arms_onSuccess
  , `Effect4.Prim.arms_onFailure
  , `Effect4.Prim.arms_onSuccessAndFailure
  , `Effect4.Prim.arms_exitFrame
  , `Effect4.Prim.arms_onExit
  , `Effect4.Prim.arms_setInterruptible
  , `Effect4.Prim.arms_whileLoop
  , `Effect4.Prim.arms_iterator
  , `Effect4.Prim.non_frames_have_no_arms
  , `Effect4.Prim.ofExit_asExit?
  , `Effect4.Prim.asExit?_success
  , `Effect4.Prim.asExit?_failure
  , `Effect4.Prim.asExit?_eq_some
  , `Effect4.Prim.ofExit_isFrame
  , `Effect4.Prim.ensure_of_no_contAll
  , `Effect4.Prim.ensure_onExit_masks
  , `Effect4.Prim.ensure_onExit_told_not_to
  , `Effect4.Prim.ensure_onExit_already_masked
  , `Effect4.Prim.ensure_onExit_no_replacement
  , `Effect4.Prim.ensure_setInterruptible_flag
  , `Effect4.Prim.ensure_setInterruptible_stack
  , `Effect4.Prim.ensure_setInterruptible_substitutes
  , `Effect4.Prim.ensure_setInterruptible_false_no_replacement
  , `Effect4.Prim.ensure_setInterruptible_no_pending
  , `Effect4.Prim.answerOf_replacement
  , `Effect4.Prim.answerOf_arm
  , `Effect4.Prim.answerOf_missing
  , `Effect4.Prim.answerOf_frame_eq
  , `Effect4.Prim.armA_isSome
  , `Effect4.Prim.armE_isSome
  , `Effect4.Prim.armA_onSuccess
  , `Effect4.Prim.armA_onSuccessAndFailure
  , `Effect4.Prim.armE_onFailure
  , `Effect4.Prim.armE_onSuccessAndFailure
  , `Effect4.Prim.armE_onSuccess_none
  , `Effect4.Prim.armA_onFailure_none
  , `Effect4.Prim.armA_setInterruptible_none
  , `Effect4.Prim.armE_setInterruptible_none
  , `Effect4.Prim.armE_whileLoop_none
  , `Effect4.Prim.armE_iterator_none
  , `Effect4.Prim.armA_exitFrame_provided
  , `Effect4.Prim.armA_exitFrame_none
  , `Effect4.Prim.armE_exitFrame_provided
  , `Effect4.Prim.armE_exitFrame_none
  , `Effect4.Prim.armA_onExit
  , `Effect4.Prim.armE_onExit
  , `Effect4.Prim.onExit_finalizer_success_restores
  , `Effect4.Prim.onExit_finalizer_failure_merges
  , `Effect4.Prim.onExit_success_finalizer_failure
  , `Effect4.Prim.onExit_arm_is_per_frame
  , `Effect4.Prim.onSuccess_arm_is_per_instance
  , `Effect4.Prim.onFailure_arm_is_per_instance
  , `Effect4.Prim.onSuccessAndFailure_arms_are_per_instance
  , `Effect4.Prim.armA_whileLoop_continue
  , `Effect4.Prim.armA_whileLoop_stop
  , `Effect4.Prim.armA_iterator_done
  , `Effect4.Prim.armA_iterator_halt
  , `Effect4.Prim.armA_iterator_resume
  , `Effect4.Prim.iteratorFolded_eq
  , `Effect4.Prim.iterator_folds_inline
  , `Effect4.Prim.finalizerEvents_onExit
  , `Effect4.Prim.finalizerEvents_onSuccess
  , `Effect4.Prim.finalizerEvents_onFailure
  , `Effect4.FrameFiber.getCont_deferred
  , `Effect4.FrameFiber.getCont_deferred_pops_nothing
  , `Effect4.FrameFiber.getCont_eq_popFrom
  , `Effect4.FrameFiber.getCont_skip_clears_deferred
  , `Effect4.FrameFiber.getCont_empty_stack
  , `Effect4.FrameFiber.popFrom_nil
  , `Effect4.FrameFiber.popFrom_answer_answer
  , `Effect4.FrameFiber.popFrom_answer_popped
  , `Effect4.FrameFiber.popFrom_answer_events
  , `Effect4.FrameFiber.popFrom_answer_fiber
  , `Effect4.FrameFiber.popFrom_continue_answer
  , `Effect4.FrameFiber.popFrom_continue_popped
  , `Effect4.FrameFiber.popFrom_continue_events
  , `Effect4.FrameFiber.popFrom_continue_fiber
  , `Effect4.FrameFiber.popFrom_answer_hasArm
  , `Effect4.FrameFiber.getCont_answer_hasArm
  , `Effect4.FrameFiber.passEvents_ranContAll
  , `Effect4.FrameFiber.passEvents_poppedFrames
  , `Effect4.FrameFiber.popFrom_popped_eq_events
  , `Effect4.FrameFiber.popFrom_ranContAll
  , `Effect4.FrameFiber.getCont_ranContAll
  , `Effect4.FrameFiber.getCont_skip_of_no_pending_cause
  , `Effect4.FrameFiber.interrupt_skips_every_handler
  , `Effect4.FrameFiber.getCont_mask_stops_skip
  , `Effect4.FrameFiber.resumeValue_empty
  , `Effect4.FrameFiber.resumeValue_deferred
  , `Effect4.FrameFiber.resumeValue_replacement
  , `Effect4.FrameFiber.resumeValue_frame
  , `Effect4.FrameFiber.resumeCause_empty
  , `Effect4.FrameFiber.resumeCause_deferred
  , `Effect4.FrameFiber.resumeCause_replacement
  , `Effect4.FrameFiber.resumeCause_frame
  , `Effect4.FrameFiber.step_success
  , `Effect4.FrameFiber.step_failure
  , `Effect4.FrameFiber.step_sync
  , `Effect4.FrameFiber.step_suspend
  , `Effect4.FrameFiber.step_withFiber
  , `Effect4.FrameFiber.step_yieldableError
  , `Effect4.FrameFiber.step_onSuccess
  , `Effect4.FrameFiber.step_onFailure
  , `Effect4.FrameFiber.step_onSuccessAndFailure
  , `Effect4.FrameFiber.step_exitFrame
  , `Effect4.FrameFiber.step_onExit
  , `Effect4.FrameFiber.step_setInterruptible_not_evaluable
  , `Effect4.FrameFiber.step_whileLoop_true
  , `Effect4.FrameFiber.step_whileLoop_false
  , `Effect4.FrameFiber.step_iterator
  , `Effect4.FrameFiber.step_ofExit_finishes
  , `Effect4.FrameFiber.run_zero
  , `Effect4.FrameFiber.run_succ_finished
  , `Effect4.FrameFiber.run_succ_running
  , `Effect4.FrameFiber.uninterruptible_already_masked
  , `Effect4.FrameFiber.uninterruptible_masks
  , `Effect4.FrameFiber.uninterruptibleMask_eq
  , `Effect4.FrameFiber.setFiberInterruptible_flag
  , `Effect4.FrameFiber.setFiberInterruptible_pushes
  , `Effect4.FrameFiber.setFiberInterruptible_immediate_failure
  , `Effect4.FrameFiber.setFiberInterruptible_no_pending
  , `Effect4.FrameFiber.interruptibleRegion_already
  , `Effect4.FrameFiber.interruptibleRegion_masked
  , `Effect4.FrameFiber.restoreAcquire_asked
  , `Effect4.FrameFiber.restoreAcquire_not_asked
  , `Effect4.Prim.scopedFrame_eq
  , `Effect4.Prim.scopedFrame_finalizer_masked
  , `Effect4.FrameFiber.step_scopedFrame
  , `Effect4.Prim.withFiber_refused
  , `Effect4.Prim.yieldableError_host_class_refused
  , `Effect4.Deep.runloopTop_deferred
  , `Effect4.Deep.runloopTop_idle
  , `Effect4.Deep.runloopTop_clears
  , `Effect4.Deep.iteration_evaluates
  , `Effect4.Deep.interruptRecord_parked_applies
  , `Effect4.Prim.armE_asyncFinalizer_interrupt
  , `Effect4.FrameFiber.popFrom_asyncFinalizer_pops_its_push
  , `Effect4.Deep.countOp_count
  , `Effect4.Deep.drive_evaluate_enters
  , `Effect4.Deep.drive_evaluate_exited
  , `Effect4.Deep.drive_evaluate_running
  , `Effect4.Deep.injectYield_latched
  , `Effect4.Deep.injectYield_fires
  , `Effect4.Deep.iteration_injected
  , `Effect4.Deep.drive_loop_parked
  , `Effect4.Deep.drive_loop_continues
  , `Effect4.Deep.start_eq
  , `Effect4.Deep.runFork_eq
  , `Effect4.Deep.interruptRecord_records
  , `Effect4.Deep.interruptRecord_running_defers
  , `Effect4.Deep.interruptRecord_idle_applies
  , `Effect4.Deep.interruptRecord_masked
  , `Effect4.Deep.spawn_daemon_untracked
  , `Effect4.Deep.spawnChild_fields
  , `Effect4.Deep.interruptRecord_exited
  , `Effect4.Deep.interruptRecord_accumulates
  , `Effect4.Deep.yieldVerdict_default
  , `Effect4.Deep.yieldVerdict_override
  , `Effect4.Deep.injectYield_no_verdict
  , `Effect4.Deep.Dispatcher.enqueue_same_bucket
  , `Effect4.Deep.Dispatcher.enqueue_lower_priority
  , `Effect4.Deep.Dispatcher.enqueue_empty
  , `Effect4.Deep.Dispatcher.enqueue_arms
  , `Effect4.Deep.Dispatcher.drain_disarms
  , `Effect4.Deep.Dispatcher.drain_eq
  , `Effect4.Deep.fire_eq
  , `Effect4.Deep.flushAll_idle
  , `Effect4.Deep.flushAll_round
  , `Effect4.Deep.evaluatePrim_yieldNowWith
  , `Effect4.Deep.drive_resume_wrong_token
  , `Effect4.Deep.drive_resume_guard
  , `Effect4.Deep.drive_resume_not_parked
  , `Effect4.Deep.budget_defaults
  , `Effect4.ContextFamily.maxOps_default
  , `Effect4.Deep.injectYield_prevented
  , `Effect4.ContextFamily.preventYield_default
  , `Effect4.Deep.stepDecision_abort
  , `Effect4.Deep.runCallback_eq
  , `Effect4.Deep.fireObserver_callback
  , `Effect4.Deep.promiseOutcome_eq
  , `Effect4.Deep.promiseOutcome_failure
  , `Effect4.Deep.runSyncExit_exited
  , `Effect4.Deep.runSyncExit_survives
  , `Effect4.Deep.spawn_eq
  , `Effect4.Deep.evaluatePrim_join_done
  , `Effect4.Deep.evaluatePrim_join_live
  , `Effect4.Deep.evaluatePrim_join_unknown
  , `Effect4.Deep.withFiber_snapshotChildren
  , `Effect4.Deep.withFiber_awaitNewChildren
  , `Effect4.Deep.withFiber_runIn
  , `Effect4.Deep.linkScope_closed
  , `Effect4.Deep.linkScope_unknown
  , `Effect4.FrameFiber.step_async_frontier
  , `Effect4.Prim.armE_asyncFinalizer_no_interrupt
  , `Effect4.Prim.ensure_asyncFinalizer_masks
  , `Effect4.Prim.arms_asyncFinalizer
  , `Effect4.Prim.hasArm_asyncFinalizer_contA_false
  , `Effect4.Deep.closeSeqChain_order
  , `Effect4.Deep.closeSeqChain_captures
  , `Effect4.Deep.closeParChain_forks_immediate_daemon
  , `Effect4.Deep.closeParChain_awaits_all
  , `Effect4.Deep.closeSeqChain_merges
  , `Effect4.Deep.scopeLinkFiber_name
  , `Effect4.Deep.scopeStore_forkChild_names
  , `Effect4.Deep.Layers.scoped_installs_and_restores
  , `Effect4.Deep.Layers.acquireRelease_captured_context
  , `Effect4.Deep.refStep_make
  , `Effect4.Deep.refMake_twice_distinct
  , `Effect4.Deep.refStep_get
  , `Effect4.Deep.refStep_get_after_set
  , `Effect4.Deep.refStep_set
  , `Effect4.Deep.set_answer_ne_update_answer
  , `Effect4.Deep.refStep_set_answers_self
  , `Effect4.Deep.refStep_getAndSet
  , `Effect4.Deep.refStep_setAndGet
  , `Effect4.Deep.refStep_update
  , `Effect4.Deep.refStep_update_applies_once
  , `Effect4.Deep.refStep_modify
  , `Effect4.Deep.refStep_modifySome_eq_modify
  , `Effect4.Deep.refStep_modifySome_none
  , `Effect4.Deep.refStep_updateSomeAndGet_some
  , `Effect4.Deep.deferredStore_make
  , `Effect4.Deep.deferredStore_isDone
  , `Effect4.Deep.awaitDeferred_is_a_park
  , `Effect4.Deep.deferredStore_register_pending
  , `Effect4.Deep.deferredStore_register_done
  , `Effect4.Deep.deferredStore_complete_done
  , `Effect4.Deep.deferredStore_complete_pending
  , `Effect4.Deep.deferredStore_complete_stores_argument
  , `Effect4.Deep.deferredStore_waiter_receives_stored
  , `Effect4.Deep.doneWith_shared
  , `Effect4.Deep.completionPrim_ofExit
  , `Effect4.Deep.interruptDeferred_delegates
  , `Effect4.Deep.interruptWith_is_completion
  , `Effect4.Deep.intoDeferred_spelling
  , `Effect4.Deep.deferredPoll_no_write
  , `Effect4.Deep.Layers.fromBuildUnsafe_no_scope
  , `Effect4.Deep.Layers.fromBuild_forks_child
  , `Effect4.Deep.Layers.fromBuild_closes_on_failure
  , `Effect4.Deep.Layers.buildWithMemoMap_installs
  , `Effect4.Deep.Layers.buildWithMemoMap_provides
  , `Effect4.Deep.Layers.memoBuild_allocates
  , `Effect4.Deep.Layers.memoBuild_entry
  , `Effect4.Deep.Layers.memoRelease_last
  , `Effect4.Deep.Layers.memoRelease_decrements
  , `Effect4.Deep.Layers.memoGet_hit
  , `Effect4.Deep.Layers.memoize_hit
  , `Effect4.Deep.Layers.MemoWorld.get_parent
  , `Effect4.Deep.Layers.getOrElseMemoize_shape
  , `Effect4.Deep.Layers.forkOrCreate
  , `Effect4.Deep.Layers.build_uses_ambient_scope
  , `Effect4.Deep.Layers.buildWithScope_forks_memo
  , `Effect4.Deep.Layers.mergeAll_scopes
  , `Effect4.Deep.Layers.provide_dependency_first
  , `Effect4.Deep.Layers.fresh_drops_memoization
  , `Effect4.Deep.Layers.launch_holds_scope
  , `Effect4.Deep.Layers.provideLayer_scope
  , `Effect4.Deep.exitFiber_eq
  , `Effect4.Deep.exitFiber_no_middleware
  , `Effect4.Deep.exitStore_fields
  , `Effect4.Deep.exitStore_fires
  , `Effect4.Deep.fireObserver_resumeAwait
  , `Effect4.Deep.stepDecision_installMiddleware
  , `Effect4.Deep.withFiber_fork
  , `Effect4.Deep.Witnesses.w1_deferred_join_child
  , `Effect4.Deep.Witnesses.w1_deferred_start_is_a_task
  , `Effect4.Deep.Witnesses.w5_middleware_interrupts_children
  , `Effect4.Deep.exitFiber_no_children
  , `Effect4.Deep.exitInterruptChildren_eq
  , `Effect4.Deep.exitInterruptChildren_interrupts
  , `Effect4.Deep.Witnesses.w5_no_middleware_leaves_children
  , `Effect4.Deep.withFiber_forkIn
  , `Effect4.Deep.linkScope_open
  , `Effect4.Deep.fireObserver_dropScopeFinalizer
  , `Effect4.Deep.withFiber_closeScope
  , `Effect4.Deep.Witnesses.w6_link_then_close
  , `Effect4.Deep.Witnesses.w6_closed_scope_interrupts_now
  , `Effect4.Deep.Witnesses.w6_child_exit_drops_key
  , `Effect4.Deep.withFiber_forkScoped_ambient
  , `Effect4.Deep.withFiber_forkScoped_none
  , `Effect4.Deep.withFiber_raceAll
  , `Effect4.Deep.raceEntrant_options
  , `Effect4.Deep.drive_launch_runs
  , `Effect4.Deep.drive_launch_skipped
  , `Effect4.Deep.fireObserver_raceCallback_pending
  , `Effect4.Deep.fireObserver_raceCallback_settles
  , `Effect4.Deep.fireObserver_raceCallback_late
  , `Effect4.Deep.resumePrim_continueWith
  , `Effect4.Deep.Witnesses.w3_empty_is_a_frontier
  , `Effect4.Deep.Witnesses.w3_empty_until_interrupted
  , `Effect4.Deep.Witnesses.w3_immediate_success_stops_launch
  , `Effect4.Deep.Witnesses.w3_failure_allows_next_launch
  , `Effect4.Deep.Witnesses.w3_all_failures_retain_order
  , `Effect4.Deep.withFiber_interrupt
  , `Effect4.Deep.interruptThenJoin_eq
  , `Effect4.Deep.interruptThenJoin_unknown
  , `Effect4.Deep.withFiber_interruptScoped_self
  , `Effect4.Deep.withFiber_interruptScoped_other
  , `Effect4.Deep.Witnesses.w2_delivered_at_unmask
  , `Effect4.Deep.Witnesses.w2_recorded_once
  , `Effect4.Deep.Witnesses.w2_masked_interrupt_does_not_apply
  , `Effect4.Deep.Witnesses.w6_self_interruptor_skipped
  , `Effect4.Deep.withFiber_interruptAll
  , `Effect4.Deep.interruptEach_nil
  , `Effect4.Deep.interruptEach_cons
  , `Effect4.Deep.interruptEach_known
  , `Effect4.Deep.fireObserver_countdown_last
  , `Effect4.Deep.fireObserver_countdown_more
  , `Effect4.Deep.Witnesses.w5_await_all_children_awaits_only_new
  , `Effect4.Deep.Witnesses.w12_awaitAll_answers_the_exits
  , `Effect4.Deep.Witnesses.w6_runIn_closed_scope_uses_no_caller_annotations
  , `Effect4.Deep.fireObserver_untrackChild
  , `Effect4.Deep.exitFiber_children
  , `Effect4.Deep.exitInterruptChildren_finalizing
  , `Effect4.Deep.exitFiber_finalizing
  , `Effect4.Deep.withFiber_closeScope_unknown
  , `Effect4.Deep.Witnesses.w6_sequential_captures_and_merges
  , `Effect4.Deep.Witnesses.w6_parallel_forks_and_merges
  , `Effect4.Deep.evaluatePrim_async_immediate
  , `Effect4.Deep.evaluatePrim_async_parks
  ]

private def expectedRowTotal : Nat := 137
private def expectedDenominator : Nat := 135

/-! ## Checks -/

private def failJoin (detail : MessageData) : CommandElabM α :=
  throwError m!"runtime coverage mismatch: {detail}"

private def firstDuplicateString? : List String → Option String
  | [] => none
  | value :: values => if values.contains value then some value else firstDuplicateString? values

private def firstDuplicateName? : List Name → Option Name
  | [] => none
  | name :: names => if names.contains name then some name else firstDuplicateName? names

/-- Canonical kernel dependency text for one witness. A witness is a semantic
theorem, so it is bound by the semantic ceiling `propext`/`Quot.sound`; any
other axiom, `Classical.choice` included, fails here rather than being spelled
into a receipt. -/
private def canonicalAxiomText (name : Name) : CommandElabM String := do
  let actual := (← collectAxioms name).toList
  let unknown := actual.filter fun axiomName =>
    axiomName != ``propext && axiomName != ``Quot.sound
  unless unknown.isEmpty do
    failJoin m!"unexpected kernel axioms for witness {name}: {unknown}"
  let parts := [``propext, ``Quot.sound].filter actual.contains
  pure <| if parts.isEmpty then "none" else
    String.intercalate "," (parts.map fun n => n.toString)

private def checkRowShape : CommandElabM Unit := do
  if let some duplicate := firstDuplicateString? (censusRows.map Row.id) then
    failJoin m!"duplicate census row id: {duplicate}"
  unless censusRows.length == expectedRowTotal do
    failJoin m!"census row count drifted: {censusRows.length}, expected {expectedRowTotal}"
  for row in censusRows do
    unless knownKinds.contains row.kind do
      failJoin m!"row {row.id} has unknown kind {row.kind}"
    unless knownDispositions.contains row.disposition do
      failJoin m!"row {row.id} has a disposition outside the PORT-MANIFEST vocabulary: {row.disposition}"
    unless knownCoverage.contains row.coverage do
      failJoin m!"row {row.id} has unknown coverage {row.coverage}"
    if let some duplicate := firstDuplicateName? (row.witnesses.map Prod.fst) then
      failJoin m!"row {row.id} lists witness {duplicate} twice"
    let hasWitness := !row.witnesses.isEmpty
    if row.coverage == "absent" && hasWitness then
      failJoin m!"row {row.id} is declared absent but carries witnesses"
    if row.coverage != "absent" && !hasWitness then
      failJoin m!"row {row.id} is declared {row.coverage} but carries no witness"
    if row.disposition == "owned" && !hasWitness then
      failJoin m!"row {row.id} is owned and must carry at least one witness"
    if excludedDispositions.contains row.disposition && hasWitness then
      failJoin m!"row {row.id} is {row.disposition}, is outside the coverage denominator, and must carry no witness"

private def checkWitnesses : CommandElabM Unit := do
  let environment ← getEnv
  for row in censusRows do
    for (name, expectedAxioms) in row.witnesses do
      match environment.find? name with
      | none => failJoin m!"row {row.id}: missing witness declaration {name}"
      | some (.thmInfo _) => pure ()
      | some info =>
          let statementIsProp ← liftTermElabM <| Meta.isProp info.type
          let kind :=
            if statementIsProp then "a Prop-typed non-theorem declaration" else "not a theorem"
          failJoin m!"row {row.id}: witness {name} is {kind}; a witness must be a theorem"
      let actualAxioms ← canonicalAxiomText name
      unless actualAxioms == expectedAxioms do
        failJoin
          m!"row {row.id}: axiom receipt for {name}: expected {expectedAxioms}, found {actualAxioms}"

private def checkSnapshot : CommandElabM Unit := do
  if let some duplicate := firstDuplicateName? snapshotWitnesses then
    failJoin m!"statement snapshot lists {duplicate} twice"
  let used := censusRows.flatMap fun row => row.witnesses.map Prod.fst
  let missing := used.filter fun name => !snapshotWitnesses.contains name
  unless missing.isEmpty do
    failJoin m!"witnesses without a frozen statement snapshot: {missing}"
  let stale := snapshotWitnesses.filter fun name => !used.contains name
  unless stale.isEmpty do
    failJoin m!"statement snapshot entries that witness no census row: {stale}"

private def denominatorRows : List Row :=
  censusRows.filter fun row => !excludedDispositions.contains row.disposition

private def checkCoverageArithmetic : CommandElabM Unit := do
  unless denominatorRows.length == expectedDenominator do
    failJoin
      m!"coverage denominator drifted: {denominatorRows.length}, expected {expectedDenominator}"

private def checkRuntimeCoverage : CommandElabM Unit := do
  checkRowShape
  checkWitnesses
  checkSnapshot
  checkCoverageArithmetic
  let total := censusRows.length
  let denominator := denominatorRows.length
  let excluded := total - denominator
  let green := (denominatorRows.filter fun row => row.coverage == "green").length
  let partial_ := (denominatorRows.filter fun row => row.coverage == "partial").length
  let absent := (denominatorRows.filter fun row => row.coverage == "absent").length
  let ownedGreen :=
    (denominatorRows.filter fun row => row.disposition == "owned" && row.coverage == "green").length
  let partialIds := (denominatorRows.filter fun row => row.coverage == "partial").map Row.id
  let absentIds := (denominatorRows.filter fun row => row.coverage == "absent").map Row.id
  logInfo m!"Effect v4 runtime coverage: {total} census rows; {excluded} excluded by disposition; denominator {denominator}; owned-with-green {ownedGreen}/{denominator}; green {green}, partial {partial_}, absent {absent}"
  logInfo m!"partial rows: {partialIds}"
  logInfo m!"absent rows: {absentIds}"

private def emitRuntimeCoverage : CommandElabM Unit := do
  checkRuntimeCoverage
  for row in censusRows do
    liftIO <| IO.println
      s!"E4RTCOV\trow\t{row.id}\t{row.kind}\t{row.disposition}\t{row.coverage}\t{row.witnesses.length}"
  for row in censusRows do
    for (name, _) in row.witnesses do
      let actual ← canonicalAxiomText name
      liftIO <| IO.println s!"E4RTCOV\twitness\t{row.id}\t{name}\t{actual}"
  for name in snapshotWitnesses do
    liftIO <| IO.println s!"E4RTCOV\tsnapshot\t{name}"
  let denominator := denominatorRows.length
  let green := (denominatorRows.filter fun row => row.coverage == "green").length
  let partial_ := (denominatorRows.filter fun row => row.coverage == "partial").length
  let absent := (denominatorRows.filter fun row => row.coverage == "absent").length
  let ownedGreen :=
    (denominatorRows.filter fun row => row.disposition == "owned" && row.coverage == "green").length
  liftIO <| IO.println
    s!"E4RTCOV\tcoverage\t{censusRows.length}\t{denominator}\t{ownedGreen}\t{green}\t{partial_}\t{absent}"

syntax (name := effect4CheckRuntimeCoverage)
  "#effect4_check_runtime_coverage" : command

syntax (name := effect4EmitRuntimeCoverage)
  "#effect4_emit_runtime_coverage" : command

elab_rules : command
  | `(#effect4_check_runtime_coverage) => checkRuntimeCoverage

elab_rules : command
  | `(#effect4_emit_runtime_coverage) => emitRuntimeCoverage

#effect4_check_runtime_coverage
#effect4_emit_runtime_coverage

end Effect4Test.Audit.RuntimeCoverage
