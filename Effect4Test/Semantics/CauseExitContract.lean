/-
Contract packet: `test/contracts/cause-exit.contract.md`

Breaker-owned red battery. The implementation phase must not edit this file.
It is red until `Effect4/Semantics/Cause.lean` and `Effect4/Semantics/Exit.lean`
declare the frozen surface.

Every public declaration is frozen by an exact `#check (@name : proposition)`
ascription so no weaker statement satisfies this contract.
-/

import Effect4.Semantics.Cause
import Effect4.Semantics.Exit

set_option autoImplicit false

namespace Effect4
end Effect4

namespace Effect4Test.Semantics.CauseExitContract

open Effect4

universe u

section AnnotationSurface

/-! A1: the finite per-reason annotation map (census: cause.annotations). -/

#check (@ReasonAnnotations : Type u -> Type u)
#check (@ReasonAnnotations.mk : forall {α : Type u} (entries : List (String × α)),
  (entries.map Prod.fst).Nodup -> ReasonAnnotations α)
#check (@ReasonAnnotations.entries :
  forall {α : Type u}, ReasonAnnotations α -> List (String × α))
#check (@ReasonAnnotations.keysNodup : forall {α : Type u} (self : ReasonAnnotations α),
  (self.entries.map Prod.fst).Nodup)

example {α : Type u} [DecidableEq α] : DecidableEq (ReasonAnnotations α) :=
  inferInstance

#check (@ReasonAnnotations.empty : forall {α : Type u}, ReasonAnnotations α)
#check (@ReasonAnnotations.keys : forall {α : Type u}, ReasonAnnotations α -> List String)
#check (@ReasonAnnotations.lookup :
  forall {α : Type u}, ReasonAnnotations α -> String -> Option α)
#check (@ReasonAnnotations.annotate :
  forall {α : Type u}, ReasonAnnotations α -> ReasonAnnotations α -> Bool -> ReasonAnnotations α)

#check (@ReasonAnnotations.keys_eq : forall {α : Type u} (self : ReasonAnnotations α),
  self.keys = self.entries.map Prod.fst)
#check (@ReasonAnnotations.keys_nodup : forall {α : Type u} (self : ReasonAnnotations α),
  self.keys.Nodup)
#check (@ReasonAnnotations.lookup_eq :
  forall {α : Type u} (self : ReasonAnnotations α) (key : String),
    self.lookup key =
      (self.entries.find? (fun entry => decide (entry.fst = key))).map Prod.snd)
#check (@ReasonAnnotations.ext : forall {α : Type u} {left right : ReasonAnnotations α},
  left.entries = right.entries -> left = right)
#check (@ReasonAnnotations.empty_entries : forall {α : Type u},
  (ReasonAnnotations.empty : ReasonAnnotations α).entries = [])
#check (@ReasonAnnotations.lookup_empty : forall {α : Type u} (key : String),
  (ReasonAnnotations.empty : ReasonAnnotations α).lookup key = none)

/-! The exact merge shape: kept position, in-place overwrite, appended tail. -/
#check (@ReasonAnnotations.annotate_entries :
  forall {α : Type u} (self extra : ReasonAnnotations α) (overwrite : Bool),
    (self.annotate extra overwrite).entries =
      self.entries.map (fun entry =>
        if overwrite = true then
          match extra.lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) ++
      extra.entries.filter (fun entry => decide (entry.fst ∉ self.keys)))
#check (@ReasonAnnotations.annotate_empty :
  forall {α : Type u} (self : ReasonAnnotations α) (overwrite : Bool),
    self.annotate ReasonAnnotations.empty overwrite = self)
#check (@ReasonAnnotations.annotate_keys :
  forall {α : Type u} (self extra : ReasonAnnotations α) (overwrite : Bool),
    (self.annotate extra overwrite).keys =
      self.keys ++ extra.keys.filter (fun key => decide (key ∉ self.keys)))
#check (@ReasonAnnotations.lookup_annotate_kept :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α),
    self.lookup key = some value ->
    (self.annotate extra false).lookup key = some value)
#check (@ReasonAnnotations.lookup_annotate_new :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α)
    (overwrite : Bool),
    self.lookup key = none -> extra.lookup key = some value ->
    (self.annotate extra overwrite).lookup key = some value)
#check (@ReasonAnnotations.lookup_annotate_overwrite :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String) (value : α),
    extra.lookup key = some value ->
    (self.annotate extra true).lookup key = some value)
#check (@ReasonAnnotations.lookup_annotate_absent :
  forall {α : Type u} (self extra : ReasonAnnotations α) (key : String)
    (overwrite : Bool),
    self.lookup key = none -> extra.lookup key = none ->
    (self.annotate extra overwrite).lookup key = none)

/-! Insertion order is retained, so annotation equality is not extensional. -/
#check (@ReasonAnnotations.order_retained :
  exists left right : ReasonAnnotations Nat,
    (forall key : String, left.lookup key = right.lookup key) /\ left ≠ right)

/-! The WeakMap host-identity memory is refused, not modelled. -/
#check (@Reason.host_memory_refused :
  forall {ε α : Type u} (recall : ε -> ReasonAnnotations α) (left right : ε),
    left = right -> recall left = recall right)

end AnnotationSurface

section ReasonSurface

/-! A2: the closed three-value reason alphabet (census: exit.reason-alphabet). -/

#check (@ReasonTag : Type)
#check (@ReasonTag.fail : ReasonTag)
#check (@ReasonTag.die : ReasonTag)
#check (@ReasonTag.interrupt : ReasonTag)
#check (@ReasonTag.all : List ReasonTag)
#synth DecidableEq ReasonTag
#synth Repr ReasonTag

#check (@ReasonTag.all_nodup : ReasonTag.all.Nodup)
#check (@ReasonTag.mem_all : forall tag : ReasonTag, tag ∈ ReasonTag.all)
#check (@ReasonTag.cases_receipt : forall tag : ReasonTag,
  tag = ReasonTag.fail \/ tag = ReasonTag.die \/ tag = ReasonTag.interrupt)

/-! A3: reasons carry payload and annotations, and nothing else. -/

#check (@Reason : Type u -> Type u -> Type u -> Type u -> Type u)
#check (@Reason.fail : forall {ε δ ι α : Type u},
  ε -> ReasonAnnotations α -> Reason ε δ ι α)
#check (@Reason.die : forall {ε δ ι α : Type u},
  δ -> ReasonAnnotations α -> Reason ε δ ι α)
#check (@Reason.interrupt : forall {ε δ ι α : Type u},
  Option ι -> ReasonAnnotations α -> Reason ε δ ι α)

example {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] : DecidableEq (Reason ε δ ι α) :=
  inferInstance

#check (@Reason.tag :
  forall {ε δ ι α : Type u}, Reason ε δ ι α -> ReasonTag)
#check (@Reason.annotations :
  forall {ε δ ι α : Type u}, Reason ε δ ι α -> ReasonAnnotations α)
#check (@Reason.error? :
  forall {ε δ ι α : Type u}, Reason ε δ ι α -> Option ε)
#check (@Reason.defect? :
  forall {ε δ ι α : Type u}, Reason ε δ ι α -> Option δ)
#check (@Reason.annotate :
  forall {ε δ ι α : Type u},
    Reason ε δ ι α -> ReasonAnnotations α -> Bool -> Reason ε δ ι α)

#check (@Reason.tag_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).tag = ReasonTag.fail)
#check (@Reason.tag_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).tag = ReasonTag.die)
#check (@Reason.tag_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι) (annotations : ReasonAnnotations α),
  (Reason.interrupt interruptor annotations : Reason ε δ ι α).tag =
    ReasonTag.interrupt)

#check (@Reason.annotations_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).annotations = annotations)
#check (@Reason.annotations_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).annotations = annotations)
#check (@Reason.annotations_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι) (annotations : ReasonAnnotations α),
  (Reason.interrupt interruptor annotations : Reason ε δ ι α).annotations =
    annotations)

#check (@Reason.error_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).error? = some error)
#check (@Reason.error_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).error? = none)
#check (@Reason.error_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι) (annotations : ReasonAnnotations α),
  (Reason.interrupt interruptor annotations : Reason ε δ ι α).error? = none)

#check (@Reason.defect_fail : forall {ε δ ι α : Type u} (error : ε)
  (annotations : ReasonAnnotations α),
  (Reason.fail error annotations : Reason ε δ ι α).defect? = none)
#check (@Reason.defect_die : forall {ε δ ι α : Type u} (defect : δ)
  (annotations : ReasonAnnotations α),
  (Reason.die defect annotations : Reason ε δ ι α).defect? = some defect)
#check (@Reason.defect_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι) (annotations : ReasonAnnotations α),
  (Reason.interrupt interruptor annotations : Reason ε δ ι α).defect? = none)

/-! Reason equality compares tag, payload, and annotations. -/
#check (@Reason.fail_inj : forall {ε δ ι α : Type u} (leftError rightError : ε)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.fail leftError leftAnnotations : Reason ε δ ι α) =
      Reason.fail rightError rightAnnotations <->
    leftError = rightError /\ leftAnnotations = rightAnnotations)
#check (@Reason.die_inj : forall {ε δ ι α : Type u} (leftDefect rightDefect : δ)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.die leftDefect leftAnnotations : Reason ε δ ι α) =
      Reason.die rightDefect rightAnnotations <->
    leftDefect = rightDefect /\ leftAnnotations = rightAnnotations)
#check (@Reason.interrupt_inj : forall {ε δ ι α : Type u}
  (leftInterruptor rightInterruptor : Option ι)
  (leftAnnotations rightAnnotations : ReasonAnnotations α),
  (Reason.interrupt leftInterruptor leftAnnotations : Reason ε δ ι α) =
      Reason.interrupt rightInterruptor rightAnnotations <->
    leftInterruptor = rightInterruptor /\
      leftAnnotations = rightAnnotations)

#check (@Reason.cases_receipt : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α),
  (exists error annotations, reason = Reason.fail error annotations) \/
  (exists defect annotations, reason = Reason.die defect annotations) \/
  (exists interruptor annotations,
    reason = Reason.interrupt interruptor annotations))
#check (@Reason.tag_mem_all : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α), reason.tag ∈ ReasonTag.all)

#check (@Reason.annotate_tag : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α) (extra : ReasonAnnotations α) (overwrite : Bool),
  (reason.annotate extra overwrite).tag = reason.tag)
#check (@Reason.annotate_annotations : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α) (extra : ReasonAnnotations α) (overwrite : Bool),
  (reason.annotate extra overwrite).annotations =
    reason.annotations.annotate extra overwrite)

end ReasonSurface

section CauseSurface

/-! A4: a cause is exactly an ordered reason list (census: cause.flat-reasons,
rule.cause-has-no-structure). -/

#check (@Cause : Type u -> Type u -> Type u -> Type u -> Type u)
#check (@Cause.mk : forall {ε δ ι α : Type u},
  List (Reason ε δ ι α) -> Cause ε δ ι α)
#check (@Cause.reasons : forall {ε δ ι α : Type u},
  Cause ε δ ι α -> List (Reason ε δ ι α))

example {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] : DecidableEq (Cause ε δ ι α) :=
  inferInstance

#check (@Cause.empty : forall {ε δ ι α : Type u}, Cause ε δ ι α)
#check (@Cause.fail : forall {ε δ ι α : Type u}, ε -> Cause ε δ ι α)
#check (@Cause.die : forall {ε δ ι α : Type u}, δ -> Cause ε δ ι α)
#check (@Cause.interrupt :
  forall {ε δ ι α : Type u}, Option ι -> Cause ε δ ι α)
#check (@Cause.annotate : forall {ε δ ι α : Type u},
  Cause ε δ ι α -> ReasonAnnotations α -> Bool -> Cause ε δ ι α)

#check (@Cause.ext : forall {ε δ ι α : Type u} {left right : Cause ε δ ι α},
  left.reasons = right.reasons -> left = right)
#check (@Cause.eq_iff : forall {ε δ ι α : Type u} (left right : Cause ε δ ι α),
  left = right <-> left.reasons = right.reasons)
/-! rc.112 `CauseImpl` equality: same length and pairwise-equal ordered reasons. -/
#check (@Cause.eq_iff_pointwise :
  forall {ε δ ι α : Type u} (left right : Cause ε δ ι α),
    left = right <->
      (left.reasons.length = right.reasons.length /\
        forall index : Nat, left.reasons[index]? = right.reasons[index]?))

#check (@Cause.empty_reasons : forall {ε δ ι α : Type u},
  (Cause.empty : Cause ε δ ι α).reasons = [])
#check (@Cause.fail_reasons : forall {ε δ ι α : Type u} (error : ε),
  (Cause.fail error : Cause ε δ ι α).reasons =
    [Reason.fail error ReasonAnnotations.empty])
#check (@Cause.die_reasons : forall {ε δ ι α : Type u} (defect : δ),
  (Cause.die defect : Cause ε δ ι α).reasons =
    [Reason.die defect ReasonAnnotations.empty])
#check (@Cause.interrupt_reasons : forall {ε δ ι α : Type u}
  (interruptor : Option ι),
  (Cause.interrupt interruptor : Cause ε δ ι α).reasons =
    [Reason.interrupt interruptor ReasonAnnotations.empty])
#check (@Cause.annotate_reasons : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (extra : ReasonAnnotations α) (overwrite : Bool),
  (self.annotate extra overwrite).reasons =
    self.reasons.map (fun reason => reason.annotate extra overwrite))

/-! A5: first-occurrence deduplication, the `Arr.union` kernel. -/

#check (@Cause.dedup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α],
  List (Reason ε δ ι α) -> List (Reason ε δ ι α))

#check (@Cause.dedup_nil : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α],
  Cause.dedup ([] : List (Reason ε δ ι α)) = [])
#check (@Cause.dedup_cons : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (rest : List (Reason ε δ ι α)),
  Cause.dedup (reason :: rest) =
    reason :: (Cause.dedup rest).filter (fun other => decide (other ≠ reason)))
#check (@Cause.mem_dedup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (list : List (Reason ε δ ι α)),
  reason ∈ Cause.dedup list <-> reason ∈ list)
#check (@Cause.dedup_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (list : List (Reason ε δ ι α)), (Cause.dedup list).Nodup)
#check (@Cause.dedup_of_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (list : List (Reason ε δ ι α)), list.Nodup -> Cause.dedup list = list)

/-! A6: `causeCombine` (census: cause.combine-union,
rule.cause-has-no-structure). -/

#check (@Cause.combine : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α],
  Cause ε δ ι α -> Cause ε δ ι α -> Cause ε δ ι α)

#check (@Cause.combine_empty_left : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (that : Cause ε δ ι α),
  Cause.combine Cause.empty that = that)
#check (@Cause.combine_empty_right : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α),
  Cause.combine self Cause.empty = self)
/-! The definition-level union law for two nonempty causes. -/
#check (@Cause.combine_reasons : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons ≠ [] -> that.reasons ≠ [] ->
  (Cause.combine self that).reasons =
    Cause.dedup (self.reasons ++ that.reasons))
#check (@Cause.mem_combine : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (self that : Cause ε δ ι α),
  reason ∈ (Cause.combine self that).reasons <->
    reason ∈ self.reasons \/ reason ∈ that.reasons)
/-! No sequential or parallel node: combine introduces no new reason. -/
#check (@Cause.combine_no_new_reason : forall {ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (reason : Reason ε δ ι α) (self that : Cause ε δ ι α),
  reason ∈ (Cause.combine self that).reasons ->
    reason ∈ self.reasons \/ reason ∈ that.reasons)
/-! `Arr.union` order: `self`, then the elements of `that` not already present. -/
#check (@Cause.combine_order : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons.Nodup -> that.reasons.Nodup ->
  (Cause.combine self that).reasons =
    self.reasons ++
      that.reasons.filter (fun reason => decide (reason ∉ self.reasons)))
#check (@Cause.combine_nodup : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (self that : Cause ε δ ι α),
  self.reasons.Nodup -> that.reasons.Nodup ->
  (Cause.combine self that).reasons.Nodup)
/-! The structural-equality short circuit. -/
#check (@Cause.combine_self : forall {ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α),
  self.reasons.Nodup -> Cause.combine self self = self)

end CauseSurface

section SquashSurface

/-! A7: `causeSquash` has four arms (census: cause.squash). -/

#check (@Squashed : Type u -> Type u -> Type u)
#check (@Squashed.error : forall {ε δ : Type u}, ε -> Squashed ε δ)
#check (@Squashed.defect : forall {ε δ : Type u}, δ -> Squashed ε δ)
#check (@Squashed.interruptedWithoutError : forall {ε δ : Type u}, Squashed ε δ)
#check (@Squashed.emptyCause : forall {ε δ : Type u}, Squashed ε δ)

example {ε δ : Type u} [DecidableEq ε] [DecidableEq δ] :
    DecidableEq (Squashed ε δ) :=
  inferInstance

#check (@Squashed.cases_receipt : forall {ε δ : Type u} (squashed : Squashed ε δ),
  (exists error, squashed = Squashed.error error) \/
  (exists defect, squashed = Squashed.defect defect) \/
  squashed = Squashed.interruptedWithoutError \/
  squashed = Squashed.emptyCause)

#check (@Cause.squash :
  forall {ε δ ι α : Type u}, Cause ε δ ι α -> Squashed ε δ)

/-! Arm one: the first `Fail` error in reason order. -/
#check (@Cause.squash_error : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (error : ε) (rest : List ε),
  self.reasons.filterMap Reason.error? = error :: rest ->
    self.squash = Squashed.error error)
/-! Arm two: with no `Fail`, the first `Die` defect in reason order. -/
#check (@Cause.squash_defect : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α) (defect : δ) (rest : List δ),
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = defect :: rest ->
    self.squash = Squashed.defect defect)
/-! Arm three: "All fibers interrupted without error". -/
#check (@Cause.squash_interrupted : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α),
  self.reasons.filterMap Reason.error? = [] ->
  self.reasons.filterMap Reason.defect? = [] ->
  self.reasons ≠ [] ->
    self.squash = Squashed.interruptedWithoutError)
/-! Arm four: "Empty cause". -/
#check (@Cause.squash_empty : forall {ε δ ι α : Type u},
  (Cause.empty : Cause ε δ ι α).squash = Squashed.emptyCause)
#check (@Cause.squash_emptyCause_iff : forall {ε δ ι α : Type u}
  (self : Cause ε δ ι α),
  self.squash = Squashed.emptyCause <-> self.reasons = [])

#check (@Cause.squash_fail : forall {ε δ ι α : Type u} (error : ε),
  (Cause.fail error : Cause ε δ ι α).squash = Squashed.error error)
#check (@Cause.squash_die : forall {ε δ ι α : Type u} (defect : δ),
  (Cause.die defect : Cause ε δ ι α).squash = Squashed.defect defect)
#check (@Cause.squash_interrupt : forall {ε δ ι α : Type u}
  (interruptor : Option ι),
  (Cause.interrupt interruptor : Cause ε δ ι α).squash =
    Squashed.interruptedWithoutError)
/-! First-occurrence order: a later `Fail` still beats an earlier `Die`. -/
#check (@Cause.squash_fail_over_die : forall {ε δ ι α : Type u} (error : ε)
  (defect : δ) (dieAnnotations failAnnotations : ReasonAnnotations α),
  (Cause.mk [Reason.die defect dieAnnotations,
      Reason.fail error failAnnotations] : Cause ε δ ι α).squash =
    Squashed.error error)

end SquashSurface

section ExitSurface

/-! A8: exits (census: exit.success-failure, cause.finalizer-merge,
scope.exit-as-void-all). -/

#check (@Exit : Type u -> Type u -> Type u -> Type u -> Type u -> Type u)
#check (@Exit.success : forall {β ε δ ι α : Type u}, β -> Exit β ε δ ι α)
#check (@Exit.failure :
  forall {β ε δ ι α : Type u}, Cause ε δ ι α -> Exit β ε δ ι α)

example {β ε δ ι α : Type u} [DecidableEq β] [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] : DecidableEq (Exit β ε δ ι α) :=
  inferInstance

#check (@Exit.void : forall {ε δ ι α : Type u}, Exit Unit ε δ ι α)
#check (@Exit.isSuccess : forall {β ε δ ι α : Type u}, Exit β ε δ ι α -> Bool)
#check (@Exit.cause? :
  forall {β ε δ ι α : Type u}, Exit β ε δ ι α -> Option (Cause ε δ ι α))
#check (@Exit.causeReasons :
  forall {β ε δ ι α : Type u}, Exit β ε δ ι α -> List (Reason ε δ ι α))
#check (@Exit.mergeFinalizer : forall {β ε δ ι α : Type u} [DecidableEq ε]
  [DecidableEq δ] [DecidableEq ι] [DecidableEq α],
  Exit β ε δ ι α -> Exit Unit ε δ ι α -> Exit Unit ε δ ι α)
#check (@Exit.restoreAfterFinalizer : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α],
  Exit β ε δ ι α -> Exit Unit ε δ ι α -> Exit β ε δ ι α)
#check (@Exit.asVoidAll : forall {β ε δ ι α : Type u},
  List (Exit β ε δ ι α) -> Exit Unit ε δ ι α)

#check (@Exit.cases_receipt : forall {β ε δ ι α : Type u}
  (self : Exit β ε δ ι α),
  (exists value, self = Exit.success value) \/
  (exists cause, self = Exit.failure cause))
#check (@Exit.success_ne_failure : forall {β ε δ ι α : Type u} (value : β)
  (cause : Cause ε δ ι α),
  (Exit.success value : Exit β ε δ ι α) ≠ Exit.failure cause)
#check (@Exit.success_inj : forall {β ε δ ι α : Type u} (left right : β),
  (Exit.success left : Exit β ε δ ι α) = Exit.success right <-> left = right)
#check (@Exit.failure_inj : forall {β ε δ ι α : Type u}
  (left right : Cause ε δ ι α),
  (Exit.failure left : Exit β ε δ ι α) = Exit.failure right <-> left = right)
#check (@Exit.void_eq : forall {ε δ ι α : Type u},
  (Exit.void : Exit Unit ε δ ι α) = Exit.success ())

#check (@Exit.isSuccess_success : forall {β ε δ ι α : Type u} (value : β),
  (Exit.success value : Exit β ε δ ι α).isSuccess = true)
#check (@Exit.isSuccess_failure : forall {β ε δ ι α : Type u}
  (cause : Cause ε δ ι α),
  (Exit.failure cause : Exit β ε δ ι α).isSuccess = false)
#check (@Exit.cause_success : forall {β ε δ ι α : Type u} (value : β),
  (Exit.success value : Exit β ε δ ι α).cause? = none)
#check (@Exit.cause_failure : forall {β ε δ ι α : Type u}
  (cause : Cause ε δ ι α),
  (Exit.failure cause : Exit β ε δ ι α).cause? = some cause)
#check (@Exit.causeReasons_success : forall {β ε δ ι α : Type u} (value : β),
  (Exit.success value : Exit β ε δ ι α).causeReasons = [])
#check (@Exit.causeReasons_failure : forall {β ε δ ι α : Type u}
  (cause : Cause ε δ ι α),
  (Exit.failure cause : Exit β ε δ ι α).causeReasons = cause.reasons)

/-! `combineFinalizerCause`, exactly as pinned at internal/effect.ts:3800-3804. -/

#check (@Exit.mergeFinalizer_success : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (value : β) (finalizer : Exit Unit ε δ ι α),
  Exit.mergeFinalizer (Exit.success value) finalizer = finalizer)
/-! Under a successful exit the finalizer failure stands alone. -/
#check (@Exit.mergeFinalizer_success_failure : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (value : β) (finalizerCause : Cause ε δ ι α),
  Exit.mergeFinalizer (Exit.success value) (Exit.failure finalizerCause) =
    Exit.failure finalizerCause)
/-! `catchCause` does not intercept a successful finalizer. -/
#check (@Exit.mergeFinalizer_failure_success : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (cause : Cause ε δ ι α) (value : Unit),
  Exit.mergeFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.success value) =
    Exit.success value)
/-! A finalizer failure under a failed exit is merged by `causeCombine`. -/
#check (@Exit.mergeFinalizer_failure_failure : forall {β ε δ ι α : Type u}
  [DecidableEq ε] [DecidableEq δ] [DecidableEq ι] [DecidableEq α]
  (cause finalizerCause : Cause ε δ ι α),
  Exit.mergeFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause))

/-! The caller-side restore at internal/effect.ts:4023-4028. -/

#check (@Exit.restoreAfterFinalizer_success_finalizer :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (self : Exit β ε δ ι α) (value : Unit),
  Exit.restoreAfterFinalizer self (Exit.success value) = self)
#check (@Exit.restoreAfterFinalizer_failure_failure :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (cause finalizerCause : Cause ε δ ι α),
  Exit.restoreAfterFinalizer (Exit.failure cause : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure (Cause.combine cause finalizerCause))
#check (@Exit.restoreAfterFinalizer_success_failure :
  forall {β ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (value : β) (finalizerCause : Cause ε δ ι α),
  Exit.restoreAfterFinalizer (Exit.success value : Exit β ε δ ι α)
      (Exit.failure finalizerCause) =
    Exit.failure finalizerCause)

/-! `exitAsVoidAll`, exactly as pinned at internal/effect.ts:2024-2038. -/

/-! The exact concatenation order: failed exits' reasons, in list order. -/
#check (@Exit.asVoidAll_reasons : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)),
  (Exit.asVoidAll exits).causeReasons = exits.flatMap Exit.causeReasons)
#check (@Exit.asVoidAll_nil : forall {β ε δ ι α : Type u},
  Exit.asVoidAll ([] : List (Exit β ε δ ι α)) = Exit.success ())
#check (@Exit.asVoidAll_all_success : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)),
  (forall exit, exit ∈ exits -> exists value, exit = Exit.success value) ->
    Exit.asVoidAll exits = Exit.success ())
#check (@Exit.asVoidAll_failure : forall {β ε δ ι α : Type u}
  (exits : List (Exit β ε δ ι α)) (reason : Reason ε δ ι α)
  (rest : List (Reason ε δ ι α)),
  exits.flatMap Exit.causeReasons = reason :: rest ->
    Exit.asVoidAll exits = Exit.failure (Cause.mk (reason :: rest)))
/-! A failed exit with an empty cause contributes nothing, so the join succeeds. -/
#check (@Exit.asVoidAll_empty_cause : forall {ε δ ι α : Type u},
  Exit.asVoidAll [(Exit.failure Cause.empty : Exit Unit ε δ ι α)] =
    Exit.success ())
/-! `exitAsVoidAll` concatenates; unlike `causeCombine` it does not deduplicate. -/
#check (@Exit.asVoidAll_keeps_duplicates : forall {ε δ ι α : Type u}
  (reason : Reason ε δ ι α),
  Exit.asVoidAll
      [(Exit.failure (Cause.mk [reason]) : Exit Unit ε δ ι α),
        Exit.failure (Cause.mk [reason])] =
    Exit.failure (Cause.mk [reason, reason]))

end ExitSurface

section GroundChecks

/-! Small executable checks over closed alphabets. They are finite probes, not
laws; each law above is separately frozen. -/

abbrev Err := Nat
abbrev Defect := Bool
abbrev Interruptor := Nat
abbrev Ann := Nat

abbrev GroundReason := Reason Err Defect Interruptor Ann
abbrev GroundCause := Cause Err Defect Interruptor Ann
abbrev GroundExit := Exit Unit Err Defect Interruptor Ann

def firstFail : GroundReason := Reason.fail 1 ReasonAnnotations.empty
def secondFail : GroundReason := Reason.fail 2 ReasonAnnotations.empty
def someDie : GroundReason := Reason.die true ReasonAnnotations.empty

def leftCause : GroundCause := Cause.mk [firstFail]
def rightCause : GroundCause := Cause.mk [secondFail]

/-! Combine deduplicates rather than appending. -/
example :
    Cause.combine leftCause (Cause.mk [firstFail, secondFail]) =
      Cause.mk [firstFail, secondFail] := by
  decide

/-! Combine is idempotent on a duplicate-free cause. -/
example : Cause.combine leftCause leftCause = leftCause := by
  decide

/-! Combine retains operand order, so it is not commutative. -/
example : Cause.combine leftCause rightCause ≠
    Cause.combine rightCause leftCause := by
  decide

/-! An earlier `Die` does not beat a later `Fail`. -/
example : (Cause.mk [someDie, firstFail] : GroundCause).squash =
    Squashed.error 1 := by
  decide

/-! A failed exit carrying an empty cause joins to success. -/
example :
    Exit.asVoidAll [(Exit.failure Cause.empty : GroundExit)] =
      Exit.success () := by
  decide

/-! The join concatenates and keeps duplicates. -/
example :
    Exit.asVoidAll
        [(Exit.failure (Cause.mk [firstFail]) : GroundExit),
          Exit.failure (Cause.mk [firstFail])] =
      Exit.failure (Cause.mk [firstFail, firstFail]) := by
  decide

/-! A finalizer failure under a successful exit stands alone. -/
example :
    Exit.mergeFinalizer (Exit.success () : GroundExit)
        (Exit.failure rightCause) =
      Exit.failure rightCause := by
  decide

/-! A finalizer failure under a failed exit is unioned into the exit cause. -/
example :
    Exit.mergeFinalizer (Exit.failure leftCause : GroundExit)
        (Exit.failure rightCause) =
      Exit.failure (Cause.mk [firstFail, secondFail]) := by
  decide

def keptAnnotations : ReasonAnnotations Ann :=
  ReasonAnnotations.mk [("effect/Cause/StackTrace", 1)] (by decide)

def replacementAnnotations : ReasonAnnotations Ann :=
  ReasonAnnotations.mk [("effect/Cause/StackTrace", 2)] (by decide)

/-! `annotate` never overwrites an existing key unless asked. -/
example :
    (keptAnnotations.annotate replacementAnnotations false).lookup
        "effect/Cause/StackTrace" = some 1 := by
  decide

/-! With `overwrite := true` the new value replaces the old one in place. -/
example :
    (keptAnnotations.annotate replacementAnnotations true).entries =
      [("effect/Cause/StackTrace", 2)] := by
  decide

/-! Annotating with the empty map is the identity. -/
example : keptAnnotations.annotate ReasonAnnotations.empty true = keptAnnotations := by
  decide

end GroundChecks

section AxiomReceipts

#print axioms Effect4.ReasonAnnotations.keys_eq
#print axioms Effect4.ReasonAnnotations.annotate_entries
#print axioms Effect4.ReasonAnnotations.lookup_annotate_kept
#print axioms Effect4.ReasonAnnotations.order_retained
#print axioms Effect4.Reason.host_memory_refused
#print axioms Effect4.Reason.cases_receipt
#print axioms Effect4.Cause.eq_iff_pointwise
#print axioms Effect4.Cause.combine_order
#print axioms Effect4.Cause.combine_self
#print axioms Effect4.Cause.squash_error
#print axioms Effect4.Cause.squash_emptyCause_iff
#print axioms Effect4.Exit.mergeFinalizer_failure_failure
#print axioms Effect4.Exit.asVoidAll_reasons

end AxiomReceipts

end Effect4Test.Semantics.CauseExitContract
