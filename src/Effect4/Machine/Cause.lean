import Std

/-!
# Semantics.Cause.lean

Owner: Typed failure, defect, and interruption causes.

This module freezes the first-order `Cause` model of `effect@4.0.0-rc.112` as
data over four opaque alphabets: the typed error, the defect, the interruptor
identity, and the annotation value. It declares the per-reason annotation map,
the closed `Fail`/`Die`/`Interrupt` reason alphabet, the flat reason list that
is a cause, first-occurrence deduplication, `causeCombine`, and the four-armed
`causeSquash` projection. Nothing above `Semantics` in
`docs/ARCHITECTURE.md` is imported.

Pinned source: `vendor/effect-4.0.0-rc.112/src/internal/core.ts` 137-319 and
`internal/effect.ts` 241-258, 298-309. The frozen surface is
`Test/contracts/cause-exit.contract.md`, held by the battery
`Test/Machine/Semantics/CauseExitContract.lean` and the axiom report
`Test/Machine/Semantics/CauseExitAxiomReport.lean`.
-/

namespace Effect4

universe u

/-- Insertion-ordered per-reason annotation map with unique keys. -/
structure ReasonAnnotations (α : Type u) where
  /-- Stored key and value pairs, in insertion order. -/
  entries : List (String × α)
  /-- The only admission boundary: a duplicate key is unconstructible. -/
  keysNodup : (entries.map Prod.fst).Nodup
deriving DecidableEq

namespace ReasonAnnotations

/-- Two annotation maps agreeing on their entries are equal. census: cause.annotations -/
theorem ext {α : Type u} {left right : ReasonAnnotations α}
    (h : left.entries = right.entries) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- The empty annotation map, rc.112's `constEmptyAnnotations`. -/
def empty {α : Type u} : ReasonAnnotations α where
  entries := []
  keysNodup := List.nodup_nil

/-- The stored keys, in insertion order. -/
def keys {α : Type u} (self : ReasonAnnotations α) : List String :=
  self.entries.map Prod.fst

/-- Read the value stored under a key, if any. -/
def lookup {α : Type u} (self : ReasonAnnotations α) (key : String) : Option α :=
  (self.entries.find? (fun entry => decide (entry.fst = key))).map Prod.snd

/-- Keys are the first components of the entries. census: cause.annotations -/
theorem keys_eq {α : Type u} (self : ReasonAnnotations α) :
    self.keys = self.entries.map Prod.fst := rfl

/-- Stored keys are duplicate-free. census: cause.annotations -/
theorem keys_nodup {α : Type u} (self : ReasonAnnotations α) : self.keys.Nodup :=
  self.keysNodup

/-- Lookup is the first matching entry's value. census: cause.annotations -/
theorem lookup_eq {α : Type u} (self : ReasonAnnotations α) (key : String) :
    self.lookup key =
      (self.entries.find? (fun entry => decide (entry.fst = key))).map Prod.snd := rfl

/-- The empty map stores no entry. census: cause.annotations -/
theorem empty_entries {α : Type u} :
    (empty : ReasonAnnotations α).entries = [] := rfl

/-- The empty map answers every key with `none`. census: cause.annotations -/
theorem lookup_empty {α : Type u} (key : String) :
    (empty : ReasonAnnotations α).lookup key = none := rfl

/-- The merged entry list of `annotate`: kept slots, then the new keys. -/
private def annotateEntries {α : Type u} (self extra : ReasonAnnotations α)
    (overwrite : Bool) : List (String × α) :=
  self.entries.map (fun entry =>
    if overwrite = true then
      match extra.lookup entry.fst with
      | some value => (entry.fst, value)
      | none => entry
    else entry) ++
  extra.entries.filter (fun entry => decide (entry.fst ∉ self.keys))

private theorem map_fst_annotate {α : Type u} (entries : List (String × α))
    (extra : ReasonAnnotations α) (overwrite : Bool) :
    (entries.map (fun entry =>
        if overwrite = true then
          match extra.lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry)).map Prod.fst = entries.map Prod.fst := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    rw [List.map_cons, List.map_cons, List.map_cons, ih]
    congr 1
    by_cases hov : overwrite = true
    · rw [if_pos hov]
      split <;> rfl
    · rw [if_neg hov]

private theorem map_fst_filter {α : Type u} (entries : List (String × α))
    (keys : List String) :
    (entries.filter (fun entry => decide (entry.fst ∉ keys))).map Prod.fst =
      (entries.map Prod.fst).filter (fun key => decide (key ∉ keys)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    by_cases hkeep : head.fst ∈ keys
    · rw [List.filter_cons_of_neg
          (by simp only [decide_eq_true_eq]; exact fun contra => contra hkeep),
        List.map_cons,
        List.filter_cons_of_neg
          (by simp only [decide_eq_true_eq]; exact fun contra => contra hkeep),
        ih]
    · rw [List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hkeep),
        List.map_cons, List.map_cons,
        List.filter_cons_of_pos (by simp only [decide_eq_true_eq]; exact hkeep),
        ih]

private theorem annotateEntries_keys {α : Type u} (self extra : ReasonAnnotations α)
    (overwrite : Bool) :
    (annotateEntries self extra overwrite).map Prod.fst =
      self.keys ++ extra.keys.filter (fun key => decide (key ∉ self.keys)) := by
  unfold annotateEntries
  rw [List.map_append, map_fst_annotate, map_fst_filter]
  rfl

/-- Merge `extra` into `self`: kept slots, in-place overwrite, appended tail. -/
def annotate {α : Type u} (self extra : ReasonAnnotations α) (overwrite : Bool) :
    ReasonAnnotations α where
  entries := annotateEntries self extra overwrite
  keysNodup := by
    rw [annotateEntries_keys]
    refine List.nodup_append.mpr ⟨self.keysNodup, ?_, ?_⟩
    · exact List.Pairwise.sublist List.filter_sublist extra.keysNodup
    · intro left hleft right hright hcontra
      have hnot := (List.mem_filter.mp hright).right
      simp only [decide_eq_true_eq] at hnot
      exact hnot (hcontra ▸ hleft)

/-- The exact merge shape of rc.112 `ReasonBase.annotate`. census: cause.annotations -/
theorem annotate_entries {α : Type u} (self extra : ReasonAnnotations α)
    (overwrite : Bool) :
    (self.annotate extra overwrite).entries =
      self.entries.map (fun entry =>
        if overwrite = true then
          match extra.lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) ++
      extra.entries.filter (fun entry => decide (entry.fst ∉ self.keys)) := rfl

/-- Annotating with the empty map is the identity. census: cause.annotations -/
theorem annotate_empty {α : Type u} (self : ReasonAnnotations α) (overwrite : Bool) :
    self.annotate empty overwrite = self := by
  refine ext ?_
  rw [annotate_entries]
  have hentry : forall entry : String × α,
      (if overwrite = true then
        match (empty : ReasonAnnotations α).lookup entry.fst with
        | some value => (entry.fst, value)
        | none => entry
      else entry) = entry := by
    intro entry
    by_cases hov : overwrite = true
    · rw [if_pos hov, lookup_empty]
    · rw [if_neg hov]
  have hmap : forall entries : List (String × α),
      entries.map (fun entry =>
        if overwrite = true then
          match (empty : ReasonAnnotations α).lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) = entries := by
    intro entries
    induction entries with
    | nil => rfl
    | cons head tail ih => rw [List.map_cons, ih, hentry head]
  rw [hmap]
  exact List.append_nil _

/-- Existing keys keep their slot; new keys are appended. census: cause.annotations -/
theorem annotate_keys {α : Type u} (self extra : ReasonAnnotations α)
    (overwrite : Bool) :
    (self.annotate extra overwrite).keys =
      self.keys ++ extra.keys.filter (fun key => decide (key ∉ self.keys)) :=
  annotateEntries_keys self extra overwrite

private theorem find_annotate {α : Type u} (entries : List (String × α))
    (extra : ReasonAnnotations α) (overwrite : Bool) (key : String) :
    (entries.map (fun entry =>
          if overwrite = true then
            match extra.lookup entry.fst with
            | some value => (entry.fst, value)
            | none => entry
          else entry)).find? (fun entry => decide (entry.fst = key)) =
      (entries.find? (fun entry => decide (entry.fst = key))).map (fun entry =>
        if overwrite = true then
          match extra.lookup entry.fst with
          | some value => (entry.fst, value)
          | none => entry
        else entry) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    have hfst : (if overwrite = true then
        match extra.lookup head.fst with
        | some value => (head.fst, value)
        | none => head
      else head).fst = head.fst := by
      by_cases hov : overwrite = true
      · rw [if_pos hov]
        split <;> rfl
      · rw [if_neg hov]
    by_cases hhead : head.fst = key
    · rw [List.map_cons,
        List.find?_cons_of_pos
          (by simp only [decide_eq_true_eq, hfst]; exact hhead),
        List.find?_cons_of_pos (by simp only [decide_eq_true_eq]; exact hhead),
        Option.map_some]
    · rw [List.map_cons,
        List.find?_cons_of_neg
          (by simp only [decide_eq_true_eq, hfst]; exact hhead),
        List.find?_cons_of_neg (by simp only [decide_eq_true_eq]; exact hhead),
        ih]

private theorem find_filter {α : Type u} (entries : List (String × α))
    (keys : List String) (key : String) (hkey : key ∉ keys) :
    (entries.filter (fun entry => decide (entry.fst ∉ keys))).find?
        (fun entry => decide (entry.fst = key)) =
      entries.find? (fun entry => decide (entry.fst = key)) := by
  induction entries with
  | nil => rfl
  | cons head tail ih =>
    by_cases hhead : head.fst = key
    · rw [List.filter_cons_of_pos
          (by simp only [decide_eq_true_eq]; exact hhead ▸ hkey),
        List.find?_cons_of_pos (by simp only [decide_eq_true_eq]; exact hhead),
        List.find?_cons_of_pos (by simp only [decide_eq_true_eq]; exact hhead)]
    · by_cases hkeep : head.fst ∈ keys
      · rw [List.filter_cons_of_neg
            (by simp only [decide_eq_true_eq]; exact fun contra => contra hkeep),
          List.find?_cons_of_neg (by simp only [decide_eq_true_eq]; exact hhead),
          ih]
      · rw [List.filter_cons_of_pos
            (by simp only [decide_eq_true_eq]; exact hkeep),
          List.find?_cons_of_neg (by simp only [decide_eq_true_eq]; exact hhead),
          List.find?_cons_of_neg (by simp only [decide_eq_true_eq]; exact hhead),
          ih]

private theorem lookup_annotate_cases {α : Type u} (self extra : ReasonAnnotations α)
    (overwrite : Bool) (key : String) :
    (self.annotate extra overwrite).lookup key =
      match self.entries.find? (fun entry => decide (entry.fst = key)) with
      | some entry =>
        if overwrite = true then
          match extra.lookup key with
          | some value => some value
          | none => some entry.snd
        else some entry.snd
      | none => extra.lookup key := by
  rw [lookup_eq, annotate_entries, List.find?_append, find_annotate]
  cases hfind : self.entries.find? (fun entry => decide (entry.fst = key)) with
  | some entry =>
    have hkey : entry.fst = key := by
      have := List.find?_some hfind
      simp only [decide_eq_true_eq] at this
      exact this
    rw [Option.map_some, Option.some_or, Option.map_some, hkey]
    show _ = if overwrite = true then
        match extra.lookup key with
        | some value => some value
        | none => some entry.snd
      else some entry.snd
    by_cases hov : overwrite = true
    · rw [if_pos hov, if_pos hov]
      split <;> rfl
    · rw [if_neg hov, if_neg hov]
  | none =>
    have hkey : key ∉ self.keys := by
      intro hmem
      have ⟨entry, hentry, heq⟩ :=
        List.mem_map.mp (show key ∈ self.entries.map Prod.fst from hmem)
      exact (List.find?_eq_none.mp hfind entry hentry)
        (by simp only [decide_eq_true_eq]; exact heq)
    rw [Option.map_none, Option.none_or, find_filter _ _ _ hkey, lookup_eq]

/-- Without `overwrite` an existing value survives the merge. census: cause.annotations -/
theorem lookup_annotate_kept {α : Type u} (self extra : ReasonAnnotations α)
    (key : String) (value : α) (h : self.lookup key = some value) :
    (self.annotate extra false).lookup key = some value := by
  rw [lookup_annotate_cases]
  rw [lookup_eq] at h
  cases hfind : self.entries.find? (fun entry => decide (entry.fst = key)) with
  | some entry =>
    rw [hfind, Option.map_some] at h
    exact h
  | none => rw [hfind, Option.map_none] at h; exact absurd h (by simp)

/-- A key absent from `self` is taken from `extra`. census: cause.annotations -/
theorem lookup_annotate_new {α : Type u} (self extra : ReasonAnnotations α)
    (key : String) (value : α) (overwrite : Bool) (hself : self.lookup key = none)
    (hextra : extra.lookup key = some value) :
    (self.annotate extra overwrite).lookup key = some value := by
  rw [lookup_annotate_cases]
  rw [lookup_eq] at hself
  cases hfind : self.entries.find? (fun entry => decide (entry.fst = key)) with
  | some entry => rw [hfind, Option.map_some] at hself; exact absurd hself (by simp)
  | none => rw [hextra]

/-- With `overwrite` the value from `extra` wins. census: cause.annotations -/
theorem lookup_annotate_overwrite {α : Type u} (self extra : ReasonAnnotations α)
    (key : String) (value : α) (hextra : extra.lookup key = some value) :
    (self.annotate extra true).lookup key = some value := by
  rw [lookup_annotate_cases]
  cases hfind : self.entries.find? (fun entry => decide (entry.fst = key)) with
  | some entry =>
    show (if true = true then
        match extra.lookup key with
        | some value => some value
        | none => some entry.snd
      else some entry.snd) = some value
    rw [if_pos rfl, hextra]
  | none => exact hextra

/-- A key absent from both maps stays absent. census: cause.annotations -/
theorem lookup_annotate_absent {α : Type u} (self extra : ReasonAnnotations α)
    (key : String) (overwrite : Bool) (hself : self.lookup key = none)
    (hextra : extra.lookup key = none) :
    (self.annotate extra overwrite).lookup key = none := by
  rw [lookup_annotate_cases]
  rw [lookup_eq] at hself
  cases hfind : self.entries.find? (fun entry => decide (entry.fst = key)) with
  | some entry => rw [hfind, Option.map_some] at hself; exact absurd hself (by simp)
  | none => exact hextra

/-- Annotation equality is finer than key-to-value content. census: cause.annotations -/
theorem order_retained :
    exists left right : ReasonAnnotations Nat,
      (forall key : String, left.lookup key = right.lookup key) /\ left ≠ right := by
  refine ⟨⟨[("a", 0), ("b", 0)], by decide⟩, ⟨[("b", 0), ("a", 0)], by decide⟩, ?_, ?_⟩
  · intro key
    by_cases ha : key = "a"
    · subst ha
      rfl
    · by_cases hb : key = "b"
      · subst hb
        rfl
      · have hnone : forall entries : List (String × Nat),
            (forall entry, entry ∈ entries -> entry.fst = "a" \/ entry.fst = "b") ->
            (entries.find? (fun entry => decide (entry.fst = key))).map Prod.snd = none := by
          intro entries
          induction entries with
          | nil => intro _; rfl
          | cons head tail ih =>
            intro hentries
            rw [List.find?_cons_of_neg (by
              simp only [decide_eq_true_eq]
              intro hcontra
              cases hentries head List.mem_cons_self with
              | inl hleft => exact ha (hcontra.symm.trans hleft)
              | inr hright => exact hb (hcontra.symm.trans hright))]
            exact ih (fun entry hmem => hentries entry (List.mem_cons_of_mem head hmem))
        simp only [ReasonAnnotations.lookup]
        rw [hnone [("a", 0), ("b", 0)] (by decide), hnone [("b", 0), ("a", 0)] (by decide)]
  · intro heq
    exact absurd (congrArg ReasonAnnotations.entries heq) (by decide)

end ReasonAnnotations

/-- The closed public reason alphabet of rc.112. -/
inductive ReasonTag
  | fail
  | die
  | interrupt
deriving DecidableEq, Repr

namespace ReasonTag

/-- Every reason tag, in declaration order. -/
def all : List ReasonTag := [fail, die, interrupt]

/-- The tag enumeration lists no tag twice. census: exit.reason-alphabet -/
theorem all_nodup : all.Nodup := by decide

/-- The tag enumeration is complete. census: exit.reason-alphabet -/
theorem mem_all (tag : ReasonTag) : tag ∈ all := by
  cases tag <;> decide

/-- There is no fourth reason tag. census: exit.reason-alphabet -/
theorem cases_receipt (tag : ReasonTag) :
    tag = fail \/ tag = die \/ tag = interrupt := by
  cases tag
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end ReasonTag

/-- One reason of a cause: a typed failure, a defect, or an interruption. -/
inductive Reason (ε δ ι α : Type u)
  /-- A typed error together with its annotations. -/
  | fail (error : ε) (annotations : ReasonAnnotations α)
  /-- An unknown defect together with its annotations. -/
  | die (defect : δ) (annotations : ReasonAnnotations α)
  /-- An optional interruptor identity together with its annotations. -/
  | interrupt (interruptor : Option ι) (annotations : ReasonAnnotations α)
deriving DecidableEq

namespace Reason

/-- The reason's tag. -/
def tag {ε δ ι α : Type u} : Reason ε δ ι α -> ReasonTag
  | fail _ _ => ReasonTag.fail
  | die _ _ => ReasonTag.die
  | interrupt _ _ => ReasonTag.interrupt

/-- The reason's annotation map. -/
def annotations {ε δ ι α : Type u} : Reason ε δ ι α -> ReasonAnnotations α
  | fail _ stored => stored
  | die _ stored => stored
  | interrupt _ stored => stored

/-- The typed error carried by a `Fail` reason. -/
def error? {ε δ ι α : Type u} : Reason ε δ ι α -> Option ε
  | fail error _ => some error
  | die _ _ => none
  | interrupt _ _ => none

/-- The defect carried by a `Die` reason. -/
def defect? {ε δ ι α : Type u} : Reason ε δ ι α -> Option δ
  | fail _ _ => none
  | die defect _ => some defect
  | interrupt _ _ => none

/-- Merge `extra` into the reason's annotations, keeping payload and tag. -/
def annotate {ε δ ι α : Type u} :
    Reason ε δ ι α -> ReasonAnnotations α -> Bool -> Reason ε δ ι α
  | fail error stored, extra, overwrite => fail error (stored.annotate extra overwrite)
  | die defect stored, extra, overwrite => die defect (stored.annotate extra overwrite)
  | interrupt interruptor stored, extra, overwrite =>
    interrupt interruptor (stored.annotate extra overwrite)

/-- The host `WeakMap` identity memory is refused, not modelled. census: cause.annotations -/
theorem host_memory_refused {ε α : Type u} (recall : ε -> ReasonAnnotations α)
    (left right : ε) (h : left = right) : recall left = recall right :=
  congrArg recall h

/-- A `Fail` reason tags as `fail`. census: cause.reason-fail -/
theorem tag_fail {ε δ ι α : Type u} (error : ε) (stored : ReasonAnnotations α) :
    (fail error stored : Reason ε δ ι α).tag = ReasonTag.fail := rfl

/-- A `Die` reason tags as `die`. census: cause.reason-die -/
theorem tag_die {ε δ ι α : Type u} (defect : δ) (stored : ReasonAnnotations α) :
    (die defect stored : Reason ε δ ι α).tag = ReasonTag.die := rfl

/-- An `Interrupt` reason tags as `interrupt`. census: cause.reason-interrupt -/
theorem tag_interrupt {ε δ ι α : Type u} (interruptor : Option ι)
    (stored : ReasonAnnotations α) :
    (interrupt interruptor stored : Reason ε δ ι α).tag = ReasonTag.interrupt := rfl

/-- A `Fail` reason carries its annotations. census: cause.reason-fail -/
theorem annotations_fail {ε δ ι α : Type u} (error : ε) (stored : ReasonAnnotations α) :
    (fail error stored : Reason ε δ ι α).annotations = stored := rfl

/-- A `Die` reason carries its annotations. census: cause.reason-die -/
theorem annotations_die {ε δ ι α : Type u} (defect : δ) (stored : ReasonAnnotations α) :
    (die defect stored : Reason ε δ ι α).annotations = stored := rfl

/-- An `Interrupt` reason carries its annotations. census: cause.reason-interrupt -/
theorem annotations_interrupt {ε δ ι α : Type u} (interruptor : Option ι)
    (stored : ReasonAnnotations α) :
    (interrupt interruptor stored : Reason ε δ ι α).annotations = stored := rfl

/-- A `Fail` reason yields its typed error. census: cause.reason-fail -/
theorem error_fail {ε δ ι α : Type u} (error : ε) (stored : ReasonAnnotations α) :
    (fail error stored : Reason ε δ ι α).error? = some error := rfl

/-- A `Die` reason yields no typed error. census: cause.reason-die -/
theorem error_die {ε δ ι α : Type u} (defect : δ) (stored : ReasonAnnotations α) :
    (die defect stored : Reason ε δ ι α).error? = none := rfl

/-- An `Interrupt` reason yields no typed error. census: cause.reason-interrupt -/
theorem error_interrupt {ε δ ι α : Type u} (interruptor : Option ι)
    (stored : ReasonAnnotations α) :
    (interrupt interruptor stored : Reason ε δ ι α).error? = none := rfl

/-- A `Fail` reason yields no defect. census: cause.reason-fail -/
theorem defect_fail {ε δ ι α : Type u} (error : ε) (stored : ReasonAnnotations α) :
    (fail error stored : Reason ε δ ι α).defect? = none := rfl

/-- A `Die` reason yields its defect. census: cause.reason-die -/
theorem defect_die {ε δ ι α : Type u} (defect : δ) (stored : ReasonAnnotations α) :
    (die defect stored : Reason ε δ ι α).defect? = some defect := rfl

/-- An `Interrupt` reason yields no defect. census: cause.reason-interrupt -/
theorem defect_interrupt {ε δ ι α : Type u} (interruptor : Option ι)
    (stored : ReasonAnnotations α) :
    (interrupt interruptor stored : Reason ε δ ι α).defect? = none := rfl

/-- `Fail` equality compares the error and the annotations. census: cause.reason-fail -/
theorem fail_inj {ε δ ι α : Type u} (leftError rightError : ε)
    (leftAnnotations rightAnnotations : ReasonAnnotations α) :
    (fail leftError leftAnnotations : Reason ε δ ι α) =
        fail rightError rightAnnotations <->
      leftError = rightError /\ leftAnnotations = rightAnnotations := by
  constructor
  · intro h
    injection h with hpayload hstored
    exact ⟨hpayload, hstored⟩
  · intro h
    rw [h.left, h.right]

/-- `Die` equality compares the defect and the annotations. census: cause.reason-die -/
theorem die_inj {ε δ ι α : Type u} (leftDefect rightDefect : δ)
    (leftAnnotations rightAnnotations : ReasonAnnotations α) :
    (die leftDefect leftAnnotations : Reason ε δ ι α) =
        die rightDefect rightAnnotations <->
      leftDefect = rightDefect /\ leftAnnotations = rightAnnotations := by
  constructor
  · intro h
    injection h with hpayload hstored
    exact ⟨hpayload, hstored⟩
  · intro h
    rw [h.left, h.right]

/-- `Interrupt` equality compares the interruptor with the annotations.
census: cause.reason-interrupt -/
theorem interrupt_inj {ε δ ι α : Type u} (leftInterruptor rightInterruptor : Option ι)
    (leftAnnotations rightAnnotations : ReasonAnnotations α) :
    (interrupt leftInterruptor leftAnnotations : Reason ε δ ι α) =
        interrupt rightInterruptor rightAnnotations <->
      leftInterruptor = rightInterruptor /\ leftAnnotations = rightAnnotations := by
  constructor
  · intro h
    injection h with hpayload hstored
    exact ⟨hpayload, hstored⟩
  · intro h
    rw [h.left, h.right]

/-- There is no fourth reason constructor. census: exit.reason-alphabet -/
theorem cases_receipt {ε δ ι α : Type u} (reason : Reason ε δ ι α) :
    (exists error stored, reason = fail error stored) \/
    (exists defect stored, reason = die defect stored) \/
    (exists interruptor stored, reason = interrupt interruptor stored) := by
  cases reason with
  | fail error stored => exact Or.inl ⟨error, stored, rfl⟩
  | die defect stored => exact Or.inr (Or.inl ⟨defect, stored, rfl⟩)
  | interrupt interruptor stored => exact Or.inr (Or.inr ⟨interruptor, stored, rfl⟩)

/-- Every reason tags inside the closed alphabet. census: exit.reason-alphabet -/
theorem tag_mem_all {ε δ ι α : Type u} (reason : Reason ε δ ι α) :
    reason.tag ∈ ReasonTag.all :=
  ReasonTag.mem_all reason.tag

/-- Annotating preserves the tag. census: cause.annotations -/
theorem annotate_tag {ε δ ι α : Type u} (reason : Reason ε δ ι α)
    (extra : ReasonAnnotations α) (overwrite : Bool) :
    (reason.annotate extra overwrite).tag = reason.tag := by
  cases reason <;> rfl

/-- Annotating merges into the reason's annotations. census: cause.annotations -/
theorem annotate_annotations {ε δ ι α : Type u} (reason : Reason ε δ ι α)
    (extra : ReasonAnnotations α) (overwrite : Bool) :
    (reason.annotate extra overwrite).annotations =
      reason.annotations.annotate extra overwrite := by
  cases reason <;> rfl

end Reason

/-- A cause is exactly an ordered list of reasons: no tree, no nodes. -/
structure Cause (ε δ ι α : Type u) where
  /-- The flat ordered reason list. -/
  reasons : List (Reason ε δ ι α)
deriving DecidableEq

/-- The lossy projection taken by rc.112's throwing entry points. -/
inductive Squashed (ε δ : Type u)
  /-- The first typed error in reason order. -/
  | error (error : ε)
  /-- The first defect in reason order. -/
  | defect (defect : δ)
  /-- Interruption without any error. -/
  | interruptedWithoutError
  /-- The empty cause, rc.112's fourth arm. -/
  | emptyCause
deriving DecidableEq

namespace Squashed

/-- There is no fifth squash observation. census: cause.squash -/
theorem cases_receipt {ε δ : Type u} (squashed : Squashed ε δ) :
    (exists error, squashed = Squashed.error error) \/
    (exists defect, squashed = Squashed.defect defect) \/
    squashed = Squashed.interruptedWithoutError \/
    squashed = Squashed.emptyCause := by
  cases squashed with
  | error error => exact Or.inl ⟨error, rfl⟩
  | defect defect => exact Or.inr (Or.inl ⟨defect, rfl⟩)
  | interruptedWithoutError => exact Or.inr (Or.inr (Or.inl rfl))
  | emptyCause => exact Or.inr (Or.inr (Or.inr rfl))

end Squashed

namespace Cause

/-- A cause is determined by its reason list. census: cause.flat-reasons -/
theorem ext {ε δ ι α : Type u} {left right : Cause ε δ ι α}
    (h : left.reasons = right.reasons) : left = right := by
  cases left
  cases right
  cases h
  rfl

/-- Cause equality is exactly reason-list equality. census: cause.flat-reasons -/
theorem eq_iff {ε δ ι α : Type u} (left right : Cause ε δ ι α) :
    left = right <-> left.reasons = right.reasons :=
  ⟨fun h => congrArg Cause.reasons h, ext⟩

/-- rc.112 `CauseImpl` equality: equal length, pairwise-equal reasons.
census: cause.flat-reasons -/
theorem eq_iff_pointwise {ε δ ι α : Type u} (left right : Cause ε δ ι α) :
    left = right <->
      (left.reasons.length = right.reasons.length /\
        forall index : Nat, left.reasons[index]? = right.reasons[index]?) := by
  constructor
  · intro h
    rw [h]
    exact ⟨rfl, fun _ => rfl⟩
  · intro h
    exact ext (List.ext_getElem? h.right)

/-- The empty cause, rc.112's `causeEmpty`. -/
def empty {ε δ ι α : Type u} : Cause ε δ ι α where
  reasons := []

/-- The single-`Fail` cause, rc.112's `causeFail`. -/
def fail {ε δ ι α : Type u} (error : ε) : Cause ε δ ι α where
  reasons := [Reason.fail error ReasonAnnotations.empty]

/-- The single-`Die` cause, rc.112's `causeDie`. -/
def die {ε δ ι α : Type u} (defect : δ) : Cause ε δ ι α where
  reasons := [Reason.die defect ReasonAnnotations.empty]

/-- The single-`Interrupt` cause, rc.112's `causeInterrupt`. -/
def interrupt {ε δ ι α : Type u} (interruptor : Option ι) : Cause ε δ ι α where
  reasons := [Reason.interrupt interruptor ReasonAnnotations.empty]

/-- Annotate every reason of the cause. -/
def annotate {ε δ ι α : Type u} (self : Cause ε δ ι α) (extra : ReasonAnnotations α)
    (overwrite : Bool) : Cause ε δ ι α where
  reasons := self.reasons.map (fun reason => reason.annotate extra overwrite)

/-- The empty cause has no reason. census: cause.flat-reasons -/
theorem empty_reasons {ε δ ι α : Type u} :
    (empty : Cause ε δ ι α).reasons = [] := rfl

/-- `causeFail` carries one unannotated `Fail`. census: cause.reason-fail -/
theorem fail_reasons {ε δ ι α : Type u} (error : ε) :
    (fail error : Cause ε δ ι α).reasons =
      [Reason.fail error ReasonAnnotations.empty] := rfl

/-- `causeDie` carries one unannotated `Die`. census: cause.reason-die -/
theorem die_reasons {ε δ ι α : Type u} (defect : δ) :
    (die defect : Cause ε δ ι α).reasons =
      [Reason.die defect ReasonAnnotations.empty] := rfl

/-- `causeInterrupt` carries one unannotated `Interrupt`. census: cause.reason-interrupt -/
theorem interrupt_reasons {ε δ ι α : Type u} (interruptor : Option ι) :
    (interrupt interruptor : Cause ε δ ι α).reasons =
      [Reason.interrupt interruptor ReasonAnnotations.empty] := rfl

/-- Annotating a cause annotates each reason in place. census: cause.annotations -/
theorem annotate_reasons {ε δ ι α : Type u} (self : Cause ε δ ι α)
    (extra : ReasonAnnotations α) (overwrite : Bool) :
    (self.annotate extra overwrite).reasons =
      self.reasons.map (fun reason => reason.annotate extra overwrite) := rfl

/-- First-occurrence deduplication, the `Arr.union` kernel. -/
def dedup {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] : List (Reason ε δ ι α) -> List (Reason ε δ ι α)
  | [] => []
  | reason :: rest =>
    reason :: (dedup rest).filter (fun other => decide (other ≠ reason))

/-- Deduplicating nothing yields nothing. census: cause.combine-union -/
theorem dedup_nil {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] : dedup ([] : List (Reason ε δ ι α)) = [] := rfl

/-- The frozen deduplication step keeps the first occurrence.
census: cause.combine-union -/
theorem dedup_cons {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (reason : Reason ε δ ι α) (rest : List (Reason ε δ ι α)) :
    dedup (reason :: rest) =
      reason :: (dedup rest).filter (fun other => decide (other ≠ reason)) := rfl

/-- Deduplication changes no membership. census: cause.combine-union -/
theorem mem_dedup {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (reason : Reason ε δ ι α) (list : List (Reason ε δ ι α)) :
    reason ∈ dedup list <-> reason ∈ list := by
  induction list with
  | nil => exact Iff.rfl
  | cons head tail ih =>
    rw [dedup_cons, List.mem_cons, List.mem_cons]
    constructor
    · intro h
      cases h with
      | inl heq => exact Or.inl heq
      | inr hmem => exact Or.inr (ih.mp (List.mem_filter.mp hmem).left)
    · intro h
      cases h with
      | inl heq => exact Or.inl heq
      | inr hmem =>
        by_cases heq : reason = head
        · exact Or.inl heq
        · refine Or.inr (List.mem_filter.mpr ⟨ih.mpr hmem, ?_⟩)
          simp only [decide_eq_true_eq]
          exact heq

/-- Deduplication produces a duplicate-free list. census: cause.combine-union -/
theorem dedup_nodup {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (list : List (Reason ε δ ι α)) : (dedup list).Nodup := by
  induction list with
  | nil => exact List.nodup_nil
  | cons head tail ih =>
    rw [dedup_cons]
    refine List.nodup_cons.mpr ⟨?_, List.Pairwise.sublist List.filter_sublist ih⟩
    intro hmem
    have := (List.mem_filter.mp hmem).right
    simp only [decide_eq_true_eq] at this
    exact this rfl

private theorem filter_ne_of_not_mem {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (list : List (Reason ε δ ι α))
    (reason : Reason ε δ ι α) (h : reason ∉ list) :
    list.filter (fun other => decide (other ≠ reason)) = list := by
  refine List.filter_eq_self.mpr ?_
  intro other hother
  simp only [decide_eq_true_eq]
  intro heq
  exact h (heq ▸ hother)

/-- Deduplication is the identity on a duplicate-free list. census: cause.combine-union -/
theorem dedup_of_nodup {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (list : List (Reason ε δ ι α)) (h : list.Nodup) : dedup list = list := by
  induction list with
  | nil => rfl
  | cons head tail ih =>
    rw [dedup_cons, ih (List.nodup_cons.mp h).right,
      filter_ne_of_not_mem tail head (List.nodup_cons.mp h).left]

private theorem dedup_append {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] :
    forall left right : List (Reason ε δ ι α), left.Nodup -> right.Nodup ->
      dedup (left ++ right) =
        left ++ right.filter (fun reason => decide (reason ∉ left)) := by
  intro left
  induction left with
  | nil =>
    intro right _ hright
    have hfilter :
        right.filter
            (fun reason => decide (reason ∉ ([] : List (Reason ε δ ι α)))) = right :=
      List.filter_eq_self.mpr
        (by intro reason _; simp only [decide_eq_true_eq]; exact List.not_mem_nil)
    rw [List.nil_append, List.nil_append, hfilter, dedup_of_nodup right hright]
  | cons head tail ih =>
    intro right hleft hright
    have hhead : head ∉ tail := (List.nodup_cons.mp hleft).left
    have htail : tail.Nodup := (List.nodup_cons.mp hleft).right
    have hpred :
        (fun reason : Reason ε δ ι α =>
            decide (reason ≠ head) && decide (reason ∉ tail)) =
          (fun reason => decide (reason ∉ head :: tail)) := by
      funext reason
      refine Bool.eq_iff_iff.mpr ?_
      simp only [Bool.and_eq_true, decide_eq_true_eq, ne_eq, List.mem_cons, not_or]
    rw [List.cons_append, dedup_cons, ih right htail hright, List.filter_append,
      filter_ne_of_not_mem tail head hhead, List.filter_filter, hpred, List.cons_append]

/-- rc.112 `hasInterrupts` (`internal/effect.ts:186`,
`self.reasons.some(isInterruptReason)`): the cause carries at least one
`Interrupt` reason. It is the predicate `AsyncFinalizer[contE]` reads before it
decides whether to run its cancel effect. census: cause.reason-interrupt -/
def hasInterrupts {ε δ ι α : Type u} (self : Cause ε δ ι α) : Bool :=
  self.reasons.any (fun reason => reason.tag == ReasonTag.interrupt)

/-- Membership form of the predicate. census: cause.reason-interrupt -/
theorem hasInterrupts_iff {ε δ ι α : Type u} (self : Cause ε δ ι α) :
    self.hasInterrupts = true <->
      exists reason, reason ∈ self.reasons /\ reason.tag = ReasonTag.interrupt := by
  simp [hasInterrupts]

/-- The empty cause carries no interruption. census: cause.reason-interrupt -/
theorem hasInterrupts_empty {ε δ ι α : Type u} :
    (empty : Cause ε δ ι α).hasInterrupts = false := rfl

/-- A single-`Fail` cause carries no interruption. census: cause.reason-interrupt -/
theorem hasInterrupts_fail {ε δ ι α : Type u} (error : ε) :
    (fail error : Cause ε δ ι α).hasInterrupts = false := rfl

/-- A single-`Die` cause carries no interruption. census: cause.reason-interrupt -/
theorem hasInterrupts_die {ε δ ι α : Type u} (defect : δ) :
    (die defect : Cause ε δ ι α).hasInterrupts = false := rfl

/-- `causeInterrupt` carries one. census: cause.reason-interrupt -/
theorem hasInterrupts_interrupt {ε δ ι α : Type u} (interruptor : Option ι) :
    (interrupt interruptor : Cause ε δ ι α).hasInterrupts = true := rfl

/-- rc.112 `causeCombine`: the empty cause is an identity, otherwise a union. -/
def combine {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ] [DecidableEq ι]
    [DecidableEq α] (self that : Cause ε δ ι α) : Cause ε δ ι α :=
  if self.reasons = [] then that
  else if that.reasons = [] then self
  else Cause.mk (dedup (self.reasons ++ that.reasons))

private theorem combine_eq {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self that : Cause ε δ ι α) :
    combine self that =
      if self.reasons = [] then that
      else if that.reasons = [] then self
      else Cause.mk (dedup (self.reasons ++ that.reasons)) := rfl

/-- The empty cause is a left identity. census: cause.combine-union -/
theorem combine_empty_left {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (that : Cause ε δ ι α) :
    combine empty that = that := by
  rw [combine_eq, if_pos empty_reasons]

/-- The empty cause is a right identity. census: cause.combine-union -/
theorem combine_empty_right {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α) :
    combine self empty = self := by
  rw [combine_eq]
  by_cases h : self.reasons = []
  · rw [if_pos h]
    exact ext h.symm
  · rw [if_neg h, if_pos empty_reasons]

/-- The definition-level union law for two nonempty causes.
census: cause.combine-union -/
theorem combine_reasons {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self that : Cause ε δ ι α)
    (hself : self.reasons ≠ []) (hthat : that.reasons ≠ []) :
    (combine self that).reasons = dedup (self.reasons ++ that.reasons) := by
  rw [combine_eq, if_neg hself, if_neg hthat]

/-- Combining is a union of the operands' reasons. census: cause.combine-union -/
theorem mem_combine {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (reason : Reason ε δ ι α)
    (self that : Cause ε δ ι α) :
    reason ∈ (combine self that).reasons <->
      reason ∈ self.reasons \/ reason ∈ that.reasons := by
  by_cases hself : self.reasons = []
  · rw [combine_eq, if_pos hself, hself]
    constructor
    · exact Or.inr
    · intro h
      cases h with
      | inl hmem => exact absurd hmem List.not_mem_nil
      | inr hmem => exact hmem
  · by_cases hthat : that.reasons = []
    · rw [combine_eq, if_neg hself, if_pos hthat, hthat]
      constructor
      · exact Or.inl
      · intro h
        cases h with
        | inl hmem => exact hmem
        | inr hmem => exact absurd hmem List.not_mem_nil
    · rw [combine_reasons self that hself hthat, mem_dedup, List.mem_append]

/-- Combining introduces no reason, so there is no cause node.
census: rule.cause-has-no-structure -/
theorem combine_no_new_reason {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (reason : Reason ε δ ι α)
    (self that : Cause ε δ ι α)
    (h : reason ∈ (combine self that).reasons) :
    reason ∈ self.reasons \/ reason ∈ that.reasons :=
  (mem_combine reason self that).mp h

/-- The `Arr.union` order: `self`, then the new elements of `that`.
census: cause.combine-union -/
theorem combine_order {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self that : Cause ε δ ι α)
    (hself : self.reasons.Nodup) (hthat : that.reasons.Nodup) :
    (combine self that).reasons =
      self.reasons ++
        that.reasons.filter (fun reason => decide (reason ∉ self.reasons)) := by
  by_cases hnil : self.reasons = []
  · rw [combine_eq, if_pos hnil, hnil, List.nil_append]
    exact (List.filter_eq_self.mpr (by
      intro reason _
      simp only [decide_eq_true_eq]
      exact List.not_mem_nil)).symm
  · by_cases hthatNil : that.reasons = []
    · rw [combine_eq, if_neg hnil, if_pos hthatNil, hthatNil]
      exact (List.append_nil _).symm
    · rw [combine_reasons self that hnil hthatNil, dedup_append _ _ hself hthat]

/-- Combining duplicate-free operands stays duplicate-free.
census: cause.combine-union -/
theorem combine_nodup {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self that : Cause ε δ ι α)
    (hself : self.reasons.Nodup) (hthat : that.reasons.Nodup) :
    (combine self that).reasons.Nodup := by
  by_cases hnil : self.reasons = []
  · rw [combine_eq, if_pos hnil]
    exact hthat
  · by_cases hthatNil : that.reasons = []
    · rw [combine_eq, if_neg hnil, if_pos hthatNil]
      exact hself
    · rw [combine_reasons self that hnil hthatNil]
      exact dedup_nodup _

private theorem filter_not_mem {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (target : List (Reason ε δ ι α)) :
    forall list : List (Reason ε δ ι α),
      (forall reason, reason ∈ list -> reason ∈ target) ->
      list.filter (fun reason => decide (reason ∉ target)) = [] := by
  intro list
  induction list with
  | nil => intro _; rfl
  | cons head tail ih =>
    intro hmem
    rw [List.filter_cons_of_neg (by
      simp only [decide_eq_true_eq]
      exact fun hnot => hnot (hmem head List.mem_cons_self))]
    exact ih (fun reason hreason => hmem reason (List.mem_cons_of_mem head hreason))

/-- The structural-equality short circuit. census: cause.combine-union -/
theorem combine_self {ε δ ι α : Type u} [DecidableEq ε] [DecidableEq δ]
    [DecidableEq ι] [DecidableEq α] (self : Cause ε δ ι α)
    (h : self.reasons.Nodup) : combine self self = self := by
  refine ext ?_
  rw [combine_order self self h h,
    filter_not_mem self.reasons self.reasons (fun _ hreason => hreason),
    List.append_nil]

private def squashOf {ε δ ι α : Type u} (errors : List ε) (defects : List δ)
    (reasons : List (Reason ε δ ι α)) : Squashed ε δ :=
  match errors with
  | error :: _ => Squashed.error error
  | [] =>
    match defects with
    | defect :: _ => Squashed.defect defect
    | [] =>
      match reasons with
      | [] => Squashed.emptyCause
      | _ :: _ => Squashed.interruptedWithoutError

/-- rc.112 `causeSquash`: partition first, then choose the first arm that fires. -/
def squash {ε δ ι α : Type u} (self : Cause ε δ ι α) : Squashed ε δ :=
  squashOf (self.reasons.filterMap Reason.error?)
    (self.reasons.filterMap Reason.defect?) self.reasons

private theorem squashOf_ne_emptyCause {ε δ ι α : Type u} (errors : List ε)
    (defects : List δ) (head : Reason ε δ ι α) (tail : List (Reason ε δ ι α)) :
    squashOf errors defects (head :: tail) ≠ Squashed.emptyCause := by
  cases errors with
  | cons headError _ =>
    show Squashed.error headError ≠ (Squashed.emptyCause : Squashed ε δ)
    intro h
    nomatch h
  | nil =>
    cases defects with
    | cons headDefect _ =>
      show Squashed.defect headDefect ≠ (Squashed.emptyCause : Squashed ε δ)
      intro h
      nomatch h
    | nil =>
      show Squashed.interruptedWithoutError ≠ (Squashed.emptyCause : Squashed ε δ)
      intro h
      nomatch h

/-- Arm one: a `Fail` anywhere beats everything else. census: cause.squash -/
theorem squash_error {ε δ ι α : Type u} (self : Cause ε δ ι α) (error : ε)
    (rest : List ε) (h : self.reasons.filterMap Reason.error? = error :: rest) :
    self.squash = Squashed.error error := by
  unfold squash
  rw [h]
  rfl

/-- Arm two: with no `Fail`, the first `Die` defect. census: cause.squash -/
theorem squash_defect {ε δ ι α : Type u} (self : Cause ε δ ι α) (defect : δ)
    (rest : List δ) (herror : self.reasons.filterMap Reason.error? = [])
    (hdefect : self.reasons.filterMap Reason.defect? = defect :: rest) :
    self.squash = Squashed.defect defect := by
  unfold squash
  rw [herror, hdefect]
  rfl

/-- Arm three: interruption without error. census: cause.squash -/
theorem squash_interrupted {ε δ ι α : Type u} (self : Cause ε δ ι α)
    (herror : self.reasons.filterMap Reason.error? = [])
    (hdefect : self.reasons.filterMap Reason.defect? = [])
    (hreasons : self.reasons ≠ []) :
    self.squash = Squashed.interruptedWithoutError := by
  have ⟨head, tail, hcons⟩ := List.exists_cons_of_ne_nil hreasons
  unfold squash
  rw [herror, hdefect, hcons]
  rfl

/-- Arm four: the empty cause. census: cause.squash -/
theorem squash_empty {ε δ ι α : Type u} :
    (empty : Cause ε δ ι α).squash = Squashed.emptyCause := rfl

/-- The fourth arm fires exactly on the empty reason list. census: cause.squash -/
theorem squash_emptyCause_iff {ε δ ι α : Type u} (self : Cause ε δ ι α) :
    self.squash = Squashed.emptyCause <-> self.reasons = [] := by
  constructor
  · intro h
    cases hreasons : self.reasons with
    | nil => rfl
    | cons head tail =>
      unfold squash at h
      rw [hreasons] at h
      exact absurd h (squashOf_ne_emptyCause _ _ head tail)
  · intro h
    unfold squash
    rw [h]
    rfl

/-- A single-`Fail` cause squashes to its error. census: cause.squash -/
theorem squash_fail {ε δ ι α : Type u} (error : ε) :
    (fail error : Cause ε δ ι α).squash = Squashed.error error := rfl

/-- A single-`Die` cause squashes to its defect. census: cause.squash -/
theorem squash_die {ε δ ι α : Type u} (defect : δ) :
    (die defect : Cause ε δ ι α).squash = Squashed.defect defect := rfl

/-- A single-`Interrupt` cause squashes to interruption. census: cause.squash -/
theorem squash_interrupt {ε δ ι α : Type u} (interruptor : Option ι) :
    (interrupt interruptor : Cause ε δ ι α).squash =
      Squashed.interruptedWithoutError := rfl

/-- A later `Fail` still beats an earlier `Die`. census: cause.squash -/
theorem squash_fail_over_die {ε δ ι α : Type u} (error : ε) (defect : δ)
    (dieAnnotations failAnnotations : ReasonAnnotations α) :
    (Cause.mk [Reason.die defect dieAnnotations,
        Reason.fail error failAnnotations] : Cause ε δ ι α).squash =
      Squashed.error error := rfl

end Cause

end Effect4
