import Effect4.Program.Compile
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.TypeAlgebra

/-!
# Laws.Program.Residual — the tag residual and the single-failure law (part 4, 2026-09-12)

DI-17 constrains every failure in a cause. The checker removes a tag column only when
the residual is empty; mixed columns remain joined unless a separate execution bound is
established. Selection still uses the first failure (DI-09). What is proved:

* `Ty.diffTag_sub` — the residual is below the column it was cut from, on every type;
* `Ty.diffTag_sound` — a value of the column on which the tag test is false is a value of
  the residual, on every type (the atom is total on values: false on a bare string, a
  natural, a pair whose first component is not the tag);
* `Ty.diffTag_canonical`, `supportedErrTy_diffTag` — on a **canonical** column the residual
  is canonical and stays in the error carrier. The unconditional statement the dispatch
  wrote (`supportedErrTy e → supportedErrTy (diffTag tag e)` on raw `e`) is false:
  `e = union (prod never string) (prod (lit "X") string)` normalizes to
  `prod (lit "X") string` and is supported, while `diffTag "X" e = prod never string` is not
  (`E4-RESID-CE-002`, `Test/Program/TypeAlgebraContract.lean`). The checker only ever cuts a
  normalized column (`catchIfError`), so the canonical statement is the one it needs;
* `catchIf_miss_admits` — the preservation law of the miss path under `SingleFail`: a cause
  with exactly one `Fail` reason, admitted at the body's column, on which the tag test
  misses (`caughtErrorValue?` answers `none`, the compile route's own decision), is admitted
  at the residual. Without the premise the statement is false: `[Fail B, Fail A]` under a
  catch of `A` misses on the first `Fail` and re-raises the whole cause, which carries `A`
  (`E4-RESID-CE-001`, `Test/Program/CatchIfContract.lean`). `caughtErrorValue?` and the
  first-`Fail` rule (DI-09) are unchanged.
-/

namespace Effect4.Program

open Effect4 Effect4.Machine

/-! ## The residual on members -/

namespace Ty

/-- A union of members each below `e` is below `e`. -/
theorem sub_ofMembers_of_forall (xs : List Ty) (e : Ty) (h : ∀ x ∈ xs, sub x e = true) :
    sub (ofMembers xs) e = true := by
  induction xs with
  | nil => exact OrderProof.sub_never e
  | cons x xs ih =>
    cases xs with
    | nil => exact h x List.mem_cons_self
    | cons y ys =>
      show sub (.union x (ofMembers (y :: ys))) e = true
      by_cases heq : Ty.union x (ofMembers (y :: ys)) = e
      · rw [heq]; exact sub_refl e
      · rw [sub_union_left _ _ _ heq]
        exact Bool.and_eq_true_iff.mpr
          ⟨h x List.mem_cons_self, ih (fun z hz => h z (List.mem_cons_of_mem x hz))⟩

/-- `diffTag_sub`: the residual is below the column, on every type. -/
theorem diffTag_sub (tag : String) (e : Ty) : sub (diffTag tag e) e = true :=
  sub_ofMembers_of_forall _ e fun _ hx =>
    OrderProof.member_sub_self (List.mem_filter.mp hx).1

/-- On a canonical column the residual is canonical: its members are the column's, in the
column's order, each fixed, and maximal among themselves. -/
theorem diffTag_canonical (tag : String) (e : Ty) (he : Canonical e) :
    Canonical (diffTag tag e) := by
  have hn : Normal e := he ▸ normal_normalize e
  unfold diffTag
  apply Normal.fixed
  refine Normal.row ⟨e.members.filter (fun m => !isTagged tag m),
      List.Pairwise.filter _ hn.members_ascending⟩ ?_ ?_ ?_
  · intro t ht
    exact hn.members (List.mem_filter.mp ht).1
  · intro t ht
    exact members_isMember (List.mem_filter.mp ht).1
  · intro x hx y hy hxy
    exact hn.members_maximal x (List.mem_filter.mp hx).1 y (List.mem_filter.mp hy).1 hxy

end Ty

/-- `supportedErrTy_diffTag`, on a canonical column: the residual's members are members of
the column, and support is member-wise. -/
theorem supportedErrTy_diffTag (tag : String) (e : Ty) (he : Ty.Canonical e)
    (hs : supportedErrTy e = true) : supportedErrTy (Ty.diffTag tag e) = true := by
  unfold supportedErrTy
  rw [Ty.diffTag_canonical tag e he]
  unfold supportedErrTy at hs
  rw [he] at hs
  unfold Ty.diffTag
  apply rawSupportedErrTy_ofMembers
  intro x hx
  exact (rawSupportedErrTy_iff_members e).mp hs x (List.mem_filter.mp hx).1

/-! ## The atom and the residual agree -/

theorem NativeAtom.eval_tagIs (tag : String) (v : Val) :
    NativeAtom.eval .tagIs [.str tag, v] = some (.bool (NativeAtom.tagHit tag v)) := rfl

/-- A pair whose first component is `str tag` is a hit; on any other value the test is false.
The `.prod (.lit tag) _` members of a column are exactly the members a hit can inhabit. -/
theorem Ty.hasTy_of_not_tagged (tag : String) (m : Ty) (v : Val) (allocated : List String)
    (hm : Ty.isTagged tag m = true) (hv : Val.hasTy v m allocated = true) :
    NativeAtom.tagHit tag v = true := by
  cases m with
  | prod a b =>
    cases a with
    | lit t =>
      simp only [Ty.isTagged, beq_iff_eq] at hm
      subst hm
      -- the value is a two-cell list whose first cell is the literal (at any allocation)
      cases v with
      | list vs =>
        cases vs with
        | nil => simp [Val.hasTy] at hv
        | cons x rest =>
          cases rest with
          | nil => simp [Val.hasTy] at hv
          | cons y more =>
            cases more with
            | cons _ _ => simp [Val.hasTy] at hv
            | nil =>
              simp only [Val.hasTy, Bool.and_eq_true] at hv
              obtain ⟨hx, _⟩ := hv
              cases x with
              | str s =>
                simp only [beq_iff_eq] at hx
                subst hx
                simp only [NativeAtom.tagHit]
                exact beq_iff_eq.mpr rfl
              | _ => simp at hx
      | _ => simp [Val.hasTy] at hv
    | _ => simp [Ty.isTagged] at hm
  | _ => simp [Ty.isTagged] at hm

/-- `diffTag_sound`: a value of the column on which the tag test is false is a value of the
residual, on every type. -/
theorem Ty.diffTag_sound (tag : String) (e : Ty) (v : Val) (allocated : List String)
    (hv : Val.hasTy v e allocated = true)
    (hmiss : NativeAtom.eval .tagIs [.str tag, v] = some (.bool false)) :
    Val.hasTy v (Ty.diffTag tag e) allocated = true := by
  rw [NativeAtom.eval_tagIs] at hmiss
  have hfalse : NativeAtom.tagHit tag v = false := by
    cases h : NativeAtom.tagHit tag v
    · rfl
    · rw [h] at hmiss
      exact absurd hmiss (by decide)
  rw [← hasTy_members] at hv
  obtain ⟨m, hm, hvm⟩ := List.any_eq_true.mp hv
  unfold Ty.diffTag
  rw [hasTy_ofMembers]
  apply List.any_eq_true.mpr
  refine ⟨m, List.mem_filter.mpr ⟨hm, ?_⟩, hvm⟩
  cases htag : Ty.isTagged tag m
  · rfl
  · have := Ty.hasTy_of_not_tagged tag m v allocated htag hvm
    rw [hfalse] at this
    cases this

/-! ## The single-failure premise and the miss path -/

/-- How many `Fail` reasons a cause carries. -/
def failCount (c : CauseV) : Nat :=
  (c.reasons.filter fun r => (Reason.error? r).isSome).length

/-- Exactly one `Fail` reason. This is a property of a cause, not a guarantee of the
Straight fragment: combined causes and failing finalizers can contain multiple failures. -/
def SingleFail (c : CauseV) : Prop := failCount c = 1

instance (c : CauseV) : Decidable (SingleFail c) := by unfold SingleFail; infer_instance

/-- With at most one `Fail` reason, any `Fail` reason of the cause is its first. -/
theorem findSome?_error?_of_le_one (rs : List (Reason Err Defect FiberId Ann))
    (hcount : (rs.filter fun r => (Reason.error? r).isSome).length ≤ 1)
    (r : Reason Err Defect FiberId Ann) (hr : r ∈ rs) (err : Err) (herr : Reason.error? r = some err) :
    rs.findSome? Reason.error? = some err := by
  induction rs with
  | nil => cases hr
  | cons x xs ih =>
    cases hx : Reason.error? x with
    | some e0 =>
      simp only [List.findSome?_cons, hx]
      simp only [List.filter_cons, hx, Option.isSome_some, ↓reduceIte, List.length_cons] at hcount
      cases hr with
      | head => rw [hx] at herr; exact herr
      | tail _ hr' =>
        have hpos : 0 < (xs.filter fun r => (Reason.error? r).isSome).length :=
          List.length_pos_of_mem (List.mem_filter.mpr ⟨hr', by rw [herr]; rfl⟩)
        omega
    | none =>
      simp only [List.findSome?_cons, hx]
      simp only [List.filter_cons, hx, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        at hcount
      cases hr with
      | head => rw [hx] at herr; cases herr
      | tail _ hr' => exact ih hcount hr'

/-- The tag test on the caught error variable evaluates to the atom on the caught value. -/
theorem evalTerm_tagTest (env : List Val) (tag : String) (w : Val) :
    evalTerm (env ++ [w]) (tagTest tag env.length) =
      some (.bool (NativeAtom.tagHit tag w)) := by
  simp only [tagTest, evalTerm, evalTerms, Lit.toVal, List.getElem?_concat_length, nativeAtom]
  rfl

/-- With at most one failure, a missed cause retains membership in the tag residual.
A cause admitted at the body's column `e`, on which the
tag test misses on the compile route (`caughtErrorValue?` answers `none`, so the whole cause
is re-raised), is admitted at the residual. -/
theorem catchIf_miss_admits_of_le_one (env : List Val) (tag : String) (e : Ty) (allocated : List String)
    (cause : CauseV) (hcount : failCount cause ≤ 1)
    (hadmits : causeAdmits (fun w _ => Val.hasTy w e allocated) e cause = true)
    (hmiss : caughtErrorValue? env (tagTest tag env.length) cause = none) :
    causeAdmits (fun w _ => Val.hasTy w (Ty.diffTag tag e) allocated) (Ty.diffTag tag e) cause
      = true := by
  unfold causeAdmits at hadmits ⊢
  apply List.all_eq_true.mpr
  intro r hr
  have hradmit := List.all_eq_true.mp hadmits r hr
  cases r with
  | die _ _ => rfl
  | interrupt _ _ => rfl
  | fail err ann =>
    simp only [reasonAdmits] at hradmit ⊢
    cases hval : valOfErr err with
    | none => rw [hval] at hradmit; cases hradmit
    | some w =>
      rw [hval] at hradmit
      -- the miss: the first (and only) `Fail` is this one, and the test is false on `w`
      have hfirst : firstFailure? cause = some err :=
        findSome?_error?_of_le_one cause.reasons hcount
          (.fail err ann) hr err rfl
      have hvalue : firstErrorValue? cause = some w := by
        simp only [firstErrorValue?, hfirst, Option.bind_some, hval]
      simp only [caughtErrorValue?, hvalue, Option.bind_eq_bind, Option.bind_some,
        evalTerm_tagTest] at hmiss
      have hfalse : NativeAtom.tagHit tag w = false := by
        cases h : NativeAtom.tagHit tag w
        · rfl
        · rw [h] at hmiss
          simp at hmiss
      exact Ty.diffTag_sound tag e w allocated hradmit
        (by rw [NativeAtom.eval_tagIs, hfalse])

/-- Recognition never confuses a test on another value with the caught-error binder. -/
theorem tagTest?_sound (test : Term) (caught : Nat) (tag : String)
    (h : tagTest? test caught = some tag) : test = tagTest tag caught := by
  unfold tagTest? at h
  split at h
  · rename_i atom actual index
    split at h
    · rename_i hshape
      rcases hshape with ⟨rfl, rfl⟩
      cases Option.some.inj h
      rfl
    · cases h
  · cases h

/-- The historical exactly-one statement is a corollary of the at-most-one law. -/
theorem catchIf_miss_admits (env : List Val) (tag : String) (e : Ty) (allocated : List String)
    (cause : CauseV) (hsingle : SingleFail cause)
    (hadmits : causeAdmits (fun w _ => Val.hasTy w e allocated) e cause = true)
    (hmiss : caughtErrorValue? env (tagTest tag env.length) cause = none) :
    causeAdmits (fun w _ => Val.hasTy w (Ty.diffTag tag e) allocated) (Ty.diffTag tag e) cause
      = true :=
  catchIf_miss_admits_of_le_one env tag e allocated cause
    (by unfold SingleFail at hsingle; omega) hadmits hmiss

/-- A represented cause with no selected failure has no typed failures at all.
Defects and interruptions remain admissible at any error type. -/
theorem causeAdmits_of_firstErrorValue_none (cause : CauseV) (e target : Ty)
    (allocated : List String)
    (hadmits : causeAdmits (fun w _ => Val.hasTy w e allocated) e cause = true)
    (hnone : firstErrorValue? cause = none) :
    causeAdmits (fun w _ => Val.hasTy w target allocated) target cause = true := by
  cases hfirst : firstFailure? cause with
  | none =>
    apply List.all_eq_true.mpr
    intro reason hmem
    have hno := List.findSome?_eq_none_iff.mp hfirst reason hmem
    cases reason with
    | fail _ _ => cases hno
    | die _ _ => rfl
    | interrupt _ _ => rfl
  | some error =>
    obtain ⟨reason, hmem, hreason⟩ := List.exists_of_findSome?_eq_some hfirst
    have hfit := List.all_eq_true.mp hadmits reason hmem
    cases reason with
    | die _ _ => cases hreason
    | interrupt _ _ => cases hreason
    | fail actual annotations =>
      have heq : actual = error := Option.some.inj hreason
      subst actual
      cases hval : valOfErr error with
      | none => simp only [reasonAdmits, hval] at hfit; cases hfit
      | some value =>
        simp only [firstErrorValue?, hfirst, Option.bind_some, hval] at hnone
        cases hnone

/-- Removing an entire tagged error column is valid for any number of failures.
If the test misses, the original cause contains only defects/interruptions. -/
theorem catchIf_miss_allCaught (env : List Val) (tag : String) (e : Ty)
    (allocated : List String) (cause : CauseV) (hall : Ty.diffTag tag e = .never)
    (hadmits : causeAdmits (fun w _ => Val.hasTy w e allocated) e cause = true)
    (hmiss : caughtErrorValue? env (tagTest tag env.length) cause = none) :
    causeAdmits (fun w _ => Val.hasTy w .never allocated) .never cause = true := by
  cases hvalue : firstErrorValue? cause with
  | none => exact causeAdmits_of_firstErrorValue_none cause e .never allocated hadmits hvalue
  | some value =>
    have hv := firstErrorValue?_typed cause e allocated value hadmits hvalue
    simp only [caughtErrorValue?, hvalue, Option.bind_eq_bind, Option.bind_some,
      evalTerm_tagTest] at hmiss
    have hfalse : NativeAtom.tagHit tag value = false := by
      cases h : NativeAtom.tagHit tag value
      · rfl
      · rw [h] at hmiss
        simp at hmiss
    have hbad := Ty.diffTag_sound tag e value allocated hv
      (by rw [NativeAtom.eval_tagIs, hfalse])
    rw [hall] at hbad
    cases hbad

/-- Every failure retained by a missed conditional handler fits the checker's actual
error bound. No restriction on cause multiplicity or predicate shape is assumed. -/
theorem catchIf_miss_error_admits (env : List Val) (test : Term) (bodyError handlerError : Ty)
    (allocated : List String) (cause : CauseV)
    (hadmits : causeAdmits (fun w _ => Val.hasTy w bodyError allocated) bodyError cause = true)
    (hmiss : caughtErrorValue? env test cause = none) :
    causeAdmits (fun w _ => Val.hasTy w
      (catchIfError test env.length bodyError handlerError) allocated)
      (catchIfError test env.length bodyError handlerError) cause = true := by
  unfold catchIfError
  split
  · rename_i htrue
    apply causeAdmits_of_firstErrorValue_none cause bodyError handlerError allocated hadmits
    cases hvalue : firstErrorValue? cause with
    | none => rfl
    | some value =>
      simp [caughtErrorValue?, hvalue, htrue, evalTerm, Lit.toVal] at hmiss
  · split
    · rename_i tag htag
      split
      · rename_i hall
        have hn : causeAdmits (fun w _ => Val.hasTy w bodyError.normalize allocated)
            bodyError.normalize cause = true :=
          causeAdmits_mono_sub (fun w hw => (hasTy_normalize bodyError w allocated).trans hw)
            cause hadmits
        have htest := tagTest?_sound test env.length tag htag
        have hnever := catchIf_miss_allCaught env tag bodyError.normalize allocated cause hall hn
          (htest ▸ hmiss)
        exact causeAdmits_mono_sub (fun _ hw => by cases hw) cause hnever
      · exact causeAdmits_mono_sub
          (fun w hw => Ty.hasTy_join_left bodyError handlerError w allocated hw) cause hadmits
    · exact causeAdmits_mono_sub
        (fun w hw => Ty.hasTy_join_left bodyError handlerError w allocated hw) cause hadmits

/-- A handler's failures also fit the same bound, whichever branch-selection rule is used. -/
theorem catchIf_handler_error_admits (test : Term) (caught : Nat) (bodyError handlerError : Ty)
    (allocated : List String) (cause : CauseV)
    (hadmits : causeAdmits (fun w _ => Val.hasTy w handlerError allocated) handlerError cause = true) :
    causeAdmits (fun w _ => Val.hasTy w (catchIfError test caught bodyError handlerError) allocated)
      (catchIfError test caught bodyError handlerError) cause = true := by
  unfold catchIfError
  split
  · exact hadmits
  · split
    · split
      · exact hadmits
      · exact causeAdmits_mono_sub
          (fun w hw => Ty.hasTy_join_right bodyError handlerError w allocated hw) cause hadmits
    · exact causeAdmits_mono_sub
        (fun w hw => Ty.hasTy_join_right bodyError handlerError w allocated hw) cause hadmits

end Effect4.Program
