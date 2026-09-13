import Effect4.Program.Compile
import Effect4.Laws.Program.Typed
import Effect4.Laws.Program.TypeAlgebra

/-!
# Laws.Program.Residual — the tag residual and the single-failure law (part 4, 2026-09-12)

Rows DI-39 (the tag test is the native atom `tagIs`; a `catchIf` whose test is that atom
types its error column as the residual `Ty.diffTag tag` joined with the handler's error) and
DI-17 (the residual is a fidelity claim to rc.112's printed type; its adequacy statement
carries the single-`Fail` premise). What is proved:

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

/-- Exactly one `Fail` reason (DI-17's premise for the tag residual): every cause the
straight-line fragment produces satisfies it, and it is checkable on a tape. -/
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

/-- `catchIf_miss_admits` (DI-17, the tag residual's adequacy under the single-`Fail`
premise): a cause with exactly one `Fail`, admitted at the body's column `e`, on which the
tag test misses on the compile route (`caughtErrorValue?` answers `none`, so the whole cause
is re-raised), is admitted at the residual. -/
theorem catchIf_miss_admits (env : List Val) (tag : String) (e : Ty) (allocated : List String)
    (cause : CauseV) (hsingle : SingleFail cause)
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
        findSome?_error?_of_le_one cause.reasons (by unfold SingleFail failCount at hsingle; omega)
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

end Effect4.Program
