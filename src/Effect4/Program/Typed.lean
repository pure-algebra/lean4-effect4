import Effect4.Program.Native

/-! Executable value admission lives below Laws so the application API can use it.
The associated inversions and term-typing proofs stay in `Laws/Program/Typed.lean`. -/

namespace Effect4.Program
open Effect4 Effect4.Machine

/-- The handle spellings the internal kinds own, each defined once beside its type
(`NativeOp.refTy`, `NativeOp.deferredTy`, `Ty.scope`, `Ty.context`). The `hasTy` arms below
read the same names, so this list and those arms cannot drift apart. -/
def internalHandleTargets : List String :=
  [NativeOp.refTarget, NativeOp.deferredTarget, Ty.scopeTarget, Ty.contextTarget]

/-- An external allocation may not reuse an internal spelling: a byte-7 handle would
otherwise read as a Ref, Deferred, Scope or Context handle by its target alone. -/
def externalHandleTarget (target : String) : Bool :=
  !internalHandleTargets.contains target

/-- Which values inhabit which types of the native cut (plan §2.1, ENSURES 1), by the type.
The scalars against the carrier's own frames; a handle against the spelling of its kind byte
(`HandleKind`, `Machine/Value.lean`): `Val.cell` against `NativeOp.refTy`, `Val.promise`
against `NativeOp.deferredTy` (`Native.lean`), `Val.scopeHandle` against `Ty.scope`, and a
context — a value `Val.context?` reads back — against `Ty.context` (`Eff.lean`); the fiber
handle against `.fiberOf`, and a snapshot of fiber handles (`Val.snapshot?`) against a `.list`
of them; a reified exit against `.exitOf` — a failure's cause must read back and every typed
failure must inhabit its error column (DI-62); a reified cause against `.causeOf` by the same
error fold; the two-cell `list` `Val.tuple` builds (`Native.lean`)
against `.prod`; a `list` against `.list` when every member does; a union as the disjunction
of its members; a string against the carrier's `str` frame and an option against its `none`
and `some` frames (DB-15). An external handle at byte 7 must name its exact target
in the supplied allocation table; the default empty table admits none. Every other
pair is a refusal named in the module header. -/
def Val.hasTy (v : Val) (ty : Ty) (allocated : List String := []) : Bool :=
  match ty with
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => Val.hasTy x inner allocated
    | _ => false
  | .handle target =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => target == NativeOp.refTarget
      | some .promise => target == NativeOp.deferredTarget
      | some .scope => target == Ty.scopeTarget
      | some .external => externalHandleTarget target && allocated[index]? == some target
      | _ => false
    | _ => target == Ty.contextTarget && (Val.context? v).isSome
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  | .exitOf a e =>
    match v with
    | Val.exitOk x => Val.hasTy x a allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmits (fun w _ => Val.hasTy w e allocated) e c
      | none => false
    | _ => false
  | .causeOf e =>
    match Val.cause? v with
    | some c => causeAdmits (fun w _ => Val.hasTy w e allocated) e c
    | none => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => Val.hasTy x ta allocated && Val.hasTy y tb allocated
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => Val.hasTy (Val.fiber id) ty allocated)
      | none => false
    | .list values => values.all fun x => Val.hasTy x ty allocated
    | _ => false
  | .union l r => Val.hasTy v l allocated || Val.hasTy v r allocated
  | .lit value => match v with | .str s => s == value | _ => false
  | .never => false
  | .int => false
  | .except _ _ => false

/-- The typed error part of a completion; defects and interruptions stay outside `E`.
This is the shared reason fold at the default empty allocation table. -/
def errAdmits (ty : Ty) : Reason Err Defect FiberId Ann → Bool :=
  reasonAdmits (fun v t => Val.hasTy v t) ty

/-- Membership of a reified cause at the public, default-allocation interface. The recursive
`Val.hasTy` arms close over their own allocation table and use the same cause fold. -/
def hasTyCause (v : Val) (e : Ty) : Bool :=
  match Val.cause? v with
  | some c => causeAdmits (fun w t => Val.hasTy w t) e c
  | none => false

theorem list_all_mono {α : Type _} {p q : α → Bool} (l : List α)
    (hpq : ∀ x, p x = true → q x = true) (hl : l.all p = true) : l.all q = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.all_cons, Bool.and_eq_true_iff] at hl ⊢
    exact ⟨hpq x hl.1, ih hl.2⟩

theorem reasonAdmits_mono_sub {m1 m2 : Val → Ty → Bool} {e1 e2 : Ty}
    (hm : ∀ w, m1 w e1 = true → m2 w e2 = true) (r : Reason Err Defect FiberId Ann) :
    reasonAdmits m1 e1 r = true → reasonAdmits m2 e2 r = true := by
  cases r with
  | fail e ann =>
    simp only [reasonAdmits]
    split <;> intro h
    · exact hm _ h
    · contradiction
  | die _ _ => simp [reasonAdmits]
  | interrupt _ _ => simp [reasonAdmits]

theorem causeAdmits_mono_sub {m1 m2 : Val → Ty → Bool} {e1 e2 : Ty}
    (hm : ∀ w, m1 w e1 = true → m2 w e2 = true) (c : CauseV) :
    causeAdmits m1 e1 c = true → causeAdmits m2 e2 c = true := by
  simp only [causeAdmits]
  intro h
  exact list_all_mono c.reasons (fun r => reasonAdmits_mono_sub hm r) h

/-- The subtype relation on `Ty` respects value typing (`hasTy`). If `Ty.sub a b = true`
and value `v` has type `a`, then `v` also has type `b`. -/
theorem hasTy_sub (a b : Ty) (v : Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true := by
  if heq : a = b then
    subst heq
    exact hv
  else
    cases a with
    | never => simp [Val.hasTy] at hv
    | int => simp [Val.hasTy] at hv
    | except _ _ => simp [Val.hasTy] at hv
    | union a1 a2 =>
      rw [Ty.sub_union_left a1 a2 b heq] at hsub
      obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
      simp only [Val.hasTy, Bool.or_eq_true] at hv
      cases hv with
      | inl h => exact hasTy_sub a1 b v allocated h1 h
      | inr h => exact hasTy_sub a2 b v allocated h2 h
    | lit s =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.lit s) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.lit s) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.lit s) b2 v allocated h2 hv)
      | string =>
        cases v with
        | str s' => rfl
        | _ => simp [Val.hasTy] at hv
      | never | unit | nat | int | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | option a' =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.option a') b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.option a') b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.option a') b2 v allocated h2 hv)
      | option b' =>
        rw [Ty.sub_option_of_ne a' b' heq] at hsub
        dsimp only [Val.hasTy] at hv ⊢
        split at hv <;> try contradiction
        · rfl
        · rename_i x
          exact hasTy_sub a' b' x allocated hsub hv
      | never | unit | nat | int | string | bool | handle _ | lit _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | list a' =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.list a') b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.list a') b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.list a') b2 v allocated h2 hv)
      | list b' =>
        rw [Ty.sub_list_of_ne a' b' heq] at hsub
        dsimp only [Val.hasTy] at hv ⊢
        split at hv <;> try contradiction
        · split at hv <;> try contradiction
          exact list_all_mono _ (fun id => hasTy_sub a' b' (Val.fiber id) allocated hsub) hv
        · rename_i vs
          exact list_all_mono vs (fun x => hasTy_sub a' b' x allocated hsub) hv
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | prod a1 a2 =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.prod a1 a2) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.prod a1 a2) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.prod a1 a2) b2 v allocated h2 hv)
      | prod b1 b2 =>
        rw [Ty.sub_prod_of_ne a1 a2 b1 b2 heq] at hsub
        obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
        dsimp only [Val.hasTy] at hv ⊢
        split at hv <;> try contradiction
        rename_i x y
        simp only [Bool.and_eq_true_iff] at hv ⊢
        exact ⟨hasTy_sub a1 b1 x allocated h1 hv.1, hasTy_sub a2 b2 y allocated h2 hv.2⟩
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | exitOf a1 e1 =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.exitOf a1 e1) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.exitOf a1 e1) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.exitOf a1 e1) b2 v allocated h2 hv)
      | exitOf a2 e2 =>
        rw [Ty.sub_exitOf_of_ne a1 e1 a2 e2 heq] at hsub
        obtain ⟨ha, he⟩ := Bool.and_eq_true_iff.mp hsub
        dsimp only [Val.hasTy] at hv ⊢
        split at hv
        · exact hasTy_sub a1 a2 _ allocated ha hv
        · split at hv <;> try contradiction
          exact causeAdmits_mono_sub (fun w hw => hasTy_sub e1 e2 w allocated he hw) _ hv
        · contradiction
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | causeOf e1 =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.causeOf e1) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.causeOf e1) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.causeOf e1) b2 v allocated h2 hv)
      | causeOf e2 =>
        rw [Ty.sub_causeOf_of_ne e1 e2 heq] at hsub
        dsimp only [Val.hasTy] at hv ⊢
        split at hv <;> try contradiction
        exact causeAdmits_mono_sub (fun w hw => hasTy_sub e1 e2 w allocated hsub hw) _ hv
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | fiberOf a1 e1 =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.fiberOf a1 e1) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.fiberOf a1 e1) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.fiberOf a1 e1) b2 v allocated h2 hv)
      | fiberOf a2 e2 =>
        simp only [Val.hasTy] at hv ⊢
        exact hv
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | unit =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right .unit b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub .unit b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub .unit b2 v allocated h2 hv)
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | nat =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right .nat b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub .nat b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub .nat b2 v allocated h2 hv)
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | string =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right .string b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub .string b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub .string b2 v allocated h2 hv)
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | bool =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right .bool b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub .bool b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub .bool b2 v allocated h2 hv)
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
    | handle target =>
      cases b with
      | union b1 b2 =>
        rw [Ty.sub_union_right (.handle target) b1 b2 rfl] at hsub
        obtain h1 | h2 := Bool.or_eq_true_iff.mp hsub
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inl (hasTy_sub (.handle target) b1 v allocated h1 hv)
        · simp only [Val.hasTy, Bool.or_eq_true]; exact Or.inr (hasTy_sub (.handle target) b2 v allocated h2 hv)
      | never | unit | nat | int | string | bool | handle _ | lit _ | option _ | list _
      | prod _ _ | except _ _ | exitOf _ _ | causeOf _ | fiberOf _ _ =>
        revert hsub; unfold Ty.sub; simp only [heq, ↓reduceIte]; intro h; contradiction
termination_by sizeOf a + sizeOf b

end Effect4.Program
