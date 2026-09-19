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
  -- a cell or a promise handle, coarse as every handle is (DI-17, decisions row 44): what it
  -- holds is typed by the world's tables
  | .refOf _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .cell
    | _ => false
  | .deferredOf _ _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .promise
    | _ => false
  -- a row template's parameter: no value inhabits it
  | .var _ => false
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
  | .unknown => true
  | .int => false
  | .except error value =>
    match v with
    | .ctor 0 [err] => Val.hasTy err error allocated
    | .ctor 1 [val] => Val.hasTy val value allocated
    | _ => false

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
and value `v` has type `a`, then `v` also has type `b`.

The proof is `fun_induction Ty.sub`, so its case list is `sub`'s own arm list: sixteen cases,
one per rule, with the catch-all a single case whose `hsub` is `false = true`. That is why
there is one `union` block rather than one per constructor of the left type, one line for the
top rather than an alternative in every mismatch arm, and no `first`: the shape of the
induction, not the discipline of the writer, is what keeps a new constructor from touching it
(tooling plan 1.5). Statement and argument order are unchanged — twenty-five call sites in
five files read it. -/
theorem hasTy_sub (a b : Ty) (v : Val) (allocated : List String := [])
    (hsub : Ty.sub a b = true) (hv : Val.hasTy v a allocated = true) :
    Val.hasTy v b allocated = true := by
  fun_induction Ty.sub a b generalizing v
  -- the reflexive guard
  case case1 => exact hv
  -- `never` is below everything and admits nothing
  case case2 => exact Bool.noConfusion hv
  -- a union on the left is a conjunction: the value is in one member, and both are below `b`
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    simp only [Val.hasTy, Bool.or_eq_true] at hv
    exact hv.elim (fun h => iha v h1 h) (fun h => ihb v h2 h)
  -- a union on the right is a choice: whichever member `a` is below, the value lands in it
  case case4 a b1 b2 _ _ _ iha ihb =>
    simp only [Val.hasTy, Bool.or_eq_true]
    exact (Bool.or_eq_true_iff.mp hsub).elim
      (fun h => Or.inl (iha v h hv)) (fun h => Or.inr (ihb v h hv))
  -- the top (decisions row 46): every value inhabits `unknown`. One line, not sixteen
  case case5 => rfl
  -- the literal rule: a string frame is a string frame
  case case6 =>
    cases v
    case str => rfl
    all_goals exact Bool.noConfusion hv
  case case7 x y _ ih =>
    dsimp only [Val.hasTy] at hv ⊢
    split at hv
    · rfl
    · rename_i w
      exact ih w hsub hv
    · exact Bool.noConfusion hv
  case case8 x y _ ih =>
    dsimp only [Val.hasTy] at hv ⊢
    split at hv
    · split at hv
      · exact list_all_mono _ (fun id => ih (Val.fiber id) hsub) hv
      · exact Bool.noConfusion hv
    · rename_i vs
      exact list_all_mono vs (fun w => ih w hsub) hv
    · exact Bool.noConfusion hv
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    dsimp only [Val.hasTy] at hv ⊢
    split at hv
    · rename_i x y
      simp only [Bool.and_eq_true_iff] at hv ⊢
      exact ⟨iha x h1 hv.1, ihb y h2 hv.2⟩
    · exact Bool.noConfusion hv
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    dsimp only [Val.hasTy] at hv ⊢
    split at hv
    · exact ihe _ h1 hv
    · exact iha _ h2 hv
    · exact Bool.noConfusion hv
  case case11 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    dsimp only [Val.hasTy] at hv ⊢
    split at hv
    · exact iha _ h1 hv
    · split at hv
      · exact causeAdmits_mono_sub (fun w hw => ihe w h2 hw) _ hv
      · exact Bool.noConfusion hv
    · exact Bool.noConfusion hv
  case case12 e1 e2 _ ih =>
    dsimp only [Val.hasTy] at hv ⊢
    split at hv
    · exact causeAdmits_mono_sub (fun w hw => ih w hsub hw) _ hv
    · exact Bool.noConfusion hv
  -- the fiber handle is coarse in `hasTy` (DI-17, decisions row 44): the arms agree
  case case13 => simp only [Val.hasTy] at hv ⊢; exact hv
  -- the cell and promise handles likewise, which is why their `sub` arms are invariant
  case case14 => simp only [Val.hasTy] at hv ⊢; exact hv
  case case15 => simp only [Val.hasTy] at hv ⊢; exact hv
  -- every other pair: `sub` answers `false`, so there is nothing to carry
  case case16 => exact Bool.noConfusion hsub


end Effect4.Program
