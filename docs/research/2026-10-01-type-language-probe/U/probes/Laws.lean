import ProbeU.Classes
import Effect4.Laws.Program.Template
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Program.Admits
import Effect4.Laws.Program.Typed.Membership
import Effect4.Schema.Codec

/-!
# Probe U, question 5: laws stated once over the fold family

Three shapes, each on the tree's own definitions:

1. **Fusion** (`cata_fusion_ty`, `ProbeU.Generic`): membership is invariant under
   normalization (`hasTy_normalize`, `Laws/Program/TypeAlgebra.lean:309`) is one fusion square
   per constructor that `normalize` overrides — two (`prod`, `union`) — and nothing for the
   eighteen it rebuilds, which the `Commutes` record's `rfl` defaults discharge. Today the law is
   an induction with eight named helper theorems (`hasTy_normalize_never`, `_union`, `_prod`,
   `_option`, `_list`, `_except`, `_exitOf`, `_causeOf`, `TypeAlgebra.lean:214-320`): every
   constructor `normalize` rebuilds costs a congruence lemma; under fusion it costs nothing.
2. **An invariant of a table-driven fold, once per layer shape** (`cata_ofLayer_inv`): a
   property every layer preserves holds of the fold. `templateAdmissible_of_closed`
   (`Laws/Program/Template.lean:281`) and its `valueVars` twin are one proof by cases on the
   *number of children* (four cases), whatever the number of constructors.
3. **A monoid homomorphism after a monoid fold** (fusion again): `closed t = (varsOf t).isEmpty`,
   so `varsOf_eq_nil_of_closed` (`Template.lean:285`) is one line.

Every theorem carries `#print axioms`.
-/

set_option autoImplicit false

open Effect4 Effect4.Machine Effect4.Program ProbeU

namespace ProbeU.Laws

/-! ## 1. `Val.hasTy` as a fold, and `hasTy_normalize` as fusion -/

/-- `Val.hasTy`'s arms as a `TyAlgebra` (the production-shaped definition: `Val.hasTy :=
cata_ty hasTyAlg`). The cause arms check the error column through `causeAdmits`, whose type
argument is never read (`causeAdmits_discard_ty`), so the algebra passes `never`. -/
def hasTyAlg : TyAlgebra (fun _ => Val → List String → Bool) where
  ty_never := fun _ _ => false
  ty_unit := fun v _ => match v with | .unit => true | _ => false
  ty_nat := fun v _ => match v with | .nat _ => true | _ => false
  ty_int := fun _ _ => false
  ty_string := fun v _ => match v with | .str _ => true | _ => false
  ty_bool := fun v _ => match v with | .bool _ => true | _ => false
  ty_handle target := fun v allocated =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => target == NativeOp.refTarget
      | some .promise => target == NativeOp.deferredTarget
      | some .scope => target == Ty.scopeTarget
      | some .external => externalHandleTarget target && allocated[index]? == some target
      | _ => false
    | _ => target == Ty.contextTarget && (Val.context? v).isSome
  ty_option inner := fun v allocated =>
    match v with
    | .none => true
    | .some x => inner x allocated
    | _ => false
  ty_list inner := fun v allocated =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => inner (Val.fiber id) allocated)
      | none => false
    | .list values => values.all fun x => inner x allocated
    | _ => false
  ty_prod a b := fun v allocated =>
    match v with
    | .list [x, y] => a x allocated && b y allocated
    | _ => false
  ty_except error value := fun v allocated =>
    match v with
    | .ctor 0 [err] => error err allocated
    | .ctor 1 [val] => value val allocated
    | _ => false
  ty_exitOf a e := fun v allocated =>
    match v with
    | Val.exitOk x => a x allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmits (fun w _ => e w allocated) .never c
      | none => false
    | _ => false
  ty_causeOf e := fun v allocated =>
    match Val.cause? v with
    | some c => causeAdmits (fun w _ => e w allocated) .never c
    | none => false
  ty_fiberOf _ _ := fun v _ => match v with | Value.fiber _ => true | _ => false
  ty_union l r := fun v allocated => l v allocated || r v allocated
  ty_lit value := fun v _ => match v with | .str s => s == value | _ => false
  ty_refOf _ := fun v _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .cell
    | _ => false
  ty_deferredOf _ _ := fun v _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .promise
    | _ => false
  ty_var _ := fun _ _ => false
  ty_unknown := fun _ _ => true

/-- **`Val.hasTy` is the fold of `hasTyAlg`** (proved; two fields read `causeAdmits_discard_ty`). -/
theorem hasTy_eq_cata (t : Ty) : (fun v a => Val.hasTy v t a) = cata_ty hasTyAlg t :=
  hom_eq_cata_ty (alg := hasTyAlg)
    { f_ty := fun s v a => Val.hasTy v s a
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun a e => by
        funext v alloc
        simp only [Val.hasTy, hasTyAlg]
        split
        · rfl
        · split
          · rename_i c hc
            simp only [hc]
            exact causeAdmits_discard_ty (fun w => Val.hasTy w e alloc) e .never c
          · rename_i hc
            simp only [hc]
        · rename_i h0 h1
          split
          · rename_i x
            exact (h0 x rfl).elim
          · rename_i w
            exact (h1 w rfl).elim
          · rfl
      h_ty_causeOf := fun e => by
        funext v alloc
        simp only [Val.hasTy, hasTyAlg]
        split
        · rename_i c hc
          rw [hc]
          exact causeAdmits_discard_ty (fun w => Val.hasTy w e alloc) e .never c
        · rename_i hc
          rw [hc]
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

theorem hasTy_eq (v : Val) (t : Ty) (a : List String) : Val.hasTy v t a = cata_ty hasTyAlg t v a :=
  congrFun (congrFun (hasTy_eq_cata t) v) a

/-- **The two fusion squares `normalize` needs**: at the two constructors it overrides. The
eighteen it rebuilds are the `Commutes` record's `rfl` defaults. -/
theorem normalize_commutes :
    TyAlgebra.Commutes (cata_ty hasTyAlg) Ty.normalize.alg hasTyAlg where
  ty_prod x y := by
    funext v alloc
    show cata_ty hasTyAlg (Ty.ofMembers (Ty.normalizeRow (Ty.productMembers x y)).elems) v alloc =
      cata_ty hasTyAlg (Ty.prod x y) v alloc
    rw [← hasTy_eq, ← hasTy_eq]
    exact (hasTy_ofMembers v _ alloc).trans ((hasTy_normalizeRow v _ alloc).trans
      (hasTy_productMembers v x y alloc))
  ty_union x y := by
    funext v alloc
    show cata_ty hasTyAlg (Ty.ofMembers (Ty.normalizeRow (Ty.members x ++ Ty.members y)).elems) v
      alloc = cata_ty hasTyAlg (Ty.union x y) v alloc
    rw [← hasTy_eq, ← hasTy_eq]
    rw [hasTy_ofMembers, hasTy_normalizeRow, List.any_append, hasTy_members, hasTy_members]
    rfl

/-- **`hasTy_normalize`, by fusion** (proved): the production statement, from the two squares. -/
theorem hasTy_normalize' (t : Ty) (v : Val) (allocated : List String) :
    Val.hasTy v t.normalize allocated = Val.hasTy v t allocated := by
  rw [hasTy_eq, hasTy_eq v t, Ty.normalize.eq_cata, cata_fusion_ty normalize_commutes]

/-! ## 2. An invariant of a table-driven fold, proved per layer shape -/

/-! The fold of a layer function one layer down (`cata_ofLayer_view`), the termination
measure (`sizeOf_tyKids`) and **the per-layer invariant** (`cata_ofLayer_inv`: a property every
layer keeps holds of the fold, proved once and naming no constructor) are emitted by the patched
generator (`ProbeU.TyFoldExtras`). -/

/-- **No parameter at all implies parameters only below the class, for every class** (proved
by four cases on the number of children). -/
theorem varsUnder_of_closed (ok : ClassRow → Bool) (t : Ty)
    (h : (cata_ty (varsUnder ok) t).1 = true) : (cata_ty (varsUnder ok) t).2 = true := by
  revert h
  refine cata_ofLayer_inv (varsUnderLayer ok) (fun p => p.1 = true → p.2 = true) ?_ t
  intro c l kids hk
  match kids, hk with
  | [], _ => intro _; rfl
  | [a], hk =>
    intro h1
    have ha := hk a (List.mem_singleton.mpr rfl) h1
    simp only [varsUnderLayer] at h1 ⊢
    cases ok (tyClasses.get c) <;> simp only [cond_true, cond_false, h1, ha]
  | [a, b], hk =>
    intro h12
    simp only [varsUnderLayer, Bool.and_eq_true] at h12 ⊢
    have ha := hk a (List.mem_cons_self) h12.1
    have hb := hk b (List.mem_cons_of_mem a List.mem_cons_self) h12.2
    cases ok (tyClasses.get c) <;>
      simp only [cond_true, cond_false, Bool.and_eq_true, ha, hb, h12.1, h12.2, and_self]
  | _ :: _ :: _ :: _, _ => intro _; rfl

/-- The pair is the fold (`MonoidFolds.templateAdmissible_eq`, restated here). -/
theorem templateAdmissible_pair (t : Ty) :
    (cata_ty (varsUnder (·.positional)) t) = (Ty.closed t, Ty.templateAdmissible t) :=
    (hom_eq_cata_ty (alg := varsUnder (·.positional))
      { f_ty := fun s => (Ty.closed s, Ty.templateAdmissible s)
        h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
        h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
        h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
        h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
        h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
        h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
        h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
        h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
        h_ty_unknown := rfl } t).symm

/-- `templateAdmissible_of_closed`, as an instance of the per-layer invariant (proved). -/
theorem templateAdmissible_of_closed' (t : Ty) (h : Ty.closed t = true) :
    Ty.templateAdmissible t = true := by
  have hp := varsUnder_of_closed (·.positional) t
  rw [templateAdmissible_pair] at hp
  exact hp h


/-! ## 2b. Monotonicity of a fold whose algebra is fieldwise monotone, once -/

theorem recCombine_and_some : ∀ (x : Bool) (xs : List Bool),
    recCombine (· && ·) (x :: xs) = some ((x :: xs).all id)
  | x, [] => by simp only [recCombine, List.all_cons, List.all_nil, id_eq, Bool.and_true]
  | x, y :: ys => by
    rw [show recCombine (· && ·) (x :: y :: ys) = (recCombine (· && ·) (y :: ys)).map (x && ·)
      from rfl, recCombine_and_some y ys]
    simp only [Option.map_some, List.all_cons, id_eq]

/-- The `(Bool, &&)` head fold's node is its flag and all its children. -/
theorem nodeThen_and (h : Bool) : ∀ (xs : List Bool), nodeThen (· && ·) h xs = (h && xs.all id)
  | [] => by simp only [nodeThen, recCombine, List.all_nil, Bool.and_true]
  | x :: xs => by simp only [nodeThen, recCombine_and_some]

/-- Two layer folds side by side are one layer fold (fieldwise `rfl`). -/
theorem prod_ofLayer {X Y : Type} (L1 : TyCtor → TyLeaf → List X → X)
    (L2 : TyCtor → TyLeaf → List Y → Y) :
    TyAlgebra.prod (TyAlgebra.ofLayer L1) (TyAlgebra.ofLayer L2) =
      TyAlgebra.ofLayer (fun c l kids => (L1 c l (kids.map (·.1)), L2 c l (kids.map (·.2)))) := rfl

/-- **A column-wise weaker class is a weaker fold**, for every pair of columns (proved once:
the banana split, then the per-layer invariant). -/
theorem allHeads_mono (col₁ col₂ : ClassRow → Bool)
    (hc : ∀ c : TyCtor, col₁ (tyClasses.get c) = true → col₂ (tyClasses.get c) = true) (t : Ty)
    (h : cata_ty (allHeads col₁) t = true) : cata_ty (allHeads col₂) t = true := by
  have hp := cata_prod_ty (allHeads col₁) (allHeads col₂) t
  rw [allHeads, allHeads, TyAlgebra.headAlg, TyAlgebra.headAlg, prod_ofLayer] at hp
  have inv := cata_ofLayer_inv
    (fun c l (kids : List (Bool × Bool)) =>
      (nodeThen (· && ·) (col₁ (tyClasses.get c)) (kids.map (·.1)),
       nodeThen (· && ·) (col₂ (tyClasses.get c)) (kids.map (·.2))))
    (fun p => p.1 = true → p.2 = true)
    (by
      intro c _ kids hk h1
      simp only [nodeThen_and, Bool.and_eq_true, List.all_eq_true, List.mem_map, id_eq] at h1 ⊢
      refine ⟨hc c h1.1, ?_⟩
      rintro _ ⟨k, hkm, rfl⟩
      exact hk k hkm (h1.2 k.1 ⟨k, hkm, rfl⟩))
    t
  rw [hp] at inv
  exact inv h

/-- The codec's class lies inside the handle-free class, row by row (`decide` per tag). -/
theorem codec_le_handleFree : ∀ c : TyCtor,
    (tyClasses.get c).codec = true → (tyClasses.get c).handleFree = true := by
  intro c
  cases c <;> decide

/-- `Codec.isSupported` is the codec column's head fold (as `MonoidFolds.isSupported_eq`). -/
theorem isSupported_eq' (t : Ty) : Schema.Codec.isSupported t = cata_ty (allHeads (·.codec)) t :=
    hom_eq_cata_ty (alg := allHeads (·.codec))
      { f_ty := Schema.Codec.isSupported
        h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
        h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
        h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
        h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
        h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
        h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
        h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
        h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
        h_ty_unknown := rfl } t

theorem handleFreeAlg_eq' : Typed.handleFreeAlg = allHeads (·.handleFree) := rfl

/-- **A type the JSON codec supports holds no handle** (proved; a law the tree does not state,
one line from the generic monotonicity and a column inclusion). -/
theorem handleFree_of_isSupported (t : Ty) (h : Schema.Codec.isSupported t = true) :
    Typed.handleFree t = true := by
  rw [isSupported_eq'] at h
  rw [Typed.handleFree, handleFreeAlg_eq']
  exact allHeads_mono (·.codec) (·.handleFree) codec_le_handleFree t h

/-! ## 3. A monoid homomorphism after a monoid fold -/

theorem isEmpty_append {α : Type} (a b : List α) : (a ++ b).isEmpty = (a.isEmpty && b.isEmpty) := by
  cases a <;> rfl

/-- `List.isEmpty` is a monoid homomorphism `(List Nat, ++, []) → (Bool, &&, true)`, so it
commutes with the two head folds at the same column: fourteen squares by `rfl`, six by the
homomorphism law. -/
theorem isEmpty_commutes :
    TyAlgebra.Commutes List.isEmpty paramsAlg (allHeads fun r => !r.param) where
  ty_prod a b := isEmpty_append a b
  ty_except a b := isEmpty_append a b
  ty_exitOf a b := isEmpty_append a b
  ty_fiberOf a b := isEmpty_append a b
  ty_union a b := isEmpty_append a b
  ty_deferredOf a b := isEmpty_append a b

/-- **`closed` is `varsOf` emptied** (proved, by fusion). -/
theorem closed_eq_isEmpty (t : Ty) : Ty.closed t = (Ty.varsOf t).isEmpty := by
  rw [closed_eq', varsOf_eq', cata_fusion_ty isEmpty_commutes]
where
  closed_eq' (t : Ty) : Ty.closed t = cata_ty (allHeads fun r => !r.param) t :=
    hom_eq_cata_ty (alg := allHeads fun r => !r.param)
      { f_ty := Ty.closed
        h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
        h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
        h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
        h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
        h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
        h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
        h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
        h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
        h_ty_unknown := rfl } t
  varsOf_eq' (t : Ty) : Ty.varsOf t = cata_ty paramsAlg t :=
    hom_eq_cata_ty (alg := paramsAlg)
      { f_ty := Ty.varsOf
        h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
        h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
        h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
        h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
        h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
        h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
        h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
        h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
        h_ty_unknown := rfl } t

/-- `varsOf_eq_nil_of_closed`, as a one-line corollary (proved). -/
theorem varsOf_eq_nil_of_closed' (t : Ty) (h : Ty.closed t = true) : Ty.varsOf t = [] :=
  List.isEmpty_iff.mp ((closed_eq_isEmpty t) ▸ h)

end ProbeU.Laws

#print axioms ProbeU.Laws.hasTy_eq_cata
#print axioms ProbeU.Laws.hasTy_eq
#print axioms ProbeU.Laws.normalize_commutes
#print axioms ProbeU.Laws.hasTy_normalize'
#print axioms ProbeU.cata_ofLayer_view
#print axioms ProbeU.sizeOf_tyKids
#print axioms ProbeU.cata_ofLayer_inv
#print axioms ProbeU.Laws.varsUnder_of_closed
#print axioms ProbeU.Laws.templateAdmissible_pair
#print axioms ProbeU.Laws.templateAdmissible_of_closed'
#print axioms ProbeU.Laws.recCombine_and_some
#print axioms ProbeU.Laws.nodeThen_and
#print axioms ProbeU.Laws.prod_ofLayer
#print axioms ProbeU.Laws.allHeads_mono
#print axioms ProbeU.Laws.codec_le_handleFree
#print axioms ProbeU.Laws.isSupported_eq'
#print axioms ProbeU.Laws.handleFreeAlg_eq'
#print axioms ProbeU.Laws.handleFree_of_isSupported
#print axioms ProbeU.Laws.isEmpty_append
#print axioms ProbeU.Laws.isEmpty_commutes
#print axioms ProbeU.Laws.closed_eq_isEmpty
#print axioms ProbeU.Laws.varsOf_eq_nil_of_closed'
