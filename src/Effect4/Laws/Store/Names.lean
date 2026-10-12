import Effect4.Store.Carrier.Fold
import Effect4.Laws.Machine.StoreValidity
import Effect4.Laws.Data.ListRel

/-!
# Effect4.Laws.Store.Names

Owner: handles as names, and the one agreement relation of `Store.Val` up to a correspondence of
names. The model, the census and the order are `docs/research/2026-10-11-handles/README.md`; this
module lands its probe `probes/Names.lean` (item 11, steps 1 and 2 of
`docs/research/2026-10-11-machine-models/CODEX-PROMPT.md`).

- A handle's name is its kind byte and its allocation index, as `Val.handle` stores them.
- A correspondence relates the names of a left run to the names of a right run. One run against
  itself is the diagonal of its allocation; a renaming is a graph; two schedules of one program
  relate their allocations.
- `Rel c v v'` says that two values have one shape and that `c` relates their handles position by
  position. It is a fold (`relAlg`), not a new traversal.
- `cata_val_related` is the abstraction theorem of the fold: two algebras that respect a
  correspondence constructor by constructor give related results on related values. It is
  proved once for the signature, and each law below is an instance of it.

Placement:

- Concept: `store-typing` (validity is the diagonal) and `initial-algebras-folds` (the abstraction
  theorem of a generated fold).
- Question: the registry claim `handle-identity-laws`, and the proposed claims `names-parametric`
  (this abstraction theorem, one per signature) and DET-3's `names-equivariant`
  (`Parametric.equivariant`).
- Reach: `Store.Val` and its fold. `Parametric` quantifies over every partial bijection.
- Consumers: `Val.validIn`'s theorems as corollaries of `validIn_iff_diag`; the support bounds of
  `KeyBounded` (`Laws/Machine/Handles.lean`) as `Parametric.support`; DET-3 as
  `Parametric.equivariant`.

What this module does not claim: Lean has no internal parametricity, so a map's parametricity is
a theorem about that map. Nothing here is about the machine's carriers, a store step or a
schedule. The generator does not emit these declarations yet (item 11, step 3).
-/

set_option autoImplicit false

namespace Effect4.Store.Names

open Effect4.Store

universe u

/-- A handle's name: the kind byte and the allocation index that `Val.handle` stores. -/
abbrev Name := UInt8 × Nat

/-! ## Correspondences of names -/

/-- A correspondence relates the names of a left run to the names of a right run. -/
abbrev Corr := Name → Name → Prop

namespace Corr

/-- A correspondence grows: every pair it relates stays related. -/
def le (c c' : Corr) : Prop := ∀ a b, c a b → c' a b

/-- A partial bijection: each name has at most one partner on either side. -/
structure PBij (c : Corr) : Prop where
  right : ∀ a b b', c a b → c a b' → b = b'
  left : ∀ a a' b, c a b → c a' b → a = a'

/-- One run against itself: each allocated name is related to itself. -/
def diag (alloc : Name → Prop) : Corr := fun a b => a = b ∧ alloc a

/-- A renaming's graph. -/
def graph (π : Name → Name) : Corr := fun a b => b = π a

theorem diag_pbij (alloc : Name → Prop) : (diag alloc).PBij :=
  ⟨fun _ _ _ h h' => h.1.symm.trans h'.1, fun _ _ _ h h' => h.1.trans h'.1.symm⟩

theorem graph_pbij {π : Name → Name} (injective : ∀ a a', π a = π a' → a = a') :
    (graph π).PBij :=
  ⟨fun _ _ _ h h' => h.trans h'.symm, fun _ _ _ h h' => injective _ _ (h.symm.trans h')⟩

/-- Relate one more pair. -/
def extend (c : Corr) (a b : Name) : Corr := fun x y => c x y ∨ (x = a ∧ y = b)

theorem le_extend (c : Corr) (a b : Name) : c.le (c.extend a b) := fun _ _ h => Or.inl h

/-- Minting on both sides keeps a partial bijection when both names are fresh. -/
theorem PBij.extend {c : Corr} (hc : c.PBij) {a b : Name} (freshLeft : ∀ y, ¬ c a y)
    (freshRight : ∀ x, ¬ c x b) : (c.extend a b).PBij := by
  constructor
  · intro x y y' h h'
    rcases h with h | ⟨rfl, rfl⟩ <;> rcases h' with h' | ⟨hx, rfl⟩
    · exact hc.right _ _ _ h h'
    · exact absurd (hx ▸ h) (freshLeft y)
    · exact absurd h' (freshLeft y')
    · rfl
  · intro x x' y h h'
    rcases h with h | ⟨rfl, rfl⟩ <;> rcases h' with h' | ⟨rfl, hy⟩
    · exact hc.left _ _ _ h h'
    · exact absurd (hy ▸ h) (freshRight x)
    · exact absurd h' (freshRight x')
    · rfl

/-- An equality test on names answers the same on both sides of a partial bijection. So a lookup
by handle respects such a correspondence, and correspondences are partial bijections. -/
theorem PBij.eq_iff {c : Corr} (hc : c.PBij) {a a' b b' : Name} (h : c a b) (h' : c a' b') :
    a = a' ↔ b = b' := by
  constructor
  · rintro rfl
    exact hc.right _ _ _ h h'
  · rintro rfl
    exact hc.left _ _ _ h h'

end Corr

/-! ## Agreement up to a correspondence, as a fold -/

/-- The relation's carrier: a value related to the values it agrees with. -/
abbrev RelCarrier : ValFam → Type
  | .val => Val → Prop

/-- The algebra of agreement up to `c`: one constructor and payload, handles related by `c`, and
children related position by position. -/
def relAlg (c : Corr) : ValAlgebra RelCarrier where
  val_unit := fun v => v = .unit
  val_bool b := fun v => v = .bool b
  val_nat n := fun v => v = .nat n
  val_str s := fun v => v = .str s
  val_bytes bs := fun v => v = .bytes bs
  val_list rs := fun
    | .list ys => ListRel (fun r y => r y) rs ys
    | _ => False
  val_pair r s := fun
    | .pair a b => r a ∧ s b
    | _ => False
  val_none := fun v => v = .none
  val_some r := fun
    | .some a => r a
    | _ => False
  val_ctor i rs := fun
    | .ctor j ys => i = j ∧ ListRel (fun r y => r y) rs ys
    | _ => False
  val_ref k d := fun v => v = .ref k d
  val_handle k n := fun
    | .handle k' n' => c (k, n) (k', n')
    | _ => False
  val_negInt n := fun v => v = .negInt n
  val_float b := fun v => v = .float b

/-- Two values agree up to the correspondence of their handles. -/
def Rel (c : Corr) (v v' : Val) : Prop := cata_val (relAlg c) v v'

theorem Rel.list_iff {c : Corr} {xs ys : List Val} :
    Rel c (.list xs) (.list ys) ↔ ListRel (fun r y => r y) (xs.map (Rel c)) ys := by
  simp only [Rel, cata_val_list]
  rfl

theorem Rel.ctor_iff {c : Corr} {i j : Nat} {xs ys : List Val} :
    Rel c (.ctor i xs) (.ctor j ys) ↔ i = j ∧ ListRel (fun r y => r y) (xs.map (Rel c)) ys := by
  simp only [Rel, cata_val_ctor]
  rfl

/-! ## The abstraction theorem of the fold -/

/-- Two algebras respect a correspondence: each constructor maps related arguments to related
results, and a handle leaf is related when the correspondence relates its names. -/
structure Related (c : Corr) {R₁ R₂ : ValFam → Type u} (alg₁ : ValAlgebra R₁)
    (alg₂ : ValAlgebra R₂) (S : R₁ .val → R₂ .val → Prop) : Prop where
  unit : S alg₁.val_unit alg₂.val_unit
  bool : ∀ b, S (alg₁.val_bool b) (alg₂.val_bool b)
  nat : ∀ n, S (alg₁.val_nat n) (alg₂.val_nat n)
  str : ∀ s, S (alg₁.val_str s) (alg₂.val_str s)
  bytes : ∀ bs, S (alg₁.val_bytes bs) (alg₂.val_bytes bs)
  list : ∀ xs ys, ListRel S xs ys → S (alg₁.val_list xs) (alg₂.val_list ys)
  pair : ∀ a a' b b', S a a' → S b b' → S (alg₁.val_pair a b) (alg₂.val_pair a' b')
  none : S alg₁.val_none alg₂.val_none
  some : ∀ a a', S a a' → S (alg₁.val_some a) (alg₂.val_some a')
  ctor : ∀ i xs ys, ListRel S xs ys → S (alg₁.val_ctor i xs) (alg₂.val_ctor i ys)
  ref : ∀ k d, S (alg₁.val_ref k d) (alg₂.val_ref k d)
  handle : ∀ k n k' n', c (k, n) (k', n') → S (alg₁.val_handle k n) (alg₂.val_handle k' n')
  negInt : ∀ n, S (alg₁.val_negInt n) (alg₂.val_negInt n)
  float : ∀ b, S (alg₁.val_float b) (alg₂.val_float b)

/-- **The abstraction theorem.** Folds by algebras that respect a correspondence map values that
agree up to it to related results. One induction for the signature. -/
theorem cata_val_related {c : Corr} {R₁ R₂ : ValFam → Type u} {alg₁ : ValAlgebra R₁}
    {alg₂ : ValAlgebra R₂} {S : R₁ .val → R₂ .val → Prop} (h : Related c alg₁ alg₂ S) :
    ∀ v v', Rel c v v' → S (cata_val alg₁ v) (cata_val alg₂ v') := by
  intro v
  induction v using Store.Val.ind with
  | unit => intro v' (hr : v' = .unit); subst hr; exact h.unit
  | bool b => intro v' (hr : v' = .bool b); subst hr; exact h.bool b
  | nat n => intro v' (hr : v' = .nat n); subst hr; exact h.nat n
  | str s => intro v' (hr : v' = .str s); subst hr; exact h.str s
  | bytes bs => intro v' (hr : v' = .bytes bs); subst hr; exact h.bytes bs
  | none => intro v' (hr : v' = .none); subst hr; exact h.none
  | ref k d => intro v' (hr : v' = .ref k d); subst hr; exact h.ref k d
  | negInt n => intro v' (hr : v' = .negInt n); subst hr; exact h.negInt n
  | float b => intro v' (hr : v' = .float b); subst hr; exact h.float b
  | handle k n =>
    intro v' hr
    cases v' with
    | handle k' n' => exact h.handle k n k' n' hr
    | _ => exact False.elim hr
  | some a ih =>
    intro v' hr
    cases v' with
    | some a' => exact h.some _ _ (ih a' hr)
    | _ => exact False.elim hr
  | pair a b iha ihb =>
    intro v' hr
    cases v' with
    | pair a' b' => exact h.pair _ _ _ _ (iha a' hr.1) (ihb b' hr.2)
    | _ => exact False.elim hr
  | list xs ih =>
    intro v' hr
    cases v' with
    | list ys =>
      rw [cata_val_list, cata_val_list]
      exact h.list _ _ (ListRel.of_map_mem (fun x member y related => ih x member y related)
        (ListRel.of_map_left (r := fun r y => r y) (f := Rel c) (Rel.list_iff.mp hr)))
    | _ => exact False.elim hr
  | ctor i xs ih =>
    intro v' hr
    cases v' with
    | ctor j ys =>
      obtain ⟨same, children⟩ := Rel.ctor_iff.mp hr
      subst same
      rw [cata_val_ctor, cata_val_ctor]
      exact h.ctor _ _ _ (ListRel.of_map_mem (fun x member y related => ih x member y related)
        (ListRel.of_map_left (r := fun r y => r y) (f := Rel c) children))
    | _ => exact False.elim hr

/-! ## The identity, a renaming and the support, as algebras -/

/-- Renaming handles: the identity algebra with its handle leaf renamed. -/
def renameAlg (π : Name → Name) : ValAlgebra ValSelfCarrier :=
  { ValAlgebra.id with val_handle := fun k n => .handle (π (k, n)).1 (π (k, n)).2 }

/-- Rename every handle of a value. -/
def rename (π : Name → Name) (v : Val) : Val := cata_val (renameAlg π) v

/-- The support algebra: the handles in payload order. -/
def suppAlg : ValAlgebra (fun _ => List Name) where
  val_unit := []
  val_bool _ := []
  val_nat _ := []
  val_str _ := []
  val_bytes _ := []
  val_list rs := rs.flatten
  val_pair a b := a ++ b
  val_none := []
  val_some a := a
  val_ctor _ rs := rs.flatten
  val_ref _ _ := []
  val_handle k n := [(k, n)]
  val_negInt _ := []
  val_float _ := []

/-- `Val.handles` is the support fold. -/
theorem handles_eq_cata (v : Val) : v.handles = cata_val suppAlg v := by
  induction v using Store.Val.ind with
  | list xs ih =>
    rw [cata_val_list]
    simp only [suppAlg]
    induction xs with
    | nil => rfl
    | cons x rest ihRest =>
      simp only [Val.handles, Val.handlesList, List.map_cons, List.flatten_cons]
      rw [ih x List.mem_cons_self]
      exact congrArg _ (ihRest fun x' member => ih x' (List.mem_cons_of_mem x member))
  | pair a b iha ihb => simp only [Val.handles, cata_val_pair, iha, ihb, suppAlg]
  | some a ih => simp only [Val.handles, cata_val_some, ih, suppAlg]
  | ctor i xs ih =>
    rw [cata_val_ctor]
    simp only [suppAlg]
    induction xs with
    | nil => rfl
    | cons x rest ihRest =>
      simp only [Val.handles, Val.handlesList, List.map_cons, List.flatten_cons]
      rw [ih x List.mem_cons_self]
      exact congrArg _ (ihRest fun x' member => ih x' (List.mem_cons_of_mem x member))
  | _ => rfl

/-- The support algebra respects every correspondence, with handle lists related position by
position. -/
theorem suppAlg_related (c : Corr) : Related c suppAlg suppAlg (ListRel c) where
  unit := .nil
  bool _ := .nil
  nat _ := .nil
  str _ := .nil
  bytes _ := .nil
  list _ _ h := ListRel.flatten h
  pair _ _ _ _ ha hb := ListRel.append ha hb
  none := .nil
  some _ _ h := h
  ctor _ _ _ h := ListRel.flatten h
  ref _ _ := .nil
  handle _ _ _ _ h := .cons h .nil
  negInt _ := .nil
  float _ := .nil

/-- **Support transport.** Values that agree up to `c` have handle lists related by `c`. -/
theorem Rel.handles {c : Corr} {v v' : Val} (h : Rel c v v') : ListRel c v.handles v'.handles := by
  rw [handles_eq_cata, handles_eq_cata]
  exact cata_val_related (suppAlg_related c) v v' h

/-- A renaming algebra and the identity algebra respect every correspondence that relates each
name to its renaming, with equality of the rebuilt values. -/
theorem renameAlg_related {c : Corr} {π : Name → Name} (hπ : ∀ a b, c a b → b = π a) :
    Related c (renameAlg π) ValAlgebra.id (fun a b => b = a) where
  unit := rfl
  bool _ := rfl
  nat _ := rfl
  str _ := rfl
  bytes _ := rfl
  list _ _ h := by
    show Val.list _ = Val.list _
    rw [ListRel.eq_symm h]
  pair _ _ _ _ ha hb := by
    show Val.pair _ _ = Val.pair _ _
    rw [ha, hb]
  none := rfl
  some _ _ h := by
    show Val.some _ = Val.some _
    rw [h]
  ctor _ _ _ h := by
    show Val.ctor _ _ = Val.ctor _ _
    rw [ListRel.eq_symm h]
  ref _ _ := rfl
  handle k n k' n' h := by
    show Val.handle k' n' = Val.handle (π (k, n)).1 (π (k, n)).2
    rw [← hπ _ _ h]
  negInt _ := rfl
  float _ := rfl

/-- The identity fold is the identity. -/
theorem cata_id (v : Val) : cata_val ValAlgebra.id v = v := by
  induction v using Store.Val.ind with
  | list xs ih =>
    rw [cata_val_list]
    show Val.list (xs.map (cata_val ValAlgebra.id)) = Val.list xs
    rw [List.map_congr_left ih, List.map_id']
  | pair a b iha ihb =>
    rw [cata_val_pair]
    show Val.pair _ _ = Val.pair a b
    rw [iha, ihb]
  | some a ih =>
    rw [cata_val_some]
    show Val.some _ = Val.some a
    rw [ih]
  | ctor i xs ih =>
    rw [cata_val_ctor]
    show Val.ctor i (xs.map (cata_val ValAlgebra.id)) = Val.ctor i xs
    rw [List.map_congr_left ih, List.map_id']
  | _ => rfl

/-- Renaming by the identity is the identity algebra. -/
theorem renameAlg_id : renameAlg (fun n => n) = ValAlgebra.id := rfl

/-- **A renaming's graph is functional.** A value agrees up to `graph π` only with its renaming. -/
theorem Rel.graph_eq {π : Name → Name} {v v' : Val} (h : Rel (Corr.graph π) v v') :
    v' = rename π v := by
  have := cata_val_related (renameAlg_related (c := Corr.graph π) fun _ _ same => same) v v' h
  rw [cata_id] at this
  exact this

/-- A value agrees with its renaming up to the renaming's graph. -/
theorem rename_rel (π : Name → Name) (v : Val) : Rel (Corr.graph π) v (rename π v) := by
  induction v using Store.Val.ind with
  | unit => rfl
  | bool _ => rfl
  | nat _ => rfl
  | str _ => rfl
  | bytes _ => rfl
  | none => rfl
  | ref _ _ => rfl
  | negInt _ => rfl
  | float _ => rfl
  | handle k n => rfl
  | some a ih => exact ih
  | pair a b iha ihb => exact ⟨iha, ihb⟩
  | list xs ih =>
    unfold rename
    rw [cata_val_list]
    refine Rel.list_iff.mpr ?_
    exact ListRel.of_map_mem (r := Eq) (fun x member y same => by subst same; exact ih x member)
      (ListRel.of_forall fun _ _ => rfl)
  | ctor i xs ih =>
    unfold rename
    rw [cata_val_ctor]
    refine Rel.ctor_iff.mpr ⟨rfl, ?_⟩
    exact ListRel.of_map_mem (r := Eq) (fun x member y same => by subst same; exact ih x member)
      (ListRel.of_forall fun _ _ => rfl)

/-- **The support of a renaming** is the renamed support. -/
theorem rename_handles (π : Name → Name) (v : Val) : (rename π v).handles = v.handles.map π :=
  ListRel.graph_eq (Rel.handles (rename_rel π v))

/-- The identity algebras respect a correspondence, with agreement up to any larger one. -/
theorem idAlg_related_le {c c' : Corr} (grows : c.le c') :
    Related c ValAlgebra.id ValAlgebra.id (Rel c') where
  unit := rfl
  bool _ := rfl
  nat _ := rfl
  str _ := rfl
  bytes _ := rfl
  list _ _ h := Rel.list_iff.mpr (ListRel.to_map_left h)
  pair _ _ _ _ ha hb := ⟨ha, hb⟩
  none := rfl
  some _ _ h := h
  ctor _ _ _ h := Rel.ctor_iff.mpr ⟨rfl, ListRel.to_map_left h⟩
  ref _ _ := rfl
  handle _ _ _ _ h := grows _ _ h
  negInt _ := rfl
  float _ := rfl

/-- **Kripke monotonicity.** Agreement up to a correspondence survives its growth. -/
theorem Rel.mono {c c' : Corr} (grows : c.le c') {v v' : Val} (h : Rel c v v') : Rel c' v v' := by
  have := cata_val_related (idAlg_related_le grows) v v' h
  rw [cata_id, cata_id] at this
  exact this

/-! ## The handle invariant is the diagonal -/

/-- The diagonal relates a value only to itself. -/
theorem Rel.diag_eq {alloc : Name → Prop} {v v' : Val} (h : Rel (Corr.diag alloc) v v') :
    v' = v := by
  have := cata_val_related
    (renameAlg_related (c := Corr.diag alloc) (π := fun n => n) fun _ _ same => same.1.symm) v v' h
  rw [renameAlg_id, cata_id, cata_id] at this
  exact this

/-- Each child's handles are handles of a list or a constructor application. -/
theorem handles_mem_children {x : Val} {xs : List Val} (member : x ∈ xs) {h : Name}
    (inner : h ∈ x.handles) : h ∈ (Val.list xs).handles ∧ ∀ i, h ∈ (Val.ctor i xs).handles := by
  have flat : h ∈ (xs.map (cata_val suppAlg)).flatten :=
    List.mem_flatten.mpr ⟨_, List.mem_map_of_mem member, handles_eq_cata x ▸ inner⟩
  refine ⟨?_, fun i => ?_⟩
  · rw [handles_eq_cata, cata_val_list]
    exact flat
  · rw [handles_eq_cata, cata_val_ctor]
    exact flat

/-- **Validity is the diagonal.** A value agrees with itself on the diagonal of an allocation
exactly when every handle it names is allocated. -/
theorem Rel.diag_iff {alloc : Name → Prop} {v : Val} :
    Rel (Corr.diag alloc) v v ↔ ∀ h ∈ v.handles, alloc h := by
  constructor
  · intro related h member
    obtain ⟨_, _, same, allocated⟩ := ListRel.mem_left (Rel.handles related) h member
    exact same ▸ allocated
  · intro allocated
    induction v using Store.Val.ind with
    | unit => rfl
    | bool _ => rfl
    | nat _ => rfl
    | str _ => rfl
    | bytes _ => rfl
    | none => rfl
    | ref _ _ => rfl
    | negInt _ => rfl
    | float _ => rfl
    | handle k n => exact ⟨rfl, allocated (k, n) List.mem_cons_self⟩
    | some a ih => exact ih allocated
    | pair a b iha ihb =>
      have split : ∀ h ∈ a.handles ++ b.handles, alloc h := allocated
      exact ⟨iha fun h member => split h (List.mem_append_left _ member),
        ihb fun h member => split h (List.mem_append_right _ member)⟩
    | list xs ih =>
      refine Rel.list_iff.mpr (ListRel.map_self fun x member => ?_)
      exact ih x member fun h inner => allocated h (handles_mem_children member inner).1
    | ctor i xs ih =>
      refine Rel.ctor_iff.mpr ⟨rfl, ListRel.map_self fun x member => ?_⟩
      exact ih x member fun h inner => allocated h ((handles_mem_children member inner).2 i)

private def validityAlg (s : Effect4.Machine.Stores) : ValAlgebra (fun _ => Bool) where
  val_unit := true
  val_bool _ := true
  val_nat _ := true
  val_str _ := true
  val_bytes _ := true
  val_list xs := xs.all id
  val_pair a b := a && b
  val_none := true
  val_some a := a
  val_ctor _ xs := xs.all id
  val_ref _ _ := true
  val_handle kind index := s.handleValid kind index
  val_negInt _ := true
  val_float _ := true

private def validityHom (s : Effect4.Machine.Stores) : ValHom (validityAlg s) where
  f_val := Machine.Val.validIn s
  h_val_unit := rfl
  h_val_bool _ := rfl
  h_val_nat _ := rfl
  h_val_str _ := rfl
  h_val_bytes _ := rfl
  h_val_list xs := by
    rw [Machine.Val.validIn, Machine.Val.validInList_eq_all]
    simp only [validityAlg, List.all_map, Function.comp_def, id_eq]
  h_val_pair _ _ := rfl
  h_val_none := rfl
  h_val_some _ := rfl
  h_val_ctor _ xs := by
    rw [Machine.Val.validIn, Machine.Val.validInList_eq_all]
    simp only [validityAlg, List.all_map, Function.comp_def, id_eq]
  h_val_ref _ _ := rfl
  h_val_handle _ _ := rfl
  h_val_negInt _ := rfl
  h_val_float _ := rfl

private def handleValidityHom (s : Effect4.Machine.Stores) : ValHom (validityAlg s) where
  f_val v := v.handles.all fun h => s.handleValid h.1 h.2
  h_val_unit := rfl
  h_val_bool _ := rfl
  h_val_nat _ := rfl
  h_val_str _ := rfl
  h_val_bytes _ := rfl
  h_val_list xs := by
    simp only [Val.handles, Val.handlesList_eq_flatMap, List.all_flatMap, validityAlg,
      List.all_map, Function.comp_def, id_eq]
  h_val_pair _ _ := by
    simp only [Val.handles, List.all_append, validityAlg]
  h_val_none := rfl
  h_val_some _ := rfl
  h_val_ctor _ xs := by
    simp only [Val.handles, Val.handlesList_eq_flatMap, List.all_flatMap, validityAlg,
      List.all_map, Function.comp_def, id_eq]
  h_val_ref _ _ := rfl
  h_val_handle _ _ := by
    simp only [Val.handles, List.all_cons, List.all_nil, Bool.and_true, validityAlg]
  h_val_negInt _ := rfl
  h_val_float _ := rfl


/-- **The connector to the stores.** `Val.validIn` is the diagonal at the stores' allocation. -/
theorem validIn_iff_diag (s : Effect4.Machine.Stores) (v : Val) :
    Effect4.Machine.Val.validIn s v = true ↔
      Rel (Corr.diag fun h => s.handleValid h.1 h.2 = true) v v := by
  have bridge := (hom_eq_cata_val (validityHom s) v).trans
    (hom_eq_cata_val (handleValidityHom s) v).symm
  change Effect4.Machine.Val.validIn s v = v.handles.all (fun h => s.handleValid h.1 h.2) at bridge
  rw [bridge, List.all_eq_true, Rel.diag_iff]

/-! ## Parametric maps -/

/-- A map is parametric in names: it keeps agreement up to every partial bijection. -/
def Parametric (f : Val → Val) : Prop :=
  ∀ c : Corr, c.PBij → ∀ v v', Rel c v v' → Rel c (f v) (f v')

/-- **Support bound.** A parametric map names only handles its input names: the shape of each
support bound of `KeyBounded` (`Laws/Machine/Handles.lean`). -/
theorem Parametric.support {f : Val → Val} (hf : Parametric f) (v : Val) :
    ∀ h ∈ (f v).handles, h ∈ v.handles := by
  have self : Rel (Corr.diag (· ∈ v.handles)) v v := Rel.diag_iff.mpr fun _ member => member
  exact Rel.diag_iff.mp (hf _ (Corr.diag_pbij _) v v self)

/-- **Equivariance.** A parametric map commutes with every injective renaming: the shape of
DET-3's `names-equivariant`. -/
theorem Parametric.equivariant {f : Val → Val} (hf : Parametric f) {π : Name → Name}
    (injective : ∀ a a', π a = π a' → a = a') (v : Val) : f (rename π v) = rename π (f v) :=
  Rel.graph_eq (hf _ (Corr.graph_pbij injective) v (rename π v) (rename_rel π v))

theorem Parametric.comp {f g : Val → Val} (hf : Parametric f) (hg : Parametric g) :
    Parametric (g ∘ f) :=
  fun c hc v v' h => hg c hc _ _ (hf c hc v v' h)

end Effect4.Store.Names
