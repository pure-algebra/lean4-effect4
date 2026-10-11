import Effect4.Store.Carrier.Fold
import Effect4.Laws.Machine.StoresLaws
import ProofGraph.AxiomAudit

/-!
# Probe: handles as names, worlds as partial bijections of names

A finite probe for `../README.md`. It works on the real value carrier `Store.Val`, its generated
fold `cata_val` and its handle traversal `Val.handles`. It shows five facts:

1. **One relation.** `Rel w v v'`: two values have the same shape, and the world `w` relates
   their handles position by position. It is a fold (`relAlg`), not a new hand traversal.
2. **The abstraction theorem of the fold.** `cata_val_related`: two algebras that respect a world
   constructor by constructor give related results on related values. It is proved once for the
   signature. The support of a renamed value, the functionality of a renaming and the identity
   of the diagonal all follow from it.
3. **The handle invariant is the diagonal.** `Rel (diag alloc) v v` holds exactly when every
   handle of `v` is allocated. At the stores' allocation it is the real `Val.validIn`.
4. **Parametric maps.** A map that preserves `Rel w` at every partial bijection `w` names only
   handles its input names, and it commutes with every injective renaming. The first fact is the
   shape of `KeyBounded`'s fields, the second the shape of the schedule-independence lemma
   `names-equivariant`.
5. **Worlds grow by fresh pairs.** Adding a pair of fresh names keeps a partial bijection, and
   agreement survives the growth (`Rel.mono`, Kripke monotonicity).

It is not a library module. It compiles with `lake env lean` against the built
`Effect4.Laws.Machine.StoresLaws`. Its last command walks its own declarations with the axiom
gate's walk (`ProofGraph.reachedAxiomsMany`), because `#axiom_audit` takes only modules.
-/

set_option autoImplicit false

namespace Effect4.Store.NamesProbe

open Effect4.Store

universe u u₁ u₂ u₃ u₄

/-- A handle's name: the kind byte and the allocation index that `Val.handle` stores. -/
abbrev Name := UInt8 × Nat

/-! ## 1. Worlds -/

/-- A world relates the names of a left run to the names of a right run. -/
abbrev World := Name → Name → Prop

namespace World

/-- A world grows: every pair it relates stays related. -/
def le (w w' : World) : Prop := ∀ a b, w a b → w' a b

/-- A partial bijection: each name has at most one partner on either side. -/
structure PBij (w : World) : Prop where
  right : ∀ a b b', w a b → w a b' → b = b'
  left : ∀ a a' b, w a b → w a' b → a = a'

/-- One run against itself: each allocated name is related to itself. -/
def diag (alloc : Name → Prop) : World := fun a b => a = b ∧ alloc a

/-- A renaming's graph. -/
def graph (π : Name → Name) : World := fun a b => b = π a

theorem diag_pbij (alloc : Name → Prop) : (diag alloc).PBij :=
  ⟨fun _ _ _ h h' => h.1.symm.trans h'.1, fun _ _ _ h h' => h.1.trans h'.1.symm⟩

theorem graph_pbij {π : Name → Name} (injective : ∀ a a', π a = π a' → a = a') :
    (graph π).PBij :=
  ⟨fun _ _ _ h h' => h.trans h'.symm, fun _ _ _ h h' => injective _ _ (h.symm.trans h')⟩

/-- Relate one more pair. -/
def extend (w : World) (a b : Name) : World := fun x y => w x y ∨ (x = a ∧ y = b)

theorem le_extend (w : World) (a b : Name) : w.le (w.extend a b) := fun _ _ h => Or.inl h

/-- **Minting on both sides keeps a partial bijection** when both names are fresh. -/
theorem PBij.extend {w : World} (hw : w.PBij) {a b : Name} (freshLeft : ∀ y, ¬ w a y)
    (freshRight : ∀ x, ¬ w x b) : (w.extend a b).PBij := by
  constructor
  · intro x y y' h h'
    rcases h with h | ⟨rfl, rfl⟩ <;> rcases h' with h' | ⟨hx, rfl⟩
    · exact hw.right _ _ _ h h'
    · exact absurd (hx ▸ h) (freshLeft y)
    · exact absurd h' (freshLeft y')
    · rfl
  · intro x x' y h h'
    rcases h with h | ⟨rfl, rfl⟩ <;> rcases h' with h' | ⟨rfl, hy⟩
    · exact hw.left _ _ _ h h'
    · exact absurd (hy ▸ h) (freshRight x)
    · exact absurd h' (freshRight x')
    · rfl

/-- An equality test on names gives the same answer on both sides of a partial bijection. This
is why lookups by handle respect such worlds, and why worlds are partial bijections and not
arbitrary relations. -/
theorem PBij.eq_iff {w : World} (hw : w.PBij) {a a' b b' : Name} (h : w a b) (h' : w a' b') :
    a = a' ↔ b = b' := by
  constructor
  · rintro rfl
    exact hw.right _ _ _ h h'
  · rintro rfl
    exact hw.left _ _ _ h h'

end World

/-! ## 2. Two lists related position by position -/

/-- Two lists related position by position. -/
def ListRel {α : Type u₁} {β : Type u₂} (r : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => r a b ∧ ListRel r as bs
  | _, _ => False

theorem ListRel.map {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄} {r : α → β → Prop} {s : γ → δ → Prop} {f : α → γ}
    {g : β → δ} : ∀ {xs : List α} {ys : List β}, (∀ x ∈ xs, ∀ y, r x y → s (f x) (g y)) →
    ListRel r xs ys → ListRel s (xs.map f) (ys.map g)
  | [], [], _, _ => trivial
  | x :: _, y :: _, step, ⟨head, tail⟩ =>
    ⟨step x List.mem_cons_self y head,
      ListRel.map (fun x' member => step x' (List.mem_cons_of_mem x member)) tail⟩

theorem ListRel.of_map_left {α : Type u₁} {β : Type u₂} {γ : Type u₃} {r : γ → β → Prop} {f : α → γ} :
    ∀ {xs : List α} {ys : List β}, ListRel r (xs.map f) ys → ListRel (fun x y => r (f x) y) xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨head, tail⟩ => ⟨head, ListRel.of_map_left tail⟩

theorem ListRel.append {α : Type u₁} {β : Type u₂} {r : α → β → Prop} :
    ∀ {xs xs' : List α} {ys ys' : List β}, ListRel r xs ys → ListRel r xs' ys' →
    ListRel r (xs ++ xs') (ys ++ ys')
  | [], _, [], _, _, h' => h'
  | _ :: _, _, _ :: _, _, ⟨head, tail⟩, h' => ⟨head, ListRel.append tail h'⟩

theorem ListRel.eq {α : Type u₁} : ∀ {xs ys : List α}, ListRel Eq xs ys → xs = ys
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨head, tail⟩ => by rw [head, ListRel.eq tail]

theorem ListRel.graph_eq {α : Type u₁} {β : Type u₂} {f : α → β} :
    ∀ {xs : List α} {ys : List β}, ListRel (fun a b => b = f a) xs ys → ys = xs.map f
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨head, tail⟩ => by rw [head, ListRel.graph_eq tail, List.map_cons]

theorem ListRel.mem_left {α : Type u₁} {β : Type u₂} {r : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel r xs ys → ∀ y ∈ ys, ∃ x ∈ xs, r x y
  | [], [], _, _, member => nomatch member
  | x :: _, _ :: _, ⟨head, tail⟩, _, member => by
    cases member with
    | head => exact ⟨x, List.mem_cons_self, head⟩
    | tail _ rest =>
      obtain ⟨x', member', related⟩ := ListRel.mem_left tail _ rest
      exact ⟨x', List.mem_cons_of_mem x member', related⟩

theorem ListRel.mem_right {α : Type u₁} {β : Type u₂} {r : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel r xs ys → ∀ x ∈ xs, ∃ y ∈ ys, r x y
  | [], [], _, _, member => nomatch member
  | _ :: _, y :: _, ⟨head, tail⟩, _, member => by
    cases member with
    | head => exact ⟨y, List.mem_cons_self, head⟩
    | tail _ rest =>
      obtain ⟨y', member', related⟩ := ListRel.mem_right tail _ rest
      exact ⟨y', List.mem_cons_of_mem y member', related⟩

theorem ListRel.to_map_left {α : Type u₁} {β : Type u₂} {γ : Type u₃} {r : γ → β → Prop} {f : α → γ} :
    ∀ {xs : List α} {ys : List β}, ListRel (fun x y => r (f x) y) xs ys → ListRel r (xs.map f) ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨head, tail⟩ => ⟨head, ListRel.to_map_left tail⟩

theorem ListRel.of_forall {α : Type u₁} {r : α → α → Prop} :
    ∀ {xs : List α}, (∀ x ∈ xs, r x x) → ListRel r xs xs
  | [], _ => trivial
  | x :: _, h => ⟨h x List.mem_cons_self, ListRel.of_forall fun x' member =>
      h x' (List.mem_cons_of_mem x member)⟩

/-! ## 3. Agreement up to a world, as a fold -/

/-- The relation's carrier: a value related to the values it agrees with. -/
abbrev RelCarrier : ValFam → Type
  | .val => Val → Prop

/-- The algebra of agreement up to `w`: the same constructor and payload, with handles related by
`w` and children related position by position. -/
def relAlg (w : World) : ValAlgebra RelCarrier where
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
    | .handle k' n' => w (k, n) (k', n')
    | _ => False
  val_negInt n := fun v => v = .negInt n
  val_float b := fun v => v = .float b

/-- Two values agree up to the world's correspondence of handles. -/
def Rel (w : World) (v v' : Val) : Prop := cata_val (relAlg w) v v'

theorem Rel.list_iff {w : World} {xs ys : List Val} :
    Rel w (.list xs) (.list ys) ↔ ListRel (fun r y => r y) (xs.map (Rel w)) ys := by
  simp only [Rel, cata_val_list]
  rfl

theorem Rel.ctor_iff {w : World} {i j : Nat} {xs ys : List Val} :
    Rel w (.ctor i xs) (.ctor j ys) ↔ i = j ∧ ListRel (fun r y => r y) (xs.map (Rel w)) ys := by
  simp only [Rel, cata_val_ctor]
  rfl

/-! ## 4. The abstraction theorem of the fold -/

/-- Two algebras respect a world: each constructor maps related arguments to related results,
and a handle leaf is related exactly when the world relates its names. -/
structure Related (w : World) {R₁ R₂ : ValFam → Type u} (alg₁ : ValAlgebra R₁)
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
  handle : ∀ k n k' n', w (k, n) (k', n') → S (alg₁.val_handle k n) (alg₂.val_handle k' n')
  negInt : ∀ n, S (alg₁.val_negInt n) (alg₂.val_negInt n)
  float : ∀ b, S (alg₁.val_float b) (alg₂.val_float b)

/-- **The abstraction theorem.** Folds by algebras that respect a world map values that agree up
to the world to related results. One induction for the signature; every corollary below is an
instance. -/
theorem cata_val_related {w : World} {R₁ R₂ : ValFam → Type u} {alg₁ : ValAlgebra R₁}
    {alg₂ : ValAlgebra R₂} {S : R₁ .val → R₂ .val → Prop} (h : Related w alg₁ alg₂ S) :
    ∀ v v', Rel w v v' → S (cata_val alg₁ v) (cata_val alg₂ v') := by
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
      exact h.list _ _ (ListRel.map (fun x member y related => ih x member y related)
        (ListRel.of_map_left (r := fun r y => r y) (f := Rel w) (Rel.list_iff.mp hr)))
    | _ => exact False.elim hr
  | ctor i xs ih =>
    intro v' hr
    cases v' with
    | ctor j ys =>
      obtain ⟨same, children⟩ := Rel.ctor_iff.mp hr
      subst same
      rw [cata_val_ctor, cata_val_ctor]
      exact h.ctor _ _ _ (ListRel.map (fun x member y related => ih x member y related)
        (ListRel.of_map_left (r := fun r y => r y) (f := Rel w) children))
    | _ => exact False.elim hr

/-! ## 5. The identity, a renaming and the support, as algebras -/

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

/-- The support algebra respects every world, with handle lists related position by position. -/
theorem suppAlg_related (w : World) : Related w suppAlg suppAlg (ListRel w) where
  unit := trivial
  bool _ := trivial
  nat _ := trivial
  str _ := trivial
  bytes _ := trivial
  list := by
    intro xs ys h
    induction xs generalizing ys with
    | nil => cases ys with
      | nil => exact trivial
      | cons _ _ => exact False.elim h
    | cons x rest ih => cases ys with
      | nil => exact False.elim h
      | cons y rest' => exact ListRel.append h.1 (ih rest' h.2)
  pair _ _ _ _ ha hb := ListRel.append ha hb
  none := trivial
  some _ _ h := h
  ctor := by
    intro _ xs ys h
    induction xs generalizing ys with
    | nil => cases ys with
      | nil => exact trivial
      | cons _ _ => exact False.elim h
    | cons x rest ih => cases ys with
      | nil => exact False.elim h
      | cons y rest' => exact ListRel.append h.1 (ih rest' h.2)
  ref _ _ := trivial
  handle _ _ _ _ h := ⟨h, trivial⟩
  negInt _ := trivial
  float _ := trivial

/-- **Support transport.** Values that agree up to `w` have handle lists related by `w`. -/
theorem Rel.handles {w : World} {v v' : Val} (h : Rel w v v') : ListRel w v.handles v'.handles := by
  rw [handles_eq_cata, handles_eq_cata]
  exact cata_val_related (suppAlg_related w) v v' h

/-- Two lists that agree position by position up to equality are equal. -/
theorem ListRel.eq_symm {α : Type u₁} : ∀ {xs ys : List α}, ListRel (fun a b => b = a) xs ys → ys = xs
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨head, tail⟩ => by rw [head, ListRel.eq_symm tail]

theorem ListRel.map_self {α : Type u₁} {γ : Type u₂} {s : γ → α → Prop} {f : α → γ} :
    ∀ {xs : List α}, (∀ x ∈ xs, s (f x) x) → ListRel s (xs.map f) xs
  | [], _ => trivial
  | x :: _, h => ⟨h x List.mem_cons_self, ListRel.map_self fun x' member =>
      h x' (List.mem_cons_of_mem x member)⟩

/-- A renaming algebra and the identity algebra respect every world that relates each name to
its renaming, with equality of the rebuilt values. -/
theorem renameAlg_related {w : World} {π : Name → Name} (hπ : ∀ a b, w a b → b = π a) :
    Related w (renameAlg π) ValAlgebra.id (fun a b => b = a) where
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
theorem Rel.graph_eq {π : Name → Name} {v v' : Val} (h : Rel (World.graph π) v v') :
    v' = rename π v := by
  have := cata_val_related (renameAlg_related (w := World.graph π) fun _ _ same => same) v v' h
  rw [cata_id] at this
  exact this

/-- A value agrees with its renaming up to the renaming's graph. -/
theorem rename_rel (π : Name → Name) (v : Val) : Rel (World.graph π) v (rename π v) := by
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
    exact ListRel.map (r := Eq) (fun x member y same => by subst same; exact ih x member)
      (ListRel.of_forall fun _ _ => rfl)
  | ctor i xs ih =>
    unfold rename
    rw [cata_val_ctor]
    refine Rel.ctor_iff.mpr ⟨rfl, ?_⟩
    exact ListRel.map (r := Eq) (fun x member y same => by subst same; exact ih x member)
      (ListRel.of_forall fun _ _ => rfl)

/-- **The support of a renaming** is the renamed support. -/
theorem rename_handles (π : Name → Name) (v : Val) : (rename π v).handles = v.handles.map π :=
  ListRel.graph_eq (Rel.handles (rename_rel π v))

/-- The identity algebras respect a world, with agreement up to any larger world. -/
theorem idAlg_related_le {w w' : World} (grows : w.le w') :
    Related w ValAlgebra.id ValAlgebra.id (Rel w') where
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

/-- **Kripke monotonicity.** Agreement up to a world survives the world's growth. -/
theorem Rel.mono {w w' : World} (grows : w.le w') {v v' : Val} (h : Rel w v v') : Rel w' v v' := by
  have := cata_val_related (idAlg_related_le grows) v v' h
  rw [cata_id, cata_id] at this
  exact this

/-! ## 6. The handle invariant is the diagonal -/

/-- The diagonal relates a value only to itself. -/
theorem Rel.diag_eq {alloc : Name → Prop} {v v' : Val} (h : Rel (World.diag alloc) v v') :
    v' = v := by
  have := cata_val_related
    (renameAlg_related (w := World.diag alloc) (π := fun n => n) fun _ _ same => same.1.symm) v v' h
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
    Rel (World.diag alloc) v v ↔ ∀ h ∈ v.handles, alloc h := by
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

/-- **The connector to the stores.** The real `Val.validIn` is the diagonal at the stores'
allocation. -/
theorem validIn_iff_diag (s : Effect4.Machine.Stores) (v : Val) :
    Effect4.Machine.Val.validIn s v = true ↔
      Rel (World.diag fun h => s.handleValid h.1 h.2 = true) v v := by
  rw [Effect4.Machine.Val.validIn_eq_handles, List.all_eq_true, Rel.diag_iff]

/-! ## 7. Parametric maps -/

/-- A map is parametric in names: it keeps agreement up to every partial bijection. -/
def Parametric (f : Val → Val) : Prop :=
  ∀ w : World, w.PBij → ∀ v v', Rel w v v' → Rel w (f v) (f v')

/-- **Support bound.** A parametric map names only handles its input names: the shape of every
`KeyBounded` field of `Laws/Machine/Handles.lean`. -/
theorem Parametric.support {f : Val → Val} (hf : Parametric f) (v : Val) :
    ∀ h ∈ (f v).handles, h ∈ v.handles := by
  have self : Rel (World.diag (· ∈ v.handles)) v v := Rel.diag_iff.mpr fun _ member => member
  exact Rel.diag_iff.mp (hf _ (World.diag_pbij _) v v self)

/-- **Equivariance.** A parametric map commutes with every injective renaming: the shape of the
schedule-independence lemma `names-equivariant`. -/
theorem Parametric.equivariant {f : Val → Val} (hf : Parametric f) {π : Name → Name}
    (injective : ∀ a a', π a = π a' → a = a') (v : Val) : f (rename π v) = rename π (f v) :=
  Rel.graph_eq (hf _ (World.graph_pbij injective) v (rename π v) (rename_rel π v))

theorem Parametric.comp {f g : Val → Val} (hf : Parametric f) (hg : Parametric g) :
    Parametric (g ∘ f) :=
  fun w hw v v' h => hg w hw _ _ (hf w hw v v' h)

/-- A real map, parametric by the abstraction theorem: wrapping a value as an exit's success
payload (`ctor 0 [v]`). -/
example : Parametric fun v => .ctor 0 [v] :=
  fun _ _ _ _ h => Rel.ctor_iff.mpr ⟨rfl, ⟨h, trivial⟩⟩

/-- A control: a map that invents a handle is not parametric. -/
example : ¬ Parametric fun _ => .handle 1 0 := by
  intro hf
  have bound := Parametric.support hf .unit (1, 0) List.mem_cons_self
  exact nomatch bound

end Effect4.Store.NamesProbe

/-! ## The audit: every declaration of this probe, by the gate's walk -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.map₂.toList.filterMap fun (n, _) =>
    if (`Effect4.Store.NamesProbe).isPrefixOf n && !n.isInternal then some n else none
  let (results, _) := ProofGraph.reachedAxiomsMany env names.toArray {} (ProofGraph.isGoal env)
  let mut outside : Array Name := #[]
  for (n, r) in names.toArray.zip results do
    match r with
    | none => outside := outside.push n
    | some reached =>
      if reached.any (fun a => !ProofGraph.trustedAxioms.contains a) then outside := outside.push n
  unless outside.isEmpty do
    throwError m!"probe audit: outside [propext, Quot.sound]: {outside}"
  logInfo m!"probe audit: {names.length} declarations within [propext, Quot.sound]"
