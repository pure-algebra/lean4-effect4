/-! Probe for C-P8: the text `tools/Effect4Gen/Fold.lean` would emit for a family whose
recursive children sit under `List`, `Option`, a one-parameter record and a product.

The miniature mirrors every position kind of `Effect4.Representation` / `Effect4.Check` and of
`Effect4.Store.Shape`:
  `List Rep`, `List Chk`, `List (ElemOf Rep)`, `RecAnn Rep` (a record holding `Option (List Rep)`),
  `Option (RecAnn Rep)`, `List (String × Rep)`, `List (String × Nat × List (String × Rep))`. -/

set_option autoImplicit false

universe u v w

structure ElemOf (α : Type u) where
  isOptional : Bool
  type : α
  note : String

structure RecAnn (α : Type u) where
  id : String
  schemas : Option (List α)

mutual
inductive Rep where
  | leaf (n : Nat)
  | susp (checks : List Chk) (thunk : Rep)
  | arr (checks : List Chk) (elements : List (ElemOf Rep)) (rest : List Rep)
  | struct (name : String) (fields : List (String × Rep))
  | sum (name : String) (cases : List (String × Nat × List (String × Rep)))
inductive Chk where
  | filter (ann : RecAnn Rep) (aborted : Bool)
  | group (ann : Option (RecAnn Rep)) (checks : List Chk)
end

/-! ## The functor maps of the containers (emitted once per record; `List`/`Option`/`Prod` are core) -/

def ElemOf.map {α : Type u} {β : Type v} (f : α → β) (e : ElemOf α) : ElemOf β :=
  { isOptional := e.isOptional, type := f e.type, note := e.note }

def RecAnn.map {α : Type u} {β : Type v} (f : α → β) (a : RecAnn α) : RecAnn β :=
  { id := a.id, schemas := a.schemas.map (List.map f) }

/-! ## Family, algebra -/

inductive RepFam where
  | rep
  | chk
deriving DecidableEq, Repr

structure RepAlgebra (R : RepFam → Type u) where
  rep_leaf : Nat → R .rep
  rep_susp : List (R .chk) → R .rep → R .rep
  rep_arr : List (R .chk) → List (ElemOf (R .rep)) → List (R .rep) → R .rep
  rep_struct : String → List (String × R .rep) → R .rep
  rep_sum : String → List (String × Nat × List (String × R .rep)) → R .rep
  chk_filter : RecAnn (R .rep) → Bool → R .chk
  chk_group : Option (RecAnn (R .rep)) → List (R .chk) → R .chk

/-! ## The fold: one helper per distinct nested position type, all in one mutual block -/

mutual
def cata_rep {R : RepFam → Type u} (alg : RepAlgebra R) (node : Rep) : R .rep :=
  match node with
  | .leaf a0 => alg.rep_leaf a0
  | .susp a0 a1 => alg.rep_susp (cata_pos_listChk alg a0) (cata_rep alg a1)
  | .arr a0 a1 a2 =>
    alg.rep_arr (cata_pos_listChk alg a0) (cata_pos_listElem alg a1) (cata_pos_listRep alg a2)
  | .struct a0 a1 => alg.rep_struct a0 (cata_pos_fields alg a1)
  | .sum a0 a1 => alg.rep_sum a0 (cata_pos_cases alg a1)
termination_by structural node
def cata_chk {R : RepFam → Type u} (alg : RepAlgebra R) (node : Chk) : R .chk :=
  match node with
  | .filter a0 a1 => alg.chk_filter (cata_pos_ann alg a0) a1
  | .group a0 a1 => alg.chk_group (cata_pos_optAnn alg a0) (cata_pos_listChk alg a1)
termination_by structural node
def cata_pos_listRep {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List Rep) : List (R .rep) :=
  match xs with
  | [] => []
  | x :: rest => cata_rep alg x :: cata_pos_listRep alg rest
termination_by structural xs
def cata_pos_listChk {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List Chk) : List (R .chk) :=
  match xs with
  | [] => []
  | x :: rest => cata_chk alg x :: cata_pos_listChk alg rest
termination_by structural xs
def cata_pos_elem {R : RepFam → Type u} (alg : RepAlgebra R) (x : ElemOf Rep) : ElemOf (R .rep) :=
  match x with
  | ⟨isOptional, type, note⟩ => ⟨isOptional, cata_rep alg type, note⟩
termination_by structural x
def cata_pos_listElem {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List (ElemOf Rep)) :
    List (ElemOf (R .rep)) :=
  match xs with
  | [] => []
  | x :: rest => cata_pos_elem alg x :: cata_pos_listElem alg rest
termination_by structural xs
def cata_pos_optListRep {R : RepFam → Type u} (alg : RepAlgebra R) (x : Option (List Rep)) :
    Option (List (R .rep)) :=
  match x with
  | none => none
  | some y => some (cata_pos_listRep alg y)
termination_by structural x
def cata_pos_ann {R : RepFam → Type u} (alg : RepAlgebra R) (x : RecAnn Rep) : RecAnn (R .rep) :=
  match x with
  | ⟨id, schemas⟩ => ⟨id, cata_pos_optListRep alg schemas⟩
termination_by structural x
def cata_pos_optAnn {R : RepFam → Type u} (alg : RepAlgebra R) (x : Option (RecAnn Rep)) :
    Option (RecAnn (R .rep)) :=
  match x with
  | none => none
  | some y => some (cata_pos_ann alg y)
termination_by structural x
def cata_pos_field {R : RepFam → Type u} (alg : RepAlgebra R) (x : String × Rep) : String × R .rep :=
  match x with
  | (a, b) => (a, cata_rep alg b)
termination_by structural x
def cata_pos_fields {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List (String × Rep)) :
    List (String × R .rep) :=
  match xs with
  | [] => []
  | x :: rest => cata_pos_field alg x :: cata_pos_fields alg rest
termination_by structural xs
def cata_pos_caseTail {R : RepFam → Type u} (alg : RepAlgebra R) (x : Nat × List (String × Rep)) :
    Nat × List (String × R .rep) :=
  match x with
  | (a, b) => (a, cata_pos_fields alg b)
termination_by structural x
def cata_pos_case {R : RepFam → Type u} (alg : RepAlgebra R)
    (x : String × Nat × List (String × Rep)) : String × Nat × List (String × R .rep) :=
  match x with
  | (a, b) => (a, cata_pos_caseTail alg b)
termination_by structural x
def cata_pos_cases {R : RepFam → Type u} (alg : RepAlgebra R)
    (xs : List (String × Nat × List (String × Rep))) :
    List (String × Nat × List (String × R .rep)) :=
  match xs with
  | [] => []
  | x :: rest => cata_pos_case alg x :: cata_pos_cases alg rest
termination_by structural xs
end

/-! ## Each helper is the container's own map of the fold (what the public equations use) -/

theorem cata_pos_listRep_eq {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List Rep) :
    cata_pos_listRep alg xs = xs.map (cata_rep alg) := by
  induction xs with
  | nil => simp only [cata_pos_listRep, List.map_nil]
  | cons x rest ih => simp only [cata_pos_listRep, List.map_cons, ih]

theorem cata_pos_listChk_eq {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List Chk) :
    cata_pos_listChk alg xs = xs.map (cata_chk alg) := by
  induction xs with
  | nil => simp only [cata_pos_listChk, List.map_nil]
  | cons x rest ih => simp only [cata_pos_listChk, List.map_cons, ih]

theorem cata_pos_elem_eq {R : RepFam → Type u} (alg : RepAlgebra R) (x : ElemOf Rep) :
    cata_pos_elem alg x = x.map (cata_rep alg) := by
  cases x
  simp only [cata_pos_elem, ElemOf.map]

theorem cata_pos_listElem_eq {R : RepFam → Type u} (alg : RepAlgebra R) (xs : List (ElemOf Rep)) :
    cata_pos_listElem alg xs = xs.map (ElemOf.map (cata_rep alg)) := by
  induction xs with
  | nil => simp only [cata_pos_listElem, List.map_nil]
  | cons x rest ih => simp only [cata_pos_listElem, List.map_cons, ih, cata_pos_elem_eq]

theorem cata_pos_ann_eq {R : RepFam → Type u} (alg : RepAlgebra R) (x : RecAnn Rep) :
    cata_pos_ann alg x = x.map (cata_rep alg) := by
  cases x with
  | mk id schemas =>
    cases schemas with
    | none => simp only [cata_pos_ann, cata_pos_optListRep, RecAnn.map, Option.map_none]
    | some ys =>
      simp only [cata_pos_ann, cata_pos_optListRep, RecAnn.map, Option.map_some,
        cata_pos_listRep_eq]

/-- The public constructor equation, stated with the containers' own maps. -/
theorem cata_rep_arr {R : RepFam → Type u} (alg : RepAlgebra R) (a0 : List Chk)
    (a1 : List (ElemOf Rep)) (a2 : List Rep) :
    cata_rep alg (.arr a0 a1 a2) =
      alg.rep_arr (a0.map (cata_chk alg)) (a1.map (ElemOf.map (cata_rep alg)))
        (a2.map (cata_rep alg)) := by
  simp only [cata_rep, cata_pos_listChk_eq, cata_pos_listElem_eq, cata_pos_listRep_eq]

/-! ## The identity algebra folds to the identity (the hand file's `rebuild` / `fold_rebuild`) -/

abbrev RepSelfCarrier : RepFam → Type
  | .rep => Rep
  | .chk => Chk

def RepAlgebra.id : RepAlgebra RepSelfCarrier where
  rep_leaf a0 := Rep.leaf a0
  rep_susp a0 a1 := Rep.susp a0 a1
  rep_arr a0 a1 a2 := Rep.arr a0 a1 a2
  rep_struct a0 a1 := Rep.struct a0 a1
  rep_sum a0 a1 := Rep.sum a0 a1
  chk_filter a0 a1 := Chk.filter a0 a1
  chk_group a0 a1 := Chk.group a0 a1

mutual
theorem cata_id_rep (node : Rep) : cata_rep RepAlgebra.id node = node := by
  match node with
  | .leaf a0 =>
    simp only [cata_rep]
    rfl
  | .susp a0 a1 =>
    simp only [cata_rep, cata_id_pos_listChk a0, cata_id_rep a1]
    rfl
  | .arr a0 a1 a2 =>
    simp only [cata_rep, cata_id_pos_listChk a0, cata_id_pos_listElem a1, cata_id_pos_listRep a2]
    rfl
  | .struct a0 a1 =>
    simp only [cata_rep, cata_id_pos_fields a1]
    rfl
  | .sum a0 a1 =>
    simp only [cata_rep, cata_id_pos_cases a1]
    rfl
termination_by structural node
theorem cata_id_chk (node : Chk) : cata_chk RepAlgebra.id node = node := by
  match node with
  | .filter a0 a1 =>
    simp only [cata_chk, cata_id_pos_ann a0]
    rfl
  | .group a0 a1 =>
    simp only [cata_chk, cata_id_pos_optAnn a0, cata_id_pos_listChk a1]
    rfl
termination_by structural node
theorem cata_id_pos_listRep (xs : List Rep) : cata_pos_listRep RepAlgebra.id xs = xs := by
  match xs with
  | [] => simp only [cata_pos_listRep]
  | x :: rest => simp only [cata_pos_listRep, cata_id_rep x, cata_id_pos_listRep rest]
termination_by structural xs
theorem cata_id_pos_listChk (xs : List Chk) : cata_pos_listChk RepAlgebra.id xs = xs := by
  match xs with
  | [] => simp only [cata_pos_listChk]
  | x :: rest => simp only [cata_pos_listChk, cata_id_chk x, cata_id_pos_listChk rest]
termination_by structural xs
theorem cata_id_pos_elem (x : ElemOf Rep) : cata_pos_elem RepAlgebra.id x = x := by
  match x with
  | ⟨isOptional, type, note⟩ => simp only [cata_pos_elem, cata_id_rep type]
termination_by structural x
theorem cata_id_pos_listElem (xs : List (ElemOf Rep)) :
    cata_pos_listElem RepAlgebra.id xs = xs := by
  match xs with
  | [] => simp only [cata_pos_listElem]
  | x :: rest => simp only [cata_pos_listElem, cata_id_pos_elem x, cata_id_pos_listElem rest]
termination_by structural xs
theorem cata_id_pos_optListRep (x : Option (List Rep)) :
    cata_pos_optListRep RepAlgebra.id x = x := by
  match x with
  | none => simp only [cata_pos_optListRep]
  | some y => simp only [cata_pos_optListRep, cata_id_pos_listRep y]
termination_by structural x
theorem cata_id_pos_ann (x : RecAnn Rep) : cata_pos_ann RepAlgebra.id x = x := by
  match x with
  | ⟨id, schemas⟩ => simp only [cata_pos_ann, cata_id_pos_optListRep schemas]
termination_by structural x
theorem cata_id_pos_optAnn (x : Option (RecAnn Rep)) : cata_pos_optAnn RepAlgebra.id x = x := by
  match x with
  | none => simp only [cata_pos_optAnn]
  | some y => simp only [cata_pos_optAnn, cata_id_pos_ann y]
termination_by structural x
theorem cata_id_pos_field (x : String × Rep) : cata_pos_field RepAlgebra.id x = x := by
  match x with
  | (a, b) => simp only [cata_pos_field, cata_id_rep b]
termination_by structural x
theorem cata_id_pos_fields (xs : List (String × Rep)) : cata_pos_fields RepAlgebra.id xs = xs := by
  match xs with
  | [] => simp only [cata_pos_fields]
  | x :: rest => simp only [cata_pos_fields, cata_id_pos_field x, cata_id_pos_fields rest]
termination_by structural xs
theorem cata_id_pos_caseTail (x : Nat × List (String × Rep)) :
    cata_pos_caseTail RepAlgebra.id x = x := by
  match x with
  | (a, b) => simp only [cata_pos_caseTail, cata_id_pos_fields b]
termination_by structural x
theorem cata_id_pos_case (x : String × Nat × List (String × Rep)) :
    cata_pos_case RepAlgebra.id x = x := by
  match x with
  | (a, b) => simp only [cata_pos_case, cata_id_pos_caseTail b]
termination_by structural x
theorem cata_id_pos_cases (xs : List (String × Nat × List (String × Rep))) :
    cata_pos_cases RepAlgebra.id xs = xs := by
  match xs with
  | [] => simp only [cata_pos_cases]
  | x :: rest => simp only [cata_pos_cases, cata_id_pos_case x, cata_id_pos_cases rest]
termination_by structural xs
end

/-! ## Uniqueness: any family of functions satisfying the constructor equations is the fold -/

def prodMapSnd {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) (x : α × β) : α × γ := (x.1, f x.2)

/-- The only equation the proofs use: on a pair literal. Unfolding `prodMapSnd` itself would also
open an inner `prodMapSnd g b` on a variable `b`, before the induction hypothesis can rewrite it. -/
theorem prodMapSnd_mk {α : Type u} {β : Type v} {γ : Type w} (f : β → γ) (a : α) (b : β) :
    prodMapSnd f (a, b) = (a, f b) := rfl

structure RepHom {R : RepFam → Type u} (alg : RepAlgebra R) where
  f_rep : Rep → R .rep
  f_chk : Chk → R .chk
  h_rep_leaf : ∀ a0, f_rep (.leaf a0) = alg.rep_leaf a0
  h_rep_susp : ∀ a0 a1, f_rep (.susp a0 a1) = alg.rep_susp (a0.map f_chk) (f_rep a1)
  h_rep_arr : ∀ a0 a1 a2, f_rep (.arr a0 a1 a2) =
    alg.rep_arr (a0.map f_chk) (a1.map (ElemOf.map f_rep)) (a2.map f_rep)
  h_rep_struct : ∀ a0 a1, f_rep (.struct a0 a1) = alg.rep_struct a0 (a1.map (prodMapSnd f_rep))
  h_rep_sum : ∀ a0 a1, f_rep (.sum a0 a1) =
    alg.rep_sum a0 (a1.map (prodMapSnd (prodMapSnd (List.map (prodMapSnd f_rep)))))
  h_chk_filter : ∀ a0 a1, f_chk (.filter a0 a1) = alg.chk_filter (a0.map f_rep) a1
  h_chk_group : ∀ a0 a1, f_chk (.group a0 a1) =
    alg.chk_group (a0.map (RecAnn.map f_rep)) (a1.map f_chk)

mutual
theorem hom_eq_cata_rep {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg) (node : Rep) :
    hom.f_rep node = cata_rep alg node := by
  match node with
  | .leaf a0 => simp only [cata_rep, hom.h_rep_leaf a0]
  | .susp a0 a1 =>
    simp only [cata_rep, hom.h_rep_susp a0 a1, hom_pos_listChk hom a0, hom_eq_cata_rep hom a1]
  | .arr a0 a1 a2 =>
    simp only [cata_rep, hom.h_rep_arr a0 a1 a2, hom_pos_listChk hom a0, hom_pos_listElem hom a1,
      hom_pos_listRep hom a2]
  | .struct a0 a1 => simp only [cata_rep, hom.h_rep_struct a0 a1, hom_pos_fields hom a1]
  | .sum a0 a1 => simp only [cata_rep, hom.h_rep_sum a0 a1, hom_pos_cases hom a1]
termination_by structural node
theorem hom_eq_cata_chk {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg) (node : Chk) :
    hom.f_chk node = cata_chk alg node := by
  match node with
  | .filter a0 a1 => simp only [cata_chk, hom.h_chk_filter a0 a1, hom_pos_ann hom a0]
  | .group a0 a1 =>
    simp only [cata_chk, hom.h_chk_group a0 a1, hom_pos_optAnn hom a0, hom_pos_listChk hom a1]
termination_by structural node
theorem hom_pos_listRep {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (xs : List Rep) : xs.map hom.f_rep = cata_pos_listRep alg xs := by
  match xs with
  | [] => simp only [cata_pos_listRep, List.map_nil]
  | x :: rest =>
    simp only [cata_pos_listRep, List.map_cons, hom_eq_cata_rep hom x, hom_pos_listRep hom rest]
termination_by structural xs
theorem hom_pos_listChk {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (xs : List Chk) : xs.map hom.f_chk = cata_pos_listChk alg xs := by
  match xs with
  | [] => simp only [cata_pos_listChk, List.map_nil]
  | x :: rest =>
    simp only [cata_pos_listChk, List.map_cons, hom_eq_cata_chk hom x, hom_pos_listChk hom rest]
termination_by structural xs
theorem hom_pos_elem {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : ElemOf Rep) : x.map hom.f_rep = cata_pos_elem alg x := by
  match x with
  | ⟨isOptional, type, note⟩ => simp only [cata_pos_elem, ElemOf.map, hom_eq_cata_rep hom type]
termination_by structural x
theorem hom_pos_listElem {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (xs : List (ElemOf Rep)) : xs.map (ElemOf.map hom.f_rep) = cata_pos_listElem alg xs := by
  match xs with
  | [] => simp only [cata_pos_listElem, List.map_nil]
  | x :: rest =>
    simp only [cata_pos_listElem, List.map_cons, hom_pos_elem hom x, hom_pos_listElem hom rest]
termination_by structural xs
theorem hom_pos_optListRep {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : Option (List Rep)) : x.map (List.map hom.f_rep) = cata_pos_optListRep alg x := by
  match x with
  | none => simp only [cata_pos_optListRep, Option.map_none]
  | some y => simp only [cata_pos_optListRep, Option.map_some, hom_pos_listRep hom y]
termination_by structural x
theorem hom_pos_ann {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : RecAnn Rep) : x.map hom.f_rep = cata_pos_ann alg x := by
  match x with
  | ⟨id, schemas⟩ => simp only [cata_pos_ann, RecAnn.map, hom_pos_optListRep hom schemas]
termination_by structural x
theorem hom_pos_optAnn {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : Option (RecAnn Rep)) : x.map (RecAnn.map hom.f_rep) = cata_pos_optAnn alg x := by
  match x with
  | none => simp only [cata_pos_optAnn, Option.map_none]
  | some y => simp only [cata_pos_optAnn, Option.map_some, hom_pos_ann hom y]
termination_by structural x
theorem hom_pos_field {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : String × Rep) : prodMapSnd hom.f_rep x = cata_pos_field alg x := by
  match x with
  | (a, b) => simp only [cata_pos_field, prodMapSnd_mk, hom_eq_cata_rep hom b]
termination_by structural x
theorem hom_pos_fields {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (xs : List (String × Rep)) : xs.map (prodMapSnd hom.f_rep) = cata_pos_fields alg xs := by
  match xs with
  | [] => simp only [cata_pos_fields, List.map_nil]
  | x :: rest =>
    simp only [cata_pos_fields, List.map_cons, hom_pos_field hom x, hom_pos_fields hom rest]
termination_by structural xs
theorem hom_pos_caseTail {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : Nat × List (String × Rep)) :
    prodMapSnd (List.map (prodMapSnd hom.f_rep)) x = cata_pos_caseTail alg x := by
  match x with
  | (a, b) => simp only [cata_pos_caseTail, prodMapSnd_mk, hom_pos_fields hom b]
termination_by structural x
theorem hom_pos_case {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (x : String × Nat × List (String × Rep)) :
    prodMapSnd (prodMapSnd (List.map (prodMapSnd hom.f_rep))) x = cata_pos_case alg x := by
  match x with
  | (a, b) => simp only [cata_pos_case, prodMapSnd_mk, hom_pos_caseTail hom b]
termination_by structural x
theorem hom_pos_cases {R : RepFam → Type u} {alg : RepAlgebra R} (hom : RepHom alg)
    (xs : List (String × Nat × List (String × Rep))) :
    xs.map (prodMapSnd (prodMapSnd (List.map (prodMapSnd hom.f_rep)))) = cata_pos_cases alg xs := by
  match xs with
  | [] => simp only [cata_pos_cases, List.map_nil]
  | x :: rest =>
    simp only [cata_pos_cases, List.map_cons, hom_pos_case hom x, hom_pos_cases hom rest]
termination_by structural xs
end

/-! ## The monoid fold: one hook per sort, children combined left to right -/

mutual
def foldMap_rep {M : Type u} (unit : M) (op : M → M → M) (node : Rep)
    (f_rep : Rep → M := fun _ => unit) (f_chk : Chk → M := fun _ => unit) : M :=
  match node with
  | .leaf a0 => f_rep (.leaf a0)
  | .susp a0 a1 =>
    op (f_rep (.susp a0 a1)) (op (foldMap_pos_listChk unit op a0 f_rep f_chk)
      (foldMap_rep unit op a1 f_rep f_chk))
  | .arr a0 a1 a2 =>
    op (f_rep (.arr a0 a1 a2)) (op (foldMap_pos_listChk unit op a0 f_rep f_chk)
      (op (foldMap_pos_listElem unit op a1 f_rep f_chk) (foldMap_pos_listRep unit op a2 f_rep f_chk)))
  | .struct a0 a1 => op (f_rep (.struct a0 a1)) (foldMap_pos_fields unit op a1 f_rep f_chk)
  | .sum a0 a1 => f_rep (.sum a0 a1)
termination_by structural node
def foldMap_chk {M : Type u} (unit : M) (op : M → M → M) (node : Chk)
    (f_rep : Rep → M := fun _ => unit) (f_chk : Chk → M := fun _ => unit) : M :=
  match node with
  | .filter a0 a1 => f_chk (.filter a0 a1)
  | .group a0 a1 => op (f_chk (.group a0 a1)) (foldMap_pos_listChk unit op a1 f_rep f_chk)
termination_by structural node
def foldMap_pos_listRep {M : Type u} (unit : M) (op : M → M → M) (xs : List Rep)
    (f_rep : Rep → M := fun _ => unit) (f_chk : Chk → M := fun _ => unit) : M :=
  match xs with
  | [] => unit
  | x :: rest => op (foldMap_rep unit op x f_rep f_chk) (foldMap_pos_listRep unit op rest f_rep f_chk)
termination_by structural xs
def foldMap_pos_listChk {M : Type u} (unit : M) (op : M → M → M) (xs : List Chk)
    (f_rep : Rep → M := fun _ => unit) (f_chk : Chk → M := fun _ => unit) : M :=
  match xs with
  | [] => unit
  | x :: rest => op (foldMap_chk unit op x f_rep f_chk) (foldMap_pos_listChk unit op rest f_rep f_chk)
termination_by structural xs
def foldMap_pos_listElem {M : Type u} (unit : M) (op : M → M → M) (xs : List (ElemOf Rep))
    (f_rep : Rep → M := fun _ => unit) (f_chk : Chk → M := fun _ => unit) : M :=
  match xs with
  | [] => unit
  | ⟨_, type, _⟩ :: rest =>
    op (foldMap_rep unit op type f_rep f_chk) (foldMap_pos_listElem unit op rest f_rep f_chk)
termination_by structural xs
def foldMap_pos_fields {M : Type u} (unit : M) (op : M → M → M) (xs : List (String × Rep))
    (f_rep : Rep → M := fun _ => unit) (f_chk : Chk → M := fun _ => unit) : M :=
  match xs with
  | [] => unit
  | (_, b) :: rest =>
    op (foldMap_rep unit op b f_rep f_chk) (foldMap_pos_fields unit op rest f_rep f_chk)
termination_by structural xs
end

#guard foldMap_rep 0 (· + ·) (.arr [] [⟨true, .leaf 3, ""⟩] [.struct "t" [("y", .leaf 5)]])
  (f_rep := fun | .leaf _ => 1 | _ => 0) == 2

/-! ## A fold used: count the leaves (a monoid fold written as an algebra on a constant carrier) -/

def countAlg : RepAlgebra (fun _ => Nat) where
  rep_leaf _ := 1
  rep_susp cs t := cs.foldl (· + ·) 0 + t
  rep_arr cs es rest := cs.foldl (· + ·) 0 + (es.map (·.type)).foldl (· + ·) 0 + rest.foldl (· + ·) 0
  rep_struct _ fs := (fs.map (·.2)).foldl (· + ·) 0
  rep_sum _ cases := (cases.map fun c => (c.2.2.map (·.2)).foldl (· + ·) 0).foldl (· + ·) 0
  chk_filter ann _ := match ann.schemas with
    | none => 0
    | some xs => xs.foldl (· + ·) 0
  chk_group ann cs := (match ann with
    | none => 0
    | some a => match a.schemas with
      | none => 0
      | some xs => xs.foldl (· + ·) 0) + cs.foldl (· + ·) 0

#guard cata_rep countAlg
  (.arr [.filter ⟨"f", some [.leaf 1, .leaf 2]⟩ false]
    [⟨true, .leaf 3, ""⟩] [.sum "s" [("a", 0, [("x", .leaf 4)])], .struct "t" [("y", .leaf 5)]]) == 5

#print axioms cata_id_rep
#print axioms cata_rep_arr
#print axioms hom_eq_cata_rep
