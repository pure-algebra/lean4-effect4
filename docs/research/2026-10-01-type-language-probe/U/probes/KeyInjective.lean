import ProbeU.FacesTable
import Effect4.Program.Ty

/-!
# Probe U, question 5: `key` injective from the table, once

`Ty.key_injective` (`Program/Ty.lean:253`) is a 24-line case split over the square of the
alphabet (`induction a generalizing b <;> cases b`, then `all_goals try …` and one bullet per
binary constructor). Read through the spelling table it is one generic theorem about the fold
of `keyNode`, whose premises are facts about the *table*, not the constructors:

* the code column is injective (the wire tags are distinct: one `decide` over the tags);
* a tag fixes its node's shape: the payload's sort and the number of children
  (`tyLeaf_sort`, `tyKids_length`: one `cases` each, emitted beside the view);
* the payload encodings are injective at each sort (a string's UTF-8 bytes; an index itself);
* no constructor has both a string payload and children (the bytes are not self-delimiting,
  so a row with both would need a length prefix — the condition a variable-arity row of the
  data wave must meet, `record`'s field names included, and its arity must be in the key too).

The proof names no constructor: it reads the node one layer down (`cata_ofLayer_view`), peels
the code, splits the prefix code, and recurses on the children by size.
-/

set_option autoImplicit false

open Effect4.Program ProbeU

namespace ProbeU.Key

/-- The sort of a payload. -/
def leafSort : TyLeaf → Nat
  | .none => 0
  | .str _ => 1
  | .nat _ => 2

/-- The shape a tag fixes: its payload's sort and its number of children (emitted with the
view, one row per constructor). -/
def ctorShape : TyCtor → Nat × Nat
  | .never | .unit | .nat | .int | .string | .bool | .unknown => (0, 0)
  | .handle | .lit => (1, 0)
  | .var => (2, 0)
  | .option | .list | .causeOf | .refOf => (0, 1)
  | .prod | .except | .exitOf | .fiberOf | .union | .deferredOf => (0, 2)

theorem tyLeaf_sort (t : Ty) : leafSort (tyLeaf t) = (ctorShape (tyCtor t)).1 := by
  cases t <;> rfl

theorem tyKids_length (t : Ty) : (tyKids t).length = (ctorShape (tyCtor t)).2 := by
  cases t <;> rfl

/-- No tag carries both a string payload and children. -/
theorem shape_str_leaf (c : TyCtor) (h : (ctorShape c).1 = 1) : (ctorShape c).2 = 0 := by
  revert h
  cases c <;> decide

/-- UTF-8 bytes determine the string (a copy of `Ty.lean`'s private `utf8_key_injective`). -/
theorem utf8_injective {s t : String}
    (h : s.toUTF8.data.toList.map UInt8.toNat = t.toUTF8.data.toList.map UInt8.toNat) : s = t := by
  have bytes : s.toUTF8.data.toList = t.toUTF8.data.toList :=
    List.map_inj_right (fun _ _ he => UInt8.toNat_inj.mp he) |>.mp h
  have arrays : s.toUTF8.data = t.toUTF8.data := Array.toList_inj.mp bytes
  apply String.toByteArray_inj.mp
  exact ByteArray.ext arrays

/-- The payload encodings are injective at each sort. -/
theorem keyLeaf_inj : ∀ {l m : TyLeaf}, leafSort l = leafSort m → keyLeaf l = keyLeaf m → l = m
  | .none, .none, _, _ => rfl
  | .str _, .str _, _, h => congrArg TyLeaf.str (utf8_injective h)
  | .nat _, .nat _, _, h => congrArg TyLeaf.nat (List.cons.inj h).1
  | .none, .str _, hs, _ | .none, .nat _, hs, _ | .str _, .none, hs, _ | .str _, .nat _, hs, _
  | .nat _, .none, hs, _ | .nat _, .str _, hs, _ => nomatch hs

/-- The prefix code of children's keys, at a fixed number of children, is injective. -/
theorem prefixed_inj : ∀ (ks js : List (List Nat)), ks.length = js.length →
    prefixed ks = prefixed js → ks = js
  | [], [], _, _ => rfl
  | [k], [j], _, h => by simp only [prefixed] at h; rw [h]
  | k :: k' :: ks, j :: j' :: js, hl, h => by
    simp only [prefixed, List.cons.injEq] at h
    obtain ⟨hlen, happ⟩ := h
    obtain ⟨hk, hrest⟩ := List.append_inj happ hlen
    have := prefixed_inj (k' :: ks) (j' :: js) (by simp only [List.length_cons] at hl ⊢; omega) hrest
    rw [hk, this]
  | [], _ :: _, hl, _ => absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
  | _ :: _, [], hl, _ => absurd hl (by simp only [List.length_nil, List.length_cons]; omega)
  | [_], _ :: _ :: _, hl, _ => absurd hl (by simp only [List.length_cons, List.length_nil]; omega)
  | _ :: _ :: _, [_], hl, _ => absurd hl (by simp only [List.length_cons, List.length_nil]; omega)

/-- A payload that is not a string is self-delimiting before the children's code. -/
theorem tail_split : ∀ {la lb : TyLeaf} {x y : List Nat}, leafSort la = leafSort lb →
    leafSort la ≠ 1 → keyLeaf la ++ x = keyLeaf lb ++ y → keyLeaf la = keyLeaf lb ∧ x = y
  | .none, .none, _, _, _, _, h => ⟨rfl, h⟩
  | .nat _, .nat _, _, _, _, _, h => by
    have h' := List.cons.inj h
    exact ⟨by rw [h'.1], h'.2⟩
  | .str _, _, _, _, _, hns, _ => absurd rfl hns
  | .none, .str _, _, _, hs, _, _ | .none, .nat _, _, _, hs, _, _ | .nat _, .none, _, _, hs, _, _
  | .nat _, .str _, _, _, hs, _, _ => nomatch hs

theorem keyNode_eq (code : Nat) (leaf : TyLeaf) (kids : List (List Nat)) :
    keyNode code leaf kids = code :: (keyLeaf leaf ++ prefixed kids) := by
  unfold keyNode
  split
  · simp only [prefixed, List.append_nil]
  · rfl

theorem key_view (tbl : TyTable FaceRow) (t : Ty) :
    cata_ty (keyAlg tbl) t = (tbl.get (tyCtor t)).code ::
      (keyLeaf (tyLeaf t) ++ prefixed ((tyKids t).map (cata_ty (keyAlg tbl)))) := by
  rw [← keyNode_eq]
  exact cata_ofLayer_view _ t

/-- **The structural key of any table with distinct codes is injective** (proved once; no
constructor named). -/
theorem key_injective_of_table (tbl : TyTable FaceRow)
    (hcode : ∀ c d : TyCtor, (tbl.get c).code = (tbl.get d).code → c = d) :
    ∀ a b : Ty, cata_ty (keyAlg tbl) a = cata_ty (keyAlg tbl) b → a = b
  | a, b, h => by
    rw [key_view, key_view] at h
    obtain ⟨hcd, htail⟩ := List.cons.inj h
    have hc : tyCtor a = tyCtor b := hcode _ _ hcd
    have hsort : leafSort (tyLeaf a) = leafSort (tyLeaf b) := by rw [tyLeaf_sort, tyLeaf_sort, hc]
    have hlen : (tyKids a).length = (tyKids b).length := by rw [tyKids_length, tyKids_length, hc]
    have hparts : keyLeaf (tyLeaf a) = keyLeaf (tyLeaf b) ∧
        prefixed ((tyKids a).map (cata_ty (keyAlg tbl))) =
          prefixed ((tyKids b).map (cata_ty (keyAlg tbl))) := by
      by_cases hstr : leafSort (tyLeaf a) = 1
      · have h0a : (tyKids a).length = 0 := by
          rw [tyKids_length]
          exact shape_str_leaf _ (by rw [← tyLeaf_sort]; exact hstr)
        have h0b : (tyKids b).length = 0 := by rw [← hlen]; exact h0a
        rw [List.length_eq_zero_iff.mp h0a, List.length_eq_zero_iff.mp h0b] at htail ⊢
        simp only [List.map_nil, prefixed, List.append_nil] at htail
        exact ⟨htail, rfl⟩
      · exact tail_split hsort hstr htail
    have hl : tyLeaf a = tyLeaf b := keyLeaf_inj hsort hparts.1
    have hm : (tyKids a).map (cata_ty (keyAlg tbl)) = (tyKids b).map (cata_ty (keyAlg tbl)) :=
      prefixed_inj _ _ (by simp only [List.length_map, hlen]) hparts.2
    have hk : ∀ (xs ys : List Ty), (∀ x ∈ xs, sizeOf x < sizeOf a) →
        xs.map (cata_ty (keyAlg tbl)) = ys.map (cata_ty (keyAlg tbl)) → xs = ys := by
      intro xs
      induction xs with
      | nil => intro ys _ e; exact (List.map_eq_nil_iff.mp e.symm).symm
      | cons x xs ih =>
        intro ys hx e
        cases ys with
        | nil => exact absurd e (by simp only [List.map_cons, List.map_nil, reduceCtorEq, not_false_eq_true])
        | cons y ys =>
          simp only [List.map_cons, List.cons.injEq] at e
          have hxa : sizeOf x < sizeOf a := hx x List.mem_cons_self
          rw [key_injective_of_table tbl hcode x y e.1,
            ih ys (fun z hz => hx z (List.mem_cons_of_mem x hz)) e.2]
    rw [← tyBuild_view a, ← tyBuild_view b, hc, hl, hk _ _ (fun x hx => sizeOf_tyKids hx) hm]
termination_by a _ _ => sizeOf a
decreasing_by assumption

/-- `Ty.key` is the code column's fold (as `SpellingFolds.key_eq_table`, restated here). -/
theorem key_eq_table' (t : Ty) : Ty.key t = cata_ty (keyAlg tyFaces) t :=
  hom_eq_cata_ty (alg := keyAlg tyFaces)
    { f_ty := Ty.key
      h_ty_never := rfl, h_ty_unit := rfl, h_ty_nat := rfl, h_ty_int := rfl
      h_ty_string := rfl, h_ty_bool := rfl, h_ty_handle := fun _ => rfl
      h_ty_option := fun _ => rfl, h_ty_list := fun _ => rfl
      h_ty_prod := fun _ _ => rfl, h_ty_except := fun _ _ => rfl
      h_ty_exitOf := fun _ _ => rfl, h_ty_causeOf := fun _ => rfl
      h_ty_fiberOf := fun _ _ => rfl, h_ty_union := fun _ _ => rfl
      h_ty_lit := fun _ => rfl, h_ty_refOf := fun _ => rfl
      h_ty_deferredOf := fun _ _ => rfl, h_ty_var := fun _ => rfl
      h_ty_unknown := rfl } t

/-- The spelling table's codes are distinct (`decide`, one tag pair at a time). -/
theorem tyFaces_codes : ∀ c d : TyCtor, (tyFaces.get c).code = (tyFaces.get d).code → c = d := by
  intro c d
  cases c <;> cases d <;> decide

/-- **`Ty.key_injective`, from the table** (proved): the production statement. -/
theorem key_injective' {a b : Ty} (h : Ty.key a = Ty.key b) : a = b := by
  rw [key_eq_table', key_eq_table'] at h
  exact key_injective_of_table tyFaces tyFaces_codes a b h

end ProbeU.Key

#print axioms ProbeU.Key.tyLeaf_sort
#print axioms ProbeU.Key.tyKids_length
#print axioms ProbeU.Key.shape_str_leaf
#print axioms ProbeU.Key.keyLeaf_inj
#print axioms ProbeU.Key.prefixed_inj
#print axioms ProbeU.Key.key_injective_of_table
#print axioms ProbeU.Key.key_eq_table'
#print axioms ProbeU.Key.tyFaces_codes
#print axioms ProbeU.Key.key_injective'
