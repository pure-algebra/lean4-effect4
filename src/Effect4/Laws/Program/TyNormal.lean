import Effect4.Program.TyNormal
import Effect4.Laws.Program.Typing.TermIntro

/-!
# Laws.Program.TyNormal — a certified type is its own normal form

Concept: Subtyping Algebra & Normalization. `Ty.normalize_of_certNormal` is a helper of the claim
`step-language-typed` (`src/Effect4/Laws/Step.lean`): the step language's typing check
certifies the normal forms that the checker's selection, list and record rules ask for, by
evaluation, where `decide` on `t.normalize = t` does not reduce at a product.

The proof is one structural recursion on `Ty`, with a companion for a record's fields. A product
uses `Ty.normalize_prod_canonical`, and a record uses `normalizeFields_fixed` and
`Field.canonBy_of_ascending`. The converse does not hold, and nothing here is claimed of it.
-/

set_option autoImplicit false

namespace Effect4.Program

/-- The certificate's second answer is whether the type is a factor. -/
theorem certNormal_factor (t : Ty) : (cata_ty certNormalAlg t).2 = t.isFactor := by
  cases t <;> rfl

/-- Two field lists with one list of names are ascending together. -/
theorem ascending_of_names {α β : Type} {l1 : List (String × α)} {l2 : List (String × β)}
    (names : l1.map Prod.fst = l2.map Prod.fst) (h : Field.Ascending Field.bytesKey l1) :
    Field.Ascending Field.bytesKey l2 := by
  have keyed : (l1.map Prod.fst).Pairwise
      (fun a b => Field.ltKey (Field.bytesKey a) (Field.bytesKey b) = true) :=
    List.pairwise_map.mpr h
  rw [names] at keyed
  exact List.pairwise_map.mp keyed

/-- The certificate's fold keeps a record's names. -/
theorem certNormal_names (fs : List (String × Bool × Ty)) :
    (cata_pos_list_prod_string_prod_bool_ty certNormalAlg fs).map Prod.fst = fs.map Prod.fst := by
  rw [cata_pos_list_prod_string_prod_bool_ty_eq, List.map_map]
  rfl

mutual
/-- **A certified type is its own normal form.** -/
theorem Ty.normalize_of_certNormal : (t : Ty) → t.certNormal = true → t.normalize = t
  | .never, _ => rfl
  | .unit, _ => rfl
  | .nat, _ => rfl
  | .int, _ => rfl
  | .string, _ => rfl
  | .bool, _ => rfl
  | .handle _, _ => rfl
  | .lit _, _ => rfl
  | .var _, _ => rfl
  | .unknown, _ => rfl
  | .null, _ => rfl
  | .undefined, _ => rfl
  | .number, _ => rfl
  | .bytes, _ => rfl
  | .option t, h => by
    show Ty.option t.normalize = .option t
    rw [Ty.normalize_of_certNormal t h]
  | .list t, h => by
    show Ty.list t.normalize = .list t
    rw [Ty.normalize_of_certNormal t h]
  | .causeOf t, h => by
    show Ty.causeOf t.normalize = .causeOf t
    rw [Ty.normalize_of_certNormal t h]
  | .refOf t, h => by
    show Ty.refOf t.normalize = .refOf t
    rw [Ty.normalize_of_certNormal t h]
  | .except a b, h => by
    have both : ((cata_ty certNormalAlg a).1 && (cata_ty certNormalAlg b).1) = true := h
    simp only [Bool.and_eq_true] at both
    show Ty.except a.normalize b.normalize = .except a b
    rw [Ty.normalize_of_certNormal a both.1, Ty.normalize_of_certNormal b both.2]
  | .exitOf a b, h => by
    have both : ((cata_ty certNormalAlg a).1 && (cata_ty certNormalAlg b).1) = true := h
    simp only [Bool.and_eq_true] at both
    show Ty.exitOf a.normalize b.normalize = .exitOf a b
    rw [Ty.normalize_of_certNormal a both.1, Ty.normalize_of_certNormal b both.2]
  | .fiberOf a b, h => by
    have both : ((cata_ty certNormalAlg a).1 && (cata_ty certNormalAlg b).1) = true := h
    simp only [Bool.and_eq_true] at both
    show Ty.fiberOf a.normalize b.normalize = .fiberOf a b
    rw [Ty.normalize_of_certNormal a both.1, Ty.normalize_of_certNormal b both.2]
  | .deferredOf a b, h => by
    have both : ((cata_ty certNormalAlg a).1 && (cata_ty certNormalAlg b).1) = true := h
    simp only [Bool.and_eq_true] at both
    show Ty.deferredOf a.normalize b.normalize = .deferredOf a b
    rw [Ty.normalize_of_certNormal a both.1, Ty.normalize_of_certNormal b both.2]
  | .map k v, h => by
    have both : ((cata_ty certNormalAlg k).1 && (cata_ty certNormalAlg v).1) = true := h
    simp only [Bool.and_eq_true] at both
    show Ty.map k.normalize v.normalize = .map k v
    rw [Ty.normalize_of_certNormal k both.1, Ty.normalize_of_certNormal v both.2]
  | .prod a b, h => by
    have all : ((cata_ty certNormalAlg a).1 && (cata_ty certNormalAlg b).1 &&
        (cata_ty certNormalAlg a).2 && (cata_ty certNormalAlg b).2) = true := h
    simp only [Bool.and_eq_true] at all
    obtain ⟨⟨⟨ha, hb⟩, fa⟩, fb⟩ := all
    rw [certNormal_factor] at fa fb
    exact Ty.normalize_prod_canonical (Ty.normalize_of_certNormal a ha)
      (Ty.normalize_of_certNormal b hb) fa fb
  | .record fs, h => by
    have both : (decide (Field.Ascending Field.bytesKey
        (cata_pos_list_prod_string_prod_bool_ty certNormalAlg fs)) &&
        (cata_pos_list_prod_string_prod_bool_ty certNormalAlg fs).all (fun f => f.2.2.1)) = true := h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at both
    have ascending : Field.Ascending Field.bytesKey fs :=
      ascending_of_names (certNormal_names fs) both.1
    show Ty.record (Ty.canon (Ty.normalizeFields fs)) = .record fs
    rw [Ty.normalizeFields_fixed fs (fields_of_certNormal fs both.2), Ty.canon,
      Field.canonBy_of_ascending fs ascending]
  | .union _ _, h => nomatch h
  | .tuple _, h => nomatch h
  | .app _ _, h => nomatch h

/-- The record arm: each certified field's type is its own normal form. -/
theorem fields_of_certNormal : (fs : List (String × Bool × Ty)) →
    (cata_pos_list_prod_string_prod_bool_ty certNormalAlg fs).all (fun f => f.2.2.1) = true →
    ∀ p ∈ fs, p.2.2.normalize = p.2.2
  | [], _, _, hp => absurd hp List.not_mem_nil
  | (_, _, t) :: rest, h, p, hp => by
    have both : ((cata_ty certNormalAlg t).1 &&
        (cata_pos_list_prod_string_prod_bool_ty certNormalAlg rest).all (fun f => f.2.2.1)) =
          true := h
    simp only [Bool.and_eq_true] at both
    rcases List.mem_cons.mp hp with same | later
    · rw [same]
      exact Ty.normalize_of_certNormal t both.1
    · exact fields_of_certNormal rest both.2 p later
end

/-- A certified product: both items are their own normal forms, and neither is a union. The
typing rule of a tuple of two asks for these four facts. -/
theorem certNormal_prod_facts {a b : Ty} (h : (Ty.prod a b).certNormal = true) :
    a.normalize = a ∧ b.normalize = b ∧ a.isFactor = true ∧ b.isFactor = true := by
  have all : ((cata_ty certNormalAlg a).1 && (cata_ty certNormalAlg b).1 &&
      (cata_ty certNormalAlg a).2 && (cata_ty certNormalAlg b).2) = true := h
  simp only [Bool.and_eq_true] at all
  obtain ⟨⟨⟨ha, hb⟩, fa⟩, fb⟩ := all
  rw [certNormal_factor] at fa fb
  exact ⟨Ty.normalize_of_certNormal a ha, Ty.normalize_of_certNormal b hb, fa, fb⟩

end Effect4.Program
