import Effect4.Schema.Modeled
import Effect4.Laws.Schema.Codec
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Schema.Modeled — membership and the JSON round trip of a modeled value

Concepts: Store Typing (membership) and Exact Codecs (the round trip).
Claims: `modeled-membership` and `modeled-codec`; requirement R3, which asks each type
constructor for its embeddings. The placement is the revision 3 note's, section 6
(`docs/research/2026-10-08-seat-MODULES-r3.md`; decisions row 330).

- `Model.member`: on the checked domain, every carrier value's encoding inhabits its type, at
  every allocation table. One structural recursion on `Ty`, with a companion for a record's
  fields. The record arm reads the fields in order, because ascending names are their own
  canonical form (`Field.canonBy_of_ascending`).
- `Modeled.member`: `Model.member` across the instance's equivalence. An instance owes no proof.
- `Modeled.codec_roundtrip`: a modeled value survives JSON and back at the normal form of its
  type. Codec admission is a premise, because it is value-specific: a natural above 2^53
  inhabits `nat` and has no exact JSON image.

These laws establish nothing for an identity type, an optional field, or the arms that the
refusal fold refuses. They establish no TypeScript codec and no target execution.
-/

set_option autoImplicit false

namespace Effect4.Schema
open Effect4.Program Effect4.Store

namespace Model

/-- A helper of `member`: an `or` of two options is `none` only when both are. -/
theorem or_none {a b : Option String} (h : a.or b = none) : a = none ∧ b = none := by
  cases a with
  | none => exact ⟨rfl, h⟩
  | some _ => nomatch h

/-- A helper of `member`: the field checks keep the record's names. -/
theorem checkers_names (alloc : List String) : ∀ fs : List (String × Bool × Ty),
    (Val.fieldCheckers fs alloc).map (·.1) = fs.map (·.1)
  | [] => rfl
  | (n, o, t) :: rest => by
    show n :: (Val.fieldCheckers rest alloc).map (·.1) = n :: rest.map (·.1)
    rw [checkers_names alloc rest]

/-- A helper of `member`: the carrier's columns keep the record's names. -/
theorem columns_names : ∀ fs : List (String × Bool × Ty),
    (columnsOf (cata_pos_list_prod_string_prod_bool_ty alg fs)).2.names = fs.map (·.1)
  | [] => rfl
  | (n, false, t) :: rest => by
    show n :: (columnsOf (cata_pos_list_prod_string_prod_bool_ty alg rest)).2.names =
      n :: rest.map (·.1)
    rw [columns_names rest]
  | (n, true, t) :: rest => by
    show n :: (columnsOf (cata_pos_list_prod_string_prod_bool_ty alg rest)).2.names =
      n :: rest.map (·.1)
    rw [columns_names rest]

/-- A helper of `member`: the refusal fold keeps the record's names. -/
theorem names_map_refusal : ∀ fs : List (String × Bool × Ty),
    (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs).map (·.1) = fs.map (·.1)
  | [] => rfl
  | (n, o, t) :: rest => by
    show n :: (cata_pos_list_prod_string_prod_bool_ty refusalAlg rest).map (·.1) =
      n :: rest.map (·.1)
    rw [names_map_refusal rest]

mutual
/-- **Membership on the checked domain** (claim `modeled-membership`): every carrier value's
encoding inhabits its type, at every allocation table. -/
@[semantics "store-typing" (requirement := R3)]
theorem member : (t : Ty) → refusal t = none → ∀ (x : Carrier t) (alloc : List String),
    Val.hasTy ((image t).toVal x) t alloc = true
  | .unit, _, _, _ => rfl
  | .nat, _, _, _ => rfl
  | .string, _, _, _ => rfl
  | .bool, _, _, _ => rfl
  | .option inner, h, x, alloc => by
    cases x with
    | none => rfl
    | some a => exact member inner h a alloc
  | .list inner, h, x, alloc => by
    show (x.map (image inner).toVal).all (fun v => Val.hasTy v inner alloc) = true
    apply List.all_eq_true.mpr
    intro v hv
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hv
    exact member inner h a alloc
  | .prod a b, h, x, alloc => by
    have hab := or_none h
    show (Val.hasTy ((image a).toVal x.1) a alloc &&
      Val.hasTy ((image b).toVal x.2) b alloc) = true
    rw [member a hab.1 x.1 alloc, member b hab.2 x.2 alloc]
    rfl
  | .record fs, h, x, alloc => by
    change (if Field.Ascending Field.bytesKey (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
      then fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs)
      else some "record fields out of canonical order") = none at h
    split at h
    · rename_i hasc
      have hnames : ((cata_pos_list_prod_string_prod_bool_ty refusalAlg fs).map (·.1)).Pairwise
          (fun a b => Field.ltKey (Field.bytesKey a) (Field.bytesKey b) = true) :=
        List.pairwise_map.mpr hasc
      rw [names_map_refusal fs, ← checkers_names alloc fs] at hnames
      have hcanon : Ty.canon (Val.fieldCheckers fs alloc) = Val.fieldCheckers fs alloc :=
        Field.canonBy_of_ascending _ (List.pairwise_map.mp hnames)
      show (match Program.recordParts? (.ctor 0 [.list ((columnsOf
          (cata_pos_list_prod_string_prod_bool_ty alg fs)).2.names.map .str),
          .list ((columnsOf (cata_pos_list_prod_string_prod_bool_ty alg fs)).2.toVals x)]) with
        | some (ns, xs) => namedHasTy (Ty.canon (Val.fieldCheckers fs alloc)) ns xs
        | none => false) = true
      simp only [Program.recordParts?]
      rw [hcanon, columns_names fs]
      exact member_fields fs h x alloc
    · nomatch h
  | .never, h, _, _ => nomatch h
  | .int, h, _, _ => nomatch h
  | .handle _, h, _, _ => nomatch h
  | .except _ _, h, _, _ => nomatch h
  | .exitOf _ _, h, _, _ => nomatch h
  | .causeOf _, h, _, _ => nomatch h
  | .fiberOf _ _, h, _, _ => nomatch h
  | .union _ _, h, _, _ => nomatch h
  | .lit _, h, _, _ => nomatch h
  | .refOf _, h, _, _ => nomatch h
  | .deferredOf _ _, h, _, _ => nomatch h
  | .var _, h, _, _ => nomatch h
  | .unknown, h, _, _ => nomatch h
  | .map _ _, h, _, _ => nomatch h
  | .tuple _, h, _, _ => nomatch h
  | .app _ _, h, _, _ => nomatch h
  | .null, h, _, _ => nomatch h
  | .undefined, h, _, _ => nomatch h
  | .number, h, _, _ => nomatch h
  | .bytes, h, _, _ => nomatch h

/-- The record arm of `member`, field by field: each value passes its field's check, in order. -/
theorem member_fields : (fs : List (String × Bool × Ty)) →
    fieldsRefusal (cata_pos_list_prod_string_prod_bool_ty refusalAlg fs) = none →
    ∀ (x : (columnsOf (cata_pos_list_prod_string_prod_bool_ty alg fs)).1) (alloc : List String),
      namedHasTy (Val.fieldCheckers fs alloc) ((fs.map (·.1)).map .str)
        ((columnsOf (cata_pos_list_prod_string_prod_bool_ty alg fs)).2.toVals x) = true
  | [], _, _, _ => rfl
  | (n, false, t) :: rest, h, x, alloc => by
    have ht := or_none h
    show (if n = n then Val.hasTy ((image t).toVal x.1) t alloc &&
        namedHasTy (Val.fieldCheckers rest alloc) ((rest.map (·.1)).map .str)
          ((columnsOf (cata_pos_list_prod_string_prod_bool_ty alg rest)).2.toVals x.2)
      else false && _) = true
    rw [if_pos rfl, member t ht.1 x.1 alloc, member_fields rest ht.2 x.2 alloc]
    rfl
  | (_, true, _) :: _, h, _, _ => nomatch h
end

end Model

namespace Modeled

/-- **Every modeled value inhabits its type**, at every allocation table: `Model.member` across
the equivalence (a reader of `modeled-membership` at each instance). -/
theorem member (α : Type) [m : Modeled α] (a : α) (alloc : List String) :
    Val.hasTy ((Modeled.image α).toVal a) m.ty alloc = true :=
  Model.member m.ty m.checked (m.toC a) alloc

/-- **The JSON round trip of a modeled value** (claim `modeled-codec`), at the normal form of its
type. Membership comes from `Modeled.member` and `hasTy_normalize`. Codec admission stays a
premise: it is value-specific, and a natural above 2^53 has no exact JSON image. -/
@[semantics "exact-codecs" (requirement := R3)]
theorem codec_roundtrip (α : Type) [m : Modeled α] (a : α)
    (admitted : Ty.isCodecValue (CTy.ofRaw m.ty).toRaw ((Modeled.image α).toVal a) = true) :
    ((encode (CTy.ofRaw m.ty).toRaw ((Modeled.image α).toVal a)).bind
        (decode (CTy.ofRaw m.ty).toRaw)).bind (Modeled.image α).ofVal = some a := by
  have hmem : Val.hasTy ((Modeled.image α).toVal a) (CTy.ofRaw m.ty).toRaw = true := by
    show Val.hasTy _ m.ty.normalize [] = true
    rw [hasTy_normalize]
    exact member α a []
  rw [decode_encode hmem admitted]
  exact (Modeled.image α).ofVal_toVal a

end Modeled
end Effect4.Schema
