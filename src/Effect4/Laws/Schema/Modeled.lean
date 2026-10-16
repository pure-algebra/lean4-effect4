import Effect4.Schema.Modeled
import Effect4.Laws.Schema.Codec
import Effect4.Laws.Program.TypeAlgebra
import Effect4.Laws.Auto.Semantics
import Effect4.Laws.Program.TyExpand
import Effect4.Laws.Program.Signature

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
- `Modeled.memberIn_ref`: a named type's reference has exactly its code's members, under a
  guarded, expandable table that holds the type's declarations (claim `modeled-name`, decisions
  row 402). `Modeled.memberIn_image`: so its codec writes members of its name.
  `Modeled.memberIn_ref_of_lawful`: the same at an admitted signature's table.

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
  | .int, _, x, _ => by cases x <;> rfl
  | .lit s, _, _, _ => by
    show (s == s) = true
    exact decide_eq_true rfl
  | .union a b, h, x, alloc => by
    have hab := or_none h
    obtain ⟨s, _⟩ := x
    cases s with
    | inl y =>
      show (Val.hasTy ((image a).toVal y) a alloc || Val.hasTy ((image a).toVal y) b alloc) = true
      rw [member a hab.1 y alloc]
      rfl
    | inr y =>
      show (Val.hasTy ((image b).toVal y) a alloc || Val.hasTy ((image b).toVal y) b alloc) = true
      rw [member b hab.2 y alloc, Bool.or_true]
  | .never, h, _, _ => nomatch h
  | .handle _, h, _, _ => nomatch h
  | .except _ _, h, _, _ => nomatch h
  | .exitOf _ _, h, _, _ => nomatch h
  | .causeOf _, h, _, _ => nomatch h
  | .fiberOf _ _, h, _, _ => nomatch h
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
    Val.hasTy ((Modeled.image α).toVal a) m.ty alloc = true := by
  show Val.hasTy (m.staged.toVal (m.toC a)) m.ty alloc = true
  rw [m.staged_eq]
  exact Model.member m.ty m.checked (m.toC a) alloc

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

/-- **A named type's reference has exactly the members of its code** (claim `modeled-name`,
decisions row 402). Take a guarded table whose computed expansions solve it, and that holds each
of the type's declarations as its entry. Membership under it at the type's reference is then
`Val.hasTy` at the type's code. Proved from `memberIn_iff_expansions` and the instance's
`ref_expands`. Placement: concept `store-typing`, R3. Consumer: `memberIn_image`, and the wiring
slice, where reply admission reads the application's table. -/
@[semantics "store-typing" (requirement := R3)]
theorem memberIn_ref (α : Type) [m : Modeled α] {decls : TyDecls} (hg : decls.guarded = true)
    (he : decls.expandable = true) (hsub : ∀ e ∈ m.decls, decls.body? e.1 = some e.2)
    (alloc : List String) (v : Val) :
    MemberIn decls alloc v m.ref ↔ Val.hasTy v m.ty alloc = true := by
  rw [memberIn_iff_expansions hg he, m.ref_expands decls.expansions
    (fun e he' => TyDecls.expands_of_expandsAll he (e.1, e.2) (TyDecls.mem_of_body? (hsub e he')))
    m.checked]

/-- **A named type's codec writes members of its name**, under every table `memberIn_ref` reads:
`member` across `memberIn_ref`. -/
theorem memberIn_image (α : Type) [m : Modeled α] {decls : TyDecls} (hg : decls.guarded = true)
    (he : decls.expandable = true) (hsub : ∀ e ∈ m.decls, decls.body? e.1 = some e.2) (a : α)
    (alloc : List String) : MemberIn decls alloc ((Modeled.image α).toVal a) m.ref :=
  (memberIn_ref α hg he hsub alloc _).mpr (member α a alloc)

/-- **At an admitted signature**: the signature's admission makes its table guarded and gives no
name two bodies (`LawfulSig`), so a named type whose declarations the table holds has, at its
reference, exactly its code's members, when the table's expansions solve it. `memberIn_ref` with
its premises read off the admission. -/
theorem memberIn_ref_of_lawful (α : Type) [m : Modeled α] {app : SigApp} (h : LawfulSig app)
    (he : app.types.expandable = true) (hsub : ∀ e ∈ m.decls, e ∈ app.types)
    (alloc : List String) (v : Val) :
    MemberIn app.types alloc v m.ref ↔ Val.hasTy v m.ty alloc = true :=
  memberIn_ref α h.guarded he
    (fun e he' => TyDecls.body?_of_consistent h.declsConsistent (hsub e he')) alloc v

end Modeled
end Effect4.Schema
