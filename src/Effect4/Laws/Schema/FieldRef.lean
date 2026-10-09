import Effect4.Schema.FieldRef
import Effect4.Laws.Schema.Codec
import Effect4.Laws.Program.Typing.TermIntro
import Effect4.Laws.Auto.Semantics

/-!
# Laws.Schema.FieldRef — a field reference is a lens, on carriers and on the record frame

Concept: Exact Codecs (the record frame's field laws). Claim: `record-field-laws`
(`FieldRef.frame_laws`), requirement R3. Their consumers are the step language's laws (`src/Effect4/Laws/Step.lean`): a
step's field read and overwrite read what the reference's `get` and `set` give.

- **On carriers** (`get_set`, `set_get`, `set_set`): a reference is a lawful lens at every
  identity context. Two references at two positions are independent (`get_set_other`), and
  their writes commute (`set_comm`). On a list of distinct names, two references at one name
  are at one position (`index_eq_of_name_eq`).
- **On the machine** (`read_law`, `write_law`): for a record whose names are strictly ascending
  by their bytes, `Machine.Record.read` at the reference's name reads the field's encoding, and
  `Machine.Record.set` at that name writes the record that `FieldRef.set` gives. The image of a
  record is the record frame of its entries (`image_record`).
- **The checker's record rules** (`fieldType_ref`, `setType_ref`): at a record type in normal
  form, the field rule answers the reference's type, and the overwrite at that type answers the
  record's type.

These laws say nothing of an optional field: a reference names a required one. They hold at
every identity context, the opaque one included, and they establish no membership.
-/

set_option autoImplicit false

namespace Effect4.Schema
open Effect4.Program Effect4.Store Model

namespace FieldRef

variable {L : Leaves}

/-! ## A lens on carriers -/

/-- The write then the read answers the written value. -/
theorem get_set : ∀ {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t)
    (x : CarrierAt L (.record fs)) (v : CarrierAt L t), f.get (f.set x v) = v
  | _, _, .here _ _ _, _, _ => rfl
  | _, _, .there _ _ _ f, x, v => get_set f x.2 v

/-- Writing what is read changes nothing. -/
theorem set_get : ∀ {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t)
    (x : CarrierAt L (.record fs)), f.set x (f.get x) = x
  | _, _, .here _ _ _, _ => rfl
  | _, _, .there _ _ _ f, x => by
    show (x.1, f.set x.2 (f.get x.2)) = x
    rw [set_get f x.2]
    rfl

/-- The second of two writes wins. -/
theorem set_set : ∀ {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t)
    (x : CarrierAt L (.record fs)) (v w : CarrierAt L t), f.set (f.set x v) w = f.set x w
  | _, _, .here _ _ _, _, _, _ => rfl
  | _, _, .there _ _ _ f, x, v, w => by
    show (x.1, f.set (f.set x.2 v) w) = (x.1, f.set x.2 w)
    rw [set_set f x.2 v w]

/-- **Independence**: a write at one position leaves the read at another. -/
theorem get_set_other : ∀ {fs : List (String × Bool × Ty)} {s t : Ty} (f : FieldRef fs s)
    (g : FieldRef fs t) (x : CarrierAt L (.record fs)) (v : CarrierAt L s),
    f.index ≠ g.index → g.get (f.set x v) = g.get x
  | _, _, _, .here _ _ _, .here _ _ _, _, _, hne => absurd rfl hne
  | _, _, _, .here _ _ _, .there _ _ _ _, _, _, _ => rfl
  | _, _, _, .there _ _ _ _, .here _ _ _, _, _, _ => rfl
  | _, _, _, .there _ _ _ f, .there _ _ _ g, x, v, hne =>
    get_set_other f g x.2 v fun h => hne (congrArg (· + 1) h)

/-- **Two writes at two positions commute.** -/
theorem set_comm : ∀ {fs : List (String × Bool × Ty)} {s t : Ty} (f : FieldRef fs s)
    (g : FieldRef fs t) (x : CarrierAt L (.record fs)) (v : CarrierAt L s) (w : CarrierAt L t),
    f.index ≠ g.index → g.set (f.set x v) w = f.set (g.set x w) v
  | _, _, _, .here _ _ _, .here _ _ _, _, _, _, hne => absurd rfl hne
  | _, _, _, .here _ _ _, .there _ _ _ _, _, _, _, _ => rfl
  | _, _, _, .there _ _ _ _, .here _ _ _, _, _, _, _ => rfl
  | _, _, _, .there _ _ _ f, .there _ _ _ g, x, v, w, hne => by
    show (x.1, g.set (f.set x.2 v) w) = (x.1, f.set (g.set x.2 w) v)
    rw [set_comm f g x.2 v w fun h => hne (congrArg (· + 1) h)]

/-- The referenced field is in the list, required, at the reference's type. -/
theorem mem_fields : ∀ {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t),
    (f.name, false, t) ∈ fs
  | _, _, .here _ _ _ => List.mem_cons_self
  | _, _, .there _ _ _ f => List.mem_cons_of_mem _ (mem_fields f)

/-- The reference's name is one of the list's names. -/
theorem name_mem {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t) :
    f.name ∈ fs.map Prod.fst :=
  List.mem_map.mpr ⟨_, mem_fields f, rfl⟩

/-- Two references at one position name one field. -/
theorem name_of_index : ∀ {fs : List (String × Bool × Ty)} {s t : Ty} (f : FieldRef fs s)
    (g : FieldRef fs t), f.index = g.index → f.name = g.name
  | _, _, _, .here _ _ _, .here _ _ _, _ => rfl
  | _, _, _, .here _ _ _, .there _ _ _ _, h => nomatch h
  | _, _, _, .there _ _ _ _, .here _ _ _, h => nomatch h
  | _, _, _, .there _ _ _ f, .there _ _ _ g, h => name_of_index f g (Nat.succ.inj h)

/-- On a list of distinct names, two references at one name are at one position. -/
theorem index_eq_of_name_eq : ∀ {fs : List (String × Bool × Ty)} {s t : Ty} (f : FieldRef fs s)
    (g : FieldRef fs t), (fs.map Prod.fst).Nodup → f.name = g.name → f.index = g.index
  | _, _, _, .here _ _ _, .here _ _ _, _, _ => rfl
  | _, _, _, .here n _ rest, .there _ _ _ g, hnd, h => by
    have same : n = g.name := h
    have inside : n ∈ rest.map Prod.fst := same ▸ name_mem g
    exact absurd inside (List.nodup_cons.mp hnd).1
  | _, _, _, .there n _ _ f, .here _ _ _, hnd, h => by
    have same : f.name = n := h
    have inside := same ▸ name_mem f
    exact absurd inside (List.nodup_cons.mp hnd).1
  | _, _, _, .there _ _ _ f, .there _ _ _ g, hnd, h =>
    congrArg (· + 1) (index_eq_of_name_eq f g (List.nodup_cons.mp hnd).2 h)

end FieldRef

/-! ## The record frame -/

section Frame

variable (L : Leaves)

/-- The entries keep the record's names. -/
theorem entries_names : ∀ (fs : List (String × Bool × Ty)) (x : CarrierAt L (.record fs)),
    (entriesAt L fs x).map Prod.fst = fs.map Prod.fst
  | [], _ => rfl
  | (n, o, u) :: rest, x => by
    show n :: (entriesAt L rest x.2).map Prod.fst = n :: rest.map Prod.fst
    rw [entries_names rest x.2]

/-- The record image's two columns are the entries' names and values. -/
theorem columns_entries : ∀ (fs : List (String × Bool × Ty)) (x : CarrierAt L (.record fs)),
    (columnsOf (cata_pos_list_prod_string_prod_bool_ty (algAt L) fs)).2.names =
      (entriesAt L fs x).map Prod.fst ∧
    (columnsOf (cata_pos_list_prod_string_prod_bool_ty (algAt L) fs)).2.toVals x =
      (entriesAt L fs x).map Prod.snd
  | [], _ => ⟨rfl, rfl⟩
  | (n, o, u) :: rest, x => by
    have ih := columns_entries rest x.2
    constructor
    · show n :: (columnsOf (cata_pos_list_prod_string_prod_bool_ty (algAt L) rest)).2.names =
        n :: (entriesAt L rest x.2).map Prod.fst
      rw [ih.1]
    · show (fieldCarrier o (cata_ty (algAt L) u)).2.toVal x.1 ::
          (columnsOf (cata_pos_list_prod_string_prod_bool_ty (algAt L) rest)).2.toVals x.2 =
        (fieldCarrier o (cata_ty (algAt L) u)).2.toVal x.1 :: (entriesAt L rest x.2).map Prod.snd
      rw [ih.2]

/-- **A record's image is the record frame of its entries.** -/
theorem image_record (fs : List (String × Bool × Ty)) (x : CarrierAt L (.record fs)) :
    (imageAt L (.record fs)).toVal x = Machine.Record.frame (entriesAt L fs x) := by
  have h := columns_entries L fs x
  show Val.ctor 0 [.list ((columnsOf (cata_pos_list_prod_string_prod_bool_ty (algAt L) fs)).2.names.map
      .str), .list ((columnsOf (cata_pos_list_prod_string_prod_bool_ty (algAt L) fs)).2.toVals x)] =
    Val.ctor 0 [.list ((entriesAt L fs x).map fun entry => .str entry.1),
      .list ((entriesAt L fs x).map Prod.snd)]
  rw [h.1, h.2, List.map_map]
  rfl

variable {L}

/-- On ascending names, the entries are ascending. -/
theorem entries_ascending {fs : List (String × Bool × Ty)}
    (h : Field.Ascending Field.bytesKey fs) (x : CarrierAt L (.record fs)) :
    Field.Ascending Field.bytesKey (entriesAt L fs x) := by
  have names : (fs.map Prod.fst).Pairwise
      (fun a b => Field.ltKey (Field.bytesKey a) (Field.bytesKey b) = true) :=
    List.pairwise_map.mpr h
  rw [← entries_names L fs x] at names
  exact List.pairwise_map.mp names

/-- On ascending names, the entries' names are distinct. -/
theorem entries_nodup {fs : List (String × Bool × Ty)} (h : Field.Ascending Field.bytesKey fs)
    (x : CarrierAt L (.record fs)) : ((entriesAt L fs x).map Prod.fst).Nodup :=
  Field.names_nodup_of_ascending (entries_ascending h x)

/-- The referenced field's entry is among the entries. -/
theorem FieldRef.get_mem : ∀ {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t)
    (x : CarrierAt L (.record fs)), (f.name, (imageAt L t).toVal (f.get x)) ∈ entriesAt L fs x
  | _, _, .here _ _ _, _ => List.mem_cons_self
  | _, _, .there _ _ _ f, x => List.mem_cons_of_mem _ (FieldRef.get_mem f x.2)

/-- **The read law**: on ascending names, the machine's read at the reference's name reads the
field's encoding. -/
theorem FieldRef.read_law {fs : List (String × Bool × Ty)} {t : Ty}
    (h : Field.Ascending Field.bytesKey fs) (f : FieldRef fs t) (x : CarrierAt L (.record fs)) :
    Machine.Record.read false ((imageAt L (.record fs)).toVal x) f.name =
      some ((imageAt L t).toVal (f.get x)) := by
  have hf : Machine.Record.entries ((imageAt L (.record fs)).toVal x) = some (entriesAt L fs x) := by
    rw [image_record L fs x]
    exact Schema.Codec.entries_frame _ (entries_nodup h x)
  simp only [Machine.Record.read, Machine.Record.lookup, hf, Option.map_some,
    Field.firstOf_of_nodup (entries_nodup h x) (FieldRef.get_mem f x)]
  rfl

/-- What a write leaves at each name: the written value at its own name, the old elsewhere. -/
theorem FieldRef.firstOf_set : ∀ {fs : List (String × Bool × Ty)} {t : Ty} (f : FieldRef fs t)
    (x : CarrierAt L (.record fs)) (v : CarrierAt L t), (fs.map Prod.fst).Nodup → ∀ n : String,
    Field.firstOf n (entriesAt L fs (f.set x v)) =
      if f.name = n then some ((imageAt L t).toVal v) else Field.firstOf n (entriesAt L fs x)
  | _, _, .here m u rest, x, v, _, n => by
    show Field.firstOf n ((m, (imageAt L u).toVal v) :: entriesAt L rest x.2) =
      if m = n then some ((imageAt L u).toVal v)
      else Field.firstOf n ((m, (imageAt L u).toVal x.1) :: entriesAt L rest x.2)
    simp only [Field.firstOf]
    by_cases hm : m = n
    · rw [if_pos hm, if_pos hm]
    · simp only [if_neg hm]
  | _, _, @FieldRef.there m o u rest t f, x, v, hnd, n => by
    show Field.firstOf n ((m, (fieldCarrier o (cata_ty (algAt L) u)).2.toVal x.1) ::
        entriesAt L rest (f.set x.2 v)) =
      if f.name = n then some ((imageAt L t).toVal v)
      else Field.firstOf n ((m, (fieldCarrier o (cata_ty (algAt L) u)).2.toVal x.1) ::
        entriesAt L rest x.2)
    have hnd' : m ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := List.nodup_cons.mp hnd
    simp only [Field.firstOf]
    by_cases hm : m = n
    · have hne : f.name ≠ n := fun e => hnd'.1 (hm ▸ e ▸ FieldRef.name_mem f)
      rw [if_pos hm, if_pos hm, if_neg hne]
    · rw [if_neg hm, if_neg hm, FieldRef.firstOf_set f x.2 v hnd'.2 n]

/-- Two lists with distinct names and one `firstOf` at every name hold the same members. -/
theorem mem_iff_of_firstOf {l1 l2 : List (String × Val)} (h1 : (l1.map Prod.fst).Nodup)
    (h2 : (l2.map Prod.fst).Nodup) (h : ∀ n, Field.firstOf n l1 = Field.firstOf n l2) :
    ∀ p, p ∈ l1 ↔ p ∈ l2 := by
  intro p
  constructor
  · intro hp
    have found := Field.firstOf_of_nodup h1 hp
    rw [h] at found
    exact Field.firstOf_mem found
  · intro hp
    have found := Field.firstOf_of_nodup h2 hp
    rw [← h] at found
    exact Field.firstOf_mem found

/-- **The write law**: on ascending names, the machine's overwrite at the reference's name
writes the record that `FieldRef.set` gives. -/
theorem FieldRef.write_law {fs : List (String × Bool × Ty)} {t : Ty}
    (h : Field.Ascending Field.bytesKey fs) (f : FieldRef fs t) (x : CarrierAt L (.record fs))
    (v : CarrierAt L t) :
    Machine.Record.set ((imageAt L (.record fs)).toVal x) f.name ((imageAt L t).toVal v) =
      some ((imageAt L (.record fs)).toVal (f.set x v)) := by
  have hf : Machine.Record.entries ((imageAt L (.record fs)).toVal x) = some (entriesAt L fs x) := by
    rw [image_record L fs x]
    exact Schema.Codec.entries_frame _ (entries_nodup h x)
  rw [image_record L fs (f.set x v)]
  show (Machine.Record.entries ((imageAt L (.record fs)).toVal x)).bind (fun fields =>
      some (Machine.Record.frame (Field.canonBy Field.bytesKey
        ((f.name, (imageAt L t).toVal v) :: fields)))) =
    some (Machine.Record.frame (entriesAt L fs (f.set x v)))
  rw [hf, Option.bind_some]
  have hnd : (fs.map Prod.fst).Nodup := by
    rw [← entries_names L fs x]
    exact entries_nodup h x
  have hcanon := Field.canonBy_ascending (key := Field.bytesKey)
    ((f.name, (imageAt L t).toVal v) :: entriesAt L fs x)
  have heq : Field.canonBy Field.bytesKey ((f.name, (imageAt L t).toVal v) :: entriesAt L fs x) =
      entriesAt L fs (f.set x v) := by
    apply Field.ascending_ext hcanon (entries_ascending h (f.set x v))
    apply mem_iff_of_firstOf (Field.names_nodup_of_ascending hcanon) (entries_nodup h _)
    intro n
    rw [Field.firstOf_canonBy Field.bytesKey_injective, FieldRef.firstOf_set f x v hnd n]
    simp only [Field.firstOf]
  rw [heq]

/-- **The record frame's field laws** (claim `record-field-laws`): for a record with ascending
names, the machine's read at a reference's name reads the field's encoding, and its overwrite at
that name writes the record that the reference's write gives. -/
@[semantics "exact-codecs" (requirement := R3)]
theorem FieldRef.frame_laws {fs : List (String × Bool × Ty)} {t : Ty}
    (h : Field.Ascending Field.bytesKey fs) (f : FieldRef fs t) (x : CarrierAt L (.record fs))
    (v : CarrierAt L t) :
    Machine.Record.read false ((imageAt L (.record fs)).toVal x) f.name =
        some ((imageAt L t).toVal (f.get x)) ∧
      Machine.Record.set ((imageAt L (.record fs)).toVal x) f.name ((imageAt L t).toVal v) =
        some ((imageAt L (.record fs)).toVal (f.set x v)) :=
  ⟨FieldRef.read_law h f x, FieldRef.write_law h f x v⟩

end Frame

/-! ## The checker's record rules at a reference -/

/-- A record type in normal form has ascending names. -/
theorem ascending_of_normal {fs : List (String × Bool × Ty)}
    (normal : Ty.normalize (.record fs) = .record fs) : Field.Ascending Field.bytesKey fs :=
  (Ty.record_normal_fields normal).1

/-- At a record type in normal form, the reference's field is the first one under its name. -/
theorem firstOf_ref {fs : List (String × Bool × Ty)} {t : Ty}
    (normal : Ty.normalize (.record fs) = .record fs) (f : FieldRef fs t) :
    Field.firstOf f.name fs = some (false, t) :=
  Field.firstOf_of_nodup (Field.names_nodup_of_ascending (ascending_of_normal normal))
    (FieldRef.mem_fields f)

/-- **The field rule at a reference**: at a record type in normal form, it answers the
reference's type. -/
theorem fieldType_ref {fs : List (String × Bool × Ty)} {t : Ty}
    (normal : Ty.normalize (.record fs) = .record fs) (f : FieldRef fs t) :
    Record.fieldType false (.record fs) f.name = some t :=
  Record.fieldType_normal normal (firstOf_ref normal f)

/-- **The overwrite rule at a reference**: at a record type in normal form, writing the field at
its own type answers the record's type. -/
theorem setType_ref {fs : List (String × Bool × Ty)} {t : Ty}
    (normal : Ty.normalize (.record fs) = .record fs) (f : FieldRef fs t) :
    Record.setType (.record fs) f.name t = some (.record fs) :=
  Record.setType_same normal (firstOf_ref normal f)
    ((Ty.record_normal_fields normal).2 _ (FieldRef.mem_fields f))

end Effect4.Schema
