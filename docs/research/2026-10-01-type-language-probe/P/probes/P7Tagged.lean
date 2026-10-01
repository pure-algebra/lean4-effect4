import P6Inhabited

/-!
# Seat P, question 4(c): tagged unions of records (type-language probe, 2026-10-01)

Research probe. No constructor: a tagged union is a `union` of records, each with a required
`_tag` field of a literal type. The tag decision (`isTagged`, `payloadOf`, `taggedColumn`,
`diffTag`, the runtime `tagHit`/`tagPayload?`; `Program/Ty.lean:774-807`,
`Machine/Term.lean:361-363`, `Laws/Program/Decision.lean`, `Laws/Program/Residual.lean`) gains a
record arm, and its two laws are re-proved at records on the copy's `Fits`:

- `diffTag_sound`: a value of the column on which the tag test is false is a value of the
  residual;
- `payload_hasTy`: on a tagged column, a hit's payload is a member of the payload type (for a
  record the payload is the whole record: what `catchTag`'s handler receives).

**Under the named value clause (row 165 (a)) the runtime tag test reads the tag by name**
(`lookupName "_tag"`, type-blind, the search the evaluator's projection uses), so tagged records
are disjoint by their tag (`tagged_disjoint`) under the plain UTF-8 byte order: the
discriminant-first key the positional clause needed (commit `056ca30b`: `tag_head`, `"X" < "_tag"`
put the tag in slot 1 of one record and slot 0 of another) is not needed. The positional red
control is kept below (`bytes_order_ambiguous`, with the positional reader defined locally) beside
its named counterpart (`named_tag_disjoint`).

**The one exception to non-distribution.** A required field whose type is a union of literals,
first in canonical order: splitting it is membership-preserving (`fits_field_split`, at any name;
`_tag` included), so a normalization that split a `_tag` union would keep `hasTy_normalize` (an
option, not landed here); the tag decision refuses such a column (`taggedColumn` admits only a
single literal tag).
-/

set_option autoImplicit false

namespace ProbeP

open Effect4 Effect4.Machine
open ProbeP.Field ProbeP.Ty

/-! ## The tag, by name -/

/-- A record is tagged `tag` when its `_tag` field is required at the literal `tag`. -/
def recordTag? (fs : List (String × Bool × Ty)) : Option String :=
  match firstOf "_tag" fs with
  | some (false, .lit t) => some t
  | _ => none

/-- **A tagged record's value names its tag (proved).** -/
theorem fits_tagged_name (w : World) {fs : List (String × Bool × Ty)} {tag : String}
    (ht : recordTag? fs = some tag) {v : Val} (hv : Fits w v (.record fs)) :
    ∃ ns xs, v = .ctor 0 [.list ns, .list xs] ∧ lookupName "_tag" ns xs = some (.str tag) := by
  unfold recordTag? at ht
  cases hf : firstOf "_tag" fs with
  | none => rw [hf] at ht; cases ht
  | some ot =>
    obtain ⟨o, t⟩ := ot
    rw [hf] at ht
    cases o
    case true => cases ht
    case false =>
      cases t
      case lit s =>
        have hst : s = tag := Option.some.inj ht
        subst hst
        have hfc : firstOf "_tag" (canonF fs) = some (false, .lit s) :=
          (firstOf_canonBy fieldKey_injective "_tag" fs).trans hf
        have hmem : ("_tag", (false, Ty.lit s)) ∈ canonF fs := firstOf_mem hfc
        obtain ⟨ns, xs, hparts, hfit⟩ := fits_record_inv w v fs hv
        obtain ⟨x, hx⟩ := namedFit_required _ ns xs hfit
          (List.mem_map.mpr ⟨("_tag", false, .lit s), hmem, rfl⟩)
        obtain ⟨p, hp, hpn, hpx⟩ := namedFit_lookup _ ns xs hfit hx
        rw [List.mem_map] at hp
        obtain ⟨⟨n', o', t'⟩, hq, rfl⟩ := hp
        simp only at hpn
        subst hpn
        have hft : firstOf "_tag" (canonF fs) = some (o', t') :=
          firstOf_of_nodup (canonBy_names_nodup fs) hq
        rw [hfc] at hft
        cases hft
        have hxs : Fits w x (.lit s) := hpx
        simp only [Fits] at hxs
        split at hxs
        · rename_i s'
          subst hxs
          exact ⟨ns, xs, recordParts?_eq_some hparts, hx⟩
        · exact hxs.elim
      all_goals cases ht

/-- **Tagged records are disjoint by their tag (proved), under the plain byte order.** -/
theorem tagged_disjoint (w : World) {fs gs : List (String × Bool × Ty)} {a b : String}
    (ha : recordTag? fs = some a) (hb : recordTag? gs = some b) {v : Val}
    (hfa : Fits w v (.record fs)) (hfb : Fits w v (.record gs)) : a = b := by
  obtain ⟨ns1, xs1, h1, hl1⟩ := fits_tagged_name w ha hfa
  obtain ⟨ns2, xs2, h2, hl2⟩ := fits_tagged_name w hb hfb
  rw [h1] at h2
  injection h2 with _ h3
  injection h3 with h4 h5
  injection h5 with h6 _
  injection h4 with hns
  injection h6 with hxs
  subst hns
  subst hxs
  rw [hl1] at hl2
  injection hl2 with h7
  injection h7

/-! ## The tag decision's record arm -/

/-- `isTagged` (`Ty.lean:774`), with the record arm. -/
def isTagged (tag : String) : Ty → Bool
  | .prod (.lit t) _ => decide (t = tag)
  | .record fs => decide (recordTag? fs = some tag)
  | _ => false

/-- `diffTag` (`Ty.lean:782`), copied. -/
def diffTag (tag : String) (t : Ty) : Ty :=
  ofMembers (t.members.filter fun m => !isTagged tag m)

/-- The tag a record value names, read type-blind. -/
def nameTag? (ns xs : List Val) : Option String :=
  match lookupName "_tag" ns xs with
  | some (.str t) => some t
  | _ => none

/-- The runtime tag test (`Machine/Term.lean:361`), with the record arm: the `_tag` name. -/
def tagHit (tag : String) : Val → Bool
  | .list [.str t, _] => decide (t = tag)
  | .ctor 0 [.list ns, .list xs] => decide (nameTag? ns xs = some tag)
  | _ => false

/-- A tagged member and a value of it: the tag test answers `true`. -/
theorem tagHit_of_isTagged (w : World) (tag : String) (m : Ty) (v : Val)
    (hm : isTagged tag m = true) (hv : Fits w v m) : tagHit tag v = true := by
  cases m
  case prod a b =>
    cases a
    case lit t =>
      simp only [isTagged, decide_eq_true_eq] at hm
      subst hm
      obtain ⟨p, q, rfl, hp, _⟩ := (fits_prod_iff w v (.lit t) b).mp hv
      simp only [Fits] at hp
      split at hp
      · rename_i s
        rw [hp]
        exact decide_eq_true rfl
      · exact hp.elim
    all_goals simp only [isTagged, Bool.false_eq_true] at hm
  case record fs =>
    have ht : recordTag? fs = some tag := by
      simp only [isTagged, decide_eq_true_eq] at hm
      exact hm
    obtain ⟨ns, xs, rfl, hl⟩ := fits_tagged_name w ht hv
    show decide (nameTag? ns xs = some tag) = true
    unfold nameTag?
    rw [hl]
    exact decide_eq_true rfl
  all_goals simp only [isTagged, Bool.false_eq_true] at hm

/-- **`diffTag_sound` at records (proved):** a value of the column on which the tag test is
false is a value of the residual. -/
theorem diffTag_sound (w : World) (tag : String) (t : Ty) (v : Val) (hv : Fits w v t)
    (hmiss : tagHit tag v = false) : Fits w v (diffTag tag t) := by
  unfold diffTag
  rw [fits_ofMembers]
  obtain ⟨m, hm, hvm⟩ := (fits_members w v t).mpr hv
  refine ⟨m, List.mem_filter.mpr ⟨hm, ?_⟩, hvm⟩
  cases htag : isTagged tag m
  · rfl
  · rw [tagHit_of_isTagged w tag m v htag hvm] at hmiss
    exact Bool.noConfusion hmiss

/-- The payload of a member carrying `tag` (`Ty.lean:798`), with the record arm: the record. -/
def payloadOf (tag : String) : Ty → Option Ty
  | .prod (.lit t) p => if t = tag then some p else none
  | .record fs => if recordTag? fs = some tag then some (.record fs) else none
  | _ => none

def payloadTy (tag : String) (t : Ty) : Option Ty :=
  match t.members.filterMap (payloadOf tag) with
  | [] => none
  | ps => some (normalize (ofMembers ps))

/-- A member a tag decision can select on: a literal-tagged pair, a tagged record, a scalar. -/
def columnMember : Ty → Bool
  | .prod (.lit _) _ => true
  | .record fs => (recordTag? fs).isSome
  | .unit | .nat | .int | .string | .bool | .lit _ => true
  | _ => false

/-- A tag decision's column (`Ty.lean:790`), with the record arm. -/
def taggedColumn (t : Ty) : Bool := t.members.all columnMember

/-- The value a hit binds: a pair's second component, a record's whole value. -/
def tagPayload? (tag : String) : Val → Option Val
  | .list [.str t, p] => if t = tag then some p else none
  | .ctor 0 [.list ns, .list xs] =>
    if nameTag? ns xs = some tag then some (.ctor 0 [.list ns, .list xs]) else none
  | _ => none

/-- **`payload_hasTy` at records (proved):** on a tagged column, a hit's payload is a member of
the payload type. -/
theorem payload_hasTy (w : World) (tag : String) (c : Ty) (v p : Val) (P : Ty)
    (hc : taggedColumn c = true) (hv : Fits w v c)
    (hp : tagPayload? tag v = some p) (hP : payloadTy tag c = some P) : Fits w p P := by
  obtain ⟨m, hm, hvm⟩ := (fits_members w v c).mpr hv
  have hcm : columnMember m = true := List.all_eq_true.mp hc m hm
  -- the member that admits the hit carries `tag`, and the payload fits its payload
  have hmem : ∃ q ∈ c.members.filterMap (payloadOf tag), Fits w p q := by
    cases m
    case prod a b =>
      cases a
      case lit t =>
        obtain ⟨x, y, rfl, hx, hy⟩ := (fits_prod_iff w v (.lit t) b).mp hvm
        simp only [Fits] at hx
        split at hx
        · rename_i s
          subst hx
          simp only [tagPayload?] at hp
          by_cases hst : s = tag
          · subst hst
            rw [if_pos rfl, Option.some.injEq] at hp
            subst hp
            refine ⟨b, List.mem_filterMap.mpr ⟨.prod (.lit s) b, hm, ?_⟩, hy⟩
            simp only [payloadOf, ↓reduceIte]
          · rw [if_neg hst] at hp
            cases hp
        · exact hx.elim
      all_goals simp only [columnMember, Bool.false_eq_true] at hcm
    case record fs =>
      obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hcm
      obtain ⟨ns, xs, rfl, hl⟩ := fits_tagged_name w ht hvm
      have hnt : nameTag? ns xs = some t := by
        unfold nameTag?
        rw [hl]
      simp only [tagPayload?, hnt] at hp
      by_cases hst : t = tag
      · subst hst
        rw [if_pos rfl, Option.some.injEq] at hp
        subst hp
        refine ⟨.record fs, List.mem_filterMap.mpr ⟨.record fs, hm, ?_⟩, hvm⟩
        simp only [payloadOf, ht, ↓reduceIte]
      · rw [if_neg (fun h => hst (Option.some.inj h))] at hp
        cases hp
    case unit =>
      simp only [Fits] at hvm
      split at hvm
      · simp only [tagPayload?, reduceCtorEq] at hp
      · exact hvm.elim
    case nat =>
      simp only [Fits] at hvm
      split at hvm
      · simp only [tagPayload?, reduceCtorEq] at hp
      · exact hvm.elim
    case int =>
      have hi : intImage v = true := hvm
      unfold intImage at hi
      split at hi
      · simp only [tagPayload?, reduceCtorEq] at hp
      · simp only [tagPayload?, reduceCtorEq] at hp
      · exact Bool.noConfusion hi
    case string =>
      simp only [Fits] at hvm
      split at hvm
      · simp only [tagPayload?, reduceCtorEq] at hp
      · exact hvm.elim
    case bool =>
      simp only [Fits] at hvm
      split at hvm
      · simp only [tagPayload?, reduceCtorEq] at hp
      · exact hvm.elim
    case lit s =>
      simp only [Fits] at hvm
      split at hvm
      · simp only [tagPayload?, reduceCtorEq] at hp
      · exact hvm.elim
    all_goals simp only [columnMember, Bool.false_eq_true] at hcm
  obtain ⟨q, hq, hpq⟩ := hmem
  unfold payloadTy at hP
  cases hfm : c.members.filterMap (payloadOf tag) with
  | nil => rw [hfm] at hq; exact absurd hq List.not_mem_nil
  | cons q0 qs =>
    rw [hfm] at hP hq
    simp only [Option.some.injEq] at hP
    subst hP
    rw [fits_normalize, fits_ofMembers]
    exact ⟨q, hq, hpq⟩

/-! ## The exception: a required field that is a union, first in canonical order -/

/-- **Splitting a canonical record at its first field's union keeps membership (proved).** -/
theorem fits_field_split (w : World) (n : String) (a b : Ty) (rest : List (String × Bool × Ty))
    (hasc : Field.Ascending fieldKey ((n, false, Ty.union a b) :: rest)) (v : Val) :
    Fits w v (.record ((n, false, .union a b) :: rest)) ↔
      Fits w v (.record ((n, false, a) :: rest)) ∨ Fits w v (.record ((n, false, b) :: rest)) := by
  have hasc' : ∀ t : Ty, Field.Ascending fieldKey ((n, false, t) :: rest) := by
    intro t
    unfold Field.Ascending at hasc ⊢
    rw [List.pairwise_cons] at hasc ⊢
    exact ⟨fun q hq => hasc.1 q hq, hasc.2⟩
  have hc : ∀ t : Ty, canonF ((n, false, t) :: rest) = (n, false, t) :: rest :=
    fun t => canonBy_of_ascending _ (hasc' t)
  cases hv : recordParts? v with
  | none =>
    rw [fits_record_none w hv, fits_record_none w hv, fits_record_none w hv]
    exact ⟨False.elim, fun h => h.elim id id⟩
  | some parts =>
    obtain ⟨ns, xs⟩ := parts
    rw [fits_record w hv, fits_record w hv, fits_record w hv, hc, hc, hc]
    simp only [List.map_cons, fitterOf]
    match ns, xs with
    | [], [] => exact ⟨fun h => absurd h.1 Bool.false_ne_true, fun h => h.elim (fun h => absurd h.1 Bool.false_ne_true) (fun h => absurd h.1 Bool.false_ne_true)⟩
    | [], _ :: _ => exact ⟨fun h => h.elim, fun h => h.elim (fun h => h.elim) (fun h => h.elim)⟩
    | v0 :: _, [] =>
      cases v0 <;> exact ⟨fun h => h.elim, fun h => h.elim (fun h => h.elim) (fun h => h.elim)⟩
    | v0 :: ns, x :: xs =>
      cases v0 with
      | str k =>
        by_cases hk : k = n
        · subst hk
          rw [namedFit_cons_eq, namedFit_cons_eq, namedFit_cons_eq]
          constructor
          · rintro ⟨hx | hx, hr⟩
            · exact Or.inl ⟨hx, hr⟩
            · exact Or.inr ⟨hx, hr⟩
          · rintro (⟨hx, hr⟩ | ⟨hx, hr⟩)
            · exact ⟨Or.inl hx, hr⟩
            · exact ⟨Or.inr hx, hr⟩
        · simp only [NamedFit]
          rw [if_neg hk, if_neg hk, if_neg hk]
          exact ⟨fun h => absurd h.1 Bool.false_ne_true,
            fun h => h.elim (fun h => absurd h.1 Bool.false_ne_true) (fun h => absurd h.1 Bool.false_ne_true)⟩
      | _ => exact ⟨fun h => h.elim, fun h => h.elim (fun h => h.elim) (fun h => h.elim)⟩

/-! ## The red control: the positional clause at the plain byte order -/

/-- The positional reader (commit `1b069d15`'s `fieldsHasTy`), kept here for the red control. -/
def fieldsHasTyPos : List Val → List (String × Bool × (Val → Bool)) → Bool
  | [], [] => true
  | x :: xs, (_, _, c) :: cs => c x && fieldsHasTyPos xs cs
  | _, _ => false

/-- A positional record check at a chosen field order. -/
def recordCheckPos (key : String → List Nat) (fs : List (String × Bool × Ty)) : Val → Bool
  | .ctor 0 vs => fieldsHasTyPos vs ((canonBy key fs).map fun q => (q.1, checkerOf [] q.2))
  | _ => false

def tagA : List (String × Bool × Ty) := [("_tag", false, .lit "A"), ("X", false, .string)]
def tagB : List (String × Bool × Ty) := [("_tag", false, .lit "B"), ("y", false, .string)]

/-- **RED CONTROL (proved), positional:** under the plain byte order one positional value fits two
records with different tags (`"X" < "_tag"` puts `A`'s tag in slot 1, `B`'s in slot 0). -/
theorem bytes_order_ambiguous :
    recordCheckPos bytesKey tagA (.ctor 0 [.str "B", .str "A"]) = true ∧
      recordCheckPos bytesKey tagB (.ctor 0 [.str "B", .str "A"]) = true := by
  decide +kernel

/-- **Named, at the same byte order (proved):** each record's value names its fields, so the two
records' values differ and each fits one record only. -/
theorem named_tag_disjoint :
    hasTy (.ctor 0 [.list [.str "X", .str "_tag"], .list [.str "B", .str "A"]]) (.record tagA) [] = true ∧
      hasTy (.ctor 0 [.list [.str "X", .str "_tag"], .list [.str "B", .str "A"]]) (.record tagB) [] = false ∧
      hasTy (.ctor 0 [.list [.str "_tag", .str "y"], .list [.str "B", .str "A"]]) (.record tagB) [] = true ∧
      hasTy (.ctor 0 [.list [.str "_tag", .str "y"], .list [.str "B", .str "A"]]) (.record tagA) [] = false := by
  decide +kernel

#guard taggedColumn (.union (.record tagA) (.record tagB))
#guard !taggedColumn (.record [("_tag", false, .union (.lit "A") (.lit "B")), ("x", false, .nat)])
#guard isTagged "A" (.record tagA) && !isTagged "B" (.record tagA)
#guard diffTag "A" (.union (.record tagA) (.record tagB)) = .record tagB
#guard tagHit "B" (.ctor 0 [.list [.str "_tag", .str "y"], .list [.str "B", .str "z"]]) &&
  !tagHit "A" (.ctor 0 [.list [.str "_tag", .str "y"], .list [.str "B", .str "z"]])
#guard tagHit "A" (.ctor 0 [.list [.str "X", .str "_tag"], .list [.str "x", .str "A"]])

end ProbeP

#print axioms ProbeP.fits_tagged_name
#print axioms ProbeP.tagged_disjoint
#print axioms ProbeP.tagHit_of_isTagged
#print axioms ProbeP.diffTag_sound
#print axioms ProbeP.payload_hasTy
#print axioms ProbeP.fits_field_split
#print axioms ProbeP.bytes_order_ambiguous
#print axioms ProbeP.named_tag_disjoint
