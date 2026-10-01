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

**The obstacle found, and its repair (proved).** With the plain UTF-8 byte order the `_tag`
field's slot depends on the other names (`"X" < "_tag" < "y"`, `"_id" < "_tag"`), so one positional
value fits two records with different tags (`bytes_order_ambiguous`), and a runtime tag test on an
untyped value cannot find the tag. The copy's order is discriminant-first (`fieldKey`): `_tag` is
always slot 0 (`tag_head`), so tagged records are disjoint by their tag (`tagged_disjoint`) and
the record arm of `tagHit` reads slot 0, as the pair arm does.

**The one exception to non-distribution.** A `_tag` field whose type is a union of literals: the
tag decision refuses the column (`taggedColumn` admits only a single literal tag), and splitting
it is membership-preserving (`fits_tag_split`), so a normalization that split it would keep
`hasTy_normalize` (an option, not landed here).
-/

set_option autoImplicit false

namespace ProbeP

open Effect4 Effect4.Machine
open ProbeP.Field ProbeP.Ty

/-! ## The discriminant slot -/

/-- `_tag`'s key is below every other name's. -/
theorem tag_key_least (n : String) (hn : n ≠ "_tag") :
    Effect4.Program.Ty.ltKey (fieldKey n) (fieldKey "_tag") = false := by
  show Effect4.Program.Ty.ltKey (tagFirstKey n) (tagFirstKey "_tag") = false
  unfold tagFirstKey
  rw [if_neg hn, if_pos rfl]
  rfl

/-- **In a canonical field list, a `_tag` field is the first.** -/
theorem tag_head {β : Type} : ∀ {l : List (String × β)}, Ascending fieldKey l → ∀ {b : β},
    ("_tag", b) ∈ l → ∃ rest, l = ("_tag", b) :: rest
  | [], _, _, hmem => absurd hmem List.not_mem_nil
  | (n, c) :: rest, hasc, b, hmem => by
    rcases List.mem_cons.mp hmem with h | h
    · exact ⟨rest, h ▸ rfl⟩
    · have hlt := (List.pairwise_cons.mp hasc).1 ("_tag", b) h
      by_cases hn : n = "_tag"
      · subst hn
        rw [ltKey_irrefl] at hlt
        exact Bool.noConfusion hlt
      · rw [tag_key_least n hn] at hlt
        exact Bool.noConfusion hlt

/-- A record is tagged `tag` when its `_tag` field is required at the literal `tag`. -/
def recordTag? (fs : List (String × Bool × Ty)) : Option String :=
  match firstOf "_tag" fs with
  | some (false, .lit t) => some t
  | _ => none

/-- **A tagged record's value starts with its tag (proved).** -/
theorem fits_tagged_head (w : World) {fs : List (String × Bool × Ty)} {tag : String}
    (ht : recordTag? fs = some tag) {v : Val} (hv : Fits w v (.record fs)) :
    ∃ rest, v = .ctor 0 (.str tag :: rest) := by
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
        obtain ⟨rest, hrest⟩ := tag_head (canonBy_ascending fs) (firstOf_mem hfc)
        obtain ⟨vs, rfl, hvs⟩ := fits_record_inv w v fs hv
        rw [hrest] at hvs
        cases vs with
        | nil => exact hvs.elim
        | cons x xs =>
          have hx : Fits w x (.lit s) := hvs.1
          simp only [Fits] at hx
          split at hx
          · rename_i s'
            rw [hx]
            exact ⟨xs, rfl⟩
          · exact hx.elim
      all_goals cases ht

/-- **Tagged records are disjoint by their tag (proved).** -/
theorem tagged_disjoint (w : World) {fs gs : List (String × Bool × Ty)} {a b : String}
    (ha : recordTag? fs = some a) (hb : recordTag? gs = some b) {v : Val}
    (hfa : Fits w v (.record fs)) (hfb : Fits w v (.record gs)) : a = b := by
  obtain ⟨r1, h1⟩ := fits_tagged_head w ha hfa
  obtain ⟨r2, h2⟩ := fits_tagged_head w hb hfb
  rw [h1] at h2
  injection h2 with _ h3
  injection h3 with h4 _
  injection h4

/-! ## The tag decision's record arm -/

/-- `isTagged` (`Ty.lean:774`), with the record arm. -/
def isTagged (tag : String) : Ty → Bool
  | .prod (.lit t) _ => decide (t = tag)
  | .record fs => decide (recordTag? fs = some tag)
  | _ => false

/-- `diffTag` (`Ty.lean:782`), copied. -/
def diffTag (tag : String) (t : Ty) : Ty :=
  ofMembers (t.members.filter fun m => !isTagged tag m)

/-- The runtime tag test (`Machine/Term.lean:361`), with the record arm: slot 0. -/
def tagHit (tag : String) : Val → Bool
  | .list [.str t, _] => decide (t = tag)
  | .ctor 0 (.str t :: _) => decide (t = tag)
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
    obtain ⟨rest, rfl⟩ := fits_tagged_head w ht hv
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
  | .ctor 0 (.str t :: rest) => if t = tag then some (.ctor 0 (.str t :: rest)) else none
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
      obtain ⟨rest, rfl⟩ := fits_tagged_head w ht hvm
      simp only [tagPayload?] at hp
      by_cases hst : t = tag
      · subst hst
        rw [if_pos rfl, Option.some.injEq] at hp
        subst hp
        refine ⟨.record fs, List.mem_filterMap.mpr ⟨.record fs, hm, ?_⟩, hvm⟩
        simp only [payloadOf, ht, ↓reduceIte]
      · rw [if_neg hst] at hp
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
    case int => exact hvm.elim
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

/-! ## The exception: a `_tag` field that is a union of literals -/

/-- **Splitting a canonical record at its leading `_tag` union keeps membership (proved).** -/
theorem fits_tag_split (w : World) (a b : Ty) (rest : List (String × Bool × Ty))
    (hasc : Field.Ascending fieldKey (("_tag", false, Ty.union a b) :: rest)) (v : Val) :
    Fits w v (.record (("_tag", false, .union a b) :: rest)) ↔
      Fits w v (.record (("_tag", false, a) :: rest)) ∨ Fits w v (.record (("_tag", false, b) :: rest)) := by
  have hasc' : ∀ t : Ty, Field.Ascending fieldKey (("_tag", false, t) :: rest) := by
    intro t
    unfold Field.Ascending at hasc ⊢
    rw [List.pairwise_cons] at hasc ⊢
    exact ⟨fun q hq => hasc.1 q hq, hasc.2⟩
  have hc : ∀ t : Ty, canonF (("_tag", false, t) :: rest) = ("_tag", false, t) :: rest :=
    fun t => canonBy_of_ascending _ (hasc' t)
  constructor
  · intro h
    obtain ⟨vs, rfl, hv⟩ := fits_record_inv w v _ h
    rw [hc] at hv
    cases vs with
    | nil => exact hv.elim
    | cons x xs =>
      rcases hv.1 with hx | hx
      · left
        rw [fits_record, hc]
        exact ⟨hx, hv.2⟩
      · right
        rw [fits_record, hc]
        exact ⟨hx, hv.2⟩
  · rintro (h | h)
    · obtain ⟨vs, rfl, hv⟩ := fits_record_inv w v _ h
      rw [hc] at hv
      rw [fits_record, hc]
      cases vs with
      | nil => exact hv.elim
      | cons x xs => exact ⟨Or.inl hv.1, hv.2⟩
    · obtain ⟨vs, rfl, hv⟩ := fits_record_inv w v _ h
      rw [hc] at hv
      rw [fits_record, hc]
      cases vs with
      | nil => exact hv.elim
      | cons x xs => exact ⟨Or.inr hv.1, hv.2⟩

/-! ## The red control: the plain byte order -/

/-- A record check at a chosen field order (the copy's `hasTy_record`, with the key a parameter). -/
def recordCheckBy (key : String → List Nat) (fs : List (String × Bool × Ty)) : Val → Bool
  | .ctor 0 vs => fieldsHasTy vs ((canonBy key fs).map fun q => (q.1, checkerOf [] q.2))
  | _ => false

def tagA : List (String × Bool × Ty) := [("_tag", false, .lit "A"), ("X", false, .string)]
def tagB : List (String × Bool × Ty) := [("_tag", false, .lit "B"), ("y", false, .string)]

/-- **RED CONTROL (proved):** under the plain byte order one value fits two records with
different tags (`"X" < "_tag"` puts `A`'s tag in slot 1, `B`'s in slot 0). -/
theorem bytes_order_ambiguous :
    recordCheckBy bytesKey tagA (.ctor 0 [.str "B", .str "A"]) = true ∧
      recordCheckBy bytesKey tagB (.ctor 0 [.str "B", .str "A"]) = true := by
  decide +kernel

/-- Under the discriminant-first order (the copy's), the same value fits only `B`. -/
theorem tagFirst_order_disjoint :
    recordCheckBy fieldKey tagA (.ctor 0 [.str "B", .str "A"]) = false ∧
      recordCheckBy fieldKey tagB (.ctor 0 [.str "B", .str "A"]) = true := by
  decide +kernel

#guard hasTy (.ctor 0 [.str "B", .str "A"]) (.record tagA) [] = false
#guard hasTy (.ctor 0 [.str "B", .str "A"]) (.record tagB) [] = true
#guard taggedColumn (.union (.record tagA) (.record tagB))
#guard !taggedColumn (.record [("_tag", false, .union (.lit "A") (.lit "B")), ("x", false, .nat)])
#guard isTagged "A" (.record tagA) && !isTagged "B" (.record tagA)
#guard diffTag "A" (.union (.record tagA) (.record tagB)) = .record tagB
#guard tagHit "B" (.ctor 0 [.str "B", .str "y"]) && !tagHit "A" (.ctor 0 [.str "B", .str "y"])

end ProbeP

#print axioms ProbeP.tag_key_least
#print axioms ProbeP.tag_head
#print axioms ProbeP.fits_tagged_head
#print axioms ProbeP.tagged_disjoint
#print axioms ProbeP.tagHit_of_isTagged
#print axioms ProbeP.diffTag_sound
#print axioms ProbeP.payload_hasTy
#print axioms ProbeP.fits_tag_split
#print axioms ProbeP.bytes_order_ambiguous
#print axioms ProbeP.tagFirst_order_disjoint
