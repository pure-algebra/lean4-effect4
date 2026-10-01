import P4Algebra
import Effect4.Program.Typed

/-!
# Seat P: the executable value check on the copy (type-language probe, 2026-10-01)

Research probe. A copy of `Val.hasTy` (`src/Effect4/Program/Typed.lean:34-101` at `bff50631`)
over `ProbeP.Ty`, with the record and map arms, and its laws: `hasTy_sub` (membership respects
`sub`), `hasTy_normalize` (R3.2, no premise), the join laws, and the named incompleteness
`record_sub_not_complete` (TY-10).

**The record arm reads the canonical order, as a fold.** The arm builds one checker per written
field (`checkers`, the field-list companion of the structural recursion), sorts the *checkers*
with the payload-polymorphic `canonF`, and reads the value's arguments positionally against
them. The recursion never sorts types, so it stays structural (`Val.keys`/`Val.keysList` is the
estate's precedent for such a companion). An optional field's slot holds `none` (the key absent)
or `some x` (present with `x`); the wrapper is needed because a present value may itself be
`none` (an optional field of `option` type).

**The map arm**: a map value is `list [pair k₁ v₁, …]` (the store's image of an association list,
`Image.list (Image.pair …)`), keys strictly ascending in the admitted key order (`keyLt`: strings
by UTF-8 bytes, naturals numerically), every key a member of the key type, every value of the
value type.
-/

set_option autoImplicit false

namespace ProbeP

open Effect4.Machine
open ProbeP.Field ProbeP.Ty

/-- Every typed failure of a cause has an image satisfying `member` (`causeAdmits`'s shape,
`Program/ErrorImage.lean:44`, with the type argument dropped: it is not read). -/
def causeAdmitsP (member : Val → Bool) (c : CauseV) : Bool :=
  c.reasons.all fun r =>
    match r with
    | .fail e _ =>
      match Effect4.Program.valOfErr e with
      | some v => member v
      | none => false
    | .die _ _ | .interrupt _ _ => true

theorem causeAdmitsP_mono {f g : Val → Bool} (h : ∀ w, f w = true → g w = true) (c : CauseV)
    (hc : causeAdmitsP f c = true) : causeAdmitsP g c = true := by
  unfold causeAdmitsP at hc ⊢
  rw [List.all_eq_true] at hc ⊢
  intro r hr
  have hrc := hc r hr
  match r, hrc with
  | .fail e ann, hrc =>
    show (match Effect4.Program.valOfErr e with | some v => g v | none => false) = true
    revert hrc
    show (match Effect4.Program.valOfErr e with | some v => f v | none => false) = true → _
    cases Effect4.Program.valOfErr e with
    | none => intro hrc; exact hrc
    | some w => intro hrc; exact h w hrc
  | .die _ _, _ => rfl
  | .interrupt _ _, _ => rfl

/-- One slot against one canonical field: a required field's slot is the value; an optional
field's slot is `none` (absent) or `some x` (present). -/
def slotHasTy (optional : Bool) (check : Val → Bool) (x : Val) : Bool :=
  if optional then
    match x with
    | .none => true
    | .some y => check y
    | _ => false
  else check x

/-- The arguments of a record value against the canonical checkers, one for one. -/
def fieldsHasTy : List Val → List (String × Bool × (Val → Bool)) → Bool
  | [], [] => true
  | x :: xs, (_, o, c) :: cs => slotHasTy o c x && fieldsHasTy xs cs
  | _, _ => false

/-- The admitted map-key order: strings by UTF-8 bytes, naturals numerically. -/
def keyLt : Val → Val → Bool
  | .str a, .str b => Effect4.Program.Ty.ltKey (bytesKey a) (bytesKey b)
  | .nat m, .nat n => decide (m < n)
  | _, _ => false

/-- The entries of a map value: pairs, keys strictly ascending. -/
def sortedEntries : List Val → Bool
  | [] => true
  | [.pair _ _] => true
  | .pair a _ :: .pair b y :: rest => keyLt a b && sortedEntries (.pair b y :: rest)
  | _ => false

/-- Every entry is a pair whose key and value pass their checks. -/
def entriesHasTy (ck cv : Val → Bool) (es : List Val) : Bool :=
  sortedEntries es && es.all fun e =>
    match e with
    | .pair a x => ck a && cv x
    | _ => false

mutual
/-- `Val.hasTy`, copied, with two arms. -/
def hasTy (v : Val) (ty : Ty) (allocated : List String) : Bool :=
  match ty with
  | .unit => match v with | .unit => true | _ => false
  | .nat => match v with | .nat _ => true | _ => false
  | .bool => match v with | .bool _ => true | _ => false
  | .string => match v with | .str _ => true | _ => false
  | .option inner =>
    match v with
    | .none => true
    | .some x => hasTy x inner allocated
    | _ => false
  | .handle target =>
    match v with
    | .handle kind index =>
      match HandleKind.ofByte? kind with
      | some .cell => target == Effect4.Program.NativeOp.refTarget
      | some .promise => target == Effect4.Program.NativeOp.deferredTarget
      | some .scope => target == Effect4.Program.Ty.scopeTarget
      | some .external =>
        Effect4.Program.externalHandleTarget target && allocated[index]? == some target
      | _ => false
    | _ => target == Effect4.Program.Ty.contextTarget && (Val.context? v).isSome
  | .fiberOf _ _ => match v with | Value.fiber _ => true | _ => false
  | .refOf _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .cell
    | _ => false
  | .deferredOf _ _ =>
    match v with
    | .handle kind _ => HandleKind.ofByte? kind == some .promise
    | _ => false
  | .var _ => false
  | .exitOf a e =>
    match v with
    | Val.exitOk x => hasTy x a allocated
    | Value.exitErr written =>
      match causeImage.ofVal written with
      | some c => causeAdmitsP (fun w => hasTy w e allocated) c
      | none => false
    | _ => false
  | .causeOf e =>
    match Val.cause? v with
    | some c => causeAdmitsP (fun w => hasTy w e allocated) c
    | none => false
  | .prod ta tb =>
    match v with
    | .list [x, y] => hasTy x ta allocated && hasTy y tb allocated
    | _ => false
  | .list ty =>
    match v with
    | Value.fiberSnapshot _ =>
      match Val.snapshot? v with
      | some ids => ids.all (fun id => hasTy (Val.fiber id) ty allocated)
      | none => false
    | .list values => values.all fun x => hasTy x ty allocated
    | _ => false
  | .union l r => hasTy v l allocated || hasTy v r allocated
  | .lit value => match v with | .str s => s == value | _ => false
  | .never => false
  | .unknown => true
  | .int => false
  | .except error value =>
    match v with
    | .ctor 0 [err] => hasTy err error allocated
    | .ctor 1 [val] => hasTy val value allocated
    | _ => false
  -- record: the value's arguments against the canonical checkers
  | .record fs =>
    match v with
    | .ctor 0 vs => fieldsHasTy vs (canonF (checkers fs allocated))
    | _ => false
  -- map: sorted pairs, keys of the key type, values of the value type
  | .map k t =>
    match v with
    | .list es => entriesHasTy (fun a => hasTy a k allocated) (fun x => hasTy x t allocated) es
    | _ => false
/-- The field-list companion: one checker per written field, in written order. -/
def checkers (fs : List (String × Bool × Ty)) (allocated : List String) :
    List (String × Bool × (Val → Bool)) :=
  match fs with
  | [] => []
  | (n, o, t) :: rest => (n, o, fun x => hasTy x t allocated) :: checkers rest allocated
end

/-- A field's checker. -/
def checkerOf (allocated : List String) (c : Bool × Ty) : Bool × (Val → Bool) :=
  (c.1, fun x => hasTy x c.2 allocated)

/-- The companion is a payload map. -/
theorem checkers_eq_map (fs : List (String × Bool × Ty)) (allocated : List String) :
    checkers fs allocated = fs.map (fun q => (q.1, checkerOf allocated q.2)) := by
  induction fs with
  | nil => rfl
  | cons p fs ih =>
    obtain ⟨n, o, t⟩ := p
    rw [checkers, ih]
    rfl

/-- The record arm, read through the canonical fields. -/
theorem hasTy_record (vs : List Val) (fs : List (String × Bool × Ty)) (allocated : List String) :
    hasTy (.ctor 0 vs) (.record fs) allocated =
      fieldsHasTy vs ((canonF fs).map (fun q => (q.1, checkerOf allocated q.2))) := by
  rw [hasTy, checkers_eq_map, canonBy_map]

/-! ## Membership respects `sub` -/

theorem slotHasTy_mono {o : Bool} {c d : Val → Bool} (h : ∀ x, c x = true → d x = true) (x : Val)
    (hx : slotHasTy o c x = true) : slotHasTy o d x = true := by
  unfold slotHasTy at hx ⊢
  cases o
  · exact h x hx
  · cases x
    case some y => exact h y hx
    all_goals exact hx

/-- Pointwise stronger checkers under one head admit more. -/
theorem fieldsHasTy_mono :
    ∀ (vs : List Val) (cf cg : List (String × Bool × (Val → Bool))),
      cf.map (fun p => (p.1, p.2.1)) = cg.map (fun p => (p.1, p.2.1)) →
      (∀ p ∈ cf.zip cg, ∀ x, p.1.2.2 x = true → p.2.2.2 x = true) →
      fieldsHasTy vs cf = true → fieldsHasTy vs cg = true
  | [], [], [], _, _, _ => rfl
  | x :: xs, (n, o, c) :: cf, (m, p, d) :: cg, hh, hpt, h => by
    simp only [List.map_cons, List.cons.injEq, Prod.mk.injEq] at hh
    obtain ⟨⟨-, hop⟩, hrest⟩ := hh
    simp only [fieldsHasTy, Bool.and_eq_true] at h ⊢
    refine ⟨?_, fieldsHasTy_mono xs cf cg hrest
      (fun q hq => hpt q (List.mem_cons_of_mem _ hq)) h.2⟩
    rw [← hop]
    exact slotHasTy_mono (hpt ((n, o, c), (m, p, d)) List.mem_cons_self) x h.1
  | [], [], _ :: _, hh, _, _ => nomatch hh
  | [], _ :: _, [], hh, _, _ => nomatch hh
  | [], _ :: _, _ :: _, _, _, h => nomatch h
  | _ :: _, [], [], _, _, h => nomatch h
  | _ :: _, [], _ :: _, hh, _, _ => nomatch hh
  | _ :: _, _ :: _, [], hh, _, _ => nomatch hh

theorem sortedEntries_entries {ck cv ck' cv' : Val → Bool} (hk : ∀ a, ck a = true → ck' a = true)
    (hv : ∀ x, cv x = true → cv' x = true) (es : List Val)
    (h : entriesHasTy ck cv es = true) : entriesHasTy ck' cv' es = true := by
  unfold entriesHasTy at h ⊢
  rw [Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, fun e he => ?_⟩
  have := h.2 e he
  cases e
  case pair a x =>
    simp only [Bool.and_eq_true] at this ⊢
    exact ⟨hk a this.1, hv x this.2⟩
  all_goals exact this

/-- **Membership respects `sub`** (`hasTy_sub`; production derives it from `cata_admits_sub`,
whose `AdmitsSub` gains a record field and a map field). By `fun_induction sub`. -/
theorem hasTy_sub {a b : Ty} (hsub : sub a b = true) :
    ∀ v allocated, hasTy v a allocated = true → hasTy v b allocated = true := by
  fun_induction sub a b
  case case1 => intro v al h; exact h
  case case2 => intro v al h; simp only [hasTy, Bool.false_eq_true] at h
  case case3 a1 a2 b _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy, Bool.or_eq_true] at h
    exact h.elim (iha h1 v al) (ihb h2 v al)
  case case4 a b1 b2 _ _ _ iha ihb =>
    intro v al h
    simp only [hasTy, Bool.or_eq_true]
    exact (Bool.or_eq_true_iff.mp hsub).elim (fun hx => Or.inl (iha hx v al h))
      (fun hx => Or.inr (ihb hx v al h))
  case case5 => intro v al _; simp only [hasTy]
  case case6 =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rfl
    · exact Bool.noConfusion h
  case case7 x y _ ih =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rfl
    · rename_i z
      exact ih hsub z al h
    · exact Bool.noConfusion h
  case case8 x y _ ih =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rename_i p
      split at h
      · rename_i ids hids
        simp only [List.all_eq_true] at h ⊢
        exact fun id hid => ih hsub _ al (h id hid)
      · exact Bool.noConfusion h
    · rw [List.all_eq_true] at h ⊢
      exact fun z hz => ih hsub z al (h z hz)
    · exact Bool.noConfusion h
  case case9 a1 a2 b1 b2 _ iha ihb =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rw [Bool.and_eq_true] at h ⊢
      exact ⟨iha h1 _ al h.1, ihb h2 _ al h.2⟩
    · exact Bool.noConfusion h
  case case10 e1 a1 e2 a2 _ ihe iha =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · exact ihe h1 _ al h
    · exact iha h2 _ al h
    · exact Bool.noConfusion h
  case case11 a1 e1 a2 e2 _ iha ihe =>
    obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp hsub
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · exact iha h1 _ al h
    · split at h
      · rename_i c _
        exact causeAdmitsP_mono (fun w hw => ihe h2 w al hw) c h
      · exact Bool.noConfusion h
    · exact Bool.noConfusion h
  case case12 e1 e2 _ ih =>
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · rename_i c _
      exact causeAdmitsP_mono (fun w hw => ih hsub w al hw) c h
    · exact Bool.noConfusion h
  case case13 =>
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case14 =>
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case15 =>
    intro v al h
    simp only [hasTy] at h ⊢
    exact h
  case case16 fs gs _ ih =>
    obtain ⟨hh, hall⟩ := Bool.and_eq_true_iff.mp hsub
    have hh' : heads (canonF fs) = heads (canonF gs) := of_decide_eq_true hh
    have hall' : ((canonF fs).zip (canonF gs)).all (fun pq => sub pq.1.2.2 pq.2.2.2) = true := by
      rw [← all_zip_attach (fun p q : String × Bool × Ty => sub p.2.2 q.2.2)]
      exact hall
    rw [List.all_eq_true] at hall'
    intro v al h
    cases v
    case ctor i vs =>
      cases i
      case zero =>
        rw [hasTy_record] at h ⊢
        refine fieldsHasTy_mono vs _ _ ?_ ?_ h
        · simp only [List.map_map]
          exact hh'
        · intro p hp x hx
          rw [List.zip_map, List.mem_map] at hp
          obtain ⟨⟨q1, q2⟩, hq, rfl⟩ := hp
          have hq1 : q1 ∈ canonF fs := (List.of_mem_zip hq).1
          have hq2 : q2 ∈ canonF gs := (List.of_mem_zip hq).2
          exact ih ⟨⟨q1, hq1⟩, ⟨q2, hq2⟩⟩ (hall' (q1, q2) hq) x al hx
      case succ n => simp only [hasTy, Bool.false_eq_true] at h
    all_goals simp only [hasTy, Bool.false_eq_true] at h
  case case17 k1 v1 k2 v2 _ ihk _ ihv =>
    obtain ⟨hk12, hv⟩ := Bool.and_eq_true_iff.mp hsub
    obtain ⟨hk, _⟩ := Bool.and_eq_true_iff.mp hk12
    intro v al h
    simp only [hasTy] at h ⊢
    split at h
    · exact sortedEntries_entries (fun a ha => ihk hk a al ha) (fun x hx => ihv hv x al hx) _ h
    · exact Bool.noConfusion h
  case case18 => exact Bool.noConfusion hsub

/-! ## Normalization keeps membership (R3.2), no premise -/

/-- copied. -/
theorem hasTy_ofMembers (v : Val) (xs : List Ty) (al : List String) :
    hasTy v (ofMembers xs) al = xs.any (fun t => hasTy v t al) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => simp only [ofMembers, List.any_cons, List.any_nil, Bool.or_false]
    | cons y ys =>
      change (hasTy v x al || hasTy v (ofMembers (y :: ys)) al) = _
      rw [ih]
      rfl

/-- copied text (rewritten without the production's `try`). -/
theorem hasTy_members (v : Val) (t : Ty) (al : List String) :
    t.members.any (fun t => hasTy v t al) = hasTy v t al := by
  induction t with
  | union a b iha ihb =>
    rw [members, List.any_append, iha, ihb]
    simp only [hasTy]
  | never => simp only [members, List.any_nil, hasTy]
  | _ => simp only [members, List.any_cons, List.any_nil, Bool.or_false]

/-- copied. -/
theorem any_row_normalize (xs : List Ty) (p : Ty → Bool) :
    (Effect4.Row.normalize xs).elems.any p = xs.any p := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mp ht, hp⟩
  · rintro ⟨t, ht, hp⟩
    exact ⟨t, (Effect4.Row.mem_normalize t xs).mpr ht, hp⟩

/-- copied. -/
theorem hasTy_normalizeRow (v : Val) (xs : List Ty) (al : List String) :
    (normalizeRow xs).elems.any (fun t => hasTy v t al) = xs.any (fun t => hasTy v t al) := by
  rw [← any_row_normalize xs (fun t => hasTy v t al)]
  apply Bool.eq_iff_iff.mpr
  simp only [normalizeRow, List.any_eq_true]
  constructor
  · rintro ⟨t, ht, hv⟩
    exact ⟨t, Effect4.Row.antichain_subset sub ht, hv⟩
  · rintro ⟨t, ht, hv⟩
    obtain ⟨u, hu, htu⟩ := Effect4.Row.antichain_coverage sub sub_refl sub_trans
      (Effect4.Row.normalize xs).elems t ht
    exact ⟨u, hu, hasTy_sub htu v al hv⟩

/-- copied. -/
theorem hasTy_factors (v : Val) (t : Ty) (al : List String) :
    t.factors.any (fun t => hasTy v t al) = hasTy v t al := by
  cases t with
  | never => rfl
  | _ => exact hasTy_members v _ al

/-- copied. -/
theorem hasTy_productMembers (v : Val) (a b : Ty) (al : List String) :
    (productMembers a b).any (fun t => hasTy v t al) = hasTy v (.prod a b) al := by
  simp only [productMembers, List.any_flatMap, List.any_map, Function.comp_def]
  simp only [hasTy]
  split
  · rename_i x y
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, Bool.and_eq_true]
    constructor
    · rintro ⟨ta, hta, tb, htb, hx, hy⟩
      exact ⟨(Bool.eq_iff_iff.mp (hasTy_factors x a al)).mp (List.any_eq_true.mpr ⟨ta, hta, hx⟩),
        (Bool.eq_iff_iff.mp (hasTy_factors y b al)).mp (List.any_eq_true.mpr ⟨tb, htb, hy⟩)⟩
    · rintro ⟨hx, hy⟩
      obtain ⟨ta, hta, hx⟩ := List.any_eq_true.mp ((Bool.eq_iff_iff.mp (hasTy_factors x a al)).mpr hx)
      obtain ⟨tb, htb, hy⟩ := List.any_eq_true.mp ((Bool.eq_iff_iff.mp (hasTy_factors y b al)).mpr hy)
      exact ⟨ta, hta, tb, htb, hx, hy⟩
  · apply List.any_eq_false.mpr
    intro x _ h
    obtain ⟨_, _, h⟩ := List.any_eq_true.mp h
    exact Bool.false_ne_true h

theorem causeAdmitsP_congr {f g : Val → Bool} (h : ∀ w, f w = g w) (c : CauseV) :
    causeAdmitsP f c = causeAdmitsP g c := by
  rw [show f = g from funext h]

/-- new: the record case of `hasTy_normalize`. The canonical read is invariant because
normalizing a record maps its canonical list, and the checker of a normalized field type is
the checker of the field type (the induction hypothesis). -/
theorem hasTy_normalize_record (fs : List (String × Bool × Ty)) (v : Val) (al : List String)
    (ih : ∀ p ∈ fs, ∀ v, hasTy v (normalize p.2.2) al = hasTy v p.2.2 al) :
    hasTy v (normalize (.record fs)) al = hasTy v (.record fs) al := by
  rw [normalize_record]
  cases v
  case ctor i vs =>
    cases i
    case zero =>
      rw [hasTy_record, hasTy_record,
        canonBy_of_ascending _ (ascending_map normPayload (canonBy_ascending fs)), List.map_map]
      congr 1
      apply List.map_congr_left
      intro q hq
      have hfun : (fun x => hasTy x (normalize q.2.2) al) = fun x => hasTy x q.2.2 al :=
        funext fun x => ih q (mem_canonBy hq) x
      simp only [Function.comp_apply, checkerOf, normPayload]
      rw [hfun]
    case succ n => rfl
  all_goals rfl

/-- **Normalization keeps membership at every type, with no premise.** case: two (record,
map); the production proof's other arms are its named congruence facts, inlined here. -/
theorem hasTy_normalize (t : Ty) (v : Val) (al : List String) :
    hasTy v t.normalize al = hasTy v t al := by
  induction t generalizing v with
  | never => rfl
  | unknown | unit | nat | int | string | bool | handle | lit | fiberOf | refOf | deferredOf | var => rfl
  | union a b iha ihb =>
    rw [normalize, hasTy_ofMembers, hasTy_normalizeRow, List.any_append,
      hasTy_members, hasTy_members, iha, ihb]
    rfl
  | prod a b iha ihb =>
    rw [normalize, hasTy_ofMembers, hasTy_normalizeRow, hasTy_productMembers]
    simp only [hasTy]
    split
    · rw [iha, ihb]
    · rfl
  | option t ih =>
    show hasTy v (.option t.normalize) al = hasTy v (.option t) al
    simp only [hasTy]
    split
    · rfl
    · exact ih _
    · rfl
  | list t ih =>
    show hasTy v (.list t.normalize) al = hasTy v (.list t) al
    simp only [hasTy]
    split
    · split
      · exact List.all_congr rfl (fun id => ih (Val.fiber id))
      · rfl
    · exact List.all_congr rfl ih
    · rfl
  | except e a ihe iha =>
    show hasTy v (.except e.normalize a.normalize) al = hasTy v (.except e a) al
    simp only [hasTy]
    split
    · exact ihe _
    · exact iha _
    · rfl
  | exitOf a e iha ihe =>
    show hasTy v (.exitOf a.normalize e.normalize) al = hasTy v (.exitOf a e) al
    simp only [hasTy]
    split
    · exact iha _
    · split
      · exact causeAdmitsP_congr ihe _
      · rfl
    · rfl
  | causeOf e ih =>
    show hasTy v (.causeOf e.normalize) al = hasTy v (.causeOf e) al
    simp only [hasTy]
    split
    · exact causeAdmitsP_congr ih _
    · rfl
  | record fs ih => exact hasTy_normalize_record fs v al (fun p hp w => ih p hp w)
  | map k t ihk iht =>
    show hasTy v (.map k.normalize t.normalize) al = hasTy v (.map k t) al
    simp only [hasTy]
    split
    · rw [show (fun a => hasTy a k.normalize al) = (fun a => hasTy a k al) from funext ihk,
        show (fun x => hasTy x t.normalize al) = (fun x => hasTy x t al) from funext iht]
    · rfl

/-- copied: membership in the join. -/
theorem hasTy_join_left (a b : Ty) (v : Val) (al : List String) (hv : hasTy v a al = true) :
    hasTy v (join a b) al = true := by
  rw [← hasTy_normalize a v al] at hv
  exact hasTy_sub (sub_normalize_union_left a b) v al hv

theorem hasTy_join_right (a b : Ty) (v : Val) (al : List String) (hv : hasTy v b al = true) :
    hasTy v (join a b) al = true := by
  rw [← hasTy_normalize b v al] at hv
  exact hasTy_sub (sub_normalize_union_right a b) v al hv

/-! ## The named incompleteness (TY-10) and the controls -/

/-- A record with one union-typed field, and the union of the two records it would distribute
into. Records are factors (row 119 (d)): `normalize` keeps the first as one member. -/
def recordOfUnion : Ty := .record [("a", false, .union .nat .string)]
def unionOfRecords : Ty := .union (.record [("a", false, .nat)]) (.record [("a", false, .string)])

/-- A one-field record's check, read without the sort. -/
theorem hasTy_record_one (vs : List Val) (n : String) (o : Bool) (t : Ty) (al : List String) :
    hasTy (.ctor 0 vs) (.record [(n, o, t)]) al = fieldsHasTy vs [(n, o, fun x => hasTy x t al)] := by
  rw [hasTy_record]
  rfl

/-- **`record_sub_not_complete`** (proved): the two have exactly the same members, the second is
below the first, and the first is not below the second. The `sub_not_complete` kind
(`Laws/Program/Template.lean:322`), at records. -/
theorem record_sub_not_complete :
    (∀ v al, hasTy v recordOfUnion al = hasTy v unionOfRecords al) ∧
      sub unionOfRecords recordOfUnion = true ∧ sub recordOfUnion unionOfRecords = false := by
  refine ⟨fun v al => ?_, by decide +kernel, by decide +kernel⟩
  cases v
  case ctor i vs =>
    cases i
    case zero =>
      show hasTy (.ctor 0 vs) (.record [("a", false, .union .nat .string)]) al =
        (hasTy (.ctor 0 vs) (.record [("a", false, .nat)]) al ||
          hasTy (.ctor 0 vs) (.record [("a", false, .string)]) al)
      rw [hasTy_record_one, hasTy_record_one, hasTy_record_one]
      match vs with
      | [] => rfl
      | [x] => simp only [fieldsHasTy, slotHasTy, Bool.false_eq_true, ↓reduceIte, Bool.and_true, hasTy]
      | _ :: _ :: _ => simp only [fieldsHasTy, Bool.and_false, Bool.or_false]
    case succ n => rfl
  all_goals rfl

-- The normal form keeps the record of a union as one member (records are factors), while a
-- product of the same union distributes.
#guard (normalize recordOfUnion).members.length = 1
#guard (normalize (.prod (.union .nat .string) .unit)).members.length = 2
-- TY-10's positive control: a permuted record is raw-below its normal form.
#guard sub (.record [("b", false, .nat), ("a", false, .string)])
  (normalize (.record [("b", false, .nat), ("a", false, .string)]))
-- membership reads canonical order: the value laid out for `{a; b}` fits the permuted spelling
#guard hasTy (.ctor 0 [.str "x", .nat 1]) (.record [("b", false, .nat), ("a", false, .string)]) []
#guard hasTy (.ctor 0 [.str "x", .nat 1]) (normalize (.record [("b", false, .nat), ("a", false, .string)])) []
-- an optional slot: absent, present, and a present `none` at an option-typed optional field
#guard hasTy (.ctor 0 [.none]) (.record [("a", true, .nat)]) []
#guard hasTy (.ctor 0 [.some (.nat 3)]) (.record [("a", true, .nat)]) []
#guard !hasTy (.ctor 0 [.nat 3]) (.record [("a", true, .nat)]) []
#guard hasTy (.ctor 0 [.some .none]) (.record [("a", true, .option .nat)]) []
#guard hasTy (.ctor 0 [.none]) (.record [("a", true, .option .nat)]) []
-- a map: sorted distinct keys only
#guard hasTy (.list [.pair (.str "a") (.nat 1), .pair (.str "b") (.nat 2)]) (.map .string .nat) []
#guard !hasTy (.list [.pair (.str "b") (.nat 1), .pair (.str "a") (.nat 2)]) (.map .string .nat) []
#guard !hasTy (.list [.pair (.str "a") (.nat 1), .pair (.str "a") (.nat 2)]) (.map .string .nat) []
#guard hasTy (.list []) (.map .string .never) []

end ProbeP

#print axioms ProbeP.hasTy_record
#print axioms ProbeP.fieldsHasTy_mono
#print axioms ProbeP.hasTy_sub
#print axioms ProbeP.hasTy_members
#print axioms ProbeP.hasTy_normalizeRow
#print axioms ProbeP.hasTy_productMembers
#print axioms ProbeP.hasTy_normalize_record
#print axioms ProbeP.hasTy_normalize
#print axioms ProbeP.hasTy_join_left
#print axioms ProbeP.hasTy_join_right
#print axioms ProbeP.record_sub_not_complete
