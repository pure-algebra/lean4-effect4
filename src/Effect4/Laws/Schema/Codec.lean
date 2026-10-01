import Effect4.Schema.Codec
import Effect4.Laws.Program.Admits

/-! S-3 checked JSON boundary laws, under the owner's 2026-09-11 admission amendment, and the
pair's exactness (decisions row 128).

The S-3 laws' type parameters range over canonical types. Exact recovery is conditional on
executable value admission; subtype agreement also requires the conservative structural
`Codec.Compatible` certificate. No host theorem or claim of completeness for the compatibility test
is made.

**Exactness** (row 128; the vocabulary's exact embedding, `AGENTS.md`): the JSON pair is exact
modulo `Codec.normJ`, the key-order normaliser (`Schema/Codec.lean`), at every type, canonical or
not (`encode` and `decode` normalize the type first):

    decode t j = some v ↔ ∃ j', encode t v = some j' ∧ normJ j' = normJ j      (`decode_iff`)

Its two halves are `decode_of_encode` (the retraction) and `encode_of_decode` (exactness). They rest
on two facts about the raw pair, each by induction over the type: the decoder reads `normJ`'s
quotient (`Codec.decodeRaw_normJ`: `fields?` and `payload?` commute with the sort, through its
permutation lemma), and every JSON the raw decoder reads is the raw encoder's image of the value it
returns, modulo `normJ` (`Codec.decodeRaw_exact`; the union arm is where the canonical-branch repair
is read). The proofs are seat P's (`docs/research/2026-10-01-type-language-probe/P/probes/P8Codec.lean`,
on today's functions) with the repaired decoder in place of the probe's copy. Not claimed: that the
repair left the checked encoder's domain unchanged (it agrees on the contract's cases; the repaired
decoder answers differently from the old one only on JSON the old one read at a non-canonical
branch). -/

set_option autoImplicit false

namespace Effect4.Schema.Codec
open Effect4 Effect4.Program Effect4.Machine

/-! ## `N_J`'s equations; the sort is a permutation -/

theorem normJs_eq_map (js : List Json) : normJs js = js.map normJ := by
  induction js with
  | nil => rfl
  | cons j js ih => rw [normJs, ih]; rfl

theorem normEs_eq_map (es : List (String × Json)) :
    normEs es = es.map (fun e => (e.1, normJ e.2)) := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨k, j⟩ := e
    rw [normEs, ih]
    rfl

theorem normJ_arr (js : List Json) : normJ (.arr js) = .arr (js.map normJ) := by
  rw [normJ, normJs_eq_map]

theorem normJ_obj (es : List (String × Json)) :
    normJ (.obj es) = .obj (sortE (es.map (fun e => (e.1, normJ e.2)))) := by
  rw [normJ, normEs_eq_map]

theorem insertE_perm (e : String × Json) : ∀ l : List (String × Json), (insertE e l).Perm (e :: l)
  | [] => List.Perm.refl _
  | f :: fs => by
    unfold insertE
    split
    · exact List.Perm.refl _
    · exact ((insertE_perm e fs).cons f).trans (List.Perm.swap e f fs)

/-- The sort is a permutation: `normJ` reorders an object's entries and drops none. -/
theorem sortE_perm (es : List (String × Json)) : (sortE es).Perm es := by
  have step : ∀ (l acc : List (String × Json)),
      (l.foldl (fun acc e => insertE e acc) acc).Perm (acc ++ l) := by
    intro l
    induction l with
    | nil => intro acc; simp only [List.foldl_nil, List.append_nil, List.Perm.refl]
    | cons e l ih =>
      intro acc
      rw [List.foldl_cons]
      exact (ih (insertE e acc)).trans
        (((insertE_perm e acc).append_right l).trans List.perm_middle.symm)
  have := step es []
  rwa [List.nil_append] at this

/-! ## The object reader is order-blind: `fields?` and `payload?` commute with `N_J` -/

/-- The value of a list's only entry. -/
def single? : List (String × Json) → Option Json
  | [(_, value)] => some value
  | _ => none

theorem single?_perm : ∀ {l1 l2 : List (String × Json)}, l1.Perm l2 → single? l1 = single? l2
  | [], l2, h => by rw [List.Perm.nil_eq h]
  | [a], l2, h => by rw [List.singleton_perm.mp h]
  | a :: b :: r, l2, h => by
    have hlen := h.length_eq
    match l2, hlen with
    | [], hlen => exact nomatch hlen
    | [_], hlen => exact nomatch hlen
    | _ :: _ :: _, _ => rfl

theorem single?_map (f : Json → Json) : ∀ l : List (String × Json),
    single? (l.map (fun e => (e.1, f e.2))) = (single? l).map f
  | [] => rfl
  | [_] => rfl
  | _ :: _ :: _ => rfl

/-- `fields?`'s per-name pick. -/
def pick (es : List (String × Json)) (name : String) : Option Json :=
  single? (es.filter (fun entry => entry.1 == name))

theorem fields?_obj (es : List (String × Json)) (names : List String) :
    fields? (.obj es) names =
      if (es.length != names.length) = true then none else names.mapM (pick es) := by
  rfl

theorem pick_normJ (es : List (String × Json)) (name : String) :
    pick (sortE (es.map (fun e => (e.1, normJ e.2)))) name = (pick es name).map normJ := by
  unfold pick
  rw [single?_perm ((sortE_perm _).filter _), List.filter_map]
  have hcomp : ((fun entry : String × Json => entry.1 == name) ∘ (fun e => (e.1, normJ e.2))) =
      (fun entry : String × Json => entry.1 == name) := rfl
  rw [hcomp, single?_map]

theorem mapM_map_option {α β γ : Type} (f : α → Option β) (g : β → γ) :
    ∀ l : List α, l.mapM (fun a => (f a).map g) = (l.mapM f).map (List.map g)
  | [] => rfl
  | a :: l => by
    rw [List.mapM_cons, List.mapM_cons, mapM_map_option f g l]
    cases f a with
    | none => rfl
    | some b =>
      cases l.mapM f with
      | none => rfl
      | some bs => rfl

/-- `fields?` reads `N_J`'s quotient: the sort changes no pick. -/
theorem fields?_normJ (j : Json) (names : List String) :
    fields? (normJ j) names = (fields? j names).map (List.map normJ) := by
  cases j with
  | obj es =>
    rw [normJ_obj, fields?_obj, fields?_obj, (sortE_perm _).length_eq, List.length_map]
    by_cases hlen : (es.length != names.length) = true
    · rw [if_pos hlen, if_pos hlen]
      rfl
    · rw [if_neg hlen, if_neg hlen, ← mapM_map_option]
      congr 1
      funext name
      exact pick_normJ es name
  | _ => rfl

theorem payload?_eq (j : Json) (tag field : String) :
    payload? j tag field = (fields? j ["_tag", field]).bind (fun l => match l with
      | [.str actual, payload] => if actual = tag then some payload else none
      | _ => none) := rfl

/-- `N_J` keeps a node's kind: a string stays the string. -/
theorem normJ_eq_str {x : Json} {s : String} : normJ x = .str s ↔ x = .str s := by
  cases x with
  | str t => exact Iff.rfl
  | arr js => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | obj es => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | null => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | bool b => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | number f => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- The tagged-pair pattern `payload?` reads commutes with `N_J`. -/
theorem tagPattern_normJ (tag : String) : ∀ l : List Json,
    (match l.map normJ with
      | [.str actual, payload] => if actual = tag then some payload else none
      | _ => none) =
    (match l with
      | [.str actual, payload] => if actual = tag then some payload else none
      | _ => none).map normJ
  | [] => rfl
  | [a] => by cases a <;> rfl
  | [x, y] => by
    cases x with
    | str a =>
      show (if a = tag then some (normJ y) else none) = (if a = tag then some y else none).map normJ
      by_cases h : a = tag
      · rw [if_pos h, if_pos h]
        rfl
      · rw [if_neg h, if_neg h]
        rfl
    | arr _ => rfl
    | obj _ => rfl
    | null => rfl
    | bool _ => rfl
    | number _ => rfl
  | a :: _ :: _ :: _ => by cases a <;> rfl

theorem payload?_normJ (j : Json) (tag field : String) :
    payload? (normJ j) tag field = (payload? j tag field).map normJ := by
  rw [payload?_eq, payload?_eq, fields?_normJ]
  cases fields? j ["_tag", field] with
  | none => rfl
  | some l => exact tagPattern_normJ tag l

theorem nat?_normJ (j : Json) : nat? (normJ j) = nat? j := by
  cases j <;> rfl

theorem mapM_map_comp {α β γ : Type} (f : α → β) (g : β → Option γ) :
    ∀ l : List α, (l.map f).mapM g = l.mapM (fun a => g (f a))
  | [] => rfl
  | a :: l => by
    rw [List.map_cons, List.mapM_cons, List.mapM_cons, mapM_map_comp f g l]

/-- A sorted object of two or more entries is one of two or more entries. -/
theorem sortE_two (e1 e2 : String × Json) (rest : List (String × Json)) :
    ∃ a b r, sortE ((e1 :: e2 :: rest).map (fun e => (e.1, normJ e.2))) = a :: b :: r := by
  have hlen := (sortE_perm ((e1 :: e2 :: rest).map (fun e => (e.1, normJ e.2)))).length_eq
  generalize sortE ((e1 :: e2 :: rest).map (fun e => (e.1, normJ e.2))) = l at hlen
  match l, hlen with
  | [], h => exact nomatch h
  | [_], h => exact nomatch h
  | a :: b :: r, _ => exact ⟨a, b, r, rfl⟩

/-- An object of one entry not named `boom` is no error image. -/
theorem decodeErr_obj_ne {k : String} (hk : k ≠ "boom") (y : Json) :
    decodeErr (.obj [(k, y)]) = none := by
  unfold decodeErr
  split
  · rename_i heq
    injection heq with heq
    injection heq with heq
    injection heq with hk' _
    exact absurd hk' hk
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rfl

/-- An object of two or more entries is no error image. -/
theorem decodeErr_obj_two (e f : String × Json) (r : List (String × Json)) :
    decodeErr (.obj (e :: f :: r)) = none := by
  unfold decodeErr
  split
  · rename_i heq
    injection heq with heq
    injection heq with _ heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rfl

theorem decodeErr_normJ (j : Json) : decodeErr (normJ j) = decodeErr j := by
  cases j with
  | arr js =>
    rw [normJ_arr]
    match js with
    | [] => rfl
    | [x] => cases x <;> rfl
    | [x, y] => cases x <;> cases y <;> rfl
    | a :: b :: _ :: _ => cases a <;> cases b <;> rfl
  | obj es =>
    rw [normJ_obj]
    match es with
    | [] => rfl
    | [(k, x)] =>
      show decodeErr (.obj [(k, normJ x)]) = decodeErr (.obj [(k, x)])
      by_cases hk : k = "boom"
      · subst hk
        cases x <;> rfl
      · rw [decodeErr_obj_ne hk, decodeErr_obj_ne hk]
    | e1 :: e2 :: rest =>
      obtain ⟨a, b, r, hab⟩ := sortE_two e1 e2 rest
      rw [hab, decodeErr_obj_two, decodeErr_obj_two]
  | _ => rfl

/-- An object of two or more entries is no defect image. -/
theorem decodeDefect_obj_two (e f : String × Json) (r : List (String × Json)) :
    decodeDefect (.obj (e :: f :: r)) = none := by
  unfold decodeDefect
  split
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rfl

/-- An object of one entry named neither `user` nor `error` is no defect image. -/
theorem decodeDefect_obj_other {k : String} (hu : k ≠ "user") (he : k ≠ "error") (y : Json) :
    decodeDefect (.obj [(k, y)]) = none := by
  unfold decodeDefect
  split
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    exact nomatch heq
  · rename_i heq
    injection heq with heq
    injection heq with heq
    injection heq with hk _
    exact absurd hk hu
  · rename_i heq
    injection heq with heq
    injection heq with heq
    injection heq with hk _
    exact absurd hk he
  · rfl

theorem decodeDefect_normJ (j : Json) : decodeDefect (normJ j) = decodeDefect j := by
  cases j with
  | obj es =>
    rw [normJ_obj]
    match es with
    | [] => rfl
    | [(k, x)] =>
      show decodeDefect (.obj [(k, normJ x)]) = decodeDefect (.obj [(k, x)])
      by_cases hu : k = "user"
      · subst hu
        show (nat? (normJ x)).map Defect.user = (nat? x).map Defect.user
        rw [nat?_normJ]
      · by_cases he : k = "error"
        · subst he
          show (decodeErr (normJ x)).map Defect.error = (decodeErr x).map Defect.error
          rw [decodeErr_normJ]
        · rw [decodeDefect_obj_other hu he, decodeDefect_obj_other hu he]
    | e1 :: e2 :: rest =>
      obtain ⟨a, b, r, hab⟩ := sortE_two e1 e2 rest
      rw [hab, decodeDefect_obj_two, decodeDefect_obj_two]
  | arr js =>
    rw [normJ_arr]
    rfl
  | _ => rfl

theorem decodeReason_normJ (dec : Json → Option Val) (hdec : ∀ j, dec (normJ j) = dec j)
    (j : Json) : decodeReason dec (normJ j) = decodeReason dec j := by
  unfold decodeReason
  rw [payload?_normJ, payload?_normJ, payload?_normJ]
  cases payload? j "Fail" "error" with
  | some p =>
    simp only [Option.map_some]
    rw [hdec]
  | none =>
    cases payload? j "Die" "defect" with
    | some p =>
      simp only [Option.map_some, Option.map_none]
      rw [decodeDefect_normJ]
    | none =>
      cases payload? j "Interrupt" "fiberId" with
      | some p =>
        simp only [Option.map_some, Option.map_none]
        cases p <;> rfl
      | none => rfl

theorem decodeCause_normJ (dec : Json → Option Val) (hdec : ∀ j, dec (normJ j) = dec j)
    (j : Json) : decodeCause dec (normJ j) = decodeCause dec j := by
  cases j with
  | arr rs =>
    rw [normJ_arr]
    show ((rs.map normJ).mapM (decodeReason dec)).map (fun rs => (⟨rs⟩ : CauseV)) =
      (rs.mapM (decodeReason dec)).map (fun rs => (⟨rs⟩ : CauseV))
    rw [mapM_map_comp]
    simp only [decodeReason_normJ dec hdec]
  | obj es =>
    rw [normJ_obj]
    rfl
  | _ => rfl

theorem fields?_tag_normJ (j : Json) (s : String) :
    (fields? (normJ j) ["_tag"] = some [.str s]) ↔ (fields? j ["_tag"] = some [.str s]) := by
  rw [fields?_normJ]
  cases fields? j ["_tag"] with
  | none => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | some l =>
    match l with
    | [] => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
    | [x] =>
      constructor
      · intro h
        simp only [Option.map_some, List.map_cons, List.map_nil, Option.some.injEq,
          List.cons.injEq, and_true] at h
        rw [normJ_eq_str.mp h]
      · intro h
        simp only [Option.some.injEq, List.cons.injEq, and_true] at h
        rw [h]
        rfl
    | _ :: _ :: _ =>
      constructor
      · intro h
        simp only [Option.map_some, List.map_cons, Option.some.injEq, List.cons.injEq,
          reduceCtorEq, and_false] at h
      · intro h
        simp only [Option.some.injEq, List.cons.injEq, reduceCtorEq, and_false] at h

/-- **The decoder reads `N_J`'s quotient** (every arm, the cause, reason, defect and error
decoders included): a JSON and its key-sorted form decode alike. -/
theorem decodeRaw_normJ : ∀ (t : Ty) (j : Json), decodeRaw t (normJ j) = decodeRaw t j := by
  intro t
  induction t with
  | unit => intro j; cases j <;> rfl
  | bool => intro j; cases j <;> rfl
  | string => intro j; cases j <;> rfl
  | lit _ => intro j; cases j <;> rfl
  | nat =>
    intro j
    show (nat? (normJ j)).map Val.nat = (nat? j).map Val.nat
    rw [nat?_normJ]
  | option t ih =>
    intro j
    rw [decodeRaw, decodeRaw]
    by_cases hn : fields? j ["_tag"] = some [.str "None"]
    · rw [if_pos ((fields?_tag_normJ j "None").mpr hn), if_pos hn]
    · rw [if_neg (fun h => hn ((fields?_tag_normJ j "None").mp h)), if_neg hn, payload?_normJ]
      cases payload? j "Some" "value" with
      | none => rfl
      | some p =>
        show (decodeRaw t (normJ p)).map Store.Val.some = (decodeRaw t p).map Store.Val.some
        rw [ih]
  | list t ih =>
    intro j
    cases j with
    | arr js =>
      rw [normJ_arr]
      show ((js.map normJ).mapM (decodeRaw t)).map Val.list = (js.mapM (decodeRaw t)).map Val.list
      rw [mapM_map_comp]
      simp only [ih]
    | obj es => rw [normJ_obj]; rfl
    | _ => rfl
  | prod a b iha ihb =>
    intro j
    cases j with
    | arr js =>
      rw [normJ_arr]
      match js with
      | [] => rfl
      | [_] => rfl
      | [jx, jy] =>
        show (do let x ← decodeRaw a (normJ jx); let y ← decodeRaw b (normJ jy); return Val.list [x, y]) =
          (do let x ← decodeRaw a jx; let y ← decodeRaw b jy; return Val.list [x, y])
        rw [iha, ihb]
      | _ :: _ :: _ :: _ => rfl
    | obj es => rw [normJ_obj]; rfl
    | _ => rfl
  | except e a ihe iha =>
    intro j
    rw [decodeRaw, decodeRaw, payload?_normJ, payload?_normJ]
    cases payload? j "Failure" "failure" with
    | some p =>
      show (decodeRaw e (normJ p)).map _ = (decodeRaw e p).map _
      rw [ihe]
    | none =>
      cases payload? j "Success" "success" with
      | some p =>
        show (decodeRaw a (normJ p)).map _ = (decodeRaw a p).map _
        rw [iha]
      | none => rfl
  | exitOf a e iha ihe =>
    intro j
    rw [decodeRaw, decodeRaw, payload?_normJ, payload?_normJ]
    cases payload? j "Success" "value" with
    | some p =>
      show (decodeRaw a (normJ p)).map _ = (decodeRaw a p).map _
      rw [iha]
    | none =>
      cases payload? j "Failure" "cause" with
      | some p =>
        show (decodeCause (decodeRaw e) (normJ p)).map Val.exitErr =
          (decodeCause (decodeRaw e) p).map Val.exitErr
        rw [decodeCause_normJ (decodeRaw e) ihe]
      | none => rfl
  | causeOf e ih =>
    intro j
    show (decodeCause (decodeRaw e) (normJ j)).map Val.exitErr =
      (decodeCause (decodeRaw e) j).map Val.exitErr
    rw [decodeCause_normJ (decodeRaw e) ih]
  | union a b iha ihb =>
    intro j
    rw [decodeRaw, decodeRaw, iha, ihb]
  | _ => intro j; rfl

/-! ## Exactness: every JSON the raw decoder reads is the raw encoder's image, modulo `N_J` -/

theorem nat?_exact {j : Json} {n : Nat} (h : nat? j = some n) : j = Arch.Json.ofNat n := by
  cases j with
  | number f =>
    have key : ∀ m : Nat, (if Arch.Json.ofNat m = Json.number f then some m else none) = some n →
        Json.number f = Arch.Json.ofNat n := by
      intro m hm
      split at hm
      · rename_i heq
        cases hm
        exact heq.symm
      · exact nomatch hm
    unfold nat? at h
    dsimp only at h
    split at h
    · rename_i h0
      cases h
      obtain ⟨b⟩ := f
      have hb : b = 0 := UInt64.toNat_inj.mp h0
      subst hb
      rfl
    · split at h
      · exact nomatch h
      · exact key _ h
  | _ => exact nomatch h

/-- `fields?` succeeds on an object of the expected length whose every name is picked. -/
theorem fields?_some {j : Json} {names : List String} {l : List Json} (h : fields? j names = some l) :
    ∃ es, j = .obj es ∧ es.length = names.length ∧ names.mapM (pick es) = some l := by
  cases j with
  | obj es =>
    rw [fields?_obj] at h
    split at h
    · exact nomatch h
    · rename_i hlen
      exact ⟨es, rfl, bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hlen), h⟩
  | _ => exact nomatch h

theorem pick_single {k' k : String} {x' x : Json} (h : pick [(k', x')] k = some x) :
    k' = k ∧ x' = x := by
  unfold pick at h
  cases hk : k' == k with
  | true =>
    simp only [List.filter, hk, single?, Option.some.injEq] at h
    exact ⟨beq_iff_eq.mp hk, h⟩
  | false =>
    simp only [List.filter, hk, single?, reduceCtorEq] at h

theorem pick_pair {e1 e2 : String × Json} {k : String} {x : Json} (h : pick [e1, e2] k = some x) :
    (e1 = (k, x) ∧ e2.1 ≠ k) ∨ (e2 = (k, x) ∧ e1.1 ≠ k) := by
  obtain ⟨k1, v1⟩ := e1
  obtain ⟨k2, v2⟩ := e2
  unfold pick at h
  cases h1 : k1 == k <;> cases h2 : k2 == k
  · simp only [List.filter, h1, h2, single?, reduceCtorEq] at h
  · simp only [List.filter, h1, h2, single?, Option.some.injEq] at h
    subst h
    rw [beq_iff_eq.mp h2]
    exact Or.inr ⟨rfl, beq_eq_false_iff_ne.mp h1⟩
  · simp only [List.filter, h1, h2, single?, Option.some.injEq] at h
    subst h
    rw [beq_iff_eq.mp h1]
    exact Or.inl ⟨rfl, beq_eq_false_iff_ne.mp h2⟩
  · simp only [List.filter, h1, h2, single?, reduceCtorEq] at h

theorem fields?_one {j : Json} {k : String} {x : Json} (h : fields? j [k] = some [x]) :
    j = .obj [(k, x)] := by
  obtain ⟨es, rfl, hlen, hm⟩ := fields?_some h
  match es, hlen, hm with
  | [(k', x')], _, hm =>
    rw [List.mapM_cons, List.mapM_nil] at hm
    cases hp : pick [(k', x')] k with
    | none => rw [hp] at hm; exact nomatch hm
    | some y =>
      rw [hp] at hm
      cases hm
      obtain ⟨rfl, rfl⟩ := pick_single hp
      rfl

theorem fields?_two {j : Json} {k1 k2 : String} (hne : k1 ≠ k2) {x1 x2 : Json}
    (h : fields? j [k1, k2] = some [x1, x2]) :
    j = .obj [(k1, x1), (k2, x2)] ∨ j = .obj [(k2, x2), (k1, x1)] := by
  obtain ⟨es, rfl, hlen, hm⟩ := fields?_some h
  match es, hlen, hm with
  | [e1, e2], _, hm =>
    rw [List.mapM_cons, List.mapM_cons, List.mapM_nil] at hm
    cases hp1 : pick [e1, e2] k1 with
    | none => rw [hp1] at hm; exact nomatch hm
    | some y1 =>
      cases hp2 : pick [e1, e2] k2 with
      | none => rw [hp1, hp2] at hm; exact nomatch hm
      | some y2 =>
        rw [hp1, hp2] at hm
        cases hm
        rcases pick_pair hp1 with ⟨rfl, _⟩ | ⟨rfl, _⟩
        · rcases pick_pair hp2 with ⟨heq, _⟩ | ⟨rfl, _⟩
          · exact absurd (congrArg Prod.fst heq) hne
          · exact Or.inl rfl
        · rcases pick_pair hp2 with ⟨rfl, _⟩ | ⟨heq, _⟩
          · exact Or.inr rfl
          · exact absurd (congrArg Prod.fst heq) hne

/-- A tagged payload read off an object: the object is the pair, in one of its two orders. -/
theorem payload?_exact {j : Json} {tag field : String} (hne : "_tag" ≠ field) {p : Json}
    (h : payload? j tag field = some p) :
    j = .obj [("_tag", .str tag), (field, p)] ∨ j = .obj [(field, p), ("_tag", .str tag)] := by
  rw [payload?_eq] at h
  cases hf : fields? j ["_tag", field] with
  | none => rw [hf] at h; exact nomatch h
  | some l =>
    rw [hf] at h
    match l, hf, h with
    | [.str a, q], hf, h =>
      have h' : (if a = tag then some q else none) = some p := h
      split at h'
      · rename_i hat
        cases h'
        subst hat
        exact fields?_two hne hf
      · exact nomatch h'

/-- `N_J` at a tagged pair whose payload name sorts after `_tag`: both orders, one normal form. -/
theorem normJ_tagged_orders {tag field : String}
    (hlt : Ty.ltKey (keyBytes "_tag") (keyBytes field) = true)
    (hgt : Ty.ltKey (keyBytes field) (keyBytes "_tag") = false) (p : Json) :
    normJ (.obj [("_tag", .str tag), (field, p)]) = .obj [("_tag", .str tag), (field, normJ p)] ∧
      normJ (.obj [(field, p), ("_tag", .str tag)]) = .obj [("_tag", .str tag), (field, normJ p)] := by
  rw [normJ_obj, normJ_obj]
  simp only [List.map_cons, List.map_nil, sortE, List.foldl_cons, List.foldl_nil, insertE, hlt,
    hgt, ↓reduceIte]
  exact ⟨rfl, rfl⟩

/-- **The object step of exactness**: a payload read off `j`, re-encoded at its tag, is `j`
modulo `N_J`. -/
theorem normJ_tagged_of_payload {tag field : String} (hne : "_tag" ≠ field)
    (hlt : Ty.ltKey (keyBytes "_tag") (keyBytes field) = true)
    (hgt : Ty.ltKey (keyBytes field) (keyBytes "_tag") = false) {j p q : Json}
    (h : payload? j tag field = some p) (hq : normJ q = normJ p) :
    normJ (tagged tag field q) = normJ j := by
  have ho := normJ_tagged_orders (tag := tag) hlt hgt q
  have hp := normJ_tagged_orders (tag := tag) hlt hgt p
  rw [show tagged tag field q = .obj [("_tag", .str tag), (field, q)] from rfl, ho.1, hq]
  rcases payload?_exact hne h with rfl | rfl
  · rw [hp.1]
  · rw [hp.2]

/-- The tag names the codec uses, in the byte order: `_tag` sorts first. -/
theorem key_value : Ty.ltKey (keyBytes "_tag") (keyBytes "value") = true ∧
    Ty.ltKey (keyBytes "value") (keyBytes "_tag") = false := by decide +kernel
theorem key_failure : Ty.ltKey (keyBytes "_tag") (keyBytes "failure") = true ∧
    Ty.ltKey (keyBytes "failure") (keyBytes "_tag") = false := by decide +kernel
theorem key_success : Ty.ltKey (keyBytes "_tag") (keyBytes "success") = true ∧
    Ty.ltKey (keyBytes "success") (keyBytes "_tag") = false := by decide +kernel
theorem key_cause : Ty.ltKey (keyBytes "_tag") (keyBytes "cause") = true ∧
    Ty.ltKey (keyBytes "cause") (keyBytes "_tag") = false := by decide +kernel
theorem key_error : Ty.ltKey (keyBytes "_tag") (keyBytes "error") = true ∧
    Ty.ltKey (keyBytes "error") (keyBytes "_tag") = false := by decide +kernel
theorem key_defect : Ty.ltKey (keyBytes "_tag") (keyBytes "defect") = true ∧
    Ty.ltKey (keyBytes "defect") (keyBytes "_tag") = false := by decide +kernel
theorem key_fiberId : Ty.ltKey (keyBytes "_tag") (keyBytes "fiberId") = true ∧
    Ty.ltKey (keyBytes "fiberId") (keyBytes "_tag") = false := by decide +kernel

/-- A list read element by element is re-encoded element by element, modulo `N_J`. -/
theorem mapM_exact {α : Type} (dec : Json → Option α) (enc : α → Option Json)
    (hex : ∀ j a, dec j = some a → ∃ j', enc a = some j' ∧ normJ j' = normJ j) :
    ∀ (js : List Json) (as : List α), js.mapM dec = some as →
      ∃ js', as.mapM enc = some js' ∧ js'.map normJ = js.map normJ
  | [], as, h => by
    rw [List.mapM_nil] at h
    cases h
    exact ⟨[], rfl, rfl⟩
  | j :: js, as, h => by
    rw [List.mapM_cons] at h
    cases hj : dec j with
    | none => rw [hj] at h; exact nomatch h
    | some a =>
      cases hjs : js.mapM dec with
      | none => rw [hj, hjs] at h; exact nomatch h
      | some as' =>
        rw [hj, hjs] at h
        cases h
        obtain ⟨j', he, hn⟩ := hex j a hj
        obtain ⟨js', hes, hns⟩ := mapM_exact dec enc hex js as' hjs
        refine ⟨j' :: js', ?_, ?_⟩
        · rw [List.mapM_cons, he, hes]
          rfl
        · rw [List.map_cons, List.map_cons, hn, hns]

theorem decodeErr_exact {j : Json} {e : Err} (h : decodeErr j = some e) : encodeErr e = j := by
  unfold decodeErr at h
  split at h
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl
  · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
    exact (nat?_exact hn).symm

theorem decodeDefect_exact {j : Json} {d : Defect} (h : decodeDefect j = some d) :
    encodeDefect d = j := by
  unfold decodeDefect at h
  split at h
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl
  · cases h
    rfl
  · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [nat?_exact hn]
    rfl
  · obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [← decodeErr_exact he]
    rfl
  · exact nomatch h

theorem decodeReason_exact (dec : Json → Option Val) (enc : Val → Option Json)
    (hex : ∀ j v, dec j = some v → ∃ j', enc v = some j' ∧ normJ j' = normJ j)
    (j : Json) (r : Reason Err Defect FiberId Ann) (h : decodeReason dec j = some r) :
    ∃ j', encodeReason enc r = some j' ∧ normJ j' = normJ j := by
  unfold decodeReason at h
  split at h
  · rename_i p hp
    obtain ⟨v, hd, h'⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at h'
    split at h'
    · rename_i hve
      cases h'
      obtain ⟨p', he, hn⟩ := hex p v hd
      refine ⟨tagged "Fail" "error" p', ?_, normJ_tagged_of_payload (by decide)
        key_error.1 key_error.2 hp hn⟩
      show (valOfErr (errOf v)).bind
        (fun v => (enc v).bind (fun x => some (tagged "Fail" "error" x))) = _
      rw [hve, Option.bind_some, he, Option.bind_some]
    · exact nomatch h'
  · split at h
    · rename_i p hp
      obtain ⟨d, hd, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨tagged "Die" "defect" (encodeDefect d), rfl, ?_⟩
      rw [decodeDefect_exact hd]
      exact normJ_tagged_of_payload (by decide) key_defect.1 key_defect.2 hp rfl
    · split at h
      · rename_i p hp
        split at h
        · cases h
          exact ⟨tagged "Interrupt" "fiberId" .null, rfl,
            normJ_tagged_of_payload (by decide) key_fiberId.1 key_fiberId.2 hp rfl⟩
        · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
          refine ⟨tagged "Interrupt" "fiberId" (Arch.Json.ofNat n), rfl, ?_⟩
          rw [← nat?_exact hn]
          exact normJ_tagged_of_payload (by decide) key_fiberId.1 key_fiberId.2 hp rfl
      · exact nomatch h

theorem decodeCause_exact (dec : Json → Option Val) (enc : Val → Option Json)
    (hex : ∀ j v, dec j = some v → ∃ j', enc v = some j' ∧ normJ j' = normJ j)
    (j : Json) (c : CauseV) (h : decodeCause dec j = some c) :
    ∃ j', encodeCause enc c = some j' ∧ normJ j' = normJ j := by
  cases j with
  | arr rs =>
    have h' : (rs.mapM (decodeReason dec)).map (fun rs => (⟨rs⟩ : CauseV)) = some c := h
    cases hm : rs.mapM (decodeReason dec) with
    | none => rw [hm] at h'; exact nomatch h'
    | some l =>
      rw [hm] at h'
      cases h'
      obtain ⟨js', he, hn⟩ := mapM_exact (decodeReason dec) (encodeReason enc)
        (decodeReason_exact dec enc hex) rs l hm
      refine ⟨.arr js', ?_, ?_⟩
      · show (l.mapM (encodeReason enc)).map Json.arr = some (.arr js')
        rw [he]
        rfl
      · rw [normJ_arr, normJ_arr, hn]
  | _ => exact nomatch h

/-- **The raw decoder is exact against the raw encoder, modulo `N_J`** (every arm). The union arm
is where the canonical-branch repair is read: a value read off the second branch is not a member
of the first, so the encoder sends it to the second (the arm without the repair fails here: the red
control `codec_not_exact` in `Test/Codegen/SchemaGenerationContract.lean`). -/
theorem decodeRaw_exact : ∀ (t : Ty) (j : Json) (v : Val), decodeRaw t j = some v →
    ∃ j', encodeRaw t v = some j' ∧ normJ j' = normJ j := by
  intro t
  induction t with
  | unit =>
    intro j v h
    cases j with
    | null => cases h; exact ⟨.null, rfl, rfl⟩
    | _ => exact nomatch h
  | bool =>
    intro j v h
    cases j with
    | bool b => cases h; exact ⟨.bool b, rfl, rfl⟩
    | _ => exact nomatch h
  | string =>
    intro j v h
    cases j with
    | str s => cases h; exact ⟨.str s, rfl, rfl⟩
    | _ => exact nomatch h
  | lit _ =>
    intro j v h
    cases j with
    | str s => cases h; exact ⟨.str s, rfl, rfl⟩
    | _ => exact nomatch h
  | nat =>
    intro j v h
    have h' : (nat? j).map Val.nat = some v := h
    cases hn : nat? j with
    | none => rw [hn] at h'; exact nomatch h'
    | some n =>
      rw [hn] at h'
      cases h'
      exact ⟨Arch.Json.ofNat n, rfl, by rw [nat?_exact hn]⟩
  | option t ih =>
    intro j v h
    rw [decodeRaw] at h
    split at h
    · rename_i hnone
      cases h
      exact ⟨.obj [("_tag", .str "None")], rfl, by rw [fields?_one hnone]⟩
    · cases hp : payload? j "Some" "value" with
      | none => rw [hp] at h; exact nomatch h
      | some p =>
        rw [hp] at h
        have h' : (decodeRaw t p).map Store.Val.some = some v := h
        cases hd : decodeRaw t p with
        | none => rw [hd] at h'; exact nomatch h'
        | some x =>
          rw [hd] at h'
          cases h'
          obtain ⟨jx, he, hn⟩ := ih p x hd
          refine ⟨tagged "Some" "value" jx, ?_, normJ_tagged_of_payload (by decide)
            key_value.1 key_value.2 hp hn⟩
          show (encodeRaw t x).map (tagged "Some" "value") = _
          rw [he]
          rfl
  | list t ih =>
    intro j v h
    cases j with
    | arr js =>
      have h' : (js.mapM (decodeRaw t)).map Val.list = some v := h
      cases hm : js.mapM (decodeRaw t) with
      | none => rw [hm] at h'; exact nomatch h'
      | some vs =>
        rw [hm] at h'
        cases h'
        obtain ⟨js', he, hn⟩ := mapM_exact (decodeRaw t) (encodeRaw t) ih js vs hm
        refine ⟨.arr js', ?_, ?_⟩
        · show (vs.mapM (encodeRaw t)).map Json.arr = some (.arr js')
          rw [he]
          rfl
        · rw [normJ_arr, normJ_arr, hn]
    | _ => exact nomatch h
  | prod a b iha ihb =>
    intro j v h
    cases j with
    | arr js =>
      match js, h with
      | [jx, jy], h =>
        have h' : (do let x ← decodeRaw a jx; let y ← decodeRaw b jy; return Val.list [x, y]) =
          some v := h
        cases hx : decodeRaw a jx with
        | none => rw [hx] at h'; exact nomatch h'
        | some x =>
          cases hy : decodeRaw b jy with
          | none => rw [hx, hy] at h'; exact nomatch h'
          | some y =>
            rw [hx, hy] at h'
            cases h'
            obtain ⟨jx', hex, hnx⟩ := iha jx x hx
            obtain ⟨jy', hey, hny⟩ := ihb jy y hy
            refine ⟨.arr [jx', jy'], ?_, ?_⟩
            · show (do let jx ← encodeRaw a x; let jy ← encodeRaw b y; return Json.arr [jx, jy]) = _
              rw [hex, hey]
              rfl
            · rw [normJ_arr, normJ_arr, List.map_cons, List.map_cons, List.map_cons,
                List.map_cons, hnx, hny]
      | [], h => exact nomatch h
      | [_], h => exact nomatch h
      | _ :: _ :: _ :: _, h => exact nomatch h
    | _ => exact nomatch h
  | except e a ihe iha =>
    intro j v h
    rw [decodeRaw] at h
    split at h
    · rename_i p hp
      cases hd : decodeRaw e p with
      | none => rw [hd] at h; exact nomatch h
      | some x =>
        rw [hd] at h
        cases h
        obtain ⟨jx, he, hn⟩ := ihe p x hd
        refine ⟨tagged "Failure" "failure" jx, ?_, normJ_tagged_of_payload (by decide)
          key_failure.1 key_failure.2 hp hn⟩
        show (encodeRaw e x).map (tagged "Failure" "failure") = _
        rw [he]
        rfl
    · cases hp : payload? j "Success" "success" with
      | none => rw [hp] at h; exact nomatch h
      | some p =>
        rw [hp] at h
        have h' : (decodeRaw a p).map (fun v => Val.ctor 1 [v]) = some v := h
        cases hd : decodeRaw a p with
        | none => rw [hd] at h'; exact nomatch h'
        | some x =>
          rw [hd] at h'
          cases h'
          obtain ⟨jx, he, hn⟩ := iha p x hd
          refine ⟨tagged "Success" "success" jx, ?_, normJ_tagged_of_payload (by decide)
            key_success.1 key_success.2 hp hn⟩
          show (encodeRaw a x).map (tagged "Success" "success") = _
          rw [he]
          rfl
  | exitOf a e iha ihe =>
    intro j v h
    rw [decodeRaw] at h
    split at h
    · rename_i p hp
      cases hd : decodeRaw a p with
      | none => rw [hd] at h; exact nomatch h
      | some x =>
        rw [hd] at h
        cases h
        obtain ⟨jx, he, hn⟩ := iha p x hd
        refine ⟨tagged "Success" "value" jx, ?_, normJ_tagged_of_payload (by decide)
          key_value.1 key_value.2 hp hn⟩
        show (encodeRaw a x).map (tagged "Success" "value") = _
        rw [he]
        rfl
    · cases hp : payload? j "Failure" "cause" with
      | none => rw [hp] at h; exact nomatch h
      | some p =>
        rw [hp] at h
        have h' : (decodeCause (decodeRaw e) p).map Val.exitErr = some v := h
        cases hd : decodeCause (decodeRaw e) p with
        | none => rw [hd] at h'; exact nomatch h'
        | some c =>
          rw [hd] at h'
          cases h'
          obtain ⟨jc, he, hn⟩ := decodeCause_exact (decodeRaw e) (encodeRaw e) ihe p c hd
          refine ⟨tagged "Failure" "cause" jc, ?_, normJ_tagged_of_payload (by decide)
            key_cause.1 key_cause.2 hp hn⟩
          show (causeImage.ofVal (causeImage.toVal c)).bind
            (fun c => (encodeCause (encodeRaw e) c).map (tagged "Failure" "cause")) = _
          rw [Store.Image.ofVal_toVal, Option.bind_some, he]
          rfl
  | causeOf e ih =>
    intro j v h
    have h' : (decodeCause (decodeRaw e) j).map Val.exitErr = some v := h
    cases hd : decodeCause (decodeRaw e) j with
    | none => rw [hd] at h'; exact nomatch h'
    | some c =>
      rw [hd] at h'
      cases h'
      obtain ⟨jc, he, hn⟩ := decodeCause_exact (decodeRaw e) (encodeRaw e) ih j c hd
      refine ⟨jc, ?_, hn⟩
      show (causeImage.ofVal (causeImage.toVal c)).bind (fun c => encodeCause (encodeRaw e) c) = _
      rw [Store.Image.ofVal_toVal, Option.bind_some]
      exact he
  | union a b iha ihb =>
    intro j v h
    rw [decodeRaw] at h
    split at h
    · rename_i w hw
      have hwv : w = v := Option.some.inj h
      subst hwv
      obtain ⟨hdw, hmem⟩ := Option.filter_eq_some_iff.mp hw
      obtain ⟨j', he, hn⟩ := iha j w hdw
      refine ⟨j', ?_, hn⟩
      show (if Val.hasTy w a then encodeRaw a w else if Val.hasTy w b then encodeRaw b w else none) = _
      rw [if_pos hmem]
      exact he
    · obtain ⟨hdv, hmem⟩ := Option.filter_eq_some_iff.mp h
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hmem
      obtain ⟨j', he, hn⟩ := ihb j v hdv
      refine ⟨j', ?_, hn⟩
      show (if Val.hasTy v a then encodeRaw a v else if Val.hasTy v b then encodeRaw b v else none) = _
      rw [if_neg (by rw [hmem.2]; exact Bool.false_ne_true), if_pos hmem.1]
      exact he
  | _ => intro j v h; exact nomatch h

end Effect4.Schema.Codec

namespace Effect4.Schema
open Effect4.Program Effect4.Machine

/-- The exact three checks behind a successful encoding. -/
theorem encode_eq_some {t : CTy} {v : Val} {j : Json} :
    encode t.toRaw v = some j ↔
      Val.hasTy v t.toRaw = true ∧ Codec.encodeRaw (Codec.layout t.toRaw) v = some j ∧
        Codec.decodeRaw (Codec.layout t.toRaw) j = some v := by
  have hn : t.toRaw.normalize = t.toRaw := t.property
  by_cases ht : Val.hasTy v t.toRaw = true
  · cases he : Codec.encodeRaw (Codec.layout t.toRaw) v with
    | none => simp [encode, hn, ht, he]
    | some k =>
      by_cases hd : Codec.decodeRaw (Codec.layout t.toRaw) k = some v
      · simp [encode, hn, ht, he, hd]
        intro h
        subst j
        exact hd
      · simp [encode, hn, ht, he, hd]
        intro h
        subst j
        exact hd
  · simp [encode, hn, ht]

/-- Executable admission is exactly the successful domain of the checked encoder. -/
theorem encode_isSome_iff {t : CTy} {v : Val} :
    (encode t.toRaw v).isSome = true ↔ Ty.isCodecValue t.toRaw v = true := by
  have hn : t.toRaw.normalize = t.toRaw := t.property
  by_cases ht : Val.hasTy v t.toRaw = true
  · cases he : Codec.encodeRaw (Codec.layout t.toRaw) v with
    | none => simp [encode, Codec.isValue, Ty.isCodecValue, hn, ht, he]
    | some j =>
      by_cases hd : Codec.decodeRaw (Codec.layout t.toRaw) j = some v <;>
        simp [encode, Codec.isValue, Ty.isCodecValue, hn, ht, he, hd]
  · cases he : Codec.encodeRaw (Codec.layout t.toRaw) v <;>
      simp [encode, Codec.isValue, Ty.isCodecValue, hn, ht, he]

/-- S-3 totality on the checked JSON value domain. Type support alone is insufficient. -/
theorem encode_of_hasTy {t : CTy} {v : Val} (_h : Val.hasTy v t.toRaw = true)
    (admitted : Ty.isCodecValue t.toRaw v = true) : (encode t.toRaw v).isSome = true :=
  (encode_isSome_iff (t := t)).mpr admitted

/-- Every successful encoding recovers exactly, including its original constructor tags: the
retraction half of exactness (`decode_iff`). At every type: `encode` and `decode` normalize it
alike, so no canonicity is needed (until row 128's commit this was stated at `CTy`). -/
theorem decode_of_encode {t : Ty} {v : Val} {j : Json}
    (h : encode t v = some j) : decode t j = some v := by
  unfold encode at h
  dsimp only at h
  split at h
  · rename_i hv
    split at h
    · exact nomatch h
    · split at h
      · rename_i hd
        cases h
        exact Option.filter_eq_some_iff.mpr ⟨hd, hv⟩
      · exact nomatch h
  · exact nomatch h

/-- **Exactness of the JSON pair, modulo `N_J`** (decisions row 128): a JSON the checked decoder
reads is, up to the order of object entries, the checked encoder's image of the value it returns. -/
theorem encode_of_decode {t : Ty} {j : Json} {v : Val} (h : decode t j = some v) :
    ∃ j', encode t v = some j' ∧ Codec.normJ j' = Codec.normJ j := by
  obtain ⟨hd, hv⟩ := Option.filter_eq_some_iff.mp h
  obtain ⟨j', he, hn⟩ := Codec.decodeRaw_exact _ j v hd
  refine ⟨j', ?_, hn⟩
  have hround : Codec.decodeRaw (Codec.layout t.normalize) j' = some v := by
    rw [← Codec.decodeRaw_normJ, hn, Codec.decodeRaw_normJ]
    exact hd
  show (if Val.hasTy v t.normalize then
      (match Codec.encodeRaw (Codec.layout t.normalize) v with
        | none => none
        | some j => if Codec.decodeRaw (Codec.layout t.normalize) j = some v then some j else none)
    else none) = some j'
  rw [if_pos hv, he]
  show (if Codec.decodeRaw (Codec.layout t.normalize) j' = some v then some j' else none) = some j'
  rw [if_pos hround]

/-- **The JSON pair is an exact embedding modulo `N_J`** (decisions row 128; `AGENTS.md`'s exact
embedding with the normaliser `Codec.normJ`): a JSON decodes to a value exactly when it is that
value's encoding up to the order of object entries. -/
theorem decode_iff {t : Ty} {j : Json} {v : Val} :
    decode t j = some v ↔ ∃ j', encode t v = some j' ∧ Codec.normJ j' = Codec.normJ j := by
  constructor
  · exact encode_of_decode
  · rintro ⟨j', he, hn⟩
    have h : (Codec.decodeRaw (Codec.layout t.normalize) j').filter
        (fun v => Val.hasTy v t.normalize) = some v := decode_of_encode he
    show (Codec.decodeRaw (Codec.layout t.normalize) j).filter
      (fun v => Val.hasTy v t.normalize) = some v
    rw [← Codec.decodeRaw_normJ, ← hn, Codec.decodeRaw_normJ]
    exact h

/-- S-3 round trip without an arbitrary default JSON inhabitant or a failing `get!`. -/
theorem decode_encode {t : CTy} {v : Val} (h : Val.hasTy v t.toRaw = true)
    (admitted : Ty.isCodecValue t.toRaw v = true) :
    (encode t.toRaw v).bind (decode t.toRaw) = some v := by
  have total := encode_of_hasTy (t := t) h admitted
  cases he : encode t.toRaw v with
  | none => rw [he] at total; exact nomatch total
  | some j => rw [Option.bind_some]; exact decode_of_encode he

/-- S-3 successful decoding implies canonical type membership, without a support premise. -/
theorem hasTy_decode {t : CTy} {j : Json} {v : Val}
    (h : decode t.toRaw j = some v) : Val.hasTy v t.toRaw = true := by
  have hn : t.toRaw.normalize = t.toRaw := t.property
  cases hd : Codec.decodeRaw (Codec.layout t.toRaw) j with
  | none => simp [decode, hn, hd] at h
  | some w =>
    simp [decode, hn, hd] at h
    exact h.2

/-- S-3 subtype agreement for a shared JSON layout. This includes literal refinements
through products, options, arrays, Results, Exits and Causes. Union selectors are retained. -/
theorem encode_sub {s t : CTy} {v : Val}
    (hsub : Ty.sub s.toRaw t.toRaw = true) (hv : Val.hasTy v s.toRaw = true)
    (compatible : Codec.Compatible s.toRaw t.toRaw) :
    encode t.toRaw v = encode s.toRaw v := by
  have hs : s.toRaw.normalize = s.toRaw := s.property
  have hn : t.toRaw.normalize = t.toRaw := t.property
  have ht := hasTy_sub s.toRaw t.toRaw v [] hsub hv
  simp only [encode, hs, hn, hv, ht, ↓reduceIte]
  rw [show Codec.layout s.toRaw = Codec.layout t.toRaw from compatible]

/-- Admitted encodings cannot identify distinct values at one type. -/
theorem encode_injective {t : CTy} {v w : Val} {j : Json}
    (hv : encode t.toRaw v = some j) (hw : encode t.toRaw w = some j) : v = w := by
  exact Option.some.inj ((decode_of_encode hv).symm.trans (decode_of_encode hw))

/-- All strings cross the JSON boundary, not merely the finite examples in the battery. -/
theorem encode_string (s : String) : encode .string (.str s) = some (.str s) := by
  simp [encode, Ty.normalize, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

theorem encode_bool (b : Bool) : encode .bool (.bool b) = some (.bool b) := by
  simp [encode, Ty.normalize, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

theorem encode_unit : encode .unit .unit = some .null := by
  simp [encode, Ty.normalize, Val.hasTy, Codec.layout, Codec.encodeRaw, Codec.decodeRaw]

end Effect4.Schema
