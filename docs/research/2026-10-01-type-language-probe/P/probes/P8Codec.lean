import P1FieldOrder
import Effect4.Laws.Schema.Codec

/-!
# Seat P, question 5: the JSON codec's exactness (row 128, the data wave's commit 2)

Research probe, against **today's** `Ty`, `Val` and codec (`src/Effect4/Schema/Codec.lean`,
`src/Effect4/Laws/Schema/Codec.lean` at `bff50631`); no copy of the type language.

**The finding (tested, then proved).** Today's pair is a retraction (`decode_of_encode`) and not
an exact embedding: at `union (except nat nat) (exitOf nat nat)` the decoder accepts a JSON the
encoder never writes for the value it returns (`codec_not_exact`, synthesis NS2). The repair is
one arm: `decodeRaw`'s union reads its second branch only for a value the encoder would send
there, i.e. one that is not a member of the first (`decodeRawC`). With it, and the key-order
normaliser `normJ` (N_J: every object's entries sorted by their key's UTF-8 bytes, stable,
recursively), the checked pair is exact:

    decodeC t j = some v → ∃ j', encodeC t v = some j' ∧ normJ j' = normJ j

(`encodeC_of_decodeC`), beside the retraction (`decodeC_of_encodeC`, production's proof).
The decoder reads objects without regard to entry order (`fields?`), which is what N_J quotients:
`decodeRawC t (normJ j) = decodeRawC t j` (`decodeRawC_normJ`).
-/

set_option autoImplicit false

namespace ProbeP.Codec

open Effect4 Effect4.Program Effect4.Machine
open Effect4.Schema.Codec
open ProbeP.Field

/-! ## N_J: the key-order normaliser, as a function -/

/-- Insert an entry by its key's UTF-8 bytes; an equal key keeps its place (stable). -/
def insertE (e : String × Json) : List (String × Json) → List (String × Json)
  | [] => [e]
  | f :: fs =>
    if Ty.ltKey (bytesKey e.1) (bytesKey f.1) = true then e :: f :: fs else f :: insertE e fs

/-- Entries sorted by key (insertion sort, stable). -/
def sortE (es : List (String × Json)) : List (String × Json) :=
  es.foldl (fun acc e => insertE e acc) []

mutual
/-- **N_J**: every object's entries sorted by key, recursively; arrays element-wise. -/
def normJ : Json → Json
  | .arr js => .arr (normJs js)
  | .obj es => .obj (sortE (normEs es))
  | j => j
def normJs : List Json → List Json
  | [] => []
  | j :: js => normJ j :: normJs js
def normEs : List (String × Json) → List (String × Json)
  | [] => []
  | (k, j) :: es => (k, normJ j) :: normEs es
end

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

/-! ### The sort is a permutation -/

theorem insertE_perm (e : String × Json) : ∀ l : List (String × Json), (insertE e l).Perm (e :: l)
  | [] => List.Perm.refl _
  | f :: fs => by
    unfold insertE
    split
    · exact List.Perm.refl _
    · exact ((insertE_perm e fs).cons f).trans (List.Perm.swap e f fs)

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

/-! ### The object reader is order-blind: `fields?` and `payload?` commute with N_J -/

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
    fields? (.obj es) names = if (es.length != names.length) = true then none else names.mapM (pick es) := by
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

/-- N_J keeps a node's kind: a string stays the string. -/
theorem normJ_eq_str {x : Json} {s : String} : normJ x = .str s ↔ x = .str s := by
  cases x with
  | str t => exact Iff.rfl
  | arr js => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | obj es => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | null => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | bool b => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | number f => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

theorem normJ_eq_null {x : Json} : normJ x = .null ↔ x = .null := by
  cases x with
  | null => exact Iff.rfl
  | arr js => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | obj es => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | str t => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | bool b => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩
  | number f => exact ⟨fun h => (nomatch h), fun h => (nomatch h)⟩

/-- The tagged-pair pattern `payload?` reads commutes with N_J. -/
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


/-! ## The repaired decoder: the union reads the encoder's canonical branch -/

/-- `decodeRaw` (copied), with one arm changed: a union reads its second branch only for a value
that is not a member of the first, i.e. one the encoder sends there (`encodeRaw`'s union arm). -/
def decodeRawC : Ty → Json → Option Val
  | .unit, .null => some .unit
  | .bool, .bool b => some (.bool b)
  | .nat, j => (nat? j).map Val.nat
  | .string, .str s | .lit _, .str s => some (.str s)
  | .option t, j =>
    if fields? j ["_tag"] = some [.str "None"] then some .none
    else do
      let payload ← payload? j "Some" "value"
      (decodeRawC t payload).map Store.Val.some
  | .list t, .arr js => (js.mapM (decodeRawC t)).map Val.list
  | .prod a b, .arr [jx, jy] => do
    let x ← decodeRawC a jx
    let y ← decodeRawC b jy
    return .list [x, y]
  | .except e a, j =>
    if let some p := payload? j "Failure" "failure" then
      (decodeRawC e p).map (fun v => .ctor 0 [v])
    else do
      let p ← payload? j "Success" "success"
      (decodeRawC a p).map (fun v => .ctor 1 [v])
  | .exitOf a e, j =>
    if let some p := payload? j "Success" "value" then
      (decodeRawC a p).map (fun v => .ctor 0 [v])
    else do
      let p ← payload? j "Failure" "cause"
      (decodeCause (decodeRawC e) p).map Val.exitErr
  | .causeOf e, j => (decodeCause (decodeRawC e) j).map Val.exitErr
  -- changed: the second branch only for a value the encoder sends there
  | .union a b, j =>
    match (decodeRawC a j).filter (fun v => Val.hasTy v a) with
    | some v => some v
    | none => (decodeRawC b j).filter (fun v => Val.hasTy v b && !Val.hasTy v a)
  | _, _ => none

/-- The checked encoder, reading back through the repaired decoder (production's `encode`, the
check's decoder replaced). -/
def encodeC (t : Ty) (v : Val) : Option Json :=
  let t := t.normalize
  if Val.hasTy v t then
    match encodeRaw (layout t) v with
    | none => none
    | some j => if decodeRawC (layout t) j = some v then some j else none
  else none

/-- The checked decoder (production's `decode`, the repaired raw decoder). -/
def decodeC (t : Ty) (j : Json) : Option Val :=
  let t := t.normalize
  (decodeRawC (layout t) j).filter (fun v => Val.hasTy v t)

/-! ## The decoder is order-blind: it reads N_J's quotient -/

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

/-- **The repaired decoder reads N_J's quotient** (proved, every arm). -/
theorem decodeRawC_normJ : ∀ (t : Ty) (j : Json), decodeRawC t (normJ j) = decodeRawC t j := by
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
    rw [decodeRawC, decodeRawC]
    by_cases hn : fields? j ["_tag"] = some [.str "None"]
    · rw [if_pos ((fields?_tag_normJ j "None").mpr hn), if_pos hn]
    · rw [if_neg (fun h => hn ((fields?_tag_normJ j "None").mp h)), if_neg hn, payload?_normJ]
      cases payload? j "Some" "value" with
      | none => rfl
      | some p =>
        show (decodeRawC t (normJ p)).map Store.Val.some = (decodeRawC t p).map Store.Val.some
        rw [ih]
  | list t ih =>
    intro j
    cases j with
    | arr js =>
      rw [normJ_arr]
      show ((js.map normJ).mapM (decodeRawC t)).map Val.list = (js.mapM (decodeRawC t)).map Val.list
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
        show (do let x ← decodeRawC a (normJ jx); let y ← decodeRawC b (normJ jy); return Val.list [x, y]) =
          (do let x ← decodeRawC a jx; let y ← decodeRawC b jy; return Val.list [x, y])
        rw [iha, ihb]
      | _ :: _ :: _ :: _ => rfl
    | obj es => rw [normJ_obj]; rfl
    | _ => rfl
  | except e a ihe iha =>
    intro j
    rw [decodeRawC, decodeRawC, payload?_normJ, payload?_normJ]
    cases payload? j "Failure" "failure" with
    | some p =>
      show (decodeRawC e (normJ p)).map _ = (decodeRawC e p).map _
      rw [ihe]
    | none =>
      cases payload? j "Success" "success" with
      | some p =>
        show (decodeRawC a (normJ p)).map _ = (decodeRawC a p).map _
        rw [iha]
      | none => rfl
  | exitOf a e iha ihe =>
    intro j
    rw [decodeRawC, decodeRawC, payload?_normJ, payload?_normJ]
    cases payload? j "Success" "value" with
    | some p =>
      show (decodeRawC a (normJ p)).map _ = (decodeRawC a p).map _
      rw [iha]
    | none =>
      cases payload? j "Failure" "cause" with
      | some p =>
        show (decodeCause (decodeRawC e) (normJ p)).map Val.exitErr =
          (decodeCause (decodeRawC e) p).map Val.exitErr
        rw [decodeCause_normJ (decodeRawC e) ihe]
      | none => rfl
  | causeOf e ih =>
    intro j
    show (decodeCause (decodeRawC e) (normJ j)).map Val.exitErr =
      (decodeCause (decodeRawC e) j).map Val.exitErr
    rw [decodeCause_normJ (decodeRawC e) ih]
  | union a b iha ihb =>
    intro j
    rw [decodeRawC, decodeRawC, iha, ihb]
  | _ => intro j; rfl


/-! ## Exactness: every decoded JSON is the encoder's image modulo N_J -/

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

theorem pick_single {k' k : String} {x' x : Json} (h : pick [(k', x')] k = some x) : k' = k ∧ x' = x := by
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

/-- N_J at a tagged pair whose payload name sorts after `_tag`: both orders, one normal form. -/
theorem normJ_tagged_orders {tag field : String}
    (hlt : Ty.ltKey (bytesKey "_tag") (bytesKey field) = true)
    (hgt : Ty.ltKey (bytesKey field) (bytesKey "_tag") = false) (p : Json) :
    normJ (.obj [("_tag", .str tag), (field, p)]) = .obj [("_tag", .str tag), (field, normJ p)] ∧
      normJ (.obj [(field, p), ("_tag", .str tag)]) = .obj [("_tag", .str tag), (field, normJ p)] := by
  rw [normJ_obj, normJ_obj]
  simp only [List.map_cons, List.map_nil, sortE, List.foldl_cons, List.foldl_nil, insertE, hlt,
    hgt, ↓reduceIte]
  exact ⟨rfl, rfl⟩

/-- **The object step of exactness**: a payload read off `j`, re-encoded at its tag, is `j`
modulo N_J. -/
theorem normJ_tagged_of_payload {tag field : String} (hne : "_tag" ≠ field)
    (hlt : Ty.ltKey (bytesKey "_tag") (bytesKey field) = true)
    (hgt : Ty.ltKey (bytesKey field) (bytesKey "_tag") = false) {j p q : Json}
    (h : payload? j tag field = some p) (hq : normJ q = normJ p) :
    normJ (tagged tag field q) = normJ j := by
  have ho := normJ_tagged_orders (tag := tag) hlt hgt q
  have hp := normJ_tagged_orders (tag := tag) hlt hgt p
  rw [show tagged tag field q = .obj [("_tag", .str tag), (field, q)] from rfl, ho.1, hq]
  rcases payload?_exact hne h with rfl | rfl
  · rw [hp.1]
  · rw [hp.2]

/-- The tag names the codec uses, in the byte order. -/
theorem key_value : Ty.ltKey (bytesKey "_tag") (bytesKey "value") = true ∧
    Ty.ltKey (bytesKey "value") (bytesKey "_tag") = false := by decide +kernel
theorem key_failure : Ty.ltKey (bytesKey "_tag") (bytesKey "failure") = true ∧
    Ty.ltKey (bytesKey "failure") (bytesKey "_tag") = false := by decide +kernel
theorem key_success : Ty.ltKey (bytesKey "_tag") (bytesKey "success") = true ∧
    Ty.ltKey (bytesKey "success") (bytesKey "_tag") = false := by decide +kernel
theorem key_cause : Ty.ltKey (bytesKey "_tag") (bytesKey "cause") = true ∧
    Ty.ltKey (bytesKey "cause") (bytesKey "_tag") = false := by decide +kernel
theorem key_error : Ty.ltKey (bytesKey "_tag") (bytesKey "error") = true ∧
    Ty.ltKey (bytesKey "error") (bytesKey "_tag") = false := by decide +kernel
theorem key_defect : Ty.ltKey (bytesKey "_tag") (bytesKey "defect") = true ∧
    Ty.ltKey (bytesKey "defect") (bytesKey "_tag") = false := by decide +kernel
theorem key_fiberId : Ty.ltKey (bytesKey "_tag") (bytesKey "fiberId") = true ∧
    Ty.ltKey (bytesKey "fiberId") (bytesKey "_tag") = false := by decide +kernel

/-- A list read element by element is re-encoded element by element, modulo N_J. -/
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

theorem decodeDefect_exact {j : Json} {d : Defect} (h : decodeDefect j = some d) : encodeDefect d = j := by
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
      show (valOfErr (errOf v)).bind (fun v => (enc v).bind (fun x => some (tagged "Fail" "error" x))) = _
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

/-- **The raw decoder is exact against the raw encoder, modulo N_J** (proved, every arm). The
union arm is where the repair is read: a value read off the second branch is not a member of the
first, so the encoder sends it to the second (production's arm fails here: `codec_not_exact`). -/
theorem decodeRawC_exact : ∀ (t : Ty) (j : Json) (v : Val), decodeRawC t j = some v →
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
    rw [decodeRawC] at h
    split at h
    · rename_i hnone
      cases h
      exact ⟨.obj [("_tag", .str "None")], rfl, by rw [fields?_one hnone]⟩
    · cases hp : payload? j "Some" "value" with
      | none => rw [hp] at h; exact nomatch h
      | some p =>
        rw [hp] at h
        have h' : (decodeRawC t p).map Store.Val.some = some v := h
        cases hd : decodeRawC t p with
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
      have h' : (js.mapM (decodeRawC t)).map Val.list = some v := h
      cases hm : js.mapM (decodeRawC t) with
      | none => rw [hm] at h'; exact nomatch h'
      | some vs =>
        rw [hm] at h'
        cases h'
        obtain ⟨js', he, hn⟩ := mapM_exact (decodeRawC t) (encodeRaw t) ih js vs hm
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
        have h' : (do let x ← decodeRawC a jx; let y ← decodeRawC b jy; return Val.list [x, y]) =
          some v := h
        cases hx : decodeRawC a jx with
        | none => rw [hx] at h'; exact nomatch h'
        | some x =>
          cases hy : decodeRawC b jy with
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
            · rw [normJ_arr, normJ_arr, List.map_cons, List.map_cons, List.map_cons, List.map_cons,
                hnx, hny]
      | [], h => exact nomatch h
      | [_], h => exact nomatch h
      | _ :: _ :: _ :: _, h => exact nomatch h
    | _ => exact nomatch h
  | except e a ihe iha =>
    intro j v h
    rw [decodeRawC] at h
    split at h
    · rename_i p hp
      cases hd : decodeRawC e p with
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
        have h' : (decodeRawC a p).map (fun v => Val.ctor 1 [v]) = some v := h
        cases hd : decodeRawC a p with
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
    rw [decodeRawC] at h
    split at h
    · rename_i p hp
      cases hd : decodeRawC a p with
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
        have h' : (decodeCause (decodeRawC e) p).map Val.exitErr = some v := h
        cases hd : decodeCause (decodeRawC e) p with
        | none => rw [hd] at h'; exact nomatch h'
        | some c =>
          rw [hd] at h'
          cases h'
          obtain ⟨jc, he, hn⟩ := decodeCause_exact (decodeRawC e) (encodeRaw e) ihe p c hd
          refine ⟨tagged "Failure" "cause" jc, ?_, normJ_tagged_of_payload (by decide)
            key_cause.1 key_cause.2 hp hn⟩
          show (causeImage.ofVal (causeImage.toVal c)).bind
            (fun c => (encodeCause (encodeRaw e) c).map (tagged "Failure" "cause")) = _
          rw [Store.Image.ofVal_toVal, Option.bind_some, he]
          rfl
  | causeOf e ih =>
    intro j v h
    have h' : (decodeCause (decodeRawC e) j).map Val.exitErr = some v := h
    cases hd : decodeCause (decodeRawC e) j with
    | none => rw [hd] at h'; exact nomatch h'
    | some c =>
      rw [hd] at h'
      cases h'
      obtain ⟨jc, he, hn⟩ := decodeCause_exact (decodeRawC e) (encodeRaw e) ih j c hd
      refine ⟨jc, ?_, hn⟩
      show (causeImage.ofVal (causeImage.toVal c)).bind (fun c => encodeCause (encodeRaw e) c) = _
      rw [Store.Image.ofVal_toVal, Option.bind_some]
      exact he
  | union a b iha ihb =>
    intro j v h
    rw [decodeRawC] at h
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

/-- **Exactness of the checked pair, modulo N_J** (row 128's second theorem, proved). -/
theorem encodeC_of_decodeC {t : Ty} {j : Json} {v : Val} (h : decodeC t j = some v) :
    ∃ j', encodeC t v = some j' ∧ normJ j' = normJ j := by
  obtain ⟨hd, hv⟩ := Option.filter_eq_some_iff.mp h
  obtain ⟨j', he, hn⟩ := decodeRawC_exact _ j v hd
  refine ⟨j', ?_, hn⟩
  have hround : decodeRawC (layout t.normalize) j' = some v := by
    rw [← decodeRawC_normJ, hn, decodeRawC_normJ]
    exact hd
  show (if Val.hasTy v t.normalize then
      (match encodeRaw (layout t.normalize) v with
        | none => none
        | some j => if decodeRawC (layout t.normalize) j = some v then some j else none)
    else none) = some j'
  rw [if_pos hv, he]
  show (if decodeRawC (layout t.normalize) j' = some v then some j' else none) = some j'
  rw [if_pos hround]

/-- **The retraction** (production's `decode_of_encode`, at the repaired pair). -/
theorem decodeC_of_encodeC {t : Ty} {v : Val} {j : Json} (h : encodeC t v = some j) :
    decodeC t j = some v := by
  unfold encodeC at h
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

/-- **The pair is an exact embedding modulo N_J**: a JSON decodes to a value exactly when it is
that value's encoding up to key order. -/
theorem decodeC_iff {t : Ty} {j : Json} {v : Val} :
    decodeC t j = some v ↔ ∃ j', encodeC t v = some j' ∧ normJ j' = normJ j := by
  constructor
  · exact encodeC_of_decodeC
  · rintro ⟨j', he, hn⟩
    have h : (decodeRawC (layout t.normalize) j').filter (fun v => Val.hasTy v t.normalize) =
        some v := decodeC_of_encodeC he
    show (decodeRawC (layout t.normalize) j).filter (fun v => Val.hasTy v t.normalize) = some v
    rw [← decodeRawC_normJ, ← hn, decodeRawC_normJ]
    exact h

/-! ## The red control: today's decoder at the union NS2 names -/

def unionTy : Ty := .union (.except .nat .nat) (.exitOf .nat .nat)
def jExitOk : Json := .obj [("_tag", .str "Success"), ("value", Arch.Json.ofNat 1)]
def jFailure : Json := .obj [("_tag", .str "Failure"), ("failure", Arch.Json.ofNat 1)]

/-- **RED CONTROL (proved): today's codec is not exact.** `Exit.Success(1)`'s JSON decodes, at
`union (except nat nat) (exitOf nat nat)`, to `ctor 0 [nat 1]`, which the encoder writes as
`Result.Failure(1)`: two JSON images of one value, not equal modulo N_J. -/
theorem codec_not_exact :
    Effect4.Schema.decode unionTy jExitOk = some (.ctor 0 [.nat 1]) ∧
      Effect4.Schema.decode unionTy jFailure = some (.ctor 0 [.nat 1]) ∧
      Effect4.Schema.encode unionTy (.ctor 0 [.nat 1]) = some jFailure ∧
      normJ jFailure ≠ normJ jExitOk := by
  decide +kernel

/-- The repaired decoder refuses the non-canonical image and keeps the canonical one. -/
theorem repaired_refuses :
    decodeC unionTy jExitOk = none ∧ decodeC unionTy jFailure = some (.ctor 0 [.nat 1]) ∧
      encodeC unionTy (.ctor 0 [.nat 1]) = some jFailure := by
  decide +kernel

end ProbeP.Codec

#print axioms ProbeP.Codec.sortE_perm
#print axioms ProbeP.Codec.fields?_normJ
#print axioms ProbeP.Codec.payload?_normJ
#print axioms ProbeP.Codec.decodeErr_normJ
#print axioms ProbeP.Codec.decodeDefect_normJ
#print axioms ProbeP.Codec.decodeReason_normJ
#print axioms ProbeP.Codec.decodeCause_normJ
#print axioms ProbeP.Codec.decodeRawC_normJ
#print axioms ProbeP.Codec.nat?_exact
#print axioms ProbeP.Codec.fields?_two
#print axioms ProbeP.Codec.payload?_exact
#print axioms ProbeP.Codec.normJ_tagged_of_payload
#print axioms ProbeP.Codec.decodeErr_exact
#print axioms ProbeP.Codec.decodeDefect_exact
#print axioms ProbeP.Codec.decodeReason_exact
#print axioms ProbeP.Codec.decodeCause_exact
#print axioms ProbeP.Codec.decodeRawC_exact
#print axioms ProbeP.Codec.encodeC_of_decodeC
#print axioms ProbeP.Codec.decodeC_of_encodeC
#print axioms ProbeP.Codec.decodeC_iff
#print axioms ProbeP.Codec.codec_not_exact
#print axioms ProbeP.Codec.repaired_refuses
