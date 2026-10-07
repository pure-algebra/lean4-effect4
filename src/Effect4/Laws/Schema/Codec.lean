import Effect4.Schema.Codec
import Effect4.Laws.Program.Admits
import Effect4.Laws.Machine.Map
import Effect4.Laws.Program.Typed.RecordValues

/-!
# Checked JSON boundary laws

Concept: Exact Codecs & Data Plane Embeddings.
Claims: `decode-encode`, `decode-iff` and `record-codec-layout`; requirements R2 and R3.
The data-language JSON codec brief places the helpers and their consumers before implementation.

`decode_iff` states exactness modulo `Codec.normJ` for every type.
Both public operations normalize that type before interpreting its wire layout.
Exact value recovery requires executable codec admission.
Subtype agreement also requires `Codec.Compatible`; the test claims no completeness for compatibility.

The raw laws retain every original type, including noncanonical union children.
`decodeRaw_normJ` proves that object-key order does not change decoding.
`decodeRaw_exact` reconstructs the normalized encoder image after every successful raw decode.
Record and map cases refuse duplicate keys before sorting.
Tuple cases retain exact positional arity.

These laws establish no target execution, arbitrary host exception encoding or host progress.
The union decoder retains decision row 128's canonical branch rule.
The original failure control remains in `Test/Codegen/SchemaGenerationContract.lean`.
-/

set_option autoImplicit false

namespace Effect4.Schema.Codec
open Effect4 Effect4.Program Effect4.Machine

/-- The codec fold retains each raw type exactly.
This supplies original union membership tests to both raw codec laws. -/
theorem wire_type (t : Ty) : (wire t).type = t := by
  induction t with
  | option t ih => exact congrArg Ty.option ih
  | list t ih => exact congrArg Ty.list ih
  | prod a b iha ihb =>
    change Ty.prod (wire a).type (wire b).type = .prod a b
    rw [iha, ihb]
  | except a b iha ihb =>
    change Ty.except (wire a).type (wire b).type = .except a b
    rw [iha, ihb]
  | exitOf a b iha ihb =>
    change Ty.exitOf (wire a).type (wire b).type = .exitOf a b
    rw [iha, ihb]
  | causeOf a ih => exact congrArg Ty.causeOf ih
  | fiberOf a b iha ihb =>
    change Ty.fiberOf (wire a).type (wire b).type = .fiberOf a b
    rw [iha, ihb]
  | union a b iha ihb =>
    change Ty.union (wire a).type (wire b).type = .union a b
    rw [iha, ihb]
  | refOf a ih => exact congrArg Ty.refOf ih
  | deferredOf a b iha ihb =>
    change Ty.deferredOf (wire a).type (wire b).type = .deferredOf a b
    rw [iha, ihb]
  | map a b iha ihb =>
    change Ty.map (wire a).type (wire b).type = .map a b
    rw [iha, ihb]
  | record fields ih =>
    unfold wire
    rw [cata_ty_record]
    change Ty.record ((fields.map (prodMapSnd (prodMapSnd (cata_ty wireAlgebra)))).map
      (fun f => (f.1, f.2.1, f.2.2.type))) = .record fields
    congr 1
    rw [List.map_map]
    calc
      _ = fields.map id := List.map_congr_left (by
        intro f hf
        change (f.1, f.2.1, (wire f.2.2).type) = f
        rw [ih f hf])
      _ = fields := List.map_id fields
  | tuple items ih =>
    unfold wire
    rw [cata_ty_tuple]
    change Ty.tuple ((items.map (cata_ty wireAlgebra)).map Wire.type) = .tuple items
    congr 1
    rw [List.map_map]
    exact (List.map_congr_left (g := id) ih).trans (List.map_id items)
  | app name items ih =>
    unfold wire
    rw [cata_ty_app]
    change Ty.app name ((items.map (cata_ty wireAlgebra)).map Wire.type) = .app name items
    congr 1
    rw [List.map_map]
    exact (List.map_congr_left (g := id) ih).trans (List.map_id items)
  | _ => rfl

/-- The option decoder's outer equation, used by the unchanged raw codec laws. -/
theorem decodeRaw_option (t : Ty) (j : Json) :
    decodeRaw (.option t) j =
      if fields? j ["_tag"] = some [.str "None"] then some .none
      else (do
        let p ← payload? j "Some" "value"
        (decodeRaw t p).map Store.Val.some) := rfl

theorem decodeRaw_except (e a : Ty) (j : Json) :
    decodeRaw (.except e a) j =
      if let some p := payload? j "Failure" "failure" then
        (decodeRaw e p).map (fun v => .ctor 0 [v])
      else (do
        let p ← payload? j "Success" "success"
        (decodeRaw a p).map (fun v => .ctor 1 [v])) := rfl

theorem decodeRaw_exitOf (a e : Ty) (j : Json) :
    decodeRaw (.exitOf a e) j =
      if let some p := payload? j "Success" "value" then
        (decodeRaw a p).map (fun v => .ctor 0 [v])
      else (do
        let p ← payload? j "Failure" "cause"
        (decodeCause (decodeRaw e) p).map Val.exitErr) := rfl

theorem decodeRaw_union (a b : Ty) (j : Json) :
    decodeRaw (.union a b) j =
      match (decodeRaw a j).filter (fun v => Val.hasTy v a) with
      | some v => some v
      | none => (decodeRaw b j).filter (fun v => Val.hasTy v b && !Val.hasTy v a) := by
  change (match (decodeRaw a j).filter (fun v => Val.hasTy v (wire a).type) with
    | some v => some v
    | none => (decodeRaw b j).filter (fun v => Val.hasTy v (wire b).type && !Val.hasTy v (wire a).type)) = _
  rw [wire_type, wire_type]

theorem encodeRaw_union (a b : Ty) (v : Val) :
    encodeRaw (.union a b) v =
      if Val.hasTy v a then encodeRaw a v
      else if Val.hasTy v b then encodeRaw b v else none := by
  change (if Val.hasTy v (wire a).type then encodeRaw a v
    else if Val.hasTy v (wire b).type then encodeRaw b v else none) = _
  rw [wire_type, wire_type]

theorem decodeRaw_record (fields : List (String × Bool × Ty)) (j : Json) :
    decodeRaw (.record fields) j =
      (objectRead (named (fields.map fun f => (f.1, decodeRaw f.2.2))) j).map Record.frame := by
  unfold decodeRaw wire
  rw [cata_ty_record]
  simp only [wireAlgebra, List.map_map, Function.comp_def, prodMapSnd]

theorem encodeRaw_record (fields : List (String × Bool × Ty)) (v : Val) :
    encodeRaw (.record fields) v = (do
      let es ← Record.entries v
      let js ← objectValues (named (fields.map fun f => (f.1, encodeRaw f.2.2))) es
      pure (.obj js)) := by
  unfold encodeRaw wire
  rw [cata_ty_record]
  simp only [wireAlgebra, List.map_map, Function.comp_def, prodMapSnd]

theorem decodeRaw_map (key value : Ty) (j : Json) :
    decodeRaw (.map key value) j = if key = .string then
      (objectRead (fun _ => decodeRaw value) j).map Map.write else none := by
  change (if (wire key).type = .string then
    (objectRead (fun _ => decodeRaw value) j).map Map.write else none) = _
  rw [wire_type]

theorem encodeRaw_map (key value : Ty) (v : Val) :
    encodeRaw (.map key value) v = if key = .string then (do
      let es ← Map.read v
      let js ← objectValues (fun _ => encodeRaw value) es
      pure (.obj js)) else none := by
  change (if (wire key).type = .string then (do
    let es ← Map.read v
    let js ← objectValues (fun _ => encodeRaw value) es
    pure (Json.obj js)) else none) = _
  rw [wire_type]

theorem decodeRaw_tuple (items : List Ty) (j : Json) :
    decodeRaw (.tuple items) j = match j with
      | .arr js => (positions (items.map decodeRaw) js).map Val.list
      | _ => none := by
  change (cata_ty wireAlgebra (.tuple items)).decode j = _
  rw [cata_ty_tuple]
  change (match j with
    | .arr js => (positions ((items.map (cata_ty wireAlgebra)).map Wire.decode) js).map Val.list
    | _ => none) = _
  have hm : (items.map (cata_ty wireAlgebra)).map Wire.decode = items.map decodeRaw := by
    rw [List.map_map]
    rfl
  rw [hm]

theorem encodeRaw_tuple (items : List Ty) (v : Val) :
    encodeRaw (.tuple items) v = match v with
      | .list vs => (positions (items.map encodeRaw) vs).map Json.arr
      | _ => none := by
  change (cata_ty wireAlgebra (.tuple items)).encode v = _
  rw [cata_ty_tuple]
  change (match v with
    | .list vs => (positions ((items.map (cata_ty wireAlgebra)).map Wire.encode) vs).map Json.arr
    | _ => none) = _
  have hm : (items.map (cata_ty wireAlgebra)).map Wire.encode = items.map encodeRaw := by
    rw [List.map_map]
    rfl
  rw [hm]

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

/-- An object of one entry named neither `boom` nor `payload` is no error image. -/
theorem decodeErr_obj_ne {k : String} (hk : k ≠ "boom") (hp : k ≠ "payload") (y : Json) :
    decodeErr (.obj [(k, y)]) = none := by
  unfold decodeErr
  split
  · rename_i heq
    injection heq with heq
    injection heq with heq
    injection heq with hk' _
    exact absurd hk' hk
  · rename_i heq
    injection heq with heq
    injection heq with heq
    injection heq with hk' _
    exact absurd hk' hp
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
      · by_cases hp : k = "payload"
        · subst hp
          cases x <;> rfl
        · rw [decodeErr_obj_ne hk hp, decodeErr_obj_ne hk hp]
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

/-- Object payload traversal retains its input keys. This serves raw codec exactness. -/
theorem objectValues_keys {α β : Type} (f : String → α → Option β) :
    ∀ (es : List (String × α)) (out : List (String × β)),
      objectValues f es = some out → out.map Prod.fst = es.map Prod.fst
  | [], out, h => by cases h; rfl
  | (key, value) :: es, out, h => by
    simp only [objectValues, List.mapM_cons, Option.bind_eq_bind] at h
    obtain ⟨head, hh, htail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, hout⟩ := Option.bind_eq_some_iff.mp htail
    cases Option.some.inj hout
    obtain ⟨next, hn, rfl⟩ := Option.map_eq_some_iff.mp hh
    simp only [List.map_cons, objectValues_keys f es tail ht]

/-- Object payload decoding ignores recursive JSON key order when each child decoder does. -/
theorem objectValues_normJ (dec : String → Json → Option Val)
    (hdec : ∀ key j, dec key (normJ j) = dec key j) (es : List (String × Json)) :
    objectValues dec (es.map (fun e => (e.1, normJ e.2))) = objectValues dec es := by
  simp only [objectValues, mapM_map_comp, hdec]

/-- Object reading refuses duplicate keys before sorting and decodes independently of key order. -/
theorem objectRead_normJ (dec : String → Json → Option Val)
    (hdec : ∀ key j, dec key (normJ j) = dec key j) (j : Json) :
    objectRead dec (normJ j) = objectRead dec j := by
  cases j with
  | obj es =>
    rw [normJ_obj]
    have hkeys : (sortE (es.map (fun e => (e.1, normJ e.2)))).map Prod.fst |>.Perm (es.map Prod.fst) := by
      simpa only [List.map_map, Function.comp_def] using
        (sortE_perm (es.map (fun e => (e.1, normJ e.2)))).map Prod.fst
    simp only [objectRead]
    by_cases hnd : (es.map Prod.fst).Nodup
    · rw [if_pos (hkeys.nodup_iff.mpr hnd), if_pos hnd]
      rw [Field.canonBy_perm Field.bytesKey_injective (sortE_perm _)
        (hkeys.nodup_iff.mpr hnd), Field.canonBy_map]
      exact objectValues_normJ dec hdec _
    · rw [if_neg (fun h => hnd (hkeys.nodup_iff.mp h)), if_neg hnd]
  | arr js => rw [normJ_arr]; rfl
  | _ => rfl

/-- One decoder per tuple position commutes with recursive JSON key normalization. -/
theorem positions_normJ :
    ∀ (decoders : List (Json → Option Val)),
      (∀ dec ∈ decoders, ∀ j, dec (normJ j) = dec j) →
      ∀ js, positions decoders (js.map normJ) = positions decoders js
  | [], _, [] => rfl
  | [], _, _ :: _ => rfl
  | _ :: _, _, [] => rfl
  | dec :: decoders, hdec, j :: js => by
    simp only [List.map_cons, positions, hdec dec (List.mem_cons_self ..),
      positions_normJ decoders (fun d hd => hdec d (List.mem_cons_of_mem _ hd)) js]

/-- A declared field decoder inherits normalization from its selected child. -/
theorem named_normJ : ∀ (fields : List (String × (Json → Option Val))),
    (∀ f ∈ fields, ∀ j, f.2 (normJ j) = f.2 j) →
    ∀ key j, named fields key (normJ j) = named fields key j
  | [], _, _, _ => rfl
  | f :: fields, h, key, j => by
    simp only [named, Field.firstOf]
    by_cases hk : f.1 = key
    · rw [if_pos hk, Option.bind_some, Option.bind_some]
      exact h f (List.mem_cons_self ..) j
    · rw [if_neg hk]
      exact named_normJ fields (fun f hf => h f (List.mem_cons_of_mem _ hf)) key j

/-- The integer wire reads a datum and its normal form alike: `normJ` keeps a number. The arm of
`decodeRaw_normJ` at `int`. -/
theorem int?_normJ (j : Json) : int? (normJ j) = int? j := by
  cases j <;> rfl

/-- The number wire reads a datum and its normal form alike. The arm of `decodeRaw_normJ` at
`number`. -/
theorem number?_normJ (j : Json) : number? (normJ j) = number? j := by
  cases j <;> rfl

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
    rw [decodeRaw_option, decodeRaw_option]
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
    rw [decodeRaw_except, decodeRaw_except, payload?_normJ, payload?_normJ]
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
    rw [decodeRaw_exitOf, decodeRaw_exitOf, payload?_normJ, payload?_normJ]
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
    rw [decodeRaw_union, decodeRaw_union, iha, ihb]
  | record fields ih =>
    intro j
    rw [decodeRaw_record, decodeRaw_record]
    congr 1
    apply objectRead_normJ
    apply named_normJ
    intro f hf j
    obtain ⟨field, hfield, rfl⟩ := List.mem_map.mp hf
    exact ih field hfield j
  | map key value _ ih =>
    intro j
    rw [decodeRaw_map, decodeRaw_map]
    by_cases hk : key = .string
    · rw [if_pos hk, if_pos hk, objectRead_normJ _ (fun _ => ih)]
    · rw [if_neg hk, if_neg hk]
  | tuple items ih =>
    intro j
    rw [decodeRaw_tuple, decodeRaw_tuple]
    cases j with
    | arr js =>
      rw [normJ_arr]
      change (positions (items.map decodeRaw) (js.map normJ)).map Val.list =
        (positions (items.map decodeRaw) js).map Val.list
      congr 1
      apply positions_normJ
      intro dec hd j
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hd
      exact ih t ht j
    | obj es => rw [normJ_obj]
    | _ => rfl
  | int => intro j; exact int?_normJ j
  | number => intro j; exact number?_normJ j
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


/-! ## Exactness of the two wires of the integers packet (slice 3): `int` and `number` -/

/-- A datum whose sign bit is set is at least the sign bit. A step of `negJson_of_nat?`. -/
theorem signBit_le_of_div {b : Nat} (h : ¬ b / signBit = 0) : signBit ≤ b :=
  Nat.le_of_not_lt fun hlt => h (Nat.div_eq_of_lt hlt)

/-- The datum of a negative integer, rebuilt from the datum of its magnitude: the one fact that
the negative halves of both exactness laws read. A step of `int?_exact` and `number?_exact`. -/
theorem negJson_of_nat? {f : Float64} {m : Nat}
    (hhigh : ¬ f.bits.toNat / signBit = 0)
    (hm : nat? (.number ⟨UInt64.ofNat (f.bits.toNat - signBit)⟩) = some (m + 1)) :
    negJson m = .number f := by
  have hj := nat?_exact hm
  have hj' : Json.number ⟨UInt64.ofNat (f.bits.toNat - signBit)⟩ =
      Json.number ⟨Arch.binary64OfNat (m + 1)⟩ := hj
  have hf : (⟨UInt64.ofNat (f.bits.toNat - signBit)⟩ : Float64) =
      ⟨Arch.binary64OfNat (m + 1)⟩ := Json.number.inj hj'
  have hbits : UInt64.ofNat (f.bits.toNat - signBit) = Arch.binary64OfNat (m + 1) :=
    Float64.mk.inj hf
  have hge : signBit ≤ f.bits.toNat := signBit_le_of_div hhigh
  have hsmall : f.bits.toNat - signBit < UInt64.size :=
    Nat.lt_of_le_of_lt (Nat.sub_le _ _) f.bits.toNat_lt
  unfold negJson
  rw [← hbits, UInt64.toNat_ofNat_of_lt' hsmall, Nat.sub_add_cancel hge, UInt64.ofNat_toNat]

/-- **Exactness of the integer wire**: a datum that reads as an integer is that integer's image.
`decodeRaw_exact` takes it at the leaf `int`, with the datum itself as the witness. -/
theorem int?_exact {j : Json} {v : Val} (h : int? j = some v) : intJson v = some j := by
  cases j with
  | number f =>
    simp only [int?] at h
    split at h
    · obtain ⟨m, hm, hle⟩ := Option.bind_eq_some_iff.mp h
      split at hle
      · next hbound =>
        cases hle
        have hj := nat?_exact hm
        simp only [intJson, if_pos hbound, hj]
      · exact nomatch hle
    · next hhigh =>
      obtain ⟨m, hm, hneg⟩ := Option.bind_eq_some_iff.mp h
      split at hneg
      · exact nomatch hneg
      · next hok =>
        cases hneg
        have hpos : 0 < m := Nat.pos_of_ne_zero fun h0 => hok (.inl h0)
        have hcancel : m - 1 + 1 = m := Nat.sub_add_cancel hpos
        have hbound : m - 1 + 1 ≤ safeBound := by
          rw [hcancel]
          exact Nat.le_of_not_lt fun hlt => hok (.inr hlt)
        have hm' : nat? (.number ⟨UInt64.ofNat (f.bits.toNat - signBit)⟩) = some (m - 1 + 1) := by
          rw [hm, hcancel]
        simp only [intJson, if_pos hbound, negJson_of_nat? hhigh hm']
  | _ => exact nomatch h

/-- **Exactness of the number wire**: a datum that reads as a number is that number's image.
`decodeRaw_exact` takes it at the leaf `number`. -/
theorem number?_exact {j : Json} {v : Val} (h : number? j = some v) : numberJson v = some j := by
  cases j with
  | number f =>
    simp only [number?] at h
    split at h
    · exact nomatch h
    · next hfinite =>
      have hfin : f.isFinite = true := by
        cases hf : f.isFinite with
        | true => rfl
        | false => exact absurd (by rw [hf]; rfl) hfinite
      split at h
      · next hframe =>
        cases h
        have hsame : (⟨f.bits⟩ : Float64) = f := rfl
        simp only [numberJson, hframe, hsame, hfin, Bool.and_self, if_true]
      · split at h
        · obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
          have hj := nat?_exact hn
          simp only [numberJson]
          rw [← hj, if_pos hn]
        · next hhigh =>
          obtain ⟨m, hm, hneg⟩ := Option.bind_eq_some_iff.mp h
          split at hneg
          · exact nomatch hneg
          · next hne =>
            cases hneg
            have hcancel : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.pos_of_ne_zero hne)
            have hm' : nat? (.number ⟨UInt64.ofNat (f.bits.toNat - signBit)⟩) =
                some (m - 1 + 1) := by
              rw [hm, hcancel]
            have hj := nat?_exact hm'
            simp only [numberJson]
            rw [← hj, if_pos hm', negJson_of_nat? hhigh hm']
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
    (hlt : Field.ltKey (keyBytes "_tag") (keyBytes field) = true)
    (hgt : Field.ltKey (keyBytes field) (keyBytes "_tag") = false) (p : Json) :
    normJ (.obj [("_tag", .str tag), (field, p)]) = .obj [("_tag", .str tag), (field, normJ p)] ∧
      normJ (.obj [(field, p), ("_tag", .str tag)]) = .obj [("_tag", .str tag), (field, normJ p)] := by
  rw [normJ_obj, normJ_obj]
  simp only [List.map_cons, List.map_nil, sortE, List.foldl_cons, List.foldl_nil, insertE, hlt,
    hgt, ↓reduceIte]
  exact ⟨rfl, rfl⟩

/-- **The object step of exactness**: a payload read off `j`, re-encoded at its tag, is `j`
modulo `N_J`. -/
theorem normJ_tagged_of_payload {tag field : String} (hne : "_tag" ≠ field)
    (hlt : Field.ltKey (keyBytes "_tag") (keyBytes field) = true)
    (hgt : Field.ltKey (keyBytes field) (keyBytes "_tag") = false) {j p q : Json}
    (h : payload? j tag field = some p) (hq : normJ q = normJ p) :
    normJ (tagged tag field q) = normJ j := by
  have ho := normJ_tagged_orders (tag := tag) hlt hgt q
  have hp := normJ_tagged_orders (tag := tag) hlt hgt p
  rw [show tagged tag field q = .obj [("_tag", .str tag), (field, q)] from rfl, ho.1, hq]
  rcases payload?_exact hne h with rfl | rfl
  · rw [hp.1]
  · rw [hp.2]

/-- The tag names the codec uses, in the byte order: `_tag` sorts first. -/
theorem key_value : Field.ltKey (keyBytes "_tag") (keyBytes "value") = true ∧
    Field.ltKey (keyBytes "value") (keyBytes "_tag") = false := by decide +kernel
theorem key_failure : Field.ltKey (keyBytes "_tag") (keyBytes "failure") = true ∧
    Field.ltKey (keyBytes "failure") (keyBytes "_tag") = false := by decide +kernel
theorem key_success : Field.ltKey (keyBytes "_tag") (keyBytes "success") = true ∧
    Field.ltKey (keyBytes "success") (keyBytes "_tag") = false := by decide +kernel
theorem key_cause : Field.ltKey (keyBytes "_tag") (keyBytes "cause") = true ∧
    Field.ltKey (keyBytes "cause") (keyBytes "_tag") = false := by decide +kernel
theorem key_error : Field.ltKey (keyBytes "_tag") (keyBytes "error") = true ∧
    Field.ltKey (keyBytes "error") (keyBytes "_tag") = false := by decide +kernel
theorem key_defect : Field.ltKey (keyBytes "_tag") (keyBytes "defect") = true ∧
    Field.ltKey (keyBytes "defect") (keyBytes "_tag") = false := by decide +kernel
theorem key_fiberId : Field.ltKey (keyBytes "_tag") (keyBytes "fiberId") = true ∧
    Field.ltKey (keyBytes "fiberId") (keyBytes "_tag") = false := by decide +kernel

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

/-- A payload's JSON text is exact (decisions row 120): what reads is the lowercase hexadecimal
of the payload's canonical bytes (`payloadHex`), character for character. Concept
`exact-codecs`; a step of `decodeErr_exact`. -/
theorem payloadOfHex?_exact {hex : String} {p : Payload} (h : payloadOfHex? hex = some p) :
    payloadHex p = hex := by
  unfold payloadOfHex? at h
  obtain ⟨bytes, _, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨q, _, h⟩ := Option.bind_eq_some_iff.mp h
  split at h
  · next hq =>
    cases h
    exact hq
  · exact nomatch h

/-- What decodes as an error re-encodes to the same JSON: exact without a normaliser, the
payload's arm included (decisions row 120). -/
theorem decodeErr_exact {j : Json} {e : Err} (h : decodeErr j = some e) : encodeErr e = j := by
  unfold decodeErr at h
  split at h
  · cases h
    rfl
  · next hex =>
    obtain ⟨p, hp, rfl⟩ := Option.map_eq_some_iff.mp h
    show Json.obj [("payload", .str (payloadHex p))] = Json.obj [("payload", .str hex)]
    rw [payloadOfHex?_exact hp]
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

/-- Stable JSON insertion agrees with field insertion when the inserted key is fresh. -/
theorem insertE_eq_insertBy (e : String × Json) :
    ∀ es, e.1 ∉ es.map Prod.fst → insertE e es = Field.insertBy Field.bytesKey e es
  | [], _ => rfl
  | f :: fs, h => by
    have hn : e.1 ≠ f.1 := by
      intro he
      exact h (List.mem_map.mpr ⟨f, List.mem_cons_self .., he.symm⟩)
    have ht : e.1 ∉ fs.map Prod.fst := fun hm => h (List.mem_cons_of_mem _ hm)
    change (if Field.ltKey (Field.bytesKey e.1) (Field.bytesKey f.1) = true then e :: f :: fs
      else f :: insertE e fs) = _
    rw [Field.insertBy]
    by_cases hl : Field.ltKey (Field.bytesKey e.1) (Field.bytesKey f.1) = true
    · rw [if_pos hl, if_pos hl]
    · rw [if_neg hl, if_neg hl,
        if_neg (fun he => hn (Field.bytesKey_injective _ _ he)), insertE_eq_insertBy e fs ht]

/-- The JSON key sort is field canonicalization only when no key repeats.
The duplicate-retaining normalizer itself remains unchanged. -/
theorem sortE_eq_canonBy (es : List (String × Json)) (hnd : (es.map Prod.fst).Nodup) :
    sortE es = Field.canonBy Field.bytesKey es := by
  have walk : ∀ (xs acc : List (String × Json)), ((acc ++ xs).map Prod.fst).Nodup →
      xs.foldl (fun acc e => insertE e acc) acc =
        xs.foldl (fun acc e => Field.insertBy Field.bytesKey e acc) acc := by
    intro xs
    induction xs with
    | nil => intro acc h; rfl
    | cons e xs ih =>
      intro acc h
      have hp : (acc ++ e :: xs).Perm (e :: acc ++ xs) := List.perm_middle
      have hn := (hp.map Prod.fst).nodup_iff.mp h
      have hf : e.1 ∉ acc.map Prod.fst := by
        intro hm
        apply (List.nodup_cons.mp hn).1
        change e.1 ∈ (acc ++ xs).map Prod.fst
        rw [List.map_append]
        exact List.mem_append_left (xs.map Prod.fst) hm
      have hi : (insertE e acc ++ xs).Perm (acc ++ e :: xs) :=
        ((insertE_perm e acc).append_right xs).trans List.perm_middle.symm
      have ht := (hi.map Prod.fst).nodup_iff.mpr h
      rw [List.foldl_cons, List.foldl_cons, ih _ ht, insertE_eq_insertBy e acc hf]
  exact walk es [] hnd

/-- Sorting distinct object keys before decoding does not change their normalized JSON image. -/
theorem normJ_canonBy (es : List (String × Json)) (hnd : (es.map Prod.fst).Nodup) :
    normJ (.obj (Field.canonBy Field.bytesKey es)) = normJ (.obj es) := by
  have hnorm : ((es.map (fun e => (e.1, normJ e.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using hnd
  have hcanon : (((Field.canonBy Field.bytesKey es).map (fun e => (e.1, normJ e.2))).map Prod.fst).Nodup := by
    simpa only [List.map_map, Function.comp_def] using Field.canonBy_names_nodup (key := Field.bytesKey) es
  rw [normJ_obj, normJ_obj, sortE_eq_canonBy _ hcanon, sortE_eq_canonBy _ hnorm,
    ← Field.canonBy_map, Field.canonBy_idem]

/-- Successful object payload conversion keeps each key and reconstructs each normalized payload. -/
theorem objectValues_exact (dec : String → Json → Option Val) (enc : String → Val → Option Json)
    (hex : ∀ key j v, dec key j = some v → ∃ j', enc key v = some j' ∧ normJ j' = normJ j) :
    ∀ (es : List (String × Json)) (vs : List (String × Val)), objectValues dec es = some vs →
      ∃ js, objectValues enc vs = some js ∧ normEs js = normEs es
  | [], vs, h => by cases h; exact ⟨[], rfl, rfl⟩
  | (key, j) :: es, vs, h => by
    simp only [objectValues, List.mapM_cons, Option.bind_eq_bind] at h
    obtain ⟨head, hh, htail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, hout⟩ := Option.bind_eq_some_iff.mp htail
    cases Option.some.inj hout
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hh
    obtain ⟨j', he, hn⟩ := hex key j v hv
    obtain ⟨js, hes, hns⟩ := objectValues_exact dec enc hex es tail ht
    refine ⟨(key, j') :: js, ?_, ?_⟩
    · simp only [objectValues] at hes ⊢
      simp only [List.mapM_cons, he, Option.map_some, hes, Option.bind_eq_bind,
        Option.bind_some, pure, Pure.pure]
    · simp only [normEs, hn, hns]

/-- A per-name codec table inherits exactness from the selected declared child. -/
theorem named_exact {α : Type} (dec : α → Json → Option Val) (enc : α → Val → Option Json) :
    ∀ (fields : List (String × α)),
      (∀ f ∈ fields, ∀ j v, dec f.2 j = some v → ∃ j', enc f.2 v = some j' ∧ normJ j' = normJ j) →
      ∀ key j v, named (fields.map (fun f => (f.1, dec f.2))) key j = some v →
        ∃ j', named (fields.map (fun f => (f.1, enc f.2))) key v = some j' ∧ normJ j' = normJ j
  | [], _, _, _, _, h => nomatch h
  | f :: fields, hex, key, j, v, h => by
    simp only [List.map_cons, named, Field.firstOf] at h ⊢
    by_cases hk : f.1 = key
    · rw [if_pos hk, Option.bind_some] at h
      rw [if_pos hk, Option.bind_some]
      exact hex f (List.mem_cons_self ..) j v h
    · rw [if_neg hk] at h ⊢
      exact named_exact dec enc fields (fun f hf => hex f (List.mem_cons_of_mem _ hf)) key j v h

/-- Positional decoding reconstructs an equally long encoder image. -/
theorem positions_exact {α : Type} (dec : α → Json → Option Val) (enc : α → Val → Option Json) :
    ∀ (items : List α),
      (∀ t ∈ items, ∀ j v, dec t j = some v → ∃ j', enc t v = some j' ∧ normJ j' = normJ j) →
      ∀ js vs, positions (items.map dec) js = some vs →
        ∃ js', positions (items.map enc) vs = some js' ∧ js'.map normJ = js.map normJ
  | [], _, [], vs, h => by cases h; exact ⟨[], rfl, rfl⟩
  | [], _, _ :: _, _, h => nomatch h
  | _ :: _, _, [], _, h => nomatch h
  | t :: items, hex, j :: js, vs, h => by
    simp only [List.map_cons, positions, Option.bind_eq_bind] at h
    obtain ⟨v, hv, htail⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨tail, ht, hout⟩ := Option.bind_eq_some_iff.mp htail
    cases Option.some.inj hout
    obtain ⟨j', he, hn⟩ := hex t (List.mem_cons_self ..) j v hv
    obtain ⟨js', hes, hns⟩ := positions_exact dec enc items
      (fun t ht => hex t (List.mem_cons_of_mem _ ht)) js tail ht
    refine ⟨j' :: js', ?_, ?_⟩
    · simp only [List.map_cons, positions, he, Option.bind_eq_bind, Option.bind_some, hes,
        pure, Pure.pure]
    · simp only [List.map_cons, hn, hns]

/-- A frame reconstructed by the object decoder reads back without losing a field. -/
theorem entries_frame (es : List (String × Val)) (h : (es.map Prod.fst).Nodup) :
    Record.entries (Record.frame es) = some es := by
  simp only [Record.entries, Record.frame, Program.recordParts?, Option.bind_eq_bind,
    Option.bind_some, Typed.readColumns_frame, if_pos h]

/-- Object decoding supplies both frame validity and the encoder's normalized object image. -/
theorem objectRead_exact (dec : String → Json → Option Val) (enc : String → Val → Option Json)
    (hex : ∀ key j v, dec key j = some v → ∃ j', enc key v = some j' ∧ normJ j' = normJ j)
    (j : Json) (vs : List (String × Val)) (h : objectRead dec j = some vs) :
    (vs.map Prod.fst).Nodup ∧ ∃ js, objectValues enc vs = some js ∧ normJ (.obj js) = normJ j := by
  cases j with
  | obj es =>
    change (if (es.map Prod.fst).Nodup then
      objectValues dec (Field.canonBy Field.bytesKey es) else none) = some vs at h
    by_cases hnd : (es.map Prod.fst).Nodup
    · rw [if_pos hnd] at h
      have hk := objectValues_keys dec _ _ h
      obtain ⟨js, he, hn⟩ := objectValues_exact dec enc hex _ _ h
      refine ⟨?_, js, he, ?_⟩
      · rw [hk]
        exact Field.canonBy_names_nodup (key := Field.bytesKey) es
      · rw [normJ, hn]
        exact normJ_canonBy es hnd
    · rw [if_neg hnd] at h
      exact nomatch h
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
    rw [decodeRaw_option] at h
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
    rw [decodeRaw_except] at h
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
    rw [decodeRaw_exitOf] at h
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
    rw [decodeRaw_union] at h
    split at h
    · rename_i w hw
      have hwv : w = v := Option.some.inj h
      subst hwv
      obtain ⟨hdw, hmem⟩ := Option.filter_eq_some_iff.mp hw
      obtain ⟨j', he, hn⟩ := iha j w hdw
      refine ⟨j', ?_, hn⟩
      rw [encodeRaw_union]
      rw [if_pos hmem]
      exact he
    · obtain ⟨hdv, hmem⟩ := Option.filter_eq_some_iff.mp h
      rw [Bool.and_eq_true, Bool.not_eq_true'] at hmem
      obtain ⟨j', he, hn⟩ := ihb j v hdv
      refine ⟨j', ?_, hn⟩
      rw [encodeRaw_union]
      rw [if_neg (by rw [hmem.2]; exact Bool.false_ne_true), if_pos hmem.1]
      exact he
  | record fields ih =>
    intro j v h
    rw [decodeRaw_record] at h
    obtain ⟨es, hes, rfl⟩ := Option.map_eq_some_iff.mp h
    have hx := objectRead_exact
      (named (fields.map fun f => (f.1, decodeRaw f.2.2)))
      (named (fields.map fun f => (f.1, encodeRaw f.2.2)))
      (named_exact (fun f : Bool × Ty => decodeRaw f.2)
        (fun f : Bool × Ty => encodeRaw f.2) fields ih) j es hes
    obtain ⟨hnd, js, he, hn⟩ := hx
    refine ⟨.obj js, ?_, hn⟩
    rw [encodeRaw_record, entries_frame es hnd, Option.bind_eq_bind, Option.bind_some, he]
    rfl
  | map key value _ ih =>
    intro j v h
    rw [decodeRaw_map] at h
    by_cases hk : key = .string
    · rw [if_pos hk] at h
      obtain ⟨es, hes, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨_, js, he, hn⟩ := objectRead_exact
        (fun _ => decodeRaw value) (fun _ => encodeRaw value) (fun _ => ih) j es hes
      refine ⟨.obj js, ?_, hn⟩
      rw [encodeRaw_map, if_pos hk, Map.read_write, Option.bind_eq_bind, Option.bind_some, he]
      rfl
    · rw [if_neg hk] at h
      exact nomatch h
  | tuple items ih =>
    intro j v h
    rw [decodeRaw_tuple] at h
    cases j with
    | arr js =>
      obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp h
      obtain ⟨js', he, hn⟩ := positions_exact decodeRaw encodeRaw items ih js vs hvs
      refine ⟨.arr js', ?_, ?_⟩
      · rw [encodeRaw_tuple]
        change (positions (items.map encodeRaw) vs).map Json.arr = _
        rw [he]
        rfl
      · rw [normJ_arr, normJ_arr, hn]
    | _ => exact nomatch h
  | int => intro j v h; exact ⟨j, int?_exact h, rfl⟩
  | number => intro j v h; exact ⟨j, number?_exact h, rfl⟩
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
  change (if some (Val.str s : Val) = some (.str s) then some (Json.str s) else none) = _
  rw [if_pos rfl]

theorem encode_bool (b : Bool) : encode .bool (.bool b) = some (.bool b) := by
  change (if some (Val.bool b : Val) = some (.bool b) then some (Json.bool b) else none) = _
  rw [if_pos rfl]

theorem encode_unit : encode .unit .unit = some .null := rfl

end Effect4.Schema
