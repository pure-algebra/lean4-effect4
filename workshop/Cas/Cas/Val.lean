import Cas.Utf8

/-!
# Cas.Val

Owner: the value tree every canonical carrier is an isomorphic image of, its one byte codec,
and the two laws that make the codec exact.

`Val` is the tag alphabet of `src/Effect4/Store/Canonical.lean:59-74` as an inductive, plus
the two frames the Wire and the address plan add: `ctor` (`Wire.lean:34-36`, tag 10) and
`ref` (the facts note, Q4, tag 11). Every frame is `tag :: be64 length ++ payload`
(`Canonical.lean:55-57`), so the bytes of a `Val` are the bytes today's instances write:
`encode (.nat 256) = [2, 0,0,0,0,0,0,0,2, 1, 0]`, a `ctor` is `framed 10 (encode (nat i) ++
args.flatten)`, a `ref` is `framed 11 (kind :: digest)`; the guards at the end are
`Test/Store/StoreContract.lean:39-47` restated on `Val`.

The decoder is the Wire's (`Wire.lean:174-269`, `567-572`): length-directed frames, exact,
total under fuel. It is organised as Foldlab's node codec is (stage readers with an
`_append`/`_encode` and an `_exact` lemma each; no composition deeper than two stages):
`readFrame` splits one frame off the front; `decodeSeq` reads frames back to back with a
count bound; `decodeBody` reads one frame's payload for its tag, given the reader for the
children; `decodeOne` ties the knot on fuel. Fuel is the byte length plus one: every frame is
at least nine bytes longer than any child, so the children always have fuel left
(`length_encode_child`). The count bound of `decodeSeq` is the payload length: a frame is at
least one byte. The laws are `decode_encode` for well-formed values, `decode_exact` (the
decoder accepts nothing outside the encoder's image, and what it accepts is well-formed), and
`encode_injective` on well-formed values as a corollary.

`Val.WF` says every frame's payload is shorter than `2^64`, the one fact a length prefix cannot
carry. It is a `Prop` by structural recursion with a Boolean companion, as `Data/Json.lean`
does for `NumbersFinite`, and it is what `decode_exact` gives back.
-/

set_option autoImplicit false

namespace Effect4.Store

/-! ## Frames and tags -/

/-- One frame: the tag, the payload length, the payload (`Canonical.lean:55-57`). -/
def framed (tag : UInt8) (payload : Bytes) : Bytes :=
  tag :: (be64 payload.length ++ payload)

/-! The tag alphabet, one byte per frame shape; 1–9 are `Canonical.lean:60-69`, `ctor` is
`Canonical.lean:73`, `ref` is new. Bytes are identity: appended, never renumbered. -/
namespace Tag
def bool : UInt8 := 1
def nat : UInt8 := 2
def string : UInt8 := 3
def list : UInt8 := 4
def pair : UInt8 := 5
def none : UInt8 := 6
def some : UInt8 := 7
def bytes : UInt8 := 8
def unit : UInt8 := 9
/-- A constructor application: the index as a `nat` frame, then the framed arguments. -/
def ctor : UInt8 := 10
/-- A reference to a node: the kind byte, then the address bytes. -/
def ref : UInt8 := 11
end Tag

/-- The tag is the first byte of every frame. -/
theorem framed_head (tag : UInt8) (payload : Bytes) : (framed tag payload).head? = some tag := rfl

/-- A frame is nine bytes longer than its payload. -/
theorem framed_length (tag : UInt8) (payload : Bytes) :
    (framed tag payload).length = payload.length + 9 := by
  simp only [framed, List.length_cons, List.length_append, length_be64]
  omega

/-- Framing at one tag is injective: equal frames carry equal payloads. -/
theorem framed_inj {tag : UInt8} {p q : Bytes} (h : framed tag p = framed tag q) : p = q :=
  List.append_inj_right (List.cons.inj h).2 (by rw [length_be64, length_be64])

theorem framed_ne_nil (tag : UInt8) (payload : Bytes) : framed tag payload ≠ [] :=
  List.cons_ne_nil _ _

/-! ## The value tree -/

/-- The value tree: the tag alphabet as an inductive. A carrier's `toVal` lands here, and the
one codec below turns it into bytes. -/
inductive Val where
  | unit
  | bool (b : Bool)
  | nat (n : Nat)
  | str (s : String)
  | bytes (bs : Bytes)
  | list (xs : List Val)
  | pair (a b : Val)
  | none
  | some (a : Val)
  /-- A constructor application: the 0-based index in declaration order, then the arguments. -/
  | ctor (index : Nat) (args : List Val)
  /-- A reference to a node: the kind byte, then the address bytes. -/
  | ref (kind : UInt8) (digest : Bytes)
deriving Repr, Inhabited

namespace Val

mutual
/-- The canonical bytes of a value: the frames of `Canonical.lean:88-112`, `Wire.lean:35-36`. -/
def encode : Val → Bytes
  | .unit => framed Tag.unit []
  | .bool b => framed Tag.bool [if b then 1 else 0]
  | .nat n => framed Tag.nat (natBytes n)
  | .str s => framed Tag.string s.toUTF8.data.toList
  | .bytes bs => framed Tag.bytes bs
  | .list xs => framed Tag.list (encodeList xs)
  | .pair a b => framed Tag.pair (encode a ++ encode b)
  | .none => framed Tag.none []
  | .some a => framed Tag.some (encode a)
  | .ctor i args => framed Tag.ctor (framed Tag.nat (natBytes i) ++ encodeList args)
  | .ref k d => framed Tag.ref (k :: d)
/-- The frames of a list of values, back to back. -/
def encodeList : List Val → Bytes
  | [] => []
  | x :: xs => encode x ++ encodeList xs
end

theorem encodeList_nil : encodeList [] = [] := rfl

theorem encodeList_cons (x : Val) (xs : List Val) : encodeList (x :: xs) = encode x ++ encodeList xs := rfl

/-- `encodeList` is the flattened map, the spelling of `Wire.ctor` (`Wire.lean:36`). -/
theorem encodeList_eq_flatten (xs : List Val) : encodeList xs = (xs.map encode).flatten := by
  induction xs with
  | nil => rfl
  | cons x xs ih => rw [encodeList_cons, List.map_cons, List.flatten_cons, ih]

/-- The tag of a value's frame. -/
def tag : Val → UInt8
  | .unit => Tag.unit
  | .bool _ => Tag.bool
  | .nat _ => Tag.nat
  | .str _ => Tag.string
  | .bytes _ => Tag.bytes
  | .list _ => Tag.list
  | .pair _ _ => Tag.pair
  | .none => Tag.none
  | .some _ => Tag.some
  | .ctor _ _ => Tag.ctor
  | .ref _ _ => Tag.ref

/-- The payload of a value's frame. -/
def payload : Val → Bytes
  | .unit => []
  | .bool b => [if b then 1 else 0]
  | .nat n => natBytes n
  | .str s => s.toUTF8.data.toList
  | .bytes bs => bs
  | .list xs => encodeList xs
  | .pair a b => encode a ++ encode b
  | .none => []
  | .some a => encode a
  | .ctor i args => framed Tag.nat (natBytes i) ++ encodeList args
  | .ref k d => k :: d

/-- Every encoding is one frame: its tag, its payload. -/
theorem encode_eq (v : Val) : encode v = framed v.tag v.payload := by
  cases v <;> rfl

/-- The single-motive induction principle for the nested inductive, in the membership form
`Data/Json.lean:304-339` gives `Json`: one hypothesis per constructor, the children of a `list`
or `ctor` quantified by membership. This is what an exactness proof over a carrier's `ofVal`
inducts with, since `termination_by structural` cannot follow a `split` into the payload
list. -/
theorem ind {motive : Val → Prop}
    (unit : motive .unit) (bool : ∀ b, motive (.bool b)) (nat : ∀ n, motive (.nat n))
    (str : ∀ s, motive (.str s)) (bytes : ∀ bs, motive (.bytes bs))
    (list : ∀ xs, (∀ x ∈ xs, motive x) → motive (.list xs))
    (pair : ∀ a b, motive a → motive b → motive (.pair a b))
    (none : motive .none) (some : ∀ a, motive a → motive (.some a))
    (ctor : ∀ i args, (∀ x ∈ args, motive x) → motive (.ctor i args))
    (ref : ∀ k d, motive (.ref k d)) : ∀ v, motive v :=
  fun v =>
    Val.rec (motive_1 := motive) (motive_2 := fun xs => ∀ x ∈ xs, motive x)
      unit bool nat str bytes list pair none some ctor ref
      (by intro _ h; cases h)
      (fun _ _ ihHead ihTail => by
        intro _ hmem
        cases hmem with
        | head => exact ihHead
        | tail _ hmem' => exact ihTail _ hmem')
      v

/-- The children a frame's payload carries, in payload order. -/
def children : Val → List Val
  | .list xs => xs
  | .pair a b => [a, b]
  | .some a => [a]
  | .ctor _ args => args
  | _ => []

/-! ## Well-formedness: every payload shorter than `2^64` -/

mutual
/-- Every frame's payload is shorter than `2^64`, so its length prefix is exact. -/
def WF : Val → Prop
  | .unit => True
  | .bool _ => True
  | .nat n => (natBytes n).length < 2 ^ 64
  | .str s => s.toUTF8.data.toList.length < 2 ^ 64
  | .bytes bs => bs.length < 2 ^ 64
  | .list xs => (encodeList xs).length < 2 ^ 64 ∧ WFList xs
  | .pair a b => (encode a ++ encode b).length < 2 ^ 64 ∧ WF a ∧ WF b
  | .none => True
  | .some a => (encode a).length < 2 ^ 64 ∧ WF a
  | .ctor i args =>
    (natBytes i).length < 2 ^ 64 ∧ (framed Tag.nat (natBytes i) ++ encodeList args).length < 2 ^ 64 ∧
      WFList args
  | .ref k d => (k :: d).length < 2 ^ 64
/-- `WF` at every member. -/
def WFList : List Val → Prop
  | [] => True
  | x :: xs => WF x ∧ WFList xs
end

mutual
/-- The Boolean companion of `WF`. -/
def wf : Val → Bool
  | .unit => true
  | .bool _ => true
  | .nat n => decide ((natBytes n).length < 2 ^ 64)
  | .str s => decide (s.toUTF8.data.toList.length < 2 ^ 64)
  | .bytes bs => decide (bs.length < 2 ^ 64)
  | .list xs => decide ((encodeList xs).length < 2 ^ 64) && wfList xs
  | .pair a b => decide ((encode a ++ encode b).length < 2 ^ 64) && wf a && wf b
  | .none => true
  | .some a => decide ((encode a).length < 2 ^ 64) && wf a
  | .ctor i args =>
    decide ((natBytes i).length < 2 ^ 64) &&
      decide ((framed Tag.nat (natBytes i) ++ encodeList args).length < 2 ^ 64) && wfList args
  | .ref k d => decide ((k :: d).length < 2 ^ 64)
/-- `wf` at every member. -/
def wfList : List Val → Bool
  | [] => true
  | x :: xs => wf x && wfList xs
end

mutual
theorem wf_iff (v : Val) : wf v = true ↔ WF v := by
  cases v
  case pair a b =>
    simp [wf, WF, wf_iff a, wf_iff b, and_assoc]
  case some a =>
    simp [wf, WF, wf_iff a]
  case list xs =>
    simp [wf, WF, wfList_iff xs]
  case ctor i args =>
    simp [wf, WF, wfList_iff args, and_assoc]
  all_goals simp [wf, WF]
termination_by structural v
theorem wfList_iff (xs : List Val) : wfList xs = true ↔ WFList xs := by
  match xs with
  | [] => simp [wfList, WFList]
  | x :: xs => simp [wfList, WFList, wf_iff x, wfList_iff xs]
termination_by structural xs
end

instance decWF : DecidablePred WF := fun v => decidable_of_iff _ (wf_iff v)

theorem WFList_mem {xs : List Val} (h : WFList xs) {c : Val} (hc : c ∈ xs) : WF c := by
  induction xs with
  | nil => exact nomatch hc
  | cons x xs ih =>
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact h.1
    · exact ih h.2 hc'

theorem WFList_of_forall {xs : List Val} (h : ∀ c ∈ xs, WF c) : WFList xs := by
  induction xs with
  | nil => trivial
  | cons x xs ih => exact ⟨h x (by simp), ih fun c hc => h c (by simp [hc])⟩

/-- A well-formed value's payload fits its length prefix. -/
theorem WF_payload_lt {v : Val} (h : WF v) : v.payload.length < 2 ^ 64 := by
  cases v with
  | unit => exact Nat.pow_pos (by decide)
  | bool b =>
    show 1 < 2 ^ 64
    decide
  | nat n => exact h
  | str s => exact h
  | bytes bs => exact h
  | list xs => exact h.1
  | pair a b => exact h.1
  | none => exact Nat.pow_pos (by decide)
  | some a => exact h.1
  | ctor i args => exact h.2.1
  | ref k d => exact h

/-- Well-formedness reaches every child. -/
theorem WF_child {v c : Val} (hv : WF v) (hc : c ∈ v.children) : WF c := by
  cases v
  case list xs => exact WFList_mem hv.2 hc
  case pair a b =>
    have hc' : c ∈ [a, b] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl
    · exact hv.2.1
    · exact hv.2.2
  case some a =>
    have hc' : c ∈ [a] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    exact hv.2
  case ctor i args => exact WFList_mem hv.2.2 hc
  all_goals exact nomatch hc

/-! ## Lengths: the fuel and count arguments -/

theorem length_encode_le_encodeList {xs : List Val} {c : Val} (hc : c ∈ xs) :
    (encode c).length ≤ (encodeList xs).length := by
  induction xs with
  | nil => exact nomatch hc
  | cons x xs ih =>
    rw [encodeList_cons, List.length_append]
    rcases List.mem_cons.mp hc with rfl | hc'
    · exact Nat.le_add_right _ _
    · exact Nat.le_trans (ih hc') (Nat.le_add_left _ _)

/-- Every child's frame is at least nine bytes shorter than the frame around it: the fuel
argument. -/
theorem length_encode_child {v c : Val} (hc : c ∈ v.children) :
    (encode c).length + 9 ≤ (encode v).length := by
  rw [encode_eq v, framed_length]
  cases v
  case list xs =>
    have hc' : c ∈ xs := hc
    exact Nat.add_le_add_right (length_encode_le_encodeList hc') 9
  case pair a b =>
    have hc' : c ∈ [a, b] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    simp only [payload, List.length_append]
    rcases hc' with rfl | rfl <;> omega
  case some a =>
    have hc' : c ∈ [a] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    subst hc'
    exact Nat.le_refl _
  case ctor i args =>
    have hc' : c ∈ args := hc
    simp only [payload, List.length_append]
    have := length_encode_le_encodeList hc'
    omega
  all_goals exact nomatch hc

/-- A frame is at least one byte, so a payload holds no more frames than bytes: the count
argument. -/
theorem length_le_encodeList (xs : List Val) : xs.length ≤ (encodeList xs).length := by
  induction xs with
  | nil => exact Nat.le_refl _
  | cons x xs ih =>
    rw [encodeList_cons, List.length_append, List.length_cons, encode_eq, framed_length]
    omega

end Val

/-! ## Stage: one frame -/

/-- One frame: the tag, its payload, the rest (`Wire.lean:180-187`). -/
def readFrame : Bytes → Option (UInt8 × Bytes × Bytes)
  | [] => none
  | tag :: rest =>
    if rest.length < 8 then none else
      let len := natOfDigits (rest.take 8)
      let body := rest.drop 8
      if body.length < len then none else some (tag, body.take len, body.drop len)

theorem readFrame_append (tag : UInt8) (payload rest : Bytes) (h : payload.length < 2 ^ 64) :
    readFrame (framed tag payload ++ rest) = some (tag, payload, rest) := by
  have hlen : (be64 payload.length).length = 8 := length_be64 _
  have htake : (be64 payload.length ++ (payload ++ rest)).take 8 = be64 payload.length := by
    rw [← hlen, List.take_left]
  have hdrop : (be64 payload.length ++ (payload ++ rest)).drop 8 = payload ++ rest := by
    rw [← hlen, List.drop_left]
  have hge : ¬ (be64 payload.length ++ (payload ++ rest)).length < 8 := by
    rw [List.length_append, hlen]
    omega
  have hbody : ¬ (payload ++ rest).length < payload.length := by
    rw [List.length_append]
    omega
  simp only [framed, List.cons_append, List.append_assoc, readFrame, if_neg hge, htake, hdrop,
    natOfDigits_be64, Nat.mod_eq_of_lt h, if_neg hbody, List.take_left, List.drop_left]

theorem readFrame_exact {b : Bytes} {tag : UInt8} {payload rest : Bytes}
    (h : readFrame b = some (tag, payload, rest)) :
    b = framed tag payload ++ rest ∧ payload.length < 2 ^ 64 := by
  cases b with
  | nil => exact nomatch h
  | cons t r =>
    simp only [readFrame] at h
    split at h
    · exact nomatch h
    · next hge =>
      split at h
      · exact nomatch h
      · next hlt =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨ht, hp, hr⟩ := h
        subst ht hp hr
        have hlen8 : (r.take 8).length = 8 := by
          rw [List.length_take]
          omega
        have hlen : ((r.drop 8).take (natOfDigits (r.take 8))).length = natOfDigits (r.take 8) := by
          rw [List.length_take]
          omega
        constructor
        · simp only [framed, List.cons_append]
          congr 1
          rw [hlen, be64_natOfDigits _ hlen8, List.append_assoc, List.take_append_drop,
            List.take_append_drop]
        · rw [hlen]
          have := natOfDigits_lt (r.take 8)
          rw [hlen8] at this
          exact this

/-! ## Stage: frames back to back -/

/-- Frames back to back until the input is exhausted, at most `n` of them; the element
reader is a parameter so the stage is not part of the fuel recursion. -/
def decodeSeq (p : Bytes → Option (Val × Bytes)) : Nat → Bytes → Option (List Val)
  | _, [] => some []
  | 0, _ :: _ => none
  | n + 1, b =>
    match p b with
    | some (v, r) => (decodeSeq p n r).map (v :: ·)
    | none => none

theorem decodeSeq_nil (p : Bytes → Option (Val × Bytes)) (n : Nat) : decodeSeq p n [] = some [] := by
  cases n <;> rfl

theorem decodeSeq_succ (p : Bytes → Option (Val × Bytes)) (n : Nat) (b : Bytes) (hb : b ≠ []) :
    decodeSeq p (n + 1) b =
      match p b with
      | some (v, r) => (decodeSeq p n r).map (v :: ·)
      | none => none := by
  cases b with
  | nil => exact absurd rfl hb
  | cons _ _ => rfl

theorem decodeSeq_encodeList (p : Bytes → Option (Val × Bytes)) (xs : List Val)
    (hp : ∀ x ∈ xs, ∀ rest, p (Val.encode x ++ rest) = some (x, rest)) :
    ∀ n, xs.length ≤ n → decodeSeq p n (Val.encodeList xs) = some xs := by
  induction xs with
  | nil =>
    intro n _
    exact decodeSeq_nil p n
  | cons x xs ih =>
    intro n hn
    cases n with
    | zero => simp at hn
    | succ n =>
      have hne : Val.encode x ++ Val.encodeList xs ≠ [] := by
        rw [Val.encode_eq, framed, List.cons_append]
        exact List.cons_ne_nil _ _
      rw [Val.encodeList_cons, decodeSeq_succ p n _ hne]
      simp only [hp x (by simp) (Val.encodeList xs),
        ih (fun y hy => hp y (by simp [hy])) n (by simp at hn; omega), Option.map_some]

theorem decodeSeq_exact (p : Bytes → Option (Val × Bytes))
    (hp : ∀ b v r, p b = some (v, r) → b = Val.encode v ++ r ∧ v.WF) :
    ∀ (n : Nat) (b : Bytes) (xs : List Val),
      decodeSeq p n b = some xs → b = Val.encodeList xs ∧ Val.WFList xs := by
  intro n
  induction n with
  | zero =>
    intro b xs h
    cases b with
    | nil =>
      rw [decodeSeq_nil] at h
      injection h with h
      subst h
      exact ⟨rfl, trivial⟩
    | cons _ _ => exact nomatch h
  | succ n ih =>
    intro b xs h
    cases b with
    | nil =>
      rw [decodeSeq_nil] at h
      injection h with h
      subst h
      exact ⟨rfl, trivial⟩
    | cons b0 b' =>
      simp only [decodeSeq] at h
      split at h
      · next v r hpb =>
        obtain ⟨xs', hxs', hx⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨hb, hv⟩ := hp _ _ _ hpb
        obtain ⟨hr, hwf⟩ := ih r xs' hxs'
        subst hx
        exact ⟨by rw [Val.encodeList_cons, hb, hr], ⟨hv, hwf⟩⟩
      · exact nomatch h

/-! ## Stage: one payload, by tag -/

/-- One frame's payload read for its tag, given the reader `dec` for the children. The
refusals are the Wire's: a wrong tag, a leading zero digit, a non-shortest UTF-8 sequence, a
short or long payload, an unconsumed byte inside a `pair` or `some`. -/
def decodeBody (dec : Bytes → Option (Val × Bytes)) (tag : UInt8) (payload : Bytes) : Option Val :=
  if tag = Tag.unit then (if payload = [] then some .unit else none)
  else if tag = Tag.bool then
    match payload with
    | [x] => if x = 0 then some (.bool false) else if x = 1 then some (.bool true) else none
    | _ => none
  else if tag = Tag.nat then
    (if payload.head? = some 0 then none else some (.nat (natOfDigits payload)))
  else if tag = Tag.string then (decodeString payload).map .str
  else if tag = Tag.bytes then some (.bytes payload)
  else if tag = Tag.list then (decodeSeq dec payload.length payload).map .list
  else if tag = Tag.pair then
    match dec payload with
    | some (a, r) =>
      match dec r with
      | some (b, []) => some (.pair a b)
      | _ => none
    | none => none
  else if tag = Tag.none then (if payload = [] then some .none else none)
  else if tag = Tag.some then
    match dec payload with
    | some (a, []) => some (.some a)
    | _ => none
  else if tag = Tag.ctor then
    match readFrame payload with
    | some (t, digits, r) =>
      if t = Tag.nat ∧ digits.head? ≠ some 0 then
        (decodeSeq dec r.length r).map (.ctor (natOfDigits digits))
      else none
    | none => none
  else if tag = Tag.ref then
    match payload with
    | k :: d => some (.ref k d)
    | [] => none
  else none

/-! The dispatch, one equation per tag: the tag comparisons are closed terms, so each is `rfl`,
and the proofs below never unfold the `Tag` constants. -/
section dispatch
variable (dec : Bytes → Option (Val × Bytes)) (payload : Bytes)

theorem decodeBody_unit :
    decodeBody dec Tag.unit payload = (if payload = [] then some .unit else none) := rfl

theorem decodeBody_bool :
    decodeBody dec Tag.bool payload =
      (match payload with
        | [x] => if x = 0 then some (.bool false) else if x = 1 then some (.bool true) else none
        | _ => none) := rfl

theorem decodeBody_nat :
    decodeBody dec Tag.nat payload =
      (if payload.head? = some 0 then none else some (.nat (natOfDigits payload))) := rfl

theorem decodeBody_string :
    decodeBody dec Tag.string payload = (decodeString payload).map .str := rfl

theorem decodeBody_bytes : decodeBody dec Tag.bytes payload = some (.bytes payload) := rfl

theorem decodeBody_list :
    decodeBody dec Tag.list payload = (decodeSeq dec payload.length payload).map .list := rfl

theorem decodeBody_pair :
    decodeBody dec Tag.pair payload =
      (match dec payload with
        | some (a, r) =>
          match dec r with
          | some (b, []) => some (.pair a b)
          | _ => none
        | none => none) := rfl

theorem decodeBody_none :
    decodeBody dec Tag.none payload = (if payload = [] then some .none else none) := rfl

theorem decodeBody_some :
    decodeBody dec Tag.some payload =
      (match dec payload with
        | some (a, []) => some (.some a)
        | _ => none) := rfl

theorem decodeBody_ctor :
    decodeBody dec Tag.ctor payload =
      (match readFrame payload with
        | some (t, digits, r) =>
          if t = Tag.nat ∧ digits.head? ≠ some 0 then
            (decodeSeq dec r.length r).map (.ctor (natOfDigits digits))
          else none
        | none => none) := rfl

theorem decodeBody_ref :
    decodeBody dec Tag.ref payload =
      (match payload with
        | k :: d => some (.ref k d)
        | [] => none) := rfl

end dispatch

theorem decodeBody_encode (dec : Bytes → Option (Val × Bytes)) (v : Val) (hwf : v.WF)
    (hdec : ∀ c ∈ v.children, ∀ rest, dec (Val.encode c ++ rest) = some (c, rest)) :
    decodeBody dec v.tag v.payload = some v := by
  cases v with
  | unit =>
    show decodeBody dec Tag.unit [] = some .unit
    rw [decodeBody_unit, if_pos rfl]
  | bool b =>
    cases b
    · show decodeBody dec Tag.bool [0] = some (.bool false)
      rw [decodeBody_bool]
      rfl
    · show decodeBody dec Tag.bool [1] = some (.bool true)
      rw [decodeBody_bool]
      rfl
  | nat n =>
    show decodeBody dec Tag.nat (natBytes n) = some (.nat n)
    rw [decodeBody_nat, if_neg (natBytes_head n), natOfDigits_natBytes]
  | str s =>
    show decodeBody dec Tag.string s.toUTF8.data.toList = some (.str s)
    rw [decodeBody_string, decodeString_toUTF8, Option.map_some]
  | bytes bs => rfl
  | list xs =>
    show decodeBody dec Tag.list (Val.encodeList xs) = some (.list xs)
    have hdec' : ∀ x ∈ xs, ∀ rest, dec (Val.encode x ++ rest) = some (x, rest) :=
      fun x hx => hdec x hx
    rw [decodeBody_list, decodeSeq_encodeList dec xs hdec' _ (Val.length_le_encodeList xs),
      Option.map_some]
  | pair a b =>
    show decodeBody dec Tag.pair (Val.encode a ++ Val.encode b) = some (.pair a b)
    have ha := hdec a (by simp [Val.children]) (Val.encode b)
    have hb := hdec b (by simp [Val.children]) []
    rw [List.append_nil] at hb
    rw [decodeBody_pair]
    simp only [ha, hb]
  | none =>
    show decodeBody dec Tag.none [] = some .none
    rw [decodeBody_none, if_pos rfl]
  | some a =>
    show decodeBody dec Tag.some (Val.encode a) = some (.some a)
    have ha := hdec a (by simp [Val.children]) []
    rw [List.append_nil] at ha
    rw [decodeBody_some]
    simp only [ha]
  | ctor i args =>
    show decodeBody dec Tag.ctor (framed Tag.nat (natBytes i) ++ Val.encodeList args) =
      some (.ctor i args)
    have hframe := readFrame_append Tag.nat (natBytes i) (Val.encodeList args) hwf.1
    have hdec' : ∀ x ∈ args, ∀ rest, dec (Val.encode x ++ rest) = some (x, rest) :=
      fun x hx => hdec x hx
    have hseq := decodeSeq_encodeList dec args hdec' _ (Val.length_le_encodeList args)
    rw [decodeBody_ctor, hframe]
    show (if Tag.nat = Tag.nat ∧ (natBytes i).head? ≠ some 0 then
        (decodeSeq dec (Val.encodeList args).length (Val.encodeList args)).map
          (Val.ctor (natOfDigits (natBytes i)))
      else none) = some (Val.ctor i args)
    rw [if_pos (show Tag.nat = Tag.nat ∧ (natBytes i).head? ≠ some 0 from ⟨rfl, natBytes_head i⟩),
      hseq, natOfDigits_natBytes, Option.map_some]
  | ref k d => rfl

/-- Any other tag byte is refused. -/
theorem decodeBody_unknown (dec : Bytes → Option (Val × Bytes)) (tag : UInt8) (payload : Bytes)
    (h1 : tag ≠ Tag.unit) (h2 : tag ≠ Tag.bool) (h3 : tag ≠ Tag.nat) (h4 : tag ≠ Tag.string)
    (h5 : tag ≠ Tag.bytes) (h6 : tag ≠ Tag.list) (h7 : tag ≠ Tag.pair) (h8 : tag ≠ Tag.none)
    (h9 : tag ≠ Tag.some) (h10 : tag ≠ Tag.ctor) (h11 : tag ≠ Tag.ref) :
    decodeBody dec tag payload = none := by
  unfold decodeBody
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6, if_neg h7, if_neg h8,
    if_neg h9, if_neg h10, if_neg h11]

theorem decodeBody_exact (dec : Bytes → Option (Val × Bytes))
    (hdec : ∀ b v r, dec b = some (v, r) → b = Val.encode v ++ r ∧ v.WF)
    {tag : UInt8} {payload : Bytes} {v : Val} (hlen : payload.length < 2 ^ 64)
    (h : decodeBody dec tag payload = some v) :
    tag = v.tag ∧ payload = v.payload ∧ v.WF := by
  by_cases h1 : tag = Tag.unit
  · rw [h1, decodeBody_unit] at h
    split at h
    · next hp =>
      injection h with h
      subst h
      exact ⟨h1, hp, trivial⟩
    · exact nomatch h
  by_cases h2 : tag = Tag.bool
  · rw [h2, decodeBody_bool] at h
    match payload, h with
    | [x], h =>
      have h' : (if x = 0 then some (Val.bool false)
          else if x = 1 then some (Val.bool true) else none) = some v := h
      by_cases hx0 : x = 0
      · rw [if_pos hx0] at h'
        injection h' with h'
        subst h' hx0
        exact ⟨h2, rfl, trivial⟩
      · rw [if_neg hx0] at h'
        by_cases hx1 : x = 1
        · rw [if_pos hx1] at h'
          injection h' with h'
          subst h' hx1
          exact ⟨h2, rfl, trivial⟩
        · rw [if_neg hx1] at h'
          exact nomatch h'
    | [], h => exact nomatch h
    | _ :: _ :: _, h => exact nomatch h
  by_cases h3 : tag = Tag.nat
  · rw [h3, decodeBody_nat] at h
    split at h
    · exact nomatch h
    · next hhead =>
      injection h with h
      subst h
      refine ⟨h3, (natBytes_natOfDigits payload hhead).symm, ?_⟩
      show (natBytes (natOfDigits payload)).length < 2 ^ 64
      rw [natBytes_natOfDigits payload hhead]
      exact hlen
  by_cases h4 : tag = Tag.string
  · rw [h4, decodeBody_string] at h
    obtain ⟨s, hs, hsv⟩ := Option.map_eq_some_iff.mp h
    subst hsv
    have hb := decodeString_exact hs
    refine ⟨h4, hb.symm, ?_⟩
    show s.toUTF8.data.toList.length < 2 ^ 64
    rw [String.toUTF8_eq_toByteArray, hb]
    exact hlen
  by_cases h5 : tag = Tag.bytes
  · rw [h5, decodeBody_bytes] at h
    injection h with h
    subst h
    exact ⟨h5, rfl, hlen⟩
  by_cases h6 : tag = Tag.list
  · rw [h6, decodeBody_list] at h
    obtain ⟨xs, hxs, hxv⟩ := Option.map_eq_some_iff.mp h
    subst hxv
    obtain ⟨hb, hwf⟩ := decodeSeq_exact dec hdec _ _ _ hxs
    refine ⟨h6, hb, ?_⟩
    show (Val.encodeList xs).length < 2 ^ 64 ∧ Val.WFList xs
    rw [← hb]
    exact ⟨hlen, hwf⟩
  by_cases h7 : tag = Tag.pair
  · rw [h7, decodeBody_pair] at h
    split at h
    · next a r ha =>
      split at h
      · next b hb =>
        injection h with h
        subst h
        obtain ⟨hpa, hwa⟩ := hdec _ _ _ ha
        obtain ⟨hrb, hwb⟩ := hdec _ _ _ hb
        rw [List.append_nil] at hrb
        subst hrb
        refine ⟨h7, hpa, ?_⟩
        show (Val.encode a ++ Val.encode b).length < 2 ^ 64 ∧ Val.WF a ∧ Val.WF b
        rw [← hpa]
        exact ⟨hlen, hwa, hwb⟩
      · exact nomatch h
    · exact nomatch h
  by_cases h8 : tag = Tag.none
  · rw [h8, decodeBody_none] at h
    split at h
    · next hp =>
      injection h with h
      subst h
      exact ⟨h8, hp, trivial⟩
    · exact nomatch h
  by_cases h9 : tag = Tag.some
  · rw [h9, decodeBody_some] at h
    split at h
    · next a ha =>
      injection h with h
      subst h
      obtain ⟨hpa, hwa⟩ := hdec _ _ _ ha
      rw [List.append_nil] at hpa
      refine ⟨h9, hpa, ?_⟩
      show (Val.encode a).length < 2 ^ 64 ∧ Val.WF a
      rw [← hpa]
      exact ⟨hlen, hwa⟩
    · exact nomatch h
  by_cases h10 : tag = Tag.ctor
  · rw [h10, decodeBody_ctor] at h
    split at h
    · next t digits r hframe =>
      split at h
      · next hguard =>
        obtain ⟨args, hargs, hav⟩ := Option.map_eq_some_iff.mp h
        subst hav
        obtain ⟨hpb, hdl⟩ := readFrame_exact hframe
        obtain ⟨hr, hwf⟩ := decodeSeq_exact dec hdec _ _ _ hargs
        obtain ⟨ht, hhead⟩ := hguard
        subst ht
        have hdigits : natBytes (natOfDigits digits) = digits :=
          natBytes_natOfDigits digits hhead
        have hpay : payload =
            framed Tag.nat (natBytes (natOfDigits digits)) ++ Val.encodeList args := by
          rw [hpb, hr, hdigits]
        refine ⟨h10, hpay, ?_⟩
        show (natBytes (natOfDigits digits)).length < 2 ^ 64 ∧
          (framed Tag.nat (natBytes (natOfDigits digits)) ++ Val.encodeList args).length < 2 ^ 64 ∧
          Val.WFList args
        rw [← hpay, hdigits]
        exact ⟨hdl, hlen, hwf⟩
      · exact nomatch h
    · exact nomatch h
  by_cases h11 : tag = Tag.ref
  · rw [h11, decodeBody_ref] at h
    split at h
    · next k d =>
      injection h with h
      subst h
      exact ⟨h11, rfl, hlen⟩
    · exact nomatch h
  rw [decodeBody_unknown dec tag payload h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11] at h
  exact nomatch h

/-! ## The knot: fuel -/

/-- One value off the front of a byte string, with fuel: the value and the rest. -/
def decodeOne : Nat → Bytes → Option (Val × Bytes)
  | 0, _ => none
  | fuel + 1, b =>
    match readFrame b with
    | some (tag, payload, rest) => (decodeBody (decodeOne fuel) tag payload).map (·, rest)
    | none => none

/-- Forward correctness under fuel: a well-formed value's frame, in front of anything, reads
back as the value and the rest, once the fuel exceeds the frame's length. -/
theorem decodeOne_encode : ∀ (fuel : Nat) (v : Val) (rest : Bytes), v.WF →
    (Val.encode v).length < fuel → decodeOne fuel (Val.encode v ++ rest) = some (v, rest) := by
  intro fuel
  induction fuel with
  | zero =>
    intro v rest _ h
    exact absurd h (Nat.not_lt_zero _)
  | succ f ih =>
    intro v rest hwf hlen
    have he : Val.encode v ++ rest = framed v.tag v.payload ++ rest := by rw [Val.encode_eq]
    rw [he]
    simp only [decodeOne, readFrame_append v.tag v.payload rest (Val.WF_payload_lt hwf)]
    rw [decodeBody_encode (decodeOne f) v hwf ?_, Option.map_some]
    intro c hc rest'
    apply ih c rest' (Val.WF_child hwf hc)
    have := Val.length_encode_child hc
    omega

/-- Image exactness under fuel: whatever the decoder answers, the input was that value's frame
followed by the rest, and the value is well-formed. -/
theorem decodeOne_exact : ∀ (fuel : Nat) (b : Bytes) (v : Val) (rest : Bytes),
    decodeOne fuel b = some (v, rest) → b = Val.encode v ++ rest ∧ v.WF := by
  intro fuel
  induction fuel with
  | zero =>
    intro b v rest h
    exact nomatch h
  | succ f ih =>
    intro b v rest h
    simp only [decodeOne] at h
    split at h
    · next tag payload rest' hframe =>
      obtain ⟨v', hv', hvr⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hvr
      obtain ⟨rfl, rfl⟩ := hvr
      obtain ⟨hb, hlen⟩ := readFrame_exact hframe
      obtain ⟨htag, hpay, hwf⟩ := decodeBody_exact (decodeOne f) (fun b v r hh => ih b v r hh) hlen hv'
      refine ⟨?_, hwf⟩
      rw [hb, Val.encode_eq, htag, hpay]
    · exact nomatch h

namespace Val

/-- The exact decoder: the whole byte string is one value and nothing else. Fuel is the byte
length plus one (`length_encode_child`). -/
def decode (b : Bytes) : Option Val :=
  match decodeOne (b.length + 1) b with
  | Option.some (v, []) => Option.some v
  | _ => Option.none

theorem decode_encode (v : Val) (h : v.WF) : decode (Val.encode v) = Option.some v := by
  have hd := decodeOne_encode ((Val.encode v).length + 1) v [] h (Nat.lt_succ_self _)
  rw [List.append_nil] at hd
  simp only [decode, hd]

theorem decode_exact {b : Bytes} {v : Val} (h : decode b = Option.some v) :
    b = Val.encode v ∧ v.WF := by
  unfold decode at h
  split at h
  · next v' hv' =>
    injection h with h
    subst h
    obtain ⟨hb, hwf⟩ := decodeOne_exact _ _ _ _ hv'
    rw [List.append_nil] at hb
    exact ⟨hb, hwf⟩
  · exact nomatch h

/-- One byte string per well-formed value: injectivity is a corollary of the round trip. -/
theorem encode_injective {a b : Val} (ha : a.WF) (hb : b.WF) (h : Val.encode a = Val.encode b) :
    a = b := by
  have h1 := decode_encode a ha
  rw [h, decode_encode b hb] at h1
  injection h1 with h1
  exact h1.symm

/-- Two values whose encodings differ are different: the direction that needs no law. -/
theorem ne_of_encode_ne {a b : Val} (h : Val.encode a ≠ Val.encode b) : a ≠ b :=
  fun e => h (congrArg Val.encode e)

end Val

/-! ## Decidable equality -/

namespace Val

mutual
def beq : Val → Val → Bool
  | .unit, .unit => true
  | .bool a, .bool b => a == b
  | .nat a, .nat b => decide (a = b)
  | .str a, .str b => decide (a = b)
  | .bytes a, .bytes b => decide (a = b)
  | .list a, .list b => beqList a b
  | .pair a1 a2, .pair b1 b2 => beq a1 b1 && beq a2 b2
  | .none, .none => true
  | .some a, .some b => beq a b
  | .ctor i a, .ctor j b => decide (i = j) && beqList a b
  | .ref k d, .ref k' d' => decide (k = k') && decide (d = d')
  | _, _ => false
def beqList : List Val → List Val → Bool
  | [], [] => true
  | a :: as, b :: bs => beq a b && beqList as bs
  | _, _ => false
end

mutual
theorem beq_iff (a b : Val) : beq a b = true ↔ a = b := by
  cases a
  case pair a1 a2 =>
    cases b <;> simp [beq, beq_iff a1, beq_iff a2]
  case some a =>
    cases b <;> simp [beq, beq_iff a]
  case list xs =>
    cases b <;> simp [beq, beqList_iff xs]
  case ctor i args =>
    cases b <;> simp [beq, beqList_iff args]
  all_goals cases b <;> simp [beq]
termination_by structural a
theorem beqList_iff (as bs : List Val) : beqList as bs = true ↔ as = bs := by
  match as, bs with
  | [], [] => simp [beqList]
  | [], _ :: _ => simp [beqList]
  | _ :: _, [] => simp [beqList]
  | a :: as, b :: bs => simp [beqList, beq_iff a b, beqList_iff as bs]
termination_by structural as
end

instance instDecidableEq : DecidableEq Val := fun a b => decidable_of_iff _ (beq_iff a b)

end Val

/-! ## Byte identity and refusals, guarded

The primitives are `Test/Store/StoreContract.lean:39-47`; the entry payload is the facts
note's §6 (74 bytes, `0a …41 02 …00 03 …06 "Effect" 03 …03 "gen" 0a …09 02 …00 02 …02 07 9b`). -/

open Val in
#guard encode .unit = [9, 0, 0, 0, 0, 0, 0, 0, 0]
open Val in
#guard encode (.bool true) = [1, 0, 0, 0, 0, 0, 0, 0, 1, 1]
open Val in
#guard encode (.nat 0) = [2, 0, 0, 0, 0, 0, 0, 0, 0]
open Val in
#guard encode (.nat 256) = [2, 0, 0, 0, 0, 0, 0, 0, 2, 1, 0]
open Val in
#guard encode (.str "A") = [3, 0, 0, 0, 0, 0, 0, 0, 1, 65]
open Val in
#guard encode (.str "é") = [3, 0, 0, 0, 0, 0, 0, 0, 2, 0xc3, 0xa9]
open Val in
#guard encode (.list []) = [4, 0, 0, 0, 0, 0, 0, 0, 0]
open Val in
#guard (encode (.list [.str "a", .str "b"])).length = 9 + 2 * (9 + 1)
#guard (framed 7 [1, 2, 3]).length = 12
open Val in
#guard (encode (.ref 2 (List.replicate 32 0))).length = 42

/-- The census entry of the facts note §6, as a value tree. -/
def sampleEntry : Val :=
  .ctor 0 [.str "Effect", .str "gen", .ctor 0 [], .nat 1947]

#guard (Val.encode sampleEntry).length = 74
#guard (Val.encode sampleEntry).take 10 = [0x0a, 0, 0, 0, 0, 0, 0, 0, 0x41, 0x02]
#guard (Val.encode sampleEntry).drop 63 = [0x02, 0, 0, 0, 0, 0, 0, 0, 0x02, 0x07, 0x9b]
#guard Val.decode (Val.encode sampleEntry) = some sampleEntry
#guard Val.decode (Val.encode (.pair (.some (.bool false)) (.list [.unit, .none]))) =
  some (.pair (.some (.bool false)) (.list [.unit, .none]))
-- A byte appended, a byte dropped, a leading-zero digit, a non-shortest UTF-8 sequence, a wrong
-- tag, a `pair` with three frames, a bad boolean, a payload under `unit`, an empty `ref`: refused.
#guard Val.decode (Val.encode sampleEntry ++ [0]) = none
#guard Val.decode (Val.encode sampleEntry).dropLast = none
#guard Val.decode (framed Tag.nat [0, 17]) = none
#guard Val.decode (framed Tag.string [0xc0, 0x80]) = none
#guard Val.decode (framed 12 []) = none
#guard Val.decode (framed Tag.pair (Val.encode .unit ++ Val.encode .unit ++ Val.encode .unit)) = none
#guard Val.decode (framed Tag.bool [2]) = none
#guard Val.decode (framed Tag.unit [0]) = none
#guard Val.decode (framed Tag.ref []) = none
#guard Val.decode (framed Tag.ctor (framed Tag.nat [0, 1])) = none

/-! ## Receipts -/

#print axioms framed
#print axioms framed_length
#print axioms framed_inj
#print axioms Val.encode
#print axioms Val.encodeList_eq_flatten
#print axioms Val.encode_eq
#print axioms Val.ind
#print axioms Val.WF
#print axioms Val.wf
#print axioms Val.wf_iff
#print axioms Val.decWF
#print axioms Val.WF_payload_lt
#print axioms Val.WF_child
#print axioms Val.length_encode_child
#print axioms Val.length_le_encodeList
#print axioms readFrame
#print axioms readFrame_append
#print axioms readFrame_exact
#print axioms decodeSeq
#print axioms decodeSeq_encodeList
#print axioms decodeSeq_exact
#print axioms decodeBody
#print axioms decodeBody_ctor
#print axioms decodeBody_unknown
#print axioms decodeBody_encode
#print axioms decodeBody_exact
#print axioms decodeOne
#print axioms decodeOne_encode
#print axioms decodeOne_exact
#print axioms Val.decode
#print axioms Val.decode_encode
#print axioms Val.decode_exact
#print axioms Val.encode_injective
#print axioms Val.ne_of_encode_ne
#print axioms Val.beq
#print axioms Val.beq_iff
#print axioms Val.instDecidableEq

end Effect4.Store
