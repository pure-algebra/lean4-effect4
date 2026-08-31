import Effects.Cas.Node
import Effects.Merkle.Decoder
import Effects.Wire.Nat32

/-!
# The proof-document codecs

Byte realizations for the proof plane, with the control-codec
discipline: canonical encodings, CLOSED decoders that reject
truncation, malformed tags, and trailing content, and exactness — a
successful decode's input IS the canonical encoding of its result.

Two documents. The inclusion-opening document carries the index, the
total chunk count, the length-prefixed leaf bytes, and the sibling
addresses root-side first — sides are never encoded; the verifier
derives them from the index and the count, per the
encoding-malleability boundary. The range-stream document carries a
twelve-byte header (total, then the requested range) followed by
items whose alphabet is EXACTLY the verified-streaming decoder's
input language: a bare skip tag (a skipped subtree's address was
bound by its parent — carrying one would be a side channel), a
length-prefixed chunk, or a parent's two child addresses.

Addresses are the full-width 32-byte kind; the width invariant rides
the subtype through decode, so no theorem restates it.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes Addr32)
open Effects.Wire

private theorem take_app {α : Type _} (xs ys : List α) :
    (xs ++ ys).take xs.length = xs := by
  simp

private theorem drop_app {α : Type _} (xs ys : List α) :
    (xs ++ ys).drop xs.length = ys := by
  simp

private theorem take_app32 (v ys : List UInt8) (hv : v.length = 32) :
    (v ++ ys).take 32 = v := by
  rw [← hv]
  exact take_app v ys

private theorem drop_app32 (v ys : List UInt8) (hv : v.length = 32) :
    (v ++ ys).drop 32 = ys := by
  rw [← hv]
  exact drop_app v ys

/-! ## Address lists -/

/-- Read a whole byte string as 32-byte addresses, exactly. -/
def readAddrs (bs : List UInt8) : Option (List Addr32) :=
  if bs.isEmpty then some []
  else if h : 32 ≤ bs.length then
    (readAddrs (bs.drop 32)).map
      (⟨bs.take 32, by simp only [List.length_take]; omega⟩ :: ·)
  else none
termination_by bs.length
decreasing_by simp only [List.length_drop]; omega

theorem readAddrs_nil : readAddrs [] = some [] := by
  rw [readAddrs.eq_def]
  simp

theorem readAddrs_cons (bs : List UInt8) (hne : ¬ bs.isEmpty)
    (h : 32 ≤ bs.length) :
    readAddrs bs =
      (readAddrs (bs.drop 32)).map
        (⟨bs.take 32, by simp only [List.length_take]; omega⟩ :: ·) := by
  conv => lhs; rw [readAddrs.eq_def]
  rw [if_neg (by simpa using hne), dif_pos h]

theorem readAddrs_short (bs : List UInt8) (hne : ¬ bs.isEmpty)
    (h : ¬ 32 ≤ bs.length) : readAddrs bs = none := by
  conv => lhs; rw [readAddrs.eq_def]
  rw [if_neg (by simpa using hne), dif_neg h]

/-- Completeness: a flattened address list reads back exactly. -/
theorem readAddrs_flat : ∀ (as : List Addr32),
    readAddrs (as.flatMap (·.val)) = some as
  | [] => by simpa using readAddrs_nil
  | a :: as => by
    have hlen : a.val.length = 32 := a.property
    have happ : (a :: as).flatMap (·.val) =
        a.val ++ as.flatMap (·.val) := by simp
    rw [happ]
    have hne : ¬ (a.val ++ as.flatMap (·.val)).isEmpty := by
      simp only [List.isEmpty_iff]
      intro hnil
      have := congrArg List.length hnil
      simp only [List.length_append, hlen, List.length_nil] at this
      omega
    have h32 : 32 ≤ (a.val ++ as.flatMap (·.val)).length := by
      simp only [List.length_append]
      omega
    rw [readAddrs_cons _ hne h32]
    have htake : (a.val ++ as.flatMap (·.val)).take 32 = a.val :=
      take_app32 a.val _ hlen
    have hdrop : (a.val ++ as.flatMap (·.val)).drop 32 =
        as.flatMap (·.val) :=
      drop_app32 a.val _ hlen
    rw [hdrop, readAddrs_flat as]
    simp only [Option.map_some, Option.some.injEq, List.cons.injEq,
      and_true]
    exact Subtype.ext htake

/-- Exactness: a successful address read's input is exactly the
flattened result. -/
theorem readAddrs_some :
    ∀ (bs : List UInt8) (as : List Addr32), readAddrs bs = some as →
      bs = as.flatMap (·.val) := by
  intro bs
  induction hn : bs.length using Nat.strongRecOn generalizing bs with
  | ind n ih =>
  intro as hread
  subst hn
  by_cases hne : bs.isEmpty
  · rw [List.isEmpty_iff.mp hne] at hread ⊢
    rw [readAddrs_nil] at hread
    injection hread with hread
    rw [← hread]
    simp
  · have hpos : 0 < bs.length := by
      cases bs with
      | nil => simp at hne
      | cons _ _ => simp
    by_cases h32 : 32 ≤ bs.length
    · rw [readAddrs_cons bs hne h32] at hread
      obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp hread
      have hdlen : (bs.drop 32).length = bs.length - 32 := by
        simp only [List.length_drop]
      have htl := ih (bs.length - 32) (by omega) (bs.drop 32) hdlen
        tail htail
      rw [← hcons]
      simp only [List.flatMap_cons]
      rw [← htl]
      exact (List.take_append_drop 32 bs).symm
    · rw [readAddrs_short bs hne h32] at hread
      exact nomatch hread

/-! ## The inclusion-opening document -/

/-- The opening document: index, total, leaf bytes, and the sibling
addresses root-side first. Sides are never part of the document. -/
structure OpeningDoc where
  index : Nat
  total : Nat
  leaf : Bytes
  sibs : List Addr32
  deriving DecidableEq

/-- The canonical opening encoding. -/
def encodeOpening (d : OpeningDoc) : List UInt8 :=
  nat32 d.index ++ nat32 d.total ++ nat32 d.leaf.length ++ d.leaf ++
    d.sibs.flatMap (·.val)

/-- The closed opening decoder. -/
def decodeOpening? (bytes : List UInt8) : Option OpeningDoc :=
  match readNat32 bytes with
  | none => none
  | some (index, r1) =>
    match readNat32 r1 with
    | none => none
    | some (total, r2) =>
      match readNat32 r2 with
      | none => none
      | some (len, r3) =>
        if len ≤ r3.length then
          match readAddrs (r3.drop len) with
          | none => none
          | some sibs => some ⟨index, total, r3.take len, sibs⟩
        else none

/-- Forward correctness on representable openings. -/
theorem decodeOpening_encodeOpening (d : OpeningDoc)
    (hi : d.index < 4294967296) (ht : d.total < 4294967296)
    (hl : d.leaf.length < 4294967296) :
    decodeOpening? (encodeOpening d) = some d := by
  unfold decodeOpening? encodeOpening
  simp only [List.append_assoc]
  rw [readNat32_nat32 d.index hi]
  dsimp only
  rw [readNat32_nat32 d.total ht]
  dsimp only
  rw [readNat32_nat32 d.leaf.length hl]
  dsimp only
  rw [if_pos (by simp only [List.length_append]; omega)]
  rw [show (d.leaf ++ d.sibs.flatMap (·.val)).drop d.leaf.length =
      d.sibs.flatMap (·.val) from drop_app _ _]
  rw [readAddrs_flat d.sibs]
  rw [show (d.leaf ++ d.sibs.flatMap (·.val)).take d.leaf.length =
      d.leaf from take_app _ _]

/-- Exactness: a successful decode's input IS the canonical encoding
of its result, with the three fields representable. -/
theorem decodeOpening_exact (bytes : List UInt8) (d : OpeningDoc)
    (h : decodeOpening? bytes = some d) :
    bytes = encodeOpening d ∧ d.index < 4294967296 ∧
      d.total < 4294967296 ∧ d.leaf.length < 4294967296 := by
  simp only [decodeOpening?] at h
  split at h
  · exact nomatch h
  · rename_i index r1 hr1
    split at h
    · exact nomatch h
    · rename_i total r2 hr2
      split at h
      · exact nomatch h
      · rename_i len r3 hr3
        split at h
        · rename_i hlen
          split at h
          · exact nomatch h
          · rename_i sibs hsibs
            injection h with h
            obtain ⟨hb1, hlt1⟩ := readNat32_some bytes index r1 hr1
            obtain ⟨hb2, hlt2⟩ := readNat32_some r1 total r2 hr2
            obtain ⟨hb3, hlt3⟩ := readNat32_some r2 len r3 hr3
            have hflat := readAddrs_some (r3.drop len) sibs hsibs
            subst h
            have hleaf_len : (r3.take len).length = len := by
              simp only [List.length_take]
              omega
            refine ⟨?_, hlt1, hlt2, by rw [hleaf_len]; exact hlt3⟩
            simp only [encodeOpening]
            rw [hb1, hb2, hb3, hleaf_len]
            simp only [List.append_assoc]
            congr 1
            congr 1
            congr 1
            rw [← hflat]
            exact (List.take_append_drop len r3).symm
        · exact nomatch h

/-! ## The range-stream document -/

/-- The stream header: the declared total and the requested range,
echoed so a client fails closed on any disagreement. -/
structure StreamHeader where
  total : Nat
  lo : Nat
  hi : Nat
  deriving DecidableEq

/-- One item's canonical encoding: the decoder's input alphabet with
one tag byte each. A skip carries nothing — the skipped subtree's
address was bound by its parent. -/
def encodeItem : DInput Addr32 → List UInt8
  | .skipNode => [0]
  | .chunkNode bytes => 1 :: (nat32 bytes.length ++ bytes)
  | .parentNode l r => 2 :: (l.val ++ r.val)

/-- Representability of one item: only chunk lengths are bounded —
addresses carry their width in the type. -/
def itemWf : DInput Addr32 → Prop
  | .chunkNode bytes => bytes.length < 4294967296
  | _ => True

instance (i : DInput Addr32) : Decidable (itemWf i) := by
  cases i <;> simp only [itemWf] <;> infer_instance

/-- The closed item reader: the whole byte string as items, exactly. -/
def readItems (bs : List UInt8) : Option (List (DInput Addr32)) :=
  match bs with
  | [] => some []
  | t :: rest =>
    if t = 0 then (readItems rest).map (.skipNode :: ·)
    else if t = 1 then
      match hr : readNat32 rest with
      | none => none
      | some (len, r) =>
        if len ≤ r.length then
          (readItems (r.drop len)).map (.chunkNode (r.take len) :: ·)
        else none
    else if t = 2 then
      if h : 64 ≤ rest.length then
        (readItems (rest.drop 64)).map
          (.parentNode ⟨rest.take 32, by simp only [List.length_take]; omega⟩
            ⟨(rest.drop 32).take 32, by
              simp only [List.length_take, List.length_drop]; omega⟩ :: ·)
      else none
    else none
termination_by bs.length
decreasing_by
  · simp only [List.length_cons]
    omega
  · have hrest := (readNat32_some rest len r hr).1
    have hrlen : rest.length = 4 + r.length := by
      rw [hrest]
      simp only [nat32, List.length_append, List.length_cons,
        List.length_nil]
    simp only [List.length_drop, List.length_cons]
    omega
  · simp only [List.length_drop, List.length_cons]
    omega

/-- Completeness: a flattened well-formed item list reads back
exactly. -/
theorem readItems_flat : ∀ (items : List (DInput Addr32)),
    (∀ i ∈ items, itemWf i) →
    readItems (items.flatMap encodeItem) = some items
  | [], _ => by simp [readItems]
  | .skipNode :: items, hwf => by
    have htl := readItems_flat items (fun i hi => hwf i (by simp [hi]))
    simp only [List.flatMap_cons, encodeItem, List.cons_append,
      List.nil_append]
    rw [readItems.eq_def]
    dsimp only
    rw [if_pos rfl, htl]
    rfl
  | .chunkNode bytes :: items, hwf => by
    have hb : bytes.length < 4294967296 := hwf (.chunkNode bytes) (by simp)
    have htl := readItems_flat items (fun i hi => hwf i (by simp [hi]))
    show readItems ((1 :: (nat32 bytes.length ++ bytes)) ++
      items.flatMap encodeItem) = _
    rw [show (1 :: (nat32 bytes.length ++ bytes)) ++
        items.flatMap encodeItem =
        1 :: (nat32 bytes.length ++ (bytes ++ items.flatMap encodeItem))
      from by simp]
    rw [readItems.eq_def]
    dsimp only
    rw [if_neg (by decide), if_pos rfl]
    rw [readNat32_nat32 bytes.length hb]
    dsimp only
    rw [if_pos (by simp only [List.length_append]; omega)]
    rw [show (bytes ++ items.flatMap encodeItem).drop bytes.length =
      items.flatMap encodeItem from drop_app _ _]
    rw [htl]
    rw [show (bytes ++ items.flatMap encodeItem).take bytes.length =
      bytes from take_app _ _]
    rfl
  | .parentNode l r :: items, hwf => by
    have htl := readItems_flat items (fun i hi => hwf i (by simp [hi]))
    show readItems ((2 :: (l.val ++ r.val)) ++ items.flatMap encodeItem) = _
    rw [show (2 :: (l.val ++ r.val)) ++ items.flatMap encodeItem =
        2 :: (l.val ++ (r.val ++ items.flatMap encodeItem)) from by simp]
    rw [readItems.eq_def]
    dsimp only
    rw [if_neg (by decide), if_neg (by decide), if_pos rfl]
    have hdrop32 : (l.val ++ (r.val ++ items.flatMap encodeItem)).drop 32 =
        r.val ++ items.flatMap encodeItem :=
      drop_app32 l.val _ l.property
    have htake1 : (l.val ++ (r.val ++ items.flatMap encodeItem)).take 32 =
        l.val :=
      take_app32 l.val _ l.property
    have htake2 : ((l.val ++ (r.val ++ items.flatMap encodeItem)).drop
        32).take 32 = r.val := by
      rw [hdrop32]
      exact take_app32 r.val _ r.property
    have hdrop64 : (l.val ++ (r.val ++ items.flatMap encodeItem)).drop 64 =
        items.flatMap encodeItem := by
      rw [show (64 : Nat) = 32 + 32 from rfl, ← List.drop_drop, hdrop32]
      exact drop_app32 r.val _ r.property
    rw [dif_pos (by
      simp only [List.length_append]
      omega)]
    rw [hdrop64, htl]
    simp only [Option.map_some, Option.some.injEq, List.cons.injEq,
      DInput.parentNode.injEq, and_true]
    exact ⟨Subtype.ext htake1, Subtype.ext htake2⟩

/-- Exactness: a successful item read's input is exactly the flattened
result, every item well-formed. -/
theorem readItems_some :
    ∀ (bs : List UInt8) (items : List (DInput Addr32)),
      readItems bs = some items →
      bs = items.flatMap encodeItem ∧ ∀ i ∈ items, itemWf i := by
  intro bs
  induction hn : bs.length using Nat.strongRecOn generalizing bs with
  | ind n ih =>
  intro items hread
  subst hn
  cases bs with
  | nil =>
    rw [readItems.eq_def] at hread
    dsimp only at hread
    injection hread with hread
    rw [← hread]
    exact ⟨rfl, by simp⟩
  | cons t rest =>
    rw [readItems.eq_def] at hread
    dsimp only at hread
    by_cases h0 : t = 0
    · rw [if_pos h0] at hread
      obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp hread
      obtain ⟨hb, hwf⟩ := ih rest.length (by simp) rest rfl tail htail
      subst h0
      rw [← hcons]
      refine ⟨?_, ?_⟩
      · simp only [List.flatMap_cons, encodeItem, List.cons_append,
          List.nil_append, List.cons.injEq, true_and]
        exact hb
      · intro i hi
        rcases List.mem_cons.mp hi with hi | hi
        · rw [hi]; trivial
        · exact hwf i hi
    · rw [if_neg h0] at hread
      by_cases h1 : t = 1
      · rw [if_pos h1] at hread
        split at hread
        · exact nomatch hread
        · rename_i len r hr
          split at hread
          · rename_i hlen
            obtain ⟨tail, htail, hcons⟩ :=
              Option.map_eq_some_iff.mp hread
            obtain ⟨hrest, hlt⟩ := readNat32_some rest len r hr
            have hrl : rest.length = 4 + r.length := by
              rw [hrest]
              simp only [nat32, List.length_append, List.length_cons,
                List.length_nil]
            obtain ⟨hb, hwf⟩ := ih (r.drop len).length (by
                simp only [List.length_drop, List.length_cons]
                omega)
              (r.drop len) rfl tail htail
            subst h1
            rw [← hcons]
            have htk : (r.take len).length = len := by
              simp only [List.length_take]
              omega
            refine ⟨?_, ?_⟩
            · simp only [List.flatMap_cons, encodeItem, List.cons_append,
                List.cons.injEq, true_and]
              rw [htk, hrest, List.append_assoc]
              congr 1
              rw [← hb]
              exact (List.take_append_drop len r).symm
            · intro i hi
              rcases List.mem_cons.mp hi with hi | hi
              · rw [hi]
                simp only [itemWf]
                rw [htk]
                exact hlt
              · exact hwf i hi
          · exact nomatch hread
      · rw [if_neg h1] at hread
        by_cases h2 : t = 2
        · rw [if_pos h2] at hread
          split at hread
          · rename_i h64
            obtain ⟨tail, htail, hcons⟩ :=
              Option.map_eq_some_iff.mp hread
            obtain ⟨hb, hwf⟩ := ih _ (by
                simp only [List.length_drop, List.length_cons]
                omega)
              (rest.drop 64) rfl tail htail
            subst h2
            rw [← hcons]
            have h1 : (rest.drop 32).drop 32 = rest.drop 64 := by
              simp [List.drop_drop]
            refine ⟨?_, ?_⟩
            · simp only [List.flatMap_cons, encodeItem, List.cons_append,
                List.cons.injEq, true_and]
              rw [← hb, List.append_assoc, ← h1, List.take_append_drop,
                List.take_append_drop]
            · intro i hi
              rcases List.mem_cons.mp hi with hi | hi
              · rw [hi]; trivial
              · exact hwf i hi
          · exact nomatch hread
        · rw [if_neg h2] at hread
          exact nomatch hread

/-- The canonical stream encoding: the twelve-byte header, then the
items. -/
def encodeStream (h : StreamHeader) (items : List (DInput Addr32)) :
    List UInt8 :=
  nat32 h.total ++ nat32 h.lo ++ nat32 h.hi ++ items.flatMap encodeItem

/-- The closed stream decoder. -/
def decodeStream? (bytes : List UInt8) :
    Option (StreamHeader × List (DInput Addr32)) :=
  match readNat32 bytes with
  | none => none
  | some (total, r1) =>
    match readNat32 r1 with
    | none => none
    | some (lo, r2) =>
      match readNat32 r2 with
      | none => none
      | some (hi, r3) =>
        match readItems r3 with
        | none => none
        | some items => some (⟨total, lo, hi⟩, items)

/-- Forward correctness on representable streams. -/
theorem decodeStream_encodeStream (h : StreamHeader)
    (items : List (DInput Addr32)) (hwf : ∀ i ∈ items, itemWf i)
    (ht : h.total < 4294967296) (hlo : h.lo < 4294967296)
    (hhi : h.hi < 4294967296) :
    decodeStream? (encodeStream h items) = some (h, items) := by
  unfold decodeStream? encodeStream
  simp only [List.append_assoc]
  rw [readNat32_nat32 h.total ht]
  dsimp only
  rw [readNat32_nat32 h.lo hlo]
  dsimp only
  rw [readNat32_nat32 h.hi hhi]
  dsimp only
  rw [readItems_flat items hwf]

/-- Exactness: a successful decode's input IS the canonical encoding
of its result, header fields representable and items well-formed. -/
theorem decodeStream_exact (bytes : List UInt8) (h : StreamHeader)
    (items : List (DInput Addr32))
    (hdec : decodeStream? bytes = some (h, items)) :
    bytes = encodeStream h items ∧ h.total < 4294967296 ∧
      h.lo < 4294967296 ∧ h.hi < 4294967296 ∧ ∀ i ∈ items, itemWf i := by
  simp only [decodeStream?] at hdec
  split at hdec
  · exact nomatch hdec
  · rename_i total r1 hr1
    split at hdec
    · exact nomatch hdec
    · rename_i lo r2 hr2
      split at hdec
      · exact nomatch hdec
      · rename_i hi r3 hr3
        split at hdec
        · exact nomatch hdec
        · rename_i its hits
          injection hdec with hdec
          injection hdec with hh hitems
          subst hh
          subst hitems
          obtain ⟨hb1, hlt1⟩ := readNat32_some bytes total r1 hr1
          obtain ⟨hb2, hlt2⟩ := readNat32_some r1 lo r2 hr2
          obtain ⟨hb3, hlt3⟩ := readNat32_some r2 hi r3 hr3
          obtain ⟨hbi, hwf⟩ := readItems_some r3 its hits
          refine ⟨?_, hlt1, hlt2, hlt3, hwf⟩
          simp only [encodeStream]
          rw [hb1, hb2, hb3, hbi]
          simp [List.append_assoc]

end Effects.Merkle
