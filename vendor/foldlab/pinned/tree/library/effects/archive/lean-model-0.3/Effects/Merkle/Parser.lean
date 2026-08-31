import Effects.Merkle.ProofCodec
import Effects.Merkle.Laws

/-!
# The incremental frame parser and the response framer

The byte-level bridge the composition law alone does not give: run
composition is over already-parsed inputs, so transport fragmentation
below the parser needs its own machine. `parseFrame` classifies the
front of a byte string as one complete frame, a valid PREFIX that may
complete later, or malformed; `drain` extracts the maximal complete
prefix greedily; `feedAll` folds arbitrary fragments while carrying
the partial-frame remainder. The laws: every fragmentation of one
byte string parses identically (the fold equals the single-shot
drain of the flattened bytes), completion agrees exactly with the
whole-string reader — so a complete parse's input IS the canonical
encoding, and a truncation either leaves a remainder or reads as a
strictly different document — and the response framer accepts
EXACTLY ONE complete decode: any nonempty trailing content after the
machine's done status is rejected, and honest responses are linear
in the tree, so a declared amplification budget of twice the leaf
count admits every honest response while a tiny range can never
license unbounded proof bytes.
-/

namespace Effects.Merkle

open Effects.Cas (Bytes Addr32)
open Effects.Wire

/-- The front-of-string classification: one complete frame, a valid
prefix awaiting more bytes, or malformed. -/
inductive FrameStep where
  | item (i : DInput Addr32) (rest : List UInt8)
  | needMore
  | malformed
  deriving DecidableEq

/-- Classify the front of a byte string. Only an unknown tag is
malformed; every short frame is a valid prefix. -/
def parseFrame : List UInt8 → FrameStep
  | [] => .needMore
  | t :: rest =>
    if t = 0 then .item .skipNode rest
    else if t = 1 then
      match readNat32 rest with
      | none => .needMore
      | some (len, r) =>
        if len ≤ r.length then .item (.chunkNode (r.take len)) (r.drop len)
        else .needMore
    else if t = 2 then
      if h : 64 ≤ rest.length then
        .item (.parentNode ⟨rest.take 32, by
            simp only [List.length_take]; omega⟩
          ⟨(rest.drop 32).take 32, by
            simp only [List.length_take, List.length_drop]; omega⟩)
          (rest.drop 64)
      else .needMore
    else .malformed

/-- A complete frame consumes at least its tag byte. -/
theorem parseFrame_shrinks (bs : List UInt8) (i : DInput Addr32)
    (rest : List UInt8) (h : parseFrame bs = .item i rest) :
    rest.length < bs.length := by
  match bs with
  | [] => exact nomatch h
  | t :: tl =>
    simp only [parseFrame] at h
    by_cases h0 : t = 0
    · rw [if_pos h0] at h
      injection h with h1 h2
      subst h2
      simp
    · rw [if_neg h0] at h
      by_cases h1 : t = 1
      · rw [if_pos h1] at h
        split at h
        · exact nomatch h
        · rename_i len r hr
          split at h
          · rename_i hlen
            injection h with hi hrest
            subst hrest
            have := (readNat32_some tl len r hr).1
            have hlen4 : tl.length = 4 + r.length := by
              rw [this]
              simp only [nat32, List.length_append, List.length_cons,
                List.length_nil]
            simp only [List.length_drop, List.length_cons]
            omega
          · exact nomatch h
      · rw [if_neg h1] at h
        by_cases h2 : t = 2
        · rw [if_pos h2] at h
          split at h
          · rename_i h64
            injection h with hi hrest
            subst hrest
            simp only [List.length_drop, List.length_cons]
            omega
          · exact nomatch h
        · rw [if_neg h2] at h
          exact nomatch h

/-- Prefix stability: a complete frame at the front stays the same
frame when more bytes arrive. -/
theorem parseFrame_append (bs y : List UInt8) (i : DInput Addr32)
    (rest : List UInt8) (h : parseFrame bs = .item i rest) :
    parseFrame (bs ++ y) = .item i (rest ++ y) := by
  match bs with
  | [] => exact nomatch h
  | t :: tl =>
    simp only [parseFrame, List.cons_append] at h ⊢
    by_cases h0 : t = 0
    · rw [if_pos h0] at h ⊢
      injection h with hi hrest
      rw [hi, hrest]
    · rw [if_neg h0] at h ⊢
      by_cases h1 : t = 1
      · rw [if_pos h1] at h ⊢
        split at h
        · exact nomatch h
        · rename_i len r hr
          split at h
          · rename_i hlen
            injection h with hi hrest
            have hb := (readNat32_some tl len r hr).1
            have hread2 : readNat32 (tl ++ y) = some (len, r ++ y) := by
              rw [hb, List.append_assoc]
              exact readNat32_nat32 len (readNat32_some tl len r hr).2 _
            rw [hread2]
            dsimp only
            rw [if_pos (by simp only [List.length_append]; omega)]
            have htake : (r ++ y).take len = r.take len := by
              rw [List.take_append]
              rw [show len - r.length = 0 from by omega]
              simp
            have hdrop : (r ++ y).drop len = r.drop len ++ y := by
              rw [List.drop_append]
              rw [show len - r.length = 0 from by omega]
              simp
            rw [htake, hdrop, ← hi, ← hrest]
          · exact nomatch h
      · rw [if_neg h1] at h ⊢
        by_cases h2 : t = 2
        · rw [if_pos h2] at h ⊢
          split at h
          · rename_i h64
            injection h with hi hrest
            rw [dif_pos (by simp only [List.length_append]; omega)]
            have htake1 : (tl ++ y).take 32 = tl.take 32 := by
              rw [List.take_append]
              rw [show 32 - tl.length = 0 from by omega]
              simp
            have hdrop32 : (tl ++ y).drop 32 = tl.drop 32 ++ y := by
              rw [List.drop_append]
              rw [show 32 - tl.length = 0 from by omega]
              simp
            have htake2 : ((tl ++ y).drop 32).take 32 =
                (tl.drop 32).take 32 := by
              rw [hdrop32, List.take_append]
              rw [show 32 - (tl.drop 32).length = 0 from by
                simp only [List.length_drop]; omega]
              simp
            have hdrop64 : (tl ++ y).drop 64 = tl.drop 64 ++ y := by
              rw [List.drop_append]
              rw [show 64 - tl.length = 0 from by omega]
              simp
            rw [← hi, ← hrest]
            simp only [FrameStep.item.injEq]
            constructor
            · simp only [DInput.parentNode.injEq]
              exact ⟨Subtype.ext htake1, Subtype.ext htake2⟩
            · exact hdrop64
          · exact nomatch h
        · rw [if_neg h2] at h
          exact nomatch h

/-- Malformed stays malformed under more bytes. -/
theorem parseFrame_malformed_append (bs y : List UInt8)
    (h : parseFrame bs = .malformed) :
    parseFrame (bs ++ y) = .malformed := by
  match bs with
  | [] => exact nomatch h
  | t :: tl =>
    simp only [parseFrame, List.cons_append] at h ⊢
    by_cases h0 : t = 0
    · rw [if_pos h0] at h
      exact nomatch h
    · rw [if_neg h0] at h ⊢
      by_cases h1 : t = 1
      · rw [if_pos h1] at h ⊢
        split at h
        · exact nomatch h
        · rename_i len r hr
          split at h <;> exact nomatch h
      · rw [if_neg h1] at h ⊢
        by_cases h2 : t = 2
        · rw [if_pos h2] at h
          split at h <;> exact nomatch h
        · rw [if_neg h2] at h ⊢

/-- Extract the maximal complete prefix greedily, returning the parsed
items and the partial-frame remainder; malformed input is `none`. -/
def drain (bs : List UInt8) :
    Option (List (DInput Addr32) × List UInt8) :=
  match _h : parseFrame bs with
  | .item i rest =>
    (drain rest).map (fun p => (i :: p.1, p.2))
  | .needMore => some ([], bs)
  | .malformed => none
termination_by bs.length
decreasing_by exact parseFrame_shrinks bs i rest _h

theorem drain_item (bs : List UInt8) (i : DInput Addr32)
    (rest : List UInt8) (h : parseFrame bs = .item i rest) :
    drain bs = (drain rest).map (fun p => (i :: p.1, p.2)) := by
  conv => lhs; rw [drain.eq_def]
  split
  · rename_i i' rest' h'
    rw [h'] at h
    rw [FrameStep.item.injEq] at h
    rw [h.1, h.2]
  · rename_i h'
    rw [h'] at h
    exact nomatch h
  · rename_i h'
    rw [h'] at h
    exact nomatch h

theorem drain_needMore (bs : List UInt8)
    (h : parseFrame bs = .needMore) : drain bs = some ([], bs) := by
  conv => lhs; rw [drain.eq_def]
  split
  · rename_i i' rest' h'
    rw [h'] at h
    exact nomatch h
  · rfl
  · rename_i h'
    rw [h'] at h
    exact nomatch h

theorem drain_malformed (bs : List UInt8)
    (h : parseFrame bs = .malformed) : drain bs = none := by
  conv => lhs; rw [drain.eq_def]
  split
  · rename_i i' rest' h'
    rw [h'] at h
    exact nomatch h
  · rename_i h'
    rw [h'] at h
    exact nomatch h
  · rfl

/-- A drain remainder is always a valid prefix awaiting more bytes. -/
theorem drain_rem (bs : List UInt8) :
    ∀ (items : List (DInput Addr32)) (rem : List UInt8),
      drain bs = some (items, rem) → parseFrame rem = .needMore := by
  induction hn : bs.length using Nat.strongRecOn generalizing bs with
  | ind n ih =>
  intro items rem h
  subst hn
  match hp : parseFrame bs with
  | .item i rest =>
    rw [drain_item bs i rest hp] at h
    obtain ⟨p, hp', hcons⟩ := Option.map_eq_some_iff.mp h
    have hbind := ih rest.length (parseFrame_shrinks bs i rest hp) rest rfl
      p.1 p.2 (by rw [hp'])
    have hrem : p.2 = rem := by
      have := congrArg Prod.snd hcons
      simpa using this
    rw [← hrem]
    exact hbind
  | .needMore =>
    rw [drain_needMore bs hp] at h
    injection h with h
    have hrem : bs = rem := congrArg Prod.snd h
    rw [← hrem]
    exact hp
  | .malformed =>
    rw [drain_malformed bs hp] at h
    exact nomatch h

/-- Draining a concatenation: the first string's complete items come
first, then draining continues from its remainder joined with the
rest. -/
theorem drain_append (x y : List UInt8) :
    drain (x ++ y) =
      match drain x with
      | some p => (drain (p.2 ++ y)).map (fun q => (p.1 ++ q.1, q.2))
      | none => none := by
  induction hn : x.length using Nat.strongRecOn generalizing x with
  | ind n ih =>
  subst hn
  match hp : parseFrame x with
  | .item i rest =>
    rw [drain_item x i rest hp,
      drain_item (x ++ y) i (rest ++ y) (parseFrame_append x y i rest hp)]
    rw [ih rest.length (parseFrame_shrinks x i rest hp) rest rfl]
    match hd : drain rest with
    | some p =>
      simp only [Option.map_some]
      match hd2 : drain (p.2 ++ y) with
      | some q => simp
      | none => simp
    | none => simp
  | .needMore =>
    rw [drain_needMore x hp]
    simp
  | .malformed =>
    rw [drain_malformed x hp,
      drain_malformed (x ++ y) (parseFrame_malformed_append x y hp)]

/-- Feed one fragment into the carried remainder. -/
def feed (buf frag : List UInt8) :
    Option (List (DInput Addr32) × List UInt8) :=
  drain (buf ++ frag)

/-- Fold a fragmentation, accumulating items and threading the
partial-frame remainder. -/
def feedAll (frags : List (List UInt8)) :
    Option (List (DInput Addr32) × List UInt8) :=
  frags.foldl
    (fun acc frag => acc.bind fun p =>
      (feed p.2 frag).map fun q => (p.1 ++ q.1, q.2))
    (some ([], []))

private theorem feedAll_none (frags : List (List UInt8)) :
    frags.foldl
      (fun acc frag => acc.bind fun p =>
        (feed p.2 frag).map fun q => (p.1 ++ q.1, q.2))
      none = none := by
  induction frags with
  | nil => rfl
  | cons frag rest ihf => simpa using ihf

private theorem feedAll_go (frags : List (List UInt8)) :
    ∀ (items : List (DInput Addr32)) (buf : List UInt8),
      parseFrame buf = .needMore →
      frags.foldl
        (fun acc frag => acc.bind fun p =>
          (feed p.2 frag).map fun q => (p.1 ++ q.1, q.2))
        (some (items, buf)) =
      (drain (buf ++ frags.flatten)).map fun q => (items ++ q.1, q.2) := by
  induction frags with
  | nil =>
    intro items buf hbuf
    simp only [List.foldl_nil, List.flatten_nil, List.append_nil]
    rw [drain_needMore buf hbuf]
    simp
  | cons frag rest ihf =>
    intro items buf hbuf
    simp only [List.foldl_cons, List.flatten_cons, Option.bind_some]
    rw [show buf ++ (frag ++ rest.flatten) =
      (buf ++ frag) ++ rest.flatten from by rw [List.append_assoc]]
    rw [drain_append (buf ++ frag) rest.flatten]
    show List.foldl _
      ((drain (buf ++ frag)).map fun q => (items ++ q.1, q.2)) rest = _
    match hd : drain (buf ++ frag) with
    | some p =>
      simp only [Option.map_some]
      have hrem := drain_rem (buf ++ frag) p.1 p.2 (by rw [hd])
      rw [ihf (items ++ p.1) p.2 hrem]
      match drain (p.2 ++ rest.flatten) with
      | some q => simp
      | none => simp
    | none =>
      simp only [Option.map_none]
      exact feedAll_none rest

/-- The fold over any fragmentation equals the single-shot drain of
the flattened bytes. -/
theorem feedAll_flatten (frags : List (List UInt8)) :
    feedAll frags = drain frags.flatten := by
  unfold feedAll
  rw [feedAll_go frags [] [] rfl]
  simp

/-- MRK-015 carrier, first half: parsing is fragmentation-invariant —
every fragmentation of one byte string parses to the same items,
remainder, and terminal. -/
theorem parse_fragmentation_invariant (fragsA fragsB : List (List UInt8))
    (h : fragsA.flatten = fragsB.flatten) :
    feedAll fragsA = feedAll fragsB := by
  rw [feedAll_flatten, feedAll_flatten, h]

/-! ## Completion agrees exactly with the whole-string reader -/

private theorem parseFrame_readItems_step (bs : List UInt8)
    (i : DInput Addr32) (rest : List UInt8)
    (h : parseFrame bs = .item i rest) :
    readItems bs = (readItems rest).map (i :: ·) := by
  match bs with
  | [] => exact nomatch h
  | t :: tl =>
    rw [readItems.eq_def]
    dsimp only
    simp only [parseFrame] at h
    by_cases h0 : t = 0
    · rw [if_pos h0] at h ⊢
      injection h with hi hrest
      rw [hi, hrest]
    · rw [if_neg h0] at h ⊢
      by_cases h1 : t = 1
      · rw [if_pos h1] at h ⊢
        split at h
        · exact nomatch h
        · rename_i len r hr
          split
          · rename_i hr'
            rw [hr] at hr'
            exact nomatch hr'
          · rename_i len' r' hr'
            rw [hr] at hr'
            injection hr' with hr'
            have hlen : len' = len := (congrArg Prod.fst hr').symm
            have hrest : r' = r := (congrArg Prod.snd hr').symm
            subst hlen
            subst hrest
            split at h
            · rename_i hle
              injection h with hi hrest
              rw [if_pos hle, ← hi, ← hrest]
            · exact nomatch h
      · rw [if_neg h1] at h ⊢
        by_cases h2 : t = 2
        · rw [if_pos h2] at h ⊢
          split at h
          · rename_i h64
            injection h with hi hrest
            rw [dif_pos h64, ← hi, ← hrest]
          · exact nomatch h
        · rw [if_neg h2] at h
          exact nomatch h

private theorem readItems_step_inv (bs : List UInt8)
    (items : List (DInput Addr32)) (h : readItems bs = some items) :
    (bs = [] ∧ items = []) ∨
      ∃ i rest tail, parseFrame bs = .item i rest ∧
        readItems rest = some tail ∧ items = i :: tail := by
  match bs with
  | [] =>
    rw [readItems.eq_def] at h
    dsimp only at h
    injection h with h
    exact Or.inl ⟨rfl, h.symm⟩
  | t :: tl =>
    right
    rw [readItems.eq_def] at h
    dsimp only at h
    by_cases h0 : t = 0
    · rw [if_pos h0] at h
      obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp h
      exact ⟨.skipNode, tl, tail, by simp [parseFrame, h0], htail,
        hcons.symm⟩
    · rw [if_neg h0] at h
      by_cases h1 : t = 1
      · rw [if_pos h1] at h
        split at h
        · exact nomatch h
        · rename_i len r hr
          split at h
          · rename_i hle
            obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp h
            refine ⟨.chunkNode (r.take len), r.drop len, tail, ?_, htail,
              hcons.symm⟩
            simp only [parseFrame, if_neg h0, if_pos h1]
            rw [hr]
            dsimp only
            rw [if_pos hle]
          · exact nomatch h
      · rw [if_neg h1] at h
        by_cases h2 : t = 2
        · rw [if_pos h2] at h
          split at h
          · rename_i h64
            obtain ⟨tail, htail, hcons⟩ := Option.map_eq_some_iff.mp h
            exact ⟨_, tl.drop 64, tail,
              by simp only [parseFrame, if_neg h0, if_neg h1, if_pos h2,
                dif_pos h64], htail, hcons.symm⟩
          · exact nomatch h
        · rw [if_neg h2] at h
          exact nomatch h

/-- A whole-string parse drains completely. -/
theorem drain_of_readItems :
    ∀ (bs : List UInt8) (items : List (DInput Addr32)),
      readItems bs = some items → drain bs = some (items, []) := by
  intro bs
  induction hn : bs.length using Nat.strongRecOn generalizing bs with
  | ind n ih =>
  intro items h
  subst hn
  rcases readItems_step_inv bs items h with ⟨hnil, hits⟩ | ⟨i, rest, tail, hp, htail, hcons⟩
  · subst hnil
    subst hits
    exact drain_needMore [] rfl
  · rw [drain_item bs i rest hp,
      ih rest.length (parseFrame_shrinks bs i rest hp) rest rfl tail htail]
    rw [hcons]
    rfl

/-- MRK-015 carrier, second half: a complete drain agrees with the
whole-string reader, so its input IS the canonical encoding of its
items — a truncation either leaves a partial-frame remainder or reads
as a strictly different document. -/
theorem readItems_of_drain :
    ∀ (bs : List UInt8) (items : List (DInput Addr32)),
      drain bs = some (items, []) → readItems bs = some items := by
  intro bs
  induction hn : bs.length using Nat.strongRecOn generalizing bs with
  | ind n ih =>
  intro items h
  subst hn
  match hp : parseFrame bs with
  | .item i rest =>
    rw [drain_item bs i rest hp] at h
    obtain ⟨p, hp', hcons⟩ := Option.map_eq_some_iff.mp h
    have hp2 : p.2 = [] := by
      have := congrArg Prod.snd hcons
      simpa using this
    have hp1 : items = i :: p.1 := by
      have := congrArg Prod.fst hcons
      simpa using this.symm
    rw [parseFrame_readItems_step bs i rest hp,
      ih rest.length (parseFrame_shrinks bs i rest hp) rest rfl p.1
        (by rw [hp', ← hp2])]
    rw [hp1]
    rfl
  | .needMore =>
    rw [drain_needMore bs hp] at h
    injection h with h
    have hbs : bs = [] := by
      have := congrArg Prod.snd h
      simpa using this
    have hits : items = [] := by
      have := congrArg Prod.fst h
      simpa using this.symm
    subst hbs
    rw [readItems.eq_def]
    dsimp only
    rw [hits]
  | .malformed =>
    rw [drain_malformed bs hp] at h
    exact nomatch h

/-- Exactness at the parser: a complete drain's input is exactly the
canonical encoding of its well-formed items. -/
theorem drain_complete_exact (bs : List UInt8)
    (items : List (DInput Addr32)) (h : drain bs = some (items, [])) :
    bs = items.flatMap encodeItem ∧ ∀ i ∈ items, itemWf i :=
  readItems_some bs items (readItems_of_drain bs items h)

/-! ## The response framer (MRK-019) -/

/-- The framer's acceptance: exactly one complete decode — the bytes
drain completely into machine inputs, the machine reaches done, and
done is reached for the FIRST time at the last item, so nothing after
completion was absorbed. -/
def ResponseAccepted (D : DParams Addr32) (bytes : List UInt8) : Prop :=
  ∃ items, drain bytes = some (items, []) ∧
    (drun D (initState D) items).1.status = .done ∧
    ∀ j < items.length,
      (drun D (initState D) (items.take j)).1.status ≠ .done

/-- MRK-019 carrier: nonempty trailing content after an accepted
response is rejected — the framer accepts exactly one complete
decode, so the machine's own absorb-after-done convenience never
reaches the wire. -/
theorem response_trailing_rejected (D : DParams Addr32)
    (bytes extra : List UInt8) (hne : extra ≠ [])
    (hacc : ResponseAccepted D bytes) :
    ¬ ResponseAccepted D (bytes ++ extra) := by
  obtain ⟨items, hdrain, hdone, hfirst⟩ := hacc
  rintro ⟨items', hdrain', hdone', hfirst'⟩
  rw [drain_append bytes extra, hdrain] at hdrain'
  dsimp only at hdrain'
  rw [List.nil_append] at hdrain'
  obtain ⟨q, hq, hcons⟩ := Option.map_eq_some_iff.mp hdrain'
  have hq2 : q.2 = [] := by
    have := congrArg Prod.snd hcons
    simpa using this
  have hq1 : items' = items ++ q.1 := by
    have := congrArg Prod.fst hcons
    simpa using this.symm
  by_cases hmore : q.1 = []
  · have hextra : extra = [] := by
      match hp : parseFrame extra with
      | .item i rest =>
        rw [drain_item extra i rest hp] at hq
        obtain ⟨r, hr, hrc⟩ := Option.map_eq_some_iff.mp hq
        exfalso
        have := congrArg Prod.fst hrc
        rw [hmore] at this
        simp at this
      | .needMore =>
        rw [drain_needMore extra hp] at hq
        injection hq with hq
        have hsnd := congrArg Prod.snd hq
        rw [hq2] at hsnd
        exact hsnd
      | .malformed =>
        rw [drain_malformed extra hp] at hq
        exact nomatch hq
    exact hne hextra
  · have hlt : items.length < items'.length := by
      rw [hq1, List.length_append]
      have : 0 < q.1.length := List.length_pos_iff.mpr hmore
      omega
    have := hfirst' items.length hlt
    rw [hq1] at this
    rw [show (items ++ q.1).take items.length = items from by simp] at this
    exact this hdone

/-- The proof-amplification bound: an honest stream is linear in the
tree, so a declared budget of twice the leaf count admits every honest
response while a tiny range never licenses unbounded proof frames. -/
theorem genStream_length {A : Type} (P : HP A) (lo hi : Nat) :
    ∀ (chunks : List Bytes) (base : Nat), 0 < chunks.length →
      (genStream P lo hi base chunks).length ≤ 2 * chunks.length - 1 := by
  intro chunks
  induction hn : chunks.length using Nat.strongRecOn
    generalizing chunks with
  | ind n ih =>
  intro base hpos
  subst hn
  by_cases hd : base + chunks.length ≤ lo ∨ hi ≤ base
  · conv => lhs; rw [genStream.eq_def]
    rw [if_pos hd]
    simp only [List.length_cons, List.length_nil]
    omega
  · by_cases h1 : chunks.length ≤ 1
    · conv => lhs; rw [genStream.eq_def]
      rw [if_neg hd, dif_pos h1]
      simp only [List.length_cons, List.length_nil]
      omega
    · have hk_lt := pow2Below_lt chunks.length (by omega)
      have hk_pos := pow2Below_pos chunks.length
      have htake_len : (chunks.take (pow2Below chunks.length)).length =
          pow2Below chunks.length := by
        simp only [List.length_take]
        omega
      have hdrop_len : (chunks.drop (pow2Below chunks.length)).length =
          chunks.length - pow2Below chunks.length := by
        simp only [List.length_drop]
      have hb₁ := ih (pow2Below chunks.length) (by omega)
        (chunks.take (pow2Below chunks.length)) htake_len base
        (by omega)
      have hb₂ := ih (chunks.length - pow2Below chunks.length) (by omega)
        (chunks.drop (pow2Below chunks.length)) hdrop_len
        (base + pow2Below chunks.length) (by omega)
      conv => lhs; rw [genStream.eq_def]
      rw [if_neg hd, dif_neg h1]
      simp only [List.length_cons, List.length_append]
      omega

private def zeroAddr : Addr32 := ⟨List.replicate 32 0, by simp⟩

/-- Anti-vacuity: the framer's acceptance is satisfiable — a one-chunk
honest response is accepted, and done first fires at its final item. -/
theorem response_accepts_example :
    ResponseAccepted ⟨⟨fun _ => zeroAddr⟩, 1, zeroAddr, 0, 1⟩
      (encodeItem (.chunkNode [])) := by
  refine ⟨[.chunkNode []], ?_, ?_, ?_⟩
  · have h1 : parseFrame (encodeItem (.chunkNode [])) =
        .item (.chunkNode []) [] := by decide
    rw [drain_item _ _ _ h1, drain_needMore [] rfl]
    rfl
  · decide
  · decide

end Effects.Merkle
