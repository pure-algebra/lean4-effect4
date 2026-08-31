import Cas.Schema.Codec.Core

/-!
# Mutual schema codec law proofs

The forward and image-exactness law families must elaborate together.
Lean's generated functional-induction terms for this well-founded mutual
decoder otherwise emit colliding private auxiliary names when compiled
in separate modules.

Each family is proved once for values, union members, fields, and
lists; the public theorems are projections of those bundled proofs.

**Exactness comes first in this module**, and that ordering is
load-bearing rather than cosmetic. The union's forward law needs one
extra fact — that no member of a discriminated list accepts a LATER
member's encoding (`decode_head_encodeMembers_tail`) — and the cheapest
proof of it runs through exactness: if a member accepted the bytes,
those bytes would BE that member's encoding, whose head `_tag` literal
is the member's own tag, and the tags are distinct. So exactness (which
needs no premise at all) is proved first, the disjointness lemma is
derived from it, and the forward family consumes it. No tactic
escalation, no second induction over the decoder.
-/

namespace Cas.Schema

set_option maxHeartbeats 1600000

/-! ## Exactness — no premise -/

/-- Image exactness for all four codec functions, from ONE functional
induction. No well-formedness premise and no discrimination premise:
the decoder accepts nothing outside the encoder's image, whatever the
code. On the union arm this is what makes try-in-order decoding safe
even when the members overlap — whichever member answers, the bytes are
that member's encoding. -/
private theorem exact_all :
    (∀ (a : Ast) (v : Json.Value), ∀ {x : El a},
        decode a v = some x → v = encode a x)
  ∧ (∀ (b : Bool) (ms : List Ast) (v : Json.Value),
        ∀ {x : cond b (ElMembers ms) Empty},
        decodeMembers b ms v = some x → v = encodeMembers b ms x)
  ∧ (∀ (fs : List (String × Bool × Ast)) (kvs : List (String × Json.Value)),
        ∀ {x : ElFields fs},
        decodeFields fs kvs = some x → kvs = encodeFields fs x)
  ∧ (∀ (a : Ast) (vs : List Json.Value), ∀ {xs : List (El a)},
        decodeList a vs = some xs → vs = xs.map (encode a)) := by
  refine decode.mutual_induct_unfolding
    (motive1 := fun a v out => ∀ {x : El a}, out = some x → v = encode a x)
    (motive2 := fun b ms v out => ∀ {x : cond b (ElMembers ms) Empty},
      out = some x → v = encodeMembers b ms x)
    (motive3 := fun fs kvs out => ∀ {x : ElFields fs},
      out = some x → kvs = encodeFields fs x)
    (motive4 := fun a vs out => ∀ {xs : List (El a)},
      out = some xs → vs = xs.map (encode a))
    ?case1 ?case2 ?case3 ?case4 ?case5 ?case6 ?case7 ?case8 ?case9 ?case10
    ?case11 ?case12 ?case13 ?case14 ?case15 ?case16 ?case17 ?case18 ?case19
    ?case20 ?case21 ?case22 ?case23 ?case24 ?case25 ?case26 ?case27 ?case28
    ?case29
  case case1 => intro x h; cases x; rfl
  case case2 => intro b x h; injection h with hx; subst hx; rfl
  case case3 => intro v x h; exact decInt_exact h
  case case4 => intro s x h; injection h with hx; subst hx; rfl
  case case5 => intro x h; cases x; rfl
  case case6 => intro b' x h; cases x; rfl
  case case7 => intro b b' hne x h; exact nomatch h
  case case8 =>
    intro i v x h
    cases x
    cases hd : decInt v with
    | none => rw [hd] at h; exact nomatch h
    | some j =>
      rw [hd] at h
      simp only [Option.bind_some] at h
      split at h
      next he =>
        subst he
        simpa only [encode, encLit] using decInt_exact hd
      next => exact nomatch h
  case case9 => intro s' x h; cases x; rfl
  case case10 => intro s s' hne x h; exact nomatch h
  case case11 =>
    intro a vs ih x h
    simp only [encode]
    rw [ih h]
  case case12 =>
    intro fs kvs ih x h
    simp only [encode]
    rw [ih h]
  case case13 =>
    intro t v x h
    cases hd : decRef t v with
    | none => rw [hd] at h; exact nomatch h
    | some addr =>
      rw [hd] at h
      change some { addr := addr } = some x at h
      injection h with hx
      subst hx
      simp only [encode]
      exact decRef_exact hd
  case case14 =>
    intro ms mode v ih x h
    exact ih h
  case case15 =>
    intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ x h
    exact nomatch h
  case case16 => intro v x _; exact Empty.elim x
  case case17 => intro a v ihv x h; exact ihv h
  case case18 =>
    intro a b rest v ihv ihr x h
    change Option.or ((decode a v).map Sum.inl)
      ((decodeMembers true (b :: rest) v).map Sum.inr) = some x at h
    cases hd : decode a v with
    | some z =>
      rw [hd] at h
      change some (Sum.inl z) = some x at h
      injection h with hx
      subst hx
      exact ihv hd
    | none =>
      rw [hd] at h
      cases ht : decodeMembers true (b :: rest) v with
      | none =>
        rw [ht] at h
        change (none : Option (El a ⊕ ElMembers (b :: rest))) = some x at h
        exact nomatch h
      | some z =>
        rw [ht] at h
        change some (Sum.inr z) = some x at h
        injection h with hx
        subst hx
        exact ihr ht
  case case19 => intro ms v x _; exact Empty.elim x
  case case20 =>
    intro x h
    change some () = some x at h
    cases x
    rfl
  case case21 =>
    intro head tail x h
    change none = some x at h
    exact nomatch h
  case case22 =>
    intro fst snd fs ih x h
    obtain ⟨xv, rest⟩ := x
    change (decodeFields fs []).bind (fun rest => some (none, rest)) =
      some (xv, rest) at h
    cases hr : decodeFields fs [] with
    | none => rw [hr] at h; exact nomatch h
    | some tail =>
      rw [hr] at h
      simp only [Option.bind_some] at h
      injection h with hp
      injection hp with hxv hrest
      subst hxv
      subst hrest
      simp only [encodeFields, List.nil_append]
      exact ih hr
  case case23 =>
    intro fst snd tail x h
    change none = some x at h
    exact nomatch h
  case case24 =>
    intro a fs k v kvs ihv ihr x h
    obtain ⟨xv, rest⟩ := x
    simp only at h
    change (decode a v).bind (fun y =>
      (decodeFields fs kvs).bind (fun tail => some (some y, tail))) =
        some (xv, rest) at h
    cases hd : decode a v with
    | none => rw [hd] at h; exact nomatch h
    | some y =>
      cases ht : decodeFields fs kvs with
      | none => rw [hd, ht] at h; exact nomatch h
      | some tail =>
        rw [hd, ht] at h
        simp only [Option.bind_some] at h
        injection h with hp
        injection hp with hxv hrest
        subst hxv
        subst hrest
        simp only [encodeFields, List.singleton_append]
        rw [← ihv hd, ← ihr ht]
  case case25 =>
    intro n a fs k v kvs hkn ihr x h
    obtain ⟨xv, rest⟩ := x
    simp only [if_neg hkn] at h
    change (decodeFields fs ((k, v) :: kvs)).bind
      (fun tail => some (none, tail)) = some (xv, rest) at h
    cases ht : decodeFields fs ((k, v) :: kvs) with
    | none => rw [ht] at h; exact nomatch h
    | some tail =>
      rw [ht] at h
      simp only [Option.bind_some] at h
      injection h with hp
      injection hp with hxv hrest
      subst hxv
      subst hrest
      simp only [encodeFields, List.nil_append]
      exact ihr ht
  case case26 =>
    intro a fs k v kvs ihv ihr x h
    obtain ⟨xv, rest⟩ := x
    simp only at h
    change (decode a v).bind (fun y =>
      (decodeFields fs kvs).bind (fun tail => some (y, tail))) =
        some (xv, rest) at h
    cases hd : decode a v with
    | none => rw [hd] at h; exact nomatch h
    | some y =>
      cases ht : decodeFields fs kvs with
      | none => rw [hd, ht] at h; exact nomatch h
      | some tail =>
        rw [hd, ht] at h
        simp only [Option.bind_some] at h
        injection h with hp
        injection hp with hxv hrest
        subst hxv
        subst hrest
        simp only [encodeFields]
        rw [← ihv hd, ← ihr ht]
  case case27 =>
    intro n a fs k v kvs hkn x h
    simp only [if_neg hkn] at h
    change none = some x at h
    exact nomatch h
  case case28 =>
    intro a xs h
    change some [] = some xs at h
    injection h with hx
    subst hx
    rfl
  case case29 =>
    intro a v vs ihv ihr xs h
    change (decode a v).bind (fun y =>
      (decodeList a vs).bind (fun tail => some (y :: tail))) = some xs at h
    cases hd : decode a v with
    | none => rw [hd] at h; exact nomatch h
    | some y =>
      cases ht : decodeList a vs with
      | none => rw [hd, ht] at h; exact nomatch h
      | some tail =>
        rw [hd, ht] at h
        simp only [Option.bind_some] at h
        injection h with hx
        subst hx
        simp only [List.map_cons]
        rw [← ihv hd, ← ihr ht]

theorem decode_exact : ∀ {a : Ast} {v : Json.Value} {x : El a},
    decode a v = some x → v = encode a x :=
  fun {a v _} h => exact_all.1 a v h

/-- Exactness on the union arm, stated for the member sum directly. -/
theorem decodeMembers_exact : ∀ {b : Bool} {ms : List Ast} {v : Json.Value}
    {x : cond b (ElMembers ms) Empty},
    decodeMembers b ms v = some x → v = encodeMembers b ms x :=
  fun {b ms v _} h => exact_all.2.1 b ms v h

theorem decodeFields_exact :
    ∀ {fs : List (String × Bool × Ast)}
      {kvs : List (String × Json.Value)} {x : ElFields fs},
      decodeFields fs kvs = some x → kvs = encodeFields fs x :=
  fun {fs kvs _} h => exact_all.2.2.1 fs kvs h

theorem decodeList_exact : ∀ {a : Ast} {vs : List Json.Value}
    {xs : List (El a)}, decodeList a vs = some xs → vs = xs.map (encode a) :=
  fun {a vs _} h => exact_all.2.2.2 a vs h

/-! ## Disjointness — why distinct tags make try-order decoding exact -/

/-- Distinct tags kill overlap: under discrimination, the head member
of a member list REFUSES every later member's encoding. That is the one
fact separating a discriminated union from a general one, and it is
where the whole staged design pays off — try-in-order decoding becomes
a function of the VALUE, not of the member order, so the forward law
holds and the union's identity survives.

The argument is three lines of content: if the head accepted the bytes
then by exactness the bytes ARE the head's encoding, whose leading
`_tag` literal is the head's own tag; but the bytes also lead with a
tag drawn from the tail, and the head's tag is not one of those. -/
theorem decode_head_encodeMembers_tail {a : Ast} {rest : List Ast}
    (h : discriminatedB (a :: rest) = true)
    (y : cond true (ElMembers rest) Empty) :
    decode a (encodeMembers true rest y) = none := by
  obtain ⟨t, ht, hnot⟩ := discriminatedB_head h
  cases hz : decode a (encodeMembers true rest y) with
  | none => rfl
  | some z =>
    exfalso
    have hex : encodeMembers true rest y = encode a z := decode_exact hz
    obtain ⟨kvs, he⟩ := encode_memberTag ht z
    obtain ⟨t', hmem, kvs', he'⟩ :=
      encodeMembers_tag rest (discriminatedB_tail h) y
    have hobj : Json.Value.obj ((tagField, Json.Value.str t) :: kvs)
        = Json.Value.obj ((tagField, Json.Value.str t') :: kvs') := by
      rw [← he, ← hex]
      exact he'
    injection hobj with hlist
    injection hlist with hhd _
    have hstr : Json.Value.str t = Json.Value.str t' := congrArg Prod.snd hhd
    injection hstr with hteq
    subst hteq
    exact hnot hmem

/-! ## Forward — under canonical fields -/

/-- The forward round trip for all four codec functions, from ONE
functional induction over the mutual block. The four public theorems
below are its projections — the members, fields, and list laws are not
re-proved, so they cannot drift from the value law.

The union arm carries the DISCRIMINATION premise and nothing else new:
an undiscriminated union denotes `Empty`, so its arm closes by
`Empty.elim` exactly as the general declaration's does, and the law
over the grown carrier stays vacuous rather than false. -/
private theorem roundtrip_all :
    (∀ (a : Ast) (v : Json.Value), a.WF → ∀ (x : El a),
        v = encode a x → decode a v = some x)
  ∧ (∀ (b : Bool) (ms : List Ast) (v : Json.Value),
        discriminatedB ms = true → WFMembers ms →
        ∀ (x : cond b (ElMembers ms) Empty),
        v = encodeMembers b ms x → decodeMembers b ms v = some x)
  ∧ (∀ (fs : List (String × Bool × Ast)) (kvs : List (String × Json.Value)),
        (fs.map (fun f => f.1)).Nodup → WFFields fs → ∀ (x : ElFields fs),
        kvs = encodeFields fs x → decodeFields fs kvs = some x)
  ∧ (∀ (a : Ast) (vs : List Json.Value), a.WF → ∀ (xs : List (El a)),
        vs = xs.map (encode a) → decodeList a vs = some xs) := by
  refine decode.mutual_induct_unfolding
    (motive1 := fun a v out => ∀ (ha : a.WF) (x : El a),
      v = encode a x → out = some x)
    (motive2 := fun b ms v out =>
      ∀ (hd : discriminatedB ms = true) (hwf : WFMembers ms)
        (x : cond b (ElMembers ms) Empty),
        v = encodeMembers b ms x → out = some x)
    (motive3 := fun fs kvs out =>
      ∀ (hnd : (fs.map (fun f => f.1)).Nodup) (hwf : WFFields fs)
        (x : ElFields fs), kvs = encodeFields fs x → out = some x)
    (motive4 := fun a vs out => ∀ (ha : a.WF) (xs : List (El a)),
      vs = xs.map (encode a) → out = some xs)
    ?case1 ?case2 ?case3 ?case4 ?case5 ?case6 ?case7 ?case8 ?case9 ?case10
    ?case11 ?case12 ?case13 ?case14 ?case15 ?case16 ?case17 ?case18 ?case19
    ?case20 ?case21 ?case22 ?case23 ?case24 ?case25 ?case26 ?case27 ?case28
    ?case29
  case case1 => intro _ x _; cases x; rfl
  case case2 =>
    intro b
    intro _ x hv
    simp only [encode] at hv
    injection hv with hx
    subst hx
    rfl
  case case3 =>
    intro v
    intro _ x hv
    rw [hv]
    change decInt (encInt x) = some x
    exact decInt_encInt x
  case case4 =>
    intro s
    intro _ x hv
    simp only [encode] at hv
    injection hv with hx
    subst hx
    rfl
  case case5 => intro _ x _; cases x; rfl
  case case6 => intro b' _ x _; cases x; rfl
  case case7 =>
    intro b b' hne
    intro _ x hv
    cases x
    simp only [encode, encLit] at hv
    injection hv with he
    exact absurd he hne
  case case8 =>
    intro i v
    intro _ x hv
    cases x
    rw [hv]
    simp only [encode, encLit, decInt_encInt, Option.bind_some, if_true]
  case case9 => intro s' _ x _; cases x; rfl
  case case10 =>
    intro s s' hne
    intro _ x hv
    cases x
    simp only [encode, encLit] at hv
    injection hv with he
    exact absurd he hne
  case case11 =>
    intro a vs ih
    intro ha xs hv
    simp only [Ast.WF] at ha
    simp only [encode] at hv
    injection hv with hvs
    exact ih ha xs hvs
  case case12 =>
    intro fs kvs ih
    intro ha x hv
    simp only [Ast.WF] at ha
    simp only [encode] at hv
    injection hv with hkvs
    exact ih (sorted_names_nodup ha.1) ha.2 x hkvs
  case case13 =>
    intro t v
    intro _ r hv
    obtain ⟨addr⟩ := r
    rw [hv]
    simp only [encode, decRef_encRef]
    change some (StoreRef.mk addr) = some (StoreRef.mk addr)
    rfl
  case case14 =>
    intro ms mode v ih
    intro ha x hv
    simp only [Ast.WF] at ha
    exact ih (discriminatedB_of_el x) ha.2 x hv
  case case15 =>
    intro schema value hnull hbool hint hstr hlitnull hlitbool
      hlitint hlitstr harr hstruct href hunion
    intro _ x hv
    cases schema with
    | null => exact False.elim (hnull rfl (by simpa only [encode] using hv))
    | bool => exact False.elim (hbool x rfl (by simpa only [encode] using hv))
    | int => exact False.elim (hint rfl)
    | str => exact False.elim (hstr x rfl (by simpa only [encode] using hv))
    | lit l =>
      cases l with
      | null =>
        exact False.elim (hlitnull rfl (by simpa only [encode, encLit] using hv))
      | bool b =>
        exact False.elim
          (hlitbool b b rfl (by simpa only [encode, encLit] using hv))
      | int i => exact False.elim (hlitint i rfl)
      | str s =>
        exact False.elim
          (hlitstr s s rfl (by simpa only [encode, encLit] using hv))
    | arr item =>
      exact False.elim
        (harr item (x.map (encode item)) rfl (by simpa only [encode] using hv))
    | struct fs =>
      exact False.elim
        (hstruct fs (encodeFields fs x) rfl (by simpa only [encode] using hv))
    | ref t => exact False.elim (href t rfl)
    | decl _ _ _ => exact x.elim
    | union ms mode => exact False.elim (hunion ms mode rfl)
    -- The enum denotes `Empty` (the named `enumEl` obligation), so this
    -- arm closes the way the general declaration's does: there is no
    -- value to have encoded, and the law is vacuous rather than false.
    | enum _ => exact x.elim
    -- And the tuple denotes `Empty` too (the named `tupleEl`
    -- obligation), for the same reason and with the same closure.
    | tuple _ _ _ => exact x.elim
    -- The two C6 codes denote `Empty` as well, and there the emptiness
    -- is a REFUSAL rather than a parked obligation: v1 states no
    -- denotational adequacy for recursive codes at all (the named
    -- `recursiveEl` obligation, `Cas/Schema/El.lean`). The closure is
    -- the same — no value exists to have been encoded — so this law
    -- holds over the grown carrier vacuously rather than falsely.
    | reference _ => exact x.elim
    | susp _ => exact x.elim
  case case16 => intro v hd hwf x _; exact Empty.elim x
  case case17 => intro a v ihv hd hwf x hv; exact ihv hwf.1 x hv
  case case18 =>
    intro a b rest v ihv ihr hd hwf x hv
    cases x with
    | inl y =>
      have h1 : decode a v = some y := ihv hwf.1 y hv
      show Option.or ((decode a v).map Sum.inl)
        ((decodeMembers true (b :: rest) v).map Sum.inr) = some (Sum.inl y)
      rw [h1]
      rfl
    | inr y =>
      have h0 : decode a v = none := by
        rw [hv]
        exact decode_head_encodeMembers_tail hd y
      have h2 : decodeMembers true (b :: rest) v = some y :=
        ihr (discriminatedB_tail hd) hwf.2 y hv
      show Option.or ((decode a v).map Sum.inl)
        ((decodeMembers true (b :: rest) v).map Sum.inr) = some (Sum.inr y)
      rw [h0, h2]
      rfl
  case case19 => intro ms v hd hwf x _; exact Empty.elim x
  case case20 =>
    intro hnd hwf x hv
    cases x
    rfl
  case case21 =>
    intro head tail hnd hwf x hv
    cases x
    simp only [encodeFields] at hv
    exact nomatch hv
  case case22 =>
    intro fst snd fs ih hnd hwf x hv
    obtain ⟨xv, rest⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnd' : (fs.map (fun f => f.1)).Nodup := hnd.2
    cases xv with
    | some value =>
      simp only [encodeFields, List.singleton_append] at hv
      exact nomatch hv
    | none =>
      simp only [encodeFields, List.nil_append] at hv
      change (decodeFields fs []).bind (fun tail => some (none, tail)) =
        some (none, rest)
      rw [ih hnd' hwf.2 rest hv]
      simp only [Option.bind_some]
  case case23 =>
    intro fst snd tail hnd hwf x hv
    obtain ⟨value, rest⟩ := x
    simp only [encodeFields] at hv
    exact nomatch hv
  case case24 =>
    intro a fs k v kvs ihv ihr hnd hwf x hv
    obtain ⟨xv, rest⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnotin : k ∉ fs.map (fun f => f.1) := hnd.1
    have hnd' : (fs.map (fun f => f.1)).Nodup := hnd.2
    simp only at ⊢
    cases xv with
    | some value =>
      simp only [encodeFields, List.singleton_append] at hv
      injection hv with hhead hkvs
      injection hhead with hkey hv'
      rw [ihv hwf.1 value hv', ihr hnd' hwf.2 rest hkvs]
      simp only [if_true, Option.bind_some]
    | none =>
      simp only [encodeFields, List.nil_append] at hv
      have hk : k ∈ fs.map (fun f => f.1) := by
        refine encodeFields_keys fs rest k ?_
        rw [← hv]
        simp
      exact absurd hk hnotin
  case case25 =>
    intro n a fs k v kvs hkn ihr hnd hwf x hv
    obtain ⟨xv, rest⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnd' : (fs.map (fun f => f.1)).Nodup := hnd.2
    simp only [if_neg hkn] at ⊢
    cases xv with
    | some value =>
      simp only [encodeFields, List.singleton_append] at hv
      injection hv with hhead htail
      injection hhead with hk hv'
      exact absurd hk hkn
    | none =>
      simp only [encodeFields, List.nil_append] at hv
      rw [ihr hnd' hwf.2 rest hv]
      simp only [Option.bind_some]
  case case26 =>
    intro a fs k v kvs ihv ihr hnd hwf x hv
    obtain ⟨value, rest⟩ := x
    simp only [List.map_cons, List.nodup_cons] at hnd
    have hnd' : (fs.map (fun f => f.1)).Nodup := hnd.2
    simp only at ⊢
    simp only [encodeFields] at hv
    injection hv with hhead hkvs
    injection hhead with hkey hv'
    rw [ihv hwf.1 value hv', ihr hnd' hwf.2 rest hkvs]
    simp only [if_true, Option.bind_some]
  case case27 =>
    intro n a fs k v kvs hkn hnd hwf x hv
    obtain ⟨value, rest⟩ := x
    simp only [if_neg hkn] at ⊢
    simp only [encodeFields] at hv
    injection hv with hhead htail
    injection hhead with hk hv'
    exact absurd hk hkn
  case case28 =>
    intro a ha xs hv
    cases xs with
    | nil => rfl
    | cons x xs =>
      simp only [List.map_cons] at hv
      exact nomatch hv
  case case29 =>
    intro a v vs ihv ihr ha xs hv
    cases xs with
    | nil =>
      simp only [List.map_nil] at hv
      exact nomatch hv
    | cons x xs =>
      simp only [List.map_cons] at hv
      injection hv with hv' hvs
      change (decode a v).bind (fun y =>
        (decodeList a vs).bind (fun tail => some (y :: tail))) = some (x :: xs)
      rw [ihv ha x hv', ihr ha xs hvs]
      simp only [Option.bind_some]

theorem decode_encode (a : Ast) (ha : a.WF) (x : El a) :
    decode a (encode a x) = some x :=
  roundtrip_all.1 a (encode a x) ha x rfl

/-- The union's forward law, stated for the member sum directly: under
discrimination, tag dispatch recovers the member that was encoded. -/
theorem decodeMembers_encodeMembers :
    ∀ (b : Bool) (ms : List Ast), discriminatedB ms = true → WFMembers ms →
      ∀ (x : cond b (ElMembers ms) Empty),
        decodeMembers b ms (encodeMembers b ms x) = some x :=
  fun b ms hd hwf x =>
    roundtrip_all.2.1 b ms (encodeMembers b ms x) hd hwf x rfl

theorem decodeFields_encodeFields :
    ∀ (fs : List (String × Bool × Ast)),
      (fs.map (fun f => f.1)).Nodup → WFFields fs → ∀ (x : ElFields fs),
        decodeFields fs (encodeFields fs x) = some x :=
  fun fs hnd hwf x => roundtrip_all.2.2.1 fs (encodeFields fs x) hnd hwf x rfl

theorem decodeList_encodeList : ∀ (a : Ast), a.WF → ∀ (xs : List (El a)),
    decodeList a (xs.map (encode a)) = some xs :=
  fun a ha xs => roundtrip_all.2.2.2 a (xs.map (encode a)) ha xs rfl

end Cas.Schema
