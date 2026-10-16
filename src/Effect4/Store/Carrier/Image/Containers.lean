module

public import Effect4.Store.Carrier.Image.Record

/-! Disjoint constructor images for sums and explicit errors. These are codecs, not
new membership rules for the program's error type. -/

@[expose] public section
namespace Effect4.Store.Image
variable {α β : Type}

def ofSum (I : Image α) (J : Image β) : Val → Option (Sum α β)
  | .ctor 0 [v] => Sum.inl <$> I.ofVal v
  | .ctor 1 [v] => Sum.inr <$> J.ofVal v
  | _ => none

def sum (I : Image α) (J : Image β) : Image (Sum α β) where
  toVal
    | .inl a => .ctor 0 [I.toVal a]
    | .inr b => .ctor 1 [J.toVal b]
  ofVal := ofSum I J
  ofVal_toVal a := by
    cases a <;> simp [ofSum, I.ofVal_toVal, J.ofVal_toVal]
  ofVal_exact := by
    intro v a h
    unfold ofSum at h
    split at h
    · next v =>
      cases hv : I.ofVal v with
      | none => simp [hv] at h
      | some x =>
        simp [hv] at h
        subst a
        rw [I.ofVal_exact hv]
    · next v =>
      cases hv : J.ofVal v with
      | none => simp [hv] at h
      | some x =>
        simp [hv] at h
        subst a
        rw [J.ofVal_exact hv]
    · exact nomatch h

/-! ### The untagged union

`Ty.union a b` has no tag frame: its member is a member of either side (`Val.hasTy`). So its
carrier is the values of a sum that exactly one side reads, and its image writes the side's own
value. For a union whose sides carry distinct `_tag` literals every value is one, so the carrier is
the whole sum (`Schema.Modeled`'s sum types). -/

/-- Whether exactly one side reads a value of the sum: the other side's reader refuses its image. -/
def unambiguous (I : Image α) (J : Image β) : Sum α β → Bool
  | .inl a => (J.ofVal (I.toVal a)).isNone
  | .inr b => (I.ofVal (J.toVal b)).isNone

/-- A value of the sum as the side's own value. -/
def unionVal (I : Image α) (J : Image β) : Sum α β → Val
  | .inl a => I.toVal a
  | .inr b => J.toVal b

/-- The side that alone reads a value. -/
def ofUnionSum (I : Image α) (J : Image β) (v : Val) : Option (Sum α β) :=
  match I.ofVal v, J.ofVal v with
  | some a, none => some (.inl a)
  | none, some b => some (.inr b)
  | _, _ => none

theorem ofUnionSum_unionVal (I : Image α) (J : Image β) (s : Sum α β)
    (h : unambiguous I J s = true) : ofUnionSum I J (unionVal I J s) = some s := by
  cases s with
  | inl a =>
    cases hj : J.ofVal (I.toVal a) with
    | none =>
      show (match I.ofVal (I.toVal a), J.ofVal (I.toVal a) with
        | some a, none => some (Sum.inl a)
        | none, some b => some (Sum.inr b)
        | _, _ => none) = some (Sum.inl a)
      rw [I.ofVal_toVal, hj]
    | some _ =>
      have hn : (J.ofVal (I.toVal a)).isNone = true := h
      rw [hj] at hn
      exact nomatch hn
  | inr b =>
    cases hi : I.ofVal (J.toVal b) with
    | none =>
      show (match I.ofVal (J.toVal b), J.ofVal (J.toVal b) with
        | some a, none => some (Sum.inl a)
        | none, some b => some (Sum.inr b)
        | _, _ => none) = some (Sum.inr b)
      rw [hi, J.ofVal_toVal]
    | some _ =>
      have hn : (I.ofVal (J.toVal b)).isNone = true := h
      rw [hi] at hn
      exact nomatch hn

theorem ofUnionSum_exact (I : Image α) (J : Image β) {v : Val} {s : Sum α β}
    (h : ofUnionSum I J v = some s) : v = unionVal I J s := by
  unfold ofUnionSum at h
  split at h
  · next a ha _ =>
    injection h with h
    subst h
    exact I.ofVal_exact ha
  · next b _ hb =>
    injection h with h
    subst h
    exact J.ofVal_exact hb
  · exact nomatch h

/-- **The untagged union's image**: the sum's unambiguous values, each written as its side's. -/
def union (I : Image α) (J : Image β) : Image {s : Sum α β // unambiguous I J s = true} where
  toVal s := unionVal I J s.val
  ofVal v :=
    match ofUnionSum I J v with
    | some s => if h : unambiguous I J s = true then some ⟨s, h⟩ else none
    | none => none
  ofVal_toVal s := by
    show (match ofUnionSum I J (unionVal I J s.val) with
      | some t => if h : unambiguous I J t = true then some ⟨t, h⟩ else none
      | none => none) = some s
    rw [ofUnionSum_unionVal I J s.val s.property]
    show (if h : unambiguous I J s.val = true then
      some (⟨s.val, h⟩ : {t : Sum α β // unambiguous I J t = true}) else none) = some s
    rw [dif_pos s.property]
  ofVal_exact := by
    intro v s h
    split at h
    · next t ht =>
      split at h
      · next hu =>
        injection h with h
        subst h
        exact ofUnionSum_exact I J ht
      · exact nomatch h
    · exact nomatch h

theorem union_handleFree (I : Image α) (J : Image β) (hI : HandleFree I) (hJ : HandleFree J) :
    HandleFree (union I J) := by
  intro s
  obtain ⟨s, _⟩ := s
  cases s with
  | inl a => exact hI a
  | inr b => exact hJ b

def except (I : Image α) (J : Image β) : Image (Except α β) :=
  (sum I J).equiv
    (fun s => match s with | .inl a => .error a | .inr b => .ok b)
    (fun e => match e with | .error a => .inl a | .ok b => .inr b)
    (fun e => by cases e <;> rfl) (fun s => by cases s <;> rfl)

def ofTuple2 (I : Image α) (J : Image β) : Val → Option (α × β)
  | .list [a, b] =>
    match I.ofVal a, J.ofVal b with
    | some x, some y => some (x, y)
    | _, _ => none
  | _ => none

/-- The product under the frame `Val.hasTy` reads: `Val.tuple [a, b]`, which is `Program.Native`'s
own spelling (`Native.lean:33`). Built from the same two element images and the same two laws;
no new codec class. -/
def tuple2 (I : Image α) (J : Image β) : Image (α × β) where
  toVal p := .list [I.toVal p.1, J.toVal p.2]
  ofVal := ofTuple2 I J
  ofVal_toVal p := by
    show (match I.ofVal (I.toVal p.1), J.ofVal (J.toVal p.2) with
      | some x, some y => some (x, y)
      | _, _ => none) = some p
    rw [I.ofVal_toVal, J.ofVal_toVal]
  ofVal_exact := by
    intro v p h
    unfold ofTuple2 at h
    split at h
    · next a b =>
      split at h
      · next x y hx hy =>
        injection h with h
        subst h
        show Val.list [a, b] = Val.list [I.toVal x, J.toVal y]
        rw [I.ofVal_exact hx, J.ofVal_exact hy]
      · exact nomatch h
    · exact nomatch h

/-- Flat tuple items reuse the exact value column, without record names.
A helper of step-language-sound, consumed by the tuple carrier and Step.tuple3. -/
def tupleColumns {ρ : Type} (R : Effect4.Store.Columns ρ) : Image ρ where
  toVal x := .list (R.toVals x)
  ofVal
    | .list vs => R.ofVals vs
    | _ => none
  ofVal_toVal x := R.ofVals_toVals x
  ofVal_exact := by
    intro v x h
    cases v with
    | list vs => exact congrArg Val.list (R.ofVals_exact h)
    | _ => nomatch h

end Effect4.Store.Image
