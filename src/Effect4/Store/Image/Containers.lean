import Effect4.Store.Image

/-! Disjoint constructor images for sums and explicit errors. These are codecs, not
new membership rules for the program's error type. -/
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


end Effect4.Store.Image
