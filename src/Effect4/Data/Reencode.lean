module

/-!
# Data.Reencode — a reader made exact by re-encoding what it read

The re-encode guard. From a writer `write : α → β` and any candidate reader `read`, `guard` reads
the normal form of its input and keeps the answer only when the writer's image of that answer has
the same normal form. So what it answers is its input modulo `norm`, whatever `read` does
(`guard_exact`). It reads its input only through the normal form (`guard_congr`). It answers on a
writer image whenever `read` inverts the writer there (`guard_image`). A reader built this way is
an exact embedding modulo `norm` once `read` is a left inverse on the image: totality on the
domain is the one obligation left to the carrier. The price is one re-encoding per read.

Two uses, one construction:

- the store's `guarded` (`Effect4/Store/Domain/Canonical.lean`): the value tree, no normaliser,
  an anonymous refusal; the generated `Canonical` instances of recursive families read through it;
- the persisted-document reader (`Effect4/Schema/DocumentJson.lean`): JSON modulo `normJ`, with a
  located refusal.
-/

@[expose] public section

namespace Effect4.Reencode

/-- **The re-encode guard**: read the normal form of `v`, and keep the answer only when the
writer's image of it has that same normal form; otherwise refuse with `miss`. A refusal of `read`
is passed through. -/
def guard {α β ε : Type} [DecidableEq β] (norm : β → β) (write : α → β)
    (read : β → Except ε α) (miss : ε) (v : β) : Except ε α :=
  match read (norm v) with
  | .ok a => if norm (write a) = norm v then .ok a else .error miss
  | .error e => .error e

/-- **Exactness**: what the guard answers is its input, modulo `norm`. -/
theorem guard_exact {α β ε : Type} [DecidableEq β] {norm : β → β} {write : α → β}
    {read : β → Except ε α} {miss : ε} {v : β} {a : α}
    (h : guard norm write read miss v = .ok a) : norm v = norm (write a) := by
  unfold guard at h
  split at h
  · split at h
    · next heq =>
      injection h with h
      subst h
      exact heq.symm
    · exact nomatch h
  · exact nomatch h

/-- The guard reads its input only through its normal form. -/
theorem guard_congr {α β ε : Type} [DecidableEq β] {norm : β → β} {write : α → β}
    {read : β → Except ε α} {miss : ε} {v v' : β} (h : norm v = norm v') :
    guard norm write read miss v = guard norm write read miss v' := by
  simp only [guard, h]

/-- **The image is answered** when `read` inverts the writer on its normal form: the left-inverse
obligation a carrier discharges to make the guarded reader total on its domain. -/
theorem guard_image {α β ε : Type} [DecidableEq β] {norm : β → β} {write : α → β}
    {read : β → Except ε α} {miss : ε} {a a' : α} (hread : read (norm (write a)) = .ok a')
    (himage : norm (write a') = norm (write a)) : guard norm write read miss (write a) = .ok a' := by
  simp only [guard, hread, himage, ↓reduceIte]

end Effect4.Reencode
