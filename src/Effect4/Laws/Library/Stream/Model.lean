import Effect4.Library.Stream.Model

/-!
# The stream cursor model's whole-loop laws

The cursor model stands in the core (`src/Effect4/Library/Stream/Model.lean`, decisions row 332).
Its laws stand here: after the end the model reads no answer, chunks gather in the order of the
pulls, and chunks then the end give the concatenation with the leftover.
-/

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Store

/-- **After the end the model reads no answer.** -/
theorem Cursor.drain_ended (gain : Val → List Val → Val) (c : Cursor) (h : c.live = false)
    (answers : List Pulled) : Cursor.drain gain c answers = c := by
  cases answers with
  | nil => rfl
  | cons a rest => rw [Cursor.drain, if_neg (by rw [h]; exact Bool.false_ne_true)]

/-- Chunks gather in the order of the pulls. -/
theorem Cursor.drain_chunks (xs : List Val) (chunks : List (List Val)) (rest : List Pulled) :
    Cursor.drain collectGain ⟨.list xs, none⟩ (chunks.map Except.ok ++ rest) =
      Cursor.drain collectGain ⟨.list (xs ++ chunks.flatten), none⟩ rest := by
  induction chunks generalizing xs with
  | nil => rw [List.map_nil, List.nil_append, List.flatten_nil, List.append_nil]
  | cons chunk chunks ih =>
    rw [List.map_cons, List.cons_append, Cursor.drain,
      if_pos (show (⟨.list xs, none⟩ : Cursor).live = true from rfl)]
    show Cursor.drain collectGain ⟨.list (xs ++ chunk), none⟩ (chunks.map Except.ok ++ rest) = _
    rw [ih, List.flatten_cons, List.append_assoc]

/-- **The model delivers each element once, in order, and the end is a state.** Chunks and then
the end give the concatenation with the leftover, whatever the host answers later. -/
theorem Cursor.collects (chunks : List (List Val)) (leftover : Val) (later : List Pulled) :
    Cursor.drain collectGain ⟨.list [], none⟩
        (chunks.map Except.ok ++ Except.error leftover :: later) =
      ⟨.list chunks.flatten, some leftover⟩ := by
  rw [Cursor.drain_chunks, List.nil_append, Cursor.drain,
    if_pos (show (⟨.list chunks.flatten, none⟩ : Cursor).live = true from rfl)]
  exact Cursor.drain_ended _ _ rfl _

-- finite evaluations of the model, and a red control: a gain that keeps the last chunk alone
#guard (Cursor.drain collectGain ⟨.list [], none⟩
    [.ok [.nat 1, .nat 2], .ok [.nat 3], .error .unit, .ok [.nat 9]]).val =
  .list [.list [.nat 1, .nat 2, .nat 3], Store.Val.some .unit]
#guard (Cursor.drain (fun _ chunk => .list chunk) ⟨.list [], none⟩
    [.ok [.nat 1, .nat 2], .ok [.nat 3], .error .unit]).val =
  .list [.list [.nat 3], Store.Val.some .unit]

end Effect4.Stream
