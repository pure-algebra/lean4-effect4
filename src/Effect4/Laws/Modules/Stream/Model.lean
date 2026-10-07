import Effect4.Machine.Value
import Effect4.Store.Carrier.Val

set_option autoImplicit false

namespace Effect4.Stream

open Effect4 Effect4.Machine Effect4.Store

/-- The cursor of one opened stream: what was gathered, and the leftover once the end arrived. -/
structure Cursor where
  acc : Val
  ended : Option Val

/-- The cursor's value: the pair that the loop carries. -/
def Cursor.val (c : Cursor) : Val :=
  .list [c.acc, match c.ended with | none => Store.Val.none | some l => Store.Val.some l]

/-- The model's step at the end. -/
def Cursor.finish (c : Cursor) (leftover : Val) : Cursor := { c with ended := some leftover }

/-- The model's step at a chunk, with the next accumulator. -/
def Cursor.gain (next : Val) : Cursor := { acc := next, ended := none }

/-- Whether the loop goes on: the test of the loop reads this. -/
def Cursor.live (c : Cursor) : Bool := c.ended.isNone

/-! ## The model of a whole loop

The model reads a list of pull answers, as the binding refines them: the end with its leftover,
or a chunk. It takes one step for each answer while the cursor is live. Three facts of the model
are the model's half of the three run statements. The machine's half is the planned goals. -/

/-- One pull's answer, as the binding refines it (`pulled?`, probe S1). -/
abbrev Pulled := Except Val (List Val)

/-- The model's step at one answer. -/
def Cursor.step (gain : Val → List Val → Val) (c : Cursor) : Pulled → Cursor
  | .error leftover => c.finish leftover
  | .ok chunk => Cursor.gain (gain c.acc chunk)

/-- **The model of the loop**: one step for each answer while the cursor is live. -/
def Cursor.drain (gain : Val → List Val → Val) : Cursor → List Pulled → Cursor
  | c, [] => c
  | c, a :: rest => if c.live then Cursor.drain gain (c.step gain a) rest else c

/-- The gain of `runCollect`: the chunk joins the gathered list at its end. -/
def collectGain (acc : Val) (chunk : List Val) : Val :=
  match acc with
  | .list xs => .list (xs ++ chunk)
  | other => other

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
