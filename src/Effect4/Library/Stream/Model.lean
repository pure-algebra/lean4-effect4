module
public import Effect4.Machine.Value
public import Effect4.Store.Carrier.Val

set_option autoImplicit false

@[expose] public section

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

end Effect4.Stream
