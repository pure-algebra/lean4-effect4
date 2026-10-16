import Effect4.Author
open Effect4 Effect4.Schema

namespace Probe.ModeledLower

/-- The to-do's record, one Lean structure that is also its `Ty`. -/
structure Todo where
  id : Nat
  title : String
  done : Bool
deriving Modeled

/-- A sum: a union of tagged records. -/
inductive Status where
  | pending
  | closed (reason : String)
deriving Modeled

def encodeTodo (t : Todo) : Store.Val := (Modeled.image Todo).toVal t
def decodeTodo (v : Store.Val) : Option Todo := (Modeled.image Todo).ofVal v
def encodeStatus (s : Status) : Store.Val := (Modeled.image Status).toVal s
def decodeStatus (v : Store.Val) : Option Status := (Modeled.image Status).ofVal v
def encodeTodos (ts : List Todo) : Store.Val := (Modeled.image (List Todo)).toVal ts

#eval decodeTodo (encodeTodo ⟨3, "milk", false⟩) |>.map (·.title)
#eval (decodeStatus (encodeStatus (.closed "done"))).isSome

/-! ## The first-order codec a deriver would write -/

def todoToVal (t : Todo) : Store.Val :=
  .ctor 0 [.list [.str "done", .str "id", .str "title"], .list [.bool t.done, .nat t.id, .str t.title]]

def todoOfVal : Store.Val → Option Todo
  | .ctor 0 [.list [.str "done", .str "id", .str "title"], .list [.bool d, .nat i, .str s]] =>
    some ⟨i, s, d⟩
  | _ => none

def statusToVal : Status → Store.Val
  | .pending => .ctor 0 [.list [.str "_tag"], .list [.str "pending"]]
  | .closed r => .ctor 0 [.list [.str "_tag", .str "reason"], .list [.str "closed", .str r]]

/-- The first-order writer is the fold's writer, by definition. -/
theorem todoToVal_eq (t : Todo) : todoToVal t = (Modeled.image Todo).toVal t := rfl

#eval [todoOfVal (encodeTodo ⟨3, "milk", false⟩) |>.map (·.title),
  decodeTodo (todoToVal ⟨4, "eggs", true⟩) |>.map (·.title)]
#eval (encodeStatus (.closed "x")) == statusToVal (.closed "x")
#eval (encodeStatus .pending) == statusToVal .pending

end Probe.ModeledLower
