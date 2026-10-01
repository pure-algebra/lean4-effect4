import Effect4.Laws.Program.Typed.Assembly

/-! Scouting only (no claims): the answer each store row actually gives, beside the shape its
`storePost` (`Typed/Residual.lean:56-82`) admits. -/
open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Sched Effect4.Program.Typed

/-- A store with one ref holding 5, one empty deferred, one open sequential scope (key 0). -/
def st0 : Stores :=
  let s1 := (syncOpStep (.refMake (.nat 5)) Stores.empty).map (·.1) |>.getD Stores.empty
  let s2 := (syncOpStep .deferredMake s1).map (·.1) |>.getD s1
  (syncOpStep (.scopeMake .sequential) s2).map (·.1) |>.getD s2

def shape : Val → String
  | .unit => "unit" | .nat _ => "nat" | .bool _ => "bool" | .str _ => "str"
  | v => s!"other {(repr v).pretty.take 60}"

def ops : List (String × SyncOp) :=
  [("refMake", .refMake (.nat 1)), ("refGet", .refGet ⟨0⟩), ("refSet", .refSet ⟨0⟩ (.nat 7)),
   ("refGetAndSet", .refGetAndSet ⟨0⟩ (.nat 7)), ("refSetAndGet", .refSetAndGet ⟨0⟩ (.nat 7)),
   ("refUpdate", .refUpdate ⟨0⟩ .incr), ("refGetAndUpdate", .refGetAndUpdate ⟨0⟩ .incr),
   ("refUpdateAndGet", .refUpdateAndGet ⟨0⟩ .incr), ("refUpdateSome", .refUpdateSome ⟨0⟩ .zeroWhenPositive),
   ("refModify", .refModify ⟨0⟩ .incr),
   ("deferredMake", .deferredMake), ("deferredIsDone", .deferredIsDone ⟨0⟩),
   ("deferredPoll", .deferredPoll ⟨0⟩),
   ("deferredCompleteWith", .deferredCompleteWith ⟨0⟩ (.ofExit (.success .unit))),
   ("deferredAwaitCleanup", .deferredAwaitCleanup ⟨0⟩ ⟨0⟩ 0),
   ("clockNow", .clockNow), ("sleepCancel", .sleepCancel ⟨0⟩ 0),
   ("scopeMake", .scopeMake .sequential), ("scopeAdd", .scopeAdd 0 (.closeChildScope 9)),
   ("scopeRemove", .scopeRemove 0 1), ("scopeIsClosed", .scopeIsClosed 0),
   ("scopeFork", .scopeFork 0 .sequential)]

#eval ops.map fun (name, op) =>
  match syncOpStep op st0 with
  | none => s!"{name}: frontier"
  | some (_, v) => s!"{name}: {shape v}"
