import Test.Dogfood.Scenario.Timeout

/-! A bounded search for `retries_declared` with a richer control alphabet than the seat's.
From the parked state with the first reply applied (or only received, or nothing), it plays
every word of length at most 3 over the scheduling moves, then a fixed tail that lets a second
attempt start and be held. It prints each failing word. A finite probe, not a proof. -/

open Effect4 Effect4.Machine Test.Dogfood.Scenario Test.Dogfood.Scenario.Timeout

set_option maxRecDepth 8192
set_option maxHeartbeats 0

def built : Option Api.Built := (Effect4.Api.Author.build fetch).toOption

def moveStr : Move → String
  | .control (.fire f) => s!"fire {f.value}"
  | .control (.evaluate f) => s!"eval {f.value}"
  | .control (.yieldVerdict f b) => s!"yield {f.value} {b}"
  | .control (.interruptFrom _ _ f) => s!"cancel {f.value}"
  | .control (.advance _) => "tick"
  | .control .flush => "flush"
  | .control _ => "control"
  | .hold _ => "hold"
  | .receive _ _ => "receive"
  | .apply _ => "apply"
  | .row _ => "row"

/-- The scheduling alphabet: fire, evaluate and a yield verdict at each of nine fibers, the
interruption of each, and the clock steps. -/
def alphabet : List Move :=
  (List.range 9).flatMap (fun k =>
    [Move.control (.fire ⟨k⟩), Move.control (.evaluate ⟨k⟩),
     Move.control (.yieldVerdict ⟨k⟩ true), Move.cancel ⟨k⟩]) ++
  [Move.flush, Move.tick 100, Move.tick 2000]

def words : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet.flatMap fun m => (words n).map (m :: ·))

def tail : List Move := [.tick 2000, .tick 100, .tick 200, .flush, .hold http]

def search (start : List Move) (len : Nat) : List String :=
  match built with
  | none => ["no build"]
  | some b =>
    let s0 := Test.Dogfood.Scenario.play (opened b) start
    ((words len).filterMap fun w =>
      let s := Test.Dogfood.Scenario.play s0 (w ++ tail)
      if (observe s).retriesDeclared then none else some (String.intercalate ", " (w.map moveStr)))

/-- Words over the alphabet with the reply's receipt and application in it. -/
def alphabet2 : List Move := alphabet ++ [.receive http (ok body1), .apply http]

def words2 : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet2.flatMap fun m => (words2 n).map (m :: ·))

def search2 (start : List Move) (len : Nat) : List String :=
  match built with
  | none => ["no build"]
  | some b =>
    let s0 := Test.Dogfood.Scenario.play (opened b) start
    ((words2 len).filterMap fun w =>
      let s := Test.Dogfood.Scenario.play s0 (w ++ tail)
      if (observe s).retriesDeclared then none else some (String.intercalate ", " (w.map moveStr)))

-- from the parked state, with the reply in the alphabet
#eval (search2 parked 3).take 60
#eval (search2 parked 3).length
