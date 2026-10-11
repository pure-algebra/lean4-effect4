import Test.Dogfood.Scenario.Timeout

/-! A bounded search over scheduling words and host answers, for three properties of the timeout
observation: `retriesDeclared` on every word, `retriesDeclared` on the words a fair host plays
(no yield verdict, no interruption of a fiber other than the attempts' callers 1 and 5), and
`staleNeverApplies` on every word. It prints the counts and the first failing words. A finite
probe, not a proof. -/

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
  | .receive _ (.ofExit (.success _)) => "ok"
  | .receive _ _ => "fail"
  | .apply _ => "apply"
  | .row _ => "row"

/-- A fair host's move: no yield verdict, and an interruption only of an attempt's caller. -/
def fair : Move → Bool
  | .control (.yieldVerdict _ _) => false
  | .control (.interruptFrom _ _ f) => f.value == 1 || f.value == 5
  | _ => true

def alphabet : List Move :=
  (List.range 9).flatMap (fun k =>
    [Move.control (.fire ⟨k⟩), Move.control (.evaluate ⟨k⟩),
     Move.control (.yieldVerdict ⟨k⟩ true), Move.cancel ⟨k⟩]) ++
  [Move.flush, Move.tick 100, Move.tick 2000,
   .receive http (ok body1), .receive http (failed "NetworkError" "down"),
   .receive http (failed "HttpError" "404"), .receive http (failed "HttpError" "503"),
   .apply http, .hold http]

def words : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => [] :: (alphabet.flatMap fun m => (words n).map (m :: ·))

def tail : List Move := [.tick 2000, .tick 100, .tick 200, .tick 400, .flush, .hold http]

structure Tally where
  runs : Nat := 0
  retries : List String := []
  fairRetries : List String := []
  stale : List String := []

def search (start : List Move) (len : Nat) : Tally :=
  match built with
  | none => {}
  | some b =>
    let s0 := Test.Dogfood.Scenario.play (opened b) start
    (words len).foldl (fun (t : Tally) w =>
      let o := observe (Test.Dogfood.Scenario.play s0 (w ++ tail))
      let name := String.intercalate ", " (w.map moveStr)
      { runs := t.runs + 1
        retries := if o.retriesDeclared then t.retries else t.retries ++ [name]
        fairRetries := if o.retriesDeclared || !w.all fair then t.fairRetries
          else t.fairRetries ++ [name]
        stale := if o.staleNeverApplies then t.stale else t.stale ++ [name] }) {}

def report (label : String) (t : Tally) : String :=
  s!"{label}: {t.runs} words; retriesDeclared fails {t.retries.length}; on fair words \
    {t.fairRetries.length} {t.fairRetries.take 5}; staleNeverApplies fails {t.stale.length} \
    {t.stale.take 5}"

#eval report "parked, length 3" (search parked 3)
#eval report "timed out, length 2" (search timedOut 2)
#eval report "received, length 2" (search (parked ++ [.receive http (ok body1)]) 2)
