import Test.Dogfood.Scenario.Atomic

/-! Scratch: a bounded search for a request that stands twice in the shop's cleanup log. A finite
probe at the battery's budgets; every prefix of every script is checked. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Test.Dogfood.Scenario
open Test.Dogfood.Scenario.Atomic

namespace Scratch.SearchAtomic

def onceOnly (s : Run) : Bool := decide (observe s).cleaned.Nodup

abbrev NEvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

def onExitPushAt (q : List Nat) : NEvent → Bool
  | .frame _ (.pushed (.onExit _ (.fin p) _)) => p.path == q
  | _ => false

def finStartAt (q : List Nat) : NEvent → Bool
  | .finalizerProgram _ (.fin p) _ => p.path == q
  | .frame _ (.ranFinalizer (.fin p) _) => p.path == q
  | _ => false

def shopRequest : Nat → List Nat
  | 1 => [1, 1, 1, 1, 0, 0, 0]
  | 2 => [1, 1, 1, 1, 1, 0, 0, 0]
  | 3 => [1, 1, 1, 1, 1, 1, 0, 0, 0]
  | 4 => [1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  | 5 => [1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]
  | _ => [1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0]

/-- The planned goals' inequalities for the six requests. -/
def planned (s : Run) : Bool :=
  let tr := s.machine.trace
  let cleaned := (observe s).cleaned
  cleaned.all (fun i => [1, 2, 3, 4, 5, 6].contains i) &&
  [1, 2, 3, 4, 5, 6].all fun i =>
    decide (tr.countP (finStartAt (shopRequest i)) ≤ tr.countP (onExitPushAt (shopRequest i))) &&
    decide (tr.countP (onExitPushAt (shopRequest i)) ≤ 1) &&
    decide (cleaned.count i ≤ tr.countP (finStartAt (shopRequest i)))

def once (s : Run) : Bool := onceOnly s && planned s

def firstBad (check : Run → Bool) (s : Run) (moves : List Move) : Option Nat :=
  (moves.foldl (fun (acc : Run × Nat × Option Nat) mv =>
    match acc.2.2 with
    | some n => (acc.1, acc.2.1, some n)
    | none =>
      let s' := Test.Dogfood.Scenario.step acc.1 mv
      (s', acc.2.1 + 1, if check s' then none else some (acc.2.1 + 1))) (s, 0, if check s then none else some 0)).2.2

/-- Fiber 0 is the root, fiber 1 the daemon, fibers 2 to 7 the requests 1 to 6. -/
def alphabet : List Move :=
  [ .start, .flush, .tick 500, .tick 1000
  , .cancel ⟨0⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .cancel ⟨3⟩, .cancel ⟨6⟩, .cancel ⟨7⟩
  , .row (.control (.yieldVerdict ⟨3⟩ true)), .row (.control (.evaluate ⟨3⟩))
  , .row (.control (.fire ⟨0⟩)), .row (.control (.interruptFrom (some ⟨2⟩) .empty ⟨3⟩))
  , .row (.control .installMiddleware) ]

def scripts : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => (scripts n).flatMap fun ms => alphabet.map fun mv => ms ++ [mv]

def build? (m : Module NativeOp) : Option Api.Built := (Effect4.Api.Author.build m).toOption

def search (b : Api.Built) (base : List Move) (depth : Nat) : Nat × Nat × Option (List Move) :=
  let s0 := Test.Dogfood.Scenario.play (opened b) base
  (scripts depth).foldl (fun (acc : Nat × Nat × Option (List Move)) ms =>
    match firstBad once s0 ms with
    | none => (acc.1 + 1, acc.2.1, acc.2.2)
    | some _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some ms)) (0, 0, none)

def timed (label : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{label}: {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  ({t1 - t0} ms)"

#eval show IO Unit from do
  match build? (shop .none), build? (shop .twice) with
  | some b, some faulty =>
    timed "depth 4 from the open program" fun _ =>
      let (n, bad, ex) := search b [] 4
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "depth 3 from started" fun _ =>
      let (n, bad, ex) := search b started 3
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "depth 3 from the root's start alone" fun _ =>
      let (n, bad, ex) := search b [.start] 3
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "red control, the finalizer that notes twice: depth 2 from the open program" fun _ =>
      let (n, bad, ex) := search faulty [] 2
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
  | _, _ => IO.println "no build"

end Scratch.SearchAtomic
