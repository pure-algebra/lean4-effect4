import Test.Dogfood.Scenario.Timeout

/-! Scratch: a bounded search against `cleanupKeeps`, and a machine-level construction that
breaks it with direct answers that no run can send. A finite probe. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 0

open Effect4 Effect4.Machine Effect4.Program Effect4.Program.Authoring Test.Dogfood.Scenario
open Test.Dogfood.Scenario.Timeout
open Test.Dogfood.P1HttpCache (retryable)

namespace Scratch.SearchTimeout

def keepsOnly (s : Run) : Bool := (observe s).cleanupKeeps

abbrev NEvent := RunEvent EffName EffThunk Val Err Defect FiberId Ann Ctx

def onExitPushOn (f : FiberId) (q : List Nat) : NEvent → Bool
  | .frame g (.pushed (.onExit _ (.fin p) _)) => g == f && p.path == q
  | _ => false

def finStartOn (f : FiberId) (q : List Nat) : NEvent → Bool
  | .finalizerProgram g (.fin p) _ => g == f && p.path == q
  | .frame g (.ranFinalizer (.fin p) _) => g == f && p.path == q
  | _ => false

/-- The attempt's fork site and its `onExit`'s path. -/
def site : List Nat := [1, 1, 0, 0, 1, 0, 0, 0, 0]
def attemptExit : List Nat := [1, 1, 0, 0, 1, 0, 0, 0, 0, 0]

def forkedAt (m : Api.Machine) (s : List Nat) : List FiberId :=
  (m.forks.filter (·.site == s)).map (·.child)

/-- The per-fiber planned goal: each attempt fiber pushes its `onExit` at most once and starts
its finalizer at most once. -/
def planned (s : Run) : Bool :=
  let tr := s.machine.trace
  (forkedAt s.machine site).all fun f =>
    decide (tr.countP (onExitPushOn f attemptExit) ≤ 1) &&
    decide (tr.countP (finStartOn f attemptExit) ≤ 1)

/-- The attempts' order: every attempt fiber but the last forked has exited. -/
def ordered (s : Run) : Bool :=
  (forkedAt s.machine site).dropLast.all fun f =>
    ((s.machine.fiber? f).bind (·.exit)).isSome

def keeps (s : Run) : Bool := keepsOnly s && planned s && ordered s

def firstBad (check : Run → Bool) (s : Run) (moves : List Move) : Option Nat :=
  (moves.foldl (fun (acc : Run × Nat × Option Nat) mv =>
    match acc.2.2 with
    | some n => (acc.1, acc.2.1, some n)
    | none =>
      let s' := Test.Dogfood.Scenario.step acc.1 mv
      (s', acc.2.1 + 1, if check s' then none else some (acc.2.1 + 1))) (s, 0, if check s then none else some 0)).2.2

def alphabet : List Move :=
  [ .start, .flush, .hold http
  , .receive http (ok body1), .receive http (failed "HttpError" "503")
  , .receive http (failed "Timeout" "x"), .receive http (failed "HttpError" "404"), .apply http
  , .tick 100, .tick 2000, .tick 100000
  , .cancel ⟨0⟩, .cancel ⟨1⟩, .cancel ⟨2⟩, .cancel ⟨5⟩
  , .row (.control (.yieldVerdict ⟨1⟩ true)), .row (.control (.evaluate ⟨1⟩))
  , .row (.control (.interruptFrom (some ⟨0⟩) .empty ⟨1⟩)) ]

def scripts : Nat → List (List Move)
  | 0 => [[]]
  | n + 1 => (scripts n).flatMap fun ms => alphabet.map fun mv => ms ++ [mv]

def build? (m : Module NativeOp) : Option Api.Built := (Effect4.Api.Author.build m).toOption

def search (b : Api.Built) (base : List Move) (depth : Nat) : Nat × Nat × Option (List Move) :=
  let s0 := Test.Dogfood.Scenario.play (opened b) base
  (scripts depth).foldl (fun (acc : Nat × Nat × Option (List Move)) ms =>
    match firstBad keeps s0 ms with
    | none => (acc.1 + 1, acc.2.1, acc.2.2)
    | some _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some ms)) (0, 0, none)

/-! ### The machine level, with direct answers -/

/-- `cleanupKeeps`'s reading at a machine: the count cell and the cleanup log. -/
def keepsAt (m : Api.Machine) : Bool :=
  let attempts := match (m.state.refs[0]? : Option Val) with
    | some (.nat n) => n
    | _ => 0
  let cleaned := (match (m.state.refs[1]? : Option Val) with
    | some (.list es) => es
    | _ => []).filterMap fun (v : Val) =>
      match v with
      | .list [.nat a, _] => some a
      | _ => none
  cleaned == (List.range cleaned.length).map (· + 1) && decide (cleaned.length ≤ attempts) &&
    decide (attempts ≤ cleaned.length + 1)

def attemptsAt (m : Api.Machine) : Nat :=
  match (m.state.refs[0]? : Option Val) with
  | some (.nat n) => n
  | _ => 0

/-- The guard token the root is parked on. -/
def rootToken (m : Api.Machine) : Option Nat :=
  match m.fiber? ⟨0⟩ with
  | some f =>
    match f.parked with
    | .withGuard t => some t
    | _ => none
  | none => none

/-- A direct answer to the root's park: a decision that no run hands the machine. -/
def answerRoot (b : Api.Built) (m : Api.Machine) (answer : Api.HostSession.Answer) : Api.Machine :=
  match rootToken m with
  | some t => steppedBy b.program 2000 b.table m (.answerAsync ⟨0⟩ t answer)
  | none => m

def orderedAt (m : Api.Machine) : Bool :=
  (forkedAt m site).dropLast.all fun f => ((m.fiber? f).bind (·.exit)).isSome

def fiberState (m : Api.Machine) (id : Nat) : String :=
  match m.fiber? ⟨id⟩ with
  | some f => s!"running {f.running}, exited {f.exit.isSome}, parked {f.parked != .notParked}"
  | none => "none"

def timed (label : String) (f : Unit → String) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{label}: {r}"
  let t1 ← IO.monoMsNow
  IO.println s!"  ({t1 - t0} ms)"

#eval show IO Unit from do
  match build? fetch, build? (client retryable true) with
  | some b, some resetting =>
    timed "depth 4 from parked" fun _ =>
      let (n, bad, ex) := search b parked 4
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "depth 3 from parked" fun _ =>
      let (n, bad, ex) := search b parked 3
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "depth 3 from timed-out" fun _ =>
      let (n, bad, ex) := search b timedOut 3
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "depth 3 from the open program" fun _ =>
      let (n, bad, ex) := search b [] 3
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "red control, the finalizer that resets the count: depth 2 from parked" fun _ =>
      let (n, bad, ex) := search resetting parked 2
      s!"{n} scripts, {bad} failing, first {repr (ex.map (·.length))}"
    timed "fuel 1..200 on four scripts, every run checked" fun _ =>
      let scriptsOf : List (List Move) :=
        [ timedOut ++ answer second (ok body2)
        , [.start, .tick 2000, .tick 100, .tick 2000, .tick 200, .tick 2000, .tick 400, .tick 2000]
        , parked ++ [.cancel ⟨1⟩, .flush, .tick 2000, .tick 100]
        , parked ++ answer http (failed "HttpError" "503") ++ [.tick 100, .hold http] ++ answer http (ok body2) ]
      let (n, bad, ex) := (List.range 200).foldl (fun (acc : Nat × Nat × Option (Nat × Nat)) f =>
        (scriptsOf.zipIdx).foldl (fun (acc : Nat × Nat × Option (Nat × Nat)) (ms, i) =>
          let s0 := Run.open b "timeout" { budget with fuel := f + 1 }
          match firstBad keeps s0 ms with
          | none => (acc.1 + 1, acc.2.1, acc.2.2)
          | some _ => (acc.1 + 1, acc.2.1 + 1, acc.2.2.orElse fun _ => some (f + 1, i))) acc) (0, 0, none)
      s!"{n} runs, {bad} failing, first {repr ex}"
    -- the machine level: attempt 1 parked on its host call, then its reply applied at a small
    -- budget, which a run can do (`.apply` at a run's budget)
    let m0 := Api.load b.program budget.compileFuel
    let m1 := steppedBy b.program 2000 b.table m0 (.evaluate Api.root)
    let tokenOf := fun (m : Api.Machine) (id : Nat) =>
      match m.fiber? ⟨id⟩ with
      | some g =>
        match g.parked with
        | .withGuard t => some t
        | _ => none
      | none => none
    IO.println s!"after start: attempts {attemptsAt m1}, fiber 0 {fiberState m1 0}, fiber 1 {fiberState m1 1}, host token {repr (tokenOf m1 1)}"
    match tokenOf m1 1 with
    | none => IO.println "attempt 1 is not parked"
    | some t =>
      let applied := fun (f : Nat) =>
        steppedBy b.program f b.table m1 (.answerAsync ⟨1⟩ t (Completion.ofExit (.success body1)))
      let cut := (List.range 200).find? fun f =>
        let m2 := applied f
        (match m2.fiber? ⟨1⟩ with
          | some g => g.running && g.exit.isNone
          | none => false) && (match (m2.state.refs[1]? : Option Val) with
          | some (.list []) => true
          | _ => false) && (rootToken m2).isSome
      IO.println s!"an application budget that leaves attempt 1 running, uncleaned, with the root parked: {repr cut}"
      match cut with
      | none => IO.println "no such budget"
      | some f =>
        let m2 := applied f
        IO.println s!"cut machine: attempts {attemptsAt m2}, fiber 0 {fiberState m2 0}, fiber 1 {fiberState m2 1}, root token {repr (rootToken m2)}"
        -- green: the run's own decisions from the cut machine
        let g1 := steppedBy b.program 2000 b.table m2 (.advance (ClockMillis.ofNat 2000))
        let g2 := steppedBy b.program 2000 b.table g1 .flush
        let g3 := steppedBy b.program 2000 b.table g2 (.advance (ClockMillis.ofNat 100))
        let g4 := steppedBy b.program 2000 b.table g3 .flush
        IO.println s!"green, run decisions only: keeps {[m2, g1, g2, g3, g4].map keepsAt}, ordered {[m2, g1, g2, g3, g4].map orderedAt}, attempts {[m2, g1, g2, g3, g4].map attemptsAt}, root {fiberState g4 0}, root token {repr (rootToken g4)}"
        -- red: from g1 (the root parked on its join of attempt 1), a direct answer
        let r1 := answerRoot b g1 (Completion.ofExit (.success .unit))
        let r2 := steppedBy b.program 2000 b.table r1 .flush
        let r3 := steppedBy b.program 2000 b.table r2 (.advance (ClockMillis.ofNat 100))
        let r4 := steppedBy b.program 2000 b.table r3 .flush
        IO.println s!"red, a direct answer to the root's join: keeps {[g1, r1, r2, r3, r4].map keepsAt}, ordered {[g1, r1, r2, r3, r4].map orderedAt}, attempt fibers {repr (forkedAt r4 site)}, attempts {[g1, r1, r2, r3, r4].map attemptsAt}, root tokens {[g1, r1, r2, r3, r4].map rootToken}, cleaned {repr (r4.state.refs[1]?)}, attempt 1 {fiberState r4 1}"
  | _, _ => IO.println "no build"

end Scratch.SearchTimeout
