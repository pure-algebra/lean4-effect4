import Effect4.Run.LiveRecord
import Effect4.Laws.Api.LiveRecord
import Tools.Session

/-!
# Test.Program.LiveRecordControls — acceptance controls for slice E (persistent keyed live sessions)

Controls from `docs/research/2026-10-17-proof-scout/README.md` §7.5 and `probes/E.lean`:

1. Case 10: two calls of one hole row; the row selector is unresolved, and the exact key answers
   one call while the other waits.
2. Case 11: the half-answered session saves and restores to the same journal, phases and waiting
   calls; its record round-trips through canonical bytes.
3. A record with an unknown format version is refused by `restore`.
4. `load` replaces the tool's live session: `liveView` then shows the restored session's waiting
   calls only, with their keys and checked instances.
-/

set_option autoImplicit false

namespace Test.Program.LiveRecordControls

open Effect4 Effect4.Machine Effect4.Program Effect4.Store
open Effect4.Api.Runner (Command)
open Tools.Session (State Request answer)
open Tools.JsonBridge (toHex printJson)

def opts : Supervision.ForkOptions :=
  { daemon := false, startImmediately := true, maskMode := .inherit }

def pairSketch : Sketch :=
  { program := .bind (.withFiber (.fork (Sketch.hole {} 0) opts))
      (.bind (.withFiber (.fork (Sketch.hole {} 0) opts))
        (.bind (.awaitFiber (.var 0) .awaitValue) (.awaitFiber (.var 1) .awaitValue))),
    holes := [Row.hole "h" .nat] }

def pairApp : SigApp := ({} : SigApp).withHoles pairSketch.holes

def pairLive : Option Live :=
  match admitProgram pairSketch.program pairApp with
  | .ok admitted => some (Live.open ⟨pairApp, pairSketch.program, admitted, [("h", 0)]⟩ "multi")
  | .error _ => none

def started : Option Live := pairLive.map fun l => (l.feed .start).1
def okAns (n : Nat) : Api.HostSession.Answer := .ofExit (.success (.nat n))

-- The checked sketch starts at its full application, and both children wait on the row.
#guard pairLive.isSome
#guard (started.map fun l => (Run.live l.run).length) = some 2

-- Control 1a (Case 10, red): the row names two live calls, so a reply by row is refused as unresolved.
#guard (started.map fun l => (l.feed (.receive (.row "h") (okAns 5))).2) =
  some (.unresolved (.row "h"))

-- Control 1b (Case 10, green twin): the exact key of the first call takes its reply, and the second call keeps waiting.
def firstKey : Option Api.HostSession.Key :=
  started.bind fun l => (Run.live l.run).head?.map (·.key)
def afterFirst : Option Live := started.bind fun l => firstKey.map fun k =>
  l.feedAll [.receive (.key k) (okAns 5), .apply (.key k), .flush]
#guard (afterFirst.map fun l => (Run.live l.run).length) = some 1
#guard (afterFirst.bind fun l => firstKey.map fun k => (Run.live l.run).any (·.key == k)) =
  some false

-- Control 2a (Case 11): the record of the half-answered session restores to the same journal, phases and waiting calls.
#guard (afterFirst.map fun l => match LiveRecord.restore (LiveRecord.save l) with
  | .ok l' => l'.run.journal == l.run.journal && l'.run.phases == l.run.phases &&
      (Run.live l'.run).length == 1
  | .error _ => false) = some true

-- Control 2b (Case 11): the record round-trips through canonical bytes (`LiveRecord.encode` / `LiveRecord.decode`).
#guard (afterFirst.map fun l =>
  let r := LiveRecord.save l
  match LiveRecord.decode (LiveRecord.encode r) with
  | some r' => r'.version == r.version && r'.session == r.session && r'.journal == r.journal &&
      r'.rowNames == r.rowNames
  | none => false) = some true

-- Control 3: a record with an unknown format version is refused by `restore`.
#guard (afterFirst.map fun l =>
  let r := { LiveRecord.save l with version := 99 }
  match LiveRecord.restore r with
  | .error why => why == .unsupportedVersion 99
  | .ok _ => false) = some true

-- Control 4: `Tools.Session` `start`, `receive` by row (unresolved) and by key, `save`, and `load` replacing the live session.
#guard
  let r0 := answer {}
    { op := "open", program := some (toHex pairSketch.program),
      holes := some (toHex pairSketch.holes) }
  let rStart := answer r0.1 { op := "start" }
  let wait2 := (rStart.1.live.map fun l => (Run.live l.run).length) == some 2
  -- receiving by rowName is refused as unresolved
  let rRow := answer rStart.1 { op := "receive", rowName := some "h", answer := some (toHex (okAns 5)) }
  -- receiving and applying by the first call's key (fiber 1, token 0) succeeds and leaves 1 call waiting
  let rRec1 := answer rStart.1
    { op := "receive", fiber := some 1, token := some 0, answer := some (toHex (okAns 5)) }
  let rApp1 := answer rRec1.1 { op := "apply", fiber := some 1, token := some 0 }
  let wait1 := (rApp1.1.live.map fun l => (Run.live l.run).length) == some 1
  -- save the half-answered session
  let rSave := answer rApp1.1 { op := "save", hex := true }
  let savedHex := (rSave.2.result.getObjValAs? String "record").toOption
  -- start a fresh session with 2 waiting calls, then load the saved record: `load` replaces the live session so `liveView` shows 1 waiting call
  let rStart2 := answer rApp1.1 { op := "start" }
  let rLoad := answer rStart2.1 { op := "load", record := savedHex }
  let rView := answer rLoad.1 { op := "liveView" }
  let waitAfterLoad :=
    (rLoad.1.live.map fun l =>
      l.view.awaiting.map fun c => (c.await.fiber.value, c.checked.isSome)) == some [(2, true)] &&
    rView.2.result.getObjValD "outcome" == printJson Api.Outcome.frontier
  rStart.2.ok && wait2 && !rRow.2.ok && rRec1.2.ok && rApp1.2.ok && wait1 &&
    rSave.2.ok && rLoad.2.ok && rView.2.ok && waitAfterLoad

end Test.Program.LiveRecordControls
