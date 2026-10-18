import Effect4.Run.LiveRecord
import Effect4.Laws.Api.LiveRecord
import Effect4.Tool.Serve
import Effect4.Tool.ToolDerived

/-!
# Test.Program.LiveRecordControls — acceptance controls for slice E (persistent keyed live sessions)

Controls from `docs/research/2026-10-17-proof-scout/README.md` §7.5 and `probes/E.lean`:

1. Case 10: two calls of one hole row; the row selector is unresolved, and the exact key answers
   one call while the other waits.
2. Case 11: the half-answered session saves and restores to the same journal, phases and waiting
   calls; its record round-trips through canonical bytes.
3. A record with an unknown format version is refused by `restore`.
4. The tool restores a record as a new run (`Tool.Action.restore`): its view shows the restored
   session's waiting call only, with its key and checked instance.
-/

set_option autoImplicit false

namespace Test.Program.LiveRecordControls

open Effect4 Effect4.Machine Effect4.Program Effect4.Store
open Effect4.Api.Runner (Command)

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

-- Control 2b (Case 11): the record round-trips through its generated canonical bytes.
#guard (afterFirst.map fun l =>
  let r := LiveRecord.save l
  match Store.Canonical.decode (α := LiveRecord) (Store.Canonical.encode r) with
  | some r' => r'.version == r.version && r'.session == r.session && r'.journal == r.journal &&
      r'.rowNames == r.rowNames
  | none => false) = some true

-- Control 3: a record with an unknown format version is refused by `restore`.
#guard (afterFirst.map fun l =>
  let r := { LiveRecord.save l with version := 99 }
  match LiveRecord.restore r with
  | .error why => why == .unsupportedVersion 99
  | .ok _ => false) = some true

-- Control 4: the tool's `start`, a play by row (unresolved) and by key, the run's record, and
-- `restore` adding a run whose view waits on the one call left.
#guard
  let serve1 (st : Tool.State) (r : Tool.Request) := (Tool.serve Check.Oracle.uncached st r).value
  let snap : Snap := ⟨⟨"multi", 0⟩, 0⟩
  let (s0, _) := serve1 Tool.empty (.act (.open_ "multi" {} pairSketch))
  let (s1, rStart) := serve1 s0 (.act (.start snap {}))
  let waiting (r : Tool.Reply) : Option Nat := match r.result with
    | .ok (.acted (.started _ _ view)) | .ok (.acted (.played _ _ view))
    | .ok (.acted (.restored _ view)) => some view.awaiting.length
    | _ => none
  -- a reply by row names two live calls, so the whole play is refused and the run is unchanged
  let (s2, rRow) := serve1 s1 (.act (.play ⟨0⟩ [.receive (.row "h") (okAns 5)]))
  -- the first call's key (fiber 1, token 0) takes its reply; one call keeps waiting
  let key : Api.HostSession.Key := ⟨⟨1⟩, 0⟩
  let (s3, rKey) := serve1 s2 (.act (.play ⟨0⟩ [.receive (.key key) (okAns 5), .apply (.key key)]))
  -- the half-answered run's record, a fresh start, then the record restored as a third run
  let (_, rRec) := serve1 s3 (.ask (.run ⟨0⟩ .record))
  let (s4, _) := serve1 s3 (.act (.start snap {}))
  match rRec.result with
  | .ok (.run _ (.record saved)) =>
    let (s5, rLoad) := serve1 s4 (.act (.restore saved))
    waiting rStart == some 2 && !rRow.result.isOk && s2.transcript.length == s1.transcript.length &&
      waiting rKey == some 1 && waiting rLoad == some 1 && s5.raw.runs.length == 3 &&
      (match rLoad.result with
       | .ok (.acted (.restored _ view)) =>
         view.awaiting.map (fun c => (c.await.fiber.value, c.checked.isSome)) == [(2, true)] &&
           view.outcome == Api.Outcome.frontier
       | _ => false)
  | _ => false

end Test.Program.LiveRecordControls
