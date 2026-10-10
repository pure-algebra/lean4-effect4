import Tools.View.Live
import Tools.View.LiveChecks

/-! The landed live loop against the landed batch frames, in one process (the interpreter). -/

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Retained Tools.View.Live
open Tools.View.LiveChecks (chain forksInOrder)

def ms (ns : Nat) : String :=
  let t := ns / 10000
  s!"{t / 100}.{if t % 100 < 10 then "0" else ""}{t % 100}"

def bench (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => IO.println s!"{name}: none"
  | some reqs =>
    let s : Settings := {}
    -- batch: each frame whole, as the driver draws a frame: page, calls, device calls, stream
    let t0 ← IO.monoNanosNow
    let fs := frames "t" reqs
    let rowsFull ← IO.lazyPure fun _ => fs.foldl (fun n f =>
      n + (stream s.look 1280 2000 2 (lowerAll 2 (pageCalls s.look 1280 f.page))).length) 0
    let t1 ← IO.monoNanosNow
    -- live: one step at a time
    let mut st : State := {}
    let mut times : List Nat := []
    let mut rowsLive := 0
    for r in reqs do
      let a ← IO.monoNanosNow
      let (st', _, rows) ← IO.lazyPure fun _ => step s "t" st r
      let n := rows.length
      let b ← IO.monoNanosNow
      if n > 0 then times := times ++ [b - a]
      rowsLive := rowsLive + n
      st := st'
    let total := times.foldl (· + ·) 0
    let worst := times.foldl max 0
    IO.println s!"{name}: {fs.length} frames; batch {ms (t1 - t0)} ms, {rowsFull} stream rows; live {ms total} ms (mean {ms (total / max 1 times.length)}, worst {ms worst}), {rowsLive} patch rows"

#eval show IO Unit from do
  IO.println s!"load: {(← IO.Process.output { cmd := "uptime" }).stdout.trimAscii}"
  for (name, p) in [("pFork", Effect4.Program.Wire.Corpus.pFork), ("chain 6", chain 6 0),
      ("chain 12", chain 12 0), ("chain 18", chain 18 0)] do
    bench name p
