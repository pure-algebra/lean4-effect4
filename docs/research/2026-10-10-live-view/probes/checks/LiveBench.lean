import ProbeView.Live

/-!
# The live loop against the batch frames

For each program, the build's requests (`Build.requests`) run twice:

- **batch**: each frame drawn whole as the driver draws it: the session page, the code, the flow,
  `pageCalls`, `lowerAll` and the stream;
- **live**: `Live.step`, one request at a time, with the retained scene and the stroke cache.

Checks: after every step, the retained scene flattened is the tree's `pageCalls` of the same page
(the live loop draws what the batch would at the same columns); and the patch rows, applied to the
rows before, give the stream rows of the new picture (`applyRows`, the C side's job, here in Lean).
Measures: the time of each step, the rows each writes, and how often the page moves across.
-/

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Retained Tools.View.Live

namespace Tools.View.LiveBench

def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

def ms (ns : Nat) : String :=
  let t := ns / 10000
  s!"{t / 100}.{if t % 100 < 10 then "0" else ""}{t % 100}"

/-- The live loop's pages, rebuilt beside it with the same columns, for the checks. -/
def livePages (s : Settings) (reqs : List Tools.Session.Request) : List (Page × Scene) :=
  (reqs.foldl (fun (acc : State × List (Page × Scene)) r =>
    let (st, out) := acc
    let (st', ans, rows) := step s "t" st r
    if rows.isEmpty then (st', out) else
    match st'.tool.session with
    | none => (st', out)
    | some l =>
      let g := (Live.page "t" r st'.tool ans l st.memo).1
      let g := { g with gutter := st'.gutter, codeAt := st'.codeAt }
      (st', out ++ [(g, st'.scene)])) ({}, [])).2

-- the retained scene flattened is the tree's own picture of the same page, at every step: the
-- same calls, and the same keys except the code lines', which the live loop keys by their text
#guard (Effect4.Program.Wire.Corpus.all ++ [("chain 4", chain 4 0)]).all fun (_, p) =>
  match requests p with
  | none => false
  | some reqs => (livePages {} reqs).all fun (g, sc) =>
    let tree := pageCalls {} 1280 g
    sc.flatten.map (·.call) == tree.map (·.call) &&
      sc.flatten.map (fun c => if c.key.startsWith "code:" then "" else c.key) == tree.map (·.key)

def bench (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => IO.println s!"{name}: none"
  | some reqs =>
    let s : Settings := {}
    -- batch: each frame whole
    let t0 ← IO.monoNanosNow
    let fs := frames "t" reqs
    let rowsFull ← IO.lazyPure fun _ => fs.foldl (fun n f =>
      n + (stream s.look 1280 2000 2 (lowerAll 2 (pageCalls s.look 1280 f.page))).length) 0
    let t1 ← IO.monoNanosNow
    -- live: one step at a time
    let mut st : State := {}
    let mut times : List Nat := []
    let mut rowsLive := 0
    let mut moves := 0
    for r in reqs do
      let a ← IO.monoNanosNow
      let (st', _, rows) ← IO.lazyPure fun _ => step s "t" st r
      let n := rows.length
      let b ← IO.monoNanosNow
      if n > 0 then times := times ++ [b - a]
      rowsLive := rowsLive + n
      if st'.gutter != st.gutter || st'.codeAt != st.codeAt then moves := moves + 1
      st := st'
    let owns := fs.map fun f => (ownGutter f.page, ownCodeAt f.page)
    let ownMoves := ((owns.zip (owns.drop 1)).filter fun (a, b) => a != b).length
    let total := times.foldl (· + ·) 0
    let worst := times.foldl max 0
    IO.println s!"{name}: {fs.length} frames; batch {ms (t1 - t0)} ms, {rowsFull} stream rows; live {ms total} ms (mean {ms (total / max 1 times.length)}, worst {ms worst}), {rowsLive} patch rows; the page moves across {moves} times live against {ownMoves} with each page's own columns"

end Tools.View.LiveBench

open Tools.View.LiveBench in
#eval show IO Unit from do
  for (name, p) in [("pFork", Effect4.Program.Wire.Corpus.pFork), ("chain 6", chain 6 0),
      ("chain 12", chain 12 0), ("chain 18", chain 18 0)] do
    bench name p
