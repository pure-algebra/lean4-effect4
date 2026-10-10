import ProbeView.Fast

open Effect4 Effect4.Program Tools.View Tools.View.Build

/-! ## The checks: each replacement equals the tree's function, frame by frame -/

namespace Tools.View.FastCheck
open Tools.View.Fast

def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))
def forksInOrder : Nat → Nat → Nat → NativeEff
  | 0, L, k => awaits k 0 L
  | n + 1, L, k =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (forksInOrder n (L + 1) k)
where
  awaits : Nat → Nat → Nat → NativeEff
    | 0, _, _ => .succeed (.lit .unit)
    | j + 1, i, L => .bind (.awaitFiber (.var i) .awaitValue) (awaits j (i + 1) (L + 1))

def programs : List (String × NativeEff) :=
  Effect4.Program.Wire.Corpus.all ++ [("chain 6", chain 6 0), ("forksInOrder 3", forksInOrder 3 0 3)]

/-- Every frame of a program built by edits. -/
def framesOf (p : NativeEff) : List Frame := ((requests p).map (frames "t")).getD []

def laidOf (f : Frame) : Laid := (f.page.graph.map (·.laid)).getD {}

-- 2 and 3: the graph's calls on the index and a fresh cache equal the tree's, on every frame,
-- in the dark look (organic strokes) and with plain strokes (no trunk)
#guard programs.all fun (_, p) => (framesOf p).all fun f =>
  (calls {} (laidOf f) 24 200).1 == Laid.calls {} (laidOf f) 24 200
#guard programs.all fun (_, p) => (framesOf p).all fun f =>
  let L : Look := { organic := { trunk := 0 } }
  (calls L (laidOf f) 24 200).1 == Laid.calls L (laidOf f) 24 200

-- 3: one cache carried along a whole sequence of frames still answers the tree's calls
#guard programs.all fun (_, p) =>
  let L : Look := {}
  ((framesOf p).foldl (fun (acc : Bool × StrokeCache) f =>
    let (cs, c) := calls L (laidOf f) 24 200 acc.2
    (acc.1 && cs == Laid.calls L (laidOf f) 24 200, c)) (true, {})).1

-- 4: the indexed session page equals the tree's, at every state of every build
#guard programs.all fun (_, p) =>
  match requests p with
  | none => false
  | some reqs =>
    (reqs.foldl (fun (acc : Bool × Tools.Session.State) r =>
      let (st, _) := Tools.Session.answer acc.2 r
      match st.session with
      | none => (acc.1, st)
      | some l =>
        let lit := if r.op == "open" then none else some r.path
        (acc.1 && (sessionPageIx l lit "t" "j" "p" "f").lines == (Program.sessionPage l lit "t" "j" "p" "f").lines, st))
      (true, {})).1

end Tools.View.FastCheck

/-! ## The timings: the tree's function against the replacement -/

namespace Tools.View.FastBench
open Tools.View.Fast Tools.View.FastCheck

def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let _ := size a
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 1000000)

/-- One program: the last frame's graph drawn by the tree and by the replacement; the whole
sequence drawn by the tree, and by the replacement with one cache; the last page by both. -/
def bench (name : String) (p : NativeEff) : IO Unit := do
  let fs := framesOf p
  match fs.getLast? with
  | none => pure ()
  | some f => do
    let L : Look := {}
    let l := laidOf f
    let (_, tTree) ← timed (fun _ => Laid.calls L l 24 200) (·.length)
    let (_, tFast) ← timed (fun _ => (calls L l 24 200).1) (·.length)
    let (_, tSeqTree) ← timed (fun _ => fs.map fun g => (Laid.calls L (laidOf g) 24 200).length) (·.length)
    let (_, tSeqFast) ← timed (fun _ => (fs.foldl (fun (acc : Nat × StrokeCache) g =>
      let (cs, c) := calls L (laidOf g) 24 200 acc.2
      (acc.1 + cs.length, c)) (0, {})).1) id
    IO.println s!"{name}: {fs.length} frames, {l.routes.size} routes; last graph: tree {tTree} ms, fast {tFast} ms; whole sequence: tree {tSeqTree} ms, fast with one cache {tSeqFast} ms"

def benchPage (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => pure ()
  | some reqs =>
    let st := reqs.foldl (fun st r => (Tools.Session.answer st r).1) ({} : Tools.Session.State)
    match st.session with
    | none => pure ()
    | some l => do
      let (_, tTree) ← timed (fun _ => Program.sessionPage l none "t" "" "" "") (·.lines.size)
      let (_, tFast) ← timed (fun _ => sessionPageIx l none "t" "" "" "") (·.lines.size)
      IO.println s!"{name}: session page of {(Program.lines l.sketch.program).length} lines: tree {tTree} ms, indexed {tFast} ms"

end Tools.View.FastBench

open Tools.View.FastBench Tools.View.FastCheck in
#eval show IO Unit from do
  for (name, p) in [("chain 6", chain 6 0), ("chain 12", chain 12 0), ("chain 18", chain 18 0),
      ("forksInOrder 6", forksInOrder 6 0 6)] do
    bench name p
  for (name, p) in [("chain 12", chain 12 0), ("chain 18", chain 18 0)] do
    benchPage name p
