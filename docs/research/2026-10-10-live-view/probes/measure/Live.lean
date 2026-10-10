import Tools.View.Build
import Tools.View.Output

/-!
# Probe: the live loop's cost and the picture's stability under edits

Within one process, the probe replays the requests that build a program (`Build.requests`)
through the session tool (`Tools.Session.answer`). After each request it computes the frame as
`Build.frames` does, stage by stage, and times each stage. It records each graph node's place
(`Flow.ofPage`), keyed by address, and compares consecutive frames:

- a node outside the edited subtree should keep its place up to one motion shared by its whole
  unchanged part (rigid motion);
- the probe counts the parts whose nodes move by different amounts, across and down.
-/

open Effect4 Effect4.Program Effect4.Store Tools.View Tools.View.Build

namespace LiveProbe

def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩

/-- `n` forks in series, each awaited at once: fork, await, fork, await, … -/
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

/-- `n` forks first, then their awaits in reverse order: the awaits cross the forks. -/
def forksThen : Nat → Nat → Nat → NativeEff
  | 0, L, k => awaitsRev k L
  | n + 1, L, k =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (forksThen n (L + 1) k)
where
  /-- await the forks at levels `k - 1`, …, `0`, each binding a value -/
  awaitsRev : Nat → Nat → NativeEff
    | 0, _ => .succeed (.lit .unit)
    | j + 1, L => .bind (.awaitFiber (.var j) .awaitValue) (awaitsRev j (L + 1))

/-- A key's address: `[0 1 2]` read back. -/
def addrOf (k : Key) : Option (List Nat) :=
  if k.startsWith "[" && k.endsWith "]" then
    let body := ((k.drop 1).dropEnd 1).toString
    if body.isEmpty then some [] else (body.splitOn " ").mapM String.toNat?
  else none

def commonPrefix : List Nat → List Nat → List Nat
  | a :: as, b :: bs => if a = b then a :: commonPrefix as bs else []
  | _, _ => []

/-- The nodes of a laid graph: key, across, down. -/
def nodesOf (l : Laid) : List (Key × Int × Int) :=
  (l.placed.toList.filter (·.node.isSome)).map fun p => (p.key, p.x, p.y)

structure Times where
  answer : Nat := 0
  page : Nat := 0
  code : Nat := 0
  flow : Nat := 0
  calls : Nat := 0
  lower : Nat := 0
deriving Repr

def ms (ns : Nat) : String :=
  let t := ns / 10000
  s!"{t / 100}.{if t % 100 < 10 then "0" else ""}{t % 100}"

/-- Time a pure value: force it through a size the caller gives. -/
def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let s := size a
  let t1 ← IO.monoNanosNow
  pure (a, s, t1 - t0)

structure FrameData where
  path : List Nat
  times : Times
  nodes : List (Key × Int × Int)
  gutter : Nat
  lines : Nat

/-- The frames of a run of requests, stage by stage. -/
def frameData (reqs : List Tools.Session.Request) : IO (List FrameData) := do
  let mut st : Tools.Session.State := {}
  let mut out : List FrameData := []
  for r in reqs do
    let ((st', ans), _, tA) ← timed (fun _ => Tools.Session.answer st r) fun p => (p.2.laws.length)
    st := st'
    match st'.session with
    | none => pure ()
    | some l =>
      let lit := if r.op == "open" then none else some r.path
      let (page, _, tP) ← timed (fun _ => Program.sessionPage l lit "t" "" "" "") (·.lines.size)
      let holes := l.sketch.holes.map (·.name)
      let (code, _, tC) ← timed (fun _ => Program.codePanel l.sketch.program
        (l.app.withHoles l.sketch.holes).rows holes) fun c => (c.map (·.lines.size)).getD 0
      let page := { page with code }
      let (laid, _, tF) ← timed (fun _ => Flow.ofPage l.sketch.program page) (·.placed.size)
      let page := { page with graph := some { title := "program", laid } }
      let L : Look := {}
      let (calls, _, tK) ← timed (fun _ => pageCalls L 1280 page) (·.length)
      let (devs, _, tL) ← timed (fun _ => stream L 1280 2000 2 (lowerAll 2 calls)) (·.length)
      let _ := ans
      let _ := devs
      out := out ++ [FrameData.mk r.path ⟨tA, tP, tC, tF, tK, tL⟩ (nodesOf laid) (ownGutter page)
        page.lines.size]
  pure out

/-- Compare two frames after an edit at `a`: for each node outside the edited subtree, its
motion; grouped by the unchanged part it stands in. -/
structure Motion where
  groupsMoved : Nat := 0
  inside : Nat := 0
  total : Nat := 0
  outside : Nat := 0
  moved : Nat := 0
  partsX : Nat := 0
  splitX : Nat := 0
  splitY : Nat := 0
  maxShift : Int := 0

def compare (a : List Nat) (before after : List (Key × Int × Int)) : Motion :=
  let common := before.filterMap fun (k, x, y) =>
    match after.lookup k, addrOf k with
    | some (x', y'), some b => if a.isPrefixOf b then none else some (b, x' - x, y' - y)
    | _, _ => none
  let groupOf (b : List Nat) : List Nat := b.take ((commonPrefix a b).length + 1)
  let groups := (common.map fun (b, _, _) => groupOf b).eraseDups
  let split (sel : Int × Int → Int) : Nat := (groups.filter fun g =>
    ((common.filter fun (b, _, _) => groupOf b == g).map fun (_, dx, dy) => sel (dx, dy)).eraseDups.length > 1).length
  let movedGroups := (groups.filter fun g => common.any fun (b, dx, dy) =>
    groupOf b == g && (dx != 0 || dy != 0)).length
  let inside := (after.filter fun (k, _, _) => match addrOf k with
    | some b => a.isPrefixOf b
    | none => false).length
  { groupsMoved := movedGroups, inside, total := after.length
    outside := common.length
    moved := (common.filter fun (_, dx, dy) => dx != 0 || dy != 0).length
    partsX := groups.length
    splitX := split (·.1)
    splitY := split (·.2)
    maxShift := common.foldl (fun m (_, dx, dy) => max m (max dx.natAbs dy.natAbs)) 0 }

def report (name : String) (p : NativeEff) : IO Unit := do
  match requests p with
  | none => IO.println s!"{name}: no requests (a sub-program has no type)"
  | some reqs =>
    let fs ← frameData reqs
    let tot := fs.foldl (fun (t : Times) f => Times.mk (t.answer + f.times.answer)
      (t.page + f.times.page) (t.code + f.times.code) (t.flow + f.times.flow)
      (t.calls + f.times.calls) (t.lower + f.times.lower)) {}
    let n := fs.length
    let last := fs.getLast?
    IO.println s!"{name}: {n} frames, {(last.map (·.lines)).getD 0} lines, {(last.map (·.nodes.length)).getD 0} graph nodes"
    IO.println s!"  mean ms per frame: answer {ms (tot.answer / n)}, page {ms (tot.page / n)}, code {ms (tot.code / n)}, flow {ms (tot.flow / n)}, calls {ms (tot.calls / n)}, lower+stream {ms (tot.lower / n)}"
    match last with
    | some f => IO.println s!"  last frame ms: answer {ms f.times.answer}, page {ms f.times.page}, code {ms f.times.code}, flow {ms f.times.flow}, calls {ms f.times.calls}, lower+stream {ms f.times.lower}"
    | none => pure ()
    let pairs := fs.zip (fs.drop 1)
    let ms := pairs.map fun (f, g) => compare g.path f.nodes g.nodes
    let outside := ms.foldl (· + ·.outside) 0
    let moved := ms.foldl (· + ·.moved) 0
    let parts := ms.foldl (· + ·.partsX) 0
    let sx := ms.foldl (· + ·.splitX) 0
    let sy := ms.foldl (· + ·.splitY) 0
    let big := ms.foldl (fun m x => max m x.maxShift) 0
    let gm := ms.foldl (· + ·.groupsMoved) 0
    let ins := ms.foldl (· + ·.inside) 0
    let tot := ms.foldl (· + ·.total) 0
    IO.println s!"  retained delta over all edits: {gm} group moves + {ins} nodes inside the edit, against {tot} nodes redrawn by a full frame"
    IO.println s!"  stability: {outside} node motions outside the edit, {moved} moved; {parts} unchanged parts, {sx} split across, {sy} split down; largest shift {big} px"
    let gutters := fs.map (·.gutter)
    let changes := (gutters.zip (gutters.drop 1)).filter (fun (a, b) => a != b) |>.length
    IO.println s!"  gutter: own widths {gutters.eraseDups}, changes between frames {changes}"

end LiveProbe

open LiveProbe in
#eval show IO Unit from do
  for (name, p) in Effect4.Program.Wire.Corpus.all do report name p
  report "chain 6" (chain 6 0)
  report "chain 12" (chain 12 0)
  report "forksThen 4" (forksThen 4 0 4)
  report "forksThen 8" (forksThen 8 0 8)
