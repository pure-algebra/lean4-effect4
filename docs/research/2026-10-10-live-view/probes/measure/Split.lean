import Tools.View.Build
import Tools.View.Output

open Effect4 Effect4.Program Effect4.Store Tools.View Tools.View.Build

namespace SplitProbe
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let s := size a
  let t1 ← IO.monoNanosNow
  pure (a, s, (t1 - t0) / 1000000)

/-- The last page of a program built by edits. -/
def lastPage (p : NativeEff) : Option Page :=
  (requests p).bind fun reqs => ((frames "t" reqs).getLast?).map (·.page)

def split (name : String) (p : NativeEff) : IO Unit := do
  match lastPage p with
  | none => IO.println s!"{name}: none"
  | some g => do
    let L : Look := {}
    let (W, H) := pageSize 1280 g
    let (a, na, ta) ← timed (fun _ => g.lines.toList.zipIdx.flatMap fun (l, i) => lineCalls L (linesWidth W g) (gutterCols g) i l g.marks) (·.length)
    let (_, nc, tc) ← timed (fun _ => codeCalls L W g) (·.length)
    let (gr, ng, tg) ← timed (fun _ => graphCalls L g) (·.length)
    let (_, nh, th) ← timed (fun _ => chromeCalls L W H g) (·.length)
    let laid := (g.graph.map (·.laid)).getD {}
    let (_, nr, tr) ← timed (fun _ => laid.routes.toList.flatMap (laid.routeCalls L 0 0)) (·.length)
    let (_, nb, tb) ← timed (fun _ => laid.placed.toList.flatMap fun p => match p.node with
      | some n => Laid.boxCalls L 0 0 p n | none => []) (·.length)
    let (_, nseg, tseg) ← timed (fun _ => laid.routes.toList.map (laid.segments L)) (·.length)
    let (_, nfind, tfind) ← timed (fun _ => laid.routes.toList.flatMap fun r => match r with
      | .down _ ks _ _ => ks.filterMap laid.find | _ => []) (·.length)
    let flat : Look := { L with organic := { L.organic with trunk := 0 } }
    let (_, nflat, tflat) ← timed (fun _ => laid.routes.toList.flatMap (laid.routeCalls flat 0 0)) (·.length)
    IO.println s!"{name}: segments of {nseg} routes {tseg} ms; {nfind} finds {tfind} ms; plain strokes {nflat} calls {tflat} ms"
    let (_, nl, tl) ← timed (fun _ => lowerAll 2 gr) (·.length)
    let _ := a
    let (pc, npc, tpc) ← timed (fun _ => pageCalls L 1280 g) (·.length)
    let (_, nlo, tlo) ← timed (fun _ => lowerAll 2 pc) (·.length)
    let (_, nst, tst) ← timed (fun _ => stream L 1280 2000 2 (lowerAll 2 pc)) (·.length)
    let (_, nsv, tsv) ← timed (fun _ => svg L 1280 2000 1 (lowerAll 1 pc)) (·.length)
    IO.println s!"{name}: pageCalls {npc} in {tpc} ms; lowerAll {nlo} in {tlo} ms; stream {nst} lines in {tst} ms; svg {nsv} chars in {tsv} ms"
    IO.println s!"{name}: lines {na} calls {ta} ms; code {nc} calls {tc} ms; graph {ng} calls {tg} ms (routes {nr} calls {tr} ms, boxes {nb} calls {tb} ms); chrome {nh} calls {th} ms; lower graph {nl} dev {tl} ms; {laid.placed.size} placed, {laid.routes.size} routes"
end SplitProbe

open SplitProbe in
#eval show IO Unit from do
  split "chain 6" (chain 6 0)
  split "chain 12" (chain 12 0)
  split "chain 18" (chain 18 0)
