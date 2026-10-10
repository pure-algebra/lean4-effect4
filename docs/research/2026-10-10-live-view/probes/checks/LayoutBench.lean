import ProbeView.Live

open Effect4 Effect4.Program Tools.View Tools.View.Build Tools.View.Live

namespace Tools.View.LayoutBench
def later : Supervision.ForkOptions := ⟨false, false, .inherit⟩
def chain : Nat → Nat → NativeEff
  | 0, _ => .succeed (.lit (.nat 0))
  | n + 1, L =>
    .bind (.withFiber (.fork (.bind (.yieldNow 0) (.succeed (.lit (.nat n)))) later))
      (.bind (.awaitFiber (.var L) .awaitValue) (chain n (L + 2)))

def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let _ := size a
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 100000)

def go (name : String) (p : NativeEff) : IO Unit := do
  let fl := Flow.ofProgram p
  let (b, tLay) ← timed (fun _ => Flow.lay fl) (·.items.length)
  let (pp, tPrep) ← timed (fun _ => Flow.preparePlacement b) (·.heights.length)
  let (_, tPlace) ← timed (fun _ => Flow.place fl) (·.placed.length)
  let (l, tLayout) ← timed (fun _ => Flow.layout fl) (·.placed.size)
  let _ := pp
  IO.println s!"{name}: {b.items.length} items, {b.edges.length} edges, {b.frames.length} frames, {b.marks.length} marks; tenths of ms: lay {tLay}, prepare {tPrep}, place {tPlace}, layout {tLayout} ({l.routes.size} routes)"
end Tools.View.LayoutBench

open Tools.View.LayoutBench in
#eval show IO Unit from do
  go "chain 12" (chain 12 0)
  go "chain 24" (chain 24 0)
  go "chain 48" (chain 48 0)
