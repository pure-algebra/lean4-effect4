import ProbeView.Layout
import Tools.View.Build

/-! The fast layout equals the tree's on every frame of the probe's builds, and the timings. -/

open Effect4 Effect4.Program Tools.View Tools.View.Build

deriving instance DecidableEq for Tools.View.GNode
deriving instance DecidableEq for Tools.View.Placed
deriving instance DecidableEq for Tools.View.Route
deriving instance DecidableEq for Tools.View.Region
deriving instance DecidableEq for Tools.View.FlowMark
deriving instance DecidableEq for Tools.View.Laid
deriving instance DecidableEq for Tools.View.Flow.PreparedPlacement

namespace Tools.View.LayoutCheck
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

def programs : List NativeEff :=
  (Effect4.Program.Wire.Corpus.all.map (·.2)) ++ [chain 6 0, forksInOrder 4 0 4]

/-- Every intermediate program of a build: each frame's sketch. -/
def sketchesOf (p : NativeEff) : List NativeEff :=
  match requests p with
  | none => []
  | some reqs => (reqs.foldl (fun (acc : Tools.Session.State × List NativeEff) r =>
      let (st, _) := Tools.Session.answer acc.1 r
      (st, acc.2 ++ (st.session.map (·.sketch.program)).toList)) ({}, [])).2

#guard programs.all fun p => (sketchesOf p).all fun q =>
  let fl := Flow.ofProgram q
  FastLayout.kahn 64 (Flow.lay fl).edges == Flow.kahn 64 (Flow.lay fl).edges &&
    FastLayout.preparePlacement (Flow.lay fl) == Flow.preparePlacement (Flow.lay fl) &&
    FastLayout.layout fl == Flow.layout fl

-- the whole programs too, and a wider order: every program at once as one flow in parallel
#guard
  let fl := Flow.Flow.par .fork "[]" (programs.map Flow.ofProgram)
  FastLayout.layout fl == Flow.layout fl

def timed {α : Type} (f : Unit → α) (size : α → Nat) : IO (α × Nat) := do
  let t0 ← IO.monoNanosNow
  let a ← IO.lazyPure f
  let _ := size a
  let t1 ← IO.monoNanosNow
  pure (a, (t1 - t0) / 100000)
end Tools.View.LayoutCheck

open Tools.View.LayoutCheck in
#eval show IO Unit from do
  for (name, p) in [("chain 12", chain 12 0), ("chain 24", chain 24 0), ("chain 48", chain 48 0),
      ("forksInOrder 12", forksInOrder 12 0 12)] do
    let fl := Flow.ofProgram p
    let (a, tTree) ← timed (fun _ => Flow.layout fl) (·.placed.size)
    let (b, tFast) ← timed (fun _ => FastLayout.layout fl) (·.placed.size)
    IO.println s!"{name}: {a.placed.size} placed; layout, tenths of ms: tree {tTree}, fast {tFast}; equal {a == b}"
