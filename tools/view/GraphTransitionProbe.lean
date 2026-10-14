import Lean
import Tools.View.Motion
import Tools.View.FlowSpecimen

/-!
# Finite prepared-transition controls and timing probe

The controls read actual layout values, including duplicate occurrence order.
The benchmark consumes every sampled layout through a checksum.
Timing is host evidence, not a complexity theorem.
The moving-bar control records an inherited mismatch; this slice keeps its observation.
-/

open Tools.View

namespace GraphTransitionProbe

private def item (key : Key) (x y : Int) : Placed :=
  { key, x, y, w := 16 }

private def source : Laid :=
  { placed := #[item "same" 0 0, item "same" 80 80, item "gone" 20 20]
    routes := #[.down "kept" ["same", "gone"], .loop "gone-route" "gone",
      .back "kept" "gone" "same" 4]
    width := 150, height := 150 }

private def target : Laid :=
  { placed := #[item "same" 10 10, item "new" 30 60, item "same" 40 80]
    routes := #[.loop "new-route" "missing", .back "kept" "same" "new" 2,
      .down "new-route" [], .down "bad-endpoints" ["missing", "same"]]
    width := 100, height := 200, marks := #[.bar "mark" 0 60 80]
    regions := #[{ key := "scope", name := "scope", x := 0, y := 0, w := 100, h := 200 }] }

private def linear : Choreography :=
  { move := { duration := 1000, ease := .linear }, enterFrom := 1700,
    draw := { delay := 1300, duration := 0 }, expand := { delay := 10, duration := 0 } }

-- Finite controls outside uniqueness, admission, and time-range premises.
#guard [0, 1, 499, 500, 999, 1000, 1001, 3000].all fun t =>
  (GraphMotion.prepare linear source target).sample t == GraphMotion.reference linear source target t
#guard (((GraphMotion.prepare linear source target).sample 500).placed.toList.map (·.x)) ==
  [20, 5, 30, 20]
#guard [0, 500, 1000, 3000].all fun t =>
  (GraphMotion.prepare linear {} target).sample t == GraphMotion.reference linear {} target t
#guard [0, 500, 1000, 3000].all fun t =>
  (GraphMotion.prepare linear source {}).sample t == GraphMotion.reference linear source {} t
#guard [0, 500, 1000, 3000].all fun t =>
  (GraphMotion.prepare linear {} {}).sample t == GraphMotion.reference linear {} {} t

private def movingFrom : Laid :=
  { placed := #[item "fork/0" 0 0], marks := #[.bar "fork" 0 30 0],
    width := 50, height := 100 }

private def movingTo : Laid :=
  { placed := #[item "fork/0" 0 100], marks := #[.bar "fork" 0 30 100],
    width := 50, height := 100 }

private def midpoint : Laid := (GraphMotion.prepare linear movingFrom movingTo).sample 500

-- The moving port stands at y=50 while the retained target mark stands at y=100.
#guard (midpoint.find "fork/0").map (·.y) == some 50
#guard midpoint.marks == #[.bar "fork" 0 30 100]
#guard (midpoint.find "fork/0").any (midpoint.onBar ·) == false
#guard (movingFrom.find "fork/0").any (movingFrom.onBar ·) == true
#guard (movingTo.find "fork/0").any (movingTo.onBar ·) == true

private def checksum (l : Laid) : Nat :=
  l.width.natAbs + l.height.natAbs + l.regions.size + l.marks.size +
    l.placed.foldl (fun n p => n + p.x.natAbs + p.y.natAbs + p.w.natAbs + p.grow) 0 +
    l.routes.foldl (fun n r => n + r.reveal) 0

private def synthetic (count : Nat) : Laid :=
  { placed := ((List.range count).map fun i =>
      { key := toString i, x := (i % 8 : Nat) * 40, y := (i / 8 : Nat) * 70, w := 32,
        node := some { key := toString i, line1 := "node" } } : List Placed).toArray
    routes := ((List.range (count - 1)).map fun i =>
      Route.down (toString i ++ "edge") [toString i, toString (i + 1)]).toArray
    width := 360, height := (count / 8 + 1) * 70 }

private def bench (label : String) (c : Choreography) (a b : Laid) (rounds : Nat) : IO Unit := do
  let start ← IO.monoNanosNow
  let retained ← IO.mkRef (GraphMotion.prepare c a b)
  let prepared ← retained.get
  let preparationChecksum := prepared.places.length + prepared.routes.length +
    prepared.gone.length + prepared.retracting.length
  let preparedAt ← IO.monoNanosNow
  let mut fast := preparationChecksum
  for _ in List.range rounds do
    for i in List.range 61 do
      fast := fast + checksum (prepared.sample (i * 1000 / 60))
  let sampledAt ← IO.monoNanosNow
  let mut reference := preparationChecksum
  for _ in List.range rounds do
    for i in List.range 61 do
      reference := reference + checksum (GraphMotion.reference c a b (i * 1000 / 60))
  let referenceAt ← IO.monoNanosNow
  unless fast == reference do throw (IO.userError "sample checksums differ")
  IO.println (Lean.Json.compress (Lean.Json.mkObj [
    ("case", Lean.toJson label), ("nodes", Lean.toJson b.placed.size),
    ("routes", Lean.toJson b.routes.size), ("samples", Lean.toJson (rounds * 61)),
    ("prepare_ns", Lean.toJson (preparedAt - start)),
    ("prepared_sample_ns", Lean.toJson (sampledAt - preparedAt)),
    ("reference_sample_ns", Lean.toJson (referenceAt - sampledAt)),
    ("checksum", Lean.toJson fast)]))

end GraphTransitionProbe

/-- Run finite actual-graph and synthetic sampling measurements. -/
def main (args : List String) : IO Unit := do
  let rounds := (args.headD "1").toNat?.getD 1
  let c := ({} : Look).motion.norm
  for (name, index) in [("nested-forks", 10), ("wide-race", 14), ("race-loop", 11),
      ("await-all", 3), ("nested-scopes", 12), ("handler-scope", 8)] do
    let some page := FlowSpecimen.frames[index]? | throw (IO.userError "missing flow specimen")
    let some graph := page.graph | throw (IO.userError "missing flow graph")
    GraphTransitionProbe.bench name c {} graph.laid rounds
  for count in [128, 512] do
    GraphTransitionProbe.bench s!"synthetic-{count}" c {} (GraphTransitionProbe.synthetic count) rounds
  IO.println (Lean.Json.compress (Lean.Json.mkObj [
    ("moving_bar", Lean.Json.mkObj [("time", Lean.toJson (500 : Nat)),
      ("port_y", Lean.toJson (50 : Nat)), ("mark_y", Lean.toJson (100 : Nat)),
      ("onBar", Lean.toJson false), ("inherited", Lean.toJson true)])]))
