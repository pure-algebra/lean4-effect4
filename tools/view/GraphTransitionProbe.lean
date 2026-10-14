import Lean
import Tools.View.Motion
import Tools.View.FlowSpecimen

/-!
# Finite prepared-transition controls and timing probe

The controls read actual layout values, including duplicate occurrence order.
The benchmark consumes every sampled layout through a checksum.
Timing is host evidence, not a complexity theorem.
The controls distinguish the legacy observation from production attachment and separation policies.
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
  { move := { duration := 1000, ease := .linear },
    leave := { duration := 1000, ease := .linear }, enterFrom := 1700,
    draw := { delay := 1300, duration := 0 }, expand := { delay := 10, duration := 0 } }

-- Finite controls outside uniqueness, admission, and time-range premises.
#guard [0, 1, 499, 500, 999, 1000, 1001, 3000].all fun t =>
  (GraphMotion.prepare linear source target).legacySample t == GraphMotion.legacyReference linear source target t
#guard (((GraphMotion.prepare linear source target).legacySample 500).placed.toList.map (·.x)) ==
  [20, 5, 30, 20]
#guard [0, 500, 1000, 3000].all fun t =>
  (GraphMotion.prepare linear {} target).legacySample t == GraphMotion.legacyReference linear {} target t
#guard [0, 500, 1000, 3000].all fun t =>
  (GraphMotion.prepare linear source {}).legacySample t == GraphMotion.legacyReference linear source {} t
#guard [0, 500, 1000, 3000].all fun t =>
  (GraphMotion.prepare linear {} {}).legacySample t == GraphMotion.legacyReference linear {} {} t

private def movingFrom : Laid :=
  { placed := #[item "fork/0" 0 0], marks := #[.bar "fork" 0 30 0],
    width := 50, height := 100 }

private def movingTo : Laid :=
  { placed := #[item "fork/0" 0 100], marks := #[.bar "fork" 0 30 100],
    width := 50, height := 100 }

private def midpoint : Laid := (GraphMotion.prepare linear movingFrom movingTo).sample 500

-- Without incidence metadata, a kept mark still interpolates with the matched point.
#guard (midpoint.find "fork/0").map (·.y) == some 50
#guard midpoint.marks == #[.bar "fork" 0 30 50]
#guard (midpoint.find "fork/0").any (midpoint.onBar ·) == true
#guard ((GraphMotion.prepare linear movingFrom movingTo).legacySample 500).marks ==
  #[.bar "fork" 0 30 100]
#guard (movingFrom.find "fork/0").any (movingFrom.onBar ·) == true
#guard (movingTo.find "fork/0").any (movingTo.onBar ·) == true

private def attachedFrom : Laid :=
  { placed := #[item "stable" 0 0, item "removed" 12 0]
    marks := #[.bar "split" 0 30 0, .diamond "retired" 8 0]
    routes := #[.back "leaving" "removed" "stable" 0]
    attachments := #[⟨"stable", "split"⟩, ⟨"removed", "split"⟩]
    regions := #[{ key := "scope", name := "scope", x := 0, y := 0, w := 30, h := 50 }]
    width := 160, height := 160, routingWidth := some 60 }

private def attachedTo : Laid :=
  { placed := #[item "stable" 20 100, item "added" 64 100]
    marks := #[.bar "split" 20 80 100]
    routes := #[.back "entering" "added" "stable" 0]
    attachments := #[⟨"stable", "split"⟩, ⟨"added", "split"⟩]
    regions := #[{ key := "scope", name := "scope", x := 20, y := 100, w := 60, h := 70 }]
    width := 200, height := 200, routingWidth := some 100 }

private def attachedMid : Laid := (GraphMotion.prepare linear attachedFrom attachedTo).sample 500

#guard attachedMid.placed.toList.map (·.y) == [50, 50, 50]
#guard attachedMid.placed.toList.map Laid.middle == [40, 18, 49]
#guard attachedMid.placed.toList.all (attachedMid.onBar ·)
#guard attachedMid.attachments == #[⟨"stable", "split"⟩, ⟨"added", "split"⟩, ⟨"removed", "split"⟩]
#guard attachedMid.routes.toList.any fun r => r.key == "leaving" && r.reveal == 500
#guard attachedMid.marks.toList.any (·.key == "retired")
#guard attachedMid.regions == #[{ key := "scope", name := "scope", x := 10, y := 50, w := 45, h := 60 }]
#guard attachedMid.routingWidth == some 100
#guard (GraphMotion.prepare linear attachedFrom attachedTo).sample 1000 == attachedTo
#guard (GraphMotion.prepare linear attachedFrom attachedTo).sample 3000 == attachedTo

-- A kept point without target incidence detaches and follows the legacy position interpolation.
private def detachedTo : Laid :=
  { attachedTo with placed := #[item "stable" 120 100], attachments := #[] }
private def detachedMid : Laid := (GraphMotion.prepare linear attachedFrom detachedTo).sample 500
#guard (detachedMid.find "stable").map (·.x) == some 60
#guard (detachedMid.find "stable").map (·.y) == some 50
#guard !(detachedMid.attachments.toList.any fun a => a.port == "stable")
#guard detachedMid.attachments.toList.any fun a => a.port == "removed"
#guard (GraphMotion.prepare linear attachedFrom detachedTo).sample 1000 == detachedTo

private def diamondFrom : Laid :=
  { placed := #[item "choice-port" 0 0], marks := #[.diamond "choice" 8 0]
    attachments := #[⟨"choice-port", "choice"⟩] }

private def diamondTo : Laid :=
  { placed := #[item "choice-port" 40 100, item "entered-choice" 40 100]
    marks := #[.diamond "choice" 48 100]
    attachments := #[⟨"choice-port", "choice"⟩, ⟨"entered-choice", "choice"⟩] }

#guard ((GraphMotion.prepare linear diamondFrom diamondTo).sample 500).placed.toList.all fun p =>
  GraphAttachment.markContains (.diamond "choice" 28 50) p

-- A missing first binding blocks a later binding on unchecked repeated incidence.
private def unresolved : Laid :=
  { attachedTo with attachments := #[⟨"added", "missing"⟩, ⟨"added", "split"⟩] }
#guard (((GraphMotion.prepare linear attachedFrom unresolved).sample 500).find "added").map (·.y) == some 100
#guard (GraphMotion.prepare linear attachedFrom unresolved).sample 1000 == unresolved

private def node (key : Key) (x : Int) : Placed :=
  { key, x, y := 0, w := 32, node := some { key, line1 := key } }

private def swapFrom : Laid :=
  { placed := #[node "left" 0, node "right" 80], marks := #[.bar "source-mark" 0 32 0]
    regions := #[{ key := "source-region", name := "source", x := 0, y := 0, w := 32, h := 48 }]
    width := 140, height := 80, routingWidth := some 120 }

private def swapTo : Laid :=
  { placed := #[node "left" 80, node "right" 0], marks := #[.bar "target-mark" 80 112 0]
    regions := #[{ key := "target-region", name := "target", x := 80, y := 0, w := 32, h := 48 }]
    width := 160, height := 80, routingWidth := some 130 }

-- Empty node-family admission does not permit a matched point to travel as a new node.
private def pointSource : Laid :=
  { swapFrom with placed := #[item "left" 0 0, item "right" 80 0] }
#guard (GraphMotion.prepare linear pointSource swapTo).policy ==
  .endpointFamilies .changedNodeFamily
#guard !((GraphMotion.prepare linear pointSource swapTo).legacySample 500).boxesApart
#guard (List.range 1001).all fun t =>
  ((GraphMotion.prepare linear pointSource swapTo).sample t).boxesApart
#guard (GraphMotion.prepare linear pointSource swapTo).sample 1000 == swapTo

#guard (GraphMotion.prepare linear swapFrom swapTo).policy ==
  .endpointFamilies (.sweptBoxes 0 1)
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 200).marks == swapFrom.marks
#guard ((GraphMotion.prepare linear { swapFrom with routingWidth := none } swapTo).sample 200).routeWidth ==
  swapFrom.width
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 800).marks == swapTo.marks
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 200).regions == swapFrom.regions
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 800).regions == swapTo.regions
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 500).placed.isEmpty
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 500).routes.isEmpty
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 500).marks.isEmpty
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 500).regions.isEmpty
#guard ((GraphMotion.prepare linear swapFrom swapTo).sample 500).attachments.isEmpty
#guard (List.range 1001).all fun t => ((GraphMotion.prepare linear swapFrom swapTo).sample t).boxesApart
#guard (GraphMotion.prepare linear swapFrom swapTo).sample 1000 == swapTo
#guard (GraphMotion.prepare linear swapFrom { swapTo with placed := #[node "left" 80] }).policy ==
  .endpointFamilies .changedNodeFamily
#guard (GraphMotion.prepare { linear with move := { ease := .spring } } swapFrom swapFrom).policy ==
  .endpointFamilies .overshootingMovement
#guard (GraphMotion.prepare linear {} swapTo).policy == .direct
#guard (List.range 1001).all fun t =>
  ((GraphMotion.prepare ({} : Look).motion.norm {} swapTo).sample t).placed.toList.all (·.grow ≤ 1000)

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
      fast := fast + checksum (prepared.legacySample (i * 1000 / 60))
  let sampledAt ← IO.monoNanosNow
  let mut reference := preparationChecksum
  for _ in List.range rounds do
    for i in List.range 61 do
      reference := reference + checksum (GraphMotion.legacyReference c a b (i * 1000 / 60))
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
  if args.headD "" == "controls" then
    IO.println "graph-transition: finite compatibility and inherited moving-bar controls pass"
    return
  let rounds := (args.headD "1").toNat?.getD 1
  let c := ({} : Look).motion.norm
  for (name, index) in [("nested-forks", 10), ("wide-race", 14), ("race-loop", 11),
      ("await-all", 3), ("nested-scopes", 12), ("handler-scope", 8)] do
    let some page := FlowSpecimen.frames[index]? | throw (IO.userError "missing flow specimen")
    let some graph := page.graph | throw (IO.userError "missing flow graph")
    GraphTransitionProbe.bench name c {} graph.laid rounds
  for count in [128, 512] do
    let target := GraphTransitionProbe.synthetic count
    GraphTransitionProbe.bench s!"synthetic-{count}" c {} target rounds
    let previous := { target with placed := target.placed.map fun p => { p with x := p.x + 12 } }
    GraphTransitionProbe.bench s!"synthetic-kept-{count}" c previous target rounds
  IO.println (Lean.Json.compress (Lean.Json.mkObj [
    ("moving_bar", Lean.Json.mkObj [("time", Lean.toJson (500 : Nat)),
      ("port_y", Lean.toJson (50 : Nat)), ("mark_y", Lean.toJson (50 : Nat)),
      ("onBar", Lean.toJson true), ("legacy_mark_y", Lean.toJson (100 : Nat))])]))
