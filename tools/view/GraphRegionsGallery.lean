import Tools.View.GraphRegionsView
import Tools.View.GraphPacking
import Tools.View.GraphBounds
import Tools.View.GraphContact
import Tools.View.FlowSpecimen
import Tools.View.SvgOut
import Tools.View.Tokens

/-! Finite region and component-packing specimens through production drawing.
The source is a display graph, not a program or a scheduler trace.
The exporter retains node members and every original edge occurrence for inspection. -/

open Tools.View Lean

namespace GraphRegionsGallery

def source : Graph :=
  { nodes := #[
      ⟨"input", "input", "request", false⟩,
      ⟨"validate", "validate", "payload", false⟩,
      ⟨"schema", "schema", "shape", false⟩,
      ⟨"policy", "policy", "access", false⟩,
      ⟨"normalize", "normalize", "value", false⟩,
      ⟨"cache-read", "read", "cache", false⟩,
      ⟨"cache-write", "write", "cache", false⟩,
      ⟨"join", "join", "results", false⟩,
      ⟨"output", "output", "response", false⟩],
    edges := #[⟨"entry", 0, 1⟩, ⟨"retry-entry", 0, 1⟩,
      ⟨"check-schema", 1, 2⟩, ⟨"check-policy", 1, 3⟩,
      ⟨"schema-result", 2, 4⟩, ⟨"policy-result", 3, 4⟩,
      ⟨"read-request", 4, 5⟩, ⟨"write-request", 4, 6⟩,
      ⟨"read-result", 5, 7⟩, ⟨"write-result", 6, 7⟩,
      ⟨"finish", 7, 8⟩, ⟨"retry-cache", 6, 5⟩,
      ⟨"policy-loop", 3, 3⟩, ⟨"short-circuit", 1, 7⟩] }

def membership : GraphRegions.Membership :=
  { regions := #[⟨"validation", none⟩, ⟨"checks", some 0⟩,
      ⟨"cache", none⟩, ⟨"empty", none⟩],
    owner := #[none, some 0, some 1, some 1, some 0, some 2, some 2, none, none] }

def labels : Array (String × String) :=
  #[("validation", "4 members"), ("checks", "2 members"),
    ("cache", "2 members"), ("empty", "0 members")]

def cases : List (String × String × Array Bool) :=
  [("Expanded", "All source nodes and edge occurrences are visible.", #[false,false,false,false]),
   ("Collapse inner checks", "Two members share one displayed node. The policy self-loop stays in provenance.", #[false,true,false,false]),
   ("Collapse validation", "The outer region hides its internal edges and retains each boundary edge.", #[true,false,false,false]),
   ("Collapse both components", "Two compound nodes retain parallel connections as separate edge occurrences.", #[true,false,true,false]),
   ("Ancestor selection wins", "Selecting checks inside selected validation gives the same visible ancestor.", #[true,true,true,false]),
   ("Explicit empty compound", "An empty selected region has a visible node with no members.", #[true,false,true,true])]

def scaleSource : Graph :=
  { nodes := (List.range 1000).toArray.map fun i =>
      { key := s!"task-{i}", line1 := s!"task {i}" },
    edges := (List.range 999).toArray.map fun i =>
      { key := s!"step-{i}", src := i, dst := i + 1 } }

def scaleMembership : GraphRegions.Membership :=
  { regions := (List.range 10).toArray.map fun i => ⟨s!"stage-{i}", none⟩,
    owner := (List.range 1000).toArray.map fun i => some (i / 100) }

def allCases : List (String × String × Graph × GraphRegions.Membership × Array Bool × Array (String × String)) :=
  (cases.map fun (title, description, selected) => (title, description, source, membership, selected, labels)) ++
    [("1,000 source nodes", "Ten visible regions retain the source graph and all 999 edge occurrences.",
      scaleSource, scaleMembership, Array.replicate 10 true,
      (List.range 10).toArray.map fun i => (s!"stage {i + 1}", "100 members"))]

structure Drawing where
  calls : List (Keyed Call)
  width : Nat
  height : Nat

def drawing (L : Look) (laid : Laid) : Drawing :=
  let calls := laid.calls L 0 0
  let viewport := GraphBounds.viewport laid calls 18
  { calls := viewport.calls calls, width := viewport.size.1.toNat, height := viewport.size.2.toNat }

def writeSvg (out : System.FilePath) (L : Look) (name : String) (d : Drawing) : IO Unit := do
  let calls := (⟨"ground", .fill .ground 1000 0 0 d.width d.height⟩ : Keyed Call) :: d.calls
  match SvgOut.fileText (SvgOut.picture L d.width d.height 1 (lowerAll 1 calls)) with
  | .error why => throw (IO.userError why)
  | .ok svg => IO.FS.writeFile (out / name) svg

def nodeJson (view : GraphRegionsView.Prepared) (laid : Laid)
    (shift : Int × Int) (n : GNode) (i : Nat) : Json :=
  let p := (laid.find n.key).getD { key := n.key, x := 0, y := 0, w := 0 }
  let members := (view.prepared.members[i]?).getD #[]
  let names := members.toList.filterMap fun j => (view.source.nodes[j]?).map (·.key)
  let origin := match view.prepared.visible[i]? with
    | some (.node j) => s!"Source vertex #{j}"
    | some (.region j) => s!"Compound region #{j}"
    | none => "Missing representative"
  Json.mkObj [("key", toJson n.key), ("label", toJson n.line1), ("origin", toJson origin),
    ("members", toJson names),
    ("bounds", toJson ([p.x + shift.1, p.y + shift.2, p.x + p.w + shift.1,
      p.y + ROWH * BOXROWS + shift.2] : List Int))]

def edgeJson (view : GraphRegionsView.Prepared)
    (e : GraphRegions.EdgeOccurrence GEdge) : Json :=
  let key (i : Nat) := ((view.graph.nodes[i]?).map (·.key)).getD ""
  Json.mkObj [("occurrence", toJson e.occurrence), ("key", toJson e.original.key),
    ("source", toJson (key e.source)), ("target", toJson (key e.target)),
    ("originalSource", toJson e.originalSource), ("originalTarget", toJson e.originalTarget),
    ("hidden", toJson e.hidden)]

def contactsJson (L : Look) (laid : Laid) (shift : Int × Int) : Json :=
  toJson ((GraphContact.collect L laid).map fun c => Json.mkObj [
    ("item", toJson c.item),
    ("side", toJson (match c.side with | .source => "source" | .target => "target")),
    ("point", toJson ([c.point.1 + shift.1, c.point.2 + shift.2] : List Int))])

def packDrawing (components : Array Drawing) (target : Nat) : Drawing × GraphPacking.Packed := Id.run do
  let sizes := components.map fun d =>
    ({ width := max 140 d.width, height := d.height + 30 } : GraphPacking.Size)
  let packed := GraphPacking.pack { targetWidth := target, gap := 28 } sizes
  let mut calls : List (Keyed Call) := []
  for p in packed.placements do
    let some d := components[p.occurrence]? | continue
    let x := p.box.x0 + 18
    let y := p.box.y0 + 18
    let name := s!"component-{p.occurrence}"
    let moved := d.calls.map fun c =>
      { key := name ++ "/" ++ c.key, call := c.call.move x (y + 30) : Keyed Call }
    calls := calls ++ [⟨name ++ "/label", .text .label (x + 8) (y + 18) 24 s!"component {p.occurrence + 1}"⟩] ++ moved
  let result : Drawing :=
    { calls, width := packed.canvas.width.toNat + 36,
      height := packed.canvas.height.toNat + 36 }
  return (result, packed)

end GraphRegionsGallery

def main (args : List String) : IO Unit := do
  let out : System.FilePath := args.headD "tools/view/out/graph-regions"
  IO.FS.createDirAll out
  let L : Look := {}
  let paper ← Tokens.lookFile "paper"
  IO.FS.writeFile (out / "look.css") (Tokens.css L ++ Tokens.css paper ++ Tokens.rules)
  let mut frames : Array Json := #[]
  let mut components : Array GraphRegionsGallery.Drawing := #[]
  for ((title, description, source, membership, selection, labels), i) in GraphRegionsGallery.allCases.zipIdx do
    let view ← match GraphRegionsView.prepare source membership selection labels with
      | .ok view => pure view
      | .error _ => throw (IO.userError s!"region view {i} refused")
    let laid := view.graph.layout
    unless (GraphCheck.laid laid).isOk do throw (IO.userError s!"region layout {i} refused")
    let calls := laid.calls L 0 0
    let viewport := GraphBounds.viewport laid calls 18
    let d : GraphRegionsGallery.Drawing := ⟨viewport.calls calls, viewport.size.1.toNat, viewport.size.2.toNat⟩
    let file := s!"region-{i}.svg"
    GraphRegionsGallery.writeSvg out L file d
    if i < 6 then components := components.push d
    frames := frames.push (Json.mkObj [("title", toJson title), ("description", toJson description),
      ("file", toJson file), ("originalNodes", toJson view.source.nodes.size),
      ("nodes", toJson (view.graph.nodes.toList.zipIdx.map fun (n, j) =>
        GraphRegionsGallery.nodeJson view laid viewport.shift n j)),
      ("edges", toJson (view.edges.toList.map (GraphRegionsGallery.edgeJson view))),
      ("contacts", GraphRegionsGallery.contactsJson L laid viewport.shift)])
    IO.println s!"region-gallery,{i},{view.source.nodes.size},{view.graph.nodes.size},{view.edges.size},{view.graph.edges.size}"
  for index in [3, 8, 10, 11, 12, 14] do
    let some frame := FlowSpecimen.frames[index]? | throw (IO.userError "missing Flow specimen")
    let some graph := frame.graph | throw (IO.userError "missing Flow graph")
    components := components.push (GraphRegionsGallery.drawing L graph.laid)
  let mut packings : Array Json := #[]
  for target in [1000, 1800, 2600] do
    let (d, packed) := GraphRegionsGallery.packDrawing components target
    let file := s!"packing-{target}.svg"
    GraphRegionsGallery.writeSvg out L file d
    packings := packings.push (Json.mkObj [("title", toJson s!"{target} px"), ("file", toJson file),
      ("count", toJson packed.placements.size), ("rows", toJson packed.rows),
      ("width", toJson d.width), ("height", toJson d.height), ("oversize", toJson packed.oversizeCount)])
    IO.println s!"packing-gallery,{target},{packed.placements.size},{packed.rows},{d.width},{d.height}"
  IO.FS.writeFile (out / "manifest.json") ((Json.mkObj [("cases", .arr frames), ("packing", .arr packings)]).pretty ++ "\n")
