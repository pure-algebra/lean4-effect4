import Tools.View.FlowSpecimen
import Tools.View.GraphBounds
import Tools.View.SvgOut

/-!
Finite controls for allocation, geometry fitting, independent lane spans and prepared pages.
The controls compare stored envelopes and calls, without a font or rasterization claim.
-/

open Tools.View Whatwg.Svg.Scene

namespace GraphBoundsProbe

def singleton : Graph :=
  { nodes := #[{ key := "one", line1 := "one" }], edges := #[⟨"loop", 0, 0⟩] }

def mixed : Graph :=
  { nodes := #[{ key := "a", line1 := "source" }, { key := "b", line1 := "target" }],
    edges := #[⟨"down", 0, 1⟩, ⟨"back", 1, 0⟩, ⟨"loop", 1, 1⟩] }

def barePoint : Laid :=
  { placed := #[{ key := "point", x := 0, y := 0, w := 16 }], routes := #[.loop "loop" "point"],
    width := 48, height := 40, routingWidth := some 16 }

def controls : List (String × Laid) :=
  [("generic-loop", singleton.layout), ("mixed-back-loop", mixed.layout),
   ("flow-loop", Flow.layout (.loop "return" (.node "one" "one" ""))),
   ("flow-point-loop", Flow.layout (.loop "return" (.region "empty" "region" (.seq [])))),
   ("bare-point-loop", barePoint),
   ("overshoot", { mixed.layout with placed := mixed.layout.placed.map fun p => { p with grow := 1800 } }),
   ("negative-origin", { barePoint with placed := barePoint.placed.map fun p => { p with x := -48, y := -48 } })]

def styles : List (String × Look) :=
  [("default", {}),
   ("plain", { organic := { trunk := 0 }, strokes := { edge := 1, radius := 0 } }),
   ("wide-stroke", { organic := { trunk := 0 }, strokes := { edge := 40, frame := 30, radius := 0 }, reach := 2500 }),
   ("organic-noise", { organic := { trunk := 32000, fine := 8000, flare := 50000, noise := 1000, wave := 6000 } })]

def require (holds : Bool) (message : String) : IO Unit :=
  unless holds do throw (IO.userError message)

def inViewport (laid : Laid) (calls : List (Keyed Call)) (halo : Nat) : Bool :=
  let v := GraphBounds.viewport laid calls halo
  calls.all fun c => match (PaintBounds.call c.call).geometry with
    | none => true
    | some b => decide (b.Inside v.bounds)

def fittedAtOrigin (laid : Laid) (calls : List (Keyed Call)) (halo : Nat) : Bool :=
  let v := GraphBounds.viewport laid calls halo
  let canvas := IBox.ofSize 0 v.size.1 v.size.2
  (v.calls calls).all fun c => match (PaintBounds.call c.call).geometry with
    | none => true
    | some b => decide (b.Inside canvas)

def allocation : IO Unit := do
  for laid in [singleton.layout, mixed.layout,
      Flow.layout (.loop "return" (.node "one" "one" "")),
      Flow.layout (.loop "return" (.region "empty" "region" (.seq [])))] do
    let canvas := IBox.ofSize 0 laid.width laid.height
    for route in laid.routes do
      match route with
      | .loop .. =>
        for c in Laid.segments {} laid.find laid.routeWidth route do
          require (decide ((PaintBounds.controlHull c).Inside canvas)) "loop control hull exceeds allocation"
      | _ => pure ()
    require laid.routingWidth.isSome "producer omitted independent routing width"
    let wider := { laid with width := laid.width + 640, height := laid.height + 320 }
    require (laid.calls {} 0 0 == wider.calls {} 0 0) "canvas expansion changes route geometry"
  let originalSingleWidth : Int := 48
  require (singleton.layout.routeWidth == originalSingleWidth) "singleton lane span changed"
  require (singleton.layout.width == originalSingleWidth + 2 * LOOP_REACH) "singleton loop room missing"
  IO.println "allocation-controls,pass"

def units : IO Unit := do
  let c : Cubic := ⟨(-1501, -1001), (-1, -1), (1001, 2001), (1501, 3001)⟩
  let shape : Keyed Call := ⟨"fractional", .shape .ink 1000 [[c]]⟩
  require ((PaintBounds.call shape.call).geometry == some (IBox.mk (-2) (-2) 2 4)) "shape rounding is not outward"
  require (PaintBounds.textUnmeasured (.cells 0 0 1 "x")) "text metric observation lost"
  require (!(PaintBounds.textUnmeasured (.curve .ink c 1))) "curve invents text metrics"
  let clip : Keyed Call := ⟨"clip", .cut (-1000) (-1000) 2000 2000⟩
  require ((PaintBounds.calls [clip]).geometry.isNone) "clip contributes paint geometry"
  IO.println "unit-controls,pass"

def run (out : Option System.FilePath) : IO Unit := do
  allocation
  units
  let mut count := 0
  IO.println "case,style,allocated_width,allocated_height,x0,y0,x1,y1,fitted_width,fitted_height,text_unmeasured"
  for (name, laid) in controls do
    for (style, look) in styles do
      let calls := laid.calls look 0 0
      let v := GraphBounds.viewport laid calls
      require (inViewport laid calls 0 && inViewport laid calls 12) "raw geometry exceeds viewport"
      require (fittedAtOrigin laid calls 0 && fittedAtOrigin laid calls 12) "translated geometry exceeds viewport"
      require (v.size.1 ≥ laid.width && v.size.2 ≥ laid.height) "fitting shrinks allocation"
      let page : Page := { title := "bounds", graph := some { title := name, laid } }
      let drawing := pageDrawingCached look 640 page {}
      let graphCanvas := IBox.ofSize 0 drawing.size.1 drawing.size.2
      for call in drawing.graph.map (Keyed.move drawing.graphOrigin.1 drawing.graphOrigin.2) do
        match (PaintBounds.call call.call).geometry with
        | none => pure ()
        | some b => require (decide (b.Inside graphCanvas)) "prepared graph exceeds page dimensions"
      if let some dir := out then
        IO.FS.createDirAll dir
        let fitted := v.calls calls
        let calls := (⟨"ground", .fill .ground 1000 0 0 v.size.1 v.size.2⟩ : Keyed Call) :: fitted
        match SvgOut.fileText (SvgOut.picture look v.size.1.toNat v.size.2.toNat 1 (lowerAll 1 calls)) with
        | .error why => throw (IO.userError why)
        | .ok svg => IO.FS.writeFile (dir / s!"{name}-{style}.svg") svg
      count := count + 1
      IO.println s!"{name},{style},{laid.width},{laid.height},{v.bounds.x0},{v.bounds.y0},{v.bounds.x1},{v.bounds.y1},{v.size.1},{v.size.2},{v.unmeasuredText}"
  IO.println s!"rendering-controls,{count},pass"

end GraphBoundsProbe

def main (args : List String) : IO Unit :=
  GraphBoundsProbe.run (args.head?.map System.FilePath.mk)
