import Test.Api.SessionContract
import Compiler.Page
import Tools.View.SvgOut
open Effect4 Effect4.Program Effect4.Api Test.Api.SessionFixtures
open Tools.View

/-! The to-do's object page: its lines typed at the object's rows, the relation row beside each line,
and the flows below, the bodies side by side and main under them (`Compiler.Page.page`). Written
with the view's own picture (`pageDrawingCached`, `SvgOut`): nothing new is drawn. -/

def proveOut : IO Unit := do
  let some b := todoSession | throw (IO.userError "no session")
  let g := Compiler.Page.page b "the to-do: term, rows and flows"
  let L : Look := {}
  let d := pageDrawingCached L 1280 g {}
  match SvgOut.fileText (SvgOut.picture L d.size.1.toNat d.size.2.toNat 1 (lowerAll 1 d.calls)) with
  | .ok text => IO.FS.writeFile "docs/research/2026-10-21-view-graph/out/object-page.gen.svg" text
  | .error why => throw (IO.userError why)
  IO.println s!"lines {g.lines.size}, size {d.size}, refused {(g.lines.filter (·.state == .refused)).size}"
  let some panel := g.graph | throw (IO.userError "no graph")
  IO.println s!"placed {panel.laid.placed.size}, routes {panel.laid.routes.size}, regions {panel.laid.regions.size}, apart {panel.laid.boxesApart}, descend {panel.laid.edgesDescend}"
  for l in g.lines.toList.take 8 do IO.println s!"  {l.key}\t{l.text}\t{l.type}\t{l.note}"
  for s in (g.code.map (·.lines.toList.take 8)).getD [] do IO.println s!"  | {s}"
  for r in panel.laid.regions.toList do IO.println s!"  region {r.key}\t{r.name}\t{r.x},{r.y} {r.w}×{r.h}"

#eval proveOut
