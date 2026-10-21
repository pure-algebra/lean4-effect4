import Test.Api.SessionContract
import Tools.View.FlowSpecimen
import Tools.View.SvgOut
open Effect4 Effect4.Program Effect4.Api Test.Api.SessionFixtures
open Tools.View

/-! The to-do's term beside its graph: the view's own page, the program's lines above and its flow
below, keyed by address. Nothing new is drawn: `FlowSpecimen.page`, `pageDrawingCached`, `SvgOut`. -/

def writeTerm (name : String) (program : NativeEff) : IO Unit := do
  let g := FlowSpecimen.page 0 name "the term and its flow" program
  let L : Look := {}
  let d := pageDrawingCached L 1280 g {}
  let calls := d.calls
  match SvgOut.fileText (SvgOut.picture L d.size.1.toNat d.size.2.toNat 1 (lowerAll 1 calls)) with
  | .ok text => IO.FS.writeFile s!"tools/view/out/view-graph/{name}.svg" text
  | .error why => throw (IO.userError why)
  IO.println s!"{name}: {g.lines.size} lines, size {d.size}"
  for l in g.lines.toList.take 12 do IO.println s!"  {l.gutter}\t{l.depth}\t{l.text}\t{l.type}"

def proveOut : IO Unit := do
  let some b := todoSession | throw (IO.userError "no session")
  let some (_, _, main, _) := b.program.block? | throw (IO.userError "no block")
  writeTerm "term-main" main
  writeTerm "term-block" b.program

#eval proveOut
