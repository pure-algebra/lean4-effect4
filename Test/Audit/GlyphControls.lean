import Tools.View.Glyph
import Tools.View.Tube.PegChecks
import Tools.View.Tube.Tile

/-!
# Controls of the vocabulary of marks (VS-1, decisions row 367, point 6)

`Tools.View.Glyph.check` is Moody's semiotic clarity over the table of marks, and the view tool
builds only when the table passes it. Each line is a control: the table with one fault, refused
for that fault and for nothing else (decisions row 301). Every value stands inside its `#guard`.
-/

namespace Test.Audit.GlyphControls

open Tools.View.Glyph

-- control: a constructor with no mark (deficit)
#guard check sorts table.tail shapeNames == ["deficit: Effect4.Program.Eff.succeed has no mark"]

-- control: two constructors of one sort drawn alike (overload)
#guard check sorts (table.map fun r =>
    if r.ctor == ``Effect4.Program.ActionTerm.forkIn then { r with variant := "" } else r) shapeNames ==
  ["overload: Effect4.Program.ActionTerm.fork and Effect4.Program.ActionTerm.forkIn are drawn alike (fork, )"]

-- control: one word drawn by two marks (redundancy): a fork in the score drawn as a sequence
#guard check sorts (table.map fun r =>
    if r.ctor == ``Effect4.Machine.RunEvent.forked then { r with shape := .series } else r) shapeNames ==
  ["redundancy: \"fork\" is drawn by 2 marks"]

-- control: a row for no constructor of a sort drawn, and a mark that draws nothing (excess)
#guard check sorts (table ++ [⟨``Nat.succ, .box, "", "run", "x"⟩]) shapeNames ==
  ["excess: Nat.succ is no constructor of a sort drawn"]
#guard (check sorts (table.filter (·.shape != .caesura)) shapeNames).getLast? ==
  some "excess: the mark Tools.View.Glyph.Shape.caesura draws nothing"

-- A real bind places its two addressed operations in successive cells.
#guard
  let program : Effect4.Program.NativeEff :=
    .bind (.succeed (.lit (.nat 3))) (.succeed (.var 0))
  let tile := Tools.View.Tube.Tile.ofProgram (fun _ ctor _ => ctor) program
  tile.items.map (·.address) == [[0], [1]] &&
    tile.items.map (·.value) == ["succeed", "succeed"] && tile.w == 17 && tile.h == 10

-- Scalars before children do not consume child addresses.
#guard
  let program : Effect4.Program.NativeEff :=
    .select (.lit (.bool true)) .bool (.succeed (.lit (.nat 3))) (.fail (.lit (.nat 4)))
  let tile := Tools.View.Tube.Tile.ofProgram (fun _ ctor _ => ctor) program
  tile.items.map (·.address) == [[], [0], [1]] &&
    tile.items.map (·.value) == ["select", "succeed", "fail"]

-- A list spine keeps its nested addresses without drawing cons or nil cells.
#guard
  let program : Effect4.Program.NativeEff :=
    .gen (.cons (.yieldDiscard (.succeed (.lit (.nat 3)))) (.cons (.ret (.var 0)) .nil))
  let tile := Tools.View.Tube.Tile.ofProgram (fun _ ctor _ => ctor) program
  tile.items.map (·.address) == [[], [0, 0, 0], [0, 1, 0]] &&
    tile.items.map (·.value) == ["gen", "succeed", "ret"]

-- A zero-child spine has no allocated cell or room.
#guard
  let tile := Tools.View.Tube.Tile.layer (Op := Effect4.Program.NativeOp)
    (fun _ ctor _ => ctor) .stmts "nil" [] []
  tile.items.isEmpty && tile.w == 0 && tile.h == 0

end Test.Audit.GlyphControls
