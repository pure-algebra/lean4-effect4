import Tools.View.Graph
import ProofGraph.AxiomAudit

/-! Finite controls of graph typography's row budget and unchanged default labels. -/

open Tools.View

-- A range includes negative, zero, narrow, and non-cell-aligned box widths.
#guard ((List.range 290).map (fun n : Nat => (n : Int) - 20)).all fun width =>
  GraphText.row none "leaf" 8 12 (width - 2 * CELL) "abcdefgh" ==
    cellsAt "leaf" 8 (12 + BASE) "abcdefgh" (width / CELL - 2)

-- A proportional face is bounded by an explicit clip in both output paths.
#guard GraphText.row (some .name) "leaf" 8 12 80 "operation" ==
  [⟨"leaf", .cut 8 12 80 ROWH⟩, ⟨"leaf", .text .name 8 (12 + BASE) 80 "operation"⟩,
    ⟨"leaf", .uncut⟩]
#guard GraphText.row (some .name) "leaf" 8 12 0 "operation" == []

-- Growth retains its existing text threshold and hit allocation.
#guard ((List.range 11).map (· * 100)).all fun grow =>
  let placed : Placed := { key := "leaf", x := 11, y := 19, w := 80, grow }
  let node : GNode := { key := "leaf", line1 := "operation", line2 := "argument" }
  let calls := Laid.boxCalls {} 0 0 placed node { first := some .name }
  (calls.any fun c => match c.call with | .text .. => true | _ => false) == (grow == 1000)

#axiom_audit checked Tools.View.GraphText
