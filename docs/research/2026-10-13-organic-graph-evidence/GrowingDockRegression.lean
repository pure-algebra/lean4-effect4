import Tools.View.Graph
open Tools.View
def growingTarget : Placed :=
  { key := "b", x := 0, y := 72, w := 80,
    node := some { key := "b", line1 := "b" }, grow := 483 }
#eval Laid.entryAt growingTarget
#guard (Laid.entryAt growingTarget).2 == 84
