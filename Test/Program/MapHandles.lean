import Effect4.Laws.Machine.Map
import Effect4.Laws.Program.Handles.Term

/-! Finite raw-handle controls for string-map operations.
These helpers serve `straight-meaning-typed` through the native atom handle subsets. -/

open Effect4 Effect4.Machine Effect4.Store

private def raw : Store.Val := .handle 255 7
private def mapValue : Store.Val := Map.write [("x", raw)]

#guard Map.get mapValue "x" = some (.some raw)
#guard Map.get mapValue "absent" = some .none
#guard (Map.set mapValue "y" (.handle 254 9)).map Val.handles = some [(255, 7), (254, 9)]
#guard (Map.keys mapValue).map Val.handles = some []
#guard (Map.entries mapValue).map Val.handles = some [(255, 7)]
#guard (Map.fromEntries (.list [.list [.str "x", raw], .list [.str "x", .handle 254 9]])).map
  Val.handles = some [(254, 9)]
#guard Map.fromEntries (.list [.pair (.str "x") raw]) = none
#guard Map.get (.list [.list [.str "x", raw]]) "x" = none

#guard Map.fromEntries (Machine.Val.fibers []) = some (.list [])
#guard Map.fromEntries (Machine.Val.fibers [⟨0⟩]) = none

#guard Program.evalTerm [mapValue] (.app "mapGet"
  (.cons (.var 0) (.cons (.lit (.str "x")) .nil))) = some (.some raw)
#guard Program.evalTerm [Machine.Val.fibers []] (.app "mapFromEntries"
  (.cons (.var 0) .nil)) = some (.list [])
