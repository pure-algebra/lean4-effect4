import Effect4.Laws.Machine.Map

/-! Finite raw-handle controls and theorem trust queries for string-map operations.
These helpers serve `m7-exit-handles-valid` through the native atom handle subsets. -/

open Effect4 Effect4.Machine Effect4.Store

private def raw : Val := .handle 255 7
private def mapValue : Val := Map.write [("x", raw)]

#guard Map.get mapValue "x" = some (.some raw)
#guard Map.get mapValue "absent" = some .none
#guard (Map.set mapValue "y" (.handle 254 9)).map Val.handles = some [(255, 7), (254, 9)]
#guard (Map.keys mapValue).map Val.handles = some []
#guard (Map.entries mapValue).map Val.handles = some [(255, 7)]
#guard (Map.fromEntries (.list [.list [.str "x", raw], .list [.str "x", .handle 254 9]])).map
  Val.handles = some [(254, 9)]
#guard Map.fromEntries (.list [.pair (.str "x") raw]) = none
#guard Map.get (.list [.list [.str "x", raw]]) "x" = none

#print axioms Map.readPairs_map
#print axioms Map.readTuples_map
#print axioms Map.readPairs_exact
#print axioms Map.readTuples_exact
#print axioms Map.read_write
#print axioms Map.read_exact
#print axioms Map.write_handles
#print axioms Map.tupleEntries_handles
#print axioms Map.read_handles
#print axioms Map.get_handles
#print axioms Map.set_handles
#print axioms Map.keys_handles
#print axioms Map.entries_handles
#print axioms Map.fromEntries_handles
