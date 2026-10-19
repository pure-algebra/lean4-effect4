import Effect4
import Effect4.Laws.Auto.Traversals

/-! Probe (coherence audit, lean core, 2026-10-19): the store's shape sort and the JSON trees.
Read-only. -/

#traversal_census Effect4.Store.Shape
#traversal_census Effect4.Json
#traversal_census Effect4.NatJson
#traversal_census Effect4.Representation
