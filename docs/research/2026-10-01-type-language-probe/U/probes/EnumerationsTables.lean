import ProbeU.Enum
import OCaml5.Eff.Metadata

/-! Probe U, question 1: the metadata fixture's per-constructor sample table reaches every
constructor (tested); it is a hand copy of what `TyCtor.all` and `sampleLeaf` emit. -/

open ProbeU

#guard missing (OCaml5.Eff.Metadata.types.map (·.2)) == []
#guard (OCaml5.Eff.Metadata.types.map (·.1)) ==
  ["never", "unknown", "unit", "nat", "int", "string", "bool", "handle", "option", "list", "prod",
   "except", "exitOf", "causeOf", "fiberOf", "union", "lit", "refOf", "deferredOf", "var"]
#guard (OCaml5.Eff.Metadata.types.map (·.1)) != TyCtor.all.map TyCtor.name
